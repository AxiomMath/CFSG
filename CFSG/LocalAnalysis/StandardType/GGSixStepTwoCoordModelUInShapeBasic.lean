module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUComp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordShapeAlign

public section

namespace CFSG.StandardType

namespace CoordSUIn

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CoordSU Multiplicative
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

section Decomp

@[expose] def cvA (F : PieceFrame f n K h p A) : Set (Fin n → K) :=
  {v | ∀ j, v ∈ (rng (F.y j)).orthogonalBilin (stdHermForm h n)}

theorem mem_cvA {F : PieceFrame f n K h p A} {v : Fin n → K} :
    v ∈ cvA F ↔ ∀ j, v ∈ (rng (F.y j)).orthogonalBilin (stdHermForm h n) :=
  Iff.rfl

theorem exists_decomp_pieces (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    (v : Fin n → K) :
    ∃ w : Fin F.r → (Fin n → K), (∀ l, w l ∈ rng (F.y l)) ∧
      (∀ l, ∀ x ∈ rng (F.y l), stdHermForm h n x (w l) = stdHermForm h n x v) ∧
      v - ∑ l, w l ∈ cvA F := by
  classical
  have hdec : ∀ l, ∃ m ∈ rng (F.y l), ∃ z ∈ (rng (F.y l)).orthogonalBilin (stdHermForm h n),
      m + z = v := fun l => exists_add_orth (F.nondeg hA l) v
  choose w hw z hz hwz using hdec
  have hcomp : ∀ l, ∀ x ∈ rng (F.y l), stdHermForm h n x (w l) = stdHermForm h n x v := by
    intro l x hx
    have e : stdHermForm h n x (z l) = 0 := (Submodule.mem_orthogonalBilin.mp (hz l)) x hx
    rw [← hwz l, map_add, e, add_zero]
  refine ⟨w, hw, hcomp, fun j => Submodule.mem_orthogonalBilin.mpr fun m' hm' => ?_⟩
  have hsum : ∑ l, stdHermForm h n m' (w l) = stdHermForm h n m' (w j) :=
    Finset.sum_eq_single j (fun l _ hlj => F.orth j l (Ne.symm hlj) m' hm' (w l) (hw l))
      (fun h' => absurd (Finset.mem_univ j) h')
  change stdHermForm h n m' (v - ∑ l, w l) = 0
  rw [map_sub, map_sum, hsum, hcomp j m' hm', sub_self]

theorem stdHermForm_eq_zero_of_cvA {F : PieceFrame f n K h p A} {v w : Fin n → K}
    (hv : v ∈ cvA F) {l : Fin F.r} (hw : w ∈ rng (F.y l)) :
    stdHermForm h n w v = 0 ∧ stdHermForm h n v w = 0 := by
  have h1 : stdHermForm h n w v = 0 := (Submodule.mem_orthogonalBilin.mp (hv l)) w hw
  refine ⟨h1, ?_⟩
  rw [← (stdHermForm_isSymm h n).eq w v, h1, map_zero]

theorem nondegOn_cvA (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) {m : Fin n → K}
    (hm : m ∈ cvA F) (hz : ∀ z ∈ cvA F, stdHermForm h n z m = 0) : m = 0 := by
  have hall : ∀ v, stdHermForm h n v m = 0 := by
    intro v
    obtain ⟨w, hw, -, hv⟩ := exists_decomp_pieces hA F v
    have hsplit : v = ∑ l, w l + (v - ∑ l, w l) := by abel
    rw [hsplit, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, hz _ hv, add_zero]
    exact Finset.sum_eq_zero fun l _ => (stdHermForm_eq_zero_of_cvA hm (hw l)).1
  refine stdHermForm_separatingLeft h n m fun v => ?_
  rw [← (stdHermForm_isSymm h n).eq v m, hall v, map_zero]

theorem lin_ι_apply_of_cvA (F : PieceFrame f n K h p A) (s : Multiplicative (Fin F.r → ZMod p))
    {v : Fin n → K} (hv : v ∈ cvA F) : lin (F.ι s) v = v :=
  (F.ι_fix s v).mpr fun j _ => hv j

end Decomp

section Rel

variable {r : ℕ}

@[expose] def ORel (O : Subgroup (ZMod p)ˣ) (T : Set (Fin r → ZMod p)) (k l : Fin r) : Prop :=
  ∃ c ∈ O, ∀ t ∈ T, t l = (c : ZMod p) * t k

variable {O : Subgroup (ZMod p)ˣ} {T : Set (Fin r → ZMod p)}

theorem ORel.refl (k : Fin r) : ORel O T k k :=
  ⟨1, O.one_mem, fun t _ => by rw [Units.val_one, one_mul]⟩

theorem ORel.symm {k l : Fin r} (hkl : ORel O T k l) : ORel O T l k := by
  obtain ⟨c, hcO, hc⟩ := hkl
  refine ⟨c⁻¹, O.inv_mem hcO, fun t ht => ?_⟩
  rw [hc t ht, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem ORel.trans {k l m : Fin r} (hkl : ORel O T k l) (hlm : ORel O T l m) :
    ORel O T k m := by
  obtain ⟨c, hcO, hc⟩ := hkl
  obtain ⟨c', hcO', hc'⟩ := hlm
  refine ⟨c' * c, O.mul_mem hcO' hcO, fun t ht => ?_⟩
  rw [hc' t ht, hc t ht, Units.val_mul, mul_assoc]

theorem exists_sep_of_not_rel [Fact p.Prime]
    (hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T) {k l : Fin r}
    {t₀ : Fin r → ZMod p} (ht₀ : t₀ ∈ T) (hk : t₀ k ≠ 0) (hkl : ¬ ORel O T k l) :
    ∃ t ∈ T, (∀ c ∈ O, t l ≠ (c : ZMod p) * t k) ∧ (t l ≠ 0 ∨ t k ≠ 0) := by
  by_contra hno
  push Not at hno
  have hno' : ∀ t ∈ T, (∃ c ∈ O, t l = (c : ZMod p) * t k) ∨ (t l = 0 ∧ t k = 0) := by
    intro t ht
    by_cases hc : ∃ c ∈ O, t l = (c : ZMod p) * t k
    · exact Or.inl hc
    · push Not at hc
      exact Or.inr (hno t ht hc)
  obtain ⟨c₀, hc₀O, hc₀⟩ := (hno' t₀ ht₀).resolve_right fun h' => hk h'.2
  apply hkl
  refine ⟨c₀, hc₀O, fun t ht => ?_⟩
  set a : ZMod p := t k / t₀ k with ha
  have ht' := hT t ht t₀ ht₀ a
  have htk : (t - a • t₀) k = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ha]
    rw [div_mul_cancel₀ _ hk, sub_self]
  have htl : (t - a • t₀) l = 0 := by
    rcases hno' _ ht' with ⟨c, -, hc⟩ | ⟨h1, -⟩
    · rw [hc, htk, mul_zero]
    · exact h1
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at htl
  rw [sub_eq_zero] at htl
  rw [htl, hc₀, ha, mul_left_comm, div_mul_cancel₀ _ hk]

end Rel

section Pieces

theorem exists_pieceIn_of_piece (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {x : ↥(unitarySU 2 f K n)} (hxA : x ∈ A) (k : Fin F.r) :
    ∃ a ∈ primaryFactors (Xe x), PieceIn F x a k := by
  classical
  have H := primaryData h hA.prime hA.ne_two (hA.pow x hxA)
  by_contra hno
  push Not at hno
  apply b_ne_one hA F k
  refine eq_of_lin_apply fun v => ?_
  rw [lin_one, Module.End.one_apply]
  have hsum := eq_sum_primaryProjection H.squarefree v
  have hfix : ∀ b ∈ primaryFactors (Xe x),
      lin (F.b k) (primaryProjection (Xe x) b v) = primaryProjection (Xe x) b v := fun b hb =>
    (piece_orbW hA F hxA hb k).resolve_left (hno b hb) _
      (Submodule.mem_sup_left (primaryProjection_mem H.squarefree hb v))
  calc lin (F.b k) v
      = lin (F.b k) (∑ b ∈ primaryFactors (Xe x), primaryProjection (Xe x) b v) := by
        rw [← hsum]
    _ = ∑ b ∈ primaryFactors (Xe x), primaryProjection (Xe x) b v := by
        rw [map_sum]
        exact Finset.sum_congr rfl hfix
    _ = v := hsum.symm

theorem eq_zero_of_pieceIn_X_sub_C_one (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {t : Fin F.r → ZMod p}
    (h1 : (X - C 1 : K[X]) ∈ primaryFactors (Xe (F.ι (ofAdd t)))) {k : Fin F.r}
    (hk : PieceIn F (F.ι (ofAdd t)) (X - C 1) k) : t k = 0 := by
  have hle := le_orbW_of_pieceIn hA F (ι_mem F _) h1 hk
  have hfix : ∀ u ∈ rng (F.y k), lin (F.ι (ofAdd t)) u = u := by
    intro u hu
    have hu' := hle hu
    rw [orbW, dualPoly_X_sub_C_one, sup_idem, primaryComponent_X_sub_C_one, LinearMap.mem_ker,
      LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hu'
    exact hu'
  have := F.coord_eq_zero hA hfix
  rwa [toAdd_ofAdd] at this

end Pieces

section Invariance

@[expose] def classSpace (F : PieceFrame f n K h p A) (O : Subgroup (ZMod p)ˣ)
    (T : Set (Fin F.r → ZMod p)) (k : Fin F.r) : Set (Fin n → K) :=
  {v | (∀ m ∈ cvA F, stdHermForm h n m v = 0) ∧
    ∀ l, ¬ ORel O T k l → v ∈ (rng (F.y l)).orthogonalBilin (stdHermForm h n)}

variable {F : PieceFrame f n K h p A} {O : Subgroup (ZMod p)ˣ} {T : Set (Fin F.r → ZMod p)}

theorem eq_sum_of_mem_classSpace (hA : MaxElemAb p A) {k : Fin F.r} {v : Fin n → K}
    (hv : v ∈ classSpace F O T k) :
    ∃ w : Fin F.r → (Fin n → K), (∀ l, w l ∈ rng (F.y l)) ∧ (∀ l, ¬ ORel O T k l → w l = 0) ∧
      v = ∑ l, w l := by
  obtain ⟨hv₀, hvX⟩ := hv
  obtain ⟨w, hw, hcomp, hv'⟩ := exists_decomp_pieces hA F v
  refine ⟨w, hw, fun l hl => F.nondeg hA l (w l) (hw l) fun x hx => ?_, ?_⟩
  · rw [hcomp l x hx]
    exact (Submodule.mem_orthogonalBilin.mp (hvX l hl)) x hx
  · have h0 : v - ∑ l, w l = 0 := nondegOn_cvA hA F hv' fun z hz => by
      rw [map_sub, hv₀ z hz, map_sum, zero_sub, neg_eq_zero]
      exact Finset.sum_eq_zero fun l _ => (stdHermForm_eq_zero_of_cvA hz (hw l)).2
    exact (sub_eq_zero.mp h0)

theorem mem_classSpace_of_rel {k l : Fin F.r} (hkl : ORel O T k l) {u : Fin n → K}
    (hu : u ∈ rng (F.y l)) : u ∈ classSpace F O T k := by
  refine ⟨fun m hm => (stdHermForm_eq_zero_of_cvA hm hu).2, fun l' hl' => F.mem_orth ?_ hu⟩
  rintro rfl
  exact hl' hkl

theorem lin_mem_orth_of_sep (hA : MaxElemAb p A) (hFm : FrameMoves F) {t : Fin F.r → ZMod p}
    {k l : Fin F.r} (hsep : ∀ c ∈ negQ p (2 ^ f), t l ≠ (c : ZMod p) * t k)
    (hne : t l ≠ 0 ∨ t k ≠ 0) {Y : ↥(unitarySU 2 f K n)}
    (hY : Y * F.ι (ofAdd t) = F.ι (ofAdd t) * Y) {u : Fin n → K} (hu : u ∈ rng (F.y k)) :
    lin Y u ∈ (rng (F.y l)).orthogonalBilin (stdHermForm h n) := by
  have hxA : F.ι (ofAdd t) ∈ A := ι_mem F _
  have hYC : Y ∈ Subgroup.centralizer {F.ι (ofAdd t)} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hY
  by_cases htk : t k = 0
  · have htl : t l ≠ 0 := hne.resolve_right (not_not.mpr htk)
    have hfix : lin (F.ι (ofAdd t)) (lin Y u) = lin Y u := by
      rw [← Module.End.mul_apply, ← lin_mul, ← hY, lin_mul, Module.End.mul_apply,
        lin_ι_apply_of_eq_zero F htk hu]
    exact (F.ι_fix _ _).mp hfix l (by rwa [toAdd_ofAdd])
  · obtain ⟨a, ha, hi⟩ := exists_pieceIn_of_piece hA F hxA k
    have ha1 : a ≠ X - C 1 := by
      rintro rfl
      exact htk (eq_zero_of_pieceIn_X_sub_C_one hA F ha hi)
    have hYW : lin Y u ∈ orbW h (F.ι (ofAdd t)) a :=
      orbW_inv hYC u (le_orbW_of_pieceIn hA F hxA ha hi hu)
    have hi' : ¬ PieceIn F (F.ι (ofAdd t)) a l := by
      intro hi'
      obtain ⟨o, hoO, ho⟩ := exists_negQ_mul_of_pieceIn hA F hFm rfl ha ha1 hi hi'
      exact hsep o hoO ho
    exact mem_orth_of_not_pieceIn hA F hxA ha hi' hYW

theorem lin_mem_cvA (hZ : ∀ k, ∃ t ∈ T, t k ≠ 0) {Y : ↥(unitarySU 2 f K n)}
    (hY : ∀ t ∈ T, Y * F.ι (ofAdd t) = F.ι (ofAdd t) * Y) {v : Fin n → K} (hv : v ∈ cvA F) :
    lin Y v ∈ cvA F := by
  intro j
  obtain ⟨t, ht, htj⟩ := hZ j
  have h1 : lin (F.ι (ofAdd t)) (lin Y v) = lin Y v := by
    rw [← Module.End.mul_apply, ← lin_mul, ← hY t ht, lin_mul, Module.End.mul_apply,
      lin_ι_apply_of_cvA F _ hv]
  exact (F.ι_fix _ _).mp h1 j (by rwa [toAdd_ofAdd])

theorem lin_mem_classSpace [Fact p.Prime] (hA : MaxElemAb p A) (hFm : FrameMoves F)
    (hT : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T) (hZ : ∀ k, ∃ t ∈ T, t k ≠ 0)
    {Y : ↥(unitarySU 2 f K n)} (hY : ∀ t ∈ T, Y * F.ι (ofAdd t) = F.ι (ofAdd t) * Y)
    {k : Fin F.r} {v : Fin n → K} (hv : v ∈ classSpace F (negQ p (2 ^ f)) T k) :
    lin Y v ∈ classSpace F (negQ p (2 ^ f)) T k := by
  have hY' : ∀ t ∈ T, Y⁻¹ * F.ι (ofAdd t) = F.ι (ofAdd t) * Y⁻¹ := fun t ht =>
    (show Commute Y (F.ι (ofAdd t)) from hY t ht).inv_left
  obtain ⟨w, hw, hw0, rfl⟩ := eq_sum_of_mem_classSpace hA hv
  refine ⟨fun m hm => ?_, fun l hl => ?_⟩
  · have hm' : lin Y⁻¹ m ∈ cvA F := lin_mem_cvA hZ hY' hm
    have h1 := isometry_lin h Y (lin Y⁻¹ m) (∑ l, w l)
    rw [← Module.End.mul_apply, ← lin_mul, mul_inv_cancel, lin_one, Module.End.one_apply] at h1
    rw [h1, map_sum]
    exact Finset.sum_eq_zero fun j _ => (stdHermForm_eq_zero_of_cvA hm' (hw j)).2
  · rw [map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : ORel (negQ p (2 ^ f)) T k j
    · have hjl : ¬ ORel (negQ p (2 ^ f)) T j l := fun h' => hl (hj.trans h')
      obtain ⟨t₀, ht₀, ht₀j⟩ := hZ j
      obtain ⟨t, ht, hsep, hne⟩ := exists_sep_of_not_rel hT ht₀ ht₀j hjl
      exact lin_mem_orth_of_sep hA hFm hsep hne (hY t ht) (hw j)
    · rw [hw0 j hj, map_zero]
      exact Submodule.zero_mem _

end Invariance

section Fix

@[expose] def fixSU (S : Set (Fin n → K)) : Subgroup ↥(unitarySU 2 f K n) where
  carrier := {Y | ∀ v ∈ S, lin Y v = v}
  mul_mem' := by
    intro Y Z hY hZ v hv
    change lin (Y * Z) v = v
    rw [lin_mul, Module.End.mul_apply, hZ v hv, hY v hv]
  one_mem' := fun v _ => by
    change lin 1 v = v
    rw [lin_one]
    rfl
  inv_mem' := by
    intro Y hY v hv
    change lin Y⁻¹ v = v
    conv_lhs => rw [← hY v hv]
    rw [← Module.End.mul_apply, ← lin_mul, inv_mul_cancel, lin_one]
    rfl

theorem mem_fixSU {S : Set (Fin n → K)} {Y : ↥(unitarySU 2 f K n)} :
    Y ∈ fixSU S ↔ ∀ v ∈ S, lin Y v = v :=
  Iff.rfl

theorem normal_fixSU {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G} {H : Subgroup G}
    (hH : H ≤ φ.range) {S : Set (Fin n → K)}
    (hS : ∀ Y : ↥(unitarySU 2 f K n), φ Y ∈ H → ∀ v ∈ S, lin Y v ∈ S) :
    (((fixSU S).map φ ⊓ H).subgroupOf H).Normal := by
  constructor
  intro m hm g
  rw [Subgroup.mem_subgroupOf] at hm ⊢
  obtain ⟨⟨Z, hZ, hZm⟩, hmH⟩ := Subgroup.mem_inf.mp hm
  obtain ⟨Y, hY⟩ := hH g.2
  have hYi : φ Y⁻¹ ∈ H := by
    rw [map_inv, hY]
    exact H.inv_mem g.2
  refine Subgroup.mem_inf.mpr ⟨⟨Y * Z * Y⁻¹, fun v hv => ?_, ?_⟩, ?_⟩
  · rw [lin_mul, lin_mul, Module.End.mul_apply, Module.End.mul_apply, hZ _ (hS _ hYi v hv),
      ← Module.End.mul_apply, ← lin_mul, mul_inv_cancel, lin_one]
    rfl
  · rw [map_mul, map_mul, map_inv, hY, hZm]
    simp
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact H.mul_mem (H.mul_mem g.2 hmH) (H.inv_mem g.2)

theorem exists_cover_two {s : ℕ} (P : Fin s → Prop)
    (h : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → P a → P b → P c → False) (i₀ : Fin s) :
    ∃ j₁ j₂, ∀ i, P i → i = j₁ ∨ i = j₂ := by
  by_cases h1 : ∃ a, P a
  · obtain ⟨a, ha⟩ := h1
    by_cases h2 : ∃ b, P b ∧ b ≠ a
    · obtain ⟨b, hb, hba⟩ := h2
      refine ⟨a, b, fun i hi => ?_⟩
      by_contra hne
      push Not at hne
      exact h a b i (Ne.symm hba) (Ne.symm hne.1) (Ne.symm hne.2) ha hb hi
    · refine ⟨a, a, fun i hi => ?_⟩
      by_contra hne
      push Not at hne
      exact h2 ⟨i, hi, hne.1⟩
  · exact ⟨i₀, i₀, fun i hi => absurd ⟨i, hi⟩ h1⟩

theorem ofAdd_sum_smul_mem {G : Type} [Group G] {s m : ℕ} [NeZero p]
    {ι : Multiplicative (Fin s → ZMod p) →* G} {H : Subgroup G} (w : Fin m → Fin s → ZMod p)
    (hw : ∀ a, ι (ofAdd (w a)) ∈ H) (x : Fin m → ZMod p) : ι (ofAdd (∑ a, x a • w a)) ∈ H := by
  refine Finset.sum_induction _ (fun u => ι (ofAdd u) ∈ H) (fun a b ha hb => ?_) ?_
    fun a _ => StepTwoToral.ofAdd_smul_mem (hw a) (x a)
  · rw [ofAdd_add, map_mul]
    exact H.mul_mem ha hb
  · rw [ofAdd_zero, map_one]
    exact H.one_mem

theorem mem_centralizer_of_commutator_eq_bot {G : Type} [Group G] {J N : Subgroup G}
    (hN : ⁅J, N⁆ = ⊥) {b : G} (hb : b ∈ N) : b ∈ Subgroup.centralizer (J : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hN ha
  exact ((Subgroup.mem_centralizer_iff.mp h1) b hb).symm

end Fix

end CoordSUIn

end CFSG.StandardType
