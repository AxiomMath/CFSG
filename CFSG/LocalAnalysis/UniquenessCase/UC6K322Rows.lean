module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.UniquenessCase.UC6K322Lin
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.K322Rows

open Matrix Subgroup CFSG.RepresentationTheory CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UCK (IrredGL3 cartanOfDecomp)
open scoped commutatorElement
open CFSG.RankThree.SubgroupLists (translate IsTransitiveMonomial omegaGL)

variable {p : ℕ} [Fact p.Prime]

theorem irreducible_of_irredGL3 {G : Subgroup (GL (Fin 3) (ZMod p))} (hG : IrredGL3 p G) :
    IsIrreducibleMatrixRep G.subtype := fun W hW => hG W fun g hg w hw => hW ⟨g, hg⟩ w hw

@[expose] def tv {F : Type*} [Field F] (c : F) : Matrix (Fin 3) (Fin 3) F :=
  Matrix.transvection (0 : Fin 3) (1 : Fin 3) c

theorem tv_mul {F : Type*} [Field F] (c d : F) : tv c * tv d = tv (c + d) :=
  Matrix.transvection_mul_transvection_same (0 : Fin 3) (1 : Fin 3) (by decide) c d

@[expose] def transvGL {F : Type*} [Field F] : GL (Fin 3) F :=
  ⟨tv 1, tv (-1), by rw [tv_mul, add_neg_cancel, tv, Matrix.transvection_zero],
    by rw [tv_mul, neg_add_cancel, tv, Matrix.transvection_zero]⟩

theorem transvGL_pow {F : Type*} [Field F] (k : ℕ) :
    ((transvGL ^ k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = tv (k : F) := by
  induction k with
  | zero => simp [tv]
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ih]
    show tv (k : F) * tv 1 = _
    rw [tv_mul, Nat.cast_succ]

theorem p_dvd_card_statedSL : p ∣ Nat.card (StatedSL 3 (ZMod p)) := by
  have hT : (transvGL : GL (Fin 3) (ZMod p)) ∈ StatedSL 3 (ZMod p) :=
    Subgroup.subset_closure (show (tv (1 : ZMod p)).det = 1 from
      Matrix.det_transvection_of_ne (0 : Fin 3) (1 : Fin 3) (by decide) 1)
  have hp : (transvGL ^ p : GL (Fin 3) (ZMod p)) = 1 := by
    apply Units.ext
    rw [transvGL_pow, ZMod.natCast_self, tv, Matrix.transvection_zero, Units.val_one]
  have h1 : (transvGL : GL (Fin 3) (ZMod p)) ≠ 1 := by
    intro h
    have := congrArg (fun g : GL (Fin 3) (ZMod p) => (g : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1) h
    simp [transvGL, tv, Matrix.transvection, Matrix.one_apply] at this
  have hord : orderOf (⟨transvGL, hT⟩ : StatedSL 3 (ZMod p)) = p := by
    apply orderOf_eq_prime
    · exact Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hp)
    · exact fun h => h1 (congrArg Subtype.val h)
  have h := orderOf_dvd_natCard (⟨transvGL, hT⟩ : StatedSL 3 (ZMod p))
  rwa [hord] at h

theorem p_dvd_card_psl2 : p ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) := by
  have hdet : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    simp [Matrix.det_fin_two]
  let u : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := ⟨!![1, 1; 0, 1], hdet⟩
  have hdetw : (!![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
    simp [Matrix.det_fin_two]
  let w : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) := ⟨!![1, 0; 1, 1], hdetw⟩
  have hpow : ∀ k : ℕ, ((u ^ k : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
      Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, (k : ZMod p); 0, 1] := by
    intro k
    induction k with
    | zero => simp [Matrix.one_fin_two]
    | succ k ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
      show !![1, (k : ZMod p); 0, 1] * !![1, 1; 0, 1] = _
      rw [Matrix.mul_fin_two]
      simp only [mul_one, mul_zero, add_zero, zero_mul, zero_add, one_mul, Nat.cast_succ]
      rw [add_comm]
  set π := QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
  have hup : π u ^ p = 1 := by
    rw [← map_pow]
    have : u ^ p = 1 := by
      apply Subtype.ext
      rw [hpow, ZMod.natCast_self]
      simp [Matrix.one_fin_two]
    rw [this, map_one]
  have hu1 : π u ≠ 1 := by
    intro h
    have hc := Subgroup.mem_center_iff.1 ((QuotientGroup.eq_one_iff u).1 h) w
    have h2 : ((w * u : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 =
        ((u * w : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 := by rw [hc]
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    have hw : (w : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 0; 1, 1] := rfl
    have hu : (u : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, 1; 0, 1] := rfl
    rw [hw, hu, Matrix.mul_fin_two, Matrix.mul_fin_two] at h2
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, mul_one, mul_zero, add_zero, zero_mul, one_mul] at h2
    have : (1 : ZMod p) = 0 := by linear_combination -h2
    exact one_ne_zero this
  have hord : orderOf (π u) = p := orderOf_eq_prime hup hu1
  have h := orderOf_dvd_natCard (π u)
  rwa [hord] at h

theorem p_dvd_card_omegaGL (hp5 : 5 ≤ p) {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M)
    (hdet : M.det ≠ 0) : p ∣ Nat.card (omegaGL M) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hp5 hMt hdet
  rw [Nat.card_congr e.toEquiv]
  exact p_dvd_card_psl2

theorem alt5_sq_of_pow_four : ∀ σ : alternatingGroup (Fin 5), σ ^ 4 = 1 → σ ^ 2 = 1 := by
  decide +kernel

theorem central_sq_of_alt5 {X : Type*} [Group X] {G H : Subgroup X} (hHG : H ≤ G)
    (e : H ≃* alternatingGroup (Fin 5))
    (hprod : ∀ g ∈ G, ∃ h ∈ H, ∃ z ∈ G, (∀ y ∈ G, z * y = y * z) ∧ g = h * z)
    (hint : ∀ z ∈ H, (∀ y ∈ G, z * y = y * z) → z = 1) {x : X} (hxG : x ∈ G)
    (hx4 : x ^ 4 = 1) : ∀ y ∈ G, x ^ 2 * y = y * x ^ 2 := by
  obtain ⟨h, hH, z, hzG, hzc, rfl⟩ := hprod x hxG
  have hhz : Commute h z := (hzc h (hHG hH)).symm
  have hzc' : ∀ k : ℕ, ∀ y ∈ G, z ^ k * y = y * z ^ k := fun k y hy =>
    ((Commute.pow_left (hzc y hy) k))
  have h4 : h ^ 4 = (z ^ 4)⁻¹ := by
    rw [hhz.mul_pow] at hx4
    exact eq_inv_of_mul_eq_one_left hx4
  have h41 : h ^ 4 = 1 := by
    apply hint _ (H.pow_mem hH 4)
    intro y hy
    rw [h4]
    have := hzc' 4 y hy
    calc (z ^ 4)⁻¹ * y = (z ^ 4)⁻¹ * (y * z ^ 4) * (z ^ 4)⁻¹ := by group
      _ = (z ^ 4)⁻¹ * (z ^ 4 * y) * (z ^ 4)⁻¹ := by rw [this]
      _ = y * (z ^ 4)⁻¹ := by group
  have h21 : h ^ 2 = 1 := by
    have h1 : (⟨h, hH⟩ : H) ^ 4 = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact h41)
    have h2 := alt5_sq_of_pow_four (e ⟨h, hH⟩) (by rw [← map_pow, h1, map_one])
    rw [← map_pow, MulEquiv.map_eq_one_iff] at h2
    have := congrArg Subtype.val h2
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  intro y hy
  rw [hhz.mul_pow, h21, one_mul]
  exact hzc' 2 y hy

theorem isQuasisimple_of_simple_k322 {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨a, b, hab⟩ := hnab
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exact absurd (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a) hab
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h | h
    · exfalso
      apply hab
      have hm : ⁅a, b⁆ ∈ commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hm
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).isSimpleGroup

theorem not_comm_of_isQuasisimple_k322 {X : Type*} [Group X] (hq : CFSG.Open.IsQuasisimple X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : commutator X = ⊥ := by
    rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact h a b
  have hone : ∀ a : X, a = 1 := fun a => by
    have ha : a ∈ commutator X := hq.1 ▸ Subgroup.mem_top a
    rw [hc, Subgroup.mem_bot] at ha
    exact ha
  haveI := hq.2
  obtain ⟨u, v, huv⟩ := (IsSimpleGroup.toNontrivial : Nontrivial (X ⧸ Subgroup.center X))
  apply huv
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
  rw [hone u, hone v]

theorem map_center_k322 {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (Subgroup.center A).map e.toMonoidHom = Subgroup.center B := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_center_iff.2 fun g => by
      obtain ⟨g, rfl⟩ := e.surjective g
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx g]
  · intro hy
    refine ⟨e.symm y, Subgroup.mem_center_iff.2 fun g => ?_, by simp⟩
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, Subgroup.mem_center_iff.1 hy]

theorem isQuasisimple_of_mulEquiv_k322 {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hB : CFSG.Open.IsQuasisimple B) : CFSG.Open.IsQuasisimple A := by
  have hcen := map_center_k322 e
  refine ⟨?_, ?_⟩
  · have hmap : (commutator A).map e.toMonoidHom = ⊤ := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective, ← commutator_def]
      exact hB.1
    have := congrArg (Subgroup.comap e.toMonoidHom) hmap
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective, Subgroup.comap_top] at this
  · haveI := hB.2
    exact (QuotientGroup.congr _ _ e hcen).isSimpleGroup

theorem genFittingLayer_eq {G H : Subgroup (GL (Fin 3) (ZMod p))} (hHG : H ≤ G)
    (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hq : CFSG.Open.IsQuasisimple ↥H)
    (hirr : IsIrreducibleMatrixRep H.subtype) : genFittingLayer ↥G = H.subgroupOf G := by
  set H' : Subgroup ↥G := H.subgroupOf G with hH'
  haveI hH'n : H'.Normal := ⟨fun n hn g =>
    Subgroup.mem_subgroupOf.2 (hnorm g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  have hq' : CFSG.Open.IsQuasisimple ↥H' :=
    isQuasisimple_of_mulEquiv_k322 (Subgroup.subgroupOfEquivOfLe hHG) hq
  have hcomp : IsComponentOf H' ⊤ :=
    ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤), hq'⟩
  have hs : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p),
      (∀ g ∈ H, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * M = M * g) →
        ∃ c : ZMod p, M = Matrix.scalar (Fin 3) c := by
    rcases CFSG.RankThree.SubgroupLists.scalar_commutant_or_cyclic Nat.prime_three hirr with
      hs | ⟨hcyc, -⟩
    · exact hs
    · exfalso
      obtain ⟨a, b, hab⟩ := not_comm_of_isQuasisimple_k322 hq
      exact hab (hcyc.isMulCommutative.is_comm.comm a b)
  have hle : ∀ L : Subgroup ↥G, IsComponentOf L ⊤ → L = H' := by
    intro L hL
    by_contra hne
    have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne L H' hL hcomp hne
    have hsc : ∀ l ∈ L, ∃ c : ZMod p,
        ((l : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) =
          Matrix.scalar (Fin 3) c := by
      intro l hl
      apply hs
      intro g hg
      have hm := Subgroup.commutator_mem_commutator hl
        (show (⟨g, hHG hg⟩ : ↥G) ∈ H' from Subgroup.mem_subgroupOf.2 hg)
      rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      have h2 := congrArg (fun w : ↥G => ((w : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p))) hm
      simp only [Subgroup.coe_mul, Units.val_mul] at h2
      exact h2.symm
    obtain ⟨a, b, hab⟩ := not_comm_of_isQuasisimple_k322 hL.2.2
    apply hab
    obtain ⟨c₁, hc₁⟩ := hsc a a.2
    obtain ⟨c₂, hc₂⟩ := hsc b b.2
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, hc₁, hc₂]
    exact (scalar_commute c₁ (fun _ => Commute.all _ _) _).eq
  rw [genFittingLayer.eq_sSup]
  exact le_antisymm (sSup_le fun L hL => (hle L hL).le) (le_sSup hcomp)

theorem mem_translate_iff_inv {F : Type*} [Field F] {g : GL (Fin 3) F}
    {W : Submodule F (Fin 3 → F)} {u : Fin 3 → F} :
    u ∈ translate g W ↔ ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u ∈ W := by
  have h := K322Lin.mulVec_mem_translate_iff (g := g) (W := W)
    (v := ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ u)
  rwa [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec] at h

theorem monomial_conclusion (hp2 : p ≠ 2) {G : Subgroup (GL (Fin 3) (ZMod p))}
    (hmono : IsTransitiveMonomial G) {x : GL (Fin 3) (ZMod p)} (hxG : x ∈ G) (hx4 : x ^ 4 = 1)
    {Z : Submodule (ZMod p) (Fin 3 → ZMod p)} (hZ : Module.finrank (ZMod p) Z = 1)
    (hfix : {v : Fin 3 → ZMod p | ((x ^ 2 : GL (Fin 3) (ZMod p)) :
      Matrix (Fin 3) (Fin 3) (ZMod p)).mulVec v = v} = (Z : Set (Fin 3 → ZMod p))) :
    Set.ncard {W : Submodule (ZMod p) (Fin 3 → ZMod p) | ∃ g ∈ G,
        W = Z.map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod p)))} = 3 ∧
      ∃ W : Fin 3 → Submodule (ZMod p) (Fin 3 → ZMod p),
        (∀ i, Module.finrank (ZMod p) (W i) = 1) ∧ iSupIndep W ∧ (⨆ i, W i) = ⊤ ∧
          G ≤ normalizer ((cartanOfDecomp p W : Subgroup (GL (Fin 3) (ZMod p))) :
            Set (GL (Fin 3) (ZMod p))) := by
  classical
  obtain ⟨L, hL, hL1, hperm, htrans⟩ := hmono
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  obtain ⟨i₀, hZi⟩ := K322Lin.eq_line_of_monomial h2 hL hL1 hperm hxG hx4 hZ hfix
  have hinj := K322Lin.injective_of_isInternal hL hL1
  refine ⟨?_, L, hL1, hL.submodule_iSupIndep, hL.submodule_iSup_eq_top, fun g hg => ?_⟩
  · have hset : {W : Submodule (ZMod p) (Fin 3 → ZMod p) | ∃ g ∈ G,
        W = Z.map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) (ZMod p)))} = Set.range L := by
      ext W
      constructor
      · rintro ⟨g, hg, rfl⟩
        obtain ⟨j, hj⟩ := hperm g hg i₀
        exact ⟨j, by rw [← hj, hZi]; rfl⟩
      · rintro ⟨j, rfl⟩
        obtain ⟨g, hg, hgj⟩ := htrans i₀ j
        exact ⟨g, hg, by rw [hZi, ← hgj]; rfl⟩
    rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  ·
    have hsurj : ∀ j, ∃ k, translate g (L k) = L j := by
      intro j
      obtain ⟨k, hk⟩ := hperm g⁻¹ (G.inv_mem hg) j
      refine ⟨k, ?_⟩
      rw [← hk, ← CFSG.RankThree.SubgroupLists.translate_mul, mul_inv_cancel,
        CFSG.RankThree.SubgroupLists.translate_one]
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh i v
      obtain ⟨k, hk⟩ := hsurj i
      have hiff : ∀ u, u ∈ L i ↔ ((g⁻¹ : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ u ∈ L k := fun u => by
        rw [← hk, mem_translate_iff_inv]
      rw [hiff, hiff v]
      have : ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
          ((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v =
          (h : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
            (((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
        congr 2
        group
      rw [this]
      exact hh k _
    · intro hh i v
      obtain ⟨j, hj⟩ := hperm g hg i
      have hiff : ∀ u, u ∈ L i ↔ (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ u ∈ L j := fun u => by
        rw [← hj, K322Lin.mulVec_mem_translate_iff]
      rw [hiff, hiff v]
      have : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ (h : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v =
          ((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
            ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
        congr 2
        group
      rw [this]
      exact hh j _

end CFSG.LocalAnalysis.UniquenessCase.UC6.K322Rows
