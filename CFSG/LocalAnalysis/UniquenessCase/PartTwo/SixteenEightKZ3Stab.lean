module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3CheckA
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

private abbrev s16kV : Type := Multiplicative (Fin 6 → ZMod 2)

private def s16kMVec (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (v : Fin 6 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2 + M i 3 * v 3 + M i 4 * v 4 + M i 5 * v 5

private lemma s16kMVec_eq_mulVec (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) (v : Fin 6 → ZMod 2) :
    s16kMVec M v = M.mulVec v := by
  funext i
  rw [Matrix.mulVec_apply_eq_sum]
  simp [s16kMVec, Fin.sum_univ_six]

private def s16kMV (g : S16kGL6) : s16kV →* s16kV where
  toFun v := Multiplicative.ofAdd
    ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (Multiplicative.toAdd v))
  map_one' := by
    apply Multiplicative.ofAdd.injective
    funext k
    simp
  map_mul' := by
    intro a b
    apply Multiplicative.ofAdd.injective
    funext k
    simp [toAdd_mul, Matrix.mulVec_add]

private lemma s16kMV_eq_ofAdd_MVec (g : S16kGL6) (v : s16kV) :
    s16kMV g v = Multiplicative.ofAdd
      (s16kMVec (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) (Multiplicative.toAdd v)) := by
  rw [s16kMV, MonoidHom.coe_mk, OneHom.coe_mk, s16kMVec_eq_mulVec]

private lemma s16kMV_mul_apply (u v : S16kGL6) (x : s16kV) :
    s16kMV (u * v) x = s16kMV u (s16kMV v x) := by
  rw [s16kMV_eq_ofAdd_MVec, s16kMV_eq_ofAdd_MVec, s16kMV_eq_ofAdd_MVec]
  congr 1
  simp only [toAdd_ofAdd, s16kMVec_eq_mulVec, Units.val_mul, Matrix.mulVec_mulVec]

private lemma s16kMV_one_apply (x : s16kV) : s16kMV 1 x = x := by
  rw [s16kMV_eq_ofAdd_MVec]
  simp [s16kMVec_eq_mulVec]

private lemma s16kMV_injective (g : S16kGL6) : Function.Injective (s16kMV g) := by
  intro a b h
  have h1 : s16kMV g⁻¹ (s16kMV g a) = a := by
    rw [← s16kMV_mul_apply, inv_mul_cancel, s16kMV_one_apply]
  have h2 : s16kMV g⁻¹ (s16kMV g b) = b := by
    rw [← s16kMV_mul_apply, inv_mul_cancel, s16kMV_one_apply]
  have hh := congrArg (s16kMV g⁻¹) h
  rwa [h1, h2] at hh

private def s16kAdd3 (a b : Fin 3) : Fin 3 := ⟨(a.val + b.val) % 3, by omega⟩

private def s16kNeg3 (a : Fin 3) : Fin 3 := ⟨(3 - a.val) % 3, by omega⟩

private def s16kProdB (e : Fin 3 → Fin 3) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  s16kBlockMat 0 ^ (e 0).val * s16kBlockMat 1 ^ (e 1).val * s16kBlockMat 2 ^ (e 2).val

private def s16kProdU (e : Fin 3 → Fin 3) : S16kGL6 :=
  s16kDi 0 ^ (e 0).val * s16kDi 1 ^ (e 1).val * s16kDi 2 ^ (e 2).val

private lemma s16kProdU_val (e : Fin 3 → Fin 3) :
    (s16kProdU e : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kProdB e := by
  simp only [s16kProdU, s16kProdB, Units.val_mul, Units.val_pow_eq_pow_val, s16kDi_val]

private lemma s16kProdB_mul (e e' : Fin 3 → Fin 3) :
    s16kProdB e * s16kProdB e' = s16kProdB (fun i => s16kAdd3 (e i) (e' i)) := by
  revert e e'
  decide +kernel

private lemma s16kProdB_eq_one_iff (e : Fin 3 → Fin 3) :
    s16kProdB e = 1 ↔ ∀ i, e i = 0 := by
  revert e
  decide +kernel

private lemma s16kAdd3_neg (a : Fin 3) : s16kAdd3 a (s16kNeg3 a) = 0 := by
  revert a
  decide +kernel

private lemma s16kProdB_fixed :
    ∀ (e : Fin 3 → Fin 3) (v : Fin 6 → ZMod 2), s16kMVec (s16kProdB e) v = v →
      ∀ i : Fin 3, (e i).val ≠ 0 → s16kBlockZero v i := by
  decide +kernel

private lemma s16kProdB_preserves :
    ∀ (e : Fin 3 → Fin 3) (v : Fin 6 → ZMod 2) (i : Fin 3), s16kBlockZero v i →
      s16kBlockZero (s16kMVec (s16kProdB e) v) i := by
  decide +kernel

private lemma s16kProdU_mul (e e' : Fin 3 → Fin 3) :
    s16kProdU e * s16kProdU e' = s16kProdU (fun i => s16kAdd3 (e i) (e' i)) := by
  apply Units.ext
  rw [Units.val_mul, s16kProdU_val, s16kProdU_val, s16kProdU_val, s16kProdB_mul]

private lemma s16kProdU_eq_one_iff (e : Fin 3 → Fin 3) :
    s16kProdU e = 1 ↔ ∀ i, e i = 0 := by
  rw [← Units.val_eq_one, s16kProdU_val, s16kProdB_eq_one_iff]

private lemma s16kProdU_inv (e : Fin 3 → Fin 3) :
    (s16kProdU e)⁻¹ = s16kProdU (fun i => s16kNeg3 (e i)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [s16kProdU_mul]
  rw [show (fun i => s16kAdd3 (e i) (s16kNeg3 (e i))) = 0 by
    funext i
    exact s16kAdd3_neg (e i)]
  rw [s16kProdU_eq_one_iff]
  simp

private lemma s16kProdU_single (i : Fin 3) :
    s16kProdU (fun j => if j = i then 1 else 0) = s16kDi i := by
  apply Units.ext
  rw [s16kProdU_val]
  fin_cases i <;> decide +kernel

private lemma s16k_mem_diag_exists_prod (u : S16kGL6) (hu : u ∈ s16kDiag) :
    ∃ e : Fin 3 → Fin 3, u = s16kProdU e := by
  rw [s16kDiag_eq_closure_range] at hu
  induction hu using Subgroup.closure_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨fun j => if j = i then 1 else 0, (s16kProdU_single i).symm⟩
  | one => exact ⟨0, ((s16kProdU_eq_one_iff 0).mpr (by simp)).symm⟩
  | mul a b ha hb iha ihb =>
      obtain ⟨e, rfl⟩ := iha
      obtain ⟨e', rfl⟩ := ihb
      exact ⟨fun i => s16kAdd3 (e i) (e' i), s16kProdU_mul e e'⟩
  | inv a ha iha =>
      obtain ⟨e, rfl⟩ := iha
      exact ⟨fun i => s16kNeg3 (e i), s16kProdU_inv e⟩

private lemma s16kOmega_cubed : s16kOmega ^ 3 = 1 := by
  rw [← s16kOmega_orderOf]
  exact pow_orderOf_eq_one _

private lemma s16kOmega_cubed_mul : (s16kOmega * s16kOmega) * s16kOmega = 1 := by
  rw [← pow_two, ← pow_succ, s16kOmega_cubed]

private def s16kBlockV (i : Fin 3) (v : s16kV) : Fin 2 → ZMod 2 :=
  fun a => Multiplicative.toAdd v ⟨2 * i.val + a.val, by omega⟩

private def s16kBlockHom (i : Fin 3) : s16kV →* Multiplicative (Fin 2 → ZMod 2) where
  toFun v := Multiplicative.ofAdd (s16kBlockV i v)
  map_one' := by
    apply Multiplicative.ofAdd.injective
    rfl
  map_mul' := by
    intro x y
    apply Multiplicative.ofAdd.injective
    rfl

private def s16kPlane (i : Fin 3) : Subgroup s16kV := (s16kBlockHom i).ker

private lemma s16kPlane_mem (i : Fin 3) (v : s16kV) :
    v ∈ s16kPlane i ↔ s16kBlockZero (Multiplicative.toAdd v) i := by
  rw [s16kPlane, MonoidHom.mem_ker]
  constructor
  · intro h
    have h' : s16kBlockV i v = 0 := by
      have hc := congrArg Multiplicative.toAdd h
      simpa [s16kBlockHom] using hc
    exact ⟨by simpa [s16kBlockZero, s16kBlockV] using congrFun h' 0,
      by simpa [s16kBlockZero, s16kBlockV] using congrFun h' 1⟩
  · rintro ⟨h0, h1⟩
    show Multiplicative.ofAdd (s16kBlockV i v) = Multiplicative.ofAdd 0
    congr 1
    funext a
    fin_cases a
    · simpa [s16kBlockV] using h0
    · simpa [s16kBlockV] using h1

private lemma s16k_pair_mod (i : Fin 3) (a : Fin 2) :
    (⟨(2 * i.val + a.val) % 2, by omega⟩ : Fin 2) = a := by
  apply Fin.ext
  simp only [Fin.val_mk]
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a.isLt]

private lemma s16kBlockHom_surjective (i : Fin 3) : Function.Surjective (s16kBlockHom i) := by
  intro w
  refine ⟨Multiplicative.ofAdd (fun k : Fin 6 =>
    if k.val / 2 = i.val then Multiplicative.toAdd w ⟨k.val % 2, by omega⟩ else 0), ?_⟩
  apply Multiplicative.ofAdd.injective
  funext a
  show (if (2 * i.val + a.val) / 2 = i.val then
      Multiplicative.toAdd w ⟨(2 * i.val + a.val) % 2, by omega⟩ else 0) =
    Multiplicative.toAdd w a
  rw [if_pos (by omega : (2 * i.val + a.val) / 2 = i.val), s16k_pair_mod i a]

private lemma s16kCardV : Nat.card s16kV = 64 := by
  rw [← Nat.card_congr (Multiplicative.ofAdd : (Fin 6 → ZMod 2) ≃ s16kV)]
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_fun, ZMod.card]

private lemma s16kCardBlock : Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4 := by
  rw [← Nat.card_congr (Multiplicative.ofAdd : (Fin 2 → ZMod 2) ≃ _)]
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_fun, ZMod.card]

private lemma s16kPlane_card (i : Fin 3) : Nat.card (s16kPlane i) = 16 := by
  have h := Subgroup.card_ker_mul_card_of_surjective (s16kBlockHom_surjective i)
  rw [s16kCardBlock, s16kCardV] at h
  change Nat.card (s16kBlockHom i).ker * 4 = 64 at h
  change Nat.card (s16kBlockHom i).ker = 16
  omega

private lemma s16kOmegaMVec (v : Fin 6 → ZMod 2) :
    s16kMVec (s16kOmega : Matrix (Fin 6) (Fin 6) (ZMod 2)) v =
      s16kMVec (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) v := by
  rw [s16kMVec_eq_mulVec, s16kMVec_eq_mulVec, s16kOmega_val, s16kOmegaMat_eq_prod]

private lemma s16kBlockZero_omega :
    ∀ (i : Fin 3) (v : Fin 6 → ZMod 2), s16kBlockZero v i →
      s16kBlockZero (s16kMVec (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) v) i := by
  decide +kernel

private lemma s16kPlane_omega_invariant (i : Fin 3) :
    ∀ v ∈ s16kPlane i, s16kMV s16kOmega v ∈ s16kPlane i := by
  intro v hv
  rw [s16kPlane_mem] at hv ⊢
  have h : Multiplicative.toAdd (s16kMV s16kOmega v) =
      s16kMVec (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) (Multiplicative.toAdd v) := by
    rw [s16kMV_eq_ofAdd_MVec]
    simp only [toAdd_ofAdd]
    exact s16kOmegaMVec (Multiplicative.toAdd v)
  rw [h]
  exact s16kBlockZero_omega i (Multiplicative.toAdd v) hv

private lemma s16kOmega_fixed_eq_zero :
    ∀ v : Fin 6 → ZMod 2,
      s16kMVec (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) v = v → v = 0 := by
  decide +kernel

private lemma s16kOmega_fixed_eq_one (v : s16kV) : s16kMV s16kOmega v = v → v = 1 := by
  intro h
  have h' : s16kMVec (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2) (Multiplicative.toAdd v) =
      Multiplicative.toAdd v := by
    have hc := congrArg Multiplicative.toAdd h
    rw [s16kMV_eq_ofAdd_MVec] at hc
    simp only [toAdd_ofAdd] at hc
    rwa [s16kOmegaMVec] at hc
  exact Multiplicative.toAdd.injective (by simpa using s16kOmega_fixed_eq_zero _ h')

private def s16kNoZeroBlock (v : Fin 6 → ZMod 2) : Prop := ∀ i : Fin 3, ¬ s16kBlockZero v i

private lemma s16kF0_zeroBlock {v : Fin 6 → ZMod 2} (hv : v ∈ s16kF0) :
    ∃ i : Fin 3, s16kBlockZero v i := by
  obtain ⟨d, hd, hdne, hdv⟩ := s16kF0_mem hv
  obtain ⟨u, hu, hud⟩ := s16kDiagAll_exists_unit hd
  obtain ⟨e, rfl⟩ := s16k_mem_diag_exists_prod u hu
  have hue : s16kProdU e ≠ 1 := by
    intro h1
    apply hdne
    rw [← hud, h1]
    rfl
  have hex : ∃ i : Fin 3, e i ≠ 0 := by
    by_contra h
    have hall : ∀ i, e i = 0 := fun i => not_not.mp (not_exists.mp h i)
    exact hue ((s16kProdU_eq_one_iff e).mpr hall)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  have hfix : s16kMVec (s16kProdB e) v = v := by
    rw [s16kMVec_eq_mulVec, ← s16kProdU_val, hud]
    exact hdv
  exact s16kProdB_fixed e v hfix i (by simpa using hi)

private lemma s16kNoZeroBlock_mem_full {v : Fin 6 → ZMod 2} (hv : v ≠ 0)
    (hnz : s16kNoZeroBlock v) : v ∈ s16kFull := by
  have hAll : v ∈ s16kAllNonzero := s16kAllNonzero_mem.mpr hv
  rw [s16kAllNonzero_eq_union] at hAll
  rcases Finset.mem_union.mp hAll with h | h
  · exact absurd (s16kF0_zeroBlock h) (not_exists.mpr (fun i hi => hnz i hi))
  · exact h

private lemma s16kFull_noZeroBlock {v : Fin 6 → ZMod 2} (hv : v ∈ s16kFull) :
    s16kNoZeroBlock v := by
  intro i hi
  let w : Fin 6 → ZMod 2 := fun _ => 1
  have hwne : w ≠ 0 := by
    intro h
    exact (by decide : (1 : ZMod 2) ≠ 0) (congrFun h 0)
  have hwnz : s16kNoZeroBlock w := by
    intro j hj
    exact (by decide : (1 : ZMod 2) ≠ 0) hj.1
  have hwFull : w ∈ s16kFull := s16kNoZeroBlock_mem_full hwne hwnz
  obtain ⟨d1, hd1, hd1v⟩ := s16kFull_transitive v hv w hwFull
  obtain ⟨u1, hu1, hu1d⟩ := s16kDiagAll_exists_unit hd1
  obtain ⟨e, rfl⟩ := s16k_mem_diag_exists_prod u1 hu1
  have hblock : s16kBlockZero (s16kMVec (s16kProdB e) v) i := s16kProdB_preserves e v i hi
  have hw : s16kMVec (s16kProdB e) v = w := by
    rw [s16kMVec_eq_mulVec, ← s16kProdU_val, hu1d]
    exact hd1v
  exact hwnz i (hw ▸ hblock)

private lemma s16kF0_iff (v : Fin 6 → ZMod 2) :
    v ∈ s16kF0 ↔ v ≠ 0 ∧ ∃ i : Fin 3, s16kBlockZero v i := by
  constructor
  · intro hv
    exact ⟨s16kAllNonzero_mem.mp (s16kF0_subset_allNonzero hv), s16kF0_zeroBlock hv⟩
  · rintro ⟨hvne, ⟨i, hi⟩⟩
    have hAll : v ∈ s16kAllNonzero := s16kAllNonzero_mem.mpr hvne
    rw [s16kAllNonzero_eq_union] at hAll
    rcases Finset.mem_union.mp hAll with h | h
    · exact h
    · exact absurd hi (s16kFull_noZeroBlock h i)

private lemma s16k_card_omega_invariant (H : Subgroup s16kV)
    (hH : ∀ v ∈ H, s16kMV s16kOmega v ∈ H) : Nat.card H ≡ 1 [MOD 3] := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let f : Function.End H := fun x => ⟨s16kMV s16kOmega (x : s16kV), hH x x.2⟩
  have hf3 : f ^ 3 = 1 := by
    funext x
    apply Subtype.ext
    show s16kMV s16kOmega (s16kMV s16kOmega (s16kMV s16kOmega (x : s16kV))) = (x : s16kV)
    rw [← s16kMV_mul_apply, ← s16kMV_mul_apply, s16kOmega_cubed_mul, s16kMV_one_apply]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := H) (f := f) (p := 3) (n := 1) hf3
  have hfix : Fintype.card f.fixedPoints = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, ?_⟩, ?_⟩
    · apply Subtype.ext
      show s16kMV s16kOmega ((1 : H) : s16kV) = (1 : H)
      rw [show ((1 : H) : s16kV) = 1 from rfl, map_one]
    · rintro ⟨y, hy⟩
      apply Subtype.ext
      apply Subtype.ext
      exact s16kOmega_fixed_eq_one y (congrArg Subtype.val hy)
  rw [Nat.card_eq_fintype_card]
  exact hmod.trans (by rw [hfix])

private lemma s16k_card_le_four_of_lt {H Q : Subgroup s16kV} (hHQ : H ≤ Q)
    (hQ : Nat.card Q = 16) (hHinv : ∀ v ∈ H, s16kMV s16kOmega v ∈ H) (hne : H ≠ Q) :
    Nat.card H ≤ 4 := by
  have hmod := s16k_card_omega_invariant H hHinv
  have hdvd : Nat.card H ∣ 16 := hQ ▸ Subgroup.card_dvd_of_le hHQ
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hle : Nat.card H ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
  have hne16 : Nat.card H ≠ 16 := by
    intro h
    exact hne (Subgroup.eq_of_le_of_card_ge hHQ (by rw [hQ, h]))
  interval_cases Nat.card H <;> simp_all [Nat.ModEq]

private lemma s16k_sub_le_plane_of_union {Q : Subgroup s16kV} (hQ : Nat.card Q = 16)
    (hQinv : ∀ v ∈ Q, s16kMV s16kOmega v ∈ Q)
    (hsub : (Q : Set s16kV) ⊆ (s16kPlane 0 : Set s16kV) ∪ (s16kPlane 1 : Set s16kV) ∪
      (s16kPlane 2 : Set s16kV)) :
    Q ≤ s16kPlane 0 ∨ Q ≤ s16kPlane 1 ∨ Q ≤ s16kPlane 2 := by
  by_contra h
  have h0 : ¬ Q ≤ s16kPlane 0 := fun hh => h (Or.inl hh)
  have h1 : ¬ Q ≤ s16kPlane 1 := fun hh => h (Or.inr (Or.inl hh))
  have h2 : ¬ Q ≤ s16kPlane 2 := fun hh => h (Or.inr (Or.inr hh))
  have hne0 : Q ⊓ s16kPlane 0 ≠ Q := fun he => h0 (inf_eq_left.mp he)
  have hne1 : Q ⊓ s16kPlane 1 ≠ Q := fun he => h1 (inf_eq_left.mp he)
  have hne2 : Q ⊓ s16kPlane 2 ≠ Q := fun he => h2 (inf_eq_left.mp he)
  have hc0 : Nat.card (Q ⊓ s16kPlane 0 : Subgroup s16kV) ≤ 4 :=
    s16k_card_le_four_of_lt inf_le_left hQ
      (fun v hv => ⟨hQinv v hv.1, s16kPlane_omega_invariant 0 v hv.2⟩) hne0
  have hc1 : Nat.card (Q ⊓ s16kPlane 1 : Subgroup s16kV) ≤ 4 :=
    s16k_card_le_four_of_lt inf_le_left hQ
      (fun v hv => ⟨hQinv v hv.1, s16kPlane_omega_invariant 1 v hv.2⟩) hne1
  have hc2 : Nat.card (Q ⊓ s16kPlane 2 : Subgroup s16kV) ≤ 4 :=
    s16k_card_le_four_of_lt inf_le_left hQ
      (fun v hv => ⟨hQinv v hv.1, s16kPlane_omega_invariant 2 v hv.2⟩) hne2
  let A0 : Subgroup s16kV := Q ⊓ s16kPlane 0
  let A1 : Subgroup s16kV := Q ⊓ s16kPlane 1
  let A2 : Subgroup s16kV := Q ⊓ s16kPlane 2
  have hcA0 : Nat.card A0 ≤ 4 := hc0
  have hcA1 : Nat.card A1 ≤ 4 := hc1
  have hcA2 : Nat.card A2 ≤ 4 := hc2
  have hcover : (Q : Set s16kV) ⊆ (A0 : Set s16kV) ∪ (A1 : Set s16kV) ∪ (A2 : Set s16kV) := by
    intro v hv
    have hh : v ∈ s16kPlane 0 ∨ v ∈ s16kPlane 1 ∨ v ∈ s16kPlane 2 := by
      have h := hsub hv
      simp only [Set.mem_union] at h
      tauto
    rcases hh with hh | hh | hh
    · exact Or.inl (Or.inl ⟨hv, hh⟩)
    · exact Or.inl (Or.inr ⟨hv, hh⟩)
    · exact Or.inr ⟨hv, hh⟩
  have hQn : (Q : Set s16kV).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]
    exact hQ
  have hA0 : (A0 : Set s16kV).ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcA0
  have hA1 : (A1 : Set s16kV).ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcA1
  have hA2 : (A2 : Set s16kV).ncard ≤ 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcA2
  have h1 : (Q : Set s16kV).ncard ≤ (A0 ∪ A1 ∪ A2 : Set s16kV).ncard :=
    Set.ncard_le_ncard hcover
  have h2 : (A0 ∪ A1 ∪ A2 : Set s16kV).ncard ≤
      (A0 : Set s16kV).ncard + (A1 : Set s16kV).ncard + (A2 : Set s16kV).ncard := by
    have hh1 := Set.ncard_union_le (A0 ∪ A1 : Set s16kV) (A2 : Set s16kV)
    have hh2 := Set.ncard_union_le (A0 : Set s16kV) (A1 : Set s16kV)
    omega
  omega

private def s16kLineV (i : Fin 3) : Subgroup s16kV where
  carrier := {v | ∀ k : Fin 6, k.val / 2 ≠ i.val → Multiplicative.toAdd v k = 0}
  one_mem' := by
    intro k _
    rw [toAdd_one]
    rfl
  mul_mem' := by
    intro a b ha hb k hk
    rw [toAdd_mul, Pi.add_apply, ha k hk, hb k hk, add_zero]
  inv_mem' := by
    intro a ha k hk
    simp [ha k hk]

private lemma s16kLineV_mem (i : Fin 3) (v : s16kV) :
    v ∈ s16kLineV i ↔ ∀ k : Fin 6, k.val / 2 ≠ i.val → Multiplicative.toAdd v k = 0 :=
  Iff.rfl

private lemma s16kLineV_mem_iff :
    ∀ (i j k : Fin 3), j ≠ i → k ≠ i → j ≠ k → ∀ v : s16kV,
      (∀ l : Fin 6, l.val / 2 ≠ i.val → Multiplicative.toAdd v l = 0) ↔
        s16kBlockZero (Multiplicative.toAdd v) j ∧
          s16kBlockZero (Multiplicative.toAdd v) k := by
  decide +kernel

private lemma s16kLineV_eq_inf (i j k : Fin 3) (hji : j ≠ i) (hki : k ≠ i) (hjk : j ≠ k) :
    s16kLineV i = s16kPlane j ⊓ s16kPlane k := by
  ext v
  rw [s16kLineV_mem, Subgroup.mem_inf, s16kPlane_mem, s16kPlane_mem]
  exact s16kLineV_mem_iff i j k hji hki hjk v

private def s16kProjV (i : Fin 3) (v : s16kV) : s16kV :=
  Multiplicative.ofAdd fun k : Fin 6 =>
    if k.val / 2 = i.val then Multiplicative.toAdd v k else 0

private lemma s16kProjV_mem (i : Fin 3) (v : s16kV) : s16kProjV i v ∈ s16kLineV i := by
  intro k hk
  simp [s16kProjV, hk]

private lemma s16kProjV_prod (v : s16kV) :
    s16kProjV 0 v * s16kProjV 1 v * s16kProjV 2 v = v := by
  apply Multiplicative.ext
  funext k
  fin_cases k <;> simp [s16kProjV]

private lemma s16kLineV_iSup : (⨆ i, s16kLineV i) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro v
  rw [← s16kProjV_prod v]
  exact Subgroup.mul_mem (H := ⨆ i, s16kLineV i)
    (Subgroup.mul_mem (H := ⨆ i, s16kLineV i)
      (Subgroup.mem_iSup_of_mem 0 (s16kProjV_mem 0 v))
      (Subgroup.mem_iSup_of_mem 1 (s16kProjV_mem 1 v)))
    (Subgroup.mem_iSup_of_mem 2 (s16kProjV_mem 2 v))

private lemma s16kMV_di_apply (i : Fin 3) (x : s16kV) :
    s16kMV (s16kDi i) x = Multiplicative.ofAdd
      (s16kMVec (s16kBlockMat i) (Multiplicative.toAdd x)) := by
  rw [s16kMV_eq_ofAdd_MVec]
  simp only [toAdd_ofAdd, s16kDi_val]

private lemma s16kMV_omega_apply (x : s16kV) :
    s16kMV s16kOmega x = Multiplicative.ofAdd
      (s16kMVec (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2)
        (Multiplicative.toAdd x)) := by
  rw [s16kMV_eq_ofAdd_MVec]
  congr 1
  exact s16kOmegaMVec (Multiplicative.toAdd x)

private lemma s16kDi_agrees_omega :
    ∀ (i : Fin 3) (x : s16kV),
      (∀ l : Fin 6, l.val / 2 ≠ i.val → Multiplicative.toAdd x l = 0) →
      s16kMVec (s16kBlockMat i) (Multiplicative.toAdd x) =
        s16kMVec (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2)
          (Multiplicative.toAdd x) := by
  decide +kernel

private lemma s16kDi_trivial :
    ∀ (i j : Fin 3), i ≠ j → ∀ x : s16kV,
      (∀ l : Fin 6, l.val / 2 ≠ i.val → Multiplicative.toAdd x l = 0) →
      s16kMVec (s16kBlockMat j) (Multiplicative.toAdd x) = Multiplicative.toAdd x := by
  decide +kernel

private def s16kEqSub (u v : S16kGL6) : Subgroup s16kV where
  carrier := {x | s16kMV u x = s16kMV v x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, map_mul, ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, map_inv, ha]

private lemma s16k_eq_of_eq_on_lines {u v : S16kGL6}
    (h : ∀ i : Fin 3, ∀ x ∈ s16kLineV i, s16kMV u x = s16kMV v x) : u = v := by
  have hle : (⨆ i, s16kLineV i) ≤ s16kEqSub u v :=
    iSup_le fun i => fun x hx => h i x hx
  have hall : ∀ x : s16kV, s16kMV u x = s16kMV v x := by
    intro x
    have hx : x ∈ (⨆ i, s16kLineV i) := by rw [s16kLineV_iSup]; trivial
    exact hle hx
  apply Units.ext
  ext r c
  have hb := congrFun (congrArg Multiplicative.toAdd
    (hall (Multiplicative.ofAdd (Pi.single c 1)))) r
  simp only [s16kMV_eq_ofAdd_MVec, toAdd_ofAdd] at hb
  rw [s16kMVec_eq_mulVec, s16kMVec_eq_mulVec] at hb
  simpa [Matrix.mulVec_single_one, Matrix.col_apply] using hb
private def s16kOther1 (i : Fin 3) : Fin 3 := ⟨(i.val + 1) % 3, by omega⟩

private def s16kOther2 (i : Fin 3) : Fin 3 := ⟨(i.val + 2) % 3, by omega⟩

private lemma s16kOther1_ne (i : Fin 3) : s16kOther1 i ≠ i := by
  revert i; decide +kernel

private lemma s16kOther2_ne (i : Fin 3) : s16kOther2 i ≠ i := by
  revert i; decide +kernel

private lemma s16kOther_ne (i : Fin 3) : s16kOther1 i ≠ s16kOther2 i := by
  revert i; decide +kernel

private lemma s16k_other_cases (i m : Fin 3) (hm : m ≠ i) :
    m = s16kOther1 i ∨ m = s16kOther2 i := by
  revert i m; decide +kernel

private lemma s16kLineV_eq_inf_other (i : Fin 3) :
    s16kLineV i = s16kPlane (s16kOther1 i) ⊓ s16kPlane (s16kOther2 i) :=
  s16kLineV_eq_inf i (s16kOther1 i) (s16kOther2 i) (s16kOther1_ne i) (s16kOther2_ne i)
    (s16kOther_ne i)

private lemma s16kOmega_mem_line_aux :
    ∀ (i : Fin 3) (x : s16kV),
      (∀ l : Fin 6, l.val / 2 ≠ i.val → Multiplicative.toAdd x l = 0) →
      (∀ l : Fin 6, l.val / 2 ≠ i.val →
        s16kMVec (s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2)
          (Multiplicative.toAdd x) l = 0) := by
  decide +kernel

private lemma s16kOmega_mem_line {i : Fin 3} {x : s16kV} (hx : x ∈ s16kLineV i) :
    s16kMV s16kOmega x ∈ s16kLineV i := by
  rw [s16kLineV_mem] at hx ⊢
  rw [s16kMV_omega_apply]
  exact s16kOmega_mem_line_aux i x hx

private lemma s16kMV_di_eq_omega {i : Fin 3} {x : s16kV} (hx : x ∈ s16kLineV i) :
    s16kMV (s16kDi i) x = s16kMV s16kOmega x := by
  rw [s16kMV_di_apply, s16kMV_omega_apply]
  congr 1
  exact s16kDi_agrees_omega i x ((s16kLineV_mem i x).mp hx)

private lemma s16kMV_di_eq_self {i j : Fin 3} (hij : i ≠ j) {x : s16kV}
    (hx : x ∈ s16kLineV i) : s16kMV (s16kDi j) x = x := by
  rw [s16kMV_di_apply]
  have h := s16kDi_trivial i j hij x ((s16kLineV_mem i x).mp hx)
  rw [h]
  rfl

private lemma s16kMV_di_sq_eq_omega_sq {i : Fin 3} {x : s16kV} (hx : x ∈ s16kLineV i) :
    s16kMV ((s16kDi i) ^ 2) x = s16kMV (s16kOmega ^ 2) x := by
  have hx1 : s16kMV s16kOmega x ∈ s16kLineV i := s16kOmega_mem_line hx
  calc s16kMV ((s16kDi i) ^ 2) x
      = s16kMV (s16kDi i) (s16kMV (s16kDi i) x) := by rw [sq, s16kMV_mul_apply]
    _ = s16kMV (s16kDi i) (s16kMV s16kOmega x) :=
          congrArg (s16kMV (s16kDi i)) (s16kMV_di_eq_omega hx)
    _ = s16kMV s16kOmega (s16kMV s16kOmega x) := s16kMV_di_eq_omega hx1
    _ = s16kMV (s16kOmega ^ 2) x := by rw [sq, s16kMV_mul_apply]

private lemma s16kMV_di_sq_eq_self {i j : Fin 3} (hij : i ≠ j) {x : s16kV}
    (hx : x ∈ s16kLineV i) : s16kMV ((s16kDi j) ^ 2) x = x := by
  have hx1 : s16kMV (s16kDi j) x ∈ s16kLineV i := by
    rw [s16kMV_di_eq_self hij hx]
    exact hx
  calc s16kMV ((s16kDi j) ^ 2) x
      = s16kMV (s16kDi j) (s16kMV (s16kDi j) x) := by rw [sq, s16kMV_mul_apply]
    _ = s16kMV (s16kDi j) x := congrArg (s16kMV (s16kDi j)) (s16kMV_di_eq_self hij hx)
    _ = x := s16kMV_di_eq_self hij hx

private lemma s16k_plane_inf_map {π : Fin 3 → Fin 3} (hπinj : Function.Injective π) (i : Fin 3) :
    s16kPlane (π (s16kOther1 i)) ⊓ s16kPlane (π (s16kOther2 i)) =
      s16kPlane (s16kOther1 (π i)) ⊓ s16kPlane (s16kOther2 (π i)) := by
  have h1 : π (s16kOther1 i) ≠ π i := fun h => s16kOther1_ne i (hπinj h)
  have h2 : π (s16kOther2 i) ≠ π i := fun h => s16kOther2_ne i (hπinj h)
  have h12 : π (s16kOther1 i) ≠ π (s16kOther2 i) :=
    fun h => s16kOther_ne i (hπinj h)
  rcases s16k_other_cases (π i) (π (s16kOther1 i)) h1 with e1 | e1 <;>
    rcases s16k_other_cases (π i) (π (s16kOther2 i)) h2 with e2 | e2
  · exact absurd (e1.trans e2.symm) h12
  · rw [e1, e2]
  · rw [e1, e2, inf_comm]
  · exact absurd (e1.trans e2.symm) h12

private lemma s16kLineV_map {g : S16kGL6} {π : Fin 3 → Fin 3} (hπinj : Function.Injective π)
    (hπ : ∀ i, (s16kPlane i).map (s16kMV g) = s16kPlane (π i)) (i : Fin 3) :
    (s16kLineV i).map (s16kMV g) = s16kLineV (π i) := by
  rw [s16kLineV_eq_inf_other i, Subgroup.map_inf _ _ _ (s16kMV_injective g), hπ, hπ,
    s16kLineV_eq_inf_other (π i), s16k_plane_inf_map hπinj i]

private lemma s16kPlane_ne_aux :
    ∀ i j : Fin 3, i ≠ j →
      s16kBlockZero (Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) 1) j ∧
        ¬ s16kBlockZero (Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) 1) i := by
  decide +kernel

private lemma s16kPlane_injective : Function.Injective s16kPlane := by
  intro i j hij
  by_contra hne
  obtain ⟨hvj, hvi⟩ := s16kPlane_ne_aux i j hne
  have hvj' : Multiplicative.ofAdd
      (Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) 1) ∈ s16kPlane j :=
    (s16kPlane_mem j _).mpr hvj
  have hvi' : Multiplicative.ofAdd
      (Pi.single (⟨2 * i.val, by omega⟩ : Fin 6) 1) ∉ s16kPlane i :=
    fun h => hvi ((s16kPlane_mem i _).mp h)
  rw [← hij] at hvj'
  exact hvi' hvj'

private lemma s16k_conj_omega_inv {g : S16kGL6}
    (hg : g ∈ Subgroup.normalizer (s16kScal : Set S16kGL6)) :
    g⁻¹ * s16kOmega * g = s16kOmega ∨ g⁻¹ * s16kOmega * g = s16kOmega ^ 2 := by
  have hginv : g⁻¹ ∈ Subgroup.normalizer (s16kScal : Set S16kGL6) :=
    (Subgroup.normalizer (s16kScal : Set S16kGL6)).inv_mem hg
  have hmem : g⁻¹ * s16kOmega * g ∈ Subgroup.zpowers s16kOmega := by
    rw [← s16kScal_eq_zpowers]
    exact (Subgroup.mem_normalizer_iff.mp hginv s16kOmega).mp
      (s16kScal_eq_zpowers.symm ▸ Subgroup.mem_zpowers s16kOmega)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hd1 : g⁻¹ * s16kOmega * g ≠ 1 := by
    intro h1
    have : s16kOmega = 1 := by
      calc s16kOmega = g * (g⁻¹ * s16kOmega * g) * g⁻¹ := by group
        _ = g * 1 * g⁻¹ := by rw [h1]
        _ = 1 := by group
    exact s16kOmega_ne_one this
  rw [← zpow_mod_orderOf, s16kOmega_orderOf] at hn
  simp only [Nat.cast_ofNat] at hn
  have hlt : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  have hnn : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h0 | h0 | h0
  · exfalso
    exact hd1 (by rw [← hn, h0, zpow_zero])
  · left
    rw [← hn, h0]
    simp
  · right
    rw [← hn, h0]
    simp

private lemma s16k_stab_image_sub {g : S16kGL6}
    (hg : g ∈ Subgroup.normalizer (s16kScal : Set S16kGL6))
    (hF : ∀ f ∈ s16kF0, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec f ∈ s16kF0)
    (i : Fin 3) :
    ((s16kPlane i).map (s16kMV g) : Set s16kV) ⊆
      (s16kPlane 0 : Set s16kV) ∪ (s16kPlane 1 : Set s16kV) ∪
        (s16kPlane 2 : Set s16kV) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
  by_cases hu1 : u = 1
  · subst hu1
    rw [map_one]
    exact Or.inl (Or.inl (s16kPlane 0).one_mem)
  · have huF0 : Multiplicative.toAdd u ∈ s16kF0 := by
      rw [s16kF0_iff]
      refine ⟨?_, ⟨i, (s16kPlane_mem i u).mp hu⟩⟩
      intro h0
      exact hu1 (Multiplicative.toAdd.injective (by simpa using h0))
    have hgF0 : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (Multiplicative.toAdd u) ∈
        s16kF0 := hF _ huF0
    obtain ⟨j, hj⟩ := ((s16kF0_iff _).mp hgF0).2
    have hmem : s16kMV g u ∈ s16kPlane j := by
      rw [s16kPlane_mem]
      have htu : Multiplicative.toAdd (s16kMV g u) =
          (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec (Multiplicative.toAdd u) := by
        rw [s16kMV_eq_ofAdd_MVec]
        simp only [toAdd_ofAdd]
        exact s16kMVec_eq_mulVec _ _
      rw [htu]
      exact hj
    fin_cases j
    · exact Or.inl (Or.inl hmem)
    · exact Or.inl (Or.inr hmem)
    · exact Or.inr hmem

private lemma s16k_stab_perm {g : S16kGL6}
    (hg : g ∈ Subgroup.normalizer (s16kScal : Set S16kGL6))
    (hF : ∀ f ∈ s16kF0, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec f ∈ s16kF0) :
    ∃ pi : Fin 3 → Fin 3, Function.Injective pi ∧
      ∀ i : Fin 3, (s16kPlane i).map (s16kMV g) = s16kPlane (pi i) := by
  classical
  have hconj_inv := s16k_conj_omega_inv hg
  have hex : ∀ i : Fin 3, ∃ j : Fin 3,
      (s16kPlane i).map (s16kMV g) = s16kPlane j := by
    intro i
    have hQcard : Nat.card ((s16kPlane i).map (s16kMV g)) = 16 := by
      rw [Subgroup.card_map_of_injective (s16kMV_injective g), s16kPlane_card]
    have hQinv : ∀ v ∈ (s16kPlane i).map (s16kMV g),
        s16kMV s16kOmega v ∈ (s16kPlane i).map (s16kMV g) := by
      intro v hv
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
      refine Subgroup.mem_map.mpr ⟨s16kMV (g⁻¹ * s16kOmega * g) u, ?_, ?_⟩
      · rcases hconj_inv with hh | hh
        · rw [hh]
          exact s16kPlane_omega_invariant i u hu
        · rw [hh, sq, s16kMV_mul_apply]
          exact s16kPlane_omega_invariant i _ (s16kPlane_omega_invariant i u hu)
      · calc s16kMV g (s16kMV (g⁻¹ * s16kOmega * g) u)
            = s16kMV (g * (g⁻¹ * s16kOmega * g)) u :=
                (s16kMV_mul_apply g (g⁻¹ * s16kOmega * g) u).symm
          _ = s16kMV (s16kOmega * g) u := by
                rw [show g * (g⁻¹ * s16kOmega * g) = s16kOmega * g from by group]
          _ = s16kMV s16kOmega (s16kMV g u) := s16kMV_mul_apply s16kOmega g u
    rcases s16k_sub_le_plane_of_union hQcard hQinv (s16k_stab_image_sub hg hF i) with h | h | h
    · exact ⟨0, Subgroup.eq_of_le_of_card_ge h (by rw [hQcard, s16kPlane_card])⟩
    · exact ⟨1, Subgroup.eq_of_le_of_card_ge h (by rw [hQcard, s16kPlane_card])⟩
    · exact ⟨2, Subgroup.eq_of_le_of_card_ge h (by rw [hQcard, s16kPlane_card])⟩
  let pi : Fin 3 → Fin 3 := fun i => Classical.choose (hex i)
  have hpi_spec : ∀ i : Fin 3, (s16kPlane i).map (s16kMV g) = s16kPlane (pi i) :=
    fun i => Classical.choose_spec (hex i)
  refine ⟨pi, ?_, hpi_spec⟩
  intro i i' hii
  have hmap : (s16kPlane i).map (s16kMV g) = (s16kPlane i').map (s16kMV g) := by
    rw [hpi_spec i, hpi_spec i', hii]
  exact s16kPlane_injective ((Subgroup.map_injective (s16kMV_injective g)) hmap)

private lemma s16k_stab_line {g : S16kGL6} {pi : Fin 3 → Fin 3}
    (hpi : Function.Injective pi)
    (hπ : ∀ i : Fin 3, (s16kPlane i).map (s16kMV g) = s16kPlane (pi i)) (i : Fin 3) :
    (s16kLineV i).map (s16kMV g) = s16kLineV (pi i) :=
  s16kLineV_map hpi hπ i

private lemma s16k_stab_conj_gen_omega {g : S16kGL6} {pi : Fin 3 → Fin 3}
    (hpi : Function.Injective pi)
    (hline : ∀ i : Fin 3, (s16kLineV i).map (s16kMV g) = s16kLineV (pi i))
    (hcase : g * s16kOmega * g⁻¹ = s16kOmega) (i : Fin 3) :
    g * s16kDi i * g⁻¹ = s16kDi (pi i) := by
  apply s16k_eq_of_eq_on_lines
  intro l x hx
  by_cases hl : l = pi i
  · subst hl
    have hx' : x ∈ (s16kLineV i).map (s16kMV g) := by rw [hline i]; exact hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
    have hgy : s16kMV g⁻¹ (s16kMV g y) = y := by
      rw [← s16kMV_mul_apply, inv_mul_cancel, s16kMV_one_apply]
    have hgw : g * s16kOmega = s16kOmega * g := by
      calc g * s16kOmega = (g * s16kOmega * g⁻¹) * g := by group
        _ = s16kOmega * g := by rw [hcase]
    calc s16kMV (g * s16kDi i * g⁻¹) (s16kMV g y)
        = s16kMV (g * s16kDi i) (s16kMV g⁻¹ (s16kMV g y)) := by rw [s16kMV_mul_apply]
      _ = s16kMV (g * s16kDi i) y := by rw [hgy]
      _ = s16kMV g (s16kMV (s16kDi i) y) := by rw [s16kMV_mul_apply]
      _ = s16kMV g (s16kMV s16kOmega y) := by rw [s16kMV_di_eq_omega hy]
      _ = s16kMV (g * s16kOmega) y := by rw [s16kMV_mul_apply]
      _ = s16kMV (s16kOmega * g) y := by rw [hgw]
      _ = s16kMV s16kOmega (s16kMV g y) := by rw [s16kMV_mul_apply]
      _ = s16kMV (s16kDi (pi i)) (s16kMV g y) := (s16kMV_di_eq_omega hx).symm
  · obtain ⟨j, rfl⟩ := (Finite.injective_iff_surjective (f := pi)).mp hpi l
    have hji : i ≠ j := fun h => hl (by rw [h])
    have hx' : x ∈ (s16kLineV j).map (s16kMV g) := by rw [hline j]; exact hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
    have hxπ : s16kMV g y ∈ s16kLineV (pi j) := by
      rw [← hline j]; exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hgy : s16kMV g⁻¹ (s16kMV g y) = y := by
      rw [← s16kMV_mul_apply, inv_mul_cancel, s16kMV_one_apply]
    calc s16kMV (g * s16kDi i * g⁻¹) (s16kMV g y)
        = s16kMV (g * s16kDi i) (s16kMV g⁻¹ (s16kMV g y)) := by rw [s16kMV_mul_apply]
      _ = s16kMV (g * s16kDi i) y := by rw [hgy]
      _ = s16kMV g (s16kMV (s16kDi i) y) := by rw [s16kMV_mul_apply]
      _ = s16kMV g y := by rw [s16kMV_di_eq_self (Ne.symm hji) hy]
      _ = s16kMV (s16kDi (pi i)) (s16kMV g y) := (s16kMV_di_eq_self hl hxπ).symm

private lemma s16k_stab_conj_gen_omega_sq {g : S16kGL6} {pi : Fin 3 → Fin 3}
    (hpi : Function.Injective pi)
    (hline : ∀ i : Fin 3, (s16kLineV i).map (s16kMV g) = s16kLineV (pi i))
    (hcase : g * s16kOmega * g⁻¹ = s16kOmega ^ 2) (i : Fin 3) :
    g * s16kDi i * g⁻¹ = (s16kDi (pi i)) ^ 2 := by
  apply s16k_eq_of_eq_on_lines
  intro l x hx
  by_cases hl : l = pi i
  · subst hl
    have hx' : x ∈ (s16kLineV i).map (s16kMV g) := by rw [hline i]; exact hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
    have hgy : s16kMV g⁻¹ (s16kMV g y) = y := by
      rw [← s16kMV_mul_apply, inv_mul_cancel, s16kMV_one_apply]
    have hgw : g * s16kOmega = (s16kOmega * s16kOmega) * g := by
      calc g * s16kOmega = (g * s16kOmega * g⁻¹) * g := by group
        _ = (s16kOmega ^ 2) * g := by rw [hcase]
        _ = (s16kOmega * s16kOmega) * g := by rw [sq]
    calc s16kMV (g * s16kDi i * g⁻¹) (s16kMV g y)
        = s16kMV (g * s16kDi i) (s16kMV g⁻¹ (s16kMV g y)) := by rw [s16kMV_mul_apply]
      _ = s16kMV (g * s16kDi i) y := by rw [hgy]
      _ = s16kMV g (s16kMV (s16kDi i) y) := by rw [s16kMV_mul_apply]
      _ = s16kMV g (s16kMV s16kOmega y) := by rw [s16kMV_di_eq_omega hy]
      _ = s16kMV (g * s16kOmega) y := by rw [s16kMV_mul_apply]
      _ = s16kMV ((s16kOmega * s16kOmega) * g) y := by rw [hgw]
      _ = s16kMV (s16kOmega * s16kOmega) (s16kMV g y) := by rw [s16kMV_mul_apply]
      _ = s16kMV ((s16kDi (pi i)) ^ 2) (s16kMV g y) := by
            rw [← sq]
            exact (s16kMV_di_sq_eq_omega_sq hx).symm
  · obtain ⟨j, rfl⟩ := (Finite.injective_iff_surjective (f := pi)).mp hpi l
    have hji : i ≠ j := fun h => hl (by rw [h])
    have hx' : x ∈ (s16kLineV j).map (s16kMV g) := by rw [hline j]; exact hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx'
    have hxπ : s16kMV g y ∈ s16kLineV (pi j) := by
      rw [← hline j]; exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hgy : s16kMV g⁻¹ (s16kMV g y) = y := by
      rw [← s16kMV_mul_apply, inv_mul_cancel, s16kMV_one_apply]
    calc s16kMV (g * s16kDi i * g⁻¹) (s16kMV g y)
        = s16kMV (g * s16kDi i) (s16kMV g⁻¹ (s16kMV g y)) := by rw [s16kMV_mul_apply]
      _ = s16kMV (g * s16kDi i) y := by rw [hgy]
      _ = s16kMV g (s16kMV (s16kDi i) y) := by rw [s16kMV_mul_apply]
      _ = s16kMV g y := by rw [s16kMV_di_eq_self (Ne.symm hji) hy]
      _ = s16kMV ((s16kDi (pi i)) ^ 2) (s16kMV g y) :=
            (s16kMV_di_sq_eq_self hl hxπ).symm

theorem s16k_z3_stab_F0 {g : S16kGL6}
    (hg : g ∈ Subgroup.normalizer (s16kScal : Set S16kGL6))
    (hF : ∀ f ∈ s16kF0, (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec f ∈ s16kF0) :
    g ∈ Subgroup.normalizer (s16kDiag : Set S16kGL6) := by
  obtain ⟨pi, hpi, hπ⟩ := s16k_stab_perm hg hF
  have hline : ∀ i : Fin 3, (s16kLineV i).map (s16kMV g) = s16kLineV (pi i) :=
    fun i => s16k_stab_line hpi hπ i
  have hginv : g⁻¹ ∈ Subgroup.normalizer (s16kScal : Set S16kGL6) :=
    (Subgroup.normalizer (s16kScal : Set S16kGL6)).inv_mem hg
  rw [s16k_mem_normalizer_diag_iff]
  intro i
  rcases s16k_conj_omega_inv hginv with hcase | hcase
  · rw [s16k_stab_conj_gen_omega hpi hline hcase i]
    exact s16kDi_mem (pi i)
  · rw [s16k_stab_conj_gen_omega_sq hpi hline hcase i]
    exact Subgroup.pow_mem _ (s16kDi_mem (pi i)) 2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
