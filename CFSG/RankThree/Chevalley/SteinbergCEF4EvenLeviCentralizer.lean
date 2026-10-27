module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenCenter
public import CFSG.LieType.Chevalley.TrialityCoverTorus

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Lattice
open scoped Pointwise

namespace NativeLevi

variable {τ : Tag} {M : Type} [Field M]

variable (τ M) in
@[expose] def standardLevi (J : Set (Fin τ.rank)) : Subgroup (ModGL τ M) :=
  torusGroup τ M ⊔ subsystemGroup τ M J

variable (τ M) in
@[expose] def simpleCharKernel (J : Set (Fin τ.rank)) : Subgroup (ModGL τ M) where
  carrier := {h | h ∈ torusGroup τ M ∧ ∀ j ∈ J, torusRootChar h (Pi.single j 1) = 1}
  one_mem' := ⟨one_mem _, fun _ _ => torusRootChar_one _⟩
  mul_mem' {a b} ha hb := ⟨mul_mem ha.1 hb.1, fun j hj => by
    rw [torusRootChar_mul (torusGroup_le_diagonalGroup ha.1) (torusGroup_le_diagonalGroup hb.1),
      ha.2 j hj, hb.2 j hj, one_mul]⟩
  inv_mem' {a} ha := ⟨inv_mem ha.1, fun j hj => by
    rw [torusRootChar_inv (torusGroup_le_diagonalGroup ha.1), ha.2 j hj, inv_one]⟩

theorem mem_simpleCharKernel {J : Set (Fin τ.rank)} {h : ModGL τ M} :
    h ∈ simpleCharKernel τ M J ↔
      h ∈ torusGroup τ M ∧ ∀ j ∈ J, torusRootChar h (Pi.single j 1) = 1 :=
  Iff.rfl

theorem torusGroup_le_standardLevi (J : Set (Fin τ.rank)) :
    torusGroup τ M ≤ standardLevi τ M J :=
  le_sup_left

theorem subsystemGroup_le_standardLevi (J : Set (Fin τ.rank)) :
    subsystemGroup τ M J ≤ standardLevi τ M J :=
  le_sup_right

theorem torusRootChar_neg {h : ModGL τ M} (hh : h ∈ torusGroup τ M) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) : torusRootChar h (-α) = (torusRootChar h α)⁻¹ := by
  rw [torusGroup] at hh
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, t⟩, rfl⟩ := hx
    rw [torusRootChar_torusElt i t (IsRoot.neg hα), torusRootChar_torusElt i t hα]
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, zpow_neg, Units.val_inv_eq_inv_val]
  | one => rw [torusRootChar_one, torusRootChar_one, inv_one]
  | mul x y hx hy ihx ihy =>
    rw [torusRootChar_mul (torusGroup_le_diagonalGroup hx) (torusGroup_le_diagonalGroup hy),
      torusRootChar_mul (torusGroup_le_diagonalGroup hx) (torusGroup_le_diagonalGroup hy), ihx,
      ihy, mul_inv]
  | inv x hx ihx =>
    rw [torusRootChar_inv (torusGroup_le_diagonalGroup hx),
      torusRootChar_inv (torusGroup_le_diagonalGroup hx), ihx]

theorem subsystemGroup_le_centralizer_of_mem {J : Set (Fin τ.rank)} {h : ModGL τ M}
    (hh : h ∈ simpleCharKernel τ M J) : subsystemGroup τ M J ≤ Subgroup.centralizer {h} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_single]
    exact ((commute_pinnedX_iff hh.1 (isRoot_single τ j)).2 (hh.2 j hj) c).symm
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff, ← pinnedX_neg_single]
    refine ((commute_pinnedX_iff hh.1 (isRoot_neg_single τ j)).2 ?_ c).symm
    rw [torusRootChar_neg hh.1 (isRoot_single τ j), hh.2 j hj, inv_one]

theorem torusGroup_le_normalizer_subsystemGroup
    (J : Set (Fin τ.rank)) :
    torusGroup τ M ≤ Subgroup.normalizer (subsystemGroup τ M J : Set (ModGL τ M)) := by
  rw [subsystemGroup_eq_rootSpan]
  exact torusGroup_le_normalizer_rootSpan fun _ hα => hα.1

theorem coe_standardLevi
    (J : Set (Fin τ.rank)) :
    (standardLevi τ M J : Set (ModGL τ M)) =
      (torusGroup τ M : Set (ModGL τ M)) * (subsystemGroup τ M J : Set (ModGL τ M)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torusGroup_le_normalizer_subsystemGroup J)

theorem standardLevi_inf_centralizer
    (J : Set (Fin τ.rank)) :
    standardLevi τ M J ⊓ Subgroup.centralizer (subsystemGroup τ M J : Set (ModGL τ M)) =
      simpleCharKernel τ M J := by
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hyL, hyC⟩
    rw [← SetLike.mem_coe, coe_standardLevi] at hyL
    obtain ⟨h, hh, z, hz, rfl⟩ := hyL
    have hH : h * z ∈ torusGroup τ M :=
      mem_torusGroup_of_commute_subsystemGroup hh hz fun x hx => (hyC x hx).symm
    refine ⟨hH, fun j hj => (commute_pinnedX_iff hH (isRoot_single τ j)).1 fun c => ?_⟩
    rw [pinnedX_single]
    exact (hyC _ (xUnit_mem_subsystemGroup hj c)).symm
  · intro hy
    exact ⟨torusGroup_le_standardLevi J hy.1, fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.1 (subsystemGroup_le_centralizer_of_mem hy hx)⟩

theorem standardLevi_le_centralizer_of_mem {J : Set (Fin τ.rank)} {h : ModGL τ M}
    (hh : h ∈ simpleCharKernel τ M J) : standardLevi τ M J ≤ Subgroup.centralizer {h} :=
  sup_le (fun _ ht => Subgroup.mem_centralizer_singleton_iff.2
      (mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup ht)
        (torusGroup_le_diagonalGroup hh.1)))
    (subsystemGroup_le_centralizer_of_mem hh)

theorem map_center_standardLevi
    (J : Set (Fin τ.rank)) :
    (Subgroup.center (standardLevi τ M J)).map (standardLevi τ M J).subtype =
      simpleCharKernel τ M J := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← standardLevi_inf_centralizer]
    refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.1 hz ⟨x, subsystemGroup_le_standardLevi J hx⟩)
  · intro hy
    exact ⟨⟨y, torusGroup_le_standardLevi J hy.1⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1
        (standardLevi_le_centralizer_of_mem hy g.2)), rfl⟩

section Interpolation

variable {Ω : Type} [Field Ω] {R : Type*} [Ring R] [Algebra Ω R]

theorem commute_of_forall_sum_pow_smul {X : R} {d : ℕ} {A : ℕ → R} {F : Finset Ω}
    (hF : d < F.card) (h : ∀ c ∈ F, Commute X (∑ k ∈ Finset.range (d + 1), c ^ k • A k))
    {k : ℕ} (hk : k ≤ d) : Commute X (A k) := by
  have key := eq_zero_of_forall_sum_pow_smul (ι := Fin (d + 1)) (n := fun i => (i : ℕ))
    Fin.val_injective (F := F) (fun i => by have := i.2; omega)
    (c := fun i => X * A i - A i * X) (fun c hc => by
      have e := (h c hc).eq
      have e' : ∑ k ∈ Finset.range (d + 1), c ^ k • (X * A k - A k * X) = 0 := by
        rw [← sub_eq_zero, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib] at e
        rw [← e]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_smul_comm, smul_mul_assoc, smul_sub]
      rw [Finset.sum_range] at e'
      exact e')
    ⟨k, Nat.lt_succ_of_le hk⟩
  exact sub_eq_zero.1 key

end Interpolation

theorem commute_xOp_yOp_of_four_le_card {X : Module.End M (RootModule τ M)} {j : Fin τ.rank}
    {F : Finset M} (hF : 4 ≤ F.card) (hx : ∀ c ∈ F, Commute X (xOp τ M j c))
    (hy : ∀ c ∈ F, Commute X (yOp τ M j c)) (c : M) :
    Commute X (xOp τ M j c) ∧ Commute X (yOp τ M j c) := by
  have hd : entryDegreeBound τ < F.card := by
    have : entryDegreeBound τ ≤ 3 := by
      unfold entryDegreeBound
      split_ifs <;> omega
    omega
  have hA : ∀ k ≤ entryDegreeBound τ, Commute X (xCoeff τ M j k) := fun k hk =>
    commute_of_forall_sum_pow_smul hd (fun c hc => by
      rw [← xOp_eq_sum_xCoeff_entryDegreeBound]
      exact hx c hc) hk
  have hB : ∀ k ≤ entryDegreeBound τ, Commute X (yCoeff τ M j k) := fun k hk =>
    commute_of_forall_sum_pow_smul hd (fun c hc => by
      rw [← yOp_eq_sum_yCoeff_entryDegreeBound]
      exact hy c hc) hk
  refine ⟨?_, ?_⟩
  · rw [xOp_eq_sum_xCoeff_entryDegreeBound]
    exact Commute.sum_right _ _ _ fun k hk =>
      (hA k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).smul_right _
  · rw [yOp_eq_sum_yCoeff_entryDegreeBound]
    exact Commute.sum_right _ _ _ fun k hk =>
      (hB k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).smul_right _

theorem map_baseChangeGL_subsystemGroup_le {K : Type} [Field K] (f : K →+* M)
    (J : Set (Fin τ.rank)) :
    (subsystemGroup τ K J).map (baseChangeGL f) ≤ subsystemGroup τ M J := by
  rw [Subgroup.map_le_iff_le_comap]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_xUnit]
    exact xUnit_mem_subsystemGroup hj _
  · rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_yUnit]
    exact yUnit_mem_subsystemGroup hj _

theorem subsystemGroup_le_centralizer_of_commute {J : Set (Fin τ.rank)} {y : ModGL τ M}
    (h : ∀ j ∈ J, ∀ c : M, Commute (y : Module.End M (RootModule τ M)) (xOp τ M j c) ∧
      Commute (y : Module.End M (RootModule τ M)) (yOp τ M j c)) :
    subsystemGroup τ M J ≤ Subgroup.centralizer {y} := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_xUnit]
    exact (h j hj c).1.symm.eq
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, coe_yUnit]
    exact (h j hj c).2.symm.eq

theorem standardLevi_inf_centralizer_conj
    (J : Set (Fin τ.rank)) (K : Subfield M) [Finite K]
    (hK : 4 ≤ Nat.card K) {a : ModGL τ M} (ha : a ∈ subsystemGroup τ M J) :
    standardLevi τ M J ⊓ Subgroup.centralizer
        ((((subsystemGroup τ K J).map (baseChangeGL K.subtype)).map
          (MulAut.conj a).toMonoidHom : Subgroup (ModGL τ M)) : Set (ModGL τ M)) =
      simpleCharKernel τ M J := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set F : Finset M := Finset.univ.map (Function.Embedding.subtype (· ∈ K)) with hFdef
  have hFcard : 4 ≤ F.card := by
    rw [hFdef, Finset.card_map, Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact hK
  have hmemF : ∀ c ∈ F, c ∈ K := by
    intro c hc
    rw [hFdef, Finset.mem_map] at hc
    obtain ⟨x, -, rfl⟩ := hc
    exact x.2
  have haL : a ∈ standardLevi τ M J := subsystemGroup_le_standardLevi J ha
  set φ := baseChangeGL (τ := τ) K.subtype with hφ
  have hle : ((subsystemGroup τ K J).map φ).map (MulAut.conj a).toMonoidHom ≤
      subsystemGroup τ M J := by
    rintro _ ⟨g, hg, rfl⟩
    have hg' := map_baseChangeGL_subsystemGroup_le K.subtype J hg
    change a * g * a⁻¹ ∈ subsystemGroup τ M J
    exact mul_mem (mul_mem ha hg') (inv_mem ha)
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hyL, hyC⟩
    set y' := a⁻¹ * y * a with hy'
    have hy'L : y' ∈ standardLevi τ M J := mul_mem (mul_mem (inv_mem haL) hyL) haL
    have hcomm : ∀ g ∈ subsystemGroup τ K J, φ g * y' = y' * φ g := by
      intro g hg
      have h1 := hyC (a * φ g * a⁻¹) ⟨φ g, ⟨g, hg, rfl⟩, rfl⟩
      calc φ g * y' = a⁻¹ * ((a * φ g * a⁻¹) * y) * a := by rw [hy']; group
        _ = a⁻¹ * (y * (a * φ g * a⁻¹)) * a := by rw [h1]
        _ = y' * φ g := by rw [hy']; group
    have hX : ∀ j ∈ J, ∀ c : M, Commute (y' : Module.End M (RootModule τ M)) (xOp τ M j c) ∧
        Commute (y' : Module.End M (RootModule τ M)) (yOp τ M j c) := by
      intro j hj
      refine commute_xOp_yOp_of_four_le_card hFcard (fun c hc => ?_) (fun c hc => ?_)
      · have h2 := congrArg Units.val (hcomm _ (xUnit_mem_subsystemGroup hj ⟨c, hmemF c hc⟩))
        rw [hφ, baseChangeGL_xUnit, Units.val_mul, Units.val_mul, coe_xUnit] at h2
        exact h2.symm
      · have h2 := congrArg Units.val (hcomm _ (yUnit_mem_subsystemGroup hj ⟨c, hmemF c hc⟩))
        rw [hφ, baseChangeGL_yUnit, Units.val_mul, Units.val_mul, coe_yUnit] at h2
        exact h2.symm
    have hcen : y' ∈ simpleCharKernel τ M J := by
      rw [← standardLevi_inf_centralizer]
      exact Subgroup.mem_inf.2 ⟨hy'L, Subgroup.mem_centralizer_iff.2 fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.1 (subsystemGroup_le_centralizer_of_commute hX hx)⟩
    have hya : a * y' = y' * a :=
      Subgroup.mem_centralizer_singleton_iff.1 (subsystemGroup_le_centralizer_of_mem hcen ha)
    have hyy : y = y' := by
      calc y = a * (a⁻¹ * y * a) * a⁻¹ := by group
        _ = y' * a * a⁻¹ := by rw [← hy', hya]
        _ = y' := by group
    rw [hyy]
    exact hcen
  · intro hy
    exact ⟨torusGroup_le_standardLevi J hy.1, fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.1 (subsystemGroup_le_centralizer_of_mem hy (hle hx))⟩

theorem odd_card_simpleCharKernel [Finite M] [CharP M 2] (J : Set (Fin τ.rank)) :
    Odd (Nat.card (simpleCharKernel τ M J)) := by
  have h1 : Nat.card (simpleCharKernel τ M J) ∣ Nat.card (supportedTorus τ M Set.univ) :=
    Subgroup.card_dvd_of_le fun _ hh => torusGroup_le_supportedTorus_univ hh.1
  have h2 := Subgroup.card_range_dvd (supportedTorusHom τ M Set.univ)
  have h3 : Odd (Nat.card (↥(Set.univ : Set (Fin τ.rank)) → Mˣ)) := by
    rw [Nat.card_pi, Finset.prod_const]
    exact (TrialityCover.odd_card_units_of_charTwo M).pow
  exact h3.of_dvd_nat (h1.trans h2)

end NativeLevi

open NativeLevi

end CFSG.RankThree.Chevalley
