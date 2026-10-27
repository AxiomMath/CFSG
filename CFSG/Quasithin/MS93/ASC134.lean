module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.ASSL3

public section

namespace CFSG.Quasithin.MS93

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped Pointwise

section Statement

variable {G : Type} [Group G]

@[expose] def IsC134Case4Corr (G₀ R L : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α ∧
      IsE2 (2 * n) ↥(c134CQ G₀ L) ∧
      centerOf (c134Q G₀ L) = c134CQ G₀ L ⊔ ⁅centerOf (c134Q G₀ L), L⁆ ∧
      c134CQ G₀ L ⊓ ⁅centerOf (c134Q G₀ L), L⁆ = ⊥ ∧
      IsSumOfNaturalModulesVia L ⁅centerOf (c134Q G₀ L), L⁆ ⊥ α false 1 ∧
      IsSumOfNaturalModulesVia L (frattiniIn (c134Q G₀ L)) (centerOf (c134Q G₀ L)) α true 1 ∧
      IsSumOfNaturalModulesVia L
        (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G))
        (frattiniIn (c134Q G₀ L)) α true 2 ∧
      IsSumOfNaturalModulesVia L (c134Q G₀ L)
        (c134Q G₀ L ⊓ Subgroup.centralizer (frattiniIn (c134Q G₀ L) : Set G)) α false 2) ∧
    C134NotCentralizerCore G₀ R

@[expose] def IsC134CaseCorr (i : ℕ) (G₀ R L : Subgroup G) : Prop :=
  match i with
  | 1 => IsC134Case1 G₀ R L
  | 2 => IsC134Case2 G₀ R L
  | 3 => IsC134Case3 G₀ R L
  | 4 => IsC134Case4Corr G₀ R L
  | 5 => IsC134Case5 G₀ R L
  | _ => False

end Statement

@[expose] def AS_C_1_34_corr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) →
    (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) →
      ∃ i : ℕ, IsC134CaseCorr i G₀ R L

@[expose] def C134NotCentralizer5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) → PUHyp G₀ R L →
    Xq G₀ ≤ Zq G₀ L ⊔ Uq G₀ R L → MS93Case5 (Vq G₀ L) L → C134NotCentralizerCore G₀ R

@[expose] def C134NotCentralizer11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) → PUHyp G₀ R L →
    Xq G₀ ≤ Zq G₀ L ⊔ Uq G₀ R L → MS93Case11 (Vq G₀ L) R L → C134NotCentralizerCore G₀ R

@[expose] def C134NotCentralizer13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (G₀ R L : Subgroup G), IsMSPair G₀ R → L ∈ cComp G₀ →
    (G₀ : Set G) = (L : Set G) * (R : Set G) → PUHyp G₀ R L →
    Xq G₀ ≤ Zq G₀ L ⊔ Uq G₀ R L → MS93Case13 (Vq G₀ L) R L → C134NotCentralizerCore G₀ R

variable {G : Type} [Group G] [Finite G]

theorem isE2_of_card {V : Type} [Group V] [Finite V] (hc : ∀ x y : V, x * y = y * x)
    (hsq : ∀ x : V, x * x = 1) {n : ℕ} (hcard : Nat.card V = 2 ^ n) : IsE2 n V := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have h2 : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    have : (2 : ℕ) • Additive.ofMul (Additive.toMul x) =
        Additive.ofMul (Additive.toMul x ^ 2) := by
      rw [ofMul_pow]
    have hx : Additive.ofMul (Additive.toMul x) = x := rfl
    rw [hx] at this
    rw [this, pow_two, hsq]
    rfl
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2
  have : Finite (Additive V) := inferInstanceAs (Finite V)
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasis (ZMod 2) (Additive V)
  have hd : Module.finrank (ZMod 2) (Additive V) = n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have hcard' : Nat.card (Additive V) = 2 ^ n := hcard
    rw [hcard', Nat.card_zmod] at h
    exact (Nat.pow_right_injective le_rfl h).symm
  let e : Additive V ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
    b.equivFun.trans (LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr hd.symm))
  exact ⟨AddEquiv.toMultiplicativeRight e.toAddEquiv⟩

theorem isModO2Surj_of_case11_data {M T L : Subgroup G} (h : PUHyp M T L) {F : Type} [Field F]
    [Finite F] {α : ↥L →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (h1 : IsSumOfNaturalModulesVia L (centerOf (Vq M L)) ⊥ α false 1)
    (h2 : IsSumOfNaturalModulesVia L (Vq M L) (centerOf (Vq M L)) α true 2) :
    IsModO2Surj L α := by
  refine ⟨hα, le_antisymm (ker_le_pCore_of_odd α fun ℓ hℓ hodd => ?_)
    (pCore_le_ker_of_statedSL3 α hα)⟩
  have hodd' : Odd (orderOf (ℓ : G)) := by rwa [Subgroup.orderOf_coe]
  have hZQ : centerOf (Vq M L) ≤ pCoreOf 2 M := inf_le_left.trans (Vq_le_pCoreOf h.L_le)
  have hZ : ∀ z ∈ centerOf (Vq M L), (ℓ : G) * z = z * ℓ := fun z hz => by
    have := commutator_mem_of_mem_ker h1 hℓ hz
    rw [Subgroup.mem_bot] at this
    calc (ℓ : G) * z = (ℓ : G) * z * (ℓ : G)⁻¹ * z⁻¹ * (z * ℓ) := by group
      _ = z * ℓ := by rw [this, one_mul]
  have hV := commute_step hodd' hZQ hZ fun b hb => commutator_mem_of_mem_ker h2 hℓ hb
  exact Subtype.ext (eq_one_of_odd_of_commute h.charTwo h.L_le ℓ.2 hodd' hV)

theorem isModO2Surj_of_case13_data {M T L : Subgroup G} (h : PUHyp M T L) {F : Type} [Field F]
    [Finite F] {α : ↥L →* ↥(StatedSL 3 F)} (hα : Function.Surjective α)
    (hZeq : centerOf (Vq M L) =
      Vq M L ⊓ Subgroup.centralizer (L : Set G) ⊔ ⁅centerOf (Vq M L), L⁆)
    (hU : IsSumOfNaturalModulesVia L ⁅centerOf (Vq M L), L⁆ ⊥ α false 1)
    (hΦ : IsSumOfNaturalModulesVia L (frattiniIn (Vq M L)) (centerOf (Vq M L)) α true 1)
    (hC : IsSumOfNaturalModulesVia L
      (Vq M L ⊓ Subgroup.centralizer (frattiniIn (Vq M L) : Set G)) (frattiniIn (Vq M L)) α true 2)
    (hVC : IsSumOfNaturalModulesVia L (Vq M L)
      (Vq M L ⊓ Subgroup.centralizer (frattiniIn (Vq M L) : Set G)) α false 2) :
    IsModO2Surj L α := by
  refine ⟨hα, le_antisymm (ker_le_pCore_of_odd α fun ℓ hℓ hodd => ?_)
    (pCore_le_ker_of_statedSL3 α hα)⟩
  have hodd' : Odd (orderOf (ℓ : G)) := by rwa [Subgroup.orderOf_coe]
  have hVQ : Vq M L ≤ pCoreOf 2 M := Vq_le_pCoreOf h.L_le
  have hZ : ∀ z ∈ centerOf (Vq M L), (ℓ : G) * z = z * ℓ := by
    have hle : centerOf (Vq M L) ≤ Subgroup.centralizer ({(ℓ : G)} : Set G) := by
      rw [hZeq]
      refine sup_le (fun c hc => ?_) (fun u hu => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 ℓ ℓ.2).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have := commutator_mem_of_mem_ker hU hℓ hu
        rw [Subgroup.mem_bot] at this
        calc u * ℓ = (ℓ : G) * u * (ℓ : G)⁻¹ * u⁻¹ * (u * ℓ) := by rw [this, one_mul]
          _ = ℓ * u := by group
    intro z hz
    exact ((Subgroup.mem_centralizer_singleton_iff).mp (hle hz)).symm
  have hZQ : centerOf (Vq M L) ≤ pCoreOf 2 M := inf_le_left.trans hVQ
  have hΦ' := commute_step hodd' hZQ hZ fun b hb => commutator_mem_of_mem_ker hΦ hℓ hb
  have hΦV : frattiniIn (Vq M L) ≤ Vq M L := Subgroup.map_subtype_le _
  have hC' := commute_step hodd' (hΦV.trans hVQ) hΦ' fun b hb =>
    commutator_mem_of_mem_ker hC hℓ hb
  have hV := commute_step hodd' (inf_le_left.trans hVQ) hC' fun b hb =>
    commutator_mem_of_mem_ker hVC hℓ hb
  exact Subtype.ext (eq_one_of_odd_of_commute h.charTwo h.L_le ℓ.2 hodd' hV)

theorem isE2_c134CQ_of_case13 {G₀ L : Subgroup G} {n : ℕ}
    (hcard : Nat.card ↥(Vq G₀ L ⊓ Subgroup.centralizer (L : Set G)) = (2 ^ n) ^ 2)
    (hE : IsElemAbelian 2 (Vq G₀ L ⊓ Subgroup.centralizer (L : Set G))) :
    IsE2 (2 * n) ↥(c134CQ G₀ L) := by
  refine isE2_of_card (fun x y => ?_) (fun x => ?_) ?_
  · exact hE.1.is_comm.comm x y
  · apply Subtype.ext
    have := hE.2 x x.2
    rw [pow_two] at this
    simpa using this
  · show Nat.card ↥(Vq G₀ L ⊓ Subgroup.centralizer (L : Set G)) = 2 ^ (2 * n)
    rw [hcard, ← pow_mul, mul_comm]

end CFSG.Quasithin.MS93
