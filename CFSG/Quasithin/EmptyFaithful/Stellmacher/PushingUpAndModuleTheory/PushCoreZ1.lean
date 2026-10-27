module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreNat

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def zOne (X S Z : Subgroup G) : Subgroup G :=
  Z ⊓ centMod (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)) (thompsonJ S)

section

variable [Finite G] {X S Z : Subgroup G}

theorem PushHyp.le_normalizer_Z0 (h : PushHyp X S Z) :
    X ≤ Subgroup.normalizer ((Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G) : Subgroup G) :
      Set G) := by
  have fwd : ∀ g ∈ X, ∀ x ∈ Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G),
      g * x * g⁻¹ ∈ Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G) := fun g hg x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp (h.normal hg) x).mp hx.1,
      conj_mem_centralizer (le_normalizer_pResidualOf X hg) hx.2⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fwd g hg x, fun hx => ?_⟩
  have := fwd g⁻¹ (X.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem mem_zOne_iff (h : PushHyp X S Z) {z : G} :
    z ∈ zOne X S Z ↔ z ∈ Z ∧ ∀ j ∈ thompsonJ S,
      ⁅j, z⁆ ∈ Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G) := by
  constructor
  · rintro ⟨hz, -, hj⟩
    exact ⟨hz, hj⟩
  · rintro ⟨hz, hj⟩
    exact ⟨hz, h.le_normalizer_Z0 (h.le_core.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hz), hj⟩

theorem centralizer_inf_le_zOne (h : PushHyp X S Z) {A : Subgroup G}
    (hJA : thompsonJ S ≤ A ⊔ pCoreOf 2 X) :
    Z ⊓ Subgroup.centralizer (A : Set G) ≤ zOne X S Z := by
  rintro z ⟨hz, hzA⟩
  rw [mem_zOne_iff h]
  refine ⟨hz, fun j hj => ?_⟩
  have hle : A ⊔ pCoreOf 2 X ≤ Subgroup.centralizer ({z} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun q hq => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]
      exact (Subgroup.mem_centralizer_iff.mp hzA a ha).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]
      exact h.core_le_centralizer hq z hz
  have hjz : z * j = j * z := (Subgroup.mem_centralizer_iff.mp (hle (hJA hj)) z rfl)
  have : ⁅j, z⁆ = 1 := by
    rw [commutatorElement_def]
    calc j * z * j⁻¹ * z⁻¹ = (j * z) * j⁻¹ * z⁻¹ := rfl
      _ = (z * j) * j⁻¹ * z⁻¹ := by rw [hjz]
      _ = 1 := by group
  rw [this]
  exact Subgroup.one_mem _

theorem centralizes_of_card_zOne (h : PushHyp X S Z) {A : Subgroup G}
    (hJA : thompsonJ S ≤ A ⊔ pCoreOf 2 X)
    (hIdx : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z ≤ (zOne X S Z).relIndex Z)
    {z : G} (hz : z ∈ Z)
    (hzJ : ∀ j ∈ thompsonJ S, ⁅j, z⁆ ∈ Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)) :
    ∀ a ∈ A, a * z * a⁻¹ = z := by
  have hle := centralizer_inf_le_zOne h hJA
  have hZ1Z : zOne X S Z ≤ Z := inf_le_left
  have hmul := Subgroup.relIndex_mul_relIndex (Z ⊓ Subgroup.centralizer (A : Set G)) (zOne X S Z) Z
    hle hZ1Z
  have h1 : (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex (zOne X S Z) = 1 := by
    have hpos := relIndex_pos (zOne X S Z) Z
    have hpos' := relIndex_pos (Z ⊓ Subgroup.centralizer (A : Set G)) (zOne X S Z)
    by_contra hne
    have : 2 ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex (zOne X S Z) := by omega
    have : 2 * (zOne X S Z).relIndex Z ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z := by
      rw [← hmul]; exact Nat.mul_le_mul_right _ this
    omega
  have hz1 : z ∈ zOne X S Z := (mem_zOne_iff h).mpr ⟨hz, hzJ⟩
  have hzA := Subgroup.relIndex_eq_one.mp h1 hz1
  intro a ha
  have := Subgroup.mem_centralizer_iff.mp hzA.2 a ha
  calc a * z * a⁻¹ = (a * z) * a⁻¹ := rfl
    _ = (z * a) * a⁻¹ := by rw [this]
    _ = z := by group

theorem natCounts_of_zOne (h : PushHyp X S Z) {m : ℕ}
    (offender_le : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      (A ⊓ pCoreOf 2 X).relIndex A ≤ m)
    (offender_ge : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      m ≤ (Z ⊓ Subgroup.centralizer (A : Set G)).relIndex Z)
    (thompsonJ_le : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      thompsonJ S ≤ A ⊔ pCoreOf 2 X)
    (residual_le : ∀ A : Subgroup G, IsMaxElemAbelian S A → ¬ A ≤ pCoreOf 2 X →
      pResidualOf 2 X ⊓ S ≤ A ⊔ pCoreOf 2 X)
    (zOne_ge : m ≤ (zOne X S Z).relIndex Z)
    (generated : ∃ g ∈ pResidualOf 2 X,
      pResidualOf 2 X ≤ (thompsonJ S ⊔ cj g (thompsonJ S)) ⊔ pCoreOf 2 X)
    (index_ge : m ^ 2 ≤ (Z ⊓ Subgroup.centralizer (pResidualOf 2 X : Set G)).relIndex Z) :
    NatCounts X S Z m where
  offender_le := offender_le
  offender_ge := offender_ge
  thompsonJ_le := thompsonJ_le
  residual_inf_le := by
    intro A hA hAQ s hs
    have hAn : A ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) :=
      hA.1.trans (h.le_self.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    obtain ⟨q', hq', a, ha, hsa⟩ := mem_sup_of_le_normalizer hAn
      (by rw [sup_comm]; exact residual_le A hA hAQ hs)
    have haX : a ∈ X := h.le_self (hA.1 ha)
    have hq : a⁻¹ * q' * a ∈ pCoreOf 2 X := by
      have := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (X.inv_mem haX)) q').mp hq'
      simpa using this
    refine ⟨a, ha, a⁻¹ * q' * a, hq, by rw [hsa]; group, ?_⟩
    exact fun z hz hzJ => centralizes_of_card_zOne h (thompsonJ_le A hA hAQ)
      ((offender_count h hA).trans ((offender_le A hA hAQ).trans zOne_ge)) hz hzJ a ha
  generated := generated
  index_ge := index_ge

end

end CFSG.Quasithin.F53Push
