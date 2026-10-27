module

public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationLocal
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationModel
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationFacts
import all CFSG.Quasithin.EmptyFaithful.A10ConfigurationClasses

public section

namespace CFSG.Quasithin.A10

open CFSG.Open CFSG.Quasithin S4 Wc

def qPred (x : Wc) : Bool :=
  (x.a ∈ dList) && (x.b ∈ dList) && (x.a⁻¹ * x.b == 1 || x.a⁻¹ * x.b == tau)

def qList : List Wc :=
  dList.flatMap fun a => [1, tau].flatMap fun c => [⟨a, a * c, false⟩, ⟨a, a * c, true⟩]

theorem qPred_iff : ∀ x : Wc, qPred x = true ↔ x ∈ qList := by decide +kernel

def Qh : Subgroup Wc where
  carrier := {x | qPred x = true}
  one_mem' := by decide +kernel
  mul_mem' := by
    intro a b ha hb
    have key : ∀ x ∈ qList, ∀ y ∈ qList, qPred (x * y) = true := by decide +kernel
    exact key a ((qPred_iff a).1 ha) b ((qPred_iff b).1 hb)
  inv_mem' := by
    intro a ha
    have key : ∀ x ∈ qList, qPred x⁻¹ = true := by decide +kernel
    exact key a ((qPred_iff a).1 ha)

theorem mem_Qh {x : Wc} : x ∈ Qh ↔ qPred x = true := Iff.rfl

instance : DecidablePred (· ∈ Qh) := fun x => decidable_of_iff (qPred x = true) mem_Qh.symm

theorem forall_mem_Qh {P : Wc → Prop}
    (h : ∀ a ∈ dList, ∀ c ∈ [1, tau], ∀ e : Bool, P ⟨a, a * c, e⟩) : ∀ x ∈ Qh, P x := by
  intro x hx
  have hx' : x ∈ qList := (qPred_iff x).1 hx
  have key : ∀ x ∈ qList, ∃ a ∈ dList, ∃ c ∈ [1, tau], ∃ e : Bool, x = ⟨a, a * c, e⟩ := by
    decide +kernel
  obtain ⟨a, ha, c, hc, e, rfl⟩ := key x hx'
  exact h a ha c hc e

theorem card_Qh : Nat.card Qh = 32 := by
  rw [card_eq_finset_card]
  decide +kernel

theorem Qh_commutator : ∀ x ∈ Qh, ∀ y ∈ Qh,
    x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z0 :=
  forall_mem_Qh fun a ha c hc e => forall_mem_Qh fun a' ha' c' hc' e' => by
    revert a ha c hc e a' ha' c' hc' e'
    decide +kernel

theorem Qh_sq : ∀ x ∈ Qh, x * x = 1 ∨ x * x = z0 :=
  forall_mem_Qh fun a ha c hc e => by revert a ha c hc e; decide +kernel

def thList : List Wc :=
  dList.flatMap fun a => dList.flatMap fun b => [⟨a, b, false⟩, ⟨a, b, true⟩]

def cList : List Wc := thList.filter fun u => u * u == 1 || u * u == z0

theorem mem_cList : ∀ v ∈ Th, (v * v = 1 ∨ v * v = z0) → v ∈ cList :=
  forall_mem_Th fun a ha b hb e => by revert a ha b hb e; decide +kernel

theorem nbhd_lt : ∀ u₀ ∈ cList, qPred u₀ = false →
    (cList.filter fun v => u₀ * v * u₀⁻¹ * v⁻¹ == 1 || u₀ * v * u₀⁻¹ * v⁻¹ == z0).length < 32 := by
  decide +kernel

theorem elemAbelianMod_le (U : Subgroup Wc) (hUT : U ≤ Th)
    (hsq : ∀ u ∈ U, u * u = 1 ∨ u * u = z0)
    (hc : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = z0) :
    Nat.card U ≤ 32 ∧ (Nat.card U = 32 → U = Qh) := by
  by_cases hUQ : U ≤ Qh
  · refine ⟨card_Qh ▸ Subgroup.card_le_of_le hUQ, fun h => ?_⟩
    exact Subgroup.eq_of_le_of_card_ge hUQ (by rw [h, card_Qh])
  · obtain ⟨u₀, hu₀, hu₀Q⟩ : ∃ u ∈ U, u ∉ Qh := by
      by_contra hcon
      push Not at hcon
      exact hUQ hcon
    have hu₀c : u₀ ∈ cList := mem_cList u₀ (hUT hu₀) (hsq u₀ hu₀)
    have hQp : qPred u₀ = false := by
      cases h : qPred u₀
      · rfl
      · exact absurd ((mem_Qh).2 h) hu₀Q
    have hlt := nbhd_lt u₀ hu₀c hQp
    have hsub : (U : Set Wc) ⊆ ↑((cList.filter fun v =>
        u₀ * v * u₀⁻¹ * v⁻¹ == 1 || u₀ * v * u₀⁻¹ * v⁻¹ == z0).toFinset) := by
      intro v hv
      rw [Finset.mem_coe, List.mem_toFinset, List.mem_filter]
      refine ⟨mem_cList v (hUT hv) (hsq v hv), ?_⟩
      rcases hc u₀ hu₀ v hv with h | h <;> simp [h]
    have hcard : Nat.card U ≤ (cList.filter fun v =>
        u₀ * v * u₀⁻¹ * v⁻¹ == 1 || u₀ * v * u₀⁻¹ * v⁻¹ == z0).length := by
      calc Nat.card U = (U : Set Wc).ncard := by rw [← Nat.card_coe_set_eq]; rfl
        _ ≤ (↑((cList.filter fun v => u₀ * v * u₀⁻¹ * v⁻¹ == 1 ||
            u₀ * v * u₀⁻¹ * v⁻¹ == z0).toFinset) : Set Wc).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
        _ = (cList.filter fun v => u₀ * v * u₀⁻¹ * v⁻¹ == 1 ||
            u₀ * v * u₀⁻¹ * v⁻¹ == z0).toFinset.card := Set.ncard_coe_finset _
        _ ≤ _ := List.toFinset_card_le _
    refine ⟨by omega, fun h => by omega⟩

theorem mem_zpowers_z0_iff {x : Wc} : x ∈ Subgroup.zpowers z0 ↔ x = 1 ∨ x = z0 := by
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rcases Int.even_or_odd' n with ⟨j, rfl | rfl⟩
    · left
      rw [zpow_mul]
      simp [pow_two, z0_sq]
    · right
      rw [zpow_add, zpow_mul]
      simp [pow_two, z0_sq]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

variable {G : Type*} [Group G]

namespace Emb

variable {T M : Subgroup G} (E : Emb G T M)

@[expose] def Q : Subgroup G := Qh.map E.ι

theorem card_Q : Nat.card E.Q = 32 := by
  unfold Q
  rw [card_map_of_inj E.injective, card_Qh]

theorem map_zpowers_z0 : (Subgroup.zpowers z0).map E.ι = Subgroup.zpowers E.z := by
  unfold z
  rw [MonoidHom.map_zpowers]

theorem mem_zpowers_z_iff {x : G} : x ∈ Subgroup.zpowers E.z ↔ x = 1 ∨ x = E.z := by
  rw [← E.map_zpowers_z0]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases mem_zpowers_z0_iff.1 hw with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers z0)

theorem Q_elemAbelian_mod_z : (∀ x ∈ E.Q, x * x ∈ Subgroup.zpowers E.z) ∧
    ∀ x ∈ E.Q, ∀ y ∈ E.Q, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers E.z := by
  constructor
  · rintro _ ⟨w, hw, rfl⟩
    rw [← map_mul, ← E.map_zpowers_z0]
    exact Subgroup.mem_map_of_mem _ (mem_zpowers_z0_iff.2 (Qh_sq w hw))
  · rintro _ ⟨w, hw, rfl⟩ _ ⟨w', hw', rfl⟩
    have : E.ι w * E.ι w' * (E.ι w)⁻¹ * (E.ι w')⁻¹ = E.ι (w * w' * w⁻¹ * w'⁻¹) := by simp
    rw [this, ← E.map_zpowers_z0]
    exact Subgroup.mem_map_of_mem _ (mem_zpowers_z0_iff.2 (Qh_commutator w hw w' hw'))

theorem Q_unique_maximal (U : Subgroup G) (hUT : U ≤ T)
    (hsq : ∀ u ∈ U, u * u ∈ Subgroup.zpowers E.z)
    (hc : ∀ u ∈ U, ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ Subgroup.zpowers E.z) :
    Nat.card U ≤ 32 ∧ (Nat.card U = 32 → U = E.Q) := by
  have hrange : U ≤ E.ι.range := E.le_range_of_le_M (hUT.trans E.T_le_M)
  have hUc : U.comap E.ι ≤ Th := by
    intro w hw
    have : E.ι w ∈ T := hUT hw
    obtain ⟨w', hw', h⟩ := (SetLike.ext_iff.mp E.map_Th (E.ι w)).2 this
    have : w' = w := E.injective h
    rwa [← this]
  have hcard : Nat.card (U.comap E.ι) = Nat.card U := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hrange]
    exact (card_map_of_inj E.injective _).symm
  have hsq' : ∀ u ∈ U.comap E.ι, u * u = 1 ∨ u * u = z0 := by
    intro u hu
    have := hsq _ hu
    rw [← map_mul, ← E.map_zpowers_z0] at this
    obtain ⟨w, hw, hwu⟩ := this
    have := E.injective hwu
    rw [← this]
    exact mem_zpowers_z0_iff.1 hw
  have hc' : ∀ u ∈ U.comap E.ι, ∀ v ∈ U.comap E.ι,
      u * v * u⁻¹ * v⁻¹ = 1 ∨ u * v * u⁻¹ * v⁻¹ = z0 := by
    intro u hu v hv
    have := hc _ hu _ hv
    have e : E.ι u * E.ι v * (E.ι u)⁻¹ * (E.ι v)⁻¹ = E.ι (u * v * u⁻¹ * v⁻¹) := by simp
    rw [e, ← E.map_zpowers_z0] at this
    obtain ⟨w, hw, hwu⟩ := this
    have := E.injective hwu
    rw [← this]
    exact mem_zpowers_z0_iff.1 hw
  obtain ⟨h1, h2⟩ := elemAbelianMod_le (U.comap E.ι) hUc hsq' hc'
  refine ⟨hcard ▸ h1, fun h => ?_⟩
  have := h2 (hcard.trans h)
  unfold Q
  rw [← this, Subgroup.map_comap_eq_self hrange]

end Emb

end CFSG.Quasithin.A10
