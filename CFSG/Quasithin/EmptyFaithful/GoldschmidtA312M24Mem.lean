module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Perf

public section

namespace CFSG.Quasithin.A312M24

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_perfectCore (Z : Subgroup G) :
    (perfectCore Z).subgroupOf Z = perfectCore (⊤ : Subgroup ↥Z) := by
  have h := map_perfectCore Z.subtype (⊤ : Subgroup ↥Z)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h
  have h2 : (perfectCore (⊤ : Subgroup ↥Z)).map Z.subtype = perfectCore Z := h
  ext x
  rw [Subgroup.mem_subgroupOf, ← h2]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [Finite G] in
theorem range_le_of_gens {H : Type} [Group H] (gens : Set G)
    (ρ : ↥(Subgroup.closure gens) →* H) (P : Subgroup H)
    (h : ∀ g (hg : g ∈ gens), ρ ⟨g, Subgroup.subset_closure hg⟩ ∈ P) : ρ.range ≤ P := by
  rintro _ ⟨⟨z, hz⟩, rfl⟩
  induction hz using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one =>
    show ρ 1 ∈ P
    rw [map_one]
    exact P.one_mem
  | mul x y hx hy hxP hyP =>
    show ρ (⟨x, hx⟩ * ⟨y, hy⟩) ∈ P
    rw [map_mul]
    exact P.mul_mem hxP hyP
  | inv x hx hxP =>
    show ρ (⟨x, hx⟩⁻¹) ∈ P
    rw [map_inv]
    exact P.inv_mem hxP

theorem card_eq_range_mul_ker {A H : Type*} [Group A] [Group H] (ρ : A →* H) :
    Nat.card A = Nat.card ρ.range * Nat.card ρ.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, mul_comm]

theorem perfectCore_eq_self_of_le_ker {Z : Subgroup G} {H : Type} [Group H] [Finite H]
    (ρ : ↥Z →* H) (hperf : perfectCore ρ.range = ρ.range) {V : Subgroup G}
    (hVA : V ≤ perfectCore Z) (hVker : ρ.ker ≤ V.subgroupOf Z) : perfectCore Z = Z := by
  have hR := subgroupOf_perfectCore Z
  have hρR : (perfectCore (⊤ : Subgroup ↥Z)).map ρ = ρ.range := by
    rw [map_perfectCore, Subgroup.map_top, hperf]
  have htop : perfectCore (⊤ : Subgroup ↥Z) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : ρ z ∈ ρ.range := ⟨z, rfl⟩
    rw [← hρR] at hz
    obtain ⟨r, hr, hrz⟩ := hz
    have hk : r⁻¹ * z ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrz, inv_mul_cancel]
    have hkV := hVker hk
    have hkR : r⁻¹ * z ∈ perfectCore (⊤ : Subgroup ↥Z) := by
      rw [← hR]
      exact hVA (Subgroup.mem_subgroupOf.mp hkV)
    have := Subgroup.mul_mem _ hr hkR
    simpa using this
  rw [← hR, Subgroup.subgroupOf_eq_top] at htop
  exact le_antisymm (perfectCore_le _) htop

theorem perfectCore_eq_self_of_ker {T B Z : Subgroup G} (hT : IsPGroup 2 T) (hB : B ∈ lFamily T)
    (hZ : B ⊔ T = Z) {H : Type} [Group H] [Finite H] (ρ : ↥Z →* H)
    (hperf : perfectCore ρ.range = ρ.range)
    {V : Subgroup G} (hVZ : V ≤ Z) (hVker : ρ.ker ≤ V.subgroupOf Z) {u : G} (hu : u ∈ Z)
    {m : ℕ} (hm : m % 2 = 1) (hum : u ^ m = 1) (hcomm : ∀ v ∈ V, ∃ x ∈ V, ⁅x, u⁆ = v) :
    perfectCore Z = Z := by
  subst hZ
  exact perfectCore_eq_self_of_le_ker ρ hperf
    (le_perfectCore_of_commutators hT hB hVZ hu hm hum hcomm) hVker

theorem map_eq_one_of_mem_perfectCore {Z : Subgroup G} {H : Type} [Group H] [Finite H]
    [Group.IsSolvable H] (ρ : ↥Z →* H) {y : G} (hy : y ∈ Z) (hyA : y ∈ perfectCore Z) :
    ρ ⟨y, hy⟩ = 1 := by
  have h1 : (⟨y, hy⟩ : ↥Z) ∈ perfectCore (⊤ : Subgroup ↥Z) := by
    rw [← subgroupOf_perfectCore Z]
    exact hyA
  have h2 : ρ ⟨y, hy⟩ ∈ perfectCore ρ.range := by
    have := map_perfectCore ρ (⊤ : Subgroup ↥Z)
    rw [Subgroup.map_top] at this
    rw [← this]
    exact ⟨_, h1, rfl⟩
  have h3 : perfectCore ρ.range = ⊥ :=
    (isSolvable_iff_perfectCore_eq_bot _).mp inferInstance
  rw [h3] at h2
  exact Subgroup.mem_bot.mp h2

end Basic

end CFSG.Quasithin.A312M24
