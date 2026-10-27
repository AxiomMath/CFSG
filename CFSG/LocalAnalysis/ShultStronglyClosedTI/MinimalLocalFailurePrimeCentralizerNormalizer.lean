module

public import Mathlib.GroupTheory.Nilpotent

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open Subgroup

theorem act_pow_two_mul_add_one_of_swap {G Ω : Type*} [Group G] (act : Ω → G → Ω)
    (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h)) {g : G} {α β : Ω}
    (hα : act α g = β) (hβ : act β g = α) (m : ℕ) : act α (g ^ (2 * m + 1)) = β := by
  induction m with
  | zero => rwa [Nat.mul_zero, Nat.zero_add, pow_one]
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, pow_succ, pow_succ, ← act_mul,
      ← act_mul, ih, hβ, hα]

theorem act_eq_of_mem_normalizer_of_fixed_pair {G Ω : Type*} [Group G] (act : Ω → G → Ω)
    (act_one : ∀ ω, act ω 1 = ω) (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α β : Ω} (hαβ : α ≠ β) (P : Subgroup G)
    (hPfix : {ω | ∀ g ∈ P, act ω g = ω} = {α, β}) {g : G} (hg : g ∈ normalizer (P : Set G))
    {k : ℕ} (hgk : g ^ p ^ k = 1) : act α g = α ∧ act β g = β := by
  have hmaps : ∀ ω, (∀ h ∈ P, act ω h = ω) → act ω g = α ∨ act ω g = β := by
    intro ω hω
    have hmem : act ω g ∈ {ω | ∀ h ∈ P, act ω h = ω} := fun h hh => by
      rw [act_mul, show g * h = g * h * g⁻¹ * g by group, ← act_mul,
        hω _ ((mem_normalizer_iff.1 hg h).1 hh)]
    rwa [hPfix] at hmem
  have hfix : ∀ ω ∈ ({α, β} : Set Ω), ∀ h ∈ P, act ω h = ω := by
    rw [← hPfix]
    exact fun ω hω => hω
  have hinj : ∀ x y, act x g = act y g → x = y := fun x y hxy => by
    simpa only [act_mul, mul_inv_cancel, act_one] using congrArg (act · g⁻¹) hxy
  obtain ⟨m, hm⟩ := (hp.odd_of_ne_two hp2).pow (n := k)
  rcases hmaps α (hfix α (Set.mem_insert _ _)) with hα | hα <;>
    rcases hmaps β (hfix β (Set.mem_insert_of_mem _ rfl)) with hβ | hβ
  · exact absurd (hinj _ _ (hβ.trans hα.symm)) hαβ.symm
  · exact ⟨hα, hβ⟩
  · have h := act_pow_two_mul_add_one_of_swap act act_mul hα hβ m
    rw [← hm, hgk, act_one] at h
    exact absurd h hαβ
  · exact absurd (hinj _ _ (hβ.trans hα.symm)) hαβ.symm

theorem pSubgroup_maximal_of_fixed_pair {G Ω : Type*} [Group G] [Finite G]
    (act : Ω → G → Ω) (act_one : ∀ ω, act ω 1 = ω)
    (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {α β : Ω} (hαβ : α ≠ β)
    (C P : Subgroup G) (hPp : IsPGroup p P) (hPC : P ≤ C)
    (hPfix : {ω | ∀ g ∈ P, act ω g = ω} = {α, β})
    (hmax : ∀ P' : Subgroup G, IsPGroup p P' → P ≤ P' → P' ≤ C →
      (∀ g ∈ P', act α g = α ∧ act β g = β) → P' = P) :
    ∀ P' : Subgroup G, IsPGroup p P' → P ≤ P' → P' ≤ C → P' = P := by
  have := Fact.mk hp
  intro P' hP' hPP' hP'C
  by_contra hne
  have hlt : P.subgroupOf P' < ⊤ :=
    lt_top_iff_ne_top.2 fun htop => hne (le_antisymm (subgroupOf_eq_top.1 htop) hPP')
  have := hP'.isNilpotent
  obtain ⟨y, hyN, hyP⟩ := IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← subgroupOf_normalizer_eq hPP', mem_subgroupOf] at hyN
  rw [mem_subgroupOf] at hyP
  have hyN' : zpowers (y : G) ≤ normalizer (P : Set G) := zpowers_le.2 hyN
  have hNp : IsPGroup p (P ⊔ zpowers (y : G) : Subgroup G) :=
    hPp.to_sup_of_normal_left' (hP'.to_le (zpowers_le.2 y.2)) hyN'
  have hNfix : ∀ g ∈ P ⊔ zpowers (y : G), act α g = α ∧ act β g = β := fun g hg => by
    obtain ⟨k, hk⟩ := hNp ⟨g, hg⟩
    exact act_eq_of_mem_normalizer_of_fixed_pair act act_one act_mul hp hp2 hαβ P hPfix
      (sup_le le_normalizer hyN' hg) (k := k) (by simpa using congrArg Subtype.val hk)
  have hNP := hmax _ hNp le_sup_left (sup_le hPC (zpowers_le.2 (hP'C y.2))) hNfix
  exact hyP (hNP ▸ mem_sup_right (mem_zpowers _))

theorem exists_sylow_map_eq_of_factorization_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K₁ K₂ : Subgroup G} (hle : K₁ ≤ K₂)
    (hv : (Nat.card K₁).factorization p = (Nat.card K₂).factorization p) (P : Sylow p K₁) :
    ∃ S : Sylow p K₂, (S : Subgroup K₂).map K₂.subtype = (P : Subgroup K₁).map K₁.subtype := by
  have hle' : (P : Subgroup K₁).map K₁.subtype ≤ K₂ := (map_subtype_le _).trans hle
  have hcard : Nat.card (((P : Subgroup K₁).map K₁.subtype).subgroupOf K₂) =
      p ^ (Nat.card K₂).factorization p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle').toEquiv,
      card_map_of_injective K₁.subtype_injective, P.card_eq_multiplicity, hv]
  exact ⟨Sylow.ofCard _ hcard, by
    rw [Sylow.coe_ofCard, subgroupOf_map_subtype, inf_of_le_left hle']⟩

theorem factorization_eq_of_sylow_map_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {K₁ K₂ : Subgroup G} (hle : K₁ ≤ K₂) (P : Sylow p K₁) (S : Sylow p K₂)
    (hPS : (S : Subgroup K₂).map K₂.subtype = (P : Subgroup K₁).map K₁.subtype) :
    (Nat.card K₁).factorization p = (Nat.card K₂).factorization p := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card S = Nat.card P := by
    rw [← card_map_of_injective K₂.subtype_injective, hPS,
      card_map_of_injective K₁.subtype_injective]
  refine le_antisymm ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2
    (card_dvd_of_le hle) p) ?_
  rw [← hp.pow_dvd_iff_le_factorization Nat.card_pos.ne', ← S.card_eq_multiplicity, hcard]
  exact card_subgroup_dvd_card _

theorem exists_sylow_of_fixed_pair {G Ω : Type*} [Group G] [Finite G]
    (act : Ω → G → Ω) (act_one : ∀ ω, act ω 1 = ω)
    (act_mul : ∀ ω g h, act (act ω g) h = act ω (g * h))
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {α β : Ω} (hαβ : α ≠ β) (C K : Subgroup G)
    (hK : ∀ g, g ∈ K ↔ g ∈ C ∧ act α g = α ∧ act β g = β) (P : Sylow p K)
    (hPfix : {ω | ∀ g ∈ (P : Subgroup K).map K.subtype, act ω g = ω} = {α, β}) :
    ∃ S : Sylow p C, (S : Subgroup C).map C.subtype = (P : Subgroup K).map K.subtype := by
  have hKC : K ≤ C := fun g hg => ((hK g).1 hg).1
  have hQK : (P : Subgroup K).map K.subtype ≤ K := map_subtype_le _
  have hQp : IsPGroup p ((P : Subgroup K).map K.subtype) := P.isPGroup'.map K.subtype
  have hmaxC := pSubgroup_maximal_of_fixed_pair act act_one act_mul Fact.out hp2 hαβ C _ hQp
    (hQK.trans hKC) hPfix fun P' hP' hQP' hP'C hfix => by
      have hP'K : P' ≤ K := fun g hg => (hK g).2 ⟨hP'C hg, hfix g hg⟩
      have hsub : P'.subgroupOf K = P := P.is_maximal' hP'.comap_subtype fun x hx =>
        mem_subgroupOf.2 (hQP' (mem_map_of_mem K.subtype hx))
      rw [← inf_of_le_left hP'K, ← subgroupOf_map_subtype, hsub]
  obtain ⟨S, hS⟩ := (hQp.comap_subtype (K := C)).exists_le_sylow
  refine ⟨S, hmaxC _ (S.isPGroup'.map C.subtype) ?_ (map_subtype_le _)⟩
  rw [← inf_of_le_left (hQK.trans hKC), ← subgroupOf_map_subtype]
  exact map_mono hS

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
