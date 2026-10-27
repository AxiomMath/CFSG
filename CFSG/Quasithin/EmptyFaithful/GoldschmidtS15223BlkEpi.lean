module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223L3Orb

public section

namespace CFSG.Quasithin.S15223

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem isPGroup_quotient_of_map_eq_top {Y : Subgroup G} {A : Type} [Group A] {α : ↥Y →* A}
    (hk : α.ker = CFSG.pCore 2 ↥Y) {N : Subgroup ↥Y} [N.Normal] (hN : N.map α = ⊤) :
    IsPGroup 2 (↥Y ⧸ N) := by
  intro c
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  have hy : α y ∈ N.map α := by rw [hN]; exact Subgroup.mem_top _
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  have hq : x⁻¹ * y ∈ CFSG.pCore 2 ↥Y := by
    rw [← hk, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨_, hq⟩
  have hm' : (x⁻¹ * y) ^ 2 ^ m = 1 := by
    have := congrArg (fun y : ↥(CFSG.pCore 2 ↥Y) => (y : ↥Y)) hm
    simpa using this
  refine ⟨m, ?_⟩
  have hmk : (QuotientGroup.mk y : ↥Y ⧸ N) = QuotientGroup.mk (x⁻¹ * y) := by
    rw [QuotientGroup.eq]
    simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance _ (N.inv_mem hx) y⁻¹
  rw [hmk, ← QuotientGroup.mk_pow, hm']
  rfl

theorem commutator_eq_self_of_epi {Y : Subgroup G}
    (hY : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → N = ⊤)
    {A : Type} [Group A] [Group.IsPerfect A] {α : ↥Y →* A} (hs : Function.Surjective α)
    (hk : α.ker = CFSG.pCore 2 ↥Y) : ⁅Y, Y⁆ = Y := by
  have htop : (⊤ : Subgroup ↥Y).map α = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective α hs
  have hN : (commutator ↥Y).map α = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, htop, ← commutator_def]
    exact Group.IsPerfect.commutator_eq_top
  have h2 := isPGroup_quotient_of_map_eq_top hk (N := commutator ↥Y) hN
  exact Subgroup.isPerfect_iff.1 ⟨hY _ h2⟩

variable [Finite G]

theorem eq_oPrimeResidualOf_of_epi_simple {Y : Subgroup G}
    (hY : ∀ (N : Subgroup ↥Y) [N.Normal], IsPGroup 2 (↥Y ⧸ N) → N = ⊤)
    {A : Type} [Group A] [IsSimpleGroup A] {α : ↥Y →* A} (hs : Function.Surjective α)
    (hk : α.ker = CFSG.pCore 2 ↥Y) (h3 : 3 ∣ Nat.card A) : Y = oPrimeResidualOf 3 Y := by
  have h3Y : 3 ∣ Nat.card ↥Y := h3.trans (Subgroup.card_dvd_of_surjective hs)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk3⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3Y
  have hNY : oPrimeResidualOf 3 Y ≤ Y := (Subgroup.closure_le _).mpr fun x hx => hx.1
  set N' : Subgroup ↥Y := (oPrimeResidualOf 3 Y).subgroupOf Y with hN'
  have hNn : N'.Normal := by
    rw [hN', Subgroup.normal_subgroupOf_iff_le_normalizer hNY]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => conj_mem_oPrimeResidualOf_of_le
        (fun y hy => Y.mul_mem (Y.mul_mem hg hy) (Y.inv_mem hg)) hx
    · intro hx
      have := conj_mem_oPrimeResidualOf_of_le (g := g⁻¹)
        (fun y hy => Y.mul_mem (Y.mul_mem (Y.inv_mem hg) hy) (Y.inv_mem (Y.inv_mem hg))) hx
      simpa [mul_assoc] using this
  have hkN : k ∈ N' := by
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨k.2, 1, ?_⟩)
    rw [pow_one, Subgroup.orderOf_coe]
    exact hk3
  have hAn : (N'.map α).Normal := hNn.map α hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N'.map α) with hbot | htop
  ·
    exfalso
    have hk1 : α k = 1 := by
      have : α k ∈ N'.map α := Subgroup.mem_map_of_mem α hkN
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have hkq : k ∈ CFSG.pCore 2 ↥Y := by rw [← hk]; exact hk1
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Y)) ⟨k, hkq⟩
    have hm1 : k ^ 2 ^ m = 1 := by
      have := congrArg (fun y : ↥(CFSG.pCore 2 ↥Y) => (y : ↥Y)) hm
      simpa using this
    have h3dvd : 3 ∣ 2 ^ m := hk3 ▸ orderOf_dvd_of_pow_eq_one hm1
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3dvd) (by norm_num)
  ·
    have htop' : N' = ⊤ := hY N' (isPGroup_quotient_of_map_eq_top hk htop)
    exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop') hNY

end CFSG.Quasithin.S15223
