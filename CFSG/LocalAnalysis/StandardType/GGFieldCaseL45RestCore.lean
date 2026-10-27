module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem exists_pow_mul_of_cyclic [Finite G] {p : ℕ} [Fact p.Prime] {U U₁ : Subgroup G}
    {g x u : G} (hUN : U ≤ Subgroup.normalizer (U₁ : Set G)) (hg : g ∈ U)
    (hcyc : U ≤ Subgroup.zpowers g ⊔ U₁) (hx : x ∈ U) (hxU₁ : x ∉ U₁) (hxp : x ^ p ∈ U₁)
    (hu : u ∈ U) (hup : u ^ p ∈ U₁) : ∃ i : ℕ, ∃ a ∈ U₁, u = x ^ i * a := by
  set N : Subgroup U := U₁.subgroupOf U with hNdef
  have hNn : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUN
  have hmk : ∀ w : U, (QuotientGroup.mk w : U ⧸ N) = 1 ↔ (w : G) ∈ U₁ := fun w => by
    rw [QuotientGroup.eq_one_iff, hNdef, Subgroup.mem_subgroupOf]
  have hgN : Subgroup.zpowers g ≤ Subgroup.normalizer (U₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hUN hg)
  have hQ : IsCyclic (U ⧸ N) := by
    refine ⟨⟨(QuotientGroup.mk (⟨g, hg⟩ : U) : U ⧸ N), fun q => ?_⟩⟩
    induction q using QuotientGroup.induction_on with
    | H w =>
      have hw : (w : G) ∈ ((Subgroup.zpowers g ⊔ U₁ : Subgroup G) : Set G) := hcyc w.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hgN] at hw
      obtain ⟨c, hc, a, ha, hca⟩ := hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      refine ⟨k, ?_⟩
      change (QuotientGroup.mk (⟨g, hg⟩ : U) : U ⧸ N) ^ k = QuotientGroup.mk w
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (((⟨g, hg⟩ : U) ^ k)⁻¹ * w : U) = (g ^ k)⁻¹ * (w : G) := by simp
      rw [this, ← hca, inv_mul_cancel_left]
      exact ha
  set xb : U ⧸ N := QuotientGroup.mk (⟨x, hx⟩ : U) with hxb
  set ub : U ⧸ N := QuotientGroup.mk (⟨u, hu⟩ : U) with hub
  have hxb1 : xb ≠ 1 := fun h => hxU₁ ((hmk _).mp h)
  have hxbp : xb ^ p = 1 := by
    rw [hxb, ← QuotientGroup.mk_pow, hmk]
    simpa using hxp
  have hubp : ub ^ p = 1 := by
    rw [hub, ← QuotientGroup.mk_pow, hmk]
    simpa using hup
  by_cases hub1 : ub = 1
  · exact ⟨0, u, (hmk _).mp hub1, by simp⟩
  have heq : Subgroup.zpowers ub = Subgroup.zpowers xb := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      orderOf_eq_prime hxbp hxb1, orderOf_eq_prime hubp hub1]
  have hubx : ub ∈ Subgroup.zpowers xb := heq ▸ Subgroup.mem_zpowers ub
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hubx)
  refine ⟨i, (x ^ i)⁻¹ * u, ?_, by group⟩
  have h1 : (QuotientGroup.mk ((⟨x, hx⟩ : U) ^ i) : U ⧸ N) = QuotientGroup.mk (⟨u, hu⟩ : U) := by
    rw [QuotientGroup.mk_pow]
    exact hi
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  simpa using h1

end General

section Core

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem ggL46_omega_of_cyclic (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hab : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) {s : ℕ} (hs : 2 ≤ s)
    (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1) {x' : G} (hx'x : Subgroup.zpowers x' = Subgroup.zpowers x)
    (hact : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1)))
    {g₀ : G} (hg₀ : g₀ ∈ U) (hcyc : U ≤ Subgroup.zpowers g₀ ⊔ U₁) :
    (∀ u ∈ U, u ^ p = 1 → u ∈ Bs) ∧
      ∀ u : G, u ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ u ∈ U₁ ∧ u ^ p = 1 := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hp := hcfg.prime
  obtain ⟨hB₁U₁, hxU₁, -⟩ := ggL4546_basic hraw hiso hcfg
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hps : p ^ (s - 1) = p * p ^ (s - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hgen : ∀ a : G, a ^ p = 1 → a ^ p ^ (s - 1) = 1 := fun a ha => by
    rw [hps, pow_mul, ha, one_pow]
  have hΩU : ∀ u ∈ U, u ^ p = 1 → u ∈ Bs := by
    intro u hu hup
    obtain ⟨i, a, ha, rfl⟩ := exists_pow_mul_of_cyclic hcfg.le_normalizer_part hg₀ hcyc hxU hxU₁
      (by rw [hcfg.x_pow]; exact one_mem _) hu (by rw [hup]; exact one_mem _)
    have hxi : x ^ i ∈ Subgroup.zpowers x' := hx'x ▸ Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hxi)
    rw [← hm] at hup ⊢
    have hx'U : x' ∈ U :=
      (Subgroup.zpowers_le.mpr hxU) (hx'x ▸ Subgroup.mem_zpowers x')
    have hx'Bs : x' ∈ Bs :=
      (Subgroup.zpowers_le.mpr hcfg.x_mem) (hx'x ▸ Subgroup.mem_zpowers x')
    have hcU₁ : (a ^ p ^ (s - 1)) ^ m ∈ U₁ := U₁.pow_mem (U₁.pow_mem ha _) _
    have hcp : ((a ^ p ^ (s - 1)) ^ m) ^ p = 1 := by
      have h1 : (a ^ p ^ (s - 1)) ^ p = 1 := by
        rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega), hexp a ha]
      rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
    have hxa : (x' ^ m)⁻¹ * a * x' ^ m = a * (a ^ p ^ (s - 1)) ^ m :=
      conj_pow_eq_mul_pow_pow hs hexp hact m a ha
    have hxc : (x' ^ m)⁻¹ * (a ^ p ^ (s - 1)) ^ m * x' ^ m = (a ^ p ^ (s - 1)) ^ m := by
      rw [conj_pow_eq_mul_pow_pow hs hexp hact m _ hcU₁, hgen _ hcp, one_pow, mul_one]
    have hac : Commute a ((a ^ p ^ (s - 1)) ^ m) := hab a ha _ hcU₁
    have hx'p : (x' ^ m) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hcfg.isElemAbelian.2 x' hx'Bs, one_pow]
    have hpow := GGL48.mul_pow_prime_eq hp hcfg.odd hxa hxc hac hx'p hcp
    have hap : a ^ p = 1 := by rw [← hpow]; exact hup
    have hax' : Commute a x' := by
      have h1 := hact a ha
      rw [pow_add, pow_one, hgen a hap, mul_one] at h1
      calc a * x' = x' * (x'⁻¹ * a * x') := by group
        _ = x' * a := by rw [h1]
    have hax : a * x = x * a := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx'x ▸ Subgroup.mem_zpowers x :
        x ∈ Subgroup.zpowers x')
      rw [← hk]
      exact (Commute.zpow_right hax' k).eq
    have haBs := hcfg.mem_of_commute (hcfg.part_le ha) hax hap
    exact Bs.mul_mem (Bs.pow_mem hx'Bs m) haBs
  refine ⟨hΩU, fun u => ⟨fun hu => ⟨hB₁U₁ hu, hcfg.isElemAbelian.2 u hu.1⟩, ?_⟩⟩
  rintro ⟨hu, hup⟩
  exact hcfg.inf_part_le hB₁U₁ hxU₁ ⟨hΩU u (hcfg.part_le hu) hup, hu⟩

end Core

theorem ggL46CoreInput_of_torus (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput) (htorus : GGL45TorusInput)
    (hcyc : GGL46CyclicInput) : GGL46CoreInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS
  have hcfg := ggL45Config_of_setup hS
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hp := hcfg.prime
  obtain ⟨hab, s, hs, hexp, hord, x', hx'x, hact⟩ := ggL46_torus hraw hcen hiso hcent htorus hS
  have habU : IsMulCommutative U₁ := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  obtain ⟨g₀, hg₀, hcycU⟩ := hcyc G p B Bs x L D J X B₂ d y K U U₁ hS
  obtain ⟨hΩU, hΩ₁⟩ := ggL46_omega_of_cyclic hraw hiso hcfg hab hs hexp hx'x hact hg₀ hcycU
  have hcard := ggL46_card_le_of_cyclic hS habU hs hexp hx'x hact hΩU hΩ₁ hg₀ hcycU
  have hOU₁ : ggPowSubgroup U₁ habU (p ^ (s - 1)) ≤ U₁ := by
    rintro _ ⟨u, hu, rfl⟩
    exact U₁.pow_mem hu _
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp ((hcfg.isPGroup.to_le hcfg.part_le).to_le hOU₁)
  obtain ⟨H, hHU₁, hHcard, hHB₁⟩ := exists_ggHomocyclic hp (by omega) habU hexp hΩ₁ hr
  refine ⟨habU, ⟨s, hs, hexp, hord, ⟨x', hx'x, hact⟩, H, r, hHU₁, fun h hh => hexp h (hHU₁ hh),
    hHcard, hHB₁, ?_⟩, hΩ₁, hΩU⟩
  rw [hr] at hcard
  rw [pow_succ, mul_comm]
  exact hcard

theorem ggL46Input_of_torus (h43 : GGL43Input) (hraw : GGRawInnFieldInput)
    (hcen : GGRawFieldCentralInput) (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput)
    (htorus : GGL45TorusInput) (hcyc : GGL46CyclicInput) : GGL46Input :=
  ggL46Input_of_core h43 (ggL46CoreInput_of_torus hraw hcen hiso hcent htorus hcyc) hcyc

end CFSG.StandardType

end
