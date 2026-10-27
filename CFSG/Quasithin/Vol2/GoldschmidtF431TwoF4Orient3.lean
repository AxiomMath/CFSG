module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Defs
public import CFSG.Quasithin.Vol2.GoldschmidtF431TS3Std
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Base

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Quasithin
  CFSG.LocalAnalysis.EvenBN.TwoF4 CFSG.Quasithin.H13.Sec53F.ReeF4
open CFSG.LieType.Ree.LargeReeCover (pairedTorusHom f4i)
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Subtype

variable {G : Type*} [Group G] (Γ : Subgroup G) (x : ↥Γ)

theorem map_subtype_centralizer_singleton :
    (Subgroup.centralizer ({x} : Set ↥Γ)).map Γ.subtype =
      Γ ⊓ Subgroup.centralizer ({(x : G)} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.coe_subtype]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, congrArg Subtype.val hg⟩
  · rintro ⟨hy, hc⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hc, rfl⟩

theorem card_centralizer_subtype :
    Nat.card ↥(Subgroup.centralizer ({x} : Set ↥Γ)) =
      Nat.card ↥(Γ ⊓ Subgroup.centralizer ({(x : G)} : Set G)) := by
  rw [← map_subtype_centralizer_singleton, Subgroup.card_map_of_injective Γ.subtype_injective]

theorem card_commutator_centralizer_subtype :
    Nat.card ↥⁅Subgroup.centralizer ({x} : Set ↥Γ), Subgroup.centralizer ({x} : Set ↥Γ)⁆ =
      Nat.card ↥⁅Γ ⊓ Subgroup.centralizer ({(x : G)} : Set G),
        Γ ⊓ Subgroup.centralizer ({(x : G)} : Set G)⁆ := by
  rw [← map_subtype_centralizer_singleton, ← Subgroup.map_commutator,
    Subgroup.card_map_of_injective Γ.subtype_injective]

end Subtype

section Generic

theorem two_pow_odd_mod_three (a : ℕ) : 2 ^ (2 * a + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem not_three_dvd_order_centralizer_z (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 12 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq := two_pow_odd_mod_three a
  generalize 2 ^ (2 * a + 1) = q at hq ⊢
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h | h
    · have := Nat.prime_three.dvd_of_dvd_pow h
      omega
    · omega
  · have h2 : (q ^ 2 + 1) % 3 = 2 := by
      rw [Nat.add_mod, Nat.pow_mod, hq]
    omega

theorem three_dvd_order_SL2 (a : ℕ) : 3 ∣ 2 ^ (2 * a + 1) * ((2 ^ (2 * a + 1)) ^ 2 - 1) := by
  have hq := two_pow_odd_mod_three a
  apply Dvd.dvd.mul_left
  have h2 : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq]
  have h1 : 1 ≤ (2 ^ (2 * a + 1)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  generalize (2 ^ (2 * a + 1)) ^ 2 = s at h1 h2 ⊢
  omega

theorem commutator_eq_self_of_simple {G : Type*} [Group G] (R : Subgroup G) [IsSimpleGroup ↥R]
    (hn : ∃ x y : ↥R, x * y ≠ y * x) : ⁅R, R⁆ = R := by
  have hW : ⁅(⊤ : Subgroup ↥R), (⊤ : Subgroup ↥R)⁆ = ⊤ := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup ↥R) ⊤).eq_bot_or_eq_top with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hn
      apply hxy
      have hmem : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup ↥R), (⊤ : Subgroup ↥R)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  have h2 : ⁅R, R⁆ = Subgroup.map R.subtype ⁅(⊤ : Subgroup ↥R), (⊤ : Subgroup ↥R)⁆ := by
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h2, hW, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Generic

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem centralizer_zg_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.centralizer ({zg hK} : Set (Gm K a)) ≤ Pg K a ⟨1, by decide⟩ := by
  intro x hx
  have hz : ((zg hK : Gm K a) : ModGL F4.tag K) = centralZ K a 1 :=
    (invE_eq_centralZ (K := K) (a := a)).1
  have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hz] at h1
  have hx' : (x : ModGL F4.tag K) ∈ F4.reeGamma K a ⊓ Subgroup.centralizer
      ({centralZ K a 1} : Set (ModGL F4.tag K)) :=
    Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 h1⟩
  exact Subgroup.mem_subgroupOf.2 (reeGamma_inf_centralizer_le_reeLocalParabolic ha hK hx')

theorem centralizer_tg_le (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.centralizer ({tg hK} : Set (Gm K a)) ≤ Pg K a ⟨0, by decide⟩ := by
  intro x hx
  have ht : ((tg hK : Gm K a) : ModGL F4.tag K) = sylowL a K 1 :=
    (invE_eq_centralZ (K := K) (a := a)).2
  have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hx)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ht] at h1
  have hx' : (x : ModGL F4.tag K) ∈ F4.reeGamma K a ⊓ Subgroup.centralizer
      ({sylowL a K 1} : Set (ModGL F4.tag K)) :=
    Subgroup.mem_inf.2 ⟨x.2, Subgroup.mem_centralizer_singleton_iff.2 h1⟩
  exact Subgroup.mem_subgroupOf.2 (reeGamma_inf_centralizer_tOne_le hK hx')

section Weyl

theorem not_centralizer_zg_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ Subgroup.centralizer ({zg hK} : Set (Gm K a)) ≤ Pg K a ⟨0, by decide⟩ := by
  intro hle
  obtain ⟨-, ⟨h1eq, hn1, -⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hnR := h1eq ▸ hn1
  have hnΓ : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨1, by decide⟩) ∈
      F4.reeGamma K a := rankOneGroupTwo_le_reeGamma hK hnR
  have hnc := rankOneGroupTwo_le_centralizer ha hK 1 hnR
  have hz : ((zg hK : Gm K a) : ModGL F4.tag K) = centralZ K a 1 :=
    (invE_eq_centralZ (K := K) (a := a)).1
  have hx : (⟨_, hnΓ⟩ : Gm K a) ∈ Subgroup.centralizer ({zg hK} : Set (Gm K a)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact Subgroup.mem_centralizer_singleton_iff.1 hnc
  have hmem := Subgroup.mem_subgroupOf.1 (hle hx)
  rw [← reeParabolic_singleton, canonicalRep_mem_reeParabolic_iff] at hmem
  exact absurd (congrArg Fin.val (Set.mem_singleton_iff.1 hmem)) (by decide)

theorem not_centralizer_tg_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ Subgroup.centralizer ({tg hK} : Set (Gm K a)) ≤ Pg K a ⟨1, by decide⟩ := by
  intro hle
  obtain ⟨⟨h0eq, hn0, -⟩, -⟩ :=
    CFSG.QuasithinUnique.Setup.X6.large_Ree_opposite_simple_blocks_generate_rank_one_model ha hK
  have hnR := h0eq ▸ hn0
  have hnΓ : canonicalRep (coxeterSystem F4.tag) K (F4.fixedOrbitElement ⟨0, by decide⟩) ∈
      F4.reeGamma K a := rankOneGroupOne_le_reeGamma hK hnR
  have hnc := rankOneGroupOne_le_centralizer_sylowL 1 hnR
  have ht : ((tg hK : Gm K a) : ModGL F4.tag K) = sylowL a K 1 :=
    (invE_eq_centralZ (K := K) (a := a)).2
  have hx : (⟨_, hnΓ⟩ : Gm K a) ∈ Subgroup.centralizer ({tg hK} : Set (Gm K a)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ht]
    exact Subgroup.mem_centralizer_singleton_iff.1 hnc
  have hmem := Subgroup.mem_subgroupOf.1 (hle hx)
  rw [← reeParabolic_singleton, canonicalRep_mem_reeParabolic_iff] at hmem
  exact absurd (congrArg Fin.val (Set.mem_singleton_iff.1 hmem)) (by decide)

end Weyl

section Zperf

variable (K a) in
@[expose] def scalZ : Subgroup (ModGL F4.tag K) where
  carrier := {g | ∃ μ : K, μ ≠ 0 ∧ ∀ c : K, g * centralZ K a c * g⁻¹ = centralZ K a (μ * c)}
  one_mem' := ⟨1, one_ne_zero, fun c => by simp⟩
  mul_mem' := by
    rintro g h ⟨μ, hμ, hg⟩ ⟨ν, hν, hh⟩
    refine ⟨μ * ν, mul_ne_zero hμ hν, fun c => ?_⟩
    calc g * h * centralZ K a c * (g * h)⁻¹ = g * (h * centralZ K a c * h⁻¹) * g⁻¹ := by group
      _ = centralZ K a (μ * ν * c) := by rw [hh, hg, mul_assoc]
  inv_mem' := by
    rintro g ⟨μ, hμ, hg⟩
    refine ⟨μ⁻¹, inv_ne_zero hμ, fun c => ?_⟩
    have h := hg (μ⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hμ, one_mul] at h
    rw [inv_inv]
    calc g⁻¹ * centralZ K a c * g = g⁻¹ * (g * centralZ K a (μ⁻¹ * c) * g⁻¹) * g := by rw [h]
      _ = centralZ K a (μ⁻¹ * c) := by group

theorem commutator_scalZ_commute {g h : ModGL F4.tag K} (hg : g ∈ scalZ K a) (hh : h ∈ scalZ K a)
    (c : K) : ⁅g, h⁆ * centralZ K a c = centralZ K a c * ⁅g, h⁆ := by
  have hinv : ∀ {g : ModGL F4.tag K} {μ : K}, μ ≠ 0 →
      (∀ c : K, g * centralZ K a c * g⁻¹ = centralZ K a (μ * c)) → ∀ c : K,
        g⁻¹ * centralZ K a c * g = centralZ K a (μ⁻¹ * c) := by
    intro g μ hμ hg c
    have h := hg (μ⁻¹ * c)
    rw [← mul_assoc, mul_inv_cancel₀ hμ, one_mul] at h
    calc g⁻¹ * centralZ K a c * g = g⁻¹ * (g * centralZ K a (μ⁻¹ * c) * g⁻¹) * g := by rw [h]
      _ = centralZ K a (μ⁻¹ * c) := by group
  obtain ⟨μ, hμ, hg⟩ := hg
  obtain ⟨ν, hν, hh⟩ := hh
  have key : ⁅g, h⁆ * centralZ K a c * ⁅g, h⁆⁻¹ = centralZ K a c := by
    have e : ⁅g, h⁆ * centralZ K a c * ⁅g, h⁆⁻¹ =
        g * (h * (g⁻¹ * (h⁻¹ * centralZ K a c * h) * g) * h⁻¹) * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, hinv hν hh, hinv hμ hg, hh, hg]
    congr 1
    field_simp
  calc ⁅g, h⁆ * centralZ K a c = (⁅g, h⁆ * centralZ K a c * ⁅g, h⁆⁻¹) * ⁅g, h⁆ := by group
    _ = centralZ K a c * ⁅g, h⁆ := by rw [key]

theorem reeLocalParabolic_one_le_scalZ (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeLocalParabolic K a ⟨1, by decide⟩ ≤ scalZ K a := by
  intro g hg
  obtain ⟨t, ⟨u, rfl⟩, s, hs, rfl⟩ := exists_mul_of_mem_reeLocalParabolic hK hg
  refine ⟨(u : K) ^ 2 ^ a, pow_ne_zero _ u.ne_zero, fun c => ?_⟩
  have hsc : s * centralZ K a c = centralZ K a c * s :=
    Subgroup.mem_centralizer_singleton_iff.1 (centralizerZ_le_centralizer ha hK c hs)
  have hτ := torusPair_conj_centralZ (a := a) hK u 1 c
  rw [rankOneTorusPair_left] at hτ
  rw [← hτ]
  calc pairedTorusHom a (f4i 0) (f4i 3) u * s * centralZ K a c *
        (pairedTorusHom a (f4i 0) (f4i 3) u * s)⁻¹ =
      pairedTorusHom a (f4i 0) (f4i 3) u * (s * centralZ K a c * s⁻¹) *
        (pairedTorusHom a (f4i 0) (f4i 3) u)⁻¹ := by group
    _ = _ := by rw [hsc]; group

theorem perfectCore_one_commute_centralZ (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : ModGL F4.tag K} (hg : g ∈ perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩))
    (c : K) : g * centralZ K a c = centralZ K a c * g := by
  have h1 : perfectCore (F4.reeLocalParabolic K a ⟨1, by decide⟩) ≤
      ⁅F4.reeLocalParabolic K a ⟨1, by decide⟩, F4.reeLocalParabolic K a ⟨1, by decide⟩⁆ :=
    perfectCore_le_derivedSeriesOf _ 1
  have h2 := Subgroup.commutator_mono (reeLocalParabolic_one_le_scalZ ha hK)
    (reeLocalParabolic_one_le_scalZ ha hK)
  have h3 : ⁅scalZ K a, scalZ K a⁆ ≤ Subgroup.centralizer {centralZ K a c} :=
    Subgroup.commutator_le.2 fun g hg h hh => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact commutator_scalZ_commute hg hh c
  exact Subgroup.mem_centralizer_singleton_iff.mp (h3 (h2 (h1 hg)))

theorem zg_mem_centerOf_perfectCore (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    zg hK ∈ centerOf (perfectCore (Pg K a ⟨1, by decide⟩)) := by
  have hz : ((zg hK : Gm K a) : ModGL F4.tag K) = centralZ K a 1 :=
    (invE_eq_centralZ (K := K) (a := a)).1
  refine ⟨?_, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
  · exact (mem_perfectCore_subgroupOf (reeLocalParabolic_le_reeGamma _) (zg hK)).2
      (reeFixedPosUnipotent_le_perfectCore_one ha hK (Subgroup.mem_subgroupOf.1 (zg_mem_Ug hK)))
  · have hg' := (mem_perfectCore_subgroupOf (reeLocalParabolic_le_reeGamma _) g).1 hg
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact perfectCore_one_commute_centralZ ha hK hg' 1

end Zperf

section Orders

theorem three_not_dvd_card_centralizer_zg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer ({zg hK} : Set (Gm K a))) := by
  have hz : ((zg hK : Gm K a) : ModGL F4.tag K) = centralZ K a 1 :=
    (invE_eq_centralZ (K := K) (a := a)).1
  rw [card_centralizer_subtype (F4.reeGamma K a) (zg hK), hz]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcard, -, -⟩ :=
    large_Ree_two_involution_centralizers a ha K hK
  rw [hcard]
  exact not_three_dvd_order_centralizer_z a

theorem three_dvd_card_commutator_centralizer_tg (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    3 ∣ Nat.card ↥⁅Subgroup.centralizer ({tg hK} : Set (Gm K a)),
      Subgroup.centralizer ({tg hK} : Set (Gm K a))⁆ := by
  have ht : ((tg hK : Gm K a) : ModGL F4.tag K) = sylowL a K 1 :=
    (invE_eq_centralZ (K := K) (a := a)).2
  rw [card_commutator_centralizer_subtype (F4.reeGamma K a) (tg hK), ht]
  have hsimple := isSimpleGroup_rankOneGroupOne ha hK
  have : IsSimpleGroup ↥(rankOneGroupOne K a) := hsimple.1
  have hle : rankOneGroupOne K a ≤ F4.reeGamma K a ⊓ Subgroup.centralizer {sylowL a K 1} :=
    le_inf (rankOneGroupOne_le_reeGamma hK) (rankOneGroupOne_le_centralizer_sylowL 1)
  have hdvd := Subgroup.card_dvd_of_le (Subgroup.commutator_mono hle hle)
  rw [commutator_eq_self_of_simple (rankOneGroupOne K a) hsimple.2, card_rankOneGroupOne hK] at hdvd
  exact dvd_trans (three_dvd_order_SL2 a) hdvd

end Orders

theorem stdOrient3_twoF4 (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Lift.StdOrient3 (Gm K a) (Pg K a ⟨1, by decide⟩) (Pg K a ⟨0, by decide⟩) (zg hK) (tg hK) where
  cz := centralizer_zg_le ha hK
  ct := centralizer_tg_le hK
  nz := not_centralizer_zg_le ha hK
  nt := not_centralizer_tg_le ha hK
  Zperf := zg_mem_centerOf_perfectCore ha hK
  F1 := three_not_dvd_card_centralizer_zg ha hK
  F2 := three_dvd_card_commutator_centralizer_tg ha hK

end CFSG.Quasithin.H13.F431.TwoF4
