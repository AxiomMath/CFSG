module

public import CFSG.Quasithin.H13.L32AC30a
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverClassical
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

section Generic

theorem odd_card_center_of_pCore_eq_bot {X : Type*} [Group X] [Finite X]
    (h : CFSG.pCore 2 X = ⊥) : Odd (Nat.card (Subgroup.center X)) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card (Subgroup.center X) := by
    rw [Nat.not_odd_iff_even] at hne
    exact even_iff_two_dvd.1 hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 2 h2
  have hzc : Subgroup.zpowers (z : X) ≤ Subgroup.center X :=
    (Subgroup.zpowers_le (H := Subgroup.center X)).mpr z.2
  have hN : (Subgroup.zpowers (z : X)).Normal := Subgroup.normal_of_le_center hzc
  have hzo : orderOf (z : X) = 2 := by rw [Subgroup.orderOf_coe, hz]
  have hP : IsPGroup 2 (Subgroup.zpowers (z : X)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  have hle : Subgroup.zpowers (z : X) ≤ CFSG.pCore 2 X := le_sSup ⟨hN, hP⟩
  rw [h, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  rw [hle, orderOf_one] at hzo
  exact absurd hzo (by norm_num)

theorem center_eq_bot_of_psl_two
    {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X) {n : ℕ}
    (h : IsPSL n 2 1 (X ⧸ Subgroup.center X)) (hodd : Odd (Nat.card (Subgroup.center X))) :
    Subgroup.center X = ⊥ := by
  have := hperf
  obtain ⟨⟨-, -, hn, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := h
  have hF2 : Nat.card F = 2 := by rw [hF, pow_one]
  have : CharP F 2 := CFSG.SectionRank.charP_two_of_card hF
  obtain ⟨φ, -, -, hD⟩ := CFSG.QuasithinUnique.Ch1.exists_cover_map_of_odd_splitting hodd e
    fun E _ _ π hπ hC hodd' => by
      obtain ⟨s, hs, -⟩ :=
        CFSG.SectionRank.EvenCover.even_linear_central_odd_extension_splitting_stated hn hπ hC
          hodd'
      exact ⟨s, hs⟩
  have hbot : (Assembly.LowTwoRank.StatedScalars (Fin n) F).subgroupOf
      (Assembly.LowTwoRank.StatedSL n F) = ⊥ := by
    classical
    have : Fintype F := Fintype.ofFinite F
    have hunit : Subsingleton Fˣ := by
      have h1 : Fintype.card Fˣ = 1 := by
        rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hF2]
      exact Fintype.card_le_one_iff_subsingleton.mp h1.le
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨c, hc⟩ := hx
    rw [Subsingleton.elim c 1, map_one] at hc
    rw [Subgroup.mem_bot]
    exact Subtype.ext hc.symm
  rw [← hD, hbot, Subgroup.map_bot]

theorem center_eq_bot_of_psu_three_three {X : Type} [Group X] [Finite X]
    (hperf : Group.IsPerfect X) (h : IsPSU 3 3 1 (X ⧸ Subgroup.center X))
    (hodd : Odd (Nat.card (Subgroup.center X))) : Subgroup.center X = ⊥ := by
  have := hperf
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 3 := charP_of_card_eq_prime_pow (f := 2) (by
    rw [← Nat.card_eq_fintype_card, hF]
    ring)
  have hsplit : ∀ q : ℕ, q = 3 → ∀ (E : Type) [Group E] [Finite E]
      (π : E →* Assembly.LowTwoRank.StatedSU 3 q F), Function.Surjective π →
      π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) →
      ∃ s : Assembly.LowTwoRank.StatedSU 3 q F →* E, ∀ g, π (s g) = g := by
    rintro q rfl E _ _ π hπ hC hodd'
    obtain ⟨⟨s, hs, -⟩, -⟩ :=
      CFSG.SectionRank.OddCover.prime_classical_three_central_odd_extension_splitting
        Nat.prime_three (by norm_num) (Or.inr ⟨rfl, by rw [hF, pow_one], rfl⟩) π hπ hC hodd'
    exact ⟨s, fun g => DFunLike.congr_fun hs g⟩
  obtain ⟨φ, -, -, hD⟩ := CFSG.QuasithinUnique.Ch1.exists_cover_map_of_odd_splitting hodd e
    (hsplit (3 ^ 1) (pow_one 3))
  have h3 := CFSG.QuasithinUnique.Ch1.card_scalars_dvd_three (F := F) (p := 3) (f := 1)
    (H := Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) F) (Or.inr ⟨hF, rfl⟩)
  have h4 := CFSG.QuasithinUnique.Ch1.card_scalars_statedSU_dvd_succ (F := F) (p := 3) (f := 1)
    hF (by norm_num)
  have h1 : Nat.card ((Assembly.LowTwoRank.StatedScalars (Fin 3) F).subgroupOf
      (Assembly.LowTwoRank.StatedSU 3 (3 ^ 1) F)) = 1 := by
    have h5 := Nat.dvd_gcd h3 h4
    rw [show Nat.gcd 3 (3 ^ 1 + 1) = 1 by norm_num, Nat.dvd_one] at h5
    exact h5
  rw [← hD, Subgroup.card_eq_one.mp h1, Subgroup.map_bot]

end Generic

section Ambient

variable {G : Type} [Group G]

noncomputable def cStarEquiv (K : Subgroup G) : cStar K ≃* ↥K ⧸ CFSG.pCore 2 ↥K :=
  QuotientGroup.quotientMulEquivOfEq (subgroupOf_pCoreOf_eq_pCore K)

theorem pCore_cStar_eq_bot (K : Subgroup G) : CFSG.pCore 2 (cStar K) = ⊥ := by
  have h := CFSG.pCore_map_iso 2 (cStarEquiv K)
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at h
  rw [← Subgroup.map_eq_bot_iff_of_injective _ (f := (cStarEquiv K).toMonoidHom)
    (cStarEquiv K).injective]
  exact h

variable [Finite G]

theorem odd_card_center_cStar (K : Subgroup G) : Odd (Nat.card (Subgroup.center (cStar K))) :=
  odd_card_center_of_pCore_eq_bot (pCore_cStar_eq_bot K)

theorem card_center_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (Subgroup.center X) = Nat.card (Subgroup.center Y) := by
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]

variable {T L V H : Subgroup G}

theorem card_center_cStar_dvd_three (h28 : Lemma14_7_28) (S : Setting147 G T L V H)
    (hL3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3) {K : Subgroup G}
    (hK : K ∈ cComp H) : Nat.card (Subgroup.center (cStar K)) ∣ 3 := by
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  set Kb := modO2Image H K with hKb
  have hcard : Nat.card (Subgroup.center (cStar K)) = Nat.card (Subgroup.center ↥Kb) :=
    card_center_eq_of_mulEquiv ((cStarEquiv K).trans e)
  set Z := Subgroup.center ↥Kb with hZ
  have hKbs : Kb.IsSubnormal := A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
  have hZn : ((Z.map Kb.subtype).subgroupOf Kb).Normal := by
    rw [map_subtype_subgroupOf']
    infer_instance
  have hZs : (Z.map Kb.subtype).IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le Z) hKbs hZn
  have hZc : Nat.card (Z.map Kb.subtype) = Nat.card Z :=
    Subgroup.card_map_of_injective Kb.subtype_injective
  have hodd : Odd (Nat.card (Z.map Kb.subtype)) := by
    rw [hZc, ← hcard]
    exact odd_card_center_cStar K
  have hle := le_oddCore_of_isSubnormal hZs hodd
  rw [hcard, ← hZc]
  rcases h28 G T L V H S with h0 | h1
  · rw [h0, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot]
    exact one_dvd 3
  · rw [h1] at hle
    have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
    have hoddL : Odd (Nat.card (modO2Image H (l1 T L V))) := h1 ▸ odd_card_oddCore
    exact (Subgroup.card_dvd_of_le hle).trans (card_modO2Image_dvd_three hL1H hL3 hoddL)

end Ambient

end CFSG.Quasithin.H13.L32A.C
