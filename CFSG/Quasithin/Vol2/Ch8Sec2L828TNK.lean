module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828J
public import CFSG.Fischer.Classification.Recognition.PSU6

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section NK

variable {G : Type} [Group G] [Finite G]

theorem s828N_K (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (hcard : Mathieu.StmtH13Card)
    (hLU : HLU82) (h825 : Stmt8_2_5) (h827 : Step827)
    {T L I H : Subgroup G} {h : G} {k : ℕ} (hyp : Hyp7_0_2 G T L I) (h731 : Hyp7_3_1 T L I)
    (h821 : Hyp8_2_1 T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I)
    (hH : IsHStar T (fsuM T L) H) (hh : h ∈ H) (hC : Concl822 T L I H h k) :
    ∃ K : Subgroup G, ch82LU L (ch82U (fsuV T I) h) ≤ K ∧
      K ≤ Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ∧
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
      CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧
      ⁅K, Subgroup.centralizer (ch82U (fsuV T I) h : Set G)⁆ ≤ pCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  obtain ⟨hV, hL0, hTL, hLN, -, hAN, hAL, hAp, hAe, hTU, hIU, hU1, hLUT⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨hfam, hLUC, -⟩ :=
    lu_facts_828 hLU hcard hyp hrow hC5 hV hL0 hTL hLN hAN hAL hAp hAe hLUT
  have hU2 : IsPGroup 2 ↥(ch82U (fsuV T I) h) := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hV.2 _ x.2.1)⟩
  have hLUU : ch82LU L (ch82U (fsuV T I) h) ≤
      Subgroup.normalizer (ch82U (fsuV T I) h : Set G) :=
    (perfectCore_le _).trans inf_le_right
  obtain ⟨K, hK, hLUK, hKn⟩ := exists_k_828 h37 h38 h39 hyp hU2 hU1 hTU hLUU hfam hLUT
  have hq := h827 G T L I hyp h731 h821 hc hrow H h k hH hh hC K hK hLUK
  have hKle := le_of_mem_cComp hK
  have hKn' := (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mp hKn
  have hXC : ¬ K ≤ Subgroup.centralizer (ch82U (fsuV T I) h : Set G) := fun hKC =>
    hLUC (hLUK.trans hKC)
  exact ⟨K, hLUK, hKle, hKn', hq, commutator_centralizer_le_828 hKle hKn' hK.2.1 hq hXC⟩

theorem s828N_no_three {U K : Subgroup G} {y : G}
    (hrank : CFSG.Open.pRank 3 (Subgroup.normalizer (U : Set G)) ≤ 2)
    (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hnc : ∀ S : Sylow 3 ↥K, ¬ IsCyclic (S : Subgroup ↥K))
    (hyU : y ∈ Subgroup.normalizer (U : Set G)) (hyK : y ∈ Subgroup.normalizer (K : Set G))
    (hy3 : y ^ 3 = 1) (hyc : ∀ x ∈ K, ⁅x, y⁆ ∈ pCoreOf 2 K) (hyn : y ∉ K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥(Subgroup.zpowers y) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hy3, one_zpow]
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_normalized_828 (p := 3) (K := K) hBp
    (Subgroup.zpowers_le.mpr hyK)
  have hO2 : IsPGroup 2 ↥((pCoreOf 2 K).subgroupOf K) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_of_injective K.subtype K.subtype_injective
  have hcent : ∀ q : ↥K, q ∈ (Q₀ : Subgroup ↥K) → Commute (q : G) y := by
    intro q hq
    obtain ⟨q', hq', hq'e⟩ := hQ₀ _ (Subgroup.mem_zpowers _) q hq
    have hc1 : q⁻¹ * q' ∈ (Q₀ : Subgroup ↥K) := mul_mem (inv_mem hq) hq'
    have hc2 : ((q⁻¹ * q' : ↥K) : G) ∈ pCoreOf 2 K := by
      have e : ((q⁻¹ * q' : ↥K) : G) = ⁅(q : G)⁻¹, y⁆ := by
        rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hq'e, inv_inv]
        group
      rw [e]
      exact hyc _ (K.inv_mem q.2)
    have hdis := IsPGroup.disjoint_of_ne 3 2 (by norm_num) (Q₀ : Subgroup ↥K)
      ((pCoreOf 2 K).subgroupOf K) Q₀.isPGroup' hO2
    have hc : q⁻¹ * q' = 1 :=
      Subgroup.disjoint_def.mp hdis hc1 (Subgroup.mem_subgroupOf.mpr hc2)
    have hqq : q' = q := (inv_mul_eq_one.mp hc).symm
    rw [hqq] at hq'e
    show (q : G) * y = y * q
    calc (q : G) * y = y * q * y⁻¹ * y := by rw [← hq'e]
      _ = y * q := by group
  have : Fact (IsPGroup 3 ↥(Q₀ : Subgroup ↥K)) := ⟨Q₀.isPGroup'⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (by norm_num : (3 : ℕ) ≠ 2) (hnc Q₀)
  set E : Subgroup G := (S.map (Q₀ : Subgroup ↥K).subtype).map K.subtype with hEdef
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [hEdef, Subgroup.card_map_of_injective K.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hScard]
  have hEK : E ≤ K := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hmemE : ∀ e ∈ E, ∃ s ∈ S, e = (((s : ↥(Q₀ : Subgroup ↥K)) : ↥K) : G) := by
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  have hS3 : ∀ s ∈ S, s ^ 3 = 1 := fun s hs => by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hSel.exponent_dvd_p ⟨s, hs⟩
    exact congrArg Subtype.val h
  have hE : CFSG.Open.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun e he => ?_⟩
    · obtain ⟨s, hs, hse⟩ := hmemE a a.2
      obtain ⟨t, ht, hte⟩ := hmemE b b.2
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hse, hte]
      have hst : (⟨s, hs⟩ : ↥S) * ⟨t, ht⟩ = ⟨t, ht⟩ * ⟨s, hs⟩ := mul_comm _ _
      have := congrArg (fun x : ↥S => (((x : ↥(Q₀ : Subgroup ↥K)) : ↥K) : G)) hst
      simpa using this
    · obtain ⟨s, hs, rfl⟩ := hmemE e he
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, hS3 s hs]
      rfl
  have hbc : ∀ e ∈ E, Commute e y := by
    intro e he
    obtain ⟨s, -, rfl⟩ := hmemE e he
    exact hcent _ s.2
  have h3 := succ_le_pRank_of_commute_828 Nat.prime_three hE hEcard hbc hy3
    (fun hyE => hyn (hEK hyE)) (hEK.trans hKU) hyU
  omega

end NK

end CFSG.Quasithin.H13
