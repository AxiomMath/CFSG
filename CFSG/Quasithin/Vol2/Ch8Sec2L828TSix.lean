module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TNC
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TStep3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section Six

variable {G : Type} [Group G] [Finite G]

theorem s828_no_dihedral3 (hLU : HLU82) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hyp : Hyp7_0_2 G T L I) (hrow : Case8_2 T L I) (hr : Row711M24Code T L I)
    (c : S828Ctx T L I H h k) :
    ¬ Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 3) := by
  classical
  rintro ⟨eI⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set V := fsuV T I with hVdef
  set J := ch82I V h with hJdef
  set P := pCoreOf 2 J with hPdef
  set U := ch82U V h with hUdef
  set LU := ch82LU L U with hLUdef
  have hmo : Odd 3 := by decide
  have h3m : 3 ∣ 3 := dvd_rfl
  have hkerI : kerIn (fsuM T L ⊓ J) J = P := by
    obtain ⟨-, -, -, -, -, -, -, hkerI, -⟩ := id c.hC
    exact hkerI
  have hJ2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hkerJ : ∀ x : ↥J, QuotientGroup.mk' ((kerIn (fsuM T L ⊓ J) J).subgroupOf J) x = 1 ↔
      (x : G) ∈ P := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hkerI]
  have hhI : h ∈ J := c.hhI
  have hVP : ¬ V ≤ P := by
    intro hVle
    have hhP : h ∈ Subgroup.normalizer (P : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hhI
    have hJle : J ≤ P := by
      refine sup_le hVle fun x hx => ?_
      rw [B6.mem_conjSub] at hx
      have := (Subgroup.mem_normalizer_iff.mp hhP _).mp (hVle hx)
      simpa [mul_assoc] using this
    have htriv : ∀ q : E2.StarQuot (fsuM T L ⊓ J) J, q = 1 := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (fsuM T L ⊓ J) J).subgroupOf J) q
      exact (hkerJ x).mpr (hJle x.2)
    have hc1 : Nat.card (E2.StarQuot (fsuM T L ⊓ J) J) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (htriv a).trans (htriv b).symm⟩, ⟨1⟩⟩
    have hc2 := Nat.card_congr eI.toEquiv
    rw [DihedralGroup.nat_card, hc1] at hc2
    omega
  obtain ⟨v, hvV, hvP⟩ := Set.not_subset.mp hVP
  let v' : ↥J := ⟨v, (le_sup_left : V ≤ J) hvV⟩
  have hv2 : v' ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hV.2 _ hvV)
  obtain ⟨y', hy3', hyv⟩ := exists_y_828 (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) hJ2 hkerJ hmo h3m eI hvP hv2
  have hy3 : (y' : G) ^ 3 = 1 := by
    have := congrArg Subtype.val hy3'
    simpa using this
  have hLUU : LU ≤ Subgroup.normalizer (U : Set G) := (perfectCore_le _).trans inf_le_right
  have hyU : (y' : G) ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      rw [c.hcen n hn y' y'.2]
      exact hn
    · intro hn
      have := c.hcen _ hn (y' : G)⁻¹ (J.inv_mem y'.2)
      have e : (y' : G)⁻¹ * ((y' : G) * n * (y' : G)⁻¹) * (y' : G)⁻¹⁻¹ = n := by group
      rw [e] at this
      rw [this]
      exact hn
  have hyLU : (y' : G) ∉ LU := by
    intro hy
    apply hyv
    have h1 : ⁅v, (y' : G)⁆ ∈ P :=
      c.hILU (Subgroup.commutator_mem_commutator ((le_sup_left : V ≤ J) hvV) hy)
    have e : ((y' * v' * y'⁻¹ * v'⁻¹ : ↥J) : G) = (⁅v, (y' : G)⁆)⁻¹ := by
      have hv'c : ((v' : ↥J) : G) = v := rfl
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv,
        hv'c]
      group
    rw [e]
    exact P.inv_mem h1
  have hyN : (y' : G) ∈ Subgroup.normalizer (LU : Set G) := c.hIN y'.2
  have hBp : IsPGroup 3 ↥(Subgroup.zpowers (y' : G)) := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hy3, one_zpow]
  obtain ⟨Q₀, hQ₀⟩ := exists_sylow_normalized_828 (p := 3) (K := LU) hBp
    (Subgroup.zpowers_le.mpr hyN)
  have hO2 : IsPGroup 2 ↥((pCoreOf 2 LU).subgroupOf LU) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LU).comap_of_injective LU.subtype
      LU.subtype_injective
  have hcent : ∀ q : ↥LU, q ∈ (Q₀ : Subgroup ↥LU) → Commute (q : G) (y' : G) := by
    intro q hq
    obtain ⟨q', hq', hq'e⟩ := hQ₀ _ (Subgroup.mem_zpowers _) q hq
    have hc1 : q⁻¹ * q' ∈ (Q₀ : Subgroup ↥LU) := mul_mem (inv_mem hq) hq'
    have hc2 : ((q⁻¹ * q' : ↥LU) : G) ∈ pCoreOf 2 LU := by
      have e : ((q⁻¹ * q' : ↥LU) : G) = ⁅(q : G)⁻¹, (y' : G)⁆ := by
        rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hq'e, inv_inv]
        group
      rw [e]
      exact c.hcomm (Subgroup.commutator_mem_commutator (LU.inv_mem q.2) y'.2)
    have hdis := IsPGroup.disjoint_of_ne 3 2 (by norm_num) (Q₀ : Subgroup ↥LU)
      ((pCoreOf 2 LU).subgroupOf LU) Q₀.isPGroup' hO2
    have hc : q⁻¹ * q' = 1 :=
      Subgroup.disjoint_def.mp hdis hc1 (Subgroup.mem_subgroupOf.mpr hc2)
    have hqq : q' = q := (inv_mul_eq_one.mp hc).symm
    rw [hqq] at hq'e
    show (q : G) * y' = y' * q
    calc (q : G) * y' = y' * q * (y' : G)⁻¹ * y' := by rw [← hq'e]
      _ = y' * q := by group
  have hAp : IsPGroup 2 ↥(ch82A V h) := B6.isPGroup_of_isElemAbelian c.hAe
  have hX6 := (hlu82_82 hLU hcard hrow c.hL0 c.hV c.hLN c.hC5 c.hAN c.hAL hAp c.hAe).2.2.1 hr
  have hU2 : IsPGroup 2 ↥U := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact c.hV.2 _ x.2.1)⟩
  have hU16 : Nat.card ↥U = 16 := by
    obtain ⟨n, hn⟩ := hU2.exists_card_eq
    have hrk : rk ↥U = 4 := (c.hC5.2.2.2.2.2.1 hr).2.2.2
    have hn4 : n = 4 := by
      rw [← hrk]
      unfold rk
      rw [hn, padicValNat.prime_pow]
    rw [hn, hn4]
    norm_num
  have hnc : ¬ IsCyclic ↥(Q₀ : Subgroup ↥LU) := s828_sylow3_noncyclic c hX6 hU16 Q₀
  have : Fact (IsPGroup 3 ↥(Q₀ : Subgroup ↥LU)) := ⟨Q₀.isPGroup'⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (by norm_num : (3 : ℕ) ≠ 2) hnc
  set E : Subgroup G := (S.map (Q₀ : Subgroup ↥LU).subtype).map LU.subtype with hEdef
  have hEcard : Nat.card E = 3 ^ 2 := by
    rw [hEdef, Subgroup.card_map_of_injective LU.subtype_injective,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hScard]
  have hELU : E ≤ LU := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hmemE : ∀ e ∈ E, ∃ s ∈ S, e = (((s : ↥(Q₀ : Subgroup ↥LU)) : ↥LU) : G) := by
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
      have := congrArg (fun x : ↥S => (((x : ↥(Q₀ : Subgroup ↥LU)) : ↥LU) : G)) hst
      simpa using this
    · obtain ⟨s, hs, rfl⟩ := hmemE e he
      rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, hS3 s hs]
      rfl
  have hbc : ∀ e ∈ E, Commute e (y' : G) := by
    intro e he
    obtain ⟨s, -, rfl⟩ := hmemE e he
    exact hcent _ s.2
  have h3 := succ_le_pRank_of_commute_828 Nat.prime_three hE hEcard hbc hy3
    (fun hyE => hyLU (hELU hyE)) (hELU.trans hLUU) hyU
  have hU1 : U ≠ ⊥ := by
    have h1 : ch82ZI V h ≠ ⊥ := c.hC.2.2.2.1
    rwa [← c.hUZ] at h1
  have hH2 : pCoreOf 2 (Subgroup.normalizer (U : Set G)) ≠ ⊥ := by
    intro hbot
    apply hU1
    rw [eq_bot_iff, ← hbot]
    exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 _ hU2
  have h2 := CFSG.Quasithin.pRank_le_two_of_pCoreOf_ne_bot hyp.fsu.qtke hH2 Nat.prime_three
    (by norm_num)
  omega

theorem s828_six_a (hMB2 : MB2_828) (hLU : HLU82) (hcard : Mathieu.StmtH13Card)
    {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (hyp : Hyp7_0_2 G T L I) (hrow : Case8_2 T L I) (hr : Row711M24Code T L I)
    (c : S828Ctx T L I H h k) :
    Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 5) := by
  rcases s828_clause3 hMB2 hcard hrow c with ⟨-, hD3⟩ | hP | ⟨-, -, hD5⟩
  · exact absurd hD3 (s828_no_dihedral3 hLU hcard hyp hrow hr c)
  · exfalso
    have hk1 : k = 1 := by
      have : (k : ℕ∞) = 1 := c.hC5.1.symm.trans (c.hC5.2.2.2.2.2.1 hr).1
      exact_mod_cast this
    rw [hk1] at hP
    obtain ⟨⟨-, -, -, h22, -⟩, -⟩ := hP
    exact absurd rfl h22
  · exact hD5

end Six

end CFSG.Quasithin.H13
