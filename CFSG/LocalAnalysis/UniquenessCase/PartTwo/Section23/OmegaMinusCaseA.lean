module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusQ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaMinusStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem zOneOf_QV_eq (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D) (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    (hA' : S23_23OmegaCaseA c) :
    zOneOf c.QV = zOneOf D.T := by
  have hQVT : c.QV ≤ D.T := c.QV_le_T hCLV
  have hJ1 : jOneOf D.T ≤ c.QV :=
    le_inf ((Subgroup.map_subtype_le (CFSG.higherElemThompson ↥D.T 1)).trans le_sup_right) hA'
  have hR : CFSG.higherElemThompson ↥D.T 1 ≤ c.QV.subgroupOf D.T :=
    (Subgroup.map_le_iff_le_comap).mp (by
      show (CFSG.higherElemThompson ↥D.T 1).map D.T.subtype ≤ c.QV
      simpa [jOneOf, CFSG.inSubgroup] using hJ1)
  have hm : 1 < CFSG.pRank 2 ↥D.T := by
    have hZV : D.Z ≤ c.V := uc22p22v_le_conjClosure c.N D.Z
    have hmono : CFSG.Open.pRank 2 D.Z ≤ CFSG.Open.pRank 2 D.T :=
      CFSG.SectionRank.pRank_mono (by norm_num) (hZV.trans (c.V_le_T h4 h1930))
    rw [CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
    omega
  obtain ⟨-, -, hthird⟩ :=
    CFSG.Quasithin.SteinbergBK.higher_elementary_thompson_intersections_and_central_involutions
      (S := ↥D.T) D.sylowM.isPGroup
  have hE := (hthird 1 hm (c.QV.subgroupOf D.T) hR).2.2.2
  have hmap := congrArg (fun K : Subgroup ↥D.T => K.map D.T.subtype) hE
  calc zOneOf c.QV = ((CFSG.higherElemThompsonOmega ↥(c.QV.subgroupOf D.T) 1).map
        (c.QV.subgroupOf D.T).subtype).map D.T.subtype :=
        (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.map_higherElemThompsonOmega_subgroupOf
          hQVT 1).symm
    _ = zOneOf D.T := hmap

private theorem Z_ne_bot_of (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z) : D.Z ≠ ⊥ := by
  have hZel : IsElemAbelian 2 D.Z := c.isElemAbelian_Z h4 h1930
  have hcard : Nat.card D.Z = 2 ^ CFSG.Open.pRank 2 D.Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_two hZel
  have hcard1 : Nat.card D.Z ≠ 1 := by
    rw [hcard]
    have h4le : 4 ≤ 2 ^ CFSG.Open.pRank 2 D.Z := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ CFSG.Open.pRank 2 D.Z := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  intro hbot
  exact hcard1 (by rw [hbot, Subgroup.card_bot])

theorem normalizer_zOne_le_N_of_caseA (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    (hA' : S23_23OmegaCaseA c) :
    Subgroup.normalizer (zOneOf D.T : Set G) ≤ c.N := by
  have hzQV : zOneOf c.QV = zOneOf D.T := c.zOneOf_QV_eq hV h4 h1930 hn2 hCLV hA'
  have hZle : D.Z ≤ zOneOf D.T :=
    c.Z_le_zOne hV hA h4 h1930 hn2 hNat hKA hCLV
  have hZne : D.Z ≠ ⊥ := Z_ne_bot_of c h4 h1930 hn2
  have hzne : zOneOf D.T ≠ ⊥ := fun h =>
    hZne (le_bot_iff.mp (h ▸ hZle))
  have hz2 : IsPGroup 2 (zOneOf D.T) :=
    D.sylowM.isPGroup.to_le (Subgroup.map_subtype_le (CFSG.higherElemThompsonOmega ↥D.T 1))
  have hT : D.T ≤ Subgroup.normalizer (zOneOf D.T : Set G) := by
    letI : (CFSG.higherElemThompsonOmega ↥D.T 1).Characteristic :=
      CFSG.Quasithin.SteinbergBK.higherElemThompsonOmega_characteristic 1
    exact Subgroup.le_normalizer.trans
      (CFSG.BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        D.T (CFSG.higherElemThompsonOmega ↥D.T 1))
  have hL : c.L ≤ Subgroup.normalizer (zOneOf D.T : Set G) := by
    letI : (CFSG.higherElemThompsonOmega ↥c.QV 1).Characteristic :=
      CFSG.Quasithin.SteinbergBK.higherElemThompsonOmega_characteristic 1
    have hstep : Subgroup.normalizer (c.QV : Set G) ≤
        Subgroup.normalizer (zOneOf c.QV : Set G) :=
      CFSG.BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        c.QV (CFSG.higherElemThompsonOmega ↥c.QV 1)
    rw [hzQV] at hstep
    exact (le_sup_left : c.L ≤ c.L ⊔ D.T).trans (c.le_normalizer_QV.trans hstep)
  exact c.normalizer_le_N_of_isPGroup hzne hz2 (sup_le hL hT)

theorem le_N_of_caseA (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hThomp : KThomp)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    (hA' : S23_23OmegaCaseA c) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {Q : Subgroup G}
    (hQ : Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)))
    (hQq : IsPGroup q ↥Q) (hTQ : Permutes D.T Q) :
    Q ≤ c.N := by
  have hJ : Subgroup.normalizer (F12.jOf D.T : Set G) ≤ c.N :=
    (c.jZero_facts hV hA h4 h1930 hn2 hNat hKA hCLV).2.2
  have hZ : Subgroup.normalizer (zOneOf D.T : Set G) ≤ c.N :=
    c.normalizer_zOne_le_N_of_caseA hV hA h4 h1930 hn2 hNat hKA hCLV hA'
  have hfac := thompson_QT D hThomp hq hq5 hQ hQq hTQ
  intro x hx
  have hxX : x ∈ ((Q ⊔ D.T : Subgroup G) : Set G) := Subgroup.mem_sup_left hx
  rw [hfac] at hxX
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxX
  rw [← hab]
  exact c.N.mul_mem (inf_le_right.trans hJ ha) (inf_le_right.trans hZ hb)

theorem pCore_bar_of_caseA (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hThomp : KThomp)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    (hA' : S23_23OmegaCaseA c) (h72 : S23_7_2 D Ch) (h72s : S23_7_2_sig D Ch)
    (hsig : D.sig.Nonempty) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) :
    IsCyclic ↥(CFSG.pCore q (Bar2 D.M)) ∧
      (q ∈ D.sig → CFSG.pCore q (Bar2 D.M) = ⊥) := by
  have hq2 : q ≠ 2 := by omega
  have hQN : ∀ Q : Subgroup G, Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) →
      IsPGroup q ↥Q → Permutes D.T Q → Q ≤ c.N := fun Q hQ hQq hTQ =>
    c.le_N_of_caseA hV hA h4 h1930 hn2 hNat hKA hThomp hCLV hA' hq hq5 hQ hQq hTQ
  have hcontra : ∀ Q : Subgroup G, Q ≠ ⊥ →
      Q ≤ barPreimage D.M (CFSG.pCore q (Bar2 D.M)) → IsPGroup q ↥Q → Permutes D.T Q →
      Q ≤ c.N → Q ⊓ c.N = ⊥ → False := by
    intro Q hQne hQ hQq hTQ hQNmem hinter
    exact hQne (le_bot_iff.mp (hinter ▸ le_inf le_rfl hQNmem))
  constructor
  · by_contra hcyc
    have hne : CFSG.pCore q (Bar2 D.M) ≠ ⊥ := fun hbot => hcyc (hbot ▸ Bot.isCyclic)
    obtain ⟨Q0, Q, hQ0, hQQ0, hQne, hexp, hcl, hQn, hperm, himp⟩ :=
      exists_good_Q D hq hq2 hne
    exact hcontra Q hQne (hQQ0.trans hQ0.le) (hQ0.isPGroup.to_le hQQ0) hperm
      (hQN Q (hQQ0.trans hQ0.le) (hQ0.isPGroup.to_le hQQ0) hperm)
      (c.inf_N_eq_bot h1930 h72 h72s hsig hq hq2 hQ0 hQQ0 hexp hcl hQn hperm
        (Or.inr (himp hcyc)))
  · intro hqsig
    by_contra hne
    obtain ⟨Q0, Q, hQ0, hQQ0, hQne, hexp, hcl, hQn, hperm, -⟩ :=
      exists_good_Q D hq hq2 hne
    exact hcontra Q hQne (hQQ0.trans hQ0.le) (hQ0.isPGroup.to_le hQQ0) hperm
      (hQN Q (hQQ0.trans hQ0.le) (hQ0.isPGroup.to_le hQQ0) hperm)
      (c.inf_N_eq_bot h1930 h72 h72s hsig hq hq2 hQ0 hQQ0 hexp hcl hQn hperm
        (Or.inl hqsig))

theorem fitting_isCyclic_of_caseA (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hNat : NatOmegaMinus (c.H hV) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z)) (hKA : KOmA)
    (hThomp : KThomp)
    (hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L)
    (hA' : S23_23OmegaCaseA c) (h72 : S23_7_2 D Ch) (h72s : S23_7_2_sig D Ch)
    (hsig : D.sig.Nonempty) (h26 : S23_26Omega D Ch)
    (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) := by
  have h3cyc : IsCyclic ↥(CFSG.pCore 3 (Bar2 D.M)) :=
    isCyclic_pCore_three_of_sylow D fun P => (h26 h1930 c hOm P).2
  refine isCyclic_fitting_of_forall_pCore D fun q hq hq2 => ?_
  rcases hq.eq_two_or_odd' with hqeq | hqodd
  · exact absurd hqeq hq2
  · rcases Nat.lt_or_ge 3 q with hq3 | hq3
    · exact (c.pCore_bar_of_caseA hV hA h4 h1930 hn2 hNat hKA hThomp hCLV hA' h72 h72s
        hsig hq (Nat.Prime.five_le_of_ne_two_of_ne_three hq hq2 (by omega))).1
    · have hqge3 : 3 ≤ q := hq.odd_iff.mp hqodd
      have hqeq3 : q = 3 := le_antisymm hq3 hqge3
      exact hqeq3 ▸ h3cyc

private theorem B0_ne_bot_of (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h52 : S23_5_2Omega D Ch) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    c.B0 ≠ ⊥ := by
  have hcn : c.n = 2 * CFSG.Open.pRank 2 D.Z := (h52 h1930 c hOm).2
  have hn : 3 ≤ c.n := hn3 h1930 c.toCtx23.toCtx21
  have h4le : 4 ≤ 2 ^ c.n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd (by omega : 2 ^ c.n - 1 ≠ 1)
  have hne : (piSet c.B0).Nonempty := by
    rw [c.hpi]
    exact ⟨r, hrp, hrdvd⟩
  intro hbot
  rw [hbot] at hne
  obtain ⟨p, hp, hpdvd⟩ := hne
  rw [Subgroup.card_bot] at hpdvd
  exact hp.not_dvd_one hpdvd

private theorem exists_prime_dvd_two_pow_sub_one {m : ℕ} (hm : 2 ≤ m) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ m - 1 := by
  have hne : 2 ^ m - 1 ≠ 1 := by
    have h4le : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hdecomp : 2 ^ m = (2 ^ m - 1) + 1 :=
      (Nat.sub_add_cancel Nat.one_le_two_pow).symm
    intro h
    rw [h] at hdecomp
    omega
  exact Nat.exists_prime_and_dvd hne

private theorem not_dvd_two_pow_add_one_of_dvd_two_pow_sub_one {m r : ℕ} (hm : 2 ≤ m)
    (hrp : r.Prime) (hrdvd : r ∣ 2 ^ m - 1) : ¬ r ∣ 2 ^ m + 1 := by
  intro hdvd2
  have hdvd2' : r ∣ 2 := by
    have hsub := Nat.dvd_sub hdvd2 hrdvd
    have harg : 2 ^ m + 1 - (2 ^ m - 1) = 2 := by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    rwa [harg] at hsub
  have hr2 : r = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2' with h1 | h2
    · exact absurd h1 hrp.ne_one
    · exact h2
  have h2dvd : 2 ∣ 2 ^ m - 1 := hr2 ▸ hrdvd
  have he : Even (2 ^ m) := Even.pow_of_ne_zero (a := (2 : ℕ)) even_two (by omega)
  exact (Nat.Even.sub_odd Nat.one_le_two_pow he (by norm_num)).not_two_dvd_nat h2dvd

private theorem exists_mem_not_mem_centralizer (c : Ctx23L D Ch)
    (hcn : c.n = 2 * CFSG.Open.pRank 2 D.Z)
    (hm : 2 ≤ CFSG.Open.pRank 2 D.Z)
    (hpi : piSet c.B = etaSet c.n)
    (hpiC : piSet (c.B ⊓ Subgroup.centralizer (D.Z : Set G)) =
      {p | p.Prime ∧ p ∣ 2 ^ CFSG.Open.pRank 2 D.Z + 1}) :
    ∃ b ∈ c.B, (b : G) ∉ Subgroup.centralizer (D.Z : Set G) := by
  obtain ⟨r, hrp, hrdvd⟩ := exists_prime_dvd_two_pow_sub_one hm
  have hrpow : r ∣ 2 ^ c.n - 1 := by
    rw [hcn]
    have hpow : (2 : ℕ) ^ (2 * CFSG.Open.pRank 2 D.Z) =
        ((2 : ℕ) ^ CFSG.Open.pRank 2 D.Z) ^ 2 := by
      rw [Nat.mul_comm, pow_mul]
    rw [hpow]
    have hsq : ((2 : ℕ) ^ CFSG.Open.pRank 2 D.Z) ^ 2 - 1 =
        (2 ^ CFSG.Open.pRank 2 D.Z + 1) * (2 ^ CFSG.Open.pRank 2 D.Z - 1) := by
      simpa using Nat.sq_sub_sq ((2 : ℕ) ^ CFSG.Open.pRank 2 D.Z) 1
    rw [hsq]
    exact dvd_mul_of_dvd_right hrdvd _
  have hrdvdB : r ∣ Nat.card ↥c.B := by
    have hmem : r ∈ piSet c.B := by
      rw [hpi]
      exact ⟨hrp, hrpow⟩
    exact hmem.2
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨b, hbord⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B) r hrdvdB
  refine ⟨b, b.2, ?_⟩
  intro hbcin
  have hbint : (b : G) ∈ c.B ⊓ Subgroup.centralizer (D.Z : Set G) := ⟨b.2, hbcin⟩
  have hdvd : r ∣ Nat.card ↥(c.B ⊓ Subgroup.centralizer (D.Z : Set G)) := by
    have h := Subgroup.orderOf_dvd_natCard
      (c.B ⊓ Subgroup.centralizer (D.Z : Set G)) hbint
    rwa [Subgroup.orderOf_coe, hbord] at h
  have hmem : r ∈ piSet (c.B ⊓ Subgroup.centralizer (D.Z : Set G)) := ⟨hrp, hdvd⟩
  rw [hpiC] at hmem
  exact not_dvd_two_pow_add_one_of_dvd_two_pow_sub_one hm hrp hrdvd hmem.2

theorem commutator_B0_Z_ne_bot (c : Ctx23L D Ch) (h1930 : H1930 D)
    (h52 : S23_5_2Omega D Ch) (h53 : S23_5_3 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hOm : IsOmegaMinus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z)) :
    ⁅c.B0, D.Z⁆ ≠ ⊥ := by
  classical
  have hB0ne : c.B0 ≠ ⊥ := B0_ne_bot_of c h1930 h52 hn3 hOm
  let c0 : Ctx23L D Ch := c.withB c.B0 c.hB0 le_rfl
  have hpi : piSet c0.B = etaSet c0.n := c.hpi
  have h5 := h53 h1930 c0 hpi
  intro hcomm
  have hleC : c0.B ≤ Subgroup.centralizer (D.Z : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rcases h5 with hbot | ⟨-, hpiC⟩
  · have hle : c0.B ≤ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact le_inf le_rfl hleC
    exact hB0ne (le_bot_iff.mp hle)
  · have hcn : c.n = 2 * CFSG.Open.pRank 2 D.Z := (h52 h1930 c hOm).2
    have hm : 2 ≤ CFSG.Open.pRank 2 D.Z := by
      have hn : 3 ≤ c.n := hn3 h1930 c.toCtx23.toCtx21
      omega
    obtain ⟨b, hbB, hbC⟩ := exists_mem_not_mem_centralizer c0 hcn hm hpi hpiC
    exact hbC (hleC hbB)

private theorem eq_bot_of_isSylowOf_fitting_of_pCore_eq_bot {p : ℕ} (hpp : p.Prime)
    {P : Subgroup (Bar2 D.M)}
    (hPsyl : CFSG.ABGLocalTools.IsSylowOf p P (CFSG.fittingSubgroup (Bar2 D.M)))
    (hpbot : CFSG.pCore p (Bar2 D.M) = ⊥) : P = ⊥ := by
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨Q, hQ⟩ := hPsyl
  have hPle : P ≤ CFSG.pCore p (Bar2 D.M) :=
    hQ ▸ Sylow.map_le_pCore CFSG.fittingSubgroup_normal CFSG.fittingSubgroup_nilpotent p Q
  rw [hpbot] at hPle
  exact le_bot_iff.mp hPle

end Ctx23L

theorem s23_23CaseA_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (hK : KOrdNatural) (hA : KTab23a)
    (h52 : S23_5_2Omega D Ch) (h53 : S23_5_3 D Ch) (h26 : S23_26Omega D Ch)
    (h72 : S23_7_2 D Ch) (h72s : S23_7_2_sig D Ch) (h10 : S23_10 D Ch)
    (hsig : D.sig.Nonempty) (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n)
    (hKA : KOmA) (hThomp : KThomp) :
    S23_23CaseA D Ch := by
  intro h1930 c hOm hV hNat hA'
  have hcn : c.n = 2 * CFSG.Open.pRank 2 D.Z := (h52 h1930 c hOm).2
  have hn : 3 ≤ c.n := hn3 h1930 c.toCtx23.toCtx21
  have hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z := by omega
  have hCLV : c.L ⊓ Subgroup.centralizer (c.V : Set G) ≤ CFSG.Open.pCoreOf 2 c.L :=
    le_of_eq (Ctx23L.inf_centralizer_V_eq_pCoreOf D Ch h2 h3 h4 hK h1930 c hOm)
  have hfit : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) :=
    c.fitting_isCyclic_of_caseA hV hA h4 h1930 hn2 hNat hKA hThomp hCLV hA' h72 h72s hsig
      h26 hOm
  have hcomm : ⁅c.B0, D.Z⁆ ≠ ⊥ :=
    Ctx23L.commutator_B0_Z_ne_bot c h1930 h52 h53 hn3 hOm
  obtain ⟨p, hpsig, P, hPsyl, hPnc⟩ :=
    h10 h1930 (c.withB c.B0 c.hB0 le_rfl) hfit hcomm
  obtain ⟨Pthree⟩ := (inferInstance : Nonempty (Sylow 3 ↥(oTwoThreeOf D.M)))
  have hp3 : p ≠ 3 := fun h => (h26 h1930 c hOm Pthree).1 (h ▸ hpsig)
  have hpp : p.Prime := (D.sig_prime p hpsig).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpsig).2
  have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hpp hp2 hp3
  have hpbot : CFSG.pCore p (Bar2 D.M) = ⊥ :=
    (c.pCore_bar_of_caseA hV hA h4 h1930 hn2 hNat hKA hThomp hCLV hA' h72 h72s hsig hpp
      hp5).2 hpsig
  have hPbot : P = ⊥ :=
    Ctx23L.eq_bot_of_isSylowOf_fitting_of_pCore_eq_bot hpp hPsyl hpbot
  apply hPnc
  rw [hPbot]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hy1 : y = 1 := by simpa using hy
  rw [hy1, one_mul, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
