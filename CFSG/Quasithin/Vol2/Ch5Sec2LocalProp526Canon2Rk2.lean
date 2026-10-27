module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Canon2Bridge
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Bd
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2B
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2C
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Z

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def Stmt5_2_6_L2K_rank2C : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → ¬ IsBenderAny (O2Q (oTwoUpper H)) →
    (∃ P : Subgroup G, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P ∧
      quasithinIsCComponent L₂ P) →
    ∀ L1' L2' : Subgroup G, ((L1' = L ∧ L2' = L₂) ∨ (L1' = L₂ ∧ L2' = L)) →
      F112ListA L1' L2' (sec52S M H) → F112Second L1' L2' (sec52S M H) → False

theorem stmt5_2_6_L2K_rank2C_of
    (h331 : Stmt3_3_1) (hRL : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2)
    (hbor : Stmt5_2_6_borel) (h524 : Stmt5_2_4) (h510 : Stmt5_1_10)
    (h38 : Vol2Native.A38ForSQTKCat) (hU3 : FactU3Cover) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h512 : Stmt5_1_2) (hU4 : Stmt5_2_6_U4ext)
    (hsecC : Stmt5_2_6_secondC) (hU4C : Stmt5_2_6_U4extC)
    (hres : Stmt5_2_6_L2K_rank2_res) : Stmt5_2_6_L2K_rank2C := by
  intro G _ _ T M L V H B D L₂ n hyp hnb ⟨P, hP, hL₂P⟩ L1' L2' hor12 hlistC hsecond
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have hN := hyp.notation59
  have hR : L2RankOneSylowFact := NQCat.l2RankOneSylowFact_holds
  set S := sec52S M H with hSdef
  obtain ⟨h111', hq', hSn', hns1', hns2'⟩ := hyp.f112_hyps hF11 hbor h524 hor12
  have hnotL : ¬ centerOf S ≤ Subgroup.centralizer (L : Set G) := fun hc =>
    h.not_omega_le_centralizer h331 hC58 h317 h512 hyp.ch5Module hyp.hStar hN.2.1
      (hyp.toHyp5_1_8.omega_le_centerOf.trans hc)
  obtain ⟨hlist, hab⟩ := Hyp5_2_4.bridge hRL h331 hR hF11 hbor h524 hsecC hU4C hyp hnotL hor12
    hlistC hsecond
  have hor := fun he => stmt5_2_6_orient_holds G L1' L2' S h111' hq' hSn' hns1' hns2' he
  have horient : (F112E3 L1' L2' S ∨ F112E4 L1' L2' S ∨ F112E6 L1' L2' S) →
      L1' = L₂ ∧ L2' = L := by
    intro he
    have hc := hor he
    rcases hor12 with ⟨h1, -⟩ | h12
    · rw [h1] at hc
      exact absurd hc hnotL
    · exact h12
  have hSN : S ≤ Subgroup.normalizer (L₂ : Set G) :=
    (le_sup_right.trans le_sup_left).trans (h524 G T M L V H B D L₂ n hyp).2.2.2
  have hS2 : S ≤ L₂ ∨ ∃ t : G, t ^ 2 = 1 ∧
      t ∈ Subgroup.normalizer (pCoreOf 2 L₂ : Set G) ∧
      pCoreOf 2 (L₂ ⊔ S) ≤ pCoreOf 2 L₂ ⊔ Subgroup.zpowers t := by
    rcases hab with ⟨-, -, hS1, hS2⟩ | hext
    · left
      rcases hor12 with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact h2 ▸ hS2
      · exact h1 ▸ hS1
    · right
      obtain ⟨h1, h2⟩ := horient (Or.inr (Or.inr hext.e6))
      subst L1' L2'
      obtain ⟨f, hf, hA, hq1, hsp, hb2, hq2, hO⟩ := hext
      obtain ⟨-, -, t, ht, -, hOeq, -⟩ :=
        hU4 G T M L V H B D L₂ n f hyp hf (hyp.isU4ExtTwo_of_orient h331 hR hbor
          (Or.inr ⟨rfl, rfl⟩) hA) hq1 hsp hb2 hq2 hO
      refine ⟨t, ht ▸ pow_orderOf_eq_one t, ?_, hOeq.le⟩
      have htO : t ∈ pCoreOf 2 (L₂ ⊔ S) := by
        rw [hOeq]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
      exact normalizer_le_normalizer_pCoreOf 2 L₂
        (sup_le Subgroup.le_normalizer hSN ((pCoreOf_le 2 _) htO))
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨hbend, hL₂K₁⟩ | ⟨-, hK₁K, -⟩
  ·
    subst hL₂K₁
    have hL₂K := hyp.eq_oTwoUpper_of_bender h38 hRL hU3 h510 h524 hK₁ hKeq hbend hS2
    exact hnb (hL₂K ▸ hbend)
  subst hK₁K
  obtain ⟨k, hk, htype, hpsl, hL₂q, hperf, hNR₀, hR₀Q, hR₀L, hcardR₀⟩ :=
    Sec526.rank2_facts h510 hyp hK₁ hnb hP hL₂P
  set R₀ := pCoreOf 2 (oTwoUpper H) ⊓ L₂ with hR₀def
  have hR₀2 : IsPGroup 2 R₀ := (pCoreOf_isPGroup 2 L₂).to_le hR₀Q
  have hk1 : 1 ≤ k := by omega
  have hn1 : 1 ≤ n := by have := h.two_le; omega
  obtain ⟨hv3, hv4⟩ := Sec526.factorization_two_of_rank2 (X := O2Q (oTwoUpper H)) hk
  have hbig : Nat.card R₀ * 2 ^ (2 * k) ≤ Nat.card (pCoreOf 2 L₂) := by
    have hv : 3 * k ≤ (Nat.card (O2Q (oTwoUpper H))).factorization 2 := by
      rcases htype with h3 | h4
      · rw [hv3 h3]
      · rw [hv4 h4]
        omega
    have hpow : 2 ^ (2 * k) * 2 ^ k ≤ 2 ^ (Nat.card (O2Q (oTwoUpper H))).factorization 2 := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2k : 0 < 2 ^ k := pow_pos (by norm_num) k
    have := Nat.mul_le_mul_left (Nat.card R₀) hpow
    rw [hcardR₀, ← mul_assoc] at this
    exact Nat.le_of_mul_le_mul_right this h2k
  have hnotShort : ¬ IsShort2 L₂ :=
    Sec526.not_isShort2_of_card hk hperf hL₂q hR₀Q hNR₀ hR₀L hbig
  have hspecial : ∀ {f w : ℕ}, f ≤ k → IsSpecialPow 2 (2 ^ f) w ↥(pCoreOf 2 L₂) →
      Nat.card R₀ ≤ 2 ^ (2 * k) → False := fun hfk hsp hc =>
    Sec526.false_of_card_le_of_special hk hfk hperf hL₂q hR₀Q hNR₀ hR₀L hsp hc
  have hq5 : ∀ {f : ℕ}, IsL2Quot f (oTwoQuot ↥L₂) → 1 ≤ f →
      IsSpecialPow 2 (2 ^ f) 2 ↥(pCoreOf 2 L₂) → (F112E3 L₂ L S ∨ F112E6 L₂ L S) →
      F112Second L₂ L S → False := by
    intro f hq1 hf1 hsp he hsec
    have hfk : f = k := eq_of_isL2Quot hf1 hk1 hq1 hL₂q
    subst hfk
    have hQ : Nat.card (pCoreOf 2 L₂) = 2 ^ (5 * f) := by
      rw [hsp.2.1, ← pow_mul]
      ring_nf
    rw [hQ, ← pow_add] at hcardR₀
    rcases htype with h3 | h4
    · rw [hv3 h3] at hcardR₀
      obtain ⟨hc, -⟩ := card_eq_two_pow_sub_of_mul hR₀2 hcardR₀
      exact hres G T M L V H B D L₂ n f hyp hk h3 ⟨P, hP, hL₂P⟩ hpsl
        (by rw [hc]; congr 1; omega) he hsec
    · rw [hv4 h4] at hcardR₀
      obtain ⟨hc, -⟩ := card_eq_two_pow_sub_of_mul hR₀2 hcardR₀
      have hle : Nat.card R₀ ≤ 2 ^ (2 * f) := by
        rw [hc]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hspecial le_rfl hsp hle
  unfold F112ListALegacyBare at hlist
  rcases hor12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    subst L1' L2'
    rcases hlist with ⟨f, -, -, -, -, hb2, -⟩ | ⟨f, -, -, -, -, hb2, -⟩ | h3 | h4 |
      ⟨a, -, -, ⟨e⟩, -⟩ | h6 | ⟨-, ⟨F, _, _, hF, ⟨e⟩⟩, -⟩
    · exact hnotShort hb2.1
    · exact hnotShort hb2.1
    · exact hnotL (hor (Or.inl h3))
    · exact hnotL (hor (Or.inr (Or.inl h4)))
    · exact not_mulEquiv_sz_of_isL2Quot hn1 hyp.isL2Quot_L e
    · exact hnotL (hor (Or.inr (Or.inr h6)))
    · exact not_mulEquiv_su34_of_isL2Quot hn1 hyp.isL2Quot_L hF e
  ·
    subst L1' L2'
    rcases hlist with ⟨f, -, -, hb1, -, -, -⟩ | ⟨f, -, -, hb1, -, -, -⟩ | h3 | h4 |
      ⟨a, -, -, ⟨e⟩, -⟩ | h6 | ⟨-, ⟨F, _, _, hF, ⟨e⟩⟩, -⟩
    · exact hnotShort hb1.1
    · exact hnotShort hb1.1
    ·
      obtain ⟨f, hf, hA, hq1, hq2, hsp, hc⟩ := h3
      have he3 : F112E3 L₂ L S := ⟨f, hf, hA, hq1, hq2, hsp, hc⟩
      rcases hab with ⟨-, -, hSL₂, -⟩ | hext
      · rw [sup_eq_left.mpr hSL₂] at hsp
        exact hq5 hq1 (by omega) hsp (Or.inl he3) hsecond
      · obtain ⟨f', hf', -, hq1', hsp', -⟩ := hext
        exact hq5 hq1' (by omega) hsp' (Or.inl he3) hsecond
    ·
      obtain ⟨f, hf, -, hq1, hsp, -⟩ := h4
      have hfk : 3 * f = k := eq_of_isL2Quot (by omega) hk1 hq1 hL₂q
      have hQ : Nat.card (pCoreOf 2 L₂) = 2 ^ (3 * k) := by
        rw [hsp.2.1, ← pow_mul, ← hfk]
        ring_nf
      rw [hQ, ← pow_add] at hcardR₀
      have hv : 3 * k ≤ (Nat.card (O2Q (oTwoUpper H))).factorization 2 := by
        rcases htype with h3 | h4
        · rw [hv3 h3]
        · rw [hv4 h4]
          omega
      obtain ⟨hc, -⟩ := card_eq_two_pow_sub_of_mul hR₀2 hcardR₀
      have hle : Nat.card R₀ ≤ 2 ^ (2 * k) := by
        rw [hc]
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      exact hspecial (by omega) hsp hle
    · exact not_mulEquiv_sz_of_isL2Quot hk1 hL₂q e
    ·
      have he6 : F112E6 L₂ L S := h6
      obtain ⟨f, hf, -, hq1, hsp, -⟩ := h6
      exact hq5 hq1 (by omega) hsp (Or.inr he6) hsecond
    · exact not_mulEquiv_su34_of_isL2Quot hk1 hL₂q hF e

end CFSG.Quasithin.H13
