module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Layer13

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.RankThree.PartOne (pElementSubgroup)

variable {Q : Type} [Group Q] [Finite Q]

theorem s13_Thirteen4Q_pElementSubgroup_le (p : ℕ) (X : Subgroup Q) :
    pElementSubgroup p X ≤ X :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem s13_Thirteen4Q_pRank_bot {p : ℕ} (hp : 1 < p) :
    CFSG.Open.pRank p (⊥ : Subgroup Q) = 0 := by
  refine Nat.le_antisymm (CFSG.SectionRank.pRank_le hp ?_) (Nat.zero_le _)
  intro E hE _
  rw [le_bot_iff.mp hE]
  simp [Subgroup.card_bot]

theorem s13_Thirteen4Q_pRank_eq_zero_of_le_one {p : ℕ} (hp : p ≤ 1) (H : Subgroup Q) :
    CFSG.Open.pRank p H = 0 := by
  obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
  · refine Nat.eq_zero_of_le_zero (csSup_le' ?_)
    rintro k ⟨E, -, -, hk⟩
    by_contra hk0
    have h1 : (0 : ℕ) ^ k = 0 := zero_pow (by omega)
    have h2 : 0 < Nat.card E := Nat.card_pos
    omega
  · have hu : {k | ∃ E : Subgroup Q, E ≤ H ∧ CFSG.Open.IsElemAbelian 1 E ∧
        Nat.card E = 1 ^ k} = Set.univ :=
      Set.eq_univ_of_forall fun k =>
        ⟨⊥, bot_le, CFSG.SectionRank.isElemAbelian_bot 1, by simp⟩
    change sSup {k | ∃ E : Subgroup Q, E ≤ H ∧ CFSG.Open.IsElemAbelian 1 E ∧
      Nat.card E = 1 ^ k} = 0
    rw [hu]
    exact (csSup_of_not_bddAbove not_bddAbove_univ).trans csSup_empty

theorem s13_Thirteen4Q_inf_pElementSubgroup_eq_bot (hns : s13_NormalSimple Q) {p : ℕ}
    (hp : p.Prime) {J : Subgroup Q}
    (hJ : J ≤ Subgroup.centralizer (pElementSubgroup p (CFSG.layer Q) : Set Q)) :
    pElementSubgroup p (CFSG.layer Q) ⊓ J = ⊥ :=
  le_bot_iff.mp <| (inf_le_inf_left _ hJ).trans
    (le_of_eq (s13_inf_centralizer_eq_bot hns hp))

theorem s13_rank_dichotomy (hns : s13_NormalSimple Q) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hcomp : ∀ J : Subgroup Q, CFSG.IsComponent J → p ∣ Nat.card J →
      CFSG.Open.pRank p J ≤ CFSG.Open.pRank r J)
    (hsum : CFSG.Open.pRank p (⊤ : Subgroup Q) =
      CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer Q)) +
        CFSG.Open.pRank p (pElementSubgroup p (Subgroup.centralizer
          (pElementSubgroup p (CFSG.layer Q) : Set Q))))
    (hsmall : CFSG.Open.pRank p (pElementSubgroup p (Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer Q) : Set Q))) ≤ 1) :
    CFSG.Open.pRank p (⊤ : Subgroup Q) ≤ CFSG.Open.pRank r (⊤ : Subgroup Q) ∨
      (pElementSubgroup p (Subgroup.centralizer (pElementSubgroup p (CFSG.layer Q) : Set Q)) ≠ ⊥ ∧
        CFSG.Open.pRank r (⊤ : Subgroup Q) ≤
          CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q))) := by
  have h1 : CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer Q)) ≤
      CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q)) :=
    s13_pRank_pElementSubgroup_layer_le hns hp hr hcomp
  have h2 : CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q)) ≤
      CFSG.Open.pRank r (⊤ : Subgroup Q) :=
    CFSG.SectionRank.pRank_mono hr.one_lt le_top
  by_cases hS0 : pElementSubgroup p (Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer Q) : Set Q)) = ⊥
  · left
    have hSrank : CFSG.Open.pRank p (pElementSubgroup p (Subgroup.centralizer
        (pElementSubgroup p (CFSG.layer Q) : Set Q))) = 0 := by
      rw [hS0]
      exact s13_Thirteen4Q_pRank_bot hp.one_lt
    omega
  · by_cases hle : CFSG.Open.pRank p (⊤ : Subgroup Q) ≤ CFSG.Open.pRank r (⊤ : Subgroup Q)
    · exact Or.inl hle
    · refine Or.inr ⟨hS0, ?_⟩
      have hlt : CFSG.Open.pRank r (⊤ : Subgroup Q) < CFSG.Open.pRank p (⊤ : Subgroup Q) :=
        lt_of_not_ge hle
      omega

theorem s13_pElementSubgroup_layer_le_of_rank (hns : s13_NormalSimple Q) {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime)
    (hrk : CFSG.Open.pRank r (⊤ : Subgroup Q) ≤
      CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q))) :
    pElementSubgroup r (CFSG.layer Q) ≤ pElementSubgroup p (CFSG.layer Q) := by
  rw [s13_pElementSubgroup_layer_eq hns hr]
  refine iSup₂_le fun J hJ => ?_
  rw [s13_mem_compsP] at hJ
  obtain ⟨hJcomp, hJdvd⟩ := hJ
  by_cases hpJ : p ∣ Nat.card J
  · rw [s13_pElementSubgroup_layer_eq hns hp]
    exact le_iSup₂ (f := fun K : Subgroup Q => fun _ : K ∈ s13_compsP Q p => K) J
      ((s13_mem_compsP).2 ⟨hJcomp, hpJ⟩)
  · have hJc : J ≤ Subgroup.centralizer (pElementSubgroup p (CFSG.layer Q) : Set Q) :=
      s13_le_centralizer_pElementSubgroup_layer hns hp hJcomp hpJ
    have hdisj := s13_Thirteen4Q_inf_pElementSubgroup_eq_bot hns hp hJc
    have hadd := s13_pRank_sup_eq_add hr hJc hdisj
    have hJ1 : 1 ≤ CFSG.Open.pRank r J := s13_one_le_pRank_of_dvd J hr hJdvd
    have hmono : CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q) ⊔ J) ≤
        CFSG.Open.pRank r (⊤ : Subgroup Q) :=
      CFSG.SectionRank.pRank_mono hr.one_lt le_top
    omega

theorem s13_eq_one_of_mem_centralizer_layer (hns : s13_NormalSimple Q) {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime)
    (hrk : CFSG.Open.pRank r (⊤ : Subgroup Q) ≤
      CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q)))
    {c : Q} (hc : c ∈ Subgroup.centralizer (CFSG.layer Q : Set Q))
    (hcr : ∃ k : ℕ, c ^ r ^ k = 1) : c = 1 := by
  by_contra hc1
  obtain ⟨k, hk⟩ := hcr
  have horder : orderOf c ∣ r ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow hr).1 horder
  have hc_mem : c ∈ pElementSubgroup r (Subgroup.zpowers c) :=
    Subgroup.subset_closure ⟨Subgroup.mem_zpowers c, ⟨j, hj⟩⟩
  have hne : pElementSubgroup r (Subgroup.zpowers c) ≠ ⊥ := by
    intro hbot
    have : c ∈ (⊥ : Subgroup Q) := by simpa [hbot] using hc_mem
    exact hc1 (Subgroup.mem_bot.mp this)
  obtain ⟨s, hs, hsorder⟩ := s13_exists_orderOf_of_pElementSubgroup_ne_bot hr hne
  have hsc : s ∈ Subgroup.zpowers c :=
    s13_Thirteen4Q_pElementSubgroup_le r (Subgroup.zpowers c) hs
  have hzpc : Subgroup.zpowers c ≤ Subgroup.centralizer (CFSG.layer Q : Set Q) :=
    Subgroup.zpowers_le.mpr hc
  have hs_cent : s ∈ Subgroup.centralizer (CFSG.layer Q : Set Q) := hzpc hsc
  have hsz : Subgroup.zpowers s ≤ Subgroup.centralizer (CFSG.layer Q : Set Q) :=
    Subgroup.zpowers_le.mpr hs_cent
  have hBcent : Subgroup.zpowers s ≤
      Subgroup.centralizer (pElementSubgroup p (CFSG.layer Q) : Set Q) :=
    hsz.trans (Subgroup.centralizer_le (s13_Thirteen4Q_pElementSubgroup_le p (CFSG.layer Q)))
  have hBcard : Nat.card (Subgroup.zpowers s) = r := by
    rw [Nat.card_zpowers, hsorder]
  have hdisj := s13_Thirteen4Q_inf_pElementSubgroup_eq_bot hns hp hBcent
  have hadd := s13_pRank_sup_eq_add hr hBcent hdisj
  have hB1 : CFSG.Open.pRank r (Subgroup.zpowers s) = 1 :=
    s13_pRank_of_card_prime (Subgroup.zpowers s) hr hBcard
  have hmono : CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q) ⊔ Subgroup.zpowers s) ≤
      CFSG.Open.pRank r (⊤ : Subgroup Q) :=
    CFSG.SectionRank.pRank_mono hr.one_lt le_top
  omega

theorem s13_mem_Ep_of_inner (hns : s13_NormalSimple Q) {p r : ℕ} (hp : p.Prime) (hr : r.Prime)
    (hrk : CFSG.Open.pRank r (⊤ : Subgroup Q) ≤
      CFSG.Open.pRank r (pElementSubgroup p (CFSG.layer Q)))
    {y : Q} (hy : ∃ k : ℕ, y ^ r ^ k = 1)
    (hinner : ∀ J : Subgroup Q, CFSG.IsComponent J →
      y ∈ J ⊔ Subgroup.centralizer (J : Set Q)) :
    y ∈ pElementSubgroup p (CFSG.layer Q) := by
  obtain ⟨e, he, c, hc, hyec⟩ := s13_exists_mul_of_inner hns hinner
  obtain ⟨a', ha', b', hb', hyab⟩ :=
    s13_exists_pPart_mul (A := CFSG.layer Q)
      (B := Subgroup.centralizer (CFSG.layer Q : Set Q)) hr le_rfl hy he hc hyec
  have ha'E : a' ∈ pElementSubgroup p (CFSG.layer Q) :=
    s13_pElementSubgroup_layer_le_of_rank hns hp hr hrk ha'
  have hsub : pElementSubgroup r (Subgroup.centralizer (CFSG.layer Q : Set Q)) ≤ ⊥ := by
    refine (Subgroup.closure_le _).2 fun x hx => ?_
    obtain ⟨k, hk⟩ := hx.2
    exact Subgroup.mem_bot.2 <| s13_eq_one_of_mem_centralizer_layer hns hp hr hrk hx.1
      ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩
  have hb'1 : b' = 1 := Subgroup.mem_bot.mp (hsub hb')
  rw [hyab, hb'1, mul_one]
  exact ha'E

theorem s13_exists_other_component {p : ℕ} {J₀ : Subgroup Q} (hJ₀ : CFSG.IsComponent J₀)
    (hJ₀rk : CFSG.Open.pRank p J₀ ≤ 1)
    (h2 : 2 ≤ CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer Q))) :
    ∃ J : Subgroup Q, CFSG.IsComponent J ∧ J ≠ J₀ := by
  by_contra hno
  have hno' : ∀ J : Subgroup Q, CFSG.IsComponent J → J = J₀ := by
    intro J hJ
    by_contra hne
    exact hno ⟨J, hJ, hne⟩
  have hset : {K : Subgroup Q | CFSG.IsComponent K} = {J₀} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨hJ₀, fun K hK => hno' K hK⟩
  have hlayer : CFSG.layer Q = J₀ := by
    rw [CFSG.layer.eq_sSup, hset, sSup_singleton]
  have hE_le : pElementSubgroup p (CFSG.layer Q) ≤ J₀ := by
    rw [hlayer]
    exact s13_Thirteen4Q_pElementSubgroup_le p J₀
  have hp1 : 1 < p := by
    by_contra hle
    have hle' : p ≤ 1 := by omega
    have hz := s13_Thirteen4Q_pRank_eq_zero_of_le_one hle'
      (pElementSubgroup p (CFSG.layer Q))
    omega
  have hmono : CFSG.Open.pRank p (pElementSubgroup p (CFSG.layer Q)) ≤
      CFSG.Open.pRank p J₀ :=
    CFSG.SectionRank.pRank_mono hp1 hE_le
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
