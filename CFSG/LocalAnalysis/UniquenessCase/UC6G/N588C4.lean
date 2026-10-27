module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.C632d
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588C4

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC22 (calNOf)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

open N588

theorem L_le_of_gen (T : Subgroup G) (hT : ∀ ℓ ∈ m.L, (∃ a : ℕ, orderOf ℓ = m.r ^ a) → ℓ ∈ T) :
    m.L ≤ T := by
  refine (Subgroup.closure_le _).2 fun x hx => hT x ?_ hx.2
  exact Subgroup.subset_closure hx

theorem L_perfect_of_simple (h620 : m.C620) (hL1 : IsSimpleGroup ↥m.L) : ⁅m.L, m.L⁆ = m.L := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have htop : commutator ↥m.L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥m.L) with h | h
    · exfalso
      have hcomm : ∀ a b : ↥m.L, a * b = b * a := by
        intro a b
        have : ⁅a, b⁆ ∈ commutator ↥m.L := by
          rw [commutator_def]; exact commutator_mem_commutator (mem_top a) (mem_top b)
        rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      have hdvd : m.r ∣ Nat.card ↥m.L := by
        have h1 := Subgroup.card_dvd_of_le (inf_le_right : m.A ⊓ m.L ≤ m.L)
        rw [m.card_A_inf_L h620] at h1
        exact (dvd_pow_self m.r two_ne_zero).trans h1
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' m.r hdvd
      have hn : (zpowers x).Normal := ⟨fun a _ g => by
        rw [hcomm g a, mul_inv_cancel_right]; assumption⟩
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (zpowers x) with h1 | h1
      · rw [zpowers_eq_bot] at h1
        rw [h1, orderOf_one] at hx
        exact m.hr.one_lt.ne hx
      · have h2 : Nat.card ↥m.L = m.r := by
          rw [← Subgroup.card_top (G := ↥m.L), ← h1, Nat.card_zpowers, hx]
        have h3 := Subgroup.card_dvd_of_le (inf_le_right : m.A ⊓ m.L ≤ m.L)
        rw [m.card_A_inf_L h620, h2] at h3
        have h4 := Nat.le_of_dvd m.hr.pos h3
        have h5 : m.r < m.r ^ 2 := by
          calc m.r = m.r ^ 1 := (pow_one _).symm
            _ < m.r ^ 2 := Nat.pow_lt_pow_right m.hr.one_lt (by norm_num)
        omega
    · exact h
  exact commutator_self_eq_of_perfect htop

private theorem L_not_le_M_n588 (h619 : m.C619) : ¬ m.L ≤ m.M := by
  intro hLM
  apply m.hZ.not_le
  have : m.H ≤ m.M := by
    rw [h619]
    exact sup_le hLM inf_le_right
  exact this

theorem five_le_r (hr3 : m.r ≠ 3) : 5 ≤ m.r := by
  have h2 := m.hr.two_le
  have hr2 : m.r ≠ 2 := m.d.odd
  have hr4 : m.r ≠ 4 := fun h => by
    have := m.hr
    rw [h] at this
    exact absurd this (by norm_num)
  omega

theorem L_GL_trivial (h620 : m.C620) (hL1 : IsSimpleGroup ↥m.L)
    (hL3 : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (GL (Fin d) (ZMod q)) ⧸ center (GL (Fin d) (ZMod q)), f = 1)
    {q : ℕ} (hq : q.Prime) (hqr : q ≠ m.r) :
    ∀ d ≤ 6, ∀ f : ↥m.L →* GL (Fin d) (ZMod q), f = 1 := fun d hd f =>
  N588.eq_one_of_forall_PGL (N588.commutator_eq_top_of_perfect (m.L_perfect_of_simple h620 hL1))
    (hL3 q hq hqr d hd) f

theorem rCore_le_M {N : Subgroup G} (hEN : m.E ≤ N) : rCore m.r N ≤ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI : IsMulCommutative ↥m.E := m.d.E_el.1
  haveI : CFSG.IsElementaryAbelian m.r ↥m.E :=
    ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact m.d.E_el.2 x x.2)⟩
  haveI : Nontrivial ↥m.E := (Subgroup.nontrivial_iff_ne_bot _).2 (Mc614.E_ne_bot m.toMc614)
  have hAV : m.E ≤ normalizer ((rCore m.r N : Subgroup G) : Set G) :=
    hEN.trans (le_normalizer_rCore _ N)
  have hVp : ¬ m.r ∣ Nat.card (rCore m.r N) :=
    (Nat.Prime.coprime_iff_not_dvd m.hr).1 (coprime_card_rCore m.r N)
  refine (CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hAV hVp).trans
    (iSup₂_le fun B hB => inf_le_right.trans ?_)
  have hBc : Nat.card B = m.r := by
    have h := B.card_mul_index
    rw [hB, m.d.E_card, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_right m.hr.pos h
  have hBp : IsPGroup m.r (B.map m.E.subtype) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Subgroup.card_map_of_injective m.E.subtype_injective, hBc, pow_one]
  have hBne : B.map m.E.subtype ≠ ⊥ := by
    intro h
    have h1 := congrArg (fun H : Subgroup G => Nat.card H) h
    simp only [Subgroup.card_map_of_injective m.E.subtype_injective, hBc,
      Subgroup.card_bot] at h1
    exact m.hr.one_lt.ne' h1
  exact (Subgroup.centralizer_le_normalizer _).trans
    ((CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 m.r m.E _ (map_subtype_le _)
      (one_le_pRank_of_ne_bot m.hr hBp hBne)).trans m.d.E_gamma)

theorem pCore_two_rCore_eq_bot (h619 : m.C619) {N : Subgroup G} (hN : m.A ⊔ m.L ≤ N) :
    (CFSG.pCore 2 ↥(rCore m.r N)).map (rCore m.r N).subtype = ⊥ := by
  by_contra hT
  have hTp : IsPGroup 2 ((CFSG.pCore 2 ↥(rCore m.r N)).map (rCore m.r N).subtype) :=
    CFSG.pCore_isPGroup.map _
  have hNT : N ≤ normalizer (((CFSG.pCore 2 ↥(rCore m.r N)).map (rCore m.r N).subtype :
      Subgroup G) : Set G) := fun n hn =>
    mem_normalizer_map_of_characteristic (le_normalizer_rCore m.r N hn)
  have hloc : IsTwoLocal (normalizer (((CFSG.pCore 2 ↥(rCore m.r N)).map
      (rCore m.r N).subtype : Subgroup G) : Set G)) := ⟨_, hT, hTp, rfl⟩
  have hEM : m.E ≤ m.M := fun x hx => m.R_le_M (m.E_le_R hx)
  have hE2 : 2 ≤ CFSG.Open.pRank m.r m.E := le_pRank_of_elemAbelian m.hr le_rfl m.d.E_el m.d.E_card
  have hle := m.hC m.r m.hr m.d.odd m.E hEM (IsElemAbelian.isPGroup m.d.E_el) hE2 m.d.E_gamma _
    hloc ((m.E_le_A.trans le_sup_left).trans (hN.trans hNT))
  exact L_not_le_M_n588 m h619 ((le_sup_right.trans hN).trans (hNT.trans hle))

theorem pRank_rCore_le_three (h619 : m.C619) {N : Subgroup G} (hN : m.A ⊔ m.L ≤ N) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) : CFSG.Open.pRank q (rCore m.r N) ≤ 3 := by
  have hOM : rCore m.r N ≤ m.M :=
    m.rCore_le_M ((m.E_le_A.trans le_sup_left).trans hN)
  by_cases hqσ : q ∈ Dat.sig
  · haveI : Fact q.Prime := ⟨hq⟩
    have hnd : ¬ q ∣ Nat.card (rCore m.r N) := by
      intro hd
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q ↥(rCore m.r N)))
      have hQsyl : IsSylowOf q ((P : Subgroup ↥(rCore m.r N)).map (rCore m.r N).subtype)
          (rCore m.r N) := ⟨P, rfl⟩
      have hPne : (P : Subgroup ↥(rCore m.r N)) ≠ ⊥ := P.ne_bot_of_dvd_card hd
      have hQne : (P : Subgroup ↥(rCore m.r N)).map (rCore m.r N).subtype ≠ ⊥ := by
        intro h
        apply hPne
        rw [eq_bot_iff]
        intro x hx
        have : (x : G) ∈ ((P : Subgroup ↥(rCore m.r N)).map (rCore m.r N).subtype) :=
          ⟨x, hx, rfl⟩
        rw [h, mem_bot] at this
        exact (mem_bot).2 (Subtype.ext this)
      have hQp : IsPGroup q ((P : Subgroup ↥(rCore m.r N)).map (rCore m.r N).subtype) :=
        P.isPGroup'.map _
      have hNQ := (m.isStronglyPEmbedded_M hqσ).normalizer_le hQne hQp
        ((map_subtype_le _).trans hOM)
      have hON : rCore m.r N ⊔ m.L ≤ normalizer ((rCore m.r N : Subgroup G) : Set G) :=
        sup_le Subgroup.le_normalizer ((le_sup_right.trans hN).trans (le_normalizer_rCore m.r N))
      have hfr := frattini_of_isSylowOf le_sup_left hON hQsyl
      apply L_not_le_M_n588 m h619
      calc m.L ≤ rCore m.r N ⊔ m.L := le_sup_right
        _ = _ := hfr
        _ ≤ m.M := sup_le hOM (inf_le_right.trans hNQ)
    obtain ⟨E', hE'O, -, hE'card⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained q hq (rCore m.r N)
    by_contra h
    have h1 : q ∣ Nat.card E' := by
      rw [hE'card]
      exact dvd_pow_self q (by omega)
    exact hnd (h1.trans (Subgroup.card_dvd_of_le hE'O))
  · exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq hOM).trans
      (m.hk.pRank_le_three hq hq2 hqσ)

theorem L_le_of_coprime_gen {q : ℕ} (hq : q.Prime) (hqr : q ≠ m.r) (T : Subgroup G)
    (hT : ∀ ℓ ∈ m.L, Nat.Coprime (orderOf ℓ) q → ℓ ∈ T) : m.L ≤ T :=
  m.L_le_of_gen T fun ℓ hℓ ⟨a, ha⟩ => hT ℓ hℓ (by
    rw [ha]
    exact Nat.Coprime.pow_left a ((Nat.coprime_primes m.hr hq).2 (Ne.symm hqr)))

theorem L_le_centralizer_fitting_rCore (h619 : m.C619) (h620 : m.C620)
    (hL1 : IsSimpleGroup ↥m.L)
    (hL3 : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (GL (Fin d) (ZMod q)) ⧸ center (GL (Fin d) (ZMod q)), f = 1)
    {N : Subgroup G} (hN : m.A ⊔ m.L ≤ N) :
    m.L ≤ centralizer (CFSG.fittingSubgroupOf (rCore m.r N) : Set G) := by
  have hLperf := m.L_perfect_of_simple h620 hL1
  have hLO : m.L ≤ normalizer ((rCore m.r N : Subgroup G) : Set G) :=
    (le_sup_right.trans hN).trans (le_normalizer_rCore m.r N)
  rw [CFSG.fittingSubgroupOf, CFSG.fitting_eq_sup_pCore, Subgroup.map_iSup]
  apply CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
  rintro ⟨⟨q, hqmem⟩, -⟩
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
  haveI : Fact q.Prime := ⟨hq⟩
  show m.L ≤ centralizer (((CFSG.pCore q ↥(rCore m.r N)).map (rCore m.r N).subtype :
    Subgroup G) : Set G)
  have hLP : m.L ≤ normalizer (((CFSG.pCore q ↥(rCore m.r N)).map (rCore m.r N).subtype :
      Subgroup G) : Set G) := fun ℓ hℓ => mem_normalizer_map_of_characteristic (hLO hℓ)
  have hPp : IsPGroup q ((CFSG.pCore q ↥(rCore m.r N)).map (rCore m.r N).subtype) :=
    CFSG.pCore_isPGroup.map _
  by_cases hq2 : q = 2
  · subst hq2
    rw [m.pCore_two_rCore_eq_bot h619 hN]
    intro x _
    rw [mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, mem_bot] at hy
    rw [hy, one_mul, mul_one]
  by_cases hqr : q = m.r
  · have hbot : (CFSG.pCore q ↥(rCore m.r N)).map (rCore m.r N).subtype = ⊥ := by
      haveI : Fact m.r.Prime := ⟨m.hr⟩
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hPp
      have hdvd : Nat.card ((CFSG.pCore q ↥(rCore m.r N)).map (rCore m.r N).subtype) ∣
          Nat.card (rCore m.r N) := Subgroup.card_dvd_of_le (map_subtype_le _)
      have hcop := coprime_card_rCore m.r N
      rw [hn, ← hqr] at hdvd
      rw [← hqr] at hcop
      have h1 : q ^ n = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left n hcop) hdvd
      rw [← Subgroup.card_eq_one, hn, h1]
    rw [hbot]
    intro x _
    rw [mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, mem_bot] at hy
    rw [hy, one_mul, mul_one]
  have hrank : CFSG.Open.pRank q ((CFSG.pCore q ↥(rCore m.r N)).map (rCore m.r N).subtype) ≤ 3 :=
    (CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq (map_subtype_le _)).trans
      (m.pRank_rCore_le_three h619 hN hq hq2)
  have h := N588.commutator_eq_bot_of_pRank_le_three hq2 hLperf (m.L_le_of_coprime_gen hq hqr)
    (m.L_GL_trivial h620 hL1 hL3 hq hqr) _ hPp hrank hLP
  exact Subgroup.le_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h)

theorem L_le_centralizer_component_rCore (hSch : UCK.KSch) (h619 : m.C619) (h620 : m.C620)
    (hL1 : IsSimpleGroup ↥m.L)
    (hL3 : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (GL (Fin d) (ZMod q)) ⧸ center (GL (Fin d) (ZMod q)), f = 1)
    (hr3 : m.r ≠ 3) {N : Subgroup G} (hN : N ∈ calNOf (m.A ⊔ m.L)) {K : Subgroup G}
    (hK : CFSG.GorensteinWalter.IsComponentOf K (rCore m.r N)) : m.L ≤ centralizer (K : Set G) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hNle : m.A ⊔ m.L ≤ N := hN.2
  have hLperf := m.L_perfect_of_simple h620 hL1
  have hLO : m.L ≤ normalizer ((rCore m.r N : Subgroup G) : Set G) :=
    (le_sup_right.trans hNle).trans (le_normalizer_rCore m.r N)
  have hF := m.L_le_centralizer_fitting_rCore h619 h620 hL1 hL3 hNle
  have hLK : m.L ≤ normalizer (K : Set G) := m.L_le_of_gen _ fun ℓ hℓ ⟨a, ha⟩ =>
    N588.mem_normalizer_of_pRank_le_three m.hr (m.five_le_r hr3) hK (hLO hℓ) ha
      (fun z hzK hzc => by
        have hzF := N588.mem_fitting_of_mem_center_component hK hzK hzc
        have h1 : z * ℓ = ℓ * z := mem_centralizer_iff.1 (hF hℓ) z hzF
        calc ℓ * z * ℓ⁻¹ = z * ℓ * ℓ⁻¹ := by rw [h1]
          _ = z := by group)
      (fun q hq hq2 => m.pRank_rCore_le_three h619 hNle hq hq2)
  have hKk : CFSG.Open.IsKGroup ↥K :=
    (Dat.standing.kProper.isKGroup N hN.1.1).of_le (hK.1.trans (rCore_le _ _))
  have hcop : Nat.Coprime m.r (Nat.card K) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hK.1) (coprime_card_rCore m.r N)
  exact N588.le_centralizer_of_coprime hSch hK.2.2 hKk hLK hLperf m.L_le_of_gen hcop

theorem commutator_rCore_L_eq_bot (hSch : UCK.KSch) (h619 : m.C619) (h620 : m.C620)
    (hL1 : IsSimpleGroup ↥m.L)
    (hL3 : ∀ (q : ℕ), q.Prime → q ≠ m.r → ∀ (d : ℕ), d ≤ 6 →
      ∀ f : ↥m.L →* (GL (Fin d) (ZMod q)) ⧸ center (GL (Fin d) (ZMod q)), f = 1)
    (hr3 : m.r ≠ 3) {N : Subgroup G} (hN : N ∈ calNOf (m.A ⊔ m.L)) :
    ⁅rCore m.r N, m.L⁆ = ⊥ :=
  N588.commutator_eq_bot_of_fitting_of_components
    ((le_sup_right.trans hN.2).trans (le_normalizer_rCore m.r N))
    (m.L_perfect_of_simple h620 hL1) (m.L_le_centralizer_fitting_rCore h619 h620 hL1 hL3 hN.2)
    fun _ hK => m.L_le_centralizer_component_rCore hSch h619 h620 hL1 hL3 hr3 hN hK

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
