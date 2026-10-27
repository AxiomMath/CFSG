module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.N588C4
public import CFSG.LocalAnalysis.UniquenessCase.UC6G.L620Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open scoped commutatorElement
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

open N588

theorem normalizer_L_le_normalizer_rCoreL :
    normalizer (m.L : Set G) ≤ normalizer ((rCore m.r m.L : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_map_of_characteristic hg

theorem H_le_normalizer_rCoreL : m.H ≤ normalizer ((rCore m.r m.L : Subgroup G) : Set G) :=
  m.H_le_normalizer_L.trans m.normalizer_L_le_normalizer_rCoreL

theorem le_M_of_coprime {V : Subgroup G} (hEV : m.E ≤ normalizer (V : Set G))
    (hVp : ¬ m.r ∣ Nat.card V) : V ≤ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI : IsMulCommutative ↥m.E := m.d.E_el.1
  haveI : CFSG.IsElementaryAbelian m.r ↥m.E :=
    ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]; exact m.d.E_el.2 x x.2)⟩
  haveI : Nontrivial ↥m.E := (Subgroup.nontrivial_iff_ne_bot _).2 (Mc614.E_ne_bot m.toMc614)
  refine (CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers hEV hVp).trans
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

theorem rCoreL_le_M : rCore m.r m.L ≤ m.M := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  exact m.le_M_of_coprime (m.hZ.E_le_centralizer.trans m.H_le_normalizer_rCoreL)
    ((Nat.Prime.coprime_iff_not_dvd m.hr).1 (coprime_card_rCore m.r m.L))

theorem odd_card_rCoreL : Odd (Nat.card (rCore m.r m.L)) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := rCore m.r m.L with hYdef
  have hEY : m.E ≤ normalizer (Y : Set G) :=
    m.hZ.E_le_centralizer.trans m.H_le_normalizer_rCoreL
  have hYcop : ¬ m.r ∣ Nat.card Y :=
    (Nat.Prime.coprime_iff_not_dvd m.hr).1 (coprime_card_rCore m.r m.L)
  have hEp : IsPGroup m.r ↥m.E := IsElemAbelian.isPGroup m.d.E_el
  obtain ⟨S, hS⟩ := CFSG.LargeEvenClassification.Helpers.coprime_action_invariant_sylow
    (sylowPrime := 2) m.hr Nat.prime_two hEp
    ((Y.normalizerMonoidHom).comp (Subgroup.inclusion hEY)) hYcop
  set T : Subgroup G := (S : Subgroup ↥Y).map Y.subtype with hT
  have hTsyl : IsSylowOf 2 T Y := ⟨S, rfl⟩
  have hET : m.E ≤ normalizer (T : Set G) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 := hS ⟨e, he⟩
    have h2 : ((Y.normalizerMonoidHom).comp (Subgroup.inclusion hEY) ⟨e, he⟩ :
        MulAut ↥Y).toMonoidHom y ∈ (S : Subgroup ↥Y) := by
      rw [← h1]
      exact Subgroup.mem_map_of_mem _ hy
    refine ⟨_, h2, ?_⟩
    simp [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have hS1 : (S : Subgroup ↥Y) ≠ ⊥ := S.ne_bot_of_dvd_card h2
  have hT1 : T ≠ ⊥ := by
    intro h
    apply hS1
    rw [eq_bot_iff]
    intro x hx
    have : (x : G) ∈ T := ⟨x, hx, rfl⟩
    rw [h, mem_bot] at this
    exact (mem_bot).2 (Subtype.ext this)
  have hloc : IsTwoLocal (normalizer (T : Set G)) := ⟨T, hT1, S.isPGroup'.map _, rfl⟩
  have hEM : m.E ≤ m.M := fun x hx => m.R_le_M (m.E_le_R hx)
  have hE2 : 2 ≤ CFSG.Open.pRank m.r m.E :=
    le_pRank_of_elemAbelian m.hr le_rfl m.d.E_el m.d.E_card
  have hNT := m.hC m.r m.hr m.d.odd m.E hEM hEp hE2 m.d.E_gamma _ hloc hET
  have hYH : Y ≤ m.H := (rCore_le _ _).trans m.L_le_H
  have hfr := frattini_of_isSylowOf hYH m.H_le_normalizer_rCoreL hTsyl
  apply m.hZ.not_le
  show m.H ≤ m.M
  rw [hfr]
  exact sup_le m.rCoreL_le_M (inf_le_right.trans hNT)

theorem isSolvable_rCoreL : Group.IsSolvable ↥(rCore m.r m.L) :=
  CFSG.FeitThompson.isSolvable_of_odd_natCard _ m.odd_card_rCoreL

theorem L_le_normalizer_rCoreL : m.L ≤ normalizer ((rCore m.r m.L : Subgroup G) : Set G) :=
  le_normalizer_rCore m.r m.L

theorem pRank_rCoreL_le_three (h619 : m.C619) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (rCore m.r m.L) ≤ 3 := by
  have hOM : rCore m.r m.L ≤ m.M := m.rCoreL_le_M
  have hLM : ¬ m.L ≤ m.M := by
    intro hLM
    apply m.hZ.not_le
    have : m.H ≤ m.M := by
      rw [h619]
      exact sup_le hLM inf_le_right
    exact this
  by_cases hqσ : q ∈ Dat.sig
  · haveI : Fact q.Prime := ⟨hq⟩
    have hnd : ¬ q ∣ Nat.card (rCore m.r m.L) := by
      intro hd
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q ↥(rCore m.r m.L)))
      have hQsyl : IsSylowOf q ((P : Subgroup ↥(rCore m.r m.L)).map (rCore m.r m.L).subtype)
          (rCore m.r m.L) := ⟨P, rfl⟩
      have hPne : (P : Subgroup ↥(rCore m.r m.L)) ≠ ⊥ := P.ne_bot_of_dvd_card hd
      have hQne : (P : Subgroup ↥(rCore m.r m.L)).map (rCore m.r m.L).subtype ≠ ⊥ := by
        intro h
        apply hPne
        rw [eq_bot_iff]
        intro x hx
        have : (x : G) ∈ ((P : Subgroup ↥(rCore m.r m.L)).map (rCore m.r m.L).subtype) :=
          ⟨x, hx, rfl⟩
        rw [h, mem_bot] at this
        exact (mem_bot).2 (Subtype.ext this)
      have hQp : IsPGroup q ((P : Subgroup ↥(rCore m.r m.L)).map (rCore m.r m.L).subtype) :=
        P.isPGroup'.map _
      have hNQ := (m.isStronglyPEmbedded_M hqσ).normalizer_le hQne hQp
        ((map_subtype_le _).trans hOM)
      have hfr := frattini_of_isSylowOf (rCore_le m.r m.L) m.L_le_normalizer_rCoreL hQsyl
      apply hLM
      rw [hfr]
      exact sup_le hOM (inf_le_right.trans hNQ)
    obtain ⟨E', hE'O, -, hE'card⟩ :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_attained q hq (rCore m.r m.L)
    by_contra h
    have h1 : q ∣ Nat.card E' := by
      rw [hE'card]
      exact dvd_pow_self q (by omega)
    exact hnd (h1.trans (Subgroup.card_dvd_of_le hE'O))
  · exact (CFSG.PreuniquenessRankFour.Helpers.pRank_mono q hq hOM).trans
      (m.hk.pRank_le_three hq hq2 hqσ)

theorem Lbar_not_comm (h620 : m.C620) (hs : IsSimpleGroup m.Lbar) :
    ¬ ∀ a b : m.Lbar, a * b = b * a := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  intro hc
  letI : CommGroup m.Lbar := { (inferInstance : Group m.Lbar) with mul_comm := hc }
  have hp : (Nat.card m.Lbar).Prime := IsSimpleGroup.prime_card
  have hgen : ∃ x : m.Lbar, x ≠ 1 ∧ ∃ a : ℕ, x ^ (m.r ^ a) = 1 := by
    by_contra hno
    push Not at hno
    have hall : ∀ ℓ ∈ m.L, (∃ a : ℕ, orderOf ℓ = m.r ^ a) →
        ℓ ∈ (CFSG.pPrimeCore m.r ↥m.L).map m.L.subtype := by
      intro ℓ hℓ ⟨a, ha⟩
      by_contra hnot
      have h1 : ((⟨ℓ, hℓ⟩ : ↥m.L) : m.Lbar) ≠ 1 := by
        intro h
        apply hnot
        exact ⟨⟨ℓ, hℓ⟩, (QuotientGroup.eq_one_iff _).1 h, rfl⟩
      apply hno _ h1 a
      rw [← QuotientGroup.mk_pow]
      have : (⟨ℓ, hℓ⟩ : ↥m.L) ^ (m.r ^ a) = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← ha]
        exact pow_orderOf_eq_one ℓ)
      rw [this, QuotientGroup.mk_one]
    have hLle := m.L_le_of_gen _ hall
    have hbot : (⊤ : Subgroup m.Lbar) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      induction x using QuotientGroup.induction_on with | H x =>
      obtain ⟨y, hy, hyx⟩ := hLle x.2
      have : x = y := Subtype.ext hyx.symm
      rw [this]
      exact (QuotientGroup.eq_one_iff _).2 hy
    have := hs.toNontrivial
    exact (bot_ne_top (α := Subgroup m.Lbar)) hbot.symm
  obtain ⟨x, hx1, a, hxa⟩ := hgen
  have hxord : orderOf x = Nat.card m.Lbar := by
    rcases hp.eq_one_or_self_of_dvd _ (orderOf_dvd_natCard x) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  have hcard : Nat.card m.Lbar = m.r := by
    have h1 : orderOf x ∣ m.r ^ a := orderOf_dvd_of_pow_eq_one hxa
    rw [hxord] at h1
    exact (Nat.prime_dvd_prime_iff_eq hp m.hr).1 (hp.dvd_of_dvd_pow h1)
  have hL : Nat.card ↥m.L = Nat.card (CFSG.pPrimeCore m.r ↥m.L) * m.r := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pPrimeCore m.r ↥m.L)]
    rw [show Nat.card (↥m.L ⧸ CFSG.pPrimeCore m.r ↥m.L) = m.r from hcard, mul_comm]
  have hdvd : m.r ^ 2 ∣ Nat.card ↥m.L := by
    rw [← m.card_A_inf_L h620]
    exact Subgroup.card_dvd_of_le inf_le_right
  rw [hL, pow_two] at hdvd
  have hcop : Nat.Coprime m.r (Nat.card (CFSG.pPrimeCore m.r ↥m.L)) :=
    CFSG.pPrimeCore_coprime_card
  have h2 : m.r ∣ Nat.card (CFSG.pPrimeCore m.r ↥m.L) :=
    Nat.dvd_of_mul_dvd_mul_right m.hr.pos hdvd
  exact m.hr.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop h2)

theorem L_ne_top : m.L ≠ ⊤ := by
  have hZ : m.Z ≠ ⊥ := by
    intro h
    have := m.card_Z
    rw [h, Subgroup.card_bot] at this
    exact m.hr.one_lt.ne this
  obtain ⟨⟨z, hz⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hZ
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  intro htop
  apply centralizer_singleton_ne_top Dat.standing.simple Dat.standing.nonab hz1'
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ m.H := m.L_le_H (htop ▸ mem_top x)
  rw [H, mem_centralizer_iff] at hx
  rw [mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact hx z hz

theorem isKGroup_L : CFSG.Open.IsKGroup ↥m.L := Dat.standing.kProper.isKGroup m.L m.L_ne_top

theorem gen_L (T : Subgroup ↥m.L)
    (hT : ∀ ℓ : ↥m.L, (∃ a : ℕ, orderOf ℓ = m.r ^ a) → ℓ ∈ T) : T = ⊤ := by
  have h := m.L_le_of_gen (T.map m.L.subtype) fun ℓ hℓ ⟨a, ha⟩ =>
    ⟨⟨ℓ, hℓ⟩, hT ⟨ℓ, hℓ⟩ ⟨a, by rw [Subgroup.orderOf_mk]; exact ha⟩, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := h x.2
  rwa [show y = x from Subtype.ext hyx] at hy

theorem isSolvable_pPrimeCore_L : Group.IsSolvable ↥(CFSG.pPrimeCore m.r ↥m.L) := by
  haveI := m.isSolvable_rCoreL
  let e : ↥(CFSG.pPrimeCore m.r ↥m.L) ≃* ↥(rCore m.r m.L) :=
    (CFSG.pPrimeCore m.r ↥m.L).equivMapOfInjective _ m.L.subtype_injective
  exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem odd_card_pPrimeCore_L : Odd (Nat.card ↥(CFSG.pPrimeCore m.r ↥m.L)) := by
  have h := m.odd_card_rCoreL
  rwa [rCore, Subgroup.card_map_of_injective m.L.subtype_injective] at h

theorem pRank_pPrimeCore_L_le_three (h619 : m.C619) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    CFSG.Open.pRank q (CFSG.pPrimeCore m.r ↥m.L) ≤ 3 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective q hq m.L.subtype
    m.L.subtype_injective _).trans (m.pRank_rCoreL_le_three h619 hq hq2)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
