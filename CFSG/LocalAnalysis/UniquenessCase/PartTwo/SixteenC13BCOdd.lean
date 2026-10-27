module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c13bc_pCoreOf_le_oddBar (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {p : ℕ} (hp : p ∈ D.sig) : pCoreOf p (Mbar D.M V₀ V hV) ≤ oddBar D.M V₀ V hV := by
  have hpp : p.Prime := (D.sig_prime p hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp).2
  haveI : Fact p.Prime := ⟨hpp⟩
  have hpg : IsPGroup p ↥(pCoreOf p (Mbar D.M V₀ V hV)) :=
    (CFSG.pCore_isPGroup (p := p) (G := ↥(Mbar D.M V₀ V hV))).map (Mbar D.M V₀ V hV).subtype
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  refine s16c13bc_le_oddBar hV (Subgroup.map_subtype_le _) ?_ ?_
  · intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hnorm : (pCore p ↥(Mbar D.M V₀ V hV)).Normal := CFSG.pCore_normal
    exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, hnorm.conj_mem y hy ⟨m, hm⟩, rfl⟩
  · rw [hn]
    exact (hpp.odd_of_ne_two hp2).pow

theorem s16c13bc_not_quasisimple_of_isPGroup {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : CFSG.Open.IsQuasisimple K) (hpg : IsPGroup p K) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hperf, hs⟩ := hK
  haveI : Group.IsPerfect K := ⟨hperf⟩
  haveI := hs.toNontrivial
  haveI : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  exact Group.IsPerfect.not_isNilpotent K (hpg.isNilpotent)

theorem s16c13bc_prime_eq_of_mem_pCoreOf {Q : Type} [Group Q] [Finite Q] {H : Subgroup Q}
    {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime) {x : Q} (hx : orderOf x = p)
    (hxH : x ∈ pCoreOf p' H) : p' = p := by
  haveI : Fact p'.Prime := ⟨hp'⟩
  have hpg : IsPGroup p' ↥(pCoreOf p' H) :=
    (CFSG.pCore_isPGroup (p := p') (G := ↥H)).map H.subtype
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hpg) ⟨x, hxH⟩
  have hk' : orderOf x = p' ^ k := (Subgroup.orderOf_coe (⟨x, hxH⟩ : ↥(pCoreOf p' H))).trans hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk'
    exact hp.ne_one (hx.symm.trans hk')
  have hdvd : p' ∣ p := by
    rw [← hx, hk']
    exact dvd_pow_self p' hk0
  exact (Nat.prime_dvd_prime_iff_eq hp' hp).1 hdvd

theorem s16c13bc_lBar_le_pCoreOf (D : Data G) {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V)
    (hc : Counterex16 D V₀ V L hV) {p : ℕ} (hp : p.Prime)
    (hLp : IsPGroup p ↥(lBar V₀ V hV L)) (hL1 : lBar V₀ V hV L ≠ ⊥) :
    lBar V₀ V hV L ≤ pCoreOf p (Mbar D.M V₀ V hV) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥(lBar V₀ V hV L) := Subtype.finite
  obtain ⟨n, hn⟩ := hLp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hL1
    rw [pow_zero] at hn
    exact Subgroup.card_eq_one.1 hn
  have hdvd : p ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [hn]
    exact dvd_pow_self p hn0
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥(lBar V₀ V hV L)) p hdvd
  have hao : orderOf (a : MulAut (Vtil V₀ V hV)) = p := by
    rw [Subgroup.orderOf_coe]
    exact ha
  obtain ⟨t, -, -, -, -, -, -, h⟩ := hc.conc
  rcases h with h133 | ⟨K, hK, g, -, -, hLK, -⟩ | ⟨hcomp, -⟩ | ⟨-, -, hcomp, -⟩
  · obtain ⟨p', hp', hLp', -⟩ := h133
    have hpp' := s16c13bc_prime_eq_of_mem_pCoreOf hp hp' hao (hLp' a.2)
    subst hpp'
    exact hLp'
  · have hKL : K ≤ lBar V₀ V hV L := by
      rw [hLK]
      exact le_sup_left
    exact (s16c13bc_not_quasisimple_of_isPGroup hp hK.2.2 (hLp.to_le hKL)).elim
  · exact (s16c13bc_not_quasisimple_of_isPGroup hp hcomp.2.2 hLp).elim
  · exact (s16c13bc_not_quasisimple_of_isPGroup hp hcomp.2.2 hLp).elim

theorem s16c13bc_oddNcCore_of_le_pCoreOf (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) {p : ℕ} (hp : p ∈ D.sig)
    {X : Subgroup (MulAut (Vtil V₀ V hV))} (hX : X ≤ pCoreOf p (Mbar D.M V₀ V hV))
    (hXp : IsPGroup p X) (hXc : ¬ IsCyclic X) : OddNcCore D V₀ V hV :=
  ⟨p, hp, X, hX.trans (s16c13bc_pCoreOf_le_oddBar D hV hp), hXp, hXc⟩

theorem s16c13bc_oddNcCore_of_case168_3 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (h3 : Case168_3 D V₀ V hV L) :
    OddNcCore D V₀ V hV := by
  obtain ⟨⟨-, hcard, hexp⟩, -, hsig⟩ := h3
  have h3σ : 3 ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLp : IsPGroup 3 ↥(lBar V₀ V hV L) := IsPGroup.of_card hcard
  have hL1 : lBar V₀ V hV L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    omega
  refine s16c13bc_oddNcCore_of_le_pCoreOf D hV h3σ
    (s16c13bc_lBar_le_pCoreOf D hV hc Nat.prime_three hLp hL1) hLp ?_
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = 3 ^ 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hdvd : 3 ^ 3 ∣ 3 := hord ▸ orderOf_dvd_of_pow_eq_one (hexp g)
  omega

theorem s16c13bc_card_elemAbelianOfRank {X : Type} [Group X] {p r : ℕ} (hp : p.Prime)
    (h : IsElemAbelianOfRank p r X) : Nat.card X = p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem s16c13bc_isPGroup_of_elemAbelianOfRank {X : Type} [Group X] {p r : ℕ} (hp : p.Prime)
    (h : IsElemAbelianOfRank p r X) : IsPGroup p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  exact IsPGroup.of_card (s16c13bc_card_elemAbelianOfRank hp h)

theorem s16c13bc_not_isCyclic_of_elemAbelianOfRank {X : Type} [Group X] {p r : ℕ}
    (hp : p.Prime) (hr : 2 ≤ r) (h : IsElemAbelianOfRank p r X) : ¬ IsCyclic X := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := h
  intro hc
  have hc' : IsCyclic (Multiplicative (Fin r → ZMod p)) := e.isCyclic.1 hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Multiplicative (Fin r → ZMod p))
  have hord : orderOf g = p ^ r := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
    simp
  have hg1 : g ^ p = 1 := by
    have h0 : p • (Multiplicative.toAdd g) = 0 := by
      funext i
      simp [nsmul_eq_mul]
    calc g ^ p = Multiplicative.ofAdd (p • Multiplicative.toAdd g) := rfl
      _ = 1 := by rw [h0]; rfl
  have hdvd : p ^ r ∣ p := hord ▸ orderOf_dvd_of_pow_eq_one hg1
  have hle : p ^ r ≤ p := Nat.le_of_dvd hp.pos hdvd
  have h2 : p ^ 2 ≤ p ^ r := Nat.pow_le_pow_right hp.pos hr
  have h3 := hp.two_le
  nlinarith

theorem s16c13bc_oddNcCore_of_case168_4 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV) (h4 : Case168_4 D V₀ V hV L) :
    OddNcCore D V₀ V hV := by
  obtain ⟨p, r, hp37, hr, hL, -, hpσ⟩ := h4
  have hpp : p.Prime := by
    rcases hp37 with rfl | rfl <;> norm_num
  have hLp : IsPGroup p ↥(lBar V₀ V hV L) := s16c13bc_isPGroup_of_elemAbelianOfRank hpp hL
  have hL1 : lBar V₀ V hV L ≠ ⊥ := by
    intro h
    have hcard := s16c13bc_card_elemAbelianOfRank hpp hL
    rw [h, Subgroup.card_bot] at hcard
    have h1 : p ^ 1 < p ^ r := Nat.pow_lt_pow_right hpp.one_lt hr
    rw [← hcard, pow_one] at h1
    have h2 := hpp.two_le
    omega
  exact s16c13bc_oddNcCore_of_le_pCoreOf D hV hpσ
    (s16c13bc_lBar_le_pCoreOf D hV hc hpp hLp hL1) hLp
    (s16c13bc_not_isCyclic_of_elemAbelianOfRank hpp hr hL)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
