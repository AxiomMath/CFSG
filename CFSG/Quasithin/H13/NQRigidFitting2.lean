module

public import CFSG.Quasithin.H13.NQRigidFitting1
public import CFSG.Quasithin.H13.NQBlockRankTwoRigidity
public import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup Module
open scoped IsMulCommutative commutatorElement

variable {H : Type*} [Group H] [Finite H]

theorem mulAut_mul_comm_of_isCyclic {Q : Type*} [Group Q] [IsCyclic Q] (φ ψ : MulAut Q) :
    φ * ψ = ψ * φ := by
  apply (IsCyclic.mulAutMulEquiv Q).injective
  rw [map_mul, map_mul, mul_comm]

theorem pRank_le_of_subgroup (p : ℕ) (hp : 1 < p) (K : Subgroup H) :
    CFSG.pRank p K ≤ CFSG.pRank p H := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact CFSG.SectionRank.pRank_top_le_of_injective hp K.subtype K.subtype_injective

theorem p_sq_le_index_frattini {p : ℕ} (hp : p.Prime) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hPrk : CFSG.pRank p P = 2) : p ^ 2 ≤ (frattini P).index := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (P ⧸ frattini P) := hP.to_quotient _
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hidx : (frattini P).index = p ^ k := hk
  by_contra hlt
  push Not at hlt
  rw [hidx] at hlt
  have hk1 : k ≤ 1 := by
    by_contra h2
    push Not at h2
    exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right hp.pos h2))
  have hcyc : IsCyclic (P ⧸ frattini P) := by
    interval_cases k
    · rw [pow_zero] at hk
      have : Subsingleton (P ⧸ frattini P) := (Nat.card_eq_one_iff_unique.mp hk).1
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hk
      exact isCyclic_of_prime_card hk
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (frattini P) g
  have hPcyc : IsCyclic P := by
    refine ⟨⟨x, fun y => ?_⟩⟩
    have htop : closure ({x} : Set P) = ⊤ := by
      apply LocalAnalysis.ComponentInitial.frattini_generator_lifting
      rw [Set.image_singleton, hx, eq_top_iff]
      intro z _
      obtain ⟨n, hn⟩ := hg z
      rw [← hn]
      exact zpow_mem (subset_closure (Set.mem_singleton g)) n
    have hy : y ∈ closure ({x} : Set P) := by rw [htop]; exact mem_top y
    rw [← zpowers_eq_closure] at hy
    exact mem_zpowers_iff.mp hy
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup P)
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top, hPrk] at hEcard
  have hEel : CFSG.IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).mpr hE
  have hEc : IsCyclic E := Subgroup.isCyclic E
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hEcard hEc

theorem exists_invariant_line_of_trivial {p : ℕ} (hp : p.Prime) {P : Subgroup H}
    (hP : IsPGroup p P) (hdim : p ^ 2 ≤ (frattini P).index)
    (htriv : ∀ x ∈ P, ∀ n ∈ normalizer (P : Set H), ⁅x, n⁆ ∈ (frattini P).map P.subtype) :
    ∃ Y : Subgroup H, (frattini P).map P.subtype ≤ Y ∧ Y ≤ P ∧
      normalizer (P : Set H) ≤ normalizer (Y : Set H) ∧
      Y ≠ (frattini P).map P.subtype ∧ Y ≠ P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (P ⧸ frattini P) := hP.to_quotient _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := P ⧸ frattini P) p
    ((dvd_pow_self p two_ne_zero).trans (show p ^ 2 ∣ Nat.card (P ⧸ frattini P) by
      obtain ⟨k, hk⟩ := hQ.exists_card_eq
      rw [hk]
      have hidx : (frattini P).index = p ^ k := hk
      rw [hidx] at hdim
      exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).mp hdim)))
  set Y₀ := zpowers w with hY₀
  have hY₀card : Nat.card Y₀ = p := by rw [Nat.card_zpowers, hw]
  set Y' : Subgroup P := Y₀.comap (QuotientGroup.mk' (frattini P)) with hY'
  set Y := Y'.map P.subtype with hY
  have hΦY' : frattini P ≤ Y' := fun x hx => by
    rw [hY', mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  refine ⟨Y, map_mono hΦY', map_subtype_le _, ?_, ?_, ?_⟩
  · intro n hn
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    all_goals
      obtain ⟨y', hy', rfl⟩ := hy
    · have hc := htriv y' y'.2 n hn
      obtain ⟨c, hc', hcc⟩ := hc
      have hmem : n * (y' : H) * n⁻¹ ∈ P := (mem_normalizer_iff.mp hn y').mp y'.2
      refine ⟨⟨_, hmem⟩, ?_, rfl⟩
      have heq : (⟨_, hmem⟩ : P) = c⁻¹ * y' := by
        apply Subtype.ext
        change n * (y' : H) * n⁻¹ = ((c : H))⁻¹ * y'
        have hcc' : (c : H) = ⁅(y' : H), n⁆ := hcc
        rw [hcc', commutatorElement_def]
        group
      rw [heq]
      exact Y'.mul_mem (Y'.inv_mem (hΦY' hc')) hy'
    · have hninv : n⁻¹ ∈ normalizer (P : Set H) := inv_mem hn
      have hc := htriv y' y'.2 n⁻¹ hninv
      obtain ⟨c, hc', hcc⟩ := hc
      have hmem : n⁻¹ * (y' : H) * n⁻¹⁻¹ ∈ P := (mem_normalizer_iff.mp hninv y').mp y'.2
      refine ⟨⟨_, hmem⟩, ?_, rfl⟩
      have heq : (⟨_, hmem⟩ : P) = c⁻¹ * y' := by
        apply Subtype.ext
        change n⁻¹ * (y' : H) * n⁻¹⁻¹ = ((c : H))⁻¹ * y'
        have hcc' : (c : H) = ⁅(y' : H), n⁻¹⁆ := hcc
        rw [hcc', commutatorElement_def]
        group
      rw [heq]
      exact Y'.mul_mem (Y'.inv_mem (hΦY' hc')) hy'
  · intro h1
    have h2 : Y' = frattini P := map_injective P.subtype_injective h1
    have h3 : Y₀ = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) z
      have : z ∈ Y' := hz
      rw [h2] at this
      exact (mem_bot).mpr ((QuotientGroup.eq_one_iff z).mpr this)
    rw [h3, card_bot] at hY₀card
    exact hp.one_lt.ne hY₀card
  · intro h1
    have h2 : Y' = ⊤ := by
      apply map_injective P.subtype_injective
      change Y = _
      rw [h1, ← MonoidHom.range_eq_map, range_subtype]
    have h3 : Y₀ = ⊤ := by
      rw [eq_top_iff]
      intro z _
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) z
      have : z ∈ Y' := h2 ▸ mem_top z
      exact this
    have h4 : p ^ 2 ≤ p := by
      calc p ^ 2 ≤ (frattini P).index := hdim
        _ = Nat.card Y₀ := by rw [h3, card_top]; rfl
        _ = p := hY₀card
    have h5 : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

theorem rank_two_odd_Fitting_normalizer_dichotomy (hO2 : CFSG.pCore 2 H = ⊥)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.pRank r H ≤ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup H} (hP : IsPGroup p P) (hPrk : CFSG.pRank p P = 2)
    (hPexp : ∀ x ∈ P, x ^ p = 1)
    (hirr : (frattini P).map P.subtype < P ∧ ∀ Y : Subgroup H,
      (frattini P).map P.subtype ≤ Y → Y ≤ P → normalizer (P : Set H) ≤ normalizer (Y : Set H) →
      Y = (frattini P).map P.subtype ∨ Y = P) :
    Odd (Nat.card (CFSG.fittingSubgroup H)) ∧
      CFSG.fittingSubgroup H ≤ normalizer (P : Set H) ∧
      (∀ r : ℕ, r.Prime → r ≠ p → ⁅CFSG.pCore r H, P⁆ = ⊥) ∧
      ((P ≤ CFSG.pCore p H ∧ (P.subgroupOf (CFSG.pCore p H)).Characteristic ∧ P.Normal) ∨
        (IsCyclic (CFSG.pCore p H) ∧ ⁅P, CFSG.fittingSubgroup H⁆ = ⊥)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hdim : p ^ 2 ≤ (frattini P).index := p_sq_le_index_frattini hp hP hPrk
  have hcore : ∀ r : ℕ, r.Prime → r ≠ p → ⁅CFSG.pCore r H, P⁆ = ⊥ := by
    intro r hr hrp
    by_cases hr2 : r = 2
    · subst hr2
      rw [hO2, commutator_bot_left]
    · have : Fact r.Prime := ⟨hr⟩
      have : (CFSG.pCore r H).Normal := CFSG.pCore_normal
      exact irreducible_exponent_prime_normalizer_centralizes_coprime_rank_two_core hp hr hp2
        hr2 (Ne.symm hrp) CFSG.pCore_isPGroup
        ((pRank_le_of_subgroup r hr.one_lt _).trans (hrk r hr hr2)) hP hPexp hdim hirr.2
  set Q := CFSG.pCore p H with hQdef
  have hQn : Q.Normal := CFSG.pCore_normal
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  have hFit : ⁅Q, P⁆ = ⊥ → ⁅P, CFSG.fittingSubgroup H⁆ = ⊥ := by
    intro hQP
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer,
      CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore]
    refine iSup_le fun r => ?_
    by_cases hrp : (r : ℕ) = p
    · rw [hrp]
      exact commutator_eq_bot_iff_le_centralizer.mp hQP
    · exact commutator_eq_bot_iff_le_centralizer.mp
        (hcore r (Nat.prime_of_mem_primeFactors r.2) hrp)
  have hdich : (P ≤ Q ∧ (P.subgroupOf Q).Characteristic ∧ P.Normal) ∨
      (IsCyclic Q ∧ ⁅Q, P⁆ = ⊥) := by
    by_cases hQ1 : Q = ⊥
    · right
      refine ⟨?_, by rw [hQ1, commutator_bot_left]⟩
      have : Subsingleton Q := by
        rw [hQ1]
        infer_instance
      exact isCyclic_of_subsingleton
    have : Nontrivial Q := (nontrivial_iff_ne_bot Q).mpr hQ1
    obtain ⟨D, hDc, hD1, hDexp, -, htors, -⟩ :=
      CFSG.SectionRank.Ccomm.supercritical_witness hp2 hQp
    set D' := D.map Q.subtype with hD'
    have hD'n : D'.Normal := inferInstance
    have hD'p : IsPGroup p D' := (hQp.to_subgroup D).map _
    have hD'exp : ∀ x ∈ D', x ^ p = 1 := by
      rintro _ ⟨d, hd, rfl⟩
      exact congrArg Subtype.val (hDexp d hd)
    by_cases hD2 : CFSG.pRank p D' = 2
    · left
      have hEq := NQBlock.nq_normal_rank_two_prime_torsion_rigidity hp2 (hrk p hp hp2) D' P hD2
        hPrk hD'exp hPexp hirr
      have hPQ : P ≤ Q := hEq ▸ map_subtype_le D
      refine ⟨hPQ, ?_, hEq ▸ hD'n⟩
      have hsub : P.subgroupOf Q = D := by
        rw [← hEq, hD']
        exact comap_map_eq_self_of_injective Q.subtype_injective D
      rw [hsub]
      exact hDc
    right
    have hD'rk : CFSG.pRank p D' ≤ 2 :=
      (pRank_le_of_subgroup p hp.one_lt D').trans (hrk p hp hp2)
    have hD'cyc : IsCyclic D' := by
      by_contra hnc
      obtain ⟨B, hB, hBcard⟩ :=
        CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two (hp.odd_of_ne_two hp2) hD'p hnc
      apply hD2
      refine le_antisymm hD'rk ?_
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact CFSG.SectionRank.le_pRank hp.one_lt le_top
        ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p B).mp hB) hBcard
    have hD'card : Nat.card D' = p := by
      have hD'1 : D' ≠ ⊥ := by
        rw [hD', Ne, map_eq_bot_iff_of_injective _ Q.subtype_injective]
        exact hD1
      have hexpD : Monoid.exponent D' ∣ p :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hD'exp x x.2)
      rw [← IsCyclic.exponent_eq_card]
      rcases (Nat.dvd_prime hp).mp hexpD with h | h
      · exfalso
        apply hD'1
        have : Subsingleton D' := Monoid.exp_eq_one_iff.mp h
        exact eq_bot_of_subsingleton D'
      · exact h
    have hQD : ∀ q ∈ Q, ∀ d ∈ D', q * d = d * q := by
      intro q hq d hd
      set c : H →* MulAut D' := MulAut.conjNormal with hc
      have hcard : Nat.card (MulAut D') = p - 1 := by
        rw [IsCyclic.card_mulAut, hD'card, Nat.totient_prime hp]
      obtain ⟨k, hk⟩ := hQp ⟨q, hq⟩
      have hcq : (c q) ^ p ^ k = 1 := by
        rw [← map_pow]
        have : q ^ p ^ k = 1 := congrArg Subtype.val hk
        rw [this, map_one]
      have hord : orderOf (c q) = 1 := by
        have h1 : orderOf (c q) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hcq
        have h2 : orderOf (c q) ∣ p - 1 := hcard ▸ orderOf_dvd_natCard (c q)
        have hp3 : 3 ≤ p := by have := hp.two_le; omega
        have hcop : Nat.Coprime (p ^ k) (p - 1) := Nat.Coprime.pow_left k
          ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h =>
            absurd (Nat.le_of_dvd (by omega) h) (by omega))
        exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
      have hc1 : c q = 1 := orderOf_eq_one_iff.mp hord
      have h3 := congrArg (fun φ : MulAut D' => ((φ ⟨d, hd⟩ : D') : H)) hc1
      simp only [hc, MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc q * d = q * d * q⁻¹ * q := by group
        _ = d * q := by rw [h3]
    have hordD : ∀ x ∈ Q, orderOf x = p → x ∈ D' := by
      intro x hx hxp
      have hxc : (⟨x, hx⟩ : Q) ∈ centralizer (D : Set Q) := by
        rw [mem_centralizer_iff]
        intro d hd
        exact Subtype.ext (hQD x hx d ⟨d, hd, rfl⟩).symm
      have hxp' : orderOf (⟨x, hx⟩ : Q) = p := by
        rw [← Subgroup.orderOf_coe]
        exact hxp
      exact ⟨_, htors _ hxc hxp', rfl⟩
    have hQcyc : IsCyclic Q := by
      by_contra hnc
      obtain ⟨B, hB, hBcard⟩ :=
        CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two (hp.odd_of_ne_two hp2) hQp hnc
      have hBD : B.map Q.subtype ≤ D' := by
        rintro _ ⟨b, hb, rfl⟩
        by_cases hb1 : b = 1
        · rw [hb1, map_one]
          exact one_mem _
        · have : CFSG.IsElementaryAbelian p B := hB
          have hbp : b ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian b hb
          apply hordD _ b.2
          rw [Subgroup.orderOf_coe]
          exact orderOf_eq_prime hbp hb1
      have hfin : Finite D' := inferInstance
      have := card_le_of_le hBD
      rw [card_map_of_injective Q.subtype_injective, hBcard, hD'card] at this
      have h5 : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    set N := normalizer (P : Set H) with hN
    set K := ⁅P, N⁆ with hK
    have hKP : K ≤ P := by
      rw [hK, commutator_le]
      intro x hx n hn
      rw [commutatorElement_def, show x * n * x⁻¹ * n⁻¹ = x * (n * x⁻¹ * n⁻¹) by group]
      exact P.mul_mem hx ((mem_normalizer_iff.mp hn x⁻¹).mp (P.inv_mem hx))
    have hconjK : ∀ n ∈ N, ∀ z ∈ K, n * z * n⁻¹ ∈ K := by
      intro n hn z hz
      have h1 : K.map (MulAut.conj n).toMonoidHom ≤ K := by
        rw [hK, Subgroup.map_commutator]
        refine commutator_mono ?_ ?_
        · rintro _ ⟨x, hx, rfl⟩
          exact (mem_normalizer_iff.mp hn x).mp hx
        · rintro _ ⟨m, hm, rfl⟩
          exact N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)
      exact h1 ⟨z, hz, rfl⟩
    have hPK : P ≤ K := by
      set Y := K ⊔ (frattini P).map P.subtype with hY
      have hYN : N ≤ normalizer (Y : Set H) := by
        refine le_trans (le_inf ?_ ?_) (inf_normalizer_le_normalizer_sup K _)
        · intro n hn
          exact mem_normalizer_of_conj_mem (hconjK n hn) (hconjK n⁻¹ (N.inv_mem hn))
        · exact LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (frattini P)
      rcases hirr.2 Y le_sup_right (sup_le hKP (map_subtype_le _)) hYN with h1 | h1
      · exfalso
        have htriv : ∀ x ∈ P, ∀ n ∈ N, ⁅x, n⁆ ∈ (frattini P).map P.subtype := fun x hx n hn =>
          h1 ▸ (le_sup_left : K ≤ Y) (commutator_mem_commutator hx hn)
        obtain ⟨Y', hΦY', hY'P, hY'N, hne1, hne2⟩ :=
          exists_invariant_line_of_trivial hp hP hdim htriv
        rcases hirr.2 Y' hΦY' hY'P hY'N with h | h
        · exact hne1 h
        · exact hne2 h
      · have h2 : K.subgroupOf P ⊔ frattini P = ⊤ := by
          have h3 : (K ⊔ (frattini P).map P.subtype).subgroupOf P = P.subgroupOf P := by
            rw [← hY, h1]
          have h4 : ((frattini P).map P.subtype).subgroupOf P = frattini P :=
            comap_map_eq_self_of_injective P.subtype_injective _
          rw [subgroupOf_sup hKP (map_subtype_le _), subgroupOf_self, h4] at h3
          exact h3
        have h3 := frattini_nongenerating h2
        intro x hx
        have : (⟨x, hx⟩ : P) ∈ K.subgroupOf P := h3 ▸ mem_top _
        exact this
    have hPQ : ∀ x ∈ P, ∀ q ∈ Q, x * q = q * x := by
      set c : H →* MulAut Q := MulAut.conjNormal with hc
      have hcK : K ≤ c.ker := by
        rw [hK, commutator_le]
        intro x _ n _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
          mulAut_mul_comm_of_isCyclic (c x) (c n)]
        group
      intro x hx q hq
      have hcx : c x = 1 := hcK (hPK hx)
      have h3 := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : H)) hcx
      simp only [hc, MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc x * q = x * q * x⁻¹ * x := by group
        _ = q * x := by rw [h3]
    refine ⟨hQcyc, ?_⟩
    rw [commutator_eq_bot_iff_le_centralizer]
    intro q hq
    rw [mem_centralizer_iff]
    intro x hx
    exact hPQ x hx q hq
  have hodd : Odd (Nat.card (CFSG.fittingSubgroup H)) := by
    obtain ⟨e, -⟩ := CFSG.LocalCores.fitting_product_prime_cores (G := H)
    rw [← Nat.card_congr e.toEquiv, Nat.card_pi, Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro hdvd
    obtain ⟨r, -, hr⟩ := (Prime.dvd_finsetProd_iff Nat.prime_two.prime _).mp hdvd
    have hrp : (r : ℕ).Prime := Nat.prime_of_mem_primeFactors r.2
    have : Fact (r : ℕ).Prime := ⟨hrp⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := (r : ℕ)) (G := H)).exists_card_eq
    rw [hk] at hr
    have h2r : 2 = (r : ℕ) :=
      (Nat.prime_dvd_prime_iff_eq Nat.prime_two hrp).mp (Nat.prime_two.dvd_of_dvd_pow hr)
    have hO : CFSG.pCore (r : ℕ) H = ⊥ := by rw [← h2r]; exact hO2
    rw [hO, card_bot] at hk
    rw [← hk] at hr
    omega
  refine ⟨hodd, ?_, hcore, ?_⟩
  · rcases hdich with ⟨-, -, hPn⟩ | ⟨-, hQP⟩
    · rw [normalizer_eq_top_iff.mpr hPn]
      exact le_top
    · have h1 := hFit hQP
      rw [commutator_comm, commutator_eq_bot_iff_le_centralizer] at h1
      exact h1.trans (centralizer_le_normalizer _)
  · rcases hdich with h1 | ⟨hQc, hQP⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hQc, hFit hQP⟩

end CFSG.Quasithin.H13.NQRigid
