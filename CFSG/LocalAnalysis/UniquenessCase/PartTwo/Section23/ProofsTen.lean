module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121B
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Solvable
public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
public import CFSG.GroupTheory.InvertingElements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem uc22s2310_key (D : Data G) (Ch : Choice2011 G)
    (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h1930 : H1930 D) (c : Ctx23L D Ch)
    {r e : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {b' : G} (hb' : b' ∈ c.B)
    (hb'Z : b' ∉ Subgroup.centralizer (D.Z : Set G)) (hord : orderOf b' = r ^ e) :
    ∀ p ∈ D.sig, ∀ Q : Subgroup (Bar2 D.M), IsPGroup p Q →
      barImage D.M c.B ≤ Subgroup.centralizer (Q : Set (Bar2 D.M)) → Q = ⊥ := by
  intro p hp Q hQp hBQ
  by_contra hQne
  have hb'M : b' ∈ D.M := (c.hle.trans c.hBM) hb'
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  obtain ⟨⟨xbar, hxQ⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hQne
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hQp ⟨xbar, hxQ⟩
  rw [Subgroup.orderOf_mk] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hn
    exact hx1 (Subtype.ext hn)
  let bbar : Bar2 D.M := uc22p21cPi D.M ⟨b', hb'M⟩
  have hbbar_mem : bbar ∈ barImage D.M c.B :=
    uc22p21c_mem_barImage.2 ⟨⟨b', hb'M⟩, hb', rfl⟩
  have hcomm_bar : Commute bbar xbar :=
    ((Subgroup.mem_centralizer_iff.mp (hBQ hbbar_mem)) xbar hxQ).symm
  let Pks : Subgroup ↥D.M := Subgroup.zpowers (⟨b', hb'M⟩ : ↥D.M)
  have hPks : IsPGroup r Pks := by
    refine IsPGroup.of_card (n := e) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hord]
  haveI hNnormal : (CFSG.pCore 2 ↥D.M).Normal :=
    CFSG.pCore_normal (p := 2) (G := ↥D.M)
  have hNcop : Nat.Coprime r (Nat.card (CFSG.pCore 2 ↥D.M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M))
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
  have hcbar : ∀ y ∈ Pks, (y : ↥D.M ⧸ CFSG.pCore 2 ↥D.M) * xbar =
      xbar * (y : ↥D.M ⧸ CFSG.pCore 2 ↥D.M) := by
    intro y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hmap : uc22p21cPi D.M ((⟨b', hb'M⟩ : ↥D.M) ^ m) = bbar ^ m := by
      rw [map_zpow]
    change uc22p21cPi D.M ((⟨b', hb'M⟩ : ↥D.M) ^ m) * xbar =
      xbar * uc22p21cPi D.M ((⟨b', hb'M⟩ : ↥D.M) ^ m)
    rw [hmap]
    exact (hcomm_bar.zpow_left m).eq
  obtain ⟨x₀, hcbar_eq, hc_comm⟩ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.exists_lift_centralizer hr
      (CFSG.pCore 2 ↥D.M) hNcop hPks hcbar
  let x : G := (x₀ : ↥D.M)
  have hxM : x ∈ D.M := x₀.2
  have hxb' : b' * x = x * b' := by
    have h := congrArg Subtype.val (hc_comm (⟨b', hb'M⟩ : ↥D.M) (Subgroup.mem_zpowers _))
    simpa [x] using h
  obtain ⟨a, q, hq_ndvd, hx_ord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p (D.sig_prime p hp).1.one_lt.ne'
  have hq0 : q ≠ 0 := by
    intro hq0
    rw [hq0, mul_zero] at hx_ord
    exact (orderOf_pos x).ne' hx_ord
  let y : G := x ^ q
  have hyM : y ∈ D.M := D.M.pow_mem hxM q
  have hybar : uc22p21cPi D.M ⟨y, hyM⟩ = xbar ^ q := by
    have hyc : (⟨y, hyM⟩ : ↥D.M) = x₀ ^ q := Subtype.ext rfl
    rw [hyc, map_pow]
    change uc22p21cPi D.M x₀ ^ q = xbar ^ q
    rw [show uc22p21cPi D.M x₀ = xbar from hcbar_eq]
  have hy_ne : y ≠ 1 := by
    intro hy1
    have h1 : xbar ^ q = 1 := by
      have hsub : (⟨y, hyM⟩ : ↥D.M) = 1 := Subtype.ext hy1
      rw [← hybar, hsub, map_one]
    have hdvd : orderOf xbar ∣ q := orderOf_dvd_of_pow_eq_one h1
    have hp_dvd : p ∣ q := by
      have hpd : p ∣ orderOf xbar := by
        rw [hn]
        exact dvd_pow_self p hn0
      exact hpd.trans hdvd
    exact hq_ndvd hp_dvd
  have hy_ord : orderOf y = p ^ a := by
    have hqdvd : q ∣ orderOf x := by
      rw [hx_ord]
      exact dvd_mul_left q (p ^ a)
    rw [show y = x ^ q from rfl, orderOf_pow_of_dvd hq0 hqdvd, hx_ord]
    exact Nat.mul_div_cancel (p ^ a) (Nat.pos_of_ne_zero hq0)
  have hXp : IsPGroup p (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := a) (by rw [Nat.card_zpowers, hy_ord])
  have hyxb : b' * y = y * b' := by
    change b' * x ^ q = x ^ q * b'
    exact ((show Commute b' x from hxb').pow_right q).eq
  have hXle : Subgroup.zpowers y ≤ D.M ⊓ Subgroup.centralizer ({b'} : Set G) := by
    refine le_inf (Subgroup.zpowers_le.mpr hyM) (Subgroup.zpowers_le.mpr ?_)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hyxb.symm
  have hXne : Subgroup.zpowers y ≠ ⊥ := by
    intro hbot
    exact hy_ne ((Subgroup.zpowers_eq_bot).1 hbot)
  have hnot : p ∉ D.sig1 :=
    (h54 h1930 c b' hb' hb'Z).2 p (D.sig_prime p hp).1
      (Subgroup.zpowers y) hXne hXp hXle |>.2
  have hp1 : p ∈ D.sig1 := by
    rw [h6 h1930 c] at hp
    exact hp
  exact hnot hp1

theorem s23_10_of_parts (D : Data G) (Ch : Choice2011 G)
    (h54 : S23_5_4 D Ch) (h6 : S23_6 D Ch) (h2121 : S21_21B D Ch) (h2123 : S21_23 D Ch)
    (hsig : D.sig.Nonempty)
    (h2 : H1930 D → Ctx23L D Ch → ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal ∧
      ¬ ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n))
    (hfalse : H1930 D → Ctx23L D Ch → ∀ {n : ℕ}, IsPowTwo n → ∀ {A B : Type} [Group A] [Group B],
      (Bar2 (Hinf D.M) ≃* A × B) → (IsL2 A n ∨ IsU3 A n) → IsL2 B n → False) :
    S23_10 D Ch := by
  intro h1930 c hcyc hBZ
  by_contra hcon
  have hneg : ∀ p ∈ D.sig, ∀ P : Subgroup (Bar2 D.M),
      CFSG.ABGLocalTools.IsSylowOf p P (CFSG.fittingSubgroup (Bar2 D.M)) →
        barImage D.M c.B ≤ Subgroup.centralizer (P : Set (Bar2 D.M)) := by
    intro p hp P hP
    by_contra hle
    exact hcon ⟨p, hp, P, hP, hle⟩
  have hoddB : ∀ b ∈ c.B, Odd (orderOf b) := fun b hb =>
    uc22p21d_odd_orderOf_of_mem_calB1 c.hB hb
  obtain ⟨b, hb, hbZ⟩ := SetLike.not_le_iff_exists.mp
    (mt Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hBZ)
  obtain ⟨b', hb', hb'Z, r, e, hr, hr2, hord⟩ :=
    CFSG.GroupTheory.exists_prime_pow_orderOf_not_mem hoddB hb hbZ
  let Fbar : Subgroup (Bar2 D.M) := CFSG.fittingSubgroup (Bar2 D.M)
  have hcycN : IsCyclic ↥(CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))) := by
    haveI : IsCyclic ↥Fbar := hcyc
    have hC₁ : (CFSG.fittingSubgroup ↥(commutator (Bar2 D.M))).map
        (commutator (Bar2 D.M)).subtype =
        commutator (Bar2 D.M) ⊓ Fbar :=
      CFSG.LocalCores.fitting_normal_intersection (commutator (Bar2 D.M))
    have hcycNF : IsCyclic ↥(commutator (Bar2 D.M) ⊓ Fbar) :=
      Subgroup.isCyclic_of_le inf_le_right
    refine (MulEquiv.isCyclic (Subgroup.equivMapOfInjective
      (CFSG.fittingSubgroup ↥(commutator (Bar2 D.M)))
      (commutator (Bar2 D.M)).subtype (commutator (Bar2 D.M)).subtype_injective)).mpr ?_
    rw [hC₁]
    exact hcycNF
  have h1 : ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M :=
    (uc22p21c_commutator_bar_eq_bot_iff D.M).2
      (uc22p21c_commutator_perfectResidual_fitting_eq_bot hcycN)
  have h3 : ∀ p ∈ D.sig, ∃ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (barPreimage D.M (centE D.M)) ∧
        P ≤ Subgroup.normalizer (c.B : Set G) := by
    intro p hp
    haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
    obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (barPreimage D.M (centE D.M))
    have hPnorm : (barImage D.M P).Normal :=
      (h2123 h1930 c.toCtx21 p hp P hP hcycN).2.2.2.1
    have hPp : IsPGroup p (barImage D.M P) := by
      rw [barImage]
      exact (hP.isPGroup.comap_subtype).map _
    have hbar_le_pCore : barImage D.M P ≤ CFSG.pCore p (Bar2 D.M) :=
      le_sSup ⟨hPnorm, hPp⟩
    have hbar_le_F : barImage D.M P ≤ Fbar :=
      hbar_le_pCore.trans (CFSG.pCore_le_fitting (Bar2 D.M) p)
    let A : Subgroup ↥Fbar := (barImage D.M P).subgroupOf Fbar
    have hAp : IsPGroup p A := hPp.comap_subtype
    obtain ⟨S, hAS⟩ := hAp.exists_le_sylow
    have hSyl : CFSG.ABGLocalTools.IsSylowOf p
        ((S : Subgroup ↥Fbar).map Fbar.subtype) Fbar := ⟨S, rfl⟩
    have hBcentS : barImage D.M c.B ≤ Subgroup.centralizer
        (((S : Subgroup ↥Fbar).map Fbar.subtype : Subgroup (Bar2 D.M)) :
          Set (Bar2 D.M)) :=
      hneg p hp _ hSyl
    have hbar_le_S : barImage D.M P ≤ (S : Subgroup ↥Fbar).map Fbar.subtype := by
      intro x hx
      have hxF : x ∈ Fbar := hbar_le_F hx
      have hxA : (⟨x, hxF⟩ : ↥Fbar) ∈ A := hx
      exact ⟨⟨x, hxF⟩, hAS hxA, rfl⟩
    have hBcent : barImage D.M c.B ≤ Subgroup.centralizer
        (barImage D.M P : Set (Bar2 D.M)) :=
      hBcentS.trans (Subgroup.centralizer_le hbar_le_S)
    have hbar_bot : barImage D.M P = ⊥ :=
      uc22s2310_key D Ch h54 h6 h1930 c hr hr2 hb' hb'Z hord p hp _
        hPp hBcent
    have hPleO : P ≤ pCoreOf 2 D.M :=
      le_pCoreOf_of_barImage_eq_bot
        (hP.le.trans (uc22p21c_barPreimage_le D.M (centE D.M))) hbar_bot
    have hP2 : IsPGroup 2 P := (uc22p21c_isPGroup_pCoreOf D.M).to_le hPleO
    have hPbot : P = ⊥ := by
      have hdisj : Disjoint P P :=
        IsPGroup.disjoint_of_ne p 2 (D.sig_prime p hp).2 P P hP.isPGroup hP2
      have h := hdisj.eq_bot
      rwa [inf_idem] at h
    exact ⟨P, hP, by rw [hPbot]; exact bot_le⟩
  have h4 : ∀ p ∈ D.sig, 1 < CFSG.Open.pRank p (barPreimage D.M (centE D.M)) →
      ¬ InvertedIn D.M c.B := by
    intro p hp _
    rintro ⟨m, hmM, hm_inv⟩
    exact (h54 h1930 c b' hb' hb'Z).1 ⟨m, hmM,
      fun a ha => hm_inv a ((Subgroup.zpowers_le.mpr hb') ha)⟩
  have hHyp : Hyp2120 D c.toCtx21 := ⟨h1, h2 h1930 c, h3, h4⟩
  have hBne : c.B ≠ ⊥ := by
    intro hbot
    exact hBZ (by rw [hbot, Subgroup.commutator_bot_left])
  obtain ⟨p, hp⟩ := hsig
  obtain ⟨hHinfEq, -, hex⟩ := h2121 h1930 c.toCtx21 hBne hHyp p hp
  obtain ⟨n, hcases, hn, -, -⟩ := hex
  rcases hcases with
    ⟨⟨A, B, hA, hB, ⟨eAB⟩, hLA, hLB⟩, -⟩ |
    ⟨⟨A, B, hA, hB, ⟨eAB⟩, hUA, hLB⟩, -⟩
  · exact hfalse h1930 c hn (hHinfEq.symm ▸ eAB) (Or.inl hLA) hLB
  · exact hfalse h1930 c hn (hHinfEq.symm ▸ eAB) (Or.inr hUA) hLB

end CFSG.LocalAnalysis.UniquenessCase.UC22
