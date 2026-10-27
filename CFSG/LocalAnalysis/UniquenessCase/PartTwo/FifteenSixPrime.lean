module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixGlue
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSixOrder
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Six_not_pow_three_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ^ 3 ∣ 2 * 168 ^ 2 := by
  intro h
  have hp1 : p ∣ 2 * 168 ^ 2 := (dvd_pow_self p (by norm_num)).trans h
  have h56 : 2 * 168 ^ 2 = 2 ^ 7 * 3 ^ 2 * 7 ^ 2 := by norm_num
  rw [h56] at hp1 h
  rcases (Nat.Prime.dvd_mul hp).1 hp1 with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2))
    · have : p = 3 :=
        (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      subst this
      norm_num at h
  · have : p = 7 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 (hp.dvd_of_dvd_pow h1)
    subst this
    norm_num at h

theorem s15_Six_exists_order_ker (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrk : 3 ≤ CFSG.Open.pRank p D.M)
    (hcard : Nat.card (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) ∣ 2 * 168 ^ 2) :
    ∃ y ∈ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V, orderOf y = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set V₁ := v1Sub D.M V₀ V hV L with hV₁
  have hMs : D.M ≤ stabTil V₁ V :=
    le_stabTil h.pairFacts.le_normalizer (s15_Infra_le_normalizer_v1Sub h hV)
  obtain ⟨E, hEM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt D.M
  by_contra hno
  let φ : ↥E →* ↥(Mbar D.M V₁ V hV) :=
    ((actTil V₁ V hV).comp (Subgroup.inclusion (hEM.trans hMs))).codRestrict
      (Mbar D.M V₁ V hV) fun e => actTil_mem_barSub V₁ V hV (hEM e.2) (hMs (hEM e.2))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    have hord : orderOf (e : G) = p := by
      refine orderOf_eq_prime (hE.2 e e.2) ?_
      intro h1
      exact hne (Subtype.ext h1)
    refine hno ⟨(e : G), ?_, hord⟩
    have hker : actTil V₁ V hV ⟨(e : G), hMs (hEM e.2)⟩ = 1 := by
      have := congrArg Subtype.val he
      exact this
    have hcomm := (actTil_eq_one_iff V₁ V hV ⟨(e : G), hMs (hEM e.2)⟩).1 hker
    refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
    exact ⟨hEM e.2, stabTil_le_normalizer₀ V₁ V (hMs (hEM e.2)), hcomm v hv⟩
  have h1 : Nat.card E ∣ 2 * 168 ^ 2 := (Subgroup.card_dvd_of_injective φ hinj).trans hcard
  rw [hEcard] at h1
  exact s15_Six_not_pow_three_dvd hp hp2 ((pow_dvd_pow p hrk).trans h1)

theorem s15_Six_comm_of_order_ker {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V) (hV₀ : V₀ ≤ V)
    (hV₀card : Nat.card V₀ ≤ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : G}
    (hy : y ∈ F11.CTilde M V₀ V) (hord : orderOf y = p) {u : G} (hu : u ∈ V) :
    y * u = u * y := by
  obtain ⟨hyM, hyN, hc⟩ : y ∈ F11.CElt M V₀ u :=
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy u) hu
  by_contra hne
  have hc1 : y * u * y⁻¹ * u⁻¹ ≠ 1 := by
    intro h1
    apply hne
    have h2 : y * u * y⁻¹ = u := mul_inv_eq_one.1 h1
    calc y * u = (y * u * y⁻¹) * y := by group
      _ = u * y := by rw [h2]
  set c := y * u * y⁻¹ * u⁻¹ with hcdef
  have hcV : c ∈ V := hV₀ hc
  have hc2 : c * c = 1 := by
    have := hV.2 c hcV
    rwa [pow_two] at this
  have hycy : y * c * y⁻¹ = c := by
    have hmem : y * c * y⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.1 hyN c).1 hc
    have hne1 : y * c * y⁻¹ ≠ 1 := by
      intro h1
      apply hc1
      have : y * c * y⁻¹ = 1 := h1
      calc c = y⁻¹ * (y * c * y⁻¹) * y := by group
        _ = 1 := by rw [this]; group
    have hcard2 : Nat.card V₀ = 2 := by
      refine le_antisymm hV₀card ?_
      have h1 : (1 : ℕ) < Nat.card V₀ := by
        refine Finite.one_lt_card_iff_nontrivial.2 ⟨⟨⟨c, hc⟩, 1, ?_⟩⟩
        intro h
        exact hc1 (congrArg Subtype.val h)
      omega
    obtain ⟨z, hz, hzu⟩ := (Nat.card_eq_two_iff' (1 : V₀)).1 hcard2
    have h1 : (⟨y * c * y⁻¹, hmem⟩ : V₀) = ⟨c, hc⟩ := by
      have e1 := hzu ⟨y * c * y⁻¹, hmem⟩ (fun h => hne1 (congrArg Subtype.val h))
      have e2 := hzu ⟨c, hc⟩ (fun h => hc1 (congrArg Subtype.val h))
      rw [e1, e2]
    exact congrArg Subtype.val h1
  have hpow : ∀ k : ℕ, y ^ k * u * (y ^ k)⁻¹ = c ^ k * u := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hcu : y * u * y⁻¹ = c * u := by rw [hcdef]; group
      have hyk : y * (c ^ k) * y⁻¹ = c ^ k := by
        have := congrArg (fun z => z ^ k) hycy
        simpa [conj_pow] using this
      calc y ^ (k + 1) * u * (y ^ (k + 1))⁻¹
          = y * (y ^ k * u * (y ^ k)⁻¹) * y⁻¹ := by group
        _ = y * (c ^ k * u) * y⁻¹ := by rw [ih]
        _ = (y * c ^ k * y⁻¹) * (y * u * y⁻¹) := by group
        _ = c ^ k * (c * u) := by rw [hyk, hcu]
        _ = c ^ (k + 1) * u := by group
  have hyp : y ^ p = 1 := hord ▸ pow_orderOf_eq_one y
  have hp1 := hpow p
  rw [hyp] at hp1
  simp only [inv_one, mul_one, one_mul] at hp1
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨m, hm⟩ := hodd
  have hcp : c ^ p = c := by
    rw [hm, pow_succ, pow_mul, pow_two, hc2]
    simp
  rw [hcp] at hp1
  exact hc1 (by
    have : c = 1 := by
      have h3 : c * u = 1 * u := by simpa using hp1.symm
      exact mul_right_cancel h3
    exact this)

theorem s15_Six_star_of_prime (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {p : ℕ}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) {y : G} (hyM : y ∈ D.M)
    (hord : orderOf y = p) (hy : ∀ u ∈ V, y * u = u * y) : s15SixStar D V₀ V L hV := by
  intro h' hh'
  rw [Subgroup.eq_bot_iff_forall]
  intro v hv
  by_contra hv1
  obtain ⟨hvW, hvV'⟩ := Subgroup.mem_inf.1 hv
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_Infra_v1Sub_le h.hyp151.hyp125 hV)
  have hu : h' * v * h'⁻¹ ∈ V := mem_conjSubgroup_iff.1 hvV'
  have hv2 : ∃ n : ℕ, v ^ (2 ^ n) = 1 := ⟨1, by simpa using hV.2 v (hWV hvW)⟩
  have hcent : centralizer ({v} : Set G) ≤ D.M :=
    (centralizer_le_of_uniqueMax D.maxLocal hv1 hv2 (h.unique₁ v hvW hv1)).1
  have hy'c : h'⁻¹ * y * h' ∈ centralizer ({v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := hy _ hu
    calc h'⁻¹ * y * h' * v = h'⁻¹ * (y * (h' * v * h'⁻¹)) * h' := by group
      _ = h'⁻¹ * ((h' * v * h'⁻¹) * y) * h' := by rw [h1]
      _ = v * (h'⁻¹ * y * h') := by group
  have hy'M : h'⁻¹ * y * h' ∈ D.M := hcent hy'c
  have hy'M' : h'⁻¹ * y * h' ∈ conjSubgroup D.M h' := by
    rw [mem_conjSubgroup_iff]
    have : h' * (h'⁻¹ * y * h') * h'⁻¹ = y := by group
    rw [this]
    exact hyM
  have hord' : orderOf (h'⁻¹ * y * h') = p := by
    rw [← hord]
    refine SemiconjBy.orderOf_eq h' ?_
    show h' * (h'⁻¹ * y * h') = y * h'
    group
  have hdvd : p ∣ Nat.card ↥(D.M ⊓ conjSubgroup D.M h') := by
    rw [← hord']
    exact Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.2 ⟨hy'M, hy'M'⟩)
  exact hsp.2.2 h'⁻¹ (fun hm => hh' (by simpa using D.M.inv_mem hm)) hdvd

theorem s15_Six_star (D : Data G) (h1217 : R1217 D) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hs : s15 D.M V₀ V hV L = 2) (hγ : gamma15 D.M V₀ V hV L = 3)
    (hδ : delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1) :
    s15SixStar D V₀ V L hV := by
  obtain ⟨p, hpsig⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpsig
  have hcard := s15_Six_card_mbar_dvd D h1217 h.hyp151 hV hL hγ hs
  obtain ⟨y, hy, hord⟩ :=
    s15_Six_exists_order_ker D h.hyp151.hyp125 hV hp hp2 (hSg.three_le p hpsig) hcard
  rw [fifteen_two_cent D h1217 h.hyp151 hV] at hy
  have hV₀V : V₀ ≤ V := h.hyp151.hyp125.pairFacts.le
  have hV₀card : Nat.card V₀ ≤ 2 := by
    have h3 := card_eq_two_pow_mSub (hV.isPGroup.to_le hV₀V)
    have hle : V₀ ≤ v1Sub D.M V₀ V hV L ⊓ wSub V₀ V hV L :=
      le_inf (s15_Infra_le_v1Sub D.M V₀ V hV L) (s15_Two_le_wSub hV hV₀V L)
    have h4 : mSub V₀ ≤ delta15 D.M V₀ V hV L := rk_mono hle
    have h5 : mSub V₀ ≤ 1 := by omega
    rw [h3]
    calc 2 ^ mSub V₀ ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h5
      _ = 2 := by norm_num
  have hyM : y ∈ D.M := (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy 1) V.one_mem).1
  exact s15_Six_star_of_prime D h hV (hSg.sig1_sp p (h1219 ▸ hpsig)) hyM hord fun u hu =>
    s15_Six_comm_of_order_ker hV hV₀V hV₀card hp hp2 hy hord hu

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
