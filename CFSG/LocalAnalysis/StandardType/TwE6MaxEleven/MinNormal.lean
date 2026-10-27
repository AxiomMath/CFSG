module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Local
public import CFSG.GroupTheory.PCentralElement
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.CharacterTheory.Burnside
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs

public section

namespace CFSG.StandardType.TwE6MaxEleven

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem exists_minNormal_le {M K : Subgroup X} (hK1 : K ≠ ⊥) (hKM : K ≤ M)
    (hMK : M ≤ normalizer (K : Set X)) :
    ∃ N : Subgroup X, N ≤ K ∧ N ≠ ⊥ ∧ N ≤ M ∧ M ≤ normalizer (N : Set X) ∧
      ∀ L : Subgroup X, L ≠ ⊥ → L ≤ N → M ≤ normalizer (L : Set X) → L = N := by
  classical
  let S : Set (Subgroup X) := {L | L ≠ ⊥ ∧ L ≤ K ∧ M ≤ normalizer (L : Set X)}
  have hne : S.Nonempty := ⟨K, hK1, le_rfl, hMK⟩
  obtain ⟨N, ⟨hN1, hNK, hMN⟩, hmin⟩ :=
    (measure fun L : Subgroup X => Nat.card L).wf.has_min S hne
  refine ⟨N, hNK, hN1, hNK.trans hKM, hMN, fun L hL1 hLN hML => ?_⟩
  have h1 : ¬ Nat.card L < Nat.card N := hmin L ⟨hL1, hLN.trans hNK, hML⟩
  exact Subgroup.eq_of_le_of_card_ge hLN (not_lt.mp h1)

theorem minNormal_isElemAbelian {M N : Subgroup X} {p : ℕ} (hp : p.Prime) (hNp : IsPGroup p N)
    (hN1 : N ≠ ⊥) (hNM : N ≤ M) (hMN : M ≤ normalizer (N : Set X))
    (hmin : ∀ L : Subgroup X, L ≠ ⊥ → L ≤ N → M ≤ normalizer (L : Set X) → L = N) :
    (∀ a ∈ N, a ^ p = 1) ∧ ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hNn : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  have hN'1 : N.subgroupOf M ≠ ⊥ := by
    intro h
    apply hN1
    have h1 := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hNM, Subgroup.map_bot] at h1
  have hmin' : ∀ K : Subgroup ↥M, K.Normal → K ≤ N.subgroupOf M →
      K = ⊥ ∨ K = N.subgroupOf M := by
    intro K hK hKN
    by_cases hK1 : K = ⊥
    · exact Or.inl hK1
    · right
      have hK'map : K.map M.subtype ≤ N := (Subgroup.map_le_iff_le_comap).mpr hKN
      have hK'1 : K.map M.subtype ≠ ⊥ := by
        intro h
        exact hK1 ((Subgroup.map_eq_bot_iff_of_injective K M.subtype_injective).mp h)
      have hK'norm : M ≤ normalizer ((K.map M.subtype : Subgroup X) : Set X) := by
        have hsub : (K.map M.subtype).subgroupOf M = K :=
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective K
        have hKn : ((K.map M.subtype).subgroupOf M).Normal := by
          rw [hsub]
          exact hK
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le K)).mp hKn
      have heq : K.map M.subtype = N := hmin _ hK'1 hK'map hK'norm
      have hsub : (K.map M.subtype).subgroupOf M = K :=
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective K
      rw [heq] at hsub
      exact hsub.symm
  have hNp' : IsPGroup p (N.subgroupOf M) :=
    hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNM).symm
  have hEA : IsElementaryAbelian p (N.subgroupOf M) :=
    CFSG.isElementaryAbelian_of_minimalNormal hNn hNp' hN'1 hmin'
  haveI : IsElementaryAbelian p (N.subgroupOf M) := hEA
  have hEA' : IsElementaryAbelian p N := by
    have h := CFSG.IsElementaryAbelian.map_subtype (p := p) (K := M) (H := N.subgroupOf M)
    rwa [Subgroup.map_subgroupOf_eq_of_le hNM] at h
  haveI : IsElementaryAbelian p N := hEA'
  constructor
  · intro a ha
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian a ha
  · intro a ha b hb
    exact congrArg Subtype.val ((isMulCommutative_iff.mp hEA'.toIsMulCommutative) ⟨a, ha⟩ ⟨b, hb⟩)

private theorem exists_prime_ge_five_dvd_card_of_not_isSolvable' {Y : Type*} [Group Y] [Finite Y]
    (h : ¬ Group.IsSolvable Y) : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧ r ∣ Nat.card Y := by
  by_contra hcon
  push Not at hcon
  apply h
  have hn : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have hpf : ∀ r : ℕ, r.Prime → r ∣ Nat.card Y → r = 2 ∨ r = 3 := by
    intro r hr hrd
    by_contra hne
    push Not at hne
    have h5 : 5 ≤ r := by
      have h2 := hr.two_le
      have h4 : r ≠ 4 := by
        rintro rfl
        norm_num at hr
      omega
    exact hcon r hr h5 hrd
  have hcard : Nat.card Y =
      2 ^ (Nat.card Y).factorization 2 * 3 ^ (Nat.card Y).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod_of_support_subset _ (s := {2, 3}) ?_ _ (fun _ _ => pow_zero _),
      Finset.prod_pair (by norm_num)]
    intro r hr
    rw [Nat.support_factorization] at hr
    have := hpf r (Nat.prime_of_mem_primeFactors hr) (Nat.dvd_of_mem_primeFactors hr)
    simpa using this
  letI := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, hcard])

private theorem exists_simple_factors {M N : Subgroup X} (hN1 : N ≠ ⊥) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set X))
    (hmin : ∀ L : Subgroup X, L ≠ ⊥ → L ≤ N → M ≤ normalizer (L : Set X) → L = N) :
    ∃ (r : ℕ) (T : Fin r → Subgroup X), 0 < r ∧ (⨆ i, T i) = N ∧
      (∀ i, IsSimpleGroup (T i)) ∧
      (∀ i j, ∃ m ∈ M, T j = CFSG.conjugate (T i) m) ∧
      Nat.card N = ∏ i, Nat.card (T i) := by
  classical
  have hNn : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  have hN'1 : N.subgroupOf M ≠ ⊥ := by
    intro h
    apply hN1
    have h1 := congrArg (Subgroup.map M.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hNM, Subgroup.map_bot] at h1
  have hmin' : ∀ K : Subgroup ↥M, K.Normal → K ≤ N.subgroupOf M →
      K = ⊥ ∨ K = N.subgroupOf M := by
    intro K hK hKN
    by_cases hK1 : K = ⊥
    · exact Or.inl hK1
    · right
      have hK'map : K.map M.subtype ≤ N := (Subgroup.map_le_iff_le_comap).mpr hKN
      have hK'1 : K.map M.subtype ≠ ⊥ := by
        intro h
        exact hK1 ((Subgroup.map_eq_bot_iff_of_injective K M.subtype_injective).mp h)
      have hK'norm : M ≤ normalizer ((K.map M.subtype : Subgroup X) : Set X) := by
        have hsub : (K.map M.subtype).subgroupOf M = K :=
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective K
        have hKn : ((K.map M.subtype).subgroupOf M).Normal := by
          rw [hsub]
          exact hK
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le K)).mp hKn
      have heq : K.map M.subtype = N := hmin _ hK'1 hK'map hK'norm
      have hsub : (K.map M.subtype).subgroupOf M = K :=
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective K
      rw [heq] at hsub
      exact hsub.symm
  obtain ⟨r, S, hr, hSN, hSsimple, hSconj, -, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hNn hN'1 hmin'
  have hcommS : Pairwise fun i j => ∀ x y : ↥M, x ∈ S i → y ∈ S j → Commute x y := by
    intro i j hij x y hx hy
    have h1 := Pi.mulSingle_commute (f := fun k => S k) hij ⟨x, hx⟩ ⟨y, hy⟩
    have h2 := congrArg (fun z => ((e z : N.subgroupOf M) : ↥M)) h1.eq
    simp only [map_mul, Subgroup.coe_mul] at h2
    rwa [he i _ fun k hk => Pi.mulSingle_eq_of_ne hk _,
      he j _ fun k hk => Pi.mulSingle_eq_of_ne hk _, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_same] at h2
  set φ : ((i : Fin r) → S i) →* ↥M := Subgroup.noncommPiCoprod hcommS with hφ
  have hφe : φ = (N.subgroupOf M).subtype.comp e.toMonoidHom := by
    refine MonoidHom.pi_ext fun i x => ?_
    rw [hφ, Subgroup.noncommPiCoprod_mulSingle, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulEquiv.coe_toMonoidHom, he i _ fun k hk => Pi.mulSingle_eq_of_ne hk _,
      Pi.mulSingle_eq_same]
  have hsupS : (⨆ i, S i) = N.subgroupOf M := by
    have hrange : φ.range = N.subgroupOf M := by
      rw [hφe]
      ext z
      constructor
      · rintro ⟨x, rfl⟩
        exact (e x).2
      · intro hz
        exact ⟨e.symm ⟨z, hz⟩, by simp⟩
    rw [← hrange, hφ, Subgroup.noncommPiCoprod_range]
  let T : Fin r → Subgroup X := fun i => (S i).map M.subtype
  have hsupT : (⨆ i, T i) = N := by
    rw [← Subgroup.map_iSup, hsupS, Subgroup.map_subgroupOf_eq_of_le hNM]
  have hTsimple : ∀ i, IsSimpleGroup (T i) := fun i =>
    ((S i).equivMapOfInjective M.subtype M.subtype_injective).symm.isSimpleGroup
  have hTconj : ∀ i j, ∃ m ∈ M, T j = CFSG.conjugate (T i) m := by
    intro i j
    obtain ⟨g, hg⟩ := hSconj i j
    refine ⟨(g : X), g.2, ?_⟩
    show (S j).map M.subtype = CFSG.conjugate ((S i).map M.subtype) (g : X)
    rw [hg, CFSG.conjugate, CFSG.conjugate, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hcardN : Nat.card N = ∏ i, Nat.card (T i) := by
    calc
      Nat.card N = Nat.card ↥(N.subgroupOf M) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv).symm
      _ = Nat.card ((i : Fin r) → ↥(S i)) := (Nat.card_congr e.toEquiv).symm
      _ = ∏ i, Nat.card ↥(S i) := Nat.card_pi
      _ = ∏ i, Nat.card ↥(T i) :=
        Finset.prod_congr rfl fun i _ =>
          (Subgroup.card_map_of_injective M.subtype_injective).symm
  exact ⟨r, T, hr, hsupT, hTsimple, hTconj, hcardN⟩

theorem minNormal_isPGroup_or_simple (hX : LocalFacts X) {M N : Subgroup X} {t : X}
    (htM : t ∈ M) (ht : orderOf t = 11) (hN1 : N ≠ ⊥) (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set X))
    (hmin : ∀ L : Subgroup X, L ≠ ⊥ → L ≤ N → M ≤ normalizer (L : Set X) → L = N) :
    (∃ p : ℕ, p.Prime ∧ IsPGroup p N) ∨
      (IsSimpleGroup N ∧ (∃ a b : N, a * b ≠ b * a) ∧ t ∈ N) := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨r, T, hr, hsupT, hTsimple, hTconj, hcardN⟩ :=
    exists_simple_factors hN1 hNM hMN hmin
  haveI : NeZero r := ⟨hr.ne'⟩
  have hcard_conj : ∀ (H : Subgroup X) (g : X), Nat.card (CFSG.conjugate H g) = Nat.card H := by
    intro H g
    rw [CFSG.conjugate]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcard_eq : ∀ i j, Nat.card (T i) = Nat.card (T j) := by
    intro i j
    obtain ⟨m, -, hm⟩ := hTconj i j
    rw [hm, hcard_conj]
  have hNpow : Nat.card N = (Nat.card (T 0)) ^ r := by
    rw [hcardN, Finset.prod_congr rfl fun i _ => hcard_eq i 0, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  have hT0N : T 0 ≤ N := hsupT ▸ le_iSup T 0
  have h11sqX : ¬ 11 ^ 2 ∣ Nat.card X := by
    rw [hX.card]
    norm_num
  have h11sqN : ¬ 11 ^ 2 ∣ Nat.card N := by
    intro h
    exact h11sqX (h.trans ((Subgroup.card_dvd_of_le hNM).trans (by
      have := Subgroup.card_dvd_of_le (le_top : M ≤ ⊤)
      rwa [Subgroup.card_top] at this)))
  by_cases hcomm : ∀ a b : ↥(T 0), a * b = b * a
  · haveI : IsMulCommutative ↥(T 0) := IsMulCommutative.of_comm hcomm
    have hp : (Nat.card (T 0)).Prime := Group.is_simple_iff_prime_card.mp (hTsimple 0)
    haveI : Fact (Nat.card (T 0)).Prime := ⟨hp⟩
    exact Or.inl ⟨Nat.card (T 0), hp, IsPGroup.iff_card.mpr ⟨r, hNpow⟩⟩
  · push Not at hcomm
    have hnsol : ¬ Group.IsSolvable ↥(T 0) := by
      intro hsol
      obtain ⟨a, b, hab⟩ := hcomm
      exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr hsol a b)
    obtain ⟨q, hq, hq5, hqT0⟩ := exists_prime_ge_five_dvd_card_of_not_isSolvable' hnsol
    have hqN : q ∣ Nat.card N := hqT0.trans (Subgroup.card_dvd_of_le hT0N)
    have h11N : 11 ∣ Nat.card N := by
      by_contra h11N
      have hq11 : q ≠ 11 := by
        intro hq11
        exact h11N (hq11 ▸ hqN)
      haveI : Fact q.Prime := ⟨hq⟩
      let P : Sylow q ↥N := Classical.choice (Sylow.nonempty (p := q) (G := ↥N))
      let R : Subgroup X := (P : Subgroup ↥N).map N.subtype
      have hRq : IsPGroup q R := P.isPGroup'.map N.subtype
      have hRN : R ≤ N := Subgroup.map_subtype_le _
      have hRcard : Nat.card R = q ^ (Nat.card N).factorization q := by
        rw [Subgroup.card_map_of_injective N.subtype_injective]
        exact Sylow.card_eq_multiplicity P
      have hdvdM : Nat.card M ∣ Nat.card N * Nat.card (normalizer (R : Set X)) :=
        card_dvd_card_mul_card_normalizer hNM hMN hRN hRcard
      have h11M : 11 ∣ Nat.card M := by
        have hle : Subgroup.zpowers t ≤ M := Subgroup.zpowers_le.mpr htM
        have h := Subgroup.card_dvd_of_le hle
        rwa [Nat.card_zpowers, ht] at h
      have h11norm : 11 ∣ Nat.card (normalizer (R : Set X)) := by
        have h := (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 11)).mp (h11M.trans hdvdM)
        exact h.resolve_left h11N
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := normalizer (R : Set X)) 11 h11norm
      have huX : orderOf (u : X) = 11 := by rw [Subgroup.orderOf_coe, hu]
      have hq2 : q ≠ 2 := by omega
      have hq3 : q ≠ 3 := by omega
      have hRbot : R = ⊥ := eq_bot_of_isPGroup_of_mem_normalizer hX huX hq hq2 hq3 hq11 hRq u.2
      have hk1 : 1 ≤ (Nat.card N).factorization q :=
        (Nat.Prime.dvd_iff_one_le_factorization hq Nat.card_pos.ne').mp hqN
      have hqR : q ∣ Nat.card R := hRcard ▸ (by simpa using pow_dvd_pow q hk1)
      have hRcard1 : Nat.card R = 1 := by rw [hRbot, Subgroup.card_bot]
      rw [hRcard1] at hqR
      exact hq.ne_one (Nat.dvd_one.mp hqR)
    have h11T0 : 11 ∣ Nat.card (T 0) :=
      Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 11) (hNpow ▸ h11N)
    have h11rN : 11 ^ r ∣ Nat.card N :=
      hNpow ▸ pow_dvd_pow_of_dvd h11T0 r
    have hr1 : r = 1 := by
      have h2 : ¬ 2 ≤ r := by
        intro h2
        exact h11sqN ((pow_dvd_pow 11 h2).trans h11rN)
      omega
    haveI : Subsingleton (Fin r) := by
      rw [hr1]
      infer_instance
    have hsup1 : (⨆ i, T i) = T 0 := by
      apply le_antisymm
      · exact iSup_le fun i => by rw [Subsingleton.elim i 0]
      · exact le_iSup T 0
    have hN_eq : N = T 0 := hsupT.symm.trans hsup1
    have htN : t ∈ N := by
      by_contra htN
      have hdisj : zpowers t ⊓ N = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        obtain ⟨hxT, hxN⟩ := Subgroup.mem_inf.mp hx
        by_contra hx1
        have hxord : orderOf x = 11 := by
          have hdvd : orderOf x ∣ 11 := by
            simpa [ht] using orderOf_dvd_of_mem_zpowers hxT
          exact (Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 11) _ hdvd).resolve_left
            (fun h => hx1 (orderOf_eq_one_iff.mp h))
        have hle : zpowers x ≤ zpowers t := Subgroup.zpowers_le.mpr hxT
        have heq : zpowers x = zpowers t :=
          Subgroup.eq_of_le_of_card_ge hle (by
            rw [Nat.card_zpowers, Nat.card_zpowers, hxord, ht])
        exact htN (Subgroup.zpowers_le.mpr hxN (heq.symm ▸ Subgroup.mem_zpowers t))
      have hleN : zpowers t ≤ normalizer (N : Set X) :=
        (Subgroup.zpowers_le.mpr htM).trans hMN
      have hform :=
        CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
          (G := X) (H := zpowers t) (K := N) hleN
      rw [hdisj, Subgroup.card_bot, Nat.card_zpowers, ht, mul_one] at hform
      have hform' : Nat.card (N ⊔ zpowers t : Subgroup X) = 11 * Nat.card N := by
        rw [sup_comm]
        simpa using hform
      have h11sqH : 11 ^ 2 ∣ Nat.card (N ⊔ zpowers t : Subgroup X) := by
        rw [hform']
        simpa [pow_two] using mul_dvd_mul_left 11 h11N
      have hHX : Nat.card (N ⊔ zpowers t : Subgroup X) ∣ Nat.card X := by
        have hHM : (N ⊔ zpowers t : Subgroup X) ≤ M := sup_le hNM (Subgroup.zpowers_le.mpr htM)
        exact (Subgroup.card_dvd_of_le hHM).trans (by
          have := Subgroup.card_dvd_of_le (le_top : M ≤ ⊤)
          rwa [Subgroup.card_top] at this)
      exact h11sqX (h11sqH.trans hHX)
    rw [hN_eq]
    exact Or.inr ⟨hTsimple 0, hcomm, hN_eq ▸ htN⟩

end CFSG.StandardType.TwE6MaxEleven
