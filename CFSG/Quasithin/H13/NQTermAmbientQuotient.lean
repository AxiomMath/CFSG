module

public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Quasithin.SteinbergCDCentralQuotientCore
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.Quasithin.H13.NQTerm

open Subgroup CFSG.Open
open scoped Pointwise

theorem comap_pCore_eq_of_isPGroup_ker {U V : Type*} [Group U] [Group V] [Finite U] {p : ℕ}
    (f : U →* V) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    (CFSG.pCore p V).comap f = CFSG.pCore p U := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.pCore_normal (p := p) (G := V)).comap f,
      (CFSG.pCore_isPGroup (p := p) (G := V)).comap_of_ker_isPGroup f hk⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_sSup ⟨(CFSG.pCore_normal (p := p) (G := U)).map f hf,
      (CFSG.pCore_isPGroup (p := p) (G := U)).map f⟩

theorem exists_pCore_quotient_mulEquiv {U V : Type*} [Group U] [Group V] [Finite U] {p : ℕ}
    (f : U →* V) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    ∃ e : (U ⧸ CFSG.pCore p U) ≃* (V ⧸ CFSG.pCore p V),
      ∀ u : U, e u = ((f u : V) : V ⧸ CFSG.pCore p V) := by
  have hg : Function.Surjective ((QuotientGroup.mk' (CFSG.pCore p V)).comp f) :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hker : CFSG.pCore p U = ((QuotientGroup.mk' (CFSG.pCore p V)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_pCore_eq_of_isPGroup_ker f hf hk]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hg), fun _ => rfl⟩

theorem isQuasisimple_pCore_quotient_iff {U V : Type*} [Group U] [Group V] [Finite U] {p : ℕ}
    (f : U →* V) (hf : Function.Surjective f) (hk : IsPGroup p f.ker) :
    CFSG.IsQuasisimple (U ⧸ CFSG.pCore p U) ↔ CFSG.IsQuasisimple (V ⧸ CFSG.pCore p V) := by
  obtain ⟨e, -⟩ := exists_pCore_quotient_mulEquiv f hf hk
  exact CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e

theorem isQuasisimple_pCore_quotient_congr {U V : Type*} [Group U] [Group V] [Finite U] {p : ℕ}
    (e : U ≃* V) :
    CFSG.IsQuasisimple (U ⧸ CFSG.pCore p U) ↔ CFSG.IsQuasisimple (V ⧸ CFSG.pCore p V) := by
  refine isQuasisimple_pCore_quotient_iff e.toMonoidHom e.surjective ?_
  have : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  rw [this]
  exact IsPGroup.of_bot

theorem isPGroup_ker_subgroupMap {G G' : Type*} [Group G] [Group G'] {p : ℕ} (η : G →* G')
    (X : Subgroup G) (h : IsPGroup p ↥(X ⊓ η.ker)) : IsPGroup p (η.subgroupMap X).ker := by
  refine h.of_injective ((X.subtype.comp (η.subgroupMap X).ker.subtype).codRestrict (X ⊓ η.ker)
    fun x => ⟨(x.1).2, ?_⟩) fun x y hxy => ?_
  · have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
    exact h1
  · have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)

theorem map_mem_cComp_of_isSolvable_ker {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
    (η : G →* G') (hker : Group.IsSolvable η.ker) {X L : Subgroup G} (hL : L ∈ cComp X) :
    L.map η ∈ cComp (X.map η) := by
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hφk : Group.IsSolvable (η.subgroupMap X).ker := by
    refine Group.isSolvable_of_isSolvable_injective (f := ((X.subtype.comp
      (η.subgroupMap X).ker.subtype).codRestrict η.ker fun x =>
        congrArg Subtype.val (MonoidHom.mem_ker.mp x.2))) fun x y hxy => ?_
    have := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext this)
  have h2 := map_mem_cComp_top (η.subgroupMap X) (η.subgroupMap_surjective X) hφk
    (subgroupOf_mem_cComp hL)
  have h3 := map_subtype_mem_cComp h2
  have heq : ((L.subgroupOf X).map (η.subgroupMap X)).map (X.map η).subtype = L.map η := by
    rw [Subgroup.map_map]
    have hc : (X.map η).subtype.comp (η.subgroupMap X) = η.comp X.subtype :=
      MonoidHom.ext fun _ => rfl
    rw [hc, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hLX]
  rwa [heq] at h3

variable {K : Type} [Group K] [Finite K]

theorem not_dvd_card_pCore_two_of_ne {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ p ∣ Nat.card (CFSG.pCore 2 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := K))
  rw [hk] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))


theorem two_core_quotient_facts
    (hK : CFSG.SectionRank.IsSQTKCat K)
    (hQ : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) :
    CFSG.SectionRank.IsSQTKCat (K ⧸ CFSG.pCore 2 K) ∧
      (Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 1 ∨
        Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 3) ∧
      IsStronglyQuasithin ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQK : CFSG.SectionRank.IsSQTKCat (K ⧸ CFSG.pCore 2 K) := ⟨fun p hp hp2 => by
      rw [CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp _
        (not_dvd_card_pCore_two_of_ne hp hp2)]
      exact hK.1 p hp hp2,
    CFSG.SectionRank.IsKGroupCat.quotient hK.2 _⟩
  have hQ2 : CFSG.pCore 2 (K ⧸ CFSG.pCore 2 K) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hZodd : Odd (Nat.card (center (K ⧸ CFSG.pCore 2 K))) := by
    rw [Nat.odd_iff]
    by_contra hev
    have h2d : 2 ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := by omega
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2d
    have hzc : Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K) ≤ center (K ⧸ CFSG.pCore 2 K) :=
      (Subgroup.zpowers_le).mpr z.2
    have hzp : IsPGroup 2 (Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one])
    have hle : Subgroup.zpowers (z : K ⧸ CFSG.pCore 2 K) ≤ CFSG.pCore 2 (K ⧸ CFSG.pCore 2 K) :=
      le_sSup ⟨Subgroup.normal_of_le_center hzc, hzp⟩
    rw [hQ2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    have h1 : orderOf z = 1 := by rw [← Subgroup.orderOf_coe, hle, orderOf_one]
    omega
  obtain ⟨hZ13, hSQT⟩ := CFSG.SectionRank.catalogStepHyp _ hQ hQK hZodd
  exact ⟨hQK, hZ13, hSQT (center (K ⧸ CFSG.pCore 2 K)) le_rfl⟩

theorem isSolvable_ker_two_core_center :
    Group.IsSolvable ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K))).ker := by
  have hNle : CFSG.pCore 2 K ≤ ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K))).ker := fun n hn => by
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 K)) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, h1, map_one]
  let g : ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K))).ker →* center (K ⧸ CFSG.pCore 2 K) :=
    ((QuotientGroup.mk' (CFSG.pCore 2 K)).comp (MonoidHom.ker _).subtype).codRestrict _
      fun x => (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)
  have hfg : g.ker ≤ (Subgroup.inclusion hNle).range := by
    intro x hx
    have h1 : (QuotientGroup.mk' (CFSG.pCore 2 K)) (x : K) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩
  have : Group.IsNilpotent (CFSG.pCore 2 K) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact (CFSG.pCore_isPGroup (p := 2) (G := K)).isNilpotent
  have : Group.IsSolvable (center (K ⧸ CFSG.pCore 2 K)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a)
  exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNle) g hfg

theorem ambient_quotient_sylow_and_component {T A : Subgroup K} (hT : quasithinIsSylowTwo T)
    (hA : A ∈ cComp (A ⊔ T)) (hAq : ¬ CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A)) :
    quasithinIsSylowTwo (T.map ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 K)))) ∧
      A.map ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
          (QuotientGroup.mk' (CFSG.pCore 2 K))) ∈
        cComp (A.map ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
          (QuotientGroup.mk' (CFSG.pCore 2 K))) ⊔
          T.map ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
            (QuotientGroup.mk' (CFSG.pCore 2 K)))) ∧
      ¬ CFSG.IsQuasisimple (A.map ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
          (QuotientGroup.mk' (CFSG.pCore 2 K))) ⧸
        CFSG.pCore 2 (A.map ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
          (QuotientGroup.mk' (CFSG.pCore 2 K))))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ν := QuotientGroup.mk' (CFSG.pCore 2 K) with hν
  set σ := QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K)) with hσ
  have hη : Function.Surjective (σ.comp ν) :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  refine ⟨?_, ?_, ?_⟩
  · let TS := (hT.1.toSylow hT.2).mapSurjective hη
    exact ⟨TS.isPGroup', TS.not_dvd_index⟩
  · have h1 := map_mem_cComp_of_isSolvable_ker (σ.comp ν) isSolvable_ker_two_core_center hA
    rwa [Subgroup.map_sup] at h1
  ·
    have hk1 : IsPGroup 2 (ν.subgroupMap A).ker := by
      refine isPGroup_ker_subgroupMap ν A ((CFSG.pCore_isPGroup (p := 2) (G := K)).to_le ?_)
      rw [hν, QuotientGroup.ker_mk']
      exact inf_le_right
    have h1 := isQuasisimple_pCore_quotient_iff (ν.subgroupMap A) (ν.subgroupMap_surjective A)
      hk1
    have hZc : (σ.subgroupMap (A.map ν)).ker ≤ center (A.map ν) := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro g
      have h2 : σ (z : K ⧸ CFSG.pCore 2 K) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
      have h3 : (z : K ⧸ CFSG.pCore 2 K) ∈ center (K ⧸ CFSG.pCore 2 K) :=
        (QuotientGroup.eq_one_iff _).mp h2
      exact Subtype.ext ((Subgroup.mem_center_iff.mp h3) g)
    have hperf : Group.IsPerfect (A.map ν) := Subgroup.isPerfect_iff.mpr (by
      rw [← Subgroup.map_commutator, perfect_of_mem_cComp hA])
    obtain ⟨-, -, h4⟩ :=
      SteinbergCD.central_quotients_preserve_prime_core_quasisimplicity Nat.prime_two _ hZc
    have h5 := h4 hperf
    let e3 := QuotientGroup.quotientKerEquivOfSurjective _ (σ.subgroupMap_surjective (A.map ν))
    have hk3 : IsPGroup 2 e3.toMonoidHom.ker := by
      have : e3.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e3.injective
      rw [this]
      exact IsPGroup.of_bot
    have h6 := isQuasisimple_pCore_quotient_iff e3.toMonoidHom e3.surjective hk3
    have h7 : (A.map ν).map σ = A.map (σ.comp ν) := Subgroup.map_map _ _ _
    have h8 := isQuasisimple_pCore_quotient_congr (p := 2) (MulEquiv.subgroupCongr h7)
    intro hq
    exact hAq (h1.mpr (h5.mpr (h6.mpr (h8.mpr hq))))


theorem not_mem_of_isPGroup_two {H : Type*} [Group H] {S : Subgroup H} (hS : IsPGroup 2 S)
    {d : ℕ} (hd : d.Prime) (hd2 : d ≠ 2) {h : H} (hh : h ∈ S) (hord : orderOf h = d) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hS ⟨h, hh⟩
  have h1 : orderOf h = orderOf (⟨h, hh⟩ : S) := Subgroup.orderOf_coe ⟨h, hh⟩
  rw [← h1, hord] at hk
  exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp (hd.dvd_of_dvd_pow (dvd_of_eq hk)))

theorem isPGroup_two_inf_ker {X : Subgroup K}
    (hZ13 : Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 1 ∨
      Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 3)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) :
    IsPGroup 2 ↥(X ⊓ ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 K))).ker) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  rw [IsPGroup.iff_orderOf]
  intro g
  have hn0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 fun {d} hd hdg => ?_⟩
  by_contra hd2
  have : Fact d.Prime := ⟨hd⟩
  obtain ⟨k, hkX, hkK, hkord⟩ : ∃ k : K, k ∈ X ∧
      k ∈ ((QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp
        (QuotientGroup.mk' (CFSG.pCore 2 K))).ker ∧ orderOf k = d := by
    refine ⟨((g ^ (orderOf g / d) : ↥(X ⊓ _)) : K), (Subgroup.mem_inf.mp (g ^ (orderOf g / d)).2).1,
      (Subgroup.mem_inf.mp (g ^ (orderOf g / d)).2).2, ?_⟩
    rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div hn0 hdg
  have hdp : d = p := by
    have hxo : orderOf (⟨k, hkX⟩ : X) = d := by rw [← Subgroup.orderOf_coe]; exact hkord
    have hm : orderOf ((⟨k, hkX⟩ : X) : X ⧸ CFSG.pCore 2 X) = d := by
      apply orderOf_eq_prime
      · rw [← QuotientGroup.mk_pow, ← hxo, pow_orderOf_eq_one, QuotientGroup.mk_one]
      · intro h1
        rw [QuotientGroup.eq_one_iff] at h1
        exact not_mem_of_isPGroup_two (CFSG.pCore_isPGroup (p := 2) (G := X)) hd hd2 h1 hxo
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hXp ((⟨k, hkX⟩ : X) : X ⧸ CFSG.pCore 2 X)
    rw [hm] at hj
    exact (Nat.prime_dvd_prime_iff_eq hd hp).mp (hd.dvd_of_dvd_pow (dvd_of_eq hj))
  have hz : QuotientGroup.mk' (CFSG.pCore 2 K) k ∈ center (K ⧸ CFSG.pCore 2 K) :=
    (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hkK)
  have hzo : orderOf (⟨_, hz⟩ : center (K ⧸ CFSG.pCore 2 K)) = d := by
    rw [← Subgroup.orderOf_coe]
    apply orderOf_eq_prime
    · show (QuotientGroup.mk' (CFSG.pCore 2 K) k) ^ d = 1
      rw [← map_pow, ← hkord, pow_orderOf_eq_one, map_one]
    · show QuotientGroup.mk' (CFSG.pCore 2 K) k ≠ 1
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact not_mem_of_isPGroup_two (CFSG.pCore_isPGroup (p := 2) (G := K)) hd hd2 h1 hkord
  have hdZ : d ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := by
    rw [← hzo]
    exact orderOf_dvd_natCard _
  rcases hZ13 with h13 | h13 <;> rw [h13] at hdZ
  · exact hd.one_lt.ne' (Nat.dvd_one.mp hdZ)
  · have := (Nat.prime_dvd_prime_iff_eq hd Nat.prime_three).mp hdZ
    omega

theorem ambient_quotient_witness_facts {T A X : Subgroup K}
    (hZ13 : Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 1 ∨
      Nat.card (center (K ⧸ CFSG.pCore 2 K)) = 3)
    (hT : quasithinIsSylowTwo T) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hXA : X ≤ A)
    (hXn : (X.subgroupOf A).Normal) (hTX : T ≤ normalizer (X : Set K))
    (hX2 : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) :
    let η : K →* (K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K) :=
      (QuotientGroup.mk' (center (K ⧸ CFSG.pCore 2 K))).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
    ((X.map η).subgroupOf (A.map η)).Normal ∧ T.map η ≤ normalizer (X.map η : Set _) ∧
      (∀ (N : Subgroup (X.map η)) [N.Normal], IsPGroup 2 ((X.map η) ⧸ N) → N = ⊤) ∧
      (∃ e : (X ⧸ CFSG.pCore 2 X) ≃* ((X.map η) ⧸ CFSG.pCore 2 (X.map η)),
        ∀ x : X, e x = ((⟨η x, Subgroup.mem_map_of_mem η x.2⟩ : X.map η) :
          (X.map η) ⧸ CFSG.pCore 2 (X.map η))) ∧
      ∀ P : Subgroup K, CFSG.ABGLocalTools.IsSylowOf p P X →
        Function.Injective (η.comp P.subtype) ∧ IsPGroup p (P.map η) ∧ ¬ IsCyclic (P.map η) ∧
        (((P.map η : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) :
            Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
          (T.map η : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) =
          (T.map η : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
            (P.map η : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)))) ∧
        ((P : Set K) * (T : Set K) = (T : Set K) * (P : Set K)) ∧
        ((P : Set K) * (T : Set K) = ((X ⊔ T : Subgroup K) : Set K)) := by
  intro η
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hker2 : IsPGroup 2 ↥(X ⊓ η.ker) := isPGroup_two_inf_ker hZ13 hp hp5 hXp
  refine ⟨?_, ?_, ?_, ?_, fun P hP => ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hXA)).mpr
      ((Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer hXA).mp hXn)).trans
        (Subgroup.le_normalizer_map η))
  · exact (Subgroup.map_mono hTX).trans (Subgroup.le_normalizer_map η)
  · intro Nb _ hNb
    have hsurj : Function.Surjective ((QuotientGroup.mk' Nb).comp (η.subgroupMap X)) :=
      (QuotientGroup.mk'_surjective _).comp (η.subgroupMap_surjective X)
    have hM := hX2 _ (hNb.of_equiv (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).symm)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk'] at hM
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := η.subgroupMap_surjective X y
    have hx : x ∈ Nb.comap (η.subgroupMap X) := by
      rw [hM]
      exact Subgroup.mem_top x
    exact hx
  · obtain ⟨e, he⟩ := exists_pCore_quotient_mulEquiv (η.subgroupMap X)
      (η.subgroupMap_surjective X) (isPGroup_ker_subgroupMap η X hker2)
    exact ⟨e, he⟩
  · obtain ⟨Qs, hQs⟩ := hP
    have hPX : P ≤ X := by
      rw [← hQs]
      exact Subgroup.map_subtype_le _
    have hPp : IsPGroup p P := by
      rw [← hQs]
      exact Qs.2.map _
    have hPk : P ⊓ η.ker = ⊥ := by
      have h1 : IsPGroup p ↥(P ⊓ η.ker) := hPp.to_le inf_le_left
      have h2 : IsPGroup 2 ↥(P ⊓ η.ker) := hker2.to_le (inf_le_inf_right _ hPX)
      exact disjoint_self.mp (IsPGroup.disjoint_of_ne p 2 hp2 _ _ h1 h2)
    have hinj : Function.Injective (η.comp P.subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have h1 : (x : K) ∈ P ⊓ η.ker := ⟨x.2, hx⟩
      rw [hPk, Subgroup.mem_bot] at h1
      exact Subtype.ext h1
    have hQtop : (Qs.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X)) :
        Subgroup (X ⧸ CFSG.pCore 2 X)) = ⊤ :=
      ((Qs.mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))).is_maximal'
        (hXp.to_subgroup ⊤) le_top).symm
    have hsurjP : ∀ x : X, ∃ y ∈ P, ∃ hy : y ∈ X,
        ((⟨y, hy⟩ : X) : X ⧸ CFSG.pCore 2 X) = x := by
      intro x
      have hx : (x : X ⧸ CFSG.pCore 2 X) ∈
          (Qs : Subgroup X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) := by
        rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X)) Qs,
          hQtop]
        exact Subgroup.mem_top _
      obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
      refine ⟨q, ?_, q.2, hqx⟩
      rw [← hQs]
      exact Subgroup.mem_map_of_mem _ hq
    have hO2T : (CFSG.pCore 2 X).map X.subtype ≤ T := by
      have hp2X : IsPGroup 2 ↥((CFSG.pCore 2 X).map X.subtype) :=
        (CFSG.pCore_isPGroup (p := 2) (G := X)).map _
      have hTn : T ≤ normalizer (((CFSG.pCore 2 X).map X.subtype : Subgroup K) : Set K) :=
        hTX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
      have hsup := hp2X.to_sup_of_normal_left' hT.1 hTn
      have heq := (hT.1.toSylow hT.2).is_maximal' hsup le_sup_right
      exact le_sup_left.trans heq.le
    have hXPT : ∀ x ∈ X, x ∈ (P : Set K) * (T : Set K) := by
      intro x hx
      obtain ⟨y, hyP, hyX, hyx⟩ := hsurjP ⟨x, hx⟩
      have h1 : (⟨y, hyX⟩ : X)⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 X := by
        rw [← QuotientGroup.eq]
        exact hyx
      exact ⟨y, hyP, y⁻¹ * x, hO2T ⟨_, h1, rfl⟩, by group⟩
    have hPT : (P : Set K) * (T : Set K) = ((X ⊔ T : Subgroup K) : Set K) := by
      rw [Subgroup.coe_mul_of_right_le_normalizer_left X T hTX]
      apply le_antisymm
      · exact Set.mul_subset_mul (SetLike.coe_subset_coe.mpr hPX) subset_rfl
      · rintro _ ⟨x, hx, t, ht, rfl⟩
        obtain ⟨y, hy, t', ht', hyt⟩ := hXPT x hx
        refine ⟨y, hy, t' * t, T.mul_mem ht' ht, ?_⟩
        have hyt' : y * t' = x := hyt
        show y * (t' * t) = x * t
        rw [← mul_assoc, hyt']
    have hTP : (T : Set K) * (P : Set K) = (P : Set K) * (T : Set K) := by
      have h1 := congrArg (fun s : Set K => s⁻¹) hPT
      simp only [mul_inv_rev, inv_coe_set] at h1
      rw [h1, hPT]
    have hncyc : ¬ IsCyclic (P.map η) := by
      intro hcyc
      have h1 : IsCyclic P := isCyclic_of_injective (η.subgroupMap P)
        fun a b hab => hinj (congrArg Subtype.val hab)
      let ψ : P →* X ⧸ CFSG.pCore 2 X :=
        (QuotientGroup.mk' (CFSG.pCore 2 X)).comp (Subgroup.inclusion hPX)
      have hψ : Function.Surjective ψ := by
        intro z
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ z
        obtain ⟨y, hyP, hyX, hyx⟩ := hsurjP x
        exact ⟨⟨y, hyP⟩, hyx⟩
      have h2 : IsCyclic (X ⧸ CFSG.pCore 2 X) := isCyclic_of_surjective ψ hψ
      have hbdd : BddAbove {r : ℕ | ∃ B : Subgroup (X ⧸ CFSG.pCore 2 X),
          CFSG.IsElementaryAbelian p B ∧ Nat.card B = p ^ r} := by
        refine ⟨Nat.card (X ⧸ CFSG.pCore 2 X), ?_⟩
        rintro r ⟨B, -, hB⟩
        calc r ≤ p ^ r := (Nat.lt_pow_self hp.one_lt).le
          _ = Nat.card B := hB.symm
          _ ≤ Nat.card (X ⧸ CFSG.pCore 2 X) := Subgroup.card_le_card_group B
      have hne : ({r : ℕ | ∃ B : Subgroup (X ⧸ CFSG.pCore 2 X),
          CFSG.IsElementaryAbelian p B ∧ Nat.card B = p ^ r}).Nonempty := by
        have hbot : ∀ a : (⊥ : Subgroup (X ⧸ CFSG.pCore 2 X)), a = 1 := fun a =>
          Subtype.ext (Subgroup.mem_bot.mp a.2)
        have : IsMulCommutative (⊥ : Subgroup (X ⧸ CFSG.pCore 2 X)) :=
          ⟨⟨fun a b => by rw [hbot a, hbot b]⟩⟩
        refine ⟨0, ⊥, ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
          rw [hbot a, one_pow]⟩, ?_⟩
        rw [Subgroup.card_bot, pow_zero]
      have hmem := Nat.sSup_mem hne hbdd
      have h3 : sSup {r : ℕ | ∃ B : Subgroup (X ⧸ CFSG.pCore 2 X),
          CFSG.IsElementaryAbelian p B ∧ Nat.card B = p ^ r} = 2 := hrk
      rw [h3] at hmem
      obtain ⟨E, hE, hEc⟩ := hmem
      have hexp : Monoid.exponent E = Nat.card E := IsCyclic.exponent_eq_card
      have hdvd := CFSG.IsElementaryAbelian.exponent_dvd_p p E
      rw [hexp, hEc] at hdvd
      have h4 : p * p ≤ p := by
        have := Nat.le_of_dvd hp.pos hdvd
        rwa [pow_two] at this
      nlinarith [hp.two_le]
    refine ⟨hinj, hPp.map η, hncyc, ?_, hTP.symm, hPT⟩
    have h1 := congrArg (Set.image η) hTP
    rw [Set.image_mul, Set.image_mul] at h1
    rw [Subgroup.coe_map η P, Subgroup.coe_map η T]
    exact h1.symm

theorem quasisimple_two_core_ambient_simple_quotient_retains_original_local_witnesses
    (hK : CFSG.SectionRank.IsSQTKCat K) (hQ : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K))
    {T A : Subgroup K} (hT : quasithinIsSylowTwo T) (hA : A ∈ cComp (A ⊔ T))
    (hAq : ¬ CFSG.IsQuasisimple (A ⧸ CFSG.pCore 2 A)) :
    let Q := K ⧸ CFSG.pCore 2 K
    let η : K →* Q ⧸ center Q :=
      (QuotientGroup.mk' (center Q)).comp (QuotientGroup.mk' (CFSG.pCore 2 K))
    (IsSimpleGroup (Q ⧸ center Q) ∧ ∃ a b : Q ⧸ center Q, a * b ≠ b * a) ∧
      CFSG.Blueprint.Catalog (Q ⧸ center Q) ∧ IsStronglyQuasithin (Q ⧸ center Q) ∧
      (Nat.card (center Q) = 1 ∨ Nat.card (center Q) = 3) ∧
      quasithinIsSylowTwo (T.map η) ∧ A.map η ∈ cComp (A.map η ⊔ T.map η) ∧
      ¬ CFSG.IsQuasisimple (A.map η ⧸ CFSG.pCore 2 (A.map η)) ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup K, X ≤ A → (X.subgroupOf A).Normal →
        T ≤ normalizer (X : Set K) →
        (∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤) →
        IsPGroup p (X ⧸ CFSG.pCore 2 X) → CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 →
        ((X.map η).subgroupOf (A.map η)).Normal ∧ T.map η ≤ normalizer (X.map η : Set _) ∧
          (∀ (N : Subgroup (X.map η)) [N.Normal], IsPGroup 2 ((X.map η) ⧸ N) → N = ⊤) ∧
          (∃ e : (X ⧸ CFSG.pCore 2 X) ≃* ((X.map η) ⧸ CFSG.pCore 2 (X.map η)),
            ∀ x : X, e x = ((⟨η x, Subgroup.mem_map_of_mem η x.2⟩ : X.map η) :
              (X.map η) ⧸ CFSG.pCore 2 (X.map η))) ∧
          ∀ P : Subgroup K, CFSG.ABGLocalTools.IsSylowOf p P X →
            Function.Injective (η.comp P.subtype) ∧ IsPGroup p (P.map η) ∧
            ¬ IsCyclic (P.map η) ∧
            ((P.map η : Set (Q ⧸ center Q)) * (T.map η : Set (Q ⧸ center Q)) =
              (T.map η : Set (Q ⧸ center Q)) * (P.map η : Set (Q ⧸ center Q))) ∧
            ((P : Set K) * (T : Set K) = (T : Set K) * (P : Set K)) ∧
            ((P : Set K) * (T : Set K) = ((X ⊔ T : Subgroup K) : Set K)) := by
  intro Q η
  obtain ⟨hQK, hZ13, hSQT⟩ := two_core_quotient_facts hK hQ
  obtain ⟨hTb, hAb, hAbq⟩ := ambient_quotient_sylow_and_component hT hA hAq
  exact ⟨⟨hQ.2.1, hQ.2.2⟩, CFSG.SectionRank.catalog_center_quotient hQ hQK.2, hSQT, hZ13, hTb,
    hAb, hAbq, fun p hp hp5 X hXA hXn hTX hX2 hXp hrk =>
      ambient_quotient_witness_facts hZ13 hT hp hp5 hXA hXn hTX hX2 hXp hrk⟩

end CFSG.Quasithin.H13.NQTerm
