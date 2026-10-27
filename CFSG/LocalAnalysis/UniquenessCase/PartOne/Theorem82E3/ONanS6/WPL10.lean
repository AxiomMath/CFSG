module

public import CFSG.LocalAnalysis.UniquenessCase.UCKP898G
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open scoped commutatorElement
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ComponentClassification.PerfectAutomorphisms
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem eq_zpowers_of_card_three {Z : Subgroup G} (hZ : Nat.card Z = 3)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) : Z = Subgroup.zpowers z := by
  have hzdvd : orderOf z ∣ 3 := by
    have h := Subgroup.orderOf_dvd_natCard Z hz
    simpa [hZ] using h
  have hzord : orderOf z = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hzdvd with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) hz1
    · exact h3
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz)
    (by rw [Nat.card_zpowers, hzord, hZ])).symm

theorem sylow_seven_cyclic_of_pRank_one {H : Type*} [Group H] [Finite H]
    (hH : CFSG.Open.pRank 7 (⊤ : Subgroup H) ≤ 1) :
    ∀ S : Sylow 7 H, IsCyclic ↥S := by
  intro S
  have hr : CFSG.pRank 7 (⊤ : Subgroup H) ≤ 1 := by
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank]
  exact CFSG.RankThree.PartOne.isCyclic_of_pRank_le_one (p := 7) (by norm_num) (by norm_num)
    le_top S.isPGroup' hr

theorem sylow_seven_cyclic_of_surjective {H X : Type*} [Group H] [Group X] [Finite H] [Finite X]
    (π : H →* X) (hπ : Function.Surjective π)
    (hH : ∀ S : Sylow 7 H, IsCyclic ↥S) : ∀ T : Sylow 7 X, IsCyclic ↥T := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro T
  let S : Sylow 7 H := Classical.choice (Sylow.nonempty (p := 7) (G := H))
  let Sbar : Sylow 7 X := S.mapSurjective hπ
  have hSbar : IsCyclic ↥Sbar := by
    let f : ↥S →* ↥Sbar := (π.comp (S : Subgroup H).subtype).codRestrict Sbar (fun s => by
      have hmem : (π.comp (S : Subgroup H).subtype) s ∈ (S : Subgroup H).map π :=
        Subgroup.mem_map_of_mem π s.2
      rw [← Sylow.coe_mapSurjective] at hmem
      exact hmem)
    refine isCyclic_of_surjective f ?_
    intro y
    have hy : (y : X) ∈ (S : Subgroup H).map π := by
      have hy' : (y : X) ∈ (Sbar : Subgroup X) := y.2
      rwa [Sylow.coe_mapSurjective] at hy'
    obtain ⟨s, hs, hys⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨s, hs⟩, Subtype.ext hys⟩
  exact isCyclic_of_surjective (Sylow.equiv Sbar T).toMonoidHom
    (Sylow.equiv Sbar T).surjective

theorem exists_order_seven_of_center_quotient {Y : Type*} [Group Y] [Finite Y]
    (h7 : 7 ∣ Nat.card (Y ⧸ Subgroup.center Y))
    (hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center Y)) :
    ∃ y : Y, orderOf y = 7 ∧ y ∉ Subgroup.center Y := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : Nat.Prime 7 := by norm_num
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Y ⧸ Subgroup.center Y) 7 h7
  obtain ⟨x, hxq⟩ := QuotientGroup.mk_surjective q
  subst hxq
  have hx7 : x ^ 7 ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq_one_iff]
    simpa [← hq] using pow_orderOf_eq_one (x : Y ⧸ Subgroup.center Y)
  let d := orderOf (x ^ 7)
  have hdvd : d ∣ Nat.card (Subgroup.center Y) := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center Y) hx7
    simpa [d] using h
  have hd7 : ¬ 7 ∣ d := fun h => hZ7 (h.trans hdvd)
  have hcop : Nat.Coprime 7 d := (hp7.coprime_iff_not_dvd).mpr hd7
  refine ⟨x ^ d, ?_, ?_⟩
  · have hpow : (x ^ d) ^ 7 = 1 := by
      rw [pow_right_comm]
      exact pow_orderOf_eq_one (x ^ 7)
    have hne : x ^ d ≠ 1 := by
      intro h1
      have h2 : (x : Y ⧸ Subgroup.center Y) ^ d = 1 := by
        rw [← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]
      have hdvd7 : 7 ∣ d := by
        have := orderOf_dvd_of_pow_eq_one h2
        simpa [hq] using this
      exact hd7 hdvd7
    exact orderOf_eq_prime hpow hne
  · intro hzc
    have h1 : (x : Y ⧸ Subgroup.center Y) ^ d = 1 := by
      rw [← QuotientGroup.mk_pow, (QuotientGroup.eq_one_iff _).mpr hzc]
    have hdvd7 : 7 ∣ d := by
      have := orderOf_dvd_of_pow_eq_one h1
      simpa [hq] using this
    exact hd7 hdvd7

theorem component_normal_of_seven {X : Type*} [Group X] [Finite X] {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (h7J : 7 ∣ Nat.card (J ⧸ Subgroup.center J))
    (hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center J))
    (hcyc : ∀ S : Sylow 7 X, IsCyclic ↥S) : J.Normal := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp7 : Nat.Prime 7 := by norm_num
  rw [← Subgroup.normalizer_eq_top_iff]
  refine eq_top_iff.mpr ?_
  intro g _
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  by_contra hmap
  let K : Subgroup X := J.map (MulAut.conj g).toMonoidHom
  have hK : CFSG.IsComponent K :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hJ
  have hne : J ≠ K := fun h => hmap h.symm
  have hcomm : ⁅J, K⁆ = ⊥ :=
    (CFSG.LocalCores.distinct_components_commute hJ hK).resolve_left hne
  have hcommute : ∀ a ∈ J, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    have h1 : ⁅a, b⁆ ∈ ⁅J, K⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hcomm, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  obtain ⟨a, haord, haZ⟩ := exists_order_seven_of_center_quotient h7J hZ7
  let aX : X := a
  have haJ : aX ∈ J := a.2
  have haXord : orderOf aX = 7 := by simpa [aX] using haord
  let e : J ≃* K :=
    Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  let b : X := MulAut.conj g aX
  have hbK : b ∈ K := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom haJ
  have hbord : orderOf b = 7 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g) aX
    simpa [b, haXord] using h
  have hbZ : (⟨b, hbK⟩ : K) ∉ Subgroup.center K := by
    intro hb
    apply haZ
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hyK : MulAut.conj g (y : X) ∈ K :=
      Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom y.2
    have hbcomm : b * MulAut.conj g (y : X) = MulAut.conj g (y : X) * b := by
      rw [Subgroup.mem_center_iff] at hb
      simpa using (congrArg Subtype.val (hb ⟨MulAut.conj g (y : X), hyK⟩)).symm
    have h := congrArg (fun z : X => g⁻¹ * z * g) hbcomm
    have h' : aX * (y : X) = (y : X) * aX := by
      simpa [b, aX, MulAut.conj_apply] using h
    simpa [aX] using h'.symm
  have hcommab : aX * b = b * aX := hcommute aX haJ b hbK
  have hbnzp : b ∉ Subgroup.zpowers aX := by
    intro hbzp
    have hbJ : b ∈ J := Subgroup.zpowers_le.mpr haJ hbzp
    have hbcenter : (⟨b, hbK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (hcommute b hbJ (y : X) y.2).symm
    exact hbZ hbcenter
  have hpair := CFSG.LocalAnalysis.UniquenessCase.UCK.closure_pair_isElemAbelian_card_of_prime
    (q := 7) (a := aX) (b := b) hp7 haXord hbord hcommab hbnzp
  let E : Subgroup X := Subgroup.closure ({aX, b} : Set X)
  have hEel : CFSG.Open.IsElemAbelian 7 E := hpair.1
  have hEcard : Nat.card E = 7 ^ 2 := hpair.2
  have hEp : IsPGroup 7 E := CFSG.Open.IsElemAbelian.isPGroup hEel
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  have hEcyc : IsCyclic ↥E := Subgroup.isCyclic_of_le hES
  obtain ⟨e0, he0⟩ := IsCyclic.exists_generator (α := ↥E)
  have hEcard' : Nat.card E = 49 := by rw [hEcard]; norm_num
  have htop : Subgroup.zpowers e0 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact he0 x
  have he0ord : orderOf e0 = 49 := by
    rw [← Nat.card_zpowers, htop, Subgroup.card_top, hEcard']
  have he07 : e0 ^ 7 = 1 := Subtype.ext (hEel.2 (e0 : X) e0.2)
  have hdvd : orderOf e0 ∣ 7 := orderOf_dvd_of_pow_eq_one he07
  rw [he0ord] at hdvd
  norm_num at hdvd

theorem center_eq_bot_of_theta_eq_bot {X : Type*} [Group X] [Finite X] {J : Subgroup X}
    (hJ : CFSG.IsComponent J) (hθ : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X = ⊥)
    (h3J : ¬ 3 ∣ Nat.card J) : Subgroup.center J = ⊥ := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let ZJ : Subgroup X := (Subgroup.center J).map J.subtype
  have hZJle : ZJ ≤ J := Subgroup.map_subtype_le _
  have hZJsub : ZJ.IsSubnormal :=
    Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hJ.2
  have hZJsolv : Group.IsSolvable ZJ :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_of_mulEquiv
      (Subgroup.equivMapOfInjective (Subgroup.center J) J.subtype J.subtype_injective)
  have h3ZJ : ¬ 3 ∣ Nat.card ZJ := fun h3 =>
    h3J (h3.trans (Subgroup.card_dvd_of_le hZJle))
  have hZJcop : Nat.Coprime 3 (Nat.card ZJ) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3ZJ
  have hZJp : ZJ ≤ CFSG.pPrimeCore 3 X :=
    CFSG.GH74.GLS.le_pPrimeCore_of_subnormal 3 hZJsub hZJcop
  have hZJrad : ZJ ≤ CFSG.solvableRadical X :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical_of_isSubnormal hZJsub hZJsolv
  have hRadn : (CFSG.solvableRadical X).Normal :=
    Subgroup.sSup_normal _ fun _ hN => hN.1
  haveI : Group.IsSolvable (CFSG.solvableRadical X) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  let N : Subgroup X := CFSG.pPrimeCore 3 X ⊓ CFSG.solvableRadical X
  have hNn : N.Normal := inferInstance
  have hNsolv : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective inf_le_right)
  have hNcop : ¬ 3 ∣ Nat.card N := by
    intro h3
    have hdvd : Nat.card N ∣ Nat.card (CFSG.pPrimeCore 3 X) :=
      Subgroup.card_dvd_of_le inf_le_left
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := X)) (h3.trans hdvd)
  have hNleθ : N ≤ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X :=
    (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := X) (p := 3) Nat.prime_three).2.2.2.1 N hNn hNsolv hNcop
  have hZJbot : ZJ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    exact hθ ▸ hNleθ ⟨hZJp hz, hZJrad hz⟩
  have hmap : (Subgroup.center J).map J.subtype = ⊥ := hZJbot
  exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).mp hmap

theorem seven_dvd_two_pow_sub_one_of_three_dvd {f : ℕ} (h3 : 3 ∣ f) :
    7 ∣ 2 ^ f - 1 := by
  obtain ⟨k, rfl⟩ := h3
  have h8 : (8 : ℕ) ≡ 1 [MOD 7] := by decide
  have hmod : (2 : ℕ) ^ (3 * k) ≡ 1 [MOD 7] := by
    simpa [pow_mul] using h8.pow k
  have hle : 1 ≤ 2 ^ (3 * k) := Nat.one_le_pow _ _ (by norm_num)
  have hdvd := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  simpa using hdvd

theorem autThetaQuot_eq_bot_of_inf_normalizer_eq_bot {X : Type*} [Group X] [Finite X]
    {A L : Subgroup X} (h : A ⊓ Subgroup.normalizer (L : Set X) = ⊥) :
    autThetaQuot A L = ⊥ := by
  have h1 : autIn A L = ⊥ := by
    unfold autIn
    rw [h]
    simp
  unfold autThetaQuot
  rw [h1, Subgroup.map_bot]

theorem suzukiBridgeData_of_three_lt'
    (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar)
    (P : Subgroup G) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (e : G)
    (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (hSzF : Sz.SzFix)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L)
    {J : Subgroup (componentsQuot e)} (hJ : CFSG.IsComponent J)
    (hntriv : ¬ TrivialZComponentAction (D := D) c P e J)
    {f : ℕ} (hSz : CFSG.Blueprint.SuzukiModel (J ⧸ Subgroup.center J) 2 f) (hf : 3 < f) :
    SuzukiComponentBridgeData (D := D) c P e J := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let Nθ : Subgroup H := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 H
  let π : H →* componentsQuot e := QuotientGroup.mk' Nθ
  have hZcard : Nat.card (zSub P c.L) = 3 :=
    c.card_inf_centralizer_of_onan hON hP
  rcases Subgroup.bot_or_exists_ne_one (zSub P c.L) with hZbot | ⟨z0, hz0Z, hz01⟩
  · rw [hZbot, Subgroup.card_bot] at hZcard
    norm_num at hZcard
  have hZeq : zSub P c.L = Subgroup.zpowers z0 :=
    eq_zpowers_of_card_three hZcard hz0Z hz01
  have hz0ord : orderOf z0 = 3 := by
    have hdvd : orderOf z0 ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (zSub P c.L) hz0Z
      rwa [hZcard] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz01
    · exact h
  have hZleH : zSub P c.L ≤ H := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hz.2 e he).symm
  have hz0H : z0 ∈ H := hZleH hz0Z
  let z : componentsQuot e := π ⟨z0, hz0H⟩
  have hz3 : z ^ 3 = 1 := by
    have h3 : (⟨z0, hz0H⟩ : H) ^ 3 = 1 := by
      apply Subtype.ext
      simpa [hz0ord] using pow_orderOf_eq_one z0
    change (π ⟨z0, hz0H⟩) ^ 3 = 1
    rw [← map_pow, h3, map_one]
  have h3J : ¬ 3 ∣ Nat.card J :=
    not_three_dvd_card_of_nontrivial e c P hZ3 hJ hntriv
  have hθX : CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 (componentsQuot e) = ⊥ := by
    have hchar := CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
      (H := H) (p := 3) Nat.prime_three
    have h := CFSG.RankThree.LocalRank.solvable_prime_complement_core_quotient_centralizers
      (G := H) (p := 3) Nat.prime_three Nθ hchar.1 hchar.2.2.1
    exact h.2.2.1
  have hZJ : Subgroup.center J = ⊥ :=
    center_eq_bot_of_theta_eq_bot hJ hθX h3J
  have hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center J) := by
    rw [hZJ, Subgroup.card_bot]
    norm_num
  let L' : Subgroup H := inSubgroup perfectResidual (J.comap π)
  have hL' := perfectResidual_comap_mem_thetaComponents (p := 3) Nat.prime_three hJ
  let L : Subgroup G := L'.map H.subtype
  have hLmem : L ∈ thetaComponentsAt 3 e := ⟨L', hL'.1, rfl⟩
  have hLmap : (L.subgroupOf H).map π = J := by
    simpa [L, Subgroup.subgroupOf_map_subtype] using hL'.2
  have hAutNe : Nat.card (autThetaQuot (zSub P c.L) L) ≠ 1 := by
    intro hc
    exact hntriv ⟨L, hLmem, hLmap, hc⟩
  have hZleN : zSub P c.L ≤ Subgroup.normalizer (L : Set G) := by
    by_contra hnot
    let K : Subgroup G := zSub P c.L ⊓ Subgroup.normalizer (L : Set G)
    have hKle : K ≤ zSub P c.L := inf_le_left
    have hKdvd : Nat.card K ∣ 3 := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le hKle
    have hKne : K ≠ zSub P c.L := fun h => hnot (h.ge.trans inf_le_right)
    rcases (Nat.dvd_prime Nat.prime_three).mp hKdvd with h1 | h3
    · have hKbot : K = ⊥ := Subgroup.eq_bot_of_card_eq K h1
      exact hAutNe (by
        rw [autThetaQuot_eq_bot_of_inf_normalizer_eq_bot hKbot, Subgroup.card_bot])
    · exact hKne (Subgroup.eq_of_le_of_card_ge hKle (by rw [h3, hZcard]))
  have hzN : z ∈ Subgroup.normalizer (J : Set (componentsQuot e)) := by
    have hz0N : (⟨z0, hz0H⟩ : H) ∈ Subgroup.normalizer (L' : Set H) :=
      (CFSG.RankThree.PartTwo.Sec13.coe_mem_normalizer_map_iff H).mp (by
        simpa [L] using hZleN hz0Z)
    have hmem : π ⟨z0, hz0H⟩ ∈ (Subgroup.normalizer (L' : Set H)).map π :=
      Subgroup.mem_map_of_mem π hz0N
    have h := Subgroup.le_normalizer_map (f := π) (H := L') hmem
    have h' : π ⟨z0, hz0H⟩ ∈
        Subgroup.normalizer ((L'.map π : Subgroup (componentsQuot e)) : Set _) := h
    rw [hL'.2] at h'
    simpa [z] using h' 
  let α : MulAut J := Subgroup.normalizerMonoidHom J ⟨z, hzN⟩
  have hα3 : α ^ 3 = 1 := by
    change (Subgroup.normalizerMonoidHom J ⟨z, hzN⟩) ^ 3 = 1
    rw [← map_pow]
    have hzN3 : (⟨z, hzN⟩ : Subgroup.normalizer (J : Set (componentsQuot e))) ^ 3 = 1 := by
      apply Subtype.ext
      simpa using hz3
    rw [hzN3, map_one]
  have hαne : centerQuotientHom J α ≠ 1 := by
    intro hα
    haveI : Group.IsPerfect ↥J := hJ.1.1
    have hα1' : α = 1 := centerQuotientHom_injective J (by rw [hα, map_one])
    have hα1 : Subgroup.normalizerMonoidHom J ⟨z, hzN⟩ = 1 := hα1' 
    let X' : Subgroup H := (zSub P c.L).subgroupOf H
    have hX'map : X'.map H.subtype = zSub P c.L :=
      Subgroup.map_subgroupOf_eq_of_le hZleH
    have hL'mapG : L'.map H.subtype = L := rfl
    have hAutH : autThetaQuot X' L' = ⊥ := by
      rw [eq_bot_iff]
      intro τ hτ
      rw [Subgroup.mem_bot]
      obtain ⟨h, hN, hX, rfl⟩ := mem_autThetaQuot_iff.mp hτ
      have hXz : (h : G) ∈ zSub P c.L := Subgroup.mem_subgroupOf.mp hX
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hZeq ▸ hXz)
      have hhk : (⟨z0, hz0H⟩ : H) ^ k = h := Subtype.ext hk
      have hπh : (h : componentsQuot e) = z ^ k := by
        have h := map_zpow π (⟨z0, hz0H⟩ : H) k
        rwa [hhk] at h
      have hαzpow : ∀ n : ℤ,
          Subgroup.normalizerMonoidHom J (⟨z, hzN⟩ ^ n) = 1 := by
        intro n
        rw [map_zpow, hα1]
        simp
      have hconj : ∀ n : ℤ, ∀ j : J,
          z ^ n * (j : componentsQuot e) * (z ^ n)⁻¹ = (j : componentsQuot e) := by
        intro n j
        have h := congrArg (fun φ : MulAut J => ((φ j : J) : componentsQuot e)) (hαzpow n)
        rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
        simpa using h
      obtain ⟨η, hη⟩ := exists_thetaQuotient_mulEquiv_map (p := 3) Nat.prime_three hL'.1.2.1
      have hτ1 : thetaQuotMulAut L' (Subgroup.normalizerMonoidHom L' ⟨h, hN⟩) = 1 := by
        ext x
        induction x using QuotientGroup.induction_on with
        | H l =>
          apply η.injective
          apply Subtype.ext
          rw [thetaQuotMulAut_mk, hη]
          simp only [MulAut.one_apply, one_mul]
          rw [hη, Subgroup.normalizerMonoidHom_apply_apply_coe]
          rw [map_mul, map_mul, map_inv]
          have hmemJ : (π l : componentsQuot e) ∈ J := by
            have := Subgroup.mem_map_of_mem π l.2
            rwa [hL'.2] at this
          have hπh' : (QuotientGroup.mk' Nθ) h = z ^ k := by
            simpa using hπh
          change (QuotientGroup.mk' Nθ) h * (QuotientGroup.mk' Nθ) l *
            ((QuotientGroup.mk' Nθ) h)⁻¹ = (QuotientGroup.mk' Nθ) l
          rw [hπh']
          exact hconj k ⟨(π l : componentsQuot e), hmemJ⟩
      exact hτ1
    have hbotG : autThetaQuot (zSub P c.L) L = ⊥ := by
      have hmapAut := CFSG.RankThree.PartTwo.Sec13.map_autThetaQuot_sub H X' L'
      rw [← hX'map, ← hL'mapG, ← hmapAut, hAutH, Subgroup.map_bot]
    exact hAutNe (by rw [hbotG, Subgroup.card_bot])
  have hσ3 : (centerQuotientHom J α) ^ 3 = 1 := by
    rw [← map_pow, hα3, map_one]
  have hσord : orderOf (centerQuotientHom J α) = 3 :=
    orderOf_eq_prime hσ3 hαne
  obtain ⟨-, -, b, hfb, -⟩ := hSzF hSz hf (centerQuotientHom J α) hσord
  have h3f : 3 ∣ f := ⟨2 * b + 1, hfb⟩
  have h7pow : 7 ∣ 2 ^ f - 1 := seven_dvd_two_pow_sub_one_of_three_dvd h3f
  have h7J : 7 ∣ Nat.card (J ⧸ Subgroup.center J) := by
    obtain ⟨-, a, ha, K, hKF, hKfin, hf_eq, hKcard, ⟨eK⟩⟩ := hSz
    letI : Field K := hKF
    letI : Finite K := hKfin
    have hS_card : Nat.card (J ⧸ Subgroup.center J) =
        Nat.card (CFSG.Blueprint.suzukiGroup a K) :=
      Nat.card_congr eK.toEquiv
    have hKcard' : Nat.card K = 2 ^ (2 * a + 1) := by
      rw [hKcard, hf_eq]
    have hsuz := CFSG.LieType.Ree.suzuki_order (a := a) (K := K) hKcard' 
    rw [hS_card, hsuz]
    have hq7 : 7 ∣ 2 ^ (2 * a + 1) - 1 := by
      simpa [← hf_eq] using h7pow
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hq7 _) _
  have hHrank : CFSG.Open.pRank 7 (⊤ : Subgroup H) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact le_of_eq hP3
  have hHcyc : ∀ S : Sylow 7 H, IsCyclic ↥S :=
    sylow_seven_cyclic_of_pRank_one hHrank
  have hXcyc : ∀ S : Sylow 7 (componentsQuot e), IsCyclic ↥S :=
    sylow_seven_cyclic_of_surjective π (QuotientGroup.mk'_surjective _) hHcyc
  have hJn : J.Normal := component_normal_of_seven hJ h7J hZ7 hXcyc
  have hWnorm : componentsImage (D := D) e ≤
      Subgroup.normalizer (J : Set (componentsQuot e)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hJn]
    exact le_top
  have hFix : CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
      (Subgroup.normalizerMonoidHom J ⟨z, hzN⟩) ≤
      (Subgroup.normalizer
        ((componentsImage (D := D) e : Subgroup (componentsQuot e)) : Set _)).comap
        J.subtype := by
    classical
    let W_H : Subgroup H := (H ⊓ CFSG.Open.pCoreOf 2 D.M).subgroupOf H
    have hWdef : componentsImage (D := D) e = W_H.map π := rfl
    let A : Subgroup H := Subgroup.zpowers (⟨z0, hz0H⟩ : H)
    have hA : IsPGroup 3 A :=
      IsPGroup.of_card (n := 1) (by
        rw [show Nat.card A = Nat.card (Subgroup.zpowers (⟨z0, hz0H⟩ : H)) from rfl,
          Nat.card_zpowers, ← Subgroup.orderOf_coe, hz0ord]
        rfl)
    have hNθ3 : ¬ 3 ∣ Nat.card Nθ :=
      (CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization
        (H := H) (p := 3) Nat.prime_three).2.2.1
    have hcop := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime (G := H) 3 Nθ hNθ3 A hA
    have hmapA : A.map π = Subgroup.zpowers z := by
      rw [show A = Subgroup.zpowers (⟨z0, hz0H⟩ : H) from rfl, MonoidHom.map_zpowers]
    have hmapCen : (Subgroup.centralizer (A : Set H)).map π ≤
        Subgroup.normalizer ((W_H.map π : Subgroup (componentsQuot e)) : Set _) := by
      rintro _ ⟨d, hd, rfl⟩
      have hdA : (⟨z0, hz0H⟩ : H) ∈ A := Subgroup.mem_zpowers _
      have hcomm : (⟨z0, hz0H⟩ : H) * d = d * ⟨z0, hz0H⟩ :=
        Subgroup.mem_centralizer_iff.mp hd ⟨z0, hz0H⟩ hdA
      have hdCen : (d : G) ∈ Subgroup.centralizer ({z0} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (congrArg Subtype.val hcomm).symm
      have hdCenClosure : (d : G) ∈
          Subgroup.centralizer ((Subgroup.closure ({z0} : Set G)) : Set G) := by
        rwa [Subgroup.centralizer_closure]
      have hdNz : (d : G) ∈
          Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) := by
        rw [hZeq, Subgroup.zpowers_eq_closure]
        exact Subgroup.centralizer_le_normalizer
          ((Subgroup.closure ({z0} : Set G) : Subgroup G) : Set G) hdCenClosure
      have hdM : (d : G) ∈ D.M := hNZ hdNz
      have hdNH : (d : G) ∈ Subgroup.normalizer (H : Set G) := Subgroup.le_normalizer d.2
      have hdNO : (d : G) ∈
          Subgroup.normalizer ((CFSG.Open.pCoreOf 2 D.M : Subgroup G) : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M hdM
      have hdNinf : (d : G) ∈
          Subgroup.normalizer ((H ⊓ CFSG.Open.pCoreOf 2 D.M : Subgroup G) : Set G) :=
        (Subgroup.inf_normalizer_le_normalizer_inf (H := H)
          (K := CFSG.Open.pCoreOf 2 D.M)) ⟨hdNH, hdNO⟩
      have hnorm : (Subgroup.normalizer
            ((H ⊓ CFSG.Open.pCoreOf 2 D.M : Subgroup G) : Set G)).comap H.subtype =
          Subgroup.normalizer (W_H : Set H) :=
        Subgroup.comap_normalizer_eq_of_le_range
          (by simpa using (inf_le_left : H ⊓ CFSG.Open.pCoreOf 2 D.M ≤ H))
      have hdNW : d ∈ Subgroup.normalizer (W_H : Set H) := by
        rw [← hnorm]
        exact hdNinf
      have hmem : π d ∈ (Subgroup.normalizer (W_H : Set H)).map π :=
        Subgroup.mem_map_of_mem π hdNW
      exact Subgroup.le_normalizer_map (f := π) (H := W_H) hmem
    have hcentEq : Subgroup.centralizer ({z} : Set (componentsQuot e)) =
        (Subgroup.centralizer (A : Set H)).map π := by
      have h1 : Subgroup.centralizer ({z} : Set (componentsQuot e)) =
          Subgroup.centralizer ((A.map π : Subgroup (componentsQuot e)) : Set _) := by
        rw [hmapA, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact h1.trans hcop.symm
    have hCXle : Subgroup.centralizer ({z} : Set (componentsQuot e)) ≤
        Subgroup.normalizer
          ((componentsImage (D := D) e : Subgroup (componentsQuot e)) : Set _) := by
      rw [hcentEq, hWdef]
      exact hmapCen
    intro j hj
    have hfix : Subgroup.normalizerMonoidHom J ⟨z, hzN⟩ j = j := by
      simpa [CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup] using hj
    have hcomm : (j : componentsQuot e) * z = z * (j : componentsQuot e) := by
      have h := congrArg (fun k : J => (k : componentsQuot e)) hfix
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      calc (j : componentsQuot e) * z = (z * (j : componentsQuot e) * z⁻¹) * z := by rw [h]
        _ = z * (j : componentsQuot e) := by group
    have hCen : (j : componentsQuot e) ∈ Subgroup.centralizer ({z} : Set _) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm
    exact hCXle hCen
  exact ⟨f, hf, hSz, z, hzN, hz3, hαne, hWnorm, hFix⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
