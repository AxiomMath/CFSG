module

public import CFSG.RankThree.PartTwo.Sec16.Item166ThetaTripleA6
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdCyc
public import CFSG.CGT.Timmesfeld75.AltCover

public section

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open scoped commutatorElement

private theorem ker_comp_sigma_le_center {Γ T : Type} [Group Γ] [Group T]
    (hperf : Group.IsPerfect Γ) (π : Γ →* T)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) :
    ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker ≤ Subgroup.center Γ := by
  haveI : Group.IsPerfect Γ := hperf
  intro g hg
  have hπg : π g ∈ Subgroup.center T := by
    rw [← ThetaTripleA6.sigmaOfTripleCover_ker hT]
    exact hg
  have hcomm : ∀ x : Γ, ⁅g, x⁆ ∈ π.ker := by
    intro x
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subgroup.mem_center_iff.1 hπg (π x)).symm
  have hgZ : (g : Γ ⧸ Subgroup.center Γ) ∈
      Subgroup.center (Γ ⧸ Subgroup.center Γ) := by
    rw [Subgroup.mem_center_iff]
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
      have hdiv : (x * g) / (g * x) = ⁅g, x⁆⁻¹ := by
        rw [div_eq_mul_inv]
        simp only [commutatorElement_def]
        group
      rw [hdiv]
      exact inv_mem (hK (hcomm x))
  rw [Group.IsPerfect.center_quotient_center_eq_bot Γ, Subgroup.mem_bot] at hgZ
  exact (QuotientGroup.eq_one_iff g).1 hgZ

private theorem card_ker_comp_sigma {Γ T : Type} [Group Γ] [Group T]
    (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    Nat.card π.ker * 3 =
      Nat.card ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker := by
  let K' : Subgroup Γ := ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker
  let ψ : K' →* Subgroup.center T :=
    (π.comp K'.subtype).codRestrict _ (fun x => by
      rw [← ThetaTripleA6.sigmaOfTripleCover_ker hT]
      exact x.2)
  have hψker : ψ.ker = π.ker.subgroupOf K' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext (MonoidHom.mem_ker.mp hx)
  have hψrange : ψ.range = ⊤ := by
    rw [eq_top_iff]
    rintro t -
    have ht1 : (ThetaTripleA6.sigmaOfTripleCover hT) (t : T) = 1 := by
      have htker : (t : T) ∈ (ThetaTripleA6.sigmaOfTripleCover hT).ker := by
        rw [ThetaTripleA6.sigmaOfTripleCover_ker hT]
        exact t.2
      exact MonoidHom.mem_ker.mp htker
    obtain ⟨x, hx⟩ := hπ (t : T)
    have hxK : x ∈ K' := by
      rw [MonoidHom.mem_ker]
      show (ThetaTripleA6.sigmaOfTripleCover hT) (π x) = 1
      rw [hx]
      exact ht1
    exact ⟨⟨x, hxK⟩, Subtype.ext hx⟩
  have hNK' : π.ker ≤ K' := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show (ThetaTripleA6.sigmaOfTripleCover hT) (π x) = 1
    rw [MonoidHom.mem_ker.mp hx, map_one]
  have hψcard := Subgroup.card_ker_mul_card_range ψ
  rw [hψker, hψrange, Subgroup.card_top, hT.1] at hψcard
  have hNsub : Nat.card (π.ker.subgroupOf K') = Nat.card π.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK').toEquiv
  rw [hNsub] at hψcard
  exact hψcard

private lemma not_sq_dvd_360 {r : ℕ} (hr : 5 ≤ r) (hrp : r.Prime) : ¬ r ^ 2 ∣ 360 := by
  intro h
  have hdvd : r ∣ 360 := (dvd_pow_self r (by norm_num : 2 ≠ 0)).trans h
  have hfac : (360 : ℕ) = 2 ^ 3 * 3 ^ 2 * 5 := by norm_num
  rw [hfac] at hdvd
  have h2 : ¬ r ∣ 2 := fun hd => by
    have h' := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp hd
    omega
  have h3 : ¬ r ∣ 3 := fun hd => by
    have h' := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_three).mp hd
    omega
  have h5 : r ∣ 5 := by
    rcases hrp.dvd_mul.mp hdvd with h' | h'
    · rcases hrp.dvd_mul.mp h' with h'' | h''
      · exact absurd (hrp.dvd_of_dvd_pow h'') h2
      · exact absurd (hrp.dvd_of_dvd_pow h'') h3
    · exact h'
  have hr5 : r = 5 := (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_five).mp h5
  have h25 : 25 ∣ 360 := by simpa [hr5] using h
  norm_num at h25

private lemma pow_dvd_360 {r n : ℕ} (hr : 5 ≤ r) (hrp : r.Prime)
    (h : r ^ n ∣ 360) : n ≤ 1 := by
  by_contra hn
  have hn2 : 2 ≤ n := by omega
  exact not_sq_dvd_360 hr hrp ((pow_dvd_pow r hn2).trans h)

private lemma isCyclic_of_isPGroup_card_360 {X : Type} [Group X] [Finite X]
    (hX : Nat.card X = 360) {r : ℕ} (hr : 5 ≤ r) (hrp : r.Prime)
    (S : Subgroup X) (hS : IsPGroup r S) : IsCyclic S := by
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := r) (G := S) hS
  have hdvd : r ^ n ∣ 360 := by
    rw [← hn, ← hX]
    exact Subgroup.card_subgroup_dvd_card S
  have hn1 : n ≤ 1 := pow_dvd_360 hr hrp hdvd
  have hSdvd : Nat.card S ∣ r := by
    rw [hn]
    interval_cases n <;> simp
  exact isCyclic_of_card_dvd_prime hSdvd

private theorem isMulCommutative_sylow_of_five_le {Γ T : Type} [Group Γ] [Finite Γ]
    [Group T] (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK' : ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker ≤ Subgroup.center Γ)
    {r : ℕ} (hrp : r.Prime) (hr : 5 ≤ r) (P : Sylow r Γ) :
    IsMulCommutative (P : Subgroup Γ) := by
  classical
  haveI : Fact r.Prime := ⟨hrp⟩
  let K' : Subgroup Γ := ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker
  let φ : (P : Subgroup Γ) →* Γ ⧸ K' :=
    (QuotientGroup.mk' K').comp (P : Subgroup Γ).subtype
  have hK'norm : K'.Normal := MonoidHom.normal_ker _
  haveI : K'.Normal := hK'norm
  have hφker : φ.ker = K'.subgroupOf (P : Subgroup Γ) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk' K') (x : Γ) = 1 ↔ (x : Γ) ∈ K'
    exact QuotientGroup.eq_one_iff (x : Γ)
  have hScyclic : IsCyclic φ.range := by
    have hcard : Nat.card (Γ ⧸ K') = 360 := by
      have hτ : Function.Surjective ((ThetaTripleA6.sigmaOfTripleCover hT).comp π) :=
        (ThetaTripleA6.sigmaOfTripleCover_surjective hT).comp hπ
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hτ).toEquiv,
        CFSG.RankThree.PartTwo.KFacts.K412.card_alternating_six_seven.1]
    have hP : IsPGroup r ↥(P : Subgroup Γ) := P.isPGroup'
    exact isCyclic_of_isPGroup_card_360 hcard hr hrp φ.range
      (hP.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective)
  have hQcyc : IsCyclic ((P : Subgroup Γ) ⧸ K'.subgroupOf (P : Subgroup Γ)) := by
    have hA : IsCyclic ((P : Subgroup Γ) ⧸ φ.ker) :=
      (QuotientGroup.quotientKerEquivRange φ).isCyclic.mpr hScyclic
    exact (QuotientGroup.quotientMulEquivOfEq hφker).isCyclic.mp hA
  haveI : IsCyclic ((P : Subgroup Γ) ⧸ K'.subgroupOf (P : Subgroup Γ)) := hQcyc
  refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (QuotientGroup.mk' (K'.subgroupOf (P : Subgroup Γ))) ?_
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext
    (Subgroup.mem_center_iff.mp (hK' (Subgroup.mem_subgroupOf.mp hx)) (y : Γ))

private theorem isPGroup_two_ker {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (hperf : Group.IsPerfect Γ) (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) (hK3 : Nat.Coprime (Nat.card π.ker) 3) :
    IsPGroup 2 π.ker := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect Γ := hperf
  have hK' : ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker ≤
      Subgroup.center Γ := ker_comp_sigma_le_center hperf π hT hK
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card π.ker).primeFactorsList.length, ?_⟩
  refine Nat.eq_prime_pow_of_unique_prime_dvd (Nat.card_pos (α := π.ker)).ne' ?_
  intro r hrp hrdvd
  by_contra hr2
  have hr3 : r ≠ 3 := by
    have hnot3 : ¬ 3 ∣ Nat.card π.ker :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hK3.symm
    rintro rfl
    exact hnot3 hrdvd
  have hr5 : 5 ≤ r := hrp.five_le_of_ne_two_of_ne_three hr2 hr3
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' (G := π.ker) r hrdvd
  have hzΓord : orderOf (z : Γ) = r := by
    rw [Subgroup.orderOf_coe]
    exact hzord
  have hzP : IsPGroup r (Subgroup.zpowers (z : Γ)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [pow_one, Nat.card_zpowers, hzΓord]
  obtain ⟨P, hPle⟩ := hzP.exists_le_sylow
  haveI : IsMulCommutative (P : Subgroup Γ) :=
    isMulCommutative_sylow_of_five_le π hπ hT hK' hrp hr5 P
  have hzPmem : (z : Γ) ∈ (P : Subgroup Γ) := hPle (Subgroup.mem_zpowers (z : Γ))
  have hzinf : (z : Γ) ∈ ((P : Subgroup Γ) ⊓ Subgroup.center Γ) :=
    Subgroup.mem_inf.mpr ⟨hzPmem, hK z.2⟩
  rw [CFSG.Quasithin.SBd19F.sylow_inf_center_eq_bot P, Subgroup.mem_bot] at hzinf
  have h1 : orderOf (z : Γ) = 1 := by rw [hzinf, orderOf_one]
  omega

private theorem exists_order_three {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6))) :
    ∃ c ∈ ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker, orderOf c = 3 := by
  have hcard := card_ker_comp_sigma (π := π) hπ hT
  have h3dvd : 3 ∣ Nat.card ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker := by
    rw [← hcard]
    exact ⟨Nat.card π.ker, by rw [mul_comm]⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ :=
    exists_prime_orderOf_dvd_card' (G := ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker)
      3 h3dvd
  exact ⟨(c : Γ), c.2, by rwa [Subgroup.orderOf_coe]⟩

private theorem card_map_ker_quotient_zpowers {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    {c : Γ} (hcK' : c ∈ ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker)
    (hcord : orderOf c = 3) [hCnormZ : (Subgroup.zpowers c).Normal] :
    Nat.card (Subgroup.map (QuotientGroup.mk' (Subgroup.zpowers c))
      ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker) = Nat.card π.ker := by
  classical
  let K' : Subgroup Γ := ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker
  let C : Subgroup Γ := Subgroup.zpowers c
  have hCcard : Nat.card C = 3 := by rw [Nat.card_zpowers, hcord]
  have hCK' : C ≤ K' := Subgroup.zpowers_le.mpr hcK'
  haveI : C.Normal := hCnormZ
  have hcardK' := card_ker_comp_sigma (π := π) hπ hT
  let φ : K' →* Γ ⧸ C := (QuotientGroup.mk' C).comp K'.subtype
  have hφker : φ.ker = C.subgroupOf K' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (QuotientGroup.mk' C) (x : Γ) = 1 ↔ (x : Γ) ∈ C
    exact QuotientGroup.eq_one_iff (x : Γ)
  have hφrange : φ.range = K'.map (QuotientGroup.mk' C) := by
    rw [show φ = (QuotientGroup.mk' C).comp K'.subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hCsubcard : Nat.card (C.subgroupOf K') = 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCK').toEquiv).trans hCcard
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hφker, hCsubcard, ← hcardK', mul_comm (Nat.card π.ker) 3] at h
  have hcardRange : Nat.card φ.range = Nat.card π.ker :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) h
  rw [← hφrange]
  exact hcardRange

private theorem exists_eta_of_order_three {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (hperf : Group.IsPerfect Γ) (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) (hN2 : IsPGroup 2 π.ker)
    {c : Γ} (hcK' : c ∈ ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker)
    (hcord : orderOf c = 3) [hCnormZ : (Subgroup.zpowers c).Normal] :
    ∃ η : Γ ⧸ Subgroup.zpowers c →* alternatingGroup (Fin 6),
      Function.Surjective η ∧
      η.ker ≤ Subgroup.center (Γ ⧸ Subgroup.zpowers c) ∧
      IsPGroup 2 η.ker ∧
      Nat.card η.ker = Nat.card π.ker ∧
      (∀ x : Γ, x ∈ π.ker → η (QuotientGroup.mk x) = 1) := by
  classical
  haveI : Group.IsPerfect Γ := hperf
  let K' : Subgroup Γ := ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker
  have hK'le : K' ≤ Subgroup.center Γ := ker_comp_sigma_le_center hperf π hT hK
  let C : Subgroup Γ := Subgroup.zpowers c
  have hCK' : C ≤ K' := Subgroup.zpowers_le.mpr hcK'
  haveI : C.Normal := hCnormZ
  let φ : K' →* Γ ⧸ C := (QuotientGroup.mk' C).comp K'.subtype
  have hφrange : φ.range = K'.map (QuotientGroup.mk' C) := by
    rw [show φ = (QuotientGroup.mk' C).comp K'.subtype from rfl,
      MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardRange : Nat.card φ.range = Nat.card π.ker := by
    rw [hφrange]
    exact card_map_ker_quotient_zpowers (π := π) hπ hT hcK' hcord (hCnormZ := hCnormZ)
  let η : Γ ⧸ C →* alternatingGroup (Fin 6) :=
    QuotientGroup.lift C ((ThetaTripleA6.sigmaOfTripleCover hT).comp π) hCK'
  have hηker : η.ker = φ.range := by
    rw [QuotientGroup.ker_lift]
    exact hφrange.symm
  have hηsurj : Function.Surjective η := by
    intro y
    obtain ⟨x, hx⟩ := (ThetaTripleA6.sigmaOfTripleCover_surjective hT).comp hπ y
    exact ⟨QuotientGroup.mk x, by rw [QuotientGroup.lift_mk']; exact hx⟩
  have hηcenter : η.ker ≤ Subgroup.center (Γ ⧸ C) := by
    rw [hηker]
    rintro _ ⟨x, -, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    change (QuotientGroup.mk g) * (QuotientGroup.mk (x : Γ)) =
      (QuotientGroup.mk (x : Γ)) * (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp (hK'le x.2) g]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) (G := π.ker) hN2
  have hcardη : Nat.card η.ker = Nat.card π.ker := by rw [hηker, hcardRange]
  have hη2 : IsPGroup 2 η.ker := by
    refine IsPGroup.of_card (n := k) ?_
    rw [hcardη, hk]
  have hηmap : ∀ x : Γ, x ∈ π.ker → η (QuotientGroup.mk x) = 1 := by
    intro x hx
    rw [QuotientGroup.lift_mk']
    show (ThetaTripleA6.sigmaOfTripleCover hT) (π x) = 1
    rw [MonoidHom.mem_ker.mp hx, map_one]
  exact ⟨η, hηsurj, hηcenter, hη2, hcardη, hηmap⟩

private theorem card_ker_le_two_of_isPGroup_two {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (hperf : Group.IsPerfect Γ) (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) (hN2 : IsPGroup 2 π.ker) :
    Nat.card π.ker ≤ 2 := by
  haveI : Group.IsPerfect Γ := hperf
  obtain ⟨c, hcK', hcord⟩ := exists_order_three (π := π) hπ hT
  have hCnorm : (Subgroup.zpowers c).Normal :=
    Subgroup.normal_of_le_center
      ((Subgroup.zpowers_le.mpr hcK').trans (ker_comp_sigma_le_center hperf π hT hK))
  obtain ⟨η, hηsurj, hηcenter, hη2, hcardη, -⟩ :=
    exists_eta_of_order_three hperf π hπ hT hK hN2 hcK' hcord (hCnormZ := hCnorm)
  have hle :=
    CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
      (n := 6) (by norm_num) η hηsurj hηcenter hη2
  rwa [hcardη] at hle

theorem card_ker_le_two {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (hperf : Group.IsPerfect Γ) (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) (hK3 : Nat.Coprime (Nat.card π.ker) 3) :
    Nat.card π.ker ≤ 2 :=
  card_ker_le_two_of_isPGroup_two hperf π hπ hT hK
    (isPGroup_two_ker hperf π hπ hT hK hK3)

private lemma card_ker_eq_two_of_mem {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (hperf : Group.IsPerfect Γ) (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) (hK3 : Nat.Coprime (Nat.card π.ker) 3)
    {z : Γ} (hz : z ∈ π.ker) (hz1 : z ≠ 1) :
    Nat.card π.ker = 2 ∧ orderOf z = 2 := by
  have hcardle := card_ker_le_two hperf π hπ hT hK hK3
  have hnt : Nontrivial π.ker :=
    ⟨⟨z, hz⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩
  have hcard2 : Nat.card π.ker = 2 := by
    have hpos : 1 < Nat.card π.ker := Finite.one_lt_card_iff_nontrivial.mpr hnt
    omega
  refine ⟨hcard2, ?_⟩
  have hdvd : orderOf z ∣ 2 := by
    rw [← hcard2]
    exact Subgroup.orderOf_dvd_natCard π.ker hz
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hz1
  · exact h2

private lemma eq_one_of_sq_eq_one_of_mem_zpowers {G : Type} [Group G] {c u : G}
    (hc : orderOf c = 3) (hu : u ∈ Subgroup.zpowers c) (hu2 : u ^ 2 = 1) : u = 1 := by
  have h1 : orderOf u ∣ 3 := by
    rw [← hc]
    exact orderOf_dvd_of_mem_zpowers hu
  have h2 : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
  have h3 : orderOf u ∣ 1 := by
    simpa using Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

private theorem involution_eq_one_or_mk_z {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (hperf : Group.IsPerfect Γ) (π : Γ →* T)
    (hK : π.ker ≤ Subgroup.center Γ)
    {C : Subgroup Γ} [hCnorm : C.Normal]
    (η : Γ ⧸ C →* alternatingGroup (Fin 6)) (hηsurj : Function.Surjective η)
    (hcardη2 : Nat.card η.ker = 2)
    (hηmap : ∀ x : Γ, x ∈ π.ker → η (QuotientGroup.mk x) = 1)
    {z : Γ} (hz : z ∈ π.ker) (hzord : orderOf z = 2) (hznotC : z ∉ C) :
    ∀ v : Γ ⧸ C, v * v = 1 → v = 1 ∨ v = QuotientGroup.mk z := by
  classical
  haveI : Group.IsPerfect Γ := hperf
  let zbar : Γ ⧸ C := QuotientGroup.mk z
  have hzbar_ne : zbar ≠ 1 := by
    intro h
    exact hznotC ((QuotientGroup.eq_one_iff z).mp h)
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hzord]
    exact pow_orderOf_eq_one z
  have hzbarsq : zbar * zbar = 1 := by
    change (QuotientGroup.mk z) * (QuotientGroup.mk z) = 1
    rw [← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]
  have hzbarmem : zbar ∈ η.ker := by
    rw [MonoidHom.mem_ker]
    exact hηmap z hz
  have hzbarcentral : ∀ x : Γ ⧸ C, x * zbar = zbar * x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    change (QuotientGroup.mk g) * (QuotientGroup.mk z) =
      (QuotientGroup.mk z) * (QuotientGroup.mk g)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp (hK hz) g]
  have hkeriff : ∀ u : Γ ⧸ C, η u = 1 ↔ u = 1 ∨ u = zbar := by
    intro u
    constructor
    · intro hu
      by_cases hu1 : u = 1
      · exact Or.inl hu1
      · right
        obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : η.ker)).mp hcardη2
        have hu' : (⟨u, hu⟩ : η.ker) ≠ 1 := fun h => hu1 (congrArg Subtype.val h)
        have hz' : (⟨zbar, hzbarmem⟩ : η.ker) ≠ 1 :=
          fun h => hzbar_ne (congrArg Subtype.val h)
        exact congrArg Subtype.val ((huniq ⟨u, hu⟩ hu').trans
          (huniq ⟨zbar, hzbarmem⟩ hz').symm)
    · rintro (rfl | rfl)
      · exact map_one η
      · exact hzbarmem
  have hperfq : Group.IsPerfect (Γ ⧸ C) := inferInstance
  intro v hv
  have h := CFSG.CGT.Timmesfeld75.involution_mem_ker_of_double_cover_six hηsurj
    hzbar_ne hzbarsq hzbarcentral hkeriff hperfq v hv
  simpa only [zbar] using h

private lemma eq_one_or_eq_of_mem_zpowers_or_mul_mem {G : Type} [Group G]
    {c z w : G} (hc : orderOf c = 3) (hz2 : z * z = 1) (hzc : z * w = w * z)
    (hw : w ^ 2 = 1) (h : w ∈ Subgroup.zpowers c ∨ w * z ∈ Subgroup.zpowers c) :
    w = 1 ∨ w = z := by
  have hww : w * w = 1 := by rw [← pow_two]; exact hw
  rcases h with hwC | hwzC
  · exact Or.inl (eq_one_of_sq_eq_one_of_mem_zpowers hc hwC hw)
  · have hu2 : (w * z) ^ 2 = 1 := by
      calc (w * z) ^ 2 = (w * z) * (w * z) := pow_two _
        _ = w * (z * w) * z := by group
        _ = w * (w * z) * z := by rw [hzc]
        _ = w * w * (z * z) := by group
        _ = 1 := by rw [hww, hz2, mul_one]
    have hu1 : w * z = 1 :=
      eq_one_of_sq_eq_one_of_mem_zpowers hc hwzC hu2
    refine Or.inr ?_
    calc w = w * 1 := by rw [mul_one]
      _ = w * (z * z) := by rw [hz2]
      _ = (w * z) * z := by group
      _ = 1 * z := by rw [hu1]
      _ = z := by rw [one_mul]

theorem eq_one_or_eq_of_sq_eq_one {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (hperf : Group.IsPerfect Γ) (π : Γ →* T) (hπ : Function.Surjective π)
    (hT : Sec4.IsTripleCover T (alternatingGroup (Fin 6)))
    (hK : π.ker ≤ Subgroup.center Γ) (hK3 : Nat.Coprime (Nat.card π.ker) 3)
    {z : Γ} (hz : z ∈ π.ker) (hz1 : z ≠ 1) {w : Γ} (hw : w ^ 2 = 1) :
    w = 1 ∨ w = z := by
  classical
  haveI : Group.IsPerfect Γ := hperf
  obtain ⟨hcard2, hzord⟩ := card_ker_eq_two_of_mem hperf π hπ hT hK hK3 hz hz1
  obtain ⟨c, hcK', hcord⟩ := exists_order_three (π := π) hπ hT
  have hK'le : ((ThetaTripleA6.sigmaOfTripleCover hT).comp π).ker ≤
      Subgroup.center Γ := ker_comp_sigma_le_center hperf π hT hK
  let C : Subgroup Γ := Subgroup.zpowers c
  have hCnorm : C.Normal :=
    Subgroup.normal_of_le_center ((Subgroup.zpowers_le.mpr hcK').trans hK'le)
  haveI : C.Normal := hCnorm
  have hznotC : z ∉ C := by
    intro hzC
    have hdvd : orderOf z ∣ 3 := by
      rw [← hcord]
      exact orderOf_dvd_of_mem_zpowers hzC
    rw [hzord] at hdvd
    exact absurd hdvd (by norm_num)
  have hN2 : IsPGroup 2 π.ker := isPGroup_two_ker hperf π hπ hT hK hK3
  have hCnormZ : (Subgroup.zpowers c).Normal := hCnorm
  obtain ⟨η, hηsurj, -, -, hcardη, hηmap⟩ :=
    exists_eta_of_order_three hperf π hπ hT hK hN2 hcK' hcord (hCnormZ := hCnormZ)
  have hcardη2 : Nat.card η.ker = 2 := by rw [hcardη, hcard2]
  have hinv := involution_eq_one_or_mk_z hperf π hK η hηsurj hcardη2 hηmap hz hzord hznotC
  have hz2 : z * z = 1 := by
    rw [← pow_two, ← hzord]
    exact pow_orderOf_eq_one z
  have hww : w * w = 1 := by rw [← pow_two]; exact hw
  have hwbar : (QuotientGroup.mk w : Γ ⧸ C) * (QuotientGroup.mk w : Γ ⧸ C) = 1 := by
    rw [← QuotientGroup.mk_mul, hww, QuotientGroup.mk_one]
  rcases hinv (QuotientGroup.mk w : Γ ⧸ C) hwbar with hw1 | hwz
  · have hwC : w ∈ Subgroup.zpowers c := (QuotientGroup.eq_one_iff w).mp hw1
    exact eq_one_or_eq_of_mem_zpowers_or_mul_mem hcord hz2
      (Subgroup.mem_center_iff.mp (hK hz) w).symm hw (Or.inl hwC)
  · have hwzC : w * z ∈ Subgroup.zpowers c := by
      have hq : (QuotientGroup.mk (w * z) : Γ ⧸ C) = 1 := by
        rw [QuotientGroup.mk_mul, hwz]
        rw [← QuotientGroup.mk_mul, hz2, QuotientGroup.mk_one]
      exact (QuotientGroup.eq_one_iff (w * z)).mp hq
    exact eq_one_or_eq_of_mem_zpowers_or_mul_mem hcord hz2
      (Subgroup.mem_center_iff.mp (hK hz) w).symm hw (Or.inr hwzC)

end CFSG.RankThree.PartTwo.Sec16.Kcd166

end
