module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTraceNode
public import CFSG.Monster.B.TwoA.Amalgam.DistThreeTraceCent
public import CFSG.Monster.B.TwoA.Amalgam.EightOrbitsBase
public import CFSG.Monster.B.TwoA.Amalgam.TypeFourDistStd

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4
open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open CFSG.Monster.B.Co2 (v0)
open CFSG.LieType.Chevalley.C2E6Overlap (K)

theorem inl_fibT_two_mem_parStar :
    (SemidirectProduct.inl (fibT 2) : GStar) ∈ parStar firstJ := by
  rw [← centralizer_rootStar, Subgroup.mem_centralizer_singleton_iff]
  have h : rootInvM * (fibT 2 : ModGL Tag.E6 K) = (fibT 2 : ModGL Tag.E6 K) * rootInvM :=
    commute_pinnedX_fibT 2 isRoot_theta (by decide +kernel) 1
  have h' : rootInv * fibT 2 = fibT 2 * rootInv := Subtype.ext h
  rw [rootStar, ← map_mul, ← map_mul, h']

theorem inl_fibT_two_mem_fibOrbit :
    (SemidirectProduct.inl (fibT 2) : GStar) ∈ fibOrbit 2 :=
  mem_conjOrbit_self _ _

theorem isMid_two : IsMid 2 := Or.inr (Or.inl rfl)

@[expose] noncomputable def proj0 :
    Pc 0 →* Unitary.Usig :=
  p1Proj.comp (MulEquiv.subgroupCongr Pc_zero_eq_P1).toMonoidHom

theorem proj0_apply
    (g : Pc 0) : proj0 g = p1Proj ⟨g, g.2⟩ := rfl

theorem rhoP1_eq_phiU_proj0
    (g : Pc 0) : rhoP1 g = Unitary.phiU (proj0 g) := rfl

theorem proj0_eq_one_iff
    (g : Pc 0) : proj0 g = 1 ↔ (g : Dfull) ∈ N1 := by
  rw [proj0_apply, ← MonoidHom.mem_ker, ker_p1Proj, Subgroup.mem_subgroupOf]

theorem cQ_zpow_mem_N1 (j : ℤ) : cQ ^ j ∈ N1 := zpow_mem Sp8.cQ_mem_N1 j

@[expose] noncomputable def cPow
    (j : ℤ) : Pc 0 := ⟨cQ ^ j, N1_le_P1 (cQ_zpow_mem_N1 j)⟩

theorem proj0_cPow
    (j : ℤ) : proj0 (cPow j) = 1 := (proj0_eq_one_iff _).2 (cQ_zpow_mem_N1 j)

theorem exists_zpow_of_mk_eq
    {a b : Eam}
    (h : (QuotientGroup.mk a : Eam ⧸ Subgroup.zpowers cE') = QuotientGroup.mk b) :
    ∃ j : ℤ, (b : Dfull) = a * cQ ^ j := by
  rw [QuotientGroup.eq] at h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
  refine ⟨j, ?_⟩
  have hj' : ((cE' ^ j : Eam) : Dfull) = ((a⁻¹ * b : Eam) : Dfull) := congrArg Subtype.val hj
  rw [SubgroupClass.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] at hj'
  have hc : ((cE' : Eam) : Dfull) = cQ := rfl
  rw [hc] at hj'
  rw [hj']
  group

section Base

variable {θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar} {f : Chamber ≃ C2E6Std.stdChamber}
  (hadj : ∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
    stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i)
  (hfeq : ∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z)
  (hfB : f baseChamber = c₀)
  (hx : θ (QuotientGroup.mk xhatEam) = rootStar)
  (hinj : ∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
    (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
      QuotientGroup.mk (e'⁻¹ * xhatEam * e'))

theorem proj0_eq_of_rho1_eq
    {q q' : Pc 0} (h : rho1 θ q = rho1 θ q') : proj0 q = proj0 q' := by
  rw [rho1_apply, rho1_apply] at h
  obtain ⟨j, hj⟩ := exists_zpow_of_mk_eq (θ.injective h)
  have e : q' = q * cPow j := Subtype.ext hj
  rw [e, map_mul, proj0_cPow, mul_one]

include hadj hfeq hfB in
theorem proj_p₀_commute
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) {p₀ : Pc 0}
    (hp₀ : rho1 θ p₀ = SemidirectProduct.inl (fibT 2)) (u' : Unitary.Usig)
    (hu' : Unitary.sigmaAct Rsp (Unitary.phiU u') = Rsp) : proj0 p₀ * u' = u' * proj0 p₀ := by
  obtain ⟨q, hrq⟩ := rhoP1_surjective (Unitary.phiU u')
  have hqu : proj0 q = u' := by
    rw [rhoP1_eq_phiU_proj0] at hrq
    exact Unitary.phiU.injective hrq
  have hq : actP1 q Rsp = Rsp := by
    rw [actP1, hrq]
    conv_lhs => rw [← hu']
    rw [← Unitary.sigmaAct_mul, mul_inv_cancel, Unitary.sigmaAct_one]
  have hy : rho1 θ q * SemidirectProduct.inl (fibT 2) * (rho1 θ q)⁻¹ ∈ fibOrbit 2 :=
    ⟨rho1 θ q, rho1_mem_parStar hadj hfeq hfB q, rfl⟩
  have hn := nquot_conj hadj hfeq hfB isMid_two q
  have h1 := nquot_conj hadj hfeq hfB isMid_two 1
  rw [map_one, one_mul, inv_one, mul_one, actP1_one] at h1
  rw [quotSp_two] at hn h1
  have hmem : rho1 θ q * SemidirectProduct.inl (fibT 2) * (rho1 θ q)⁻¹ ∈
      conjOrbit radStar (SemidirectProduct.inl (fibT 2)) :=
    (nquot_eq_iff hadj hfeq hfB isMid_two inl_fibT_two_mem_fibOrbit hy).1 (by rw [h1, hn, hq])
  obtain ⟨γ, hγ, hγe⟩ := hmem
  rw [← map_cNE_eq_radStar hk0 hk hadj hfeq hfB] at hγ
  obtain ⟨n, hn', rfl⟩ := hγ
  have hnN : (n : Dfull) ∈ N1 := cNE_le_N1 (Subgroup.mem_subgroupOf.1 hn')
  have hrho : rho1 θ (q * p₀ * q⁻¹) = rho1 θ (n * p₀ * n⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hp₀, hγe]
  have h2 := proj0_eq_of_rho1_eq hrho
  have e1 : proj0 (q * p₀ * q⁻¹) = u' * proj0 p₀ * u'⁻¹ := by
    rw [map_mul, map_mul, map_inv, hqu]
  have e2 : proj0 (n * p₀ * n⁻¹) = proj0 p₀ := by
    rw [map_mul, map_mul, map_inv, (proj0_eq_one_iff n).2 hnN, one_mul, inv_one, mul_one]
  have h3 : u' * proj0 p₀ * u'⁻¹ = proj0 p₀ := e1.symm.trans (h2.trans e2)
  calc proj0 p₀ * u' = (u' * proj0 p₀ * u'⁻¹) * u' := by rw [h3]
    _ = u' * proj0 p₀ := by group

include hadj hfeq hfB in
theorem proj_p₀_ne_one
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) {p₀ : Pc 0}
    (hp₀ : rho1 θ p₀ = SemidirectProduct.inl (fibT 2)) : proj0 p₀ ≠ 1 := by
  intro h1
  have hp : (p₀ : Dfull) ∈ N1 := (proj0_eq_one_iff p₀).1 h1
  set x₁ : Pc 0 := ⟨xhat, xhat_mem_P1⟩
  have hsub : conjOrbit radStar (SemidirectProduct.inl (fibT 2)) ⊆
      {rho1 θ p₀, rho1 θ (p₀ * x₁)} := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [← map_cNE_eq_radStar hk0 hk hadj hfeq hfB] at hγ
    obtain ⟨n, hn', rfl⟩ := hγ
    have hnN : (n : Dfull) ∈ N1 := cNE_le_N1 (Subgroup.mem_subgroupOf.1 hn')
    have hc := Ehat_comm ⟨n, hnN.1⟩ ⟨p₀, hp.1⟩
    have hxn : (n : Dfull) * xhat = xhat * n := xhat_comm_of_mem_Jhat (P1_le_Jhat n.2)
    set b := (bV (psiW ⟨n, hnN.1⟩) (psiW ⟨p₀, hp.1⟩)).val with hb
    have hconj : (n : Dfull) * p₀ * (n : Dfull)⁻¹ = p₀ * xhat ^ b := by
      have hc' : (n : Dfull) * p₀ = p₀ * n * xhat ^ b := hc
      have hxb : (n : Dfull) * xhat ^ b = xhat ^ b * n := (Commute.pow_right hxn b).eq
      calc (n : Dfull) * p₀ * (n : Dfull)⁻¹ = p₀ * n * xhat ^ b * (n : Dfull)⁻¹ := by rw [hc']
        _ = p₀ * (n * xhat ^ b) * (n : Dfull)⁻¹ := by group
        _ = p₀ * xhat ^ b := by rw [hxb]; group
    have hb2 : b = 0 ∨ b = 1 := by
      have := ZMod.val_lt (bV (psiW ⟨n, hnN.1⟩) (psiW ⟨p₀, hp.1⟩))
      omega
    rw [← hp₀, ← map_mul, ← map_inv, ← map_mul, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hb2 with hb0 | hb1
    · left
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hconj, hb0, pow_zero, mul_one]
    · right
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hconj, hb1, pow_one]
      rfl
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [ncard_conjOrbit_radStar inl_fibT_two_mem_fibOrbit] at hle
  have h2 := Set.ncard_insert_le (rho1 θ p₀) {rho1 θ (p₀ * x₁)}
  rw [Set.ncard_singleton] at h2
  have h64 : fibUSize 2 = 64 := by decide
  omega

include hadj hfeq hfB in
theorem proj_p₀_eq
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) {p₀ : Pc 0}
    (hp₀ : rho1 θ p₀ = SemidirectProduct.inl (fibT 2)) : proj0 p₀ = Unitary.genU 6 :=
  (eq_one_or_eq_genU_six_of_commute (proj_p₀_commute hadj hfeq hfB hk0 hk hp₀)).resolve_left
    (proj_p₀_ne_one hadj hfeq hfB hk0 hk hp₀)

include hinj in
theorem exists_nbrRoot_eq
    {u : CVert} (hu : u ∈ cgraph.neighborSet (cvMul cv0 1)) :
    ∃ e : Eam, nbrRoot (ivB hx hinj 1) u = rho0 θ (xconj e) ∧
      clabel u = cQ * (xconj e : Dfull) := by
  obtain ⟨e, he⟩ := nbrShift_symm_mk (rfl : cvMul cv0 1 = cvMul cv0 1) ⟨u, hu⟩
  refine ⟨e, ?_, ?_⟩
  · rw [nbrRoot_of_mem (ivB hx hinj 1) hu, ivB,
      rootV_eq_of_coe θ hx hinj (rfl : cvMul cv0 1 = cvMul cv0 1) he, inl_rootPt_mk]
  · have he' : u = nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e) := by
      change u = cvMul (nbr a0_mem_Ehat a0_not_mem_N1 (Quotient.mk _ e)) 1 at he
      rw [he, cvMul_one]
    rw [he', clabel_nbr]
    rfl

theorem eightSize_eq_iff : ∀ i : Fin 8, eightSize i = 8064 → i = 1 := by decide

include hadj hfeq hfB in
theorem mem_omegaB_one_of_omegaTwo
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) (hτ : psiW (labE k) = Unitary.tauW) {u : CVert}
    (hΩ : u ∈ omegaTwo cv0 (cvOf (jhatS k))) : u ∈ omegaB hx hinj 1 1 := by
  obtain ⟨huΓ, hcard⟩ := hΩ
  have hu1 : u ∈ cgraph.neighborSet (cvMul cv0 1) := by rw [cvMul_one]; exact huΓ
  obtain ⟨i, hi, -⟩ := existsUnique_mem_omegaB hadj hfeq hfB hx hinj 1 hu1
  have horb := cvOrbit_omegaB hadj hfeq hfB hx hinj 1 hk0 hk hτ i hi
  have hsize := ncard_omegaB hadj hfeq hfB hx hinj 1 hk0 hk hτ i
  rw [cvMul_one, cvMul_one] at horb
  have hi8 : eightSize i = 8064 := by
    rw [← hsize, ← horb]
    exact hcard
  obtain rfl := eightSize_eq_iff i hi8
  exact hi

include hadj hfeq hfB in
theorem exists_clabel_eq
    {u : CVert} (hu1 : u ∈ cgraph.neighborSet (cvMul cv0 1))
    (hroot : u ∈ rootSubB hx hinj 1 2) {p₀ : Pc 0}
    (hp₀ : rho1 θ p₀ = SemidirectProduct.inl (fibT 2)) :
    ∃ (p : Pc 0) (j : ℤ),
      nbrRoot (ivB hx hinj 1) u = rho1 θ p * SemidirectProduct.inl (fibT 2) * (rho1 θ p)⁻¹ ∧
      clabel u = ((cPow 1 * (p * p₀ * p⁻¹) * cPow j : Pc 0) : Dfull) := by
  obtain ⟨e, hre, hle⟩ := exists_nbrRoot_eq hx hinj hu1
  have hxo := nbrRoot_mem_of_mem_nbrPull (ivB hx hinj 1) hroot
  obtain ⟨p, hp⟩ := exists_rho1_conj hadj hfeq hfB hxo
  have hr1 : rho1 θ (p * p₀ * p⁻¹) = nbrRoot (ivB hx hinj 1) u := by
    rw [map_mul, map_mul, map_inv, hp₀]
    exact hp
  have hr2 : θ (QuotientGroup.mk ⟨((p * p₀ * p⁻¹ : Pc 0) : Dfull), Pc_le_Eam 0 (p * p₀ * p⁻¹).2⟩) =
      θ (QuotientGroup.mk (xconj e)) := hr1.trans hre
  obtain ⟨j, hj⟩ := exists_zpow_of_mk_eq (θ.injective hr2)
  refine ⟨p, j, hp.symm, ?_⟩
  rw [hle, hj]
  simp only [cPow, Subgroup.coe_mul, zpow_one]
  group

include hadj hfeq hfB in
theorem quotB_eq_sigmaAct
    {u : CVert} {p : Pc 0}
    (hp : nbrRoot (ivB hx hinj 1) u = rho1 θ p * SemidirectProduct.inl (fibT 2) * (rho1 θ p)⁻¹) :
    quotB hx hinj 1 2 u = Unitary.sigmaAct Rsp (Unitary.phiU (proj0 p)⁻¹) := by
  have hq1 : quotB hx hinj 1 2 u =
      nquot θ 2 (rho1 θ p * SemidirectProduct.inl (fibT 2) * (rho1 θ p)⁻¹) := by
    rw [← hp]
    rfl
  have h5 : nquot θ 2 (rho1 θ p * SemidirectProduct.inl (fibT 2) * (rho1 θ p)⁻¹) =
      actP1 p (quotSp 2) := nquot_conj hadj hfeq hfB isMid_two p
  have h6 : actP1 p (quotSp 2) = Unitary.sigmaAct Rsp (Unitary.phiU (proj0 p)⁻¹) := by
    rw [quotSp_two, map_inv Unitary.phiU (proj0 p)]
    exact congrArg (fun g => Unitary.sigmaAct Rsp g⁻¹) (rhoP1_eq_phiU_proj0 p)
  exact hq1.trans (h5.trans h6)

include hadj hfeq hfB in
theorem label_transv_of_mem_rootSubB
    {k : Jhat} (hk0 : cvOf (jhatS k) ≠ cv0)
    (hk : ¬ cgraph.Adj cv0 (cvOf (jhatS k))) {u : CVert}
    (hu1 : u ∈ cgraph.neighborSet (cvMul cv0 1)) (hroot : u ∈ rootSubB hx hinj 1 2) :
    ∃ hP : clabel u ∈ P1, p1Proj ⟨clabel u, hP⟩ = Unitary.transvU (quotB hx hinj 1 2 u) := by
  obtain ⟨p₀, hp₀⟩ := exists_rho1_eq hadj hfeq hfB inl_fibT_two_mem_parStar
  obtain ⟨p, j, hp, hlab⟩ := exists_clabel_eq hadj hfeq hfB hx hinj hu1 hroot hp₀
  have hP : clabel u ∈ P1 := by
    rw [hlab]
    exact (cPow 1 * (p * p₀ * p⁻¹) * cPow j).2
  refine ⟨hP, ?_⟩
  have hpe : proj0 p₀ = Unitary.genU 6 := proj_p₀_eq hadj hfeq hfB hk0 hk hp₀
  have hs₀ : proj0 (cPow 1 * (p * p₀ * p⁻¹) * cPow j) = proj0 p * Unitary.genU 6 * (proj0 p)⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_mul, map_inv, proj0_cPow, proj0_cPow, one_mul, mul_one, hpe]
  have himg : p1Proj ⟨clabel u, hP⟩ = proj0 p * Unitary.genU 6 * (proj0 p)⁻¹ := by
    refine Eq.trans ?_ hs₀
    show p1Proj ⟨clabel u, hP⟩ =
      p1Proj ((MulEquiv.subgroupCongr Pc_zero_eq_P1) (cPow 1 * (p * p₀ * p⁻¹) * cPow j))
    congr 1
    exact Subtype.ext hlab
  rw [himg, quotB_eq_sigmaAct hadj hfeq hfB hx hinj hp,
    Unitary.transvU_sigmaAct Unitary.isSingPt_Rsp (proj0 p)⁻¹, Unitary.transvU_Rsp,
    inv_inv (proj0 p)]

end Base

theorem distThreeBaseTransvFact_holds :
    DistThreeBaseTransvFact := by
  intro k u h4 hτ' hΩ
  obtain ⟨θ₁, f₁, h1, h2, h3⟩ := short_F4_standard_twisted_E6_quotient
  obtain ⟨θ, f, hadj, -, hfeq, hfB⟩ := exists_normalized_quotient θ₁ f₁ h1 h2 h3
  have hx := map_mk_xhatEam_of_quotient hadj hfeq hfB
  have hinj := vtx_zero_eq_iff_of_quotient hadj hfeq hfB
  obtain ⟨hne, hna, -⟩ := cgraph_dist_eq_two_iff.1 h4.1
  have hk0 : cvOf (jhatS k) ≠ cv0 := Ne.symm hne
  have hτ : psiW (labE k) = Unitary.tauW := by rw [psiW_labE, hτ']
  have hi := mem_omegaB_one_of_omegaTwo hadj hfeq hfB hx hinj hk0 hna hτ hΩ
  rw [(omegaB_eq_parts hx hinj 1).2.2.1] at hi
  obtain ⟨hroot, hquot⟩ := hi
  have hu1 : u ∈ cgraph.neighborSet (cvMul cv0 1) := by rw [cvMul_one]; exact hΩ.1
  obtain ⟨hP, himg⟩ := label_transv_of_mem_rootSubB hadj hfeq hfB hx hinj hk0 hna hu1 hroot
  exact ⟨hP, quotB hx hinj 1 2 u, hquot, himg⟩

end CFSG.Monster.B.TwoA.Amalgam
