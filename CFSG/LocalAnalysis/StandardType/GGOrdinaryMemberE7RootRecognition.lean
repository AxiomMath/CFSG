module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoGenHyper
public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenSL
public import CFSG.LocalAnalysis.StandardType.PhanEStdRootNodes
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusE7
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LieType.SeitzGeneration.ExcTorusCount
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.SplitRootAction
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveFrameCentralizer
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNormalClosureNbr
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Conjugation

public noncomputable section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.CurtisTits CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.PhiTwoRootGen
  CFSG.RankThree.PartOne.KE6

theorem exists_e7_parent_le_phiTwoComp_of_prime_with_fixed_character
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (lambda : e7Data_valid.minGroup K →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (hBs : Bs ≤ lambda.range)
    (S : LangSetup .E7 (AlgebraicClosure K) 5)
    (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K))
    (hinj : Function.Injective iota)
    (hformula : ∀ u, iota u = S.D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL .E7 K) * S.D.g0)
    (hwhole : ∀ z : ModGL .E7 (AlgebraicClosure K),
      (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧
        iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K u) = z) ↔
      ∃ b : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ,
        (∀ j, b j ^ p = 1) ∧ rootDiagUnit .E7 b = z)
    {r : MulAut Bs} (hr : GGIsReflection p r) (j : Fin Tag.E7.rank)
    (hroot : (CFSG.LieType.CurtisTits.rankOne
        (e7Datum K).rootGroup j).map lambda = ggRankOnePerf Bs r) :
    ∃ beta : Fin Tag.E7.rank → ℤ, IsRoot .E7 beta ∧
      (CFSG.LieType.CurtisTits.rankOne (e7Datum K).rootGroup j).map
        (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom ≤
          phiTwoComp S.D.g0 beta ∧
      ∀ (y : e7Data_valid.minGroup K) (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ)
        (hyBs : lambda y ∈ Bs),
        r ⟨lambda y, hyBs⟩ = ⟨lambda y, hyBs⟩ →
        iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K y) = rootDiagUnit .E7 a →
        rootChar a beta = 1 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let theta := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K
  let psi : adjointGroup .E7 K →* G := lambda.comp theta.symm.toMonoidHom
  have hlambda : Function.Injective lambda := by
    apply (MonoidHom.ker_eq_bot_iff lambda).mp
    apply le_antisymm _ bot_le
    simpa only [CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot] using hker
  have hpsi : Function.Injective psi := hlambda.comp theta.symm.injective
  let E : Subgroup (adjointGroup .E7 K) := Bs.comap psi
  have hEwhole : ∀ z : ModGL .E7 (AlgebraicClosure K),
      (∃ u : adjointGroup .E7 K, u ∈ E ∧ iota u = z) ↔
      ∃ b : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ,
        (∀ j, b j ^ p = 1) ∧ rootDiagUnit .E7 b = z := by
    intro z
    rw [← hwhole z]
    constructor
    · rintro ⟨u, hu, he⟩
      exact ⟨theta.symm u, hu, by simpa [theta] using he⟩
    · rintro ⟨u, hu, he⟩
      refine ⟨theta u, ?_, he⟩
      change lambda (theta.symm (theta u)) ∈ Bs
      simpa using hu
  obtain ⟨zeta, hzeta⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := AlgebraicClosure K) Nat.prime_two hp hp2
  obtain ⟨T, hTinj, hTrange, hT⟩ :=
    exists_torus_param_of_full_image E iota hinj hEwhole zeta hzeta.eq_orderOf.symm hzeta.pow_eq_one
  let chi : Multiplicative (Fin Tag.E7.rank → ZMod p) →* G := psi.comp T
  have hchiinj : Function.Injective chi := hpsi.comp hTinj
  have hchirange : chi.range = Bs := by
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      have ht : T t ∈ E := hTrange ▸ (show T t ∈ T.range from ⟨t, rfl⟩)
      exact ht
    · intro b hb
      obtain ⟨u, hu⟩ := hBs hb
      have hEu : theta u ∈ E := by
        change lambda (theta.symm (theta u)) ∈ Bs
        simpa [hu] using hb
      have hEuT : theta u ∈ T.range := by
        rw [hTrange]
        exact hEu
      obtain ⟨t, ht⟩ := hEuT
      refine ⟨t, ?_⟩
      change lambda (theta.symm (T t)) = b
      rw [ht, theta.symm_apply_apply, hu]
  let toBs := chi.codRestrict Bs (fun t => hchirange ▸ (show chi t ∈ chi.range from ⟨t, rfl⟩))
  have htoBs : Function.Bijective toBs := by
    constructor
    · intro a b he
      exact hchiinj (congrArg Subtype.val he)
    · intro b
      have hb : (b : G) ∈ chi.range := by
        rw [hchirange]
        exact b.property
      obtain ⟨t, ht⟩ := hb
      exact ⟨t, Subtype.ext ht⟩
  let e : Multiplicative (Fin Tag.E7.rank → ZMod p) ≃* Bs :=
    MulEquiv.ofBijective toBs htoBs
  let V : Set (Fin Tag.E7.rank → ZMod p) := {t | r (e (Multiplicative.ofAdd t)) = e (Multiplicative.ofAdd t)}
  let eV : V ≃ {b : Bs // r b = b} :=
    { toFun := fun t => ⟨e (Multiplicative.ofAdd t.val), t.property⟩
      invFun := fun b => ⟨(e.symm b.val).toAdd, by simpa [V] using b.property⟩
      left_inv := fun t => by simp
      right_inv := fun b => by simp }
  have hBscard : Nat.card Bs = p ^ 7 := by
    rw [← Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Tag.rank]
  have hV : V.ncard = p ^ (Tag.E7.rank - 1) := by
    rw [← Nat.card_coe_set_eq, Nat.card_congr eV]
    have hh := hr.2
    rw [hBscard] at hh
    change Nat.card {b : Bs // r b = b} = p ^ 6
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    simpa only [pow_succ] using hh
  let R := CFSG.LieType.CurtisTits.rankOne (e7Datum K).rootGroup j
  let P : Subgroup (adjointGroup .E7 K) := R.map theta.toMonoidHom
  obtain ⟨phi, hphiinj, hphirange, -, -⟩ :=
    CFSG.ClassicalInvolution.Phan.PhanE.exists_e7_primitive_simpleNode (k := K) j
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) := by
    letI := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (show 4 ≤ (Finset.univ : Finset K).card by
        simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hK)
    exact CFSG.LinearGroups.special_linear_dimension_two_perfect ⟨s, hs⟩
  haveI : Group.IsPerfect R := by
    rw [show R = phi.range from hphirange.symm]
    exact Group.IsPerfect.range (f := phi)
  have hperf : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.mp
    (Group.IsPerfect.map (H := R) (f := theta.toMonoidHom))
  have hbase : ∀ t : Fin Tag.E7.rank → ZMod p,
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (T (Multiplicative.ofAdd t) : ModGL .E7 K) =
        S.D.g0 * rootDiagUnit .E7 (TableBExc.E6Three.zetaVec zeta hzeta.pow_eq_one t) * S.D.g0⁻¹ := by
    intro t
    have hh := hT t
    rw [hformula] at hh
    rw [← hh]
    group
  have hcomm : ∀ z ∈ P, ∀ t ∈ V, z * T (Multiplicative.ofAdd t) = T (Multiplicative.ofAdd t) * z := by
    rintro _ ⟨u, hu, rfl⟩ t ht
    apply hpsi
    rw [map_mul, map_mul]
    have hfixed : chi (Multiplicative.ofAdd t) ∈ ggHyperplane Bs r := by
      apply Subgroup.mem_map.mpr
      refine ⟨e (Multiplicative.ofAdd t), ?_, rfl⟩
      exact ht
    have hcent : lambda u ∈ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
      apply CFSG.Quasithin.perfectCore_le _
      change lambda u ∈ ggRankOnePerf Bs r
      rw [← hroot]
      exact ⟨u, hu, rfl⟩
    have hh := Subgroup.mem_centralizer_iff.mp hcent _ hfixed
    simpa [psi, chi] using hh.symm
  have hPne : P ≠ ⊥ := by
    let A : Matrix.SpecialLinearGroup (Fin 2) K := CFSG.LieType.Steinberg.sl2Upper 1
    have hAne : A ≠ 1 := by
      intro he
      have hh := congrArg (fun B : Matrix.SpecialLinearGroup (Fin 2) K =>
        (B : Matrix (Fin 2) (Fin 2) K) 0 1) he
      simpa [A, CFSG.LieType.Steinberg.sl2Upper] using hh
    intro he
    have hphiA : phi A ∈ R := by
      rw [show R = phi.range from hphirange.symm]
      exact ⟨A, rfl⟩
    have hp : theta (phi A) ∈ P := ⟨phi A, hphiA, rfl⟩
    rw [he] at hp
    have htheta0 : theta (phi A) = 1 := Subgroup.mem_bot.mp hp
    have hphi0 : phi A = 1 := theta.injective (htheta0.trans theta.map_one.symm)
    exact hAne (hphiinj (hphi0.trans phi.map_one.symm))
  obtain ⟨beta, hbeta, hle, hvan⟩ := exists_isRoot_perfect_le_phiTwoComp_with_vanishing
    (Or.inr (Or.inl rfl)) hp2
    S.D.g0_mem hzeta.eq_orderOf.symm hzeta.pow_eq_one hbase hV hperf hcomm
  refine ⟨beta, hbeta, hle, ?_⟩
  intro y a hyBs hfix hya
  have hyT : theta y ∈ T.range := by
    rw [hTrange]
    change lambda (theta.symm (theta y)) ∈ Bs
    simpa using hyBs
  obtain ⟨t, ht⟩ := hyT
  have heT : e t = ⟨lambda y, hyBs⟩ := by
    apply Subtype.ext
    change psi (T t) = lambda y
    rw [ht]
    change lambda (theta.symm (theta y)) = lambda y
    simp
  have htV : t.toAdd ∈ V := by
    change r (e (Multiplicative.ofAdd t.toAdd)) = e (Multiplicative.ofAdd t.toAdd)
    change r (e t) = e t
    rw [heT]
    exact hfix
  have hvec : TableBExc.E6Three.zetaVec zeta hzeta.pow_eq_one t.toAdd = a := by
    apply rootDiagUnit_injective
    rw [← hT t.toAdd]
    change iota (T t) = rootDiagUnit .E7 a
    rw [ht]
    exact hya
  rw [← hvec, NoOffE8Five.rootChar_zetaVec hzeta.pow_eq_one, hvan hPne t.toAdd htV]
  simp

theorem exists_e7_parent_eq_phiTwoComp_of_prime_with_fixed_character
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (lambda : e7Data_valid.minGroup K →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (hBs : Bs ≤ lambda.range)
    (S : LangSetup .E7 (AlgebraicClosure K) 5)
    (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K))
    (hinj : Function.Injective iota)
    (hformula : ∀ u, iota u = S.D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL .E7 K) * S.D.g0)
    (hwhole : ∀ z : ModGL .E7 (AlgebraicClosure K),
      (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧
        iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K u) = z) ↔
      ∃ b : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ,
        (∀ j, b j ^ p = 1) ∧ rootDiagUnit .E7 b = z)
    {r : MulAut Bs} (hr : GGIsReflection p r) (j : Fin Tag.E7.rank)
    (hroot : (rankOne (e7Datum K).rootGroup j).map lambda = ggRankOnePerf Bs r)
    (sigma : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hsigma : ∀ c, sigma c = c ^ Nat.card K)
    (hPhi : S.D.Φ = frobGL sigma)
    (hRho : ∀ alpha, IsRoot .E7 alpha → S.ρ alpha = -alpha) :
    ∃ beta : Fin Tag.E7.rank → ℤ, IsRoot .E7 beta ∧
      (rankOne (e7Datum K).rootGroup j).map
        (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom =
          phiTwoComp S.D.g0 beta ∧
      ∀ (y : e7Data_valid.minGroup K) (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ)
        (hyBs : lambda y ∈ Bs),
        r ⟨lambda y, hyBs⟩ = ⟨lambda y, hyBs⟩ →
        iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K y) = rootDiagUnit .E7 a →
        rootChar a beta = 1 := by
  obtain ⟨beta, hbeta, hle, hchar⟩ := exists_e7_parent_le_phiTwoComp_of_prime_with_fixed_character hp hp2
    hK lambda hker hBs S iota hinj hformula hwhole hr j hroot
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hwbeta : w • beta = -beta :=
    (S.frob.weyl_smul_eq sigma hPhi w hn hbeta).trans (hRho beta hbeta)
  have hlang : Units.map (entrywiseHom sigma.toRingHom) S.D.g0 =
      S.D.g0 * canonicalRep (coxeterSystem .E7) (AlgebraicClosure K) w := by
    have h := S.D.lang
    rw [hPhi, hn] at h
    exact h
  have hrat : ∀ X : Subgroup (ModGL .E7 (AlgebraicClosure K)), Finite X →
      X ≤ adjointGroup .E7 (AlgebraicClosure K) →
      (∀ x ∈ X, Units.map (entrywiseHom sigma.toRingHom) x = x) →
      X ≤ (adjointGroup .E7 K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
    intro X hX hXC hXF
    letI := hX
    exact finite_fixed_le_map_adjointGroup_E7 sigma.toRingHom hsigma X hXC hXF
  obtain ⟨e⟩ := nonempty_mulEquiv_phiTwoComp hsigma hrat S.D.g0_mem hlang hbeta hwbeta
  let R := rankOne (e7Datum K).rootGroup j
  let theta := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K
  obtain ⟨phi, hphiinj, hphirange, -, -⟩ :=
    CFSG.ClassicalInvolution.Phan.PhanE.exists_e7_primitive_simpleNode (k := K) j
  have hRcard : Nat.card R = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    change Nat.card (rankOne (e7Datum K).rootGroup j) = _
    rw [← hphirange]
    exact (Nat.card_congr (MonoidHom.ofInjective hphiinj).toEquiv).symm
  have hPcard : Nat.card (R.map theta.toMonoidHom) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
    (Nat.card_congr (R.equivMapOfInjective theta.toMonoidHom theta.injective).toEquiv).symm.trans hRcard
  exact ⟨beta, hbeta, Subgroup.eq_of_le_of_card_ge hle
    ((Nat.card_congr e.toEquiv).trans hPcard.symm).le, hchar⟩

theorem exists_e7_parent_root_in_e6_component_of_prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (lambda : e7Data_valid.minGroup K →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (hBs : Bs ≤ lambda.range)
    (S : LangSetup .E7 (AlgebraicClosure K) 5)
    (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K))
    (hinj : Function.Injective iota) (hrange : iota.range = S.Γ)
    (hformula : ∀ u, iota u = S.D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL .E7 K) * S.D.g0)
    (hwhole : ∀ z : ModGL .E7 (AlgebraicClosure K),
      (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧
        iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K u) = z) ↔
      ∃ b : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ,
        (∀ j, b j ^ p = 1) ∧ rootDiagUnit .E7 b = z)
    {r : MulAut Bs} (hr : GGIsReflection p r) (hrL : r ∈ ggAutomizer L Bs)
    (j : Fin Tag.E7.rank)
    (hroot : (rankOne (e7Datum K).rootGroup j).map lambda = ggRankOnePerf Bs r)
    (sigma : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hsigma : ∀ c, sigma c = c ^ Nat.card K)
    (hPhi : S.D.Φ = frobGL sigma)
    (hRho : ∀ alpha, IsRoot .E7 alpha → S.ρ alpha = -alpha)
    (y : e7Data_valid.minGroup K) (M : Subgroup (e7Data_valid.minGroup K))
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({y} : Set _)))
    (hML : M.map lambda = L) (hRM : rankOne (e7Datum K).rootGroup j ≤ M)
    (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ) (hyBs : lambda y ∈ Bs)
    (hya : iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K y) = rootDiagUnit .E7 a)
    (c : KernelComponent (rootCharHom a)) (w : WeylGroup .E7)
    (hMC : M.map (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom) =
      rationalComponent S.ρ S.Γ (rootCharHom a) c)
    (hPsi : componentRoots (rootCharHom a) c =
      (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7)) :
    ∃ beta : Fin Tag.E7.rank → ℤ, IsRoot .E7 beta ∧
      beta ∈ componentRoots (rootCharHom a) c ∧
      -beta ∈ componentRoots (rootCharHom a) c ∧
      ((rankOne (e7Datum K).rootGroup j).map
        (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom).map iota =
        rootSpan .E7 (AlgebraicClosure K) {beta, -beta} ⊓ S.Γ ∧
      ((rankOne (e7Datum K).rootGroup j).map
        (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom).map iota ≤
        rationalComponent S.ρ S.Γ (rootCharHom a) c := by
  have hLC : L ≤ Subgroup.centralizer ({lambda y} : Set G) := by
    intro n hn
    rw [← hML] at hn
    obtain ⟨u, hu, rfl⟩ := hn
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    have hh := Subgroup.mem_centralizer_iff.mp (hM.1 hu) y (by simp)
    simpa only [map_mul] using congrArg lambda hh
  have hfix : r ⟨lambda y, hyBs⟩ = ⟨lambda y, hyBs⟩ := by
    apply (forall_ggAutomizer_apply_eq_iff (X := L) ⟨lambda y, hyBs⟩).mpr _ r hrL
    intro n hn _
    have hh := Subgroup.mem_centralizer_iff.mp (hLC hn) (lambda y) (by simp)
    rw [← hh]
    group
  obtain ⟨beta, hbeta, heq, hchar⟩ := exists_e7_parent_eq_phiTwoComp_of_prime_with_fixed_character hp hp2
    hK lambda hker hBs S iota hinj hformula hwhole hr j hroot sigma hsigma hPhi hRho
  have hbetaChar : rootChar a beta = 1 := hchar y a hyBs hfix hya
  have hkernel : beta ∈ kernelRoots (rootCharHom a) := ⟨hbeta, hbetaChar⟩
  have hnegkernel : -beta ∈ kernelRoots (rootCharHom a) := by
    refine ⟨IsRoot.neg hbeta, ?_⟩
    change rootChar a (-beta) = 1
    have hh := (rootCharHom a).map_inv (Multiplicative.ofAdd beta)
    change rootChar a (-beta) = (rootChar a beta)⁻¹ at hh
    rw [hh, hbetaChar, inv_one]
  have hkerEq := kernelRoots_eq_componentRoots_of_E7_e6 (rootCharHom a) c w hPsi
  refine ⟨beta, hbeta, hkerEq ▸ hkernel, hkerEq ▸ hnegkernel, ?_, ?_⟩
  · rw [heq]
    have hcomap : phiTwoComp S.D.g0 beta =
        (rootSpan .E7 (AlgebraicClosure K) {beta, -beta}).comap iota := by
      ext z
      rw [mem_phiTwoComp_iff, Subgroup.mem_comap, hformula]
    rw [hcomap, Subgroup.map_comap_eq, hrange, inf_comm]
  · rw [Subgroup.map_map, ← hMC]
    exact Subgroup.map_mono hRM

theorem exists_e7_parent_fixed_root_in_e6_component_of_prime
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (lambda : e7Data_valid.minGroup K →* G)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (hBs : Bs ≤ lambda.range)
    (S : LangSetup .E7 (AlgebraicClosure K) 5)
    (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K))
    (hinj : Function.Injective iota) (hrange : iota.range = S.Γ)
    (hformula : ∀ u, iota u = S.D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL .E7 K) * S.D.g0)
    (hwhole : ∀ z : ModGL .E7 (AlgebraicClosure K),
      (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧
        iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K u) = z) ↔
      ∃ b : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ,
        (∀ j, b j ^ p = 1) ∧ rootDiagUnit .E7 b = z)
    {r : MulAut Bs} (hr : GGIsReflection p r) (hrL : r ∈ ggAutomizer L Bs)
    (j : Fin Tag.E7.rank)
    (hroot : (rankOne (e7Datum K).rootGroup j).map lambda = ggRankOnePerf Bs r)
    (sigma : AlgebraicClosure K ≃+* AlgebraicClosure K)
    (hsigma : ∀ c, sigma c = c ^ Nat.card K)
    (hPhi : S.D.Φ = frobGL sigma)
    (hRho : ∀ alpha, IsRoot .E7 alpha → S.ρ alpha = -alpha)
    (y : e7Data_valid.minGroup K) (M : Subgroup (e7Data_valid.minGroup K))
    (hM : CFSG.Assembly.IsComponentOf M (Subgroup.centralizer ({y} : Set _)))
    (hML : M.map lambda = L) (hRM : rankOne (e7Datum K).rootGroup j ≤ M)
    (a : Fin Tag.E7.rank → (AlgebraicClosure K)ˣ) (hyBs : lambda y ∈ Bs)
    (hya : iota (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K y) = rootDiagUnit .E7 a)
    (c : KernelComponent (rootCharHom a)) (w : WeylGroup .E7)
    (hMC : M.map (iota.comp (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom) =
      rationalComponent S.ρ S.Γ (rootCharHom a) c)
    (hPsi : componentRoots (rootCharHom a) c =
      (fun alpha => w • alpha) '' parabolicRoots .E7 (e6Nodes .E7)) :
    ∃ beta : Fin Tag.E7.rank → ℤ, IsRoot .E7 beta ∧
      beta ∈ componentRoots (rootCharHom a) c ∧
      -beta ∈ componentRoots (rootCharHom a) c ∧
      ((rankOne (e7Datum K).rootGroup j).map
        (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom).map iota =
        rootSpan .E7 (AlgebraicClosure K) {beta, -beta} ⊓
          S.D.step.eqLocus (MonoidHom.id _) ∧
      ((rankOne (e7Datum K).rootGroup j).map
        (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom).map iota ≤
        rationalComponent S.ρ S.Γ (rootCharHom a) c := by
  obtain ⟨beta, hbeta, hbetaPsi, hnegPsi, heqGamma, hQcomp⟩ :=
    exists_e7_parent_root_in_e6_component_of_prime hp hp2 hK lambda hker hBs S iota hinj hrange
      hformula hwhole hr hrL j hroot sigma hsigma hPhi hRho y M hM hML hRM
      a hyBs hya c w hMC hPsi
  have hkerEq := kernelRoots_eq_componentRoots_of_E7_e6 (rootCharHom a) c w hPsi
  have hneg : ∀ alpha ∈ componentRoots (rootCharHom a) c,
      -alpha ∈ componentRoots (rootCharHom a) c := by
    intro alpha halpha
    rw [← hkerEq] at halpha ⊢
    refine ⟨IsRoot.neg halpha.1, ?_⟩
    have hh := (rootCharHom a).map_inv (Multiplicative.ofAdd alpha)
    change (rootCharHom a) (Multiplicative.ofAdd (-alpha)) =
      ((rootCharHom a) (Multiplicative.ofAdd alpha))⁻¹ at hh
    rw [hh, halpha.2, inv_one]
  have hstable : ∀ alpha ∈ componentRoots (rootCharHom a) c,
      S.ρ alpha ∈ componentRoots (rootCharHom a) c := by
    intro alpha halpha
    have hk : alpha ∈ kernelRoots (rootCharHom a) := by rwa [hkerEq]
    rw [hRho alpha hk.1]
    exact hneg alpha halpha
  obtain ⟨nW, hn⟩ := S.D.n_weyl
  have hw : ∀ alpha ∈ componentRoots (rootCharHom a) c,
      nW • alpha ∈ componentRoots (rootCharHom a) c := by
    intro alpha halpha
    have hk : alpha ∈ kernelRoots (rootCharHom a) := by rwa [hkerEq]
    rw [S.frob.weyl_smul_eq sigma hPhi nW hn hk.1]
    exact hstable alpha halpha
  obtain ⟨-, hqs⟩ := rootSpan_inf_model_quasisimple
    (τ := .E7) (by intro t; cases t <;> decide) S hn w (by
      intro alpha halpha
      rw [← hPsi] at halpha ⊢
      exact hw alpha halpha)
  have hqsActual : CFSG.IsQuasisimple
      ↥(rootSpan .E7 (AlgebraicClosure K) (componentRoots (rootCharHom a) c) ⊓ S.D.model) := by
    rw [hPsi]
    exact hqs
  have hcompEq := rationalComponent_eq_rootSpan_inf_model_of_layer S c hstable hqsActual
  have hpairH : rootSpan .E7 (AlgebraicClosure K) {beta, -beta} ≤
      rootSpan .E7 (AlgebraicClosure K) (componentRoots (rootCharHom a) c) :=
    rootSpan_mono (by
      intro alpha halpha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at halpha
      rcases halpha with rfl | rfl
      · exact hbetaPsi
      · exact hnegPsi)
  have hpairAdj : rootSpan .E7 (AlgebraicClosure K) {beta, -beta} ≤
      adjointGroup .E7 (AlgebraicClosure K) := by
    unfold rootSpan
    exact iSup_le fun alpha => iSup_le fun _ => rootSubgroup_le_adjointGroup alpha
  have hGammaModel : S.Γ ≤ S.D.model := by
    apply Subgroup.commutator_le.mpr
    intro u hu v hv
    rw [commutatorElement_def]
    exact S.D.model.mul_mem (S.D.model.mul_mem (S.D.model.mul_mem hu hv)
      (S.D.model.inv_mem hu)) (S.D.model.inv_mem hv)
  have hcompGamma : rationalComponent S.ρ S.Γ (rootCharHom a) c ≤ S.Γ := by
    apply Subgroup.commutator_le.mpr
    intro u hu v hv
    rw [commutatorElement_def]
    exact S.Γ.mul_mem (S.Γ.mul_mem (S.Γ.mul_mem hu.2 hv.2)
      (S.Γ.inv_mem hu.2)) (S.Γ.inv_mem hv.2)
  refine ⟨beta, hbeta, hbetaPsi, hnegPsi, ?_, hQcomp⟩
  rw [heqGamma]
  apply le_antisymm
  · intro u hu
    exact ⟨hu.1, (hGammaModel hu.2).2⟩
  · intro u hu
    have huModel : u ∈ S.D.model := ⟨hpairAdj hu.1, hu.2⟩
    have huComp : u ∈ rationalComponent S.ρ S.Γ (rootCharHom a) c := by
      rw [hcompEq]
      exact ⟨hpairH hu.1, huModel⟩
    exact ⟨hu.1, hcompGamma huComp⟩

end CFSG.StandardType
