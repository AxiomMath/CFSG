module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnTwDFixed
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnSpecial

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section SelfDualThree

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.isQuasisimple_specialBlock_selfDual_of_three_le
    (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : Odd p) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 3 ≤ primaryMultiplicity x.toLinearMap h)
    (hK4 : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  have hdvd := hx.dvd_card_pow_add_one hp hh hne1 hroot
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm ?_
  have h3 : 3 ≤ finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) := hm
  have hdpos : 1 ≤ d := by
    have := hirr.natDegree_pos
    omega
  have hnq : (finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h), ℓ ^ (f * d)) ≠ (3, 2) :=
    fun e => by
      have h2 := congrArg Prod.snd e
      simp only at h2
      have hle : ℓ ^ f ≤ ℓ ^ (f * d) :=
        Nat.pow_le_pow_right hU.prime.pos (Nat.le_mul_of_pos_right f hdpos)
      have h4' : 4 ≤ ℓ ^ (f * d) := calc 4 ≤ Nat.card K := hK4
        _ = ℓ ^ f := hq
        _ ≤ ℓ ^ (f * d) := hle
      omega
  exact isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl h3 hnq

end SelfDualThree

end CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd SmallOrth
  CFSG.RankThree.PartOne.K159 CFSG.GroupTheory.WeirSylow

section SpecialFour

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

theorem innerConcl_of_special_four (S : FourData Q p A) (h4 : 4 ≤ Nat.card K)
    {D : Subgroup (V ≃ₗ[K] V)} {a : V ≃ₗ[K] V} (hE : EndData p (orthDerived Q) A D a)
    {h : K[X]} (hh : h ∈ primaryFactors a.toLinearMap) (hne : h ≠ X - 1)
    (hX : D ≤ ⁅supportedBlock Q a h, supportedBlock Q a h⁆) : InnerConcl A D := by
  classical
  haveI : Fact p.Prime := ⟨S.prime⟩
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd S.prime S.odd
  have hIso : IsoGroup (QuadraticMap.polarBilin Q) p A :=
    isoGroup_of_le S.regular S.le_omega S.elem
  have haA : a ∈ A := hE.a_mem
  have hap : a ^ p = 1 := S.elem.2 a haA
  have hx : OddOrderIsometry Q p a :=
    ⟨orthDerived_le_orthogonalGroup (S.le_omega haA), hap, hpK, fun v hv =>
      S.regular.1 v fun w => by rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hself : h = reciprocalPolynomial h :=
    CFSG.LieType.SeitzGeneration.OrthBlk.selfDual_of_dvd hx hh (d := 1)
      (by rw [pow_one]; exact S.dvd)
  have hdeg : h.natDegree = 2 :=
    SpNS.natDegree_eq_two S.prime S.odd hpK
      (CoordSU.dvd_cyclotomic_of_dvd S.prime (irreducible_of_mem_primaryFactors hh)
        (monic_of_mem_primaryFactors hh) (by rw [C_1]; exact hx.dvd_X_pow_sub_one hh)
        (by rw [C_1]; exact hne)) S.dvd
  set B := QuadraticMap.polarBilin Q with hB
  have hUeq : orbitSpace a.toLinearMap h = primaryComponent a.toLinearMap h := by
    rw [orbitSpace, ← hself, sup_idem]
  have hc := hx.isCompl_orbit_others hh
  have horth : ∀ u ∈ orbitSpace a.toLinearMap h, ∀ r ∈ othersSpace a.toLinearMap h, B u r = 0 :=
    fun u hu r hr => by
      rw [hB, QuadraticMap.polarBilin_apply_apply]
      exact hx.polar_orbit_others hh hu hr
  have hcomm : ∀ g ∈ A, g ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (TableB.IsElemAbelian.comm S.elem hg haA)
  have hUinv : ∀ g ∈ A, ∀ s ∈ orbitSpace a.toLinearMap h, g s ∈ orbitSpace a.toLinearMap h :=
    fun g hg s hs => mem_orbitSpace_of_apply (hcomm g hg) hs
  have ha1 : a ≠ 1 := hE.a_ne
  have hord : orderOf a = p := orderOf_eq_prime hap ha1
  have hker1 : (resHom A (orbitSpace a.toLinearMap h) hUinv).ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    have hgU : ∀ u ∈ orbitSpace a.toLinearMap h, (g : V ≃ₗ[K] V) u = u := fun u hu =>
      congrArg Subtype.val (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hg) ⟨u, hu⟩)
    have hgz : (g : V ≃ₗ[K] V) ∈ Subgroup.zpowers a := by
      refine hE.A_cent g g.2 fun d hd => ?_
      exact commute_of_fix_orbit hx hh (hcomm g g.2) hgU (commutator_self_le _ (hX hd))
    by_contra hg1
    have hg1' : (g : V ≃ₗ[K] V) ≠ 1 := fun e => hg1 (Subtype.ext e)
    have hgp : (g : V ≃ₗ[K] V) ^ p = 1 := S.elem.2 _ g.2
    have hog : orderOf (g : V ≃ₗ[K] V) = p := orderOf_eq_prime hgp hg1'
    have hzeq : Subgroup.zpowers (g : V ≃ₗ[K] V) = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hog])
    have hfix : Subgroup.zpowers (g : V ≃ₗ[K] V) ≤
        fixingSubgroup (V ≃ₗ[K] V) (orbitSpace a.toLinearMap h : Set V) :=
      Subgroup.zpowers_le.mpr ((mem_fixingSubgroup_iff _).mpr fun u hu => hgU u hu)
    have haU : ∀ u ∈ orbitSpace a.toLinearMap h, a u = u := fun u hu =>
      (mem_fixingSubgroup_iff _).mp (hfix (hzeq ▸ Subgroup.mem_zpowers a)) u hu
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have hvU : v ∈ orbitSpace a.toLinearMap h := hUeq ▸ hv
    have h0 := mem_primaryComponent.mp hv
    rw [aeval_apply_of_fixed h (haU v hvU)] at h0
    exact hv0 ((smul_eq_zero.mp h0).resolve_left (eval_one_ne_zero hh hne))
  have hAU : Nat.card A = Nat.card (resHom A (orbitSpace a.toLinearMap h) hUinv).range := by
    have := Subgroup.card_ker_mul_card_range (resHom A (orbitSpace a.toLinearMap h) hUinv)
    rw [hker1, Subgroup.card_bot, one_mul] at this
    exact this.symm
  have hVh : finrank K (orbitSpace a.toLinearMap h) = 2 * primaryMultiplicity a.toLinearMap h := by
    have h1 := finrank_primaryComponent (x := a.toLinearMap) (a := h)
    rw [hdeg] at h1
    have h2 : primaryMultiplicity a.toLinearMap h =
        finrank (AdjoinRoot h) (primaryComponent a.toLinearMap h) := rfl
    rw [hUeq, h1, h2]
  have hUdim : 3 ≤ finrank K (orbitSpace a.toLinearMap h) / 2 := by
    have h1 := card_res_le S.prime hpK hIso hc hUinv horth
    have h2 : p ^ 3 ≤ p ^ (finrank K (orbitSpace a.toLinearMap h) / 2) :=
      calc p ^ 3 ≤ Nat.card A := S.card_ge
        _ = _ := hAU
        _ ≤ _ := h1
    exact (Nat.pow_le_pow_iff_right S.prime.one_lt).mp h2
  have hm3 : 3 ≤ primaryMultiplicity a.toLinearMap h := by omega
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have h8 := S.finrank_eq
  have hgR : ∀ g : A, ∀ r ∈ othersSpace a.toLinearMap h, (g : V ≃ₗ[K] V) r = r := by
    by_cases hbig : 4 ≤ primaryMultiplicity a.toLinearMap h
    · intro g r hr
      have hR0 : finrank K (othersSpace a.toLinearMap h) = 0 := by omega
      rw [Submodule.finrank_eq_zero.mp hR0, Submodule.mem_bot] at hr
      rw [hr, map_zero]
    · have hR2 : finrank K (othersSpace a.toLinearMap h) = 2 := by omega
      have hCle : fixedSpace a ≤ othersSpace a.toLinearMap h := by
        intro v hv
        obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_of_isCompl hc v
        have hcen : a ∈ Subgroup.centralizer ({a} : Set (V ≃ₗ[K] V)) :=
          Subgroup.mem_centralizer_singleton_iff.mpr rfl
        have hau : a u ∈ orbitSpace a.toLinearMap h := mem_orbitSpace_of_apply hcen hu
        have har : a r ∈ othersSpace a.toLinearMap h := mem_othersSpace_of_apply hcen hr
        have hfixv : a u + a r = u + r := by
          have := mem_fixedSpace.1 hv
          rwa [map_add] at this
        have h1 : a u = u := by
          have hmem1 : a u - u ∈ orbitSpace a.toLinearMap h := Submodule.sub_mem _ hau hu
          have hmem2 : a u - u ∈ othersSpace a.toLinearMap h := by
            have e : a u - u = r - a r := by
              rw [sub_eq_sub_iff_add_eq_add, add_comm r u]
              exact hfixv
            rw [e]
            exact Submodule.sub_mem _ hr har
          exact sub_eq_zero.mp ((Submodule.disjoint_def.1 hc.disjoint) _ hmem1 hmem2)
        have hu0 : u = 0 := by
          have h0 := mem_primaryComponent.mp (hUeq ▸ hu)
          rw [aeval_apply_of_fixed h h1] at h0
          exact (smul_eq_zero.mp h0).resolve_left (eval_one_ne_zero hh hne)
        rw [hu0, zero_add]
        exact hr
      have hft := fixed_type hx S.prime S.odd S.dvd S.finrank_eq S.minus ha1
      have hCdim : finrank K (fixedSpace a) = 2 := by
        have := Submodule.finrank_mono hCle
        omega
      have hCeq : fixedSpace a = othersSpace a.toLinearMap h :=
        Submodule.eq_of_le_of_finrank_eq hCle (by omega)
      have hCplus : IsPlusType (Q.comp (fixedSpace a).subtype) :=
        CFSG.RankThree.PartOne.KFR4.Frm.isPlusType_fixed_of_finrank_two hx S.prime S.odd S.dvd
          S.finrank_eq S.minus hCdim
      have hCinv : ∀ g ∈ A, ∀ s ∈ fixedSpace a, g s ∈ fixedSpace a := fun g hg s hs =>
        mem_fixedSpace_of_apply (hcomm g hg) hs
      intro g r hr
      have hrC : r ∈ fixedSpace a := hCeq ▸ hr
      have hτO : resHom A (fixedSpace a) hCinv g ∈
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace a).subtype) :=
        TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun s => by
          change Q ((g : V ≃ₗ[K] V) (s : V)) = Q (s : V)
          exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
            (orthDerived_le_orthogonalGroup (S.le_omega g.2)) s
      have hτp : (resHom A (fixedSpace a) hCinv g) ^ p = 1 := by
        rw [← map_pow, show g ^ p = 1 from Subtype.ext (hIso.pow g g.2), map_one]
      have h1 := eq_one_of_pow_of_plus_plane (QW := Q.comp (fixedSpace a).subtype)
        hx.polarBilin_fixed_nondegenerate hCdim hCplus S.prime S.odd S.dvd _ hτO hτp
      have h2 := congrArg
        (fun f : fixedSpace a ≃ₗ[K] fixedSpace a => ((f ⟨r, hrC⟩ : fixedSpace a) : V)) h1
      have h3 : ((resHom A (fixedSpace a) hCinv g ⟨r, hrC⟩ : fixedSpace a) : V) = r := by
        simpa using h2
      exact (resHom_apply (fixedSpace a) hCinv g ⟨r, hrC⟩).symm.trans h3
  have hgM : ∀ g : A, (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q a := fun g =>
    mem_isometryCentralizer.mpr
      ⟨fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup (S.le_omega g.2)) v, fun v =>
        congrArg (fun f : V ≃ₗ[K] V => f v)
          (Subgroup.mem_centralizer_singleton_iff.mp (hcomm g g.2))⟩
  have hAB : A ≤ supportedBlock Q a h := fun g hg =>
    mem_supportedBlock.mpr ⟨hgM ⟨g, hg⟩, fun r hr => hgR ⟨g, hg⟩ r hr⟩
  have hFq := hx.isQuasisimple_specialBlock_selfDual_of_three_le S.prime
    (S.prime.odd_of_ne_two S.odd) hh hne hself hm3 h4
  set F := specialBlock Q a h with hF
  have hFM : F ≤ isometryCentralizer Q a := specialBlock_le_isometryCentralizer h
  have hFΩ : F ≤ orthDerived Q := specialBlock_le_orthDerived_of_perfect hFq.1
    (hFM.trans fun _ hg => (Subgroup.mem_inf.mp hg).1)
  have hDF : D ≤ F := fun d hd => commutator_supportedBlock_le_specialBlock h (hX hd)
  have hFn : ∀ b ∈ F, ∀ d ∈ D, b * d * b⁻¹ ∈ D := fun b hb d hd =>
    hE.D_norm b (hFΩ hb) (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (hFM hb)).2) d hd
  have hDeq : D = F := StdSubRestThree.eq_of_le_of_quasisimple hDF hFn hFq hE.D_qs
  set φ : A →* AdjoinRoot h := (blockDet Q a h).comp (Subgroup.inclusion hAB) with hφ
  set φ' : A →* (AdjoinRoot h)ˣ := φ.toHomUnits with hφ'
  have hrange : Nat.card φ'.range ≤ p := by
    have hle : φ'.range ≤ rootsOfUnity p (AdjoinRoot h) := by
      rintro _ ⟨g, rfl⟩
      rw [mem_rootsOfUnity, ← map_pow]
      have : g ^ p = 1 := Subtype.ext (S.elem.2 _ g.2)
      rw [this, map_one]
    exact (Subgroup.card_le_of_le hle).trans (card_rootsOfUnity (AdjoinRoot h) p)
  have hkerc := Subgroup.card_ker_mul_card_range φ'
  have hEA : φ'.ker.map A.subtype ≤ A := Subgroup.map_subtype_le _
  have hEF : φ'.ker.map A.subtype ≤ F := by
    rintro _ ⟨g, hg, rfl⟩
    refine mem_specialBlock.mpr ⟨hAB g.2, ?_⟩
    have h1 : φ' g = 1 := hg
    exact congrArg Units.val h1
  have hEcard : p ^ 2 ≤ Nat.card (φ'.ker.map A.subtype) := by
    have hmapcard : Nat.card (φ'.ker.map A.subtype) = Nat.card φ'.ker :=
      (Nat.card_congr (φ'.ker.equivMapOfInjective A.subtype A.subtype_injective).toEquiv).symm
    rw [hmapcard]
    have h1 : p ^ 3 ≤ Nat.card φ'.ker * p := by
      calc p ^ 3 ≤ Nat.card A := S.card_ge
        _ = _ := hkerc.symm
        _ ≤ Nat.card φ'.ker * p := Nat.mul_le_mul_left _ hrange
    rw [pow_succ] at h1
    exact Nat.le_of_mul_le_mul_right h1 S.prime.pos
  have hp2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right S.prime.one_lt (by norm_num)
  rw [pow_one] at hp2
  exact innerConcl_of_card S.prime hE hEA (hDeq ▸ hEF) (lt_of_lt_of_le hp2 hEcard)

end SpecialFour

end SmallOrthUn

end CFSG.StandardType

end
