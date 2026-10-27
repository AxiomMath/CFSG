module

public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator
public import CFSG.RankThree.GroupTheory.SteinbergCELocalCoreImage
public import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaMixedBalance
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977StandardCyclic
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalAlmostSimple

public section

namespace CFSG.RankThree.GroupTheory.SteinbergBM

open Subgroup CFSG CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

variable {G : Type*} [Group G]

theorem isSolvable_inf_centralizer_of_sup {L R : Subgroup G} (hRL : R ≤ normalizer (L : Set G))
    (hR : Group.IsSolvable R) :
    Group.IsSolvable ((L ⊔ R) ⊓ centralizer (L : Set G) : Subgroup G) := by
  have hLN : L ≤ L ⊔ R := le_sup_left
  have hRN : R ≤ L ⊔ R := le_sup_right
  have hNL : L ⊔ R ≤ normalizer (L : Set G) := sup_le le_normalizer hRL
  have : (L.subgroupOf (L ⊔ R)).Normal := (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  have hq : Group.IsSolvable ((L ⊔ R : Subgroup G) ⧸ L.subgroupOf (L ⊔ R)) := by
    refine Group.isSolvable_of_surjective
      (f := (QuotientGroup.mk' (L.subgroupOf (L ⊔ R))).comp (inclusion hRN)) fun q => ?_
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hn : (n : G) ∈ (L : Set G) * (R : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left L R hRL]
      exact n.2
    obtain ⟨l, hl, r, hr, hlr⟩ := hn
    refine ⟨⟨r, hr⟩, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      mem_subgroupOf]
    have e : (((inclusion hRN ⟨r, hr⟩)⁻¹ * n : (L ⊔ R : Subgroup G)) : G) = r⁻¹ * l * r⁻¹⁻¹ := by
      simp only [coe_mul, coe_inv, coe_inclusion, ← hlr]
      group
    rw [e]
    exact (mem_normalizer_iff.mp (hRL (inv_mem hr)) l).mp hl
  set g := (QuotientGroup.mk' (L.subgroupOf (L ⊔ R))).comp
    (inclusion (inf_le_left : (L ⊔ R) ⊓ centralizer (L : Set G) ≤ L ⊔ R))
  have hk : Group.IsSolvable g.ker := Group.isSolvable_of_comm fun x y => by
    have hx : (((x : _) : _) : G) ∈ L := by
      have h := MonoidHom.mem_ker.mp x.2
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
      exact h
    exact Subtype.ext (Subtype.ext (mem_centralizer_iff.mp y.1.2.2 _ hx))
  exact Group.isSolvable_of_ker_le_range g.ker.subtype g (by rw [range_subtype])

theorem map_inSubgroup_aschbacherSolvableCore_centralizer_le {H K : Type*} [Group H] [Group K]
    [Finite H] [Finite K] {p : ℕ} (hp : p.Prime) (φ : H →* K) (hφ : Function.Surjective φ)
    (hN : Group.IsSolvable φ.ker) {a : H} (ha : IsPGroup p (zpowers a)) :
    (inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set H))).map φ ≤
      inSubgroup (aschbacherSolvableCore p) (centralizer ({φ a} : Set K)) := by
  have h := local_solvable_core_image_under_solvable_quotient hp φ hφ hN ha
  rwa [MonoidHom.map_zpowers, ← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers,
    ← SteinbergBY.centralizer_singleton_eq_centralizer_zpowers] at h

theorem subgroupOf_inSubgroup_aschbacherSolvableCore_le [Finite G] {p : ℕ} (hp : p.Prime)
    (J : Subgroup G) {a : G} (ha : a ∈ J) :
    (inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set G))).subgroupOf J ≤
      inSubgroup (aschbacherSolvableCore p) (centralizer ({(⟨a, ha⟩ : J)} : Set J)) := by
  intro x hx
  rw [← mem_map_iff_mem J.subtype_injective, inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
    RankThreeEvenClassification.Helpers.thetaCoreOf_element_centralizer_subtype_map p hp J a ha]
  refine RankThreeEvenClassification.Helpers.theta_element_centralizer_intersection_le p hp J a
    ⟨x.2, ?_⟩
  rw [← inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
  exact hx

theorem faithful_component_local_core_almost_simple_image [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) = ⊥) :
    let S := inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G))
    let J := L ⊔ S ⊔ E
    let π : J →* MulAut (L ⧸ center L) :=
      (Finkelstein1977.automizer L).comp (inclusion (sup_le (sup_le le_normalizer hSL) hEL))
    let B := π.range
    let Ebar : Subgroup B := (E.subgroupOf J).map π.rangeRestrict
    let tbar : B := π.rangeRestrict ⟨t, mem_sup_right ht⟩
    let W := ⁅S, E⁆ ⊔ thetaT p E
    let Wbar : Subgroup B :=
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({tbar} : Set B)), Ebar⁆ ⊔ thetaT p Ebar
    π.ker.map J.subtype = J ⊓ centralizer (L : Set G) ∧ Group.IsSolvable π.ker ∧
      (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range ≤ B ∧
      generalizedFitting B =
        (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range.subgroupOf B ∧
      Nonempty ((MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range.subgroupOf B ≃*
        (L ⧸ center L)) ∧
      IsElementaryAbelian p Ebar ∧ Nat.card Ebar = p ^ 2 ∧ tbar ≠ 1 ∧
      (W : Set G) = ((⁅S, E⁆ : Subgroup G) : Set G) * (thetaT p E : Set G) ∧ W ≤ J ∧
      (Wbar : Set B) =
        ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({tbar} : Set B)), Ebar⁆ :
          Subgroup B) : Set B) * (thetaT p Ebar : Set B) ∧
      (W.subgroupOf J).map π.rangeRestrict ≤ Wbar := by
  intro S J π B Ebar tbar W Wbar
  have := hE
  have hLq := hL.1
  have : Group.IsPerfect L := hLq.1
  have : IsSimpleGroup (L ⧸ center L) := hLq.2.1
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    SteinbergBY.mul_comm_of_isMulCommutative hx hy
  have hθN : ∀ H : Subgroup G, H ≤ normalizer
      (inSubgroup (aschbacherSolvableCore p) H : Set G) := fun H =>
    le_normalizer.trans (SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore p H)
  have hEC : E ≤ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hEcomm x hx t ht)
  have hES : E ≤ normalizer (S : Set G) := hEC.trans (hθN _)
  have hJN : J ≤ normalizer (L : Set G) := sup_le (sup_le le_normalizer hSL) hEL
  have hLJ : L ≤ J := le_sup_left.trans le_sup_left
  have hSJ : S ≤ J := le_sup_right.trans le_sup_left
  have hEJ : E ≤ J := le_sup_right
  set π' : J →* B := π.rangeRestrict with hπ'
  have hπ1 : ∀ j : J, π j = 1 ↔ (j : G) ∈ centralizer (L : Set G) := fun j =>
    Finkelstein1977.automizer_eq_one_iff L (inclusion hJN j)
  have hker : π.ker.map J.subtype = J ⊓ centralizer (L : Set G) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.2, (hπ1 j).mp (MonoidHom.mem_ker.mp hj)⟩
    · rintro ⟨hxJ, hxC⟩
      exact ⟨⟨x, hxJ⟩, MonoidHom.mem_ker.mpr ((hπ1 ⟨x, hxJ⟩).mpr hxC), rfl⟩
  have hSsolv : Group.IsSolvable S := by
    change Group.IsSolvable (inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)))
    rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
    exact RankThreeEvenClassification.Helpers.thetaCoreOf_solvable p hp _
  have hEsolv : Group.IsSolvable E := Group.isSolvable_of_comm fun x y =>
    Subtype.ext (hEcomm x x.2 y y.2)
  have hKsolv : Group.IsSolvable (J ⊓ centralizer (L : Set G) : Subgroup G) := by
    have h := isSolvable_inf_centralizer_of_sup (sup_le hSL hEL)
      (isSolvable_sup_of_le_normalizer hES hSsolv hEsolv)
    rwa [← sup_assoc] at h
  have hkerSolv : Group.IsSolvable π.ker := by
    rw [← hker] at hKsolv
    exact Group.isSolvable_of_surjective
      (f := (π.ker.equivMapOfInjective J.subtype J.subtype_injective).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hInn : (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range ≤ B := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨⟨l, hLJ l.2⟩, ?_⟩
    ext w
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
    change Finkelstein1977.automizer L (inclusion hJN ⟨l, hLJ l.2⟩) (m : L ⧸ center L) = _
    rw [Finkelstein1977.automizer_apply_mk, MulAut.conj_apply]
    rfl
  obtain ⟨-, -, -, hF, hiso⟩ :=
    ComponentClassification.SmallLocal.almost_simple_inner_generalized_fitting hLq.2.2 B hInn
  have hEinj : ∀ e (he : e ∈ E), π ⟨e, hEJ he⟩ = 1 → e = 1 := by
    intro e he h
    have hmem : e ∈ E ⊓ centralizer (L : Set G) := ⟨he, (hπ1 ⟨e, hEJ he⟩).mp h⟩
    rw [hCEL] at hmem
    exact hmem
  have hφE : Function.Injective (π'.comp (inclusion hEJ)) := by
    refine (MonoidHom.ker_eq_bot_iff _).mp (eq_bot_iff.mpr fun e he => ?_)
    have h : π ⟨e, hEJ e.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp he)
    exact (mem_bot).mpr (Subtype.ext (hEinj e e.2 h))
  have hEbar : Ebar = (π'.comp (inclusion hEJ)).range := by
    rw [MonoidHom.range_comp, inclusion_range]
  have hEbarcard : Nat.card Ebar = p ^ 2 := by
    rw [hEbar, ← hEcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hφE).toEquiv).symm
  have hEbarEA : IsElementaryAbelian p Ebar := by
    refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      apply Subtype.ext
      rw [coe_mul, coe_mul, ← hax, ← hby, ← map_mul, ← map_mul,
        show a * b = b * a from Subtype.ext (hEcomm a ha b hb)]
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨a, ha, hax⟩ := x.2
      apply Subtype.ext
      rw [coe_pow, ← hax, ← map_pow,
        show a ^ p = 1 from Subtype.ext ((J.coe_pow a p).trans
          (elemPow_eq_one_of_isElementaryAbelian _ ha)), map_one]
      rfl
  have htbar : tbar ≠ 1 := fun h => ht1 (hEinj t ht (congrArg Subtype.val h))
  have hres := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t ht ht1
  have htbarE : tbar ∈ Ebar := ⟨⟨t, hEJ ht⟩, ht, rfl⟩
  have hresB := (SteinbergBY.section_nine_residual_to_intersection hp hp2 Ebar).1 tbar htbarE htbar
  have hSE : ⁅S, E⁆ ≤ S := le_normalizer_iff_commutator_le_left.mp hES
  have hTS : thetaT p E ≤ S := fun x hx => by
    simp only [thetaT, mem_iInf] at hx
    exact hx t ht ht1
  have hWJ : W ≤ J := (sup_le hSE hTS).trans hSJ
  have hEp : IsPGroup p (E.subgroupOf J) :=
    (IsPGroup.of_card hEcard).of_equiv (subgroupOfEquivOfLe hEJ).symm
  have hker' : Group.IsSolvable π'.ker := by
    rw [hπ', MonoidHom.ker_rangeRestrict]
    exact hkerSolv
  have himage : ∀ a (ha : a ∈ E), ((inSubgroup (aschbacherSolvableCore p)
      (centralizer ({a} : Set G))).subgroupOf J).map π' ≤
        inSubgroup (aschbacherSolvableCore p) (centralizer ({π' ⟨a, hEJ ha⟩} : Set B)) := by
    intro a ha
    refine (map_mono (subgroupOf_inSubgroup_aschbacherSolvableCore_le hp J (hEJ ha))).trans ?_
    exact map_inSubgroup_aschbacherSolvableCore_centralizer_le hp π'
      (MonoidHom.rangeRestrict_surjective π) hker'
      (hEp.to_le (zpowers_le.mpr (show (⟨a, hEJ ha⟩ : J) ∈ E.subgroupOf J from ha)))
  refine ⟨hker, hkerSolv, hInn, hF, hiso, hEbarEA, hEbarcard, htbar, hres, hWJ, hresB, ?_⟩
  have hcommJ : ⁅S, E⁆.subgroupOf J = ⁅S.subgroupOf J, E.subgroupOf J⁆ := by
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le (hSE.trans hSJ), map_commutator, map_subgroupOf_eq_of_le hSJ,
      map_subgroupOf_eq_of_le hEJ]
  have h1 : (⁅S, E⁆.subgroupOf J).map π' ≤
      ⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({tbar} : Set B)), Ebar⁆ := by
    rw [hcommJ, map_commutator]
    exact commutator_mono (himage t ht) le_rfl
  have h2 : ((thetaT p E).subgroupOf J).map π' ≤ thetaT p Ebar := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [thetaT, mem_iInf]
    intro b hb hb1
    obtain ⟨e', he', rfl⟩ := hb
    have he1 : (e' : G) ≠ 1 := fun h => hb1 (by rw [show e' = 1 from Subtype.ext h, map_one])
    have hxθ : (x : G) ∈
        inSubgroup (aschbacherSolvableCore p) (centralizer ({(e' : G)} : Set G)) := by
      have hx' : (x : G) ∈ thetaT p E := hx
      simp only [thetaT, mem_iInf] at hx'
      exact hx' _ he' he1
    exact himage _ he' ⟨x, hxθ, rfl⟩
  have hsub : W.subgroupOf J = ⁅S, E⁆.subgroupOf J ⊔ (thetaT p E).subgroupOf J :=
    subgroupOf_sup (hSE.trans hSJ) (hTS.trans hSJ)
  rw [hsub, Subgroup.map_sup]
  exact sup_le_sup h1 h2

end CFSG.RankThree.GroupTheory.SteinbergBM
