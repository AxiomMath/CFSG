module

public import CFSG.RankThree.GroupTheory.SteinbergBMFaithfulComponentAlmostSimpleImage
public import CFSG.RankThree.GroupTheory.SteinbergBYAutCentralizerTheta
public import CFSG.RankThree.Coprime.PlaneCoreCentralizesComponent

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree.LocalRank CFSG.RankThree CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

@[expose] noncomputable def autThetaT (p : ℕ) {M : Type*} [Group M] (B A : Subgroup M) :
    Subgroup M :=
  ⨅ (a : M) (_ : a ∈ A) (_ : a ≠ 1),
    inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({a} : Set M))

@[expose] noncomputable def autPlaneProduct (p : ℕ) {M : Type*} [Group M] (B A : Subgroup M)
    (t : M) : Subgroup M :=
  ⁅inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({t} : Set M)), A⁆ ⊔ autThetaT p B A

@[expose] def PlaneLocalCoreOdd (p : ℕ) (T : Type*) [Group T] : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ A : Subgroup (MulAut T), A ≤ B → IsElementaryAbelian p A → Nat.card A = p ^ 2 →
      ∀ t ∈ A, t ≠ 1 → ¬ 2 ∣ Nat.card (autPlaneProduct p B A t)

@[expose] def PlaneLocalCoreInner (p : ℕ) (T : Type*) [Group T]
    (P : Subgroup (MulAut T) → Prop) : Prop :=
  ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
    ∀ A : Subgroup (MulAut T), A ≤ (MulAut.conj : T →* MulAut T).range →
      IsElementaryAbelian p A → Nat.card A = p ^ 2 → P A →
      ∀ t ∈ A, t ≠ 1 → autPlaneProduct p B A t = ⊥

theorem map_centralizer_singleton_mulEquiv {M M' : Type*} [Group M] [Group M'] (φ : M ≃* M')
    (t : M) : (centralizer ({t} : Set M)).map φ.toMonoidHom = centralizer ({φ t} : Set M') := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have := congrArg φ h
    simpa using this
  · intro h
    apply φ.injective
    simpa using h

theorem map_inSubgroup_theta_centralizer_mulEquiv {M M' : Type*} [Group M] [Group M']
    [Finite M] {p : ℕ} (hp : p.Prime) (φ : M ≃* M') (B : Subgroup M) (a : M) :
    (inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({a} : Set M))).map φ.toMonoidHom =
      inSubgroup (aschbacherSolvableCore p)
        (B.map φ.toMonoidHom ⊓ centralizer ({φ a} : Set M')) := by
  rw [SteinbergBY.map_inSubgroup_aschbacherSolvableCore_mulEquiv hp φ,
    Subgroup.map_inf _ _ _ φ.injective, map_centralizer_singleton_mulEquiv]

theorem map_autThetaT_mulEquiv {M M' : Type*} [Group M] [Group M'] [Finite M] {p : ℕ}
    (hp : p.Prime) (φ : M ≃* M') (B A : Subgroup M) :
    (autThetaT p B A).map φ.toMonoidHom =
      autThetaT p (B.map φ.toMonoidHom) (A.map φ.toMonoidHom) := by
  ext x
  rw [Subgroup.mem_map_equiv]
  simp only [autThetaT, Subgroup.mem_iInf]
  constructor
  · intro h a' ha' ha'1
    obtain ⟨a, haA, rfl⟩ := Subgroup.mem_map.mp ha'
    have ha1 : a ≠ 1 := fun h1 => ha'1 (by simp [h1])
    have h2 := Subgroup.mem_map_equiv.mpr (h a haA ha1)
    rw [map_inSubgroup_theta_centralizer_mulEquiv hp φ B a] at h2
    exact h2
  · intro h a haA ha1
    have h1 := h (φ a) (Subgroup.mem_map_of_mem _ haA)
      (fun h1 => ha1 (φ.injective (by simpa using h1)))
    rw [← map_inSubgroup_theta_centralizer_mulEquiv hp φ B a] at h1
    exact Subgroup.mem_map_equiv.mp h1

theorem map_autPlaneProduct_mulEquiv {M M' : Type*} [Group M] [Group M'] [Finite M] {p : ℕ}
    (hp : p.Prime) (φ : M ≃* M') (B A : Subgroup M) (t : M) :
    (autPlaneProduct p B A t).map φ.toMonoidHom =
      autPlaneProduct p (B.map φ.toMonoidHom) (A.map φ.toMonoidHom) (φ t) := by
  rw [autPlaneProduct, autPlaneProduct, Subgroup.map_sup, Subgroup.map_commutator,
    map_inSubgroup_theta_centralizer_mulEquiv hp φ B t, map_autThetaT_mulEquiv hp φ]

theorem mulAutCongr_conj {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') (x : T) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem map_conj_range_mulAutCongr {T T' : Type*} [Group T] [Group T'] (e : T ≃* T') :
    (((MulAut.conj : T →* MulAut T).range).map (MulAut.congr e).toMonoidHom) =
      (MulAut.conj : T' →* MulAut T').range := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, ⟨x, rfl⟩, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨e x, (mulAutCongr_conj e x).symm⟩
  · rintro ⟨x, rfl⟩
    refine Subgroup.mem_map.mpr ⟨MulAut.conj (e.symm x), ⟨e.symm x, rfl⟩, ?_⟩
    have := mulAutCongr_conj e (e.symm x)
    simpa using this

theorem PlaneLocalCoreOdd.of_mulEquiv {T T' : Type*} [Group T] [Group T'] [Finite T] {p : ℕ}
    (hp : p.Prime) (e : T ≃* T') (h : PlaneLocalCoreOdd p T') : PlaneLocalCoreOdd p T := by
  intro B hB A hAB hA hAcard t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set φ := MulAut.congr e with hφ
  have h1 := h (B.map φ.toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr e]; exact Subgroup.map_mono hB)
    (A.map φ.toMonoidHom) (Subgroup.map_mono hAB) (IsElementaryAbelian.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hAcard]) (φ t)
    (Subgroup.mem_map_of_mem _ htA) (fun h1 => ht1 (φ.injective (by simpa using h1)))
  rw [← map_autPlaneProduct_mulEquiv hp φ, Subgroup.card_map_of_injective φ.injective] at h1
  exact h1

theorem PlaneLocalCoreInner.of_mulEquiv {T T' : Type*} [Group T] [Group T'] [Finite T] {p : ℕ}
    (hp : p.Prime) (e : T ≃* T') {P' : Subgroup (MulAut T') → Prop}
    (h : PlaneLocalCoreInner p T' P') :
    PlaneLocalCoreInner p T (fun A => P' (A.map (MulAut.congr e).toMonoidHom)) := by
  intro B hB A hAB hA hAcard hPA t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  set φ := MulAut.congr e with hφ
  have h1 := h (B.map φ.toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr e]; exact Subgroup.map_mono hB)
    (A.map φ.toMonoidHom)
    (by rw [← map_conj_range_mulAutCongr e]; exact Subgroup.map_mono hAB)
    (IsElementaryAbelian.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hAcard]) hPA (φ t)
    (Subgroup.mem_map_of_mem _ htA) (fun h1 => ht1 (φ.injective (by simpa using h1)))
  rw [← map_autPlaneProduct_mulEquiv hp φ] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective (autPlaneProduct p B A t) (f := φ.toMonoidHom)
    φ.injective).mp h1

theorem map_subtype_theta_centralizer {M : Type*} [Group M] [Finite M] {p : ℕ}
    (hp : p.Prime) (B : Subgroup M) (a : B) :
    (inSubgroup (aschbacherSolvableCore p) (centralizer ({a} : Set B))).map B.subtype =
      inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({(a : M)} : Set M)) := by
  set C : Subgroup B := centralizer ({a} : Set B) with hC
  have hCK : C.map B.subtype = B ⊓ centralizer ({(a : M)} : Set M) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, hC, mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      have := congrArg Subtype.val hy
      simpa using this
    · rintro ⟨hxB, hx⟩
      refine ⟨⟨x, hxB⟩, ?_, rfl⟩
      exact Subtype.ext (by simpa using hx)
  let e : C ≃* (B ⊓ centralizer ({(a : M)} : Set M) : Subgroup M) :=
    (C.equivMapOfInjective B.subtype B.subtype_injective).trans (MulEquiv.subgroupCongr hCK)
  have h1 := aschbacherSolvableCore_map_mulEquiv hp e
  have h2 : inSubgroup (aschbacherSolvableCore p) (B ⊓ centralizer ({(a : M)} : Set M)) =
      ((aschbacherSolvableCore p C).map e.toMonoidHom).map
        (B ⊓ centralizer ({(a : M)} : Set M)).subtype := by
    rw [h1]; rfl
  rw [h2, Subgroup.map_map, inSubgroup, Subgroup.map_map]
  congr 1

theorem map_subtype_thetaT_le {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (A : Subgroup B) :
    (thetaT p A).map B.subtype ≤ autThetaT p B (A.map B.subtype) := by
  rintro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  simp only [autThetaT, Subgroup.mem_iInf]
  intro a ha ha1
  obtain ⟨b, hbA, rfl⟩ := Subgroup.mem_map.mp ha
  have hb1 : b ≠ 1 := fun h => ha1 (by simp [h])
  have hy' : y ∈ inSubgroup (aschbacherSolvableCore p) (centralizer ({b} : Set B)) := by
    have := hy
    simp only [thetaT, Subgroup.mem_iInf] at this
    exact this b hbA hb1
  have h2 : B.subtype y ∈ (inSubgroup (aschbacherSolvableCore p)
      (centralizer ({b} : Set B))).map B.subtype := Subgroup.mem_map_of_mem _ hy'
  rw [map_subtype_theta_centralizer hp B b] at h2
  exact h2

theorem map_subtype_planeProduct_le {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (A : Subgroup B) (t : B) :
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), A⁆ ⊔
        thetaT p A).map B.subtype ≤ autPlaneProduct p B (A.map B.subtype) (t : M) := by
  rw [Subgroup.map_sup, Subgroup.map_commutator, map_subtype_theta_centralizer hp B t]
  exact sup_le_sup le_rfl (map_subtype_thetaT_le hp B A)

theorem relIndex_inf_left_of_le {G : Type*} [Group G] {J W C : Subgroup G} (hWJ : W ≤ J) :
    (J ⊓ C).relIndex W = C.relIndex W := by
  unfold Subgroup.relIndex
  congr 1
  ext w
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨hWJ w.2, h⟩⟩

theorem twoPrimeResidual_le_centralizer_of_odd_relIndex {G : Type*} [Group G] {W L : Subgroup G}
    (hWN : W ≤ normalizer (L : Set G)) (hodd : ¬ 2 ∣ (centralizer (L : Set G)).relIndex W) :
    CFSG.Quasithin.twoPrimeResidual W ≤ centralizer (L : Set G) := by
  have hnorm : W ≤ normalizer ((W ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hwN := hWN hw
    have hCN := Subgroup.le_normalizer_iff.mp
      (CFSG.RankThreeEvenClassification.Helpers.normalizes_centralizer_of_normalizes _ L le_rfl)
    constructor
    · rintro ⟨hxW, hxC⟩
      exact ⟨W.mul_mem (W.mul_mem hw hxW) (W.inv_mem hw), hCN w hwN x hxC⟩
    · rintro ⟨hxW, hxC⟩
      refine ⟨?_, ?_⟩
      · have := W.mul_mem (W.mul_mem (W.inv_mem hw) hxW) hw
        simpa [mul_assoc] using this
      · have h := hCN w⁻¹ (inv_mem hwN) _ hxC
        simpa [mul_assoc] using h
  have hodd' : ¬ 2 ∣ (W ⊓ centralizer (L : Set G)).relIndex W := by
    rwa [inf_comm, Subgroup.inf_relIndex_right]
  have hres : CFSG.Quasithin.twoPrimeResidual W ≤ W ⊓ centralizer (L : Set G) :=
    iInf₂_le (W ⊓ centralizer (L : Set G)) ⟨inf_le_left, hnorm, hodd'⟩
  exact hres.trans inf_le_right

@[expose] noncomputable def actualPlane {G : Type*} [Group G] (L E : Subgroup G) :
    Subgroup (MulAut (L ⧸ center L)) :=
  (E.subgroupOf (normalizer (L : Set G))).map (Finkelstein1977.automizer L)

theorem plane_reduction_odd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) = ⊥)
    (hplane : PlaneLocalCoreOdd p (L ⧸ center L)) :
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
        normalizer (L : Set G) ∧
      ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) := by
  have hBM := SteinbergBM.faithful_component_local_core_almost_simple_image hp hp2 hE hEcard ht
    ht1 hL hEL hSL hCEL
  obtain ⟨hker, hsolv, hInn, hFit, hIso, hEbar, hEbarcard, htbar, hWset, hWJ, hWbarset, hmap⟩ :=
    hBM
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) with hS
  have hJN : L ⊔ S ⊔ E ≤ normalizer (L : Set G) := sup_le (sup_le le_normalizer hSL) hEL
  set J := L ⊔ S ⊔ E with hJ
  set π : J →* MulAut (L ⧸ center L) := (Finkelstein1977.automizer L).comp (inclusion hJN)
    with hπ
  set B := π.range with hB
  set Ebar : Subgroup B := (E.subgroupOf J).map π.rangeRestrict with hEbar_def
  set tbar : B := π.rangeRestrict ⟨t, mem_sup_right ht⟩ with htbar_def
  set W := ⁅S, E⁆ ⊔ thetaT p E with hW
  have hWN : W ≤ normalizer (L : Set G) := hWJ.trans hJN
  refine ⟨hWN, ?_⟩
  have hA' : IsElementaryAbelian p (Ebar.map B.subtype) := by
    have : Fact p.Prime := ⟨hp⟩
    have := hEbar
    exact IsElementaryAbelian.map_subtype
  have hA'card : Nat.card (Ebar.map B.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]; exact hEbarcard
  have htA' : (tbar : MulAut (L ⧸ center L)) ∈ Ebar.map B.subtype := by
    refine Subgroup.mem_map.mpr ⟨tbar, ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨t, mem_sup_right ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have ht'1 : (tbar : MulAut (L ⧸ center L)) ≠ 1 := fun h => htbar (Subtype.ext h)
  have hodd := hplane B hInn (Ebar.map B.subtype) (Subgroup.map_subtype_le _) hA' hA'card _
    htA' ht'1
  have hle := map_subtype_planeProduct_le hp B Ebar tbar
  have hWbar_odd : ¬ 2 ∣ Nat.card (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({tbar} : Set B)), Ebar⁆ ⊔ thetaT p Ebar : Subgroup B) := by
    intro h2
    apply hodd
    have h3 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective B.subtype_injective] at h3
    exact h2.trans h3
  have himg : ¬ 2 ∣ Nat.card ((W.subgroupOf J).map π.rangeRestrict) := fun h2 =>
    hWbar_odd (h2.trans (Subgroup.card_dvd_of_le hmap))
  have hrel : (centralizer (L : Set G)).relIndex W =
      Nat.card ((W.subgroupOf J).map π.rangeRestrict) := by
    have h1 : π.rangeRestrict.ker.relIndex (W.subgroupOf J) =
        Nat.card ((W.subgroupOf J).map π.rangeRestrict) := by
      rw [← MonoidHom.comap_bot, Subgroup.relIndex_comap, Subgroup.relIndex_bot_left]
    have hker' : π.ker.map J.subtype = J ⊓ centralizer (L : Set G) := hker
    rw [← h1, MonoidHom.ker_rangeRestrict,
      ← Subgroup.relIndex_map_map_of_injective π.ker (W.subgroupOf J) J.subtype_injective,
      hker', Subgroup.map_subgroupOf_eq_of_le hWJ, relIndex_inf_left_of_le hWJ]
  rw [hrel]
  exact himg

theorem plane_reduction_inner {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G} (hL : IsComponent L)
    (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hCEL : E ⊓ centralizer (L : Set G) = ⊥)
    {P : Subgroup (MulAut (L ⧸ center L)) → Prop}
    (hplane : PlaneLocalCoreInner p (L ⧸ center L) P) (hP : P (actualPlane L E))
    (hinner : actualPlane L E ≤ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range) :
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
      centralizer (L : Set G) := by
  have hBM := SteinbergBM.faithful_component_local_core_almost_simple_image hp hp2 hE hEcard ht
    ht1 hL hEL hSL hCEL
  obtain ⟨hker, hsolv, hInn, hFit, hIso, hEbar, hEbarcard, htbar, hWset, hWJ, hWbarset, hmap⟩ :=
    hBM
  set S := inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) with hS
  have hJN : L ⊔ S ⊔ E ≤ normalizer (L : Set G) := sup_le (sup_le le_normalizer hSL) hEL
  set J := L ⊔ S ⊔ E with hJ
  set π : J →* MulAut (L ⧸ center L) := (Finkelstein1977.automizer L).comp (inclusion hJN)
    with hπ
  set B := π.range with hB
  set Ebar : Subgroup B := (E.subgroupOf J).map π.rangeRestrict with hEbar_def
  set tbar : B := π.rangeRestrict ⟨t, mem_sup_right ht⟩ with htbar_def
  set W := ⁅S, E⁆ ⊔ thetaT p E with hW
  have hEJ : E ≤ J := le_sup_right
  have hplaneEq : Ebar.map B.subtype = actualPlane L E := by
    ext x
    simp only [hEbar_def, actualPlane, Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨⟨(j : G), hJN j.2⟩, hj, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨π.rangeRestrict ⟨n, hEJ hn⟩, ⟨⟨n, hEJ hn⟩, hn, rfl⟩, rfl⟩
  have hA' : IsElementaryAbelian p (Ebar.map B.subtype) := by
    have : Fact p.Prime := ⟨hp⟩
    have := hEbar
    exact IsElementaryAbelian.map_subtype
  have hA'card : Nat.card (Ebar.map B.subtype) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective B.subtype_injective]; exact hEbarcard
  have htA' : (tbar : MulAut (L ⧸ center L)) ∈ Ebar.map B.subtype := by
    refine Subgroup.mem_map.mpr ⟨tbar, ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨t, mem_sup_right ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have ht'1 : (tbar : MulAut (L ⧸ center L)) ≠ 1 := fun h => htbar (Subtype.ext h)
  have hbot := hplane B hInn (Ebar.map B.subtype) (hplaneEq ▸ hinner) hA' hA'card
    (hplaneEq ▸ hP) _ htA' ht'1
  have hle := map_subtype_planeProduct_le hp B Ebar tbar
  have hWbar_bot : (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({tbar} : Set B)), Ebar⁆ ⊔ thetaT p Ebar : Subgroup B) = ⊥ := by
    have h1 : (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({tbar} : Set B)), Ebar⁆ ⊔ thetaT p Ebar : Subgroup B).map B.subtype = ⊥ :=
      le_bot_iff.mp (hbot ▸ hle)
    exact (Subgroup.map_eq_bot_iff_of_injective _ B.subtype_injective).mp h1
  have hWker : (W.subgroupOf J).map π.rangeRestrict = ⊥ := le_bot_iff.mp (hWbar_bot ▸ hmap)
  have hker' : π.ker.map J.subtype = J ⊓ centralizer (L : Set G) := hker
  intro w hw
  have hwJ : (⟨w, hWJ hw⟩ : J) ∈ π.rangeRestrict.ker := by
    have : π.rangeRestrict ⟨w, hWJ hw⟩ ∈ (W.subgroupOf J).map π.rangeRestrict :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hw)
    rw [hWker, Subgroup.mem_bot] at this
    exact this
  rw [MonoidHom.ker_rangeRestrict] at hwJ
  have : w ∈ π.ker.map J.subtype := Subgroup.mem_map_of_mem _ hwJ
  rw [hker'] at this
  exact this.2

theorem commutator_le_normalizer_of_le {G : Type*} [Group G] {S E L : Subgroup G}
    (hS : S ≤ normalizer (L : Set G)) (hE : E ≤ normalizer (L : Set G)) :
    ⁅S, E⁆ ≤ normalizer (L : Set G) := by
  refine Subgroup.commutator_le.mpr fun s hs e he => ?_
  rw [commutatorElement_def]
  exact (normalizer (L : Set G)).mul_mem
    ((normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).mul_mem (hS hs) (hE he))
      ((normalizer (L : Set G)).inv_mem (hS hs))) ((normalizer (L : Set G)).inv_mem (hE he))

theorem component_local_core_odd_action_of_plane {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    (hplane : PlaneLocalCoreOdd p (L ⧸ center L)) :
    ((((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
        thetaT p E : Subgroup G)) : Set G) =
      ((⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ : Subgroup G) :
        Set G) * (thetaT p E : Set G)) ∧
    (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
        normalizer (L : Set G) ∧
      ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ∧
    CFSG.Quasithin.twoPrimeResidual
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
          thetaT p E) ≤ centralizer (L : Set G) ∧
    (E ⊓ centralizer (L : Set G) ≠ ⊥ →
      (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
        centralizer (L : Set G)) := by
  have hset := (SteinbergBY.section_nine_residual_to_intersection hp hp2 E).1 t ht ht1
  by_cases hC : E ⊓ centralizer (L : Set G) = ⊥
  · obtain ⟨hWN, hodd⟩ := plane_reduction_odd hp hp2 hE hEcard ht ht1 hL hEL hSL hC hplane
    exact ⟨hset, hWN, hodd, twoPrimeResidual_le_centralizer_of_odd_relIndex hWN hodd,
      fun h => absurd hC h⟩
  · have hXL := commutator_le_normalizer_of_le hSL hEL
    have hcent := (Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE
      hEcard ht ht1 hL hXL hC).2.2
    have hWC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcent
    have hWN : (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
        thetaT p E) ≤ normalizer (L : Set G) := hWC.trans
          (Subgroup.centralizer_le_normalizer (L : Set G))
    have hodd : ¬ 2 ∣ (centralizer (L : Set G)).relIndex
        (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔
          thetaT p E) := by
      rw [Subgroup.relIndex_eq_one.mpr hWC]
      omega
    exact ⟨hset, hWN, hodd, twoPrimeResidual_le_centralizer_of_odd_relIndex hWN hodd,
      fun _ => hWC⟩

theorem component_local_core_centralizes_of_inner_plane {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElementaryAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {t : G} (ht : t ∈ E) (ht1 : t ≠ 1) {L : Subgroup G}
    (hL : IsComponent L) (hEL : E ≤ normalizer (L : Set G))
    (hSL : inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)) ≤
      normalizer (L : Set G))
    {P : Subgroup (MulAut (L ⧸ center L)) → Prop}
    (hplane : PlaneLocalCoreInner p (L ⧸ center L) P)
    (hP : E ⊓ centralizer (L : Set G) ≠ ⊥ ∨
      (P (actualPlane L E) ∧
        actualPlane L E ≤ (MulAut.conj : L ⧸ center L →* MulAut (L ⧸ center L)).range)) :
    ⁅⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆, L⁆ = ⊥ ∧
      ⁅thetaT p E, L⁆ = ⊥ ∧
      (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set G)), E⁆ ⊔ thetaT p E) ≤
        centralizer (L : Set G) := by
  by_cases hC : E ⊓ centralizer (L : Set G) = ⊥
  · obtain ⟨hPE, hinner⟩ := hP.resolve_left (not_not.mpr hC)
    have hWC := plane_reduction_inner hp hp2 hE hEcard ht ht1 hL hEL hSL hC hplane hPE hinner
    refine ⟨Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_sup_left.trans hWC), ?_, hWC⟩
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (le_sup_right.trans hWC)
  · have hXL := commutator_le_normalizer_of_le hSL hEL
    obtain ⟨h1, h2, h3⟩ := Coprime.nonfaithful_plane_local_core_product_centralizes_component hp
      hE hEcard ht ht1 hL hXL hC
    exact ⟨h1, h2, Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3⟩

end CFSG.RankThree.PartOne
