module

public import CFSG.Assembly.LargeEvenDefs
public import CFSG.GH74.GLS.Basic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.LocalAnalysis.ComponentInitial.SolvableCoreComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts

public section

namespace CFSG.StandardType.QTwo

open CFSG

private theorem qtwoDB7_a1_not_le_core {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (h3 : 3 ∣ Nat.card (J ⧸ Subgroup.center J)) :
    ¬ J ≤ CFSG.pPrimeCore 3 X := by
  intro hJR
  have hdvd : Nat.card (J ⧸ Subgroup.center J) ∣ Nat.card J :=
    Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (Subgroup.center J))
      (QuotientGroup.mk'_surjective _)
  have h3J : 3 ∣ Nat.card J := h3.trans hdvd
  have hcop : Nat.Coprime 3 (Nat.card J) :=
    (CFSG.pPrimeCore_coprime_card (p := 3) (G := X)).coprime_dvd_right
      (Subgroup.card_dvd_of_le hJR)
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop) h3J

theorem qtwoDB7_pPrimeCore_quotient {X : Type} [Group X] [Finite X] :
    CFSG.pPrimeCore 3 (X ⧸ CFSG.pPrimeCore 3 X) = ⊥ := by
  let R := CFSG.pPrimeCore 3 X
  have hker : Nat.Coprime 3 (Nat.card (QuotientGroup.mk' R).ker) := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  have hmap := CFSG.Semidihedral.Local.pPrimeCore_map_eq_of_coprime_ker 3 (QuotientGroup.mk' R)
    (QuotientGroup.mk'_surjective R) hker
  rw [← hmap, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem qtwoDB7_inf_core_le_center {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (hJ : CFSG.IsQuasisimple J) (h3 : 3 ∣ Nat.card (J ⧸ Subgroup.center J)) :
    (J ⊓ CFSG.pPrimeCore 3 X).subgroupOf J ≤ Subgroup.center J := by
  have hNn : ((J ⊓ CFSG.pPrimeCore 3 X).subgroupOf J).Normal := by
    rw [Subgroup.inf_subgroupOf_left]
    exact Subgroup.normal_subgroupOf
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hJ hNn with h | h
  · exfalso
    have hJR : J ≤ CFSG.pPrimeCore 3 X := by
      intro j hj
      have hmem : (⟨j, hj⟩ : J) ∈ (J ⊓ CFSG.pPrimeCore 3 X).subgroupOf J := by
        rw [h]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
    exact qtwoDB7_a1_not_le_core h3 hJR
  · exact h

theorem qtwoDB7_map_isQuasisimple {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (hJ : CFSG.IsQuasisimple J) (h3 : 3 ∣ Nat.card (J ⧸ Subgroup.center J)) :
    CFSG.IsQuasisimple (J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) := by
  set f : J →* X ⧸ CFSG.pPrimeCore 3 X :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)).comp J.subtype with hf
  have hrange : f.range = J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hJ f with h | h
  · exfalso
    have hbot : J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥ := by rwa [← hrange]
    have hJR : J ≤ CFSG.pPrimeCore 3 X := by
      rw [← QuotientGroup.ker_mk' (CFSG.pPrimeCore 3 X)]
      exact (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) J).mp hbot
    exact qtwoDB7_a1_not_le_core h3 hJR
  · rwa [hrange] at h

theorem qtwoDB7_centerQuot_of_surj {J Jb : Type} [Group J] [Group Jb] (hJ : commutator J = ⊤)
    (f : J →* Jb) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center J) :
    Nonempty (J ⧸ Subgroup.center J ≃* Jb ⧸ Subgroup.center Jb) := by
  letI : Group.IsPerfect J := ⟨hJ⟩
  have hcomap := CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel
    f hf hker
  have hc : Subgroup.center J = ((QuotientGroup.mk' (Subgroup.center Jb)).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      ((QuotientGroup.mk'_surjective _).comp hf))⟩

private theorem qtwoDB7_a1_three_dvd_map {X : Type} [Group X] [Finite X] {J : Subgroup X}
    (hJ : CFSG.IsQuasisimple J) (h3 : 3 ∣ Nat.card (J ⧸ Subgroup.center J)) :
    3 ∣ Nat.card ((J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ⧸
      Subgroup.center (J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) := by
  let R := CFSG.pPrimeCore 3 X
  let f : J →* X ⧸ R := (QuotientGroup.mk' R).comp J.subtype
  have hrange : f.range = J.map (QuotientGroup.mk' R) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.rangeRestrict.ker ≤ Subgroup.center J := by
    intro j hj
    have hj1 : f j = 1 := by
      have := MonoidHom.mem_ker.mp hj
      simpa using congrArg Subtype.val this
    have hjR : (j : X) ∈ R := by
      rw [← QuotientGroup.ker_mk' R]
      simpa [f] using hj1
    exact qtwoDB7_inf_core_le_center hJ h3 (Subgroup.mem_subgroupOf.mpr ⟨j.2, hjR⟩)
  obtain ⟨e⟩ := qtwoDB7_centerQuot_of_surj hJ.1.commutator_eq_top f.rangeRestrict
    f.rangeRestrict_surjective hker
  rw [← hrange, ← Nat.card_congr e.toEquiv]
  exact h3

theorem qtwoDB7_image_isPCompIn {X : Type} [Group X] [Finite X] {J : Subgroup X} {y : X}
    (hy3 : y ^ 3 = 1) (hJC : J ≤ Subgroup.centralizer ({y} : Set X))
    (hc : CFSG.IsComponent (J.subgroupOf (Subgroup.centralizer ({y} : Set X))))
    (h3 : 3 ∣ Nat.card (J ⧸ Subgroup.center J)) :
    CFSG.GH74.GLS.IsPCompIn 3
      (Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) y} :
        Set (X ⧸ CFSG.pPrimeCore 3 X)))
      (J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) ∧
    CFSG.IsComponent
      ((J.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).subgroupOf
        (Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pPrimeCore 3 X) y} :
          Set (X ⧸ CFSG.pPrimeCore 3 X)))) := by
  let R := CFSG.pPrimeCore 3 X
  let π := QuotientGroup.mk' R
  let C := Subgroup.centralizer ({y} : Set X)
  let Cb := Subgroup.centralizer ({π y} : Set (X ⧸ R))
  let Jb : Subgroup (X ⧸ R) := J.map π
  have hJ : CFSG.IsQuasisimple J :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hJC)).1 hc.1
  have hJbCb : Jb ≤ Cb := by
    rintro _ ⟨j, hj, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa using congrArg π (Subgroup.mem_centralizer_singleton_iff.mp (hJC hj))
  have hJbqs : CFSG.IsQuasisimple Jb := qtwoDB7_map_isQuasisimple hJ h3
  have h3' : 3 ∣ Nat.card (Jb ⧸ Subgroup.center Jb) := qtwoDB7_a1_three_dvd_map hJ h3
  have hCb : Cb = C.map π := by
    have hA : IsPGroup 3 (Subgroup.zpowers y) := by
      have hdvd : orderOf y ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hy3
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3, pow_one])
    have hN : ¬ 3 ∣ Nat.card R :=
      Nat.prime_three.coprime_iff_not_dvd.mp
        (CFSG.pPrimeCore_coprime_card (p := 3) (G := X))
    have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 R hN
      (Subgroup.zpowers y) hA
    have h1 : Subgroup.centralizer (Subgroup.zpowers y : Set X) =
        Subgroup.centralizer ({y} : Set X) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have h2 : (Subgroup.zpowers y).map π = Subgroup.zpowers (π y) :=
      MonoidHom.map_zpowers π y
    have h3 : Subgroup.centralizer (Subgroup.zpowers (π y) : Set (X ⧸ R)) =
        Subgroup.centralizer ({π y} : Set (X ⧸ R)) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rw [h1, h2, h3] at h
    exact h.symm
  let φ : ↥C →* ↥Cb :=
    { toFun := fun c => ⟨π (c : X), by
        rw [hCb]
        exact Subgroup.mem_map_of_mem π c.2⟩
      map_one' := Subtype.ext (map_one π)
      map_mul' := fun a b => Subtype.ext (map_mul π (a : X) (b : X)) }
  have hφ : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    rw [hCb] at hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨c, hc⟩, rfl⟩
  have hmap : (J.subgroupOf C).map φ = Jb.subgroupOf Cb := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mp hj))
    · intro hx
      obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
      exact ⟨⟨j, hJC hj⟩, Subgroup.mem_subgroupOf.mpr hj, Subtype.ext hjx⟩
  have hsub : (Jb.subgroupOf Cb).IsSubnormal := by
    rw [← hmap]
    exact hc.2.map hφ
  have hcomp : CFSG.IsComponent (Jb.subgroupOf Cb) :=
    ⟨(CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
        (Subgroup.subgroupOfEquivOfLe hJbCb)).2 hJbqs, hsub⟩
  have hnotle : ¬ (Jb.subgroupOf Cb) ≤ CFSG.pPrimeCore 3 ↥Cb := by
    intro hle
    have hdvd1 : Nat.card (Jb.subgroupOf Cb) ∣ Nat.card (CFSG.pPrimeCore 3 ↥Cb) :=
      Subgroup.card_dvd_of_le hle
    have hcard : Nat.card (Jb.subgroupOf Cb) = Nat.card Jb :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJbCb).toEquiv
    have hdvd : Nat.card Jb ∣ Nat.card (CFSG.pPrimeCore 3 ↥Cb) := hcard ▸ hdvd1
    have hcop : Nat.Coprime 3 (Nat.card Jb) :=
      (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Cb)).coprime_dvd_right hdvd
    have h3Jb : 3 ∣ Nat.card Jb :=
      h3'.trans (Subgroup.card_dvd_of_surjective
        (f := QuotientGroup.mk' (Subgroup.center Jb)) (QuotientGroup.mk'_surjective _))
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hcop) h3Jb
  have hpc : CFSG.IsPComponent 3 (Jb.subgroupOf Cb) :=
    CFSG.LocalAnalysis.ComponentInitial.isPComponent_of_isComponent_of_not_le 3 hcomp hnotle
  exact ⟨⟨hJbCb, hpc⟩, hcomp⟩

private theorem qtwoDB7_a1_centralizer_subgroupOf {G : Type*} [Group G] (H : Subgroup G)
    (y : ↥H) :
    (Subgroup.centralizer ({(y : G)} : Set G)).subgroupOf H =
      Subgroup.centralizer ({y} : Set ↥H) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

private theorem qtwoDB7_a1_isComponentOf_subgroupOf {G : Type*} [Group G] {K X H : Subgroup G}
    (hXH : X ≤ H) (hK : CFSG.Assembly.IsComponentOf K X) :
    CFSG.Assembly.IsComponentOf (K.subgroupOf H) (X.subgroupOf H) := by
  have hKH : K ≤ H := hK.1.trans hXH
  have hle : K.subgroupOf H ≤ X.subgroupOf H := Subgroup.subgroupOf_mono H hK.1
  refine ⟨hle, ?_, ?_⟩
  · have hsubX : (K.subgroupOf X).IsSubnormal :=
      (CFSG.Assembly.IsSubnormal.iff_subgroupOf hK.1).mp hK.2.1
    let e : X ≃* X.subgroupOf H := (Subgroup.subgroupOfEquivOfLe hXH).symm
    have hmap : (K.subgroupOf X).map (e : X →* X.subgroupOf H) =
        (K.subgroupOf H).subgroupOf (X.subgroupOf H) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        exact ⟨⟨(y : G), y.2⟩, hy, Subtype.ext (Subtype.ext rfl)⟩
    have hsn : ((K.subgroupOf H).subgroupOf (X.subgroupOf H)).IsSubnormal := by
      rw [← hmap]
      exact hsubX.map (f := (e : X →* X.subgroupOf H)) e.surjective
    exact (CFSG.Assembly.IsSubnormal.iff_subgroupOf hle).mpr hsn
  · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hKH) hK.2.2

theorem qtwoDB7_transfer {G : Type} [Group G] [Finite G] {H J : Subgroup G} {y : ↥H}
    (hc : CFSG.Assembly.IsComponentOf J (H ⊓ Subgroup.centralizer ({(y : G)} : Set G))) :
    J ≤ H ∧ J.subgroupOf H ≤ Subgroup.centralizer ({y} : Set ↥H) ∧
      CFSG.IsQuasisimple (J.subgroupOf H) ∧
      CFSG.IsComponent ((J.subgroupOf H).subgroupOf (Subgroup.centralizer ({y} : Set ↥H))) := by
  have hJH : J ≤ H := hc.1.trans inf_le_left
  have hJCH : J.subgroupOf H ≤ Subgroup.centralizer ({y} : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hxD : (x : G) ∈ H ⊓ Subgroup.centralizer ({(y : G)} : Set G) :=
      hc.1 (Subgroup.mem_subgroupOf.mp hx)
    exact Subgroup.mem_centralizer_singleton_iff.mp hxD.2
  have hDCH : (H ⊓ Subgroup.centralizer ({(y : G)} : Set G)).subgroupOf H =
      Subgroup.centralizer ({y} : Set ↥H) := by
    rw [Subgroup.inf_subgroupOf_left]
    exact qtwoDB7_a1_centralizer_subgroupOf H y
  have hcompH : CFSG.Assembly.IsComponentOf (J.subgroupOf H)
      (Subgroup.centralizer ({y} : Set ↥H)) := by
    have h1 := qtwoDB7_a1_isComponentOf_subgroupOf
      (X := H ⊓ Subgroup.centralizer ({(y : G)} : Set G)) (H := H) inf_le_left hc
    rwa [hDCH] at h1
  have hqs : CFSG.IsQuasisimple (J.subgroupOf H) :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hJH)).2
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native J).1 hc.2.2)
  exact ⟨hJH, hJCH, hqs,
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hJCH).1 hcompH⟩

end CFSG.StandardType.QTwo

end
