module

public import CFSG.GroupTheory.ComponentImageUniqueness
public import CFSG.GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership
public import CFSG.Quasithin.Vol2.Ch3Sec3UniqueMax
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanK8K9
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPFF2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL11
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL3
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL4
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL6
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL8b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPR
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS2b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS6f
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7a
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPS7b
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPZ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open GroupTheory.CoprimeActionSupport.CentralizerOnQuotientMembership (mem_centralizerOnQuotient)
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GorensteinLyons (orbitConjugates)
open scoped Pointwise commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}
variable (c : Ctx82E3 D) {P A : Subgroup G} {a : G}

theorem mem_centralizerAt_of_mem_isElemAbelian
    (hA : CFSG.Open.IsElemAbelian 3 A) (ha : a ∈ A) {b : G} (hb : b ∈ A) :
    b ∈ centralizerAt a := by
  rw [centralizerAt, Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hA.1.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)

theorem mem_thetaComponentsAt_of_mem_orbitConjugates
    {J K : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a)
    (hK : K ∈ orbitConjugates (perfectCoreL c a) J) :
    K ∈ thetaComponentsAt 3 a := by
  obtain ⟨b, hb, rfl⟩ := hK
  exact CFSG.RankThree.PartOne.F106.conj_mem_thetaComponentsAt_cent Nat.prime_three
    (Subgroup.inv_mem _ (perfectCoreL_le c a hb).2) hJ

theorem isComponent_thetaImgAt {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a) :
    IsComponent (thetaImgAt a K) := by
  exact isComponent_map_of_mem_thetaComponents Nat.prime_three
    ((CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff (p := 3) (a := a) (L := K)).mp hK).2

theorem A_normalizes_orbit'
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz) (hK8 : K8Cat)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (hA : CFSG.Open.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) (hZA : zSub P c.L ≤ A)
    (hAPL : A ≤ P ⊓ c.L) (ha : a ∈ A) (haZ : a ∉ zSub P c.L)
    (hP2 : IsTripleCover (perfectCoreL c a ⧸ CFSG.Open.pCore 2 ↥(perfectCoreL c a))
        (alternatingGroup (Fin 6)) ∧
      zSub P c.L ≤ perfectCoreL c a ∧
      ⁅perfectCoreL c a, zSub P c.L⁆ ≤
        CFSG.Open.pCoreOf 2 (perfectCoreL c a) ∧
      A ≤ Subgroup.closure ({a} : Set G) ⊔ perfectCoreL c a)
    (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({a} : Set G)) = 1)
    (hP5 : ∀ W : Subgroup G, W ≤ D.M → Group.IsPerfect ↥W → ¬ 3 ∣ Nat.card W →
      W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
        (CFSG.Open.pCoreOf 2 c.L) c.L)
    {J : Subgroup G} (hJ : J ∈ thetaComponentsAt 3 a) (h3 : ¬ 3 ∣ Nat.card J)
    (h6 : (orbitConjugates (perfectCoreL c a) J).ncard = 6)
    (h7J : ¬ 7 ∣ Nat.card (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J))
    (hS1 : ∀ z ∈ zSub P c.L, ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      z ∈ Subgroup.normalizer (K : Set G))
    (hS2 : ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      autThetaQuot (zSub P c.L) K = ⊥)
    {z : G} (hz : z ∈ zSub P c.L) (hz1 : z ≠ 1)
    (hzgen : zSub P c.L = Subgroup.zpowers z)
    {W : Subgroup G}
    (hWH : W ≤ centralizerAt a)
    (hWz : W ≤ Subgroup.centralizer ({z} : Set G))
    (hWperf : Group.IsPerfect ↥W) (hW3 : ¬ 3 ∣ Nat.card W)
    (hWmap : ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      thetaImgAt a K ≤
        (W.subgroupOf (centralizerAt a)).map (QuotientGroup.mk' (thetaAt a))) :
    ∀ K ∈ orbitConjugates (perfectCoreL c a) J,
      A ≤ Subgroup.normalizer (K : Set G) := by
  classical
  intro K hK b hbA
  have hbH : b ∈ centralizerAt a :=
    mem_centralizerAt_of_mem_isElemAbelian hA ha hbA
  have hbL : b ∈ c.L := (hAPL hbA).2
  have hKθ : K ∈ thetaComponentsAt 3 a :=
    mem_thetaComponentsAt_of_mem_orbitConjugates (c := c) hJ hK
  let π : ↥(centralizerAt a) →* ↥(centralizerAt a) ⧸ thetaAt a :=
    QuotientGroup.mk' (thetaAt a)
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 c.L ⊓ centralizerAt a
  let T : Subgroup G := W ⊔ Q
  let Tbar : Subgroup (↥(centralizerAt a) ⧸ thetaAt a) :=
    (T.subgroupOf (centralizerAt a)).map π
  let Qbar : Subgroup (↥(centralizerAt a) ⧸ thetaAt a) :=
    (Q.subgroupOf (centralizerAt a)).map π
  let bbar : ↥(centralizerAt a) ⧸ thetaAt a := π ⟨b, hbH⟩
  let C : Subgroup (↥(centralizerAt a) ⧸ thetaAt a) :=
    (K.subgroupOf (centralizerAt a)).map π
  let Cb : Subgroup (↥(centralizerAt a) ⧸ thetaAt a) :=
    C.map (MulAut.conj bbar).toMonoidHom
  have hQT : Q ≤ T := le_sup_right
  have hQH : Q ≤ centralizerAt a := inf_le_right
  have hV0_2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.L
  have hQ2 : IsPGroup 2 Q := hV0_2.to_le inf_le_left
  have hTH : T ≤ centralizerAt a := sup_le hWH hQH
  have hleNZ : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) := by
    intro x hx
    have hxzp : x ∈ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hx
    rw [hzgen]
    exact Subgroup.centralizer_le_normalizer (Subgroup.zpowers z : Set G) hxzp
  have hWM : W ≤ D.M := (hWz.trans hleNZ).trans hNZ
  have hWcent : W ≤ CFSG.LocalAnalysis.RankThreeUC.centralizerOnQuotient D.M
      (CFSG.Open.pCoreOf 2 c.L) c.L := hP5 W hWM hWperf hW3
  have hWcomm : ∀ w ∈ W, ∀ v ∈ c.L, w * v * w⁻¹ * v⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
    fun w hw v hv =>
      (mem_centralizerOnQuotient.mp
        (hWcent hw)).2.2.2 v hv
  have hWNV0 : W ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 c.L : Subgroup G) : Set G) :=
    fun w hw =>
      (mem_centralizerOnQuotient.mp
        (hWcent hw)).2.2.1
  have hWNQ : W ≤ Subgroup.normalizer (Q : Set G) := by
    intro w hw
    have hWHn : w ∈ Subgroup.normalizer ((centralizerAt a : Subgroup G) : Set G) :=
      Subgroup.le_normalizer (hWH hw)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hWNV0 hw, hWHn⟩
  have hTNQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hWNQ Subgroup.le_normalizer
  have hQnormT : (Q.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQT).mpr hTNQ
  have hQbarLeTbar : Qbar ≤ Tbar := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map_of_mem π
      (Subgroup.subgroupOf_mono (centralizerAt a) hQT hq)
  have hTbarLeNorm : Tbar ≤
      Subgroup.normalizer (Qbar : Set (↥(centralizerAt a) ⧸ thetaAt a)) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hz
      have huT : (u : G) ∈ T := Subgroup.mem_subgroupOf.mp hu
      have hqQ : (q : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
      have hconj : (u : G) * (q : G) * (u : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hTNQ huT) (q : G)).1 hqQ
      have hconj' : u * q * u⁻¹ ∈ Q.subgroupOf (centralizerAt a) := by
        rw [Subgroup.mem_subgroupOf]
        exact hconj
      have heq : π u * π q * (π u)⁻¹ = π (u * q * u⁻¹) := by
        simp [map_mul, map_inv]
      rw [heq]
      exact Subgroup.mem_map_of_mem π hconj'
    · intro hz'
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨q, hqz⟩ := QuotientGroup.mk'_surjective (thetaAt a) z
      rw [← hqz] at hz'
      obtain ⟨q1, hq1, hq1eq⟩ := Subgroup.mem_map.mp hz'
      have huT : (u : G) ∈ T := Subgroup.mem_subgroupOf.mp hu
      have hq1Q : (q1 : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq1
      have hconj : (u : G)⁻¹ * (q1 : G) * (u : G) ∈ Q := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hTNQ (T.inv_mem huT)) (q1 : G)).1 hq1Q
      have hconj' : u⁻¹ * q1 * u ∈ Q.subgroupOf (centralizerAt a) := by
        rw [Subgroup.mem_subgroupOf]
        exact hconj
      have heq : π q = π (u⁻¹ * q1 * u) := by
        calc π q = (π u)⁻¹ * (π u * π q * (π u)⁻¹) * π u := by group
          _ = (π u)⁻¹ * π q1 * π u := by rw [hq1eq]
          _ = π (u⁻¹ * q1 * u) := by simp only [map_mul, map_inv]
      rw [← hqz, heq]
      exact Subgroup.mem_map_of_mem π hconj'
  have hQbarNorm : (Qbar.subgroupOf Tbar).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQbarLeTbar).mpr hTbarLeNorm
  have hCcomp : IsComponent C := isComponent_thetaImgAt hKθ
  have hCW : C ≤ (W.subgroupOf (centralizerAt a)).map π := hWmap K hK
  have hCT : C ≤ Tbar :=
    hCW.trans (Subgroup.map_mono (Subgroup.subgroupOf_mono (centralizerAt a) le_sup_left))
  have hCbcomp : IsComponent Cb :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj bbar) hCcomp
  have hbwb_mem : ∀ w ∈ W, b * w * b⁻¹ ∈ T ∧ b * w * b⁻¹ ∈ centralizerAt a := by
    intro w hw
    have hwH : w ∈ centralizerAt a := hWH hw
    have hcommV0 : w * b * w⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
      hWcomm w hw b hbL
    have hcommV0' : b * w * b⁻¹ * w⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := by
      have hinv := Subgroup.inv_mem _ hcommV0
      have he : (w * b * w⁻¹ * b⁻¹)⁻¹ = b * w * b⁻¹ * w⁻¹ := by group
      rwa [he] at hinv
    have hcommH : b * w * b⁻¹ * w⁻¹ ∈ centralizerAt a :=
      mul_mem (mul_mem (mul_mem hbH hwH) (Subgroup.inv_mem _ hbH))
        (Subgroup.inv_mem _ hwH)
    have hcommQ : b * w * b⁻¹ * w⁻¹ ∈ Q := ⟨hcommV0', hcommH⟩
    have hbwbT : b * w * b⁻¹ ∈ T := by
      have he : b * w * b⁻¹ = (b * w * b⁻¹ * w⁻¹) * w := by group
      rw [he]
      exact T.mul_mem (hQT hcommQ) (Subgroup.mem_sup_left hw)
    have hbwbH : b * w * b⁻¹ ∈ centralizerAt a :=
      mul_mem (mul_mem hbH hwH) (Subgroup.inv_mem _ hbH)
    exact ⟨hbwbT, hbwbH⟩
  have hpi_conj : ∀ u : ↥(centralizerAt a),
      π (⟨b, hbH⟩ * u * (⟨b, hbH⟩⁻¹)) =
        π ⟨b, hbH⟩ * π u * (π ⟨b, hbH⟩)⁻¹ := by
    intro u
    simp only [map_mul, map_inv]
  have hpi_conj_inv : ∀ u : ↥(centralizerAt a),
      π (⟨b, hbH⟩ * u * (⟨b, hbH⟩⁻¹) * u⁻¹) =
        π ⟨b, hbH⟩ * π u * (π ⟨b, hbH⟩)⁻¹ * (π u)⁻¹ := by
    intro u
    simp only [map_mul, map_inv]
  have hCbT : Cb ≤ Tbar := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp (hCW hy)
    obtain ⟨hbwbT, hbwbH⟩ := hbwb_mem (w : G) (Subgroup.mem_subgroupOf.mp hw)
    have heq : (MulAut.conj bbar) y = π ⟨b * (w : G) * b⁻¹, hbwbH⟩ := by
      rw [← hwy]
      show π ⟨b, hbH⟩ * π w * (π ⟨b, hbH⟩)⁻¹ = π ⟨b * (w : G) * b⁻¹, hbwbH⟩
      rw [← hpi_conj w]
      congr 1
    change (MulAut.conj bbar) y ∈ Tbar
    rw [heq]
    exact Subgroup.mem_map_of_mem π (by
      rw [Subgroup.mem_subgroupOf]
      exact hbwbT)
  have hcongr : ∀ x ∈ C,
      (MulEquiv.toMonoidHom (MulAut.conj bbar)) x * x⁻¹ ∈ Qbar := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (hCW hx)
    obtain ⟨hbwbT, hbwbH⟩ := hbwb_mem (w : G) (Subgroup.mem_subgroupOf.mp hw)
    have hcommV0 : (w : G) * b * (w : G)⁻¹ * b⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L :=
      hWcomm (w : G) (Subgroup.mem_subgroupOf.mp hw) b hbL
    have hcommV0' : b * (w : G) * b⁻¹ * (w : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 c.L := by
      have hinv := Subgroup.inv_mem _ hcommV0
      have he : ((w : G) * b * (w : G)⁻¹ * b⁻¹)⁻¹ = b * (w : G) * b⁻¹ * (w : G)⁻¹ := by
        group
      rwa [he] at hinv
    have hcommH : b * (w : G) * b⁻¹ * (w : G)⁻¹ ∈ centralizerAt a :=
      mul_mem (mul_mem (mul_mem hbH (hWH (Subgroup.mem_subgroupOf.mp hw)))
        (Subgroup.inv_mem _ hbH))
        (Subgroup.inv_mem _ (hWH (Subgroup.mem_subgroupOf.mp hw)))
    have hcommQ : b * (w : G) * b⁻¹ * (w : G)⁻¹ ∈ Q := ⟨hcommV0', hcommH⟩
    have heq : (MulAut.conj bbar) x * x⁻¹ =
        π ⟨b * (w : G) * b⁻¹ * (w : G)⁻¹, hcommH⟩ := by
      rw [← hwx]
      show π ⟨b, hbH⟩ * π w * (π ⟨b, hbH⟩)⁻¹ * (π w)⁻¹ =
        π ⟨b * (w : G) * b⁻¹ * (w : G)⁻¹, hcommH⟩
      rw [← hpi_conj_inv w]
      congr 1
    change (MulAut.conj bbar) x * x⁻¹ ∈ Qbar
    rw [heq]
    exact Subgroup.mem_map_of_mem π (by
      rw [Subgroup.mem_subgroupOf]
      exact hcommQ)
  have hCeqH : C = Cb := by
    have hQbar2 : IsPGroup 2 Qbar :=
      (show IsPGroup 2 (Q.subgroupOf (centralizerAt a)) from hQ2.comap_subtype).map π
    have hCnotQ : ¬ C ≤ Qbar := by
      intro hle
      haveI : Nontrivial ↥C := CFSG.LocalCores.isQuasisimple_nontrivial hCcomp.1
      haveI : Group.IsNilpotent ↥Qbar := IsPGroup.isNilpotent hQbar2
      haveI : Group.IsSolvable ↥Qbar := IsNilpotent.to_isSolvable
      haveI : Group.IsPerfect ↥C := hCcomp.1.1
      exact Group.IsPerfect.not_isSolvable ↥C
        (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
          (Subgroup.inclusion_injective hle))
    let Qsub : Subgroup Tbar := Qbar.subgroupOf Tbar
    haveI hQsub : Qsub.Normal := hQbarNorm
    let ψ : Tbar →* Tbar ⧸ Qsub := QuotientGroup.mk' Qsub
    let C1 : Subgroup Tbar := C.subgroupOf Tbar
    let C2 : Subgroup Tbar := Cb.subgroupOf Tbar
    have hC1 : IsComponent C1 := CFSG.LocalCores.component_overgroup hCcomp hCT
    have hC2 : IsComponent C2 := CFSG.LocalCores.component_overgroup hCbcomp hCbT
    have hmap : C1.map ψ = C2.map ψ := by
      ext y
      constructor
      · intro hy
        obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
        have hxC : (x : ↥(centralizerAt a) ⧸ thetaAt a) ∈ C := hx
        have hxz : (MulEquiv.toMonoidHom (MulAut.conj bbar))
            (x : ↥(centralizerAt a) ⧸ thetaAt a) *
            (x : ↥(centralizerAt a) ⧸ thetaAt a)⁻¹ ∈ Qbar := hcongr _ hxC
        let z : ↥(centralizerAt a) ⧸ thetaAt a :=
          (MulAut.conj bbar) (x : ↥(centralizerAt a) ⧸ thetaAt a)
        have hzCb : z ∈ Cb := Subgroup.mem_map_of_mem _ hxC
        have hzT : z ∈ Tbar := hCbT hzCb
        refine Subgroup.mem_map.mpr ⟨⟨z, hzT⟩, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact hzCb
        · have hmem : (⟨z, hzT⟩ : Tbar) / x ∈ Qsub := by
            rw [Subgroup.mem_subgroupOf]
            simpa [div_eq_mul_inv, z] using hxz
          exact (QuotientGroup.eq_iff_div_mem (N := Qsub)).mpr hmem
      · intro hy
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
        have huCb : (u : ↥(centralizerAt a) ⧸ thetaAt a) ∈ Cb := hu
        obtain ⟨x, hxC, hxeq⟩ := Subgroup.mem_map.mp huCb
        have hxz : (MulEquiv.toMonoidHom (MulAut.conj bbar)) x * x⁻¹ ∈ Qbar :=
          hcongr x hxC
        have hux : (u : ↥(centralizerAt a) ⧸ thetaAt a) * x⁻¹ ∈ Qbar := by
          have h := hxz
          rw [hxeq] at h
          exact h
        have hxu : x * (u : ↥(centralizerAt a) ⧸ thetaAt a)⁻¹ ∈ Qbar := by
          simpa [mul_inv_rev, inv_inv] using Subgroup.inv_mem _ hux
        have hxT : x ∈ Tbar := hCT hxC
        refine Subgroup.mem_map.mpr ⟨⟨x, hxT⟩, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact hxC
        · have hmem : (⟨x, hxT⟩ : Tbar) / u ∈ Qsub := by
            rw [Subgroup.mem_subgroupOf]
            simpa [div_eq_mul_inv] using hxu
          exact (QuotientGroup.eq_iff_div_mem (N := Qsub)).mpr hmem
    have hC1notQ : ¬ C1 ≤ ψ.ker := by
      rw [QuotientGroup.ker_mk']
      intro h
      apply hCnotQ
      intro x hx
      have hx1 : (⟨x, hCT hx⟩ : Tbar) ∈ C1 := by
        rw [Subgroup.mem_subgroupOf]
        exact hx
      exact Subgroup.mem_subgroupOf.mp (h hx1)
    have hqimg : CFSG.IsQuasisimple ↥(C1.map ψ) :=
      CFSG.LocalCores.isQuasisimple_map hC1.1 ψ hC1notQ
    have hna : ∃ a ∈ C1.map ψ, ∃ b ∈ C1.map ψ, a * b ≠ b * a := by
      have hnc : ¬ IsMulCommutative ↥(C1.map ψ) := by
        haveI : Nontrivial ↥(C1.map ψ) :=
          CFSG.LocalCores.isQuasisimple_nontrivial hqimg
        haveI : Group.IsPerfect ↥(C1.map ψ) := hqimg.1
        exact Group.IsPerfect.not_isMulCommutative (G := ↥(C1.map ψ))
      obtain ⟨a, b, hab⟩ : ∃ a b : ↥(C1.map ψ), a * b ≠ b * a := by
        by_contra h
        apply hnc
        rw [isMulCommutative_iff]
        intro x y
        by_contra hxy
        exact h ⟨x, y, hxy⟩
      exact ⟨a, a.2, b, b.2, fun h => hab (Subtype.ext h)⟩
    have hCeq : C1 = C2 :=
      CFSG.ComponentImage.isComponent_eq_of_map_eq_of_noncommuting ψ hC1 hC2 hmap hna
    have h := congrArg (fun S : Subgroup Tbar => S.map Tbar.subtype) hCeq
    simpa [C1, C2, Subgroup.map_subgroupOf_eq_of_le hCT,
      Subgroup.map_subgroupOf_eq_of_le hCbT] using h
  have hbbarNorm : bbar ∈
      Subgroup.normalizer (C : Set (↥(centralizerAt a) ⧸ thetaAt a)) :=
    CFSG.LocalAnalysis.GorensteinLyons.map_conj_eq_self_iff.mp hCeqH.symm
  have hKsub : K.subgroupOf (centralizerAt a) ∈ thetaComponents 3 (centralizerAt a) :=
    ((CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff (p := 3) (a := a) (L := K)).mp hKθ).2
  have hbNormH : (⟨b, hbH⟩ : ↥(centralizerAt a)) ∈
      Subgroup.normalizer ((K.subgroupOf (centralizerAt a) : Subgroup ↥(centralizerAt a)) :
        Set ↥(centralizerAt a)) :=
    (CFSG.RankThree.mem_normalizer_iff_mk_mem_normalizer Nat.prime_three hKsub
      ⟨b, hbH⟩).mpr hbbarNorm
  exact (CFSG.Quasithin.H13.Ch3Sec3.mem_normalizer_subgroupOf_iff
    ((CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff (p := 3) (a := a) (L := K)).mp hKθ).1
    ⟨b, hbH⟩).mp hbNormH

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
