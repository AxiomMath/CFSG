module

public import CFSG.RankThree.PartTwo.Sec14.Item148ResProofHJInner
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec6.BThreeFromLBalance
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148HJResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofHyp
import CFSG.RankThree.PartTwo.Sec14.Item148ResProofThetaK
import CFSG.RankThree.PartTwo.Sec14.Item148StepOne
import CFSG.RankThree.PartTwo.Sec14.Item148ProofLift
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec14.Concrete
import CFSG.RankThree.PartTwo.Sec13.Item131aAlpha
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Descent2
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec6.Item65One

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace HJRes148

open Res148 Main148
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

theorem mem_normalizer_alpha_of {A Y : Subgroup G} [(ker148 A Y).Normal] (hA3 : IsPGroup 3 A)
    {a : G} (ha : a ∈ A)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G))
    {g : ↥(Y ⊔ A) ⧸ ker148 A Y}
    (hg : g ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    g ∈ Subgroup.normalizer
      (Subgroup.zpowers (alpha148 A Y a ha) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (ker148 A Y) g
  set R : Subgroup ↥(Y ⊔ A) := A.subgroupOf (Y ⊔ A) with hR
  set C := ker148 A Y with hC
  have hR3 : IsPGroup 3 R := hA3.comap_of_injective (Y ⊔ A).subtype (Y ⊔ A).subtype_injective
  have hC3 : ¬ 3 ∣ Nat.card C := not_three_dvd_card_ker148
  have hpre : ∀ y : ↥(Y ⊔ A), y ∈ C ⊔ R ↔ QuotientGroup.mk' C y ∈ img148 A Y A := by
    intro y
    have h1 : (img148 A Y A).comap (QuotientGroup.mk' C) = R ⊔ C := by
      rw [img148, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [← Subgroup.mem_comap, h1]
    exact ⟨fun h => (sup_comm C R).le h, fun h => (sup_comm R C).le h⟩
  have hxn : x ∈ Subgroup.normalizer ((C ⊔ R : Subgroup ↥(Y ⊔ A)) : Set ↥(Y ⊔ A)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hpre, hpre, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hg _
  obtain ⟨o, ho, hon⟩ := StrongThree.exists_mul_mem_normalizer_of_sup hR3 hC3 hxn
  have hoxA : ((o * x : ↥(Y ⊔ A)) : G) ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have hzM : z ∈ Y ⊔ A := Subgroup.mem_sup_right hz
      have h1 := (Subgroup.mem_normalizer_iff.mp hon ⟨z, hzM⟩).mp hz
      exact h1
    · intro hz
      set w : ↥(Y ⊔ A) := o * x with hw
      have hzM : z ∈ Y ⊔ A := by
        have h1 : (w : G) * z * (w : G)⁻¹ ∈ Y ⊔ A := Subgroup.mem_sup_right hz
        have h2 := (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).inv_mem w.2) h1) w.2
        simpa [mul_assoc] using h2
      have h1 := (Subgroup.mem_normalizer_iff.mp hon ⟨z, hzM⟩).mpr hz
      exact h1
  have hoxa := hW hoxA
  have hoxa' : ((o * x : ↥(Y ⊔ A)) : G) * a * ((o * x : ↥(Y ⊔ A)) : G)⁻¹ ∈
      Subgroup.zpowers a :=
    (Subgroup.mem_normalizer_iff.mp hoxa a).mp (Subgroup.mem_zpowers a)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hoxa'
  have hoα : QuotientGroup.mk' C o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  refine Item148HJ.mem_normalizer_of_conj_mem fun u hu => ?_
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  refine Subgroup.mem_zpowers_iff.mpr ⟨k * m, ?_⟩
  have hconj : QuotientGroup.mk' C x * alpha148 A Y a ha * (QuotientGroup.mk' C x)⁻¹ =
      alpha148 A Y a ha ^ k := by
    have e1 : QuotientGroup.mk' C (o * x) = QuotientGroup.mk' C x := by
      rw [map_mul, hoα, one_mul]
    rw [← e1, alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul, ← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk.symm)
  rw [zpow_mul, ← hconj, conj_zpow]

theorem item4_27_of_le (h427 : Sec4.Item4_27) {Γ : Type} [Group Γ] [Finite Γ] (C : Subgroup Γ)
    (hC4 : SectionFourHyp ↥C) (hCθ : aschbacherSolvableCore 3 ↥C = ⊥)
    (hCE : partTwoE ↥C = partTwoF ↥C) {A L K : Subgroup Γ} {d : Γ} (hAC : A ≤ C) (hLC : L ≤ C)
    (hA : Late.IsE27 A) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hW : ∀ g ∈ C, g ∈ Subgroup.normalizer (A : Set Γ) →
      g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set Γ))
    (hLq : IsQuasisimple ↥L) (hLn : C ≤ Subgroup.normalizer (L : Set Γ))
    (hKL : K ≤ L ⊓ Subgroup.centralizer {d}) (hKq : IsQuasisimple ↥K)
    (hKsub : (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal)
    (htype : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      (d ∈ K ∧ Sec4.IsExtOf (↥K ⧸ CFSG.pCore 2 ↥K) Blueprint.NativeSporadic.ON
        (Multiplicative (ZMod 3)))) :
    K = L := by
  have hdC : d ∈ C := hAC hdA
  have hKC : K ≤ C := (hKL.trans inf_le_left).trans hLC
  set d' : ↥C := ⟨d, hdC⟩ with hd'def
  set L' : Subgroup ↥C := L.subgroupOf C with hL'def
  set A' : Subgroup ↥C := A.subgroupOf C with hA'def
  set K' : Subgroup ↥C := K.subgroupOf C with hK'def
  set M : Subgroup ↥C := L' ⊓ Subgroup.centralizer ({d'} : Set ↥C) with hMdef
  have hK'M : K' ≤ M := by
    intro x hx
    have hx' : (x : Γ) ∈ L ⊓ Subgroup.centralizer {d} := hKL hx
    refine ⟨hx'.1, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext ?_)⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp hx'.2
  set K₀ : Subgroup ↥M := K'.subgroupOf M with hK₀def
  let eL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLC
  let eK : ↥K₀ ≃* ↥K :=
    (Subgroup.subgroupOfEquivOfLe hK'M).trans (Subgroup.subgroupOfEquivOfLe hKC)
  have hA' : Late.IsE27 A' := by
    refine ⟨⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩, ?_⟩
    · have h := congrArg Subtype.val
        (hA.1.1.is_comm.comm ⟨((x : ↥C) : Γ), x.2⟩ ⟨((y : ↥C) : Γ), y.2⟩)
      simpa using h
    · simpa using hA.1.2 _ hx
    · rw [← hA.2]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  have hd'A : d' ∈ A' := hdA
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hL'n : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLC).mpr hLn
  have hL' : IsComponent L' := ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eL.symm hLq,
    hL'n.isSubnormal⟩
  have hW' : Subgroup.normalizer (A' : Set ↥C) ≤
      Subgroup.normalizer (Subgroup.zpowers d' : Set ↥C) := by
    intro x hx
    have hxA : (x : Γ) ∈ Subgroup.normalizer (A : Set Γ) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have h1 := (Subgroup.mem_normalizer_iff.mp hx ⟨z, hAC hz⟩).mp hz
        exact h1
      · intro hz
        have hzC : z ∈ C := by
          have h1 : (x : Γ) * z * (x : Γ)⁻¹ ∈ C := hAC hz
          have h2 := C.mul_mem (C.mul_mem (C.inv_mem x.2) h1) x.2
          simpa [mul_assoc] using h2
        exact (Subgroup.mem_normalizer_iff.mp hx ⟨z, hzC⟩).mpr hz
    have hxd := hW x x.2 hxA
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have hz : ∀ w : ↥C, w ∈ Subgroup.zpowers d' ↔ (w : Γ) ∈ Subgroup.zpowers d := by
      intro w
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨n, by simp [hd'def]⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext (by simpa [hd'def] using hn)⟩
    rw [hz z, hz (x * z * x⁻¹)]
    simpa using Subgroup.mem_normalizer_iff.mp hxd (z : Γ)
  have hfmem : ∀ m : ↥M, ((m : ↥C) : Γ) ∈ L ⊓ Subgroup.centralizer {d} := by
    intro m
    refine ⟨m.2.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp m.2.2)
  let f : ↥M →* ↥(L ⊓ Subgroup.centralizer {d}) :=
    MonoidHom.codRestrict (C.subtype.comp M.subtype) (L ⊓ Subgroup.centralizer {d}) hfmem
  have hK₀eq : K₀ = (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).comap f := by
    ext m
    exact Iff.rfl
  have hK₀ : IsComponent K₀ := ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eK.symm hKq,
    hK₀eq ▸ hKsub.comap f⟩
  have hK'eq : K₀.map M.subtype = K' := Subgroup.map_subgroupOf_eq_of_le hK'M
  have hO2 : (CFSG.pCore 2 ↥K₀).map eK.toMonoidHom = CFSG.pCore 2 ↥K := CFSG.pCore_map_iso 2 eK
  let eQ : ↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.congr _ _ eK hO2
  have htype' : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 5)) ∨
      (d' ∈ K₀.map M.subtype ∧ Sec4.IsExtOf (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)
        Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3))) := by
    rcases htype with ⟨⟨φ⟩⟩ | ⟨hdK, hext⟩
    · exact Or.inl ⟨eQ.trans φ⟩
    · refine Or.inr ⟨?_, ?_⟩
      · rw [hK'eq]
        exact hdK
      · obtain ⟨N, hN, ⟨e1⟩, ⟨e2⟩⟩ := hext
        have hN' : (N.comap eQ.toMonoidHom).Normal := hN.comap _
        refine ⟨N.comap eQ.toMonoidHom, hN', ⟨?_⟩, ⟨?_⟩⟩
        · exact ((eQ.subgroupMap (N.comap eQ.toMonoidHom)).trans
            (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective
              eQ.surjective N))).trans e1
        · exact (QuotientGroup.congr _ _ eQ (Subgroup.map_comap_eq_self_of_surjective
            eQ.surjective N)).trans e2
  have h1 := h427 ↥C hC4 A' hA' hCE hCθ L' hL' d' hd'A hd'1 hW' K₀ hK₀ htype'
  rw [hK'eq] at h1
  have h' := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_of_le_left hKC, inf_of_le_left hLC] at h'

theorem theta_commutator_le (hGW : Sec6.GWLBalanceStatement) {A Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hM4 : SectionFourHyp ↥(Y ⊔ A)) {d : G}
    (hd : d ∈ A) (hd3 : d ^ 3 = 1) {Yd J : Subgroup G}
    (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hJ : J ∈ thetaComponentsIn Y) (hYdJ : Yd ≤ J) (h3Yd : 3 ∣ Nat.card Yd) :
    ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y := by
  have hYdYC : Yd ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) := le_of_mem_thetaComponentsIn hYd
  obtain ⟨hJY, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  have hYde : Yd ≤ Subgroup.centralizer {d} := hYdYC.trans inf_le_right
  have hYn : (Y.subgroupOf (Y ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hAY)
  have hJYA : J ∈ thetaComponentsIn (Y ⊔ A) :=
    Sec6.mem_thetaComponentsIn_of (hJY.trans le_sup_left) (isPerfect_of_mem_thetaComponentsIn hJ)
      (isSubnormal_subgroupOf_trans148 hJY le_sup_left hJ'.2.1 hYn.isSubnormal)
      (Sec6.isQuasisimple_of_mem_thetaComponentsIn hJ)
  have hYdsubJ : (Yd.subgroupOf (J ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hYd).2.2.1
    have hle' : J ⊓ Subgroup.centralizer {d} ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) :=
      inf_le_inf_right _ hJY
    have h2 := h1.comap (Subgroup.inclusion hle')
    have heq : (Yd.subgroupOf (Y ⊓ Subgroup.centralizer ({d} : Set G))).comap
        (Subgroup.inclusion hle') = Yd.subgroupOf (J ⊓ Subgroup.centralizer {d}) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  have hB3 := Sec6.bThreeProperty_of_three_dvd hGW hM4 hJYA (Subgroup.mem_sup_right hd) hd3
    (le_inf hYdJ hYde) (isPerfect_of_mem_thetaComponentsIn hYd) hYdsubJ
    (Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd) h3Yd
  refine hB3.trans ((Sec13.inSubgroup_theta_le_of_isSubnormal hJY hJ'.2.1).trans ?_)
  exact inSubgroup_theta_le_pPrimeCoreOf Y

theorem ydAlpha_facts {A Y : Subgroup G} [(ker148 A Y).Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {d : G} (hd : d ∈ A) (hd3 : d ^ 3 = 1)
    {Yd J : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hJ : J ∈ thetaComponentsIn Y) (hYdJ : Yd ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (h3Yd : 3 ∣ Nat.card Yd)
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y) :
    img148 A Y Yd ≤ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y d hd} ∧
      ((img148 A Y Yd).subgroupOf
        (img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y d hd})).IsSubnormal ∧
      Group.IsPerfect ↥(img148 A Y Yd) ∧
      aschbacherSolvableCore 3 ↥(img148 A Y Yd) ≤ Subgroup.center ↥(img148 A Y Yd) ∧
      Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃*
        ↥(img148 A Y Yd) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y Yd)) := by
  have hYdYC : Yd ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) := le_of_mem_thetaComponentsIn hYd
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  have hYde : Yd ≤ Subgroup.centralizer {d} := hYdYC.trans inf_le_right
  have hYdp : Group.IsPerfect Yd := isPerfect_of_mem_thetaComponentsIn hYd
  have hYdq : IsQuasisimple (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsIn hYd
  have hYdαp : Group.IsPerfect ↥(img148 A Y Yd) := isPerfect_img148 hYdM
  have hCJ := img148_inf_centralizer_alpha148 hAY hJM hAJ hd hd3
  have hYdsubJ : (Yd.subgroupOf (J ⊓ Subgroup.centralizer {d})).IsSubnormal := by
    have h1 := (mem_thetaComponentsIn_iff.mp hYd).2.2.1
    have hle' : J ⊓ Subgroup.centralizer {d} ≤ Y ⊓ Subgroup.centralizer ({d} : Set G) :=
      inf_le_inf_right _ hJY
    have h2 := h1.comap (Subgroup.inclusion hle')
    have heq : (Yd.subgroupOf (Y ⊓ Subgroup.centralizer ({d} : Set G))).comap
        (Subgroup.inclusion hle') = Yd.subgroupOf (J ⊓ Subgroup.centralizer {d}) := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h2
  have hle : img148 A Y Yd ≤ img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y d hd} := by
    rw [hCJ]
    exact img148_mono (le_inf hYdJ hYde)
  have hsub : ((img148 A Y Yd).subgroupOf
      (img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y d hd})).IsSubnormal := by
    rw [hCJ]
    exact isSubnormal_img148 (le_inf hYdJ hYde) (inf_le_left.trans hJM) hYdsubJ
  set ψ : ↥Yd →* ↥(img148 A Y Yd) :=
    (MulEquiv.subgroupCongr (range_phi148 (A := A) (Y := Y) hYdM)).toMonoidHom.comp
      (phi148 (A := A) (Y := Y) hYdM).rangeRestrict with hψ
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨w, hw⟩ := (phi148 (A := A) (Y := Y) hYdM).rangeRestrict_surjective
      ((MulEquiv.subgroupCongr (range_phi148 (A := A) (Y := Y) hYdM)).symm z)
    refine ⟨w, ?_⟩
    rw [hψ, MonoidHom.comp_apply, hw, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  have hψone : ∀ k : ↥Yd, ψ k = 1 ↔ (k : G) ∈ pPrimeCoreOf 3 Y := by
    intro k
    rw [← phi148_eq_one_iff hYdM k, hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (MulEquiv.injective _), ← Subtype.coe_inj]
    rfl
  have hψker : ψ.ker = (phi148 (A := A) (Y := Y) hYdM).ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψone, phi148_eq_one_iff]
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := by
    rw [hψker]
    exact not_three_dvd_card_ker_phi148 hYdM
  have hYdα1 : Nontrivial ↥(img148 A Y Yd) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hker3
    have htop : ψ.ker = ⊤ := by
      rw [eq_top_iff]
      intro k _
      exact Subsingleton.elim _ _
    rw [htop, Subgroup.card_top]
    exact h3Yd
  have hkerθ : ψ.ker ≤ aschbacherSolvableCore 3 ↥Yd := by
    rcases ker_le_theta_or_subsingleton ψ hψs hYdαp hYdq hker3 with hle' | hsub'
    · exact hle'
    · exact absurd hsub' (not_subsingleton_iff_nontrivial.mpr hYdα1)
  obtain ⟨hθeq, ⟨η⟩⟩ := theta_quot_of_ker_le ψ hψs hkerθ hker3
  refine ⟨hle, hsub, hYdαp, ?_, ⟨η⟩⟩
  rw [hθeq]
  rintro _ ⟨t, ht, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro w
  obtain ⟨y, rfl⟩ := hψs w
  have hcomm : ((t : G) * y * (t : G)⁻¹ * (y : G)⁻¹) ∈ pPrimeCoreOf 3 Y := by
    refine hθ ?_
    have htθ : (t : G) ∈ inSubgroup (aschbacherSolvableCore 3) Yd := ⟨t, ht, rfl⟩
    exact Subgroup.commutator_mem_commutator htθ y.2
  have h1 : ψ (t * y * t⁻¹ * y⁻¹) = 1 := (hψone _).mpr (by simpa using hcomm)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem false_of_outer_a5_on
    (h427 : Sec4.Item4_27)
    (h41 : Sec4.Item4_1LargePrime) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A) (hs : ¬ Group.IsSolvable ↥Y) {d : G} (hd : d ∈ A)
    (hd1 : d ≠ 1)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    {Yd J : Subgroup G} (hYd : Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)))
    (hJ : J ∈ thetaComponentsIn Y) (hYdJ : Yd ≤ J) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (h3J : 3 ∣ Nat.card J) (h3Yd : 3 ∣ Nat.card Yd)
    (hθ : ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y)
    (htype : Nonempty (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd ≃* alternatingGroup (Fin 5)) ∨
      (d ∈ Yd ∧ Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd)
        CFSG.Blueprint.NativeSporadic.ON))
    (hdc : d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y)) : False := by
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hd3 : d ^ 3 = 1 := hA3 d hd
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hYdM : Yd ≤ Y ⊔ A := hYdJ.trans hJM
  obtain ⟨hKle, hKsub, hKp, hKθ, ⟨η⟩⟩ := ydAlpha_facts hY.2 hd hd3 hYd hJ hYdJ hAJ h3Yd hθ
  have : Group.IsPerfect ↥(img148 A Y Yd) := hKp
  have hKq_type : IsQuasisimple ↥(img148 A Y Yd) ∧
      (Nonempty (↥(img148 A Y Yd) ⧸ CFSG.pCore 2 ↥(img148 A Y Yd) ≃* alternatingGroup (Fin 5)) ∨
        (alpha148 A Y d hd ∈ img148 A Y Yd ∧
          Sec4.IsExtOf (↥(img148 A Y Yd) ⧸ CFSG.pCore 2 ↥(img148 A Y Yd))
            Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3)))) := by
    rcases htype with ⟨⟨φ⟩⟩ | ⟨hdYd, hON⟩
    · obtain ⟨hq, hO2⟩ := a5Type_of_central hKθ ⟨η.symm.trans φ⟩
      exact ⟨hq, Or.inl hO2⟩
    · obtain ⟨hq, hO2⟩ := onType_of_central hKθ (KFacts.KS14.isTripleCover_congr η hON)
      exact ⟨hq, Or.inr ⟨mem_img148_iff.mpr ⟨d, Subgroup.mem_sup_right hd, hdYd, rfl⟩,
        hO2.isExtOf⟩⟩
  obtain ⟨hKq, htype'⟩ := hKq_type
  obtain ⟨hJq, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨hC4, hCE⟩ := hyp429In148_of h41 G A c L h Y hY hs J hJ hAJ h3J
  have hCeq : img148 A Y (J ⊔ A) = img148 A Y J ⊔ img148 A Y A := img148_sup hJM le_sup_right
  have hAαJα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAα3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥(img148 A Y (J ⊔ A)) = ⊥ := by
    rw [hCeq]
    exact aschbacherSolvableCore_sup_eq_bot hAαJα hAα3 hJθ
  have hAC : img148 A Y A ≤ img148 A Y (J ⊔ A) := img148_mono le_sup_right
  have hLC : img148 A Y J ≤ img148 A Y (J ⊔ A) := img148_mono le_sup_left
  have hLn : img148 A Y (J ⊔ A) ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαJα
  have hA3' : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hWα : ∀ g ∈ img148 A Y (J ⊔ A),
      g ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      g ∈ Subgroup.normalizer
        (Subgroup.zpowers (alpha148 A Y d hd) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun g _ hg => mem_normalizer_alpha_of hA3' hd hW hg
  have heq := item4_27_of_le h427 (img148 A Y (J ⊔ A)) hC4 hCθ hCE hAC hLC (img148_isE27 hA)
    (alpha148_mem_img148 hd) (alpha148_ne_one hd hd1 hd3) hWα hJq hLn hKle hKq hKsub htype'
  apply hdc
  refine ⟨hd, fun j hj => ?_⟩
  have hjM : j ∈ Y ⊔ A := hJM hj
  have hjα : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ ∈ img148 A Y Yd := by
    rw [heq]
    exact mem_img148_iff.mpr ⟨j, hjM, hj, rfl⟩
  have hc' := Subgroup.mem_centralizer_singleton_iff.mp (hKle hjα).2
  have hdM : d ∈ Y ⊔ A := Subgroup.mem_sup_right hd
  have hmem : d * j * d⁻¹ * j⁻¹ ∈ Y ⊔ A :=
    (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hdM hjM) ((Y ⊔ A).inv_mem hdM))
      ((Y ⊔ A).inv_mem hjM)
  have h1 : QuotientGroup.mk' (ker148 A Y) (⟨d * j * d⁻¹ * j⁻¹, hmem⟩ : ↥(Y ⊔ A)) = 1 := by
    have e : (⟨d * j * d⁻¹ * j⁻¹, hmem⟩ : ↥(Y ⊔ A)) =
        ⟨d, hdM⟩ * ⟨j, hjM⟩ * (⟨d, hdM⟩)⁻¹ * (⟨j, hjM⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← alpha148_eq_mk', mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul, hc']
  exact mk'_ker148_eq_one_iff.mp h1

end HJRes148

open HJRes148 Res148 Main148

@[expose] def KF148HJA6Outer : Prop :=
  ∀ (Γ : Type) [Group Γ] [Finite Γ] (C : Subgroup Γ), SectionFourHyp ↥C →
    aschbacherSolvableCore 3 ↥C = ⊥ → partTwoE ↥C = partTwoF ↥C →
    ∀ (A L K : Subgroup Γ) (d : Γ), Late.IsE27 A → L ⊔ A = C → d ∈ A → d ≠ 1 →
      (∀ g ∈ C, g ∈ Subgroup.normalizer (A : Set Γ) →
        g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set Γ)) →
      IsQuasisimple ↥L → C ≤ Subgroup.normalizer (L : Set Γ) →
      ¬ L ≤ Subgroup.centralizer {d} → K ≤ L ⊓ Subgroup.centralizer {d} →
      (K.subgroupOf (L ⊓ Subgroup.centralizer {d})).IsSubnormal → IsQuasisimple ↥K →
      A ≤ Subgroup.normalizer (K : Set Γ) →
      Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K) (alternatingGroup (Fin 6)) →
      Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
        Nonempty (↥L ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
        Sec4.IsTripleCover ↥L CFSG.Blueprint.NativeSporadic.ON

section Certificates

@[expose] def Step148HJTypeJOuterA6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
    Ind148 A (lB A) Y → ∀ B : Subgroup G, IsHyperplane A B → ¬ YBOne A (lB A) Y B →
    ∀ YB ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer (B : Set G)),
      (Sec4.IsTripleCover (↥YB ⧸ aschbacherSolvableCore 3 ↥YB) (alternatingGroup (Fin 6)) ∨
        Nonempty (↥YB ⧸ aschbacherSolvableCore 3 ↥YB ≃* alternatingGroup (Fin 5))) →
      deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G)) ≤
        pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) ⊔ YB →
      ∀ (b d : G) (Lb : Subgroup G), IsLBConfig A B b d Lb →
      YB ≤ pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔ lB A B →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      ∀ Yd ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({d} : Set G)), YB ≤ Yd →
        A ≤ Subgroup.normalizer (Yd : Set G) →
        Sec4.IsTripleCover (↥Yd ⧸ aschbacherSolvableCore 3 ↥Yd) (alternatingGroup (Fin 6)) →
        ⁅inSubgroup (aschbacherSolvableCore 3) Yd, Yd⁆ ≤ pPrimeCoreOf 3 Y →
      ∀ J ∈ thetaComponentsIn Y, Yd ≤ J → A ≤ Subgroup.normalizer (J : Set G) →
        3 ∣ Nat.card J → d ∉ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) →
      letI := ker148_normal hY.2
      (Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 5)) ∨
          Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
          Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M24) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) (alternatingGroup (Fin 6)) ∨
          Sec4.IsTripleCover ↥(img148 A Y J) CFSG.Blueprint.NativeSporadic.ON) ∨
        (Case148Two A (lB A) Y ∨ Case148Three A (lB A) Y ∨ Case148Six A (lB A) Y)

theorem step148HJTypeJOuter_of_a6
    (h427 : Sec4.Item4_27)
    (hGW : Sec6.GWLBalanceStatement) (h41 : Sec4.Item4_1LargePrime) (h134 : Item134)
    (h48 : Sec4.Item4_8) (hA6 : Step148HJTypeJOuterA6) : Step148HJTypeJOuter := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle Yd hYd hYBYd hAYd hYdt J
    hJ hYdJ hAJ h3J hdc
  let := ker148_normal hY.2
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hd : d ∈ A := hB.1 hdB
  have hd3 : d ^ 3 = 1 := hA.1.2 d hd
  have hW := normalizer_le_normalizer_zpowers_d h134 h48 h hB hc
  have hMtop : Y ⊔ A ≠ ⊤ := by
    intro htop
    have hMN : Y ⊔ A ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hY.2
    have : IsSimpleGroup G := h.isSimpleGroup
    have hYn : Y.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (htop ▸ hMN))
    rcases hYn.eq_bot_or_eq_top with hY1 | hYt
    · apply hs
      rw [hY1]
      infer_instance
    · exact hY.1 hYt
  have hM4 : SectionFourHyp ↥(Y ⊔ A) := h.toTheoremFourHyp.sectionFourHyp hMtop
  have h3Yd : 3 ∣ Nat.card Yd := three_dvd_card_of_ydType148 hYdt
  have hθ := theta_commutator_le hGW hY.2 hM4 hd hd3 hYd hJ hYdJ h3Yd
  rcases hYdt with hA5 | hA6' | ⟨hdYd, hON⟩
  · exact (false_of_outer_a5_on h427 h41 h hY hs hd hd1 hW hYd hJ hYdJ hAJ h3J h3Yd hθ
      (Or.inl hA5) hdc).elim
  · exact hA6 G A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle hW Yd hYd hYBYd hAYd
      hA6' hθ J hJ hYdJ hAJ h3J hdc
  · exact (false_of_outer_a5_on h427 h41 h hY hs hd hd1 hW hYd hJ hYdJ hAJ h3J h3Yd hθ
      (Or.inr ⟨hdYd, hON⟩) hdc).elim

theorem step148HJTypeJOuterA6_of_kf (hKF : KF148HJA6Outer) (h41 : Sec4.Item4_1LargePrime) :
    Step148HJTypeJOuterA6 := by
  intro G _ _ A c L h Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle hW Yd hYd hYBYd hAYd
    hA6 hθ J hJ hYdJ hAJ h3J hdc
  let := ker148_normal hY.2
  left
  have hA : Late.IsE27 A := h.isE27
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  obtain ⟨-, hdB, -, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hd : d ∈ A := hB.1 hdB
  have hd3 : d ^ 3 = 1 := hA3 d hd
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have h3Yd : 3 ∣ Nat.card Yd := three_dvd_card_of_ydType148 (d := d) (Or.inr (Or.inl hA6))
  obtain ⟨hKle, hKsub, hKp, hKθ, ⟨η⟩⟩ := ydAlpha_facts hY.2 hd hd3 hYd hJ hYdJ hAJ h3Yd hθ
  have : Group.IsPerfect ↥(img148 A Y Yd) := hKp
  have hA6α : Sec4.IsTripleCover (↥(img148 A Y Yd) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y Yd))
      (alternatingGroup (Fin 6)) := KFacts.KS14.isTripleCover_congr η hA6
  have hKq : IsQuasisimple ↥(img148 A Y Yd) := by
    set θ := aschbacherSolvableCore 3 ↥(img148 A Y Yd)
    have hθn : θ.Normal := Subgroup.normal_of_le_center hKθ
    obtain ⟨hZ3, ⟨eT⟩⟩ := hA6α
    have hTp : Group.IsPerfect (↥(img148 A Y Yd) ⧸ θ) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective θ)
    have hA6s : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    have hTs : IsSimpleGroup ((↥(img148 A Y Yd) ⧸ θ) ⧸ Subgroup.center (↥(img148 A Y Yd) ⧸ θ)) :=
      eT.isSimpleGroup
    have hnc : ∃ a b : (↥(img148 A Y Yd) ⧸ θ) ⧸ Subgroup.center (↥(img148 A Y Yd) ⧸ θ),
        a * b ≠ b * a := by
      refine ⟨eT.symm ⟨Equiv.swap 0 1 * Equiv.swap 1 2,
          Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
        eT.symm ⟨Equiv.swap 1 2 * Equiv.swap 2 3,
          Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩, fun h0 => ?_⟩
      have h1 := congrArg (fun z => ((eT z : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) h0
      simp only [map_mul, MulEquiv.apply_symm_apply, Subgroup.coe_mul] at h1
      revert h1
      decide
    exact (CFSG.LocalCores.isQuasisimple_iff_of_surjective hKp (QuotientGroup.mk' θ)
      (QuotientGroup.mk'_surjective θ) (by rwa [QuotientGroup.ker_mk'])).mpr ⟨hTp, hTs, hnc⟩
  obtain ⟨hJq, hJθ⟩ := img148_isQuasisimple (A := A) (Y := Y) hJ h3J
  obtain ⟨hC4, hCE⟩ := hyp429In148_of h41 G A c L h Y hY hs J hJ hAJ h3J
  have hCeq : img148 A Y (J ⊔ A) = img148 A Y J ⊔ img148 A Y A := img148_sup hJM le_sup_right
  have hAαJα : img148 A Y A ≤ Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    img148_le_normalizer hAJ
  have hAα3 : ∀ a ∈ img148 A Y A, a ^ 3 = 1 := (img148_isE27 hA).1.2
  have hCθ : aschbacherSolvableCore 3 ↥(img148 A Y (J ⊔ A)) = ⊥ := by
    rw [hCeq]
    exact aschbacherSolvableCore_sup_eq_bot hAαJα hAα3 hJθ
  have hLn : img148 A Y (J ⊔ A) ≤
      Subgroup.normalizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
    rw [hCeq]
    exact sup_le Subgroup.le_normalizer hAαJα
  have hA3' : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hA.2]; norm_num)
  have hWα : ∀ g ∈ img148 A Y (J ⊔ A),
      g ∈ Subgroup.normalizer (img148 A Y A : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) →
      g ∈ Subgroup.normalizer
        (Subgroup.zpowers (alpha148 A Y d hd) : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) :=
    fun g _ hg => mem_normalizer_alpha_of hA3' hd hW hg
  have hnc : ¬ img148 A Y J ≤ Subgroup.centralizer {alpha148 A Y d hd} := by
    intro hJc
    apply hdc
    refine ⟨hd, fun j hj => ?_⟩
    have hjM : j ∈ Y ⊔ A := hJM hj
    have hjα : QuotientGroup.mk' (ker148 A Y) ⟨j, hjM⟩ ∈ img148 A Y J :=
      mem_img148_iff.mpr ⟨j, hjM, hj, rfl⟩
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp (hJc hjα)
    have hdM : d ∈ Y ⊔ A := Subgroup.mem_sup_right hd
    have hmem : d * j * d⁻¹ * j⁻¹ ∈ Y ⊔ A :=
      (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem hdM hjM) ((Y ⊔ A).inv_mem hdM))
        ((Y ⊔ A).inv_mem hjM)
    have h1 : QuotientGroup.mk' (ker148 A Y) (⟨d * j * d⁻¹ * j⁻¹, hmem⟩ : ↥(Y ⊔ A)) = 1 := by
      have e : (⟨d * j * d⁻¹ * j⁻¹, hmem⟩ : ↥(Y ⊔ A)) =
          ⟨d, hdM⟩ * ⟨j, hjM⟩ * (⟨d, hdM⟩)⁻¹ * (⟨j, hjM⟩)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← alpha148_eq_mk', mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul, hc']
    exact mk'_ker148_eq_one_iff.mp h1
  rcases hKF _ (img148 A Y (J ⊔ A)) hC4 hCθ hCE (img148 A Y A) (img148 A Y J) (img148 A Y Yd)
      (alpha148 A Y d hd) (img148_isE27 hA) hCeq.symm (alpha148_mem_img148 hd)
      (alpha148_ne_one hd hd1 hd3) hWα hJq hLn hnc hKle hKsub hKq (img148_le_normalizer hAYd)
      hA6α with hJ2 | hM24 | hON
  · exact Or.inr (Or.inl hJ2)
  · exact Or.inr (Or.inr (Or.inl hM24))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hON)))

end Certificates

end CFSG.RankThree.PartTwo.Sec14
