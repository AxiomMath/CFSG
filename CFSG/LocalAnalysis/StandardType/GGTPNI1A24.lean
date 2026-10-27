module

public import CFSG.LocalAnalysis.StandardType.GGTPNI1
public import CFSG.LocalAnalysis.StandardType.GGTPNSL6Bridge
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.RankThree.PartTwo.KFacts.KS12SLCenter
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.GGHalf Matrix

private theorem tpa24_inLambda2_a51 : LargeEvenInLambda2 (⟨.A, 5, 1⟩ : LargeEvenLabel) := by
  simp [LargeEvenInLambda2]

private theorem tpa24_center_sl6_eq_bot :
    Subgroup.center (SpecialLinearGroup (Fin 6) F2) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨c, hc, hcz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  have hc01 : c = 0 ∨ c = 1 := by
    have hcard : Nat.card F2 = 2 := by
      simpa using GaloisField.card 2 1 (by omega)
    by_cases h0 : c = 0
    · exact Or.inl h0
    · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
      exact Or.inr ((huniq c h0).trans (huniq 1 one_ne_zero).symm)
  rcases hc01 with h0 | h1
  · rw [h0] at hc
    norm_num at hc
  · rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hcz, h1]
    simp

private theorem tpa24_conj_injective {G : Type*} [Group G]
    (hZ : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [Subgroup.mem_bot]
  have hxc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun f : MulAut G => f y) hx
    rw [MulAut.one_apply, MulAut.conj_apply] at h
    have h' : x * y = y * x := by
      have := congrArg (fun t => t * x) h
      simpa [mul_assoc] using this
    exact h'.symm
  rw [hZ, Subgroup.mem_bot] at hxc
  exact hxc

private theorem tpa24_centerQuotAut_conj {X : Type} [Group X] (g : X) :
    centerQuotAut X (MulAut.conj g : MulAut X) =
      MulAut.conj (QuotientGroup.mk g : X ⧸ Subgroup.center X) := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  simp [centerQuotAut_mk, MulAut.conj_apply]

private theorem tpa24_ggInducedAut_conj {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (g : X) :
    ggInducedAut θ (MulAut.conj g : MulAut X) =
      MulAut.conj (θ (g : X ⧸ Subgroup.center X)) := by
  change MulAut.congr θ (centerQuotAut X (MulAut.conj g)) =
    MulAut.conj (θ (g : X ⧸ Subgroup.center X))
  rw [tpa24_centerQuotAut_conj, mulAut_congr_conj]

private theorem tpa24_mem_A_inner {X : Type} [Group X] {R : Type} [Group R]
    (hperf : commutator X = ⊤) (θ : X ⧸ Subgroup.center X ≃* R) {I : Set (MulAut R)}
    (hI : I ⊆ LargeEvenInnSet R) {A : Subgroup (MulAut X)} (hind : GGInducedInn A θ I) :
    A ≤ (MulAut.conj : X →* MulAut X).range := by
  rintro a ha
  have h1 : ggInducedAut θ a ∈ I := hind a ha
  obtain ⟨r, hr⟩ := hI h1
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (θ.symm r)
  refine ⟨g, ?_⟩
  apply ggInducedAut_injective_of_perfect hperf θ
  have hgr : θ (g : X ⧸ Subgroup.center X) = r := by
    rw [show (g : X ⧸ Subgroup.center X) = θ.symm r from hg, MulEquiv.apply_symm_apply]
  rw [tpa24_ggInducedAut_conj, hgr]
  exact hr

private theorem tpa24_eq_A51_of_ggLabelIso {lab : LargeEvenLabel}
    (hiso : GGLabelIso lab ⟨.A, 5, 1⟩) : lab = ⟨.A, 5, 1⟩ := by
  rcases hiso with h | h | h | h | h | h | h | h
  · exact h
  · exact absurd h.2.1 (by decide)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.rank h.2) (by simp)
  · exact absurd (congrArg LargeEvenLabel.tag h.1) (by decide)

theorem ggI1PairRankOn_A24 :
    GGI1PairRankOn GGPairA24 := by
  intro p hp hp2 L _ _ J y E labL labJ hΛL hΛJ hP hhasL hhasJ hy hyE hEab hcomp hfix hmark
  obtain ⟨hp3, hlabL, hlabJ⟩ := hP
  subst hp3
  subst hlabL
  subst hlabJ
  obtain ⟨hperf, lab, hΛlab, hraw⟩ := hmark
  have hhas_lab : GGHasLabel lab (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F hq => by
      obtain ⟨-, -, hθ⟩ := hq
      obtain ⟨θ, -⟩ := hθ
      exact ⟨θ⟩) hraw
  have hiso := ggLabelRigidInput_holds lab ⟨.A, 5, 1⟩ (L ⧸ Subgroup.center L)
    hΛlab tpa24_inLambda2_a51 hhas_lab hhasL
  have hlab : lab = ⟨.A, 5, 1⟩ := tpa24_eq_A51_of_ggLabelIso hiso
  subst hlab
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hKfield, hKfin, hKcard, hQR⟩ := hraw
  letI : Field K := hKfield
  letI : Finite K := hKfin
  obtain ⟨-, -, hθ⟩ := hQR
  obtain ⟨θ, hind⟩ := hθ
  have hKcard2 : Nat.card K = 2 := by simpa using hKcard
  have hcardu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hKcard2]
  have hI : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 6) K)) Set.univ ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin 6) K)) :=
    matConjImage_gl_subset_inn (K := K) (d := 6) (by rw [hcardu]; exact Nat.coprime_one_left 6)
  have hEinner : E ≤ (MulAut.conj : L →* MulAut L).range :=
    tpa24_mem_A_inner hperf θ hI hind
  have hhasTop : GGHasLabel ⟨.A, 5, 1⟩
      ((⊤ : Subgroup L) ⧸ Subgroup.center (⊤ : Subgroup L)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.topEquiv (G := L)).symm hhasL
  have hmodTop : CFSG.Open.StatedClassicalModel
      ((⊤ : Subgroup L) ⧸ Subgroup.center (⊤ : Subgroup L)) .PSL 6 2 1 :=
    statedClassicalModel_of_hasLabel_typeA tpa24_inLambda2_a51 hhasTop
  have hperfTop : commutator ↥(⊤ : Subgroup L) = ⊤ := by
    haveI : Group.IsPerfect L := ⟨hperf⟩
    haveI : Group.IsPerfect ↥(⊤ : Subgroup L) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := L)).symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨φ, hφrange, hφinj⟩ := GGHalf.exists_slLift_two (m := 3) (by norm_num) hperfTop hmodTop
  let ψ : L ≃* SpecialLinearGroup (Fin 6) F2 :=
    (MulEquiv.ofBijective φ ⟨hφinj, MonoidHom.range_eq_top.mp hφrange⟩).symm
  have hZL : Subgroup.center L = ⊥ :=
    CFSG.RankThree.PartTwo.KFacts.center_eq_bot_of_mulEquiv ψ tpa24_center_sl6_eq_bot
  have hconj_inj : Function.Injective (MulAut.conj : L →* MulAut L) := tpa24_conj_injective hZL
  intro e he
  obtain ⟨g, hg⟩ := hEinner he
  obtain ⟨y₀, hy₀⟩ := hEinner hyE
  have hy03 : y₀ ^ 3 = 1 := hconj_inj (by
    show MulAut.conj (y₀ ^ 3) = MulAut.conj 1
    rw [map_pow, hy₀, hEab.2 y hyE, map_one])
  let t : SpecialLinearGroup (Fin 6) F2 := ψ y₀
  have ht3 : t ^ 3 = 1 := by
    change (ψ y₀) ^ 3 = 1
    rw [← map_pow, hy03, map_one]
  have hJ' : GGHasLabel ⟨.A, 2, 2⟩
      (J.map ψ.toMonoidHom ⧸ Subgroup.center (J.map ψ.toMonoidHom)) :=
    ggHasLabel_quotCenter_of_mulEquiv
      (Subgroup.equivMapOfInjective J ψ.toMonoidHom ψ.injective) hhasJ
  have hcent0 : Subgroup.centralizer ({y₀} : Set L) = ggAutFixedSubgroup y := by
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, mem_ggAutFixedSubgroup]
    constructor
    · intro hz
      rw [← hy₀, MulAut.conj_apply, show y₀ * z = z * y₀ from hz.symm]
      group
    · intro hz
      have h1 : MulAut.conj y₀ z = z := by rw [hy₀]; exact hz
      rw [MulAut.conj_apply] at h1
      calc z * y₀ = (y₀ * z * y₀⁻¹) * y₀ := by rw [h1]
        _ = y₀ * z := by group
  have hJcomp0 : IsComponentOf J (Subgroup.centralizer ({y₀} : Set L)) := by
    rw [hcent0]; exact hcomp
  have hJ'comp : IsComponentOf (J.map ψ.toMonoidHom)
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 6) F2))) := by
    have hcentψ : Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 6) F2)) =
        (Subgroup.centralizer ({y₀} : Set L)).map ψ.toMonoidHom := by
      have hle : Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin 6) F2)) ≤
          ψ.toMonoidHom.range := by
        rw [MonoidHom.range_eq_top.mpr ψ.surjective]; exact le_top
      change Subgroup.centralizer ({ψ y₀} : Set (SpecialLinearGroup (Fin 6) F2)) =
        (Subgroup.centralizer ({y₀} : Set L)).map ψ.toMonoidHom
      rw [TagsExc.centralizer_singleton_eq_comap ψ y₀, Subgroup.map_comap_eq_self hle]
    rw [hcentψ]
    exact isComponentOf_map_of_injective ψ.toMonoidHom ψ.injective hJcomp0
  have hMcent : ∀ j ∈ J.map ψ.toMonoidHom, (ψ g) * j = j * (ψ g) := by
    intro j hj
    obtain ⟨j₀, hj₀, rfl⟩ := Subgroup.mem_map.mp hj
    have h1 : MulAut.conj g j₀ = j₀ := by
      have := hfix e he j₀ hj₀
      rwa [← hg] at this
    rw [MulAut.conj_apply] at h1
    have hcomm : g * j₀ = j₀ * g := by
      calc g * j₀ = (g * j₀ * g⁻¹) * g := by group
        _ = j₀ * g := by rw [h1]
    have h2 : ψ g * ψ j₀ = ψ j₀ * ψ g := by rw [← map_mul, ← map_mul, hcomm]
    simpa using h2
  have hMmem := (sl6b_component_commutant ht3 hJ'comp hJ') (ψ g) hMcent
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hMmem
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have hgk : y₀ ^ k = g := ψ.injective (by rw [map_zpow]; exact hk)
  rw [← hg, ← hgk, map_zpow, hy₀]

end CFSG.StandardType

end
