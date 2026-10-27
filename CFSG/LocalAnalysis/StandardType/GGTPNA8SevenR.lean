module

public import CFSG.LocalAnalysis.StandardType.GGTPNA8Seven
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGSL9TwoProj
public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeHypSix
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVPComp
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsExcBasic
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.StandardType.GGHalf (F2)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem tpa8r_isElemAbelian_map {G H : Type*} [Group G] [Group H] {p : ℕ}
    {E : Subgroup G} (f : G →* H) (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  obtain ⟨hc, hp⟩ := hE
  refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
  · obtain ⟨x, hx, hxu⟩ := u.2
    obtain ⟨y, hy, hyv⟩ := v.2
    apply Subtype.ext
    change (u : H) * v = v * u
    rw [← hxu, ← hyv, ← map_mul, ← map_mul, Subgroup.mul_comm_of_mem_isMulCommutative E hx hy]
  · obtain ⟨x, hx, rfl⟩ := hz
    rw [← map_pow, hp x hx, map_one]

private theorem tpa8r_center_eq_bot_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hH : Subgroup.center H = ⊥) : Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzH : e z ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := e.surjective w
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz) y]
  rw [hH, Subgroup.mem_bot] at hzH
  exact e.injective (by rw [hzH, map_one])

private theorem tpa8r_conj_injective {G : Type*} [Group G]
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

private theorem tpa8r_centerQuotAut_conj {X : Type} [Group X] (g : X) :
    centerQuotAut X (MulAut.conj g : MulAut X) =
      MulAut.conj (QuotientGroup.mk g : X ⧸ Subgroup.center X) := by
  ext q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  simp [centerQuotAut_mk, MulAut.conj_apply]

private theorem tpa8r_ggInducedAut_conj {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (g : X) :
    ggInducedAut θ (MulAut.conj g : MulAut X) =
      MulAut.conj (θ (g : X ⧸ Subgroup.center X)) := by
  change MulAut.congr θ (centerQuotAut X (MulAut.conj g)) =
    MulAut.conj (θ (g : X ⧸ Subgroup.center X))
  rw [tpa8r_centerQuotAut_conj, mulAut_congr_conj]

private theorem tpa8r_mem_A_inner {X : Type} [Group X] {R : Type} [Group R]
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
  rw [tpa8r_ggInducedAut_conj, hgr]
  exact hr

private theorem tpa8r_inLambda2_a23 : LargeEvenInLambda2 ⟨.A, 2, 3⟩ := by simp [LargeEvenInLambda2]
private theorem tpa8r_inLambda2_a51 : LargeEvenInLambda2 ⟨.A, 5, 1⟩ := by simp [LargeEvenInLambda2]
private theorem tpa8r_row_a23_a8 : GGTablePRow 7 ⟨.A, 2, 3⟩ ⟨.A, 8, 1⟩ := by
  simp only [GGTablePRow]; norm_num
private theorem tpa8r_row_a51_a8 : GGTablePRow 7 ⟨.A, 5, 1⟩ ⟨.A, 8, 1⟩ := by
  simp only [GGTablePRow]; norm_num

private theorem tpa8r_E0inf {X G : Type} [Group X] [Group G]
    (ρ : X ≃* G) (σ : MulAut X) (A : Subgroup (MulAut X)) (J : Subgroup X)
    (Aρ : Subgroup (MulAut G)) (E₀ J₀ : Subgroup G) (x : G) (x₀ : X)
    (hAρ : Aρ = A.map (MulAut.congr ρ).toMonoidHom)
    (hE0 : E₀ = Aρ.comap (MulAut.conj : G →* MulAut G))
    (hJ0 : J₀ = J.map ρ.toMonoidHom)
    (hx : x = ρ x₀)
    (hx₀ : MulAut.conj x₀ = σ)
    (hconj_x : MulAut.conj x = MulAut.congr ρ σ)
    (hconj_inj : Function.Injective (MulAut.conj : G →* MulAut G))
    (hAρ_le : ∀ a ∈ Aρ, ∀ j ∈ J₀, a j ∈ J₀)
    (hAonly : ∀ a ∈ A, (∀ j ∈ J, a j = j) → a ∈ Subgroup.zpowers σ)
    (hJcomp : IsComponentOf J (ggAutFixedSubgroup σ))
    (hxE : x ∈ E₀)
    (hcent : Subgroup.centralizer ({x} : Set G) = (ggAutFixedSubgroup σ).map ρ.toMonoidHom) :
    E₀ ⊓ Subgroup.centralizer (J₀ : Set G) = Subgroup.zpowers x := by
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgE, hgC⟩ := hg
    have hgA : (MulAut.conj g : MulAut G) ∈ Aρ := by
      rw [hE0] at hgE
      exact Subgroup.mem_comap.mp hgE
    rw [hAρ] at hgA
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hgA
    have haeq' : (MulAut.congr ρ) a = MulAut.conj g := by simpa using haeq
    have hact : ∀ j ∈ J, a j = j := by
      intro j hj
      have hρj : ρ j ∈ J₀ := by
        rw [hJ0]
        exact Subgroup.mem_map_of_mem ρ.toMonoidHom hj
      have h1 : (MulAut.conj g : MulAut G) (ρ j) = ρ j := by
        have hcomm : ρ j * g = g * ρ j := Subgroup.mem_centralizer_iff.mp hgC (ρ j) hρj
        rw [MulAut.conj_apply, hcomm.symm, mul_assoc, mul_inv_cancel, mul_one]
      have h2 : ρ (a j) = ρ j := by
        have h3 : (MulAut.congr ρ a) (ρ j) = ρ (a j) := by simp [MulAut.congr_apply]
        rw [← h3, haeq']
        exact h1
      exact ρ.injective h2
    have hconj_z : MulAut.conj g ∈
        (Subgroup.zpowers σ).map (MulAut.congr ρ).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, hAonly a ha hact, haeq'⟩
    rw [MonoidHom.map_zpowers] at hconj_z
    have hfx : (MulAut.congr ρ).toMonoidHom σ = MulAut.conj x := by
      rw [hconj_x]; rfl
    rw [hfx] at hconj_z
    have hmap : (Subgroup.zpowers x).map (MulAut.conj : G →* MulAut G) =
        Subgroup.zpowers (MulAut.conj x) := MonoidHom.map_zpowers _ _
    rw [← hmap] at hconj_z
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hconj_z
    have hyg : y = g := hconj_inj hyeq
    rwa [← hyg]
  · rw [Subgroup.zpowers_le]
    refine ⟨hxE, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    rw [hJ0] at hy
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
    have hjfix : σ j = j := hJcomp.1 hj
    have hx0j : j * x₀ = x₀ * j := by
      have h1 : MulAut.conj x₀ j = j := by rw [hx₀]; exact hjfix
      rw [MulAut.conj_apply] at h1
      calc j * x₀ = (x₀ * j * x₀⁻¹) * x₀ := by rw [h1]
        _ = x₀ * j := by group
    rw [hx]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hx0j]

private theorem tpa8r_only {X G : Type} [Group X] [Finite X] [Group G]
    (ρ : X ≃* G) (σ : MulAut X) (J : Subgroup X) (J₀ : Subgroup G) (x : G)
    (hJ0 : J₀ = J.map ρ.toMonoidHom)
    (hcent : Subgroup.centralizer ({x} : Set G) = (ggAutFixedSubgroup σ).map ρ.toMonoidHom)
    (honly : GGTPNOnlyComp 7 σ J) :
    ∀ J'' : Subgroup G, IsComponentOf J'' (Subgroup.centralizer ({x} : Set G)) →
      7 ∣ Nat.card J'' → J'' = J₀ := by
  intro J'' hJ'' h7J''
  have hJ''map : (J''.comap ρ.toMonoidHom).map ρ.toMonoidHom = J'' := by
    have hle : J'' ≤ ρ.toMonoidHom.range := by
      rw [MonoidHom.range_eq_top.mpr ρ.surjective]; exact le_top
    rw [Subgroup.map_comap_eq_self hle]
  have hcomp1 : IsComponentOf (J''.comap ρ.toMonoidHom) (ggAutFixedSubgroup σ) := by
    apply TagsExc.isComponentOf_comap ρ.toMonoidHom ρ.injective
    rwa [hcent] at hJ''
  have hcard : Nat.card (J''.comap ρ.toMonoidHom) = Nat.card J'' := by
    rw [← Subgroup.card_map_of_injective (f := ρ.toMonoidHom)
      (K := J''.comap ρ.toMonoidHom) ρ.injective, hJ''map]
  have h7 : 7 ∣ Nat.card (J''.comap ρ.toMonoidHom) := by rw [hcard]; exact h7J''
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hpc : LargeEvenPComponent 7 (ggAutFixedSubgroup σ) (J''.comap ρ.toMonoidHom) := by
    rw [ggLargeEvenPComponent_iff]
    exact ⟨hcomp1.1, isPComponent_subgroupOf_of_isComponentOf_of_dvd hcomp1 h7⟩
  have := honly (J''.comap ρ.toMonoidHom) hpc
  rw [← hJ''map, this]
  exact hJ0.symm
private theorem tpa8r_setup (hRig : GGLabelRigidInput) (p n : ℕ)
    {X : Type} [Group X] [Finite X] (A Ab : Subgroup (MulAut X)) (σ : MulAut X) (J : Subgroup X)
    (hD : GGTPNDatumB p n (fun _ _ => True) A Ab σ J)
    (hp7 : p = 7) (hlabX : GGHasLabel ⟨.A, 8, 1⟩ (X ⧸ Subgroup.center X)) :
    p = 7 ∧ GGHasLabel ⟨.A, 8, 1⟩ (X ⧸ Subgroup.center X) ∧
    ∃ (ρ : X ≃* Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))
      (x : Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))
      (E₀ J₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))),
      J₀ = J.map ρ.toMonoidHom ∧
      orderOf x = 7 ∧ x ∈ E₀ ∧ IsElemAbelian 7 E₀ ∧ 7 ^ 3 ≤ Nat.card E₀ ∧
      IsComponentOf J₀ (Subgroup.centralizer
        ({x} : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) ∧
      E₀ ≤ Subgroup.normalizer (J₀ : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) ∧
      E₀ ⊓ Subgroup.centralizer (J₀ : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2))) =
        Subgroup.zpowers x ∧
      (∀ J' : Subgroup (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)),
        IsComponentOf J' (Subgroup.centralizer
          ({x} : Set (Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)))) →
        7 ∣ Nat.card J' → J' = J₀) := by
  obtain ⟨⟨hloc, hflat, hcardAb, hrankb, hnum, hself, honly, hmark⟩, hcor⟩ := hD
  obtain ⟨hAab, hσA, hσne, hJcomp, hAJ⟩ := hloc
  obtain ⟨hAbA, hσAb, hcardle, hkerb⟩ := hflat
  obtain ⟨hperf, lab, hlabIn, hraw⟩ := hmark
  have hhasLab : GGHasLabel lab (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F hq => ⟨hq.2.2.choose⟩) hraw
  have hlabEq : lab = ⟨.A, 8, 1⟩ := by
    rcases ggLabelIso_typeA_cases hRig (r := 8) (f := 1) (by norm_num)
      hlabIn largeEvenInLambda2_a8 hhasLab hlabX with h | ⟨h83, -⟩
    · exact h
    · omega
  rw [hlabEq] at hraw
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  simp only [LargeEvenRecipeLinear] at hraw
  obtain ⟨K, hKfield, hKfin, hKcard, hQR⟩ := hraw
  obtain ⟨hsimp, hna, hθex⟩ := hQR
  obtain ⟨θ, hShalf⟩ := hθex
  obtain ⟨-, hhalf, hind⟩ := hShalf
  have hhas : GGHasLabel ⟨.A, 8, 1⟩ (X ⧸ Subgroup.center X) := hlabX
  subst hp7
  have hI : LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 9) K)) Set.univ ⊆
      LargeEvenInnSet (LargeEvenProj (LargeEvenSLGroup (Fin 9) K)) := by
    have hcardu : Nat.card Kˣ = 1 := by rw [Nat.card_units, hKcard]; norm_num
    exact matConjImage_gl_subset_inn (K := K) (d := 9)
      (by rw [hcardu]; exact Nat.coprime_one_left 9)
  have hinner : A ≤ (MulAut.conj : X →* MulAut X).range :=
    tpa8r_mem_A_inner hperf θ hI hind
  have hσrange : σ ∈ (MulAut.conj : X →* MulAut X).range := hinner hσA
  obtain ⟨x₀, hx₀⟩ := hσrange
  have hhasTop : GGHasLabel ⟨.A, 8, 1⟩
      ((⊤ : Subgroup X) ⧸ Subgroup.center (⊤ : Subgroup X)) :=
    ggHasLabel_quotCenter_of_mulEquiv (Subgroup.topEquiv (G := X)).symm hhas
  have hmodTop : CFSG.Open.StatedClassicalModel
      ((⊤ : Subgroup X) ⧸ Subgroup.center (⊤ : Subgroup X)) .PSL 9 2 1 :=
    statedClassicalModel_of_hasLabel_typeA largeEvenInLambda2_a8 hhasTop
  have hperfTop : commutator ↥(⊤ : Subgroup X) = ⊤ := by
    haveI : Group.IsPerfect X := ⟨hperf⟩
    haveI : Group.IsPerfect ↥(⊤ : Subgroup X) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := X)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := X)).symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  obtain ⟨φ, hφrange, hφinj⟩ :=
    GGHalf.exists_slLift_two (m := 6) (by norm_num) hperfTop hmodTop
  have hF2card : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  let eX : X ≃* Matrix.SpecialLinearGroup (Fin 9) F2 :=
    (MulEquiv.ofBijective φ ⟨hφinj, MonoidHom.range_eq_top.mp hφrange⟩).symm
  let eSL : Matrix.SpecialLinearGroup (Fin 9) F2 ≃* projectiveSL 9 F2 :=
    MulEquiv.ofBijective (proj 9 F2)
      ⟨proj_nine_injective_of_card_two (K := F2) hF2card, proj_surjective 9 F2⟩
  let G : Type := Matrix.GeneralLinearGroup (Fin 9) (ZMod 2)
  let ρ : X ≃* G :=
    eX.trans (eSL.trans ((ggSL9ProjEquiv (K := F2) hF2card).trans ggSL9GLEquiv.symm))
  let x : G := ρ x₀
  have hconj_x : MulAut.conj x = MulAut.congr ρ σ := by
    change MulAut.conj (ρ x₀) = MulAut.congr ρ σ
    rw [← hx₀]
    exact (mulAut_congr_conj ρ x₀).symm
  have hZGLV : Subgroup.center (GGSL9V ≃ₗ[ZMod 2] GGSL9V) = ⊥ := center_ggSL9_eq_bot
  have hZGL9 : Subgroup.center G = ⊥ := tpa8r_center_eq_bot_of_mulEquiv ggSL9GLEquiv hZGLV
  have hconj_inj : Function.Injective (MulAut.conj : G →* MulAut G) :=
    tpa8r_conj_injective hZGL9
  let Aρ : Subgroup (MulAut G) := Ab.map (MulAut.congr ρ).toMonoidHom
  let E₀ : Subgroup G := Aρ.comap (MulAut.conj : G →* MulAut G)
  let J₀ : Subgroup G := J.map ρ.toMonoidHom
  have hAρ_le : ∀ a ∈ Aρ, ∀ j ∈ J₀, a j ∈ J₀ := by
    rintro a ⟨b, hb, rfl⟩ j ⟨k, hk, rfl⟩
    have h := Subgroup.mem_map_of_mem ρ.toMonoidHom (hAJ b (hAbA hb) k hk)
    have hbk : ((MulAut.congr ρ).toMonoidHom b) (ρ.toMonoidHom k) = ρ.toMonoidHom (b k) := by
      simp [MulAut.congr_apply]
    rwa [hbk]
  have hAρ_range : Aρ ≤ (MulAut.conj : G →* MulAut G).range := by
    rintro a ⟨b, hb, rfl⟩
    obtain ⟨g, hg⟩ := hinner (hAbA hb)
    refine ⟨ρ g, ?_⟩
    rw [← hg]
    exact (mulAut_congr_conj ρ g).symm
  have hE0map : E₀.map (MulAut.conj : G →* MulAut G) = Aρ :=
    Subgroup.map_comap_eq_self hAρ_range
  have hcardE0eqA : Nat.card E₀ = Nat.card Ab := by
    calc Nat.card E₀ = Nat.card (E₀.map (MulAut.conj : G →* MulAut G)) :=
          (Subgroup.card_map_of_injective hconj_inj).symm
      _ = Nat.card Aρ := by rw [hE0map]
      _ = Nat.card Ab := Subgroup.card_map_of_injective (MulAut.congr ρ).injective
  have hcardE0 : 7 ^ 3 ≤ Nat.card E₀ := by rw [hcardE0eqA]; exact hcardAb
  have hAbab : IsElemAbelian 7 Ab := by
    obtain ⟨hc, hp⟩ := hAab
    haveI : IsMulCommutative A := hc
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · apply Subtype.ext
      exact Subgroup.mul_comm_of_mem_isMulCommutative A (hAbA u.2) (hAbA v.2)
    · exact hp z (hAbA hz)
  have hE0ab : IsElemAbelian 7 E₀ := by
    obtain ⟨hAρc, hAρp⟩ := tpa8r_isElemAbelian_map (MulAut.congr ρ).toMonoidHom hAbab
    haveI : IsMulCommutative Aρ := hAρc
    let eE0 : E₀ ≃* Aρ :=
      (Subgroup.equivMapOfInjective E₀ (MulAut.conj : G →* MulAut G) hconj_inj).trans
        (MulEquiv.subgroupCongr hE0map)
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun z hz => ?_⟩
    · apply eE0.injective
      rw [map_mul, map_mul]
      exact Subtype.ext
        (Subgroup.mul_comm_of_mem_isMulCommutative Aρ (eE0 u).2 (eE0 v).2)
    · have hz' : (⟨z, hz⟩ : ↥E₀) ^ 7 = 1 := by
        apply eE0.injective
        rw [map_pow, map_one]
        exact Subtype.ext (by simpa using hAρp (eE0 ⟨z, hz⟩) (eE0 ⟨z, hz⟩).2)
      exact congrArg Subtype.val hz'
  have hxE : x ∈ E₀ := by
    rw [Subgroup.mem_comap]
    show MulAut.conj x ∈ Aρ
    rw [hconj_x]
    exact Subgroup.mem_map_of_mem (MulAut.congr ρ).toMonoidHom hσAb
  have hcent0 : Subgroup.centralizer ({x₀} : Set X) = ggAutFixedSubgroup σ := by
    ext z
    rw [Subgroup.mem_centralizer_singleton_iff, mem_ggAutFixedSubgroup]
    constructor
    · intro hz
      rw [← hx₀, MulAut.conj_apply, show x₀ * z = z * x₀ from hz.symm]
      group
    · intro hz
      have h1 : MulAut.conj x₀ z = z := by rw [hx₀]; exact hz
      rw [MulAut.conj_apply] at h1
      calc z * x₀ = (x₀ * z * x₀⁻¹) * x₀ := by rw [h1]
        _ = x₀ * z := by group
  have hcent : Subgroup.centralizer ({x} : Set G) =
      (ggAutFixedSubgroup σ).map ρ.toMonoidHom := by
    change Subgroup.centralizer ({ρ x₀} : Set G) = (ggAutFixedSubgroup σ).map ρ.toMonoidHom
    have hle : Subgroup.centralizer ({ρ x₀} : Set G) ≤ ρ.toMonoidHom.range := by
      rw [MonoidHom.range_eq_top.mpr ρ.surjective]; exact le_top
    rw [← hcent0, TagsExc.centralizer_singleton_eq_comap ρ x₀, Subgroup.map_comap_eq_self hle]
  have hJ0comp : IsComponentOf J₀ (Subgroup.centralizer ({x} : Set G)) := by
    rw [hcent]
    exact isComponentOf_map_of_injective ρ.toMonoidHom ρ.injective hJcomp
  have hE0norm : E₀ ≤ Subgroup.normalizer (J₀ : Set G) := by
    intro g hg
    have hgA : (MulAut.conj g : MulAut G) ∈ Aρ := by
      rw [← Subgroup.mem_comap]; exact hg
    rw [Subgroup.mem_normalizer_iff]
    intro j
    constructor
    · intro hj
      have hmem := hAρ_le (MulAut.conj g) hgA j hj
      rwa [MulAut.conj_apply] at hmem
    · intro hj
      have hmem : (MulAut.conj g : MulAut G) j ∈ J₀ := by
        rw [MulAut.conj_apply]; exact hj
      have hg'inv : (MulAut.conj g : MulAut G)⁻¹ ∈ Aρ := Aρ.inv_mem hgA
      have hmem2 := hAρ_le _ hg'inv _ hmem
      have hthis : (MulAut.conj g : MulAut G)⁻¹ ((MulAut.conj g) j) = j := by
        rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      rwa [hthis] at hmem2
  have hE0inf : E₀ ⊓ Subgroup.centralizer (J₀ : Set G) = Subgroup.zpowers x :=
    tpa8r_E0inf ρ σ Ab J Aρ E₀ J₀ x x₀ rfl rfl rfl rfl hx₀ hconj_x hconj_inj hAρ_le hkerb
      hJcomp hxE hcent
  have hx7 : x ^ 7 = 1 := by
    apply hconj_inj
    rw [map_pow, hconj_x, ← map_pow (MulAut.congr ρ) σ, hAab.2 σ hσA]
    simp only [map_one]
  have hxne : x ≠ 1 := by
    intro hx1
    have h1 : MulAut.conj x = 1 := by rw [hx1, map_one]
    rw [hconj_x] at h1
    have hσ1 : σ = 1 := by
      apply (MulAut.congr ρ).injective
      rw [h1, map_one]
    exact hσne hσ1
  have hxord : orderOf x = 7 := by
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact orderOf_eq_prime hx7 hxne
  have honly' : ∀ J'' : Subgroup G,
      IsComponentOf J'' (Subgroup.centralizer ({x} : Set G)) →
      7 ∣ Nat.card J'' → J'' = J₀ :=
    tpa8r_only ρ σ J J₀ x rfl hcent honly
  exact ⟨rfl, hhas, ρ, x, E₀, J₀, rfl, hxord, hxE, hE0ab, hcardE0, hJ0comp, hE0norm,
    hE0inf, honly'⟩

theorem ggTablePKnownR_a8Seven :
    GGTablePKnownR GGRegimeA8Seven := by
  intro p hp hp2 X _ hXfin A Ab σ J n hD labJ labX hJ hX hr hhJ hhX
  obtain ⟨hp7, hlabXeq⟩ := hr
  subst hp7
  subst hlabXeq
  obtain ⟨-, hhas, ρ, x, E₀, J₀, hJ0, hxord, hxE, hE0ab, hcardE0, hJ0comp, hE0norm,
    hE0inf, honly'⟩ :=
    tpa8r_setup ggLabelRigidInput_holds 7 n A Ab σ J hD rfl hhX
  have hleaf : GGHasLabel ⟨.A, 2, 3⟩ (J₀ ⧸ Subgroup.center J₀) ∨
      GGHasLabel ⟨.A, 5, 1⟩ (J₀ ⧸ Subgroup.center J₀) :=
    ggTablePA8SevenKnown_holds x E₀ J₀ hxord hxE hE0ab hcardE0 hJ0comp hE0norm hE0inf honly'
  have hiso : J ≃* J₀ :=
    (Subgroup.equivMapOfInjective J ρ.toMonoidHom ρ.injective).trans
      (MulEquiv.subgroupCongr hJ0.symm)
  rcases hleaf with h23 | h51
  · refine ⟨⟨.A, 2, 3⟩, ⟨.A, 8, 1⟩, tpa8r_inLambda2_a23, largeEvenInLambda2_a8,
      tpa8r_row_a23_a8, ?_, hhas⟩
    exact ggHasLabel_quotCenter_of_mulEquiv hiso.symm h23
  · refine ⟨⟨.A, 5, 1⟩, ⟨.A, 8, 1⟩, tpa8r_inLambda2_a51, largeEvenInLambda2_a8,
      tpa8r_row_a51_a8, ?_, hhas⟩
    exact ggHasLabel_quotCenter_of_mulEquiv hiso.symm h51

end CFSG.StandardType

end
