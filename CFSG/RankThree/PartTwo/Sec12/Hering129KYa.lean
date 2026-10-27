module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvShape
public import CFSG.RankThree.PartTwo.Sec12.Hering129HLift

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG.RankThree.LocalRank

namespace Hering129KYa

open scoped MatrixGroups

theorem center_eq_one_of_pow_three {K : Type} [Field K] {z : SL(2, K)}
    (hz : z ∈ Subgroup.center SL(2, K)) (h3 : z ^ 3 = 1) : z = 1 := by
  obtain ⟨r, hr2, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hz
  rw [Fintype.card_fin] at hr2
  have hm : (Matrix.scalar (Fin 2) r) ^ 3 = 1 := by
    rw [hrz, ← Matrix.SpecialLinearGroup.coe_pow, h3, Matrix.SpecialLinearGroup.coe_one]
  rw [← map_pow] at hm
  have hr3 : r ^ 3 = 1 := by
    have h1 : Matrix.scalar (Fin 2) (r ^ 3) = Matrix.scalar (Fin 2) (1 : K) := by
      rw [map_one]
      exact hm
    exact Matrix.scalar_inj.mp h1
  have hr1 : r = 1 := by
    rw [pow_succ, hr2, one_mul] at hr3
    exact hr3
  apply Subtype.ext
  rw [← hrz, hr1, map_one]
  rfl

theorem projSL_two_eq_range (K : Type) [Field K] :
    CFSG.PGLModel.projSL 2 K = (Matrix.SpecialLinearGroup.toPGL :
      SL(2, K) →* Matrix.ProjGenLinGroup (Fin 2) K).range := by
  rw [CFSG.PGLModel.projSL, CFSG.PGLModel.projImage, Matrix.SpecialLinearGroup.toPGL,
    MonoidHom.range_comp, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

theorem nonempty_quotTheta_equiv_projSL_of_four_le {X : Type} [Group X] [Finite X] {K : Type}
    [Field K] [Finite K] (h4 : 4 ≤ Nat.card K) (φ : X →* SL(2, K))
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ aschbacherSolvableCore 3 X) :
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* ↥(CFSG.PGLModel.projSL 2 K)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hθs, -, hθ3, hθmax, -, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hQ : CFSG.IsQuasisimple SL(2, K) := CFSG.GH74.GLS.IVK.GHInv.isQuasisimple_sl2 h4
  obtain ⟨pr, hpr⟩ : ∃ pr : SL(2, K) →* Matrix.ProjGenLinGroup (Fin 2) K,
      pr = Matrix.SpecialLinearGroup.toPGL := ⟨_, rfl⟩
  have hprker : pr.ker = Subgroup.center SL(2, K) := by
    rw [hpr, Matrix.SpecialLinearGroup.toPGL_ker]
  have hprrange : CFSG.PGLModel.projSL 2 K = pr.range := by
    rw [hpr]
    exact projSL_two_eq_range K
  have hprmem : ∀ g : SL(2, K), g ∈ Subgroup.center SL(2, K) ↔ pr g = 1 := fun g => by
    rw [← hprker]
    exact MonoidHom.mem_ker
  haveI hφθn : ((aschbacherSolvableCore 3 X).map φ).Normal :=
    Subgroup.Normal.map inferInstance φ hφ
  have hφθs : Group.IsSolvable ↥((aschbacherSolvableCore 3 X).map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective (aschbacherSolvableCore 3 X))
  have hφθc : (aschbacherSolvableCore 3 X).map φ ≤ Subgroup.center SL(2, K) :=
    CFSG.RankThree.PartTwo.Sec12.Hering129HLift.solvable_normal_le_center hQ
      ((aschbacherSolvableCore 3 X).map φ) hφθs
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : X →* ↥pr.range, ψ = pr.rangeRestrict.comp φ := ⟨_, rfl⟩
  have hψval : ∀ x : X, ((ψ x : ↥pr.range) : Matrix.ProjGenLinGroup (Fin 2) K) = pr (φ x) := by
    intro x
    rw [hψdef]
    rfl
  have hψsurj : Function.Surjective ψ := by
    rw [hψdef]
    exact (MonoidHom.rangeRestrict_surjective pr).comp hφ
  have hψ1 : ∀ x : X, ψ x = 1 ↔ φ x ∈ Subgroup.center SL(2, K) := by
    intro x
    rw [hprmem (φ x)]
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rw [hψval x] at h'
      exact h'
    · intro h
      apply Subtype.ext
      rw [hψval x]
      exact h
  have hθker : aschbacherSolvableCore 3 X ≤ ψ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hψ1]
    exact hφθc (Subgroup.mem_map_of_mem φ hx)
  have hkerθ : ψ.ker ≤ aschbacherSolvableCore 3 X := by
    have hPc : ∀ x ∈ ψ.ker, φ x ∈ Subgroup.center SL(2, K) := fun x hx =>
      (hψ1 x).mp (MonoidHom.mem_ker.mp hx)
    have hkerφψ : φ.ker ≤ ψ.ker := hker.trans hθker
    haveI : Group.IsSolvable ↥φ.ker :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hker)
    have hPs : Group.IsSolvable ↥ψ.ker := by
      refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hkerφψ)
        ((φ.comp ψ.ker.subtype).codRestrict (Subgroup.center SL(2, K))
          (fun x => hPc x.1 x.2)) ?_
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hφx : φ (x : X) = 1 := congrArg Subtype.val hx
      exact MonoidHom.mem_range.mpr ⟨⟨(x : X), MonoidHom.mem_ker.mpr hφx⟩, rfl⟩
    have hP3 : ¬ 3 ∣ Nat.card ↥ψ.ker := by
      intro h3
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥ψ.ker) 3 h3
      have hg3 : (g : X) ^ 3 = 1 := by
        have h := pow_orderOf_eq_one g
        rw [hg] at h
        have h' := congrArg Subtype.val h
        simpa using h'
      have hφg1 : φ (g : X) = 1 := by
        apply center_eq_one_of_pow_three (hPc _ g.2)
        rw [← map_pow, hg3, map_one]
      have hgθ : (g : X) ∈ aschbacherSolvableCore 3 X := hker (MonoidHom.mem_ker.mpr hφg1)
      have hord : orderOf (⟨(g : X), hgθ⟩ : ↥(aschbacherSolvableCore 3 X)) = 3 := by
        rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg]
      have h3θ : 3 ∣ Nat.card ↥(aschbacherSolvableCore 3 X) := by
        have hdvd := orderOf_dvd_natCard (⟨(g : X), hgθ⟩ : ↥(aschbacherSolvableCore 3 X))
        rwa [hord] at hdvd
      exact hθ3 h3θ
    exact hθmax ψ.ker inferInstance hPs hP3
  have hker_eq : ψ.ker = aschbacherSolvableCore 3 X := le_antisymm hkerθ hθker
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker_eq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)).trans
    (MulEquiv.subgroupCongr hprrange.symm)⟩

theorem nonempty_quotTheta_equiv_projSL {X : Type} [Group X] [Finite X] {F : Type} [Field F]
    [Finite F] {p n : ℕ} [Fact p.Prime] (hF : Nat.card F = p ^ n) (h4 : 4 ≤ Nat.card F)
    (φ : X →* Matrix.SpecialLinearGroup (Fin 2) F) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X) :
    Nonempty (X ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X ≃*
      CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField p n)) := by
  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hF
    omega
  have hGF : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n hn
  haveI : Fintype F := Fintype.ofFinite F
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  have hcard : Fintype.card F = Fintype.card (GaloisField p n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hGF]
  let e : F ≃+* GaloisField p n := FiniteField.ringEquivOfCardEq hcard
  let χ : SL(2, F) →* SL(2, GaloisField p n) := Matrix.SpecialLinearGroup.map e.toRingHom
  have hleft : ∀ g : SL(2, F), Matrix.SpecialLinearGroup.map e.symm.toRingHom (χ g) = g := by
    intro g
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [χ]
  have hright : ∀ g : SL(2, GaloisField p n),
      χ (Matrix.SpecialLinearGroup.map e.symm.toRingHom g) = g := by
    intro g
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    simp [χ]
  have hχinj : Function.Injective χ := Function.LeftInverse.injective hleft
  have hright' : Function.RightInverse (Matrix.SpecialLinearGroup.map e.symm.toRingHom) χ :=
    hright
  have hχsurj : Function.Surjective χ := Function.RightInverse.surjective hright'
  have hker' : (χ.comp φ).ker ≤ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 X := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    exact hker (MonoidHom.mem_ker.mpr (hχinj (hx.trans (map_one χ).symm)))
  have h4' : 4 ≤ Nat.card (GaloisField p n) := by
    rw [hGF, ← hF]
    exact h4
  exact nonempty_quotTheta_equiv_projSL_of_four_le (K := GaloisField p n) h4' (χ.comp φ)
    (hχsurj.comp hφ) hker'

end Hering129KYa

end CFSG.RankThree.PartTwo.Sec12

end
