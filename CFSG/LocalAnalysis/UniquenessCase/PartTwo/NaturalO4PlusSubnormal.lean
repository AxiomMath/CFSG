module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
public import CFSG.Quasithin.Background.G64RealizeSec
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFix
public import CFSG.Quasithin.Background.G64Statement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open CFSG.StandardType.OmNonsplit CFSG.Quasithin.G64

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_mulEquiv_sl2_of_isSubnormal_isNaturalO4Plus {R : Subgroup (MulAut W)}
    {e : ℕ} {Kc : Subgroup (MulAut W)} (hKbar : CFSG.Open.IsQuasisimple Kc)
    (hsub : CFSG.Open.IsSubnormal Kc R) (hnat : IsNaturalO4Plus R e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
      4 ≤ Nat.card K ∧ Nonempty (Kc ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨K, hKfield, hKfinite, hKcard, hreal⟩ := hnat
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  let Γ := CFSG.PGLModel.orthogonalPlus 2 K
  obtain ⟨π, hπ⟩ := hreal
  have hinj : Function.Injective π :=
    RealizesVia.injective_of_faithful' (CFSG.Quasithin.FFModel.nat_faithful _) hπ
  let eΓ : Γ ≃* ↥R := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  let TΓ : Subgroup Γ := (Kc.subgroupOf R).map eΓ.symm.toMonoidHom
  have hTΓsub : CFSG.Open.IsSubnormal TΓ ⊤ := by
    have h1 : (Kc.subgroupOf R).IsSubnormal := CFSG.Open.IsSubnormal.subgroupOf hsub
    exact CFSG.Open.IsSubnormal.of_mathlib (h1.map eΓ.symm.surjective)
  let eK : Kc ≃* Kc.subgroupOf R :=
    (Subgroup.subgroupOfEquivOfLe (CFSG.Open.IsSubnormal.le hsub)).symm
  let eT : Kc ≃* TΓ := eK.trans (MulEquiv.subgroupMap eΓ.symm (Kc.subgroupOf R))
  have hTΓq : CFSG.IsQuasisimple TΓ := by
    have hKq' : CFSG.IsQuasisimple Kc := CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hKbar
    exact CFSG.IsQuasisimple.of_mulEquiv eT.symm hKq'
  let fL := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2) K)
  let O := TauCeti.QuadraticMap.orthogonalGroup (CFSG.LieType.Universal.Spin.quadPlus 2 K)
  let Tgl : Subgroup (GL (Fin 2 ⊕ Fin 2) K) := TΓ.map Γ.subtype
  let T : Subgroup ((Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] (Fin 2 ⊕ Fin 2 → K)) :=
    Tgl.map fL.toMonoidHom
  have hQ : ⇑(CFSG.LieType.Universal.Spin.quadPlus 2 K) =
      CFSG.PGLModel.plusQuadForm 2 (K := K) := by
    funext v
    rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
    rfl
  have hΓO : Γ = O.comap fL.toMonoidHom := by
    rw [show Γ = CFSG.MatrixModel.isometryCore (CFSG.PGLModel.plusQuadForm 2 (K := K))
      from rfl]
    exact CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap hQ
  have hΓmap : Γ.map fL.toMonoidHom = O := by
    rw [hΓO, Subgroup.map_comap_eq_self_of_surjective fL.surjective]
  have hTle : Tgl ≤ Γ := Subgroup.map_subtype_le TΓ
  have hTO : T ≤ O := by
    calc Tgl.map fL.toMonoidHom ≤ Γ.map fL.toMonoidHom := Subgroup.map_mono hTle
      _ = O := hΓmap
  have hTglq : CFSG.IsQuasisimple Tgl :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective TΓ Γ.subtype Γ.subtype_injective).symm hTΓq
  have hTq : CFSG.IsQuasisimple T :=
    CFSG.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective Tgl fL.toMonoidHom fL.injective).symm hTglq
  have hTsub : CFSG.Assembly.IsSubnormal T O := by
    have h1 : CFSG.Assembly.IsSubnormal TΓ ⊤ := CFSG.Assembly.isSubnormal_iff_open.mpr hTΓsub
    have h2 := h1.map Γ.subtype
    have h3 : (⊤ : Subgroup ↥Γ).map Γ.subtype = Γ := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [h3] at h2
    have h4 := h2.map fL.toMonoidHom
    rwa [hΓmap] at h4
  haveI : CharP K 2 := by
    have h1 : Fintype.card K = 2 ^ e := by
      rw [← Nat.card_eq_fintype_card]
      exact hKcard
    exact charP_of_card_eq_prime_pow (f := e) h1
  have hsp : SplitFour (CFSG.LieType.Universal.Spin.quadPlus 2 K) := by
    classical
    let L : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
      { toFun := fun v => fun i => v (Sum.inr i)
        map_add' := by intro x y; ext i; rfl
        map_smul' := by intro a x; ext i; rfl }
    refine ⟨?_, ⟨LinearMap.ker L, ?_, ?_⟩⟩
    · rw [Module.finrank_fintype_fun_eq_card]
      simp [Fintype.card_sum]
    · have hsurj : Function.Surjective L := by
        intro y
        refine ⟨fun z => Sum.rec (fun _ => (0 : K)) (fun i => y i) z, ?_⟩
        ext i
        rfl
      have hrange : LinearMap.range L = ⊤ := LinearMap.range_eq_top.mpr hsurj
      have hV : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by
        rw [Module.finrank_fintype_fun_eq_card]
        simp [Fintype.card_sum]
      have h := LinearMap.finrank_range_add_finrank_ker L
      rw [hrange, finrank_top, Module.finrank_fintype_fun_eq_card, hV] at h
      simp only [Fintype.card_fin] at h
      omega
    · intro x hx
      rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
      simp only [LinearMap.mem_ker] at hx
      apply Finset.sum_eq_zero
      intro i _
      have hxi : x (Sum.inr i) = 0 := by
        have := congrFun hx i
        simpa [L] using this
      rw [hxi, mul_zero]
  have hnd : (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus 2 K)).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus 2 K
  obtain ⟨-, hcases⟩ :=
    CFSG.StandardType.OmNonsplit.structure_of_isSubnormal (K := K)
      (W := Fin 2 ⊕ Fin 2 → K) (R := CFSG.LieType.Universal.Spin.quadPlus 2 K) hnd hTq hTsub
  rcases hcases with ⟨hnsp, -⟩ | ⟨-, hK4, ψ, hψi, hψr⟩
  · exact absurd hsp hnsp
  · let eψ : Matrix.SpecialLinearGroup (Fin 2) K ≃* T :=
      (MonoidHom.ofInjective hψi).trans (MulEquiv.subgroupCongr hψr)
    let eTglT : Tgl ≃* T := Subgroup.equivMapOfInjective Tgl fL.toMonoidHom fL.injective
    let eTΓTgl : TΓ ≃* Tgl := Subgroup.equivMapOfInjective TΓ Γ.subtype Γ.subtype_injective
    exact ⟨K, hKfield, hKfinite, hKcard, hK4,
      ⟨(eψ.trans (eTglT.symm.trans (eTΓTgl.symm.trans eT.symm))).symm⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
