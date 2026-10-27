module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmCoordinates
public import CFSG.LocalAnalysis.StandardType.GGTorusGenOrthPieces
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
import CFSG.ClassicalGroups.SpecialLinear.TvModLinAlg
import CFSG.LinearAlgebra.QuadraticPieceDihedral
import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusExtraction
import CFSG.ClassicalInvolution.Q3.Q3PlanParams
import CFSG.LargeExtraspecial.A2ModLines

public section

open Module Multiplicative QuadraticMap
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ClassicalGroups.Orthogonal
open CFSG.GroupTheory.WeirSylow
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open scoped commutatorElement

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p r : ℕ}
  {A : Subgroup (V ≃ₗ[K] V)}

theorem TBJOmData.commutator_le_supportedDerived_polarPerp
    [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate)
    (hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (T : Finset (Fin r)) {H : Subgroup (V ≃ₗ[K] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hH : ∀ g ∈ H, ∀ i ∈ T,
      Commute g (Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))))) :
    ⁅H, H⁆ ≤ supportedDerived Q (polarPerp Q (T.sup Δ.F.U)) := by
  classical
  let R : Submodule K V := T.sup Δ.F.U
  let M : Submodule K V := polarPerp Q R
  have hgen : ∀ i : Fin r, toAdd (piMul r p (Pi.mulSingle i (ofAdd (1 : ZMod p)))) i ≠ 0 := by
    intro i
    rw [piMul_apply, toAdd_ofAdd, Pi.mulSingle_eq_same, toAdd_ofAdd]
    exact (one_ne_zero : (1 : ZMod p) ≠ 0)
  have hpiece : ∀ x ∈ H, ∀ i ∈ T, ∀ u ∈ Δ.F.U i, x u ∈ Δ.F.U i := by
    intro x hx i hi u hu
    let t : V ≃ₗ[K] V := Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))
    have hconj : x * t * x⁻¹ = t := by
      rw [(hH x hx i hi).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Δ.mapsTo_piece_of_conj_tau_mulSingle hQ (hHO hx) hconj u hu
  have hpiece_inv : ∀ x ∈ H, ∀ i ∈ T, ∀ u ∈ Δ.F.U i, x.symm u ∈ Δ.F.U i := by
    intro x hx i hi u hu
    let t : V ≃ₗ[K] V := Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))
    have hxinv : x⁻¹ ∈ H := H.inv_mem hx
    have hconj : x⁻¹ * t * (x⁻¹)⁻¹ = t := by
      rw [(hH x⁻¹ hxinv i hi).eq, mul_assoc, mul_inv_cancel, mul_one]
    have h := Δ.mapsTo_piece_of_conj_tau_mulSingle hQ (hHO hxinv) hconj u hu
    simpa using h
  have hRmaps : ∀ x ∈ H, ∀ v ∈ R, x v ∈ R := by
    intro x hx
    have hle : R ≤ Submodule.comap x.toLinearMap R := by
      refine Finset.sup_le fun i hi => ?_
      intro u hu
      rw [Submodule.mem_comap]
      exact Finset.le_sup (f := Δ.F.U) hi (hpiece x hx i hi u hu)
    intro v hv
    exact hle hv
  have hRinv : ∀ x ∈ H, ∀ v ∈ R, x.symm v ∈ R := by
    intro x hx
    have hle : R ≤ Submodule.comap x.symm.toLinearMap R := by
      refine Finset.sup_le fun i hi => ?_
      intro u hu
      rw [Submodule.mem_comap]
      exact Finset.le_sup (f := Δ.F.U) hi (hpiece_inv x hx i hi u hu)
    intro v hv
    exact hle hv
  have hMmaps : ∀ x ∈ H, ∀ v ∈ M, x v ∈ M := by
    intro x hx v hv
    rw [mem_polarPerp_iff] at hv ⊢
    intro y hy
    calc polar Q y (x v) = polar Q (x (x.symm y)) (x v) := by rw [x.apply_symm_apply]
      _ = polar Q (x.symm y) v :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (hHO hx) _ _
      _ = 0 := hv _ (hRinv x hx y hy)
  have hMinv : ∀ x ∈ H, ∀ v ∈ M, x.symm v ∈ M := by
    intro x hx v hv
    rw [mem_polarPerp_iff] at hv ⊢
    intro y hy
    have hxO : x.symm ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem (hHO hx)
    calc polar Q y (x.symm v) = polar Q (x.symm (x y)) (x.symm v) := by
          rw [x.symm_apply_apply]
      _ = polar Q (x y) v :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hxO _ _
      _ = 0 := hv _ (hRmaps x hx y hy)
  refine Subgroup.commutator_le.mpr fun g hg h hh => ?_
  change ⁅g, h⁆ ∈ supportedDerived Q M
  have hfix_piece : ∀ i ∈ T, ∀ u : Δ.F.U i, ⁅g, h⁆ (u : V) = (u : V) := by
    intro i hi
    let U : Submodule K V := Δ.F.U i
    let t : V ≃ₗ[K] V := Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))
    have hgmap : ∀ u ∈ U, g u ∈ U := hpiece g hg i hi
    have hginv : ∀ u ∈ U, g.symm u ∈ U := hpiece_inv g hg i hi
    have hhmap : ∀ u ∈ U, h u ∈ U := hpiece h hh i hi
    have hhinv : ∀ u ∈ U, h.symm u ∈ U := hpiece_inv h hh i hi
    have htmap : ∀ u ∈ U, t u ∈ U := by
      intro u hu
      rw [show t = Δ.F.ι (piMul r p (Pi.mulSingle i (ofAdd (1 : ZMod p)))) from by
        simp [t, Δ.τ_eq]]
      exact Δ.F.mapsTo _ i u hu
    have htinv : ∀ u ∈ U, t.symm u ∈ U := by
      intro u hu
      have ht : t.symm = Δ.τ ((Pi.mulSingle i (ofAdd (1 : ZMod p)))⁻¹) := by
        simp only [t]
        exact (map_inv Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))).symm
      rw [ht, Δ.τ_eq]
      exact Δ.F.mapsTo _ i u hu
    let gRes : U ≃ₗ[K] U := restrictEquiv U g hgmap hginv
    let hRes : U ≃ₗ[K] U := restrictEquiv U h hhmap hhinv
    let tRes : U ≃ₗ[K] U := restrictEquiv U t htmap htinv
    have hUreg : PolarNondegOn Q U := fun u hu hperp =>
      Δ.F.nondeg i u hu fun v hv => by
        rw [QuadraticMap.polar_comm]
        exact hperp v hv
    have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      hAO (Δ.τ_range.le ⟨Pi.mulSingle i (ofAdd (1 : ZMod p)), by simp [t]⟩)
    have hfpf : ∀ u ∈ U, t u = u → u = 0 := by
      intro u hu htu
      exact Δ.F.fpf (piMul r p (Pi.mulSingle i (ofAdd (1 : ZMod p)))) i (hgen i) u hu
        (by simpa [t, Δ.τ_eq] using htu)
    have htScalar : ∀ c : K, tRes.toLinearMap ≠ c • 1 :=
      CFSG.StandardType.OrthTorusGen.restrictEquiv_not_scalar hUreg (Δ.F.ne_bot i) htO
        htmap htinv hfpf
    have hgt : Commute (gRes : U →ₗ[K] U) (tRes : U →ₗ[K] U) := by
      rw [commute_iff_eq]
      have h := CFSG.StandardType.OrthTorusGen.restrictEquiv_commute hgmap hginv htmap htinv
        (hH g hg i hi).eq
      simpa [gRes, tRes, LinearEquiv.coe_toLinearMap_mul] using congrArg LinearEquiv.toLinearMap h
    have hht : Commute (hRes : U →ₗ[K] U) (tRes : U →ₗ[K] U) := by
      rw [commute_iff_eq]
      have h := CFSG.StandardType.OrthTorusGen.restrictEquiv_commute hhmap hhinv htmap htinv
        (hH h hh i hi).eq
      simpa [hRes, tRes, LinearEquiv.coe_toLinearMap_mul] using congrArg LinearEquiv.toLinearMap h
    have hcomm : Commute (gRes : U →ₗ[K] U) (hRes : U →ₗ[K] U) :=
      CFSG.ClassicalGroups.SpecialLinear.TvMod.commute_of_commute_of_finrank_eq_two
        (K := K) (V := U) (Δ.finrank_piece i) htScalar hgt.symm hht.symm
    have hpoint : ∀ u : U, g (h (u : V)) = h (g (u : V)) := by
      intro u
      have h := congrArg (fun e : Module.End K U => ((e u : U) : V)) hcomm.eq
      simpa [Module.End.mul_apply, coe_restrictEquiv, gRes, hRes] using h
    intro u
    have hmem : g⁻¹ (h⁻¹ (u : V)) ∈ U := by
      have h1 : h⁻¹ (u : V) ∈ U := by
        simpa using hpiece_inv h hh i hi (u : V) u.2
      simpa using hpiece_inv g hg i hi (h⁻¹ (u : V)) h1
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply]
    calc g (h (g⁻¹ (h⁻¹ (u : V)))) = h (g (g⁻¹ (h⁻¹ (u : V)))) :=
          hpoint ⟨g⁻¹ (h⁻¹ (u : V)), hmem⟩
      _ = h (h⁻¹ (u : V)) := by
          rw [show g (g⁻¹ (h⁻¹ (u : V))) = h⁻¹ (u : V) from g.apply_symm_apply _]
      _ = (u : V) := h.apply_symm_apply _
  have hfix_sup : ∀ S : Finset (Fin r), S ⊆ T → ∀ v ∈ S.sup Δ.F.U, ⁅g, h⁆ v = v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _ v hv
        rw [Finset.sup_empty, Submodule.mem_bot] at hv
        simpa [hv]
    | insert i S hi ih =>
        intro hS v hv
        rw [Finset.sup_insert] at hv
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
        have hiT : i ∈ T := hS (Finset.mem_insert_self i S)
        have hST : S ⊆ T := fun j hj => hS (Finset.mem_insert_of_mem hj)
        calc ⁅g, h⁆ (a + b) = ⁅g, h⁆ a + ⁅g, h⁆ b := map_add _ a b
          _ = a + b := by rw [hfix_piece i hiT ⟨a, ha⟩, ih hST b hb]
  have hfix_R : ∀ v ∈ R, ⁅g, h⁆ v = v := fun v hv => hfix_sup T le_rfl v hv
  have hsupp : suppPerp Q M = R := by
    change LinearMap.BilinForm.orthogonal (polarBilin Q)
      (LinearMap.BilinForm.orthogonal (polarBilin Q) (T.sup Δ.F.U)) = T.sup Δ.F.U
    exact LinearMap.BilinForm.orthogonal_orthogonal hQ
      (QuadraticMap.isSymm_polarBilin Q).isRefl (T.sup Δ.F.U)
  have hfix_supp : ∀ v ∈ suppPerp Q M, ⁅g, h⁆ v = v := by
    intro v hv
    rw [hsupp] at hv
    exact hfix_R v hv
  let gM : M ≃ₗ[K] M := restrictEquiv M g (hMmaps g hg) (hMinv g hg)
  let hM : M ≃ₗ[K] M := restrictEquiv M h (hMmaps h hh) (hMinv h hh)
  have hcoe_gM : ∀ w : M, ((gM w : M) : V) = g (w : V) := fun w =>
    coe_restrictEquiv M g (hMmaps g hg) (hMinv g hg) w
  have hcoe_hM : ∀ w : M, ((hM w : M) : V) = h (w : V) := fun w =>
    coe_restrictEquiv M h (hMmaps h hh) (hMinv h hh) w
  have hcoe_gMinv : ∀ w : M, ((gM⁻¹ w : M) : V) = g⁻¹ (w : V) := by
    intro w
    rfl
  have hcoe_hMinv : ∀ w : M, ((hM⁻¹ w : M) : V) = h⁻¹ (w : V) := by
    intro w
    rfl
  have hgM : gM ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    change Q ((gM w : M) : V) = Q (w : V)
    rw [hcoe_gM]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hHO hg) (w : V)
  have hhM : hM ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp M.subtype) := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    change Q ((hM w : M) : V) = Q (w : V)
    rw [hcoe_hM]
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (hHO hh) (w : V)
  refine mem_supportedDerived.mpr ⟨hfix_supp, ⟨⁅gM, hM⁆, ?_, ?_⟩⟩
  · exact Subgroup.commutator_mem_commutator hgM hhM
  · intro w
    rw [commutatorElement_def]
    simp only [LinearEquiv.mul_apply]
    simp only [hcoe_gM, hcoe_hM, hcoe_gMinv, hcoe_hMinv]
    rfl

theorem TBJOmData.commutator_centralizer_le_supportedDerived_polarPerp
    [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (T : Finset (Fin r)) :
    let C := orthDerived Q ⊓ Subgroup.centralizer
      ({g : V ≃ₗ[K] V | ∃ i ∈ T,
        g = Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))} : Set (V ≃ₗ[K] V))
    ⁅C, C⁆ ≤ supportedDerived Q (polarPerp Q (T.sup Δ.F.U)) := by
  classical
  let s : Set (V ≃ₗ[K] V) :=
    {g : V ≃ₗ[K] V | ∃ i ∈ T, g = Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))}
  let C : Subgroup (V ≃ₗ[K] V) := orthDerived Q ⊓ Subgroup.centralizer s
  change ⁅C, C⁆ ≤ supportedDerived Q (polarPerp Q (T.sup Δ.F.U))
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hA.trans (orthDerived_le_orthogonalGroup_of_commutator Q)
  have hHO : C ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (inf_le_left : C ≤ orthDerived Q).trans
      (orthDerived_le_orthogonalGroup_of_commutator Q)
  have hH : ∀ g ∈ C, ∀ i ∈ T,
      Commute g (Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))) := by
    intro g hg i hi
    have hgC : g ∈ Subgroup.centralizer s := (Subgroup.mem_inf.mp (by simpa [C] using hg)).2
    have ht : Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) ∈ s := ⟨i, hi, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp hgC _ ht).symm
  exact Δ.commutator_le_supportedDerived_polarPerp hQ hAO T hHO hH

theorem TBJOmData.polarPerp_compl_sup_eq_originalAnchor_sup
    [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate)
    (o : Fin r) (hWS : IsCompl Δ.originalAnchor Δ.originalActive)
    (S : Finset (Fin r)) :
    polarPerp Q ((Sᶜ).sup Δ.F.U) =
      Δ.originalAnchor ⊔ S.sup Δ.F.U := by
  classical
  let ψ : V ≃ₗ[K] (Δ.originalAnchor × (Fin r → Δ.F.U o)) :=
    Δ.originalCoordinates hQ o hWS
  have hψ := Δ.originalCoordinates_quadratic_apply hQ o hWS
  refine le_antisymm ?_ ?_
  · intro v hv
    set w : Δ.originalAnchor := (ψ v).1 with hw
    set x : Fin r → Δ.F.U o := (ψ v).2 with hx
    have hxzero : ∀ i ∈ Sᶜ, x i = 0 := by
      intro i hi
      have hUreg : (polarBilin (Q.comp (Δ.F.U o).subtype)).Nondegenerate :=
        Δ.originalPlaneForm_nondegenerate o
      apply hUreg.1 (x i)
      intro e
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
      have hy : ψ.symm (0, Pi.single i e) ∈ (Sᶜ).sup Δ.F.U := by
        rw [show ψ = Δ.originalCoordinates hQ o hWS from rfl]
        rw [Δ.originalCoordinates_symm_single hQ o hWS i e]
        exact Finset.le_sup (f := Δ.F.U) hi ((Δ.planeIsometry hQ o i) e).2
      have hperp : polar Q (ψ.symm (0, Pi.single i e)) v = 0 :=
        (mem_polarPerp_iff.mp hv) _ hy
      have hcoord : polar Q (ψ.symm (0, Pi.single i e)) v =
          polar (Q.comp Δ.originalAnchor.subtype) (0 : Δ.originalAnchor) w +
          ∑ k, polar (Q.comp (Δ.F.U o).subtype)
            ((Pi.single i e : Fin r → Δ.F.U o) k) (x k) := by
        have h := polar_coord (QR := Q.comp Δ.originalAnchor.subtype)
          (QE := Q.comp (Δ.F.U o).subtype) ψ hψ (ψ.symm (0, Pi.single i e)) v
        simpa [w, x, LinearEquiv.apply_symm_apply] using h
      have hsum : (∑ k, polar (Q.comp (Δ.F.U o).subtype)
            ((Pi.single i e : Fin r → Δ.F.U o) k) (x k)) =
          polar (Q.comp (Δ.F.U o).subtype) e (x i) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          rw [Pi.single_eq_of_ne hji]
          simp
        · intro hi'
          exact (hi' (Finset.mem_univ i)).elim
      rw [hcoord, hsum] at hperp
      simpa using hperp
    have hdecomp : v = (w : V) +
        ∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) := by
      calc v = ψ.symm (w, x) := by
              simpa [ψ, w, x] using (ψ.symm_apply_apply v).symm
        _ = (w : V) + ∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) :=
              Δ.originalCoordinates_symm_apply hQ o hWS w x
    have hsumS : (∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V)) =
        ∑ i ∈ S, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) := by
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro i _ hiS
      have hxi : x i = 0 := hxzero i (by simpa using hiS)
      simp [hxi]
    have hsum_mem : (∑ i ∈ S, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V)) ∈
        S.sup Δ.F.U := by
      refine Submodule.sum_mem _ fun i hi => ?_
      exact Finset.le_sup (f := Δ.F.U) hi ((Δ.planeIsometry hQ o i) (x i)).2
    rw [hdecomp, hsumS]
    exact Submodule.add_mem_sup w.2 hsum_mem
  · refine sup_le ?_ ?_
    · intro w hw
      rw [mem_polarPerp_iff]
      intro y hy
      have hwA : w ∈ polarPerp Q Δ.originalActive := by
        simpa [TBJOmData.originalAnchor] using hw
      have hyA : y ∈ Δ.originalActive := by
        refine (Finset.sup_le (f := Δ.F.U) fun i _ => ?_) hy
        exact le_iSup (fun j => Δ.F.U j) i
      exact mem_polarPerp_iff.mp hwA y hyA
    · refine Finset.sup_le fun i hi => ?_
      intro u hu
      rw [mem_polarPerp_iff]
      intro y hy
      have hle : (Sᶜ).sup Δ.F.U ≤ suppPerp Q (Submodule.span K {u}) := by
        refine Finset.sup_le fun j hj => ?_
        intro z hz
        rw [mem_suppPerp]
        intro a ha
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
        have hij : i ≠ j := by
          intro hij
          exact (Finset.mem_compl.mp hj) (hij ▸ hi)
        rw [polar_smul_left, Δ.F.orth i j hij u hu z hz, smul_zero]
      have hy' : y ∈ suppPerp Q (Submodule.span K {u}) := hle hy
      have hzero : polar Q u y = 0 :=
        mem_suppPerp.mp hy' u (Submodule.subset_span (by simp))
      rwa [polar_comm] at hzero

theorem TBJOmData.commutator_centralizer_le_supportedDerived_originalAnchor_sup
    [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hA : A ≤ orthDerived Q)
    (o : Fin r) (hWS : IsCompl Δ.originalAnchor Δ.originalActive)
    (S : Finset (Fin r)) :
    let C := orthDerived Q ⊓ Subgroup.centralizer
      ({g : V ≃ₗ[K] V | ∃ i ∈ Sᶜ,
        g = Δ.τ (Pi.mulSingle i (ofAdd (1 : ZMod p)))} : Set (V ≃ₗ[K] V))
    ⁅C, C⁆ ≤ supportedDerived Q (Δ.originalAnchor ⊔ S.sup Δ.F.U) := by
  have h := Δ.commutator_centralizer_le_supportedDerived_polarPerp hQ hA Sᶜ
  dsimp only at h
  rw [Δ.polarPerp_compl_sup_eq_originalAnchor_sup hQ o hWS S] at h
  exact h

theorem TBJOmData.smallSupport_facts [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hr : 3 ≤ r)
    (hQ : (polarBilin Q).Nondegenerate) (hE : A ≤ orthDerived Q)
    (hdim : finrank K V = 2 * (r + 1)) (hminus : ¬ IsPlusType Q)
    (hrow : p ∣ Nat.card K - 1 ∨ Odd r ∧ p ∣ Nat.card K + 1)
    {S : Finset (Fin r)} (hS : S.Nonempty) (hS2 : S.card ≤ 2) :
    (polarBilin (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)).Nondegenerate ∧
      (finrank K ↥(Δ.originalAnchor ⊔ S.sup Δ.F.U) = 4 ∨
        finrank K ↥(Δ.originalAnchor ⊔ S.sup Δ.F.U) = 6) ∧
      IsSimpleGroup ↥(orthDerived (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)) ∧
      Group.IsPerfect ↥(orthDerived (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)) ∧
      (∃ a b : ↥(orthDerived (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)),
        a * b ≠ b * a) ∧
      (∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup
          (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype),
        ∀ k : ℕ, Odd k → g ^ k = 1 →
          g ∈ orthDerived (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)) := by
  classical
  have hr1 : 1 ≤ r := by omega
  let o : Fin r := ⟨0, by omega⟩
  have hdata := Δ.inactive_plane_of_minus hp2 hQ hE hr1 hdim hminus hrow
  dsimp only at hdata
  have hWdim : finrank K Δ.originalAnchor = 2 := hdata.2.1
  have hWreg : (polarBilin (Q.comp Δ.originalAnchor.subtype)).Nondegenerate := hdata.2.2.1
  have hcompl : IsCompl Δ.originalAnchor Δ.originalActive := hdata.2.2.2.1
  have htype : ∀ i : Fin r, IsPlusType (Q.comp Δ.originalAnchor.subtype) ↔
      ¬ IsPlusType (Q.comp (Δ.F.U i).subtype) := hdata.2.2.2.2
  have hWpoly : PolarNondegOn Q Δ.originalAnchor :=
    polarNondegOn_of_nondegenerate hWreg
  have hWUorth : ∀ i : Fin r,
      CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep Q Δ.originalAnchor (Δ.F.U i) := by
    intro i a ha u hu
    have ha' : a ∈ polarPerp Q Δ.originalActive := by
      simpa [TBJOmData.originalAnchor] using ha
    rw [polar_comm]
    exact (mem_polarPerp_iff.mp ha') u
      (by simpa [TBJOmData.originalActive] using Submodule.mem_iSup_of_mem i hu)
  have hdisj : ∀ i : Fin r, Disjoint Δ.originalAnchor (Δ.F.U i) := fun i =>
    CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint hWpoly (hWUorth i)
  have hreg : (polarBilin (Q.comp (Δ.originalAnchor ⊔ S.sup Δ.F.U).subtype)).Nondegenerate := by
    have h := coordSupport_nondegenerate (Δ.originalCoordinates hQ o hcompl)
      (Δ.originalCoordinates_quadratic_apply hQ o hcompl) hQ
      (Δ.originalPlaneForm_nondegenerate o) S
    rw [Δ.coordSupport_originalCoordinates hQ o hcompl S] at h
    exact h
  have hcard : S.card = 1 ∨ S.card = 2 := by
    have hpos : 0 < S.card := Finset.card_pos.mpr hS
    omega
  rcases hcard with hcard | hcard
  ·
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    have hsup : ({i} : Finset (Fin r)).sup Δ.F.U = Δ.F.U i := Finset.sup_singleton
    rw [hsup] at hreg ⊢
    have hdim4 : finrank K ↥(Δ.originalAnchor ⊔ Δ.F.U i) = 4 := by
      rw [CFSG.LieType.SeitzGeneration.finrank_sup_of_disjoint (hdisj i), hWdim,
        Δ.finrank_piece i]
    have hiso := CFSG.RankThree.PartOne.K159.isometryEquivSup Q Δ.originalAnchor (Δ.F.U i)
      (hdisj i) (hWUorth i)
    have hprod_not : ¬ IsPlusType ((Q.comp Δ.originalAnchor.subtype).prod
        (Q.comp (Δ.F.U i).subtype)) := by
      rw [CFSG.RankThree.PartOne.K159.isPlusType_prod_iff hWreg
        (Δ.originalPlaneForm_nondegenerate i) (d₁ := 1) (d₂ := 1) le_rfl le_rfl hWdim
        (Δ.finrank_piece i)]
      rintro ⟨hPQ, hQP⟩
      by_cases hP : IsPlusType (Q.comp Δ.originalAnchor.subtype)
      · exact (htype i).mp hP (hPQ hP)
      · exact hP ((htype i).mpr fun hQ => hP (hQP hQ))
    have hnotplus : ¬ IsPlusType (Q.comp (Δ.originalAnchor ⊔ Δ.F.U i).subtype) := by
      intro hp
      exact hprod_not ((isPlusType_congr hiso).mp hp)
    have hts : ∀ U : Submodule K ↥(Δ.originalAnchor ⊔ Δ.F.U i),
        finrank K U = finrank K ↥(Δ.originalAnchor ⊔ Δ.F.U i) / 2 →
          ∃ u ∈ U, (Q.comp (Δ.originalAnchor ⊔ Δ.F.U i).subtype) u ≠ 0 := by
      intro U hU
      by_contra h
      push Not at h
      apply hnotplus
      refine ⟨U, ?_, h⟩
      rw [hdim4] at hU
      omega
    obtain ⟨hsimple, hperfect, hna, -, hodd, -⟩ :=
      CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
        (Q.comp (Δ.originalAnchor ⊔ Δ.F.U i).subtype) hreg (Or.inl hdim4) hts
    push Not at hna
    refine ⟨hreg, Or.inl hdim4, hsimple, hperfect, hna, ?_⟩
    intro g hg k hk hpow
    exact hodd g hg (Odd.of_dvd_nat hk (orderOf_dvd_of_pow_eq_one hpow))
  ·
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hcard
    have hsup : ({i, j} : Finset (Fin r)).sup Δ.F.U = Δ.F.U i ⊔ Δ.F.U j := by
      rw [Finset.sup_insert, Finset.sup_singleton]
    rw [hsup] at hreg ⊢
    have hUUorth : CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep Q (Δ.F.U i) (Δ.F.U j) :=
      fun a ha b hb => Δ.F.orth i j hij a ha b hb
    have hUUdisj : Disjoint (Δ.F.U i) (Δ.F.U j) :=
      CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint
        (polarNondegOn_of_nondegenerate (Δ.originalPlaneForm_nondegenerate i)) hUUorth
    have hUij_dim : finrank K ↥(Δ.F.U i ⊔ Δ.F.U j) = 4 := by
      rw [CFSG.LieType.SeitzGeneration.finrank_sup_of_disjoint hUUdisj, Δ.finrank_piece i,
        Δ.finrank_piece j]
    have hWUij : CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep Q Δ.originalAnchor
        (Δ.F.U i ⊔ Δ.F.U j) := by
      intro a ha b hb
      obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp hb
      rw [polar_add_right, hWUorth i a ha b₁ hb₁, hWUorth j a ha b₂ hb₂, add_zero]
    have hWdisj : Disjoint Δ.originalAnchor (Δ.F.U i ⊔ Δ.F.U j) :=
      CFSG.LieType.SeitzGeneration.OrthBlk.OrthSep.disjoint hWpoly hWUij
    have hdim6 : finrank K ↥(Δ.originalAnchor ⊔ (Δ.F.U i ⊔ Δ.F.U j)) = 6 := by
      rw [CFSG.LieType.SeitzGeneration.finrank_sup_of_disjoint hWdisj, hWdim, hUij_dim]
    let QS : QuadraticForm K ↥(Δ.originalAnchor ⊔ (Δ.F.U i ⊔ Δ.F.U j)) :=
      Q.comp (Δ.originalAnchor ⊔ (Δ.F.U i ⊔ Δ.F.U j)).subtype
    obtain ⟨hq, hcenter, hodd⟩ :=
      CFSG.StandardType.OrthRestOdd.orthDerived_facts QS hreg (by rw [hdim6])
    let e : ↥(orthDerived QS) ≃*
        (↥(orthDerived QS) ⧸ Subgroup.center (orthDerived QS)) :=
      (QuotientGroup.quotientBot (G := ↥(orthDerived QS))).symm.trans
        (QuotientGroup.quotientMulEquivOfEq hcenter.symm)
    haveI : IsSimpleGroup (↥(orthDerived QS) ⧸ Subgroup.center (orthDerived QS)) := hq.2.1
    have hsimple : IsSimpleGroup ↥(orthDerived QS) := e.isSimpleGroup
    have hna : ∃ a b : ↥(orthDerived QS), a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hq.2.2
      exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    exact ⟨hreg, Or.inr hdim6, hsimple, hq.1, hna, hodd⟩

theorem TBJOmData.tau_mem_supportedDerived_of_smallSupport [Fact p.Prime] (hp2 : p ≠ 2)
    (Δ : TBJOmData Q p A r) (hr : 3 ≤ r)
    (hQ : (polarBilin Q).Nondegenerate) (hE : A ≤ orthDerived Q)
    (hdim : finrank K V = 2 * (r + 1)) (hminus : ¬ IsPlusType Q)
    (hrow : p ∣ Nat.card K - 1 ∨ Odd r ∧ p ∣ Nat.card K + 1)
    {S : Finset (Fin r)} (hS : S.Nonempty) (hS2 : S.card ≤ 2)
    {w : Fin r → Multiplicative (ZMod p)} (hw : ∀ i, i ∉ S → w i = 1) :
    Δ.τ w ∈ supportedDerived Q (Δ.originalAnchor ⊔ S.sup Δ.F.U) := by
  classical
  let V_S : Submodule K V := Δ.originalAnchor ⊔ S.sup Δ.F.U
  let t : V ≃ₗ[K] V := Δ.τ w
  have hx := Δ.oddOrderIsometry hp2 hQ hE w
  have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hx.mem
  have htpow : t ^ p = 1 := hx.pow_eq_one
  have hWfix : ∀ a ∈ Δ.originalAnchor, t a = a := by
    intro a ha
    exact Δ.polarPerp_iSup_le_commonFixed
      (by simpa [TBJOmData.originalAnchor, TBJOmData.originalActive] using ha)
      t (Δ.τ_range.le ⟨w, rfl⟩)
  have hpiece_map : ∀ i : Fin r, ∀ u ∈ Δ.F.U i, t u ∈ Δ.F.U i := by
    intro i u hu
    simpa [t, Δ.τ_eq] using Δ.F.mapsTo (piMul r p w) i u hu
  have hpiece_inv : ∀ i : Fin r, ∀ u ∈ Δ.F.U i, t⁻¹ u ∈ Δ.F.U i := by
    intro i u hu
    have h : t⁻¹ = Δ.τ w⁻¹ := by
      change (Δ.τ w)⁻¹ = Δ.τ w⁻¹
      exact (map_inv Δ.τ w).symm
    rw [h, Δ.τ_eq]
    exact Δ.F.mapsTo (piMul r p w⁻¹) i u hu
  have hSsup_map : S.sup Δ.F.U ≤ Submodule.comap t.toLinearMap (S.sup Δ.F.U) := by
    refine Finset.sup_le fun i hi => ?_
    intro u hu
    rw [Submodule.mem_comap]
    exact Finset.le_sup (f := Δ.F.U) hi (hpiece_map i u hu)
  have hSsup_inv : S.sup Δ.F.U ≤ Submodule.comap t⁻¹.toLinearMap (S.sup Δ.F.U) := by
    refine Finset.sup_le fun i hi => ?_
    intro u hu
    rw [Submodule.mem_comap]
    exact Finset.le_sup (f := Δ.F.U) hi (hpiece_inv i u hu)
  have hWfix_inv : ∀ a ∈ Δ.originalAnchor, t⁻¹ a = a := by
    intro a ha
    calc t⁻¹ a = t⁻¹ (t a) := by rw [hWfix a ha]
      _ = a := t.symm_apply_apply a
  have hmap : ∀ v ∈ V_S, t v ∈ V_S := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (by rw [hWfix a ha]; exact ha)
      (Submodule.mem_comap.mp (hSsup_map hb))
  have hinv : ∀ v ∈ V_S, t⁻¹ v ∈ V_S := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (by rw [hWfix_inv a ha]; exact ha)
      (Submodule.mem_comap.mp (hSsup_inv hb))
  let tS : V_S ≃ₗ[K] V_S := restrictEquiv V_S t hmap hinv
  have htS_O : tS ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp V_S.subtype) :=
    CFSG.LinearAlgebra.restrictEquiv_mem_orthogonalGroup htO hmap hinv
  have htS_pow : tS ^ p = 1 := by
    ext x
    rw [CFSG.LinearAlgebra.restrictEquiv_pow_apply V_S t hmap hinv p x, htpow]
    rfl
  have hmem : tS ∈ orthDerived (Q.comp V_S.subtype) := by
    have hfacts := Δ.smallSupport_facts hp2 hr hQ hE hdim hminus hrow hS hS2
    exact hfacts.2.2.2.2.2 tS htS_O p ((Fact.out : p.Prime).odd_of_ne_two hp2) htS_pow
  have hperpfix : ∀ v ∈ suppPerp Q V_S, t v = v := by
    intro v hv
    rw [← mem_fixedSpace]
    rw [Δ.mem_fixedSpace_iff]
    intro j hj u hu
    have hjS : j ∈ S := by
      by_contra hjs
      have hwj : w j = 1 := hw j hjs
      rw [hwj] at hj
      simpa using hj
    exact mem_suppPerp.mp hv u
      (show u ∈ V_S from Submodule.mem_sup_right (Finset.le_sup (f := Δ.F.U) hjS hu))
  exact mem_supportedDerived.mpr ⟨hperpfix, tS, hmem, fun x => rfl⟩

theorem TBJOmData.commute_supportedDerived_of_zeroOn [Fact p.Prime]
    (Δ : TBJOmData Q p A r)
    (hQ : (polarBilin Q).Nondegenerate) (hE : A ≤ orthDerived Q)
    (o : Fin r) (hWS : IsCompl Δ.originalAnchor Δ.originalActive)
    (S : Finset (Fin r)) {w : Fin r → Multiplicative (ZMod p)}
    (hw : ∀ i ∈ S, w i = 1) :
    ∀ g ∈ supportedDerived Q (Δ.originalAnchor ⊔ S.sup Δ.F.U),
      Commute (Δ.τ w) g := by
  classical
  let V_S : Submodule K V := Δ.originalAnchor ⊔ S.sup Δ.F.U
  let t : V ≃ₗ[K] V := Δ.τ w
  have hreg : (polarBilin (Q.comp V_S.subtype)).Nondegenerate := by
    have h := coordSupport_nondegenerate (Δ.originalCoordinates hQ o hWS)
      (Δ.originalCoordinates_quadratic_apply hQ o hWS) hQ
      (Δ.originalPlaneForm_nondegenerate o) S
    rw [Δ.coordSupport_originalCoordinates hQ o hWS S] at h
    exact h
  have htA : t ∈ A := by
    rw [← Δ.τ_range]
    exact ⟨w, rfl⟩
  have htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    orthDerived_le_orthogonalGroup_of_commutator Q (hE htA)
  have hWfix : ∀ a ∈ Δ.originalAnchor, t a = a := by
    intro a ha
    exact Δ.polarPerp_iSup_le_commonFixed
      (by simpa [TBJOmData.originalAnchor, TBJOmData.originalActive] using ha)
      t (Δ.τ_range.le ⟨w, rfl⟩)
  have hSfix : ∀ b ∈ S.sup Δ.F.U, t b = b := by
    intro b hb
    have hle : S.sup Δ.F.U ≤ fixedSpace t :=
      Finset.sup_le fun i hi => by
        have hi0 : toAdd (w i) = 0 := by simp [hw i hi]
        simpa [t] using Δ.piece_le_fixedSpace w hi0
    exact mem_fixedSpace.mp (hle hb)
  have hfix : ∀ v ∈ V_S, t v = v := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hWfix a ha, hSfix b hb]
  intro g hg
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq hreg htO hfix
    (fun x hx => supportedDerived_apply_mem hg hx)
    (fun x hx => supportedDerived_apply_perp hg hx)

end OrthTorus

end CFSG.StandardType

end
