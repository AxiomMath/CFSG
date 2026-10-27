module

public import CFSG.Monster.B.TwoA.Fischer.AdjointIntertwinerCore
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.E6.FixedE6 CFSG.Monster.B.E6.FixedE6Root CFSG.Monster.B.E6.StdF4
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.FieldExtension

section Gram

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι]

theorem linearIndependent_of_gram (B : LinearMap.BilinForm K M) {v : ι → M}
    {G : Matrix ι ι K} (hG : ∀ i k, B (v i) (v k) = G i k) (hdet : G.det ≠ 0) :
    LinearIndependent K v := by
  refine Fintype.linearIndependent_iff.2 fun g hg => ?_
  have hv : Matrix.vecMul g G = 0 := by
    funext k
    have h1 : B (∑ i, g i • v i) (v k) = Matrix.vecMul g G k := by
      rw [map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hG]
      rfl
    rw [← h1, hg, map_zero, LinearMap.zero_apply]
    rfl
  exact fun i => congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet hv) i

omit [DecidableEq ι] in
theorem span_eq_top_of_linearIndependent [Nonempty ι] {v : ι → M} (hv : LinearIndependent K v)
    (hdim : Module.finrank K M = Fintype.card ι) : Submodule.span K (Set.range v) = ⊤ :=
  hv.span_eq_top_of_card_eq_finrank hdim.symm

end Gram

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

section Equiv

variable {ρ : sliceGroup lab Y →* stdGroup} (hsurj : Function.Surjective (adjMap ρ))
  (hker : ∀ u, adjMap ρ u = 0 ↔ u ∈ ncommRad lab Y)

@[expose] def adjLin : NcommQuot lab Y →ₗ[ZMod 2] fixedL where
  toFun x := Quotient.liftOn' x (adjMap ρ) fun u v huv => by
    have h0 := (hker _).2 ((Submodule.quotientRel_def _).1 huv)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  map_add' x x' := by
    induction x using Submodule.Quotient.induction_on with | H u => ?_
    induction x' using Submodule.Quotient.induction_on with | H u' => ?_
    exact map_add (adjMap ρ) u u'
  map_smul' c x := by
    induction x using Submodule.Quotient.induction_on with | H u => ?_
    exact map_smul (adjMap ρ) c u

theorem adjLin_mk (u : Y →₀ ZMod 2) : adjLin hker (Submodule.Quotient.mk u) = adjMap ρ u := rfl

include hsurj in
theorem adjLin_bijective : Function.Bijective (adjLin hker) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun v => ?_⟩
  · induction x using Submodule.Quotient.induction_on with | H u => ?_
    rw [adjLin_mk] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((hker u).1 hx)
  · obtain ⟨u, rfl⟩ := hsurj v
    exact ⟨_, adjLin_mk hker u⟩

@[expose] def adjEquiv : NcommQuot lab Y ≃ₗ[ZMod 2] fixedL :=
  LinearEquiv.ofBijective (adjLin hker) (adjLin_bijective hsurj hker)

theorem adjEquiv_mk (u : Y →₀ ZMod 2) :
    adjEquiv hsurj hker (Submodule.Quotient.mk u) = adjMap ρ u := rfl

theorem adjEquiv_ncommVec (y : Y) : adjEquiv hsurj hker (ncommVec lab Y y) = adjVec ρ y := by
  rw [ncommVec, adjEquiv_mk, adjMap_single_one]

@[expose] def adjProd : NcommQuot lab Y →ₗ[ZMod 2] NcommQuot lab Y →ₗ[ZMod 2] NcommQuot lab Y :=
  (bracketBil.compl₁₂ (adjEquiv hsurj hker).toLinearMap (adjEquiv hsurj hker).toLinearMap).compr₂
    (adjEquiv hsurj hker).symm.toLinearMap

theorem adjEquiv_adjProd (x x' : NcommQuot lab Y) :
    adjEquiv hsurj hker (adjProd hsurj hker x x') =
      bracketL (adjEquiv hsurj hker x) (adjEquiv hsurj hker x') :=
  (adjEquiv hsurj hker).apply_symm_apply _

theorem adjProd_self (x : NcommQuot lab Y) : adjProd hsurj hker x x = 0 :=
  (adjEquiv hsurj hker).injective (by rw [adjEquiv_adjProd, bracketL_self', map_zero])

theorem adjProd_jacobi (x x' x'' : NcommQuot lab Y) :
    adjProd hsurj hker x (adjProd hsurj hker x' x'') +
        adjProd hsurj hker x' (adjProd hsurj hker x'' x) +
      adjProd hsurj hker x'' (adjProd hsurj hker x x') = 0 :=
  (adjEquiv hsurj hker).injective (by
    rw [map_add, map_add, adjEquiv_adjProd, adjEquiv_adjProd, adjEquiv_adjProd, adjEquiv_adjProd,
      adjEquiv_adjProd, adjEquiv_adjProd, bracketL_jacobi, map_zero])

end Equiv

namespace IsFischerSlice

variable (hS : IsFischerSlice act lab Y) {ρ : sliceGroup lab Y →* stdGroup}
  (hρ : Function.Injective ρ) (hroot : ∀ y : Y, ρ ⟨lab y, lab_mem_sliceGroup y.2⟩ ∈ rootClass)
include hS hρ hroot

section Minor

variable {yb : Fin 78 → Y} {G : Matrix (Fin 78) (Fin 78) (ZMod 2)} (hdet : G.det ≠ 0)
  (hG : ∀ i k, ncommInd lab (yb i) (yb k) = G i k)
include hdet hG

theorem adjMap_surjective :
    Function.Surjective (adjMap ρ) := by
  let e := basisL.equivFun
  have hv : LinearIndependent (ZMod 2) fun i => e (adjVec ρ (yb i)) := by
    refine linearIndependent_of_gram (formL.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap)
      (fun i k => ?_) hdet
    rw [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, hS.formL_adjVec hρ hroot, hG]
  have hspan := span_eq_top_of_linearIndependent hv
    (by rw [Module.finrank_fintype_fun_eq_card, card_label_E6, Fintype.card_fin])
  have hrange : LinearMap.range (e.toLinearMap ∘ₗ adjMap ρ) = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Finsupp.single (yb i) 1, by
      rw [LinearMap.comp_apply, adjMap_single_one, LinearEquiv.coe_coe]⟩
  intro v
  obtain ⟨u, hu⟩ := LinearMap.range_eq_top.1 hrange (e v)
  exact ⟨u, e.injective hu⟩

end Minor

section Props

variable (hsurj : Function.Surjective (adjMap ρ))
include hsurj

theorem adjMap_eq_zero_iff
    (u : Y →₀ ZMod 2) : adjMap ρ u = 0 ↔ u ∈ ncommRad lab Y := by
  rw [← LinearMap.mem_ker, hS.ker_adjMap hρ hroot hsurj]

theorem formL_adjEquiv
    (x x' : NcommQuot lab Y) :
    formL (adjEquiv hsurj (hS.adjMap_eq_zero_iff hρ hroot hsurj) x)
        (adjEquiv hsurj (hS.adjMap_eq_zero_iff hρ hroot hsurj) x') = ncommQuotForm lab Y x x' := by
  induction x using Submodule.Quotient.induction_on with | H u => ?_
  induction x' using Submodule.Quotient.induction_on with | H u' => ?_
  rw [adjEquiv_mk, adjEquiv_mk, hS.formL_adjMap hρ hroot, ncommQuotForm_mk]

omit hρ in
theorem adjEquiv_ncommQuotRep
    (hker : ∀ u, adjMap ρ u = 0 ↔ u ∈ ncommRad lab Y)
    (h : sliceGroup lab Y) (x : NcommQuot lab Y) :
    adjEquiv hsurj hker (ncommQuotRep act lab Y (sliceGroup lab Y) hS.mapsTo hS.lab_act h x) =
      actStar (SemidirectProduct.inl (ρ h)) (adjEquiv hsurj hker x) := by
  induction x using Submodule.Quotient.induction_on with | H u => ?_
  rw [ncommQuotRep_mk, adjEquiv_mk, adjEquiv_mk, hS.adjMap_ncommRep hroot, actStar_inl_eq_gL]

theorem ncommProd_mem_ncommRad
    {u : Y →₀ ZMod 2} (hu : u ∈ ncommRad lab Y)
    (u' : Y →₀ ZMod 2) :
    ncommProd act lab Y u u' ∈ ncommRad lab Y ∧ ncommProd act lab Y u' u ∈ ncommRad lab Y := by
  rw [← hS.ker_adjMap hρ hroot hsurj] at hu ⊢
  rw [LinearMap.mem_ker] at hu
  refine ⟨?_, ?_⟩ <;> rw [LinearMap.mem_ker, hS.adjMap_ncommProd hρ hroot, hu]
  · show bracketBil 0 (adjMap ρ u') = 0
    rw [map_zero, LinearMap.zero_apply]
  · show bracketBil (adjMap ρ u') 0 = 0
    rw [map_zero]

theorem adjProd_mk
    (u u' : Y →₀ ZMod 2) :
    adjProd hsurj (hS.adjMap_eq_zero_iff hρ hroot hsurj) (Submodule.Quotient.mk u)
        (Submodule.Quotient.mk u') = Submodule.Quotient.mk (ncommProd act lab Y u u') := by
  refine (adjEquiv hsurj (hS.adjMap_eq_zero_iff hρ hroot hsurj)).injective ?_
  rw [adjEquiv_adjProd, adjEquiv_mk, adjEquiv_mk, adjEquiv_mk, hS.adjMap_ncommProd hρ hroot]

theorem ncommQuotRep_lab
    (y : Y) (x : NcommQuot lab Y) :
    ncommQuotRep act lab Y (sliceGroup lab Y) hS.mapsTo hS.lab_act
        ⟨lab y, lab_mem_sliceGroup y.2⟩ x =
      x + adjProd hsurj (hS.adjMap_eq_zero_iff hρ hroot hsurj) (ncommVec lab Y y) x +
        ncommQuotForm lab Y (ncommVec lab Y y) x • ncommVec lab Y y := by
  refine (adjEquiv hsurj (hS.adjMap_eq_zero_iff hρ hroot hsurj)).injective ?_
  rw [hS.adjEquiv_ncommQuotRep hroot hsurj, actStar_inl_of_mem_rootClass (hroot y), map_add,
    map_add, map_smul, adjEquiv_adjProd, ← hS.formL_adjEquiv hρ hroot hsurj,
    adjEquiv_ncommVec]
  rfl

end Props

section Coord

variable {yb : Fin 78 → Y} {G : Matrix (Fin 78) (Fin 78) (ZMod 2)} (hdet : G.det ≠ 0)
  (hG : ∀ i k, ncommInd lab (yb i) (yb k) = G i k)
include hdet hG

omit hS hρ hroot in
theorem linearIndependent_ncommVec_yb :
    LinearIndependent (ZMod 2) fun i => ncommVec lab Y (yb i) :=
  linearIndependent_of_gram (ncommQuotForm lab Y)
    (fun i k => (ncommQuotForm_ncommVec lab Y _ _).trans (hG i k)) hdet

theorem finrank_ncommQuot :
    Module.finrank (ZMod 2) (NcommQuot lab Y) = 78 := by
  have hsurj := hS.adjMap_surjective hρ hroot hdet hG
  rw [((adjEquiv hsurj (hS.adjMap_eq_zero_iff hρ hroot hsurj)).trans
    basisL.equivFun).finrank_eq, Module.finrank_fintype_fun_eq_card, card_label_E6]

theorem span_ncommVec_yb :
    Submodule.span (ZMod 2) (Set.range fun i => ncommVec lab Y (yb i)) = ⊤ :=
  span_eq_top_of_linearIndependent (linearIndependent_ncommVec_yb hdet hG)
    (by rw [hS.finrank_ncommQuot hρ hroot hdet hG, Fintype.card_fin])

theorem ncommVec_eq_sum
    (y : Y) (c : Fin 78 → ZMod 2)
    (hc : G.mulVec c = fun i => ncommInd lab (yb i) y) :
    ncommVec lab Y y = ∑ i, c i • ncommVec lab Y (yb i) := by
  have hzero : ∀ k, ncommQuotForm lab Y (ncommVec lab Y (yb k))
      (∑ i, c i • ncommVec lab Y (yb i) - ncommVec lab Y y) = 0 := by
    intro k
    rw [map_sub, map_sum]
    simp only [map_smul, smul_eq_mul, ncommQuotForm_ncommVec, hG]
    have h := congrFun hc k
    simp only [Matrix.mulVec, dotProduct] at h
    rw [← h, sub_eq_zero]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hall : ∀ z, ncommQuotForm lab Y z
      (∑ i, c i • ncommVec lab Y (yb i) - ncommVec lab Y y) = 0 := by
    intro z
    have hz : z ∈ Submodule.span (ZMod 2) (Set.range fun i => ncommVec lab Y (yb i)) := by
      rw [hS.span_ncommVec_yb hρ hroot hdet hG]
      exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, hk⟩ := hz
      have hk' : ncommVec lab Y (yb k) = z := hk
      rw [← hk']
      exact hzero k
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add z z' _ _ hz hz' => rw [map_add, LinearMap.add_apply, hz, hz', add_zero]
    | smul a z _ hz => rw [map_smul, LinearMap.smul_apply, hz, smul_zero]
  have h0 := (ncommQuotForm_nondegenerate lab Y).2 _ hall
  exact (sub_eq_zero.1 h0).symm

end Coord

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
