module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusResGroup
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusLeviRes
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitCoverTorus
import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusData
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailLeviPPrime
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.AGLEmbedding.LeviBlock
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

@[expose] noncomputable def om6mX (b c : K) :
    Subgroup ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) :=
  ((orthResDer K b c 1).map (orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num))).subgroupOf
    (orthElementaryGroup (quadTail 2 (minusTailForm K b c)))

theorem om6m_orthLeviRes_injective :
    Function.Injective (orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num)) := by
  intro B B' h
  have h2 := congrArg (orthResMat (K := K) (A := Fin 2 → K) (show 1 ≤ 2 by norm_num)) h
  rw [orthResMat_orthLeviRes, orthResMat_orthLeviRes] at h2
  exact LinearEquiv.ext (LinearMap.congr_fun h2)

private theorem commutator_orthogonalGroup_quadTail_minus_two_D09
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail 2 (minusTailForm K b c)),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail 2 (minusTailForm K b c))⁆ =
        orthElementaryGroup (quadTail 2 (minusTailForm K b c)) := by
  let ψ : (quadTail 2 (minusTailForm K b c)).IsometryEquiv (quadMinus 3 K b c) :=
    minusTailIsometry 3 K b c
  apply Subgroup.map_injective (f := (LinearEquiv.autCongr ψ.toLinearEquiv).toMonoidHom)
    (LinearEquiv.autCongr ψ.toLinearEquiv).injective
  rw [orthMinus_map_autCongr_commutator ψ,
    commutator_orthogonalGroup_quadMinus_of_two_le (n := 3) (by norm_num) hirr]
  exact (CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.elementaryGroup_map ψ).symm

theorem om6m_map_orthLeviRes_le (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (orthResDer K b c 1).map (orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num)) ≤
      orthElementaryGroup (quadTail 2 (minusTailForm K b c)) := by
  intro y hy
  obtain ⟨B, hB, rfl⟩ := hy
  rw [← commutator_orthogonalGroup_quadTail_minus_two_D09 (K := K) (b := b) (c := c) hirr]
  exact orthLeviRes_mem_commutator (A := Fin 2 → K) (qA := minusTailForm K b c)
    (show 1 ≤ 2 by norm_num) hB

@[expose] noncomputable def om6mXEquiv (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ↥(om6mX b c) ≃* ↥(orthResDer K b c 1) :=
  (Subgroup.subgroupOfEquivOfLe (om6m_map_orthLeviRes_le hirr)).trans
    ((orthResDer K b c 1).equivMapOfInjective _ om6m_orthLeviRes_injective).symm

private theorem om6m_prodCongr_swapAll_mem_D09 {r : ℕ} :
    ((swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K))) ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)) := by
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun v => ?_
  rw [LinearEquiv.prodCongr_apply]
  change quadTail r (minusTailForm K b c) ((swapAll r K) v.1, v.2) =
    quadTail r (minusTailForm K b c) v
  rw [quadTail_apply, quadTail_apply,
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup swapAll_mem_orthogonalGroup]

private theorem om6m_prodCongr_swapAll_mul_self_D09 {r : ℕ} :
    ((swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K))) *
        ((swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K))) = 1 := by
  refine LinearEquiv.ext fun v => ?_
  simp only [LinearEquiv.mul_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  rw [show (swapAll r K) ((swapAll r K) v.1) = v.1 by
    rw [← LinearEquiv.mul_apply, swapAll_mul_self]
    rfl]
  rfl

private theorem om6m_prodCongr_swapAll_conj_tailDiag_D09 {r : ℕ} (t : Fin r → Kˣ) :
    ((swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K))) * tailDiag r t 1 *
        ((swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K))) = tailDiag r t⁻¹ 1 := by
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply]
  change ((swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K)))
      (tailDiag r t 1 (((swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K))) v)) =
    tailDiag r t⁻¹ 1 v
  rw [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, tailDiag_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, tailDiag_apply]
  refine Prod.ext ?_ rfl
  rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, swapAll_mul_torusElt_mul_swapAll]

private theorem om6m_tailDiag_inv_D09 {r : ℕ} (t : Fin r → Kˣ) :
    (tailDiag r t (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)))⁻¹ =
      tailDiag r t⁻¹ (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) := by
  rw [inv_eq_iff_mul_eq_one, tailDiag_mul, mul_inv_cancel, mul_one, tailDiag_one_one]

private theorem om6m_commutator_swapAll_tailDiag_D09 {r : ℕ} (t : Fin r → Kˣ) :
    ⁅(swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K)),
      tailDiag r t (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))⁆ =
      tailDiag r (t⁻¹ * t⁻¹) (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)) := by
  have hinv : ((swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K)))⁻¹ =
      (swapAll r K).prodCongr (LinearEquiv.refl K (Fin 2 → K)) :=
    inv_eq_of_mul_eq_one_right (om6m_prodCongr_swapAll_mul_self_D09 (K := K) (r := r))
  rw [commutatorElement_def, hinv, om6m_prodCongr_swapAll_conj_tailDiag_D09 t,
    om6m_tailDiag_inv_D09 t,
    tailDiag_mul t⁻¹ t⁻¹ (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))
      (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K)), mul_one]

theorem om6m_tailDiag_mem_commutator {r : ℕ} (t : Fin r → Kˣ) :
    tailDiag r t 1 ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c)),
      TauCeti.QuadraticMap.orthogonalGroup (quadTail r (minusTailForm K b c))⁆ := by
  haveI : Finite Kˣ := Finite.of_injective (fun u : Kˣ => (u : K)) fun _ _ => Units.ext
  have hinj : Function.Injective fun x : Kˣ => x⁻¹ * x⁻¹ := by
    intro x y h
    have h' : ((x⁻¹ : Kˣ) : K) * ((x⁻¹ : Kˣ) : K) =
        ((y⁻¹ : Kˣ) : K) * ((y⁻¹ : Kˣ) : K) := by
      rw [← Units.val_mul, ← Units.val_mul]
      exact congrArg Units.val h
    exact inv_injective (Units.ext (eq_of_mul_self_eq_mul_self h'))
  choose e he using fun i => (Finite.injective_iff_surjective.1 hinj) (t i)
  have ht : t = e⁻¹ * e⁻¹ := funext fun i => (he i).symm
  rw [ht, ← om6m_commutator_swapAll_tailDiag_D09 (K := K) (r := r) e]
  refine Subgroup.commutator_mem_commutator
    (om6m_prodCongr_swapAll_mem_D09 (K := K) (b := b) (c := c) (r := r)) ?_
  rw [tailDiag_eq_dMap]
  exact dMap_mem_orthogonalGroup (diagGL e) (one_mem _)

private noncomputable def tailDiag2Hom_D09 :
    Kˣ →* (((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) where
  toFun u := tailDiag 2 ![u, u⁻¹] 1
  map_one' := by
    have h1 : (![1, (1 : Kˣ)⁻¹] : Fin 2 → Kˣ) = 1 := by
      funext i; fin_cases i <;> simp
    rw [h1, tailDiag_one_one]
  map_mul' u v := by
    have h : (![u, u⁻¹] * ![v, v⁻¹] : Fin 2 → Kˣ) = ![u * v, (u * v)⁻¹] := by
      funext i; fin_cases i <;> simp [Pi.mul_apply, mul_inv, mul_comm]
    rw [tailDiag_mul, h, mul_one]

private theorem tailDiag2Hom_D09_injective :
    Function.Injective (tailDiag2Hom_D09 (K := K)) := by
  intro u v h
  have hfst : torusElt 2 K ![u, u⁻¹] = torusElt 2 K ![v, v⁻¹] := by
    refine LinearEquiv.ext fun x => ?_
    have hx := congrArg (fun f : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) => (f (x, 0)).1) h
    simpa [tailDiag2Hom_D09, tailDiag_apply] using hx
  have := congrFun (torusElt_injective (K := K) (r := 2) hfst) 0
  simpa using this

theorem om6m_orderOf_eq_of_tailDiag {s : Kˣ}
    {g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hg : (g : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
      tailDiag 2 ![s, s⁻¹] 1) :
    orderOf g = orderOf s := by
  have h1 : orderOf (g : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) = orderOf s := by
    rw [hg]
    exact orderOf_injective (tailDiag2Hom_D09 (K := K)) tailDiag2Hom_D09_injective s
  rw [← Subgroup.orderOf_coe g]
  exact h1

private theorem om6m_hiPart_torusElt_two_D09 (a : Fin 2 → Kˣ) (v : Fin 2 ⊕ Fin 2 → K) :
    hiPart (show 1 ≤ 2 by norm_num) (torusElt 2 K a v) =
      torusElt (2 - 1) K
        (fun t => a (splitIdx (show 1 ≤ 2 by norm_num) (Sum.inr t)))
        (hiPart (show 1 ≤ 2 by norm_num) v) := by
  funext t
  rcases t with t | t <;> rfl

private theorem om6m_splitIdx_inr_zero_D09 {hj : 1 ≤ 2} :
    splitIdx hj (Sum.inr (0 : Fin (2 - 1))) = (1 : Fin 2) := by
  apply Fin.ext
  simpa using splitIdx_inr hj (0 : Fin (2 - 1))

private theorem om6m_splitIdx_symm_one_D09 {hj : 1 ≤ 2} :
    (splitIdx hj).symm (1 : Fin 2) = Sum.inr (0 : Fin (2 - 1)) := by
  rw [← om6m_splitIdx_inr_zero_D09]
  exact Equiv.symm_apply_apply _ _

private theorem om6m_tailDiag_proj_D09 (s : Kˣ)
    (v : (Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) :
    orthResProj K (Fin 2 → K) (show 1 ≤ 2 by norm_num) (tailDiag 2 ![s, s⁻¹] 1 v) =
      tailDiag 1 ![s⁻¹] 1
        (orthResProj K (Fin 2 → K) (show 1 ≤ 2 by norm_num) v) := by
  change (hiPart (show 1 ≤ 2 by norm_num) (torusElt 2 K ![s, s⁻¹] v.1), v.2) =
    (torusElt 1 K ![s⁻¹] (hiPart (show 1 ≤ 2 by norm_num) v.1), v.2)
  refine Prod.ext (funext fun c => ?_) (funext fun a => ?_)
  · rw [om6m_hiPart_torusElt_two_D09]
    apply congrArg (fun a : Fin (2 - 1) → Kˣ =>
      (torusElt (2 - 1) K a) (hiPart (show 1 ≤ 2 by norm_num) v.1) c)
    funext t
    have ht : t = 0 := by
      apply Fin.ext
      omega
    rw [ht, om6m_splitIdx_inr_zero_D09]
    rfl
  · rfl

private theorem om6m_tailDiag_incl_D09 (s : Kˣ)
    (u : (Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) :
    tailDiag 2 ![s, s⁻¹] 1
        (orthResIncl K (Fin 2 → K) (show 1 ≤ 2 by norm_num) u) =
      orthResIncl K (Fin 2 → K) (show 1 ≤ 2 by norm_num) (tailDiag 1 ![s⁻¹] 1 u) := by
  change (torusElt 2 K ![s, s⁻¹] (joinHi (show 1 ≤ 2 by norm_num) 0 u.1), u.2) =
    (joinHi (show 1 ≤ 2 by norm_num) 0 (torusElt 1 K ![s⁻¹] u.1), u.2)
  refine Prod.ext (funext fun c => ?_) (funext fun a => ?_)
  · rcases c with p | p <;> obtain ⟨i, rfl⟩ := (splitIdx (show 1 ≤ 2 by norm_num)).surjective p <;>
      rcases i with i | i <;>
      (have hi : i = 0 := by apply Fin.ext; omega) <;>
      rw [hi] <;>
      (try rw [om6m_splitIdx_inr_zero_D09]) <;>
      simp only [joinHi, torusElt_apply, splitIdx_inl, splitIdx_inr, Equiv.symm_apply_apply,
        om6m_splitIdx_symm_one_D09, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff] <;>
      simp
  · rfl

private theorem om6m_mul_conj_apply_D09
    (D B : ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)))
    (x : (Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) :
    (D * B * D⁻¹) (D x) = D (B x) := by
  simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]

theorem om6m_tailDiag_conj_orthLeviRes (s : Kˣ)
    (B : ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K))) :
    tailDiag 2 ![s, s⁻¹] 1 * orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num) B *
        (tailDiag 2 ![s, s⁻¹] 1)⁻¹ =
      orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num)
        (tailDiag 1 ![s⁻¹] 1 * B * (tailDiag 1 ![s⁻¹] 1)⁻¹) := by
  rw [mul_inv_eq_iff_eq_mul]
  refine LinearEquiv.ext fun v => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, orthLeviRes_apply, orthLeviRes_apply,
    orthResExt_apply, orthResExt_apply, map_add]
  congr 1
  rw [om6m_tailDiag_incl_D09, om6m_tailDiag_proj_D09, map_sub]
  congr 1
  set D : ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) ≃ₗ[K]
    ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) := tailDiag 1 ![s⁻¹] 1
  set y := (orthResProj K (Fin 2 → K) (show 1 ≤ 2 by norm_num)) v
  congr 1
  change D (B y) = (D * B * D⁻¹) (D y)
  rw [om6m_mul_conj_apply_D09]

private theorem om6m_tailDiag_one_mem_orthogonalGroup_D09 (s : Kˣ) :
    tailDiag 1 ![s⁻¹] 1 ∈
      TauCeti.QuadraticMap.orthogonalGroup (quadTail 1 (minusTailForm K b c)) := by
  rw [tailDiag_eq_dMap]
  exact dMap_mem_orthogonalGroup (diagGL ![s⁻¹]) (one_mem _)

private theorem om6m_orthResDer_le_orthogonalGroup_D09 :
    orthResDer K b c 1 ≤ TauCeti.QuadraticMap.orthogonalGroup (quadTail 1 (minusTailForm K b c)) :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem om6m_mem_normalizer_om6mX {s : Kˣ}
    {g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hg : (g : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
      tailDiag 2 ![s, s⁻¹] 1) :
    g ∈ Subgroup.normalizer (om6mX b c : Set ↥(orthElementaryGroup
      (quadTail 2 (minusTailForm K b c)))) := by
  haveI : Finite ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) := by
    haveI : Finite (((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) :=
      finite_orthLinearEquiv (K := K) (M := ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)))
    exact Finite.of_injective Subtype.val Subtype.val_injective
  haveI : Finite (om6mX b c : Set ↥(orthElementaryGroup
      (quadTail 2 (minusTailForm K b c)))) := Finite.of_injective _ Subtype.val_injective
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨B, hB, hBn⟩ := Subgroup.mem_subgroupOf.1 hn
  refine Subgroup.mem_subgroupOf.2
    ⟨tailDiag 1 ![s⁻¹] 1 * B * (tailDiag 1 ![s⁻¹] 1)⁻¹, ?_, ?_⟩
  · rw [show tailDiag 1 ![s⁻¹] 1 * B * (tailDiag 1 ![s⁻¹] 1)⁻¹ =
        ⁅tailDiag 1 ![s⁻¹] 1, B⁆ * B by rw [commutatorElement_def]; group]
    exact mul_mem (Subgroup.commutator_mem_commutator
      (om6m_tailDiag_one_mem_orthogonalGroup_D09 (K := K) (b := b) (c := c) s)
      (om6m_orthResDer_le_orthogonalGroup_D09 (K := K) (b := b) (c := c) hB)) hB
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hg, ← hBn, om6m_tailDiag_conj_orthLeviRes]

private noncomputable def tailDiag1Hom_D09 :
    Kˣ →* (((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K))) where
  toFun u := tailDiag 1 ![u] 1
  map_one' := by
    have h1 : (![1] : Fin 1 → Kˣ) = 1 := by funext i; fin_cases i <;> simp
    rw [h1, tailDiag_one_one]
  map_mul' u v := by
    have h : (![u] * ![v] : Fin 1 → Kˣ) = ![u * v] := by
      funext i; fin_cases i <;> simp [Pi.mul_apply]
    rw [tailDiag_mul, h, mul_one]

private theorem tailDiag1Hom_D09_injective :
    Function.Injective (tailDiag1Hom_D09 (K := K)) := by
  intro u v h
  have hfst : torusElt 1 K ![u] = torusElt 1 K ![v] := by
    refine LinearEquiv.ext fun x => ?_
    have hx := congrArg (fun f : ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 1 ⊕ Fin 1 → K) × (Fin 2 → K)) => (f (x, 0)).1) h
    simpa [tailDiag1Hom_D09, tailDiag_apply] using hx
  have := congrFun (torusElt_injective (K := K) (r := 1) hfst) 0
  simpa using this

theorem om6m_exists_root_of_tailDiag (hirr : ∀ u : K, u ^ 2 + b * u + c ≠ 0) {s : Kˣ}
    {g : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c)))}
    (hg : (g : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
      tailDiag 2 ![s, s⁻¹] 1) :
    ∃ d ∈ om6mX b c, orderOf d = orderOf s ∧ ∀ x ∈ om6mX b c, g * x * g⁻¹ = d * x * d⁻¹ := by
  have hDmem : tailDiag 1 ![s⁻¹] 1 ∈ orthResDer K b c 1 :=
    om6m_tailDiag_mem_commutator (K := K) (b := b) (c := c) (r := 1) ![s⁻¹]
  have hd0E : orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num)
      (tailDiag 1 ![s⁻¹] 1) ∈ orthElementaryGroup (quadTail 2 (minusTailForm K b c)) :=
    om6m_map_orthLeviRes_le (K := K) (b := b) (c := c) hirr
      (Subgroup.mem_map_of_mem _ hDmem)
  let d : ↥(orthElementaryGroup (quadTail 2 (minusTailForm K b c))) :=
    ⟨orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num) (tailDiag 1 ![s⁻¹] 1), hd0E⟩
  refine ⟨d, ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ hDmem)
  · have h1 : orderOf (d : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
        ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) = orderOf s := by
      have hL : orderOf (orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num)
          (tailDiag 1 ![s⁻¹] 1)) = orderOf (tailDiag 1 ![s⁻¹] 1) :=
        orderOf_injective (orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num))
          om6m_orthLeviRes_injective (tailDiag 1 ![s⁻¹] 1)
      have hD : orderOf (tailDiag 1 ![s⁻¹] (1 : (Fin 2 → K) ≃ₗ[K] (Fin 2 → K))) =
          orderOf s := by
        have := orderOf_injective (tailDiag1Hom_D09 (K := K)) tailDiag1Hom_D09_injective s⁻¹
        simpa [tailDiag1Hom_D09, orderOf_inv] using this
      exact hL.trans hD
    rw [← Subgroup.orderOf_coe d]
    exact h1
  · intro x hx
    obtain ⟨B, hB, hBx⟩ := Subgroup.mem_subgroupOf.1 hx
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hg, ← hBx,
      show (d : ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)) ≃ₗ[K]
          ((Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K))) =
        orthLeviRes K (Fin 2 → K) (show 1 ≤ 2 by norm_num) (tailDiag 1 ![s⁻¹] 1) from rfl,
      om6m_tailDiag_conj_orthLeviRes, map_mul, map_mul, map_inv]

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
