module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTailBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.SeitzReduction.OmegaPilot QuadraticMap
open scoped commutatorElement

namespace OrthRestTail

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

section Eich

variable (Q : QuadraticForm K (ι → K)) (s t : ι)

omit [Fintype ι] in
@[expose] noncomputable def eichLin (w : ι → K) : (ι → K) →ₗ[K] (ι → K) where
  toFun v := v + v t • w + (polar Q v w + Q w * v t) • Pi.single s 1
  map_add' v v' := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, polar_add_left]
    ring
  map_smul' c v := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, polar_smul_left, RingHom.id_apply]
    ring

omit [Fintype ι] in
theorem eichLin_apply (w v : ι → K) :
    eichLin Q s t w v = v + v t • w + (polar Q v w + Q w * v t) • Pi.single s 1 :=
  rfl

variable {Q s t}

omit [Fintype ι] in
theorem eichLin_zero (v : ι → K) : eichLin Q s t 0 v = v := by
  rw [eichLin_apply, smul_zero, add_zero, polar_zero_right, QuadraticMap.map_zero, zero_mul,
    add_zero, zero_smul, add_zero]

omit [Fintype ι] in
theorem eichLin_apply_t (hst : IsHypCoord Q s t) {w : ι → K} (hw : w t = 0) (v : ι → K) :
    eichLin Q s t w v t = v t := by
  rw [eichLin_apply]
  simp [hw, hst.ne.symm]

omit [Fintype ι] in
theorem polar_eichLin (hst : IsHypCoord Q s t) (w v x : ι → K) :
    polar Q (eichLin Q s t w v) x =
      polar Q v x + v t * polar Q w x + (polar Q v w + Q w * v t) * x t := by
  rw [eichLin_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    hst.polar_left, smul_eq_mul, smul_eq_mul]

omit [Fintype ι] in
theorem eichLin_add (hst : IsHypCoord Q s t) {w w' : ι → K} (hw : w t = 0) (hw' : w' t = 0)
    (v : ι → K) : eichLin Q s t w (eichLin Q s t w' v) = eichLin Q s t (w + w') v := by
  have h1 := polar_eichLin hst w' v w
  have h2 := eichLin_apply_t hst hw' v
  rw [eichLin_apply Q s t w, h1, h2, hw, eichLin_apply Q s t w', eichLin_apply Q s t (w + w'),
    polar_add_right, QuadraticMap.map_add (⇑Q) w w', polar_comm Q w' w]
  funext k
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable [CharP K 2]

omit [Fintype ι] in
theorem map_eichLin (hst : IsHypCoord Q s t) {w : ι → K} (hw : w t = 0) (v : ι → K) :
    Q (eichLin Q s t w v) = Q v := by
  rw [eichLin_apply, QuadraticMap.map_add (⇑Q) (v + v t • w), QuadraticMap.map_add (⇑Q) v,
    QuadraticMap.map_smul,
    QuadraticMap.map_smul, hst.map_left, polar_add_left, polar_smul_left, polar_smul_right,
    polar_smul_right, polar_smul_right, polar_comm Q v (Pi.single s 1), hst.polar_left,
    polar_comm Q w (Pi.single s 1), hst.polar_left, hw]
  simp only [smul_eq_mul]
  linear_combination (v t * v t * Q w + v t * polar Q v w) * CharTwo.two_eq_zero (R := K)

omit [Fintype ι] in
theorem eichLin_eichLin (hst : IsHypCoord Q s t) {w : ι → K} (hw : w t = 0) (v : ι → K) :
    eichLin Q s t w (eichLin Q s t w v) = v := by
  rw [eichLin_add hst hw hw, show w + w = 0 from funext fun k => CharTwo.add_self_eq_zero (w k),
    eichLin_zero]

theorem toMatrix'_eichLin_mul_self (hst : IsHypCoord Q s t) {w : ι → K} (hw : w t = 0) :
    LinearMap.toMatrix' (eichLin Q s t w) * LinearMap.toMatrix' (eichLin Q s t w) = 1 := by
  rw [← LinearMap.toMatrix'_comp, show (eichLin Q s t w).comp (eichLin Q s t w) = LinearMap.id
    from LinearMap.ext (eichLin_eichLin hst hw), LinearMap.toMatrix'_id]

@[expose] noncomputable def eichGL (hst : IsHypCoord Q s t) (w : ι → K) (hw : w t = 0) :
    GL ι K :=
  ⟨LinearMap.toMatrix' (eichLin Q s t w), LinearMap.toMatrix' (eichLin Q s t w),
    toMatrix'_eichLin_mul_self hst hw, toMatrix'_eichLin_mul_self hst hw⟩

theorem eichGL_mulVec (hst : IsHypCoord Q s t) {w : ι → K} (hw : w t = 0) (v : ι → K) :
    ((eichGL hst w hw : GL ι K) : Matrix ι ι K) *ᵥ v = eichLin Q s t w v :=
  LinearMap.toMatrix'_mulVec _ v

theorem eichGL_mem_orth (hst : IsHypCoord Q s t) {w : ι → K} (hw : w t = 0) :
    eichGL hst w hw ∈ LargeEvenOrthGroup ⇑Q :=
  TableBSymp.mem_orthGroup_of_isometry fun v => by
    rw [eichGL_mulVec, map_eichLin hst hw]

omit [Fintype ι] [DecidableEq ι] [CharP K 2] in
theorem polar_isometry {f : (ι → K) → (ι → K)} (hf : ∀ v, Q (f v) = Q v)
    (hadd : ∀ v w, f (v + w) = f v + f w) (v w : ι → K) : polar Q (f v) (f w) = polar Q v w := by
  rw [polar, polar, ← hadd, hf, hf, hf]

omit [CharP K 2] in
theorem eichLin_conj {S : Set ι} (hs : s ∉ S) (ht : t ∉ S) {g : GL ι K}
    (hgS : g ∈ suppSub K S) (hgQ : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v) (w v : ι → K) :
    (g : Matrix ι ι K) *ᵥ eichLin Q s t w (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) =
      eichLin Q s t ((g : Matrix ι ι K) *ᵥ w) v := by
  have hgS' : IsSuppMat S (g : Matrix ι ι K) := hgS
  have hgiS : IsSuppMat S ((g⁻¹ : GL ι K) : Matrix ι ι K) := Subgroup.inv_mem _ hgS
  have he : (g : Matrix ι ι K) *ᵥ Pi.single s 1 = Pi.single s 1 :=
    hgS'.mulVec_eq_self fun k hk => by
      rw [Pi.single_apply, ite_eq_right_iff]
      intro h
      exact absurd (h ▸ hk) hs
  have hu : (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) t = v t := hgiS.1 v t ht
  have hp : polar Q (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) w =
      polar Q v ((g : Matrix ι ι K) *ᵥ w) := by
    rw [← polar_isometry hgQ (fun a b => mulVec_add _ a b), mulVec_inv_mulVec]
  rw [eichLin_apply, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, he, mulVec_inv_mulVec, hu,
    hp, ← hgQ w, eichLin_apply]

theorem eichGL_inv_mulVec (hst : IsHypCoord Q s t) {w : ι → K} (hw : w t = 0) (v : ι → K) :
    (((eichGL hst w hw)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v = eichLin Q s t w v :=
  LinearMap.toMatrix'_mulVec _ v

theorem eichGL_conj (hst : IsHypCoord Q s t) {S : Set ι} (hs : s ∉ S) (ht : t ∉ S)
    {g : GL ι K} (hgS : g ∈ suppSub K S) (hgQ : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    {w : ι → K} (hw : w t = 0) :
    g * eichGL hst w hw * g⁻¹ =
      eichGL hst ((g : Matrix ι ι K) *ᵥ w) (by rw [(mem_suppSub.mp hgS).1 w t ht, hw]) :=
  gl_ext fun v => by
    rw [mul_mulVec, mul_mulVec, eichGL_mulVec, eichGL_mulVec, eichLin_conj hs ht hgS hgQ]

theorem eichGL_commutator (hst : IsHypCoord Q s t) {S : Set ι} (hs : s ∉ S) (ht : t ∉ S)
    {g : GL ι K} (hgS : g ∈ suppSub K S) (hgQ : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v)
    {w : ι → K} (hw : w t = 0) :
    ⁅g, eichGL hst w hw⁆ = eichGL hst ((g : Matrix ι ι K) *ᵥ w + w)
      (by rw [Pi.add_apply, (mem_suppSub.mp hgS).1 w t ht, hw, add_zero]) := by
  rw [commutatorElement_def, eichGL_conj hst hs ht hgS hgQ hw]
  refine gl_ext fun v => ?_
  rw [mul_mulVec, eichGL_mulVec, eichGL_inv_mulVec, eichGL_mulVec,
    eichLin_add hst (by rw [(mem_suppSub.mp hgS).1 w t ht, hw]) hw]

@[expose] def eichSub (hst : IsHypCoord Q s t) (S : Set ι) : Subgroup (GL ι K) where
  carrier := {g | ∃ w : ι → K, w t = 0 ∧ (∀ k ∉ S, w k = 0) ∧
    ∀ v, (g : Matrix ι ι K) *ᵥ v = eichLin Q s t w v}
  one_mem' := ⟨0, rfl, fun _ _ => rfl, fun v => by rw [Units.val_one, one_mulVec, eichLin_zero]⟩
  mul_mem' := by
    rintro g h ⟨w, hw, hwS, hg⟩ ⟨w', hw', hwS', hh⟩
    refine ⟨w + w', by rw [Pi.add_apply, hw, hw', add_zero],
      fun k hk => by rw [Pi.add_apply, hwS k hk, hwS' k hk, add_zero], fun v => ?_⟩
    rw [mul_mulVec, hh, hg, eichLin_add hst hw hw']
  inv_mem' := by
    rintro g ⟨w, hw, hwS, hg⟩
    refine ⟨w, hw, hwS, fun v => ?_⟩
    have h1 : (g : Matrix ι ι K) *ᵥ eichLin Q s t w v = v := by rw [hg, eichLin_eichLin hst hw]
    calc ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v =
        ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ eichLin Q s t w v) := by
          rw [h1]
      _ = eichLin Q s t w v := inv_mulVec_mulVec g _

theorem eichGL_mem_eichSub (hst : IsHypCoord Q s t) {S : Set ι} {w : ι → K} (hw : w t = 0)
    (hwS : ∀ k ∉ S, w k = 0) : eichGL hst w hw ∈ eichSub hst S :=
  ⟨w, hw, hwS, eichGL_mulVec hst hw⟩

theorem eichSub_sq (hst : IsHypCoord Q s t) {S : Set ι} {g : GL ι K} (hg : g ∈ eichSub hst S) :
    g ^ 2 = 1 := by
  obtain ⟨w, hw, -, hgw⟩ := hg
  refine gl_ext fun v => ?_
  rw [pow_two, mul_mulVec, hgw, hgw, eichLin_eichLin hst hw, Units.val_one, one_mulVec]

theorem conj_mem_eichSub (hst : IsHypCoord Q s t) {S T : Set ι} (hs : s ∉ T) (ht : t ∉ T)
    {h : GL ι K} (hhT : h ∈ suppSub K T) (hhQ : ∀ v, Q ((h : Matrix ι ι K) *ᵥ v) = Q v)
    (hhS : ∀ w : ι → K, (∀ k ∉ S, w k = 0) → ∀ k ∉ S, ((h : Matrix ι ι K) *ᵥ w) k = 0)
    {g : GL ι K} (hg : g ∈ eichSub hst S) : h * g * h⁻¹ ∈ eichSub hst S := by
  obtain ⟨w, hw, hwS, hgw⟩ := hg
  have hg' : g = eichGL hst w hw := gl_ext fun v => by rw [hgw, eichGL_mulVec]
  rw [hg', eichGL_conj hst hs ht hhT hhQ hw]
  exact eichGL_mem_eichSub hst _ (hhS w hwS)

end Eich

end OrthRestTail

end CFSG.StandardType
