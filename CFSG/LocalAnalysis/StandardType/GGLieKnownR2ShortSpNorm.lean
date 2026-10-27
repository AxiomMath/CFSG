module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortSpDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpCent

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique.B113Lie.Sp
  CFSG.LocalAnalysis.ComponentInitial

open scoped Matrix

private theorem spJ_mulVec_dotProduct_comm {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u v : Fin n ⊕ Fin n → F) :
    ((spJ n F) *ᵥ u) ⬝ᵥ v = u ⬝ᵥ ((spJ n F) *ᵥ v) := by
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, spJ_transpose_char_two]

private theorem spForm_β_symm {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u v : Fin n ⊕ Fin n → F) : (spForm n F).β u v = (spForm n F).β v u := by
  rw [spForm_β, spForm_β, dotProduct_comm u, spJ_mulVec_dotProduct_comm]

private theorem spForm_β_add_left {n : ℕ} {F : Type} [Field F]
    (u u' v : Fin n ⊕ Fin n → F) :
    (spForm n F).β (u + u') v = (spForm n F).β u v + (spForm n F).β u' v :=
  (spForm n F).add_left u u' v

private theorem spForm_β_smul_left {n : ℕ} {F : Type} [Field F]
    (c : F) (u v : Fin n ⊕ Fin n → F) :
    (spForm n F).β (c • u) v = c * (spForm n F).β u v := by
  rw [(spForm n F).smul_left]
  rfl

private def siegelE (n : ℕ) (F : Type) [Field F] (a₁ a₂ : Fin n ⊕ Fin n → F) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
  Matrix.vecMulVec a₁ ((spJ n F) *ᵥ a₂) + Matrix.vecMulVec a₂ ((spJ n F) *ᵥ a₁)

private theorem siegelE_mulVec {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (a₁ a₂ v : Fin n ⊕ Fin n → F) :
    (siegelE n F a₁ a₂) *ᵥ v =
      (a₂ ⬝ᵥ ((spJ n F) *ᵥ v)) • a₁ + (a₁ ⬝ᵥ ((spJ n F) *ᵥ v)) • a₂ := by
  rw [siegelE, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  simp only [IsCentralScalar.op_smul_eq_smul, spJ_mulVec_dotProduct_comm]

private theorem siegelE_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F} (h12 : (spForm n F).β a₁ a₂ = 0) :
    siegelE n F a₁ a₂ * siegelE n F a₁ a₂ = 0 := by
  have h21 : (spForm n F).β a₂ a₁ = 0 := by rw [spForm_β_symm, h12]
  have h11 : (spForm n F).β a₁ a₁ = 0 := spForm_self n F a₁
  have h22 : (spForm n F).β a₂ a₂ = 0 := spForm_self n F a₂
  have e11 : ((spJ n F) *ᵥ a₂) ⬝ᵥ a₁ = 0 := by
    rw [spJ_mulVec_dotProduct_comm]; exact h21
  have e12 : ((spJ n F) *ᵥ a₂) ⬝ᵥ a₂ = 0 := by
    rw [spJ_mulVec_dotProduct_comm]; exact h22
  have e21 : ((spJ n F) *ᵥ a₁) ⬝ᵥ a₁ = 0 := by
    rw [spJ_mulVec_dotProduct_comm]; exact h11
  have e22 : ((spJ n F) *ᵥ a₁) ⬝ᵥ a₂ = 0 := by
    rw [spJ_mulVec_dotProduct_comm]; exact h12
  rw [siegelE, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  simp only [Matrix.vecMulVec_mul_vecMulVec, e11, e12, e21, e22, zero_smul,
    Matrix.vecMulVec_zero, add_zero]

private theorem siegelE_mul_formula {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F} (h12 : (spForm n F).β a₁ a₂ = 0) (c d : F) :
    (1 + c • siegelE n F a₁ a₂) * (1 + d • siegelE n F a₁ a₂) =
      1 + (c + d) • siegelE n F a₁ a₂ := by
  have hEE := siegelE_mul_self (n := n) (F := F) (a₁ := a₁) (a₂ := a₂) h12
  have hprod : (c • siegelE n F a₁ a₂) * (d • siegelE n F a₁ a₂) = 0 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hEE, smul_zero, smul_zero]
  calc (1 + c • siegelE n F a₁ a₂) * (1 + d • siegelE n F a₁ a₂)
      = (1 + c • siegelE n F a₁ a₂) * 1 +
          (1 + c • siegelE n F a₁ a₂) * (d • siegelE n F a₁ a₂) := by rw [Matrix.mul_add]
    _ = (1 + c • siegelE n F a₁ a₂) +
          (1 * (d • siegelE n F a₁ a₂) +
            (c • siegelE n F a₁ a₂) * (d • siegelE n F a₁ a₂)) := by
          rw [mul_one, Matrix.add_mul]
    _ = (1 + c • siegelE n F a₁ a₂) + d • siegelE n F a₁ a₂ := by
          rw [one_mul, hprod, add_zero]
    _ = 1 + (c + d) • siegelE n F a₁ a₂ := by rw [add_assoc, ← add_smul]

private theorem mulVec_one_add_smul_siegelE {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (a₁ a₂ : Fin n ⊕ Fin n → F) (c : F) (v : Fin n ⊕ Fin n → F) :
    Matrix.mulVec (1 + c • siegelE n F a₁ a₂) v =
      v + (c * (a₂ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₁ +
        (c * (a₁ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₂ := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, siegelE_mulVec]
  simp only [smul_add, smul_smul, add_assoc]

theorem exists_mulVec_of_mem_spAltSiegel {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ : Fin n ⊕ Fin n → F} (h12 : (spForm n F).β a₁ a₂ = 0) {g : StatedSp n F}
    (hg : g ∈ spAltSiegel n F a₁ a₂) :
    ∃ c : F, ∀ v : Fin n ⊕ Fin n → F,
      Matrix.mulVec ((g : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v =
        v + (c * (a₂ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₁ +
          (c * (a₁ ⬝ᵥ Matrix.mulVec (spJ n F) v)) • a₂ := by
  have hg' : ((g : StatedSp n F) : GL (Fin n ⊕ Fin n) F) ∈
      Subgroup.closure {x : GL (Fin n ⊕ Fin n) F |
        ∃ c : F, (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
          1 + c • siegelE n F a₁ a₂} := hg
  have hmem : ∃ c : F, (((g : StatedSp n F) : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 + c • siegelE n F a₁ a₂ := by
    refine Subgroup.closure_induction
      (p := fun (x : GL (Fin n ⊕ Fin n) F) _ => ∃ c : F,
        (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 + c • siegelE n F a₁ a₂)
      ?_ ?_ ?_ ?_ hg'
    · rintro x ⟨c, hc⟩
      exact ⟨c, hc⟩
    · exact ⟨0, by rw [Units.val_one, zero_smul, add_zero]⟩
    · rintro x y hx hy ⟨c, hc⟩ ⟨d, hd⟩
      refine ⟨c + d, ?_⟩
      rw [Units.val_mul, hc, hd, siegelE_mul_formula h12 c d]
    · rintro x hx ⟨c, hc⟩
      refine ⟨c, ?_⟩
      have hxx : x * x = 1 := by
        apply Units.ext
        rw [Units.val_mul, hc, siegelE_mul_formula h12 c c, CharTwo.add_self_eq_zero,
          zero_smul, add_zero, Units.val_one]
      rw [inv_eq_of_mul_eq_one_right hxx]
      exact hc
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, fun v => by rw [hc, mulVec_one_add_smul_siegelE]⟩

private theorem siegel_conj_vector {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (α β γ δ c : F) (a₁ a₂ v : Fin n ⊕ Fin n → F) :
    (spForm n F).β (γ • a₁ + δ • a₂) v • (c • (α • a₁ + β • a₂)) +
      (spForm n F).β (α • a₁ + β • a₂) v • (c • (γ • a₁ + δ • a₂)) =
    (c * (α * δ + β * γ) * (spForm n F).β a₂ v) • a₁ +
      (c * (α * δ + β * γ) * (spForm n F).β a₁ v) • a₂ := by
  simp only [spForm_β_add_left, spForm_β_smul_left]
  match_scalars
  · have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (c * α * γ * (spForm n F).β a₁ v) * h2
  · have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (c * β * δ * (spForm n F).β a₂ v) * h2

private theorem conj_mem_spAltSiegel {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂) {g : StatedSp n F}
    (hg : g ∈ SymplecticFlag.stabilizer n F (Submodule.span F {a₁, a₂})) :
    ∀ h ∈ spAltSiegel n F a₁ a₂, g * h * g⁻¹ ∈ spAltSiegel n F a₁ a₂ := by
  intro h hh
  have h12 : (spForm n F).β a₁ a₂ = 0 := hp.2.2.1
  have ha₁ : a₁ ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) :=
    Submodule.subset_span (by simp)
  have ha₂ : a₂ ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) :=
    Submodule.subset_span (by simp)
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp (rep_mem_of_mem_stabilizer hg ha₁)
  obtain ⟨γ, δ, hγδ⟩ := Submodule.mem_span_pair.mp (rep_mem_of_mem_stabilizer hg ha₂)
  obtain ⟨c, hc⟩ := exists_mulVec_of_mem_spAltSiegel h12 hh
  have hh' : ∀ w : Fin n ⊕ Fin n → F, natRep (StatedSp n F) h w =
      w + (spForm n F).β a₂ w • (c • a₁) + (spForm n F).β a₁ w • (c • a₂) := by
    intro w
    rw [natRep_apply, hc w, spForm_β, spForm_β, smul_smul, smul_smul,
      mul_comm (a₂ ⬝ᵥ ((spJ n F) *ᵥ w)) c, mul_comm (a₁ ⬝ᵥ ((spJ n F) *ᵥ w)) c]
  refine mem_spAltSiegel_of_mulVec (c * (α * δ + β * γ)) (fun v => ?_)
  rw [← natRep_apply, rep_conj_apply (isIsometric_natRep_statedSp n F) hh' g v, add_assoc,
    ← hγδ, ← hαβ, map_smul, map_smul, ← hαβ, ← hγδ, siegel_conj_vector, spForm_β, spForm_β,
    add_assoc]

private theorem mem_span_of_mem_normalizer {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂) {g : StatedSp n F}
    (hg : g ∈ Subgroup.normalizer (spAltSiegel n F a₁ a₂ : Set (StatedSp n F))) :
    ∀ v ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)),
      (g : GL (Fin n ⊕ Fin n) F) *ᵥ v ∈
        Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) := by
  have ha₁ : a₁ ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) :=
    Submodule.subset_span (by simp)
  have ha₂ : a₂ ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) :=
    Submodule.subset_span (by simp)
  have h12 : (spForm n F).β a₁ a₂ = 0 := hp.2.2.1
  obtain ⟨s, hs, hs'⟩ := exists_mem_spAltSiegel_mulVec (n := n) (F := F) hp.2.2.1 1
  have hb1 : (spForm n F).β a₁ b₁ = 1 := hp.1
  have hb2 : (spForm n F).β a₂ b₂ = 1 := hp.2.1
  have hb1' : (spForm n F).β a₂ b₁ = 0 := hp.2.2.2.2.2
  have hb2' : (spForm n F).β a₁ b₂ = 0 := hp.2.2.2.2.1
  have hgsg : g * s * g⁻¹ ∈ spAltSiegel n F a₁ a₂ :=
    (Subgroup.mem_normalizer_iff.mp hg s).1 hs
  obtain ⟨c, hc⟩ := exists_mulVec_of_mem_spAltSiegel h12 hgsg
  intro v hv
  obtain ⟨α, βf, hαβ⟩ := Submodule.mem_span_pair.mp hv
  have hα₁ : (spForm n F).β a₁ (α • b₂ + βf • b₁) = βf := by
    rw [(spForm n F).add_right, (spForm n F).smul_right, (spForm n F).smul_right, hb2', hb1]
    ring
  have hα₂ : (spForm n F).β a₂ (α • b₂ + βf • b₁) = α := by
    rw [(spForm n F).add_right, (spForm n F).smul_right, (spForm n F).smul_right, hb2, hb1']
    ring
  have hα₁' : a₁ ⬝ᵥ ((spJ n F) *ᵥ (α • b₂ + βf • b₁)) = βf := by
    rw [← spForm_β]; exact hα₁
  have hα₂' : a₂ ⬝ᵥ ((spJ n F) *ᵥ (α • b₂ + βf • b₁)) = α := by
    rw [← spForm_β]; exact hα₂
  have hsw : natRep (StatedSp n F) s (α • b₂ + βf • b₁) =
      (α • b₂ + βf • b₁) + v := by
    rw [natRep_apply, hs', hα₂', hα₁', one_mul, one_mul, add_assoc, hαβ]
  have hginv : natRep (StatedSp n F) g⁻¹
      (natRep (StatedSp n F) g (α • b₂ + βf • b₁)) = (α • b₂ + βf • b₁) := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have heq : natRep (StatedSp n F) g v =
      natRep (StatedSp n F) (g * s * g⁻¹) (natRep (StatedSp n F) g (α • b₂ + βf • b₁)) -
        natRep (StatedSp n F) g (α • b₂ + βf • b₁) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hginv, hsw, map_add]
    abel
  have hmem : natRep (StatedSp n F) g v ∈
      Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) := by
    rw [heq]
    simp only [natRep_apply]
    rw [hc, add_assoc, add_sub_cancel_left]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha₁) (Submodule.smul_mem _ _ ha₂)
  rwa [natRep_apply] at hmem

theorem normalizer_spAltSiegel_eq_stabilizer {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂) :
    Subgroup.normalizer (spAltSiegel n F a₁ a₂ : Set ↥(StatedSp n F)) =
      SymplecticFlag.stabilizer n F (Submodule.span F {a₁, a₂}) := by
  refine le_antisymm ?_ ?_
  · intro g hg
    refine SymplecticFlag.mem_stabilizer_of_mulVec_mem (W := Submodule.span F {a₁, a₂}) ?_ ?_
    · exact mem_span_of_mem_normalizer hp hg
    · exact mem_span_of_mem_normalizer hp (inv_mem hg)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact conj_mem_spAltSiegel hp hg h hh
    · intro hh
      have hconj := conj_mem_spAltSiegel hp (g := g⁻¹) (inv_mem hg) (g * h * g⁻¹) hh
      rwa [show g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h by group] at hconj

theorem sprad_le_centralizer_spAltSiegel {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F} (hp : SpPlanePair n F a₁ a₂ b₁ b₂)
    {hW : (spForm n F).IsTotallyIsotropic (Submodule.span F {a₁, a₂})} :
    sprad (Submodule.span F {a₁, a₂}) hW ≤
      Subgroup.centralizer (spAltSiegel n F a₁ a₂ : Set ↥(StatedSp n F)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have ha₁ : a₁ ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) :=
    Submodule.subset_span (by simp)
  have ha₂ : a₂ ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)) :=
    Submodule.subset_span (by simp)
  have hgfix : ∀ w ∈ Submodule.span F ({a₁, a₂} : Set (Fin n ⊕ Fin n → F)),
      natRep (StatedSp n F) g w = w := (mem_rad.mp hg).1
  have hga₁ : natRep (StatedSp n F) g a₁ = a₁ := hgfix a₁ ha₁
  have hga₂ : natRep (StatedSp n F) g a₂ = a₂ := hgfix a₂ ha₂
  obtain ⟨c, hc⟩ := exists_mulVec_of_mem_spAltSiegel hp.2.2.1 hs
  have hs' : ∀ v : Fin n ⊕ Fin n → F, natRep (StatedSp n F) s v =
      v + (spForm n F).β a₂ v • (c • a₁) + (spForm n F).β a₁ v • (c • a₂) := by
    intro v
    rw [natRep_apply, hc v, spForm_β, spForm_β, smul_smul, smul_smul,
      mul_comm (a₂ ⬝ᵥ ((spJ n F) *ᵥ v)) c, mul_comm (a₁ ⬝ᵥ ((spJ n F) *ᵥ v)) c]
  have hconj : natRep (StatedSp n F) (g * s * g⁻¹) = natRep (StatedSp n F) s := by
    refine LinearMap.ext fun v => ?_
    rw [rep_conj_apply (isIsometric_natRep_statedSp n F) hs' g v, hga₂, hga₁, map_smul,
      map_smul, hga₁, hga₂, hs' v]
  have hcomm : g * s * g⁻¹ = s := natRep_injective (StatedSp n F) hconj
  calc s * g = (g * s * g⁻¹) * g := by rw [hcomm]
    _ = g * s := by group

end CFSG.StandardType.LieKnownR2.Short
