module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenBlock
public import CFSG.RankThree.SubgroupLists.SchurCommutant
import CFSG.RankThree.PartTwo.Sec16.KL3SubProofMain

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open Matrix CFSG.RankThree.PartTwo.Sec16.KL3SubProof

variable {F : Type} [Field F]

theorem vecMulVec_mulVec' (u v w : Fin 3 → F) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem vecMul_vecMulVec' (u v w : Fin 3 → F) : w ᵥ* vecMulVec u v = (w ⬝ᵥ u) • v :=
  vecMul_vecMulVec w u v

theorem elat_inv_eq [CharP F 2] {g : GL (Fin 3) F} {a φ : Fin 3 → F} (h : IsElat g a φ) :
    g⁻¹ = g :=
  inv_eq_of_mul_eq_one_right h.mul_self

theorem exists_conj_genPos [CharP F 2] {D : Subgroup (GL (Fin 3) F)}
    (hirr : SubgroupLists.IsIrreducibleOn D) {x : GL (Fin 3) F} (hx : x ∈ D) {a φ : Fin 3 → F}
    (hxE : IsElat x a φ) (hgen : Subgroup.normalClosure {(⟨x, hx⟩ : D)} = ⊤)
    {b ψ : Fin 3 → F} (hb : b ≠ 0) (hψ : ψ ≠ 0) :
    ∃ d ∈ D, ψ ⬝ᵥ ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ a) ≠ 0 ∧
      (φ ᵥ* ((d⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ⬝ᵥ b ≠ 0 := by
  classical
  by_contra hno
  push Not at hno
  have hirr' : CFSG.RankThree.PartTwo.Sec16.KSL3TwoIrrProof.IsIrr D := fun W hW => hirr W hW
  let A : Submodule F (Fin 3 → F) :=
    { carrier := {v | ∀ d ∈ D, ψ ⬝ᵥ ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ a) ≠ 0 →
        (φ ᵥ* ((d⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ⬝ᵥ v = 0}
      add_mem' := fun {v w} hv hw d hd hda => by
        rw [dotProduct_add, hv d hd hda, hw d hd hda, add_zero]
      zero_mem' := fun d _ _ => by rw [dotProduct_zero]
      smul_mem' := fun c v hv d hd hda => by
        rw [dotProduct_smul, hv d hd hda, smul_zero] }
  have hmemA : ∀ v, v ∈ A ↔ ∀ d ∈ D, ψ ⬝ᵥ ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ a) ≠ 0 →
      (φ ᵥ* ((d⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ⬝ᵥ v = 0 := fun v => Iff.rfl
  have hbA : b ∈ A := hno
  obtain ⟨d₁, hd₁, hd₁a⟩ := exists_dotProduct_mulVec_ne_zero hirr' hxE.1 hψ
  have hAtop : A ≠ ⊤ := by
    intro h
    apply hxE.2.1
    have h0 : φ ᵥ* ((d₁⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 0 := by
      funext i
      have hi : (Pi.single i 1 : Fin 3 → F) ∈ A := h ▸ Submodule.mem_top
      have := hi d₁ hd₁ hd₁a
      rwa [dotProduct_single, mul_one] at this
    have hmul : ((d₁⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        (d₁ : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have := congrArg (fun v => v ᵥ* (d₁ : Matrix (Fin 3) (Fin 3) F)) h0
    simpa [Matrix.vecMul_vecMul, hmul] using this
  have hinvconj : ∀ d ∈ D, ∀ v ∈ A, ((d * x * d⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v
      ∈ A := by
    intro d hd v hv
    have hdE := hxE.conj d
    rw [hdE.2.2.2, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec']
    by_cases hd1 : ψ ⬝ᵥ ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ a) ≠ 0
    · rw [hv d hd hd1, zero_smul, add_zero]
      exact hv
    · push Not at hd1
      by_cases hda : (d : Matrix (Fin 3) (Fin 3) F) *ᵥ a ∈ A
      · exact A.add_mem hv (A.smul_mem _ hda)
      · rw [hmemA] at hda
        push Not at hda
        obtain ⟨d₂, hd₂, hd₂a, hne⟩ := hda
        have hx₂E := hxE.conj d₂
        have hd' : d₂ * x * d₂⁻¹ * d ∈ D :=
          D.mul_mem (D.mul_mem (D.mul_mem hd₂ hx) (D.inv_mem hd₂)) hd
        have hψd' : ψ ⬝ᵥ (((d₂ * x * d₂⁻¹ * d : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ a)
            ≠ 0 := by
          rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx₂E.2.2.2, Matrix.add_mulVec,
            Matrix.one_mulVec, vecMulVec_mulVec', dotProduct_add, dotProduct_smul, hd1, zero_add,
            smul_eq_mul]
          exact mul_ne_zero hne hd₂a
        have hv' := hv _ hd' hψd'
        have hv₂ := hv d₂ hd₂ hd₂a
        have hinv : (d₂ * x * d₂⁻¹ * d)⁻¹ = d⁻¹ * (d₂ * x * d₂⁻¹) := by
          rw [_root_.mul_inv_rev, elat_inv_eq hx₂E]
        rw [hinv, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, hx₂E.2.2.2,
          Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec', hv₂, zero_smul,
          add_zero] at hv'
        rw [hv', zero_smul, add_zero]
        exact hv
  let Stab : Subgroup (GL (Fin 3) F) :=
    { carrier := {g | ∀ v ∈ A, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ A ∧
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ A}
      mul_mem' := fun {g h} hg hh v hv => by
        refine ⟨?_, ?_⟩
        · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
          exact (hg _ (hh v hv).1).1
        · rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
          exact (hh _ (hg v hv).2).2
      one_mem' := fun v hv => by
        simp only [inv_one, Units.val_one, Matrix.one_mulVec]
        exact ⟨hv, hv⟩
      inv_mem' := fun {g} hg v hv => by
        rw [inv_inv]
        exact ⟨(hg v hv).2, (hg v hv).1⟩ }
  have hconjStab : ∀ d ∈ D, d * x * d⁻¹ ∈ Stab := by
    intro d hd v hv
    have hinv : (d * x * d⁻¹)⁻¹ = d * x * d⁻¹ := elat_inv_eq (hxE.conj d)
    refine ⟨hinvconj d hd v hv, ?_⟩
    rw [hinv]
    exact hinvconj d hd v hv
  have hle : Subgroup.normalClosure {(⟨x, hx⟩ : D)} ≤ Stab.subgroupOf D := by
    change Subgroup.closure (Group.conjugatesOfSet {(⟨x, hx⟩ : D)}) ≤ _
    rw [Subgroup.closure_le]
    intro c hc
    obtain ⟨b', hb', hc'⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    rw [Set.mem_singleton_iff] at hb'
    subst hb'
    obtain ⟨d, rfl⟩ := isConj_iff.mp hc'
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hconjStab d d.2
  have hDStab : ∀ g ∈ D, g ∈ Stab := by
    intro g hg
    have hg' : (⟨g, hg⟩ : D) ∈ Subgroup.normalClosure {(⟨x, hx⟩ : D)} :=
      hgen ▸ Subgroup.mem_top _
    exact hle hg'
  rcases hirr A (fun g hg v hv => (hDStab g hg v hv).1) with h | h
  · exact hb ((Submodule.mem_bot F).mp (h ▸ hbA))
  · exact hAtop h

theorem root_structure [Finite F] [CharP F 2]
    {D : Subgroup (GL (Fin 3) F)} (hirr : SubgroupLists.IsIrreducibleOn D)
    {x : GL (Fin 3) F} (hx : x ∈ D) {a φ : Fin 3 → F} (hxE : IsElat x a φ)
    (hgen : Subgroup.normalClosure {(⟨x, hx⟩ : D)} = ⊤) {c : F} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hc : c ∈ rootSet D a φ) :
    ∃ K₀ : Subfield F, c ∈ K₀ ∧
      (∀ z ∈ D, ∀ p ℓ : Fin 3 → F, IsElat z p ℓ → rootSet D p ℓ = K₀) ∧
      (∀ z ∈ D, ∀ w ∈ D, ∀ p ℓ b ψ : Fin 3 → F, IsElat z p ℓ → IsElat w b ψ → ℓ ⬝ᵥ b ≠ 0 →
        ψ ⬝ᵥ p ≠ 0 → (ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p) ∈ K₀) := by
  have hirr' : CFSG.RankThree.PartTwo.Sec16.KSL3TwoIrrProof.IsIrr D := fun W hW => hirr W hW
  obtain ⟨s, hs, b₀, ψ₀, hsE, hφb₀, hψ₀a⟩ := exists_genPos hirr' hx hxE
  obtain ⟨K₀, hK₀a, -, -⟩ := block_field D hxE.2.2.1 hsE.2.2.1 hφb₀ hψ₀a
    (one_mem_rootSet hx hxE) hc0 hc1 hc (one_mem_rootSet hs hsE)
  have hcK : c ∈ K₀ := by
    have : c ∈ (K₀ : Set F) := hK₀a ▸ hc
    exact this
  have hR1 : ∀ z ∈ D, ∀ p ℓ : Fin 3 → F, IsElat z p ℓ → rootSet D p ℓ = K₀ := by
    intro z hz p ℓ hzE
    obtain ⟨d, hd, hd1, hd2⟩ := exists_conj_genPos hirr hx hxE hgen hzE.1 hzE.2.1
    have hdE := hxE.conj d
    have hconj := rootSet_conj hd a φ
    have hcd : c ∈ rootSet D ((d : Matrix (Fin 3) (Fin 3) F) *ᵥ a)
        (φ ᵥ* ((d⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := hconj ▸ hc
    obtain ⟨K₁, h1, h2, -⟩ := block_field D hdE.2.2.1 hzE.2.2.1 hd2 hd1
      (one_mem_rootSet (D.mul_mem (D.mul_mem hd hx) (D.inv_mem hd)) hdE) hc0 hc1 hcd
      (one_mem_rootSet hz hzE)
    rw [h2, ← h1, hconj, hK₀a]
  refine ⟨K₀, hcK, hR1, ?_⟩
  intro z hz w hw p ℓ b ψ hzE hwE hℓb hψp
  have hcz : c ∈ rootSet D p ℓ := by rw [hR1 z hz p ℓ hzE]; exact hcK
  obtain ⟨K₁, h1, -, hν⟩ := block_field D hzE.2.2.1 hwE.2.2.1 hℓb hψp
    (one_mem_rootSet hz hzE) hc0 hc1 hcz (one_mem_rootSet hw hwE)
  have hK : (K₁ : Set F) = K₀ := by rw [← h1, hR1 z hz p ℓ hzE]
  have : (ℓ ⬝ᵥ b) * (ψ ⬝ᵥ p) ∈ (K₁ : Set F) := hν
  rw [hK] at this
  exact this

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
