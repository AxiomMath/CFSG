module

public import CFSG.RankThree.PartOne.N1322.CoreDefs
public import CFSG.RankThree.PartOne.NF7H.Statement

public section

namespace CFSG.RankThree.PartOne.N1322

open Matrix Equiv

variable {K : Type*} [Field K]

structure CoreData (K : Type*) [Field K] where
  X : Subgroup (GL (Fin 3) K)
  D : Set (GL (Fin 3) K)
  Lm : Subgroup (GL (Fin 3) K)
  c : Fin 3 → K
  n : ℕ

@[expose] def KHStmt (d : CoreData K) : Prop :=
  ∀ g ∈ d.X, (∃ μ : K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c = μ • d.c) →
    ∀ t ∈ d.D, ∀ s ∈ d.D, t ∈ d.Lm → s ∈ d.Lm → (∀ l ∈ d.Lm, l * t * l⁻¹ ≠ s) → g * t * g⁻¹ ≠ s

structure MonoHyp (d : CoreData K) : Prop where
  refl : ∀ g ∈ d.D, IsRefl g
  gen : d.X = Subgroup.closure d.D
  Dconj : ∀ x ∈ d.X, ∀ g ∈ d.D, x * g * x⁻¹ ∈ d.D
  Lle : d.Lm ≤ d.X
  Lgen : Subgroup.closure (d.D ∩ (d.Lm : Set (GL (Fin 3) K))) = d.Lm
  Ldih : Nonempty (d.Lm ≃* DihedralGroup d.n)
  n_mem : d.n = 4 ∨ d.n = 6 ∨ d.n = 8
  c_ne : d.c ≠ 0
  c_fix : ∀ l ∈ d.Lm, (l : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c = d.c
  lines : ∀ v : Fin 3 → K, v ≠ 0 →
    (∀ l ∈ d.Lm, ∃ μ : K, (l : Matrix (Fin 3) (Fin 3) K) *ᵥ v = μ • v) → ∃ μ : K, v = μ • d.c
  N : ∀ h ∈ d.X, (∃ μ : K, (h : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c = μ • d.c) →
    ∀ l ∈ d.Lm, h * l * h⁻¹ ∈ d.Lm
  kHU : KHStmt d ∨ (d.n = 4 ∧ NF7H.KUMat d.X d.Lm d.c)

section Conj

variable (P : GL (Fin 3) K)

@[expose] def cj : GL (Fin 3) K ≃* GL (Fin 3) K := MulAut.conj P

theorem cj_apply (g : GL (Fin 3) K) : cj P g = P * g * P⁻¹ := rfl

theorem cj_symm_apply (g : GL (Fin 3) K) : (cj P).symm g = P⁻¹ * g * P :=
  MulAut.conj_symm_apply P g

theorem cj_conj_back (a : GL (Fin 3) K) : P⁻¹ * (P * a * P⁻¹) * P = a := by group

theorem mem_image_cj (S : Set (GL (Fin 3) K)) (g : GL (Fin 3) K) :
    g ∈ cj P '' S ↔ P⁻¹ * g * P ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [cj_apply, cj_conj_back]; exact hx
  · intro h
    exact ⟨P⁻¹ * g * P, h, by rw [cj_apply]; group⟩

theorem mem_map_cj (H : Subgroup (GL (Fin 3) K)) (g : GL (Fin 3) K) :
    g ∈ H.map (cj P).toMonoidHom ↔ P⁻¹ * g * P ∈ H := by
  rw [Subgroup.mem_map_equiv, cj_symm_apply]

theorem mulVec_conj (x : GL (Fin 3) K) (v : Fin 3 → K) :
    ((P * x * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem mulVec_conj_symm (x : GL (Fin 3) K) (v : Fin 3 → K) :
    ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem mulVec_inv_mulVec (v : Fin 3 → K) :
    ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      v := by
  rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem mulVec_mulVec_inv (v : Fin 3 → K) :
    (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      v := by
  rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

@[expose] def CoreData.conj (d : CoreData K) : CoreData K where
  X := d.X.map (cj P).toMonoidHom
  D := cj P '' d.D
  Lm := d.Lm.map (cj P).toMonoidHom
  c := (P : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c
  n := d.n

theorem MonoHyp.conj {d : CoreData K} (h : MonoHyp d) : MonoHyp (d.conj P) := by
  have hX : ∀ g, g ∈ (d.conj P).X ↔ P⁻¹ * g * P ∈ d.X := mem_map_cj P _
  have hL : ∀ g, g ∈ (d.conj P).Lm ↔ P⁻¹ * g * P ∈ d.Lm := mem_map_cj P _
  have hD : ∀ g, g ∈ (d.conj P).D ↔ P⁻¹ * g * P ∈ d.D := mem_image_cj P _
  have hc : (d.conj P).c = (P : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c := rfl
  have hmulc : ∀ (a b : GL (Fin 3) K), P⁻¹ * (a * b * a⁻¹) * P =
      (P⁻¹ * a * P) * (P⁻¹ * b * P) * (P⁻¹ * a * P)⁻¹ := by
    intro a b; group
  have hstab : ∀ x : GL (Fin 3) K, (∃ μ : K, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ (d.conj P).c =
      μ • (d.conj P).c) → ∃ μ : K, ((P⁻¹ * x * P : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c =
        μ • d.c := by
    rintro x ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    have h2 : (x : Matrix (Fin 3) (Fin 3) K) *ᵥ ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c) =
        μ • ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c) := hμ
    rw [mulVec_conj_symm, h2, Matrix.mulVec_smul, mulVec_inv_mulVec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, h.n_mem, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro g hg
    obtain ⟨x, hx, rfl⟩ := hg
    exact (h.refl x hx).conj P
  ·
    show d.X.map (cj P).toMonoidHom = Subgroup.closure (cj P '' d.D)
    rw [h.gen, MonoidHom.map_closure]
    try rfl
  ·
    intro x hx g hg
    rw [hX] at hx
    rw [hD] at hg ⊢
    rw [hmulc]
    exact h.Dconj _ hx _ hg
  ·
    intro l hl
    rw [hL] at hl
    rw [hX]
    exact h.Lle hl
  ·
    have h1 : cj P '' d.D ∩ ((d.Lm.map (cj P).toMonoidHom : Subgroup (GL (Fin 3) K)) :
        Set (GL (Fin 3) K)) = cj P '' (d.D ∩ (d.Lm : Set (GL (Fin 3) K))) := by
      rw [Set.image_inter (cj P).injective]
      try rfl
    show Subgroup.closure (cj P '' d.D ∩ ((d.Lm.map (cj P).toMonoidHom : Subgroup (GL (Fin 3) K)) :
      Set (GL (Fin 3) K))) = d.Lm.map (cj P).toMonoidHom
    rw [h1]
    calc Subgroup.closure (cj P '' (d.D ∩ (d.Lm : Set (GL (Fin 3) K))))
        = (Subgroup.closure (d.D ∩ (d.Lm : Set (GL (Fin 3) K)))).map (cj P).toMonoidHom := by
          rw [MonoidHom.map_closure]; try rfl
      _ = d.Lm.map (cj P).toMonoidHom := by rw [h.Lgen]
  ·
    obtain ⟨e⟩ := h.Ldih
    exact ⟨((cj P).subgroupMap d.Lm).symm.trans e⟩
  ·
    intro h0
    apply h.c_ne
    have := congrArg (fun w => ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) h0
    simpa [hc, mulVec_inv_mulVec] using this
  ·
    intro l hl
    rw [hL] at hl
    have e : P * (P⁻¹ * l * P) * P⁻¹ = l := by group
    have h1 := mulVec_conj P (P⁻¹ * l * P) ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c)
    rw [e, mulVec_inv_mulVec, h.c_fix _ hl] at h1
    exact h1
  ·
    intro v hv hinv
    set w := ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v with hw
    have hwv : (P : Matrix (Fin 3) (Fin 3) K) *ᵥ w = v := mulVec_mulVec_inv P v
    have hw0 : w ≠ 0 := by
      intro h0; apply hv; rw [← hwv, h0, Matrix.mulVec_zero]
    obtain ⟨μ, hμ⟩ := h.lines w hw0 (by
      intro l hl
      have hl' : P * l * P⁻¹ ∈ (d.conj P).Lm := by rw [hL, cj_conj_back]; exact hl
      obtain ⟨ν, hν⟩ := hinv _ hl'
      refine ⟨ν, ?_⟩
      have h1 := mulVec_conj_symm P (P * l * P⁻¹) w
      rw [cj_conj_back, hwv, hν, Matrix.mulVec_smul] at h1
      exact h1)
    refine ⟨μ, ?_⟩
    show v = μ • ((P : Matrix (Fin 3) (Fin 3) K) *ᵥ d.c)
    rw [← hwv, hμ, Matrix.mulVec_smul]
  ·
    intro x hx hμ l hl
    rw [hX] at hx
    rw [hL] at hl
    rw [hL, hmulc]
    exact h.N _ hx (hstab x hμ) _ hl
  ·
    rcases h.kHU with hkH | ⟨hn4, hkU⟩
    · left
      intro g hg hμ t ht s hs htL hsL hdiff heq
      rw [hX] at hg
      rw [hD] at ht hs
      rw [hL] at htL hsL
      have hmain := hkH (P⁻¹ * g * P) hg (hstab g hμ) (P⁻¹ * t * P) ht (P⁻¹ * s * P) hs htL hsL (by
        intro l hl hlt
        apply hdiff (P * l * P⁻¹) (by rw [hL, cj_conj_back]; exact hl)
        have h3 : P * (l * (P⁻¹ * t * P) * l⁻¹) * P⁻¹ = (P * l * P⁻¹) * t * (P * l * P⁻¹)⁻¹ := by
          group
        rw [← h3, hlt]; group)
      apply hmain
      rw [← hmulc, heq]
    · exact Or.inr ⟨hn4, hkU.conj P⟩

end Conj

end CFSG.RankThree.PartOne.N1322
