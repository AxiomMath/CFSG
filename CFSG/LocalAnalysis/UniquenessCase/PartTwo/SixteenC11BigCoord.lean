module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11BigDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16c11_big_coord_fix_iff {X K L₀ : Subgroup (MulAut W)} {J₀ : Subgroup W}
    (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (h2 : ∀ g ∈ X, (∀ k ∈ K, g * k = k * g) → ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    (hX : L₀ ≤ X) (hcomm : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k)
    {φ : MulAut W} (hφ : φ ∈ L₀) (w : W) :
    φ w = w ↔ ∀ i : Fin 3, φ (((ψ w).1 i : ↥J₀) : W) = ((ψ w).1 i : W) := by
  have hφX : φ ∈ X := hX hφ
  have hφK : ∀ k ∈ K, φ * k = k * φ := fun k hk => (hcomm k hk φ hφ).symm
  constructor
  · intro hw i
    have h := h2 φ hφX hφK w i
    rw [hw] at h
    exact h.symm
  · intro hw
    apply ψ.injective
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact (h2 φ hφX hφK w i).trans (hw i)

private theorem s16c11_big_coord_mem_fixV_iff {X K L₀ H : Subgroup (MulAut W)}
    {J₀ : Subgroup W}
    (ψ : W ≃* ↥(s16c2m_Triples ↥J₀))
    (h2 : ∀ g ∈ X, (∀ k ∈ K, g * k = k * g) → ∀ (w : W) (i : Fin 3),
      (((ψ (g w)).1 i : ↥J₀) : W) = g (((ψ w).1 i : ↥J₀) : W))
    (hX : L₀ ≤ X) (hcomm : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k)
    (hH : H ≤ L₀) (w : W) :
    w ∈ fixV H ↔ ∀ i : Fin 3, (((ψ w).1 i : ↥J₀) : W) ∈ fixV H := by
  rw [mem_fixV]
  constructor
  · intro hw i
    rw [mem_fixV]
    intro φ hφ
    exact (s16c11_big_coord_fix_iff ψ h2 hX hcomm (hH hφ) w).mp (hw φ hφ) i
  · intro hw φ hφ
    exact (s16c11_big_coord_fix_iff ψ h2 hX hcomm (hH hφ) w).mpr (fun i => hw i φ hφ)

theorem s16c11_big_card_eq {n : ℕ} {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) : Nat.card W = Nat.card ↥J₀ ^ 2 := by
  obtain ⟨_, ψ, _, _⟩ := h.model
  calc Nat.card W = Nat.card ↥(s16c2m_Triples ↥J₀) := Nat.card_congr ψ.toEquiv
    _ = Nat.card ↥J₀ ^ 2 := s16c2m_card_Triples ↥J₀

theorem s16c11_big_fixV_card {n : ℕ} {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) {H : Subgroup (MulAut W)} (hH : H ≤ L₀) :
    Nat.card ↥(fixV H) = Nat.card ↥(J₀ ⊓ fixV H) ^ 2 := by
  obtain ⟨_, ψ, _, h2⟩ := h.model
  have hX : L₀ ≤ X := h.l₀_le
  have hcomm : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k := s16c11_comm_of_isInternalDirect h.dir
  let F : Subgroup W := J₀ ⊓ fixV H
  let G : Type := {x : ↥J₀ // (x : W) ∈ fixV H}
  have he1 : ∀ w : W, ((ψ.trans (s16c2m_tripleEquiv ↥J₀)) w).1 = (ψ w).1 0 := fun _ => rfl
  have he2 : ∀ w : W, ((ψ.trans (s16c2m_tripleEquiv ↥J₀)) w).2 = (ψ w).1 1 := fun _ => rfl
  have hP : ∀ w : W, w ∈ fixV H ↔
      (((ψ.trans (s16c2m_tripleEquiv ↥J₀)) w).1 : W) ∈ fixV H ∧
      (((ψ.trans (s16c2m_tripleEquiv ↥J₀)) w).2 : W) ∈ fixV H := by
    intro w
    rw [he1 w, he2 w, s16c11_big_coord_mem_fixV_iff ψ h2 hX hcomm hH w]
    constructor
    · intro hh; exact ⟨hh 0, hh 1⟩
    · intro hh i
      fin_cases i
      · exact hh.1
      · exact hh.2
      · have hc : (((ψ w).1 2 : ↥J₀) : W) ∈ fixV H := by
          rw [s16c2m_Triples_two_eq (ψ w).2]
          exact inv_mem (mul_mem hh.1 hh.2)
        exact hc
  let e3 : G ≃ ↥F :=
    Equiv.subtypeSubtypeEquivSubtypeInter (fun x : W => x ∈ J₀) (fun x : W => x ∈ fixV H)
  have hcard : Nat.card ↥(fixV H) = Nat.card ↥F ^ 2 := by
    calc Nat.card ↥(fixV H)
        = Nat.card {c : ↥J₀ × ↥J₀ // (c.1 : W) ∈ fixV H ∧ (c.2 : W) ∈ fixV H} :=
          Nat.card_congr (Equiv.subtypeEquiv (ψ.trans (s16c2m_tripleEquiv ↥J₀)).toEquiv hP)
      _ = Nat.card (G × G) :=
          Nat.card_congr (Equiv.subtypeProdEquivProd
            (p := fun x : ↥J₀ => (x : W) ∈ fixV H)
            (q := fun x : ↥J₀ => (x : W) ∈ fixV H))
      _ = Nat.card G * Nat.card G := Nat.card_prod G G
      _ = Nat.card ↥F * Nat.card ↥F := by rw [Nat.card_congr e3]
      _ = Nat.card ↥F ^ 2 := (sq _).symm
  exact hcard

theorem s16c11_big_fix_of_coords {n : ℕ} {X L K L₀ : Subgroup (MulAut W)} {J₀ J₁ : Subgroup W}
    (h : S16C11AltSetup n X L K L₀ J₀ J₁) (w : W) :
    ∃ a b : W, a ∈ J₀ ∧ b ∈ J₀ ∧ ∀ φ ∈ L₀, φ a = a → φ b = b → φ w = w := by
  obtain ⟨_, ψ, _, h2⟩ := h.model
  have hX : L₀ ≤ X := h.l₀_le
  have hcomm : ∀ k ∈ K, ∀ l ∈ L₀, k * l = l * k := s16c11_comm_of_isInternalDirect h.dir
  refine ⟨(((ψ w).1 0 : ↥J₀) : W), (((ψ w).1 1 : ↥J₀) : W),
    ((ψ w).1 0).2, ((ψ w).1 1).2, ?_⟩
  intro φ hφ ha hb
  rw [s16c11_big_coord_fix_iff ψ h2 hX hcomm hφ w]
  intro i
  have hc : φ (((ψ w).1 2 : ↥J₀) : W) = (((ψ w).1 2 : ↥J₀) : W) := by
    rw [s16c2m_Triples_two_eq (ψ w).2, Subgroup.coe_inv, Subgroup.coe_mul,
      map_inv, map_mul, ha, hb]
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
