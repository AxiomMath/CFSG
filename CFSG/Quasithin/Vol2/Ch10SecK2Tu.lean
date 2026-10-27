module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tt
public import CFSG.Quasithin.Vol2.Ch10SecK2Ta

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA
open scoped IsMulCommutative

variable {Γ : Type} [Group Γ] [Finite Γ]

structure K2Ctx (R J L V₁ V : Subgroup Γ) (n : ℕ) : Prop where
  hJV : J ≤ Subgroup.normalizer (V : Set Γ)
  hOJ : pCoreOf 2 J ≤ Subgroup.centralizer (V : Set Γ)
  hLJ : L ≤ J
  hRL : R ≤ Subgroup.normalizer (L : Set Γ)
  hq : CFSG.IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J)
  hZY : Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) = 1 ∨
    Nat.card (Subgroup.center (↥J ⧸ CFSG.pCore 2 ↥J)) = 3
  hP : ∃ P : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J), IsMaxParabolic2 ⊤ P ∧
    modO2Image J L = perfectCore P
  hLne : modO2Image J L ≠ ⊤
  hT : IsSylowTwoOf (((R ⊓ J).subgroupOf J).map (QuotientGroup.mk' (CFSG.pCore 2 ↥J))) ⊤
  hn : 2 ≤ n
  hlevi : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) F)
  hV₁V : V₁ ≤ V
  hV₁ : ∀ W : Subgroup Γ, V₁ ≤ W → ValidX J L R W (2 ^ n) V₁
  hne : V₁ ≠ ⊥

theorem finish_of_line {J L V₁ W : Subgroup Γ} [IsMulCommutative ↥W] (hW : IsElemAbelian 2 W)
    (hJW : J ≤ Subgroup.normalizer (W : Set Γ)) (hLJ : L ≤ J) (hV₁W : V₁ ≤ W)
    {S : Subgroup (MulAut ↥W)} {Z U₂ : Subgroup ↥W} {q : ℕ}
    (hHZ : ∀ h ∈ autOn J W, ∀ z ∈ Z, h z = z) (hLF : LineFacts (autOn J W) Z U₂)
    (hLT : LineTorusFacts (autOn J W) S Z U₂ q)
    (hL : perfectCore (autOn J W ⊓ stabW U₂) = autOn L W)
    (hV : V₁.subgroupOf W = commS (autOn L W) U₂) :
    ∃ y ∈ J ⊓ Subgroup.normalizer (V₁ : Set Γ), y ∉ Subgroup.centralizer (V₁ : Set Γ) ∧
      (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ)) ∧
      y ^ (q - 1) ∈ Subgroup.centralizer (V₁ : Set Γ) := by
  obtain ⟨t, ht, h1, h2, h3, h4⟩ := torus_of_line hHZ hLF hLT
  rw [hL, ← hV] at h1 h2 h3
  exact conclusion_of_torusAut hW (hLJ.trans hJW) hV₁W
    ⟨t, ht, h1, h2, h3, fun w _ => congrArg (fun φ : MulAut ↥W => φ w) h4⟩

omit [Finite Γ] in
theorem not_le_centralizer_of_ctx {R J L V₁ V : Subgroup Γ} {n : ℕ} (hC : K2Ctx R J L V₁ V n)
    {W : Subgroup Γ} (hV₁W : V₁ ≤ W) : ¬ J ≤ Subgroup.centralizer (W : Set Γ) := by
  intro h
  apply hC.hne
  rw [← (hC.hV₁ W hV₁W).comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  exact (Subgroup.mem_centralizer_iff.mp (h (hC.hLJ hl)) x (hV₁W hx)).symm

theorem torus_of_natural {R J L V₁ V : Subgroup Γ} {n : ℕ} (hV : IsElemAbelian 2 V)
    (hC : K2Ctx R J L V₁ V n) {W : Subgroup Γ} [IsMulCommutative ↥W] (hWV : W ≤ V)
    (hJW : J ≤ Subgroup.normalizer (W : Set Γ)) (hV₁W : V₁ ≤ W) {Z : Subgroup ↥W} {m : ℕ}
    (hD : TorusData (autOn J W) Z (2 ^ m)) :
    ∃ y ∈ J ⊓ Subgroup.normalizer (V₁ : Set Γ), y ∉ Subgroup.centralizer (V₁ : Set Γ) ∧
      (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ)) ∧
      y ^ (2 ^ n - 1) ∈ Subgroup.centralizer (V₁ : Set Γ) := by
  have hW : IsElemAbelian 2 W := ⟨inferInstance, fun x hx => hV.2 x (hWV hx)⟩
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hW.2 w w.2)
  obtain ⟨P, hP, hLP⟩ := hC.hP
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hC.hlevi
  obtain ⟨U₂, hLF, hLT, hL, heq⟩ := core_line hW2 hJW
    (hC.hOJ.trans (Subgroup.centralizer_le hWV)) (not_le_centralizer_of_ctx hC hV₁W) hC.hLJ
    hC.hRL hC.hq hC.hZY hP hLP hC.hLne hC.hT hC.hn hF e hD (hC.hV₁ W hV₁W) hC.hne
  exact finish_of_line hW hJW hC.hLJ hV₁W hD.hZ hLF hLT hL
    (heq V₁ (hC.hV₁ W hV₁W) hC.hne)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
