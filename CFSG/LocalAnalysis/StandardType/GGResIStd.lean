module

public import CFSG.LocalAnalysis.StandardType.GGResIISym
public import CFSG.LocalAnalysis.StandardType.GGResIDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggStdEntryI {R : Type} (ι : ℤ → R) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : R) (k : Fin (n + 1)) (l : Fin (n + 2)) : R :=
  if hk : k.val < n then
    if hl : l.val < n then ι (C ⟨k.val, hk⟩ ⟨l.val, hl⟩)
    else if l.val = n then (if k.val = ic.val then ι e₂ else if k.val = ib.val then v else ι 0)
    else ι 0
  else
    if l.val < n then (if l.val = ic.val then ι e₁ else if l.val = ib.val then u else ι 0)
    else if l.val = n then ι 2
    else ι 0

@[expose] def ggStdTableI {R : Type} (ι : ℤ → R) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : R) : Fin (n + 1) → Vector R (n + 2) :=
  fun k => Vector.ofFn (ggStdEntryI ι C ib ic e₁ e₂ u v k)

@[expose] def ggStdTableSymI {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) :
    Fin (n + 1) → Vector GGPoly (n + 2) :=
  ggStdTableI GGPoly.const C ib ic e₁ e₂ GGPoly.U GGPoly.V

theorem ggStdTableI_eval {S : Type} [CommRing S] (u v : S) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (ib ic : Fin n) (e₁ e₂ : ℤ) :
    GGPoly.evalT u v (ggStdTableSymI C ib ic e₁ e₂) = ggStdTableI (Int.cast) C ib ic e₁ e₂ u v := by
  funext k
  ext l hl
  change (GGPoly.evalV u v (ggStdTableSymI C ib ic e₁ e₂ k)).get ⟨l, hl⟩ =
    (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v k).get ⟨l, hl⟩
  rw [GGPoly.get_evalV, ggStdTableSymI, ggStdTableI, ggStdTableI, Vector.get_ofFn,
    Vector.get_ofFn]
  unfold ggStdEntryI
  split_ifs <;> simp [GGPoly.eval_const]

section Entries

variable {R : Type} (ι : ℤ → R) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
  (e₁ e₂ : ℤ) (u v : R)

theorem ggStdEntryI_LL (j i : Fin n) :
    ggStdEntryI ι C ib ic e₁ e₂ u v j.castSucc i.castSucc.castSucc = ι (C j i) := by
  unfold ggStdEntryI
  simp

theorem ggStdEntryI_La (j : Fin n) :
    ggStdEntryI ι C ib ic e₁ e₂ u v j.castSucc (Fin.last n).castSucc =
      if j.val = ic.val then ι e₂ else if j.val = ib.val then v else ι 0 := by
  unfold ggStdEntryI
  simp

theorem ggStdEntryI_aL (i : Fin n) :
    ggStdEntryI ι C ib ic e₁ e₂ u v (Fin.last n) i.castSucc.castSucc =
      if i.val = ic.val then ι e₁ else if i.val = ib.val then u else ι 0 := by
  unfold ggStdEntryI
  simp

theorem ggStdEntryI_aa : ggStdEntryI ι C ib ic e₁ e₂ u v (Fin.last n) (Fin.last n).castSucc = ι 2 := by
  unfold ggStdEntryI
  simp

theorem ggStdEntryI_x (k : Fin (n + 1)) :
    ggStdEntryI ι C ib ic e₁ e₂ u v k (Fin.last (n + 1)) = ι 0 := by
  unfold ggStdEntryI
  simp only [Fin.val_last]
  split_ifs <;> first | rfl | omega

end Entries

section Concl

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def GGResIConcl {n : ℕ} (g : Fin (n + 1) → (V ≃ₗ[ZMod p] V)) (h : Fin (n + 1) → V)
    (α : Fin (n + 1) → Module.Dual (ZMod p) V) (ib : Fin n) (x : V) : Prop :=
  (∃ t ∈ Subgroup.closure (Set.range g),
      Module.finrank (ZMod p) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w) ∨
    (5 ≤ p ∧ ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ j j' : Fin n, j ≠ ib ∧ j' ≠ ib ∧
      GGTriBad p (ggTriMat (α j.castSucc) (α j'.castSucc)
        ((α j.castSucc).comp (ψ⁻¹ : V ≃ₗ[ZMod p] V).toLinearMap) (h j.castSucc)
        (h j'.castSucc) (ψ (h j.castSucc)))) ∨
    (p = 3 ∧ ∃ R : List (V ≃ₗ[ZMod p] V), (∀ k : Fin n, g k.castSucc ∈ R) ∧
      (∀ k : Fin n, ∀ r ∈ R, g k.castSucc * r * (g k.castSucc)⁻¹ ∈ R) ∧
      ∃ ψ ∈ Subgroup.closure (Set.range g), ∃ i : Fin n, α i.castSucc (ψ⁻¹ x) = 0 ∧
        ψ * g i.castSucc * ψ⁻¹ ∉ R) ∨
    ZS.LinWeyl p (Subgroup.closure (Set.range g))

end Concl

end CFSG.StandardType
