module

public import CFSG.Quasithin.Recognition.RuTypeJ47Cert
public import CFSG.Quasithin.Background.F3Paths

public noncomputable section

namespace CFSG.Quasithin.H13.F45Ru

open CFSG.Quasithin CFSG.Sporadic.Schreier.Tits

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

abbrev Vtx : Type := Fin 1755 ⊕ Fin 2925

@[expose] def octAdj : Vtx → Vtx → Prop
  | Sum.inl p, Sum.inr v => p ∈ titsLine v
  | Sum.inr v, Sum.inl p => p ∈ titsLine v
  | _, _ => False

@[expose] def octGraph : SimpleGraph Vtx where
  Adj := octAdj
  symm := ⟨by
    intro a b h
    cases a <;> cases b <;> exact h⟩
  loopless := ⟨by
    intro a h
    cases a <;> exact h⟩

theorem octGraph_adj_inl_inr {p : Fin 1755} {v : Fin 2925} :
    octGraph.Adj (Sum.inl p) (Sum.inr v) ↔ p ∈ titsLine v := Iff.rfl

theorem octGraph_adj_inr_inl {p : Fin 1755} {v : Fin 2925} :
    octGraph.Adj (Sum.inr v) (Sum.inl p) ↔ p ∈ titsLine v := Iff.rfl

section Action


instance octAction : MulAction ↥TA Vtx :=
  letI : MulAction ↥TA (Fin 2925) := MulAction.compHom (Fin 2925) titsLineHom
  inferInstance

theorem smul_inl (g : ↥TA) (p : Fin 1755) : g • (Sum.inl p : Vtx) = Sum.inl (g.1 p) := rfl

theorem smul_inr (g : ↥TA) (v : Fin 2925) :
    g • (Sum.inr v : Vtx) = Sum.inr (titsLineHom g v) := rfl

instance octGraphAction : GraphAction ↥TA octGraph where
  adj_smul g a b := by
    cases a <;> cases b
    · exact Iff.rfl
    · rename_i p v
      change g.1 p ∈ titsLine (titsLineHom g v) ↔ p ∈ titsLine v
      rw [titsLine_lineHom]
      exact Finset.smul_mem_smul_finset_iff g.1
    · rename_i v p
      change g.1 p ∈ titsLine (titsLineHom g v) ↔ p ∈ titsLine v
      rw [titsLine_lineHom]
      exact Finset.smul_mem_smul_finset_iff g.1
    · exact Iff.rfl

end Action

@[expose] def vCode : Vtx → ℕ
  | Sum.inl p => p
  | Sum.inr v => 1755 + v

@[expose] def ofCode (n : ℕ) : Vtx :=
  if h : n < 1755 then Sum.inl ⟨n, h⟩ else Sum.inr (finPt 2925 (n - 1755))

theorem vCode_lt (x : Vtx) : vCode x < 4680 := by
  cases x with
  | inl p => have := p.2; simp only [vCode]; omega
  | inr v => have := v.2; simp only [vCode]; omega

theorem ofCode_vCode (x : Vtx) : ofCode (vCode x) = x := by
  cases x with
  | inl p => simp [vCode, ofCode, p.2]
  | inr v =>
    have hv : 1755 + (v : ℕ) - 1755 < 2925 := by have := v.2; omega
    show ofCode (1755 + (v : ℕ)) = Sum.inr v
    unfold ofCode
    split
    · exfalso
      omega
    · exact congrArg Sum.inr (Fin.ext (by rw [finPt_val hv]; omega))

theorem vCode_ofCode {n : ℕ} (hn : n < 4680) : vCode (ofCode n) = n := by
  unfold ofCode
  split
  · rfl
  · show 1755 + ((finPt 2925 (n - 1755) : Fin 2925) : ℕ) = n
    rw [finPt_val (by omega)]
    omega

theorem vCode_injective : Function.Injective vCode := fun x y h =>
  (ofCode_vCode x).symm.trans ((congrArg ofCode h).trans (ofCode_vCode y))

theorem ofCode_inl {n : ℕ} (h : n < 1755) : ofCode n = Sum.inl ⟨n, h⟩ := by
  unfold ofCode
  split
  · rfl
  · exfalso
    omega

theorem ofCode_inr {n : ℕ} (h1 : 1755 ≤ n) (h2 : n < 4680) :
    ofCode n = Sum.inr ⟨n - 1755, by omega⟩ := by
  unfold ofCode
  split
  · exfalso
    omega
  · exact congrArg Sum.inr (Fin.ext (by rw [finPt_val (by omega)]))

end CFSG.Quasithin.H13.F45Ru
