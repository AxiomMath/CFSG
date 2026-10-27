module

public import CFSG.Quasithin.Vol2.KGFactC31J4M4F
public import Certificates.Data.J4M4GenData

public section

namespace CFSG.Quasithin.KGC31.J4M4.Gen

open CFSG.Sporadic.J4 CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4

@[expose] def Line.eval {G : Type*} [Group G] (inp : ℕ → G) (mem : List G) : Line → G
  | .gen k => inp k
  | .mul i j => mem.getD i 1 * mem.getD j 1
  | .inv i => (mem.getD i 1)⁻¹
  | .pow i e => mem.getD i 1 ^ e

@[expose] def evalSlp {G : Type*} [Group G] (inp : ℕ → G) : List Line → List G → List G
  | [], mem => mem
  | l :: ls, mem => evalSlp inp ls (mem ++ [l.eval inp mem])

theorem getD_append_singleton {α : Type*} (l : List α) (x d : α) (k : ℕ) :
    (l ++ [x]).getD k d = if k = l.length then x else l.getD k d := by
  rcases lt_trichotomy k l.length with h | h | h
  · rw [List.getD_append _ _ _ _ h, if_neg (by omega)]
  · subst h
    simp
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem evalSlp_mem {G : Type*} [Group G] (K : Subgroup G) {inp : ℕ → G} (hin : ∀ k, inp k ∈ K) :
    ∀ (ls : List Line) (mem : List G), (∀ k, mem.getD k 1 ∈ K) →
      ∀ k, (evalSlp inp ls mem).getD k 1 ∈ K
  | [], mem, hmem => hmem
  | l :: ls, mem, hmem => by
    refine evalSlp_mem K hin ls (mem ++ [l.eval inp mem]) (fun k => ?_)
    rw [getD_append_singleton]
    split_ifs
    · cases l with
      | gen j => exact hin j
      | mul i j => exact K.mul_mem (hmem i) (hmem j)
      | inv i => exact K.inv_mem (hmem i)
      | pow i e => exact K.pow_mem (hmem i) e
    · exact hmem k

@[expose, irreducible] noncomputable def z1Elt : G₀ := (evalSlp m4gen slpZ []).getD outZ 1

@[expose] noncomputable def inpC (k : ℕ) : G₀ := if k = 2 then z1Elt else baseJ k

@[expose, irreducible] noncomputable def cElt : G₀ := (evalSlp inpC slpC []).getD outC 1

@[expose] noncomputable def inpAB (k : ℕ) : G₀ := if k = 2 then cElt else m4gen k

@[expose, irreducible] noncomputable def apElt : G₀ := (evalSlp inpAB slpAB []).getD outA 1

@[expose, irreducible] noncomputable def bpElt : G₀ := (evalSlp inpAB slpAB []).getD outB 1

@[expose, irreducible] noncomputable def uElt : G₀ := wordProd m4gen uWord

theorem z1Elt_def : z1Elt = (evalSlp m4gen slpZ []).getD outZ 1 := by
  unfold z1Elt
  rfl

theorem cElt_def : cElt = (evalSlp inpC slpC []).getD outC 1 := by
  unfold cElt
  rfl

theorem apElt_def : apElt = (evalSlp inpAB slpAB []).getD outA 1 := by
  unfold apElt
  rfl

theorem bpElt_def : bpElt = (evalSlp inpAB slpAB []).getD outB 1 := by
  unfold bpElt
  rfl

theorem uElt_def : uElt = wordProd m4gen uWord := by
  unfold uElt
  rfl

theorem apElt_bpElt_mem (K : Subgroup G₀) (hw₁ : CFSG.Quasithin.KGJ4.w1 ∈ K)
    (hw₂ : CFSG.Quasithin.KGJ4.w2 ∈ K) (hc : cElt ∈ K) : apElt ∈ K ∧ bpElt ∈ K := by
  have hin : ∀ k, inpAB k ∈ K := fun k => by
    unfold inpAB
    split_ifs with h
    · exact hc
    · unfold m4gen
      split_ifs
      · exact hw₁
      · exact hw₂
      · exact K.one_mem
  have h := evalSlp_mem K hin slpAB [] (fun k => by simp [K.one_mem])
  rw [apElt_def, bpElt_def]
  exact ⟨h outA, h outB⟩

end CFSG.Quasithin.KGC31.J4M4.Gen

end
