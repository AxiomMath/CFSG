module

public import CFSG.Timmesfeld.Transvection.PresSp
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.Timmesfeld.ARS.CaseOADeg

open CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.Pres CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Symplectic
open scoped commutatorElement

@[expose] def graphPair : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → (Fin 2 ⊕ Fin 2) × (Fin 2 ⊕ Fin 2)
  | .inl a, .inl b => if a = b then (if a = 0 then (.inl 0, .inl 1) else (.inl 0, .inr 1))
      else (.inl 0, .inl 0)
  | .inr a, .inr b => if a = b then (if a = 0 then (.inr 0, .inr 1) else (.inl 1, .inr 0))
      else (.inr 0, .inr 0)
  | .inl a, .inr b => if a = b then (.inl 0, .inl 0) else
      (if a = 0 then (.inl 1, .inl 1) else (.inr 1, .inr 1))
  | .inr a, .inl b => if a = b then (.inl 0, .inl 0) else
      (if b = 0 then (.inl 1, .inl 1) else (.inr 1, .inr 1))

theorem graphPair_comm (a b : Fin 2 ⊕ Fin 2) : graphPair b a = graphPair a b := by
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;> rfl

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def sqrtF (c : K) : K := (frobeniusEquiv K 2).symm c

theorem sqrtF_sq (c : K) : sqrtF c ^ 2 = c := by
  have h := frobenius_apply_frobeniusEquiv_symm K 2 c
  rwa [frobenius_def] at h

theorem sqrtF_add (c d : K) : sqrtF (c + d) = sqrtF c + sqrtF d :=
  map_add (frobeniusEquiv K 2).symm c d

theorem sqrtF_sq_mul (s t : K) : sqrtF (s ^ 2 * t) = s * sqrtF t := by
  have e : s ^ 2 * t = (s * sqrtF t) ^ 2 := by rw [mul_pow, sqrtF_sq]
  rw [e, sqrtF, ← frobenius_def, frobeniusEquiv_symm_apply_frobenius]

@[expose] noncomputable def graphElt (a b : Fin 2 ⊕ Fin 2) (c : K) : StatedSp 2 K :=
  spElt (graphPair a b).1 (graphPair a b).2 (if a = b then sqrtF c else c)

section Model

omit [Finite K]

theorem model_comm {p q p' q' : Fin 2 ⊕ Fin 2} (h1 : q ≠ Sum.swap p) (h2 : q' ≠ Sum.swap p')
    (h3 : p' ≠ Sum.swap p) (h4 : p' ≠ Sum.swap q) (h5 : q' ≠ Sum.swap p) (h6 : q' ≠ Sum.swap q)
    (s t : K) : ⁅spElt p q s, spElt p' q' t⁆ = 1 :=
  (spRelationsModel (n := 2) (K := K)).comm p q p' q' h1 h2 h3 h4 h5 h6 s t

theorem model_commLong {a b b' : Fin 2 ⊕ Fin 2} (h : idx a ≠ idx b) (hb : b' = Sum.swap b)
    (s t : K) : ⁅spElt a b s, spElt a b' t⁆ = 1 := by
  subst hb
  exact (spRelationsModel (n := 2) (K := K)).commLong a b h s t

theorem swap_ne_swap_of_idx_ne {a b : Fin 2 ⊕ Fin 2} (h : idx a ≠ idx b) :
    Sum.swap b ≠ Sum.swap a :=
  fun e => ne_of_idx_ne h (by simpa using congrArg Sum.swap e)

theorem model_commLong₁ {a b b' : Fin 2 ⊕ Fin 2} (h : idx a ≠ idx b) (hb : b' = Sum.swap b)
    (s t : K) : ⁅spElt b a s, spElt a b' t⁆ = 1 := by
  rw [spElt_comm (ne_swap_of_idx_ne h)]
  exact model_commLong h hb s t

theorem model_commLong₂ {a b b' : Fin 2 ⊕ Fin 2} (h : idx a ≠ idx b) (hb : b' = Sum.swap b)
    (s t : K) : ⁅spElt a b s, spElt b' a t⁆ = 1 := by
  subst hb
  rw [spElt_comm (swap_ne_swap_of_idx_ne h)]
  exact model_commLong h rfl s t

theorem model_commLong₃ {a b b' : Fin 2 ⊕ Fin 2} (h : idx a ≠ idx b) (hb : b' = Sum.swap b)
    (s t : K) : ⁅spElt b a s, spElt b' a t⁆ = 1 := by
  rw [spElt_comm (ne_swap_of_idx_ne h)]
  exact model_commLong₂ h hb s t

end Model

theorem model_longShort {c d x y x' y' : Fin 2 ⊕ Fin 2} (h : idx c ≠ idx d)
    (hxy : (x = Sum.swap c ∧ y = d) ∨ (x = d ∧ y = Sum.swap c))
    (hxy' : (x' = c ∧ y' = d) ∨ (x' = d ∧ y' = c)) (s t : K) :
    ⁅spElt c c s, spElt x y (sqrtF t)⁆ = spElt d d (s * t) * spElt x' y' (sqrtF (s ^ 2 * t)) := by
  have hdc : d ≠ Sum.swap c := ne_swap_of_idx_ne h
  have hcd : c ≠ Sum.swap d := ne_swap_of_idx_ne h.symm
  have hdc' : d ≠ Sum.swap (Sum.swap c) := by rw [Sum.swap_swap]; exact ne_of_idx_ne h
  have e1 : spElt x y (sqrtF t) = spElt (Sum.swap c) d (sqrtF t) := by
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact spElt_comm hdc' _
  have e2 : spElt x' y' (sqrtF (s ^ 2 * t)) = spElt c d (s * sqrtF t) := by
    rw [sqrtF_sq_mul]
    rcases hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact spElt_comm hdc _
  have hcomm : Commute (spElt (n := 2) d d (s * t)) (spElt c d (s * sqrtF t)) := by
    have := model_comm (K := K) (p := c) (q := d) (p' := d) (q' := d) hdc
      ((swap_ne_self d).symm) hdc ((swap_ne_self d).symm) hdc ((swap_ne_self d).symm)
      (s * sqrtF t) (s * t)
    exact ((commutatorElement_eq_one_iff_mul_comm.1 this).symm)
  have hls := (spRelationsModel (n := 2) (K := K)).longShort h s (sqrtF t)
  rw [spRelationsModel_ξ] at hls
  rw [e1, e2, hls, sqrtF_sq]
  exact hcomm.eq.symm

macro "graph_comm" : tactic => `(tactic| first
  | (with_reducible refine model_comm ?_ ?_ ?_ ?_ ?_ ?_ _ _) <;> decide
  | (with_reducible refine model_commLong ?_ ?_ _ _) <;> decide
  | (with_reducible refine model_commLong₁ ?_ ?_ _ _) <;> decide
  | (with_reducible refine model_commLong₂ ?_ ?_ _ _) <;> decide
  | (with_reducible refine model_commLong₃ ?_ ?_ _ _) <;> decide)

theorem graphElt_symm (a b : Fin 2 ⊕ Fin 2) (c : K) : graphElt b a c = graphElt a b c := by
  by_cases hab : a = b
  · subst hab; rfl
  · simp only [graphElt, graphPair_comm, hab, Ne.symm hab, ite_false]

theorem graphElt_add (a b : Fin 2 ⊕ Fin 2) (s t : K) :
    graphElt a b (s + t) = graphElt a b s * graphElt a b t := by
  rw [graphElt, graphElt, graphElt]
  split_ifs
  · rw [sqrtF_add, spElt_add]
  · rw [spElt_add]

theorem graphElt_short (a b d : Fin 2 ⊕ Fin 2) (hab : idx a ≠ idx b) (hbd : idx b ≠ idx d)
    (had : idx a ≠ idx d) (s t : K) :
    ⁅graphElt a b s, graphElt (Sum.swap b) d t⁆ = graphElt a d (s * t) := by
  exfalso
  revert hab hbd had
  generalize idx a = x
  generalize idx b = y
  generalize idx d = z
  revert x y z
  decide

theorem graphElt_shortLong (a b : Fin 2 ⊕ Fin 2) (hab : idx a ≠ idx b) (s t : K) :
    ⁅graphElt a b s, graphElt (Sum.swap b) (Sum.swap b) t⁆ =
      graphElt a (Sum.swap b) (s * t) * graphElt a a (s ^ 2 * t) := by
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [graphElt, graphPair, idx] at hab ⊢ <;>
    ((with_reducible refine model_longShort ?_ ?_ ?_ s t) <;> decide)

theorem graphElt_commLong (a b : Fin 2 ⊕ Fin 2) (hab : idx a ≠ idx b) (s t : K) :
    ⁅graphElt a b s, graphElt a (Sum.swap b) t⁆ = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [graphElt, graphPair, idx] at hab ⊢ <;> graph_comm

theorem graphElt_commLL (a c : Fin 2 ⊕ Fin 2) (hca : c ≠ Sum.swap a) (s t : K) :
    ⁅graphElt a a s, graphElt c c t⁆ = 1 := by
  rcases a with a | a <;> rcases c with c | c <;> fin_cases a <;> fin_cases c <;>
    simp [graphElt, graphPair] at hca ⊢ <;> graph_comm

theorem graphElt_commLS (a c d : Fin 2 ⊕ Fin 2) (hcd : idx c ≠ idx d) (hca : c ≠ Sum.swap a)
    (hda : d ≠ Sum.swap a) (s t : K) : ⁅graphElt a a s, graphElt c d t⁆ = 1 := by
  rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> fin_cases a <;>
    fin_cases c <;> fin_cases d <;>
    simp [graphElt, graphPair, idx] at hcd hca hda ⊢ <;> graph_comm

theorem graphElt_commSS (a b c d : Fin 2 ⊕ Fin 2) (hab : idx a ≠ idx b) (hcd : idx c ≠ idx d)
    (hca : c ≠ Sum.swap a) (hcb : c ≠ Sum.swap b) (hda : d ≠ Sum.swap a) (hdb : d ≠ Sum.swap b)
    (s t : K) : ⁅graphElt a b s, graphElt c d t⁆ = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d <;>
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [graphElt, graphPair, idx] at hab hcd hca hcb hda hdb ⊢ <;> graph_comm

@[expose] noncomputable def graphRelations : SpRelations 2 K (StatedSp 2 K) :=
  SpRelations.ofSplit graphElt (fun a b _ c => graphElt_symm a b c)
    (fun a b _ s t => graphElt_add a b s t) graphElt_short graphElt_shortLong graphElt_commLong
    graphElt_commLL graphElt_commLS graphElt_commSS

@[expose] noncomputable def graphHom : StatedSp 2 K →* StatedSp 2 K :=
  (graphRelations (K := K)).toHom le_rfl

theorem graphHom_spElt {a b : Fin 2 ⊕ Fin 2} (hab : b ≠ Sum.swap a) (c : K) :
    graphHom (spElt a b c) = graphElt a b c :=
  (graphRelations (K := K)).toHom_spElt le_rfl hab c

theorem graphHom_x_single_zero (c : K) :
    graphHom (Sp.x 2 K (Pi.single 0 1) c) = spElt (Sum.inl 1) (Sum.inl 1) c := by
  rw [x_eq_spElt (a := Sum.inl 0) (b := Sum.inr 1) (by decide) (by decide),
    graphHom_spElt (by decide)]
  rfl

theorem graphHom_x_neg_single_zero (c : K) :
    graphHom (Sp.x 2 K (-Pi.single 0 1) c) = spElt (Sum.inr 1) (Sum.inr 1) c := by
  rw [x_eq_spElt (a := Sum.inl 1) (b := Sum.inr 0) (by decide) (by decide),
    graphHom_spElt (by decide)]
  rfl

theorem graphHom_x_single_one (c : K) :
    graphHom (Sp.x 2 K (Pi.single 1 1) c) = spElt (Sum.inl 0) (Sum.inr 1) (sqrtF c) := by
  rw [x_eq_spElt (a := Sum.inl 1) (b := Sum.inl 1) (by decide) (by decide),
    graphHom_spElt (by decide)]
  rfl

theorem graphHom_x_neg_single_one (c : K) :
    graphHom (Sp.x 2 K (-Pi.single 1 1) c) = spElt (Sum.inl 1) (Sum.inr 0) (sqrtF c) := by
  rw [x_eq_spElt (a := Sum.inr 1) (b := Sum.inr 1) (by decide) (by decide),
    graphHom_spElt (by decide)]
  rfl

end CFSG.Timmesfeld.ARS.CaseOADeg
