module

public import CFSG.Quasithin.Background.Harris.R1.SignChoice
public import CFSG.Quasithin.Background.Harris.R1.D4VertPres

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.LieType.BorelTits
open D4Vert

section Words

variable {X : Type*} [Group X]

@[expose] def liftAB (r : List (Fin 2 × Bool)) : List (Fin 4 × Bool) :=
  r.map fun p => (![(2 : Fin 4), 3] p.1, p.2)

@[expose] def invW {m : ℕ} (r : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (r.map fun p => (p.1, !p.2)).reverse

theorem evalWord_liftAB (z x a b : X) (r : List (Fin 2 × Bool)) :
    evalWord ![z, x, a, b] (liftAB r) = evalWord ![a, b] r := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    simp only [liftAB, List.map_cons] at ih ⊢
    rw [evalWord_cons, evalWord_cons, ih]
    obtain ⟨i, s⟩ := p
    fin_cases i <;> rfl

theorem evalWord_invW {m : ℕ} (g : Fin m → X) (r : List (Fin m × Bool)) :
    evalWord g (invW r) = (evalWord g r)⁻¹ := by
  induction r with
  | nil => simp [invW, evalWord]
  | cons p r ih =>
    simp only [invW, List.map_cons, List.reverse_cons] at ih ⊢
    rw [evalWord_append, ih]
    obtain ⟨i, s⟩ := p
    cases s <;> simp [evalWord]

theorem evalWord_flatten {m : ℕ} (g : Fin m → X) (L : List (List (Fin m × Bool))) :
    evalWord g L.flatten = (L.map (evalWord g)).prod := by
  induction L with
  | nil => rfl
  | cons r L ih => rw [List.flatten_cons, evalWord_append, ih, List.map_cons, List.prod_cons]

theorem hRels_low (i : Fin 4) : hRels.getD (5 + i) [] = liftAB (l28Rels.getD i []) := by
  fin_cases i <;> decide +kernel

theorem hRels9 : hRels.getD 9 [] = [(1, true)] ++ liftAB l28C ++ [(1, false)] ++ invW (liftAB l28C) := by
  decide +kernel

theorem hRels10 :
    hRels.getD 10 [] = [(1, true)] ++ liftAB l28U ++ [(1, false)] ++ invW (liftAB l28U) := by
  decide +kernel

theorem hRels11 : hRels.getD 11 [] =
    [(1, true), (2, true), (1, true), (2, false), (1, false), (2, true), (1, false), (2, false),
      (0, false)] := by
  decide +kernel

theorem hRels12 : hRels.getD 12 [] =
    (List.ofFn fun i : Fin 9 => liftAB (l28H.getD i []) ++ [(1, true)] ++
      invW (liftAB (l28H.getD i []))).flatten ++ [(0, false)] := by
  decide +kernel

theorem hRels_length : hRels.length = 13 := by decide +kernel

theorem l28Rels_getD_mem (i : Fin 4) : l28Rels.getD i [] ∈ l28Rels := by
  fin_cases i <;> decide +kernel

theorem evalWord_hRels {z x a b : X} (hz2 : z * z = 1) (hzx : z * x = x * z) (hza : z * a = a * z)
    (hzb : z * b = b * z) (hx2 : x * x = 1) (hl28 : ∀ r ∈ l28Rels, evalWord ![a, b] r = 1)
    (hxc : x * evalWord ![a, b] l28C = evalWord ![a, b] l28C * x)
    (hxu : x * evalWord ![a, b] l28U = evalWord ![a, b] l28U * x)
    (hxa : x * a * x * a⁻¹ * x⁻¹ * a * x⁻¹ * a⁻¹ = z)
    (hprod : (List.ofFn fun i : Fin 9 => evalWord ![a, b] (l28H.getD i []) * x *
      (evalWord ![a, b] (l28H.getD i []))⁻¹).prod = z) :
    ∀ r ∈ hRels, evalWord ![z, x, a, b] r = 1 := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
  rw [hRels_length] at hi
  have hget : hRels[i]'(by rw [hRels_length]; exact hi) = hRels.getD i [] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]
    rfl
  rw [hget]
  have hcomm : ∀ {u v : X}, u * v = v * u → u * v * u⁻¹ * v⁻¹ = 1 := fun {u v} h => by
    rw [h]; group
  interval_cases i
  · show evalWord _ [(0, true), (0, true)] = 1
    simp [evalWord, hz2]
  · show evalWord _ [(0, true), (1, true), (0, false), (1, false)] = 1
    have := hcomm hzx
    simpa [evalWord, mul_assoc] using this
  · show evalWord _ [(0, true), (2, true), (0, false), (2, false)] = 1
    have := hcomm hza
    simpa [evalWord, mul_assoc] using this
  · show evalWord _ [(0, true), (3, true), (0, false), (3, false)] = 1
    have := hcomm hzb
    simpa [evalWord, mul_assoc] using this
  · show evalWord _ [(1, true), (1, true)] = 1
    simp [evalWord, hx2]
  · rw [show (5 : ℕ) = 5 + (0 : Fin 4) from rfl, hRels_low, evalWord_liftAB]
    exact hl28 _ (l28Rels_getD_mem 0)
  · rw [show (6 : ℕ) = 5 + (1 : Fin 4) from rfl, hRels_low, evalWord_liftAB]
    exact hl28 _ (l28Rels_getD_mem 1)
  · rw [show (7 : ℕ) = 5 + (2 : Fin 4) from rfl, hRels_low, evalWord_liftAB]
    exact hl28 _ (l28Rels_getD_mem 2)
  · rw [show (8 : ℕ) = 5 + (3 : Fin 4) from rfl, hRels_low, evalWord_liftAB]
    exact hl28 _ (l28Rels_getD_mem 3)
  · rw [hRels9, evalWord_append, evalWord_append, evalWord_append, evalWord_invW, evalWord_liftAB]
    have := hcomm hxc
    simpa [evalWord, mul_assoc] using this
  · rw [hRels10, evalWord_append, evalWord_append, evalWord_append, evalWord_invW, evalWord_liftAB]
    have := hcomm hxu
    simpa [evalWord, mul_assoc] using this
  · rw [hRels11]
    simp only [evalWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    simp only [Matrix.cons_val, Bool.false_eq_true, ↓reduceIte, mul_one]
    rw [← hxa]
    group
  · rw [hRels12, evalWord_append, evalWord_flatten]
    have e : (List.map (evalWord ![z, x, a, b]) (List.ofFn fun i : Fin 9 =>
        liftAB (l28H.getD i []) ++ [(1, true)] ++ invW (liftAB (l28H.getD i [])))) =
        List.ofFn fun i : Fin 9 => evalWord ![a, b] (l28H.getD i []) * x *
          (evalWord ![a, b] (l28H.getD i []))⁻¹ := by
      rw [List.map_ofFn]
      congr 1
      funext i
      simp only [Function.comp_apply]
      rw [evalWord_append, evalWord_append, evalWord_invW, evalWord_liftAB]
      simp [evalWord]
    rw [e, hprod]
    simp [evalWord]

end Words

section Flip

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω) {z : G} {σ : Ω → G}

theorem IsSignChoice.flip (hz : z ∈ Zs) (hσ : IsSignChoice C z σ) :
    IsSignChoice C z (fun ω => z * σ ω) := by
  intro ω
  show z * σ ω = C.zf ω ∨ z * σ ω = z * C.zf ω
  rcases hσ ω with h | h
  · right; rw [h]
  · left; rw [h, ← mul_assoc, C.Zs_sq hz, one_mul]

theorem signStab_flip (hz : z ∈ Zs) : signStab C (fun ω => z * σ ω) = signStab C σ := by
  ext k
  rw [mem_signStab_iff, mem_signStab_iff]
  refine exists_congr fun hk => forall_congr' fun ω => ?_
  have hzk : k * z * k⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp (C.h.K1_cent_Z hk) z hz
    rw [← this]; group
  have e : k * (z * σ ω) * k⁻¹ = z * (k * σ ω * k⁻¹) := by
    calc k * (z * σ ω) * k⁻¹ = (k * z * k⁻¹) * (k * σ ω * k⁻¹) := by group
      _ = z * (k * σ ω * k⁻¹) := by rw [hzk]
  rw [e]
  exact ⟨fun h => mul_left_cancel h, fun h => by rw [h]⟩

end Flip

end CFSG.Quasithin.Background.Harris.R1
