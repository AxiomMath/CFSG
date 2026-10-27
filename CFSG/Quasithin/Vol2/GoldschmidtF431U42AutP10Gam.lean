module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Eq
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Mod

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431 CFSG.CosetTable
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem p10sA_one : p10sA 1 = fhatA := by
  refine Subtype.ext (eq_of_repL (repL_p10sA 1) ?_)
  have : p10sL.getD 1 idL = p10fL := by decide +kernel
  rw [this]
  exact repL_p10fL

theorem p10_sq_check : ∀ j < 6, evalSL [j, j] = idL := by decide +kernel

theorem p10sA_sq (j : ℕ) (hj : j < 6) : p10sA j * p10sA j = 1 := by
  have := wordSA_eq_one (p10_sq_check j hj)
  simpa [wordSA] using this

theorem p10_letters_cox : ∀ r ∈ p10Cox, ∀ l ∈ r, l.1.val < 6 := by decide

theorem p10_R3_eq : p10R3 = (List.replicate 3 ((6, true) :: [(3, true), (1, true), (2, true),
    (3, true), (4, true), (5, true)])).flatten := by decide

namespace RhoData

variable {G : Type} [Group G] (d : RhoData G)

@[expose] noncomputable def gG : Fin 7 → G := fun i => if i.val < 6 then d.ι (p10sA i.val) else d.ρ

theorem gG_lt (i : Fin 7) (h : i.val < 6) : d.gG i = d.ι (p10sA i.val) := by simp [gG, h]

theorem gG_six : d.gG 6 = d.ρ := by simp [gG]

theorem prod_gG (w : List (Fin 7)) (hw : ∀ i ∈ w, i.val < 6) :
    (w.map d.gG).prod = d.ι (wordSA (w.map Fin.val)) := by
  induction w with
  | nil => simp [wordSA]
  | cons i w ih =>
    rw [List.map_cons, List.prod_cons, ih fun j hj => hw j (List.mem_cons_of_mem _ hj),
      d.gG_lt i (hw i List.mem_cons_self), List.map_cons, ← map_mul]
    rfl

theorem rel_two (a : Ah) (hsq : a * a = 1)
    (hc : d.ρ * d.ι a * d.ρ⁻¹ = d.ι a * d.F) :
    d.ρ * (d.ι a * (d.ρ * (d.ρ * (d.ρ * (d.F * d.ι a))))) = 1 := by
  have hrx : d.ρ * d.ι a = d.ι a * d.F * d.ρ := by
    rw [← hc]; group
  have h4 : d.ρ * d.ρ * d.ρ * d.ρ = d.F * d.F := by
    have : d.ρ ^ 2 = d.F := d.sq
    calc d.ρ * d.ρ * d.ρ * d.ρ = d.ρ ^ 2 * d.ρ ^ 2 := by simp only [pow_two, mul_assoc]
      _ = d.F * d.F := by rw [this]
  have hxx : d.ι a * d.ι a = 1 := by rw [← map_mul, hsq, map_one]
  calc d.ρ * (d.ι a * (d.ρ * (d.ρ * (d.ρ * (d.F * d.ι a)))))
      = (d.ρ * d.ι a) * (d.ρ * d.ρ * d.ρ) * d.F * d.ι a := by group
    _ = (d.ι a * d.F * d.ρ) * (d.ρ * d.ρ * d.ρ) * d.F * d.ι a := by rw [hrx]
    _ = d.ι a * d.F * (d.ρ * d.ρ * d.ρ * d.ρ) * d.F * d.ι a := by group
    _ = d.ι a * (d.F * d.F) * (d.F * d.F) * d.ι a := by rw [h4]; group
    _ = 1 := by rw [d.F_mul_F]; simpa using hxx

theorem rel_holds [Finite G]
    (hH : Nat.card d.H = 576) : ∀ r ∈ p10Ws, ((r.map Prod.fst).map d.gG).prod = 1 := by
  intro r hr
  have hr' : r ∈ p10Cox ++ [p10R1] ++ p10R2 ++ [p10R3] := hr
  simp only [List.mem_append, List.mem_singleton] at hr'
  rcases hr' with ((hc | rfl) | h2) | rfl
  · rw [d.prod_gG _ (fun i hi => by
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hi
      exact p10_letters_cox r hc l hl)]
    have : (r.map Prod.fst).map Fin.val = relN r := by simp [relN, List.map_map]
    rw [this, wordSA_cox r hc, map_one]
  · have h1 := d.gG_six
    have h2 := d.gG_lt 1 (by decide)
    simp only [p10R1, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h1]
    rw [h2, show (1 : Fin 7).val = 1 from rfl, p10sA_one, ← mul_assoc, ← pow_two, d.sq]
    exact d.F_mul_F
  · have h6 := d.gG_six
    have hs1 : d.gG 1 = d.F := by
      rw [d.gG_lt 1 (by decide)]
      show d.ι (p10sA 1) = d.ι fhatA
      rw [p10sA_one]
    have hmem : r = [(6, true), (0, true), (6, true), (6, true), (6, true), (1, true), (0, true)] ∨
        r = [(6, true), (4, true), (6, true), (6, true), (6, true), (1, true), (4, true)] ∨
        r = [(6, true), (5, true), (6, true), (6, true), (6, true), (1, true), (5, true)] := by
      simpa [p10R2] using h2
    rcases hmem with rfl | rfl | rfl
    · have hj : d.gG 0 = d.ι (p10sA 0) := d.gG_lt 0 (by decide)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h6, hs1, hj]
      exact d.rel_two (p10sA 0) (p10sA_sq 0 (by decide)) (d.conj _ (by simp))
    · have hj : d.gG 4 = d.ι (p10sA 4) := d.gG_lt 4 (by decide)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h6, hs1, hj]
      exact d.rel_two (p10sA 4) (p10sA_sq 4 (by decide)) (d.conj _ (by simp))
    · have hj : d.gG 5 = d.ι (p10sA 5) := d.gG_lt 5 (by decide)
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, h6, hs1, hj]
      exact d.rel_two (p10sA 5) (p10sA_sq 5 (by decide)) (d.conj _ (by simp))
  · rw [p10_R3_eq]
    have hw0 : ∀ i ∈ [(3 : Fin 7), 1, 2, 3, 4, 5], i.val < 6 := by decide
    have hp := d.prod_gG [3, 1, 2, 3, 4, 5] hw0
    have hbase : ((((6, true) :: [(3, true), (1, true), (2, true), (3, true), (4, true),
        (5, true)] : List (Fin 7 × Bool)).map Prod.fst).map d.gG).prod = d.ρ * d.ι p10hA := by
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp ⊢
      rw [d.gG_six]
      congr 1
    simp only [List.map_flatten, List.map_replicate, List.prod_flatten, List.prod_replicate]
    rw [hbase]
    exact d.triangle hH

theorem lift_gG_pos (w : List (Fin 7)) :
    FreeGroup.lift d.gG (FreeGroup.mk (w.map fun i => (i, true))) = (w.map d.gG).prod := by
  rw [FreeGroup.lift_mk]
  simp [List.map_map, Function.comp_def]

@[expose] noncomputable def toG [Finite G]
    (hH : Nat.card d.H = 576) : PG 7 p10Ws →* G :=
  PresentedGroup.toGroup (f := d.gG) (by
    intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    rw [p10_eq_map_fst (p10_pos w hw), d.lift_gG_pos]
    exact d.rel_holds hH w hw)

theorem toG_of [Finite G]
    (hH : Nat.card d.H = 576) (i : Fin 7) : d.toG hH (PresentedGroup.of i) = d.gG i :=
  PresentedGroup.toGroup.of _

theorem toG_surjective [Finite G]
    (hH : Nat.card d.H = 576) (hG : d.ι.range ⊔ d.H = ⊤) : Function.Surjective (d.toG hH) := by
  set φ := d.toG hH with hφ
  have hι : d.ι.range ≤ φ.range := by
    rintro _ ⟨a, rfl⟩
    have ha : a ∈ Subgroup.closure (Set.range fun i : Fin 6 => p10sA i) := by
      rw [closure_p10sA]; trivial
    refine Subgroup.closure_induction (p := fun a _ => d.ι a ∈ φ.range) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨i, rfl⟩
      refine ⟨PresentedGroup.of (Fin.castLE (by omega : 6 ≤ 7) i), ?_⟩
      rw [hφ, d.toG_of hH, d.gG_lt _ (by simp)]
      rfl
    · rw [map_one]; exact φ.range.one_mem
    · intro x y _ _ hx hy
      rw [map_mul]; exact φ.range.mul_mem hx hy
    · intro x _ hx
      rw [map_inv]; exact φ.range.inv_mem hx
  have hρ : d.ρ ∈ φ.range := ⟨PresentedGroup.of 6, by rw [hφ, d.toG_of hH, d.gG_six]⟩
  have hH' : d.H ≤ φ.range := by
    rw [d.H_eq_sup hH]
    refine sup_le ?_ (Subgroup.zpowers_le.2 hρ)
    exact (Subgroup.map_le_range _ _).trans hι
  refine MonoidHom.range_eq_top.1 (eq_top_iff.2 ?_)
  rw [← hG]
  exact sup_le hι hH'

end RhoData

end CFSG.Quasithin.H13.F431.U42Aut
