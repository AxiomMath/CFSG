module

public import CFSG.Quasithin.MS93.S4AEA

public section

namespace CFSG.Quasithin.MS93.S4A

open Matrix
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def IsCocycle3 (f : SL3 F → (Fin 3 → F)) : Prop :=
  ∀ g h : SL3 F, f (g * h) = f g + ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f h

private theorem SL3_ext {g g' : SL3 F}
    (h : ∀ v : Fin 3 → F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) : g = g' :=
  Subtype.ext (Matrix.ext_of_mulVec_single fun _ => h _)

namespace IsCocycle3

variable {f : SL3 F → (Fin 3 → F)}

theorem map_one (hf : IsCocycle3 f) : f 1 = 0 := by
  have h := hf 1 1
  rw [mul_one, coe_one_SL3, one_mulVec] at h
  simpa using h

theorem map_inv (hf : IsCocycle3 f) (g : SL3 F) :
    f g⁻¹ = -(((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f g) := by
  have h := hf g⁻¹ g
  rw [inv_mul_cancel, hf.map_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem sub_coboundary (hf : IsCocycle3 f) (n : Fin 3 → F) :
    IsCocycle3 fun g => f g - (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n) := by
  intro g h
  simp only
  rw [hf g h, coe_mul_SL3, ← mulVec_mulVec, mulVec_sub, mulVec_sub]
  abel

theorem conj (hf : IsCocycle3 f) (y : SL3 F) :
    IsCocycle3 fun g => ((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f (y * g * y⁻¹) := by
  intro g h
  simp only
  have e : y * (g * h) * y⁻¹ = y * g * y⁻¹ * (y * h * y⁻¹) := by group
  have e' : y⁻¹ * (y * g * y⁻¹) = g * y⁻¹ := by group
  rw [e, hf, mulVec_add]
  congr 1
  rw [mulVec_mulVec, mulVec_mulVec, ← coe_mul_SL3, ← coe_mul_SL3, e']

theorem eq_zero_of_commute (hf : IsCocycle3 f) {h : SL3 F}
    (hfix : ∀ v : Fin 3 → F, ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v → v = 0)
    (hfh : f h = 0) {g : SL3 F} (hgh : g * h = h * g) : f g = 0 := by
  apply hfix
  have h1 := hf g h
  rw [hgh, hf h g, hfh, mulVec_zero, add_zero, zero_add] at h1
  exact h1

theorem rootElt_rel (hf : IsCocycle3 f) {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) :
    f (rootElt i k 1) k = 0 ∧ f (rootElt i k 1) j = -f (rootElt i j 1) k ∧
      f (rootElt i k 1) i = f (rootElt j k 1) j - f (rootElt j k 1) k - f (rootElt i j 1) k := by
  have hrel : rootElt i j (1 : F) * rootElt j k 1 =
      rootElt i k 1 * rootElt j k 1 * rootElt i j 1 := by
    have e := rootElt_commutator hij hjk hik (1 : F) 1
    rw [commutatorElement_def, mul_one] at e
    rw [← e]
    group
  have e := congrArg f hrel
  rw [hf, hf, hf, coe_mul_SL3, ← mulVec_mulVec, rootElt_mulVec hij, rootElt_mulVec hjk,
    rootElt_mulVec hik, rootElt_mulVec hik] at e
  have ei := congrFun e i
  have ej := congrFun e j
  have ek := congrFun e k
  simp only [one_mul, Pi.add_apply, Pi.single_eq_same, ne_eq, not_false_eq_true,
    Pi.single_eq_of_ne, add_zero, hij, hij.symm, hjk.symm, hik.symm] at ei ej ek
  exact ⟨by linear_combination -ek, by linear_combination -ej, by linear_combination -ei⟩

end IsCocycle3

private def zeroSet {f : SL3 F → (Fin 3 → F)} (hf : IsCocycle3 f) : Subgroup (SL3 F) where
  carrier := {g | f g = 0}
  mul_mem' {g h} hg hh := by
    change f (g * h) = 0
    rw [hf, show f g = 0 from hg, show f h = 0 from hh, mulVec_zero, add_zero]
  one_mem' := hf.map_one
  inv_mem' {g} hg := by
    change f g⁻¹ = 0
    rw [hf.map_inv, show f g = 0 from hg, mulVec_zero, neg_zero]

private theorem mem_zeroSet {f : SL3 F → (Fin 3 → F)} (hf : IsCocycle3 f) {g : SL3 F} :
    g ∈ zeroSet hf ↔ f g = 0 :=
  Iff.rfl

theorem eq_top_of_rootElt_mem_four {H : Subgroup (SL3 F)}
    (h01 : ∀ c : F, rootElt 0 1 c ∈ H) (h10 : ∀ c : F, rootElt 1 0 c ∈ H)
    (h12 : ∀ c : F, rootElt 1 2 c ∈ H) (h21 : ∀ c : F, rootElt 2 1 c ∈ H) : H = ⊤ := by
  have hcomm : ∀ {a b : SL3 F}, a ∈ H → b ∈ H → ⁅a, b⁆ ∈ H := fun ha hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
  have h02 : ∀ c : F, rootElt 0 2 c ∈ H := fun c => by
    have e := rootElt_commutator (show (0 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 2 by decide)
      (show (0 : Fin 3) ≠ 2 by decide) c 1
    rw [mul_one] at e
    rw [← e]
    exact hcomm (h01 c) (h12 1)
  have h20 : ∀ c : F, rootElt 2 0 c ∈ H := fun c => by
    have e := rootElt_commutator (show (2 : Fin 3) ≠ 1 by decide) (show (1 : Fin 3) ≠ 0 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) c 1
    rw [mul_one] at e
    rw [← e]
    exact hcomm (h21 c) (h10 1)
  apply eq_top_of_rootElt_mem
  intro i j c hij
  fin_cases i <;> fin_cases j
  all_goals first
    | exact absurd rfl hij
    | exact h01 c | exact h02 c | exact h10 c | exact h12 c | exact h20 c | exact h21 c

private def dg (d : Fin 3 → F) (hd : d 0 * d 1 * d 2 = 1) : SL3 F :=
  ⟨Matrix.diagonal d, by rw [Matrix.det_diagonal, Fin.prod_univ_three, hd]⟩

private theorem dg_mulVec (d : Fin 3 → F) (hd : d 0 * d 1 * d 2 = 1) (v : Fin 3 → F) :
    ((dg d hd : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = fun k => d k * v k := by
  funext k
  exact Matrix.mulVec_diagonal d v k

private theorem dg_comm {d d' : Fin 3 → F} (hd : d 0 * d 1 * d 2 = 1)
    (hd' : d' 0 * d' 1 * d' 2 = 1) : dg d hd * dg d' hd' = dg d' hd' * dg d hd := by
  apply SL3_ext
  intro v
  simp only [coe_mul_SL3, ← mulVec_mulVec, dg_mulVec]
  funext k
  ring

private theorem rootElt_mul_dg {d : Fin 3 → F} (hd : d 0 * d 1 * d 2 = 1) {i j : Fin 3}
    (hij : i ≠ j) (hdij : d i = d j) (c : F) :
    rootElt i j c * dg d hd = dg d hd * rootElt i j c := by
  apply SL3_ext
  intro v
  simp only [coe_mul_SL3, ← mulVec_mulVec, dg_mulVec, rootElt_mulVec hij]
  funext k
  by_cases hk : k = i
  · subst hk
    simp [hdij]
    ring
  · simp [hk]

private theorem dg_fix {d : Fin 3 → F} (hd : d 0 * d 1 * d 2 = 1) (h1 : ∀ k, d k ≠ 1)
    (v : Fin 3 → F) (hv : ((dg d hd : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) : v = 0 := by
  rw [dg_mulVec] at hv
  funext k
  have hk := congrFun hv k
  have : (d k - 1) * v k = 0 := by rw [sub_mul, one_mul, hk, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr (h1 k))

private theorem exists_eq_dg_sub {d : Fin 3 → F} (hd : d 0 * d 1 * d 2 = 1) (h1 : ∀ k, d k ≠ 1)
    (w : Fin 3 → F) :
    ∃ n : Fin 3 → F, w = ((dg d hd : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
  refine ⟨fun k => w k / (d k - 1), ?_⟩
  rw [dg_mulVec]
  funext k
  have := sub_ne_zero.mpr (h1 k)
  simp only [Pi.sub_apply]
  field_simp

theorem exists_coboundary_of_sq_ne_one {l : F} (hl0 : l ≠ 0) (hl : l ^ 2 ≠ 1)
    {f : SL3 F → (Fin 3 → F)} (hf : IsCocycle3 f) :
    ∃ n : Fin 3 → F, ∀ g : SL3 F, f g = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
  have hl1 : l ≠ 1 := fun h => hl (by rw [h, one_pow])
  have hm1 : (l ^ 2)⁻¹ ≠ 1 := fun h => hl (inv_eq_one.mp h)
  have hd : (![l, l, (l ^ 2)⁻¹] : Fin 3 → F) 0 * ![l, l, (l ^ 2)⁻¹] 1 *
      ![l, l, (l ^ 2)⁻¹] 2 = 1 := by
    change l * l * (l ^ 2)⁻¹ = 1
    field_simp
  have hd' : (![(l ^ 2)⁻¹, l, l] : Fin 3 → F) 0 * ![(l ^ 2)⁻¹, l, l] 1 *
      ![(l ^ 2)⁻¹, l, l] 2 = 1 := by
    change (l ^ 2)⁻¹ * l * l = 1
    field_simp
  have hfix : ∀ k, (![l, l, (l ^ 2)⁻¹] : Fin 3 → F) k ≠ 1 := fun k => by
    fin_cases k
    exacts [hl1, hl1, hm1]
  have hfix' : ∀ k, (![(l ^ 2)⁻¹, l, l] : Fin 3 → F) k ≠ 1 := fun k => by
    fin_cases k
    exacts [hm1, hl1, hl1]
  obtain ⟨n, hn⟩ := exists_eq_dg_sub hd hfix (f (dg _ hd))
  refine ⟨n, fun g => ?_⟩
  have hf' := hf.sub_coboundary n
  have hf'h : f (dg _ hd) - (((dg _ hd : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n) = 0 :=
    sub_eq_zero.mpr hn
  have hf'h' := hf'.eq_zero_of_commute (dg_fix hd hfix) hf'h (dg_comm hd' hd)
  have htop : zeroSet hf' = ⊤ := by
    apply eq_top_of_rootElt_mem_four <;> intro c <;> rw [mem_zeroSet]
    · exact hf'.eq_zero_of_commute (dg_fix hd hfix) hf'h
        (rootElt_mul_dg hd (show (0 : Fin 3) ≠ 1 by decide) rfl c)
    · exact hf'.eq_zero_of_commute (dg_fix hd hfix) hf'h
        (rootElt_mul_dg hd (show (1 : Fin 3) ≠ 0 by decide) rfl c)
    · exact hf'.eq_zero_of_commute (dg_fix hd' hfix') hf'h'
        (rootElt_mul_dg hd' (show (1 : Fin 3) ≠ 2 by decide) rfl c)
    · exact hf'.eq_zero_of_commute (dg_fix hd' hfix') hf'h'
        (rootElt_mul_dg hd' (show (2 : Fin 3) ≠ 1 by decide) rfl c)
  have hg : g ∈ zeroSet hf' := htop ▸ Subgroup.mem_top g
  exact sub_eq_zero.mp hg

private theorem exists_ne_zero_ne_one [Finite F] (hq : 2 < Nat.card F) :
    ∃ l : F, l ≠ 0 ∧ l ≠ 1 := by
  by_contra! h
  have hs : Function.Surjective fun b : Bool => if b then (1 : F) else 0 := by
    intro l
    by_cases hl : l = 0
    · exact ⟨false, by simp [hl]⟩
    · exact ⟨true, by simp [h l hl]⟩
  have := Nat.card_le_card_of_surjective _ hs
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at this
  omega

private theorem sq_ne_one_of_ne_one [CharP F 2] {l : F} (hl : l ≠ 1) : l ^ 2 ≠ 1 :=
  fun h => hl (CharTwo.sq_inj.mp (h.trans (one_pow 2).symm))

theorem exists_coboundary_of_four_le [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    {f : SL3 F → (Fin 3 → F)} (hf : IsCocycle3 f) :
    ∃ n : Fin 3 → F, ∀ g : SL3 F, f g = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
  obtain ⟨l, hl0, hl1⟩ := exists_ne_zero_ne_one (F := F) (by omega)
  exact exists_coboundary_of_sq_ne_one hl0 (sq_ne_one_of_ne_one hl1) hf

theorem exists_coboundary_of_apply_rootElt02 (h01 : ∀ c : F, c = 0 ∨ c = 1)
    {f : SL3 F → (Fin 3 → F)} (hf : IsCocycle3 f) (hε : f (rootElt 0 2 1) 1 = 0) :
    ∃ n : Fin 3 → F, ∀ g : SL3 F, f g = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
  obtain ⟨a1, b1, c1⟩ := hf.rootElt_rel (i := 0) (j := 1) (k := 2) (by decide) (by decide)
    (by decide)
  obtain ⟨a2, b2, c2⟩ := hf.rootElt_rel (i := 0) (j := 2) (k := 1) (by decide) (by decide)
    (by decide)
  obtain ⟨a3, b3, c3⟩ := hf.rootElt_rel (i := 1) (j := 0) (k := 2) (by decide) (by decide)
    (by decide)
  obtain ⟨a4, b4, c4⟩ := hf.rootElt_rel (i := 1) (j := 2) (k := 0) (by decide) (by decide)
    (by decide)
  obtain ⟨a5, b5, c5⟩ := hf.rootElt_rel (i := 2) (j := 0) (k := 1) (by decide) (by decide)
    (by decide)
  obtain ⟨a6, b6, c6⟩ := hf.rootElt_rel (i := 2) (j := 1) (k := 0) (by decide) (by decide)
    (by decide)
  have e01 : f (rootElt 0 1 1) 2 = 0 := by rw [b2, hε, neg_zero]
  have e12 : f (rootElt 1 2 1) 1 = f (rootElt 0 2 1) 0 := by linear_combination -c1 + a3 + e01
  have e10 : f (rootElt 1 0 1) 2 = 0 := by linear_combination c3 - e12 - a1
  have e12' : f (rootElt 1 2 1) 0 = 0 := by rw [b3, e10, neg_zero]
  have e20 : f (rootElt 2 0 1) 2 = f (rootElt 1 0 1) 1 := by linear_combination -c4 + a6 + e12'
  have e21 : f (rootElt 2 1 1) 0 = 0 := by linear_combination c6 - e20 - a4
  have e20' : f (rootElt 2 0 1) 1 = 0 := by rw [b6, e21, neg_zero]
  have e21' : f (rootElt 2 1 1) 2 = f (rootElt 0 1 1) 0 := by linear_combination c5 - a2 - e20'
  set n : Fin 3 → F := ![f (rootElt 1 0 1) 1, f (rootElt 0 1 1) 0, f (rootElt 0 2 1) 0] with hn
  have hroot : ∀ i j : Fin 3, i ≠ j →
      f (rootElt i j 1) = ((rootElt i j 1 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
    intro i j hij
    rw [rootElt_mulVec hij, add_sub_cancel_left, one_mul]
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | (funext m; fin_cases m <;>
          simp [hn, hε, a1, a2, a3, a4, a5, a6, e01, e12, e10, e12', e20, e21, e20', e21'])
  have hf' := hf.sub_coboundary n
  have htop : zeroSet hf' = ⊤ := by
    apply eq_top_of_rootElt_mem
    intro i j c hij
    rw [mem_zeroSet]
    rcases h01 c with rfl | rfl
    · rw [rootElt_zero, hf.map_one, coe_one_SL3, one_mulVec, sub_self, sub_zero]
    · rw [hroot i j hij, sub_self]
  refine ⟨n, fun g => ?_⟩
  exact sub_eq_zero.mp ((mem_zeroSet hf').mp (htop ▸ Subgroup.mem_top g))

theorem exists_conj_rootElt02_eq [Finite F] [CharP F 2] (h01 : ∀ c : F, c = 0 ∨ c = 1)
    {t : SL3 F} (ht : t * t = 1) (ht1 : t ≠ 1) : ∃ y : SL3 F, y * rootElt 0 2 1 * y⁻¹ = t := by
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq, ht]) ht1
  have hP : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  obtain ⟨x, hx⟩ := exists_conj_le_sStar hP
  have hs : x * t * x⁻¹ ∈ (sStar : Subgroup (SL3 F)) :=
    hx ⟨t, Subgroup.mem_zpowers t, rfl⟩
  obtain ⟨a, b, c, habc⟩ := mem_sStar_iff.mp hs
  suffices hz : ∃ z : SL3 F, z * rootElt 0 2 1 * z⁻¹ = uniTri a b c by
    obtain ⟨z, hz⟩ := hz
    refine ⟨x⁻¹ * z, ?_⟩
    calc x⁻¹ * z * rootElt 0 2 1 * (x⁻¹ * z)⁻¹ = x⁻¹ * (z * rootElt 0 2 1 * z⁻¹) * x := by
          group
      _ = t := by rw [hz, habc]; group
  have hinv : uniTri a b c * uniTri a b c = 1 := by
    rw [habc]
    calc x * t * x⁻¹ * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
      _ = 1 := by rw [ht, mul_one, mul_inv_cancel]
  have hne : uniTri a b c ≠ 1 := by
    rw [habc]
    intro h
    apply ht1
    calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
      _ = 1 := by rw [h, mul_one, inv_mul_cancel]
  have hac := (uniTri_mul_self_eq_one_iff a b c).mp hinv
  rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;> rcases h01 c with rfl | rfl
  · exact absurd uniTri_zero hne
  · exact ⟨swap01, by rw [swap01_conj_rootElt02, rootElt12_eq_uniTri]⟩
  · exact ⟨1, by rw [one_mul, inv_one, mul_one, rootElt02_eq_uniTri]⟩
  · refine ⟨rootElt 1 0 1, ?_⟩
    have e := rootElt_commutator (show (1 : Fin 3) ≠ 0 by decide)
      (show (0 : Fin 3) ≠ 2 by decide) (show (1 : Fin 3) ≠ 2 by decide) (1 : F) 1
    rw [commutatorElement_def, mul_one] at e
    rw [show uniTri (0 : F) 1 1 = rootElt 1 2 1 * rootElt 0 2 1 by
      rw [rootElt12_eq_uniTri, rootElt02_eq_uniTri, uniTri_mul]; simp, ← e]
    group
  · refine ⟨cyc * cyc * swap01, ?_⟩
    rw [← rootElt01_eq_uniTri]
    calc cyc * cyc * swap01 * rootElt 0 2 1 * (cyc * cyc * swap01)⁻¹ =
        cyc * (cyc * (swap01 * rootElt 0 2 (1 : F) * swap01⁻¹) * cyc⁻¹) * cyc⁻¹ := by group
      _ = rootElt 0 1 1 := by
        rw [swap01_conj_rootElt02, cyc_conj_rootElt, cyc_conj_rootElt]
        rfl
  · exact absurd hac (by simp)
  · refine ⟨rootElt 2 1 1, ?_⟩
    have e := rootElt_commutator (show (0 : Fin 3) ≠ 2 by decide)
      (show (2 : Fin 3) ≠ 1 by decide) (show (0 : Fin 3) ≠ 1 by decide) (1 : F) 1
    rw [commutatorElement_def, mul_one] at e
    have hinv01 : (rootElt 0 1 (1 : F))⁻¹ = rootElt 0 1 1 :=
      inv_eq_of_mul_eq_one_right (rootElt_mul_self 0 1 1)
    rw [show uniTri (1 : F) 1 0 = rootElt 0 1 1 * rootElt 0 2 1 by
      rw [rootElt01_eq_uniTri, rootElt02_eq_uniTri, uniTri_mul]; simp, ← hinv01, ← e]
    group
  · exact absurd hac (by simp)

theorem exists_coboundary_of_forall_eq_zero_or_eq_one [Finite F] [CharP F 2]
    (h01 : ∀ c : F, c = 0 ∨ c = 1) {f : SL3 F → (Fin 3 → F)} (hf : IsCocycle3 f) {t : SL3 F}
    (ht : t * t = 1) (ht1 : t ≠ 1) (hft : f t = 0) :
    ∃ n : Fin 3 → F, ∀ g : SL3 F, f g = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
  obtain ⟨y, hy⟩ := exists_conj_rootElt02_eq h01 ht ht1
  obtain ⟨n, hn⟩ := exists_coboundary_of_apply_rootElt02 h01 (hf.conj y) (by
    rw [hy, hft, mulVec_zero]
    rfl)
  refine ⟨((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n, fun g => ?_⟩
  have h := hn (y⁻¹ * g * y)
  rw [show y * (y⁻¹ * g * y) * y⁻¹ = g by group] at h
  calc f g = ((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((y⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ f g) := by
        rw [mulVec_mulVec, ← coe_mul_SL3, mul_inv_cancel, coe_one_SL3, one_mulVec]
    _ = ((y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((y⁻¹ * g * y : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n) := by rw [h]
    _ = _ := by
        rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, ← coe_mul_SL3, ← coe_mul_SL3,
          show y * (y⁻¹ * g * y) = g * y by group]

theorem exists_coboundary [Finite F] [CharP F 2] {f : SL3 F → (Fin 3 → F)} (hf : IsCocycle3 f)
    {t : SL3 F} (ht : t * t = 1) (ht1 : t ≠ 1) (hft : f t = 0) :
    ∃ n : Fin 3 → F, ∀ g : SL3 F, f g = ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ n - n := by
  by_cases h01 : ∀ c : F, c = 0 ∨ c = 1
  · exact exists_coboundary_of_forall_eq_zero_or_eq_one h01 hf ht ht1 hft
  · obtain ⟨l, hl⟩ := not_forall.mp h01
    rw [not_or] at hl
    exact exists_coboundary_of_sq_ne_one hl.1 (sq_ne_one_of_ne_one hl.2) hf

end CFSG.Quasithin.MS93.S4A
