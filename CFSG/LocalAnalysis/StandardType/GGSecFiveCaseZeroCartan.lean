module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.Sporadic.Bridge.ONSurj

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma cartanB_step_zmod {p : ℕ} [Fact p.Prime] {m : ℕ} {i j : Fin m}
    (hj : j.val + 1 < m) :
    ((CartanMatrix.B m i j : ℤ) : ZMod p) =
      ((if i = j then (1 : ZMod p) else 0) - (if i.val + 1 = j.val then 1 else 0)) -
        ((if i = ⟨j.val + 1, hj⟩ then (1 : ZMod p) else 0) -
          (if i.val + 1 = j.val + 1 then 1 else 0)) := by
  have hjne : j.val ≠ m - 1 := by omega
  by_cases h1 : i = j
  · subst h1
    have h2 : ¬ i.val + 1 = i.val := by omega
    have h3 : ¬ i = ⟨i.val + 1, hj⟩ := by
      intro h
      have hval := congrArg Fin.val h
      simp only at hval
      omega
    simp [CartanMatrix.B, Matrix.of_apply, h3]
    norm_num
  · by_cases h2 : i.val + 1 = j.val
    · have hB : ((CartanMatrix.B m i j : ℤ) : ZMod p) = -1 := by
        simp only [CartanMatrix.B, Matrix.of_apply]
        rw [if_neg h1, if_pos h2, if_neg hjne]
        norm_num
      rw [hB]
      have h3 : ¬ i = ⟨j.val + 1, hj⟩ := by
        intro h
        have hval := congrArg Fin.val h
        simp only at hval
        omega
      have h4 : ¬ i.val + 1 = j.val + 1 := by omega
      simp [h1, h2, h3]
    · by_cases h3 : i = ⟨j.val + 1, hj⟩
      · have hB : ((CartanMatrix.B m i j : ℤ) : ZMod p) = -1 := by
          simp only [CartanMatrix.B, Matrix.of_apply]
          rw [if_neg h1, if_neg h2, if_pos (show j.val + 1 = i.val from by
            have hval := congrArg Fin.val h3
            simp only at hval
            omega)]
          norm_num
        rw [hB]
        have h4 : ¬ i.val + 1 = j.val + 1 := by
          have hval := congrArg Fin.val h3
          simp only at hval
          omega
        have h5 : ¬ (⟨j.val + 1, hj⟩ : Fin m) = j := by
          intro h
          have hval := congrArg Fin.val h
          simp only at hval
          omega
        have h6 : ¬ j.val + 1 + 1 = j.val := by omega
        simp [h3, h5, h6]
      · have hB : ((CartanMatrix.B m i j : ℤ) : ZMod p) = 0 := by
          simp only [CartanMatrix.B, Matrix.of_apply]
          rw [if_neg h1, if_neg h2]
          have hji : ¬ j.val + 1 = i.val := by
            intro h
            exact h3 (Fin.ext h.symm)
          rw [if_neg hji]
          norm_num
        rw [hB]
        have h4 : ¬ i.val + 1 = j.val + 1 := by
          intro h
          exact h1 (Fin.ext (by omega))
        have h1val : ¬ i.val = j.val := by
          intro h
          exact h1 (Fin.ext h)
        simp [h1, h1val, h2, h3]

private lemma cartanB_last_zmod {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ} {last : Fin m}
    (hlast : last.val = m - 1) (i : Fin m) :
    (2 : ZMod p)⁻¹ * ((CartanMatrix.B m i last : ℤ) : ZMod p) =
      (if i = last then (1 : ZMod p) else 0) -
        (if i.val + 1 = last.val then 1 else 0) := by
  have htwo : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
  have hc : (2 : ZMod p)⁻¹ * 2 = 1 := inv_mul_cancel₀ htwo
  have hcneg : (2 : ZMod p)⁻¹ * (-2) = -1 := by
    rw [mul_neg, hc]
  by_cases h1 : i = last
  · rw [h1]
    have hB : ((CartanMatrix.B m last last : ℤ) : ZMod p) = 2 := by
      simp [CartanMatrix.B, Matrix.of_apply]
    rw [hB, hc]
    have hne : last.val + 1 ≠ last.val := by omega
    simp
  · by_cases h2 : i.val + 1 = last.val
    · have hB : ((CartanMatrix.B m i last : ℤ) : ZMod p) = -2 := by
        simp only [CartanMatrix.B, Matrix.of_apply]
        rw [if_neg h1, if_pos h2, if_pos hlast]
        norm_num
      rw [hB, hcneg]
      simp [h1, h2]
    · have hB : ((CartanMatrix.B m i last : ℤ) : ZMod p) = 0 := by
        simp only [CartanMatrix.B, Matrix.of_apply]
        rw [if_neg h1, if_neg h2]
        have h3 : ¬ last.val + 1 = i.val := by omega
        rw [if_neg h3]
        norm_num
      rw [hB, mul_zero]
      simp [h1, h2]

section

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggCZ_coordsB (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) {m : ℕ} (hm : 2 ≤ m)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggInduced ⊤ Bs) (f : (CoxeterMatrix.B m).Group ≃* ↥A)
    (hf : ∀ i, GGIsReflection p ((f ((CoxeterMatrix.B m).simple i) : ↥A) : MulAut ↥Bs))
    (ιV : Additive ↥Bs ≃+ V) :
    ∃ (e : Fin m → V) (φ : Fin m → Module.Dual (ZMod p) V), GGCZDual e φ ∧
      Subgroup.map (ggLin (p := p) ιV) A = ggCZWB p e φ := by
  classical
  have hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs := fun φ hφ => hA hφ
  obtain ⟨h, α, hα, hrefl, hP⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_iso (p := p) hp2 hNT
      (ggIntCartan_B m) (SecFiveRootRefl.entries_B m)
      (SecFiveRootRefl.cartanTree_B m (by omega)) f hf hind ιV
  let last : Fin m := ⟨m - 1, by omega⟩
  let c : ZMod p := (2 : ZMod p)⁻¹
  let e : Fin m → V := fun j => (∑ k ∈ Finset.Ici j, h k) - c • h last
  let φ : Fin m → Module.Dual (ZMod p) V := fun i => ∑ l ∈ Finset.Ici i, α l
  have hIci_succ : ∀ j (hj : j.val + 1 < m),
      Finset.Ici j = insert j (Finset.Ici (⟨j.val + 1, hj⟩ : Fin m)) := by
    intro j hj
    ext x
    simp only [Finset.mem_Ici, Finset.mem_insert]
    constructor
    · intro hx
      by_cases hxj : x = j
      · exact Or.inl hxj
      · right
        simp only [Fin.le_def] at hx ⊢
        omega
    · rintro (rfl | hx)
      · exact le_rfl
      · simp only [Fin.le_def] at hx ⊢
        omega
  have he_succ : ∀ j (hj : j.val + 1 < m),
      e j = h j + e (⟨j.val + 1, hj⟩ : Fin m) := by
    intro j hj
    have hnot : j ∉ Finset.Ici (⟨j.val + 1, hj⟩ : Fin m) := by
      simp only [Finset.mem_Ici, Fin.le_def]
      omega
    simp only [e, hIci_succ j hj, Finset.sum_insert hnot]
    abel
  have hIci_last : Finset.Ici last = {last} := by
    ext x
    simp only [Finset.mem_Ici, Finset.mem_singleton]
    constructor
    · intro hx
      have hx' : last.val ≤ x.val := hx
      have hlastval : last.val = m - 1 := rfl
      have hxlt : x.val < m := x.isLt
      exact Fin.ext (by omega)
    · rintro rfl
      exact le_rfl
  have he_last : (2 : ZMod p) • e last = h last := by
    have hc2 : (2 : ZMod p) * c = 1 := by
      simp only [c]
      exact mul_inv_cancel₀ (zmod_two_ne_zero hp2)
    simp only [e, hIci_last, Finset.sum_singleton]
    rw [smul_sub, smul_smul, hc2, one_smul, two_smul]
    abel
  have hφ_succ : ∀ i (hi : i.val + 1 < m),
      φ i = α i + φ (⟨i.val + 1, hi⟩ : Fin m) := by
    intro i hi
    have hnot : i ∉ Finset.Ici (⟨i.val + 1, hi⟩ : Fin m) := by
      simp only [Finset.mem_Ici, Fin.le_def]
      omega
    simp only [φ, hIci_succ i hi, Finset.sum_insert hnot]
  have hφ_last : φ last = α last := by
    simp only [φ, hIci_last, Finset.sum_singleton]
  have hα_succ : ∀ i (hi : i.val + 1 < m),
      α i = φ i - φ (⟨i.val + 1, hi⟩ : Fin m) := by
    intro i hi
    rw [hφ_succ i hi]
    abel
  have hh_succ : ∀ i (hi : i.val + 1 < m),
      h i = e i - e (⟨i.val + 1, hi⟩ : Fin m) := by
    intro i hi
    rw [he_succ i hi]
    abel
  have hαe : ∀ i j : Fin m, α i (e j) =
      (if i = j then (1 : ZMod p) else 0) - (if i.val + 1 = j.val then 1 else 0) := by
    intro i j
    induction hk : (m - 1 - j.val) using Nat.strong_induction_on generalizing j with
    | h n ih =>
      by_cases hj : j.val + 1 = m
      · have hjeq : j = last := Fin.ext (by simp [last]; omega)
        rw [hjeq]
        have hbase : α i (e last) = c * ((CartanMatrix.B m i last : ℤ) : ZMod p) := by
          have h2e : (2 : ZMod p) * α i (e last) =
              ((CartanMatrix.B m i last : ℤ) : ZMod p) := by
            have h := congrArg (α i) he_last
            simpa [map_smul, smul_eq_mul, hP] using h
          calc α i (e last)
              = c * ((2 : ZMod p) * α i (e last)) := by
                  rw [← mul_assoc, inv_mul_cancel₀ (zmod_two_ne_zero hp2), one_mul]
            _ = c * ((CartanMatrix.B m i last : ℤ) : ZMod p) := by rw [h2e]
        rw [hbase]
        exact cartanB_last_zmod hp2 rfl i
      · have hlt : j.val + 1 < m := by omega
        let j' : Fin m := ⟨j.val + 1, hlt⟩
        have hih : α i (e j') =
            (if i = j' then (1 : ZMod p) else 0) -
              (if i.val + 1 = j'.val then 1 else 0) :=
          ih (m - 1 - j'.val) (by simp [j']; omega) j' rfl
        have hrec : α i (e j) = ((CartanMatrix.B m i j : ℤ) : ZMod p) + α i (e j') := by
          rw [he_succ j hlt, map_add, hP i j]
        rw [hrec, hih]
        have hstep := cartanB_step_zmod (p := p) (m := m) (i := i) (j := j) hlt
        rw [hstep]
        simp only [j']
        abel
  have hdual : GGCZDual e φ := by
    intro i j
    have hφsum : φ i (e j) = ∑ l ∈ Finset.Ici i, α l (e j) := by
      simp only [φ, LinearMap.sum_apply]
    rw [hφsum]
    have hterm : ∀ l ∈ Finset.Ici i, α l (e j) =
        (if l = j then (1 : ZMod p) else 0) -
          (if l.val + 1 = j.val then 1 else 0) := fun l _ => hαe l j
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    have hsum1 : (∑ l ∈ Finset.Ici i, (if l = j then (1 : ZMod p) else 0)) =
        if i ≤ j then 1 else 0 := by
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_Ici]
    have hsum2 : (∑ l ∈ Finset.Ici i, (if l.val + 1 = j.val then (1 : ZMod p) else 0)) =
        if i.val < j.val then 1 else 0 := by
      by_cases hj0 : j.val = 0
      · have hzero : ∀ l : Fin m, ¬ l.val + 1 = j.val := by
          intro l
          omega
        simp [hj0]
      · let pj : Fin m := ⟨j.val - 1, by omega⟩
        have hiff : ∀ l : Fin m, (l.val + 1 = j.val) ↔ l = pj := by
          intro l
          constructor
          · intro h
            apply Fin.ext
            simp [pj]
            omega
          · rintro rfl
            simp [pj]
            omega
        have hcongr : (∑ l ∈ Finset.Ici i,
              (if l.val + 1 = j.val then (1 : ZMod p) else 0)) =
            ∑ l ∈ Finset.Ici i, (if l = pj then (1 : ZMod p) else 0) := by
          apply Finset.sum_congr rfl
          intro l _
          by_cases hl : l.val + 1 = j.val
          · have hl' : l = pj := (hiff l).mp hl
            have hpj : pj.val + 1 = j.val := by
              simp [pj]
              omega
            simp [hl', hpj]
          · have hl' : l ≠ pj := fun h => hl ((hiff l).mpr h)
            simp [hl, hl']
        rw [hcongr, Finset.sum_ite_eq']
        have hmem : pj ∈ Finset.Ici i ↔ i.val < j.val := by
          constructor
          · intro hh
            have hh' : i.val ≤ pj.val := by
              simpa only [Finset.mem_Ici, Fin.le_def] using hh
            have hpj : pj.val = j.val - 1 := rfl
            omega
          · intro hh
            have hh' : i.val ≤ pj.val := by
              have hpj : pj.val = j.val - 1 := rfl
              omega
            rw [Finset.mem_Ici, Fin.le_def]
            exact hh'
        by_cases hjt : i.val < j.val
        · have hm : pj ∈ Finset.Ici i := hmem.mpr hjt
          rw [if_pos hm, if_pos hjt]
        · have hm : pj ∉ Finset.Ici i := fun hh => hjt (hmem.mp hh)
          rw [if_neg hm, if_neg hjt]
    rw [hsum1, hsum2]
    by_cases hlt : i.val < j.val
    · have hle : i ≤ j := Fin.le_def.mpr (le_of_lt hlt)
      have hne : i ≠ j := by
        intro h
        subst h
        omega
      simp [hlt, hle, hne]
    · by_cases heq : i = j
      · subst heq
        simp
      · have hle : ¬ i ≤ j := by
          simp only [Fin.le_def]
          omega
        simp [hlt, hle, heq]
  let img : Fin m → (V ≃ₗ[ZMod p] V) := fun i =>
    ggLin (p := p) ιV ((f ((CoxeterMatrix.B m).simple i) : ↥A) : MulAut ↥Bs)
  have hgen_left : ∀ i (hi : i.val + 1 < m) (v : V),
      img i v = v - (φ i v - φ (⟨i.val + 1, hi⟩ : Fin m) v) •
        (e i - e (⟨i.val + 1, hi⟩ : Fin m)) := by
    intro i hi v
    dsimp only [img]
    rw [hrefl i, Module.reflection_apply, hα_succ i hi, hh_succ i hi]
    simp only [LinearMap.sub_apply]
  have hgen_right : ∀ i (hi : i.val + 1 = m) (v : V),
      img i v = v - (2 * φ i v) • e i := by
    intro i hi v
    have hilast : i = last := Fin.ext (by simp [last]; omega)
    dsimp only [img]
    rw [hrefl i, Module.reflection_apply, hilast, hφ_last, ← he_last]
    rw [smul_smul, mul_comm]
  have hgen : ∀ i, GGCZGensB e φ (img i) := by
    intro i
    by_cases hi : i.val + 1 < m
    · exact Or.inl ⟨i, ⟨i.val + 1, hi⟩, rfl, hgen_left i hi⟩
    · have hi' : i.val + 1 = m := by omega
      exact Or.inr ⟨i, hi', hgen_right i hi'⟩
  have hset : {r : V ≃ₗ[ZMod p] V | GGCZGensB e φ r} = Set.range img := by
    ext r
    constructor
    · rintro (⟨i, j, hij, hr⟩ | ⟨i, hi, hr⟩)
      · have hi' : i.val + 1 < m := by omega
        have hjeq : j = ⟨i.val + 1, hi'⟩ := Fin.ext (by simpa using hij.symm)
        subst hjeq
        refine ⟨i, ?_⟩
        ext v
        rw [hr v, hgen_left i hi' v]
      · refine ⟨i, ?_⟩
        ext v
        rw [hr v, hgen_right i hi v]
    · rintro ⟨i, rfl⟩
      exact hgen i
  have hmap : Subgroup.map (ggLin (p := p) ιV) A = Subgroup.closure (Set.range img) := by
    have hrangeA : ((Subgroup.subtype A).comp f.toMonoidHom).range = A := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 f.surjective, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [← hrangeA, ← MonoidHom.range_comp]
    rw [MonoidHom.range_eq_map,
      ← (CoxeterMatrix.B m).toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  refine ⟨e, φ, hdual, ?_⟩
  rw [hmap, ggCZWB, hset]

theorem ggCZ_coordsF4 (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs) {A : Subgroup (MulAut ↥Bs)}
    (hA : A ≤ ggInduced ⊤ Bs) (f : CoxeterMatrix.F₄.Group ≃* ↥A)
    (hf : ∀ i, GGIsReflection p ((f (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs))
    (ιV : Additive ↥Bs ≃+ V) :
    ∃ (e : Fin 4 → V) (φ : Fin 4 → Module.Dual (ZMod p) V), GGCZDual e φ ∧
      (∀ i, GGCZGensF4 e φ i
        (ggLin (p := p) ιV ((f (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs))) ∧
      Subgroup.map (ggLin (p := p) ιV) A = ggCZWF4 p e φ := by
  classical
  have hind : ∀ φ ∈ A, φ ∈ ggInduced ⊤ Bs := fun φ hφ => hA hφ
  obtain ⟨h, α, hα, hrefl, hP⟩ :=
    SecFiveRootRefl.exists_cartan_pairing_of_iso (p := p) hp2 hNT
      (ggIntCartan_F₄) (SecFiveRootRefl.entries_F₄) (SecFiveRootRefl.cartanTree_F₄)
      f hf hind ιV
  let c : ZMod p := (2 : ZMod p)⁻¹
  let e3 : V := c • h 2
  let e2 : V := h 1 + e3
  let e1 : V := h 0 + e2
  let e0 : V := h 3 + e1 + e2 + e3
  let e : Fin 4 → V := ![e0, e1, e2, e3]
  let p3 : Module.Dual (ZMod p) V := α 2
  let p2 : Module.Dual (ZMod p) V := α 1 + p3
  let p1 : Module.Dual (ZMod p) V := α 0 + p2
  let p0 : Module.Dual (ZMod p) V := (2 : ZMod p) • α 3 + p1 + p2 + p3
  let φ : Fin 4 → Module.Dual (ZMod p) V := ![p0, p1, p2, p3]
  have hc2 : (2 : ZMod p) * c = 1 := by
    simp only [c]
    exact mul_inv_cancel₀ (zmod_two_ne_zero hp2)
  have hdual : GGCZDual e φ := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e, φ, e0, e1, e2, e3, p0, p1, p2, p3, c, CartanMatrix.F₄,
        map_add, map_smul, hP] <;>
      try field_simp [zmod_two_ne_zero hp2] <;> ring
  have he12 : e 1 - e 2 = h 0 := by
    simp [e, e1, e2, e3]
  have he23 : e 2 - e 3 = h 1 := by
    simp [e, e2, e3]
  have he0 : e 0 - e 1 - e 2 - e 3 = h 3 := by
    simp [e, e0, e1, e2, e3]
    abel
  have he3 : (2 : ZMod p) • e 3 = h 2 := by
    change (2 : ZMod p) • e3 = h 2
    simp only [e3, smul_smul, hc2, one_smul]
  have hφ10 : ∀ v : V, φ 1 v - φ 2 v = α 0 v := by
    intro v
    simp [φ, p1, p2, p3]
  have hφ21 : ∀ v : V, φ 2 v - φ 3 v = α 1 v := by
    intro v
    simp [φ, p1, p2, p3]
  have hφ3 : ∀ v : V, φ 3 v = α 2 v := by
    intro v
    simp [φ, p3]
  have hφsum : ∀ v : V,
      c * (φ 0 v - φ 1 v - φ 2 v - φ 3 v) = α 3 v := by
    intro v
    have hsum : φ 0 v - φ 1 v - φ 2 v - φ 3 v = (2 : ZMod p) * α 3 v := by
      simp [φ, p0, p1, p2, p3]
      ring
    have hc2' : c * 2 = 1 := by rw [mul_comm, hc2]
    rw [hsum, ← mul_assoc, hc2', one_mul]
  let img : Fin 4 → (V ≃ₗ[ZMod p] V) := fun i =>
    ggLin (p := p) ιV ((f (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs)
  have hgen : ∀ i, GGCZGensF4 e φ i (img i) := by
    intro i
    dsimp only [img]
    have hri := hrefl i
    fin_cases i
    · intro v
      rw [hri, Module.reflection_apply]
      change v - α (0 : Fin 4) v • h (0 : Fin 4) =
        v - (φ 1 v - φ 2 v) • (e 1 - e 2)
      rw [hφ10 v, he12]
    · intro v
      rw [hri, Module.reflection_apply]
      change v - α (1 : Fin 4) v • h (1 : Fin 4) =
        v - (φ 2 v - φ 3 v) • (e 2 - e 3)
      rw [hφ21 v, he23]
    · intro v
      rw [hri, Module.reflection_apply]
      change v - α (2 : Fin 4) v • h (2 : Fin 4) =
        v - (2 * φ 3 v) • e 3
      rw [hφ3 v]
      rw [show α 2 v • h 2 = (2 * α 2 v) • e 3 from by
        rw [← he3, smul_smul]
        congr 1
        ring]
    · intro v
      rw [hri, Module.reflection_apply]
      change v - α (3 : Fin 4) v • h (3 : Fin 4) =
        v - (2⁻¹ * (φ 0 v - φ 1 v - φ 2 v - φ 3 v)) • (e 0 - e 1 - e 2 - e 3)
      rw [he0, hφsum v]
  have hset : {r : V ≃ₗ[ZMod p] V | ∃ i, GGCZGensF4 e φ i r} = Set.range img := by
    ext r
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hgi := hgen i
      ext v
      fin_cases i <;> simp only [GGCZGensF4] at hi hgi ⊢ <;> rw [hi, hgi]
    · rintro ⟨i, rfl⟩
      exact ⟨i, hgen i⟩
  have hmap : Subgroup.map (ggLin (p := p) ιV) A = Subgroup.closure (Set.range img) := by
    have hrangeA : ((Subgroup.subtype A).comp f.toMonoidHom).range = A := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 f.surjective, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [← hrangeA, ← MonoidHom.range_comp]
    rw [MonoidHom.range_eq_map,
      ← CoxeterMatrix.F₄.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  refine ⟨e, φ, hdual, hgen, ?_⟩
  rw [hmap, ggCZWF4, hset]

end

end CFSG.StandardType

end
