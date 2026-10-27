module

public import CFSG.LocalAnalysis.StandardType.GGRCAbsIrred
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section RootSpan7

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggRS7_pair_symm (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hA : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ v, g (g v - v) = g v - v))
    (s t : V ≃ₗ[ZMod 3] V) (hs : s ∈ A) (ht : t ∈ A) (h k : V) (a b : Module.Dual (ZMod 3) V)
    (hsv : ∀ v, s v = v - a v • h) (htv : ∀ v, t v = v - b v • k) (ha : a h = 2) (hb : b k = 2)
    (hak : a k = 0) : b h = 0 := by
  by_contra hbh
  have h2ne : (2 : ZMod 3) ≠ 0 := by decide
  have hk : k ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hb
    exact h2ne hb.symm
  set g : V ≃ₗ[ZMod 3] V := t * s * t * s with hgdef
  have hmem : g ∈ A := by
    rw [hgdef]
    exact A.mul_mem (A.mul_mem (A.mul_mem ht hs) ht) hs
  have hgv : ∀ v, g v = v - (b h * a v) • k := by
    intro v
    rw [hgdef]
    simp only [LinearEquiv.mul_apply]
    have e1 : s v = v - a v • h := hsv v
    have e2 : t (s v) = s v - b (s v) • k := htv (s v)
    have e3 : s (t (s v)) = t (s v) - a (t (s v)) • h := hsv (t (s v))
    have e4 : t (s (t (s v))) = s (t (s v)) - b (s (t (s v))) • k :=
      htv (s (t (s v)))
    rw [e4, e3, e2, e1]
    simp only [map_sub, map_smul, ha, hb, hak, mul_zero, zero_smul, sub_zero, sub_self,
      neg_zero, mul_neg, neg_neg]
    module
  have hker_a : ∀ v, a (g v - v) = 0 := by
    intro v
    have hsub : g v - v = -(b h * a v) • k := by
      rw [hgv v]
      module
    rw [hsub, map_smul, hak, smul_zero]
  have hsq : ∀ v, g (g v - v) = g v - v := by
    intro v
    rw [hgv (g v - v), hker_a v, mul_zero, zero_smul, sub_zero]
  have hrange : ggLinMove g = Submodule.span (ZMod 3) {k} := by
    rw [ggLinMove]
    apply le_antisymm
    · rintro x ⟨v, rfl⟩
      change g v - v ∈ Submodule.span (ZMod 3) {k}
      have hsub : g v - v = -(b h * a v) • k := by
        rw [hgv v]
        module
      rw [hsub]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton k))
    · rw [Submodule.span_le]
      rintro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      refine ⟨-((2 * b h)⁻¹) • h, ?_⟩
      change g (-((2 * b h)⁻¹) • h) - (-((2 * b h)⁻¹) • h) = k
      rw [hgv]
      have hscal : b h * a (-((2 * b h)⁻¹) • h) = -1 := by
        rw [map_smul, ha, smul_eq_mul]
        have hne : (2 : ZMod 3) * b h ≠ 0 := mul_ne_zero (by decide) hbh
        calc b h * (-((2 * b h)⁻¹) * 2)
            = -(b h * ((2 * b h)⁻¹ * 2)) := by ring
          _ = -((2 * b h) * (2 * b h)⁻¹) := by ring
          _ = -1 := by rw [mul_inv_cancel₀ hne]
      rw [hscal]
      module
  have hfr : Module.finrank (ZMod 3) (ggLinMove g) = 1 := by
    rw [hrange, finrank_span_singleton hk]
  exact hA g hmem ⟨hfr, hsq⟩

theorem ggRS7_indepD {hD : Fin 6 → V} {aD : Fin 6 → Module.Dual (ZMod 3) V}
    (pairD : ∀ i j, aD i (hD j) = (CartanMatrix.D 6 i j : ZMod 3)) :
    LinearIndependent (ZMod 3) hD := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ c : Fin 6 → ZMod 3,
      (∀ i, ∑ j, c j * (CartanMatrix.D 6 i j : ZMod 3) = 0) → ∀ j, c j = 0 := by
    decide +kernel
  exact key c (fun i => by
    have h := congrArg (aD i) hc
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
    simpa only [pairD] using h)

theorem ggRS7_cross_ne {hE : Fin 6 → V} {aD aE : Fin 6 → Module.Dual (ZMod 3) V} (x : V)
    (pairE : ∀ i j, aE i (hE j) = (CartanMatrix.E₆ i j : ZMod 3))
    (fixD : ∀ v, (∀ i, aD i v = 0) → v ∈ Submodule.span (ZMod 3) {x}) :
    ∃ i j, aD i (hE j) ≠ 0 := by
  by_contra h
  push Not at h
  choose c hc using fun j =>
    Submodule.mem_span_singleton.mp (fixD (hE j) (fun i => h i j))
  have hc' : ∀ j, hE j = c j • x := fun j => (hc j).symm
  have hu : ∀ i j, aE i (hE j) = c j * aE i x := by
    intro i j
    rw [hc' j, map_smul, smul_eq_mul]
  have h00 : c 0 * aE 0 x = 2 := by
    rw [← hu 0 0, pairE 0 0, CartanMatrix.E₆, CartanMatrix.E_diag]
    norm_num
  have h11 : c 1 * aE 1 x = 2 := by
    rw [← hu 1 1, pairE 1 1, CartanMatrix.E₆, CartanMatrix.E_diag]
    norm_num
  have h01 : c 1 * aE 0 x = 0 := by
    rw [← hu 0 1, pairE 0 1, CartanMatrix.E₆]
    decide +kernel
  have h10 : c 0 * aE 1 x = 0 := by
    rw [← hu 1 0, pairE 1 0, CartanMatrix.E₆]
    decide +kernel
  have hcon : (2 : ZMod 3) * 2 = 0 := by
    calc (2 : ZMod 3) * 2
        = (c 0 * aE 0 x) * (c 1 * aE 1 x) := by rw [h00, h11]
      _ = (c 1 * aE 0 x) * (c 0 * aE 1 x) := by ring
      _ = 0 := by rw [h01, h10, mul_zero]
  exact (by decide : (2 : ZMod 3) * 2 ≠ 0) hcon

private lemma lr6rs_reflTransGen_symm {α : Type*} {r : α → α → Prop}
    (hsymm : ∀ a b, r a b → r b a) :
    ∀ {a b}, Relation.ReflTransGen r a b → Relation.ReflTransGen r b a := by
  intro a b h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (hsymm _ _ hbc) ih

theorem ggRS7_connected (A : Subgroup (V ≃ₗ[ZMod 3] V))
    (hA : ∀ g ∈ A, ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ v, g (g v - v) = g v - v))
    {hD hE : Fin 6 → V} {aD aE : Fin 6 → Module.Dual (ZMod 3) V}
    (rD rE : Fin 6 → V ≃ₗ[ZMod 3] V) (x : V)
    (rDA : ∀ i, rD i ∈ A) (rEA : ∀ i, rE i ∈ A)
    (pairD : ∀ i j, aD i (hD j) = (CartanMatrix.D 6 i j : ZMod 3))
    (pairE : ∀ i j, aE i (hE j) = (CartanMatrix.E₆ i j : ZMod 3))
    (hrD : ∀ i v, rD i v = v - aD i v • hD i) (hrE : ∀ i v, rE i v = v - aE i v • hE i)
    (fixD : ∀ v, (∀ i, aD i v = 0) → v ∈ Submodule.span (ZMod 3) {x}) :
    ∀ a b : Fin 6 ⊕ Fin 6,
      Relation.ReflTransGen
        (fun a b => Sum.elim aD aE a (Sum.elim hD hE b) ≠ 0 ∧
          Sum.elim aD aE b (Sum.elim hD hE a) ≠ 0) a b := by
  let R := fun a b : Fin 6 ⊕ Fin 6 =>
    Sum.elim aD aE a (Sum.elim hD hE b) ≠ 0 ∧
      Sum.elim aD aE b (Sum.elim hD hE a) ≠ 0
  have hdd : ∀ i j, (CartanMatrix.D 6 i j : ZMod 3) ≠ 0 →
      (CartanMatrix.D 6 j i : ZMod 3) ≠ 0 → R (Sum.inl i) (Sum.inl j) := by
    intro i j hij hji
    dsimp only [R]
    simp only [Sum.elim_inl]
    exact ⟨by simpa [pairD i j] using hij, by simpa [pairD j i] using hji⟩
  have hee : ∀ i j, (CartanMatrix.E 6 i j : ZMod 3) ≠ 0 →
      (CartanMatrix.E 6 j i : ZMod 3) ≠ 0 → R (Sum.inr i) (Sum.inr j) := by
    intro i j hij hji
    dsimp only [R]
    simp only [Sum.elim_inr]
    exact ⟨by rw [pairE i j, CartanMatrix.E₆]; exact hij,
      by rw [pairE j i, CartanMatrix.E₆]; exact hji⟩
  have h01 : R (Sum.inl 0) (Sum.inl 1) := hdd 0 1 (by decide +kernel) (by decide +kernel)
  have h12 : R (Sum.inl 1) (Sum.inl 2) := hdd 1 2 (by decide +kernel) (by decide +kernel)
  have h23 : R (Sum.inl 2) (Sum.inl 3) := hdd 2 3 (by decide +kernel) (by decide +kernel)
  have h34 : R (Sum.inl 3) (Sum.inl 4) := hdd 3 4 (by decide +kernel) (by decide +kernel)
  have h35 : R (Sum.inl 3) (Sum.inl 5) := hdd 3 5 (by decide +kernel) (by decide +kernel)
  have e02 : R (Sum.inr 0) (Sum.inr 2) := hee 0 2 (by decide +kernel) (by decide +kernel)
  have e23 : R (Sum.inr 2) (Sum.inr 3) := hee 2 3 (by decide +kernel) (by decide +kernel)
  have e31 : R (Sum.inr 3) (Sum.inr 1) := hee 3 1 (by decide +kernel) (by decide +kernel)
  have e34 : R (Sum.inr 3) (Sum.inr 4) := hee 3 4 (by decide +kernel) (by decide +kernel)
  have e45 : R (Sum.inr 4) (Sum.inr 5) := hee 4 5 (by decide +kernel) (by decide +kernel)
  have p0 : Relation.ReflTransGen R (Sum.inl 0) (Sum.inl 0) := Relation.ReflTransGen.refl
  have p1 : Relation.ReflTransGen R (Sum.inl 0) (Sum.inl 1) := Relation.ReflTransGen.single h01
  have p2 : Relation.ReflTransGen R (Sum.inl 0) (Sum.inl 2) := p1.tail h12
  have p3 : Relation.ReflTransGen R (Sum.inl 0) (Sum.inl 3) := p2.tail h23
  have p4 : Relation.ReflTransGen R (Sum.inl 0) (Sum.inl 4) := p3.tail h34
  have p5 : Relation.ReflTransGen R (Sum.inl 0) (Sum.inl 5) := p3.tail h35
  have dconn : ∀ i, Relation.ReflTransGen R (Sum.inl 0) (Sum.inl i) := by
    intro i
    fin_cases i
    exacts [p0, p1, p2, p3, p4, p5]
  have q0 : Relation.ReflTransGen R (Sum.inr 0) (Sum.inr 0) := Relation.ReflTransGen.refl
  have q2 : Relation.ReflTransGen R (Sum.inr 0) (Sum.inr 2) := Relation.ReflTransGen.single e02
  have q3 : Relation.ReflTransGen R (Sum.inr 0) (Sum.inr 3) := q2.tail e23
  have q1 : Relation.ReflTransGen R (Sum.inr 0) (Sum.inr 1) := q3.tail e31
  have q4 : Relation.ReflTransGen R (Sum.inr 0) (Sum.inr 4) := q3.tail e34
  have q5 : Relation.ReflTransGen R (Sum.inr 0) (Sum.inr 5) := q4.tail e45
  have econn : ∀ j, Relation.ReflTransGen R (Sum.inr 0) (Sum.inr j) := by
    intro j
    fin_cases j
    exacts [q0, q1, q2, q3, q4, q5]
  obtain ⟨i, j, hi⟩ := ggRS7_cross_ne x pairE fixD
  have hji : aE j (hD i) ≠ 0 := by
    intro hzero
    have hb : aD i (hD i) = 2 := by
      rw [pairD i i, CartanMatrix.D_diag]
      norm_num
    have ha : aE j (hE j) = 2 := by
      rw [pairE j j, CartanMatrix.E₆, CartanMatrix.E_diag]
      norm_num
    exact hi (ggRS7_pair_symm A hA (rE j) (rD i) (rEA j) (rDA i) (hE j) (hD i)
      (aE j) (aD i) (hrE j) (hrD i) ha hb hzero)
  have hcross : R (Sum.inl i) (Sum.inr j) := by
    dsimp only [R]
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact ⟨hi, hji⟩
  have rev : ∀ {a b : Fin 6 ⊕ Fin 6}, Relation.ReflTransGen R a b →
      Relation.ReflTransGen R b a :=
    lr6rs_reflTransGen_symm (r := R) (fun _ _ h => ⟨h.2, h.1⟩)
  have base : Relation.ReflTransGen R (Sum.inl 0) (Sum.inr 0) :=
    (dconn i).trans ((Relation.ReflTransGen.single hcross).trans (rev (econn j)))
  have toBase : ∀ a, Relation.ReflTransGen R a (Sum.inl 0) := by
    intro a
    cases a with
    | inl i' => exact rev (dconn i')
    | inr j' => exact (rev (econn j')).trans (rev base)
  have fromBase : ∀ b, Relation.ReflTransGen R (Sum.inl 0) b := by
    intro b
    cases b with
    | inl i' => exact dconn i'
    | inr j' => exact base.trans (econn j')
  intro a b
  exact (toBase a).trans (fromBase b)

theorem ggRS7_fixA {hD hE : Fin 6 → V} {aD aE : Fin 6 → Module.Dual (ZMod 3) V}
    (rD rE : Fin 6 → V ≃ₗ[ZMod 3] V) (x : V)
    (pairD : ∀ i j, aD i (hD j) = (CartanMatrix.D 6 i j : ZMod 3))
    (hrD : ∀ i v, rD i v = v - aD i v • hD i) (hrE : ∀ i v, rE i v = v - aE i v • hE i)
    (fixD : ∀ v, (∀ i, aD i v = 0) → v ∈ Submodule.span (ZMod 3) {x})
    (moves : ∃ i, rE i x ≠ x) :
    ∀ v : V, (∀ g ∈ Subgroup.closure (Set.range rD ∪ Set.range rE), g v = v) → v = 0 := by
  intro v hv
  have hDmem : ∀ i, rD i ∈ Subgroup.closure (Set.range rD ∪ Set.range rE) := fun i =>
    Subgroup.subset_closure (Or.inl (Set.mem_range_self i))
  have hEmem : ∀ i, rE i ∈ Subgroup.closure (Set.range rD ∪ Set.range rE) := fun i =>
    Subgroup.subset_closure (Or.inr (Set.mem_range_self i))
  have haDv : ∀ i, aD i v = 0 := by
    intro i
    have hfix := hv (rD i) (hDmem i)
    rw [hrD i v] at hfix
    have hzero : aD i v • hD i = 0 := sub_eq_self.mp hfix
    have hhD : hD i ≠ 0 := by
      intro h0
      have hpi := pairD i i
      rw [h0, map_zero, CartanMatrix.D_diag] at hpi
      exact (by decide : (0 : ZMod 3) ≠ 2) hpi
    exact (smul_eq_zero.mp hzero).resolve_right hhD
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (fixD v haDv)
  have hvx : v = c • x := hc.symm
  by_cases hc0 : c = 0
  · rw [hvx, hc0, zero_smul]
  · obtain ⟨i0, hi0⟩ := moves
    have hfixE := hv (rE i0) (hEmem i0)
    rw [hrE i0 v, hvx] at hfixE
    have hzero : aE i0 (c • x) • hE i0 = 0 := sub_eq_self.mp hfixE
    rw [map_smul, smul_eq_mul, mul_smul] at hzero
    have hx0 : aE i0 x • hE i0 = 0 := (smul_eq_zero.mp hzero).resolve_left hc0
    have : rE i0 x = x := by rw [hrE i0 x, hx0, sub_zero]
    exact absurd this hi0

theorem ggRS7_w0 {hD : Fin 6 → V} {aD : Fin 6 → Module.Dual (ZMod 3) V}
    (rD : Fin 6 → V ≃ₗ[ZMod 3] V)
    (pairD : ∀ i j, aD i (hD j) = (CartanMatrix.D 6 i j : ZMod 3))
    (hrD : ∀ i v, rD i v = v - aD i v • hD i) :
    ∀ j, ((rD 0 * rD 1 * rD 2 * rD 3 * rD 4 * rD 5) ^ 5) (hD j) = - hD j := by
  let T6 : (Fin 6 → ZMod 3) →ₗ[ZMod 3] V :=
    { toFun := fun c => ∑ j, c j • hD j
      map_add' := by
        intro c d
        simp [Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro a c
        simp [Finset.smul_sum, smul_smul] }
  let E : Fin 6 → Matrix (Fin 6) (Fin 6) (ZMod 3) := fun i =>
    Matrix.of fun k j => if k = i then (CartanMatrix.D 6 i j : ZMod 3) else 0
  let Rm : Fin 6 → Matrix (Fin 6) (Fin 6) (ZMod 3) := fun i => 1 - E i
  have hEvec : ∀ i c k, ((E i).mulVec c) k =
      if k = i then ∑ j, (CartanMatrix.D 6 i j : ZMod 3) * c j else 0 := by
    intro i c k
    simp only [E, Matrix.mulVec, Matrix.of_apply]
    by_cases hk : k = i <;> simp [hk, dotProduct]
  have hT6E : ∀ i c, T6 ((E i).mulVec c) =
      (∑ j, (CartanMatrix.D 6 i j : ZMod 3) * c j) • hD i := by
    intro i c
    change (∑ k, ((E i).mulVec c) k • hD k) = _
    rw [Finset.sum_eq_single i
      (fun k _ hk => by rw [hEvec i c k, if_neg hk, zero_smul])
      (fun hi => absurd (Finset.mem_univ i) hi)]
    rw [hEvec i c i, if_pos rfl]
  have hRmvec : ∀ i c, (Rm i).mulVec c = c - (E i).mulVec c := by
    intro i c
    simp only [Rm, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hT6 : ∀ i c, rD i (T6 c) = T6 ((Rm i).mulVec c) := by
    intro i c
    have hL : rD i (T6 c) =
        T6 c - (∑ j, (CartanMatrix.D 6 i j : ZMod 3) * c j) • hD i := by
      change rD i (∑ j, c j • hD j) =
        (∑ j, c j • hD j) - (∑ j, (CartanMatrix.D 6 i j : ZMod 3) * c j) • hD i
      rw [map_sum]
      have hterm : ∀ j, rD i (c j • hD j) =
          c j • hD j - (c j * (CartanMatrix.D 6 i j : ZMod 3)) • hD i := by
        intro j
        rw [map_smul, hrD i (hD j), pairD i j]
        module
      rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
        ← Finset.sum_smul]
      have hscalar : ∑ j, c j * (CartanMatrix.D 6 i j : ZMod 3) =
          ∑ j, (CartanMatrix.D 6 i j : ZMod 3) * c j :=
        Finset.sum_congr rfl (fun j _ => by rw [mul_comm])
      rw [hscalar]
    rw [hRmvec i c, map_sub, hT6E i c]
    exact hL
  have hprod : ∀ c, (rD 0 * rD 1 * rD 2 * rD 3 * rD 4 * rD 5) (T6 c) =
      T6 ((Rm 0 * Rm 1 * Rm 2 * Rm 3 * Rm 4 * Rm 5).mulVec c) := by
    intro c
    simp only [LinearEquiv.mul_apply]
    rw [hT6 5 c, hT6 4, hT6 3, hT6 2, hT6 1, hT6 0]
    simp only [Matrix.mulVec_mulVec, mul_assoc]
  have hpow : ∀ n c, ((rD 0 * rD 1 * rD 2 * rD 3 * rD 4 * rD 5) ^ n) (T6 c) =
      T6 (((Rm 0 * Rm 1 * Rm 2 * Rm 3 * Rm 4 * Rm 5) ^ n).mulVec c) := by
    intro n
    induction n with
    | zero => intro c; simp
    | succ n ih =>
        intro c
        rw [pow_succ, LinearEquiv.mul_apply, hprod, ih, pow_succ, Matrix.mulVec_mulVec]
  have hmat : (Rm 0 * Rm 1 * Rm 2 * Rm 3 * Rm 4 * Rm 5) ^ 5 = -1 := by
    decide +kernel
  intro j
  let ej : Fin 6 → ZMod 3 := Pi.single j (1 : ZMod 3)
  have hsingle : T6 ej = hD j := by
    change (∑ k, ej k • hD k) = hD j
    rw [Finset.sum_eq_single j
      (fun k _ hk => by simp [ej, Pi.single_eq_of_ne hk])
      (fun hj => absurd (Finset.mem_univ j) hj)]
    simp [ej]
  calc ((rD 0 * rD 1 * rD 2 * rD 3 * rD 4 * rD 5) ^ 5) (hD j)
      = ((rD 0 * rD 1 * rD 2 * rD 3 * rD 4 * rD 5) ^ 5) (T6 ej) := by
        rw [hsingle]
    _ = T6 (((Rm 0 * Rm 1 * Rm 2 * Rm 3 * Rm 4 * Rm 5) ^ 5).mulVec ej) :=
        hpow 5 ej
    _ = T6 ((-1 : Matrix (Fin 6) (Fin 6) (ZMod 3)).mulVec ej) := by rw [hmat]
    _ = T6 (-ej) := by rw [Matrix.neg_mulVec, Matrix.one_mulVec]
    _ = - T6 ej := by rw [map_neg]
    _ = - hD j := by rw [hsingle]

theorem ggRS7_span_top (hdim : Module.finrank (ZMod 3) V = 7)
    {hD hE : Fin 6 → V} {aD aE : Fin 6 → Module.Dual (ZMod 3) V}
    (rD rE : Fin 6 → V ≃ₗ[ZMod 3] V) (x : V)
    (pairD : ∀ i j, aD i (hD j) = (CartanMatrix.D 6 i j : ZMod 3))
    (pairE : ∀ i j, aE i (hE j) = (CartanMatrix.E₆ i j : ZMod 3))
    (hrD : ∀ i v, rD i v = v - aD i v • hD i) (hrE : ∀ i v, rE i v = v - aE i v • hE i)
    (hx : x ≠ 0) (hxD : ∀ i, aD i x = 0)
    (fixD : ∀ v, (∀ i, aD i v = 0) → v ∈ Submodule.span (ZMod 3) {x})
    (moves : ∃ i, rE i x ≠ x)
    (hA : ∀ g ∈ Subgroup.closure (Set.range rD ∪ Set.range rE),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ v, g (g v - v) = g v - v)) :
    Submodule.span (ZMod 3) (Set.range hD ∪ Set.range hE) = ⊤ := by
  haveI : FiniteDimensional (ZMod 3) V :=
    FiniteDimensional.of_finrank_pos (by rw [hdim]; decide)
  let A : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range rD ∪ Set.range rE)
  let T : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range hD ∪ Set.range hE)
  let R : Submodule (ZMod 3) V := Submodule.span (ZMod 3) (Set.range hD)
  change T = ⊤
  have hmemD : ∀ i, rD i ∈ A := fun i =>
    Subgroup.subset_closure (Or.inl (Set.mem_range_self i))
  have hmemE : ∀ i, rE i ∈ A := fun i =>
    Subgroup.subset_closure (Or.inr (Set.mem_range_self i))
  have hgen : ∀ g ∈ Set.range rD ∪ Set.range rE, ∀ v, g v - v ∈ T := by
    rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩) v
    · have hhi : hD i ∈ T := Submodule.subset_span (Or.inl (Set.mem_range_self i))
      have hsub : rD i v - v = -(aD i v) • hD i := by rw [hrD i v]; module
      rw [hsub]
      exact T.smul_mem _ hhi
    · have hhi : hE i ∈ T := Submodule.subset_span (Or.inr (Set.mem_range_self i))
      have hsub : rE i v - v = -(aE i v) • hE i := by rw [hrE i v]; module
      rw [hsub]
      exact T.smul_mem _ hhi
  have hT_stable : ∀ g ∈ A, ∀ v, g v - v ∈ T := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ v, g v - v ∈ T)
      (fun x hx v => hgen x hx v) (fun v => by simp) ?_ ?_ hg
    · intro x y hx hy ihx ihy v
      have hsub : (x * y) v - v = (x (y v) - y v) + (y v - v) := by
        rw [LinearEquiv.mul_apply]; module
      rw [hsub]
      exact T.add_mem (ihx (y v)) (ihy v)
    · intro x hx ihx v
      have hsub : x⁻¹ v - v = -(x (x⁻¹ v) - x⁻¹ v) := by
        change x.symm v - v = -(x (x.symm v) - x.symm v)
        rw [LinearEquiv.apply_symm_apply]
        module
      rw [hsub]
      exact T.neg_mem (ihx (x⁻¹ v))
  have hT_stable' : ∀ g ∈ A, ∀ v ∈ T, g v ∈ T := by
    intro g hg v hv
    have h1 := hT_stable g hg v
    have h2 : g v = v + (g v - v) := by abel
    rw [h2]
    exact T.add_mem hv h1
  have hfixA : ∀ v, (∀ g ∈ A, g v = v) → v = 0 :=
    ggRS7_fixA rD rE x pairD hrD hrE fixD moves
  have hind : LinearIndependent (ZMod 3) hD := ggRS7_indepD pairD
  have hRdim : Module.finrank (ZMod 3) R = 6 := by
    change Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (Set.range hD)) = 6
    rw [finrank_span_eq_card hind]
    simp
  have hRT : R ≤ T := Submodule.span_mono Set.subset_union_left
  by_contra hTne
  have hTlt : Module.finrank (ZMod 3) T < Module.finrank (ZMod 3) V :=
    Submodule.finrank_lt hTne
  have hTdim : Module.finrank (ZMod 3) T = 6 := by
    have hle := Submodule.finrank_mono hRT
    rw [hRdim] at hle
    rw [hdim] at hTlt
    omega
  have hTR : T = R := (Submodule.eq_of_le_of_finrank_eq hRT (by rw [hTdim, hRdim])).symm
  have hinj : ∀ g ∈ A, (∀ v ∈ T, g v = v) → g = 1 := by
    intro g hg hfix
    by_contra hg1
    let φ : V →ₗ[ZMod 3] V := g.toLinearMap - LinearMap.id
    have hφ : ∀ v, φ v = g v - v := fun v => by simp [φ, LinearMap.sub_apply]
    have hker : T ≤ LinearMap.ker φ := by
      intro v hv
      rw [LinearMap.mem_ker, hφ, sub_eq_zero]
      exact hfix v hv
    have hkerle := Submodule.finrank_mono hker
    have hrn := LinearMap.finrank_range_add_finrank_ker φ
    have hrange_le : Module.finrank (ZMod 3) (LinearMap.range φ) ≤ 1 := by
      rw [hTdim] at hkerle
      omega
    have hrange_ne : LinearMap.range φ ≠ ⊥ := by
      intro hbot
      apply hg1
      ext v
      have hv : φ v ∈ LinearMap.range φ := ⟨v, rfl⟩
      rw [hbot, Submodule.mem_bot] at hv
      rw [hφ, sub_eq_zero] at hv
      exact hv
    have hrange_pos : 0 < Module.finrank (ZMod 3) (LinearMap.range φ) := by
      rw [Module.finrank_pos_iff]
      exact Submodule.nontrivial_iff_ne_bot.mpr hrange_ne
    have hrange_one : Module.finrank (ZMod 3) (LinearMap.range φ) = 1 := by omega
    have hsquare : ∀ v, g (g v - v) = g v - v := fun v => hfix (g v - v) (hT_stable g hg v)
    exact hA g hg ⟨by rw [ggLinMove]; exact hrange_one, hsquare⟩
  let w : V ≃ₗ[ZMod 3] V := (rD 0 * rD 1 * rD 2 * rD 3 * rD 4 * rD 5) ^ 5
  have hwA : w ∈ A :=
    A.pow_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (A.mul_mem (hmemD 0) (hmemD 1))
      (hmemD 2)) (hmemD 3)) (hmemD 4)) (hmemD 5)) 5
  have hw_neg : ∀ v ∈ T, w v = -v := by
    intro v hv
    rw [hTR] at hv
    change v ∈ Submodule.span (ZMod 3) (Set.range hD) at hv
    refine Submodule.span_induction (p := fun x _ => w x = -x) ?_ ?_ ?_ ?_ hv
    · rintro y ⟨j, rfl⟩
      exact ggRS7_w0 rD pairD hrD j
    · simp
    · intro x y hx hy ihx ihy
      rw [map_add, ihx, ihy, neg_add]
    · intro a x hx ihx
      rw [map_smul, ihx, smul_neg]
  have hww : w * w = 1 := by
    apply hinj (w * w) (A.mul_mem hwA hwA)
    intro v hv
    rw [LinearEquiv.mul_apply]
    have h1 : w v = -v := hw_neg v hv
    have h2 : w (w v) = -(w v) := hw_neg (w v) (hT_stable' w hwA v hv)
    rw [h2, h1, neg_neg]
  have hww_apply : ∀ v, w (w v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hww]
    rfl
  have hcentral : ∀ a ∈ A, a * w = w * a := by
    intro a ha
    have hcomm : a * w * a⁻¹ * w⁻¹ = 1 := by
      apply hinj (a * w * a⁻¹ * w⁻¹)
        (A.mul_mem (A.mul_mem (A.mul_mem ha hwA) (A.inv_mem ha)) (A.inv_mem hwA))
      intro v hv
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      have h1 : a⁻¹ v ∈ T := hT_stable' a⁻¹ (A.inv_mem ha) v hv
      have h2 : w (a⁻¹ v) = -(a⁻¹ v) := hw_neg (a⁻¹ v) h1
      have h3 : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
      calc a (w (a⁻¹ (w⁻¹ v)))
          = a (w (a⁻¹ (w v))) := by rw [h3]
        _ = a (w (a⁻¹ (-v))) := by rw [hw_neg v hv]
        _ = a (w (-(a⁻¹ v))) := by rw [map_neg]
        _ = a (-(w (a⁻¹ v))) := by rw [map_neg]
        _ = a (-(-(a⁻¹ v))) := by rw [h2]
        _ = a (a⁻¹ v) := by rw [neg_neg]
        _ = v := by
          change a (a.symm v) = v
          rw [LinearEquiv.apply_symm_apply]
    have h1 : a * w * a⁻¹ = w := by
      have hc := congrArg (fun x => x * w) hcomm
      simpa [mul_assoc] using hc
    have h2 : a * w = w * a := by
      have hc := congrArg (fun x => x * a) h1
      simpa [mul_assoc] using hc
    exact h2
  let F : Submodule (ZMod 3) V := LinearMap.ker (w.toLinearMap - LinearMap.id)
  have hFmem : ∀ v, v ∈ F ↔ w v = v := by
    intro v
    simp only [F, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
      LinearEquiv.coe_toLinearMap]
  have hFne : F ≠ ⊥ := by
    intro hFbot
    have hall : ∀ v, w v = -v := by
      intro v
      have hmem : w v + v ∈ F := (hFmem (w v + v)).mpr (by
        rw [map_add, hww_apply, add_comm])
      rw [hFbot, Submodule.mem_bot] at hmem
      exact eq_neg_of_add_eq_zero_left hmem
    have hTtop : T = ⊤ := by
      rw [Submodule.eq_top_iff']
      intro v
      have hmemT : w v - v ∈ T := hT_stable w hwA v
      rw [hall v] at hmemT
      have hv2 : -v - v = (-2 : ZMod 3) • v := by module
      rw [hv2] at hmemT
      have hmem := T.smul_mem ((-2 : ZMod 3)⁻¹) hmemT
      rwa [smul_smul, inv_mul_cancel₀ (by decide : (-2 : ZMod 3) ≠ 0), one_smul] at hmem
    exact hTne hTtop
  obtain ⟨f, hfF, hf0⟩ := (Submodule.ne_bot_iff F).mp hFne
  have hwf : w f = f := (hFmem f).mp hfF
  have hFT : F ⊓ T = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvF, hvT⟩ := hv
    have hwv : w v = v := (hFmem v).mp hvF
    have hneg : w v = -v := hw_neg v hvT
    rw [hwv] at hneg
    have h2 : (2 : ZMod 3) • v = 0 := by
      rw [two_smul (ZMod 3) v]
      exact eq_neg_iff_add_eq_zero.mp hneg
    exact (smul_eq_zero.mp h2).resolve_left (by decide : (2 : ZMod 3) ≠ 0)
  have hfixf : ∀ a ∈ A, a f = f := by
    intro a ha
    have hafF : a f ∈ F := (hFmem (a f)).mpr (by
      rw [← LinearEquiv.mul_apply, ← hcentral a ha, LinearEquiv.mul_apply, hwf])
    have hmem : a f - f ∈ F ⊓ T := ⟨F.sub_mem hafF hfF, hT_stable a ha f⟩
    rw [hFT, Submodule.mem_bot] at hmem
    exact sub_eq_zero.mp hmem
  exact hf0 (hfixA f hfixf)

theorem ggRootSpan7_holds
    (hdim : Module.finrank (ZMod 3) V = 7)
    (hD hE : Fin 6 → V) (aD aE : Fin 6 → Module.Dual (ZMod 3) V)
    (rD rE : Fin 6 → V ≃ₗ[ZMod 3] V) (x : V)
    (pairD : ∀ i j, aD i (hD j) = (CartanMatrix.D 6 i j : ZMod 3))
    (pairE : ∀ i j, aE i (hE j) = (CartanMatrix.E₆ i j : ZMod 3))
    (hrD : ∀ i v, rD i v = v - aD i v • hD i) (hrE : ∀ i v, rE i v = v - aE i v • hE i)
    (hx : x ≠ 0) (hxD : ∀ i, aD i x = 0)
    (fixD : ∀ v, (∀ i, aD i v = 0) → v ∈ Submodule.span (ZMod 3) {x})
    (moves : ∃ i, rE i x ≠ x)
    (hA : ∀ g ∈ Subgroup.closure (Set.range rD ∪ Set.range rE),
      ¬ (Module.finrank (ZMod 3) (ggLinMove g) = 1 ∧ ∀ v, g (g v - v) = g v - v)) :
    Submodule.span (ZMod 3) (Set.range hD ∪ Set.range hE) = ⊤ ∧
      ZS.AbsIrred 3 (Subgroup.closure (Set.range rD ∪ Set.range rE)) := by
  have hspan := ggRS7_span_top hdim rD rE x pairD pairE hrD hrE hx hxD fixD moves hA
  refine ⟨hspan, ?_⟩
  refine ggRC_absIrred_of_connected (p := 3) (V := V) (ι := Fin 6 ⊕ Fin 6) (by decide)
    (Sum.elim rD rE) (Sum.elim hD hE) (Sum.elim aD aE) ?_ ?_ ?_ ?_ ?_
    (Subgroup.closure (Set.range rD ∪ Set.range rE)) ?_
  · rintro (i | i) w
    · exact hrD i w
    · exact hrE i w
  · rintro (i | i)
    · change aD i (hD i) = 2
      rw [pairD i i, CartanMatrix.D_diag]
      norm_num
    · change aE i (hE i) = 2
      rw [pairE i i, CartanMatrix.E₆, CartanMatrix.E_diag]
      norm_num
  · rw [Set.Sum.elim_range]
    exact hspan
  · intro w hw
    apply ggRS7_fixA rD rE x pairD hrD hrE fixD moves
    intro g hg
    have hgen : ∀ g ∈ Set.range rD ∪ Set.range rE, g w = w := by
      rintro g (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · rw [hrD i w, show aD i w = 0 from hw (Sum.inl i)]
        simp
      · rw [hrE i w, show aE i w = 0 from hw (Sum.inr i)]
        simp
    refine Subgroup.closure_induction (p := fun g _ => g w = w)
      (fun x hx => hgen x hx) ?_ ?_ ?_ hg
    · simp
    · intro x y hx hy ihx ihy
      rw [LinearEquiv.mul_apply, ihy, ihx]
    · intro x hx ihx
      calc x⁻¹ w = x⁻¹ (x w) := by rw [ihx]
        _ = w := by
          change x.symm (x w) = w
          rw [LinearEquiv.symm_apply_apply]
  · exact ggRS7_connected (Subgroup.closure (Set.range rD ∪ Set.range rE)) hA rD rE x
      (fun i => Subgroup.subset_closure (Or.inl (Set.mem_range_self i)))
      (fun i => Subgroup.subset_closure (Or.inr (Set.mem_range_self i)))
      pairD pairE hrD hrE fixD
  · rw [Set.Sum.elim_range]

end RootSpan7

end CFSG.StandardType

end
