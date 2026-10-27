module

public import CFSG.Timmesfeld.Bridge.RootStructR2Higman

public section

namespace CFSG.Timmesfeld.Bridge.NatSum

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule

variable (K V : Type*) [Field K] [AddCommGroup V]
  [DistribMulAction (SpecialLinearGroup (Fin 2) K) V]

@[expose] def fixedUpper : AddSubgroup V where
  carrier := {v | ∀ t : K, upperElt K t • v = v}
  add_mem' {v w} hv hw t := by rw [smul_add, hv t, hw t]
  zero_mem' _ := smul_zero _
  neg_mem' {v} hv t := by rw [smul_neg, hv t]

@[expose] def fixedLower : AddSubgroup V where
  carrier := {v | ∀ t : K, lowerElt K t • v = v}
  add_mem' {v w} hv hw t := by rw [smul_add, hv t, hw t]
  zero_mem' _ := smul_zero _
  neg_mem' {v} hv t := by rw [smul_neg, hv t]

variable {K V}

theorem mem_fixedUpper {v : V} : v ∈ fixedUpper K V ↔ ∀ t : K, upperElt K t • v = v := Iff.rfl

theorem mem_fixedLower {v : V} : v ∈ fixedLower K V ↔ ∀ t : K, lowerElt K t • v = v := Iff.rfl

variable [CharP K 2]

theorem weylElt_smul_mem_fixedLower {v : V} (hv : v ∈ fixedUpper K V) :
    weylElt K • v ∈ fixedLower K V := by
  intro t
  rw [lowerElt_smul, weylElt_smul_weylElt_smul, hv t]

theorem weylElt_smul_mem_fixedUpper {v : V} (hv : v ∈ fixedLower K V) :
    weylElt K • v ∈ fixedUpper K V := by
  intro t
  calc upperElt K t • weylElt K • v = weylElt K • (weylElt K • upperElt K t • weylElt K • v) :=
        (weylElt_smul_weylElt_smul _).symm
    _ = weylElt K • (lowerElt K t • v) := by rw [lowerElt_smul]
    _ = weylElt K • v := by rw [hv t]

theorem card_fixedLower_eq [Finite V] :
    Nat.card (fixedLower K V) = Nat.card (fixedUpper K V) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨weylElt K • (v : V), weylElt_smul_mem_fixedUpper v.2⟩
      invFun := fun v => ⟨weylElt K • (v : V), weylElt_smul_mem_fixedLower v.2⟩
      left_inv := fun v => Subtype.ext (weylElt_smul_weylElt_smul _)
      right_inv := fun v => Subtype.ext (weylElt_smul_weylElt_smul _) }

section Quadratic

variable (hquad : ∀ (s t : K) (v : V),
    upperElt K s • (upperElt K t • v - v) = upperElt K t • v - v)
  (hfix : ∀ v : V, (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0)

omit [CharP K 2] in
include hfix in
theorem eq_zero_of_mem_fixed {v : V} (hu : v ∈ fixedUpper K V) (hl : v ∈ fixedLower K V) :
    v = 0 :=
  hfix v (sl2_induction (one_smul _ v) (fun x y hx hy => by rw [mul_smul, hy, hx])
    (fun x hx => by rw [inv_smul_eq_iff, hx]) hu hl)

theorem natVec_zero_left (c : K) : natVec (0 : V) c = 0 := by
  simp [natVec]

theorem natVec_add_left (u u' : V) (c : K) : natVec (u + u') c = natVec u c + natVec u' c := by
  simp only [natVec, smul_add]
  abel

variable [PerfectRing K 2]

@[expose, reducible] noncomputable def moduleFixedUpper : Module K (fixedUpper K V) where
  smul c u := ⟨natVec (u : V) c, fun t => upperElt_smul_natVec hquad _ t c⟩
  one_smul u := Subtype.ext (natVec_one hquad hfix u.2)
  mul_smul c c' u := by
    apply Subtype.ext
    show natVec (u : V) (c * c') = natVec (natVec (u : V) c') c
    by_cases hc : c = 0
    · rw [hc, zero_mul, natVec_zero, natVec_zero]
    by_cases hc' : c' = 0
    · rw [hc', mul_zero, natVec_zero, natVec_zero_left]
    have h1 := natVec_eq_diagElt_smul hquad hfix u.2 (Units.mk0 (c * c') (mul_ne_zero hc hc'))
    have h2 := natVec_eq_diagElt_smul hquad hfix u.2 (Units.mk0 c' hc')
    have h3 := natVec_eq_diagElt_smul hquad hfix (fun t => upperElt_smul_natVec hquad (u : V) t c')
      (Units.mk0 c hc)
    rw [Units.val_mk0] at h1 h2 h3
    rw [h1, h3, h2, ← mul_smul, diagElt_mul_diagElt]
    congr 2
    ext
    simp
  smul_zero c := Subtype.ext (natVec_zero_left c)
  smul_add c u u' := Subtype.ext (natVec_add_left (u : V) u' c)
  add_smul c c' u := Subtype.ext (natVec_add hquad _ c c')
  zero_smul u := Subtype.ext (natVec_zero _)

variable [Finite K] [Finite V]

include hquad hfix in
theorem card_fixedUpper :
    Nat.card (fixedUpper K V) =
      Nat.card K ^ @Module.finrank K (fixedUpper K V) _ _ (moduleFixedUpper hquad hfix) := by
  let := moduleFixedUpper hquad hfix
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (fixedUpper K V)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

include hquad hfix in
theorem exists_natural_sum
    (hspan : ∀ v : V, ∃ u ∈ fixedUpper K V, ∃ w ∈ fixedLower K V, v = u + w) :
    ∃ k : ℕ, ∃ θ : Fin k → (Fin 2 → K) →+ V,
      (∀ i, Function.Injective (θ i)) ∧
      (∀ i (x : SpecialLinearGroup (Fin 2) K) (v : Fin 2 → K),
        θ i ((x : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = x • θ i v) ∧
      (∀ i (s : K), θ i ![s, 0] ∈ fixedUpper K V ∧ θ i ![0, s] ∈ fixedLower K V) ∧
      (∀ v : V, ∃ c : Fin k → Fin 2 → K, v = ∑ i, θ i (c i)) ∧
      Nat.card V = Nat.card K ^ (2 * k) ∧
      Nat.card (fixedUpper K V) = Nat.card K ^ k ∧
      Nat.card (fixedLower K V) = Nat.card K ^ k := by
  let := moduleFixedUpper hquad hfix
  set k := Module.finrank K (fixedUpper K V) with hk
  let b := Module.finBasis K (fixedUpper K V)
  have hcardU : Nat.card (fixedUpper K V) = Nat.card K ^ k := card_fixedUpper hquad hfix
  have hcardW : Nat.card (fixedLower K V) = Nat.card K ^ k := by
    rw [card_fixedLower_eq, hcardU]
  have hmemU : ∀ (w : V), w ∈ fixedUpper K V → ∀ c : K, natVec w c ∈ fixedUpper K V :=
    fun w _ c t => upperElt_smul_natVec hquad w t c
  let θ : Fin k → (Fin 2 → K) →+ V := fun i =>
    AddMonoidHom.mk' (natMap ((b i : fixedUpper K V) : V)) (natMap_add hquad _)
  have hθ : ∀ i v, θ i v = natVec (b i : V) (v 0) + weylElt K • natVec (b i : V) (v 1) :=
    fun i v => rfl
  have hcoe : ∀ (c : K) (u : fixedUpper K V), ((c • u : fixedUpper K V) : V) = natVec (u : V) c :=
    fun c u => rfl
  refine ⟨k, θ, fun i => ?_, fun i x v => natMap_mulVec hquad hfix (b i).2 x v,
    fun i s => ⟨?_, ?_⟩, fun v => ?_, ?_, hcardU, hcardW⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hθ] at hv
    have h1 : natVec (b i : V) (v 0) = -(weylElt K • natVec (b i : V) (v 1)) :=
      eq_neg_of_add_eq_zero_left hv
    have hu := hmemU _ (b i).2 (v 0)
    have hl : natVec (b i : V) (v 0) ∈ fixedLower K V := by
      rw [h1]
      exact neg_mem (weylElt_smul_mem_fixedLower (hmemU _ (b i).2 (v 1)))
    have h0 := eq_zero_of_mem_fixed hfix hu hl
    have h0' : natVec (b i : V) (v 1) = 0 := by
      rw [h0, eq_comm, neg_eq_zero] at h1
      exact (smul_eq_zero_iff_eq (weylElt K)).1 h1
    have hz : ∀ c : K, natVec (b i : V) c = 0 → c = 0 := by
      intro c hc
      have : c • b i = 0 := Subtype.ext (by rw [hcoe]; exact hc)
      exact (smul_eq_zero.1 this).resolve_right (b.ne_zero i)
    have e0 := hz _ h0
    have e1 := hz _ h0'
    ext j
    fin_cases j
    · exact e0
    · exact e1
  · rw [hθ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, natVec_zero, smul_zero, add_zero]
    exact hmemU _ (b i).2 s
  · rw [hθ]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, natVec_zero, zero_add]
    exact weylElt_smul_mem_fixedLower (hmemU _ (b i).2 s)
  · obtain ⟨u, hu, w, hw, rfl⟩ := hspan v
    set u₀ : fixedUpper K V := ⟨u, hu⟩
    set u₁ : fixedUpper K V := ⟨weylElt K • w, weylElt_smul_mem_fixedUpper hw⟩
    refine ⟨fun i => ![b.repr u₀ i, b.repr u₁ i], ?_⟩
    simp only [hθ, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum]
    have e0 : ∑ i, natVec (b i : V) (b.repr u₀ i) = u := by
      have := congrArg Subtype.val (b.sum_repr u₀)
      rw [AddSubgroup.val_finsetSum] at this
      exact this
    have e1 : ∑ i, natVec (b i : V) (b.repr u₁ i) = weylElt K • w := by
      have := congrArg Subtype.val (b.sum_repr u₁)
      rw [AddSubgroup.val_finsetSum] at this
      exact this
    rw [e0, e1, weylElt_smul_weylElt_smul]
  ·
    have hbij : Function.Bijective
        (fun p : fixedUpper K V × fixedLower K V => (p.1 : V) + p.2) := by
      refine ⟨fun p p' h => ?_, fun v => ?_⟩
      · have h1 : (p.1 : V) - p'.1 = p'.2 - p.2 := by
          simp only at h
          rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
        have hu : (p.1 : V) - p'.1 ∈ fixedUpper K V := sub_mem p.1.2 p'.1.2
        have hl : (p.1 : V) - p'.1 ∈ fixedLower K V := by rw [h1]; exact sub_mem p'.2.2 p.2.2
        have h0 := eq_zero_of_mem_fixed hfix hu hl
        have h0' : (p'.2 : V) - p.2 = 0 := by rw [← h1, h0]
        exact Prod.ext (Subtype.ext (sub_eq_zero.1 h0)) (Subtype.ext (sub_eq_zero.1 h0').symm)
      · obtain ⟨u, hu, w, hw, rfl⟩ := hspan v
        exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), rfl⟩
    rw [← Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_prod, hcardU, hcardW, ← pow_add,
      two_mul]

end Quadratic

end CFSG.Timmesfeld.Bridge.NatSum

namespace CFSG.Timmesfeld.Bridge.QuotMod

open Matrix CFSG.Timmesfeld CFSG.Timmesfeld.RankOne CFSG.Timmesfeld.ARS.NaturalModule
  CFSG.Timmesfeld.Bridge.NatSum

variable {G : Type*} [Group G]

structure Hyp (X N N₀ : Subgroup G) : Prop where
  le : N₀ ≤ N
  comm : ∀ n ∈ N, ∀ n' ∈ N, n * n' * n⁻¹ * n'⁻¹ ∈ N₀
  conj : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N
  conj₀ : ∀ g ∈ X, ∀ n ∈ N₀, g * n * g⁻¹ ∈ N₀

variable {X N N₀ : Subgroup G}

theorem Hyp.conj_mem (h : Hyp X N N₀) {n m : G} (hn : n ∈ N) (hm : m ∈ N₀) :
    n * m * n⁻¹ ∈ N₀ := by
  have e : n * m * n⁻¹ = (n * m * n⁻¹ * m⁻¹) * m := by group
  rw [e]
  exact N₀.mul_mem (h.comm n hn m (h.le hm)) hm

theorem Hyp.normal (h : Hyp X N N₀) : (N₀.subgroupOf N).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.conj_mem g.2 hn⟩

section Quot

variable [(N₀.subgroupOf N).Normal]

@[expose] def mk (N₀ : Subgroup G) [(N₀.subgroupOf N).Normal] (n : N) :
    Additive (↥N ⧸ N₀.subgroupOf N) :=
  Additive.ofMul (QuotientGroup.mk n)

theorem mk_mul (n n' : N) : mk N₀ (n * n') = mk N₀ n + mk N₀ n' := rfl

theorem mk_inv (n : N) : mk N₀ n⁻¹ = -mk N₀ n := rfl

theorem mk_one : mk N₀ (1 : N) = 0 := rfl

theorem mk_eq_zero_iff (n : N) : mk N₀ n = 0 ↔ (n : G) ∈ N₀ := by
  change (QuotientGroup.mk n : ↥N ⧸ N₀.subgroupOf N) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mk_eq_mk_iff (n n' : N) : mk N₀ n = mk N₀ n' ↔ (n : G)⁻¹ * n' ∈ N₀ := by
  change (QuotientGroup.mk n : ↥N ⧸ N₀.subgroupOf N) = QuotientGroup.mk n' ↔ _
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

theorem mk_surjective : Function.Surjective (mk (N := N) N₀) := fun v =>
  QuotientGroup.mk_surjective (Additive.toMul v)

@[reducible] def addCommGroup (h : Hyp X N N₀) :
    AddCommGroup (Additive (↥N ⧸ N₀.subgroupOf N)) :=
  { (inferInstance : AddGroup (Additive (↥N ⧸ N₀.subgroupOf N))) with
    add_comm := fun a b => by
      obtain ⟨n, rfl⟩ := mk_surjective (N₀ := N₀) a
      obtain ⟨n', rfl⟩ := mk_surjective (N₀ := N₀) b
      rw [← mk_mul, ← mk_mul, mk_eq_mk_iff]
      have := h.comm _ (N.inv_mem n'.2) _ (N.inv_mem n.2)
      simp only [Subgroup.coe_mul] at this ⊢
      convert this using 1
      group }

@[expose] def conjN (h : Hyp X N N₀) (g : G) (hg : g ∈ X) : N →* N where
  toFun n := ⟨g * n * g⁻¹, h.conj g hg n n.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' n n' := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

@[expose] def conjQ (h : Hyp X N N₀) (g : G) (hg : g ∈ X) :
    (↥N ⧸ N₀.subgroupOf N) →* (↥N ⧸ N₀.subgroupOf N) :=
  QuotientGroup.map _ _ (conjN h g hg) (fun n hn => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf] at *
    exact h.conj₀ g hg n hn)

variable {K : Type*} [Field K]

@[reducible] def action (h : Hyp X N N₀) (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K) :
    DistribMulAction (SpecialLinearGroup (Fin 2) K) (Additive (↥N ⧸ N₀.subgroupOf N)) where
  smul s v := Additive.ofMul (conjQ h (φ.symm s) (φ.symm s).2 (Additive.toMul v))
  one_smul v := by
    obtain ⟨n, rfl⟩ := mk_surjective (N₀ := N₀) v
    change mk N₀ (conjN h _ _ n) = mk N₀ n
    congr 1
    ext
    simp [conjN]
  mul_smul s s' v := by
    obtain ⟨n, rfl⟩ := mk_surjective (N₀ := N₀) v
    change mk N₀ (conjN h _ _ n) = mk N₀ (conjN h _ _ (conjN h _ _ n))
    congr 1
    ext
    simp only [conjN, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, Subgroup.coe_mul]
    group
  smul_zero s := map_one (conjQ h (φ.symm s) (φ.symm s).2)
  smul_add s v v' :=
    map_mul (conjQ h (φ.symm s) (φ.symm s).2) (Additive.toMul v) (Additive.toMul v')

variable [Finite K] [CharP K 2] [PerfectRing K 2]

theorem exists_isNaturalQuotient [Finite G] (h : Hyp X N N₀)
    (φ : ↥X ≃* SpecialLinearGroup (Fin 2) K) {A B : Subgroup G}
    (hN₀A : N₀ ≤ A) (hN₀B : N₀ ≤ B) (hAN : A ≤ N) (hBN : B ≤ N) (hNAB : A ⊔ B = N)
    (hupA : ∀ x : X, φ x ∈ upperUnipotent K → ∀ k ∈ A, (x : G) * k * (x : G)⁻¹ * k⁻¹ ∈ N₀)
    (hupB : ∀ x : X, φ x ∈ upperUnipotent K → ∀ w ∈ B, (x : G) * w * (x : G)⁻¹ * w⁻¹ ∈ A)
    (hup₀ : ∃ x₀ : X, φ x₀ ∈ upperUnipotent K ∧
      ∀ w ∈ B, (x₀ : G) * w * (x₀ : G)⁻¹ * w⁻¹ ∈ N₀ → w ∈ N₀)
    (hloB : ∀ y : X, φ y ∈ lowerUnipotent K → ∀ w ∈ B, (y : G) * w * (y : G)⁻¹ * w⁻¹ ∈ N₀)
    (hlo₀ : ∃ y₀ : X, φ y₀ ∈ lowerUnipotent K ∧
      ∀ k ∈ A, (y₀ : G) * k * (y₀ : G)⁻¹ * k⁻¹ ∈ N₀ → k ∈ N₀) :
    ∃ k : ℕ, ∃ Nf : Fin k → Subgroup G, ∃ θ : Fin k → (Fin 2 → K) → G,
      (∀ i, N₀ ≤ Nf i ∧ Higman.IsNaturalQuotient φ (Nf i) N₀ (θ i)) ∧
      (∀ i (s : K), θ i ![s, 0] ∈ A ∧ θ i ![0, s] ∈ B) ∧
      N₀ ⊔ ⨆ i, Nf i = N ∧
      Nat.card N = Nat.card N₀ * Nat.card K ^ (2 * k) ∧
      Nat.card A = Nat.card N₀ * Nat.card K ^ k ∧
      Nat.card B = Nat.card N₀ * Nat.card K ^ k := by
  classical
  let _ : AddCommGroup (Additive (↥N ⧸ N₀.subgroupOf N)) := addCommGroup h
  let _ := action h φ
  have hsmul : ∀ (s : SpecialLinearGroup (Fin 2) K) (g : G) (hg : g ∈ N),
      s • mk N₀ ⟨g, hg⟩ =
        mk N₀ ⟨(φ.symm s : G) * g * (φ.symm s : G)⁻¹, h.conj _ (φ.symm s).2 g hg⟩ :=
    fun _ _ _ => rfl
  have hcl : A ⊔ B = Subgroup.closure ((A : Set G) ∪ B) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hclN : Subgroup.closure ((A : Set G) ∪ B) ≤ N := by rw [← hcl, hNAB]
  have hdec : ∀ g (hg : g ∈ N), ∃ k, ∃ hk : k ∈ A, ∃ w, ∃ hw : w ∈ B,
      mk N₀ ⟨g, hg⟩ = mk N₀ ⟨k, hAN hk⟩ + mk N₀ ⟨w, hBN hw⟩ := by
    intro g hg
    have hg' : g ∈ Subgroup.closure ((A : Set G) ∪ B) := by rw [← hcl, hNAB]; exact hg
    revert hg
    induction hg' using Subgroup.closure_induction with
    | mem g hg =>
      intro hgN
      rcases hg with hgA | hgB
      · refine ⟨g, hgA, 1, B.one_mem, ?_⟩
        rw [show (⟨1, hBN B.one_mem⟩ : N) = 1 from rfl, mk_one, add_zero]
      · refine ⟨1, A.one_mem, g, hgB, ?_⟩
        rw [show (⟨1, hAN A.one_mem⟩ : N) = 1 from rfl, mk_one, zero_add]
    | one =>
      intro _
      refine ⟨1, A.one_mem, 1, B.one_mem, ?_⟩
      rw [show (⟨1, hAN A.one_mem⟩ : N) = 1 from rfl, mk_one, add_zero]
    | mul g g' hg hg' ihg ihg' =>
      intro _
      obtain ⟨k, hk, w, hw, e⟩ := ihg (hclN hg)
      obtain ⟨k', hk', w', hw', e'⟩ := ihg' (hclN hg')
      refine ⟨k * k', A.mul_mem hk hk', w * w', B.mul_mem hw hw', ?_⟩
      change mk N₀ (⟨g, hclN hg⟩ * ⟨g', hclN hg'⟩) =
        mk N₀ (⟨k, hAN hk⟩ * ⟨k', hAN hk'⟩) + mk N₀ (⟨w, hBN hw⟩ * ⟨w', hBN hw'⟩)
      rw [mk_mul, mk_mul, mk_mul, e, e']
      abel
    | inv g hg ihg =>
      intro _
      obtain ⟨k, hk, w, hw, e⟩ := ihg (hclN hg)
      refine ⟨k⁻¹, A.inv_mem hk, w⁻¹, B.inv_mem hw, ?_⟩
      change mk N₀ (⟨g, hclN hg⟩)⁻¹ = mk N₀ (⟨k, hAN hk⟩)⁻¹ + mk N₀ (⟨w, hBN hw⟩)⁻¹
      rw [mk_inv, mk_inv, mk_inv, e]
      abel
  have hphiU : ∀ t : K, φ (φ.symm (upperElt K t)) ∈ upperUnipotent K := fun t => by
    rw [MulEquiv.apply_symm_apply]
    exact (mem_upperUnipotent_iff K).2 ⟨t, rfl⟩
  have hphiL : ∀ t : K, φ (φ.symm (lowerElt K t)) ∈ lowerUnipotent K := fun t => by
    rw [MulEquiv.apply_symm_apply]
    exact (mem_lowerUnipotent_iff K).2 ⟨t, rfl⟩
  have hfixA : ∀ (t : K) (k : G) (hk : k ∈ A),
      upperElt K t • mk N₀ ⟨k, hAN hk⟩ = mk N₀ ⟨k, hAN hk⟩ := by
    intro t k hk
    rw [hsmul, mk_eq_mk_iff]
    have := hupA _ (hphiU t) k⁻¹ (A.inv_mem hk)
    convert this using 1
    simp only [inv_inv]
    group
  have hfixB : ∀ (t : K) (w : G) (hw : w ∈ B),
      lowerElt K t • mk N₀ ⟨w, hBN hw⟩ = mk N₀ ⟨w, hBN hw⟩ := by
    intro t w hw
    rw [hsmul, mk_eq_mk_iff]
    have := hloB _ (hphiL t) w⁻¹ (B.inv_mem hw)
    convert this using 1
    simp only [inv_inv]
    group
  have hU : ∀ v, v ∈ fixedUpper K (Additive (↥N ⧸ N₀.subgroupOf N)) ↔
      ∃ k, ∃ hk : k ∈ A, v = mk N₀ ⟨k, hAN hk⟩ := by
    intro v
    refine ⟨fun hv => ?_, fun ⟨k, hk, e⟩ t => by rw [e]; exact hfixA t k hk⟩
    obtain ⟨n, rfl⟩ := mk_surjective (N₀ := N₀) v
    obtain ⟨k, hk, w, hw, e⟩ := hdec n n.2
    obtain ⟨x₀, hx₀, hx₀B⟩ := hup₀
    obtain ⟨t₀, ht₀⟩ := (mem_upperUnipotent_iff K).1 hx₀
    have h1 := hv t₀
    rw [e, smul_add, hfixA t₀ k hk, add_right_inj, hsmul, mk_eq_mk_iff] at h1
    have hx₀' : φ.symm (upperElt K t₀) = x₀ := by rw [← ht₀, MulEquiv.symm_apply_apply]
    rw [hx₀'] at h1
    have hw' : w⁻¹ ∈ N₀ := hx₀B _ (B.inv_mem hw) (by convert h1 using 1; simp only [inv_inv]; group)
    have hw0 : mk N₀ ⟨w, hBN hw⟩ = 0 := (mk_eq_zero_iff _).2 (by simpa using N₀.inv_mem hw')
    exact ⟨k, hk, by rw [e, hw0, add_zero]⟩
  have hW : ∀ v, v ∈ fixedLower K (Additive (↥N ⧸ N₀.subgroupOf N)) ↔
      ∃ w, ∃ hw : w ∈ B, v = mk N₀ ⟨w, hBN hw⟩ := by
    intro v
    refine ⟨fun hv => ?_, fun ⟨w, hw, e⟩ t => by rw [e]; exact hfixB t w hw⟩
    obtain ⟨n, rfl⟩ := mk_surjective (N₀ := N₀) v
    obtain ⟨k, hk, w, hw, e⟩ := hdec n n.2
    obtain ⟨y₀, hy₀, hy₀A⟩ := hlo₀
    obtain ⟨t₀, ht₀⟩ := (mem_lowerUnipotent_iff K).1 hy₀
    have h1 := hv t₀
    rw [e, smul_add, hfixB t₀ w hw, add_left_inj, hsmul, mk_eq_mk_iff] at h1
    have hy₀' : φ.symm (lowerElt K t₀) = y₀ := by rw [← ht₀, MulEquiv.symm_apply_apply]
    rw [hy₀'] at h1
    have hk' : k⁻¹ ∈ N₀ := hy₀A _ (A.inv_mem hk) (by convert h1 using 1; simp only [inv_inv]; group)
    have hk0 : mk N₀ ⟨k, hAN hk⟩ = 0 := (mk_eq_zero_iff _).2 (by simpa using N₀.inv_mem hk')
    exact ⟨w, hw, by rw [e, hk0, zero_add]⟩
  have hquad : ∀ (s t : K) (v : Additive (↥N ⧸ N₀.subgroupOf N)),
      upperElt K s • (upperElt K t • v - v) = upperElt K t • v - v := by
    intro s t v
    obtain ⟨n, rfl⟩ := mk_surjective (N₀ := N₀) v
    obtain ⟨k, hk, w, hw, e⟩ := hdec n n.2
    have hc := hupB _ (hphiU t) w hw
    have e2 : upperElt K t • mk N₀ ⟨w, hBN hw⟩ - mk N₀ ⟨w, hBN hw⟩ = mk N₀ ⟨_, hAN hc⟩ := by
      rw [hsmul, sub_eq_iff_eq_add, ← mk_mul]
      congr 1
      ext
      simp only [Subgroup.coe_mul]
      group
    rw [e, smul_add, hfixA t k hk, add_sub_add_left_eq_sub, e2, hfixA s _ hc]
  have hfix : ∀ v : Additive (↥N ⧸ N₀.subgroupOf N),
      (∀ x : SpecialLinearGroup (Fin 2) K, x • v = v) → v = 0 := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := (hU v).1 (fun t => hv _)
    obtain ⟨y₀, hy₀, hy₀A⟩ := hlo₀
    obtain ⟨t₀, ht₀⟩ := (mem_lowerUnipotent_iff K).1 hy₀
    have h1 := hv (lowerElt K t₀)
    rw [hsmul, mk_eq_mk_iff] at h1
    have hy₀' : φ.symm (lowerElt K t₀) = y₀ := by rw [← ht₀, MulEquiv.symm_apply_apply]
    rw [hy₀'] at h1
    have hk' : k⁻¹ ∈ N₀ := hy₀A _ (A.inv_mem hk) (by convert h1 using 1; simp only [inv_inv]; group)
    exact (mk_eq_zero_iff _).2 (by simpa using N₀.inv_mem hk')
  have hspan : ∀ v : Additive (↥N ⧸ N₀.subgroupOf N),
      ∃ u ∈ fixedUpper K (Additive (↥N ⧸ N₀.subgroupOf N)),
        ∃ w ∈ fixedLower K (Additive (↥N ⧸ N₀.subgroupOf N)), v = u + w := by
    intro v
    obtain ⟨n, rfl⟩ := mk_surjective (N₀ := N₀) v
    obtain ⟨k, hk, w, hw, e⟩ := hdec n n.2
    exact ⟨_, (hU _).2 ⟨k, hk, rfl⟩, _, (hW _).2 ⟨w, hw, rfl⟩, e⟩
  obtain ⟨k, θ, hinj, hequiv, hcoord, hsum, hcardV, hcardU, hcardW⟩ :=
    exists_natural_sum hquad hfix hspan
  have hcardN₀ : Nat.card (N₀.subgroupOf N) = Nat.card N₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  have hcardQ : Nat.card (↥N ⧸ N₀.subgroupOf N) = Nat.card K ^ (2 * k) := by
    rw [← hcardV]
    exact Nat.card_congr Additive.ofMul
  have hcardSub : ∀ {C : Subgroup G} (hCN : C ≤ N) (hN₀C : N₀ ≤ C)
      (S : AddSubgroup (Additive (↥N ⧸ N₀.subgroupOf N)))
      (hS : ∀ v, v ∈ S ↔ ∃ c, ∃ hc : c ∈ C, v = mk N₀ ⟨c, hCN hc⟩),
      Nat.card C = Nat.card N₀ * Nat.card S := by
    intro C hCN hN₀C S hS
    let ψ : C →* (↥N ⧸ N₀.subgroupOf N) :=
      (QuotientGroup.mk' (N₀.subgroupOf N)).comp (Subgroup.inclusion hCN)
    have hker : ψ.ker = N₀.subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact mk_eq_zero_iff (N₀ := N₀) (Subgroup.inclusion hCN c)
    have hrange : Nat.card ψ.range = Nat.card S := by
      refine Nat.card_congr
        { toFun := fun q => ⟨Additive.ofMul q.1, by
            obtain ⟨c, hc⟩ := q.2
            rw [hS, ← hc]
            exact ⟨c, c.2, rfl⟩⟩
          invFun := fun v => ⟨Additive.toMul v.1, by
            obtain ⟨c, hc, e⟩ := (hS v.1).1 v.2
            exact ⟨⟨c, hc⟩, by rw [e]; rfl⟩⟩
          left_inv := fun q => rfl
          right_inv := fun v => rfl }
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hrange, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN₀C).toEquiv, mul_comm]
  have hcardA : Nat.card A = Nat.card N₀ * Nat.card K ^ k := by
    rw [hcardSub hAN hN₀A _ hU, hcardU]
  have hcardB : Nat.card B = Nat.card N₀ * Nat.card K ^ k := by
    rw [hcardSub hBN hN₀B _ hW, hcardW]
  have hcardN : Nat.card N = Nat.card N₀ * Nat.card K ^ (2 * k) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (N₀.subgroupOf N), hcardQ, hcardN₀,
      mul_comm]
  choose! fA hfA hfA' using fun u hu => (hU u).1 hu
  choose! fB hfB hfB' using fun w hw => (hW w).1 hw
  have hfA0 : fA 0 ∈ N₀ := by
    have := hfA' 0 (zero_mem _)
    exact (mk_eq_zero_iff _).1 this.symm
  have hfB0 : fB 0 ∈ N₀ := by
    have := hfB' 0 (zero_mem _)
    exact (mk_eq_zero_iff _).1 this.symm
  let θ' : Fin k → (Fin 2 → K) → G := fun i v => fA (θ i ![v 0, 0]) * fB (θ i ![0, v 1])
  have hθ'A : ∀ (i : Fin k) (v : Fin 2 → K), fA (θ i ![v 0, 0]) ∈ A := fun i v =>
    hfA _ (hcoord i (v 0)).1
  have hθ'B : ∀ (i : Fin k) (v : Fin 2 → K), fB (θ i ![0, v 1]) ∈ B := fun i v =>
    hfB _ (hcoord i (v 1)).2
  have hθ'N : ∀ (i : Fin k) (v : Fin 2 → K), θ' i v ∈ N := fun i v =>
    N.mul_mem (hAN (hθ'A i v)) (hBN (hθ'B i v))
  have hmkθ' : ∀ (i : Fin k) (v : Fin 2 → K), mk N₀ ⟨θ' i v, hθ'N i v⟩ = θ i v := by
    intro i v
    change mk N₀ (⟨_, hAN (hθ'A i v)⟩ * ⟨_, hBN (hθ'B i v)⟩) = _
    rw [mk_mul, ← hfA' _ (hcoord i (v 0)).1, ← hfB' _ (hcoord i (v 1)).2, ← map_add]
    congr 1
    ext j
    fin_cases j <;> simp
  let Nf : Fin k → Subgroup G := fun i =>
    { carrier := {g | ∃ hg : g ∈ N, mk N₀ ⟨g, hg⟩ ∈ (θ i).range}
      mul_mem' := by
        rintro g g' ⟨hg, hgθ⟩ ⟨hg', hg'θ⟩
        refine ⟨N.mul_mem hg hg', ?_⟩
        change mk N₀ (⟨g, hg⟩ * ⟨g', hg'⟩) ∈ _
        rw [mk_mul]
        exact add_mem hgθ hg'θ
      one_mem' := by
        refine ⟨N.one_mem, ?_⟩
        change mk N₀ 1 ∈ _
        rw [mk_one]
        exact zero_mem _
      inv_mem' := by
        rintro g ⟨hg, hgθ⟩
        refine ⟨N.inv_mem hg, ?_⟩
        change mk N₀ (⟨g, hg⟩)⁻¹ ∈ _
        rw [mk_inv]
        exact neg_mem hgθ }
  have hmemNf : ∀ i g, g ∈ Nf i ↔ ∃ hg : g ∈ N, mk N₀ ⟨g, hg⟩ ∈ (θ i).range := fun _ _ => Iff.rfl
  have hmk_mul_inv : ∀ (g g' : G) (hg : g ∈ N) (hg' : g' ∈ N),
      mk N₀ ⟨g⁻¹ * g', N.mul_mem (N.inv_mem hg) hg'⟩ = -mk N₀ ⟨g, hg⟩ + mk N₀ ⟨g', hg'⟩ :=
    fun g g' hg hg' => by
      change mk N₀ ((⟨g, hg⟩)⁻¹ * ⟨g', hg'⟩) = _
      rw [mk_mul, mk_inv]
  refine ⟨k, Nf, θ', fun i => ⟨fun m hm => ⟨h.le hm, ?_⟩, ⟨fun v => ?_, fun v w => ?_,
    fun v hv => ?_, fun n hn => ?_, fun x v => ?_⟩⟩, fun i s => ⟨?_, ?_⟩, ?_, hcardN, hcardA,
    hcardB⟩
  · rw [(mk_eq_zero_iff _).2 hm]
    exact zero_mem _
  · exact ⟨hθ'N i v, by rw [hmkθ']; exact ⟨v, rfl⟩⟩
  · rw [← mk_eq_zero_iff (N₀ := N₀) ⟨_, N.mul_mem (N.inv_mem (N.mul_mem (hθ'N i v) (hθ'N i w)))
      (hθ'N i (v + w))⟩]
    rw [hmk_mul_inv _ _ (N.mul_mem (hθ'N i v) (hθ'N i w)) (hθ'N i (v + w))]
    change -mk N₀ (⟨_, hθ'N i v⟩ * ⟨_, hθ'N i w⟩) + _ = 0
    rw [mk_mul, hmkθ', hmkθ', hmkθ', map_add]
    abel
  · have h0 : mk N₀ ⟨θ' i v, hθ'N i v⟩ = 0 := (mk_eq_zero_iff _).2 hv
    rw [hmkθ'] at h0
    exact hinj i (h0.trans (map_zero _).symm)
  · obtain ⟨hnN, v, hv⟩ := hn
    refine ⟨v, ?_⟩
    rw [← mk_eq_zero_iff (N₀ := N₀) ⟨_, N.mul_mem (N.inv_mem (hθ'N i v)) hnN⟩,
      hmk_mul_inv _ _ (hθ'N i v) hnN, hmkθ', ← hv]
    abel
  · have hxN : (x : G) * θ' i v * (x : G)⁻¹ ∈ N := h.conj _ x.2 _ (hθ'N i v)
    rw [← mk_eq_zero_iff (N₀ := N₀) ⟨_, N.mul_mem (N.inv_mem (hθ'N i _)) hxN⟩,
      hmk_mul_inv _ _ (hθ'N i _) hxN, hmkθ']
    have e : mk N₀ ⟨(x : G) * θ' i v * (x : G)⁻¹, hxN⟩ = φ x • mk N₀ ⟨θ' i v, hθ'N i v⟩ := by
      rw [hsmul]
      simp only [MulEquiv.symm_apply_apply]
    rw [e, hmkθ', hequiv]
    abel
  · change fA (θ i ![s, 0]) * fB (θ i ![0, 0]) ∈ A
    rw [show (![0, 0] : Fin 2 → K) = 0 from vec2_zero, map_zero]
    exact A.mul_mem (hfA _ (hcoord i s).1) (hN₀A hfB0)
  · change fA (θ i ![0, 0]) * fB (θ i ![0, s]) ∈ B
    rw [show (![0, 0] : Fin 2 → K) = 0 from vec2_zero, map_zero]
    exact B.mul_mem (hN₀B hfA0) (hfB _ (hcoord i s).2)
  · refine le_antisymm (sup_le h.le (iSup_le fun i g hg => hg.1)) fun n hn => ?_
    set S := N₀ ⊔ ⨆ i, Nf i with hS
    have hSN : S ≤ N := sup_le h.le (iSup_le fun i g hg => hg.1)
    let P : Set (Additive (↥N ⧸ N₀.subgroupOf N)) :=
      {v | ∃ g, ∃ hg : g ∈ S, mk N₀ ⟨g, hSN hg⟩ = v}
    have hP0 : (0 : Additive (↥N ⧸ N₀.subgroupOf N)) ∈ P := ⟨1, S.one_mem, mk_one⟩
    have hPadd : ∀ v w, v ∈ P → w ∈ P → v + w ∈ P := by
      rintro v w ⟨g, hg, rfl⟩ ⟨g', hg', rfl⟩
      exact ⟨g * g', S.mul_mem hg hg', mk_mul (N₀ := N₀) ⟨g, hSN hg⟩ ⟨g', hSN hg'⟩⟩
    have hPθ : ∀ i c, θ i c ∈ P := fun i c =>
      ⟨θ' i c, Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem i
        (⟨hθ'N i c, by rw [hmkθ']; exact ⟨c, rfl⟩⟩ : θ' i c ∈ Nf i)), hmkθ' i c⟩
    obtain ⟨c, hc⟩ := hsum (mk N₀ ⟨n, hn⟩)
    have hmem : mk N₀ ⟨n, hn⟩ ∈ P := by
      rw [hc]
      exact Finset.sum_induction _ (· ∈ P) hPadd hP0 fun i _ => hPθ i (c i)
    obtain ⟨g, hg, hgn⟩ := hmem
    have hgn' : g⁻¹ * n ∈ N₀ := (mk_eq_mk_iff _ _).1 hgn
    have : n = g * (g⁻¹ * n) := by group
    rw [this]
    exact S.mul_mem hg (Subgroup.mem_sup_left hgn')

end Quot

end CFSG.Timmesfeld.Bridge.QuotMod
