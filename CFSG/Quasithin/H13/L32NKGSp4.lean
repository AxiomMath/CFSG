module

public import CFSG.Quasithin.H13.L32NKG14332
public import Certificates.Certificate7100
public import Certificates.Certificate7101

public section

namespace CFSG.Quasithin.H13.KGCert

@[expose] def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem b2z_xor (a b : Bool) : b2z (a ^^ b) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

theorem b2z_inj {a b : Bool} (h : b2z a = b2z b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

@[expose] def vec4 (n : ℕ) : Fin 4 → ZMod 2 := fun i => b2z (n.testBit i)

@[expose] def enc4 (v : Fin 4 → ZMod 2) : ℕ :=
  (v 0).val + 2 * (v 1).val + 4 * (v 2).val + 8 * (v 3).val

theorem vec4_enc4 (v : Fin 4 → ZMod 2) : vec4 (enc4 v) = v := by
  have key : ∀ a b c d : ZMod 2, vec4 (enc4 ![a, b, c, d]) = ![a, b, c, d] := by decide
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact key _ _ _ _

theorem enc4_lt (v : Fin 4 → ZMod 2) : enc4 v < 16 := by
  have h0 := ZMod.val_lt (v 0)
  have h1 := ZMod.val_lt (v 1)
  have h2 := ZMod.val_lt (v 2)
  have h3 := ZMod.val_lt (v 3)
  simp only [enc4]
  omega

theorem vec4_inj {m n : ℕ} (hm : m < 16) (hn : n < 16) (h : vec4 m = vec4 n) : m = n := by
  have key : ∀ m < 16, ∀ n < 16, vec4 m = vec4 n → m = n := by decide
  exact key m hm n hn h

theorem vec4_xor (m n : ℕ) : vec4 (m ^^^ n) = vec4 m + vec4 n := by
  ext i
  simp only [vec4, Nat.testBit_xor, b2z_xor, Pi.add_apply]

theorem vec4_zero : vec4 0 = 0 := by
  ext i
  simp [vec4, b2z]

theorem vec4_ite (c : Bool) (a : ℕ) : vec4 (if c then a else 0) = b2z c • vec4 a := by
  cases c <;> simp [vec4_zero, b2z]

@[expose] def gram (t : ℕ) : Fin 6 → ZMod 2 := fun k => b2z (t.testBit k)

@[expose] def enc6 (g : Fin 6 → ZMod 2) : ℕ :=
  (g 0).val + 2 * (g 1).val + 4 * (g 2).val + 8 * (g 3).val + 16 * (g 4).val + 32 * (g 5).val

theorem gram_enc6 (g : Fin 6 → ZMod 2) : gram (enc6 g) = g := by
  have key : ∀ a b c d e f : ZMod 2, gram (enc6 ![a, b, c, d, e, f]) = ![a, b, c, d, e, f] := by
    decide
  have hg : g = ![g 0, g 1, g 2, g 3, g 4, g 5] := by
    ext i
    fin_cases i <;> rfl
  rw [hg]
  exact key _ _ _ _ _ _

theorem enc6_lt (g : Fin 6 → ZMod 2) : enc6 g < 64 := by
  have h0 := ZMod.val_lt (g 0)
  have h1 := ZMod.val_lt (g 1)
  have h2 := ZMod.val_lt (g 2)
  have h3 := ZMod.val_lt (g 3)
  have h4 := ZMod.val_lt (g 4)
  have h5 := ZMod.val_lt (g 5)
  simp only [enc6]
  omega

@[expose] def bfE (g : Fin 6 → ZMod 2) (u w : Fin 4 → ZMod 2) : ZMod 2 :=
  g 0 * (u 0 * w 1 + u 1 * w 0) + g 1 * (u 0 * w 2 + u 2 * w 0) +
    g 2 * (u 0 * w 3 + u 3 * w 0) + g 3 * (u 1 * w 2 + u 2 * w 1) +
    g 4 * (u 1 * w 3 + u 3 * w 1) + g 5 * (u 2 * w 3 + u 3 * w 2)

@[expose] def qfE (g : Fin 6 → ZMod 2) (q₀ x : Fin 4 → ZMod 2) : ZMod 2 :=
  x 0 * q₀ 0 + x 1 * q₀ 1 + x 2 * q₀ 2 + x 3 * q₀ 3 + g 0 * x 0 * x 1 + g 1 * x 0 * x 2 +
    g 2 * x 0 * x 3 + g 3 * x 1 * x 2 + g 4 * x 1 * x 3 + g 5 * x 2 * x 3

@[expose] def applyE (δ : Fin 4 → Fin 4 → ZMod 2) (x : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  x 0 • δ 0 + x 1 • δ 1 + x 2 • δ 2 + x 3 • δ 3

theorem fin_vals : ((0 : Fin 4) : ℕ) = 0 ∧ ((1 : Fin 4) : ℕ) = 1 ∧ ((2 : Fin 4) : ℕ) = 2 ∧
    ((3 : Fin 4) : ℕ) = 3 ∧ ((0 : Fin 6) : ℕ) = 0 ∧ ((1 : Fin 6) : ℕ) = 1 ∧
    ((2 : Fin 6) : ℕ) = 2 ∧ ((3 : Fin 6) : ℕ) = 3 ∧ ((4 : Fin 6) : ℕ) = 4 ∧
    ((5 : Fin 6) : ℕ) = 5 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem b2z_bfN (t u w : ℕ) : b2z (bfN t u w) = bfE (gram t) (vec4 u) (vec4 w) := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3, f4, f5⟩ := fin_vals
  simp only [bfN, bfE, b2z_xor, b2z_and, gram, vec4, bt, e0, e1, e2, e3, f0, f1, f2, f3, f4, f5]

theorem b2z_qfN (t q₀ x : ℕ) : b2z (qfN t q₀ x) = qfE (gram t) (vec4 q₀) (vec4 x) := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3, f4, f5⟩ := fin_vals
  simp only [qfN, qfE, b2z_xor, b2z_and, gram, vec4, bt, e0, e1, e2, e3, f0, f1, f2, f3, f4, f5]

theorem vec4_applyN (δ : List ℕ) (x : ℕ) :
    vec4 (applyN δ x) = applyE (fun i => vec4 (δ.getD i 0)) (vec4 x) := by
  simp only [applyN, applyE, vec4_xor, vec4_ite, vec4, bt]
  rfl

section Coordinates

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def gramOf (B : LinearMap.BilinForm (ZMod 2) V)
    (b : Module.Basis (Fin 4) (ZMod 2) V) : Fin 6 → ZMod 2 :=
  ![B (b 0) (b 1), B (b 0) (b 2), B (b 0) (b 3), B (b 1) (b 2), B (b 1) (b 3), B (b 2) (b 3)]

theorem gramOf_apply (B : LinearMap.BilinForm (ZMod 2) V) (b : Module.Basis (Fin 4) (ZMod 2) V) :
    gramOf B b 0 = B (b 0) (b 1) ∧ gramOf B b 1 = B (b 0) (b 2) ∧ gramOf B b 2 = B (b 0) (b 3) ∧
      gramOf B b 3 = B (b 1) (b 2) ∧ gramOf B b 4 = B (b 1) (b 3) ∧
      gramOf B b 5 = B (b 2) (b 3) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem symm_of_alt {B : LinearMap.BilinForm (ZMod 2) V} (hB : ∀ v, B v v = 0) (u w : V) :
    B w u = B u w := by
  have h := hB (u + w)
  simp only [map_add, LinearMap.add_apply, hB, zero_add, add_zero] at h
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  rw [eq_neg_of_add_eq_zero_left h, hneg]

theorem B_eq_bfE {B : LinearMap.BilinForm (ZMod 2) V} (hB : ∀ v, B v v = 0)
    (b : Module.Basis (Fin 4) (ZMod 2) V) (x y : V) :
    B x y = bfE (gramOf B b) (b.equivFun x) (b.equivFun y) := by
  conv_lhs => rw [← b.sum_equivFun x, ← b.sum_equivFun y]
  simp only [Fin.sum_univ_four, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  rw [hB (b 0), hB (b 1), hB (b 2), hB (b 3), symm_of_alt hB (b 0) (b 1),
    symm_of_alt hB (b 0) (b 2), symm_of_alt hB (b 0) (b 3), symm_of_alt hB (b 1) (b 2),
    symm_of_alt hB (b 1) (b 3), symm_of_alt hB (b 2) (b 3)]
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := gramOf_apply B b
  simp only [bfE, g0, g1, g2, g3, g4, g5]
  ring

theorem q_smul {B : LinearMap.BilinForm (ZMod 2) V} {q : V → ZMod 2}
    (hpol : ∀ v w, q (v + w) = q v + q w + B v w) (c : ZMod 2) (v : V) : q (c • v) = c * q v := by
  have h0 : q 0 = 0 := by
    have h := hpol 0 0
    simp only [add_zero, map_zero] at h
    revert h
    generalize q 0 = x
    decide +revert
  have hc : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc with rfl | rfl
  · simp [h0]
  · simp

theorem q_eq_qfE {B : LinearMap.BilinForm (ZMod 2) V} {q : V → ZMod 2}
    (hpol : ∀ v w, q (v + w) = q v + q w + B v w) (b : Module.Basis (Fin 4) (ZMod 2) V) (x : V) :
    q x = qfE (gramOf B b) (fun i => q (b i)) (b.equivFun x) := by
  conv_lhs => rw [← b.sum_equivFun x]
  rw [Fin.sum_univ_four, hpol, hpol, hpol]
  simp only [q_smul hpol, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := gramOf_apply B b
  simp only [qfE, g0, g1, g2, g3, g4, g5]
  ring

@[expose] noncomputable def frameOf (b : Module.Basis (Fin 4) (ZMod 2) V) (γ : V → V) : List ℕ :=
  [enc4 (b.equivFun (γ (b 0))), enc4 (b.equivFun (γ (b 1))), enc4 (b.equivFun (γ (b 2))),
    enc4 (b.equivFun (γ (b 3)))]

theorem bfN_frame {B : LinearMap.BilinForm (ZMod 2) V} (hB : ∀ v, B v v = 0)
    (b : Module.Basis (Fin 4) (ZMod 2) V) {γ : V → V} (hγ : ∀ x y, B (γ x) (γ y) = B x y)
    (i j : Fin 4) (k : ℕ) (hk : b2z (bt (enc6 (gramOf B b)) k) = B (b i) (b j)) :
    bfN (enc6 (gramOf B b)) (enc4 (b.equivFun (γ (b i)))) (enc4 (b.equivFun (γ (b j)))) =
      bt (enc6 (gramOf B b)) k := by
  apply b2z_inj
  rw [hk, b2z_bfN, gram_enc6, vec4_enc4, vec4_enc4, ← B_eq_bfE hB, hγ]

theorem frameOf_mem {B : LinearMap.BilinForm (ZMod 2) V} (hB : ∀ v, B v v = 0)
    (b : Module.Basis (Fin 4) (ZMod 2) V) {γ : V → V} (hγ : ∀ x y, B (γ x) (γ y) = B x y) :
    frameOf b γ ∈ spFramesN (enc6 (gramOf B b)) := by
  have hg := gram_enc6 (gramOf B b)
  have hk : ∀ k : Fin 6, b2z (bt (enc6 (gramOf B b)) k) = gramOf B b k := fun k => by
    show gram (enc6 (gramOf B b)) k = gramOf B b k
    rw [hg]
  simp only [spFramesN, frameOf, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map,
    beq_iff_eq, Bool.and_eq_true]
  refine ⟨_, enc4_lt _, _, ⟨enc4_lt _, ?_⟩, _, ⟨enc4_lt _, ?_, ?_⟩, _, ⟨enc4_lt _, ⟨?_, ?_⟩, ?_⟩,
    rfl⟩
  · exact bfN_frame hB b hγ 0 1 0 (hk 0)
  · exact bfN_frame hB b hγ 0 2 1 (hk 1)
  · exact bfN_frame hB b hγ 1 2 3 (hk 3)
  · exact bfN_frame hB b hγ 0 3 2 (hk 2)
  · exact bfN_frame hB b hγ 1 3 4 (hk 4)
  · exact bfN_frame hB b hγ 2 3 5 (hk 5)

theorem frameOf_injective (b : Module.Basis (Fin 4) (ZMod 2) V) {γ γ' : V ≃ₗ[ZMod 2] V}
    (h : frameOf b γ = frameOf b γ') : γ = γ' := by
  simp only [frameOf, List.cons.injEq, and_true] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  have key : ∀ i : Fin 4, enc4 (b.equivFun (γ (b i))) = enc4 (b.equivFun (γ' (b i))) →
      γ (b i) = γ' (b i) := fun i hi => by
    have := congrArg vec4 hi
    rw [vec4_enc4, vec4_enc4] at this
    exact b.equivFun.injective this
  have hb : ∀ i, γ (b i) = γ' (b i) := by
    intro i
    fin_cases i
    · exact key 0 h0
    · exact key 1 h1
    · exact key 2 h2
    · exact key 3 h3
  exact LinearEquiv.toLinearMap_injective (b.ext hb)

theorem nondegN_eq_true {B : LinearMap.BilinForm (ZMod 2) V} (hB : ∀ v, B v v = 0)
    (hnd : ∀ v, (∀ w, B v w = 0) → v = 0) (b : Module.Basis (Fin 4) (ZMod 2) V) :
    nondegN (enc6 (gramOf B b)) = true := by
  simp only [nondegN, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true]
  intro v hv
  by_cases hv0 : v = 0
  · exact Or.inl hv0
  right
  set x := b.equivFun.symm (vec4 v) with hx
  have hx0 : x ≠ 0 := by
    intro h0
    apply hv0
    have : vec4 v = vec4 0 := by
      rw [vec4_zero, ← b.equivFun.apply_symm_apply (vec4 v), ← hx, h0, map_zero]
    exact vec4_inj hv (by norm_num) this
  obtain ⟨y, hy⟩ : ∃ y, B x y ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hx0 (hnd x hall)
  refine ⟨enc4 (b.equivFun y), enc4_lt _, ?_⟩
  have h := b2z_bfN (enc6 (gramOf B b)) v (enc4 (b.equivFun y))
  rw [gram_enc6, vec4_enc4, show vec4 v = b.equivFun x by rw [hx, LinearEquiv.apply_symm_apply],
    ← B_eq_bfE hB] at h
  cases hb : bfN (enc6 (gramOf B b)) v (enc4 (b.equivFun y))
  · rw [hb] at h
    exact absurd h.symm (by simpa [b2z] using hy)
  · rfl

end Coordinates

theorem kgSp4Quad : KGSp4Quad := by
  intro V _ _ _ B hB hnd h4 Γ hΓ q hpol hq
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set b := Module.finBasisOfFinrankEq (ZMod 2) V h4 with hbdef
  set t := enc6 (gramOf B b) with ht
  set q₀ := enc4 (fun i => q (b i)) with hq₀
  have hlen : ((spFramesN t).filter (qPresN t q₀)).length ≤ 120 := by
    have h := Certificates.certificate7100
    simp only [sp4QuadCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      Bool.not_eq_true', decide_eq_true_eq] at h
    rcases h t (enc6_lt _) with h1 | h1
    · rw [nondegN_eq_true hB hnd b] at h1
      exact absurd h1 (by decide)
    · exact h1 q₀ (enc4_lt _)
  have hqv : vec4 q₀ = fun i => q (b i) := vec4_enc4 _
  have hmem : ∀ γ ∈ Γ, frameOf b γ ∈ (spFramesN t).filter (qPresN t q₀) := by
    intro γ hγ
    refine List.mem_filter.mpr ⟨frameOf_mem hB b (hΓ γ hγ), ?_⟩
    have key : ∀ i : Fin 4, qfN t q₀ (enc4 (b.equivFun (γ (b i)))) = bt q₀ i := fun i => by
      apply b2z_inj
      rw [b2z_qfN, gram_enc6, vec4_enc4 (b.equivFun (γ (b i))), hqv, ← q_eq_qfE hpol, hq γ hγ]
      show q (b i) = vec4 q₀ i
      rw [hqv]
    simp only [qPresN, frameOf, List.getD_cons_zero, List.getD_cons_succ, beq_iff_eq,
      Bool.and_eq_true]
    exact ⟨⟨⟨key 0, key 1⟩, key 2⟩, key 3⟩
  have hinj : Nat.card Γ ≤ ((spFramesN t).filter (qPresN t q₀)).toFinset.card := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective
      (fun γ => ⟨frameOf b (γ : V ≃ₗ[ZMod 2] V), List.mem_toFinset.mpr (hmem γ γ.2)⟩) ?_
    intro γ γ' h
    exact Subtype.ext (frameOf_injective b (congrArg Subtype.val h))
  exact hinj.trans ((List.toFinset_card_le _).trans hlen)

theorem bfE_self (g : Fin 6 → ZMod 2) (u : Fin 4 → ZMod 2) : bfE g u u = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [bfE]
  linear_combination (g 0 * u 0 * u 1 + g 1 * u 0 * u 2 + g 2 * u 0 * u 3 + g 3 * u 1 * u 2 +
    g 4 * u 1 * u 3 + g 5 * u 2 * u 3) * h2

theorem bfE_symm (g : Fin 6 → ZMod 2) (u w : Fin 4 → ZMod 2) : bfE g w u = bfE g u w := by
  simp only [bfE]
  ring

theorem bfE_applyE (g : Fin 6 → ZMod 2) (D : Fin 4 → Fin 4 → ZMod 2)
    (h01 : bfE g (D 0) (D 1) = g 0) (h02 : bfE g (D 0) (D 2) = g 1)
    (h03 : bfE g (D 0) (D 3) = g 2) (h12 : bfE g (D 1) (D 2) = g 3)
    (h13 : bfE g (D 1) (D 3) = g 4) (h23 : bfE g (D 2) (D 3) = g 5) (x y : Fin 4 → ZMod 2) :
    bfE g (applyE D x) (applyE D y) = bfE g x y := by
  have key : bfE g (applyE D x) (applyE D y) =
      x 0 * y 0 * bfE g (D 0) (D 0) + x 1 * y 1 * bfE g (D 1) (D 1) +
      x 2 * y 2 * bfE g (D 2) (D 2) + x 3 * y 3 * bfE g (D 3) (D 3) +
      (x 0 * y 1 + x 1 * y 0) * bfE g (D 0) (D 1) + (x 0 * y 2 + x 2 * y 0) * bfE g (D 0) (D 2) +
      (x 0 * y 3 + x 3 * y 0) * bfE g (D 0) (D 3) + (x 1 * y 2 + x 2 * y 1) * bfE g (D 1) (D 2) +
      (x 1 * y 3 + x 3 * y 1) * bfE g (D 1) (D 3) +
      (x 2 * y 3 + x 3 * y 2) * bfE g (D 2) (D 3) := by
    simp only [applyE, bfE, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [key, bfE_self, bfE_self, bfE_self, bfE_self, h01, h02, h03, h12, h13, h23]
  simp only [bfE]
  ring

section Line

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def spGroup (B : LinearMap.BilinForm (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {γ | ∀ x y, B (γ x) (γ y) = B x y}
  mul_mem' := fun {γ δ} hγ hδ x y => by
    show B (γ (δ x)) (γ (δ y)) = B x y
    rw [hγ, hδ]
  one_mem' := fun x y => rfl
  inv_mem' := fun {γ} hγ x y => by
    have := hγ (γ⁻¹ x) (γ⁻¹ y)
    rwa [show γ (γ⁻¹ x) = x from γ.apply_symm_apply x,
      show γ (γ⁻¹ y) = y from γ.apply_symm_apply y, eq_comm] at this

theorem exists_isometry_of_frame [Finite V] {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : ∀ v, B v v = 0) (hnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (b : Module.Basis (Fin 4) (ZMod 2) V) {δ' : List ℕ} (hδ' : δ' ∈ spFramesN (enc6 (gramOf B b))) :
    ∃ δ ∈ spGroup B, ∀ x, b.equivFun (δ x) =
      applyE (fun i => vec4 (δ'.getD i 0)) (b.equivFun x) := by
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set g := gramOf B b with hgdef
  set D : Fin 4 → Fin 4 → ZMod 2 := fun i => vec4 (δ'.getD i 0) with hD
  have hg := gram_enc6 g
  have hcond : ∀ i j : Fin 4, ∀ k : Fin 6,
      bfN (enc6 g) (δ'.getD i 0) (δ'.getD j 0) = bt (enc6 g) k → bfE g (D i) (D j) = g k := by
    intro i j k h
    have := congrArg b2z h
    rw [b2z_bfN, hg] at this
    rw [this]
    show gram (enc6 g) k = g k
    rw [hg]
  simp only [spFramesN, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map,
    beq_iff_eq, Bool.and_eq_true] at hδ'
  obtain ⟨w₀, -, w₁, ⟨-, c01⟩, w₂, ⟨-, c02, c12⟩, w₃, ⟨-, ⟨c03, c13⟩, c23⟩, rfl⟩ := hδ'
  have h01 := hcond 0 1 0 c01
  have h02 := hcond 0 2 1 c02
  have h12 := hcond 1 2 3 c12
  have h03 := hcond 0 3 2 c03
  have h13 := hcond 1 3 4 c13
  have h23 := hcond 2 3 5 c23
  set δl : V →ₗ[ZMod 2] V := b.constr (ZMod 2) fun i => b.equivFun.symm (D i) with hδl
  have hδc : ∀ x, b.equivFun (δl x) = applyE D (b.equivFun x) := by
    intro x
    rw [hδl, Module.Basis.constr_apply_fintype, map_sum, Fin.sum_univ_four]
    simp only [map_smul, LinearEquiv.apply_symm_apply, applyE]
  have hδB : ∀ x y, B (δl x) (δl y) = B x y := by
    intro x y
    rw [B_eq_bfE hB b, B_eq_bfE hB b x y, hδc, hδc, bfE_applyE g D h01 h02 h03 h12 h13 h23]
  have hinj : Function.Injective δl := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine hnd x fun y => ?_
    rw [← hδB, hx, map_zero, LinearMap.zero_apply]
  refine ⟨LinearEquiv.ofInjectiveEndo δl hinj, fun x y => hδB x y, fun x => hδc x⟩

end Line

theorem mem_plane {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {ℓ : Submodule (ZMod 2) V} (hℓ : Module.finrank (ZMod 2) ℓ = 2) {v w : V} (hv : v ∈ ℓ)
    (hw : w ∈ ℓ) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hwv : w ≠ v) {u : V} (hu : u ∈ ℓ) :
    u = 0 ∨ u = v ∨ u = w ∨ u = v + w := by
  classical
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hneg : ∀ x : V, -x = x := fun x => by
    have h2 : x + x = 0 := by
      rw [← two_smul (ZMod 2) x]
      exact (congrArg (· • x) (rfl : (2 : ZMod 2) = 0)).trans (zero_smul _ x)
    exact (eq_neg_of_add_eq_zero_left h2).symm
  have hvw0 : v + w ≠ 0 := fun h => hwv (by rw [eq_neg_of_add_eq_zero_right h, hneg])
  set f : Fin 4 → ℓ := ![⟨0, ℓ.zero_mem⟩, ⟨v, hv⟩, ⟨w, hw⟩, ⟨v + w, ℓ.add_mem hv hw⟩] with hfdef
  have hf : Function.Injective f := by
    intro i j h
    have h' := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> simp [hfdef] at h' ⊢
    all_goals first
      | exact absurd h'.symm hv0 | exact absurd h' hv0 | exact absurd h'.symm hw0
      | exact absurd h' hw0 | exact absurd h' hwv | exact absurd h'.symm hwv
      | exact absurd h'.symm hvw0 | exact absurd h' hvw0
  have hcard : Nat.card ℓ = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hℓ, Nat.card_zmod]
    norm_num
  have hbij : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨i, hi⟩ := hbij.2 ⟨u, hu⟩
  have hiu := congrArg Subtype.val hi
  fin_cases i <;> simp [hfdef] at hiu
  · exact Or.inl hiu.symm
  · exact Or.inr (Or.inl hiu.symm)
  · exact Or.inr (Or.inr (Or.inl hiu.symm))
  · exact Or.inr (Or.inr (Or.inr hiu.symm))

theorem getD_lt_of_mem {t : ℕ} {δ : List ℕ} (hδ : δ ∈ spFramesN t) (i : ℕ) : δ.getD i 0 < 16 := by
  simp only [spFramesN, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map] at hδ
  obtain ⟨w₀, h₀, w₁, ⟨h₁, -⟩, w₂, ⟨h₂, -⟩, w₃, ⟨h₃, -⟩, rfl⟩ := hδ
  rcases i with _ | _ | _ | _ | i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃
  · simp

theorem applyN_lt {δ : List ℕ} (hδ : ∀ i, δ.getD i 0 < 16) (x : ℕ) : applyN δ x < 16 := by
  have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
  have hite : ∀ (c : Bool) (n : ℕ), n < 2 ^ 4 → (if c then n else 0) < 2 ^ 4 := by
    intro c n hn
    cases c
    · simp
    · simpa using hn
  rw [h16] at hδ ⊢
  simp only [applyN]
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (hite _ _ (hδ 0))
    (hite _ _ (hδ 1))) (hite _ _ (hδ 2))) (hite _ _ (hδ 3))

theorem kgSp4Line : KGSp4Line := by
  intro V _ _ _ B hB hnd h4 Γ hΓ h360 v hv0 ℓ hvℓ hℓ hti
  have : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  set b := Module.finBasisOfFinrankEq (ZMod 2) V h4 with hbdef
  set t := enc6 (gramOf B b) with ht
  have hcheck := Certificates.certificate7101
  simp only [sp4LineCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.any_eq_true] at hcheck
  obtain ⟨hlen, hline⟩ : (spFramesN t).length ≤ 720 ∧ _ := by
    rcases hcheck t (enc6_lt _) with h1 | h1
    · rw [nondegN_eq_true hB hnd b] at h1
      exact absurd h1 (by decide)
    · exact h1
  have hSp : Nat.card (spGroup B) ≤ 720 := by
    have hinj : Nat.card (spGroup B) ≤ (spFramesN t).toFinset.card := by
      rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
      refine Nat.card_le_card_of_injective
        (fun γ => ⟨frameOf b ((γ : V ≃ₗ[ZMod 2] V) : V → V),
          List.mem_toFinset.mpr (frameOf_mem hB b γ.2)⟩) ?_
      intro γ γ' h
      exact Subtype.ext (frameOf_injective b (congrArg Subtype.val h))
    exact hinj.trans ((List.toFinset_card_le _).trans hlen)
  have hΓS : Γ ≤ spGroup B := fun γ hγ x y => hΓ γ hγ x y
  have hsq : ∀ δ ∈ spGroup B, δ * δ ∈ Γ := by
    intro δ hδ
    have : Finite (V ≃ₗ[ZMod 2] V) :=
      Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
    set Γ' := Γ.subgroupOf (spGroup B) with hΓ'
    have hc : Nat.card Γ' = Nat.card Γ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΓS).toEquiv
    have hidx := Subgroup.index_mul_card Γ'
    rw [hc] at hidx
    have hi0 : Γ'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hi2 : Γ'.index ≤ 2 := by
      by_contra h3
      push Not at h3
      have : 3 * 360 ≤ Γ'.index * Nat.card Γ := Nat.mul_le_mul h3 h360
      omega
    have hmem : (⟨δ, hδ⟩ : ↥(spGroup B)) ^ 2 ∈ Γ' := by
      rcases (show Γ'.index = 1 ∨ Γ'.index = 2 by omega) with h1 | h2
      · rw [Subgroup.index_eq_one.mp h1]
        exact Subgroup.mem_top _
      · exact Subgroup.sq_mem_of_index_two h2 _
    rw [hΓ', Subgroup.mem_subgroupOf] at hmem
    simpa [pow_two] using hmem
  obtain ⟨w, hwℓ, hw0, hwv⟩ : ∃ w ∈ ℓ, w ≠ 0 ∧ w ≠ v := by
    by_contra hall
    push Not at hall
    have hle : ℓ ≤ Submodule.span (ZMod 2) {v} := by
      intro u hu
      by_cases hu0 : u = 0
      · rw [hu0]
        exact Submodule.zero_mem _
      · rw [hall u hu hu0]
        exact Submodule.subset_span rfl
    have h1 := Submodule.finrank_mono hle
    rw [hℓ] at h1
    have h2 := finrank_span_le_card (R := ZMod 2) ({v} : Set V)
    simp at h2
    omega
  set v' := enc4 (b.equivFun v) with hv'
  set w' := enc4 (b.equivFun w) with hw'
  have hcv : vec4 v' = b.equivFun v := vec4_enc4 _
  have hcw : vec4 w' = b.equivFun w := vec4_enc4 _
  have hv'0 : v' ≠ 0 := by
    intro h
    apply hv0
    have := hcv
    rw [h, vec4_zero] at this
    exact b.equivFun.injective (this.symm.trans (map_zero _).symm)
  have hw'0 : w' ≠ 0 := by
    intro h
    apply hw0
    have := hcw
    rw [h, vec4_zero] at this
    exact b.equivFun.injective (this.symm.trans (map_zero _).symm)
  have hw'v' : w' ≠ v' := fun h => hwv (b.equivFun.injective (by rw [← hcv, ← hcw, h]))
  have hbvw : bfN t v' w' = false := by
    cases hb : bfN t v' w'
    · rfl
    · exfalso
      have := b2z_bfN t v' w'
      rw [hb, gram_enc6, hcv, hcw, ← B_eq_bfE hB, hti v hvℓ w hwℓ] at this
      exact absurd this (by decide)
  rcases hline v' (enc4_lt _) with h0 | hline'
  · exact absurd h0 hv'0
  rcases hline' w' (enc4_lt _) with ((h0 | h0) | h0) | ⟨δ', hδ', hwit⟩
  · exact absurd h0 hw'0
  · exact absurd h0 hw'v'
  · rw [hbvw] at h0
    exact absurd h0 (by decide)
  simp only [lineWitN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hwit
  obtain ⟨⟨⟨⟨hfix, hn0⟩, hnv⟩, hnw⟩, hnvw⟩ := hwit
  obtain ⟨δ, hδS, hδc⟩ := exists_isometry_of_frame hB hnd b hδ'
  have hlt := getD_lt_of_mem hδ'
  have hδδ : ∀ x : V, b.equivFun ((δ * δ) x) =
      vec4 (applyN δ' (applyN δ' (enc4 (b.equivFun x)))) := by
    intro x
    rw [vec4_applyN, vec4_applyN, vec4_enc4, LinearEquiv.mul_apply, hδc, hδc]
  refine ⟨δ * δ, hsq δ hδS, ?_, w, hwℓ, ?_⟩
  · apply b.equivFun.injective
    rw [hδδ, ← hv', hfix, hcv]
  · intro hmem
    have hlt' := applyN_lt hlt (applyN δ' w')
    rcases mem_plane hℓ hvℓ hwℓ hv0 hw0 hwv hmem with h | h | h | h
    · apply hn0
      apply vec4_inj hlt' (by norm_num)
      rw [vec4_zero, hw', ← hδδ w, h, map_zero]
    · apply hnv
      apply vec4_inj hlt' (enc4_lt _)
      rw [hw', ← hδδ w, h, hcv]
    · apply hnw
      apply vec4_inj hlt' (enc4_lt _)
      rw [hw', ← hδδ w, h, ← hw', hcw]
    · apply hnvw
      have hxor : v' ^^^ w' < 16 := by
        have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
        rw [h16]
        exact Nat.xor_lt_two_pow (h16 ▸ enc4_lt _) (h16 ▸ enc4_lt _)
      apply vec4_inj hlt' hxor
      rw [vec4_xor, hcv, hcw, hw', ← hδδ w, h, map_add]

end CFSG.Quasithin.H13.KGCert
