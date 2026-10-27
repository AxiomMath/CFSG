module

public import CFSG.Quasithin.H13.L32NLem1442e
public import CFSG.Quasithin.H13.L32NLem1442h
public import CFSG.Quasithin.H13.L32NLem14324k
public import CFSG.Quasithin.H13.L32NLem14324a
public import CFSG.Quasithin.H13.L32NLem14411b

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Mat8Cert L1442M

namespace L1442

theorem perm7_normal_data {Γ : Type*} [Group Γ] (e : Γ ≃* Equiv.Perm (Fin 7)) :
    ∃ A : Subgroup Γ, A.Normal ∧ CFSG.Open.IsComponentOf A ⊤ ∧
      ∀ g h : Γ, g ∉ A → h ∉ A → g * h⁻¹ ∈ A := by
  classical
  have h5 : 5 ≤ Nat.card (Fin 7) := by simp
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup h5
  set A : Subgroup Γ := (alternatingGroup (Fin 7)).map e.symm.toMonoidHom with hA
  have hAmem : ∀ g : Γ, g ∈ A ↔ Equiv.Perm.sign (e g) = 1 := by
    intro g
    rw [hA, Subgroup.mem_map]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      simpa using Equiv.Perm.mem_alternatingGroup.1 hσ
    · intro hg
      exact ⟨e g, Equiv.Perm.mem_alternatingGroup.2 hg, by simp⟩
  have hAnormal : A.Normal := (inferInstance : (alternatingGroup (Fin 7)).Normal).map
    e.symm.toMonoidHom e.symm.surjective
  let φ : ↥(alternatingGroup (Fin 7)) ≃* ↥A := e.symm.subgroupMap (alternatingGroup (Fin 7))
  have hAsimple : IsSimpleGroup ↥A := φ.symm.isSimpleGroup
  have hAnc : ∃ a b : ↥A, a * b ≠ b * a := by
    have hma : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    have hmb : Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 3 ∈ alternatingGroup (Fin 7) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      decide +kernel
    have hne : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) * (Equiv.swap 0 1 * Equiv.swap 1 3) ≠
        (Equiv.swap 0 1 * Equiv.swap 1 3) * (Equiv.swap 0 1 * Equiv.swap 1 2) := by decide +kernel
    refine ⟨φ ⟨_, hma⟩, φ ⟨_, hmb⟩, fun h => hne ?_⟩
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (φ.injective h)
  refine ⟨A, hAnormal, ?_, ?_⟩
  · refine ⟨le_top, CFSG.Open.IsSubnormal.step le_top ?_ (CFSG.Open.IsSubnormal.refl _),
      SzN28.isQuasisimple_of_simple hAnc⟩
    exact hAnormal.subgroupOf ⊤
  · intro g h hg hh
    rw [hAmem] at hg hh ⊢
    simp only [map_mul, map_inv]
    have key : ∀ u v : ℤˣ, u ≠ 1 → v ≠ 1 → u * v⁻¹ = 1 := by decide
    exact key _ _ hg hh

theorem b4V_eq (x y : Fin 8 → ZMod 2) :
    b4V x y = ∑ k : Fin 4, (x (Fin.castAdd 4 k) * y (Fin.natAdd 4 k) +
      y (Fin.castAdd 4 k) * x (Fin.natAdd 4 k)) := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  simp only [b4V, q4V, Pi.add_apply, Fin.sum_univ_four]
  have e0 : Fin.castAdd 4 (0 : Fin 4) = (0 : Fin 8) := rfl
  have e1 : Fin.castAdd 4 (1 : Fin 4) = (1 : Fin 8) := rfl
  have e2 : Fin.castAdd 4 (2 : Fin 4) = (2 : Fin 8) := rfl
  have e3 : Fin.castAdd 4 (3 : Fin 4) = (3 : Fin 8) := rfl
  have f0 : Fin.natAdd 4 (0 : Fin 4) = (4 : Fin 8) := rfl
  have f1 : Fin.natAdd 4 (1 : Fin 4) = (5 : Fin 8) := rfl
  have f2 : Fin.natAdd 4 (2 : Fin 4) = (6 : Fin 8) := rfl
  have f3 : Fin.natAdd 4 (3 : Fin 4) = (7 : Fin 8) := rfl
  rw [e0, e1, e2, e3, f0, f1, f2, f3]
  linear_combination (x 0 * x 4 + x 1 * x 5 + x 2 * x 6 + x 3 * x 7 + y 0 * y 4 + y 1 * y 5 +
    y 2 * y 6 + y 3 * y 7) * h2

private theorem s7_span_facts :
    ∀ i : Fin 8, ∃ j : Fin 2, ∃ n : Fin 256,
      mv8 ((Mat8Cert.colsOf ((if j = 0 then s7g0 else s7g1 : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2)))) n ^^^ n = 2 ^ (i : ℕ) := by
  decide +kernel

end L1442

namespace S8Tr.Frame

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {I I' : Submodule (ZMod 2) V} (F : Frame B I I')
include F

theorem B_eq_b4V (b : Module.Basis (Fin 4) (ZMod 2) I) {d : Fin 4 → V}
    (hd : ∀ k, d k ∈ I') (hbd : ∀ l k, B (b l) (d k) = if l = k then 1 else 0) (v w : V) :
    B v w = b4V (F.coord b hd hbd v) (F.coord b hd hbd w) := by
  have hc : ∀ (u : V) (k : Fin 4), F.coord b hd hbd u (Fin.castAdd 4 k) = B u (d k) := by
    intro u k
    rw [F.coord_apply, Function.comp_apply, e8, finSumFinEquiv_symm_apply_castAdd]
    rfl
  have hc' : ∀ (u : V) (k : Fin 4), F.coord b hd hbd u (Fin.natAdd 4 k) = B (b k) u := by
    intro u k
    rw [F.coord_apply, Function.comp_apply, e8, finSumFinEquiv_symm_apply_natAdd]
    rfl
  rw [L1442.b4V_eq]
  simp only [hc, hc']
  conv_lhs => rw [F.expand b hd hbd v]
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [F.symm (d k) w]
  ring

end S8Tr.Frame

namespace S8Cert

theorem q4V_s8 {γ : GL (Fin 8) (ZMod 2)} (hγ : γ ∈ s8)
    (v : Fin 8 → ZMod 2) : q4V ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) = q4V v := by
  have hgen : ∀ g ∈ s8G, ∀ n < 256, q4N (mv8 g n) = q4N n := by decide +kernel
  rw [s8_eq] at hγ
  induction hγ using Subgroup.closure_induction generalizing v with
  | mem g hg =>
    have hg' : colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ s8G := hg
    rw [← vec8_code8 v, ← dec8_colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)), dec8_mulVec,
      ← q4N_spec, ← q4N_spec, hgen _ hg' _ (code8_lt v)]
  | one => simp
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hx, hy]
  | inv x _ hx =>
    have h1 := hx (((x⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    exact h1.symm

theorem b4V_s8 {γ : GL (Fin 8) (ZMod 2)} (hγ : γ ∈ s8)
    (v w : Fin 8 → ZMod 2) :
    b4V ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)
      ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w) = b4V v w := by
  simp only [b4V]
  rw [← Matrix.mulVec_add, q4V_s8 hγ, q4V_s8 hγ, q4V_s8 hγ]

@[expose] def InI (v : Fin 8 → ZMod 2) : Prop := v 4 = 0 ∧ v 5 = 0 ∧ v 6 = 0 ∧ v 7 = 0

@[expose] def InIs (v : Fin 8 → ZMod 2) : Prop := v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0

theorem inI_iff_mem_subI (v : Fin 8 → ZMod 2) : InI v ↔ v ∈ subI := by
  constructor
  · rintro ⟨h4, h5, h6, h7⟩ i hi
    have hi8 := i.2
    have : i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> assumption
  · intro h
    exact ⟨h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)⟩

theorem inII_iff (v : Fin 8 → ZMod 2) : inII (code8 v) = true ↔ InI v ∨ InIs v := by
  have key : ∀ a b c d e f g h : ZMod 2, inII (code8 ![a, b, c, d, e, f, g, h]) = true ↔
      (e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) := by
    decide
  have hv : v = ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7] := by
    ext i
    fin_cases i <;> rfl
  rw [hv]
  exact key _ _ _ _ _ _ _ _

theorem subI_cases {γ : GL (Fin 8) (ZMod 2)} (hγ : γ ∈ s8) :
    (∀ v, InI v → InI ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)) ∨
      (∀ v, InI v → InIs ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)) := by
  have hII : ∀ v, InI v → InI ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) ∨
      InIs ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) := by
    intro v hv
    rw [← inII_iff, inII_s8 hγ v, inII_iff]
    exact Or.inl hv
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨v₁, hv₁, hn₁⟩, ⟨v₂, hv₂, hn₂⟩⟩ := hcon
  have h₁ : InIs ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v₁) := (hII v₁ hv₁).resolve_left hn₁
  have h₂ : InI ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v₂) := (hII v₂ hv₂).resolve_right hn₂
  have hv : InI (v₁ + v₂) := by
    obtain ⟨a4, a5, a6, a7⟩ := hv₁
    obtain ⟨b4, b5, b6, b7⟩ := hv₂
    exact ⟨by simp [a4, b4], by simp [a5, b5], by simp [a6, b6], by simp [a7, b7]⟩
  have hsub : ∀ a b : ZMod 2, a + b = 0 → b = 0 → a = 0 := by decide
  rcases hII _ hv with h | h
  · apply hn₁
    rw [Matrix.mulVec_add] at h
    obtain ⟨c4, c5, c6, c7⟩ := h
    obtain ⟨d4, d5, d6, d7⟩ := h₂
    exact ⟨hsub _ _ c4 d4, hsub _ _ c5 d5, hsub _ _ c6 d6, hsub _ _ c7 d7⟩
  · apply hn₂
    rw [Matrix.mulVec_add] at h
    obtain ⟨c0, c1, c2, c3⟩ := h
    obtain ⟨d0, d1, d2, d3⟩ := h₁
    have hsub' : ∀ a b : ZMod 2, a + b = 0 → a = 0 → b = 0 := by decide
    exact ⟨hsub' _ _ c0 d0, hsub' _ _ c1 d1, hsub' _ _ c2 d2, hsub' _ _ c3 d3⟩


theorem subIs_cases {γ : GL (Fin 8) (ZMod 2)} (hγ : γ ∈ s8) :
    (∀ v, InIs v → InI ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)) ∨
      (∀ v, InIs v → InIs ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)) := by
  have hII : ∀ v, InIs v → InI ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) ∨
      InIs ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) := by
    intro v hv
    rw [← inII_iff, inII_s8 hγ v, inII_iff]
    exact Or.inr hv
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨v₁, hv₁, hn₁⟩, ⟨v₂, hv₂, hn₂⟩⟩ := hcon
  have h₁ : InIs ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v₁) := (hII v₁ hv₁).resolve_left hn₁
  have h₂ : InI ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v₂) := (hII v₂ hv₂).resolve_right hn₂
  have hv : InIs (v₁ + v₂) := by
    obtain ⟨a0, a1, a2, a3⟩ := hv₁
    obtain ⟨b0, b1, b2, b3⟩ := hv₂
    exact ⟨by simp [a0, b0], by simp [a1, b1], by simp [a2, b2], by simp [a3, b3]⟩
  have hsub : ∀ a b : ZMod 2, a + b = 0 → b = 0 → a = 0 := by decide
  have hsub' : ∀ a b : ZMod 2, a + b = 0 → a = 0 → b = 0 := by decide
  rcases hII _ hv with h | h
  · apply hn₁
    rw [Matrix.mulVec_add] at h
    obtain ⟨c4, c5, c6, c7⟩ := h
    obtain ⟨d4, d5, d6, d7⟩ := h₂
    exact ⟨hsub _ _ c4 d4, hsub _ _ c5 d5, hsub _ _ c6 d6, hsub _ _ c7 d7⟩
  · apply hn₂
    rw [Matrix.mulVec_add] at h
    obtain ⟨c0, c1, c2, c3⟩ := h
    obtain ⟨d0, d1, d2, d3⟩ := h₁
    exact ⟨hsub' _ _ c0 d0, hsub' _ _ c1 d1, hsub' _ _ c2 d2, hsub' _ _ c3 d3⟩

theorem eq_zero_of_inI_inIs {v : Fin 8 → ZMod 2} (h1 : InI v) (h2 : InIs v) : v = 0 := by
  obtain ⟨a4, a5, a6, a7⟩ := h1
  obtain ⟨a0, a1, a2, a3⟩ := h2
  ext i
  fin_cases i <;> assumption

theorem exists_decomp (v : Fin 8 → ZMod 2) : ∃ v₁ v₂, InI v₁ ∧ InIs v₂ ∧ v = v₁ + v₂ := by
  refine ⟨![v 0, v 1, v 2, v 3, 0, 0, 0, 0], ![0, 0, 0, 0, v 4, v 5, v 6, v 7],
    ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  ext i
  fin_cases i <;> simp

theorem not_both {γ : GL (Fin 8) (ZMod 2)} {P : (Fin 8 → ZMod 2) → Prop}
    (hP : ∀ v w, P v → P w → P (v + w)) (hne : ∃ u, ¬ P u)
    (h1 : ∀ v, InI v → P ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v))
    (h2 : ∀ v, InIs v → P ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v)) : False := by
  obtain ⟨u, hu⟩ := hne
  set v := ((γ⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec u with hv
  obtain ⟨v₁, v₂, hv₁, hv₂, hvv⟩ := exists_decomp v
  apply hu
  have : (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v = u := by
    rw [hv, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [← this, hvv, Matrix.mulVec_add]
  exact hP _ _ (h1 v₁ hv₁) (h2 v₂ hv₂)

theorem inI_add {v w : Fin 8 → ZMod 2} (hv : InI v) (hw : InI w) : InI (v + w) := by
  obtain ⟨a4, a5, a6, a7⟩ := hv
  obtain ⟨b4, b5, b6, b7⟩ := hw
  exact ⟨by simp [a4, b4], by simp [a5, b5], by simp [a6, b6], by simp [a7, b7]⟩

theorem inIs_add {v w : Fin 8 → ZMod 2} (hv : InIs v) (hw : InIs w) : InIs (v + w) := by
  obtain ⟨a0, a1, a2, a3⟩ := hv
  obtain ⟨b0, b1, b2, b3⟩ := hw
  exact ⟨by simp [a0, b0], by simp [a1, b1], by simp [a2, b2], by simp [a3, b3]⟩

theorem not_inI_single : ¬ InI (Pi.single (4 : Fin 8) (1 : ZMod 2)) := by
  rintro ⟨h4, -⟩
  exact absurd h4 (by decide)

theorem not_inIs_single : ¬ InIs (Pi.single (0 : Fin 8) (1 : ZMod 2)) := by
  rintro ⟨h0, -⟩
  exact absurd h0 (by decide)

end S8Cert


namespace L1442

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

theorem case4_of_concl8
    (h12213 : Stmt12_2_13)
    (h8 : G112Concl8 D.B (D.img (l32nH T V)) (D.img (CFSG.conjugate (l32nW T V V₂) g))) :
    Case1442Four T V V₂ g D := by
  classical
  have hB := C.g111.toG101Hyp
  have h8' := h8
  obtain ⟨hd8, ⟨φ⟩, I, hI4, hIiso, hIinv, x, hxX, ⟨v₀, hv₀I, hxv₀⟩, hcompl⟩ := h8
  set Γ := D.img (l32nH T V) with hΓ
  set X := D.img (CFSG.conjugate (l32nW T V V₂) g) with hX
  have hxΓ : x ∈ Γ := C.X_le hxX
  have hxx : x * x = 1 := hB.X_sq x hxX
  have hxinv : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hxx).symm
  have hxxv : ∀ w, x (x w) = w := fun w => by
    rw [← LinearEquiv.mul_apply, hxx]
    rfl
  have hX8 : Nat.card X = 2 ^ 3 := by
    obtain ⟨k, hk⟩ := C.exists_card_X
    have hlt : ¬ 16 ≤ Nat.card X := fun h16 =>
      L14324.false_of_concl8 C.X_le hB.X_sq hk h16 h8'
    have hlow := C.lower
    rw [hd8] at hlow
    rw [hk] at hlt hlow ⊢
    have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hlow)
    have hk4 : k < 4 := by
      by_contra h4
      exact hlt (by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 ≤ k by omega)
        simpa using this)
    rw [show k = 3 by omega]
  obtain ⟨A₀, hA₀n, hA₀c, hA₀o⟩ := perm7_normal_data φ
  set A : Subgroup (D.V ≃ₗ[ZMod 2] D.V) := A₀.map Γ.subtype with hA
  have hAΓ : A ≤ Γ := Subgroup.map_subtype_le A₀
  have hAI : ∀ a' ∈ A, ∀ i ∈ I, a' i ∈ I := by
    rintro _ ⟨a₀, ha₀, rfl⟩ i hi
    have hlay : a₀ ∈ genFittingLayer ↥Γ := (le_sSup hA₀c : A₀ ≤ genFittingLayer ↥Γ) ha₀
    exact hIinv _ ⟨a₀, hlay, rfl⟩ i hi
  have hxA : x ∉ A := fun hx => hxv₀ (hAI x hx v₀ hv₀I)
  have houter : ∀ γ ∈ Γ, γ ∉ A → ∃ a' ∈ A, γ = a' * x := by
    intro γ hγ hγA
    have hγ' : (⟨γ, hγ⟩ : ↥Γ) ∉ A₀ := fun h => hγA ⟨_, h, rfl⟩
    have hx' : (⟨x, hxΓ⟩ : ↥Γ) ∉ A₀ := fun h => hxA ⟨_, h, rfl⟩
    have h1 := hA₀o _ _ hγ' hx'
    refine ⟨γ * x⁻¹, ⟨_, h1, rfl⟩, by group⟩
  set I' : Submodule (ZMod 2) D.V := I.map (x : D.V →ₗ[ZMod 2] D.V) with hI'
  have hxI : ∀ i ∈ I, x i ∈ I' := fun i hi => ⟨i, hi, rfl⟩
  have hxI' : ∀ j ∈ I', x j ∈ I := by
    rintro _ ⟨i, hi, rfl⟩
    rw [LinearEquiv.coe_coe, hxxv]
    exact hi
  have hAI' : ∀ a' ∈ A, ∀ j ∈ I', a' j ∈ I' := by
    rintro _ ⟨a₀, ha₀, rfl⟩ _ ⟨i, hi, rfl⟩
    have hc : (⟨x, hxΓ⟩ : ↥Γ) * a₀ * (⟨x, hxΓ⟩ : ↥Γ)⁻¹ ∈ A₀ := hA₀n.conj_mem a₀ ha₀ _
    have hcA : x * (a₀ : D.V ≃ₗ[ZMod 2] D.V) * x ∈ A := by
      refine ⟨_, hc, ?_⟩
      simp [hxinv]
    refine ⟨(x * (a₀ : D.V ≃ₗ[ZMod 2] D.V) * x) i, hAI _ hcA i hi, ?_⟩
    simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply, Subgroup.coe_subtype, hxxv]
  have F : S8Tr.Frame D.B I I' :=
    { alt := hB.alt
      nd := hB.nondegenerate
      compl := hcompl
      iso := hIiso
      iso' := by
        rintro _ ⟨i, hi, rfl⟩ _ ⟨i', hi', rfl⟩
        exact (hB.isometry x hxΓ i i').trans (hIiso i hi i' hi')
      rank := hI4
      rank' := by rw [hI', LinearEquiv.finrank_map_eq, hI4] }
  let bI : Module.Basis (Fin 4) (ZMod 2) I := Module.finBasisOfFinrankEq (ZMod 2) I hI4
  obtain ⟨d, hd, hbd⟩ := F.exists_dual bI
  set e₀ := F.coord bI hd hbd with he₀
  have hAs8 : ∀ a' ∈ A, L14411.matOf e₀ a' ∈ s8 := by
    intro a' ha'
    obtain ⟨hdet, hmat⟩ := F.matOf_eq_blk bI hd hbd (hB.isometry a' (hAΓ ha')) (hAI a' ha')
      (hAI' a' ha')
    obtain ⟨u, hu, hu'⟩ := S8Cert.blk_mem_s8 _ hdet
    have : L14411.matOf e₀ a' = u := Units.ext (hmat.trans hu'.symm)
    rw [this]
    exact hu
  have hxs8 : L14411.matOf e₀ x ∈ s8 := by
    obtain ⟨hdet, hmat⟩ := F.matOf_eq_blk_tau bI hd hbd (hB.isometry x hxΓ) hxI hxI'
    obtain ⟨u, hu, hu'⟩ := S8Cert.blk_mem_s8 _ hdet
    have : L14411.matOf e₀ x = u * s8g4 := Units.ext (by rw [hmat, Units.val_mul, hu'])
    rw [this]
    exact mul_mem hu S8Cert.s8g4_mem
  have hΓs8 : ∀ γ ∈ Γ, L14411.matOf e₀ γ ∈ s8 := by
    intro γ hγ
    by_cases hγA : γ ∈ A
    · exact hAs8 γ hγA
    · obtain ⟨a', ha', rfl⟩ := houter γ hγ hγA
      rw [map_mul]
      exact mul_mem (hAs8 a' ha') hxs8
  set Y := Γ.map (L14411.matOf e₀) with hY
  have hYs8 : Y ≤ s8 := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact hΓs8 γ hγ
  let ψ : ↥Γ ≃* ↥Y := Γ.equivMapOfInjective _ (L14411.matOf_injective e₀)
  obtain ⟨m, hm, hmY⟩ := S7Conj.exists_conj_s7 hYs8 (φ.symm.trans ψ)
  set e₁ := e₀.trans (L14411.linOf m) with he₁
  have he₁v : ∀ v, e₁ v = (m : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e₀ v) := fun v => rfl
  have hΓs7 : ∀ γ ∈ Γ, L14411.matOf e₁ γ ∈ s7 := by
    intro γ hγ
    rw [he₁, L14411.matOf_trans]
    exact hmY _ ⟨γ, hγ, rfl⟩
  have himg : Γ.map (L14411.matOf e₁) = s7 := by
    refine Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨γ, hγ, rfl⟩; exact hΓs7 γ hγ) ?_
    rw [S7Cert.card_s7, Subgroup.card_map_of_injective (L14411.matOf_injective e₁),
      Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  obtain ⟨q, hqU, hqB, hqΓ⟩ := C.exists_quad h12213
  have hBe₁ : ∀ v w, D.B v w = b4V (e₁ v) (e₁ w) := by
    intro v w
    rw [F.B_eq_b4V bI hd hbd v w, he₁v, he₁v, S8Cert.b4V_s8 hm]
  set lam : (Fin 8 → ZMod 2) → ZMod 2 := fun y => q (e₁.symm y) + q4V y with hlam
  have h2 : (2 : ZMod 2) = 0 := rfl
  have hadd : ∀ y z, lam (y + z) = lam y + lam z := by
    intro y z
    simp only [hlam]
    rw [map_add, hqB, hBe₁, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [b4V]
    linear_combination (q4V (y + z)) * h2
  have hinv : ∀ γ ∈ s7, ∀ y, lam ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec y) = lam y := by
    intro γ hγ y
    rw [← himg] at hγ
    obtain ⟨ψ', hψ', rfl⟩ := hγ
    simp only [hlam]
    rw [S8Cert.q4V_s8 (S7Conj.s7_le_s8 (hΓs7 ψ' hψ')), L14411.matOf_mulVec',
      LinearEquiv.symm_apply_apply, hqΓ ψ' hψ']
  have hlam0 : lam 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    have key : ∀ c : ZMod 2, c = c + c → c = 0 := by decide
    exact key _ this
  have hsingle : ∀ i : Fin 8, lam (Pi.single i 1) = 0 := by
    intro i
    obtain ⟨j, n, hjn⟩ := s7_span_facts i
    set γ : GL (Fin 8) (ZMod 2) := if j = 0 then s7g0 else s7g1 with hγ
    have hγs7 : γ ∈ s7 := by
      rw [hγ]
      split_ifs
      · exact S7Conj.s7g0_mem_s7
      · exact Subgroup.subset_closure (by simp)
    have hvec : Pi.single i (1 : ZMod 2) =
        (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (vec8 n) + vec8 n := by
      rw [← dec8_colsOf (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)), dec8_mulVec, ← vec8_xor, hjn]
      ext k
      fin_cases i <;> fin_cases k <;> rfl
    rw [hvec, hadd, hinv γ hγs7]
    have key : ∀ c : ZMod 2, c + c = 0 := by decide
    exact key _
  have hlamall : ∀ y, lam y = 0 := by
    intro y
    have hsum : ∀ (s : Finset (Fin 8)), lam (∑ i ∈ s, y i • Pi.single i (1 : ZMod 2)) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using hlam0
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, hadd, ih, add_zero]
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (y i) with h | h
        · rw [h, zero_smul, hlam0]
        · rw [h, one_smul, hsingle]
    rw [pi_eq_sum_univ' y]
    exact hsum _
  have hq4 : ∀ v, q v = quadOf q4 (e₁ v) := by
    intro v
    have h1 := hlamall (e₁ v)
    simp only [hlam, LinearEquiv.symm_apply_apply] at h1
    rw [L14411.quadOf_q4]
    have key : ∀ c c' : ZMod 2, c + c' = 0 → c = c' := by decide
    exact key _ _ h1
  refine ⟨e₁, ⟨fun u hu => ?_, fun φ' => ?_⟩, hX8, ?_⟩
  · rw [← hq4, hqU u hu, sq]
  · constructor
    · intro hφ'
      exact ⟨L14411.matOf e₁ φ', hΓs7 φ' hφ', fun v => (L14411.matOf_mulVec e₁ φ' v).symm⟩
    · rintro ⟨γ, hγ, hγv⟩
      rw [← himg] at hγ
      obtain ⟨ψ', hψ', rfl⟩ := hγ
      have : φ' = ψ' := L14411.matOf_injective e₁ ((L14411.matOf_eq_iff e₁ φ' _).mpr hγv)
      rw [this]
      exact hψ'
  ·
    have he₀I : ∀ i ∈ I, S8Cert.InI (e₀ i) := by
      intro i hi
      have h0 : ∀ k : Fin 4, e₀ i (Fin.natAdd 4 k) = 0 := by
        intro k
        rw [he₀, F.coord_apply, Function.comp_apply, S8Tr.e8, finSumFinEquiv_symm_apply_natAdd]
        exact F.iso _ (bI k).2 _ hi
      exact ⟨h0 0, h0 1, h0 2, h0 3⟩
    have he₀I' : ∀ j ∈ I', S8Cert.InIs (e₀ j) := by
      intro j hj
      have h0 : ∀ k : Fin 4, e₀ j (Fin.castAdd 4 k) = 0 := by
        intro k
        rw [he₀, F.coord_apply, Function.comp_apply, S8Tr.e8, finSumFinEquiv_symm_apply_castAdd]
        exact F.iso' _ hj _ (hd k)
      exact ⟨h0 0, h0 1, h0 2, h0 3⟩
    have hv₀ne : v₀ ≠ 0 := fun h => hxv₀ (by rw [h, map_zero]; exact I.zero_mem)
    have hne : ∀ v, v ≠ 0 → e₁ v ≠ 0 := fun v hv h => hv (e₁.injective (h.trans e₁.map_zero.symm))
    have hInIadd : ∀ v w, S8Cert.InI v → S8Cert.InI w → S8Cert.InI (v + w) :=
      fun _ _ => S8Cert.inI_add
    have hInIsadd : ∀ v w, S8Cert.InIs v → S8Cert.InIs w → S8Cert.InIs (v + w) :=
      fun _ _ => S8Cert.inIs_add
    rcases S8Cert.subI_cases hm with hcase | hcase
    ·
      have hcase' : ∀ v, S8Cert.InIs v →
          S8Cert.InIs ((m : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) := by
        rcases S8Cert.subIs_cases hm with h | h
        · exact (S8Cert.not_both hInIadd ⟨_, S8Cert.not_inI_single⟩ hcase h).elim
        · exact h
      refine ⟨x, hxX, v₀, ?_, ?_⟩
      · rw [← S8Cert.inI_iff_mem_subI, he₁v]
        exact hcase _ (he₀I v₀ hv₀I)
      · intro hmem
        rw [← S8Cert.inI_iff_mem_subI, he₁v] at hmem
        have h1 := hcase' _ (he₀I' _ (hxI v₀ hv₀I))
        have h0 := S8Cert.eq_zero_of_inI_inIs hmem h1
        rw [← he₁v] at h0
        exact hne _ (fun h => hv₀ne (by rw [← hxxv v₀, h, map_zero])) h0
    ·
      have hcase' : ∀ v, S8Cert.InIs v →
          S8Cert.InI ((m : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v) := by
        rcases S8Cert.subIs_cases hm with h | h
        · exact h
        · exact (S8Cert.not_both hInIsadd ⟨_, S8Cert.not_inIs_single⟩ hcase h).elim
      refine ⟨x, hxX, x v₀, ?_, ?_⟩
      · rw [← S8Cert.inI_iff_mem_subI, he₁v]
        exact hcase' _ (he₀I' _ (hxI v₀ hv₀I))
      · intro hmem
        rw [hxxv, ← S8Cert.inI_iff_mem_subI, he₁v] at hmem
        have h1 := hcase _ (he₀I v₀ hv₀I)
        have h0 := S8Cert.eq_zero_of_inI_inIs hmem h1
        rw [← he₁v] at h0
        exact hne _ hv₀ne h0

end Ctx

end L1442

end CFSG.Quasithin.H13
