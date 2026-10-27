module

public import CFSG.LocalAnalysis.StandardType.GGF4BstarCoords
public import CFSG.LocalAnalysis.StandardType.GGF4Frame
import CFSG.LocalAnalysis.StandardType.GGF4WeylMat
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace F4Model

section ModP

variable {p : ℕ}

@[expose] def F4Vec.modP (p : ℕ) (v : F4Vec) : Fin 4 → ZMod p := ![v.v0, v.v1, v.v2, v.v3]

@[expose] def f4HighRoot : F4Vec := ⟨2, 3, 4, 2⟩

private theorem sm0_eq : Sm 0 = ⟨-1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩ := rfl
private theorem sm1_eq : Sm 1 = ⟨1, 0, 0, 0, 1, -1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1⟩ := rfl
private theorem sm2_eq : Sm 2 = ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 2, -1, 1, 0, 0, 0, 1⟩ := rfl
private theorem sm3_eq : Sm 3 = ⟨1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, -1⟩ := rfl

theorem sm0_map_mulVec (c : Fin 4 → ZMod p) :
    ((Sm 0).toMat.map (Int.castRingHom (ZMod p))).mulVec c = ![-c 0 + c 1, c 1, c 2, c 3] := by
  rw [sm0_eq]
  ext i
  fin_cases i <;> simp [M4.toMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

theorem sm1_map_mulVec (c : Fin 4 → ZMod p) :
    ((Sm 1).toMat.map (Int.castRingHom (ZMod p))).mulVec c = ![c 0, c 0 - c 1 + c 2, c 2, c 3] := by
  rw [sm1_eq]
  ext i
  fin_cases i
  all_goals simp [M4.toMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem sm2_map_mulVec (c : Fin 4 → ZMod p) :
    ((Sm 2).toMat.map (Int.castRingHom (ZMod p))).mulVec c =
      ![c 0, c 1, 2 * c 1 - c 2 + c 3, c 3] := by
  rw [sm2_eq]
  ext i
  fin_cases i
  all_goals simp [M4.toMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem sm3_map_mulVec (c : Fin 4 → ZMod p) :
    ((Sm 3).toMat.map (Int.castRingHom (ZMod p))).mulVec c = ![c 0, c 1, c 2, c 2 - c 3] := by
  rw [sm3_eq]
  ext i
  fin_cases i
  all_goals simp [M4.toMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

theorem eq_of_sm0_fix {c : Fin 4 → ZMod p}
    (h : ((Sm 0).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c) : c 1 = 2 * c 0 := by
  rw [sm0_map_mulVec] at h
  have h0 : -c 0 + c 1 = c 0 := congrFun h 0
  linear_combination h0

theorem eq_of_sm1_fix {c : Fin 4 → ZMod p}
    (h : ((Sm 1).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c) :
    c 2 = 2 * c 1 - c 0 := by
  rw [sm1_map_mulVec] at h
  have h1 : c 0 - c 1 + c 2 = c 1 := congrFun h 1
  linear_combination h1

theorem eq_of_sm2_fix {c : Fin 4 → ZMod p}
    (h : ((Sm 2).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c) :
    c 3 = 2 * c 2 - 2 * c 1 := by
  rw [sm2_map_mulVec] at h
  have h2 : 2 * c 1 - c 2 + c 3 = c 2 := congrFun h 2
  linear_combination h2

theorem sm1_fix_of_eq {c : Fin 4 → ZMod p} (h : c 2 = 2 * c 1 - c 0) :
    ((Sm 1).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c := by
  rw [sm1_map_mulVec]
  ext i
  fin_cases i
  · rfl
  · show c 0 - c 1 + c 2 = c 1
    linear_combination h
  · rfl
  · rfl

theorem sm2_fix_of_eq {c : Fin 4 → ZMod p} (h : c 3 = 2 * c 2 - 2 * c 1) :
    ((Sm 2).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c := by
  rw [sm2_map_mulVec]
  ext i
  fin_cases i
  · rfl
  · rfl
  · show 2 * c 1 - c 2 + c 3 = c 2
    linear_combination h
  · rfl

theorem sm3_fix_of_eq {c : Fin 4 → ZMod p} (h : c 2 = 2 * c 3) :
    ((Sm 3).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c := by
  rw [sm3_map_mulVec]
  ext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · show c 2 - c 3 = c 3
    linear_combination h

theorem eq_smul_e1_of_fix {c : Fin 4 → ZMod p}
    (h0 : ((Sm 0).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c)
    (h1 : ((Sm 1).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c)
    (h2 : ((Sm 2).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c) :
    c = c 0 • f4E1.modP p := by
  have e0 := eq_of_sm0_fix h0
  have e1 := eq_of_sm1_fix h1
  have e2 := eq_of_sm2_fix h2
  ext i
  fin_cases i
  · show c 0 = c 0 * ((1 : ℤ) : ZMod p)
    simp
  · show c 1 = c 0 * ((2 : ℤ) : ZMod p)
    push_cast
    linear_combination e0
  · show c 2 = c 0 * ((3 : ℤ) : ZMod p)
    push_cast
    linear_combination e1 + 2 * e0
  · show c 3 = c 0 * ((2 : ℤ) : ZMod p)
    push_cast
    linear_combination e2 + 2 * e1 + 2 * e0

@[expose] def IsF4FrameVec (ε : Fin 4 → ZMod p) : Prop :=
  ε = f4E1.modP p ∨ ε = f4E1.neg.modP p ∨ ε = f4E2.modP p ∨ ε = f4E2.neg.modP p

theorem IsF4FrameVec.eqs {ε : Fin 4 → ZMod p} (hε : IsF4FrameVec ε) :
    ε 2 = 2 * ε 1 - ε 0 ∧ ε 3 = 2 * ε 2 - 2 * ε 1 ∧
      (2 * ε 1 - ε 2 - ε 3 = 1 ∨ 2 * ε 1 - ε 2 - ε 3 = -1) := by
  rcases hε with rfl | rfl | rfl | rfl
  · refine ⟨?_, ?_, Or.inr ?_⟩ <;>
      simp [F4Vec.modP, f4E1] <;> norm_num
  · refine ⟨?_, ?_, Or.inl ?_⟩ <;>
      simp [F4Vec.modP, f4E1, F4Vec.neg] <;> norm_num
  · refine ⟨?_, ?_, Or.inl ?_⟩ <;>
      simp [F4Vec.modP, f4E2] <;> norm_num
  · refine ⟨?_, ?_, Or.inr ?_⟩ <;>
      simp [F4Vec.modP, f4E2, F4Vec.neg] <;> norm_num

theorem IsF4FrameVec.exists_decomp {ε c : Fin 4 → ZMod p} (hε : IsF4FrameVec ε)
    (h1 : c 2 = 2 * c 1 - c 0) (h2 : c 3 = 2 * c 2 - 2 * c 1) :
    ∃ X j : ZMod p, c = X • ε + j • f4HighRoot.modP p := by
  rcases hε with rfl | rfl | rfl | rfl
  · refine ⟨2 * c 1 - 3 * c 0, 2 * c 0 - c 1, ?_⟩
    ext i
    fin_cases i <;> simp [F4Vec.modP, f4E1, f4HighRoot]
    · ring
    · ring
    · linear_combination h1
    · linear_combination h2 + 2 * h1
  · refine ⟨-(2 * c 1 - 3 * c 0), 2 * c 0 - c 1, ?_⟩
    ext i
    fin_cases i <;> simp [F4Vec.modP, f4E1, f4HighRoot, F4Vec.neg]
    · ring
    · ring
    · linear_combination h1
    · linear_combination h2 + 2 * h1
  · refine ⟨3 * c 0 - 2 * c 1, c 1 - c 0, ?_⟩
    ext i
    fin_cases i <;> simp [F4Vec.modP, f4E2, f4HighRoot]
    · ring
    · ring
    · linear_combination h1
    · linear_combination h2 + 2 * h1
  · refine ⟨-(3 * c 0 - 2 * c 1), c 1 - c 0, ?_⟩
    ext i
    fin_cases i <;> simp [F4Vec.modP, f4E2, f4HighRoot, F4Vec.neg]
    · ring
    · ring
    · linear_combination h1
    · linear_combination h2 + 2 * h1

theorem IsF4FrameVec.highRoot_ne_smul [Fact p.Prime] (hp2 : p ≠ 2) {ε : Fin 4 → ZMod p}
    (hε : IsF4FrameVec ε) (μ : ZMod p) : f4HighRoot.modP p ≠ μ • ε := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h3 := congrFun h 3
  rcases hε with rfl | rfl | rfl | rfl <;>
    simp [F4Vec.modP, f4E1, f4E2, f4HighRoot, F4Vec.neg] at h0 h1 h3
  · exact one_ne_zero (α := ZMod p) (by linear_combination 2 * h0 - h1)
  · exact one_ne_zero (α := ZMod p) (by linear_combination 2 * h0 - h1)
  · exact zmod_two_ne_zero hp2 h3
  · exact zmod_two_ne_zero hp2 h3

theorem F4Vec.modP_apply (v : F4Vec) (i : Fin 4) : v.modP p i = (v.toFun i : ZMod p) := by
  fin_cases i <;> rfl

theorem highRoot_short_minor : ∀ s ∈ f4ShortOrb, ∃ i ∈ ([0, 1, 2, 3] : List (Fin 4)),
    ∃ j ∈ ([0, 1, 2, 3] : List (Fin 4)),
      f4HighRoot.toFun i * s.toFun j - f4HighRoot.toFun j * s.toFun i ∈
        ([1, -1, 2, -2, 4, -4, 8, -8] : List ℤ) := by
  decide +kernel

theorem highRoot_ne_smul_short [Fact p.Prime] (hp2 : p ≠ 2) {s : F4Vec} (hs : s ∈ f4ShortOrb)
    (μ : ZMod p) : f4HighRoot.modP p ≠ μ • s.modP p := by
  intro h
  obtain ⟨i, -, j, -, hm⟩ := highRoot_short_minor s hs
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.smul_apply, smul_eq_mul, F4Vec.modP_apply] at hi hj
  set m : ℤ := f4HighRoot.toFun i * s.toFun j - f4HighRoot.toFun j * s.toFun i with hmdef
  have hm0 : (m : ZMod p) = 0 := by
    rw [hmdef]
    push_cast
    rw [hi, hj]
    ring
  have hm8 : m ∣ 8 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  obtain ⟨c, hc⟩ := hm8
  have h8 : ((8 : ℤ) : ZMod p) = 0 := by rw [hc]; push_cast; rw [hm0, zero_mul]
  have h2 : (2 : ZMod p) ^ 3 = 0 := by
    have : ((8 : ℤ) : ZMod p) = (2 : ZMod p) ^ 3 := by norm_num
    rw [← this, h8]
  exact zmod_two_ne_zero hp2 (pow_eq_zero_iff (by norm_num) |>.mp h2)

theorem highRoot_fix :
    ((Sm 1).toMat.map (Int.castRingHom (ZMod p))).mulVec (f4HighRoot.modP p) =
        f4HighRoot.modP p ∧
      ((Sm 2).toMat.map (Int.castRingHom (ZMod p))).mulVec (f4HighRoot.modP p) =
        f4HighRoot.modP p ∧
      ((Sm 3).toMat.map (Int.castRingHom (ZMod p))).mulVec (f4HighRoot.modP p) =
        f4HighRoot.modP p := by
  refine ⟨sm1_fix_of_eq ?_, sm2_fix_of_eq ?_, sm3_fix_of_eq ?_⟩ <;>
    simp [F4Vec.modP, f4HighRoot] <;> norm_num

end ModP

section RhoMod

variable {W : Type} [Group W] {n S : Type} [Fintype n] [DecidableEq n] [CommRing S]

theorem monoidHom_inv_mulVec_mulVec (π : W →* Matrix n n S) (g : W) (c : n → S) :
    (π g⁻¹).mulVec ((π g).mulVec c) = c := by
  rw [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem monoidHom_mulVec_inv_mulVec (π : W →* Matrix n n S) (g : W) (c : n → S) :
    (π g).mulVec ((π g⁻¹).mulVec c) = c := by
  rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]

theorem monoidHom_mul_mulVec (π : W →* Matrix n n S) (g h : W) (c : n → S) :
    (π (g * h)).mulVec c = (π g).mulVec ((π h).mulVec c) := by
  rw [map_mul, Matrix.mulVec_mulVec]

theorem monoidHom_conj_fix_iff (π : W →* Matrix n n S) (g z : W) (c : n → S) :
    (π (g * z * g⁻¹)).mulVec c = c ↔
      (π z).mulVec ((π g⁻¹).mulVec c) = (π g⁻¹).mulVec c := by
  rw [monoidHom_mul_mulVec, monoidHom_mul_mulVec]
  constructor
  · intro h
    rw [← monoidHom_inv_mulVec_mulVec π g ((π z).mulVec ((π g⁻¹).mulVec c)), h]
  · intro h
    rw [h, monoidHom_mulVec_inv_mulVec]

end RhoMod

end F4Model

open F4Model

theorem exists_bstarFrame_at {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hEl : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hcard : Nat.card ↥Bs ≤ p ^ 4) {A : Subgroup (MulAut ↥Bs)} (hind : A ≤ ggInduced ⊤ Bs)
    (e : CoxeterMatrix.F₄.Group ≃* ↥A)
    (he : ∀ i : Fin 4, GGIsReflection p ((e (CoxeterMatrix.F₄.simple i) : ↥A) : MulAut ↥Bs))
    (R : F4Rep CoxeterMatrix.F₄.Group) (hRs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i)
    {AL : Subgroup (MulAut ↥Bs)} {a : Fin 3 → CoxeterMatrix.F₄.Group}
    (haL : ∀ z, z ∈ Subgroup.closure (Set.range a) → ((e z : ↥A) : MulAut ↥Bs) ∈ AL)
    {ga : CoxeterMatrix.F₄.Group}
    (hga : ga * a 0 * ga⁻¹ = R.s 0 ∧ ga * a 1 * ga⁻¹ = R.s 1 ∧ ga * a 2 * ga⁻¹ = R.s 2)
    {x : ↥Bs} (hx1 : x ≠ 1) (hxL : ∀ φ ∈ AL, φ x = x) (w₂ : CoxeterMatrix.F₄.Group)
    (hv : (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E1.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E1.neg.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E2.toFun ∨
      (R.ρ (ga * w₂)⁻¹).mulVec f4E1.toFun = f4E2.neg.toFun) :
    ∃ d : ↥Bs,
      ((e (w₂ * R.s 2 * w₂⁻¹) : ↥A) : MulAut ↥Bs) x = x ∧
      ((e (w₂ * R.s 1 * w₂⁻¹) : ↥A) : MulAut ↥Bs) x = x ∧
      ((e (w₂ * R.s 2 * w₂⁻¹) : ↥A) : MulAut ↥Bs) d = d ∧
      ((e (w₂ * R.s 1 * w₂⁻¹) : ↥A) : MulAut ↥Bs) d = d ∧
      ((e (w₂ * R.s 3 * w₂⁻¹) : ↥A) : MulAut ↥Bs) d = d ∧
      (∀ z : ↥Bs, ((e (w₂ * R.s 2 * w₂⁻¹) : ↥A) : MulAut ↥Bs) z = z →
        ((e (w₂ * R.s 1 * w₂⁻¹) : ↥A) : MulAut ↥Bs) z = z → ∃ i j : ℕ, z = x ^ i * d ^ j) ∧
      ((e (w₂ * R.s 2 * w₂⁻¹) : ↥A) : MulAut ↥Bs)
          (((e (w₂ * R.s 3 * w₂⁻¹) : ↥A) : MulAut ↥Bs) x) ≠
        ((e (w₂ * R.s 3 * w₂⁻¹) : ↥A) : MulAut ↥Bs) x ∧
      (∃ φ ∈ AL, φ d ≠ d) ∧
      ∀ (v : CoxeterMatrix.F₄.Group) (k : ℕ), ((e v : ↥A) : MulAut ↥Bs) d ≠ x ^ k := by
  classical
  obtain ⟨Ψ, hΨ⟩ := exists_bstar_f4Coords hp2 hEl hNT hcard hind e he R hRs
  set π : CoxeterMatrix.F₄.Group →* Matrix (Fin 4) (Fin 4) (ZMod p) :=
    (Int.castRingHom (ZMod p)).mapMatrix.toMonoidHom.comp R.ρ with hπ
  have hπs : ∀ k, π (R.s k) = (Sm k).toMat.map (Int.castRingHom (ZMod p)) := fun k => by
    rw [← R.hs k]
    rfl
  set ι : CoxeterMatrix.F₄.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom with hι
  have hι : ∀ w, ι w = ((e w : ↥A) : MulAut ↥Bs) := fun w => rfl
  set κ : ↥Bs → (Fin 4 → ZMod p) := fun z => Multiplicative.toAdd (Ψ.symm z) with hκ
  have hκΨ : ∀ z, Ψ (Multiplicative.ofAdd (κ z)) = z := fun z => by
    simp only [hκ, ofAdd_toAdd, MulEquiv.apply_symm_apply]
  have hκ_apply : ∀ c, κ (Ψ (Multiplicative.ofAdd c)) = c := fun c => by
    simp only [hκ, MulEquiv.symm_apply_apply, toAdd_ofAdd]
  have hκinj : Function.Injective κ := fun z z' h => by rw [← hκΨ z, h, hκΨ]
  have hκact : ∀ w z, κ (ι w z) = (π w).mulVec (κ z) := by
    intro w z
    conv_lhs => rw [← hκΨ z]
    rw [show ι w (Ψ (Multiplicative.ofAdd (κ z))) =
      Ψ (Multiplicative.ofAdd ((π w).mulVec (κ z))) from hΨ w (κ z), hκ_apply]
  have hfix : ∀ w z, ι w z = z ↔ (π w).mulVec (κ z) = κ z := by
    intro w z
    rw [← hκinj.eq_iff, hκact]
  have hfixS : ∀ (w : CoxeterMatrix.F₄.Group) (k : Fin 4) (z : ↥Bs),
      ι (w * R.s k * w⁻¹) z = z ↔
        ((Sm k).toMat.map (Int.castRingHom (ZMod p))).mulVec ((π w⁻¹).mulVec (κ z)) =
          (π w⁻¹).mulVec (κ z) := by
    intro w k z
    rw [hfix, monoidHom_conj_fix_iff, hπs]
  have hB : ∀ z : ↥Bs, (∀ k : Fin 3, ι (a k) z = z) →
      κ z = ((π ga).mulVec (κ z)) 0 • (π ga⁻¹).mulVec (f4E1.modP p) := by
    intro z hz
    have hk : ∀ k : Fin 4, k ≠ 3 → ∀ j : Fin 3, ga * a j * ga⁻¹ = R.s k →
        ((Sm k).toMat.map (Int.castRingHom (ZMod p))).mulVec ((π ga).mulVec (κ z)) =
          (π ga).mulVec (κ z) := by
      intro k _ j hj
      have h1 := hz j
      rw [show a j = ga⁻¹ * R.s k * ga⁻¹⁻¹ by rw [← hj]; group, hfixS, inv_inv] at h1
      exact h1
    have hc := eq_smul_e1_of_fix (hk 0 (by decide) 0 hga.1) (hk 1 (by decide) 1 hga.2.1)
      (hk 2 (by decide) 2 hga.2.2)
    calc κ z = (π ga⁻¹).mulVec ((π ga).mulVec (κ z)) := (monoidHom_inv_mulVec_mulVec π ga _).symm
      _ = _ := by rw [← Matrix.mulVec_smul, ← hc]
  have haLk : ∀ k : Fin 3, ι (a k) ∈ AL := fun k =>
    haL (a k) (Subgroup.subset_closure ⟨k, rfl⟩)
  set lx : ZMod p := ((π ga).mulVec (κ x)) 0 with hlx
  have hcx : κ x = lx • (π ga⁻¹).mulVec (f4E1.modP p) := hB x fun k => hxL _ (haLk k)
  have hlx0 : lx ≠ 0 := by
    intro h0
    apply hx1
    rw [← hκΨ x, hcx, h0, zero_smul, ofAdd_zero, map_one]
  set ε : Fin 4 → ZMod p := (π (ga * w₂)⁻¹).mulVec (f4E1.modP p) with hεdef
  have hcast : ∀ (g : CoxeterMatrix.F₄.Group) (v v' : F4Vec),
      (R.ρ g).mulVec v.toFun = v'.toFun → (π g).mulVec (v.modP p) = v'.modP p := by
    intro g v v' h
    ext i
    have h1 := RingHom.map_mulVec (Int.castRingHom (ZMod p)) (R.ρ g) v.toFun i
    have hv : (Int.castRingHom (ZMod p)) ∘ v.toFun = v.modP p := by
      ext j
      fin_cases j <;> rfl
    rw [h, hv] at h1
    change ((R.ρ g).map (Int.castRingHom (ZMod p))).mulVec (v.modP p) i = v'.modP p i
    rw [← h1]
    fin_cases i <;> rfl
  have hε : IsF4FrameVec ε := by
    rcases hv with h | h | h | h
    · exact Or.inl (hcast _ _ _ h)
    · exact Or.inr (Or.inl (hcast _ _ _ h))
    · exact Or.inr (Or.inr (Or.inl (hcast _ _ _ h)))
    · exact Or.inr (Or.inr (Or.inr (hcast _ _ _ h)))
  obtain ⟨hε1, hε2, hε3⟩ := hε.eqs
  have hFx : (π w₂⁻¹).mulVec (κ x) = lx • ε := by
    rw [hcx, Matrix.mulVec_smul, ← monoidHom_mul_mulVec, ← mul_inv_rev]
  set d : ↥Bs := Ψ (Multiplicative.ofAdd ((π w₂).mulVec (f4HighRoot.modP p))) with hd
  have hFd : (π w₂⁻¹).mulVec (κ d) = f4HighRoot.modP p := by
    rw [hd, hκ_apply, monoidHom_inv_mulVec_mulVec]
  obtain ⟨hθ1, hθ2, hθ3⟩ := highRoot_fix (p := p)
  have hsm_smul : ∀ (k : Fin 4) (c : Fin 4 → ZMod p),
      ((Sm k).toMat.map (Int.castRingHom (ZMod p))).mulVec c = c →
        ((Sm k).toMat.map (Int.castRingHom (ZMod p))).mulVec (lx • c) = lx • c := by
    intro k c h
    rw [Matrix.mulVec_smul, h]
  refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [← hι, hfixS, hFx]
    exact hsm_smul 2 ε (sm2_fix_of_eq hε2)
  ·
    rw [← hι, hfixS, hFx]
    exact hsm_smul 1 ε (sm1_fix_of_eq hε1)
  ·
    rw [← hι, hfixS, hFd]
    exact hθ2
  ·
    rw [← hι, hfixS, hFd]
    exact hθ1
  ·
    rw [← hι, hfixS, hFd]
    exact hθ3
  ·
    intro z hrz huz
    rw [← hι, hfixS] at hrz huz
    obtain ⟨X, j, hXj⟩ := hε.exists_decomp (eq_of_sm1_fix huz) (eq_of_sm2_fix hrz)
    set i : ZMod p := X * lx⁻¹ with hi
    have hF : (π w₂⁻¹).mulVec (κ z) =
        i • (π w₂⁻¹).mulVec (κ x) + j • (π w₂⁻¹).mulVec (κ d) := by
      rw [hXj, hFx, hFd, smul_smul, hi, inv_mul_cancel_right₀ hlx0]
    have hz : κ z = i • κ x + j • κ d := by
      rw [← monoidHom_mulVec_inv_mulVec π w₂ (κ z), hF, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_smul, monoidHom_mulVec_inv_mulVec, monoidHom_mulVec_inv_mulVec]
    have hnat : ∀ (m : ZMod p) (c : Fin 4 → ZMod p), m • c = m.val • c := by
      intro m c
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) m.val c, ZMod.natCast_zmod_val]
    refine ⟨i.val, j.val, ?_⟩
    rw [← hκΨ z, hz, hnat i, hnat j, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow,
      map_pow, hκΨ, hκΨ]
  ·
    intro h
    rw [← hι, ← hι, hfixS, hκact, ← monoidHom_mul_mulVec,
      show w₂⁻¹ * (w₂ * R.s 3 * w₂⁻¹) = R.s 3 * w₂⁻¹ by group, monoidHom_mul_mulVec, hFx,
      hπs] at h
    have h3' := eq_of_sm2_fix h
    rw [sm3_map_mulVec] at h3'
    have h3'' : lx * ε 2 - lx * ε 3 = 2 * (lx * ε 2) - 2 * (lx * ε 1) := h3'
    rcases hε3 with h1 | h1
    · exact hlx0 (by linear_combination h3'' - lx * h1)
    · exact hlx0 (by linear_combination -h3'' + lx * h1)
  ·
    by_contra hall
    push Not at hall
    have hcd := hB d fun k => hall _ (haLk k)
    set μ : ZMod p := ((π ga).mulVec (κ d)) 0 with hμ
    apply hε.highRoot_ne_smul hp2 μ
    rw [← hFd, hcd, Matrix.mulVec_smul, ← monoidHom_mul_mulVec, ← mul_inv_rev, ← hεdef]
  ·
    intro v k hvk
    have hκx : κ (x ^ k) = (k : ZMod p) • κ x := by
      rw [hκ]
      dsimp only
      rw [map_pow, toAdd_pow, ← Nat.cast_smul_eq_nsmul (ZMod p)]
    have h1 := congrArg κ hvk
    rw [← hι, hκact, hκx, hcx] at h1
    have hκd : κ d = (π w₂).mulVec (f4HighRoot.modP p) := by rw [hd, hκ_apply]
    obtain ⟨s, hs, hsv, -⟩ := R.exists_orbit (ga * (v * w₂))⁻¹
    have hs' : (π (ga * (v * w₂))⁻¹).mulVec (f4E1.modP p) = s.modP p := hcast _ _ _ hsv
    apply highRoot_ne_smul_short hp2 hs ((k : ZMod p) * lx)
    calc f4HighRoot.modP p
        = (π (v * w₂)⁻¹).mulVec ((π (v * w₂)).mulVec (f4HighRoot.modP p)) :=
          (monoidHom_inv_mulVec_mulVec π _ _).symm
      _ = (π (v * w₂)⁻¹).mulVec ((π v).mulVec (κ d)) := by rw [monoidHom_mul_mulVec, hκd]
      _ = (π (v * w₂)⁻¹).mulVec ((k : ZMod p) • lx • (π ga⁻¹).mulVec (f4E1.modP p)) := by
          rw [h1]
      _ = ((k : ZMod p) * lx) • (π (ga * (v * w₂))⁻¹).mulVec (f4E1.modP p) := by
          rw [smul_smul, Matrix.mulVec_smul, ← monoidHom_mul_mulVec, ← mul_inv_rev]
      _ = ((k : ZMod p) * lx) • s.modP p := by rw [hs']

end CFSG.StandardType

end
