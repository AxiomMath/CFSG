module

public import CFSG.RankThree.GF2n.Stroth80.Sec715TriSpin
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriOctFam
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.RankThree.GF2n.Stroth80.Tri

open CFSG.LieType.D4Small Module
open scoped Matrix

theorem swap_inj {m n : Fin 4 ⊕ Fin 4} (h : m.swap = n.swap) : m = n := by
  simpa using congrArg Sum.swap h

section Oct

variable {K : Type*} [CommRing K]

theorem octNorm_smul (c : K) (x : Oct K) : octNorm (c • x) = c * c * octNorm x := by
  simp only [octNorm, octA_smul, octB_smul, octU_smul, octW_smul, dot3]
  ring

@[expose] def octQuad (K : Type*) [CommRing K] : QuadraticForm K (Oct K) where
  toFun := octNorm
  toFun_smul c x := by rw [smul_eq_mul]; exact octNorm_smul c x
  exists_companion' := ⟨octPolarBil, fun x y => by rw [octPolarBil_apply, octPolar]; ring⟩

@[simp] theorem octQuad_apply (x : Oct K) : octQuad K x = octNorm x := rfl

end Oct

section CharTwo

variable {K : Type*} [CommRing K] [CharP K 2]

theorem octNorm_eq_sum (x : Oct K) : octNorm x = ∑ k : Fin 4, x (.inl k) * x (.inr k) := by
  rw [Fin.sum_univ_succ]
  simp only [octNorm, Fin.sum_univ_three, dot3, octA, octB, octU, octW, CharTwo.sub_eq_add]

theorem octPolar_eq_sum (x y : Oct K) :
    octPolar x y = ∑ m : Fin 4 ⊕ Fin 4, x m * y m.swap := by
  rw [octPolar_eq_char2, Fintype.sum_sum_type]
  simp only [Sum.swap_inl, Sum.swap_inr, Finset.sum_add_distrib, mul_comm (y (.inl _)) (x (.inr _))]

theorem octPolar_single_single (m n : Fin 4 ⊕ Fin 4) :
    octPolar (Pi.single m 1 : Oct K) (Pi.single n 1) = if n = m.swap then 1 else 0 := by
  rw [octPolar_eq_sum, Finset.sum_eq_single m]
  · rw [Pi.single_eq_same, one_mul, Pi.single_apply]
    exact if_congr eq_comm rfl rfl
  · intro p _ hp
    rw [Pi.single_eq_of_ne hp, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ m) h

theorem octNorm_single (m : Fin 4 ⊕ Fin 4) : octNorm (Pi.single m 1 : Oct K) = 0 := by
  rw [octNorm_eq_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : m = .inl k
  · subst h
    simp [Pi.single_apply]
  · rw [Pi.single_eq_of_ne (Ne.symm h), zero_mul]

end CharTwo

section Unipotent

variable {K : Type*} [Field K] [CharP K 2]

@[expose] def stepMat (R : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Prop) [DecidableRel R] :
    Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K :=
  Matrix.of fun m' m => if R m m' then 1 else 0

theorem stepMat_mulVec_apply (R : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Prop) [DecidableRel R]
    (y : Oct K) (m' : Fin 4 ⊕ Fin 4) :
    (stepMat R *ᵥ y) m' = ∑ m, if R m m' then y m else 0 := by
  simp only [Matrix.mulVec, dotProduct, stepMat, Matrix.of_apply, ite_mul, one_mul, zero_mul]

theorem octNorm_add_smul_stepMat (R : Fin 4 ⊕ Fin 4 → Fin 4 ⊕ Fin 4 → Prop) [DecidableRel R]
    (hR2 : ∀ m, ¬ R m m.swap) (hR3 : ∀ m n, R n m.swap ↔ R m n.swap)
    (hR4 : ∀ m₁ m₂ n, ¬ (R m₁ n ∧ R m₂ n.swap)) (c : K) (y : Oct K) :
    octNorm (y + c • (stepMat R *ᵥ y)) = octNorm y := by
  set w : Oct K := stepMat R *ᵥ y with hw
  have hwapp : ∀ m', w m' = ∑ m, if R m m' then y m else 0 :=
    fun m' => stepMat_mulVec_apply R y m'
  have h1 : octNorm w = 0 := by
    rw [octNorm_eq_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : ∃ m, R m (.inl k)
    · obtain ⟨m₁, hm₁⟩ := h
      have : w (.inr k) = 0 := by
        rw [hwapp]
        refine Finset.sum_eq_zero fun m _ => ?_
        exact if_neg (fun hm => hR4 m₁ m (.inl k) ⟨hm₁, hm⟩)
      rw [this, mul_zero]
    · push Not at h
      have : w (.inl k) = 0 := by
        rw [hwapp]
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [if_neg (h m)]
      rw [this, zero_mul]
  have h2 : octPolar y w = 0 := by
    rw [octPolar_eq_sum]
    simp only [hwapp, Finset.mul_sum]
    rw [← Finset.sum_product' Finset.univ Finset.univ
      (fun m n => y m * if R n m.swap then y n else 0)]
    refine Finset.sum_ninvolution (fun p => (p.2, p.1)) ?_ ?_ (fun p => Finset.mem_univ _)
      (fun p => rfl)
    · rintro ⟨m, n⟩
      by_cases h : R n m.swap
      · have h' : R m n.swap := (hR3 m n).1 h
        simp only [if_pos h, if_pos h']
        rw [mul_comm (y n) (y m)]
        exact CharTwo.add_self_eq_zero _
      · have h' : ¬ R m n.swap := fun h' => h ((hR3 m n).2 h')
        simp only [if_neg h, if_neg h', mul_zero, add_zero]
    · rintro ⟨m, n⟩ hf hg
      have hnm : n = m := (Prod.mk.inj hg).1
      subst hnm
      exact hf (by simp only [if_neg (hR2 n), mul_zero])
  rw [octNorm_add, octNorm_smul, octPolar_smul_right, h1, h2]
  ring

end Unipotent

section Module

attribute [local instance] Fintype.ofFinite Classical.propDecidable

variable {G : Type*} [Group G] {K : Type*} [Field K] [Finite K] [CharP K 2]
  {X : Type*} [AddCommGroup X] [Module K X]
  {D : D4Datum G K} {ρ : Representation K G X} {e : ℕ} {b₀ : ZMod (Nat.card Kˣ)}
  {C : Finset (Fin 4 → ZMod (Nat.card Kˣ))} {b : (Fin 4 → ZMod (Nat.card Kˣ)) → X}

theorem exists_wtChar_ne_one {a : Fin 4 → ZMod (Nat.card Kˣ)} (ha : a ≠ 0) :
    ∃ t : Fin 4 → Kˣ, ((D4Datum.wtChar a t : Kˣ) : K) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have h := D4Datum.sum_wtChar (K := K) a
  simp only [hcon, ha, if_false, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
  have hcard : Fintype.card (Fin 4 → Kˣ) = Nat.card Kˣ ^ 4 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 4),
      Fintype.card_fin]
  rw [hcard, Nat.cast_pow, D4Datum.natCard_units_cast_eq_one, one_pow] at h
  exact one_ne_zero h

theorem polar_invariant_of_invariant {q : QuadraticForm K X}
    (hq : ∀ (g : G) (x : X), q (ρ g x) = q x) (g : G) (x y : X) :
    QuadraticMap.polar q (ρ g x) (ρ g y) = QuadraticMap.polar q x y := by
  simp only [QuadraticMap.polar, ← map_add, hq]

variable (hN : SpinNF D ρ e b₀ C b) (L : ZLab e)

include hN

theorem SpinNF.equiv_root {i j : Fin 4} (hij : i ≠ j) (u v : Bool) (c : K) (x : X) :
    hN.equiv L (ρ (D.x (rootZ i j u v) c) x) =
      hN.equiv L x + c • (stepMat (L.Rel i j u v) *ᵥ hN.equiv L x) := by
  have h : (hN.equiv L).toLinearMap ∘ₗ (ρ (D.x (rootZ i j u v) c)) =
      (hN.equiv L).toLinearMap +
        c • ((Matrix.mulVecLin (stepMat (L.Rel i j u v))) ∘ₗ (hN.equiv L).toLinearMap) := by
    refine (hN.basis L).ext fun m => ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply,
      LinearMap.smul_apply, Matrix.mulVecLin_apply, hN.equiv_basis L]
    by_cases hex : ∃ m', L.Rel i j u v m m'
    · obtain ⟨m', hm'⟩ := hex
      rw [hN.root_apply_of_rel L hij hm' c, map_add, map_smul, hN.equiv_basis L,
        hN.equiv_basis L]
      congr 2
      rw [Matrix.mulVec_single_one]
      funext m''
      rw [Matrix.col_apply, stepMat, Matrix.of_apply, Pi.single_apply]
      exact if_congr ⟨fun h' => by rw [h']; exact hm', fun h' => (hm'.unique h').symm⟩ rfl rfl
    · push Not at hex
      rw [hN.root_apply_of_not_rel L hij hex c]
      have : stepMat (L.Rel i j u v) *ᵥ (Pi.single m 1 : Fin 4 ⊕ Fin 4 → K) = 0 := by
        rw [Matrix.mulVec_single_one]
        funext m''
        rw [Matrix.col_apply, stepMat, Matrix.of_apply, if_neg (hex m'')]
        rfl
      rw [hN.equiv_basis L, this, smul_zero, add_zero]
  have := LinearMap.congr_fun h x
  simpa using this

theorem SpinNF.octNorm_equiv_root {i j : Fin 4} (hij : i ≠ j) (u v : Bool) (c : K) (x : X) :
    octNorm (hN.equiv L (ρ (D.x (rootZ i j u v) c) x)) = octNorm (hN.equiv L x) := by
  rw [hN.equiv_root L hij u v c x]
  refine octNorm_add_smul_stepMat (L.Rel i j u v) ?_ ?_ ?_ c _
  · intro m hm
    unfold ZLab.Rel at hm
    rw [L.swap] at hm
    exact SignVec.step_ne_neg i j u v (L.lab m) hij hm
  · intro m n
    have h := SignVec.step_neg_iff i j u v (L.lab m) (L.lab n) hij
    unfold ZLab.Rel
    rwa [L.swap, L.swap]
  · rintro m₁ m₂ n ⟨h1, h2⟩
    unfold ZLab.Rel at h1 h2
    rw [L.swap] at h2
    exact SignVec.step_not_both hij ⟨h1, h2⟩

theorem SpinNF.octNorm_equiv_invariant (g : G) (x : X) :
    octNorm (hN.equiv L (ρ g x)) = octNorm (hN.equiv L x) := by
  let H : Subgroup G :=
    { carrier := {g | ∀ x, octNorm (hN.equiv L (ρ g x)) = octNorm (hN.equiv L x)}
      mul_mem' := fun {a b} ha hb x => by
        rw [map_mul, Module.End.mul_apply, ha, hb]
      one_mem' := fun x => by rw [map_one, Module.End.one_apply]
      inv_mem' := fun {a} ha x => by
        have h := ha (ρ a⁻¹ x)
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] at h
        exact h.symm }
  have hH : H = ⊤ := by
    rw [eq_top_iff, ← D.closure_eq, Subgroup.closure_le]
    rintro g ⟨α, hα, c, rfl⟩ x
    obtain ⟨i, j, u, v, hij, rfl⟩ := exists_rootZ hα
    exact hN.octNorm_equiv_root L hij u v c x
  have hg : g ∈ H := hH ▸ Subgroup.mem_top g
  exact hg x

@[expose] noncomputable def SpinNF.quad : QuadraticForm K X :=
  (octQuad K).comp (hN.equiv L).toLinearMap

theorem SpinNF.quad_invariant (g : G) (x : X) : hN.quad L (ρ g x) = hN.quad L x :=
  hN.octNorm_equiv_invariant L g x

variable {q : QuadraticForm K X}

theorem SpinNF.polar_eq_zero_of_ne_swap (hq : ∀ (g : G) (x : X), q (ρ g x) = q x)
    {m n : Fin 4 ⊕ Fin 4} (hmn : n ≠ m.swap) :
    QuadraticMap.polar q (hN.basis L m) (hN.basis L n) = 0 := by
  haveI := hN.nontrivial
  have hne : hsWeight b₀ (L.lab m) + hsWeight b₀ (L.lab n) ≠ 0 := by
    intro h
    rw [hsWeight_add_eq_zero_iff hN.two_mul] at h
    apply hmn
    apply L.injective
    rw [h, L.swap]
  obtain ⟨t, ht⟩ := exists_wtChar_ne_one (K := K) hne
  have h1 := polar_invariant_of_invariant hq (D.h t) (hN.basis L m) (hN.basis L n)
  rw [hN.torus_apply L, hN.torus_apply L, QuadraticMap.polar_smul_left,
    QuadraticMap.polar_smul_right, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← Units.val_mul, ← D4Datum.wtChar_add] at h1
  have h2 : (((D4Datum.wtChar (hsWeight b₀ (L.lab m) + hsWeight b₀ (L.lab n)) t : Kˣ) : K) - 1) *
      QuadraticMap.polar q (hN.basis L m) (hN.basis L n) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h) ht
  · exact h

theorem SpinNF.eq_zero_of_invariant (hq : ∀ (g : G) (x : X), q (ρ g x) = q x)
    (m : Fin 4 ⊕ Fin 4) : q (hN.basis L m) = 0 := by
  haveI := hN.nontrivial
  have hne : hsWeight b₀ (L.lab m) + hsWeight b₀ (L.lab m) ≠ 0 :=
    hsWeight_add_self_ne_zero hN.two_mul _
  obtain ⟨t, ht⟩ := exists_wtChar_ne_one (K := K) hne
  have h1 := hq (D.h t) (hN.basis L m)
  rw [hN.torus_apply L, QuadraticMap.map_smul, smul_eq_mul, ← Units.val_mul,
    ← D4Datum.wtChar_add] at h1
  have h2 : (((D4Datum.wtChar (hsWeight b₀ (L.lab m) + hsWeight b₀ (L.lab m)) t : Kˣ) : K) - 1) *
      q (hN.basis L m) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h) ht
  · exact h

theorem SpinNF.polar_swap_eq_of_rel (hq : ∀ (g : G) (x : X), q (ρ g x) = q x) {i j : Fin 4}
    (hij : i ≠ j) {u v : Bool} {m m' : Fin 4 ⊕ Fin 4} (h : L.Rel i j u v m m') :
    QuadraticMap.polar q (hN.basis L m) (hN.basis L m.swap) =
      QuadraticMap.polar q (hN.basis L m') (hN.basis L m'.swap) := by
  have hrel : L.Rel i j u v m'.swap m.swap := by
    have := SignVec.step_neg_neg i j u v (L.lab m) (L.lab m') hij h
    unfold ZLab.Rel
    rwa [L.swap, L.swap]
  have hne : m ≠ m' := by
    rintro rfl
    exact SignVec.step_ne_self i j u v (L.lab m) (L.lab m) hij h rfl
  have h1 := polar_invariant_of_invariant hq (D.x (rootZ i j u v) 1) (hN.basis L m)
    (hN.basis L m'.swap)
  rw [hN.root_apply_of_rel L hij h, hN.root_apply_of_rel L hij hrel] at h1
  simp only [one_smul, QuadraticMap.polar_add_left, QuadraticMap.polar_add_right] at h1
  rw [hN.polar_eq_zero_of_ne_swap L hq (m := m) (n := m'.swap)
      (fun h' => hne (swap_inj h').symm),
    hN.polar_eq_zero_of_ne_swap L hq (m := m') (n := m.swap)
      (fun h' => hne (swap_inj h')), zero_add, add_zero] at h1
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination h1 - QuadraticMap.polar q (hN.basis L m') (hN.basis L m'.swap) * h2

theorem SpinNF.polar_swap_const (hq : ∀ (g : G) (x : X), q (ρ g x) = q x)
    (m m' : Fin 4 ⊕ Fin 4) :
    QuadraticMap.polar q (hN.basis L m) (hN.basis L m.swap) =
      QuadraticMap.polar q (hN.basis L m') (hN.basis L m'.swap) := by
  rcases SignVec.step_conn (L.lab m) (L.lab m')
      (by rw [L.minusCount_mod m, L.minusCount_mod m']) with
    h | ⟨i, j, u, v, hij, h⟩ | ⟨s'', ⟨i, j, u, v, hij, h1⟩, ⟨i', j', u', v', hij', h2⟩⟩
  · rw [L.injective h]
  · exact hN.polar_swap_eq_of_rel L hq hij h
  · have hs'' : s''.minusCount % 2 = e % 2 := by
      rw [← L.minusCount_mod m]
      exact SignVec.step_minusCount_mod i j u v _ _ hij h1
    obtain ⟨m'', rfl⟩ := L.surjective s'' hs''
    exact (hN.polar_swap_eq_of_rel L hq hij h1).trans (hN.polar_swap_eq_of_rel L hq hij' h2)

theorem SpinNF.exists_eq_mul_octNorm (hq : ∀ (g : G) (x : X), q (ρ g x) = q x) :
    ∃ μ : K, ∀ x, q x = μ * octNorm (hN.equiv L x) := by
  set μ : K := QuadraticMap.polar q (hN.basis L (.inl 0)) (hN.basis L (Sum.inl 0).swap) with hμ
  have hbasis : ∀ m n, QuadraticMap.polar q (hN.basis L m) (hN.basis L n) =
      μ * octPolar (Pi.single m 1 : Oct K) (Pi.single n 1) := by
    intro m n
    rw [octPolar_single_single]
    by_cases hn : n = m.swap
    · subst hn
      rw [if_pos rfl, mul_one, hμ]
      exact hN.polar_swap_const L hq m (.inl 0)
    · rw [if_neg hn, mul_zero]
      exact hN.polar_eq_zero_of_ne_swap L hq hn
  have hbil : ∀ x y, QuadraticMap.polar q x y = μ * octPolar (hN.equiv L x) (hN.equiv L y) := by
    intro x y
    have hB : QuadraticMap.polarBilin q =
        μ • (octPolarBil.compl₁₂ (hN.equiv L).toLinearMap (hN.equiv L).toLinearMap) :=
      LinearMap.ext_basis (hN.basis L) (hN.basis L) fun m n => by
        simp [hbasis, hN.equiv_basis L]
    have := LinearMap.congr_fun₂ hB x y
    simpa using this
  let d : X →+ K := AddMonoidHom.mk' (fun x => q x - μ * octNorm (hN.equiv L x)) (fun x y => by
    rw [QuadraticMap.map_add q x y, hbil x y, map_add, octNorm_add]
    ring)
  have hd_smul : ∀ (c : K) (x : X), d (c • x) = c * c * d x := by
    intro c x
    show q (c • x) - μ * octNorm (hN.equiv L (c • x)) =
      c * c * (q x - μ * octNorm (hN.equiv L x))
    rw [QuadraticMap.map_smul, smul_eq_mul, map_smul, octNorm_smul]
    ring
  have hd_basis : ∀ m, d (hN.basis L m) = 0 := by
    intro m
    show q (hN.basis L m) - μ * octNorm (hN.equiv L (hN.basis L m)) = 0
    rw [hN.equiv_basis L, octNorm_single, mul_zero, sub_zero]
    exact hN.eq_zero_of_invariant L hq m
  refine ⟨μ, fun x => ?_⟩
  have hdx : d x = 0 := by
    rw [← (hN.basis L).sum_equivFun x, map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [hd_smul, hd_basis, mul_zero]
  exact sub_eq_zero.1 hdx

end Module

end CFSG.RankThree.GF2n.Stroth80.Tri

end
