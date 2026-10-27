module

public import CFSG.LocalAnalysis.StandardType.GGPSLGraphAlgebra

public section

namespace CFSG.StandardType

open CFSG.StandardType.ClassicalPosition Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private lemma pslB3_count_ker {A A' C D : Type*} [Group A] [Group A'] [Group C] [Group D]
    [Finite A]
    (N : A →* A') (δ : A →* C) (c : δ.ker →* D)
    (h : ∀ t : δ.ker, c t = 1 → N (t : A) = 1) :
    Nat.card c.ker ≤ Nat.card N.ker := by
  let f : c.ker → N.ker := fun t => ⟨(t : A), by
    simpa using h (t : δ.ker) t.2⟩
  refine Nat.card_le_card_of_injective f ?_
  intro x y hxy
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : N.ker => (z : A)) hxy

private lemma pslB3_count {A A' C D : Type*} [Group A] [Group A'] [Group C] [Group D]
    [Finite A] [Finite C]
    (N : A →* A') (δ : A →* C) (c : δ.ker →* D)
    (h : ∀ t : δ.ker, c t = 1 → N (t : A) = 1) :
    Nat.card N.range ≤ Nat.card C * Nat.card c.range := by
  have hker : Nat.card c.ker ≤ Nat.card N.ker := pslB3_count_ker N δ c h
  have hN := Subgroup.card_ker_mul_card_range N
  have hδ := Subgroup.card_ker_mul_card_range δ
  have hc := Subgroup.card_ker_mul_card_range c
  have hδle : Nat.card δ.range ≤ Nat.card C := Subgroup.card_le_card_group δ.range
  have hNpos : 0 < Nat.card N.ker := by
    haveI : Nonempty N.ker := ⟨1, N.ker.one_mem⟩
    exact Nat.card_pos
  have key : Nat.card N.range * Nat.card N.ker ≤
      Nat.card N.ker * (Nat.card C * Nat.card c.range) := by
    calc Nat.card N.range * Nat.card N.ker
        = Nat.card N.ker * Nat.card N.range := by rw [Nat.mul_comm]
      _ = Nat.card A := hN
      _ = Nat.card δ.ker * Nat.card δ.range := hδ.symm
      _ = (Nat.card c.ker * Nat.card c.range) * Nat.card δ.range := by rw [hc]
      _ ≤ (Nat.card N.ker * Nat.card c.range) * Nat.card C :=
            Nat.mul_le_mul (Nat.mul_le_mul hker (le_refl _)) hδle
      _ = Nat.card N.ker * (Nat.card C * Nat.card c.range) := by ac_rfl
  have key' : Nat.card N.ker * Nat.card N.range ≤
      Nat.card N.ker * (Nat.card C * Nat.card c.range) := by
    rw [Nat.mul_comm (Nat.card N.ker) (Nat.card N.range)]; exact key
  exact Nat.le_of_mul_le_mul_left key' hNpos

private lemma pslB3_alg_comm {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    ∀ a b : pslAlg B, a * b = b * a := by
  have hcommS : (Units.val '' ({B} : Set (GL (Fin n) K)) :
      Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
    rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
    rw [Set.mem_singleton_iff] at hs hs'
    rw [hs, hs']
  letI : CommSemiring (pslAlg B) := Algebra.adjoinCommSemiringOfComm K hcommS
  intro a b
  exact mul_comm a b

private noncomputable def pslB3_star {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    pslAlg B →+* pslAlg B where
  toFun a := ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
    pslGraph_star_mem S a a.2⟩
  map_one' := by
    apply Subtype.ext
    exact Geo.formAdj_one (RingHom.id K) S.det_isUnit
  map_mul' := by
    intro a b
    apply Subtype.ext
    simp only [Subalgebra.coe_mul]
    rw [Geo.formAdj_mul (RingHom.id K) S.det_isUnit]
    exact congrArg Subtype.val
      (pslB3_alg_comm B
        ⟨formAdj (RingHom.id K) G (b : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S b b.2⟩
        ⟨formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K),
          pslGraph_star_mem S a a.2⟩)
  map_zero' := by
    apply Subtype.ext
    simpa using Geo.formAdj_smul (RingHom.id K) G (0 : K) (1 : Matrix (Fin n) (Fin n) K)
  map_add' := by
    intro a b
    apply Subtype.ext
    exact Geo.formAdj_add (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K)
      (b : Matrix (Fin n) (Fin n) K)

private noncomputable def pslB3_theta {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    (pslAlg B)ˣ →* (pslAlg B)ˣ :=
  Units.map (pslB3_star S).toMonoidHom

private noncomputable def pslB3_N {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    (pslAlg B)ˣ →* (pslAlg B)ˣ where
  toFun t := pslB3_theta S t * t
  map_one' := by
    apply Units.ext
    simp [pslB3_theta]
  map_mul' := by
    have hcommS : (Units.val '' ({B} : Set (GL (Fin n) K)) :
        Set (Matrix (Fin n) (Fin n) K)).Pairwise Commute := by
      rintro a ⟨s, hs, rfl⟩ b ⟨s', hs', rfl⟩ _
      rw [Set.mem_singleton_iff] at hs hs'
      rw [hs, hs']
    letI : CommSemiring (pslAlg B) := Algebra.adjoinCommSemiringOfComm K hcommS
    intro s t
    apply Units.ext
    simp only [Units.val_mul]
    rw [map_mul (pslB3_theta S)]
    simp only [Units.val_mul]
    ac_rfl

private lemma pslB3_N_apply {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (t : (pslAlg B)ˣ) :
    ((pslB3_N S t : (pslAlg B)ˣ) : Matrix (Fin n) (Fin n) K) =
      formAdj (RingHom.id K) G (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) *
        (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) := by
  rfl

private lemma pslB3_normImage_card {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    Nat.card (pslNormImage G B) = Nat.card (pslB3_N S).range := by
  let f : pslNormImage G B → (pslB3_N S).range := fun m =>
    ⟨pslB3_N S (Classical.choose m.2), ⟨Classical.choose m.2, rfl⟩⟩
  let g : (pslB3_N S).range → pslNormImage G B := fun u =>
    ⟨((u : (pslAlg B)ˣ) : Matrix (Fin n) (Fin n) K), by
      obtain ⟨t, ht⟩ := u.2
      exact ⟨t, by rw [← ht, pslB3_N_apply]⟩⟩
  have hleft : Function.LeftInverse g f := by
    intro m
    apply Subtype.ext
    rw [pslB3_N_apply]
    exact (Classical.choose_spec m.2).symm
  have hright : Function.RightInverse g f := by
    intro u
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    rw [pslB3_N_apply]
    exact (Classical.choose_spec (g u).2).symm
  exact Nat.card_congr
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright }

private noncomputable def pslB3_det {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    (pslAlg B)ˣ →* Kˣ :=
  Matrix.GeneralLinearGroup.det.comp
    (Units.map (Subalgebra.val (pslAlg B)).toRingHom.toMonoidHom)

private lemma pslB3_det_apply {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (pslAlg B)ˣ) :
    ((pslB3_det B t : Kˣ) : K) =
      Matrix.det (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) := by
  rfl

private lemma pslB3_mem_chat {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {B : GL (Fin n) K} {x : SpecialLinearGroup (Fin n) K}
    (hcomm : (B : Matrix (Fin n) (Fin n) K) * (x : Matrix (Fin n) (Fin n) K) =
      (x : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K)) :
    x ∈ pslChat B := by
  show proj n K x ∈ pslCent B
  show conjAut n K B (proj n K x) = proj n K x
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  have hBBinv : (B : Matrix (Fin n) (Fin n) K) *
      ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hcomm, Matrix.mul_assoc, hBBinv, Matrix.mul_one]

private lemma pslB3_B_mem {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K) :
    (B : Matrix (Fin n) (Fin n) K) ∈ pslAlg B :=
  Algebra.subset_adjoin ⟨B, Set.mem_singleton B, rfl⟩

private lemma pslB3_comm_B {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (pslAlg B)ˣ) :
    (B : Matrix (Fin n) (Fin n) K) * (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) =
      (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) * (B : Matrix (Fin n) (Fin n) K) := by
  have h := pslB3_alg_comm B (⟨(B : Matrix (Fin n) (Fin n) K), pslB3_B_mem B⟩ : pslAlg B)
    (t : pslAlg B)
  simpa using congrArg Subtype.val h

private noncomputable def pslB3_gl {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (pslAlg B)ˣ) : GL (Fin n) K :=
  Units.map (Subalgebra.val (pslAlg B)).toRingHom.toMonoidHom t

private lemma pslB3_gl_val {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (pslAlg B)ˣ) :
    ((pslB3_gl B t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) := by
  rfl

private lemma pslB3_units_val_mul {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (u v : (pslAlg B)ˣ) :
    ((u : pslAlg B) : Matrix (Fin n) (Fin n) K) *
      ((v : pslAlg B) : Matrix (Fin n) (Fin n) K) =
    (((u * v : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K) := by
  rw [Units.val_mul, Subalgebra.coe_mul]

private noncomputable def pslB3_sl {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (pslB3_det B).ker) : SpecialLinearGroup (Fin n) K :=
  ⟨pslB3_gl B (t : (pslAlg B)ˣ), by
    have ht : pslB3_det B (t : (pslAlg B)ˣ) = 1 := t.2
    rw [pslB3_gl_val, ← pslB3_det_apply B (t : (pslAlg B)ˣ), ht]
    rfl⟩

private lemma pslB3_sl_val {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (pslB3_det B).ker) :
    ((pslB3_sl B t : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((t : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K) := by
  rfl

private lemma pslB3_sl_inv_val {n : ℕ} {K : Type} [Field K] (B : GL (Fin n) K)
    (t : (pslB3_det B).ker) :
    (((pslB3_sl B t)⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((((t : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K) := by
  have h1 : SpecialLinearGroup.toGL ((pslB3_sl B t)⁻¹) =
      (pslB3_gl B (t : (pslAlg B)ˣ))⁻¹ := by
    rw [map_inv]
    congr 1
    apply Units.ext
    rfl
  have h2 : (pslB3_gl B (t : (pslAlg B)ˣ))⁻¹ =
      pslB3_gl B ((t : (pslAlg B)ˣ)⁻¹) := by
    simp only [pslB3_gl]
    exact (map_inv (Units.map (Subalgebra.val (pslAlg B)).toRingHom.toMonoidHom)
      ((t : (pslAlg B)ˣ))).symm
  have h3 := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) (h1.trans h2)
  simpa [pslB3_sl, pslB3_gl] using h3

private lemma pslB3_fix_apply {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (t : (pslB3_det B).ker) :
    ∃ d : Kˣ, formAdj (RingHom.id K) G
        (((((t : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
          Matrix (Fin n) (Fin n) K)) =
      (d : K) • ((((t : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) := by
  have hx : pslB3_sl B t ∈ pslChat B := by
    apply pslB3_mem_chat
    rw [pslB3_sl_val]
    exact pslB3_comm_B B (t : (pslAlg B)ˣ)
  obtain ⟨d, hd⟩ := S.fix (pslB3_sl B t) hx
  refine ⟨d, ?_⟩
  rw [pslB3_sl_inv_val, pslB3_sl_val] at hd
  exact hd

private lemma pslB3_c_unique {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (t : (pslAlg B)ˣ) (d d' : Kˣ)
    (h : formAdj (RingHom.id K) G
        ((((t⁻¹ : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) =
      (d : K) • (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)))
    (h' : formAdj (RingHom.id K) G
        ((((t⁻¹ : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) =
      (d' : K) • (((t : pslAlg B) : Matrix (Fin n) (Fin n) K))) :
    d = d' := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by have := S.three_le; omega⟩⟩
  have hMne : (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) ≠ 0 := by
    rw [← pslB3_gl_val B t]
    exact Units.ne_zero (pslB3_gl B t)
  have hd : (d : K) • (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) =
      (d' : K) • (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) := h.symm.trans h'
  have hzero : ((d : K) - (d' : K)) •
      (((t : pslAlg B) : Matrix (Fin n) (Fin n) K)) = 0 := by
    rw [sub_smul, hd, sub_self]
  rcases (smul_eq_zero.mp hzero) with hdd | hM0
  · exact Units.ext (sub_eq_zero.mp hdd)
  · exact absurd hM0 hMne

private noncomputable def pslB3_c {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    (pslB3_det B).ker →* Kˣ where
  toFun t := Classical.choose (pslB3_fix_apply S t)
  map_one' := by
    apply pslB3_c_unique S (1 : (pslB3_det B).ker)
    · exact Classical.choose_spec (pslB3_fix_apply S (1 : (pslB3_det B).ker))
    · simp [Geo.formAdj_one (RingHom.id K) S.det_isUnit]
  map_mul' := by
    intro s t
    apply pslB3_c_unique S (s * t)
    · exact Classical.choose_spec (pslB3_fix_apply S (s * t))
    · have hs : formAdj (RingHom.id K) G
          (((((s : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
            Matrix (Fin n) (Fin n) K)) =
          (((Classical.choose (pslB3_fix_apply S s) : Kˣ) : K) •
            ((((s : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K))) :=
        Classical.choose_spec (pslB3_fix_apply S s)
      have ht : formAdj (RingHom.id K) G
          (((((t : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
            Matrix (Fin n) (Fin n) K)) =
          (((Classical.choose (pslB3_fix_apply S t) : Kˣ) : K) •
            ((((t : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K))) :=
        Classical.choose_spec (pslB3_fix_apply S t)
      calc formAdj (RingHom.id K) G
            (((((s * t : (pslB3_det B).ker) : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
              Matrix (Fin n) (Fin n) K)
          = formAdj (RingHom.id K) G
              ((((t : (pslAlg B)ˣ)⁻¹ * (s : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
                Matrix (Fin n) (Fin n) K) := by
              rw [show ((s * t : (pslB3_det B).ker) : (pslAlg B)ˣ) =
                  (s : (pslAlg B)ˣ) * (t : (pslAlg B)ˣ) from rfl, _root_.mul_inv_rev]
        _ = formAdj (RingHom.id K) G
              (((((s : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
                Matrix (Fin n) (Fin n) K)) *
            formAdj (RingHom.id K) G
              (((((t : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
                Matrix (Fin n) (Fin n) K)) := by
              rw [Units.val_mul, Subalgebra.coe_mul, Geo.formAdj_mul (RingHom.id K) S.det_isUnit]
        _ = (((Classical.choose (pslB3_fix_apply S s) : Kˣ) : K) •
              (((s : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) *
              (((Classical.choose (pslB3_fix_apply S t) : Kˣ) : K) •
              (((t : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) := by
              conv_lhs => rw [hs, ht]
        _ = ((Classical.choose (pslB3_fix_apply S s) *
                Classical.choose (pslB3_fix_apply S t) : Kˣ) : K) •
              ((((s : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K) *
                (((t : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) := by
              rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.val_mul]
        _ = ((Classical.choose (pslB3_fix_apply S s) *
                Classical.choose (pslB3_fix_apply S t) : Kˣ) : K) •
              (((((s * t : (pslB3_det B).ker) : (pslAlg B)ˣ) : pslAlg B) :
                Matrix (Fin n) (Fin n) K)) := by
              rw [show ((s * t : (pslB3_det B).ker) : (pslAlg B)ˣ) =
                  (s : (pslAlg B)ˣ) * (t : (pslAlg B)ˣ) from rfl,
                ← pslB3_units_val_mul B (s : (pslAlg B)ˣ) (t : (pslAlg B)ˣ)]

private lemma pslB3_c_spec {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (t : (pslB3_det B).ker) :
    formAdj (RingHom.id K) G
        (((((t : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) =
      ((pslB3_c S t : Kˣ) : K) •
        ((((t : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) := by
  exact Classical.choose_spec (pslB3_fix_apply S t)

private lemma pslB3_det_formAdj {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (a : pslAlg B) :
    Matrix.det (formAdj (RingHom.id K) G (a : Matrix (Fin n) (Fin n) K)) =
      Matrix.det (a : Matrix (Fin n) (Fin n) K) := by
  unfold formAdj
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have hdet : (G⁻¹).det * G.det = 1 := by
    rw [← Matrix.det_mul, Matrix.nonsing_inv_mul G S.det_isUnit, Matrix.det_one]
  have hmap : ((a : Matrix (Fin n) (Fin n) K).map (RingHom.id K)) =
      (a : Matrix (Fin n) (Fin n) K) := by
    ext i j
    rfl
  rw [hmap]
  calc (G⁻¹).det * (a : Matrix (Fin n) (Fin n) K).det * G.det
      = (a : Matrix (Fin n) (Fin n) K).det * ((G⁻¹).det * G.det) := by ring
    _ = (a : Matrix (Fin n) (Fin n) K).det := by rw [hdet, mul_one]

private lemma pslB3_c_pow {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (t : (pslB3_det B).ker) : (pslB3_c S t) ^ n = 1 := by
  have hspec := pslB3_c_spec S t
  have hdet := congrArg Matrix.det hspec
  have hL : Matrix.det (formAdj (RingHom.id K) G
      ((((t : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
        Matrix (Fin n) (Fin n) K)) = 1 := by
    rw [pslB3_det_formAdj S (((t : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B)]
    have h := pslB3_det_apply B ((t : (pslAlg B)ˣ)⁻¹)
    rw [map_inv, t.2, inv_one] at h
    simpa using h.symm
  have hR : Matrix.det (((pslB3_c S t : Kˣ) : K) •
      ((((t : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K))) =
      ((pslB3_c S t : Kˣ) : K) ^ n := by
    rw [Matrix.det_smul, ← pslB3_det_apply B (t : (pslAlg B)ˣ), t.2, Units.val_one,
      mul_one, Fintype.card_fin]
  rw [hL, hR] at hdet
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact hdet.symm

private lemma pslB3_ker {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B)
    (t : (pslB3_det B).ker) (h : pslB3_c S t = 1) :
    pslB3_N S (t : (pslAlg B)ˣ) = 1 := by
  have hspec := pslB3_c_spec S t
  rw [h] at hspec
  simp only [Units.val_one, one_smul] at hspec
  have hflip : ((((t : (pslAlg B)ˣ)⁻¹ : (pslAlg B)ˣ) : pslAlg B) :
      Matrix (Fin n) (Fin n) K) = formAdj (RingHom.id K) G
      ((((t : (pslAlg B)ˣ) : pslAlg B) : Matrix (Fin n) (Fin n) K)) := by
    have h2 := congrArg (formAdj (RingHom.id K) G) hspec
    rw [Geo.formAdj_formAdj (RingHom.id K) (fun x => rfl) S.det_isUnit
      (by simpa using S.symm)] at h2
    simpa using h2
  apply Units.ext
  apply Subtype.ext
  rw [pslB3_N_apply, ← hflip, ← Subalgebra.coe_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Subalgebra.coe_one]

private lemma pslB3_roots (K : Type) [Field K] [Finite K] (n : ℕ) (H : Subgroup Kˣ)
    (hn : ∀ x ∈ H, x ^ n = 1) :
    Nat.card H ≤ Nat.gcd n (Nat.card K - 1) := by
  haveI : IsCyclic H := subgroup_units_cyclic H
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  have hgn : g ^ n = 1 := by
    apply Subtype.ext
    simpa using hn (g : Kˣ) g.2
  have hdiv1 : Nat.card H ∣ n := by
    have := orderOf_dvd_of_pow_eq_one hgn
    rwa [hg] at this
  have hdiv2 : Nat.card H ∣ Nat.card K - 1 := by
    have hdvd : Nat.card H ∣ Nat.card Kˣ := Subgroup.card_subgroup_dvd_card H
    rwa [Nat.card_units K] at hdvd
  have hK : 1 < Nat.card K := by
    haveI : Fintype K := Fintype.ofFinite K
    have := Fintype.one_lt_card (α := K)
    rwa [← Nat.card_eq_fintype_card] at this
  have hgpos : 0 < Nat.gcd n (Nat.card K - 1) := by
    apply Nat.gcd_pos_of_pos_right
    omega
  exact Nat.le_of_dvd hgpos (Nat.dvd_gcd hdiv1 hdiv2)

theorem pslGraph_torus_bound {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {G : Matrix (Fin n) (Fin n) K} {B : GL (Fin n) K} (S : PSLGraphSetting n K G B) :
    Nat.card (pslNormImage G B) ≤ (Nat.card K - 1) * Nat.gcd n (Nat.card K - 1) := by
  have hcard := pslB3_normImage_card S
  have hcount := pslB3_count (pslB3_N S) (pslB3_det B) (pslB3_c S) (pslB3_ker S)
  have hroot : ∀ x ∈ (pslB3_c S).range, x ^ n = 1 := by
    intro x hx
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
    exact pslB3_c_pow S t
  rw [hcard]
  calc Nat.card (pslB3_N S).range
      ≤ Nat.card Kˣ * Nat.card (pslB3_c S).range := hcount
    _ = (Nat.card K - 1) * Nat.card (pslB3_c S).range := by rw [Nat.card_units K]
    _ ≤ (Nat.card K - 1) * Nat.gcd n (Nat.card K - 1) :=
          Nat.mul_le_mul_left _ (pslB3_roots K n (pslB3_c S).range hroot)

end CFSG.StandardType
