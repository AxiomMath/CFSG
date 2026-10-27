module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

private def ggQ2s6_sig : Fin 6 → Fin 6 := ![5, 1, 4, 3, 2, 0]

private lemma ggQ2s6_sig_sig (i : Fin 6) : ggQ2s6_sig (ggQ2s6_sig i) = i := by
  fin_cases i <;> decide

private abbrev ggQ2s6_Adj (i j : Fin 6) : Prop := i ≠ j ∧ (CartanMatrix.E 6 i j : ZMod 3) ≠ 0

private lemma ggQ2s6_E6_symm (i j : Fin 6) : CartanMatrix.E 6 i j = CartanMatrix.E 6 j i := by
  fin_cases i <;> fin_cases j <;> decide

private lemma ggQ2s6_adj_sym {i j : Fin 6} (h : ggQ2s6_Adj i j) : ggQ2s6_Adj j i :=
  ⟨h.1.symm, by rw [ggQ2s6_E6_symm]; exact h.2⟩

private lemma ggQ2s6_adj_cartan {i j : Fin 6} (h : ggQ2s6_Adj i j) :
    (CartanMatrix.E 6 i j : ZMod 3) = -1 := by
  rcases h with ⟨hne, hc⟩
  revert hne hc; revert i j; decide

private lemma ggQ2s6_deg3 (v a b c : Fin 6)
    (h : ggQ2s6_Adj v a ∧ ggQ2s6_Adj v b ∧ ggQ2s6_Adj v c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    v = 3 := by
  revert h
  revert v a b c
  decide

private lemma ggQ2s6_adj3 (v : Fin 6) : ggQ2s6_Adj v 3 → v = 1 ∨ v = 2 ∨ v = 4 := by
  revert v; decide

private lemma ggQ2s6_adj1 (v : Fin 6) : ggQ2s6_Adj v 1 → v = 3 := by
  revert v; decide

private lemma ggQ2s6_adj2 (v : Fin 6) : ggQ2s6_Adj v 2 → v = 0 ∨ v = 3 := by
  revert v; decide

private lemma ggQ2s6_adj4 (v : Fin 6) : ggQ2s6_Adj v 4 → v = 3 ∨ v = 5 := by
  revert v; decide

private lemma ggQ2s6_classify (P : Fin 6 ≃ Fin 6)
    (hP : ∀ i j, ggQ2s6_Adj i j → ggQ2s6_Adj (P i) (P j)) :
    (∀ i, P i = i) ∨ (∀ i, P i = ggQ2s6_sig i) := by
  have h3 : P 3 = 3 := ggQ2s6_deg3 (P 3) (P 1) (P 2) (P 4)
    ⟨hP 3 1 (by decide), hP 3 2 (by decide), hP 3 4 (by decide),
     (fun h => absurd (P.injective h) (by decide)),
     (fun h => absurd (P.injective h) (by decide)),
     (fun h => absurd (P.injective h) (by decide))⟩
  have h13 : ggQ2s6_Adj (P 1) 3 := by have h := hP 1 3 (by decide); rwa [h3] at h
  have h23 : ggQ2s6_Adj (P 2) 3 := by have h := hP 2 3 (by decide); rwa [h3] at h
  have h43 : ggQ2s6_Adj (P 4) 3 := by have h := hP 4 3 (by decide); rwa [h3] at h
  have hm1 : P 1 = 1 ∨ P 1 = 2 ∨ P 1 = 4 := ggQ2s6_adj3 (P 1) h13
  have hm2 : P 2 = 1 ∨ P 2 = 2 ∨ P 2 = 4 := ggQ2s6_adj3 (P 2) h23
  have hm4 : P 4 = 1 ∨ P 4 = 2 ∨ P 4 = 4 := ggQ2s6_adj3 (P 4) h43
  have h0ne3 : P 0 ≠ 3 := fun h => absurd (P.injective (h.trans h3.symm)) (by decide)
  have h5ne3 : P 5 ≠ 3 := fun h => absurd (P.injective (h.trans h3.symm)) (by decide)
  have h02 : ggQ2s6_Adj (P 0) (P 2) := hP 0 2 (by decide)
  have h45 : ggQ2s6_Adj (P 4) (P 5) := hP 4 5 (by decide)
  have hneq21 : P 2 ≠ 1 := by
    intro h
    have h' := h02
    rw [h] at h'
    exact h0ne3 (ggQ2s6_adj1 (P 0) h')
  have hneq41 : P 4 ≠ 1 := by
    intro h
    have h' := h45
    rw [h] at h'
    exact h5ne3 ((ggQ2s6_adj1 (P 5) (ggQ2s6_adj_sym h')))
  have hP0 : P 2 = 2 → P 0 = 0 := by
    intro h
    have h' := h02
    rw [h] at h'
    rcases ggQ2s6_adj2 (P 0) h' with h'' | h''
    · exact h''
    · exact absurd h'' h0ne3
  have hP0' : P 2 = 4 → P 0 = 5 := by
    intro h
    have h' := h02
    rw [h] at h'
    rcases ggQ2s6_adj4 (P 0) h' with h'' | h''
    · exact absurd h'' h0ne3
    · exact h''
  have hP5 : P 4 = 2 → P 5 = 0 := by
    intro h
    have h' := h45
    rw [h] at h'
    rcases ggQ2s6_adj2 (P 5) (ggQ2s6_adj_sym h') with h'' | h''
    · exact h''
    · exact absurd h'' h5ne3
  have hP5' : P 4 = 4 → P 5 = 5 := by
    intro h
    have h' := h45
    rw [h] at h'
    rcases ggQ2s6_adj4 (P 5) (ggQ2s6_adj_sym h') with h'' | h''
    · exact absurd h'' h5ne3
    · exact h''
  have h24 : P 2 ≠ P 4 := fun h => absurd (P.injective h) (by decide)
  rcases hm2 with h2 | h2 | h2
  · exact absurd h2 hneq21
  · rcases hm4 with h4 | h4 | h4
    · exact absurd h4 hneq41
    · exact absurd (h24 (h2.trans h4.symm)) (by decide)
    · have h0 := hP0 h2
      have h5 := hP5' h4
      have h1 : P 1 = 1 := by
        rcases hm1 with h1 | h1 | h1
        · exact h1
        · exact absurd (P.injective (h1.trans h2.symm)) (by decide)
        · exact absurd (P.injective (h1.trans h4.symm)) (by decide)
      left
      intro i
      fin_cases i <;> assumption
  · rcases hm4 with h4 | h4 | h4
    · exact absurd h4 hneq41
    · have h0 := hP0' h2
      have h5 := hP5 h4
      have h1 : P 1 = 1 := by
        rcases hm1 with h1 | h1 | h1
        · exact h1
        · exact absurd (P.injective (h1.trans h4.symm)) (by decide)
        · exact absurd (P.injective (h1.trans h2.symm)) (by decide)
      right
      intro i
      fin_cases i <;> simp [ggQ2s6_sig, h0, h1, h2, h3, h4, h5]
    · exact absurd (h24 (h2.trans h4.symm)) (by decide)

private def ggQ2s6_phi (j : Fin 6) : (Fin 6 → ZMod 3) →ₗ[ZMod 3] ZMod 3 where
  toFun := fun x => ∑ k, (CartanMatrix.E 6 j k : ZMod 3) * x k
  map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl; intro k _
    ring

private lemma ggQ2s6_phi_single (j k : Fin 6) :
    ggQ2s6_phi j (Pi.single k 1) = (CartanMatrix.E 6 j k : ZMod 3) := by
  simp only [ggQ2s6_phi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro hk; exact absurd (Finset.mem_univ k) hk

private def ggQ2s6_sR (j : Fin 6) :
    (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) where
  toFun := fun x => x - ggQ2s6_phi j x • Pi.single j 1
  map_add' := by
    intro x y
    simp only [map_add, Pi.add_apply, add_smul, sub_eq_add_neg]
    abel
  map_smul' := by
    intro a x
    simp only [map_smul, Pi.smul_apply, smul_sub, smul_smul, smul_eq_mul, RingHom.id_apply]

private lemma ggQ2s6_sR_apply (j : Fin 6) (x : Fin 6 → ZMod 3) :
    ggQ2s6_sR j x = x - ggQ2s6_phi j x • Pi.single j 1 := rfl

private def ggQ2s6_matOf (e : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3)) :
    Matrix (Fin 6) (Fin 6) (ZMod 3) := fun i k => e (Pi.single k 1) i

private lemma ggQ2s6_matOf_one :
    ggQ2s6_matOf (1 : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3)) = 1 := by
  funext i k
  change Pi.single k 1 i = if i = k then 1 else 0
  simp only [Pi.single_apply]

private def ggQ2s6_Rmat (j : Fin 6) : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  fun i k => (if i = k then 1 else 0) - (if i = j then (CartanMatrix.E 6 j k : ZMod 3) else 0)

private lemma ggQ2s6_matOf_sR (j : Fin 6) : ggQ2s6_matOf (ggQ2s6_sR j) = ggQ2s6_Rmat j := by
  funext i k
  simp only [ggQ2s6_matOf, ggQ2s6_sR_apply, ggQ2s6_phi_single, ggQ2s6_Rmat,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : i = j <;> simp [h, Pi.single_apply]

private lemma ggQ2s6_single_expand (x : Fin 6 → ZMod 3) :
    x = ∑ k, x k • Pi.single k 1 := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne (Ne.symm hb), mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2s6_matOf_mul (e1 e2 : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3)) :
    ggQ2s6_matOf (e1 * e2) = ggQ2s6_matOf e1 * ggQ2s6_matOf e2 := by
  funext i k
  change e1 (e2 (Pi.single k 1)) i = ∑ x, e1 (Pi.single x 1) i * e2 (Pi.single k 1) x
  conv_lhs => rw [show e2 (Pi.single k 1) = ∑ x, e2 (Pi.single k 1) x • Pi.single x 1 from
    ggQ2s6_single_expand (e2 (Pi.single k 1))]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl; intro x _
  ring

private def ggQ2s6_mm : List (Fin 6) → Matrix (Fin 6) (Fin 6) (ZMod 3)
  | [] => 1
  | j :: l => ggQ2s6_mm l * ggQ2s6_Rmat j

private lemma ggQ2s6_matOf_foldl (l : List (Fin 6))
    (A : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3)) :
    ggQ2s6_matOf (l.foldl (fun M j => ggQ2s6_sR j * M) A) = ggQ2s6_mm l * ggQ2s6_matOf A := by
  induction l generalizing A with
  | nil => simp [ggQ2s6_mm, ggQ2s6_matOf_one]
  | cons j l ih =>
      rw [List.foldl_cons, ih, ggQ2s6_matOf_mul, ggQ2s6_matOf_sR, ggQ2s6_mm, Matrix.mul_assoc]

private def ggQ2s6_Tmat : Matrix (Fin 6) (Fin 6) (ZMod 3) :=
  fun i k => -(if ggQ2s6_sig i = k then 1 else 0)

private def ggQ2s6_c1 : List (Fin 6) := [0,1,2,0,3,1,2,0,3,2,4,3]
private def ggQ2s6_c2 : List (Fin 6) := [1,2,0,3,2,4,3,1,5,4,3,1]
private def ggQ2s6_c3 : List (Fin 6) := [2,0,3,2,4,3,1,5,4,3,2,0]

private def ggQ2s6_Mfun : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
  ggQ2s6_c3.foldl (fun M j => ggQ2s6_sR j * M)
    (ggQ2s6_c2.foldl (fun M j => ggQ2s6_sR j * M)
      (ggQ2s6_c1.foldl (fun M j => ggQ2s6_sR j * M) 1))

private lemma ggQ2s6_matOf_Mfun : ggQ2s6_matOf ggQ2s6_Mfun = ggQ2s6_Tmat := by
  rw [ggQ2s6_Mfun, ggQ2s6_matOf_foldl, ggQ2s6_matOf_foldl, ggQ2s6_matOf_foldl,
    ggQ2s6_matOf_one, Matrix.mul_one]
  decide

private lemma ggQ2s6_M_single (i : Fin 6) :
    ggQ2s6_Mfun (Pi.single i 1) = - Pi.single (ggQ2s6_sig i) 1 := by
  funext k
  have hki : ggQ2s6_Mfun (Pi.single i 1) k = ggQ2s6_Tmat k i := by
    rw [← congrFun (congrFun ggQ2s6_matOf_Mfun k) i]; rfl
  rw [hki]
  simp only [ggQ2s6_Tmat]
  by_cases h : ggQ2s6_sig k = i
  · have hk : k = ggQ2s6_sig i := by
      have := congrArg ggQ2s6_sig h
      rwa [ggQ2s6_sig_sig] at this
    subst hk
    rw [ggQ2s6_sig_sig]
    simp
  · have hk : k ≠ ggQ2s6_sig i := by
      intro hh; exact h (by rw [hh, ggQ2s6_sig_sig])
    simp [h, hk]

private noncomputable def ggQ2s6_Phi (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a}) :
    (Fin 6 → ZMod 3) →ₗ[ZMod 3] D.V where
  toFun := fun x => ∑ i, x i • D.coroot (f i)
  map_add' := by
    intro x y
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    simp only [Pi.smul_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [smul_eq_mul, smul_smul, RingHom.id_apply]

private lemma ggQ2s6_Phi_single (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a}) (i : Fin 6) :
    ggQ2s6_Phi D f (Pi.single i 1) = D.coroot (f i) := by
  simp only [ggQ2s6_Phi, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

private lemma ggQ2s6_Phi_sR (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 6 i j)
    (j : Fin 6) (x : Fin 6 → ZMod 3) :
    ggQ2s6_Phi D f (ggQ2s6_sR j x) = D.simpleRefl (f j) (ggQ2s6_Phi D f x) := by
  rw [ggQ2s6_sR_apply, map_sub, map_smul, ggQ2s6_Phi_single]
  rw [show D.simpleRefl (f j) = Module.reflection (D.root_coroot_self (f j)) from rfl,
    Module.reflection_apply]
  congr 1
  congr 1
  simp only [ggQ2s6_phi, ggQ2s6_Phi, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    D.pairing, hf, smul_eq_mul]
  apply Finset.sum_congr rfl; intro i _
  ring

private lemma ggQ2s6_foldl_W (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a})
    (l : List (Fin 6)) (A : D.V →ₗ[ZMod 3] D.V) :
    l.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W) A =
      (l.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W) 1) * A := by
  induction l generalizing A with
  | nil => rw [List.foldl_nil, List.foldl_nil, one_mul]
  | cons j l ih =>
      rw [List.foldl_cons, List.foldl_cons, mul_one,
        ih ((D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * A),
        ih (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V), mul_assoc]

private lemma ggQ2s6_Phi_foldl (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 6 i j)
    (l : List (Fin 6)) (A : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3))
    (x : Fin 6 → ZMod 3) :
    ggQ2s6_Phi D f ((l.foldl (fun M j => ggQ2s6_sR j * M) A) x) =
      ((l.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W) 1)
        (ggQ2s6_Phi D f (A x))) := by
  induction l generalizing A with
  | nil => rfl
  | cons j l ih =>
      rw [List.foldl_cons, List.foldl_cons, mul_one, ih (ggQ2s6_sR j * A)]
      rw [show (ggQ2s6_sR j * A) x = ggQ2s6_sR j (A x) from rfl, ggQ2s6_Phi_sR D f hf]
      rw [ggQ2s6_foldl_W D f l (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V)]
      rfl

private noncomputable def ggQ2s6_Wlin (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a}) :
    D.V →ₗ[ZMod 3] D.V :=
  ggQ2s6_c3.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W)
    (ggQ2s6_c2.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W)
      (ggQ2s6_c1.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W) 1))

private noncomputable def ggQ2s6_Wfun (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a}) :
    D.V ≃ₗ[ZMod 3] D.V :=
  ggQ2s6_c3.foldl (fun W j => D.simpleRefl (f j) * W)
    (ggQ2s6_c2.foldl (fun W j => D.simpleRefl (f j) * W)
      (ggQ2s6_c1.foldl (fun W j => D.simpleRefl (f j) * W) 1))

private lemma ggQ2s6_Wfun_coe (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a}) :
    (ggQ2s6_Wfun D f : D.V →ₗ[ZMod 3] D.V) = ggQ2s6_Wlin D f := rfl

private lemma ggQ2s6_Phi_Mfun (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 6 i j) (x : Fin 6 → ZMod 3) :
    ggQ2s6_Phi D f (ggQ2s6_Mfun x) = ggQ2s6_Wlin D f (ggQ2s6_Phi D f x) := by
  have h1 := ggQ2s6_Phi_foldl D f hf ggQ2s6_c1 1 x
  have h2 := ggQ2s6_Phi_foldl D f hf ggQ2s6_c2
    (ggQ2s6_c1.foldl (fun M j => ggQ2s6_sR j * M) 1) x
  have h3 := ggQ2s6_Phi_foldl D f hf ggQ2s6_c3
    (ggQ2s6_c2.foldl (fun M j => ggQ2s6_sR j * M)
      (ggQ2s6_c1.foldl (fun M j => ggQ2s6_sR j * M) 1)) x
  rw [show ggQ2s6_Mfun = ggQ2s6_c3.foldl (fun M j => ggQ2s6_sR j * M)
      (ggQ2s6_c2.foldl (fun M j => ggQ2s6_sR j * M)
        (ggQ2s6_c1.foldl (fun M j => ggQ2s6_sR j * M) 1)) from rfl]
  rw [h3, h2, h1]
  rw [show (1 : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3)) x = x from rfl]
  rw [ggQ2s6_Wlin]
  rw [ggQ2s6_foldl_W D f ggQ2s6_c3
      (ggQ2s6_c2.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W)
        (ggQ2s6_c1.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W) 1)),
    ggQ2s6_foldl_W D f ggQ2s6_c2
      (ggQ2s6_c1.foldl (fun W j => (D.simpleRefl (f j) : D.V →ₗ[ZMod 3] D.V) * W) 1),
    Module.End.mul_apply, Module.End.mul_apply]

private lemma ggQ2s6_Wfun_mem (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a}) :
    ggQ2s6_Wfun D f ∈ D.parab {k | k ≠ D.a} := by
  have hgen : ∀ j : Fin 6, D.simpleRefl (f j) ∈ D.parab {k | k ≠ D.a} := by
    intro j
    exact Subgroup.subset_closure ⟨f j, (f j).2, rfl⟩
  have hmem : ∀ (l : List (Fin 6)) (A : D.V ≃ₗ[ZMod 3] D.V),
      A ∈ D.parab {k | k ≠ D.a} →
      l.foldl (fun W j => D.simpleRefl (f j) * W) A ∈ D.parab {k | k ≠ D.a} := by
    intro l
    induction l with
    | nil => intro A hA; simpa using hA
    | cons j l ih =>
        intro A hA
        rw [List.foldl_cons]
        exact ih (D.simpleRefl (f j) * A) (mul_mem (hgen j) hA)
  rw [ggQ2s6_Wfun]
  exact hmem ggQ2s6_c3 _
    (hmem ggQ2s6_c2 _ (hmem ggQ2s6_c1 1 (one_mem _)))

private lemma ggQ2s6_Wfun_coroot (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 6 i j) (i : Fin 6) :
    ggQ2s6_Wfun D f (D.coroot (f i)) = - D.coroot (f (ggQ2s6_sig i)) := by
  have h := ggQ2s6_Phi_Mfun D f hf (Pi.single i 1)
  rw [ggQ2s6_M_single] at h
  have h2 : -(ggQ2s6_Phi D f (Pi.single (ggQ2s6_sig i) 1)) =
      ggQ2s6_Wlin D f (ggQ2s6_Phi D f (Pi.single i 1)) := by
    rw [← map_neg (ggQ2s6_Phi D f) (Pi.single (ggQ2s6_sig i) 1)]
    exact h
  rw [ggQ2s6_Phi_single, ggQ2s6_Phi_single] at h2
  rw [← ggQ2s6_Wfun_coe] at h2
  exact h2.symm

private lemma ggQ2s6_zmod3_eq_one_or_neg_one {x : ZMod 3} (hx : x ≠ 0) :
    x = 1 ∨ x = -1 :=
  (by decide : ∀ y : ZMod 3, y ≠ 0 → y = 1 ∨ y = -1) x hx

theorem ggQ2s5_of_E6 (D : GGQ2Lin 3) (f : Fin 6 ≃ {k // k ≠ D.a})
    (hf : ∀ i j, D.cartan (f i) (f j) = CartanMatrix.E 6 i j)
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} {μ : {k // k ≠ D.a} → ZMod 3}
    (h : D.ScaledAut D.a π μ) : D.ScalarModW D.a π μ := by
  let π' : Fin 6 ≃ Fin 6 := (f.trans π).trans f.symm
  let μ' : Fin 6 → ZMod 3 := fun i => μ (f i)
  have hπ : ∀ i : Fin 6, π (f i) = f (π' i) := by intro i; simp [π']
  have hadj : ∀ i j, ggQ2s6_Adj i j → ggQ2s6_Adj (π' i) (π' j) := by
    intro i j hij
    have hne : π' i ≠ π' j := fun hc => hij.1 (π'.injective hc)
    have hc : (D.cartan (f i) (f j) : ZMod 3) ≠ 0 := by rw [hf]; exact hij.2
    have h2 := h.2 (f i) (f j)
    rw [hπ i, hπ j] at h2
    have : (D.cartan (f (π' i)) (f (π' j)) : ZMod 3) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h2
      exact (mul_ne_zero (h.1 (f i)) hc) h2
    rw [hf] at this
    exact ⟨hne, this⟩
  have hclass := ggQ2s6_classify π' hadj
  have hmu : ∀ i, μ' i = μ' 0 := by
    have hedge : ∀ i j : Fin 6, ggQ2s6_Adj i j → μ' i = μ' j := by
      intro i j hij
      have h2 := h.2 (f i) (f j)
      rw [hπ i, hπ j] at h2
      simp only [hf] at h2
      rw [ggQ2s6_adj_cartan hij, ggQ2s6_adj_cartan (hadj i j hij)] at h2
      have h3 : μ (f i) = μ (f j) :=
        mul_right_cancel₀ (by decide : (-1 : ZMod 3) ≠ 0) h2
      simpa only [μ'] using h3
    have h02 : μ' 0 = μ' 2 := hedge 0 2 (by decide)
    have h23 : μ' 2 = μ' 3 := hedge 2 3 (by decide)
    have h34 : μ' 3 = μ' 4 := hedge 3 4 (by decide)
    have h45 : μ' 4 = μ' 5 := hedge 4 5 (by decide)
    have h31 : μ' 3 = μ' 1 := hedge 3 1 (by decide)
    intro i
    fin_cases i
    · rfl
    · exact h31.symm.trans (h23.symm.trans h02.symm)
    · exact h02.symm
    · exact h23.symm.trans h02.symm
    · exact h34.symm.trans (h23.symm.trans h02.symm)
    · exact h45.symm.trans (h34.symm.trans (h23.symm.trans h02.symm))
  rcases hclass with hid | hsig
  · refine ⟨μ' 0, ggQ2s6_zmod3_eq_one_or_neg_one (h.1 (f 0)), 1, Subgroup.one_mem _, ?_⟩
    intro i
    have hpi : π i = i := by
      have h := hπ (f.symm i)
      rw [Equiv.apply_symm_apply] at h
      rw [h, hid (f.symm i)]
      simp
    rw [hpi]
    rw [show (1 : D.V ≃ₗ[ZMod 3] D.V) (D.coroot i) = D.coroot i from by simp]
    rw [show μ i = μ' (f.symm i) from by simp [μ'], hmu (f.symm i)]
  · refine ⟨-μ' 0, ?_, ggQ2s6_Wfun D f, ggQ2s6_Wfun_mem D f, ?_⟩
    · rcases ggQ2s6_zmod3_eq_one_or_neg_one (h.1 (f 0)) with h0 | h0
      · right; change -μ (f 0) = -1; simp only [h0]
      · left; change -μ (f 0) = 1; rw [h0]; decide
    · intro i
      have hpi : π i = f (ggQ2s6_sig (f.symm i)) := by
        have h := hπ (f.symm i)
        rw [Equiv.apply_symm_apply] at h
        rw [h, hsig (f.symm i)]
      rw [hpi]
      rw [show μ i = μ' (f.symm i) from by simp [μ']]
      rw [show D.coroot ↑i = D.coroot ↑(f (f.symm i)) from
        congrArg D.coroot (congrArg Subtype.val (Equiv.apply_symm_apply f i).symm)]
      rw [ggQ2s6_Wfun_coroot D f hf (f.symm i), hmu (f.symm i)]
      rw [show (-μ' 0) • (-D.coroot (f (ggQ2s6_sig (f.symm i)))) =
          μ' 0 • D.coroot (f (ggQ2s6_sig (f.symm i))) from
        neg_smul_neg (μ' 0) (D.coroot (f (ggQ2s6_sig (f.symm i))))]

end CFSG.StandardType

end
