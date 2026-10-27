module

public import CFSG.Quasithin.Background.H156V9
public import CFSG.Quasithin.Background.H156Irr

public section

open scoped Matrix

namespace CFSG.Quasithin.H156

open CFSG.Quasithin.H158U CFSG.Quasithin.H158T CFSG.Quasithin.H.Coc24 CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.LU CFSG.Monster.Code CFSG.Quasithin CFSG.Open
  CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Coc CFSG.ASVolI.ChH

@[expose] def PsiSpec (g : MulAut W11) (a : GL (Fin 3) (ZMod 2)) (c : GL (Fin 2) (ZMod 2)) : Prop :=
  (∀ u ∈ UT, beta3 (g u) = natHom 3 (ZMod 2) a (beta3 u)) ∧
  (∀ x, beta2 (g x) = natHom 2 (ZMod 2) c (beta2 x)) ∧
  (∀ x ∈ V9, beta6 (g x) = tensAut (invTGL 3 a) c (beta6 x))

theorem tensAut_mul (g g' : GL (Fin 3) (ZMod 2)) (h h' : GL (Fin 2) (ZMod 2)) (X : Mat32) :
    tensAut g h (tensAut g' h' X) = tensAut (g * g') (h * h') X := by
  apply Multiplicative.toAdd.injective
  show (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      ((g' : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
        ((h' : Matrix (Fin 2) (Fin 2) (ZMod 2)))ᵀ) * ((h : Matrix (Fin 2) (Fin 2) (ZMod 2)))ᵀ =
    ((g * g' : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
      ((h * h' : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ
  rw [Units.val_mul, Units.val_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem tensAut_one (X : Mat32) : tensAut 1 1 X = X := by
  apply Multiplicative.toAdd.injective
  show ((1 : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd X *
    ((1 : GL (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2))ᵀ = Multiplicative.toAdd X
  simp

theorem natHom_mul_apply (n : ℕ) (a b : GL (Fin n) (ZMod 2)) (w : Wn n) :
    natHom n (ZMod 2) (a * b) w = natHom n (ZMod 2) a (natHom n (ZMod 2) b w) :=
  (congrArg (fun φ : MulAut (Wn n) => φ w) (map_mul (natHom n (ZMod 2)) a b)).trans rfl

theorem natHom_one_apply (n : ℕ) (w : Wn n) : natHom n (ZMod 2) 1 w = w :=
  (congrArg (fun φ : MulAut (Wn n) => φ w) (map_one (natHom n (ZMod 2)))).trans rfl

theorem natHom_inv_apply {n : ℕ} (a : GL (Fin n) (ZMod 2)) {w w' : Wn n}
    (h : natHom n (ZMod 2) a w = w') : natHom n (ZMod 2) a⁻¹ w' = w := by
  rw [← h, ← natHom_mul_apply, inv_mul_cancel, natHom_one_apply]

theorem aut_mul_apply {V : Type*} [CommGroup V] (g h : MulAut V) (x : V) :
    (g * h : MulAut V) x = g (h x) := rfl

theorem aut_one_apply {V : Type*} [CommGroup V] (x : V) : (1 : MulAut V) x = x := rfl

theorem aut_apply_inv {V : Type*} [CommGroup V] (g : MulAut V) (x : V) : g (g⁻¹ x) = x :=
  MulAut.apply_inv_self V g x

theorem tensAut_inv_apply {a : GL (Fin 3) (ZMod 2)} {c : GL (Fin 2) (ZMod 2)} {X X' : Mat32}
    (h : tensAut a c X = X') : tensAut a⁻¹ c⁻¹ X' = X := by
  rw [← h, tensAut_mul, inv_mul_cancel, inv_mul_cancel, tensAut_one]

theorem psiSpec_one : PsiSpec 1 1 1 := by
  refine ⟨fun u _ => ?_, fun x => ?_, fun x _ => ?_⟩
  · exact (congrArg beta3 (aut_one_apply u)).trans (natHom_one_apply 3 _).symm
  · exact (congrArg beta2 (aut_one_apply x)).trans (natHom_one_apply 2 _).symm
  · refine (congrArg beta6 (aut_one_apply x)).trans ?_
    rw [map_one]
    exact (tensAut_one _).symm

theorem psiSpec_mul {g h : MulAut W11} {a a' : GL (Fin 3) (ZMod 2)} {c c' : GL (Fin 2) (ZMod 2)}
    (hh : h ∈ stabSub UT) (hh9 : h ∈ stabSub V9) (hg : PsiSpec g a c) (hh' : PsiSpec h a' c') :
    PsiSpec (g * h) (a * a') (c * c') := by
  obtain ⟨g3, g2, gT⟩ := hg
  obtain ⟨h3, h2, hT⟩ := hh'
  refine ⟨fun u hu => ?_, fun x => ?_, fun x hx => ?_⟩
  · have hhu : h u ∈ UT := (mem_stabSub.1 hh u).2 hu
    calc beta3 ((g * h : MulAut W11) u) = beta3 (g (h u)) := congrArg beta3 (aut_mul_apply g h u)
      _ = natHom 3 (ZMod 2) a (beta3 (h u)) := g3 (h u) hhu
      _ = natHom 3 (ZMod 2) a (natHom 3 (ZMod 2) a' (beta3 u)) := by rw [h3 u hu]
      _ = natHom 3 (ZMod 2) (a * a') (beta3 u) := (natHom_mul_apply 3 a a' _).symm
  · calc beta2 ((g * h : MulAut W11) x) = beta2 (g (h x)) := congrArg beta2 (aut_mul_apply g h x)
      _ = natHom 2 (ZMod 2) c (beta2 (h x)) := g2 (h x)
      _ = natHom 2 (ZMod 2) c (natHom 2 (ZMod 2) c' (beta2 x)) := by rw [h2 x]
      _ = natHom 2 (ZMod 2) (c * c') (beta2 x) := (natHom_mul_apply 2 c c' _).symm
  · have hhx : h x ∈ V9 := (mem_stabSub.1 hh9 x).2 hx
    calc beta6 ((g * h : MulAut W11) x) = beta6 (g (h x)) := congrArg beta6 (aut_mul_apply g h x)
      _ = tensAut (invTGL 3 a) c (beta6 (h x)) := gT (h x) hhx
      _ = tensAut (invTGL 3 a) c (tensAut (invTGL 3 a') c' (beta6 x)) := by rw [hT x hx]
      _ = tensAut (invTGL 3 (a * a')) (c * c') (beta6 x) := by
        rw [tensAut_mul, map_mul]

theorem psiSpec_inv {g : MulAut W11} {a : GL (Fin 3) (ZMod 2)} {c : GL (Fin 2) (ZMod 2)}
    (hs : g ∈ stabSub UT) (hs9 : g ∈ stabSub V9) (hg : PsiSpec g a c) :
    PsiSpec g⁻¹ a⁻¹ c⁻¹ := by
  obtain ⟨g3, g2, gT⟩ := hg
  refine ⟨fun u hu => ?_, fun x => ?_, fun x hx => ?_⟩
  · have hgu : g⁻¹ u ∈ UT := (mem_stabSub.1 (Subgroup.inv_mem _ hs) u).2 hu
    have h1 : beta3 u = natHom 3 (ZMod 2) a (beta3 (g⁻¹ u)) :=
      (congrArg beta3 (aut_apply_inv g u)).symm.trans (g3 _ hgu)
    exact (natHom_inv_apply a h1.symm).symm
  · have h1 : beta2 x = natHom 2 (ZMod 2) c (beta2 (g⁻¹ x)) :=
      (congrArg beta2 (aut_apply_inv g x)).symm.trans (g2 _)
    exact (natHom_inv_apply c h1.symm).symm
  · have hgx : g⁻¹ x ∈ V9 := (mem_stabSub.1 (Subgroup.inv_mem _ hs9) x).2 hx
    have h1 : beta6 x = tensAut (invTGL 3 a) c (beta6 (g⁻¹ x)) :=
      (congrArg beta6 (aut_apply_inv g x)).symm.trans (gT _ hgx)
    have := tensAut_inv_apply h1.symm
    rw [← map_inv] at this
    exact this.symm

@[expose] def GoodSub : Subgroup (MulAut W11) where
  carrier := {g | g ∈ stabSub UT ∧ g ∈ stabSub V9 ∧ ∃ a c, PsiSpec g a c}
  mul_mem' {g h} hg hh := by
    obtain ⟨hg1, hg2, a, c, hgs⟩ := hg
    obtain ⟨hh1, hh2, a', c', hhs⟩ := hh
    exact ⟨(stabSub UT).mul_mem hg1 hh1, (stabSub V9).mul_mem hg2 hh2, a * a', c * c',
      psiSpec_mul hh1 hh2 hgs hhs⟩
  one_mem' := ⟨(stabSub UT).one_mem, (stabSub V9).one_mem, 1, 1, psiSpec_one⟩
  inv_mem' {g} hg := by
    obtain ⟨hg1, hg2, a, c, hgs⟩ := hg
    exact ⟨(stabSub UT).inv_mem hg1, (stabSub V9).inv_mem hg2, a⁻¹, c⁻¹,
      psiSpec_inv hg1 hg2 hgs⟩

@[expose] def matBitsM (y : ℕ) : Matrix (Fin 3) (Fin 2) (ZMod 2) :=
  Matrix.of fun i j => if y.testBit (i + 3 * j) then 1 else 0

theorem beta6_toW (m : ℕ) : beta6 (toW 11 m) = Multiplicative.ofAdd (matBitsM (actM c6 m)) := by
  show matOfW (maskHom 11 6 c6 (toW 11 m)) = _
  rw [maskHom_toW c6_len]
  rfl

theorem psiSpec_of_cols {g : MulAut W11} {cols A iA C iC : List ℕ} (hg : ActsBy g cols)
    (hA : A.length = 3) (hC : C.length = 2)
    (h1 : colMat 3 A * colMat 3 iA = 1) (h2 : colMat 3 iA * colMat 3 A = 1)
    (h3 : colMat 2 C * colMat 2 iC = 1) (h4 : colMat 2 iC * colMat 2 C = 1)
    (s3 : ∀ m ∈ uTMasks, actM c3 (actM cols m) = actM A (actM c3 m))
    (s2 : ∀ m < 2 ^ 11, actM c2 (actM cols m) = actM C (actM c2 m))
    (sT : ∀ m < 2 ^ 11, actM c2 m = 0 →
      matBitsM (actM c6 (actM cols m)) = (colMat 3 iA)ᵀ * matBitsM (actM c6 m) * (colMat 2 C)ᵀ) :
    PsiSpec g (mkGL 3 A iA h1 h2) (mkGL 2 C iC h3 h4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨m, hm, rfl⟩ := hu
    have hlt := combos_lt uTBasis_lt m hm
    have hmem : m ∈ uTMasks := (uT_combos m hlt).1 hm
    have e : g (toW 11 m) = toW 11 (actM cols m) := hg m
    rw [e, beta3_toW, beta3_toW, natHom_mkGL hA, s3 m hmem]
  · intro x
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
    have e : g (toW 11 m) = toW 11 (actM cols m) := hg m
    rw [e, beta2_toW, beta2_toW, natHom_mkGL hC, s2 m hm]
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
    have hm0 : actM c2 m = 0 := (mem_V9_iff m).1 hx
    have e : g (toW 11 m) = toW 11 (actM cols m) := hg m
    rw [e, beta6_toW, beta6_toW, sT m hm hm0]
    rfl

theorem mem_stabSub_V9 {g : MulAut W11} {cols : List ℕ} (hg : ActsBy g cols)
    (h : ∀ m < 2 ^ 11, actM c2 (actM cols m) = 0 ↔ actM c2 m = 0) : g ∈ stabSub V9 := by
  intro u
  obtain ⟨m, hm, rfl⟩ := toW_surj 11 u
  have e : g (toW 11 m) = toW 11 (actM cols m) := hg m
  exact (Iff.of_eq (congrArg (· ∈ V9) e)).trans
    ((mem_V9_iff _).trans ((h m hm).trans (mem_V9_iff m).symm))

@[expose] def aA : GL (Fin 3) (ZMod 2) :=
  mkGL 3 [4, 5, 7] [3, 6, 1] (by decide +kernel) (by decide +kernel)
@[expose] def cA : GL (Fin 2) (ZMod 2) :=
  mkGL 2 [1, 2] [1, 2] (by decide +kernel) (by decide +kernel)
@[expose] def aB : GL (Fin 3) (ZMod 2) :=
  mkGL 3 [4, 3, 6] [7, 5, 1] (by decide +kernel) (by decide +kernel)
@[expose] def cB : GL (Fin 2) (ZMod 2) :=
  mkGL 2 [1, 2] [1, 2] (by decide +kernel) (by decide +kernel)
@[expose] def aT3 : GL (Fin 3) (ZMod 2) :=
  mkGL 3 [1, 2, 4] [1, 2, 4] (by decide +kernel) (by decide +kernel)
@[expose] def cT3 : GL (Fin 2) (ZMod 2) :=
  mkGL 2 [3, 1] [2, 3] (by decide +kernel) (by decide +kernel)
@[expose] def aT2 : GL (Fin 3) (ZMod 2) :=
  mkGL 3 [2, 1, 6] [2, 1, 5] (by decide +kernel) (by decide +kernel)
@[expose] def cT2 : GL (Fin 2) (ZMod 2) :=
  mkGL 2 [2, 1] [2, 1] (by decide +kernel) (by decide +kernel)

theorem psiSpec_gA : PsiSpec gA aA cA :=
  psiSpec_of_cols actsBy_gA (by decide) (by decide) _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem psiSpec_gB : PsiSpec gB aB cB :=
  psiSpec_of_cols actsBy_gB (by decide) (by decide) _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem psiSpec_gT3 : PsiSpec gT3 aT3 cT3 :=
  psiSpec_of_cols actsBy_gT3 (by decide) (by decide) _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem psiSpec_gT2 : PsiSpec gT2 aT2 cT2 :=
  psiSpec_of_cols actsBy_gT2 (by decide) (by decide) _ _ _ _ (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

end CFSG.Quasithin.H156
