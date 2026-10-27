module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveA11Strong
public import CFSG.LocalAnalysis.StandardType.GGHalfFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import Certificates.Data.A8Nbr476

public section

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear

namespace CFSG.StandardType.A11

abbrev F2 : Type := GaloisField 2 1

abbrev SL (n : ℕ) : Type := Matrix.SpecialLinearGroup (Fin n) F2

theorem two_eq_zero : (2 : F2) = 0 := two_eq_zero_of_card (GaloisField.card 2 1 (by omega)) le_rfl

@[expose] noncomputable def permSL (m : ℕ) : Equiv.Perm (Fin (m + 1)) →* SL (m + 1) :=
  (slWeylLift m two_eq_zero).comp (typeAWeylHom (m := m))

@[expose] def blk : Fin 12 → Fin 4 := ![1, 1, 1, 0, 2, 2, 2, 0, 0, 3, 3, 3]

@[expose] def idxIn : Fin 12 → Fin 3 := ![0, 1, 2, 0, 0, 1, 2, 1, 2, 0, 1, 2]

@[expose] def pos : Fin 4 → Fin 3 → Fin 12 := ![![3, 7, 8], ![0, 1, 2], ![4, 5, 6], ![9, 10, 11]]

@[expose] def swapBlocks (l : Fin 4) : Equiv.Perm (Fin 12) :=
  Equiv.swap (pos l 0) (pos 3 0) * Equiv.swap (pos l 1) (pos 3 1) * Equiv.swap (pos l 2) (pos 3 2)

@[expose] noncomputable def Om : Matrix (Fin 3) (Fin 3) F2 := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] noncomputable def T9mat (i : Fin 3) : Matrix (Fin 9) (Fin 9) F2 :=
  Matrix.of fun a b =>
    if blk (Fin.castLE (by omega) a) = (i.castSucc : Fin 4) ∧
        blk (Fin.castLE (by omega) b) = i.castSucc
    then Om (idxIn (Fin.castLE (by omega) a)) (idxIn (Fin.castLE (by omega) b))
    else if a = b then 1 else 0

private def a11t9_e0fun : Fin 9 → Fin 3 ⊕ Fin 6 :=
  ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 0, Sum.inr 3, Sum.inr 4, Sum.inr 5, Sum.inl 1, Sum.inl 2]

private noncomputable def a11t9_e0 : Fin 9 ≃ Fin 3 ⊕ Fin 6 :=
  Equiv.ofBijective a11t9_e0fun (by decide)

private def a11t9_e1fun : Fin 9 → Fin 3 ⊕ Fin 6 :=
  ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5]

private noncomputable def a11t9_e1 : Fin 9 ≃ Fin 3 ⊕ Fin 6 :=
  Equiv.ofBijective a11t9_e1fun (by decide)

private def a11t9_e2fun : Fin 9 → Fin 3 ⊕ Fin 6 :=
  ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 4, Sum.inr 5]

private noncomputable def a11t9_e2 : Fin 9 ≃ Fin 3 ⊕ Fin 6 :=
  Equiv.ofBijective a11t9_e2fun (by decide)

theorem T9mat_det (i : Fin 3) : (T9mat i).det = 1 := by
  fin_cases i
  · change (T9mat 0).det = 1
    have h : T9mat 0 =
        (Matrix.fromBlocks Om (0 : Matrix (Fin 3) (Fin 6) F2) 0
          (1 : Matrix (Fin 6) (Fin 6) F2)).submatrix a11t9_e0 a11t9_e0 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [T9mat, Matrix.fromBlocks, Matrix.submatrix, a11t9_e0, a11t9_e0fun, blk, idxIn, Om]
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Om, Matrix.det_fin_three]
  · change (T9mat 1).det = 1
    have h : T9mat 1 =
        (Matrix.fromBlocks Om (0 : Matrix (Fin 3) (Fin 6) F2) 0
          (1 : Matrix (Fin 6) (Fin 6) F2)).submatrix a11t9_e1 a11t9_e1 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [T9mat, Matrix.fromBlocks, Matrix.submatrix, a11t9_e1, a11t9_e1fun, blk, idxIn, Om]
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Om, Matrix.det_fin_three]
  · change (T9mat 2).det = 1
    have h : T9mat 2 =
        (Matrix.fromBlocks Om (0 : Matrix (Fin 3) (Fin 6) F2) 0
          (1 : Matrix (Fin 6) (Fin 6) F2)).submatrix a11t9_e2 a11t9_e2 := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [T9mat, Matrix.fromBlocks, Matrix.submatrix, a11t9_e2, a11t9_e2fun, blk, idxIn, Om]
    rw [h, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
    simp [Om, Matrix.det_fin_three]

@[expose] noncomputable def T9 (i : Fin 3) : SL 9 := ⟨T9mat i, T9mat_det i⟩

@[expose] noncomputable def T9' (i : Fin 4) : SL 9 := if h : i.val < 3 then T9 ⟨i.val, h⟩ else 1

@[expose] noncomputable def tv9 (a b : Fin 12) : SL 9 :=
  if h : a.val < 9 ∧ b.val < 9 ∧ a ≠ b then
    SpecialLinearGroup.transvection (i := (⟨a.val, h.1⟩ : Fin 9)) (j := ⟨b.val, h.2.1⟩)
      (fun e => h.2.2 (Fin.ext (by simpa using congrArg Fin.val e))) (1 : F2)
  else 1

@[expose] noncomputable def tvAt (l : Fin 4) (a b : Fin 12) : SL 9 :=
  tv9 (swapBlocks l a) (swapBlocks l b)

@[expose] noncomputable def trAt (l : Fin 4) (a b : Fin 12) : SL 9 :=
  if h : (swapBlocks l a).val < 9 ∧ (swapBlocks l b).val < 9 ∧ a ≠ b then
    permSL 8 (Equiv.swap (⟨(swapBlocks l a).val, h.1⟩ : Fin 9) ⟨(swapBlocks l b).val, h.2.1⟩)
  else 1

@[expose] def Coherent {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) : Prop :=
  ∀ (l m : Fin 4) (a b : Fin 12), a ≠ b → blk a ≠ l → blk b ≠ l → blk a ≠ m → blk b ≠ m →
    Φ l (tvAt l a b) = Φ m (tvAt m a b)

@[expose] def ext9 (π : Equiv.Perm (Fin 9)) : Equiv.Perm (Fin 12) :=
  π.viaFintypeEmbedding (Fin.castLEEmb (by omega : 9 ≤ 12))

@[expose] def Clos {G : Type} [Group G] (φ₃ : SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G) : Subgroup G :=
  Subgroup.closure {g | ∃ (w : Equiv.Perm (Fin 12)) (s : SL 8),
    g = ρ w * φ₃ (slBlockHom 7 F2 s) * (ρ w)⁻¹}

@[expose] def RhoEval {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G) :
    Prop :=
  ∀ (l : Fin 4) (a b : Fin 12), a ≠ b → blk a ≠ l → blk b ≠ l →
    ρ (Equiv.swap a b) = Φ l (trAt l a b)

@[expose] def RhoOn9 {G : Type} [Group G] (φ₃ : SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G) : Prop :=
  ∀ π : Equiv.Perm (Fin 9), ρ (ext9 π) = φ₃ (permSL 8 π)

@[expose] def RhoStab {G : Type} [Group G] (φ₃ : SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G) : Prop :=
  ∀ a b : Fin 12, a.val < 8 → b.val < 8 → a ≠ b → ∀ w : Equiv.Perm (Fin 12), w a = a → w b = b →
    ρ w * φ₃ (tv9 a b) = φ₃ (tv9 a b) * ρ w

@[expose] def A11RhoCore {G : Type} [Group G] (φ₃ : SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G) : Prop :=
  Function.Injective ρ ∧ RhoOn9 φ₃ ρ ∧ RhoStab φ₃ ρ

@[expose] def A11RhoSpec {G : Type} [Group G] (Φ : Fin 4 → SL 9 →* G) (ρ : Equiv.Perm (Fin 12) →* G) :
    Prop :=
  A11RhoCore (Φ 3) ρ ∧ (∀ l, (Φ l).range ≤ Clos (Φ 3) ρ) ∧ ρ.range ≤ ⨆ l, (Φ l).range

@[expose] def A11GlueHyp {G : Type} [Group G] (φ₃ : SL 9 →* G) (f n : Fin 4 → G) : Prop :=
  Function.Injective φ₃ ∧ (∀ i : Fin 3, f i.castSucc = φ₃ (T9 i)) ∧ (∀ i j, f i * f j = f j * f i) ∧
    (∀ i, orderOf (f i) = 7) ∧ Nat.card (Subgroup.closure (Set.range f)) = 7 ^ 4 ∧ n 3 = 1 ∧
    (∀ l i, n l * f i * (n l)⁻¹ = f (Equiv.swap l 3 i)) ∧
    IsComponentOf φ₃.range (Subgroup.centralizer ({f 3} : Set G))

@[expose] def A11CohSpec {G : Type} [Group G] (φ₃ : SL 9 →* G) (f n : Fin 4 → G)
    (Φ : Fin 4 → SL 9 →* G) : Prop :=
  Φ 3 = φ₃ ∧ (∀ l, Function.Injective (Φ l)) ∧
    (∀ l, (Φ l).range = φ₃.range.map (MulAut.conj (n l)).toMonoidHom) ∧
    (∀ l k, k ≠ l → Φ l (T9' (Equiv.swap l 3 k)) = f k) ∧ Coherent Φ

@[expose] noncomputable def J9 : Subgroup (SL 9) :=
  ⁅Subgroup.centralizer ({T9 0 * T9 1 * T9 2} : Set (SL 9)),
    Subgroup.centralizer ({T9 0 * T9 1 * T9 2} : Set (SL 9))⁆

@[expose] def A11FrameSpec {G : Type} [Group G] [Finite G] (B Bs : Subgroup G) (x : G)
    (L D J : Subgroup G) (y : G) (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) : Prop :=
  A11GlueHyp φ₃ f n ∧ φ₃.range = K ∧ GGNbr 7 B x D J y K ∧ Subgroup.closure (Set.range f) = Bs ∧
    x = f 0 * f 1 * f 2 * f 3 ∧ y ∈ Subgroup.zpowers (f 3) ∧ D = Subgroup.closure {x, f 3} ∧
    (∀ l, n l ∈ L) ∧ J ≤ K ∧ J ≤ J9.map φ₃ ∧
    L ≤ Subgroup.closure ((J : Set G) ∪ (J.map (MulAut.conj (n 2)).toMonoidHom : Set G))

@[expose] def ev (j : Fin 4) : Fin 4 → ZMod 7 := Pi.single j 1

@[expose] def Good9B (j : Fin 4) (h : Certificates.A8Nbr476.M4) : Prop :=
  Matrix.vecMul (ev j) h = ev j ∧ ∃ (π : Equiv.Perm (Fin 4)) (u : Fin 4 → ZMod 7), π j = j ∧
    (∀ i, i ≠ j → Matrix.vecMul (ev i) h = u i • ev (π i)) ∧
    ((∀ i, i ≠ j → u i = 1 ∨ u i = 2 ∨ u i = 4) ∨ (∀ i, i ≠ j → u i = 3 ∨ u i = 5 ∨ u i = 6))

@[expose] def G314gens : Set Certificates.A8Nbr476.M4 :=
  {!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,1], !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,1],
   !![1,0,0,0; 0,1,0,0; 0,0,0,1; 0,0,1,0], !![2,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1]}

@[expose] def A11StrongOfDataInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp 7 B Bs x L D J → GGSecFiveA11Config 7 B Bs x L D J →
    ∀ (y : G) (K : Subgroup G) (φ₃ : SL 9 →* G) (f n : Fin 4 → G) (Φ : Fin 4 → SL 9 →* G)
      (ρ : Equiv.Perm (Fin 12) →* G),
      A11FrameSpec B Bs x L D J y K φ₃ f n → A11CohSpec φ₃ f n Φ → A11RhoSpec Φ ρ →
      (∀ (y' : G) (K' : Subgroup G), GGNbr 7 B x D J y' K' → K' ≤ Clos φ₃ ρ) →
      ∃ (ψ₀ : (ggU .PSL 12 1).K →* G) (y' : G) (K' : Subgroup G) (u : (ggU .PSL 12 1).K),
        GGPresentsG0 (ggG0 7 B x L D J) (ggU .PSL 12 1).D .PSL 12 1 ψ₀ ∧ GGNbr 7 B x D J y' K' ∧
          K' = (ψ₀.comp ((MulAut.conj u).toMonoidHom.comp
            (slBlockHom₃ 8 (GaloisField 2 1)))).range

end CFSG.StandardType.A11

end
