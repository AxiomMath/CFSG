module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGPDDefs
public import CFSG.LocalAnalysis.StandardType.GGPDCoords
public import CFSG.LocalAnalysis.StandardType.GGPDLift

public section

namespace CFSG.StandardType

open CFSG.Assembly

private def pdi_L : List (Fin 4) := [3, 2, 1, 0]

private theorem pdi_conj_list {G H : Type} [Group G] [Group H] (π : G →* H)
    {A : Subgroup H} (gsF : Fin 4 → G) (φF : Fin 4 → MulAut ↥A)
    (hgsF : ∀ i y (a : ↥A), π y = (a : H) →
      π (gsF i * y * (gsF i)⁻¹) = ((φF i a : ↥A) : H))
    (l : List (Fin 4)) (y : G) (a : ↥A) (hy : π y = (a : H)) :
    π ((l.map gsF).prod * y * ((l.map gsF).prod)⁻¹) =
      ((((l.map φF).prod : MulAut ↥A) a : ↥A) : H) := by
  induction l generalizing y a with
  | nil =>
      simpa using hy
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons]
      have hconj : (gsF i * (l.map gsF).prod) * y * (gsF i * (l.map gsF).prod)⁻¹ =
          gsF i * ((l.map gsF).prod * y * ((l.map gsF).prod)⁻¹) * (gsF i)⁻¹ := by
        group
      rw [hconj]
      have hspec := hgsF i ((l.map gsF).prod * y * ((l.map gsF).prod)⁻¹)
        ((l.map φF).prod a) (ih y a hy)
      simpa using hspec

private theorem pdi_kappa_list {A : Type} [Group A]
    (κ : Additive A ≃+ (Fin 4 → ZMod 3)) (φF : Fin 4 → MulAut A)
    (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hκ : ∀ i a, κ (Additive.ofMul (φF i a)) =
      (ggPDRefl M i).mulVec (κ (Additive.ofMul a)))
    (l : List (Fin 4)) (a : A) :
    κ (Additive.ofMul (((l.map φF).prod : MulAut A) a)) =
      (((l.map (fun i => ggPDRefl M i)).prod : Matrix (Fin 4) (Fin 4) (ZMod 3)).mulVec
        (κ (Additive.ofMul a))) := by
  induction l generalizing a with
  | nil =>
      rw [List.map_nil, List.prod_nil, List.map_nil, List.prod_nil, MulAut.one_apply,
        Matrix.one_mulVec]
  | cons i l ih =>
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, MulAut.mul_apply]
      rw [hκ i ((l.map φF).prod a), ih a, Matrix.mulVec_mulVec]

private theorem pdi_kappa_pow {A : Type} [Group A]
    (κ : Additive A ≃+ (Fin 4 → ZMod 3)) (Φ : MulAut A)
    (S : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (h : ∀ a, κ (Additive.ofMul (Φ a)) = S.mulVec (κ (Additive.ofMul a))) (n : ℕ) (a : A) :
    κ (Additive.ofMul ((Φ ^ n) a)) = (S ^ n).mulVec (κ (Additive.ofMul a)) := by
  induction n generalizing a with
  | zero =>
      rw [pow_zero, pow_zero, MulAut.one_apply, Matrix.one_mulVec]
  | succ n ih =>
      rw [pow_succ', pow_succ', MulAut.mul_apply]
      rw [h ((Φ ^ n) a), ih a, Matrix.mulVec_mulVec]

private theorem pdi_neg_one_mulVec : ∀ v : Fin 4 → ZMod 3,
    (-1 : Matrix (Fin 4) (Fin 4) (ZMod 3)).mulVec v = -v := by
  decide +kernel

private theorem pdi_Phi_pow_six_inv {A : Type} [Group A]
    (κ : Additive A ≃+ (Fin 4 → ZMod 3)) (Φ : MulAut A)
    (S : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (h : ∀ a, κ (Additive.ofMul (Φ a)) = S.mulVec (κ (Additive.ofMul a)))
    (hS : S ^ 6 = -1) : ∀ a : A, (Φ ^ 6) a = a⁻¹ := by
  intro a
  apply Additive.ofMul.injective
  apply κ.injective
  have h1 : κ (Additive.ofMul ((Φ ^ 6) a)) = (S ^ 6).mulVec (κ (Additive.ofMul a)) :=
    pdi_kappa_pow κ Φ S h 6 a
  rw [h1, hS, pdi_neg_one_mulVec (κ (Additive.ofMul a)), ofMul_inv, map_neg]

private theorem pdi_word_minus_one (M : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (hM : M = ggPDC3 ∨ M = ggPDC3.transpose) :
    ((pdi_L.map (fun i => ggPDRefl M i)).prod) ^ 6 = -1 := by
  rcases hM with h | h <;> rw [h] <;> decide +kernel

theorem ggPD_inversion_lift {K : Type} [Field K] {d : ℕ}
    {A : Subgroup (Matrix.GeneralLinearGroup (Fin d) K ⧸
      Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))}
    (hcard : Nat.card A = 3 ^ 4)
    [Fact (Nat.Prime 3)] {Γ : Type} [Fintype Γ] [DecidableEq Γ] {C : Matrix Γ Γ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ι : Additive ↥A ≃+ V}
    {φ : Γ → MulAut ↥A} {h : Γ → V} {α : Γ → Module.Dual (ZMod 3) V}
    (hD : GGExtDatum ι C φ h α) (e : Fin 4 ≃ Γ)
    (hF4 : (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i)) :
    ∃ z : Matrix.GeneralLinearGroup (Fin d) K,
      ∀ y ∈ A.comap (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))),
        z * y * z⁻¹ ∈
            A.comap (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))) ∧
          QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K))
              (z * y * z⁻¹) =
            (QuotientGroup.mk' (Subgroup.center (Matrix.GeneralLinearGroup (Fin d) K)) y)⁻¹ := by
  classical
  let G := Matrix.GeneralLinearGroup (Fin d) K
  let Z : Subgroup G := Subgroup.center G
  let π : G →* G ⧸ Z := QuotientGroup.mk' Z
  have hgs : ∀ i : Γ, ∃ g : G, ∀ y (a : ↥A), π y = (a : G ⧸ Z) →
      π (g * y * g⁻¹) = ((φ i a : ↥A) : G ⧸ Z) :=
    fun i => ggPD_normalizer_lift hD i
  let gs : Γ → G := fun i => Classical.choose (hgs i)
  have hgs_spec : ∀ i y (a : ↥A), π y = (a : G ⧸ Z) →
      π (gs i * y * (gs i)⁻¹) = ((φ i a : ↥A) : G ⧸ Z) :=
    fun i => Classical.choose_spec (hgs i)
  let φF : Fin 4 → MulAut ↥A := fun i => φ (e i)
  let gsF : Fin 4 → G := fun i => gs (e i)
  have hgsF : ∀ i y (a : ↥A), π y = (a : G ⧸ Z) →
      π (gsF i * y * (gsF i)⁻¹) = ((φF i a : ↥A) : G ⧸ Z) :=
    fun i y a hy => hgs_spec (e i) y a hy
  let M : Matrix (Fin 4) (Fin 4) (ZMod 3) := Matrix.of fun j k => (C (e j) (e k) : ZMod 3)
  obtain ⟨κ, hκ⟩ := ggPD_coords hcard hD e
  have hκ' : ∀ i (a : ↥A), κ (Additive.ofMul (φF i a)) =
      (ggPDRefl M i).mulVec (κ (Additive.ofMul a)) := fun i a => hκ i a
  have hM : M = ggPDC3 ∨ M = ggPDC3.transpose := by
    rcases hF4 with h | h
    · left
      ext j k
      show ((C (e j) (e k) : ℤ) : ZMod 3) = ((CartanMatrix.F₄ j k : ℤ) : ZMod 3)
      rw [h j k]
    · right
      ext j k
      show ((C (e j) (e k) : ℤ) : ZMod 3) = ((CartanMatrix.F₄ k j : ℤ) : ZMod 3)
      rw [h j k]
  let w : G := (pdi_L.map gsF).prod
  let Φ : MulAut ↥A := (pdi_L.map φF).prod
  let Sword : Matrix (Fin 4) (Fin 4) (ZMod 3) := (pdi_L.map (fun i => ggPDRefl M i)).prod
  have hw : ∀ y (a : ↥A), π y = (a : G ⧸ Z) →
      π (w * y * w⁻¹) = ((Φ a : ↥A) : G ⧸ Z) :=
    fun y a hy => pdi_conj_list π gsF φF hgsF pdi_L y a hy
  have hpow : ∀ n y (a : ↥A), π y = (a : G ⧸ Z) →
      π (w ^ n * y * (w ^ n)⁻¹) = (((Φ ^ n) a : ↥A) : G ⧸ Z) := by
    intro n
    induction n with
    | zero =>
        intro y a hy
        simpa using hy
    | succ n ih =>
        intro y a hy
        have h1 : π (w * y * w⁻¹) = ((Φ a : ↥A) : G ⧸ Z) := hw y a hy
        have h2 := ih (w * y * w⁻¹) (Φ a) h1
        have heq : (w ^ n * w) * y * (w ^ n * w)⁻¹ =
            w ^ n * (w * y * w⁻¹) * (w ^ n)⁻¹ := by
          group
        rw [pow_succ, pow_succ, MulAut.mul_apply, heq]
        exact h2
  have hκΦ : ∀ a : ↥A, κ (Additive.ofMul (Φ a)) = Sword.mulVec (κ (Additive.ofMul a)) :=
    fun a => pdi_kappa_list κ φF M hκ' pdi_L a
  have hSword : Sword ^ 6 = -1 := pdi_word_minus_one M hM
  have hPhinv : ∀ a : ↥A, (Φ ^ 6) a = a⁻¹ := pdi_Phi_pow_six_inv κ Φ Sword hκΦ hSword
  refine ⟨w ^ 6, ?_⟩
  intro y hy
  have ha : π y ∈ A := Subgroup.mem_comap.mp hy
  have hpow6 := hpow 6 y ⟨π y, ha⟩ rfl
  have hinv : (Φ ^ 6) ⟨π y, ha⟩ = ⟨π y, ha⟩⁻¹ := hPhinv _
  rw [hinv] at hpow6
  have hfin : π (w ^ 6 * y * (w ^ 6)⁻¹) = (π y)⁻¹ := by
    rw [hpow6]
    rfl
  refine ⟨?_, hfin⟩
  exact Subgroup.mem_comap.mpr (by rw [hfin]; exact A.inv_mem ha)

end CFSG.StandardType

end
