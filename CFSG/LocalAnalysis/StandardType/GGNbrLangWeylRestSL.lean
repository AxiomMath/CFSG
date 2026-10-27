module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangWeylRestVac
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeAWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix Polynomial CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification NbrLangTypeA CoordSL
open Multiplicative

namespace NbrLangWeylSL

section Matrix

variable {d : ℕ} {F : Type} [Field F] [Finite F]

theorem pow_conj_eq' {X : Type*} [Group X] {H : Type*} [Group H] {φ : H →* X} {x : X} {T : H}
    (hx : ∀ h, x * φ h * x⁻¹ = φ (T * h * T⁻¹)) (j : ℕ) (h : H) :
    x ^ j * φ h * (x ^ j)⁻¹ = φ (T ^ j * h * (T ^ j)⁻¹) := by
  induction j generalizing h with
  | zero => simp
  | succ j ih =>
    have e1 : x ^ (j + 1) * φ h * (x ^ (j + 1))⁻¹ = x ^ j * (x * φ h * x⁻¹) * (x ^ j)⁻¹ := by
      group
    rw [e1, hx, ih]
    congr 1
    group

theorem exists_sl_pow_eq_one {X : Type*} [Group X]
    {φ : SpecialLinearGroup (Fin d) F →* X}
    (hφ : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin d) F)) (hd : 0 < d) {p : ℕ}
    (hp : p.Prime) (hpF : ¬ p ∣ Nat.card F - 1) {b : X} (hbp : b ^ p = 1) {A : GL (Fin d) F}
    (hb : ∀ h, b * φ h * b⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F A h)) :
    ∃ Y : SpecialLinearGroup (Fin d) F, Y ^ p = 1 ∧ ∀ h, b * φ h * b⁻¹ = φ (Y * h * Y⁻¹) := by
  have h1 : ∀ h, φ (CatalogueBHigherLinearAction.slConjugation d F (A ^ p) h) =
      φ (CatalogueBHigherLinearAction.slConjugation d F 1 h) := by
    intro h
    rw [← pow_conj_eq hb p h, hbp, map_one, MulAut.one_apply]
    group
  obtain ⟨c, hc⟩ := exists_scalar_of_forall_conj_eq hφ h1
  rw [inv_one, one_mul] at hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h2 := congrFun (congrFun hc ⟨0, hd⟩) ⟨0, hd⟩
    have h3 : ((A ^ p : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *
        (((A ^ p)⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hc, scalar_apply, diagonal_zero, Matrix.zero_mul] at h3
    have h4 := congrFun (congrFun h3 ⟨0, hd⟩) ⟨0, hd⟩
    simp at h4
  obtain ⟨μ, hμ⟩ := OrdPNS.exists_pow_eq hp hpF (Units.mk0 c hc0)
  set S : GL (Fin d) F := Matrix.GeneralLinearGroup.scalar (Fin d) μ⁻¹ with hS
  set A' : GL (Fin d) F := A * S with hA'
  have hScomm : Commute A S :=
    (show Commute S A from Matrix.GeneralLinearGroup.scalar_commute μ⁻¹ A).symm
  have hAp : A ^ p = Matrix.GeneralLinearGroup.scalar (Fin d) (Units.mk0 c hc0) := by
    apply Units.ext
    rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  have hA'p : A' ^ p = 1 := by
    rw [hA', hScomm.mul_pow, hAp, hS, ← map_pow, ← map_mul, ← hμ, inv_pow, mul_inv_cancel,
      map_one]
  have hdet : (A' : Matrix (Fin d) (Fin d) F).det = 1 :=
    OrdPNS.det_eq_one_of_pow_eq_one hp hpF (by rw [← Units.val_pow_eq_pow_val, hA'p, Units.val_one])
  set Y : SpecialLinearGroup (Fin d) F := ⟨A', hdet⟩ with hY
  have hYGL : SpecialLinearGroup.toGL Y = A' := Units.ext rfl
  refine ⟨Y, ?_, fun h => ?_⟩
  · apply SpecialLinearGroup.toGL_injective
    rw [map_pow, hYGL, hA'p, map_one]
  · rw [hb h]
    congr 1
    rw [← slConjugation_toGL, hYGL]
    apply SpecialLinearGroup.toGL_injective
    rw [CatalogueBHigherLinearAction.toGL_slConjugation,
      CatalogueBHigherLinearAction.toGL_slConjugation, hA', _root_.mul_inv_rev]
    have hSh : S * SpecialLinearGroup.toGL h = SpecialLinearGroup.toGL h * S :=
      Matrix.GeneralLinearGroup.scalar_commute μ⁻¹ _
    calc A * SpecialLinearGroup.toGL h * A⁻¹
        = A * (S * SpecialLinearGroup.toGL h * S⁻¹) * A⁻¹ := by rw [hSh, mul_inv_cancel_right]
      _ = A * S * SpecialLinearGroup.toGL h * (S⁻¹ * A⁻¹) := by group

theorem commute_of_conj_eq {X : Type*} [Group X] {φ : SpecialLinearGroup (Fin d) F →* X}
    (hφ : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin d) F)) (hd : 0 < d) {p : ℕ}
    (hp : p.Prime) (hpF : ¬ p ∣ Nat.card F - 1) {Y Z : SpecialLinearGroup (Fin d) F}
    (hYp : Y ^ p = 1) (h : ∀ g, φ (Y * Z * g * (Y * Z)⁻¹) = φ (Z * Y * g * (Z * Y)⁻¹)) :
    Y * Z = Z * Y := by
  have h1 : ∀ g, φ (CatalogueBHigherLinearAction.slConjugation d F
      (SpecialLinearGroup.toGL (Y * Z)) g) = φ (CatalogueBHigherLinearAction.slConjugation d F
      (SpecialLinearGroup.toGL (Z * Y)) g) := by
    intro g
    rw [slConjugation_toGL, slConjugation_toGL]
    exact h g
  obtain ⟨c, hc⟩ := exists_scalar_of_forall_conj_eq hφ h1
  set z := (Z * Y)⁻¹ * (Y * Z) with hz
  have hzm : (z : Matrix (Fin d) (Fin d) F) = scalar (Fin d) c := by
    have e : SpecialLinearGroup.toGL z =
        (SpecialLinearGroup.toGL (Z * Y))⁻¹ * SpecialLinearGroup.toGL (Y * Z) := by
      rw [hz, map_mul, map_inv]
    rw [← hc, ← e]
    rfl
  have hzc : z ∈ Subgroup.center (SpecialLinearGroup (Fin d) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show ((g * z : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      ((z * g : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)
    rw [Matrix.SpecialLinearGroup.coe_mul g z, Matrix.SpecialLinearGroup.coe_mul z g, hzm]
    exact ((scalar_commute c (fun _ => Commute.all _ _) _).symm).eq
  have hYZ : Y * Z = Z * Y * z := by rw [hz]; group
  have hconj : Z⁻¹ * Y * Z = Y * z := by
    calc Z⁻¹ * Y * Z = Z⁻¹ * (Y * Z) := by group
      _ = Z⁻¹ * (Z * Y * z) := by rw [hYZ]
      _ = Y * z := by group
  have hzp : z ^ p = 1 := by
    have e1 : (Z⁻¹ * Y * Z) ^ p = (Y * z) ^ p := by rw [hconj]
    have e2 : (Z⁻¹ * Y * Z) ^ p = Z⁻¹ * Y ^ p * Z := by
      have := _root_.conj_pow (a := Z⁻¹) (b := Y) (i := p)
      rwa [inv_inv] at this
    have e3 : (Y * z) ^ p = Y ^ p * z ^ p :=
      Commute.mul_pow (Subgroup.mem_center_iff.mp hzc Y) p
    rw [e2, e3, hYp, mul_one, inv_mul_cancel, one_mul] at e1
    exact e1.symm
  have hcp : c ^ p = 1 := by
    have e1 := congrArg (fun t : SpecialLinearGroup (Fin d) F =>
      (t : Matrix (Fin d) (Fin d) F) ⟨0, hd⟩ ⟨0, hd⟩) hzp
    simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one,
      one_apply_eq] at e1
    rwa [hzm, scalar_apply, diagonal_pow, diagonal_apply_eq] at e1
  have hc1 := OrdPNS.eq_one_of_pow_eq_one hp hpF hcp
  have hz1 : z = 1 := by
    apply Subtype.ext
    show (z : Matrix (Fin d) (Fin d) F) = ((1 : SpecialLinearGroup (Fin d) F) :
      Matrix (Fin d) (Fin d) F)
    rw [hzm, hc1, map_one, Matrix.SpecialLinearGroup.coe_one]
  rw [hYZ, hz1, mul_one]

end Matrix

section Rank

variable {G : Type} [Group G] [Finite G]

theorem false_of_cyclic_action {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {z : G} (hzK : z ∈ K) (hzp : z ^ p = 1)
    (hact : ∀ b ∈ Bs, ∃ m : ℕ, ∀ l ∈ K, b * l * b⁻¹ = z ^ m * l * (z ^ m)⁻¹) : False := by
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have := Fact.mk hp
  have hB : IsElemAbelian p B := hC.1.2.2.2.2.2.2.1.1.1
  have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hC.1.2.2.2.2.2.2.1.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hC.1.2.2.2.2.2.1.2.2.2
  have hBN : B ≤ Subgroup.normalizer (K : Set G) := hC.2.1.1.trans hN
  have hS : LargeEvenSHat p B y K := hK.1
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hzK
  set α : ↥B →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN) with hα
  have hker : α.ker ≤ (Subgroup.zpowers y).subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf, ← inf_centralizer_eq_zpowers_of_sHat hS]
    refine ⟨b.2, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    have h1 : (b : G) * l * (b : G)⁻¹ = l :=
      congrArg (fun f : MulAut ↥K => ((f ⟨l, hl⟩ : ↥K) : G)) hb
    calc l * b = (b : G) * l * (b : G)⁻¹ * b := by rw [h1]
      _ = b * l := by group
  have hyB : y ∈ B := hS.2.1
  have hy : Nat.card ((Subgroup.zpowers y).subgroupOf B) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hB.2 y hyB) hS.2.2.1]
  have hk : Nat.card α.ker ≤ p := hy ▸ Subgroup.card_le_of_le hker
  set γ : MulAut ↥K := K.normalizerMonoidHom ⟨z, hzN⟩ with hγ
  have hrange : α.range ≤ Subgroup.zpowers γ := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hact b (hC.2.1.1 b.2)
    refine ⟨(m : ℤ), ?_⟩
    show γ ^ (m : ℤ) = α b
    rw [zpow_natCast, hγ, ← map_pow]
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    exact (hm l l.2).symm
  have hγp : γ ^ p = 1 := by
    rw [hγ, ← map_pow]
    have e : (⟨z, hzN⟩ : Subgroup.normalizer (K : Set G)) ^ p = 1 := Subtype.ext hzp
    rw [e, map_one]
  have hγc : Nat.card (Subgroup.zpowers γ) ≤ p := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hγp)
  have hr : Nat.card α.range ≤ p := (Subgroup.card_le_of_le hrange).trans hγc
  have h1 := Subgroup.card_ker_mul_card_range α
  have h2 : p ^ 4 ≤ Nat.card B := by
    rw [hBc]
    exact Nat.pow_le_pow_right hp.pos h4
  have h3 : Nat.card B ≤ p * p := h1 ▸ Nat.mul_le_mul hk hr
  have h5 : p * p < p ^ 4 := by
    calc p * p = p ^ 2 := (sq p).symm
      _ < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end Rank

section Frame

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K] (g : K[X])
  [Fact (Irreducible g)] {n s r p : ℕ} [Fact p.Prime]

theorem weyl_of_frame (hpK : ¬ p ∣ Nat.card K - 1) (hpK0 : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (φ : SpecialLinearGroup (Fin n) K →* G)
    (hφ : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K))
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (A₀ : SpecialLinearGroup (Fin n) K)
    (hC : (rootMat g).det = 1) {Bs : Subgroup G} (hBc : ∀ a ∈ Bs, ∀ c ∈ Bs, a * c = c * a)
    (k : G → Fin s → ℕ)
    (hact : ∀ b ∈ Bs, ∀ h, b * φ h * b⁻¹ = φ ((A₀ * SLNS.nsSL ε hC (k b) * A₀⁻¹) * h *
      (A₀ * SLNS.nsSL ε hC (k b) * A₀⁻¹)⁻¹))
    (π : Equiv.Perm (Fin s)) (u : Fin s → ℕ) (σ : Fin s → (AdjoinRoot g ≃ₐ[K] AdjoinRoot g))
    (hσ : ∀ i, σ i (AdjoinRoot.root g) = AdjoinRoot.root g ^ u i) {x : G} (hx : x ∈ Bs)
    (hmove : ∀ j : ℕ, ¬ ∀ i, ((u i * k x (π i) : ℕ) : ZMod p) = (j : ZMod p) * (k x i : ZMod p)) :
    ∃ w ∈ φ.range, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  have hp : p.Prime := Fact.out
  have : NeZero p := ⟨hp.ne_zero⟩
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK0 hgd
  obtain ⟨M, hM⟩ := exists_move g ε π σ
  set k₂ : G → Fin s → ℕ := fun b i => u i * k b (π i) with hk₂
  have hrel : ∀ b, SLNS.nsSL ε hC (k₂ b) * M = M * SLNS.nsSL ε hC (k b) := by
    intro b
    apply Subtype.ext
    refine hM _ _ fun i => ?_
    rw [hσ i, ← pow_mul]
  set T : G → SpecialLinearGroup (Fin n) K := fun b => A₀ * SLNS.nsSL ε hC (k b) * A₀⁻¹
    with hT
  set T₂ : G → SpecialLinearGroup (Fin n) K := fun b => A₀ * SLNS.nsSL ε hC (k₂ b) * A₀⁻¹
    with hT₂
  obtain ⟨W, hW⟩ : ∃ W : SpecialLinearGroup (Fin n) K, W = A₀ * M * A₀⁻¹ := ⟨_, rfl⟩
  have hWT : ∀ b, W * T b * W⁻¹ = T₂ b := by
    intro b
    have h1 : M * SLNS.nsSL ε hC (k b) * M⁻¹ = SLNS.nsSL ε hC (k₂ b) := by
      rw [← hrel b, mul_inv_cancel_right]
    simp only [hW, hT, hT₂]
    rw [← h1]
    group
  have hcomm : ∀ a c : Fin s → ℕ, Commute (A₀ * SLNS.nsSL ε hC a * A₀⁻¹)
      (A₀ * SLNS.nsSL ε hC c * A₀⁻¹) := by
    intro a c
    have e := SLNS.nsSL_comm ε hC a c
    calc A₀ * SLNS.nsSL ε hC a * A₀⁻¹ * (A₀ * SLNS.nsSL ε hC c * A₀⁻¹)
        = A₀ * (SLNS.nsSL ε hC a * SLNS.nsSL ε hC c) * A₀⁻¹ := by group
      _ = A₀ * (SLNS.nsSL ε hC c * SLNS.nsSL ε hC a) * A₀⁻¹ := by rw [e]
      _ = A₀ * SLNS.nsSL ε hC c * A₀⁻¹ * (A₀ * SLNS.nsSL ε hC a * A₀⁻¹) := by group
  refine ⟨φ W, ⟨W, rfl⟩, fun b hb => ?_, ?_⟩
  ·
    have h1 : φ W * b * (φ W)⁻¹ = φ (T₂ b * (T b)⁻¹) * b := by
      have h2 := hact b hb W⁻¹
      calc φ W * b * (φ W)⁻¹ = φ W * (b * φ W⁻¹ * b⁻¹) * b := by rw [map_inv]; group
        _ = φ W * φ (T b * W⁻¹ * (T b)⁻¹) * b := by rw [h2]
        _ = φ (W * T b * W⁻¹ * (T b)⁻¹) * b := by
          rw [← map_mul, show W * (T b * W⁻¹ * (T b)⁻¹) = W * T b * W⁻¹ * (T b)⁻¹ by group]
        _ = φ (T₂ b * (T b)⁻¹) * b := by rw [hWT]
    rw [h1, Subgroup.mem_centralizer_iff]
    intro c hc
    have h3 : c * φ (T₂ b * (T b)⁻¹) * c⁻¹ = φ (T₂ b * (T b)⁻¹) := by
      rw [hact c hc]
      congr 1
      have e := ((hcomm (k c) (k₂ b)).mul_right (hcomm (k c) (k b)).inv_right).eq
      rw [e, mul_inv_cancel_right]
    calc c * (φ (T₂ b * (T b)⁻¹) * b) = (c * φ (T₂ b * (T b)⁻¹) * c⁻¹) * (c * b) := by group
      _ = φ (T₂ b * (T b)⁻¹) * (b * c) := by rw [h3, hBc c hc b hb]
      _ = φ (T₂ b * (T b)⁻¹) * b * c := by group
  · intro hmem
    have hxfin : IsOfFinOrder x := isOfFinOrder_of_finite x
    obtain ⟨j, hj⟩ : ∃ j : ℕ, x ^ j = φ W * x * (φ W)⁻¹ :=
      hxfin.mem_powers_iff_mem_zpowers.mpr hmem
    apply hmove j
    have hag : ∀ h, φ (T₂ x * h * (T₂ x)⁻¹) = φ (T x ^ j * h * (T x ^ j)⁻¹) := by
      intro h
      rw [← pow_conj_eq' (hact x hx) j h, hj]
      symm
      calc φ W * x * (φ W)⁻¹ * φ h * (φ W * x * (φ W)⁻¹)⁻¹
          = φ W * (x * φ (W⁻¹ * h * W) * x⁻¹) * φ W⁻¹ := by
            simp only [map_mul, map_inv]
            group
        _ = φ W * φ (T x * (W⁻¹ * h * W) * (T x)⁻¹) * φ W⁻¹ := by rw [hact x hx]
        _ = φ (W * (T x * (W⁻¹ * h * W) * (T x)⁻¹) * W⁻¹) := by rw [← map_mul, ← map_mul]
        _ = φ (T₂ x * h * (T₂ x)⁻¹) := by
          rw [show T₂ x * h * (T₂ x)⁻¹ = W * (T x * (W⁻¹ * h * W) * (T x)⁻¹) * W⁻¹ by
            rw [← hWT x]; group]
    have hag' : ∀ h, φ (CatalogueBHigherLinearAction.slConjugation n K
        (SpecialLinearGroup.toGL (T₂ x)) h) = φ (CatalogueBHigherLinearAction.slConjugation n K
        (SpecialLinearGroup.toGL (T x ^ j)) h) := by
      intro h
      rw [slConjugation_toGL, slConjugation_toGL]
      exact hag h
    obtain ⟨c, hc⟩ := exists_scalar_of_forall_conj_eq hφ hag'
    have hzm : (((T x ^ j)⁻¹ * T₂ x : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = scalar (Fin n) c := by
      have e : SpecialLinearGroup.toGL ((T x ^ j)⁻¹ * T₂ x) =
          (SpecialLinearGroup.toGL (T x ^ j))⁻¹ * SpecialLinearGroup.toGL (T₂ x) := by
        rw [map_mul, map_inv]
      rw [← hc, ← e]
      rfl
    have hzc : (T x ^ j)⁻¹ * T₂ x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show ((y * ((T x ^ j)⁻¹ * T₂ x) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = ((((T x ^ j)⁻¹ * T₂ x) * y : SpecialLinearGroup (Fin n) K) :
          Matrix (Fin n) (Fin n) K)
      rw [Matrix.SpecialLinearGroup.coe_mul y, Matrix.SpecialLinearGroup.coe_mul _ y, hzm]
      exact ((scalar_commute c (fun _ => Commute.all _ _) _).symm).eq
    set ψ := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) K)) with hψ
    have hψker : ψ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [hψ, QuotientGroup.ker_mk']
    have hinj := frameHom_injective ψ A₀ ε hC hCp hψker (rootPB_dim_pos g)
      (isUnit_rootMat_pow_sub hp hpK hpK0 hgd)
    have hψeq : ψ (T x ^ j) = ψ (T₂ x) := QuotientGroup.eq.mpr hzc
    have h1 : frameHom ψ A₀ ε hC hCp (ofAdd fun i => ((k₂ x i : ℕ) : ZMod p)) =
        frameHom ψ A₀ ε hC hCp (ofAdd fun i => (j : ZMod p) * (k x i : ZMod p)) := by
      have h2 : (ofAdd fun i => (j : ZMod p) * (k x i : ZMod p) :
          Multiplicative (Fin s → ZMod p)) = (ofAdd fun i => ((k x i : ℕ) : ZMod p)) ^ j := by
        rw [← ofAdd_nsmul]
        congr 1
        funext i
        rw [Pi.smul_apply, nsmul_eq_mul]
      rw [h2, map_pow, frameHom_natCast, frameHom_natCast, SLRep.ggFrame_apply,
        SLRep.ggFrame_apply, ← map_pow]
      exact hψeq.symm
    intro i
    have h3 := congrFun (congrArg toAdd (hinj h1)) i
    simpa [hk₂] using h3

end Frame

section Marking

variable {G : Type} [Group G] [Finite G]

theorem not_forall_conj_eq_of_nbr {p : ℕ} {B : Subgroup G} {x : G} {D J : Subgroup G} {y : G}
    {K : Subgroup G} (hK : GGNbr p B x D J y K) : ¬ ∀ l ∈ K, x * l * x⁻¹ = l := by
  intro hall
  apply hK.2.2.2
  have h2 : x ∈ Subgroup.centralizer (K : Set G) := Subgroup.mem_centralizer_iff.mpr fun l hl => by
    calc l * x = x * l * x⁻¹ * x := by rw [hall l hl]
      _ = x * l := by group
  have h3 : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) := (Subgroup.zpowers_le).mpr h2
  have h4 : (⁅Subgroup.zpowers x, K⁆ : Subgroup G) = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr h3
  rw [Subgroup.commutator_comm, h4]
  exact bot_le

theorem weyl_of_linearNs_of_lift {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {d : ℕ} (hd : 3 ≤ d)
    {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m) (hpF : ¬ p ∣ 2 ^ m - 1)
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (hL : ∃ φ₀ : SpecialLinearGroup (Fin d) F →* K, Function.Surjective φ₀ ∧
      φ₀.ker ≤ Subgroup.center (SpecialLinearGroup (Fin d) F) ∧
      ∀ g, (θ.trans (TypeA.recipeEquiv d F)) (QuotientGroup.mk (φ₀ g)) = proj d F g)
    (hBI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ) :
    ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  classical
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have hBs : IsElemAbelian p Bs := hC.2.1.2.1
  have hxBs : x ∈ Bs := hC.2.1.1 hC.1.2.2.2.2.2.2.1.2.1
  have hBc : ∀ a ∈ Bs, ∀ c ∈ Bs, a * c = c * a := fun a ha c hc =>
    TableB.IsElemAbelian.comm hBs ha hc
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  have hpF' : ¬ p ∣ Nat.card F - 1 := by rwa [hF]
  set θ₁ := θ.trans (TypeA.recipeEquiv d F) with hθ₁
  obtain ⟨φ₀, hsurj, hφker, hlift⟩ := hL
  have hSL : commutator (SpecialLinearGroup (Fin d) F) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hd)).commutator_eq_top
  set φ : SpecialLinearGroup (Fin d) F →* G := K.subtype.comp φ₀ with hφ
  have hφk : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin d) F) := by
    intro h hh
    apply hφker
    rw [MonoidHom.mem_ker] at hh ⊢
    exact K.subtype_injective (by rw [map_one]; exact hh)
  have hY : ∀ b ∈ Bs, ∃ Y : SpecialLinearGroup (Fin d) F, Y ^ p = 1 ∧
      ∀ h, b * φ h * b⁻¹ = φ (Y * h * Y⁻¹) := by
    intro b hb
    have hlin : ggLAut K θ₁ ⟨b, hN hb⟩ ∈ linearAutGroup d F := (mem_conjImage_iff θ _).mp (hBI b hb)
    obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp hlin
    have hact : ∀ h, b * φ h * b⁻¹ = φ (CatalogueBHigherLinearAction.slConjugation d F A h) :=
      fun h => conj_lift_eq hSL θ₁ φ₀ hlift (hN hb)
        (CatalogueBHigherLinearAction.slConjugation d F A) (by rw [← hA]; rfl) h
    exact exists_sl_pow_eq_one hφk (by omega) hp hpF' (hBs.2 b hb) hact
  choose Y₀ hY₀p hY₀ using hY
  set Y : G → SpecialLinearGroup (Fin d) F := fun b => if hb : b ∈ Bs then Y₀ b hb else 1 with hYd
  have hYeq : ∀ b (hb : b ∈ Bs), Y b = Y₀ b hb := fun b hb => by
    simp only [hYd, hb, ↓reduceDIte]
  have hYp : ∀ b ∈ Bs, Y b ^ p = 1 := fun b hb => by
    rw [hYeq b hb]
    exact hY₀p b hb
  have hYact : ∀ b ∈ Bs, ∀ h, b * φ h * b⁻¹ = φ (Y b * h * (Y b)⁻¹) := fun b hb h => by
    rw [hYeq b hb]
    exact hY₀ b hb h
  have hYc : ∀ b ∈ Bs, ∀ c ∈ Bs, Y b * Y c = Y c * Y b := by
    intro b hb c hc
    refine commute_of_conj_eq hφk (by omega) hp hpF' (hYp b hb) fun g => ?_
    calc φ (Y b * Y c * g * (Y b * Y c)⁻¹) = b * (c * φ g * c⁻¹) * b⁻¹ := by
          rw [hYact c hc, hYact b hb]
          congr 1
          group
      _ = (b * c) * φ g * (b * c)⁻¹ := by group
      _ = (c * b) * φ g * (c * b)⁻¹ := by rw [hBc b hb c hc]
      _ = c * (b * φ g * b⁻¹) * c⁻¹ := by group
      _ = φ (Y c * Y b * g * (Y c * Y b)⁻¹) := by
          rw [hYact b hb, hYact c hc]
          congr 1
          group
  have hpK : (p : F) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  have hne : ¬ IsUnit (cyclotomic p F) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p F),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p F)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hC' : (rootMat g).det = 1 := det_rootMat hp hpF' hpK hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK hgd
  obtain ⟨s, r, ε, A₀, hframe⟩ := exists_frame g hp hpK hgd
    (Set.range fun b : Bs => ((Y b : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F))
    (by
      rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
      show ((Y b : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          ((Y c : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) =
        ((Y c : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) *
          ((Y b : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F)
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        hYc b b.2 c c.2])
    (by
      rintro _ ⟨b, rfl⟩
      show ((Y b : SpecialLinearGroup (Fin d) F) : Matrix (Fin d) (Fin d) F) ^ p = 1
      rw [← Matrix.SpecialLinearGroup.coe_pow, hYp b b.2, Matrix.SpecialLinearGroup.coe_one])
  have hk : ∀ b ∈ Bs, ∃ kv : Fin s → ℕ, Y b = A₀ * SLNS.nsSL ε hC' kv * A₀⁻¹ := by
    intro b hb
    obtain ⟨kv, hkv⟩ := hframe _ ⟨⟨b, hb⟩, rfl⟩
    refine ⟨kv, ?_⟩
    have h1 : Y b * A₀ = A₀ * SLNS.nsSL ε hC' kv := Subtype.ext hkv
    rw [← h1, mul_inv_cancel_right]
  choose kk hkk using hk
  set kf : G → Fin s → ℕ := fun b => if hb : b ∈ Bs then kk b hb else 0 with hkf
  have hkfeq : ∀ b (hb : b ∈ Bs), kf b = kk b hb := fun b hb => by
    simp only [hkf, hb, ↓reduceDIte]
  have hact : ∀ b ∈ Bs, ∀ h, b * φ h * b⁻¹ = φ ((A₀ * SLNS.nsSL ε hC' (kf b) * A₀⁻¹) * h *
      (A₀ * SLNS.nsSL ε hC' (kf b) * A₀⁻¹)⁻¹) := by
    intro b hb h
    rw [hYact b hb h, hkk b hb, hkfeq b hb]
  set t : Fin s → ZMod p := fun i => ((kf x i : ℕ) : ZMod p) with ht
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, t i₁ ≠ 0 := by
    by_contra hall
    push Not at hall
    apply not_forall_conj_eq_of_nbr hK
    intro l hl
    obtain ⟨h, hh⟩ := hsurj ⟨l, hl⟩
    have hl' : φ h = l := congrArg Subtype.val hh
    have hT1 : SLNS.nsSL ε hC' (kf x) = 1 := by
      rw [← SLNS.nsSL_zero ε hC']
      refine SLNS.nsSL_congr ε hC' hCp fun i => ?_
      have h0 : ((kf x i : ℕ) : ZMod p) = 0 := hall i
      rw [Pi.zero_apply, Nat.zero_mod]
      exact Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp h0)
    rw [← hl', hact x hxBs h]
    simp only [hT1, mul_one, mul_inv_cancel, one_mul, inv_one]
  by_cases hz : ∃ i₂, t i₂ = 0
  ·
    obtain ⟨i₂, hi₂⟩ := hz
    obtain ⟨w, ⟨W, rfl⟩, hw1, hw2⟩ := weyl_of_frame g hpF' hpK hgd φ hφk ε A₀ hC' hBc kf hact
      (Equiv.swap i₁ i₂) (fun _ => 1) (fun _ => AlgEquiv.refl) (fun i => by rw [pow_one]; rfl)
      hxBs (fun j hj => by
        have h2 := hj i₂
        rw [Equiv.swap_apply_right, one_mul] at h2
        have hi₂' : ((kf x i₂ : ℕ) : ZMod p) = 0 := hi₂
        apply hi₁
        show ((kf x i₁ : ℕ) : ZMod p) = 0
        rw [h2, hi₂', mul_zero])
    exact ⟨φ W, (φ₀ W).2, hw1, hw2⟩
  push Not at hz
  by_cases hs : ∃ i₀, i₀ ≠ i₁
  ·
    obtain ⟨i₀, hi₀⟩ := hs
    have : Module.Finite F (AdjoinRoot g) := (rootPB g).finite
    have : Algebra.IsAlgebraic F (AdjoinRoot g) := Algebra.IsAlgebraic.of_finite F (AdjoinRoot g)
    set σ : Fin s → (AdjoinRoot g ≃ₐ[F] AdjoinRoot g) := fun i =>
      if i = i₁ then FiniteField.frobeniusAlgEquivOfAlgebraic F (AdjoinRoot g) else AlgEquiv.refl
      with hσd
    set u : Fin s → ℕ := fun i => if i = i₁ then Fintype.card F else 1 with hud
    have hσ : ∀ i, σ i (AdjoinRoot.root g) = AdjoinRoot.root g ^ u i := by
      intro i
      by_cases hi : i = i₁
      · simp only [hσd, hud, hi, ite_true]
        rfl
      · simp [hσd, hud, hi]
    obtain ⟨w, ⟨W, rfl⟩, hw1, hw2⟩ := weyl_of_frame g hpF' hpK hgd φ hφk ε A₀ hC' hBc kf hact
      (Equiv.refl _) u σ hσ hxBs (fun j hj => by
        have h0 := hj i₀
        have h1 := hj i₁
        have hu₀ : u i₀ = 1 := by simp only [hud, hi₀, ite_false]
        have hu₁ : u i₁ = Fintype.card F := by simp only [hud, ite_true]
        rw [hu₀, Equiv.refl_apply, one_mul] at h0
        have hj1 : (j : ZMod p) = 1 :=
          mul_right_cancel₀ (hz i₀) (h0.symm.trans (one_mul (t i₀)).symm)
        rw [hu₁, Equiv.refl_apply, Nat.cast_mul, hj1, one_mul] at h1
        have hq1 : ((Fintype.card F : ℕ) : ZMod p) = 1 :=
          mul_right_cancel₀ (hz i₁) (h1.trans (one_mul (t i₁)).symm)
        apply hpF'
        rw [← Nat.card_eq_fintype_card] at hq1
        rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub Nat.card_pos, hq1, Nat.cast_one, sub_self])
    exact ⟨φ W, (φ₀ W).2, hw1, hw2⟩
  ·
    push Not at hs
    exfalso
    set T₁ := A₀ * SLNS.nsSL ε hC' (fun _ => 1) * A₀⁻¹ with hT₁
    refine false_of_cyclic_action hC hK hN (z := φ T₁) (φ₀ T₁).2 ?_ fun b hb => ?_
    · rw [← map_pow, hT₁, conj_pow, SLNS.nsSL_pow]
      have e : SLNS.nsSL ε hC' (p • fun _ => 1) = 1 := by
        rw [← SLNS.nsSL_zero ε hC']
        refine SLNS.nsSL_congr ε hC' hCp fun i => ?_
        simp
      rw [e, mul_one, mul_inv_cancel, map_one]
    · refine ⟨kf b i₁, fun l hl => ?_⟩
      obtain ⟨h, hh⟩ := hsurj ⟨l, hl⟩
      have hl' : φ h = l := congrArg Subtype.val hh
      have hkb : SLNS.nsSL ε hC' (kf b) = SLNS.nsSL ε hC' (fun _ => 1) ^ (kf b i₁) := by
        rw [SLNS.nsSL_pow]
        congr 1
        funext i
        rw [hs i]
        simp
      rw [← hl', hact b hb h, hkb, ← conj_pow, ← hT₁, map_mul, map_mul, map_inv, map_pow]

theorem exists_lift_of_five_le {d : ℕ} {F : Type} [Field F] [Finite F] {K : Type*} [Group K]
    (hd : 5 ≤ d) (hK : commutator K = ⊤) (θ₁ : K ⧸ Subgroup.center K ≃* projectiveSL d F) :
    ∃ φ₀ : SpecialLinearGroup (Fin d) F →* K, Function.Surjective φ₀ ∧
      φ₀.ker ≤ Subgroup.center (SpecialLinearGroup (Fin d) F) ∧
      ∀ g, θ₁ (QuotientGroup.mk (φ₀ g)) = proj d F g := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  set θ := θ₁.trans (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n + 1) F)) with hθ
  obtain ⟨E, hE⟩ : ∃ E : Subgroup (K × SpecialLinearGroup (Fin (n + 1)) F),
      E = MonoidHom.eqLocus
        ((θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))).comp (MonoidHom.fst _ _))
        ((QuotientGroup.mk' (Subgroup.center _)).comp (MonoidHom.snd _ _)) := ⟨_, rfl⟩
  have hmem : ∀ e : K × SpecialLinearGroup (Fin (n + 1)) F,
      e ∈ E ↔ θ (QuotientGroup.mk e.1) = QuotientGroup.mk e.2 := by
    intro e
    rw [hE]
    rfl
  let π : E →* SpecialLinearGroup (Fin (n + 1)) F := (MonoidHom.snd _ _).comp E.subtype
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (θ.symm (QuotientGroup.mk g))
    refine ⟨⟨(l, g), (hmem _).mpr ?_⟩, rfl⟩
    change θ (QuotientGroup.mk l) = QuotientGroup.mk g
    rw [hl, MulEquiv.apply_symm_apply]
  have hcen : π.ker ≤ Subgroup.center E := by
    intro e he
    have h2 : (e : K × SpecialLinearGroup (Fin (n + 1)) F).2 = 1 := he
    have h1 : (e : K × SpecialLinearGroup (Fin (n + 1)) F).1 ∈ Subgroup.center K := by
      have h := (hmem _).mp e.2
      rw [h2, QuotientGroup.mk_one, ← map_one θ] at h
      exact (QuotientGroup.eq_one_iff _).mp (θ.injective h)
    rw [Subgroup.mem_center_iff]
    intro e'
    apply Subtype.ext
    apply Prod.ext
    · exact (Subgroup.mem_center_iff.mp h1 _)
    · change (e' : K × SpecialLinearGroup (Fin (n + 1)) F).2 *
          (e : K × SpecialLinearGroup (Fin (n + 1)) F).2 =
        (e : K × SpecialLinearGroup (Fin (n + 1)) F).2 *
          (e' : K × SpecialLinearGroup (Fin (n + 1)) F).2
      rw [h2, one_mul, mul_one]
  obtain ⟨σ, hσ⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_four_le (by omega) hπ hcen
  let φ : SpecialLinearGroup (Fin (n + 1)) F →* K := (MonoidHom.fst _ _).comp (E.subtype.comp σ)
  have hφθ : ∀ g, θ (QuotientGroup.mk (φ g)) = QuotientGroup.mk g := by
    intro g
    have h := (hmem _).mp (σ g).2
    have h' : ((σ g : E) : K × SpecialLinearGroup (Fin (n + 1)) F).2 = g := hσ g
    rw [h'] at h
    exact h
  have hdecomp : ∀ l : K, ∃ g, (φ g)⁻¹ * l ∈ Subgroup.center K := by
    intro l
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (θ (QuotientGroup.mk l))
    refine ⟨g, (QuotientGroup.eq (s := Subgroup.center K)).mp (θ.injective ?_)⟩
    rw [hφθ, hg]
  refine ⟨φ, ?_, ?_, fun g => ?_⟩
  · have hle : commutator K ≤ φ.range := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨g₁, hg₁⟩ := hdecomp a
      obtain ⟨g₂, hg₂⟩ := hdecomp b
      have ea : a = φ g₁ * ((φ g₁)⁻¹ * a) := by group
      have eb : b = φ g₂ * ((φ g₂)⁻¹ * b) := by group
      rw [ea, eb, commutatorElement_mul_mem_center hg₁ hg₂, ← map_commutatorElement]
      exact ⟨_, rfl⟩
    intro l
    exact (hle (hK ▸ Subgroup.mem_top l) : l ∈ φ.range)
  · intro g hg
    have h := hφθ g
    rw [show φ g = 1 from hg, QuotientGroup.mk_one, map_one] at h
    exact (QuotientGroup.eq_one_iff _).mp h.symm
  · apply (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n + 1) F)).injective
    exact hφθ g

theorem weyl_of_linearNs {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hperf : commutator K = ⊤) {d : ℕ} (hd : 3 ≤ d)
    {F : Type} [Field F] [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m)
    (hcov : (2 ≤ m ∧ ¬ (d = 3 ∧ m = 2)) ∨ 5 ≤ d) (hpF : ¬ p ∣ 2 ^ m - 1)
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (hBI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ) :
    ∃ w ∈ K, (∀ b ∈ Bs, w * b * w⁻¹ ∈ Subgroup.centralizer (Bs : Set G)) ∧
      w * x * w⁻¹ ∉ Subgroup.zpowers x := by
  refine weyl_of_linearNs_of_lift hC hK hN hd hF hpF θ ?_ hBI
  rcases hcov with ⟨hm, h34⟩ | h5
  · have h4m : 4 ≤ 2 ^ m := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have hF2 : Nat.card F ≠ 2 := by rw [hF]; omega
    have hF3 : Nat.card F ≠ 3 := by
      rw [hF]
      intro h
      have : 2 ∣ 2 ^ m := dvd_pow_self 2 (by omega)
      omega
    have hF4 : ¬ (d = 3 ∧ Nat.card F = 4) := by
      rintro ⟨h3, h4⟩
      apply h34
      refine ⟨h3, ?_⟩
      rw [hF] at h4
      have : 2 ^ m = 2 ^ 2 := by rw [h4]; norm_num
      exact Nat.pow_right_injective (le_refl 2) this
    exact NbrLangTypeA.exists_lift hd hF2 hF4 hF3 hperf _
  · exact exists_lift_of_five_le h5 hperf _

end Marking

end NbrLangWeylSL

open NbrLangWeylSL NbrLangRest

@[expose] def GGNbrLinearNsLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ((lab.tag = .A ∧ 2 ≤ lab.rank) ∨ (lab.tag = .D ∧ lab.rank = 3)) ∧ ¬ p ∣ 2 ^ lab.n - 1 ∧
    ¬ p ∣ lab.n ∧ ((2 ≤ lab.n ∧ ¬ (lab.tag = .A ∧ lab.rank = 2 ∧ lab.n = 2)) ∨
      (lab.tag = .A ∧ 4 ≤ lab.rank))

theorem ggNbrInnerWeylOn_linearNs :
    GGNbrInnerWeylOn GGNbrLinearNsLabel := by
  intro G _ _ p B Bs x L D J hC y K hK hN hxK P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases hS : GGNbrLinearNsLabel p lab
  · have hp : p.Prime := hC.1.2.2.2.2.2.1.1
    have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
    have hD4 : ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3) := by
      rintro ⟨hD, h4, -⟩
      rcases hS.1 with ⟨hA, -⟩ | ⟨-, h3⟩
      · rw [hA] at hD
        exact absurd hD (by decide)
      · omega
    have hraw' := largeEvenLabelAll_pow_mem_powMem hp hp2 hlab
      ⟨Or.inr (Or.inl ⟨hS.1.imp (fun h => h.1) id, hS.2.2.1⟩), hD4⟩ _ hraw
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨htag, hpq, hpn, hcov⟩ := hS
    rcases htag with ⟨ht, hl⟩ | ⟨ht, hl⟩ <;> dsimp only at ht hl hpq hpn hcov <;> subst ht
    · dsimp only [LargeEvenRawDatum] at hraw' ⊢
      obtain ⟨F, _, _, hF, ⟨hs, hna, θ, hPθ⟩, hpw⟩ := hraw'
      refine ⟨F, inferInstance, inferInstance, hF, hs, hna, θ, hPθ, fun _ _ => ?_⟩
      have hcov' : (2 ≤ n ∧ ¬ (l + 1 = 3 ∧ n = 2)) ∨ 5 ≤ l + 1 := by
        rcases hcov with ⟨hn2, hA2⟩ | ⟨-, h4⟩
        · exact Or.inl ⟨hn2, fun h => hA2 ⟨rfl, by omega, h.2⟩⟩
        · exact Or.inr (by omega)
      exact weyl_of_linearNs hC hK hN hperf (d := l + 1) (by omega) hF hcov' hpq θ
        (fun b hb => hpw hs hna _ (ggLAut_pow_eq_one K θ (hN hb) (hC.2.1.2.1.2 b hb)))
    · subst hl
      simp only [LargeEvenRawDatum, ↓reduceIte] at hraw' ⊢
      obtain ⟨F, _, _, hF, ⟨hs, hna, θ, hPθ⟩, hpw⟩ := hraw'
      refine ⟨F, inferInstance, inferInstance, hF, hs, hna, θ, hPθ, fun _ _ => ?_⟩
      have hcov' : (2 ≤ n ∧ ¬ (4 = 3 ∧ n = 2)) ∨ 5 ≤ 4 := by
        rcases hcov with ⟨hn2, -⟩ | ⟨hA, -⟩
        · exact Or.inl ⟨hn2, fun h => by omega⟩
        · exact absurd hA (by decide)
      exact weyl_of_linearNs hC hK hN hperf (d := 4) (by omega) hF hcov' hpq θ
        (fun b hb => hpw hs hna _ (ggLAut_pow_eq_one K θ (hN hb) (hC.2.1.2.1.2 b hb)))
  · exact largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, hθ, fun h => absurd h hS⟩) hraw

end CFSG.StandardType

end
