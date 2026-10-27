module

public import CFSG.RankThree.SubgroupLists.MitchellDickson
public import CFSG.RankThree.SubgroupLists.SymplecticSkewAxes
public import CFSG.RankThree.SubgroupLists.DicksonGL2
public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Certificates.Certificate43
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Maximal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

theorem commute_of_six_le_orderOf_pgl {k : Type} [Field k] [Finite k] {p : ℕ} [Fact p.Prime]
    [CharP k p] (J : Subgroup PGL(Fin 2, k)) (hJ : ¬ p ∣ Nat.card J) {w : J}
    (hw : 6 ≤ orderOf w) {x y : J} (hx : 2 < orderOf x) (hy : 2 < orderOf y) :
    x * y = y * x := by
  have := Fintype.ofFinite k
  let E := FiniteField.Extension k p 2
  have := Fintype.ofFinite E
  have hEcard : Nat.card E = Nat.card k ^ 2 := FiniteField.natCard_extension k p 2
  obtain ⟨f, -, hkcard⟩ := FiniteField.card k p
  have hEp : Nat.card E = p ^ (2 * (f : ℕ)) := by
    rw [hEcard, Nat.card_eq_fintype_card, hkcard, ← pow_mul, mul_comm]
  have hsq : ∀ x : k, IsSquare (algebraMap k E x) :=
    CFSG.LinearGroups.isSquare_algebraMap_of_card_eq_sq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEcard])
  set ι := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := E)
  set J₁ := J.map (CFSG.LinearGroups.pglExtend k E)
  have hJ₁ : J₁ ≤ ι.range := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.LinearGroups.pglExtend_mem_range_toPGL hsq x
  set H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) := J₁.comap ι
  have hmap : H.map ι = J₁ := Subgroup.map_comap_eq_self hJ₁
  let eH : H ≃* J :=
    ((H.equivMapOfInjective ι Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
      (MulEquiv.subgroupCongr hmap)).trans
      (J.equivMapOfInjective (CFSG.LinearGroups.pglExtend k E)
        CFSG.LinearGroups.pglExtend_injective).symm
  have hcard : Nat.card H = Nat.card J := Nat.card_congr eH.toEquiv
  have hHp : ¬ p ∣ Nat.card H := hcard ▸ hJ
  have key := commute_of_six_le_orderOf hEp H hHp (w := eH.symm w)
    (by rw [MulEquiv.orderOf_eq]; exact hw) (x := eH.symm x) (y := eH.symm y)
    (by rw [MulEquiv.orderOf_eq]; exact hx) (by rw [MulEquiv.orderOf_eq]; exact hy)
  apply eH.symm.injective
  rw [map_mul, map_mul, key]

variable {F : Type} [Field F]

@[expose] def IsBlockDiag (M : Matrix V₄ V₄ F) : Prop := M.toBlocks₁₂ = 0 ∧ M.toBlocks₂₁ = 0

theorem eq_fromBlocks_of_isBlockDiag {M : Matrix V₄ V₄ F} (h : IsBlockDiag M) :
    M = fromBlocks M.toBlocks₁₁ 0 0 M.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [h.1, h.2]

theorem isBlockDiag_fromBlocks (A D : Matrix (Fin 2) (Fin 2) F) :
    IsBlockDiag (fromBlocks A 0 0 D) := by
  simp [IsBlockDiag]

theorem fromBlocks_diag_mul (A D A' D' : Matrix (Fin 2) (Fin 2) F) :
    fromBlocks A 0 0 D * fromBlocks A' 0 0 D' = fromBlocks (A * A') 0 0 (D * D') := by
  rw [Matrix.fromBlocks_multiply]
  simp

theorem toBlocks₁₁_mul_of_isBlockDiag {X Y : Matrix V₄ V₄ F} (hX : IsBlockDiag X) :
    (X * Y).toBlocks₁₁ = X.toBlocks₁₁ * Y.toBlocks₁₁ := by
  ext i j
  have h0 : ∀ m : Fin 2, X (Sum.inl i) (Sum.inr m) = 0 := fun m =>
    congrFun (congrFun hX.1 i) m
  simp [Matrix.toBlocks₁₁, Matrix.mul_apply, Fintype.sum_sum_type, h0]

@[expose] def blockDiagGL (F : Type) [Field F] : Subgroup (GL V₄ F) where
  carrier := {g | IsBlockDiag (g : Matrix V₄ V₄ F)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul] at ha hb ⊢
    rw [eq_fromBlocks_of_isBlockDiag ha, eq_fromBlocks_of_isBlockDiag hb, fromBlocks_diag_mul]
    exact isBlockDiag_fromBlocks _ _
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one]
    rw [← Matrix.fromBlocks_one]
    exact isBlockDiag_fromBlocks _ _
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : (a : Matrix V₄ V₄ F) * ((a⁻¹ : GL V₄ F) : Matrix V₄ V₄ F) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1' : ((a⁻¹ : GL V₄ F) : Matrix V₄ V₄ F) * (a : Matrix V₄ V₄ F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    set X := (a : Matrix V₄ V₄ F)
    set Y := ((a⁻¹ : GL V₄ F) : Matrix V₄ V₄ F)
    have e1 := congrArg Matrix.toBlocks₁₂ h1
    have e2 := congrArg Matrix.toBlocks₂₁ h1
    have e3 := congrArg Matrix.toBlocks₁₁ h1'
    have e4 := congrArg Matrix.toBlocks₂₂ h1'
    rw [eq_fromBlocks_of_isBlockDiag ha] at e1 e2 e3 e4
    conv at e1 => rw [← Matrix.fromBlocks_toBlocks Y]
    conv at e2 => rw [← Matrix.fromBlocks_toBlocks Y]
    conv at e3 => rw [← Matrix.fromBlocks_toBlocks Y]
    conv at e4 => rw [← Matrix.fromBlocks_toBlocks Y]
    simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks_fromBlocks₁₂,
      Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₂,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, ← Matrix.fromBlocks_one] at e1 e2 e3 e4
    constructor
    · calc Y.toBlocks₁₂ = Y.toBlocks₁₁ * (X.toBlocks₁₁ * Y.toBlocks₁₂) := by
            rw [← Matrix.mul_assoc, e3, Matrix.one_mul]
        _ = 0 := by rw [e1, Matrix.mul_zero]
    · calc Y.toBlocks₂₁ = Y.toBlocks₂₂ * (X.toBlocks₂₂ * Y.toBlocks₂₁) := by
            rw [← Matrix.mul_assoc, e4, Matrix.one_mul]
        _ = 0 := by rw [e2, Matrix.mul_zero]

theorem toBlocks₁₁_inv_mul {g : GL V₄ F} (hg : g ∈ blockDiagGL F) :
    ((g⁻¹ : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁ * (g : Matrix V₄ V₄ F).toBlocks₁₁ = 1 := by
  rw [← toBlocks₁₁_mul_of_isBlockDiag (inv_mem hg : g⁻¹ ∈ blockDiagGL F), ← Units.val_mul,
    inv_mul_cancel, Units.val_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

theorem toBlocks₁₁_mul_inv {g : GL V₄ F} (hg : g ∈ blockDiagGL F) :
    (g : Matrix V₄ V₄ F).toBlocks₁₁ * ((g⁻¹ : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁ = 1 := by
  rw [← toBlocks₁₁_mul_of_isBlockDiag hg, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

@[expose] noncomputable def blockHom₁ (F : Type) [Field F] : blockDiagGL F →* GL (Fin 2) F where
  toFun g := ⟨((g : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁,
    (((g⁻¹ : blockDiagGL F) : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁,
    toBlocks₁₁_mul_inv g.2, toBlocks₁₁_inv_mul g.2⟩
  map_one' := by
    apply Units.ext
    change ((1 : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁ = 1
    rw [Units.val_one, ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]
  map_mul' g h := by
    apply Units.ext
    change (((g * h : blockDiagGL F) : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁ =
      ((g : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁ * ((h : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁
    rw [Subgroup.coe_mul, Units.val_mul]
    exact toBlocks₁₁_mul_of_isBlockDiag g.2

theorem coe_blockHom₁ (g : blockDiagGL F) :
    ((blockHom₁ F g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      ((g : GL V₄ F) : Matrix V₄ V₄ F).toBlocks₁₁ := rfl

theorem fromBlocks_diag_pow (A D : Matrix (Fin 2) (Fin 2) F) (n : ℕ) :
    (fromBlocks A 0 0 D) ^ n = fromBlocks (A ^ n) 0 0 (D ^ n) := by
  induction n with
  | zero => simp [Matrix.fromBlocks_one]
  | succ n ih => rw [pow_succ, ih, fromBlocks_diag_mul, ← pow_succ, ← pow_succ]

theorem diag_two_pow (a b : F) (n : ℕ) : !![a, 0; 0, b] ^ n = !![a ^ n, 0; 0, b ^ n] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]

theorem fromBlocks_diag_sub_one (A D : Matrix (Fin 2) (Fin 2) F) :
    fromBlocks A 0 0 D - 1 = fromBlocks (A - 1) 0 0 (D - 1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply]

variable [Finite F]

theorem isSqZero_of_pow_char {p : ℕ} [Fact p.Prime] [CharP F p] {h : GL V₄ F}
    (hh : h ∈ blockDiagGL F) (hp : h ^ p = 1) :
    IsSqZero h := by
  have hX := eq_fromBlocks_of_isBlockDiag (show IsBlockDiag (h : Matrix V₄ V₄ F) from hh)
  set A := (h : Matrix V₄ V₄ F).toBlocks₁₁
  set D := (h : Matrix V₄ V₄ F).toBlocks₂₂
  have hpow : (h : Matrix V₄ V₄ F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hp, Units.val_one]
  rw [hX, fromBlocks_diag_pow, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj] at hpow
  obtain ⟨hA, -, -, hD⟩ := hpow
  have hA' : (A - 1) * (A - 1) = 0 := by
    apply mul_self_eq_zero_of_pow_eq_zero (k := p)
    rw [sub_pow_char_of_commute (p := p) (Commute.one_right A), hA, one_pow, sub_self]
  have hD' : (D - 1) * (D - 1) = 0 := by
    apply mul_self_eq_zero_of_pow_eq_zero (k := p)
    rw [sub_pow_char_of_commute (p := p) (Commute.one_right D), hD, one_pow, sub_self]
  unfold IsSqZero
  rw [hX, fromBlocks_diag_sub_one, fromBlocks_diag_mul, hA', hD', Matrix.fromBlocks_zero]

theorem false_of_thm_eight_core (p : ℕ) [Fact p.Prime] [CharP F p] {G : Subgroup (GL V₄ F)}
    (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
    {z w : GL V₄ F} (hzG : z ∈ G) (hwG : w ∈ G) {lam eps beta Q : F}
    {Dz Dw : Matrix (Fin 2) (Fin 2) F}
    (hz : (z : Matrix V₄ V₄ F) = fromBlocks !![lam, 0; 0, eps] 0 0 Dz)
    (hw : (w : Matrix V₄ V₄ F) = fromBlocks !![beta, Q; 1, -beta] 0 0 Dw)
    (hbQ : beta * beta + Q = 1) (hbeta : beta ≠ 0) (hQ : Q ≠ 0) (heps : eps ≠ 0)
    (hord : ∀ k, 1 ≤ k → k < 6 → (lam * eps⁻¹) ^ k ≠ 1) : False := by
  classical
  haveI : Finite PGL(Fin 2, F) :=
    inferInstanceAs (Finite (GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F)))
  set B := blockDiagGL F
  have hzB : z ∈ B := by
    show IsBlockDiag (z : Matrix V₄ V₄ F)
    rw [hz]
    exact isBlockDiag_fromBlocks _ _
  have hwB : w ∈ B := by
    show IsBlockDiag (w : Matrix V₄ V₄ F)
    rw [hw]
    exact isBlockDiag_fromBlocks _ _
  set H₀ : Subgroup B := G.subgroupOf B
  set J : Subgroup PGL(Fin 2, F) := (H₀.map (blockHom₁ F)).map Matrix.ProjGenLinGroup.mk
  have hH₀ : ¬ p ∣ Nat.card H₀ := by
    intro hdvd
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hcG : (((c : B) : GL V₄ F)) ∈ G := c.2
    have hpow : ((c : B) : GL V₄ F) ^ p = 1 := by
      have h1 := pow_orderOf_eq_one c
      rw [hc] at h1
      have := congrArg (fun x : H₀ => ((x : B) : GL V₄ F)) h1
      simpa using this
    have h1 := hU0 _ hcG (isSqZero_of_pow_char (c : B).2 hpow)
    have hc1 : c = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact h1
    rw [hc1, orderOf_one] at hc
    exact (Fact.out : p.Prime).one_lt.ne hc
  have hJ : ¬ p ∣ Nat.card J := fun h => hH₀ (dvd_trans h (dvd_trans
    (Subgroup.card_map_dvd _ _) (Subgroup.card_map_dvd _ _)))
  have hmemJ : ∀ (g : GL V₄ F) (hg : g ∈ B), g ∈ G →
      Matrix.ProjGenLinGroup.mk (blockHom₁ F ⟨g, hg⟩) ∈ J := fun g hg hgG =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ (show (⟨g, hg⟩ : B) ∈ H₀ from hgG))
  set E : GL V₄ F := w * z * w⁻¹ with hEdef
  have hEB : E ∈ B := mul_mem (mul_mem hwB hzB) (inv_mem hwB)
  have hEG : E ∈ G := G.mul_mem (G.mul_mem hwG hzG) (G.inv_mem hwG)
  let zJ : J := ⟨_, hmemJ z hzB hzG⟩
  let EJ : J := ⟨_, hmemJ E hEB hEG⟩
  let wJ : J := ⟨_, hmemJ w hwB hwG⟩
  set Dm : Matrix (Fin 2) (Fin 2) F := !![lam, 0; 0, eps] with hDm
  set Bm : Matrix (Fin 2) (Fin 2) F := !![beta, Q; 1, -beta] with hBm
  have hρz : ((blockHom₁ F ⟨z, hzB⟩ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Dm := by
    rw [coe_blockHom₁]
    change (z : Matrix V₄ V₄ F).toBlocks₁₁ = Dm
    rw [hz, Matrix.toBlocks_fromBlocks₁₁]
  have hρw : ((blockHom₁ F ⟨w, hwB⟩ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = Bm := by
    rw [coe_blockHom₁]
    change (w : Matrix V₄ V₄ F).toBlocks₁₁ = Bm
    rw [hw, Matrix.toBlocks_fromBlocks₁₁]
  have hBB : Bm * Bm = 1 := by
    rw [hBm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | linear_combination hbQ | ring1
  have hρE : ((blockHom₁ F ⟨E, hEB⟩ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Bm * Dm * Bm := by
    have e : (⟨E, hEB⟩ : B) = ⟨w, hwB⟩ * ⟨z, hzB⟩ * (⟨w, hwB⟩ : B)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, hρw, hρz]
    congr 1
    calc (((blockHom₁ F ⟨w, hwB⟩)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = Bm * Bm * (((blockHom₁ F ⟨w, hwB⟩)⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
          rw [hBB, Matrix.one_mul]
      _ = Bm := by
          rw [Matrix.mul_assoc, ← hρw, ← Units.val_mul, mul_inv_cancel, Units.val_one,
            Matrix.mul_one]
  have hz6 : 6 ≤ orderOf zJ := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < orderOf zJ := orderOf_pos zJ
    have hm1 := pow_orderOf_eq_one zJ
    have hmk : Matrix.ProjGenLinGroup.mk ((blockHom₁ F ⟨z, hzB⟩) ^ orderOf zJ) = 1 := by
      have := congrArg Subtype.val hm1
      simpa [zJ, map_pow] using this
    rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmk
    obtain ⟨u, hu⟩ := hmk
    have hmat := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hu
    simp only [Units.val_pow_eq_pow_val, hρz, hDm, diag_two_pow] at hmat
    have h00 := congrFun (congrFun hmat 0) 0
    have h11 := congrFun (congrFun hmat 1) 1
    simp [Matrix.GeneralLinearGroup.coe_scalar] at h00 h11
    apply hord (orderOf zJ) hpos hlt
    rw [mul_pow, inv_pow, ← h00, h11, mul_inv_cancel₀ (pow_ne_zero _ heps)]
  have hEconj : EJ = wJ * zJ * wJ⁻¹ := by
    apply Subtype.ext
    simp only [EJ, zJ, wJ, Subgroup.coe_mul, Subgroup.coe_inv, ← map_mul, ← map_inv]
    rfl
  have hE6 : orderOf EJ = orderOf zJ := by
    rw [hEconj, show wJ * zJ * wJ⁻¹ = MulAut.conj wJ zJ from rfl, MulEquiv.orderOf_eq]
  have hcomm := commute_of_six_le_orderOf_pgl J hJ hz6 (x := zJ) (y := EJ) (by omega)
    (by rw [hE6]; omega)
  have hmk : Matrix.ProjGenLinGroup.mk
      (blockHom₁ F ⟨z, hzB⟩ * blockHom₁ F ⟨E, hEB⟩ *
        (blockHom₁ F ⟨E, hEB⟩ * blockHom₁ F ⟨z, hzB⟩)⁻¹) = 1 := by
    have := congrArg Subtype.val hcomm
    simp only [zJ, EJ, Subgroup.coe_mul] at this
    rw [map_mul, map_inv, map_mul, map_mul, this, mul_inv_cancel]
  rw [Matrix.ProjGenLinGroup.mk_eq_one, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmk
  obtain ⟨u, hu⟩ := hmk
  have hu' : blockHom₁ F ⟨z, hzB⟩ * blockHom₁ F ⟨E, hEB⟩ =
      Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (blockHom₁ F ⟨E, hEB⟩ * blockHom₁ F ⟨z, hzB⟩) := by
    rw [hu, inv_mul_cancel_right]
  have hmat := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hu'
  simp only [Units.val_mul, hρz, hρE, Matrix.GeneralLinearGroup.coe_scalar] at hmat
  have h01 := congrFun (congrFun hmat 0) 1
  simp [hDm, hBm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at h01
  have hne : lam ≠ eps := by
    intro h
    apply hord 1 le_rfl (by norm_num)
    rw [pow_one, h, mul_inv_cancel₀ heps]
  have hX : beta * Q * (lam - eps) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hbeta hQ) (sub_ne_zero.mpr hne)
  have hlam : lam = (u : F) * eps := by
    have : (lam - (u : F) * eps) * (beta * Q * (lam - eps)) = 0 := by linear_combination h01
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hX)
  have h10 := congrFun (congrFun hmat 1) 0
  simp [hDm, hBm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] at h10
  have hY : beta * (lam - eps) ≠ 0 := mul_ne_zero hbeta (sub_ne_zero.mpr hne)
  have heps' : eps = (u : F) * lam := by
    have : (eps - (u : F) * lam) * (beta * (lam - eps)) = 0 := by linear_combination h10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hY)
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply heps
    rw [heps', h0, mul_zero]
  have hu2 : (u : F) * (u : F) = 1 := by
    have : ((u : F) * (u : F) - 1) * lam = 0 := by
      linear_combination (-(u : F)) * heps' - hlam
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hlam0)
  apply hord 2 (by norm_num) (by norm_num)
  rw [hlam, mul_assoc, mul_inv_cancel₀ heps, mul_one, pow_two, hu2]

end CFSG.RankThree.SubgroupLists
