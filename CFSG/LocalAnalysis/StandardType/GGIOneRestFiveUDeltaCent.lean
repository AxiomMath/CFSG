module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUDeltaField
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitarySemi
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDvdFrame
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGSixLinearModelSUAut

public section

namespace CFSG.StandardType.IOneUDelta

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.SectionRank.OddCover
  CFSG.StandardType.TableBUE CFSG.StandardType.InndiagSU
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

@[expose] def nodeDiag {K : Type} [Field K] {d : ℕ} (c : Fin d) (ρ : Kˣ) : Fin d → Kˣ :=
  fun k => if k = c then ρ else 1

section Generic

variable {G M : Type} [Group G] [Group M]

theorem eq_one_of_central_hom (f : G → M) (hmul : ∀ x y, f (x * y) = f x * f y)
    (hcen : ∀ x, f x ∈ Subgroup.center M) (hG : commutator G = ⊤) (x : G) : f x = 1 := by
  let F : G →* M := MonoidHom.mk' f hmul
  have hker : commutator G ≤ F.ker := by
    rw [commutator, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      ((Subgroup.mem_center_iff.mp (hcen b)) (f a))
  have hx : x ∈ commutator G := by
    rw [hG]
    exact Subgroup.mem_top x
  exact MonoidHom.mem_ker.mp (hker hx)

end Generic

section Helpers

variable {K : Type} [Field K] {n d : ℕ}

theorem gl_central_of_projMk_eq_one {x : ↥(unitarySU 2 n K d)}
    (hx : LargeEvenProjMk (unitarySU 2 n K d) x = 1) :
    (x : GL (Fin d) K) ∈ Subgroup.center (GL (Fin d) K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have h1 := hx
  rw [LargeEvenProjMk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, largeEvenScalars_def] at h1
  exact h1

theorem gl_eq_smul_of_projU_eq [Finite K] {x y : ↥(unitarySU 2 n K d)}
    (hxy : InndiagSU.projU n d K x = InndiagSU.projU n d K y) :
    ∃ c : Kˣ, (x : GL (Fin d) K) =
      Matrix.GeneralLinearGroup.scalar (Fin d) c * (y : GL (Fin d) K) := by
  have h1 : InndiagSU.projU n d K (x * y⁻¹) = 1 := by
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  have hz := gl_central_of_projMk_eq_one (n := n) (d := d) (x := x * y⁻¹) h1
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨c, hc⟩ := hz
  refine ⟨c, ?_⟩
  have hx : (x : GL (Fin d) K) =
      ((x * y⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * (y : GL (Fin d) K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [hx, ← hc]

theorem coe_diagHom' {d : ℕ} (σ : Fin d → Kˣ) :
    ((diagHom d σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      Matrix.diagonal fun k => (σ k : K) :=
  coe_diagHom σ

theorem trace_diagHom' {d : ℕ} (σ : Fin d → Kˣ) :
    Matrix.trace ((diagHom d σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      ∑ k, ((σ k : Kˣ) : K) := by
  rw [coe_diagHom', Matrix.trace_diagonal]

theorem exists_block_of_diag [Finite K] (h : UnitaryFieldData 2 n K) (S : Finset (Fin d))
    (σ : Fin d → Kˣ) (hnorm : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1) (hprod : ∏ k, σ k = 1)
    (hS : ∀ k, k ∉ S → σ k = 1) :
    ∃ u : ↥(blockSU (n := n) (K := K) S), (u : GL (Fin d) K) = diagHom d σ := by
  have hmem : diagHom d σ ∈ unitarySU 2 n K d :=
    TableBUE.mem_unitarySU_of_mem_primeFormUnitary h
      (TableBUD.diagHom_mem_primeFormUnitary h hnorm)
      (by rw [CFSG.SectionRank.OddCover.det_diagHom, ← Units.coe_prod, hprod, Units.val_one])
  refine ⟨⟨⟨diagHom d σ, hmem⟩, ?_⟩, rfl⟩
  intro i j hij
  rw [coe_diagHom', Matrix.diagonal_apply]
  by_cases hij' : i = j
  · subst hij'
    have hi : i ∉ S := by
      rcases hij with hi | hi
      · exact hi
      · exact hi
    rw [if_pos rfl, hS i hi, Units.val_one, Matrix.one_apply_eq]
  · rw [if_neg hij', Matrix.one_apply_ne hij']

end Helpers

section Sums

variable {K : Type} [Field K]

theorem prod_two_point {d : ℕ} (a b : Fin d) (hab : a ≠ b) (x y : Kˣ) :
    ∏ k, (if k = a then x else if k = b then y else 1) = x * y := by
  have h : ∀ k : Fin d, (if k = a then x else if k = b then y else 1) =
      (if k = a then x else 1) * (if k = b then y else 1) := by
    intro k
    by_cases ha : k = a
    · subst ha
      simp [hab]
    · by_cases hb : k = b
      · subst hb
        simp [ha]
      · simp [ha, hb]
  rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_mul_distrib]
  simp

theorem prod_three_point {d : ℕ} (i j k0 : Fin d) (hij : i ≠ j) (hik : i ≠ k0) (hjk : j ≠ k0)
    (a b c : Kˣ) :
    ∏ k, (if k = i then a else if k = j then b else if k = k0 then c else 1) = a * b * c := by
  have h : ∀ k : Fin d, (if k = i then a else if k = j then b else if k = k0 then c else 1) =
      (if k = i then a else 1) * (if k = j then b else 1) * (if k = k0 then c else 1) := by
    intro k
    by_cases hi : k = i
    · subst hi
      simp [hij, hik]
    · by_cases hj : k = j
      · subst hj
        simp [hi, hjk]
      · by_cases hk : k = k0
        · subst hk
          simp [hi, hj]
        · simp [hi, hj, hk]
  rw [Finset.prod_congr rfl (fun k _ => h k), Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp

theorem sum_three_point [CharP K 2] {d : ℕ} (i j k0 : Fin d) (hij : i ≠ j) (hik : i ≠ k0)
    (hjk : j ≠ k0) (a b c : K) :
    ∑ k : Fin d, (if k = i then a else if k = j then b else if k = k0 then c else 1) =
      (d : K) + (a - 1) + (b - 1) + (c - 1) := by
  have h : ∀ k : Fin d, (if k = i then a else if k = j then b else if k = k0 then c else 1) =
      1 + ((if k = i then a - 1 else 0) + (if k = j then b - 1 else 0) +
        (if k = k0 then c - 1 else 0)) := by
    intro k
    by_cases hi : k = i
    · subst hi
      simp [hij, hik]
    · by_cases hj : k = j
      · subst hj
        simp [hi, hjk]
      · by_cases hk : k = k0
        · subst hk
          simp [hi, hj]
        · simp [hi, hj, hk]
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

end Sums

section Main

variable {K : Type} [Field K] {n d : ℕ}

@[expose] def ActsR (α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (σ : Fin d → Kˣ) : Prop :=
  ∃ hD : diagHom d σ ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)),
    ∀ u : ↥(unitarySU 2 n K d),
      α (InndiagSU.projU n d K u) = InndiagSU.projU n d K (LineU.conjN (diagHom d σ) hD u)

theorem normalizer_of_prime [Finite K] (h : UnitaryFieldData 2 n K) {B : GL (Fin d) K}
    (hB : B ∈ primeFormUnitary h (idGram K d)) :
    B ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 := InndiagSU.semilin_mem h hB (1 : K ≃+* K) ⟨x, hx⟩
    rw [SUModel.glAut_one_apply] at h1
    exact h1
  · intro hx
    have hB' : B⁻¹ ∈ primeFormUnitary h (idGram K d) := Subgroup.inv_mem _ hB
    have h2 := InndiagSU.semilin_mem h hB' (1 : K ≃+* K) ⟨B * x * B⁻¹, hx⟩
    rw [SUModel.glAut_one_apply, inv_inv] at h2
    have e : B⁻¹ * (B * x * B⁻¹) * B = x := by group
    rw [e] at h2
    exact h2

theorem permGL_swap_apply {K : Type} [Field K] {d : ℕ} (a z i j : Fin d) :
    ((CFSG.RankThree.Classical.permGL (Equiv.swap a z) : GL (Fin d) K) :
      Matrix (Fin d) (Fin d) K) i j = if Equiv.swap a z i = j then 1 else 0 := by
  show (Equiv.Perm.permMatrix K (Equiv.swap a z)⁻¹) i j = _
  rw [Equiv.swap_inv]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]

theorem trace_glAut (φ : K ≃+* K) (X : GL (Fin d) K) :
    Matrix.trace ((glAut φ X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      φ (Matrix.trace (X : Matrix (Fin d) (Fin d) K)) := by
  rw [SUModel.glAut_eq_map]
  simp [Matrix.trace, map_sum]

theorem mul_center_of_hom {G : Type} [Group G] (X : G → G) (hX : ∀ a b, X (a * b) = X a * X b)
    (a b s t : G) (hsa : X a = s * a) (hsb : X b = t * b) (hs : s ∈ Subgroup.center G)
    (ht : t ∈ Subgroup.center G) : X (a * b) * (a * b)⁻¹ = s * t := by
  have hat : a * t = t * a := Subgroup.mem_center_iff.mp ht a
  rw [hX, hsa, hsb]
  calc s * a * (t * b) * (a * b)⁻¹ = s * (a * t) * (b * b⁻¹) * a⁻¹ := by group
    _ = s * (t * a) * a⁻¹ := by rw [hat, mul_inv_cancel, mul_one]
    _ = s * t := by group

theorem exists_mem_ne_of_one_lt_card {d : ℕ} (S : Finset (Fin d)) (hS : 1 < S.card) (a : Fin d) :
    ∃ z ∈ S, z ≠ a := by
  by_contra hcon
  push_neg at hcon
  have hsub : S ⊆ {a} := fun z hz => Finset.mem_singleton.mpr (hcon z hz)
  have := Finset.card_le_card hsub
  rw [Finset.card_singleton] at this
  omega

theorem isBlockOn_swap {K : Type} [Field K] {d : ℕ} (S : Finset (Fin d)) {a z : Fin d}
    (ha : a ∈ S) (hz : z ∈ S) :
    TableBUE.IsBlockOn S
      ((CFSG.RankThree.Classical.permGL (Equiv.swap a z) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) := by
  intro i j hij
  rw [permGL_swap_apply]
  rcases hij with hi | hj
  · have hi' : Equiv.swap a z i = i :=
      Equiv.swap_apply_of_ne_of_ne (fun e => hi (by rw [e]; exact ha))
        (fun e => hi (by rw [e]; exact hz))
    simp only [hi', Matrix.one_apply]
  · have hj' : Equiv.swap a z j = j :=
      Equiv.swap_apply_of_ne_of_ne (fun e => hj (by rw [e]; exact ha))
        (fun e => hj (by rw [e]; exact hz))
    simp only [Equiv.swap_apply_eq_iff, hj', Matrix.one_apply]

theorem centR_of_fix [Finite K] (h : UnitaryFieldData 2 n K) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hn : 1 ≤ n) (hd : 5 ≤ d) (c : Fin d) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (α : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))))
    (hαp : α ^ p = 1)
    (hfix : ∀ u ∈ blockSU (n := n) (K := K) (Finset.univ.erase c),
      α (InndiagSU.projU n d K u) = InndiagSU.projU n d K u) :
    ∃ ρ : Kˣ, ρ ^ p = 1 ∧ ActsR α (nodeDiag c ρ) := by
  classical
  have hCh : CharP K 2 := h.charP
  have hd3 : 3 ≤ d := by omega
  have hq : ¬(d = 3 ∧ 2 ^ n = 2) := fun ⟨h1, _⟩ => by omega
  set S : Finset (Fin d) := Finset.univ.erase c with hSdef
  have hcS : c ∉ S := by simp [hSdef]
  have hSmem : ∀ k, k ∈ S ↔ k ≠ c := fun k => by simp [hSdef]
  have hScard : S.card = d - 1 := by
    rw [hSdef, Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  have hS3 : 3 ≤ S.card := by omega
  have hS2 : 1 < S.card := by omega
  obtain ⟨B, hB, hsl⟩ := InndiagSU.exists_isSemilin h hd3 hq α
  set τ := InndiagSU.fieldFactorU h hd3 hq α with hτdef
  have hQ : commutator ↥(blockSU (n := n) (K := K) S) = ⊤ :=
    Group.isPerfect_def.mp (TableBUE.isQuasisimple_blockSU S h hK hS3 (by
      intro he
      have := congrArg Prod.fst he
      simp only at this
      omega)).1
  have hcen : ∀ g : ↥(blockSU (n := n) (K := K) S),
      (B * glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹) *
        ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K)⁻¹ ∈ Subgroup.center (GL (Fin d) K) := by
    intro g
    have hv := hsl (g : ↥(unitarySU 2 n K d))
      ⟨B * glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹,
        InndiagSU.semilin_mem h hB τ (g : ↥(unitarySU 2 n K d))⟩ rfl
    have hfg := hfix (g : ↥(unitarySU 2 n K d)) g.2
    obtain ⟨c', hc'⟩ := gl_eq_smul_of_projU_eq (hv.symm.trans hfg)
    have hc'' : B * glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) c' * ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) :=
      hc'
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    refine ⟨c', ?_⟩
    rw [hc'']
    group
  have hmulX : ∀ X Y : GL (Fin d) K, B * glAut τ (X * Y) * B⁻¹ =
      (B * glAut τ X * B⁻¹) * (B * glAut τ Y * B⁻¹) := by
    intro X Y
    rw [map_mul]
    group
  have hblock0 : ∀ g : ↥(blockSU (n := n) (K := K) S),
      (B * glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹) *
        ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K)⁻¹ = 1 := by
    intro g
    refine eq_one_of_central_hom
      (fun g : ↥(blockSU (n := n) (K := K) S) =>
        (B * glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹) *
          ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K)⁻¹) ?_ hcen hQ g
    intro g1 g2
    have hX := mul_center_of_hom (fun X : GL (Fin d) K => B * glAut τ X * B⁻¹) hmulX
      ((g1 : ↥(unitarySU 2 n K d)) : GL (Fin d) K) ((g2 : ↥(unitarySU 2 n K d)) : GL (Fin d) K)
      ((B * glAut τ ((g1 : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹) *
          ((g1 : ↥(unitarySU 2 n K d)) : GL (Fin d) K)⁻¹)
      ((B * glAut τ ((g2 : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹) *
          ((g2 : ↥(unitarySU 2 n K d)) : GL (Fin d) K)⁻¹)
      (by rw [inv_mul_cancel_right]) (by rw [inv_mul_cancel_right])
      (hcen g1) (hcen g2)
    simp only [Subgroup.coe_mul]
    exact hX
  have hblock : ∀ g : ↥(blockSU (n := n) (K := K) S),
      B * glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹ =
        ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) := fun g =>
    mul_inv_eq_one.mp (hblock0 g)
  have hτtr : ∀ g : ↥(blockSU (n := n) (K := K) S),
      τ (Matrix.trace (((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)) =
        Matrix.trace (((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro g
    have e1 : glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
        B⁻¹ * ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B := by
      calc glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K)
          = B⁻¹ * (B * glAut τ ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B⁻¹) * B := by group
        _ = B⁻¹ * ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B := by rw [hblock g]
    rw [← trace_glAut, e1, Units.val_mul, Units.val_mul, Matrix.trace_mul_comm,
      ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hτx : ∀ x : K, x ^ (2 ^ n + 1) = 1 → τ x = x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero _)] at hx
      exact zero_ne_one hx
    obtain ⟨i, hi, j, hj, k0, hk0, hij, hik, hjk⟩ :=
      Finset.two_lt_card.mp (by omega : 2 < S.card)
    set x' : Kˣ := Units.mk0 x hx0 with hx'
    have hx'K : ((x' : Kˣ) : K) = x := rfl
    have hxq : x' ^ (2 ^ n + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hx'K, hx, Units.val_one]
    set m : ℕ := 2 ^ (n - 1) + 1 with hm
    have h2m : 2 * m = 2 ^ n + 2 := by
      have : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
    set y' : Kˣ := (x'⁻¹) ^ m with hy'
    have hyq : y' ^ (2 ^ n + 1) = 1 := by
      rw [hy', ← pow_mul, mul_comm, pow_mul, inv_pow, hxq, inv_one, one_pow]
    have hyK : ((y' : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hyq, Units.val_one]
    have hxK : ((x' : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val, hxq, Units.val_one]
    have hy2 : y' * y' * x' = 1 := by
      rw [hy', ← pow_add, show m + m = (2 ^ n + 1) + 1 by omega, pow_succ, inv_pow, hxq, inv_one,
        one_mul, inv_mul_cancel]
    set σ : Fin d → Kˣ := fun k => if k = i then y' else if k = j then y' else if k = k0 then x'
      else 1 with hσ
    have hprod : ∏ k, σ k = 1 := by
      rw [hσ, prod_three_point i j k0 hij hik hjk, hy2]
    have hnorm : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
      intro k
      rw [hσ]
      dsimp only
      split_ifs
      · exact hyK
      · exact hyK
      · exact hxK
      · simp
    have hSσ : ∀ k, k ∉ S → σ k = 1 := by
      intro k hk
      have h1 : k ≠ i := fun e => hk (by rw [e]; exact hi)
      have h2 : k ≠ j := fun e => hk (by rw [e]; exact hj)
      have h3 : k ≠ k0 := fun e => hk (by rw [e]; exact hk0)
      rw [hσ]
      dsimp only
      rw [if_neg h1, if_neg h2, if_neg h3]
    obtain ⟨u, hu⟩ := exists_block_of_diag h S σ hnorm hprod hSσ
    have hT := hτtr u
    rw [hu, trace_diagHom'] at hT
    have hfun : ∀ k, ((σ k : Kˣ) : K) =
        (if k = i then ((y' : Kˣ) : K) else if k = j then ((y' : Kˣ) : K)
          else if k = k0 then x else 1) := by
      intro k
      rw [hσ]
      dsimp only
      split_ifs <;> simp [hx'K]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsum : ∑ k, ((σ k : Kˣ) : K) = (d : K) + x + 1 := by
      rw [Finset.sum_congr rfl (fun k _ => hfun k),
        sum_three_point i j k0 hij hik hjk]
      linear_combination ((((y' : Kˣ) : K)) - 2) * h2
    rw [hsum] at hT
    simp only [map_add, map_one, map_natCast] at hT
    linear_combination hT
  have hτone : τ = 1 := RingEquiv.ext (fun x => fieldAut_eq_id_of_fix hn hK τ hτx x)
  have hcommB : ∀ g : ↥(blockSU (n := n) (K := K) S),
      B * ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
        ((g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * B := by
    intro g
    have h1 := hblock g
    rw [hτone, SUModel.glAut_one_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  obtain ⟨ω, hω⟩ := exists_orderOf_eq_succ hn hK
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hωq : ω ^ (2 ^ n + 1) = 1 := by
    rw [← hω]
    exact pow_orderOf_eq_one ω
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hω
    omega
  have hωinv : ω⁻¹ ≠ ω := by
    intro he
    have h2' : ω ^ 2 = 1 := by
      rw [pow_two]
      calc ω * ω = ω * ω⁻¹ := by rw [he]
        _ = 1 := mul_inv_cancel ω
    have hdvd : orderOf ω ∣ 2 := orderOf_dvd_of_pow_eq_one h2'
    rw [hω] at hdvd
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hoff : ∀ a ∈ S, ∀ y : Fin d, y ≠ a →
      ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) a y = 0 ∧
        ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) y a = 0 := by
    intro a ha y hya
    obtain ⟨z, hz, hza⟩ := exists_mem_ne_of_one_lt_card S hS2 a
    set σ : Fin d → Kˣ := fun k => if k = a then ω else if k = z then ω⁻¹ else 1 with hσ
    have hprod : ∏ k, σ k = 1 := by
      rw [hσ, prod_two_point a z hza.symm ω ω⁻¹, mul_inv_cancel]
    have hnorm : ∀ k, ((σ k : Kˣ) : K) ^ (2 ^ n + 1) = 1 := by
      intro k
      rw [hσ]
      dsimp only
      split_ifs
      · rw [← Units.val_pow_eq_pow_val, hωq, Units.val_one]
      · rw [← Units.val_pow_eq_pow_val, inv_pow, hωq, inv_one, Units.val_one]
      · simp
    have hSσ : ∀ k, k ∉ S → σ k = 1 := by
      intro k hk
      have h1 : k ≠ a := fun e => hk (by rw [e]; exact ha)
      have h2' : k ≠ z := fun e => hk (by rw [e]; exact hz)
      rw [hσ]
      dsimp only
      rw [if_neg h1, if_neg h2']
    obtain ⟨u, hu⟩ := exists_block_of_diag h S σ hnorm hprod hSσ
    have hc := hcommB u
    rw [hu] at hc
    have hσa : σ a = ω := by
      rw [hσ]
      dsimp only
      rw [if_pos rfl]
    have hσy : σ y ≠ ω := by
      rw [hσ]
      dsimp only
      split_ifs with h1 h2'
      · exact absurd h1 hya
      · exact hωinv
      · exact fun e => hω1 e.symm
    constructor
    · exact TableBUE.entry_eq_zero_of_commute hc (by
        rw [hσa]
        exact fun e => hσy e.symm)
    · exact TableBUE.entry_eq_zero_of_commute hc (by
        rw [hσa]
        exact hσy)
  have hoffall : ∀ x y : Fin d, x ≠ y →
      ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) x y = 0 := by
    intro x y hxy
    by_cases hx : x ∈ S
    · exact (hoff x hx y hxy.symm).1
    · have hxc : x = c := by
        by_contra hne
        exact hx ((hSmem x).mpr hne)
      have hyc : y ≠ c := fun e => hxy (hxc.trans e.symm)
      exact (hoff y ((hSmem y).mpr hyc) x hxy).2
  have hBne : ∀ k, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k ≠ 0 := by
    intro k hk
    have e := congrArg (fun X : GL (Fin d) K => ((X : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k)
      (mul_inv_cancel B)
    simp only [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at e
    rw [Finset.sum_eq_single k] at e
    · rw [hk, zero_mul] at e
      exact zero_ne_one e
    · intro l _ hl
      rw [hoffall k l (Ne.symm hl), zero_mul]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  have hdiag_eq : ∀ a ∈ S, ∀ z ∈ S,
      ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) a a =
        ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) z z := by
    intro a ha z hz
    by_cases haz : a = z
    · rw [haz]
    set Pg : GL (Fin d) K := CFSG.RankThree.Classical.permGL (Equiv.swap a z) with hPg
    have hPmem : Pg ∈ unitarySU 2 n K d := LineU.permGL_mem_unitarySU h (Equiv.swap a z)
    have hPblock : (⟨Pg, hPmem⟩ : ↥(unitarySU 2 n K d)) ∈ blockSU (n := n) (K := K) S :=
      isBlockOn_swap S ha hz
    have hc : B * Pg = Pg * B := hcommB ⟨⟨Pg, hPmem⟩, hPblock⟩
    have hPaz : (Pg : Matrix (Fin d) (Fin d) K) a z = 1 := by
      rw [hPg, permGL_swap_apply, Equiv.swap_apply_left, if_pos rfl]
    have e := congrArg (fun X : GL (Fin d) K => (X : Matrix (Fin d) (Fin d) K) a z) hc
    simp only [Units.val_mul] at e
    have hL : ∑ k, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) a k *
        (Pg : Matrix (Fin d) (Fin d) K) k z =
        ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) a a *
          (Pg : Matrix (Fin d) (Fin d) K) a z := by
      rw [Finset.sum_eq_single a]
      · intro l _ hl
        rw [hoffall a l (Ne.symm hl), zero_mul]
      · intro h'
        exact absurd (Finset.mem_univ a) h'
    have hR : ∑ k, (Pg : Matrix (Fin d) (Fin d) K) a k *
        ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k z =
        (Pg : Matrix (Fin d) (Fin d) K) a z *
          ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) z z := by
      rw [Finset.sum_eq_single z]
      · intro l _ hl
        rw [hoffall l z hl, mul_zero]
      · intro h'
        exact absurd (Finset.mem_univ z) h'
    rw [Matrix.mul_apply, Matrix.mul_apply, hL, hR, hPaz, mul_one, one_mul] at e
    exact e
  obtain ⟨s0, hs0⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hs0c : s0 ≠ c := (hSmem s0).mp hs0
  set γ : K := ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) s0 s0 with hγdef
  set β : K := ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) c c with hβdef
  have hγne : γ ≠ 0 := hBne s0
  have hβne : β ≠ 0 := hBne c
  have hγ : ∀ k ∈ S, ((B : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) k k = γ :=
    fun k hk => hdiag_eq k hk s0 hs0
  set g0 : Kˣ := Units.mk0 γ hγne with hg0
  set ρu : Kˣ := Units.mk0 (γ⁻¹ * β) (mul_ne_zero (inv_ne_zero hγne) hβne) with hρu
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹ ∈ Subgroup.center (GL (Fin d) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨g0⁻¹, rfl⟩
  have hDB : diagHom d (nodeDiag c ρu) =
      Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹ * B := by
    apply Units.ext
    rw [coe_diagHom', Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_apply]
    by_cases hij : i = j
    · subst hij
      by_cases hic : i = c
      · subst hic
        simp [nodeDiag, hρu, hg0, hγdef, hβdef]
      · have hiS : i ∈ S := (hSmem i).mpr hic
        simp [nodeDiag, hic, hγ i hiS, hg0, hγne]
    · rw [if_neg hij, hoffall i j hij, mul_zero]
  have hscN : Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹ ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx := Subgroup.mem_center_iff.mp hsc x
    have e : Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹ * x *
        (Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹)⁻¹ = x := by
      rw [← hx]
      group
    rw [e]
  have hDmem : diagHom d (nodeDiag c ρu) ∈
      Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)) := by
    rw [hDB]
    exact Subgroup.mul_mem _ hscN (normalizer_of_prime h hB)
  have hact : ∀ u : ↥(unitarySU 2 n K d),
      α (InndiagSU.projU n d K u) =
        InndiagSU.projU n d K (LineU.conjN (diagHom d (nodeDiag c ρu)) hDmem u) := by
    intro u
    have hv := hsl u ⟨B * glAut τ (u : GL (Fin d) K) * B⁻¹, InndiagSU.semilin_mem h hB τ u⟩ rfl
    rw [hv]
    congr 1
    apply Subtype.ext
    show B * glAut τ (u : GL (Fin d) K) * B⁻¹ =
      (diagHom d (nodeDiag c ρu) : GL (Fin d) K) * (u : GL (Fin d) K) *
        (diagHom d (nodeDiag c ρu) : GL (Fin d) K)⁻¹
    rw [hτone, SUModel.glAut_one_apply, hDB]
    have hc := Subgroup.mem_center_iff.mp hsc (B * (u : GL (Fin d) K) * B⁻¹)
    have e : Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹ * B * (u : GL (Fin d) K) *
        (Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹ * B)⁻¹ =
        (Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹) * (B * (u : GL (Fin d) K) * B⁻¹) *
          (Matrix.GeneralLinearGroup.scalar (Fin d) g0⁻¹)⁻¹ := by
      group
    rw [e, ← hc]
    group
  set D : GL (Fin d) K := diagHom d (nodeDiag c ρu) with hDdef
  have hiter : ∀ m : ℕ, ∀ u : ↥(unitarySU 2 n K d), ∃ v : ↥(unitarySU 2 n K d),
      ((v : ↥(unitarySU 2 n K d)) : GL (Fin d) K) = (D ^ m) * (u : GL (Fin d) K) * (D ^ m)⁻¹ ∧
        (α ^ m) (InndiagSU.projU n d K u) = InndiagSU.projU n d K v := by
    intro m
    induction m with
    | zero =>
      intro u
      exact ⟨u, by simp, by simp⟩
    | succ m ih =>
      intro u
      obtain ⟨w, hw1, hw2⟩ := ih (LineU.conjN D hDmem u)
      refine ⟨w, ?_, ?_⟩
      · rw [hw1, pow_succ]
        simp only [LineU.conjN, _root_.mul_inv_rev, mul_assoc]
      · rw [pow_succ, MulAut.mul_apply, hact u, hw2]
  have hDp : D ^ p = diagHom d (nodeDiag c (ρu ^ p)) := by
    rw [hDdef, ← map_pow]
    congr 1
    funext k
    by_cases hk : k = c
    · subst hk
      simp [nodeDiag]
    · simp [nodeDiag, hk]
  have hρp : ρu ^ p = 1 := by
    set P : ↥(unitarySU 2 n K d) :=
      ⟨CFSG.RankThree.Classical.permGL (Equiv.swap s0 c),
        LineU.permGL_mem_unitarySU h (Equiv.swap s0 c)⟩
      with hPdef
    obtain ⟨v, hv1, hv2⟩ := hiter p P
    rw [hαp, MulAut.one_apply] at hv2
    obtain ⟨c', hc'⟩ := gl_eq_smul_of_projU_eq hv2.symm
    have hEq : D ^ p * ((P : ↥(unitarySU 2 n K d)) : GL (Fin d) K) * (D ^ p)⁻¹ =
        Matrix.GeneralLinearGroup.scalar (Fin d) c' *
          ((P : ↥(unitarySU 2 n K d)) : GL (Fin d) K) := by
      rw [← hv1]
      exact hc'
    have hEq2 := mul_inv_eq_iff_eq_mul.mp hEq
    rw [hDp] at hEq2
    have hcoe := congrArg (fun X : GL (Fin d) K => (X : Matrix (Fin d) (Fin d) K)) hEq2
    simp only [Units.val_mul, coe_diagHom', Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at hcoe
    have hWsc : ((P : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
        CFSG.RankThree.Classical.permGL (Equiv.swap s0 c) := rfl
    have hW1 : ((CFSG.RankThree.Classical.permGL (Equiv.swap s0 c) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) s0 c = 1 := by
      rw [permGL_swap_apply, Equiv.swap_apply_left, if_pos rfl]
    have hW2 : ((CFSG.RankThree.Classical.permGL (Equiv.swap s0 c) : GL (Fin d) K) :
        Matrix (Fin d) (Fin d) K) c s0 = 1 := by
      rw [permGL_swap_apply, Equiv.swap_apply_right, if_pos rfl]
    have h1 := congrFun (congrFun hcoe s0) c
    have h2 := congrFun (congrFun hcoe c) s0
    rw [hWsc] at h1 h2
    have hn0 : nodeDiag c (ρu ^ p) s0 = 1 := by simp [nodeDiag, hs0c]
    have hc0 : nodeDiag c (ρu ^ p) c = ρu ^ p := by simp [nodeDiag]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hW1, hW2, hn0, hc0, Units.val_one,
      Units.val_pow_eq_pow_val, mul_one, one_mul] at h1 h2
    have hx : ((ρu : K)) ^ p * ((ρu : K)) ^ p = 1 := by
      linear_combination (((ρu : K)) ^ p) * h2 - h1
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    have hsq : ((ρu : K) ^ p + 1) ^ 2 = 0 := by
      linear_combination hx + ((ρu : K) ^ p) * h2' + h2'
    have hx1 : (ρu : K) ^ p + 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
    have hxeq : (ρu : K) ^ p = 1 := by
      linear_combination hx1 - h2'
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hxeq, Units.val_one])
  exact ⟨ρu, hρp, hDmem, hact⟩

end Main

end CFSG.StandardType.IOneUDelta

end
