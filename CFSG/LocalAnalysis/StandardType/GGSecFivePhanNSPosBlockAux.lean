module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosTorus
public import CFSG.ClassicalInvolution.Phan.Center
import CFSG.ClassicalGroups.Unitary.Base
import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix

open scoped MatrixGroups

theorem ggNSPosPB_diag_comm_block {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {a b : Fin n} {d : Fin n → K} (hda : d a = d b) {A : Su K 2 f n}
    (hA : A ∈ ggSuPairBlock K 2 f n a b) :
    Matrix.diagonal d * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Matrix.diagonal d := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : i ∈ ({a, b} : Finset (Fin n))
  · by_cases hj : j ∈ ({a, b} : Finset (Fin n))
    · rw [Finset.mem_insert, Finset.mem_singleton] at hi hj
      obtain hi | hi := hi
      · obtain hj | hj := hj
        · subst hi; subst hj; ring
        · subst hi; subst hj; rw [hda]; ring
      · obtain hj | hj := hj
        · subst hi; subst hj; rw [hda]; ring
        · subst hi; subst hj; ring
    · rw [Finset.mem_insert, Finset.mem_singleton] at hi
      have hj' : j ≠ a ∧ j ≠ b := by
        constructor <;> intro h <;> exact hj (by rw [Finset.mem_insert, Finset.mem_singleton]; tauto)
      have h1 : (((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j =
          (1 : Matrix (Fin n) (Fin n) K) i j := hA i j (Or.inr hj')
      rw [h1]
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, mul_one, one_mul]
      · rw [Matrix.one_apply_ne hij, mul_zero, zero_mul]
  · have hi' : i ≠ a ∧ i ≠ b := by
      constructor <;> intro h <;> exact hi (by rw [Finset.mem_insert, Finset.mem_singleton]; tauto)
    have h1 : (((A : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) i j =
        (1 : Matrix (Fin n) (Fin n) K) i j := hA i j (Or.inl hi')
    rw [h1]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, mul_one, one_mul]
    · rw [Matrix.one_apply_ne hij, mul_zero, zero_mul]

private lemma ggNSPosPB1_permMatrix_apply {K : Type} [Field K] {n : ℕ} (τ : Equiv.Perm (Fin n))
    (i j : Fin n) : (τ.permMatrix K) i j = if j = τ i then 1 else 0 := by
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  by_cases h : j = τ i
  · simp [h]
  · have h' : τ i ≠ j := fun hh => h hh.symm
    simp [h, h']

private lemma ggNSPosPB1_perm_mul_apply {K : Type} [Field K] {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (τ : Equiv.Perm (Fin n)) (i k : Fin n) :
    (τ.permMatrix K * G) i k = G (τ i) k := by
  rw [Matrix.mul_apply]
  simp only [ggNSPosPB1_permMatrix_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

private lemma ggNSPosPB1_mul_perm_apply {K : Type} [Field K] {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (τ : Equiv.Perm (Fin n)) (i k : Fin n) :
    (G * τ.permMatrix K) i k = G i (τ⁻¹ k) := by
  rw [Matrix.mul_apply]
  have h : ∀ l, G i l * (τ.permMatrix K) l k = (if l = τ⁻¹ k then G i l else 0) := by
    intro l
    by_cases hl : l = τ⁻¹ k
    · subst hl
      rw [ggNSPosPB1_permMatrix_apply, if_pos (by simp), if_pos rfl, mul_one]
    · have hk : ¬ k = τ l := by
        intro hk
        exact hl (by rw [hk]; simp)
      rw [ggNSPosPB1_permMatrix_apply, if_neg hk, if_neg hl, mul_zero]
  simp only [h]
  rw [Finset.sum_ite_eq']
  simp

private lemma ggNSPosPB1_perm_conj_apply {K : Type} [Field K] {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (τ : Equiv.Perm (Fin n)) (hτ : τ * τ = 1) (i j : Fin n) :
    (τ.permMatrix K * G * τ.permMatrix K) i j = G (τ i) (τ j) := by
  have hτk : ∀ k, τ (τ k) = k := by
    intro k
    have h := congrArg (fun e : Equiv.Perm (Fin n) => e k) hτ
    simpa [Equiv.Perm.mul_apply] using h
  rw [Matrix.mul_apply]
  have h1 : ∀ k, (τ.permMatrix K * G) i k = G (τ i) k :=
    fun k => ggNSPosPB1_perm_mul_apply G τ i k
  simp only [h1]
  have h3 : ∀ k, G (τ i) k * (τ.permMatrix K) k j = (if k = τ j then G (τ i) k else 0) := by
    intro k
    rw [ggNSPosPB1_permMatrix_apply]
    by_cases hk : k = τ j
    · subst hk
      rw [if_pos (by rw [hτk]), if_pos rfl, mul_one]
    · rw [if_neg hk]
      have : j ≠ τ k := by
        intro h
        exact hk (by rw [h, hτk k])
      rw [if_neg this, mul_zero]
  simp only [h3]
  rw [Finset.sum_ite_eq']
  simp

private lemma ggNSPosPB1_diag_perm_apply {K : Type} [Field K] {n : ℕ}
    (d : Fin n → K) (G : Matrix (Fin n) (Fin n) K) (τ : Equiv.Perm (Fin n))
    (hτ : τ * τ = 1) (i : Fin n) :
    (Matrix.diagonal d * τ.permMatrix K * G * τ.permMatrix K) i i =
      d i * G (τ i) (τ i) := by
  rw [show Matrix.diagonal d * τ.permMatrix K * G * τ.permMatrix K =
      Matrix.diagonal d * (τ.permMatrix K * G * τ.permMatrix K) by
        simp only [Matrix.mul_assoc],
    Matrix.diagonal_mul, ggNSPosPB1_perm_conj_apply G τ hτ i i]

theorem ggNSPosPB_diag_eq {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a b : Fin n) (hab : a ≠ b) (r : MulAut ↥Bs)
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹)
    {t : ↥Bs} (ht : r t = t) {g : GL (Fin n) K} (hdg : ggIsDiagMat g)
    (hact : GGInducesUnitary (p := 2) (f := f) ψ (t : G) g) :
    ∀ d : Fin n → K, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d →
      d a = d b := by
  intro d hgd
  have hactAll := hact.2
  let P : Su K 2 f n := ggPermSU (K := K) (f := f) (Equiv.swap a b)
  have hPval : (((P : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Equiv.swap a b).permMatrix K := rfl
  have hτ : (Equiv.swap a b) * (Equiv.swap a b) = 1 := Equiv.swap_mul_self a b
  have hP2 : P * P = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    apply Units.ext
    rw [Units.val_mul, hPval, ← Matrix.permMatrix_mul, hτ, Matrix.permMatrix_one, Units.val_one]
  have hPinv : P⁻¹ = P := inv_eq_of_mul_eq_one_right hP2
  have hT : (t : G) = ψ P * (t : G) * (ψ P)⁻¹ := by
    have h1 := hr t
    rw [ht] at h1
    exact h1
  obtain ⟨y, hy, hyact⟩ := hactAll P
  have hpsi : ψ y = ψ P := by
    rw [← hyact]
    nth_rewrite 1 [hT]
    group
  let z : Su K 2 f n := y * P⁻¹
  have hzval : ((z : Su K 2 f n) : GL (Fin n) K) =
      (g : GL (Fin n) K) * ((P : Su K 2 f n) : GL (Fin n) K) * (g⁻¹ : GL (Fin n) K) *
        ((P : Su K 2 f n) : GL (Fin n) K) := by
    change ((y * P⁻¹ : Su K 2 f n) : GL (Fin n) K) = _
    have hPinv' : ((P⁻¹ : Su K 2 f n) : GL (Fin n) K) = ((P : Su K 2 f n) : GL (Fin n) K) :=
      congrArg Subtype.val hPinv
    rw [Subgroup.coe_mul, hPinv', hy]
  have hzker : z ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    change ψ (y * P⁻¹) = 1
    rw [map_mul, MonoidHom.map_inv, hpsi]
    group
  have hzcenter : z ∈ Subgroup.center (Su K 2 f n) := h.ker hzker
  have hn4 : 4 ≤ n := h.four_le
  have hle : ({a, b} : Finset (Fin n)).card ≤ 2 := by
    simpa using Finset.card_insert_le a ({b} : Finset (Fin n))
  have hpos : 0 < (({a, b} : Finset (Fin n))ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin]
    omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  obtain ⟨hka, hkb⟩ := hk
  let Ginv : Matrix (Fin n) (Fin n) K := (((g⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
  have hDG : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Ginv = 1 := by
    change ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((g⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hDG_diag : ∀ i, d i * Ginv i i = 1 := by
    intro i
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i i) hDG
    rw [hgd, Matrix.diagonal_mul, Matrix.one_apply_eq] at h
    exact h
  have hzmat : (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Matrix.diagonal d * (Equiv.swap a b).permMatrix K * Ginv *
        (Equiv.swap a b).permMatrix K := by
    have h := congrArg (fun u : GL (Fin n) K => (u : Matrix (Fin n) (Fin n) K)) hzval
    rw [Units.val_mul, Units.val_mul, Units.val_mul] at h
    rw [hgd, hPval] at h
    exact h
  have hzkk : (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k k = 1 := by
    rw [hzmat, ggNSPosPB1_diag_perm_apply d Ginv (Equiv.swap a b) hτ k]
    have hswap : (Equiv.swap a b) k = k := by
      rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
    rw [hswap]
    exact hDG_diag k
  have hzaa : (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a =
      d a * Ginv b b := by
    rw [hzmat, ggNSPosPB1_diag_perm_apply d Ginv (Equiv.swap a b) hτ a]
    rw [Equiv.swap_apply_left]
  let Q : Su K 2 f n := ggPermSU (K := K) (f := f) (Equiv.swap a k)
  have hQval : (((Q : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (Equiv.swap a k).permMatrix K := rfl
  have hσ : (Equiv.swap a k) * (Equiv.swap a k) = 1 := Equiv.swap_mul_self a k
  have hzQ : z * Q = Q * z := (Subgroup.mem_center_iff.mp hzcenter Q).symm
  have hzQmat : (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (((Q : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (((Q : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have h := congrArg (fun u : Su K 2 f n =>
      (((u : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hzQ
    simpa only [Subgroup.coe_mul, Units.val_mul] using h
  have hL : ((((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (Equiv.swap a k).permMatrix K) k a =
      (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k k := by
    rw [ggNSPosPB1_mul_perm_apply]
    congr 1
    rw [show (Equiv.swap a k)⁻¹ = Equiv.swap a k from inv_eq_of_mul_eq_one_right hσ,
      Equiv.swap_apply_left]
  have hR : ((Equiv.swap a k).permMatrix K *
      (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) k a =
      (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a := by
    rw [ggNSPosPB1_perm_mul_apply]
    congr 1
    rw [Equiv.swap_apply_right]
  have hkk_aa : (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) k k =
      (((z : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a a := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) K => M k a) hzQmat
    rw [hQval, hL, hR] at h
    exact h
  have haa_eq : d a * Ginv b b = 1 := by
    rw [← hzaa, ← hkk_aa]
    exact hzkk
  have hdb : d b * Ginv b b = 1 := hDG_diag b
  have hGne : Ginv b b ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdb
    exact zero_ne_one hdb
  exact mul_right_cancel₀ hGne (by rw [haa_eq, hdb])

theorem ggNSPosPB_block_le_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a b : Fin n) (hab : a ≠ b) (r : MulAut ↥Bs)
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹) :
    (ggSuPairBlock K 2 f n a b).map ψ ≤
      ψ.range ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) := by
  rintro _ ⟨A, hA, rfl⟩
  refine ⟨⟨A, rfl⟩, ?_⟩
  intro s hs
  obtain ⟨t, ht, hts⟩ := Subgroup.mem_map.mp hs
  rw [← hts]
  have ht' : r t = t := ht
  obtain ⟨g, ⟨d, hdg⟩, hunit, hact⟩ := hd (t : G) t.2
  obtain ⟨y, hy, hyact⟩ := hact A
  have hcomm : g * A = A * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hdg]
    exact ggNSPosPB_diag_comm_block (ggNSPosPB_diag_eq h hd a b hab r hr ht' ⟨d, hdg⟩ ⟨hunit, hact⟩ d hdg) hA
  have hyA : y = A := by
    apply Subtype.ext
    rw [hy, hcomm]
    group
  rw [hyA] at hyact
  exact mul_inv_eq_iff_eq_mul.mp hyact

open CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

lemma ggNSPosPB2_su_two_closure_invol {K : Type} [Field K] [Finite K] [CharP K 2]
    {f m : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hm : m = 2) :
    (⊤ : Subgroup (Su K 2 f m)) ≤ Subgroup.closure {g : Su K 2 f m | g ^ 2 = 1} := by
  subst hm
  have hσI : IsUnitaryInvolution (unitaryInvolution K 2 f) :=
    isUnitaryInvolution_unitaryInvolution hK
  rw [← T_two_eq_top (σ := unitaryInvolution K 2 f) hσI]
  apply Subgroup.closure_mono
  intro g hg
  obtain ⟨a, c, ha, hc, hact⟩ := hg
  have hg_eq : g = tv hσI.invol ha hc := by
    apply ext_smul
    intro v
    rw [hact v, tv_smul]
  rw [hg_eq]
  change (tv hσI.invol ha hc) ^ 2 = 1
  have hcc : c + c = 0 := CharTwo.add_self_eq_zero c
  have hcd : (c + c) + unitaryInvolution K 2 f (c + c) = 0 := by rw [hcc, map_zero, add_zero]
  rw [pow_two, tv_mul_tv hσI.invol ha hc hc hcd]
  have h0 : (0 : K) + unitaryInvolution K 2 f 0 = 0 := by rw [map_zero, add_zero]
  have hsame : tv hσI.invol ha hcd = tv hσI.invol ha h0 := by
    apply ext_smul
    intro v
    rw [tv_smul, tv_smul, hcc, zero_mul, zero_smul]
  rw [hsame, tv_zero hσI.invol ha h0]

lemma ggNSPosPB2_range_blockSUOn_le_closure_invol {K : Type} [Field K] [Finite K]
    [CharP K 2] {f n : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (J : Finset (Fin n))
    (hJ : J.card = 2) :
    (blockSUOn K 2 f J).range ≤
      Subgroup.closure {A : Su K 2 f n | A ∈ (blockSUOn K 2 f J).range ∧ A ^ 2 = 1} := by
  set F := blockSUOn K 2 f J with hF
  have htop := ggNSPosPB2_su_two_closure_invol (K := K) (f := f) (m := J.card) hK hJ
  calc F.range = Subgroup.map F ⊤ := MonoidHom.range_eq_map F
    _ ≤ Subgroup.map F (Subgroup.closure {g : Su K 2 f J.card | g ^ 2 = 1}) :=
        Subgroup.map_mono htop
    _ = Subgroup.closure (F '' {g : Su K 2 f J.card | g ^ 2 = 1}) := MonoidHom.map_closure F _
    _ ≤ Subgroup.closure {A : Su K 2 f n | A ∈ F.range ∧ A ^ 2 = 1} := by
          apply Subgroup.closure_mono
          rintro A ⟨g, hg, rfl⟩
          exact ⟨⟨g, rfl⟩, by rw [← map_pow, hg, map_one]⟩

theorem ggSuPairBlock_eq_coordBlockSU {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    (a b : Fin n) :
    ggSuPairBlock K 2 f n a b = coordBlockSU K 2 f ({a, b} : Finset (Fin n)) := by
  ext A
  rw [mem_coordBlockSU_iff]
  constructor
  · intro hA i j hij
    have h' : (i ≠ a ∧ i ≠ b) ∨ (j ≠ a ∧ j ≠ b) := by
      rcases hij with hi | hj
      · exact Or.inl (by simpa [Finset.mem_insert, Finset.mem_singleton] using hi)
      · exact Or.inr (by simpa [Finset.mem_insert, Finset.mem_singleton] using hj)
    rw [hA i j h', Matrix.one_apply]
  · intro hA i j hij
    have h' : i ∉ ({a, b} : Finset (Fin n)) ∨ j ∉ ({a, b} : Finset (Fin n)) := by
      rcases hij with ⟨hi1, hi2⟩ | ⟨hj1, hj2⟩
      · exact Or.inl (by simp [Finset.mem_insert, Finset.mem_singleton, hi1, hi2])
      · exact Or.inr (by simp [Finset.mem_insert, Finset.mem_singleton, hj1, hj2])
    rw [Matrix.one_apply]
    exact hA i j h'

theorem ggNSPosPB_block_le_oTwoPrime {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ)
    (hd : GGActsDiagonally (p := 2) (f := f) ψ Bs) (a b : Fin n) (hab : a ≠ b) (r : MulAut ↥Bs)
    (hr : ∀ s : ↥Bs, ((r s : ↥Bs) : G) =
      ψ (ggPermSU (Equiv.swap a b)) * (s : G) * (ψ (ggPermSU (Equiv.swap a b)))⁻¹) :
    (ggSuPairBlock K 2 f n a b).map ψ ≤
      ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G)) := by
  have hgen := ggNSPosPB2_range_blockSUOn_le_closure_invol (K := K) (f := f) h.card
    ({a, b} : Finset (Fin n)) (by
      rw [Finset.card_insert_of_notMem (by simpa [Finset.mem_singleton] using hab),
        Finset.card_singleton])
  have hblock_eq := ggSuPairBlock_eq_coordBlockSU (K := K) (f := f) a b
  have hgen' : ggSuPairBlock K 2 f n a b ≤
      Subgroup.closure {A : Su K 2 f n | A ∈ ggSuPairBlock K 2 f n a b ∧ A ^ 2 = 1} := by
    rw [hblock_eq]
    simpa only [coordBlockSU] using hgen
  have hYle := ggNSPosPB_block_le_centralizer h hd a b hab r hr
  calc (ggSuPairBlock K 2 f n a b).map ψ
      ≤ (Subgroup.closure {B : Su K 2 f n | B ∈ ggSuPairBlock K 2 f n a b ∧ B ^ 2 = 1}).map ψ :=
        Subgroup.map_mono hgen'
    _ = Subgroup.closure (ψ '' {B : Su K 2 f n | B ∈ ggSuPairBlock K 2 f n a b ∧ B ^ 2 = 1}) :=
        MonoidHom.map_closure ψ _
    _ ≤ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G)) := by
        refine (Subgroup.closure_le (ggOTwoPrime (ψ.range ⊓
          Subgroup.centralizer (ggHyperplane Bs r : Set G)))).mpr ?_
        rintro z ⟨B, ⟨hBblock, hB2⟩, rfl⟩
        refine Subgroup.subset_closure ⟨hYle ⟨B, hBblock, rfl⟩, 1, ?_⟩
        rw [show (2 : ℕ) ^ 1 = 2 by norm_num, pow_two, ← map_mul, ← pow_two, hB2, map_one]

end CFSG.StandardType

end
