module

public import CFSG.RankThree.PartTwo.KFacts.KS222U4OddCent
public import CFSG.RankThree.PartOne.KF.U4Su3
public import CFSG.RankThree.PartOne.KF.U4Group
public import CFSG.Permutation.SymmetricCoxeter
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223KFactsProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (torusVec torusSU diagU diagU_val symAct coe_symAct symAut
  symAut_apply movedSub permGL coe_permGL coe_permGL_inv permGL_conj_diagU permGL_mem_unitarySU
  coordPerm coe_coordPerm blk mem_blk_iff map_blk_coordPerm_of_eq card_torusVec_eq
  card_movedSub_swap movedSub_swap torusElt torusEltV coe_torusEltV torusElt_apply_left
  torusElt_apply_right torusElt_apply_other exists_perm_pair coordEmbed_apply_of_not_mem_left)
open CFSG.RankThree.PartOne.KCUnitaryCoord (coordEmbed)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.RankThree.PartTwo.Sec21.U4OddLines (blk2 blkSU2 blkGL2 coe_blkGL2 dvecD0 d0 coe_d0
  phiD0 ker_phiD0)
open scoped commutatorElement Matrix

variable {K : Type} [Field K]

@[expose] def hplane (K : Type) [Field K] (a b : Fin 4) : Subgroup (torusVec 3 4 K) :=
  fixedSubgroupOf (symAut 3 K (Equiv.swap a b))

theorem mem_hplane_iff {a b : Fin 4} {d : torusVec 3 4 K} :
    d ∈ hplane K a b ↔ (d : Fin 4 → Kˣ) a = (d : Fin 4 → Kˣ) b := by
  rw [hplane, mem_fixedSubgroupOf, symAut_apply]
  constructor
  · intro h
    have h1 := congrFun (congrArg Subtype.val h) a
    rw [coe_symAct, Equiv.symm_swap, Equiv.swap_apply_left] at h1
    exact h1.symm
  · intro h
    apply Subtype.ext
    funext i
    rw [coe_symAct, Equiv.symm_swap]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, h]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]

theorem commOf_symAut (σ : Equiv.Perm (Fin 4)) : commOf (symAut 3 K σ) = movedSub 3 K σ := by
  rw [commOf, movedSub]
  congr 1
  ext x
  simp only [Set.mem_range, symAut_apply]
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨d, mul_comm _ _⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d, mul_comm _ _⟩

theorem card_hplane [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 3) {a b : Fin 4} (hab : a ≠ b) :
    Nat.card (hplane K a b) = 9 := by
  have h27 : Nat.card (torusVec 3 4 K) = 27 := card_torusVec_eq (by norm_num) hζ 3
  have h3 := card_movedSub_swap (K := K) Nat.prime_three (by norm_num) hζ hab
  have h := card_eq_card_fixed_mul_card_commOf (fun x y : torusVec 3 4 K => mul_comm x y)
    (symAut 3 K (Equiv.swap a b))
  rw [commOf_symAut, h3, h27] at h
  rw [hplane]
  omega

theorem entry_eq_zero_of_commute_diagU {d : Fin 4 → Kˣ} {g : GL (Fin 4) K}
    (hg : g * diagU d = diagU d * g) {i j : Fin 4} (hij : d i ≠ d j) :
    (g : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
  have h := congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K) i j) hg
  simp only [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have h2 : (g : Matrix (Fin 4) (Fin 4) K) i j * ((d j : K) - (d i : K)) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (Units.ext (sub_eq_zero.mp h3).symm) hij

theorem isDiag_of_separating {H : Subgroup (torusVec 3 4 K)}
    (hsep : ∀ i j : Fin 4, i ≠ j → ∃ d ∈ H, (d : Fin 4 → Kˣ) i ≠ (d : Fin 4 → Kˣ) j)
    {g : GL (Fin 4) K} (hg : ∀ d ∈ H, g * diagU (d : Fin 4 → Kˣ) = diagU (d : Fin 4 → Kˣ) * g) :
    (g : Matrix (Fin 4) (Fin 4) K).IsDiag := by
  intro i j hij
  obtain ⟨d, hd, hne⟩ := hsep i j hij
  exact entry_eq_zero_of_commute_diagU (hg d hd) hne

theorem commute_of_separating {H : Subgroup (torusVec 3 4 K)}
    (hsep : ∀ i j : Fin 4, i ≠ j → ∃ d ∈ H, (d : Fin 4 → Kˣ) i ≠ (d : Fin 4 → Kˣ) j)
    {g g' : GL (Fin 4) K}
    (hg : ∀ d ∈ H, g * diagU (d : Fin 4 → Kˣ) = diagU (d : Fin 4 → Kˣ) * g)
    (hg' : ∀ d ∈ H, g' * diagU (d : Fin 4 → Kˣ) = diagU (d : Fin 4 → Kˣ) * g') :
    g * g' = g' * g := by
  have h1 := (Matrix.isDiag_iff_diagonal_diag _).mp (isDiag_of_separating hsep hg)
  have h2 := (Matrix.isDiag_iff_diagonal_diag _).mp (isDiag_of_separating hsep hg')
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  calc (g : Matrix (Fin 4) (Fin 4) K) * (g' : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (g : Matrix (Fin 4) (Fin 4) K).diag *
        Matrix.diagonal (g' : Matrix (Fin 4) (Fin 4) K).diag := by rw [h1, h2]
    _ = Matrix.diagonal (g' : Matrix (Fin 4) (Fin 4) K).diag *
        Matrix.diagonal (g : Matrix (Fin 4) (Fin 4) K).diag := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      exact mul_comm _ _
    _ = _ := by rw [h1, h2]

theorem separating_or_le_hplane (H : Subgroup (torusVec 3 4 K)) :
    (∀ i j : Fin 4, i ≠ j → ∃ d ∈ H, (d : Fin 4 → Kˣ) i ≠ (d : Fin 4 → Kˣ) j) ∨
      ∃ a b : Fin 4, a ≠ b ∧ H ≤ hplane K a b := by
  by_cases h : ∀ i j : Fin 4, i ≠ j → ∃ d ∈ H, (d : Fin 4 → Kˣ) i ≠ (d : Fin 4 → Kˣ) j
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨a, b, hab, h⟩ := h
    exact ⟨a, b, hab, fun d hd => mem_hplane_iff.mpr (h d hd)⟩

theorem eq_hplane_of_le [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 3) {a b : Fin 4}
    (hab : a ≠ b) {H : Subgroup (torusVec 3 4 K)} (hH : H ≤ hplane K a b)
    (h9 : 9 ≤ Nat.card H) : H = hplane K a b :=
  Subgroup.eq_of_le_of_card_ge hH (by rw [card_hplane hζ hab]; exact h9)

theorem blk2_eq_coordEmbed (X : Matrix (Fin 2) (Fin 2) K) :
    blk2 X = coordEmbed K (0 : Fin 4) 1 X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk2, coordEmbed, CFSG.RankThree.PartOne.KCUnitaryCoord.coordIncl,
      CFSG.RankThree.PartOne.KCUnitaryCoord.coordProj, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

variable {f : ℕ} (hU : UnitaryFieldData 2 f K)
include hU

theorem blkSU2_eq_blk : blkSU2 f K = blk hU (show (0 : Fin 4) ≠ 1 by decide) := by
  have hgram : unitarySU 2 f K 2 = gramSU hU (idGram K 2) := by
    rw [unitarySU_eq_gramSU hU 2]
    rfl
  ext g
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine (mem_blk_iff _).mpr ⟨X, hgram ▸ hX, ?_⟩
    rw [coe_blkGL2, blk2_eq_coordEmbed]
  · intro hg
    obtain ⟨X, hX, hgX⟩ := (mem_blk_iff _).mp hg
    refine ⟨X, hgram ▸ hX, Units.ext ?_⟩
    rw [coe_blkGL2, blk2_eq_coordEmbed, hgX]

omit hU in
theorem permGL_conj_eq_coordPerm {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : GL (Fin n) K) :
    permGL σ * g * (permGL σ)⁻¹ = coordPerm K σ g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_permGL_inv, coe_coordPerm,
    Equiv.Perm.permMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv]
  rfl

omit hU in
theorem symAct_d0_mem_hplane {ω : Kˣ} (hω3 : ω ^ 3 = 1) {a b : Fin 4} {π : Equiv.Perm (Fin 4)}
    (hπ0 : π 0 = a) (hπ1 : π 1 = b) : symAct 3 K π (d0 hω3) ∈ hplane K a b := by
  have ha : π.symm a = 0 := by rw [Equiv.symm_apply_eq, hπ0]
  have hb : π.symm b = 1 := by rw [Equiv.symm_apply_eq, hπ1]
  rw [mem_hplane_iff, coe_symAct, coe_symAct, coe_d0, ha, hb]
  rfl

omit hU in
theorem permGL_conj_diagU_d0 {ω : Kˣ} (hω3 : ω ^ 3 = 1) (π : Equiv.Perm (Fin 4)) :
    permGL π * diagU (dvecD0 ω) * (permGL π)⁻¹ =
      diagU ((symAct 3 K π (d0 hω3) : torusVec 3 4 K) : Fin 4 → Kˣ) := by
  rw [permGL_conj_diagU]
  rfl

omit hU in
theorem ne_inv_of_isPrimitiveRoot_three {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) : ω ≠ ω⁻¹ := by
  intro h
  have hsq : ω ^ 2 = 1 := by
    calc ω ^ 2 = ω * ω := sq ω
      _ = ω * ω⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel ω
  exact hω.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) hsq

theorem le_blk_of_perfect {ω : Kˣ} (hω : IsPrimitiveRoot ω 3) {a b : Fin 4} (hab : a ≠ b)
    {S : Subgroup (GL (Fin 4) K)} (hSU : S ≤ unitarySU 2 f K 4) (hS : Group.IsPerfect S)
    (hc : ∀ g ∈ S, ∀ d ∈ hplane K a b,
      g * diagU (d : Fin 4 → Kˣ) = diagU (d : Fin 4 → Kˣ) * g) :
    S ≤ blk hU hab := by
  obtain ⟨π, hπ0, hπ1⟩ := exists_perm_pair (show (0 : Fin 4) ≠ 1 by decide) hab
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have h1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have h2 : ω ≠ ω⁻¹ := ne_inv_of_isPrimitiveRoot_three hω
  set P : GL (Fin 4) K := permGL π with hP
  have hPU : P ∈ unitarySU 2 f K 4 := permGL_mem_unitarySU hU π
  set S₀ := S.map (MulAut.conj P⁻¹).toMonoidHom with hS₀
  set C₀ := unitarySU 2 f K 4 ⊓ Subgroup.centralizer {diagU (dvecD0 ω)} with hC₀
  have hconj : ∀ g : GL (Fin 4) K, (MulAut.conj P⁻¹).toMonoidHom g = P⁻¹ * g * P := by
    intro g
    simp
  have hS₀C : S₀ ≤ C₀ := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hconj]
    refine Subgroup.mem_inf.mpr ⟨(unitarySU 2 f K 4).mul_mem ((unitarySU 2 f K 4).mul_mem
      ((unitarySU 2 f K 4).inv_mem hPU) (hSU hg)) hPU, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he := hc g hg _ (symAct_d0_mem_hplane hω3 hπ0 hπ1)
    rw [← permGL_conj_diagU_d0 hω3 π, ← hP] at he
    calc P⁻¹ * g * P * diagU (dvecD0 ω) =
        P⁻¹ * (g * (P * diagU (dvecD0 ω) * P⁻¹)) * P := by group
      _ = P⁻¹ * ((P * diagU (dvecD0 ω) * P⁻¹) * g) * P := by rw [he]
      _ = diagU (dvecD0 ω) * (P⁻¹ * g * P) := by group
  have hS₀p : Group.IsPerfect S₀ :=
    Group.IsPerfect.ofSurjective
      (f := (S.equivMapOfInjective _ (MulAut.conj P⁻¹).injective).toMonoidHom)
      (S.equivMapOfInjective _ (MulAut.conj P⁻¹).injective).surjective
  have hS₀B : S₀ ≤ blkSU2 f K := by
    rw [← Subgroup.isPerfect_iff.mp hS₀p, Subgroup.commutator_le]
    intro x hx y hy
    have hk : ⁅(⟨x, hS₀C hx⟩ : C₀), (⟨y, hS₀C hy⟩ : C₀)⁆ ∈ (phiD0 hU h1 h2).ker := by
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    rw [ker_phiD0, Subgroup.mem_subgroupOf] at hk
    exact hk
  intro g hg
  have hg₀ : P⁻¹ * g * P ∈ blk hU (show (0 : Fin 4) ≠ 1 by decide) := by
    rw [← blkSU2_eq_blk hU, ← hconj]
    exact hS₀B ⟨g, hg, rfl⟩
  rw [← map_blk_coordPerm_of_eq hU π (show (0 : Fin 4) ≠ 1 by decide) hπ0 hπ1 hab]
  refine ⟨P⁻¹ * g * P, hg₀, ?_⟩
  rw [MulEquiv.coe_toMonoidHom, ← permGL_conj_eq_coordPerm, ← hP]
  group

theorem mem_movedSub_of_diagU_mem_blk {a b : Fin 4} (hab : a ≠ b) {d : torusVec 3 4 K}
    (hd : diagU (d : Fin 4 → Kˣ) ∈ blk hU hab) : d ∈ movedSub 3 K (Equiv.swap a b) := by
  rw [movedSub_swap Nat.prime_three (by norm_num) hab]
  have hk : ∀ k, k ≠ a → k ≠ b → (d : Fin 4 → Kˣ) k = 1 := by
    intro k hka hkb
    obtain ⟨X, -, hX⟩ := (mem_blk_iff hab).mp hd
    have h := congrFun (congrFun hX k) k
    rw [diagU_val, Matrix.diagonal_apply_eq, coordEmbed_apply_of_not_mem_left hka hkb,
      Matrix.one_apply_eq] at h
    exact Units.ext h
  have hprod : ∏ i, (d : Fin 4 → Kˣ) i = 1 := d.2.2
  have hab' : (d : Fin 4 → Kˣ) a * (d : Fin 4 → Kˣ) b = 1 := by
    rw [← hprod, Finset.prod_eq_mul a b hab (fun c _ hc => hk c hc.1 hc.2) (by simp) (by simp)]
  have hu : (d : Fin 4 → Kˣ) a ∈ rootsOfUnity 3 K := (mem_rootsOfUnity 3 _).mpr (d.2.1 a)
  refine ⟨⟨(d : Fin 4 → Kˣ) a, hu⟩, Subtype.ext ?_⟩
  rw [coe_torusEltV]
  funext k
  by_cases hka : k = a
  · subst hka
    rw [torusElt_apply_left hab]
  · by_cases hkb : k = b
    · subst hkb
      rw [torusElt_apply_right hab]
      exact (eq_inv_of_mul_eq_one_right hab').symm
    · rw [torusElt_apply_other hka hkb, hk k hka hkb]

theorem card_blk {a b : Fin 4} (hab : a ≠ b) :
    Nat.card (blk hU hab) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  obtain ⟨e₁⟩ := CFSG.RankThree.PartOne.KFU.nonempty_blk_mulEquiv hU hab
  obtain ⟨e₂⟩ := CFSG.RankThree.PartOne.KFU.nonempty_gramSU_two_mulEquiv_SL2 hU
  have := hU.finite
  rw [Nat.card_congr (e₁.trans e₂).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hU.card_fixedField]

theorem blk_sup_blk_mulEquiv_su3_of_share (hf : 2 ≤ f) {a b c d : Fin 4} (hab : a ≠ b)
    (hcd : c ≠ d)
    (hs : (a = c ∧ b ≠ d) ∨ (a = d ∧ b ≠ c) ∨ (b = c ∧ a ≠ d) ∨ (b = d ∧ a ≠ c)) :
    Nonempty (↥(blk hU hab ⊔ blk hU hcd) ≃* ↥(unitarySU 2 f K 3)) := by
  rcases hs with ⟨rfl, hbd⟩ | ⟨rfl, hbc⟩ | ⟨rfl, had⟩ | ⟨rfl, hac⟩
  · have h := CFSG.RankThree.PartOne.KFU.blk_sup_blk_mulEquiv_su3 hU hf hab.symm hcd hbd
    rwa [CFSG.RankThree.PartOne.KFU.blk_symm hab] at h
  · have h := CFSG.RankThree.PartOne.KFU.blk_sup_blk_mulEquiv_su3 hU hf hcd hab hbc.symm
    rwa [sup_comm] at h
  · exact CFSG.RankThree.PartOne.KFU.blk_sup_blk_mulEquiv_su3 hU hf hab hcd had
  · have h := CFSG.RankThree.PartOne.KFU.blk_sup_blk_mulEquiv_su3 hU hf hab hcd.symm hac
    rwa [CFSG.RankThree.PartOne.KFU.blk_symm hcd] at h

omit hU in
theorem unitarySU_three_eq_SU3 (m : ℕ) : unitarySU 2 m (GaloisField 2 (2 * m)) 3 = SU3 m := by
  have hset : {A : GL (Fin 3) (GaloisField 2 (2 * m)) |
      (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))).det = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))).map (· ^ (2 ^ m)))ᵀ *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))) = 1} =
      {A : GL (Fin 3) (GaloisField 2 (2 * m)) | Matrix.GeneralLinearGroup.det A = 1 ∧
      ((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))).map (· ^ (2 ^ m)))ᵀ *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * m))) = 1} := by
    ext A
    simp only [Set.mem_ofPred_eq, Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply,
      Units.val_one]
  rw [unitarySU, CFSG.Assembly.LowTwoRank.StatedSU, SU3, hset]

end CFSG.RankThree.PartTwo.Sec21.Item223KFactsProof

namespace CFSG.RankThree.PartTwo.Sec21.Item223KFactsProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem swap_dichotomy : ∀ a b c d : Fin 4, a ≠ b → c ≠ d →
    Equiv.swap a b ≠ Equiv.swap c d →
    (Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b ∧
        a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) ∨
      (Equiv.swap a b * Equiv.swap c d ≠ Equiv.swap c d * Equiv.swap a b ∧
        (Equiv.swap a b * Equiv.swap c d) ^ 3 = 1 ∧
        ((a = c ∧ b ≠ d) ∨ (a = d ∧ b ≠ c) ∨ (b = c ∧ a ≠ d) ∨ (b = d ∧ a ≠ c))) := by
  decide

theorem fixedSubgroupOf_congr {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (φ : MulAut P) :
    fixedSubgroupOf (MulAut.congr e φ) = (fixedSubgroupOf φ).map e.toMonoidHom := by
  ext y
  rw [mem_fixedSubgroupOf, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  constructor
  · intro h
    refine ⟨e.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf]
    apply e.injective
    rw [h, MulEquiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroupOf] at hx
    simp [hx]

theorem commOf_congr {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q) (φ : MulAut P) :
    commOf (MulAut.congr e φ) = (commOf φ).map e.toMonoidHom := by
  rw [commOf, commOf, MonoidHom.map_closure]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image, MulAut.congr_apply, MulEquiv.trans_apply]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, ⟨e.symm z, rfl⟩, by simp⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, by simp⟩

open CFSG.Permutation.SymmetricCoxeter in
theorem closure_pair_mulEquiv_perm_three {H : Type*} [Group H] {u v : H} (hu : u * u = 1)
    (hv : v * v = 1) (hcub : (u * v) ^ 3 = 1) (hne : u * v ≠ v * u) :
    Nonempty (↥(Subgroup.closure {u, v}) ≃* Equiv.Perm (Fin 3)) := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv
  let x : ℕ → H := fun i => if i = 0 then u else if i = 1 then v else 1
  have hbraid : u * v * u = v * u * v := by
    have h1 : (u * v * u) * (v * u * v) = 1 := by
      calc (u * v * u) * (v * u * v) = (u * v) ^ 3 := by rw [pow_three']; group
        _ = 1 := hcub
    have h2 := eq_inv_of_mul_eq_one_left h1
    rw [h2, mul_inv_rev, mul_inv_rev, hui, hvi, mul_assoc]
  have hx : IsCoxeterA 2 x := by
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      interval_cases i
      · simpa [x] using hu
      · simpa [x] using hv
    · intro i hi
      have : i = 0 := by omega
      subst this
      simpa [x] using hbraid
    · intro i j hij hj
      omega
  obtain ⟨ψ, hψ⟩ := exists_hom_perm 2 x hx
  have hψ0 : ψ (Equiv.swap 0 1) = u := by
    have := hψ 0 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    simpa [x] using this
  have hψ1 : ψ (Equiv.swap 1 2) = v := by
    have := hψ 1 (by norm_num)
    rw [adjSwap_of_lt (by norm_num)] at this
    simpa [x] using this
  have hu1 : u ≠ 1 := fun h => hne (by rw [h, one_mul, mul_one])
  have hv1 : v ≠ 1 := fun h => hne (by rw [h, one_mul, mul_one])
  have huv1 : u * v ≠ 1 := fun h => hne (by
    have : v = u := by
      calc v = u⁻¹ * (u * v) := by group
        _ = u := by rw [h, mul_one, hui]
    rw [this])
  have hvu1 : v * u ≠ 1 := fun h => hne (by
    have : u = v := by
      calc u = v⁻¹ * (v * u) := by group
        _ = v := by rw [h, mul_one, hvi]
    rw [this])
  have huvu1 : u * v * u ≠ 1 := fun h => hv1 (by
    calc v = u⁻¹ * (u * v * u) * u⁻¹ := by group
      _ = 1 := by rw [h, mul_one, hui, hu])
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hall : ∀ σ : Equiv.Perm (Fin 3), σ = 1 ∨ σ = Equiv.swap 0 1 ∨ σ = Equiv.swap 1 2 ∨
        σ = Equiv.swap 0 1 * Equiv.swap 1 2 ∨ σ = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
        σ = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by decide
    rcases hall σ with rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · rw [hψ0] at hσ
      exact absurd hσ hu1
    · rw [hψ1] at hσ
      exact absurd hσ hv1
    · rw [map_mul, hψ0, hψ1] at hσ
      exact absurd hσ huv1
    · rw [map_mul, hψ0, hψ1] at hσ
      exact absurd hσ hvu1
    · rw [map_mul, map_mul, hψ0, hψ1] at hσ
      exact absurd hσ huvu1
  have hrange : ψ.range = Subgroup.closure {u, v} := by
    rw [MonoidHom.range_eq_map, ← closure_adjSwap 2, MonoidHom.map_closure]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_Iio, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      interval_cases i
      · left
        rw [← hψ0, adjSwap_of_lt (by norm_num)]
        rfl
      · right
        rw [← hψ1, adjSwap_of_lt (by norm_num)]
        rfl
    · rintro (rfl | rfl)
      · refine ⟨_, ⟨0, by norm_num, rfl⟩, ?_⟩
        rw [adjSwap_of_lt (by norm_num)]
        exact hψ0
      · refine ⟨_, ⟨1, by norm_num, rfl⟩, ?_⟩
        rw [adjSwap_of_lt (by norm_num)]
        exact hψ1
  exact ⟨((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm⟩

section Model

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (torusSU)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)

theorem three_dvd_two_pow_add_one {k : ℕ} (hk : Odd k) : 3 ∣ 2 ^ k + 1 := by
  obtain ⟨j, rfl⟩ := hk
  have h : (2 : ℕ) ^ (2 * j + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h]

theorem unitaryFieldData_galoisField {k : ℕ} (hk : 1 ≤ k) :
    UnitaryFieldData 2 k (GaloisField 2 (2 * k)) :=
  ⟨Nat.prime_two, hk, GaloisField.card 2 (2 * k) (by omega)⟩

theorem center_eq_bot_of_mulEquiv_projSU {Y : Type} [Group Y] {k : ℕ} (hk : 1 ≤ k)
    (e : Y ≃* projSU 4 2 k) {a b : Y} (hab : a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  have := isSimpleGroup_projSU (m := 4) (n := k) le_rfl hk
  have : IsSimpleGroup Y := e.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab

theorem exists_diag_model_le {Y : Type} [Group Y] [Finite Y] {k : ℕ} (hk : 1 ≤ k) (hko : Odd k)
    (e : Y ≃* projSU 4 2 k) (hZ : Subgroup.center Y = ⊥) (E : Subgroup Y)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) :
    ∃ ψ : unitarySU 2 k (GaloisField 2 (2 * k)) 4 ≃* Y, ∀ g, ψ g ∈ E →
      (g : GL (Fin 4) (GaloisField 2 (2 * k))) ∈ torusSU 3 4 (GaloisField 2 (2 * k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * k)) = (2 ^ k) ^ 2 :=
    U4Lines.card_galoisField_two_mul k (by omega)
  let e₀ : projSU 4 2 k ≃* StatedProj (StatedSU 4 (2 ^ k) (GaloisField 2 (2 * k))) :=
    (MulEquiv.subgroupCongr (Census.projImage_statedSU 4 2 k).symm).trans
      (Census.statedProjEquivProjImage _).symm
  let e' : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU 4 (2 ^ k) (GaloisField 2 (2 * k))) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans (e.trans e₀))
  exact CFSG.RankThree.PartOne.KFU.exists_diag_iso_le hk hK Nat.prime_three
    (three_dvd_two_pow_add_one hko) hZ e' E hexp hcomm

theorem exists_diag_model {Y : Type} [Group Y] [Finite Y] {k : ℕ} (hk : 1 ≤ k) (hko : Odd k)
    (e : Y ≃* projSU 4 2 k) (hZ : Subgroup.center Y = ⊥) (E : Subgroup Y)
    (hexp : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcard : Nat.card E = 3 ^ 3) :
    ∃ ψ : unitarySU 2 k (GaloisField 2 (2 * k)) 4 ≃* Y, ∀ g, ψ g ∈ E ↔
      (g : GL (Fin 4) (GaloisField 2 (2 * k))) ∈ torusSU 3 4 (GaloisField 2 (2 * k)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 (2 * k)) = (2 ^ k) ^ 2 :=
    U4Lines.card_galoisField_two_mul k (by omega)
  let e₀ : projSU 4 2 k ≃* StatedProj (StatedSU 4 (2 ^ k) (GaloisField 2 (2 * k))) :=
    (MulEquiv.subgroupCongr (Census.projImage_statedSU 4 2 k).symm).trans
      (Census.statedProjEquivProjImage _).symm
  let e' : Y ⧸ Subgroup.center Y ≃* StatedProj (StatedSU 4 (2 ^ k) (GaloisField 2 (2 * k))) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientBot.trans (e.trans e₀))
  exact CFSG.RankThree.PartOne.KFU.exists_diag_iso hk hK Nat.prime_three
    (three_dvd_two_pow_add_one hko) hZ e' E hexp hcomm hcard

end Model

end CFSG.RankThree.PartTwo.Sec21.Item223KFactsProof
