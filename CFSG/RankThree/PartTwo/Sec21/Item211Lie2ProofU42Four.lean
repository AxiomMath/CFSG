module

public import CFSG.RankThree.PartTwo.Sec21.Item211LieProofU42
import CFSG.RankThree.PartTwo.Sec21.Item223KFactsProofCore
import CFSG.RankThree.PartTwo.Sec21.Item21Early2ProofModels

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Lie2Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (torusSU torusVec diagU diagU_val mem_torusSU_iff)

theorem exists_ne_one_mem_centralizer_of_card_nine {G : Type*} [Group G] [Finite G]
    {D T : Subgroup G} (hD9 : Nat.card D = 9) (hT4 : Nat.card T = 4)
    (hDT : D ≤ Subgroup.normalizer (T : Set G)) :
    ∃ b ∈ D, b ≠ 1 ∧ b ∈ Subgroup.centralizer (T : Set G) := by
  set φ : D →* Equiv.Perm T :=
    (MulAut.toPerm T).comp ((T.normalizerMonoidHom).comp (Subgroup.inclusion hDT)) with hφ
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hD9] at hcard
  have hr24 : Nat.card φ.range ∣ 24 := by
    have h := Subgroup.card_subgroup_dvd_card φ.range
    rwa [Nat.card_perm, hT4] at h
  have hr9 : Nat.card φ.range ∣ 9 := ⟨_, hcard⟩
  have hr3 : Nat.card φ.range ∣ 3 := by
    have := Nat.dvd_gcd hr9 hr24
    rwa [show Nat.gcd 9 24 = 3 by norm_num] at this
  have hk : 1 < Nat.card φ.ker := by
    have hr : Nat.card φ.range ≤ 3 := Nat.le_of_dvd (by norm_num) hr3
    by_contra hk
    push Not at hk
    have : Nat.card φ.range * Nat.card φ.ker ≤ 3 * 1 := Nat.mul_le_mul hr hk
    omega
  have hne : φ.ker ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hk; omega
  obtain ⟨⟨⟨b, hbD⟩, hbk⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  refine ⟨b, hbD, fun h => hb1 (Subtype.ext (Subtype.ext h)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  have h1 : b * t * b⁻¹ = t :=
    congrArg (fun σ : Equiv.Perm T => (σ ⟨t, ht⟩ : G)) (MonoidHom.mem_ker.mp hbk)
  calc t * b = b * t * b⁻¹ * b := by rw [h1]
    _ = b * t := by group

theorem fin_four_compl_two : ∀ a b : Fin 4, a ≠ b →
    ∃ c d : Fin 4, c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b ∧ c ≠ d := by
  decide

theorem fin_four_compl_three : ∀ a b c : Fin 4, a ≠ b → a ≠ c → b ≠ c →
    ∃ d : Fin 4, d ≠ a ∧ d ≠ b ∧ d ≠ c := by
  decide

theorem fin_four_cover : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ x : Fin 4, x = a ∨ x = b ∨ x = c ∨ x = d := by
  decide

theorem sum_fin_four_of_ne {M : Type*} [AddCommMonoid M] {a b c d : Fin 4} (hab : a ≠ b)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (f : Fin 4 → M) :
    ∑ x, f x = f a + f b + f c + f d := by
  classical
  have huniv : (Finset.univ : Finset (Fin 4)) = {a, b, c, d} := by
    refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
    rw [Finset.card_univ, Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  rw [huniv, Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_pair hcd]
  simp only [add_assoc]

section Matrix

variable {K : Type*} [Field K]

theorem pow_three_of_ne [DecidableEq K] (hcube : ∀ x : K, x ≠ 0 → x ^ 3 = 1) (x : K) :
    x ^ 2 * x = if x = 0 then 0 else 1 := by
  split_ifs with hx
  · rw [hx, mul_zero]
  · rw [← pow_succ, hcube x hx]

theorem exists_zero_of_two_ne_zero (h2 : (2 : K) = 0) (hcube : ∀ x : K, x ≠ 0 → x ^ 3 = 1)
    {c : Fin 4 → K} (hn : ∑ x, c x ^ 2 * c x = 1) {i i' : Fin 4} (hii' : i ≠ i')
    (hi : c i ≠ 0) (hi' : c i' ≠ 0) : ∃ m, c m = 0 ∧ ∀ x, x ≠ m → c x ≠ 0 := by
  classical
  have hn3 := pow_three_of_ne hcube
  have h11 : (1 : K) + 1 = 0 := by rw [← one_add_one_eq_two] at h2; exact h2
  obtain ⟨r, s, hri, hri', hsi, hsi', hrs⟩ := fin_four_compl_two i i' hii'
  rw [sum_fin_four_of_ne hii' (Ne.symm hri) (Ne.symm hsi) (Ne.symm hri') (Ne.symm hsi') hrs, hn3,
    hn3, hn3, hn3, ite_eq_right hi, ite_eq_right hi', h11, zero_add] at hn
  have hcov := fin_four_cover i i' r s hii' (Ne.symm hri) (Ne.symm hsi) (Ne.symm hri')
    (Ne.symm hsi') hrs
  by_cases hr : c r = 0 <;> by_cases hs : c s = 0
  · rw [ite_eq_left hr, ite_eq_left hs, add_zero] at hn
    exact absurd hn zero_ne_one
  · refine ⟨r, hr, fun x hx => ?_⟩
    rcases hcov x with rfl | rfl | rfl | rfl
    · exact hi
    · exact hi'
    · exact absurd rfl hx
    · exact hs
  · refine ⟨s, hs, fun x hx => ?_⟩
    rcases hcov x with rfl | rfl | rfl | rfl
    · exact hi
    · exact hi'
    · exact hr
    · exact absurd rfl hx
  · rw [ite_eq_right hr, ite_eq_right hs, h11] at hn
    exact absurd hn zero_ne_one

theorem eq_of_ne_zero_of_ne_zero (h2 : (2 : K) = 0) (hcube : ∀ x : K, x ≠ 0 → x ^ 3 = 1)
    {t : Matrix (Fin 4) (Fin 4) K} (hH : ∀ i j, t i j = t j i ^ 2)
    (hU : ∀ j k, ∑ i, t i j ^ 2 * t i k = if j = k then 1 else 0)
    {β : Fin 4 → K} (hβ : ∀ i j, t i j ≠ 0 → β i = β j) (hns : ∃ i j, β i ≠ β j)
    {j i i' : Fin 4} (hi : t i j ≠ 0) (hi' : t i' j ≠ 0) : i = i' := by
  classical
  by_contra hii'
  have hn3 := pow_three_of_ne hcube
  have h11 : (1 : K) + 1 = 0 := by rw [← one_add_one_eq_two] at h2; exact h2
  obtain ⟨m, hmj, hother⟩ := exists_zero_of_two_ne_zero h2 hcube (c := fun x => t x j)
    (by simpa using hU j j) hii' hi hi'
  have hβj : ∀ x, x ≠ m → β x = β j := fun x hx => hβ x j (hother x hx)
  have hβm : β m ≠ β j := by
    intro hm
    obtain ⟨x, y, hxy⟩ := hns
    have hx : β x = β j := by
      rcases eq_or_ne x m with h | h
      · rw [h, hm]
      · exact hβj x h
    have hy : β y = β j := by
      rcases eq_or_ne y m with h | h
      · rw [h, hm]
      · exact hβj y h
    exact hxy (hx.trans hy.symm)
  have hjm : j ≠ m := fun h => hβm (by rw [h])
  obtain ⟨k, hkj, hkm⟩ : ∃ k, k ≠ j ∧ k ≠ m := by
    obtain ⟨c, d, hcj, hcm, hdj, hdm, -⟩ := fin_four_compl_two j m hjm
    exact ⟨c, hcj, hcm⟩
  obtain ⟨l, hlj, hlk, hlm⟩ := fin_four_compl_three j k m (Ne.symm hkj) hjm hkm
  have hsum4 := sum_fin_four_of_ne (M := K) (Ne.symm hkj) (Ne.symm hlj) hjm (Ne.symm hlk) hkm hlm
  have hjj : t j j ≠ 0 := hother j hjm
  have hkj0 : t k j ≠ 0 := hother k hkm
  have hlj0 : t l j ≠ 0 := hother l hlm
  have hjk : t j k ≠ 0 := by rw [hH j k]; exact pow_ne_zero 2 hkj0
  have hmk : t m k = 0 := by
    by_contra h
    exact hβm ((hβ m k h).trans (hβj k hkm))
  have hnk := hU k k
  rw [ite_eq_left rfl, hsum4, hn3, hn3, hn3, hn3, ite_eq_right hjk, ite_eq_left hmk,
    add_zero] at hnk
  have hjk' := hU j k
  rw [ite_eq_right (Ne.symm hkj), hsum4, hmk, mul_zero, add_zero] at hjk'
  have hdiag : ∀ x, t x x ≠ 0 → t x x = 1 := by
    intro x hx
    have h1 := hH x x
    have h2' : t x x * (t x x - 1) = 0 := by rw [mul_sub, mul_one, ← sq, ← h1, sub_self]
    rcases mul_eq_zero.mp h2' with h | h
    · exact absurd h hx
    · exact sub_eq_zero.mp h
  by_cases hkk : t k k = 0
  ·
    rw [ite_eq_left hkk] at hnk
    have hlk0 : t l k = 0 := by
      by_contra h
      rw [ite_eq_right h, add_zero, h11] at hnk
      exact zero_ne_one hnk
    rw [hkk, hlk0, mul_zero, mul_zero, add_zero, add_zero] at hjk'
    exact mul_ne_zero (pow_ne_zero 2 hjj) hjk hjk'
  ·
    have hlk0 : t l k ≠ 0 := by
      intro h
      rw [ite_eq_right hkk, ite_eq_left h, add_zero, h11] at hnk
      exact zero_ne_one hnk
    rw [hdiag j hjj, hdiag k hkk, ← hH j k, one_pow, one_mul, mul_one, ← two_mul, h2,
      zero_mul, zero_add] at hjk'
    exact mul_ne_zero (pow_ne_zero 2 hlj0) hlk0 hjk'

theorem eq_of_mul_comm_of_support (h2 : (2 : K) = 0) (hcube : ∀ x : K, x ≠ 0 → x ^ 3 = 1)
    {t₁ t₂ : Matrix (Fin 4) (Fin 4) K} (hH : ∀ i j, t₁ i j = t₁ j i ^ 2)
    (hU : ∀ j k, ∑ i, t₁ i j ^ 2 * t₁ i k = if j = k then 1 else 0)
    {β : Fin 4 → K} (hβ : ∀ i j, t₁ i j ≠ 0 → β i = β j) (hns : ∃ i j, β i ≠ β j)
    (hsq₁ : t₁ * t₁ = 1) (hsq₂ : t₂ * t₂ = 1) (hc : t₁ * t₂ = t₂ * t₁)
    (hsupp : ∀ i j, t₂ i j ≠ 0 → t₁ i j ≠ 0) : t₁ = t₂ := by
  have hoff : ∀ i k, i ≠ k → (t₁ * t₂) i k = 0 := by
    intro i k hik
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_contra hne
    have h1 : t₁ i x ≠ 0 := left_ne_zero_of_mul hne
    have h2' : t₁ x k ≠ 0 := hsupp x k (right_ne_zero_of_mul hne)
    have h3 : t₁ k x ≠ 0 := by rw [hH k x]; exact pow_ne_zero 2 h2'
    exact hik (eq_of_ne_zero_of_ne_zero h2 hcube hH hU hβ hns h1 h3)
  have hPP : (t₁ * t₂) * (t₁ * t₂) = 1 := by
    calc (t₁ * t₂) * (t₁ * t₂) = t₁ * (t₂ * t₁) * t₂ := by simp only [Matrix.mul_assoc]
      _ = t₁ * (t₁ * t₂) * t₂ := by rw [hc]
      _ = (t₁ * t₁) * (t₂ * t₂) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hsq₁, hsq₂, Matrix.one_mul]
  have hP1 : t₁ * t₂ = 1 := by
    ext i k
    by_cases hik : i = k
    · subst hik
      have h1 := congrFun (congrFun hPP i) i
      rw [Matrix.mul_apply, Finset.sum_eq_single i (fun x _ hx => by rw [hoff i x (Ne.symm hx),
        zero_mul]) (fun h => absurd (Finset.mem_univ i) h), Matrix.one_apply_eq] at h1
      have h3 : ((t₁ * t₂) i i - 1) * ((t₁ * t₂) i i - 1) = 0 := by
        have h4 : ((t₁ * t₂) i i - 1) * ((t₁ * t₂) i i - 1) =
            (t₁ * t₂) i i * (t₁ * t₂) i i - 2 * (t₁ * t₂) i i + 1 := by ring
        rw [h4, h1, h2, zero_mul, sub_zero, one_add_one_eq_two, h2]
      rw [Matrix.one_apply_eq]
      exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
    · rw [hoff i k hik, Matrix.one_apply_ne hik]
  calc t₁ = t₁ * (t₂ * t₂) := by rw [hsq₂, Matrix.mul_one]
    _ = (t₁ * t₂) * t₂ := by rw [Matrix.mul_assoc]
    _ = t₂ := by rw [hP1, Matrix.one_mul]

end Matrix

end Item211Lie2Proof

open Item211Lie2Proof
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KFU (diagU diagU_val mem_torusSU_iff)
open scoped Matrix

theorem ks211U42FourGroup_holds : KS211U42FourGroup := by
  intro D T hDe hD9 hTe hT4 hDT
  set K := GaloisField 2 (2 * 1) with hKdef
  have hU : UnitaryFieldData 2 1 K := Item223KFactsProof.unitaryFieldData_galoisField le_rfl
  have hfin : Finite K := hU.finite
  have : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = 4 := by
    rw [← Nat.card_eq_fintype_card, hU.card]
    norm_num
  have h2 : (2 : K) = 0 := by
    have : CharP K 2 := hU.charP
    exact_mod_cast CharP.cast_eq_zero K 2
  have hcube : ∀ x : K, x ≠ 0 → x ^ 3 = 1 := fun x hx => by
    have := FiniteField.pow_card_sub_one_eq_one x hx
    rwa [hcardK] at this
  have hbar : ∀ c : K, hU.bar c = c ^ 2 := fun c => by rw [hU.bar_apply, pow_one]
  have : Finite (Matrix.ProjGenLinGroup (Fin 4) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (projSU 4 2 1) := Subtype.finite
  have hZ : Subgroup.center (projSU 4 2 1) = ⊥ := Item21Early2Proof.center_projSU_four_eq_bot le_rfl
  obtain ⟨b, hbD, hb1, hbC⟩ := exists_ne_one_mem_centralizer_of_card_nine hD9 hT4 hDT
  obtain ⟨ψ, hψ⟩ := Item223KFactsProof.exists_diag_model_le (k := 1) le_rfl odd_one
    (MulEquiv.refl _) hZ D hDe.2 fun x hx y hy =>
      congrArg Subtype.val (hDe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hmemU : ∀ g : unitarySU 2 1 K 4,
      ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
        (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map hU.bar)ᵀ *
          ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
    fun g => (mem_unitarySU_iff hU).mp g.2
  have hdiag : ∀ g : unitarySU 2 1 K 4, ψ g ∈ D →
      ∃ δ : Fin 4 → Kˣ, (∀ i, δ i ^ 3 = 1) ∧ ∏ i, δ i = 1 ∧ diagU δ = (g : GL (Fin 4) K) :=
    fun g hg => mem_torusSU_iff.mp (hψ g hg)
  have hinv : ∀ y ∈ T, ((ψ.symm y : unitarySU 2 1 K 4) : GL (Fin 4) K) *
      ((ψ.symm y : unitarySU 2 1 K 4) : GL (Fin 4) K) = 1 := by
    intro y hy
    have h1 : ψ.symm y * ψ.symm y = 1 := by
      rw [← map_mul, ← sq, hTe.2 y hy, map_one]
    exact congrArg Subtype.val h1
  obtain ⟨β, hβ3, hβ1, hβb⟩ := hdiag (ψ.symm b) (by rw [MulEquiv.apply_symm_apply]; exact hbD)
  have hns : ∃ i j, (β i : K) ≠ (β j : K) := by
    by_contra hcon
    push Not at hcon
    apply hb1
    have hβc : β = fun _ => β 0 := funext fun i => Units.ext (hcon i 0)
    have h4 : β 0 ^ 4 = 1 := by
      rw [hβc] at hβ1
      simpa [Fin.prod_univ_four, pow_succ, mul_assoc] using hβ1
    have h01 : β 0 = 1 := by
      have := hβ3 0
      calc β 0 = β 0 ^ 4 * (β 0 ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4, this, inv_one, one_mul]
    have hb : ψ.symm b = 1 := by
      apply Subtype.ext
      rw [← hβb, Subgroup.coe_one, hβc, h01]
      exact CFSG.RankThree.PartOne.KFU.diagU_one
    rw [← MulEquiv.apply_symm_apply ψ b, hb, map_one]
  intro x hxD
  rw [Subgroup.mem_centralizer_iff]
  intro y hyT
  by_contra hxy
  obtain ⟨δ, -, -, hδx⟩ := hdiag (ψ.symm x) (by rw [MulEquiv.apply_symm_apply]; exact hxD)
  have hz : x * y * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hDT hxD) y).mp hyT
  set t₁ : Matrix (Fin 4) (Fin 4) K :=
    (((ψ.symm y : unitarySU 2 1 K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) with ht₁
  set t₂ : Matrix (Fin 4) (Fin 4) K :=
    (((ψ.symm (x * y * x⁻¹) : unitarySU 2 1 K 4) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    with ht₂
  have hsq₁ : t₁ * t₁ = 1 := by
    rw [ht₁, ← Units.val_mul, hinv y hyT, Units.val_one]
  have hsq₂ : t₂ * t₂ = 1 := by
    rw [ht₂, ← Units.val_mul, hinv _ hz, Units.val_one]
  have hstar : (t₁.map hU.bar)ᵀ = t₁ := by
    calc (t₁.map hU.bar)ᵀ = (t₁.map hU.bar)ᵀ * (t₁ * t₁) := by rw [hsq₁, Matrix.mul_one]
      _ = ((t₁.map hU.bar)ᵀ * t₁) * t₁ := by rw [Matrix.mul_assoc]
      _ = t₁ := by rw [(hmemU _).2, Matrix.one_mul]
  have hH : ∀ i j, t₁ i j = t₁ j i ^ 2 := by
    intro i j
    have := congrFun (congrFun hstar i) j
    rw [Matrix.transpose_apply, Matrix.map_apply, hbar] at this
    exact this.symm
  have hUt : ∀ j k, ∑ i, t₁ i j ^ 2 * t₁ i k = if j = k then 1 else 0 := by
    intro j k
    have := congrFun (congrFun (hmemU (ψ.symm y)).2 j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa only [Matrix.transpose_apply, Matrix.map_apply, hbar] using this
  have hcb : (ψ.symm y : GL (Fin 4) K) * diagU β = diagU β * (ψ.symm y : GL (Fin 4) K) := by
    rw [hβb]
    have h1 : ψ.symm y * ψ.symm b = ψ.symm b * ψ.symm y := by
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp hbC y hyT)]
    exact congrArg Subtype.val h1
  have hβt : ∀ i j, t₁ i j ≠ 0 → (β i : K) = (β j : K) := by
    intro i j hij
    by_contra hne
    exact hij (Item223KFactsProof.entry_eq_zero_of_commute_diagU hcb
      (fun h => hne (congrArg Units.val h)))
  have ht₂eq : (ψ.symm (x * y * x⁻¹) : GL (Fin 4) K) =
      diagU δ * (ψ.symm y : GL (Fin 4) K) * (diagU δ)⁻¹ := by
    rw [hδx, map_mul, map_mul, map_inv]
    rfl
  have hsupp : ∀ i j, t₂ i j ≠ 0 → t₁ i j ≠ 0 := by
    intro i j hij
    rw [ht₂, ht₂eq, Units.val_mul, Units.val_mul, Matrix.mul_apply] at hij
    obtain ⟨c, -, hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
    rw [Matrix.mul_apply] at hc
    obtain ⟨c', -, hc'⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hc)
    have hc'' := right_ne_zero_of_mul hc'
    have hcj : ((diagU δ)⁻¹ : GL (Fin 4) K) c j ≠ 0 := right_ne_zero_of_mul hc
    have hd : ((diagU δ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i c' ≠ 0 :=
      left_ne_zero_of_mul hc'
    have hic' : i = c' := by
      by_contra h
      rw [diagU_val, Matrix.diagonal_apply_ne _ h] at hd
      exact hd rfl
    have hcj' : c = j := by
      by_contra h
      apply hcj
      have hinv' : ((diagU δ)⁻¹ : GL (Fin 4) K) = diagU δ⁻¹ := by
        rw [inv_eq_iff_mul_eq_one, CFSG.RankThree.PartOne.KFU.diagU_mul, mul_inv_cancel,
          CFSG.RankThree.PartOne.KFU.diagU_one]
      rw [hinv', diagU_val, Matrix.diagonal_apply_ne _ h]
    rw [← hic', hcj'] at hc''
    exact hc''
  have hc : t₁ * t₂ = t₂ * t₁ := by
    have h1 : ψ.symm y * ψ.symm (x * y * x⁻¹) = ψ.symm (x * y * x⁻¹) * ψ.symm y := by
      have h0 : y * (x * y * x⁻¹) = x * y * x⁻¹ * y :=
        congrArg Subtype.val (hTe.1.is_comm.comm ⟨y, hyT⟩ ⟨_, hz⟩)
      rw [← map_mul, ← map_mul, h0]
    have h2' := congrArg (fun g : unitarySU 2 1 K 4 => ((g : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) h1
    simpa only [Subgroup.coe_mul, Units.val_mul] using h2'
  have heq := eq_of_mul_comm_of_support h2 hcube hH hUt hβt hns hsq₁ hsq₂ hc hsupp
  apply hxy
  have h3 : ψ.symm y = ψ.symm (x * y * x⁻¹) := Subtype.ext (Units.ext heq)
  have h4 : y = x * y * x⁻¹ := ψ.symm.injective h3
  calc y * x = x * y * x⁻¹ * x := by rw [← h4]
    _ = x * y := by group

end CFSG.RankThree.PartTwo.Sec21
