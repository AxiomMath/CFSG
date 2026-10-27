module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
public import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel suzukiS suzukiN suzukiGroup)
open CFSG.Open (StatedProj StatedSL)

theorem sectionalTwoRankLE_section {Y : Type} [Group Y] [Finite Y] {r : ℕ}
    (hY : CFSG.GH74.SectionalTwoRankLE Y r) (M : Subgroup Y) (N : Subgroup M) [N.Normal] :
    CFSG.GH74.SectionalTwoRankLE (M ⧸ N) r :=
  (hY.subgroup M).quotient N

theorem not_sectionalTwoRankLE_of_injective_of_sq_eq_one {A X : Type*} [CommGroup A] [Group X]
    {r : ℕ} (hA : ∀ a : A, a ^ 2 = 1) (hcard : 2 ^ r < Nat.card A) (φ : A →* X)
    (hφ : Function.Injective φ) : ¬ CFSG.GH74.SectionalTwoRankLE X r := by
  intro hX
  have hE : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup A) := ⟨inferInstance, fun x _ => hA x⟩
  have h := (CFSG.GH74.SectionalTwoRankLE.of_injective φ hφ hX).card_le_of_elementary ⊤ hE
  rw [Subgroup.card_top] at h
  omega

private theorem charP_two_of_natCard_eq_two_pow_sect {K : Type*} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 2 ^ n) : CharP K 2 := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := n) (by rwa [← Nat.card_eq_fintype_card])

theorem not_sectionalTwoRankLE_two_of_injective_multiplicative {K X : Type*} [Field K]
    [Finite K] [Group X] {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 3 ≤ n)
    (φ : Multiplicative K →* X) (hφ : Function.Injective φ) :
    ¬ CFSG.GH74.SectionalTwoRankLE X 2 := by
  have : CharP K 2 := charP_two_of_natCard_eq_two_pow_sect hK
  refine not_sectionalTwoRankLE_of_injective_of_sq_eq_one (fun a => ?_) ?_ φ hφ
  · apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, CharTwo.add_self_eq_zero]
  · rw [Nat.card_congr Multiplicative.toAdd, hK]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)

theorem exists_injective_multiplicative_statedProj_statedSL {m : ℕ} (hm : 2 ≤ m) (K : Type)
    [Field K] : ∃ φ : Multiplicative K →* StatedProj (StatedSL m K), Function.Injective φ := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  let T : Multiplicative K →* Matrix (Fin m) (Fin m) K :=
    { toFun := fun a => Matrix.transvection i j a.toAdd
      map_one' := Matrix.transvection_zero i j
      map_mul' := fun a b => (Matrix.transvection_mul_transvection_same i j hij _ _).symm }
  let T' : Multiplicative K →* StatedSL m K :=
    T.toHomUnits.codRestrict (StatedSL m K) fun a =>
      Subgroup.subset_closure (Matrix.det_transvection_of_ne i j hij a.toAdd)
  refine ⟨(QuotientGroup.mk' _).comp T', ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro a ha
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at ha
  obtain ⟨c, hc⟩ := ha
  have hij' := congrArg (fun g : GL (Fin m) K => (g : Matrix (Fin m) (Fin m) K) i j) hc
  simp [T', T, Matrix.transvection, hij] at hij'
  exact Subgroup.mem_bot.mpr (Multiplicative.toAdd.injective (by simpa using hij'.symm))

theorem exists_injective_multiplicative_suzukiGroup (a : ℕ) (K : Type) [Field K] [CharP K 2] :
    ∃ φ : Multiplicative K →* suzukiGroup a K, Function.Injective φ := by
  have hadd : ∀ x y : K, (x + y) ^ 2 ^ (a + 1) = x ^ 2 ^ (a + 1) + y ^ 2 ^ (a + 1) :=
    fun x y => add_pow_char_pow x y 2 (a + 1)
  let S : Multiplicative K →* Matrix (Fin 4) (Fin 4) K :=
    { toFun := fun v => suzukiS a 0 v.toAdd
      map_one' := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN]
      map_mul' := fun v w => by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [suzukiS, suzukiN, Matrix.mul_apply, Fin.sum_univ_four, hadd] }
  let S' : Multiplicative K →* suzukiGroup a K :=
    S.toHomUnits.codRestrict (suzukiGroup a K) fun v =>
      Subgroup.subset_closure (Or.inl ⟨0, v.toAdd, rfl⟩)
  refine ⟨S', fun v w hvw => ?_⟩
  have h20 := congrArg
    (fun g : suzukiGroup a K => ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 2 0) hvw
  simpa [S', S, suzukiS] using h20

theorem not_sectionalTwoRankLE_two_of_isCalL1 {X : Type} [Group X] [Finite X] (h : IsCalL1 X) :
    ¬ CFSG.GH74.SectionalTwoRankLE X 2 := by
  obtain ⟨n, hodd, hn1, hX⟩ := h
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hodd
    omega
  rcases hX with hL2 | hSz | hL3
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      (show LieModel X .PSL 2 2 n from hL2).statedClassicalModel (by decide)
    obtain ⟨φ, hφ⟩ := exists_injective_multiplicative_statedProj_statedSL le_rfl K
    exact not_sectionalTwoRankLE_two_of_injective_multiplicative hK hn3
      (e.symm.toMonoidHom.comp φ) (e.symm.injective.comp hφ)
  · obtain ⟨-, -, a, -, K, _, _, -, hK, ⟨e⟩⟩ :=
      (show LieModel X .twistedB2 0 2 n from hSz).suzukiModel
    have : CharP K 2 := charP_two_of_natCard_eq_two_pow_sect hK
    obtain ⟨φ, hφ⟩ := exists_injective_multiplicative_suzukiGroup a K
    exact not_sectionalTwoRankLE_two_of_injective_multiplicative hK hn3
      (e.symm.toMonoidHom.comp φ) (e.symm.injective.comp hφ)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ :=
      (show LieModel X .PSL 3 2 n from hL3).statedClassicalModel (by decide)
    obtain ⟨φ, hφ⟩ := exists_injective_multiplicative_statedProj_statedSL (m := 3) (by norm_num) K
    exact not_sectionalTwoRankLE_two_of_injective_multiplicative hK hn3
      (e.symm.toMonoidHom.comp φ) (e.symm.injective.comp hφ)

theorem not_isCalL1_of_sectionalTwoRankLE_two {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.GH74.SectionalTwoRankLE Y 2) (M : Subgroup Y) (N : Subgroup M) [N.Normal] :
    ¬ IsCalL1 (M ⧸ N) := fun h =>
  not_sectionalTwoRankLE_two_of_isCalL1 h (sectionalTwoRankLE_section hY M N)

end CFSG.LocalAnalysis.WeakClosure81

end
