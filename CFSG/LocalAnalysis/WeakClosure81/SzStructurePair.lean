module

public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiRelations
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

open Subgroup CFSG.SectionRank.LargeRee CFSG.BenderSuzuki.PFAppendixIII

theorem exists_suzukiGroup_involution_pair (a : ℕ) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ u v : CFSG.Blueprint.suzukiGroup a K, u * u = 1 ∧ v * v = 1 ∧
      orderOf (u * v) = 2 ^ (2 * a + 1) - 1 := by
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hWW : CFSG.Blueprint.suzukiW K * CFSG.Blueprint.suzukiW K = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.Blueprint.suzukiW, Matrix.mul_apply, Fin.sum_univ_four]
  let W : CFSG.Blueprint.suzukiGroup a K :=
    ⟨⟨CFSG.Blueprint.suzukiW K, CFSG.Blueprint.suzukiW K, hWW, hWW⟩,
      Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩
  let D := suzukiDElt a l
  have h1 : W * W = 1 := Subtype.ext (Units.ext hWW)
  have h2 : W * D * W = suzukiDElt a l⁻¹ :=
    Subtype.ext (Units.ext (suzukiW_mul_suzukiD_mul_suzukiW a l))
  let φ : Kˣ →* CFSG.Blueprint.suzukiGroup a K :=
    MonoidHom.mk' (suzukiDElt a)
      (fun l m => Subtype.ext (Units.ext (CFSG.LieType.Ree.suzukiD_mul a l m).symm))
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro μ hμ
    have hM : CFSG.Blueprint.suzukiD a μ = 1 := by
      have h := congrArg (fun g : CFSG.Blueprint.suzukiGroup a K =>
        (((g : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)) hμ
      change CFSG.Blueprint.suzukiD a μ = 1 at h
      exact h
    have h00 : ((μ ^ (1 + (2 ^ a : ℤ)) : Kˣ) : K) = 1 := by
      have h := congrFun (congrFun hM 0) 0
      simpa [CFSG.Blueprint.suzukiD, Matrix.diagonal_apply_eq] using h
    have h11 : ((μ ^ (2 ^ a : ℤ) : Kˣ) : K) = 1 := by
      have h := congrFun (congrFun hM 1) 1
      simpa [CFSG.Blueprint.suzukiD, Matrix.diagonal_apply_eq] using h
    have hA : μ ^ (1 + (2 ^ a : ℤ)) = 1 := Units.val_eq_one.mp h00
    have hB : μ ^ (2 ^ a : ℤ) = 1 := Units.val_eq_one.mp h11
    calc
      μ = μ ^ (1 + (2 ^ a : ℤ)) * (μ ^ (2 ^ a : ℤ))⁻¹ := by
            rw [zpow_add, zpow_one]; group
      _ = 1 := by rw [hA, hB, inv_one, mul_one]
  have hDord : orderOf D = 2 ^ (2 * a + 1) - 1 := by
    calc
      orderOf D = orderOf (φ l) := rfl
      _ = orderOf l := orderOf_injective φ hφinj l
      _ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hl
      _ = Nat.card K - 1 := Nat.card_units K
      _ = 2 ^ (2 * a + 1) - 1 := by rw [hK]
  refine ⟨W, W * D, h1, ?_, ?_⟩
  · calc
      (W * D) * (W * D) = (W * D * W) * D := by group
      _ = suzukiDElt a l⁻¹ * D := by rw [h2]
      _ = (suzukiDElt a l)⁻¹ * D := by rw [suzukiDElt_inv]
      _ = 1 := inv_mul_cancel D
  · have huv : W * (W * D) = D := by rw [← mul_assoc, h1, one_mul]
    calc
      orderOf (W * (W * D)) = orderOf D := by rw [huv]
      _ = 2 ^ (2 * a + 1) - 1 := hDord

theorem exists_involution_pair_of_isSz {S : Type} [Group S] {n : ℕ}
    (hS : CFSG.Quasithin.IsSz n S) :
    ∃ u v : S, u * u = 1 ∧ v * v = 1 ∧ orderOf (u * v) = 2 ^ n - 1 := by
  obtain ⟨-, a, _, K, _, _, rfl, hK, ⟨e⟩⟩ := hS
  obtain ⟨u₀, v₀, hu₀, hv₀, huv₀⟩ := exists_suzukiGroup_involution_pair a hK
  exact ⟨e.symm u₀, e.symm v₀, by rw [← map_mul, hu₀, map_one],
    by rw [← map_mul, hv₀, map_one], by rw [← map_mul, MulEquiv.orderOf_eq, huv₀]⟩

theorem isConj_of_involutions_of_isSz {S : Type} [Group S] [Finite S] {n : ℕ}
    (hS : CFSG.Quasithin.IsSz n S) {x y : S} (hx : x * x = 1) (hx1 : x ≠ 1)
    (hy : y * y = 1) (hy1 : y ≠ 1) : IsConj x y := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hS
  let e' : S ≃* CFSG.Open.Sz a :=
    e.trans ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hK))
  have hM := CFSG.ComponentClassification.AschbacherToolkit.Bender.isStronglyEmbedded_of_fusion
    ((CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_sz ha e') default).1
  obtain ⟨g, hg⟩ := hM.involutions_conjugate ⟨hx1, by rw [pow_two]; exact hx⟩
    ⟨hy1, by rw [pow_two]; exact hy⟩
  exact isConj_iff.mpr ⟨g⁻¹, by simpa [rightConjugateElem] using hg⟩

theorem exists_orderOf_mul_conj_of_isSz {S : Type} [Group S] [Finite S] {n : ℕ}
    (hS : CFSG.Quasithin.IsSz n S) {a : S} (ha : a * a = 1) (ha1 : a ≠ 1) :
    ∃ g : S, orderOf (a * (g⁻¹ * a * g)) = 2 ^ n - 1 := by
  obtain ⟨u, v, hu, hv, huv⟩ := exists_involution_pair_of_isSz hS
  have hn3 : 3 ≤ n := by
    obtain ⟨-, b, hb, -, -, -, hn, -⟩ := hS
    omega
  have hgt : 2 < 2 ^ n - 1 := by
    have h8 : 8 ≤ 2 ^ n := by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn3
    omega
  have hu1 : u ≠ 1 := by
    intro h
    have : orderOf v ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2)
      (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hv))
    rw [h, one_mul] at huv
    omega
  have hv1 : v ≠ 1 := by
    intro h
    have : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num : 0 < 2)
      (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hu))
    rw [h, mul_one] at huv
    omega
  obtain ⟨h, hh⟩ := isConj_iff.mp (isConj_of_involutions_of_isSz hS hu hu1 ha ha1)
  let v' : S := h * v * h⁻¹
  have hv'mul : v' * v' = 1 := by
    dsimp [v']
    rw [show (h * v * h⁻¹) * (h * v * h⁻¹) = h * (v * v) * h⁻¹ by group, hv]
    group
  have hv'1 : v' ≠ 1 := by
    intro hcon
    apply hv1
    rw [show v = h⁻¹ * v' * h by dsimp [v']; group, hcon]
    group
  obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_involutions_of_isSz hS ha ha1 hv'mul hv'1)
  refine ⟨c⁻¹, ?_⟩
  have hav' : a * v' = h * (u * v) * h⁻¹ := by
    dsimp [v']
    rw [← hh]
    group
  rw [inv_inv, hc, hav',
    show h * (u * v) * h⁻¹ = (MulAut.conj h) (u * v) by rw [MulAut.conj_apply],
    MulEquiv.orderOf_eq, huv]

end CFSG.LocalAnalysis.WeakClosure81.SevenK
