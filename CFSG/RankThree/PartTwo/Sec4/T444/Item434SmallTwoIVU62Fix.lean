module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Torus
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Eigen
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIVU62Group
import CFSG.RankThree.PartOne.Q1327C.BU5Diag

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

theorem exists_isPrimitiveRoot_three : ∃ ζ : F4, IsPrimitiveRoot ζ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ξ, hξ⟩ := exists_prime_orderOf_dvd_card' (G := F4ˣ) 3 (by rw [card_units_F4])
  have hprim : IsPrimitiveRoot ξ 3 := by
    have := IsPrimitiveRoot.orderOf ξ
    rwa [hξ] at this
  exact ⟨ξ, IsPrimitiveRoot.coe_units_iff.mpr hprim⟩

theorem exists_scalar_comm {a b : GU6} (h : conj6 a * conj6 b = conj6 b * conj6 a) :
    ∃ c : F4ˣ, ((a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * (b : GL (Fin 6) F4) =
      (c : F4) • (((b : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * (a : GL (Fin 6) F4)) := by
  have h1 : conj6 ⁅a, b⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 h
  have h2 : ⁅a, b⁆ ∈ scalarGU6.range := by
    rw [← ker_conj6]
    exact h1
  obtain ⟨c, hc⟩ := h2
  refine ⟨c, ?_⟩
  have h3 : (GeneralLinearGroup.scalar (Fin 6) c : GL (Fin 6) F4) =
      (a : GL (Fin 6) F4) * b * (a : GL (Fin 6) F4)⁻¹ * (b : GL (Fin 6) F4)⁻¹ := by
    have := congrArg (fun g : GU6 => (g : GL (Fin 6) F4)) hc
    simpa [commutatorElement_def, coe_scalarGU6] using this
  have h4 : (a : GL (Fin 6) F4) * b = GeneralLinearGroup.scalar (Fin 6) c * ((b : GL (Fin 6) F4) *
      a) := by
    rw [h3]
    group
  have h5 := congrArg (fun g : GL (Fin 6) F4 => (g : Matrix (Fin 6) (Fin 6) F4)) h4
  simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply] at h5
  rw [← smul_eq_diagonal_mul] at h5
  exact h5

theorem conj6_hR {S : Subgroup (MulAut P6)} (hSc : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hS3 : ∀ x ∈ S, x ^ 3 = 1) (a b r : GU6) (ha : conj6 a ∈ S) (hb : conj6 b ∈ S)
    (hr : conj6 r ∈ S) (ha3 : a ^ 3 = 1) (hab : a * b ≠ b * a) (hra : r * a = a * r) :
    r ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := exists_scalar_comm (hSc _ ha _ hb)
  have hc1 : (c : F4) ≠ 1 := by
    intro h1
    apply hab
    apply Subtype.ext
    apply Units.ext
    rw [h1, one_smul] at hc
    exact hc
  have hr3 : conj6 (r ^ 3) = 1 := by
    rw [map_pow]
    exact hS3 _ hr
  obtain ⟨d, hd⟩ : r ^ 3 ∈ scalarGU6.range := by
    rw [← ker_conj6]
    exact hr3
  by_contra hne
  have hd1 : (d : F4) ≠ 1 := by
    intro h1
    apply hne
    rw [← hd, Units.val_eq_one.1 h1, map_one]
  have ha3' : ((a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ^ 3 = 1 := by
    have := congrArg (fun g : GU6 => ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) ha3
    simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this
  have hra' : ((r : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * (a : GL (Fin 6) F4) =
      ((a : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) * (r : GL (Fin 6) F4) := by
    have := congrArg (fun g : GU6 => ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) hra
    simpa using this
  have hr3' : ((r : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) ^ 3 = (d : F4) • 1 := by
    have := congrArg (fun g : GU6 => ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) hd
    simp only [coe_scalarGU6, GeneralLinearGroup.coe_scalar, Subgroup.coe_pow,
      Units.val_pow_eq_pow_val, scalar_apply] at this
    rw [smul_one_eq_diagonal]
    exact this.symm
  exact false_of_cube_scalar two_eq_zero_F4 (fun x hx => pow_three_F4 hx) ha3'
    (b : GL (Fin 6) F4).isUnit c.ne_zero hc1 hc hra' d.ne_zero hd1 hr3'

theorem exists_fixed_e81 {Astar : Subgroup (MulAut P6)}
    (hA : CFSG.Assembly.IsElemAbelian 3 Astar) (hcard : Nat.card Astar = 27) :
    ∃ Bs : Subgroup (MulAut P6), Bs ≤ Astar ∧ 9 ≤ Nat.card Bs ∧
      ∃ D : Subgroup P6, CFSG.Assembly.IsElemAbelian 3 D ∧ 81 ≤ Nat.card D ∧
        ∀ β ∈ Bs, ∀ d ∈ D, β d = d := by
  have hSc : ∀ x ∈ Astar, ∀ y ∈ Astar, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hS3 : ∀ x ∈ Astar, x ^ 3 = 1 := hA.2
  have hSr : Astar ≤ conj6.range := fun α hα => by
    obtain ⟨A, hA'⟩ := exists_conj6_eq_of_pow_three (hS3 α hα)
    exact ⟨A, hA'⟩
  obtain ⟨B, hkerB, hBS, hB27, hBc, hB3⟩ := exists_abelian_exp_three_of_comap conj6 Astar
    ker_conj6_le_center card_ker_conj6 hSc hS3 hSr hcard
    (fun a b r ha hb hr ha3 hab hra => conj6_hR hSc hS3 a b r ha hb hr ha3 hab hra)
  refine ⟨B.map conj6, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hBS x hx
  · have := card_eq_card_ker_mul_card_map conj6 hkerB
    rw [card_ker_conj6] at this
    omega
  · obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_three
    obtain ⟨P, hP⟩ := CFSG.RankThree.PartOne.Q1327C.exists_unitary_conj_diag_m uData hζ
      (by norm_num : 3 ∣ 2 ^ 1 + 1) B hBc hB3
    have hDe : CFSG.Assembly.IsElemAbelian 3 (torusP6.range.map (conj6 P).toMonoidHom) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨_, a', ha', rfl⟩ := a
        obtain ⟨_, b', hb', rfl⟩ := b
        apply Subtype.ext
        change conj6 P a' * conj6 P b' = conj6 P b' * conj6 P a'
        have hcomm : a' * b' = b' * a' := congrArg Subtype.val
          (isElemAbelian_range_torusP6.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩)
        rw [← map_mul, ← map_mul, hcomm]
      · rintro _ ⟨a', ha', rfl⟩
        change (conj6 P a') ^ 3 = 1
        rw [← map_pow, isElemAbelian_range_torusP6.2 a' ha', map_one]
    refine ⟨torusP6.range.map (conj6 P).toMonoidHom, hDe, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (f := (conj6 P).toMonoidHom) (conj6 P).injective,
        card_range_torusP6]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨_, ⟨y, rfl⟩, rfl⟩
      have h1 : conj6 x * conj6 P = conj6 P * conj6 (P⁻¹ * x * P) := by
        rw [← map_mul, ← map_mul]
        congr 1
        group
      calc conj6 x (conj6 P (torusP6 y)) = (conj6 x * conj6 P) (torusP6 y) := rfl
        _ = (conj6 P * conj6 (P⁻¹ * x * P)) (torusP6 y) := by rw [h1]
        _ = conj6 P (conj6 (P⁻¹ * x * P) (torusP6 y)) := rfl
        _ = conj6 P (torusP6 y) := by rw [conj6_torusP6 (hP x hx) y]

end CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIVU62
