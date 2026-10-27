module

public import CFSG.Quasithin.EmptyFaithful.R3c5Star
public import CFSG.Quasithin.Background.A318PL3Iso
public import CFSG.GroupTheory.WeirSylow.UnitaryBridge
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.Quasithin.R3c5

open CFSG.Quasithin Matrix
open CFSG.Assembly.LowTwoRank (StatedProj StatedScalars)

section PGL

variable {K : Type} [Field K]

theorem scalar_injective_fin_three : Function.Injective (GeneralLinearGroup.scalar (Fin 3) (R := K)) := by
  intro a b hab
  apply Units.ext
  have h := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hab
  simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] using h

theorem card_statedProj_top_gl3 [Finite K] :
    Nat.card (StatedProj (⊤ : Subgroup (GL (Fin 3) K))) =
      Nat.card K ^ 3 * (((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 3 - 1)) := by
  set Z' : Subgroup ↥(⊤ : Subgroup (GL (Fin 3) K)) :=
    (StatedScalars (Fin 3) K).subgroupOf ⊤ with hZ'
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z'
  have h2 : Nat.card ↥(⊤ : Subgroup (GL (Fin 3) K)) = Nat.card (GL (Fin 3) K) := Subgroup.card_top
  have h3 : Nat.card ↥Z' = Nat.card Kˣ := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_top : StatedScalars (Fin 3) K ≤ ⊤)).toEquiv]
    exact Nat.card_congr
      (MonoidHom.ofInjective (scalar_injective_fin_three (K := K))).toEquiv.symm
  have h4 := Matrix.card_SL_mul_card_units (n := Fin 3) (R := K)
  have hpos : 0 < Nat.card Kˣ := Nat.card_pos
  have h5 : Nat.card (StatedProj (⊤ : Subgroup (GL (Fin 3) K))) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) := by
    have : Nat.card (StatedProj (⊤ : Subgroup (GL (Fin 3) K))) * Nat.card Kˣ =
        Nat.card (Matrix.SpecialLinearGroup (Fin 3) K) * Nat.card Kˣ := by
      rw [h4, ← h2, h1, h3]
    exact Nat.eq_of_mul_eq_mul_right hpos this
  rw [h5, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num : 1 ≤ 3)]
  have hI : Finset.Icc 2 3 = ({2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.prod_pair (by norm_num)]

end PGL

section PGU

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 mem_unitaryIsom3)

variable {p f : ℕ} {K : Type} [Field K]

theorem scalar_mem_statedGU_iff (h : UnitaryFieldData p f K) {c : Kˣ} :
    GeneralLinearGroup.scalar (Fin 3) c ∈ StatedGU 3 (p ^ f) K ↔ c ^ (p ^ f + 1) = 1 := by
  rw [A318P.statedGU_eq_unitaryIsom3 h]
  constructor
  · intro hc
    rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at hc
    have h0 := congrFun (congrFun hc 0) 0
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h0
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, ← UnitaryFieldData.bar_apply h]
    exact h0
  · intro hc
    have hN : h.bar (c : K) * c = 1 := by
      rw [UnitaryFieldData.bar_apply h, ← pow_succ, ← Units.val_pow_eq_pow_val, hc, Units.val_one]
    rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    simp [hN]

theorem succ_dvd_sq_sub_one {Q : ℕ} (hQ : 1 ≤ Q) : Q + 1 ∣ Q ^ 2 - 1 := by
  refine ⟨Q - 1, ?_⟩
  zify [hQ, show 1 ≤ Q ^ 2 from Nat.one_le_pow _ _ hQ]
  ring

theorem card_scalars_statedGU (h : UnitaryFieldData p f K) :
    Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedGU 3 (p ^ f) K)) = p ^ f + 1 := by
  have hfin : Finite K := h.finite
  let ρ : ↥(rootsOfUnity (p ^ f + 1) K) →* ↥(StatedGU 3 (p ^ f) K) :=
    ((GeneralLinearGroup.scalar (Fin 3) (R := K)).comp
      (rootsOfUnity (p ^ f + 1) K).subtype).codRestrict (StatedGU 3 (p ^ f) K)
      fun ζ => (scalar_mem_statedGU_iff h).2 ((mem_rootsOfUnity _ _).1 ζ.2)
  have hinj : Function.Injective ρ := by
    intro a b hab
    exact Subtype.ext (scalar_injective_fin_three (congrArg Subtype.val hab))
  have hrange : ρ.range = (StatedScalars (Fin 3) K).subgroupOf (StatedGU 3 (p ^ f) K) := by
    ext ⟨A, hA⟩
    constructor
    · rintro ⟨ζ, hζ⟩
      exact ⟨ζ.1, congrArg Subtype.val hζ⟩
    · intro hZ
      obtain ⟨c, rfl⟩ := hZ
      exact ⟨⟨c, (mem_rootsOfUnity _ _).2 ((scalar_mem_statedGU_iff h).1 hA)⟩, rfl⟩
  have hQ : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd, h.card, pow_mul']
  exact Nat.gcd_eq_right (succ_dvd_sq_sub_one hQ)

theorem card_statedGU_three (h : UnitaryFieldData p f K) :
    Nat.card (StatedGU 3 (p ^ f) K) =
      (p ^ f) ^ 3 * ((p ^ f + 1) * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1))) := by
  have hfin : Finite K := h.finite
  have := Fintype.ofFinite K
  have hq : Fintype.card K = (p ^ f) ^ 2 := by
    rw [← Nat.card_eq_fintype_card, h.card, pow_mul']
  have hc := CFSG.GroupTheory.WeirSylow.natCard_statedGU_cast hq (n := 3) (by norm_num)
  have hQ : 1 ≤ p ^ f := Nat.one_le_pow _ _ h.prime.pos
  have h2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hQ
  apply Nat.cast_injective (R := ℤ)
  rw [hc]
  have hI : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [hI, Finset.prod_insert (by decide), Finset.prod_pair (by decide),
    Finset.prod_insert (by decide), Finset.prod_pair (by decide)]
  push_cast [Nat.cast_sub h2]
  ring

theorem card_statedProj_statedGU_three (h : UnitaryFieldData p f K) :
    Nat.card (StatedProj (StatedGU 3 (p ^ f) K)) =
      (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((StatedScalars (Fin 3) K).subgroupOf (StatedGU 3 (p ^ f) K))
  rw [card_scalars_statedGU h, card_statedGU_three h] at h1
  have hpos : 0 < p ^ f + 1 := Nat.succ_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card (StatedProj (StatedGU 3 (p ^ f) K)) * (p ^ f + 1)
      = Nat.card (↥(StatedGU 3 (p ^ f) K) ⧸
          (StatedScalars (Fin 3) K).subgroupOf (StatedGU 3 (p ^ f) K)) * (p ^ f + 1) := rfl
    _ = (p ^ f) ^ 3 * ((p ^ f + 1) * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1))) := h1.symm
    _ = (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) * (p ^ f + 1) := by ring

end PGU

section Index

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem pglIndex_holds : PGLIndex := by
  intro s q A _ _ P X _ hP hX hmod
  obtain ⟨p, e, hp, he, rfl, hXs⟩ := hX
  have hQ : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  cases s
  · obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := hP
    have h : UnitaryFieldData p e K := ⟨hp, he, by rw [hK, ← pow_mul, mul_comm]⟩
    obtain ⟨-, -, -, -, hX3⟩ := psu3_data hXs
    have hcard := card_statedProj_statedGU_three h
    have h3 : 3 ∣ p ^ e + 1 := by
      have h' : Int.ModEq 3 ((p ^ e : ℕ) : ℤ) (-1) := by simpa using hmod
      unfold Int.ModEq at h'
      omega
    rw [Nat.gcd_eq_left h3] at hX3
    rw [Nat.card_congr φ.toEquiv, hcard, ← hX3, mul_comm]
  · obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := hP
    obtain ⟨-, -, -, -, hX3⟩ := psl3_data hXs
    have hcard := card_statedProj_top_gl3 (K := K)
    rw [hK] at hcard
    have h3 : 3 ∣ p ^ e - 1 := by
      have h' : Int.ModEq 3 ((p ^ e : ℕ) : ℤ) 1 := by simpa using hmod
      unfold Int.ModEq at h'
      omega
    rw [Nat.gcd_eq_left h3] at hX3
    rw [Nat.card_congr φ.toEquiv, hcard, ← hX3, mul_comm]

end Index

end CFSG.Quasithin.R3c5
