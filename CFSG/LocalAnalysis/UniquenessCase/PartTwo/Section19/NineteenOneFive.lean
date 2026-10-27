module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight
public import CFSG.GroupTheory.AltFiveConjCommutator
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_zpowers_five_of_isA5A5Cyclic5 {X : Type} [Group X]
    (h : S17.IsA5A5Cyclic5 ↥(CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup X))) :
    ∃ f : X, orderOf f = 5 ∧ ∀ m : X, m * f * m⁻¹ ∈ Subgroup.zpowers f := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set P := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup X) with hPdef
  obtain ⟨e, he1, ⟨φ⟩⟩ := h
  set C := Multiplicative (ZMod (5 ^ e)) with hCdef
  have : NeZero (5 ^ e) := ⟨by positivity⟩
  have hPn : P.Normal := uc22p22r_pElementSubgroup_normal
  have hcardC : Nat.card C = 5 ^ e := by
    rw [hCdef, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have h5C : 5 ∣ Nat.card C := by
    rw [hcardC]
    exact dvd_pow_self 5 (by omega)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 5 h5C
  let f₀ : ↥P := φ.symm (1, 1, c)
  have hf₀ord : orderOf f₀ = 5 := by
    have h1 : orderOf f₀ = orderOf ((1, 1, c) : alternatingGroup (Fin 5) ×
        alternatingGroup (Fin 5) × C) := MulEquiv.orderOf_eq φ.symm _
    rw [h1, Prod.orderOf, Prod.orderOf]
    simp [hc]
  refine ⟨(f₀ : X), by rw [Subgroup.orderOf_coe, hf₀ord], ?_⟩
  intro m
  let g₀ : ↥P := ⟨m * (f₀ : X) * m⁻¹, hPn.conj_mem _ f₀.2 m⟩
  have hf₀c : ∀ y : ↥P, f₀ * y = y * f₀ := by
    intro y
    apply φ.injective
    rw [map_mul, map_mul]
    show φ (φ.symm (1, 1, c)) * φ y = φ y * φ (φ.symm (1, 1, c))
    rw [MulEquiv.apply_symm_apply]
    ext
    · simp
    · simp
    · simp [mul_comm]
  have hg₀c : ∀ y : ↥P, g₀ * y = y * g₀ := by
    intro y
    apply Subtype.ext
    have hy' : m⁻¹ * (y : X) * m ∈ P := by
      have := hPn.conj_mem _ y.2 m⁻¹
      simpa using this
    have h1 := congrArg Subtype.val (hf₀c ⟨m⁻¹ * (y : X) * m, hy'⟩)
    simp only [Subgroup.coe_mul] at h1
    show m * (f₀ : X) * m⁻¹ * y = y * (m * (f₀ : X) * m⁻¹)
    calc m * (f₀ : X) * m⁻¹ * y = m * ((f₀ : X) * (m⁻¹ * y * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * y * m) * (f₀ : X)) * m⁻¹ := by rw [h1]
      _ = y * (m * (f₀ : X) * m⁻¹) := by group
  have hg₀ord : orderOf g₀ = 5 := by
    have h1 : orderOf (g₀ : X) = orderOf (f₀ : X) := by
      have hsc : SemiconjBy m (f₀ : X) (m * (f₀ : X) * m⁻¹) := by
        unfold SemiconjBy
        group
      exact (SemiconjBy.orderOf_eq m hsc).symm
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe] at h1
    rw [h1, hf₀ord]
  have hφc : ∀ y, φ g₀ * y = y * φ g₀ := by
    intro y
    have := congrArg φ (hg₀c (φ.symm y))
    simpa [map_mul] using this
  obtain ⟨h11, h12⟩ := CFSG.GroupTheory.eq_one_one_of_central hφc
  set c' : C := (φ g₀).2.2 with hc'def
  have hφg₀ : φ g₀ = (1, 1, c') := Prod.ext h11 (Prod.ext h12 rfl)
  have hc'ord : orderOf c' = 5 := by
    have h1 : orderOf (φ g₀) = 5 := by rw [MulEquiv.orderOf_eq]; exact hg₀ord
    rw [hφg₀, Prod.orderOf, Prod.orderOf] at h1
    simpa using h1
  have hzp : Subgroup.zpowers c' = Subgroup.zpowers c := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, hc'ord, hc]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    (hzp ▸ Subgroup.mem_zpowers c' : c' ∈ Subgroup.zpowers c)
  have hg₀eq : g₀ = f₀ ^ k := by
    apply φ.injective
    rw [hφg₀, map_zpow]
    show (1, 1, c') = (φ (φ.symm (1, 1, c))) ^ k
    rw [MulEquiv.apply_symm_apply, ← hk]
    exact Prod.ext (by simp) (Prod.ext (by simp) (by simp))
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  have := congrArg Subtype.val hg₀eq
  simpa using this.symm

theorem exists_normal_zpowers_five_bar2 (D : Data G)
    {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h68 : S17.R17_68At D V₀ V) (hL2 : IsL2 (Bar2 L) 2) :
    ∃ f : Bar2 D.M, orderOf f = 5 ∧ ∀ m : Bar2 D.M, m * f * m⁻¹ ∈ Subgroup.zpowers f :=
  exists_normal_zpowers_five_of_isA5A5Cyclic5
    (h68 p h.hyp.hp L h.hyp.hL _ rfl h.hyp.hX (S17.isAlt_five_of_isL2_two hL2)).2.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
