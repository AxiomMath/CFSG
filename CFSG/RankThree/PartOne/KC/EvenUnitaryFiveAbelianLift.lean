module

public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveDiagonalPlane
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveDiagonalize

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG CFSG.RankThree.LocalRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCEvenUnitaryFive

theorem even_unitary_five_abelian_lift_plane_core_intersection_trivial {f : ℕ} {K : Type}
    [Field K] (h : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)
    (B : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))
    (hB : (MulAut.conj : primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) →*
      MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))).range ≤ B)
    (A : Subgroup (MulAut (primeFormP h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))))
    (_hAB : A ≤ B) (hAD : A ≤ primeFormD h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K))
    (hAel : IsElementaryAbelian 5 A) (hAcard : Nat.card A = 5 ^ 2)
    (hab : ∀ x y : primeFormUnitary h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K),
      primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) x ∈ A →
      primeFormConjHom h ((1 : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) y ∈ A → x * y = y * x) :
    autThetaT 5 B A = ⊥ := by
  classical
  have hn : 3 ≤ 5 := by norm_num
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.le_of_dvd (by positivity) h5
    omega
  have hq3 : 3 < 2 ^ f := by omega
  have hfinK := h.finite
  have hfinT : Finite (primeFormP h (idGram K 5)) := finite_primeFormP
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set ρ := primeFormConjHom h (idGram K 5) with hρ
  set G : Subgroup (primeFormUnitary h (idGram K 5)) := A.comap ρ with hG
  have hGcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x := fun x hx y hy => hab x y hx hy
  have hGpow : ∀ x ∈ G, x ^ 5 ∈ idScalarKernel h 5 := fun x hx => by
    refine (primeFormConjHom_eq_one_iff hn hq3 _).mp ?_
    rw [map_pow]
    exact elemPow_eq_one_of_isElementaryAbelian _ hx
  have hGnc : ¬ IsCyclic G := by
    intro hcyc
    let π : G →* A := (ρ.comp G.subtype).codRestrict A (fun x => x.2)
    have hπ : Function.Surjective π := by
      intro a
      obtain ⟨x, hx⟩ := hAD a.2
      exact ⟨⟨x, by rw [hG, Subgroup.mem_comap, hx]; exact a.2⟩, Subtype.ext hx⟩
    have hAcyc : IsCyclic A := isCyclic_of_surjective π hπ
    have h1 := IsCyclic.exponent_eq_card (α := A)
    have h2 : Monoid.exponent A ∣ 5 := IsElementaryAbelian.exponent_dvd_p 5 A
    rw [hAcard] at h1
    rw [h1] at h2
    norm_num at h2
  obtain ⟨P, hP⟩ := exists_unitary_diagonalizing h h5 G hGcomm hGnc hGpow
  set γ0 : MulAut (primeFormP h (idGram K 5)) := (ρ P)⁻¹ with hγ0
  let φ : MulAut (MulAut (primeFormP h (idGram K 5))) := MulAut.conj γ0
  have hφρ : ∀ x : primeFormUnitary h (idGram K 5), φ (ρ x) = ρ (P⁻¹ * x * P) := by
    intro x
    change γ0 * ρ x * γ0⁻¹ = _
    rw [hγ0, map_mul, map_mul, map_inv, inv_inv]
  have hB' : (MulAut.conj : primeFormP h (idGram K 5) →*
      MulAut (primeFormP h (idGram K 5))).range ≤ B.map φ.toMonoidHom := by
    intro z hz
    refine Subgroup.mem_map.mpr ⟨φ.symm z, hB ?_, φ.apply_symm_apply z⟩
    have hnorm := (CFSG.ComponentClassification.OuterAutomorphisms.innerNormal
      (primeFormP h (idGram K 5)))
    have hz' : γ0⁻¹ * z * γ0⁻¹⁻¹ ∈ (MulAut.conj : primeFormP h (idGram K 5) →*
        MulAut (primeFormP h (idGram K 5))).range := hnorm.conj_mem z hz γ0⁻¹
    have hsymm : φ.symm z = γ0⁻¹ * z * γ0⁻¹⁻¹ := by
      rw [inv_inv]
      exact MulAut.conj_symm_apply γ0 z
    rw [hsymm]
    exact hz'
  have hAD' : A.map φ.toMonoidHom ≤ primeFormD h (idGram K 5) := by
    rintro _ ⟨a, haA, rfl⟩
    obtain ⟨x₀, hx₀⟩ := hAD haA
    refine ⟨P⁻¹ * x₀ * P, ?_⟩
    rw [← hφρ, hx₀]
    rfl
  have hdiag' : ∀ y : primeFormUnitary h (idGram K 5), ρ y ∈ A.map φ.toMonoidHom →
      ((y : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).IsDiag := by
    intro y hy
    obtain ⟨a, haA, hay⟩ := Subgroup.mem_map.mp hy
    obtain ⟨x₀, hx₀⟩ := hAD haA
    have hx₀G : x₀ ∈ G := by rw [hG, Subgroup.mem_comap, hx₀]; exact haA
    have hD0 := hP x₀ hx₀G
    have hay' : φ (ρ x₀) = ρ y := by rw [hx₀]; exact hay
    rw [hφρ] at hay'
    have h1 : ρ ((P⁻¹ * x₀ * P)⁻¹ * y) = 1 := by
      rw [map_mul, map_inv, hay', inv_mul_cancel]
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn hq3 _).mp h1
    have hy' : ((y : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) =
        ((P⁻¹ * x₀ * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) *
          GeneralLinearGroup.scalar (Fin 5) c := by
      rw [← hc, ← Subgroup.coe_mul, mul_inv_cancel_left]
    rw [hy', Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    intro i j hij
    rw [Matrix.mul_diagonal, hD0 hij, zero_mul]
  have hbot := autThetaT_eq_bot_of_diagonal h h5 (B.map φ.toMonoidHom) hB'
    (A.map φ.toMonoidHom) hAD' (IsElementaryAbelian.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hAcard]) hdiag'
  rw [← map_autThetaT_mulEquiv Nat.prime_five φ B A] at hbot
  exact (Subgroup.map_eq_bot_iff_of_injective (autThetaT 5 B A) (f := φ.toMonoidHom)
    φ.injective).mp hbot

end CFSG.RankThree.PartOne
