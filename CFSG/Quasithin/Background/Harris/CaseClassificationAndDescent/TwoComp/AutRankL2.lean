module

public import CFSG.Quasithin.Background.Harris.L2.Rank

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp

open scoped MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField

theorem card_elemAbelian_mulAut_sl2 {n : ℕ} (hn : 2 ≤ n) {S : Type} [Group S]
    (e : S ≃* SL(2, GaloisField 2 n)) :
    ∀ B : Subgroup (MulAut S), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ n := by
  classical
  intro B hcomm hsq
  have hn0 : n ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
  let ψ : Gamma (GaloisField 2 n) ≃* MulAut S :=
    (gammaEquivMulAut (by omega) hcard).trans (MulAut.congr e.symm)
  let A : Subgroup (Gamma (GaloisField 2 n)) := B.comap ψ.toMonoidHom
  have hAcard : Nat.card A = Nat.card B := by
    have : A = B.map ψ.symm.toMonoidHom := by
      ext x
      simp only [A, Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
      constructor
      · intro h
        exact ⟨ψ x, h, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    rw [this]
    exact (Nat.card_congr (B.equivMapOfInjective _ ψ.symm.injective).toEquiv).symm
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    apply ψ.injective
    rw [map_mul, map_mul]
    exact hcomm _ hx _ hy
  have hAsq : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    apply ψ.injective
    rw [map_mul, map_one]
    exact hsq _ hx
  have hAea : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hAcomm x x.2 y y.2)⟩⟩
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
        apply Subtype.ext
        simpa [pow_two] using hAsq x x.2 }
  rw [← hAcard]
  by_cases hA : A ≤ linearKernel (GaloisField 2 n)
  ·
    let X : Subgroup SL(2, GaloisField 2 n) :=
      A.comap (SemidirectProduct.inl : SL(2, GaloisField 2 n) →* Gamma (GaloisField 2 n))
    have hXcard : Nat.card X = Nat.card A := by
      have hinj : Function.Injective
          (SemidirectProduct.inl : SL(2, GaloisField 2 n) →* Gamma (GaloisField 2 n)) :=
        SemidirectProduct.inl_injective
      refine Nat.card_congr (Equiv.ofBijective
        (fun x : X => (⟨SemidirectProduct.inl (x : SL(2, GaloisField 2 n)), x.2⟩ : A)) ⟨?_, ?_⟩)
      · intro x y h
        exact Subtype.ext (hinj (congrArg Subtype.val h))
      · intro a
        have ha := (mem_linearKernel_iff _).mp (hA a.2)
        have hg : (SemidirectProduct.inl (a : Gamma (GaloisField 2 n)).left :
            Gamma (GaloisField 2 n)) = a :=
          SemidirectProduct.ext (by simp) (by simp [ha])
        exact ⟨⟨(a : Gamma (GaloisField 2 n)).left, by simp [X, hg]⟩, Subtype.ext hg⟩
    have hXp : IsPGroup 2 X := by
      intro x
      refine ⟨1, ?_⟩
      have h := hAsq (SemidirectProduct.inl (x : SL(2, GaloisField 2 n))) x.2
      apply Subtype.ext
      rw [← map_mul] at h
      have := SemidirectProduct.inl_injective (h.trans (map_one _).symm)
      simpa [pow_two] using this
    have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have : CharP (GaloisField 2 n) 2 := inferInstance
    have hF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
      rw [← Nat.card_eq_fintype_card, hcard]
    rw [← hXcard]
    exact CFSG.Quasithin.G11.Harris.L2.card_le_of_isPGroup_sl2 hF X hXp
  ·
    obtain ⟨a, haA, haL⟩ := Set.not_subset.mp hA
    obtain ⟨-, hper⟩ := (original_even_SL2_outer_involution_field_conjugacy_and_rank
      (F := GaloisField 2 n) (by omega) hcard).2 A hAea hA
    obtain ⟨s, hs1, hns, -, -, -, -, -, -, hAle, -⟩ := hper a haA haL
    calc Nat.card A ≤ 2 ^ (s + 1) := hAle
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
