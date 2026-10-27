module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem exists_fixed_mod_of_isPGroup {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Finite V] (Λ : Subgroup (V ≃ₗ[K] V)) (hΛ : IsPGroup 2 Λ)
    (A S : Submodule K V) (hSA : S ≤ A) (hne : S ≠ A)
    (hA : ∀ T ∈ Λ, ∀ v ∈ A, T v ∈ A) (hS : ∀ T ∈ Λ, ∀ v ∈ S, T v ∈ S) :
    ∃ v ∈ A, v ∉ S ∧ ∀ T ∈ Λ, T v - v ∈ S := by
  let S' : Submodule K ↥A := S.comap A.subtype
  let act : Λ → (↥A →ₗ[K] ↥A) := fun T => LinearMap.restrict T.1.toLinearMap (hA T.1 T.2)
  have hact : ∀ T : Λ, S' ≤ S'.comap (act T) := by
    intro T v hv
    exact hS T.1 T.2 (v : V) hv
  let L : Λ → (↥A ⧸ S') →ₗ[K] (↥A ⧸ S') := fun T => Submodule.mapQ S' S' (act T) (hact T)
  have hL : ∀ (T : Λ) (v : ↥A), L T (Submodule.Quotient.mk v) = Submodule.Quotient.mk (act T v) :=
    fun T v => rfl
  letI : MulAction Λ (↥A ⧸ S') :=
    { smul := fun T q => L T q
      one_smul := fun q => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective S' q
        show L 1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v
        rw [hL]
        exact congrArg Submodule.Quotient.mk (Subtype.ext rfl)
      mul_smul := fun a b q => by
        obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective S' q
        show L (a * b) (Submodule.Quotient.mk v) = L a (L b (Submodule.Quotient.mk v))
        rw [hL b v, hL a (act b v), hL (a * b) v]
        exact congrArg Submodule.Quotient.mk (Subtype.ext rfl) }
  have hS'top : S' ≠ ⊤ := by
    intro htop
    apply hne
    refine le_antisymm hSA ?_
    intro v hv
    have hmem : (⟨v, hv⟩ : ↥A) ∈ S' := by
      rw [htop]
      exact Submodule.mem_top
    exact hmem
  haveI : Nontrivial (↥A ⧸ S') := Submodule.Quotient.nontrivial_iff.mpr hS'top
  haveI : Finite (↥A ⧸ S') :=
    Finite.of_surjective (Submodule.Quotient.mk : ↥A → ↥A ⧸ S')
      (Submodule.Quotient.mk_surjective S')
  haveI : Module.Finite K (↥A ⧸ S') := Module.Finite.of_finite
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hΛ.card_modEq_card_fixedPoints (↥A ⧸ S')
  have hQeven : 2 ∣ Nat.card (↥A ⧸ S') := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥A ⧸ S')]
    have hK : 2 ∣ Nat.card K := by
      haveI := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact (CharP.cast_eq_zero_iff K 2 _).mp (FiniteField.cast_card_eq_zero K)
    have hpos : 0 < Module.finrank K (↥A ⧸ S') := Module.finrank_pos
    exact dvd_pow hK hpos.ne'
  have hF : 2 ∣ Nat.card (MulAction.fixedPoints Λ (↥A ⧸ S')) :=
    (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hQeven))
  by_contra hcon
  have h0 : ∀ a : MulAction.fixedPoints Λ (↥A ⧸ S'), (a : ↥A ⧸ S') = 0 := by
    intro a
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective S' (a : ↥A ⧸ S')
    by_contra hz
    apply hcon
    refine ⟨(v : V), v.2, fun hvS => hz ?_, fun T hT => ?_⟩
    · rw [← hv]
      exact (Submodule.Quotient.mk_eq_zero S').mpr hvS
    · have hfix : (⟨T, hT⟩ : Λ) • (a : ↥A ⧸ S') = (a : ↥A ⧸ S') :=
        MulAction.mem_fixedPoints.mp a.2 ⟨T, hT⟩
      rw [← hv] at hfix
      have h2 : Submodule.Quotient.mk (act ⟨T, hT⟩ v) = (Submodule.Quotient.mk v : ↥A ⧸ S') :=
        hfix
      rw [Submodule.Quotient.eq] at h2
      exact h2
  have hsub : Subsingleton (MulAction.fixedPoints Λ (↥A ⧸ S')) :=
    ⟨fun a b => Subtype.ext ((h0 a).trans (h0 b).symm)⟩
  have hle : Nat.card (MulAction.fixedPoints Λ (↥A ⧸ S')) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hsub
  haveI : Nonempty (MulAction.fixedPoints Λ (↥A ⧸ S')) :=
    ⟨⟨0, MulAction.mem_fixedPoints.mpr fun g => map_zero (L g)⟩⟩
  have hpos : 0 < Nat.card (MulAction.fixedPoints Λ (↥A ⧸ S')) := Nat.card_pos
  have h2le := Nat.le_of_dvd hpos hF
  omega

end CFSG.RankThree.GF2n.Stroth80
