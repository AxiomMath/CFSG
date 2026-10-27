module

public import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
public import CFSG.LocalAnalysis.StandardType.GGTorusGenSLComp
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBPermAut
import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBRefl
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJSwap
import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLinePSL

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.SeitzReduction.LinearPilot

private theorem permAut_swap_mem_reflSetIn {G : Type} [Group G] [Finite G] {p : ℕ}
    {L J : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
    {φ : SpecialLinearGroup (Fin (m + 1)) F →* L} {A : Subgroup (MulAut ↥L)}
    (hN : ∀ σ, NbrInnerWeylA.permConj φ σ ∈
      Subgroup.normalizer (A : Set (MulAut ↥L)))
    {S : Finset (Fin (m + 1))} {i j : Fin (m + 1)} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    (hJ : J = (blockSpecialLinear (K := F) S).map (L.subtype.comp φ))
    (hm3 : 3 ≤ m + 1)
    (hker : ∀ g, φ g = 1 → g ∈ scalars (m + 1) F)
    (hdiag : ∀ a ∈ A, ∃ t : Fin (m + 1) → F, TypeANbrDvd.ActsDiag φ a t)
    (hAp : ∀ a ∈ A, a ^ p = 1) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card F - 1) (hφs : Function.Surjective φ) (hA : IsElemAbelian p A)
    (hsc : GGTorusSelfCent p A) :
    TypeANbrDvd.permAut φ A hN (Equiv.swap i j) ∈ ggTorusReflSetIn p J A := by
  set τ : Equiv.Perm (Fin (m + 1)) := Equiv.swap i j with hτ
  have hnW : GGTorusWeylElt p A (φ (TypeA.permSL τ⁻¹)) :=
    weyl_mul_apply_inv_diag hker hdiag hAp _ ⟨τ⁻¹, rfl⟩
  have hnN : MulAut.conj (φ (TypeA.permSL τ⁻¹)) ∈
      Subgroup.normalizer (A : Set (MulAut ↥L)) := hN τ
  have hnJ : ((φ (TypeA.permSL τ⁻¹) : ↥L) : G) ∈ J := by
    rw [hJ]
    have hτinv : τ⁻¹ = Equiv.swap i j := by rw [hτ, Equiv.swap_inv]
    rw [hτinv]
    exact Subgroup.mem_map_of_mem _ (ggPermSL_swap_mem_blockSpecialLinear (I := S) hi hj)
  have heq : TypeANbrDvd.permAut φ A hN τ = ggConjAut A hnN :=
    TypeANbrDvd.permAut_apply φ A hN τ
  have hR : GGIsReflection p (TypeANbrDvd.permAut φ A hN τ) := by
    obtain ⟨-, -, -, -, hR⟩ :=
      TypeANbrDvd.permAut_swap_mem_reflSet hp hp2 hpK hm3 hφs hker hA hsc
        hdiag hN (i := i) (j := j) hij
    exact hR
  exact ⟨φ (TypeA.permSL τ⁻¹), hnN, hnJ, hnW, heq, hR⟩

theorem ggTBJR1Lin_noncomm {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {L J : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2] {d : ℕ} (hd : 4 ≤ d)
    (hpF : p ∣ Nat.card F - 1) {φ : SpecialLinearGroup (Fin d) F →* L}
    (hφs : Function.Surjective φ) (hker : ∀ g, φ g = 1 → g ∈ scalars d F)
    {A : Subgroup (MulAut ↥L)} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → F, TypeANbrDvd.ActsDiag φ a t)
    {S : Finset (Fin d)} (hS3 : 3 ≤ S.card)
    (hJ : J = (blockSpecialLinear (K := F) S).map (L.subtype.comp φ)) :
    ∃ a ∈ ggTorusReflSetIn p J A, ∃ b ∈ ggTorusReflSetIn p J A, a * b ≠ b * a := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  have hm3 : 3 ≤ m + 1 := by omega
  have hp2 : p ≠ 2 := LinUnitL.prime_ne_two_of_dvd_card_sub_one hpF
  have hN : ∀ σ, NbrInnerWeylA.permConj φ σ ∈
      Subgroup.normalizer (A : Set (MulAut ↥L)) :=
    TypeANbrDvd.permConj_mem_normalizer_of_selfCent hφs hker hA.2 hsc hdiag
  let ρ := TypeANbrDvd.permAut φ A hN
  have hρinj : Function.Injective ρ :=
    TypeANbrDvd.permAut_injective hp hp2 hpF hd hφs hker hA hsc hdiag hN
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (s := S) hS3
  obtain ⟨i, j, k, hij, hik, hjk, rfl⟩ := Finset.card_eq_three.mp hTcard
  have hi : i ∈ S := hTS (by simp)
  have hj : j ∈ S := hTS (by simp)
  have hk : k ∈ S := hTS (by simp)
  have hmem1 : ρ (Equiv.swap i j) ∈ ggTorusReflSetIn p J A :=
    permAut_swap_mem_reflSetIn hN hi hj hij hJ hm3 hker hdiag hA.2 hp hp2 hpF hφs hA hsc
  have hmem2 : ρ (Equiv.swap j k) ∈ ggTorusReflSetIn p J A :=
    permAut_swap_mem_reflSetIn hN hj hk hjk hJ hm3 hker hdiag hA.2 hp hp2 hpF hφs hA hsc
  refine ⟨ρ (Equiv.swap i j), hmem1, ρ (Equiv.swap j k), hmem2, ?_⟩
  intro hcomm
  have hperm : ρ (Equiv.swap i j * Equiv.swap j k) =
      ρ (Equiv.swap j k * Equiv.swap i j) := by
    rw [map_mul, map_mul]
    exact hcomm
  have heqperm := hρinj hperm
  have hval := congrArg (fun σ : Equiv.Perm (Fin (m + 1)) => σ i) heqperm
  simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne,
    hij, hik, hjk] at hval

end CFSG.StandardType

end
