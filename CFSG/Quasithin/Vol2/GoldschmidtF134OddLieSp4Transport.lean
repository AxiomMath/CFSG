module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Borel
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.NQCore.Psp4

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique
open SymplecticFlag SymplecticHigher
open CFSG.Quasithin.F134.Sp4

theorem normalizes_of_mulEquiv_odd {A : Type*} [Group A] [Finite A] {L U P : Subgroup A}
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (ψ₀ : ↥L ≃* StatedSp 2 K)
    (hU : IsSylowTwoOf U L) (hPL : P ≤ L) {p a : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (ha : a = 2 ∨ a = 3) (hPa : Nat.card P = p ^ a) (hexp : ∀ x ∈ P, x ^ p = 1)
    (hmul : ∀ u ∈ U, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ U, u * x = y * s) :
    (∀ y ∈ P, ∀ u ∈ U, y * u * y⁻¹ ∈ U) ∧ (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) ∧
      p ∣ Nat.card K - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₁ := (U.subgroupOf L).map ψ₀.toMonoidHom with hU₁def
  have hU₁ : IsSylowTwoOf U₁ (⊤ : Subgroup (StatedSp 2 K)) := by
    refine ⟨le_top, (hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm).map _, ?_⟩
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right, hU₁def]
    erw [Subgroup.index_map_equiv]
    exact hU.2.2
  obtain ⟨g, -, hg⟩ := IsSylowTwoOf.exists_conj hU₁ (isSylowTwoOf_unipotent (K := K))
  set ψ : ↥L ≃* StatedSp 2 K := ψ₀.trans (MulAut.conj g) with hψ
  have hψU : ∀ l : L, ψ l ∈ unipotent 2 K ↔ (l : A) ∈ U := by
    intro l
    rw [hg, Subgroup.mem_map_equiv, hU₁def, Subgroup.mem_map_equiv, hψ, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Subgroup.mem_subgroupOf]
  set P₁ := (P.subgroupOf L).map ψ.toMonoidHom with hP₁
  have hP₁a : Nat.card P₁ = p ^ a := by
    rw [hP₁, Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective, ← hPa]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  have hP₁exp : ∀ x ∈ P₁, x ^ p = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow]
    have : y ^ p = 1 := Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.mp hy))
    rw [this, map_one]
  have hP₁U : ∀ u ∈ unipotent 2 K, ∀ x ∈ P₁, ∃ y ∈ P₁, ∃ s ∈ unipotent 2 K,
      u * x = y * s := by
    intro u hu x hx
    obtain ⟨x', hx', rfl⟩ := hx
    set u' := ψ.symm u with hu'
    have hu'U : (u' : A) ∈ U := (hψU u').mp (by rw [hu', MulEquiv.apply_symm_apply]; exact hu)
    obtain ⟨y, hy, s, hs, hys⟩ := hmul _ hu'U _ (Subgroup.mem_subgroupOf.mp hx')
    refine ⟨ψ ⟨y, hPL hy⟩, ⟨⟨y, hPL hy⟩, hy, rfl⟩, ψ ⟨s, hU.1 hs⟩, (hψU _).mpr hs, ?_⟩
    rw [← MulEquiv.apply_symm_apply ψ u, ← hu']
    change ψ u' * ψ x' = _
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hys
  obtain ⟨hB, h3⟩ := le_borelSubgroup_of_mul_odd hK hp2 ha hP₁a hP₁exp hP₁U
  refine ⟨fun y hy u hu => ?_, fun x hx y hy => ?_, h3⟩
  · have hyB : ψ ⟨y, hPL hy⟩ ∈ Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
      rw [normalizer_unipotent]
      exact hB ⟨⟨y, hPL hy⟩, hy, rfl⟩
    have huU : ψ ⟨u, hU.1 hu⟩ ∈ unipotent 2 K := (hψU _).mpr hu
    have h1 := (Subgroup.mem_normalizer_iff.mp hyB _).mp huU
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    exact (hψU _).mp h1
  · have hP₁p : IsPGroup p P₁ := IsPGroup.of_card hP₁a
    have h1 := mul_comm_of_le_borelSubgroup hp2 hP₁p hB
      (x := ψ ⟨x, hPL hx⟩) (y := ψ ⟨y, hPL hy⟩) ⟨⟨x, hPL hx⟩, hx, rfl⟩ ⟨⟨y, hPL hy⟩, hy, rfl⟩
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (ψ.injective h1)

end CFSG.Quasithin.H13.NQCore.Psp4
