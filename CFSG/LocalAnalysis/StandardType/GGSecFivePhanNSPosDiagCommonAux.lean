module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRank
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosCommRank
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDiagAux
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal CFSG.ClassicalInvolution.Phan
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.Unitary

open scoped MatrixGroups

private theorem ggNSPosPE_one_le_f {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ f + 1) : 1 ≤ f := by
  by_contra hf
  have hf0 : f = 0 := by omega
  have hp_dvd_two : p ∣ 2 := by simpa [hf0] using hdvd
  have hp_eq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hp_dvd_two
  exact hp2 hp_eq

private theorem ggNSPosPE_unitaryFieldData {K : Type} [Field K] {f : ℕ} (hcard : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    UnitaryFieldData 2 f K :=
  ⟨Nat.prime_two, hf, by rw [hcard, ← pow_mul, mul_comm f 2]⟩

private theorem ggNSPosPE_su_eq_unitarySU {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} (hcard : Nat.card K = (2 ^ f) ^ 2) :
    SUid (unitaryInvolution K 2 f) n = unitarySU (p := 2) (f := f) K n :=
  SUid_eq_statedSU hcard n

private theorem ggNSPosPE_isPerfect_su {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} (hcard : Nat.card K = (2 ^ f) ^ 2) (hn : 4 ≤ n) :
    Group.IsPerfect (Su K 2 f n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ : IsUnitaryInvolution (unitaryInvolution K 2 f) :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := f) hcard
  exact isPerfect_SUid hσ (by omega) (fun h3 => by omega)

private theorem ggNSPosPE_induces_mul {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} {b₁ b₂ : G} {g₁ g₂ : GL (Fin n) K}
    (h₁ : GGInducesUnitary (p := 2) (f := f) ψ b₁ g₁)
    (h₂ : GGInducesUnitary (p := 2) (f := f) ψ b₂ g₂) :
    GGInducesUnitary (p := 2) (f := f) ψ (b₁ * b₂) (g₁ * g₂) := by
  obtain ⟨hu₁, ha₁⟩ := h₁
  obtain ⟨hu₂, ha₂⟩ := h₂
  refine ⟨ggNSPosPE_isUnitaryMat_mul hu₁ hu₂, ?_⟩
  intro x
  obtain ⟨y₂, hy₂eq, hy₂act⟩ := ha₂ x
  obtain ⟨y₁, hy₁eq, hy₁act⟩ := ha₁ y₂
  refine ⟨y₁, ?_, ?_⟩
  · rw [hy₁eq, hy₂eq]
    group
  · calc b₁ * b₂ * ψ x * (b₁ * b₂)⁻¹
        = b₁ * (b₂ * ψ x * b₂⁻¹) * b₁⁻¹ := by group
      _ = b₁ * ψ y₂ * b₁⁻¹ := by rw [hy₂act]
      _ = ψ y₁ := hy₁act

private theorem ggNSPosPE_induces_pow {G : Type} [Group G] {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} {b : G} {g : GL (Fin n) K}
    (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) (k : ℕ) :
    GGInducesUnitary (p := 2) (f := f) ψ (b ^ k) (g ^ k) := by
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · unfold ggIsUnitaryMat
        rw [pow_zero, Units.val_one, conjTr_one, Matrix.one_mul]
      · intro x
        exact ⟨x, by simp, by simp⟩
  | succ k ih =>
      have h := ggNSPosPE_induces_mul ih hg
      simpa only [pow_succ] using h

private theorem ggNSPosPE_scalar_of_induces_one {G : Type} [Group G] {p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ 2 ^ f + 1) (hn : 4 ≤ n)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n)) {N : GL (Fin n) K}
    (hN : GGInducesUnitary (p := 2) (f := f) ψ 1 N) :
    ∃ u : Kˣ, N = GeneralLinearGroup.scalar (Fin n) u := by
  classical
  have hf : 1 ≤ f := ggNSPosPE_one_le_f hp hp2 hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdata : UnitaryFieldData 2 f K := ggNSPosPE_unitaryFieldData hcard hf
  have hperf : Group.IsPerfect (Su K 2 f n) := ggNSPosPE_isPerfect_su hcard hn
  let τ : Su K 2 f n →* Su K 2 f n :=
    { toFun := fun x =>
        ⟨N * (x : GL (Fin n) K) * N⁻¹, by
          obtain ⟨y, hy, -⟩ := hN.2 x
          rw [← hy]
          exact y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have hτ : ∀ x, τ x = x :=
    CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hker hperf τ (MonoidHom.id _) (fun x => by
      obtain ⟨y, hy, hψ⟩ := hN.2 x
      have hxy : τ x = y := Subtype.ext hy.symm
      rw [hxy]
      simpa using hψ.symm)
  have hcomm : ∀ x : Su K 2 f n,
      N * (x : GL (Fin n) K) = (x : GL (Fin n) K) * N := by
    intro x
    have h1 : (τ x : GL (Fin n) K) = (x : GL (Fin n) K) := congrArg Subtype.val (hτ x)
    have h2 : (τ x : GL (Fin n) K) = N * (x : GL (Fin n) K) * N⁻¹ := rfl
    rw [h2] at h1
    calc N * (x : GL (Fin n) K)
        = (N * (x : GL (Fin n) K) * N⁻¹) * N := by group
      _ = (x : GL (Fin n) K) * N := by rw [h1]
  have hNu : ∀ g' ∈ unitarySU (p := 2) (f := f) K n, N * g' = g' * N := by
    intro g' hg'
    have hg'' : g' ∈ SUid (unitaryInvolution K 2 f) n := by
      rw [ggNSPosPE_su_eq_unitarySU hcard]
      exact hg'
    exact hcomm ⟨g', hg''⟩
  obtain ⟨u, hu⟩ := TableBUE.mem_scalars_of_commute hdata hp hdvd hNu
  exact ⟨u, hu.symm⟩

theorem ggNSPosPE_lift_pow_scalar_aux {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) {b : G} (hb : b ∈ Bs)
    {g : GL (Fin n) K} (hg : GGInducesUnitary (p := 2) (f := f) ψ b g) :
    ∃ u : Kˣ, g ^ p = GeneralLinearGroup.scalar (Fin n) u := by
  have hbp : b ^ p = 1 := h.bstar.2.1.2 b hb
  have hgp : GGInducesUnitary (p := 2) (f := f) ψ 1 (g ^ p) := by
    have hh := ggNSPosPE_induces_pow (ψ := ψ) hg p
    rwa [hbp] at hh
  exact ggNSPosPE_scalar_of_induces_one h.card h.prime h.odd h.dvd h.four_le h.ker hgp

end CFSG.StandardType

end
