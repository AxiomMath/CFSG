module

public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Tau
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticPerfectCoverOuterPrime

public section

namespace CFSG.Quasithin.Sp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.QuasithinUnique.Lin2.Five
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBSymplecticTwo (kernel_generation)

theorem mem_iff_of_forall_mem {G : Type*} [Group G] [Finite G] (φ : MulAut G) (H : Subgroup G)
    (h : ∀ x ∈ H, φ x ∈ H) (x : G) : φ x ∈ H ↔ x ∈ H := by
  refine ⟨fun hx => ?_, h x⟩
  have hinj : Function.Injective (fun y : H => (⟨φ y, h y y.2⟩ : H)) := fun y z hyz =>
    Subtype.ext (φ.injective (congrArg Subtype.val hyz))
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinj ⟨φ x, hx⟩
  have hyx : φ y = φ x := congrArg Subtype.val hy
  rw [← φ.injective hyx]
  exact y.2

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem tauAut_mem_projUnipotent_iff (x : StatedProj (StatedSp 2 F)) :
    tauAut x ∈ projUnipotent 2 F ↔ x ∈ projUnipotent 2 F := by
  refine mem_iff_of_forall_mem tauAut (projUnipotent 2 F) ?_ x
  rintro _ ⟨u, hu, rfl⟩
  rw [tauAut_proj]
  exact ⟨tauSp u, tauSp_mem_unipotent hu, rfl⟩

theorem fieldAut_mem_projUnipotent_iff (σ : F ≃+* F) (x : StatedProj (StatedSp 2 F)) :
    fieldAut 2 F σ x ∈ projUnipotent 2 F ↔ x ∈ projUnipotent 2 F := by
  refine mem_iff_of_forall_mem (fieldAut 2 F σ) (projUnipotent 2 F) ?_ x
  rintro _ ⟨u, hu, rfl⟩
  rw [fieldAut_proj]
  exact ⟨_, fieldSp_mem_unipotent σ hu, rfl⟩

omit [Finite F] [CharP F 2] in
theorem borelSubgroup_decomp {b : StatedSp 2 F} (hb : b ∈ borelSubgroup 2 F) :
    ∃ u ∈ unipotent 2 F, ∃ s : Fin 2 → Fˣ, b = u * SymplecticTorusWeyl.torusHom s := by
  set s : Fin 2 → Fˣ := diagHom 2 F ⟨b, hb⟩ with hs
  have ht : SymplecticTorusWeyl.torusHom s ∈ borelSubgroup 2 F := torus_le_borelSubgroup ⟨s, rfl⟩
  have key : diagHom 2 F ⟨SymplecticTorusWeyl.torusHom s, ht⟩ = s := by
    funext i
    apply Units.ext
    simp [diagHom, diagEntry, SymplecticTorusWeyl.coe_torusHom]
  have hker : (⟨b, hb⟩ : borelSubgroup 2 F) * ⟨SymplecticTorusWeyl.torusHom s, ht⟩⁻¹ ∈
      (diagHom 2 F).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, key, hs, mul_inv_cancel]
  rw [ker_diagHom, Subgroup.mem_subgroupOf] at hker
  refine ⟨b * (SymplecticTorusWeyl.torusHom s)⁻¹, hker, s, by group⟩

theorem normalizer_projUnipotent_decomp {g : StatedProj (StatedSp 2 F)}
    (hg : g ∈ Subgroup.normalizer (projUnipotent 2 F : Set (StatedProj (StatedSp 2 F)))) :
    ∃ u ∈ unipotent 2 F, ∃ s : Fin 2 → Fˣ,
      g = proj 2 F (u * SymplecticTorusWeyl.torusHom s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnipotent (r := 2) (K := F) 2 (by norm_num)] at hg
  obtain ⟨b, hb, rfl⟩ := hg
  obtain ⟨u, hu, s, rfl⟩ := borelSubgroup_decomp hb
  exact ⟨u, hu, s, rfl⟩

theorem exists_standard_form {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card F = 2 ^ n)
    {α : MulAut (StatedProj (StatedSp 2 F))}
    (hα : ∀ x, α x ∈ projUnipotent 2 F ↔ x ∈ projUnipotent 2 F) :
    ∃ (σ : F ≃+* F) (u : StatedSp 2 F) (s : Fin 2 → Fˣ) (ε : Bool), u ∈ unipotent 2 F ∧
      α = MulAut.conj (proj 2 F (u * SymplecticTorusWeyl.torusHom s)) * fieldAut 2 F σ *
        (if ε then tauAut else 1) := by
  classical
  have hτE : (tauAut : MulAut (StatedProj (StatedSp 2 F))) ∉ spSemilinearAutGroup 2 F :=
    tauAut_not_mem_E
  obtain ⟨-, -, -, hEidx⟩ := kernel_generation (K := F)
  have hEne : (spSemilinearAutGroup 2 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hEne1 : (spSemilinearAutGroup 2 F).index ≠ 1 := fun h1 => hτE (by
    rw [Subgroup.index_eq_one.mp h1]
    exact Subgroup.mem_top _)
  have hE2 : (spSemilinearAutGroup 2 F).index = 2 := by omega
  have hDle : spLinearAutGroup 2 F ≤ inner (StatedProj (StatedSp 2 F)) := by
    have h := relIndex_inner_spLinearAutGroup_dvd (r := 2) (K := F) Nat.prime_two hn hK
    have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 := by
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      obtain ⟨k, hk⟩ : Even (2 ^ n) := Nat.even_pow.mpr ⟨even_two, by omega⟩
      exact Nat.coprime_two_left.mpr ⟨k - 1, by omega⟩
    rw [hgcd] at h
    exact Subgroup.relIndex_eq_one.mp (Nat.dvd_one.mp h)
  obtain ⟨γ, ε, hγ, hαγ⟩ : ∃ (γ : MulAut (StatedProj (StatedSp 2 F))) (ε : Bool),
      γ ∈ spSemilinearAutGroup 2 F ∧ α = γ * (if ε then tauAut else 1) := by
    by_cases hαE : α ∈ spSemilinearAutGroup 2 F
    · exact ⟨α, false, hαE, by simp⟩
    · refine ⟨α * tauAut⁻¹, true, ?_, by simp⟩
      exact (Subgroup.mul_mem_iff_of_index_two hE2).mpr
        ⟨fun h => absurd h hαE, fun h => absurd (inv_mem_iff.mp h) hτE⟩
  obtain ⟨A, σ, rfl⟩ := mem_spSemilinearAutGroup_iff.mp hγ
  obtain ⟨x, hx⟩ := hDle (conjAut_mem_spLinearAutGroup A)
  set ψ : MulAut (StatedProj (StatedSp 2 F)) :=
    fieldAut 2 F σ * (if ε then tauAut else 1) with hψdef
  have hψ : ∀ z, ψ z ∈ projUnipotent 2 F ↔ z ∈ projUnipotent 2 F := by
    intro z
    rw [hψdef, MulAut.mul_apply, fieldAut_mem_projUnipotent_iff]
    cases ε
    · simp
    · simp only [ite_true]
      exact tauAut_mem_projUnipotent_iff z
  have hαψ : α = MulAut.conj x * ψ := by
    rw [hαγ, hx, hψdef, mul_assoc]
  have hxN : x ∈ Subgroup.normalizer (projUnipotent 2 F :
      Set (StatedProj (StatedSp 2 F))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have h1 := hα (ψ⁻¹ w)
    have h2 := hψ (ψ⁻¹ w)
    have h3 : ψ (ψ⁻¹ w) = w := by simp
    have h4 : α (ψ⁻¹ w) = x * w * x⁻¹ := by
      rw [hαψ, MulAut.mul_apply, h3, MulAut.conj_apply]
    rw [h3] at h2
    rw [h4] at h1
    exact h2.trans h1.symm
  obtain ⟨u, hu, s, hxs⟩ := normalizer_projUnipotent_decomp hxN
  refine ⟨σ, u, s, ε, hu, ?_⟩
  rw [hαψ, hxs, hψdef, mul_assoc]

end CFSG.Quasithin.Sp4
