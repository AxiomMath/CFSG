module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUModel
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5StepOne

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.Assembly
open scoped commutatorElement

variable {K : Type} [Field K] {n : ℕ}

theorem exists_cover_actsAs [Finite K] {G : Type} [Group G] [Finite G]
    (hKd : UnitaryFieldData 2 n K) (hcov : UnitaryCoverAt n 6 K) {L : Subgroup G}
    (hL : commutator L = ⊤) (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 n K 6))
    {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hBI : ∀ b ∈ B, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ φ : ↥(unitarySU 2 n K 6) →* G,
      (∀ s, φ s ∈ L) ∧ (∀ l ∈ L, ∃ s, φ s = l) ∧
      (∀ s, (∀ l ∈ L, φ s * l = l * φ s) ↔ LargeEvenProjMk (unitarySU 2 n K 6) s = 1) ∧
      (∀ (s : ↥(unitarySU 2 n K 6)) (h : φ s ∈ L),
        θ ((⟨φ s, h⟩ : ↥L) : L ⧸ Subgroup.center L) = LargeEvenProjMk (unitarySU 2 n K 6) s) ∧
      ∀ b ∈ B, ∃ M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n), ActsAs φ b M := by
  classical
  obtain ⟨hperfSU, hcov'⟩ := hcov
  set ψ : ↥L →* LargeEvenProj (unitarySU 2 n K 6) := ggQuotHom θ with hψ
  obtain ⟨φ₀, hφ₀⟩ := hcov' ↥L ψ (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL
  have hφs : Function.Surjective φ₀ := by
    have hcomm : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ φ₀.range := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      obtain ⟨s, hs⟩ : ∃ s : ↥(unitarySU 2 n K 6),
          ψ x = LargeEvenProjMk (unitarySU 2 n K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ x)
        exact ⟨s0, hs0.symm⟩
      obtain ⟨s', hs'⟩ : ∃ s : ↥(unitarySU 2 n K 6),
          ψ y = LargeEvenProjMk (unitarySU 2 n K 6) s := by
        obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ y)
        exact ⟨s0, hs0.symm⟩
      have hz : x * (φ₀ s)⁻¹ ∈ Subgroup.center ↥L := by
        rw [← ker_ggQuotHom θ, MonoidHom.mem_ker, map_mul, map_inv, ← hψ, hφ₀, ← hs,
          mul_inv_cancel]
      have hz' : y * (φ₀ s')⁻¹ ∈ Subgroup.center ↥L := by
        rw [← ker_ggQuotHom θ, MonoidHom.mem_ker, map_mul, map_inv, ← hψ, hφ₀, ← hs',
          mul_inv_cancel]
      have hx : x = (x * (φ₀ s)⁻¹) * φ₀ s := by group
      have hy : y = (y * (φ₀ s')⁻¹) * φ₀ s' := by group
      rw [hx, hy, comm_mul_central hz hz']
      exact ⟨⁅s, s'⁆, by rw [map_commutatorElement]⟩
    have htop : (⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ : Subgroup ↥L) = ⊤ := hL
    rw [htop] at hcomm
    intro l
    obtain ⟨s, hs⟩ := hcomm (Subgroup.mem_top l)
    exact ⟨s, hs⟩
  refine ⟨L.subtype.comp φ₀, fun s => (φ₀ s).2, ?_, ?_, ?_, ?_⟩
  · intro l hl
    obtain ⟨s, hs⟩ := hφs ⟨l, hl⟩
    exact ⟨s, congrArg Subtype.val hs⟩
  · intro s
    have hψs : ψ (φ₀ s) = LargeEvenProjMk (unitarySU 2 n K 6) s := hφ₀ s
    constructor
    · intro h
      rw [← hψs]
      have hc : φ₀ s ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro l
        exact Subtype.ext (h l l.2).symm
      rw [← MonoidHom.mem_ker, hψ, ker_ggQuotHom]
      exact hc
    · intro h l hl
      have hc : φ₀ s ∈ Subgroup.center ↥L := by
        rw [← ker_ggQuotHom θ, MonoidHom.mem_ker, ← hψ, hψs]
        exact h
      have := Subgroup.mem_center_iff.mp hc ⟨l, hl⟩
      exact (congrArg Subtype.val this).symm
  · intro s h
    exact hφ₀ s
  · intro b hb
    obtain ⟨A, hA, hgraph⟩ := ggLAut_mem_of_induces L θ hBN hBI hb
    have hAN : A ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
      TableBUE.gu_subset_normalizer (d := 6) hKd hA
    refine ⟨A, hA, hAN, fun s => ?_⟩
    set f₁ : ↥(unitarySU 2 n K 6) →* ↥L :=
      (L.normalizerMonoidHom ⟨b, hBN hb⟩).toMonoidHom.comp φ₀ with hf₁
    set f₂ : ↥(unitarySU 2 n K 6) →* ↥L := φ₀.comp (conjNHom A hAN) with hf₂
    have hf : f₁ = f₂ := by
      refine TypeA.eq_of_inv_mul_mem_center hperfSU f₁ f₂ fun s => ?_
      rw [← ker_ggQuotHom θ, MonoidHom.mem_ker, ← hψ, map_mul, map_inv, inv_mul_eq_one]
      have h1 : ψ (φ₀ s) = LargeEvenProjMk (unitarySU 2 n K 6) s := hφ₀ s
      have h2 : ψ (f₂ s) = LargeEvenProjMk (unitarySU 2 n K 6) (conjN A hAN s) := by
        rw [hf₂, MonoidHom.comp_apply, coe_conjNHom, hφ₀]
      have h3 : ψ (f₁ s) = ggLAut L θ ⟨b, hBN hb⟩ (LargeEvenProjMk (unitarySU 2 n K 6) s) := by
        rw [← h1, hψ, ggQuotHom_apply, ggQuotHom_apply, ggLAut_apply]
        rfl
      rw [h2, h3]
      exact (hgraph s (conjN A hAN s) rfl).symm ▸ rfl
    have h' := congrArg (fun f : ↥(unitarySU 2 n K 6) →* ↥L => ((f s : ↥L) : G)) hf
    simp only [hf₁, hf₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      normalizerMonoidHom_coe] at h'
    exact h'

theorem exists_scalar_of_proj_eq_one [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {s : ↥(unitarySU 2 n K 6)}
    (hs : LargeEvenProjMk (unitarySU 2 n K 6) s = 1) :
    ∃ z : Kˣ, z ^ 3 = 1 ∧ (s : GL (Fin 6) K) = GeneralLinearGroup.scalar (Fin 6) z := by
  have h2 : s ∈ (LargeEvenScalars (Fin 6) K).subgroupOf (unitarySU 2 n K 6) :=
    (QuotientGroup.eq_one_iff s).mp hs
  rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at h2
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp h2
  refine ⟨z, pow_three_eq_one_of_scalar_mem_unitarySU hKd hpq (hz ▸ s.2), hz.symm⟩

theorem injective_of_central_three [Finite K] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) {G : Type} [Group G] (φ : ↥(unitarySU 2 n K 6) →* G)
    (hZ : ∀ s, (∀ l ∈ φ.range, φ s * l = l * φ s) ↔
      LargeEvenProjMk (unitarySU 2 n K 6) s = 1)
    {z : G} (hzr : z ∈ φ.range) (hzc : ∀ l ∈ φ.range, z * l = l * z) (hz1 : z ≠ 1) :
    Function.Injective φ := by
  classical
  rw [injective_iff_map_eq_one]
  intro t ht
  by_contra ht1
  obtain ⟨s₀, rfl⟩ := hzr
  have ht' : LargeEvenProjMk (unitarySU 2 n K 6) t = 1 :=
    (hZ t).mp (fun l _ => by rw [ht, one_mul, mul_one])
  have hs₀' : LargeEvenProjMk (unitarySU 2 n K 6) s₀ = 1 := (hZ s₀).mp hzc
  obtain ⟨c₁, hc₁3, hc₁⟩ := exists_scalar_of_proj_eq_one hKd hpq ht'
  obtain ⟨c₀, hc₀3, hc₀⟩ := exists_scalar_of_proj_eq_one hKd hpq hs₀'
  have hc₁1 : c₁ ≠ 1 := by
    rintro rfl
    apply ht1
    apply Subtype.ext
    rw [hc₁, map_one]
    rfl
  have hc₀1 : c₀ ≠ 1 := by
    rintro rfl
    apply hz1
    have : s₀ = 1 := Subtype.ext (by rw [hc₀, map_one]; rfl)
    rw [this, map_one]
  haveI : IsCyclic (⊤ : Subgroup Kˣ) := (Subgroup.topEquiv (G := Kˣ)).isCyclic.mpr inferInstance
  have hmem : c₀ ∈ Subgroup.zpowers c₁ :=
    mem_zpowers_of_isCyclic_of_pow_three (S := (⊤ : Subgroup Kˣ)) inferInstance trivial trivial
      hc₁3 hc₁1 hc₀3
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply hz1
  have h1 : s₀ = t ^ k := by
    apply Subtype.ext
    rw [hc₀, ← hk, Subgroup.coe_zpow, hc₁, ← map_zpow]
  rw [h1, map_zpow, ht, _root_.one_zpow]

end CFSG.StandardType.Line63.H5

end
