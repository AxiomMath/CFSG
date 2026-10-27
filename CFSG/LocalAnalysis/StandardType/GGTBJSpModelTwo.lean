module

public import CFSG.LocalAnalysis.StandardType.GGTBJSpModel
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBSymp

theorem ggTBJ_sp_torus_normalizes_two {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m]
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1)
    {L' : Type} [Group L'] [Finite L']
    (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (A : Subgroup (MulAut L'))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) L' ψ A) :
    ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ ∀ a ∈ A, ∀ u ∈ U, a u ∈ U := by
  classical
  obtain ⟨ζ, hζ, x, σ, Θ, _hζo, hψσ, hΘ, _hW⟩ :=
    ggTBJ_sp_stdModel hp hp2 hpq ψ A hA
  let i₀ : Fin m := ⟨0, Nat.pos_of_ne_zero (NeZero.ne m)⟩
  let U₀ : Subgroup (LargeEvenProj (LargeEvenSpGroup K m)) :=
    (spRootGroup (K := K) i₀).map (MulAut.conj x).toMonoidHom
  have hU₀ : U₀ ≠ ⊥ := by
    intro h
    apply spRootGroup_ne_bot (K := K) i₀
    apply Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective
    simpa only [Subgroup.map_bot] using h
  have hU₀2 : IsPGroup 2 U₀ := (spRootGroup_isPGroup (K := K) i₀).map _
  have hEU : ∀ e ∈ σ.range, ∀ u ∈ U₀, ψ e * u * (ψ e)⁻¹ ∈ U₀ := by
    rintro e ⟨f, rfl⟩ u ⟨u₀, hu₀, rfl⟩
    refine Subgroup.mem_map.mpr ⟨spTorus hζ f * u₀ * (spTorus hζ f)⁻¹,
      spTorus_conj_spRootGroup hζ i₀ f hu₀, ?_⟩
    rw [hψσ f]
    change x * (spTorus hζ f * u₀ * (spTorus hζ f)⁻¹) * x⁻¹ =
      (x * spTorus hζ f * x⁻¹) * (x * u₀ * x⁻¹) * (x * spTorus hζ f * x⁻¹)⁻¹
    group
  obtain ⟨U, hU, hU2, hEN⟩ := exists_twoSubgroup_lift hA.1 hA.2.1 hU₀ hU₀2 hEU
  refine ⟨U, hU, hU2, ?_⟩
  intro a ha u hu
  obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
  have haσ : a = MulAut.conj (σ f) := by
    have h := hΘ f
    rw [hf] at h
    exact h
  rw [haσ, MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.mp (hEN ⟨f, rfl⟩) u).mp hu

theorem GGConfig.bstar_eq_of_gamma_invariant_two
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (X : Subgroup G) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (U : Subgroup X) (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    (hInv : ∀ a ∈ (ggGamma X hN).range, ∀ u ∈ U, a u ∈ U) : Bs = B := by
  classical
  obtain ⟨hp, hBs, _hx, _hLx, _hcard⟩ := hcfg.tableB_facts
  let T : Subgroup G := U.map X.subtype
  have hT : T ≠ ⊥ := by
    intro h
    apply hU
    apply Subgroup.map_injective (f := X.subtype) X.subtype_injective
    simpa only [Subgroup.map_bot] using h
  have hT2 : IsPGroup 2 T := hU2.map X.subtype
  have hBsT : Bs ≤ Subgroup.normalizer (T : Set G) := by
    intro b hb
    refine mem_normalizer_of_forall_conj_mem fun t ht => ?_
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp ht
    let b' : Bs := ⟨b⁻¹, Bs.inv_mem hb⟩
    let a : MulAut X := ggGamma X hN b'
    have ha : a ∈ (ggGamma X hN).range := ⟨b', rfl⟩
    refine Subgroup.mem_map.mpr ⟨a u, hInv a ha u hu, ?_⟩
    change ((ggGamma X hN b' u : X) : G) = b⁻¹ * (u : G) * b
    simp only [ggGamma_coe, b', inv_inv]
  have hCard := TableB.card_le_of_twoLocal hp ⟨T, hT, hT2, rfl⟩ hBsT hBs
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hS.1.2.1
  rw [← hBcard] at hCard
  exact (Subgroup.eq_of_le_of_card_ge hcfg.2.1.1 hCard).symm

theorem ggTBJ_sp_bstar_eq {G : Type} [Group G] [Finite G] {p m : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) [NeZero m] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (X : Subgroup G) (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K - 1)
    (ψ : X →* LargeEvenProj (LargeEvenSpGroup K m))
    (hA : GGTorusTBGroup p m (LargeEvenProj (LargeEvenSpGroup K m))
      (Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
        MulAut (LargeEvenProj (LargeEvenSpGroup K m)))) X ψ (ggGamma X hN).range) :
    Bs = B := by
  obtain ⟨U, hU, hU2, hInv⟩ := ggTBJ_sp_torus_normalizes_two hp hp2 hpq ψ _ hA
  exact hcfg.bstar_eq_of_gamma_invariant_two X hN U hU hU2 hInv

end CFSG.StandardType
