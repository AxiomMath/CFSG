module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1Defs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosHolds
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
public import CFSG.LocalAnalysis.StandardType.GGRankOneTags
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagWeyl
public import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTags
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Quasithin CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.CurtisTits

private theorem l1f_exists_sl2_range_rankOne {K : Type} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] (hM : GGRankOneModel D k) (i : Fin D.rank) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) k →* K, Function.Injective φ ∧
      φ.range = ggRootLevi D (Pi.single i 1) := by
  unfold GGRankOneModel at hM
  obtain ⟨x, C, O, hE, -⟩ := hM
  obtain ⟨φ, hφinj, hφu, hφl⟩ := hE.rankOne i
  refine ⟨φ, hφinj, ?_⟩
  apply le_antisymm
  · rintro y ⟨M, rfl⟩
    have hM' : M ∈ Subgroup.closure
        (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
          Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) := by
      rw [CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top]
      exact Subgroup.mem_top M
    have hs : (Set.range (sl2Upper : k → Matrix.SpecialLinearGroup (Fin 2) k) ∪
        Set.range (sl2Lower : k → Matrix.SpecialLinearGroup (Fin 2) k)) ⊆
        (D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ := by
      rintro x (hx | hx)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Upper c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφu c]
        exact Subgroup.mem_sup_left
          (((hE.param (Pi.single i 1) (single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
      · obtain ⟨c, rfl⟩ := hx
        change φ (sl2Lower c) ∈
          D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)
        rw [hφl c]
        exact Subgroup.mem_sup_right
          (((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 _).mpr ⟨c, rfl⟩)
    exact Subgroup.mem_comap.mp
      (Subgroup.mem_closure.mp hM'
        ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1)).comap φ) hs)
  · change D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-Pi.single i 1) ≤ φ.range
    apply sup_le
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (Pi.single i 1) (single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Upper c, by rw [hφu c, hc]⟩
    · intro z hz
      obtain ⟨c, hc⟩ := ((hE.param (-Pi.single i 1) (neg_single_mem_roots i)).1 z).mp hz
      exact ⟨sl2Lower c, by rw [hφl c, hc]⟩

private theorem l1f_rootLevi_perfect {K : Type} [Group K] {D : UniversalRootDatum K}
    {k : Type*} [Field k] [Finite k] (hM : GGRankOneModel D k) (i : Fin D.rank)
    (h4 : 4 ≤ Nat.card k) :
    ⁅ggRootLevi D (Pi.single i 1), ggRootLevi D (Pi.single i 1)⁆ =
      ggRootLevi D (Pi.single i 1) := by
  obtain ⟨φ, hφinj, hφrange⟩ := l1f_exists_sl2_range_rankOne hM i
  haveI : Fintype k := Fintype.ofFinite k
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset k)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) k) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect (K := k) ⟨s, hs⟩
  have hsurj : Function.Surjective φ.rangeRestrict := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hperfR : Group.IsPerfect ↥(φ.range) :=
    Group.IsPerfect.ofSurjective (f := φ.rangeRestrict) hsurj
  rw [← hφrange]
  exact Subgroup.isPerfect_iff.1 hperfR

private lemma l1f_rootGroup_map_conj_weylLift {K G : Type} [Group K] [Group G]
    (D : UniversalRootDatum K) (ν : GGWeyl D →* K)
    (hν : GGWeylLift D ν) (ψ : K →* G) (u : GGWeyl D) (γ : Fin D.rank → ℤ)
    (hγ : γ ∈ D.roots) :
    (D.rootGroup (weylAction D.isFiniteType u γ)).map ψ =
      (D.rootGroup γ).map ((MulAut.conj (ψ (ν u))).toMonoidHom.comp ψ) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨(ν u)⁻¹ * y * ν u, ?_, ?_⟩
    · have h := hν.conj_mem (u⁻¹) (weylAction D.isFiniteType u γ)
        (weylAction_mem_roots D.isFiniteType u hγ) y hy
      rw [map_inv ν u, inv_inv, weylAction_inv_apply_apply] at h
      exact h
    · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
        map_inv]
      group
  · rintro x ⟨z, hz, rfl⟩
    refine ⟨ν u * z * (ν u)⁻¹, hν.conj_mem u γ hγ z hz, ?_⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

private lemma l1f_ggRootLevi_map_conj_weylLift {K G : Type} [Group K] [Group G]
    (D : UniversalRootDatum K) (ν : GGWeyl D →* K)
    (hν : GGWeylLift D ν) (ψ : K →* G) (u : GGWeyl D) (i : Fin D.rank) :
    (ggRootLevi D (weylAction D.isFiniteType u (Pi.single i 1))).map ψ =
      ((ggRootLevi D (Pi.single i 1 : Fin D.rank → ℤ)).map ψ).map
        (MulAut.conj (ψ (ν u))).toMonoidHom := by
  have hsingle : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (isCTRootSystem D.isFiniteType D.divisible).single_mem i
  have h1 := l1f_rootGroup_map_conj_weylLift D ν hν ψ u (Pi.single i 1) hsingle
  have hsingle' : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hsingle
  have h2 := l1f_rootGroup_map_conj_weylLift D ν hν ψ u (-(Pi.single i 1)) hsingle'
  change (D.rootGroup (weylAction D.isFiniteType u (Pi.single i 1)) ⊔
      D.rootGroup (-(weylAction D.isFiniteType u (Pi.single i 1)))).map ψ =
    ((D.rootGroup (Pi.single i 1) ⊔ D.rootGroup (-(Pi.single i 1))).map ψ).map
      (MulAut.conj (ψ (ν u))).toMonoidHom
  rw [← map_neg (weylAction D.isFiniteType u) (Pi.single i 1)]
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map,
    h1, h2]

theorem ggSecFiveRankOneInPerfInput_holds :
    GGSecFiveRankOneInPerfInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs r hrA hrC
  obtain ⟨t, n, f, ψ, hadm, h3, hker, hrange, htag, hpf, hpos⟩ :=
    ggSecFiveKGPosInput_holds G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs
  obtain ⟨ε, hεrefl, hεlevi, -⟩ := hpos
  have hW : GGIsWeylMatrix (coxeterMatrix (ggU t n f).D.isFiniteType) :=
    (ggTag_weylMatrix htag hadm).1
  have h3ψ : ∀ i j : Fin (ggU t n f).D.rank, i ≠ j →
      (coxeterMatrix (ggU t n f).D.isFiniteType).M i j ≤ 3 :=
    (ggTag_weylMatrix htag hadm).2
  have hpresψ : GGCoxeterPres p (ggAutomizer X Bs)
      (coxeterMatrix (ggU t n f).D.isFiniteType) ε := ⟨hW, hεrefl⟩
  have hrefl : GGIsReflection p r := ggCoxRefl_isReflection hpres.2 hrC
  have hrCox : r ∈ ggCoxRefl (coxeterMatrix (ggU t n f).D.isFiniteType) ε :=
    ggCoxRefl_of_cfg hcfg (ggAutomizer_le_top X Bs) hpresψ h3ψ hrA hrefl
  obtain ⟨w, i, hw⟩ := hrCox
  have hlevi : ggRankOneIn X Bs r =
      (ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))).map ψ := by
    rw [hw]
    exact hεlevi w i
  have hperf_levi : ⁅ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)),
      ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1))⁆ =
      ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) := by
    obtain ⟨ν, hν⟩ := (ggTagFacts_of_admissible hadm h3).2.1
    have hconj := l1f_ggRootLevi_map_conj_weylLift (ggU t n f).D ν hν
      (MonoidHom.id (ggU t n f).K) w i
    have hγ_eq : ggRootLevi (ggU t n f).D
        (weylAction (ggU t n f).D.isFiniteType w (Pi.single i 1)) =
        (ggRootLevi (ggU t n f).D (Pi.single i 1)).map
          (MulAut.conj (ν w)).toMonoidHom := by
      simpa using hconj
    rw [hγ_eq]
    have hM : GGRankOneModel (ggU t n f).D (GaloisField 2 f) :=
      ggRankOneModel_of_tag htag hadm h3
    have h4 : 4 ≤ Nat.card (GaloisField 2 f) := by
      have hf : 1 ≤ f := hadm.2.1
      have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
        GaloisField.card 2 f (by omega)
      have hp : p.Prime := (ggRouteCfg_prime hcfg).1
      have hp2 : p ≠ 2 := (ggRouteCfg_prime hcfg).2
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have h2f : 4 ≤ 2 ^ f := by
        have h2fpos : 0 < 2 ^ f - 1 := by
          have h2 : 2 ≤ 2 ^ f := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
          omega
        have hle : p ≤ 2 ^ f - 1 := Nat.le_of_dvd h2fpos hpf
        omega
      omega
    have hsimp : ⁅ggRootLevi (ggU t n f).D (Pi.single i 1),
        ggRootLevi (ggU t n f).D (Pi.single i 1)⁆ =
        ggRootLevi (ggU t n f).D (Pi.single i 1) :=
      l1f_rootLevi_perfect hM i h4
    rw [← Subgroup.map_commutator, hsimp]
  rw [hlevi, ← Subgroup.map_commutator, hperf_levi]

end CFSG.StandardType

end
