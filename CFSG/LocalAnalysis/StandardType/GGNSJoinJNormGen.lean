module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJNormOfFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNbrGenKNOfInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanOrb
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem

namespace NSJoin

open CFSG.StandardType

theorem jnormD_of_two_reflections {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs L D J : Subgroup G} {x : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hNT : GGNoTransvection p Bs)
    (hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S)
    (hxD : x ∈ D)
    (hJ : J = CFSG.Assembly.LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)))
    (r₁ r₂ : MulAut ↥Bs)
    (h₁A : r₁ ∈ ggAutomizer L Bs) (h₂A : r₂ ∈ ggAutomizer L Bs)
    (h₁ : GGIsReflection p r₁) (h₂ : GGIsReflection p r₂) (hne : r₁ ≠ r₂) :
    ∀ c ∈ Subgroup.centralizer (D : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
  intro c hc j hj
  have hnc := s2jn_not_isCyclic_of_two_refl hp hp2 hBs hN hNT h₁A h₂A h₁ h₂ hne
  have hcx : c ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp hc) x hxD
  have hcL := s2jn_mem_normalizer_of_not_cyclic hLc hcyc hBs hnc hcx
  exact s2jn_layer_conj_mem hc hcL hJ j hj

theorem genN_of_anchor_orbit {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs X J : Subgroup G} {r₀ : MulAut ↥Bs}
    (hgen : X ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs),
        ⨆ (_ : GGIsReflection p r), ggRankOneIn X Bs r)
    (hanchor : ggRankOneIn X Bs r₀ ≤ J)
    (horbit : ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r →
      ∃ a ∈ ggAutomizer X Bs, a * r₀ * a⁻¹ = r) :
    X ≤ ⨆ (n : G) (_ : n ∈ X) (_ : ∃ φ : MulAut ↥Bs,
        n ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
        J.map (MulAut.conj n).toMonoidHom := by
  refine hgen.trans ?_
  refine iSup_le fun r => ?_
  refine iSup_le fun hrA => ?_
  refine iSup_le fun hr => ?_
  obtain ⟨a, haA, hra⟩ := horbit r hrA hr
  obtain ⟨g, hgX, hgN, hga⟩ := mem_ggAutomizer_iff.mp haA
  have hmap : (ggRankOneIn X Bs r₀).map (MulAut.conj g).toMonoidHom = ggRankOneIn X Bs r := by
    have hX : X.map (MulAut.conj g).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgX)
    rw [ggRankOneIn_map_conj hga r₀, hX, hra]
  rw [← hmap]
  refine (Subgroup.map_mono hanchor).trans ?_
  exact le_iSup_of_le g (le_iSup_of_le hgX (le_iSup_of_le ⟨a, hgN, hga⟩ le_rfl))

theorem genN_of_anchor_simple {G : Type} [Group G] [Finite G]
    {p : ℕ} {Bs X J D : Subgroup G} {r₀ : MulAut ↥Bs}
    (hgen : X ≤ ⨆ r : MulAut ↥Bs, ⨆ (_ : r ∈ ggAutomizer X Bs),
        ⨆ (_ : GGIsReflection p r), ggRankOneIn X Bs r)
    (hr₀J : r₀ ∈ ggAutomizer J Bs) (hr₀2 : r₀ ^ 2 = 1) (hr₀1 : r₀ ≠ 1) (hJX : J ≤ X)
    (hDB : D ≤ Bs) (hJD : J ≤ Subgroup.centralizer (D : Set G))
    (hDJ : ∀ c ∈ Subgroup.centralizer (D : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J)
    (hsimp : ∀ N : Subgroup G, N ≤ ggRankOneIn X Bs r₀ → N ≠ ⊥ →
      (∀ a ∈ ggRankOneIn X Bs r₀, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn X Bs r₀ ≤ N)
    (horbit : ∀ r ∈ ggAutomizer X Bs, GGIsReflection p r →
      ∃ a ∈ ggAutomizer X Bs, a * r₀ * a⁻¹ = r) :
    X ≤ ⨆ (n : G) (_ : n ∈ X) (_ : ∃ φ : MulAut ↥Bs,
        n ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = n * b * n⁻¹),
        J.map (MulAut.conj n).toMonoidHom :=
  genN_of_anchor_orbit hgen
    (s2jn_ggRankOneIn_le_of_simple hr₀J hr₀2 hr₀1 hJX hDB hJD hDJ hsimp) horbit

theorem jnormD_of_phan_gen_pair
    (hGen : GGSecFiveGenPhanInput) (hPair : GGSecFivePhanPairInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hbig : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → Nat.card (ggRankOneIn L Bs r) ≠ 6) :
    ∀ c ∈ Subgroup.centralizer (D : Set G), ∀ j ∈ J, c * j * c⁻¹ ∈ J := by
  have hC : GGConfig p B Bs x L D J := hcfg.1.1
  have hI : GGThmIHyp p B x L := hC.1
  have hβ : p ∈ LargeEvenBeta 4 G := hI.2.2.2.2.2.1
  have hp : p.Prime := (ggConfig_bstar_facts hC).1
  have hp2 : p ≠ 2 := hβ.2.1
  have hBs : IsElemAbelian p Bs := (ggConfig_bstar_facts hC).2.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hLc : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S → IsCyclic S :=
    hS.2.2.2.2
  have hxD : x ∈ D := hC.2.2.1.2.2.2.1
  have hJ : J = CFSG.Assembly.LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hC.2.2.1.2.2.2.2.1
  have hNT : GGNoTransvection p Bs := hcfg.1.2.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGInnerDiagOn.le_normalizer hcfg.1.2.2.1.1
  obtain ⟨ra, hra, rb, hrb, hraC, hrbC, hnc⟩ :=
    ggPhan_noncomm_reflections_of_gen_pair hGen hPair hcfg hns hpres hle3 hbig
  have h₁ : GGIsReflection p ra := ggCoxRefl_isReflection hpres.2 hraC
  have h₂ : GGIsReflection p rb := ggCoxRefl_isReflection hpres.2 hrbC
  have hne : ra ≠ rb := fun h => hnc (by rw [h])
  exact jnormD_of_two_reflections hp hp2 hBs hN hNT hLc hcyc hxD hJ ra rb hra hrb h₁ h₂ hne

end NSJoin

end CFSG.StandardType

