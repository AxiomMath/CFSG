module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsFactors
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGClSp

public section

namespace CFSG.StandardType

namespace LayerExcThree

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix LayerCores LayerFacts

theorem ggNotExcThree_of_isComponentOf_sp {G : Type*} [Group G] [Finite G] {n : ℕ} {F : Type}
    [Field F] [Finite F] [CharP F 2] (hF : 4 ≤ Nat.card F) {ψ : StatedSp n F →* G}
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n F)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : G} (hx : x ^ p = 1) {s : StatedSp n F} (hs : (x, s) ∈ ggConjPairs ψ)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x})) :
    GGNotExcThreeOrder (ggCQ K) := by
  classical
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans (CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := F) n).le
  have hZ1 : ∀ g : StatedSp n F, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot, Subgroup.mem_bot] at h
  have hsp : s ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem hs p
    rwa [Prod.pow_mk, hx] at h)
  have hAu : (s : GL (Fin n ⊕ Fin n) F) ∈ unitaryOf (isInvol_spAdj (n := n) (F := F)) :=
    mem_unitaryOf_spAdj_iff.mpr s.2
  have hAp : (s : GL (Fin n ⊕ Fin n) F) ^ p = 1 := by
    rw [← Subgroup.coe_pow, hsp, Subgroup.coe_one]
  have hcard := ClNonsplit.natCast_card_zpowers_ne_zero hp hp2 hAp
  obtain ⟨Y, hY1, hY2⟩ := exists_symd_spAdj (A := Subgroup.zpowers (s : GL (Fin n ⊕ Fin n) F))
    (fun g hg => Subgroup.zpowers_le.mpr s.2 hg) hcard
  obtain ⟨β, S, hS, hgood⟩ := exists_coreFamily_adjCent_excThree hcard
    (isInvol_spAdj (n := n) (F := F)) (ClNonsplit.adj_stab_zpowers _ hAu) ⟨Y, hY1, hY2⟩ hF
    (Or.inr fun c X => spAdj_smul c X)
  have hle : adjCent (Subgroup.zpowers (s : GL (Fin n ⊕ Fin n) F))
      (isInvol_spAdj (n := n) (F := F)) ≤ (StatedSp n F).subtype.range := fun g hg =>
    ⟨⟨g, mem_unitaryOf_spAdj_iff.mp (Subgroup.mem_inf.mp hg).2⟩, rfl⟩
  have hS' := hS.comap (StatedSp n F).subtype (Subgroup.subtype_injective _) hle
  rw [ClNonsplit.comap_adjCent_sp s] at hS'
  rw [ClNonsplit.range_inf_centralizer_eq hinj hs] at hK
  obtain ⟨c, rfl⟩ := LayerPDiv.exists_eq_map_of_isComponentOf ψ hker le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) (ggCommutator_self_le _) _ hS'.1 hS'.2.1
    hS'.2.2.1 hS'.2.2.2.1 hK
  rw [ggCQ_map_of_injective ψ hinj,
    ggCQ_comap_of_injective _ (Subgroup.subtype_injective _) ((hS.1 c).trans hle)]
  exact hgood c

end LayerExcThree

section Tag

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

theorem ggAKFG_excThree_PSp {G : Type} [Group G] [Finite G] {n f : ℕ}
    {ψ : (ggU .PSp n f).K →* G} {G₀ : Subgroup G}
    (hpres : GGPresentsG0 G₀ (ggU .PSp n f).D .PSp n f ψ) (hf : 2 ≤ f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {y : G} (hy : y ^ p = 1) (hdiag : GGPsiInnerDiag (ggU .PSp n f).D ψ y)
    {C : Subgroup G} (hC : IsComponentOf C (G₀ ⊓ Subgroup.centralizer {y})) :
    GGNotExcThreeOrder (ggCQ C) := by
  obtain ⟨⟨-, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  rw [← hrange] at hC
  obtain ⟨s, hs⟩ := LayerPDiv.exists_mem_ggConjPairs_sp (F := GaloisField 2 f) hrk ψ hker hdiag
  have hF : 4 ≤ Nat.card (GaloisField 2 f) := by
    rw [GaloisField.card 2 f (by omega)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact LayerExcThree.ggNotExcThree_of_isComponentOf_sp hF hker hp hp2 hy hs hC

theorem ggLayerNotDFourTwoTag_PSp : GGLayerNotDFourTwoTag .PSp := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  exact (ggAKFG_not_excThree (ggAKFG_excThree_PSp hpres hf hp hp2 hy hdiag hC)).1

theorem ggLayerNotUFourAltSixTag_PSp : GGLayerNotUFourAltSixTag .PSp := by
  intro G _ _ n f ψ G₀ hpres hf p hp hp2 y hy _ hdiag C hC
  exact (ggAKFG_not_excThree (ggAKFG_excThree_PSp hpres hf hp hp2 hy hdiag hC)).2

end Tag

end CFSG.StandardType
