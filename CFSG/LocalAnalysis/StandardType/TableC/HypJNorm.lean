module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGSixCtxKnownSupply
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNormalizer

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType

private theorem mem_normalizer_inf_of_mem_normalizer {G : Type} [Group G] {A K : Subgroup G}
    {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.mp hA h) (Subgroup.mem_normalizer_iff.mp hK h)

private theorem mem_normalizer_centralizer_of_mem_centralizer {G : Type} [Group G]
    {D : Subgroup G} {g : G} (hg : g ∈ Subgroup.centralizer (D : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (D : Set G) : Set G) :=
  Subgroup.le_normalizer hg

theorem GGTCCtx.j_norm
    {t : StatedLieTag} {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (h : GGTCCtx t p B Bs x L D J n f ψ) : B ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨hD_le_B, _, _, _, hJ_layer, _, _⟩ := h.1.stdSub.1
  have hBL : B ≤ Subgroup.normalizer (L : Set G) :=
    (ggSixCtx_normalizer_and_innerDiag_on_L h.1).1
  have hB_comm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val ((h.1.sstar.1.1).1.is_comm.comm (⟨u, hu⟩ : ↥B) ⟨v, hv⟩)
  have hBC : B ≤ Subgroup.centralizer (D : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (hB_comm b hb d (hD_le_B hd)).symm
  have hBH : B ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := fun b hb =>
    mem_normalizer_inf_of_mem_normalizer (hBL hb)
      (mem_normalizer_centralizer_of_mem_centralizer (hBC hb))
  intro b hb
  have hbH : b ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := hBH hb
  have hbH' : b⁻¹ ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := hBH (B.inv_mem hb)
  have h1 : J.map (MulAut.conj b).toMonoidHom ≤ J := by
    calc J.map (MulAut.conj b).toMonoidHom
        = (LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))).map
            (MulAut.conj b).toMonoidHom := by rw [hJ_layer]
      _ ≤ LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
            map_conj_largeEvenLayer_le hbH
      _ = J := hJ_layer.symm
  have h2 : J.map (MulAut.conj b⁻¹).toMonoidHom ≤ J := by
    calc J.map (MulAut.conj b⁻¹).toMonoidHom
        = (LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))).map
            (MulAut.conj b⁻¹).toMonoidHom := by rw [hJ_layer]
      _ ≤ LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
            map_conj_largeEvenLayer_le hbH'
      _ = J := hJ_layer.symm
  rw [Subgroup.mem_normalizer_iff]
  intro j
  constructor
  · intro hj
    exact h1 (Subgroup.mem_map_of_mem (MulAut.conj b).toMonoidHom hj)
  · intro hj
    have hmem : (MulAut.conj b⁻¹) (b * j * b⁻¹) ∈ J :=
      h2 (Subgroup.mem_map_of_mem (MulAut.conj b⁻¹).toMonoidHom hj)
    have hconj : (MulAut.conj b⁻¹) (b * j * b⁻¹) = j := by
      simp only [MulAut.conj_apply, inv_inv]
      group
    rwa [hconj] at hmem

end CFSG.StandardType.TableCRes

end
