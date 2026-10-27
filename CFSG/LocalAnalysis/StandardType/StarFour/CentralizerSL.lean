module

public import CFSG.LocalAnalysis.StandardType.StarFour.CentralizerSLDecomp
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.StandardType.GGSixLayerPDivBasic
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsPiGL

public section

namespace CFSG.StandardType.StarFour

open CFSG.Assembly

variable {F : Type} [Field F] {P : Type} [CommGroup P] {V : Type} [AddCommGroup V]
  [Module F V]

variable {ρ : P →* (V ≃ₗ[F] V)}

namespace SemiFrame

variable (fr : SemiFrame F ρ)

private theorem blockLin_blockSpecialLinear_self (b : Fin fr.r)
    (B : SpecialLinearGroup (fr.E b) (Fin (fr.m b) → fr.E b))
    (hC : blockSpecialLinear fr b B ∈ repCentSL ρ) :
    blockLin fr ⟨blockSpecialLinear fr b B, hC⟩ b =
      (B : (Fin (fr.m b) → fr.E b) →ₗ[fr.E b] (Fin (fr.m b) → fr.E b)) := by
  symm
  apply blockLin_unique
  intro v
  have := congrFun (blockSpecialLinear_apply fr b B v) b
  simpa [Function.update_self] using this

private theorem blockLin_blockSpecialLinear_ne (b j : Fin fr.r) (hj : j ≠ b)
    (B : SpecialLinearGroup (fr.E b) (Fin (fr.m b) → fr.E b))
    (hC : blockSpecialLinear fr b B ∈ repCentSL ρ) :
    blockLin fr ⟨blockSpecialLinear fr b B, hC⟩ j = LinearMap.id := by
  symm
  apply blockLin_unique
  intro v
  have := congrFun (blockSpecialLinear_apply fr b B v) j
  simpa [Function.update_of_ne hj] using this

private theorem blockEquiv_blockSpecialLinear_self (b : Fin fr.r)
    (B : SpecialLinearGroup (fr.E b) (Fin (fr.m b) → fr.E b))
    (hC : blockSpecialLinear fr b B ∈ repCentSL ρ) :
    blockEquiv fr ⟨blockSpecialLinear fr b B, hC⟩ b = B := by
  apply LinearEquiv.ext
  intro z
  change blockLin fr ⟨blockSpecialLinear fr b B, hC⟩ b z = B z
  rw [blockLin_blockSpecialLinear_self fr b B hC]
  rfl

private theorem blockEquiv_blockSpecialLinear_ne (b j : Fin fr.r) (hj : j ≠ b)
    (B : SpecialLinearGroup (fr.E b) (Fin (fr.m b) → fr.E b))
    (hC : blockSpecialLinear fr b B ∈ repCentSL ρ) :
    blockEquiv fr ⟨blockSpecialLinear fr b B, hC⟩ j = 1 := by
  apply LinearEquiv.ext
  intro z
  change blockLin fr ⟨blockSpecialLinear fr b B, hC⟩ j z = z
  rw [blockLin_blockSpecialLinear_ne fr b j hj B hC]
  rfl

private theorem subgroupOf_iSup_eq {β : Type*}
    (S : β → Subgroup (SpecialLinearGroup F V)) (hS : ∀ b, S b ≤ repCentSL ρ) :
    (⨆ b, S b).subgroupOf (repCentSL ρ) = ⨆ b, (S b).subgroupOf (repCentSL ρ) := by
  refine le_antisymm ?_ ?_
  · apply (Subgroup.map_le_map_iff_of_injective (repCentSL ρ).subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le (iSup_le hS), Subgroup.map_iSup]
    simp_rw [Subgroup.map_subgroupOf_eq_of_le (hS _)]
    exact le_rfl
  · apply (Subgroup.map_le_map_iff_of_injective (repCentSL ρ).subtype_injective).mp
    rw [Subgroup.map_iSup, Subgroup.map_subgroupOf_eq_of_le (iSup_le hS)]
    simp_rw [Subgroup.map_subgroupOf_eq_of_le (hS _)]
    exact le_rfl

private theorem ggDer_le (H : Subgroup (SpecialLinearGroup F V)) (k : ℕ) :
    LayerFacts.ggDer H k ≤ H := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      rw [LayerFacts.ggDer_succ]
      exact (LayerFacts.ggCommutator_self_le (LayerFacts.ggDer H k)).trans ih

private theorem ggDer_subgroupOf_eq (H : Subgroup (SpecialLinearGroup F V)) (k : ℕ) :
    (LayerFacts.ggDer H k).subgroupOf H = LayerFacts.ggDer (⊤ : Subgroup H) k := by
  have h1 : LayerFacts.ggDer H k = (LayerFacts.ggDer (⊤ : Subgroup H) k).map H.subtype := by
    rw [LayerFacts.map_ggDer H.subtype ⊤ k, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [h1]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

private theorem le_of_subgroupOf_le_subgroupOf
    {H K : Subgroup (SpecialLinearGroup F V)} (hH : H ≤ repCentSL ρ)
    (h : H.subgroupOf (repCentSL ρ) ≤ K.subgroupOf (repCentSL ρ)) : H ≤ K := by
  intro x hx
  have h1 : (⟨x, hH hx⟩ : repCentSL ρ) ∈ K.subgroupOf (repCentSL ρ) :=
    h (show (⟨x, hH hx⟩ : repCentSL ρ) ∈ H.subgroupOf (repCentSL ρ) from hx)
  exact Subgroup.mem_subgroupOf.mp h1

private theorem blockPiGL_injective : Function.Injective (blockPiGL fr) := by
  intro h₁ h₂ h
  apply Subtype.ext
  apply SpecialLinearGroup.ext
  intro v
  apply fr.Φ.injective
  funext j
  have h1 : blockEquiv fr h₁ j = blockEquiv fr h₂ j := by
    exact linEquivToGL.injective (congrFun h j)
  have h2 : blockLin fr h₁ j = blockLin fr h₂ j := by
    rw [show blockLin fr h₁ j = (blockEquiv fr h₁ j).toLinearMap from rfl,
      show blockLin fr h₂ j = (blockEquiv fr h₂ j).toLinearMap from rfl, h1]
  calc fr.Φ ((h₁ : V ≃ₗ[F] V) v) j = blockLin fr h₁ j (fr.Φ v j) := blockLin_spec fr h₁ j v
    _ = blockLin fr h₂ j (fr.Φ v j) := by rw [h2]
    _ = fr.Φ ((h₂ : V ≃ₗ[F] V) v) j := (blockLin_spec fr h₂ j v).symm

end SemiFrame

theorem SemiFrame.slOnBlock_le_repCentSL (fr : SemiFrame F ρ) (i : Fin fr.r) :
    fr.slOnBlock i ≤ repCentSL ρ := by
  intro g hg
  obtain ⟨B, hB⟩ := hg
  rw [repCentSL, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
  intro h hh
  obtain ⟨p, rfl⟩ := hh
  refine (((fr.comm (g : V ≃ₗ[F] V)).mpr fun j => ?_) p).symm
  by_cases hj : j = i
  · rw [hj]
    refine ⟨(B : (Fin (fr.m i) → fr.E i) →ₗ[fr.E i] (Fin (fr.m i) → fr.E i)),
      fun v => ?_⟩
    rw [hB v, Function.update_self]
    rfl
  · exact ⟨LinearMap.id, fun v => by rw [hB v, Function.update_of_ne hj, LinearMap.id_apply]⟩


namespace SemiFrame

variable (fr : SemiFrame F ρ)

private theorem map_slOnBlock_subgroupOf_eq_blockSL (b : Fin fr.r) :
    ((fr.slOnBlock b).subgroupOf (repCentSL ρ)).map (blockPiGL fr) =
      CFSG.RankThree.PartOne.KCLinComm.blockSL fr.E fr.m b := by
  apply le_antisymm
  · rintro w ⟨x, hx, rfl⟩
    exact (mem_slOnBlock_iff_mem_comap fr x b).mp (Subgroup.mem_subgroupOf.mp hx)
  · intro w hw
    obtain ⟨s, rfl⟩ := hw
    let B := Matrix.SpecialLinearGroup.toLin'_equiv s
    let hB : blockSpecialLinear fr b B ∈ fr.slOnBlock b :=
      ⟨B, blockSpecialLinear_apply fr b B⟩
    let hC : blockSpecialLinear fr b B ∈ repCentSL ρ := slOnBlock_le_repCentSL fr b hB
    refine ⟨⟨blockSpecialLinear fr b B, hC⟩, ?_, ?_⟩
    · exact hB
    · funext j
      by_cases hj : j = b
      · rw [hj]
        rw [CFSG.RankThree.PartOne.KCLinComm.blockEmbed_apply_self]
        show linEquivToGL (blockEquiv fr ⟨blockSpecialLinear fr b B, hC⟩ b) =
          Matrix.SpecialLinearGroup.toGL s
        rw [show blockEquiv fr ⟨blockSpecialLinear fr b B, hC⟩ b = B from
          blockEquiv_blockSpecialLinear_self fr b B hC]
        exact linEquivToGL_toLin' s
      · rw [CFSG.RankThree.PartOne.KCLinComm.blockEmbed_apply_of_ne hj]
        show linEquivToGL (blockEquiv fr ⟨blockSpecialLinear fr b B, hC⟩ j) = 1
        rw [show blockEquiv fr ⟨blockSpecialLinear fr b B, hC⟩ j = 1 from
          blockEquiv_blockSpecialLinear_ne fr b j hj B hC]
        exact map_one _

end SemiFrame
private theorem isQuasisimple_slOnBlock_native [Finite F] (fr : SemiFrame F ρ) (i : Fin fr.r)
    (hm : 2 ≤ fr.m i) (hE : 3 ≤ fr.m i ∨ ∃ s : Finset (fr.E i), s.card = 4) :
    CFSG.IsQuasisimple (fr.slOnBlock i) :=
  CFSG.LocalCores.isQuasisimple_of_mulEquiv (SemiFrame.blockMulEquiv fr i)
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Matrix.SpecialLinearGroup.toLin'_equiv (n := Fin (fr.m i)) (R := fr.E i))
      (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_SL hm hE))

theorem SemiFrame.isQuasisimple_slOnBlock [Finite F] (fr : SemiFrame F ρ) {i : Fin fr.r}
    (hi : fr.GoodAtBlock i) : IsQuasisimple (fr.slOnBlock i) := by
  classical
  obtain ⟨hm2, hm3 | h4⟩ := hi
  · exact isQuasisimple_slOnBlock_native fr i hm2 (Or.inl hm3)
  · haveI : Fintype (fr.E i) := Fintype.ofFinite _
    obtain ⟨s, -, hs⟩ :=
      Finset.exists_subset_card_eq (s := (Finset.univ : Finset (fr.E i))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; exact h4)
    exact isQuasisimple_slOnBlock_native fr i hm2 (Or.inr ⟨s, hs⟩)

theorem SemiFrame.exists_eq_slOnBlock_of_isComponentOf [Finite F] [CharP F 2] [Module.Finite F V]
    (fr : SemiFrame F ρ) {K : Subgroup (SpecialLinearGroup F V)}
    (hK : IsComponentOf K (repCentSL ρ)) : ∃ i, fr.GoodAtBlock i ∧ K = fr.slOnBlock i := by
  classical
  haveI : Finite V :=
    Finite.of_injective ((Module.finBasis F V).equivFun : V → (Fin (Module.finrank F V) → F))
      (Module.finBasis F V).equivFun.injective
  haveI : Finite (SpecialLinearGroup F V) :=
    Finite.of_injective (fun u : SpecialLinearGroup F V => (u : V → V))
      (fun u v h => by ext x; exact congrFun h x)
  haveI : ∀ b, CharP (fr.E b) 2 := fun b =>
    charP_of_injective_algebraMap (algebraMap F (fr.E b)).injective 2
  let β := {i : Fin fr.r // LayerFacts.GoodBlock fr.E fr.m i}
  have hSC : ∀ b : β, fr.slOnBlock b.1 ≤ repCentSL ρ := fun b => fr.slOnBlock_le_repCentSL b.1
  have hC₀H : (repCentSL ρ).map (MonoidHom.id (SpecialLinearGroup F V)) ≤ repCentSL ρ := by
    rw [Subgroup.map_id]
  have hnorm : (((repCentSL ρ).map (MonoidHom.id (SpecialLinearGroup F V))).subgroupOf
      (repCentSL ρ)).Normal := by
    rw [Subgroup.map_id, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hcomm : ⁅repCentSL ρ, repCentSL ρ⁆ ≤
      (repCentSL ρ).map (MonoidHom.id (SpecialLinearGroup F V)) := by
    rw [Subgroup.map_id]
    exact LayerFacts.ggCommutator_self_le _
  have hSn : ∀ b : β, ∀ c ∈ repCentSL ρ, ∀ s ∈ fr.slOnBlock b.1,
      c * s * c⁻¹ ∈ fr.slOnBlock b.1 := by
    intro b c hc s hs
    have h1 : blockPiGL fr ⟨s, hSC b hs⟩ ∈
        CFSG.RankThree.PartOne.KCLinComm.blockSL fr.E fr.m b.1 :=
      (SemiFrame.mem_slOnBlock_iff_mem_comap fr ⟨s, hSC b hs⟩ b.1).mp hs
    have h2 : blockPiGL fr ⟨c, hc⟩ * blockPiGL fr ⟨s, hSC b hs⟩ *
        (blockPiGL fr ⟨c, hc⟩)⁻¹ ∈ CFSG.RankThree.PartOne.KCLinComm.blockSL fr.E fr.m b.1 :=
      CFSG.RankThree.PartOne.KCLinComm.conj_mem_blockSL b.1 (blockPiGL fr ⟨c, hc⟩) h1
    have hC : c * s * c⁻¹ ∈ repCentSL ρ :=
      (repCentSL ρ).mul_mem ((repCentSL ρ).mul_mem hc (hSC b hs)) ((repCentSL ρ).inv_mem hc)
    refine (SemiFrame.mem_slOnBlock_iff_mem_comap fr ⟨c * s * c⁻¹, hC⟩ b.1).mpr ?_
    have h2' : blockPiGL fr ⟨c * s * c⁻¹, hC⟩ =
        blockPiGL fr ⟨c, hc⟩ * blockPiGL fr ⟨s, hSC b hs⟩ * (blockPiGL fr ⟨c, hc⟩)⁻¹ := by
      rw [show (⟨c * s * c⁻¹, hC⟩ : repCentSL ρ) =
          (⟨c, hc⟩ : repCentSL ρ) * (⟨s, hSC b hs⟩ : repCentSL ρ) *
            (⟨c, hc⟩ : repCentSL ρ)⁻¹ from Subtype.ext rfl]
      simp only [map_mul, map_inv]
    rw [h2']
    exact h2
  have hder : ∃ k, LayerFacts.ggDer (repCentSL ρ) k ≤ ⨆ b : β, fr.slOnBlock b.1 := by
    obtain ⟨k, hk⟩ :=
      LayerFacts.exists_derivedSeries_le_goodSL (E := fr.E) (m := fr.m) (ι := Fin fr.r)
    refine ⟨k, ?_⟩
    have h1 : ((LayerFacts.ggDer (repCentSL ρ) k).subgroupOf (repCentSL ρ)).map (blockPiGL fr) ≤
        ((⨆ b : β, fr.slOnBlock b.1).subgroupOf (repCentSL ρ)).map (blockPiGL fr) := by
      rw [SemiFrame.subgroupOf_iSup_eq (fun b : β => fr.slOnBlock b.1) hSC, Subgroup.map_iSup]
      simp_rw [SemiFrame.map_slOnBlock_subgroupOf_eq_blockSL fr]
      rw [SemiFrame.ggDer_subgroupOf_eq (repCentSL ρ) k, LayerFacts.map_ggDer]
      calc LayerFacts.ggDer ((⊤ : Subgroup (repCentSL ρ)).map (blockPiGL fr)) k
          ≤ LayerFacts.ggDer (⊤ : Subgroup (∀ j, GL (Fin (fr.m j)) (fr.E j))) k :=
            LayerFacts.ggDer_mono le_top k
        _ = derivedSeries (∀ j, GL (Fin (fr.m j)) (fr.E j)) k := LayerFacts.ggDer_top k
        _ ≤ LayerFacts.goodSL fr.E fr.m := hk
    exact SemiFrame.le_of_subgroupOf_le_subgroupOf (SemiFrame.ggDer_le (repCentSL ρ) k)
      ((Subgroup.map_le_map_iff_of_injective (SemiFrame.blockPiGL_injective fr)).mp h1)
  have hSq : ∀ b : β, CFSG.IsQuasisimple (fr.slOnBlock b.1) :=
    fun b => isQuasisimple_slOnBlock_native fr b.1 b.2.1 b.2.2
  obtain ⟨b, hb⟩ := LayerPDiv.exists_eq_map_of_isComponentOf (MonoidHom.id (SpecialLinearGroup F V))
    (by rw [MonoidHom.ker_id]; exact bot_le) hC₀H hnorm hcomm (fun b : β => fr.slOnBlock b.1)
    hSC hSn hSq hder hK
  refine ⟨b.1, ⟨b.2.1, ?_⟩, ?_⟩
  · rcases b.2.2 with h3 | ⟨s, hs⟩
    · exact Or.inl h3
    · refine Or.inr ?_
      haveI : Fintype (fr.E b.1) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card]
      calc 4 = s.card := hs.symm
        _ ≤ (Finset.univ : Finset (fr.E b.1)).card := Finset.card_le_univ s
        _ = Fintype.card (fr.E b.1) := Finset.card_univ
  · simpa using hb

end CFSG.StandardType.StarFour
