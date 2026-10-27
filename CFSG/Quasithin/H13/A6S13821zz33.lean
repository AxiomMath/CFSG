module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F918P5
public import CFSG.Quasithin.H13.A6S13821zz19
public import CFSG.Quasithin.H13.A6S13821zz26
public import CFSG.Quasithin.H13.A6S1385b

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

attribute [local instance] commGroupOfFact

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem false_of_pair_sl34_13820b (hS : S.Hyp138) {H K : Subgroup G} (hH : H ∈ S.Hz)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHKT : H = K ⊔ T)
    (hF : HypF918 T V L (fsuV1 T V) S.V3 H K) {I : Subgroup G} (hIU : I ≤ conjClosure S.V3 H)
    (hkerK : ∀ k ∈ K, (∀ u ∈ conjClosure I H, k * u * k⁻¹ * u⁻¹ ∈ fsuV1 T V) →
      k ∈ pCoreOf 2 H) :
    haveI := factElem hF hIU
    ∀ t ∈ autIH (fsuV1 T V) I H T,
      BinaryNaturalSL (autIH (fsuV1 T V) I H K) (subM (fsuV1 T V) (conjClosure I H) I) ⊥ 3 2 →
      subM (fsuV1 T V) (conjClosure I H) I ⊓
          (subM (fsuV1 T V) (conjClosure I H) I).map t.toMonoidHom = ⊥ →
      subM (fsuV1 T V) (conjClosure I H) I ⊔
          (subM (fsuV1 T V) (conjClosure I H) I).map t.toMonoidHom = ⊤ →
      ¬ CFSG.Quasithin.H.Pair.IsoMod (autIH (fsuV1 T V) I H K)
          (subM (fsuV1 T V) (conjClosure I H) I)
          ((subM (fsuV1 T V) (conjClosure I H) I).map t.toMonoidHom) →
      False := by
  classical
  have hFe := factElem hF hIU
  intro t htT hnat hinf hsup hniso
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hHKT ▸ le_sup_right
  have hV₁ := hF.H_le_normalizer_V₁
  have hIH := le_normalizer_conjClosure I H
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  set ψ := actH hV₁ hIH with hψ
  have hHU := le_normalizer_conjClosure S.V3 H
  have hXU : conjClosure I H ≤ conjClosure S.V3 H := conjClosure_le fun h hh x hx =>
    (Subgroup.mem_normalizer_iff.mp (hHU hh) x).mp (hIU hx)
  have hconjK : ∀ h : ↥H, ∀ l ∈ autIH (fsuV1 T V) I H K,
      ψ h * l * (ψ h)⁻¹ ∈ autIH (fsuV1 T V) I H K := by
    intro h l hl
    rw [autIH_eq_map hF hKH] at hl ⊢
    obtain ⟨k, hk, rfl⟩ := hl
    refine ⟨h * k * h⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (Subgroup.mem_normalizer_iff.mp (hKn h.2) _).mp (Subgroup.mem_subgroupOf.mp hk)
  have hnorm : ∀ h : ↥H, ψ h ∈ Subgroup.normalizer
      ((autIH (fsuV1 T V) I H K : Subgroup (MulAut _)) : Set (MulAut _)) := by
    intro h
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨hconjK h l, fun hl => ?_⟩
    have h1 := hconjK h⁻¹ _ hl
    rwa [map_inv, inv_inv, show (ψ h)⁻¹ * (ψ h * l * (ψ h)⁻¹) * ψ h = l by group] at h1
  have htN : t ∈ Subgroup.normalizer
      ((autIH (fsuV1 T V) I H K : Subgroup (MulAut _)) : Set (MulAut _)) := by
    rw [autIH_eq_map hF hTH] at htT
    obtain ⟨h, -, rfl⟩ := htT
    exact hnorm h
  refine S.false_of_section_13820b hS hH hKn hHKT ψ hXU hIH (tildeHom hIHN)
    (tildeHom_surjective hIHN) (fun x hx => Subtype.ext (by
      rw [tildeHom_coe]
      exact secMk_eq_one_iff.mpr hx)) (fun h x hx => ?_) (fun h hhK h1 => ?_) ?_
  · have e1 : tildeHom hIHN x = modMk hIHN x x.2 := rfl
    rw [e1, actH_modMk hV₁ hIHN hIH h x.2]
    rfl
  · rw [hψ, A6Tv.actH_eq_one_iff hV₁ hIHN hIH] at h1
    exact hkerK h hhK h1
  · intro A hA hAel D hD a₁ hDA
    refine A6S20.sl34_quad hnat htN hinf hsup hniso ?_ hAel hD a₁ hDA
    intro a ha
    obtain ⟨h, rfl⟩ := hA ha
    exact hnorm h

end Setting4

end CFSG.Quasithin.H13.A6
