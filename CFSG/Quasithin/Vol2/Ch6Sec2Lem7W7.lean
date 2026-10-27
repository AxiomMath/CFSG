module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.SBc3List

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Correspondence

variable {G : Type} [Group G] [Finite G] {Γ : Type} [Group Γ] [Finite Γ]

theorem exists_cComp_of_quasisimple627 {H : Subgroup G} (ρ : ↥H →* Γ)
    (hker : Group.IsSolvable ρ.ker) {L : Subgroup Γ} (hsn : IsSubnormal L ρ.range)
    (hq : CFSG.IsQuasisimple ↥L) : ∃ K ∈ cComp H, (K.subgroupOf H).map ρ = L := by
  classical
  have hLX : L ≤ ρ.range := A3.subnormal_le hsn
  set f := ρ.rangeRestrict with hf
  have hfs : Function.Surjective f := MonoidHom.rangeRestrict_surjective ρ
  have hfk : Group.IsSolvable f.ker := by rw [hf, MonoidHom.ker_rangeRestrict]; exact hker
  set L' := L.subgroupOf ρ.range with hL'
  have hq' : CFSG.IsQuasisimple ↥L' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX).symm hq
  have hL'c : L' ∈ cComp (⊤ : Subgroup ↥ρ.range) :=
    mem_cComp_top_of_isComponent ⟨hq', SBc3.isSubnormal_subgroupOf hsn⟩
  obtain ⟨K₁, hK₁, hK₁L⟩ := map_surjOn_cComp_top f hfs hfk hL'c
  refine ⟨K₁.map H.subtype, map_subtype_mem_cComp hK₁, ?_⟩
  have h1 : (K₁.map H.subtype).subgroupOf H = K₁ :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective K₁
  rw [h1, ← MonoidHom.subtype_comp_rangeRestrict ρ, ← Subgroup.map_map, ← hf, hK₁L, hL',
    Subgroup.map_subgroupOf_eq_of_le hLX]

theorem uniq_of_cComp627 {H : Subgroup G} (ρ : ↥H →* Γ) (hker : Group.IsSolvable ρ.ker)
    (hres : ∀ K K' : Subgroup G, K ∈ cComp H → K' ∈ cComp H → 3 ∣ Nat.card K →
      3 ∣ Nat.card K' → K = K')
    (L₁ L₂ : Subgroup Γ) (hs₁ : IsSubnormal L₁ ρ.range) (hs₂ : IsSubnormal L₂ ρ.range)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂) (h₁ : 3 ∣ Nat.card L₁)
    (h₂ : 3 ∣ Nat.card L₂) : L₁ = L₂ := by
  obtain ⟨K₁, hK₁, rfl⟩ := exists_cComp_of_quasisimple627 ρ hker hs₁ hq₁
  obtain ⟨K₂, hK₂, rfl⟩ := exists_cComp_of_quasisimple627 ρ hker hs₂ hq₂
  have h3 : ∀ K : Subgroup G, K ≤ H → 3 ∣ Nat.card ((K.subgroupOf H).map ρ) → 3 ∣ Nat.card K :=
    fun K hKH h => h.trans (Dvd.dvd.trans (Subgroup.card_map_dvd _ _)
      (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv)))
  rw [hres K₁ K₂ hK₁ hK₂ (h3 K₁ (le_of_mem_cComp hK₁) h₁) (h3 K₂ (le_of_mem_cComp hK₂) h₂)]

omit [Finite G] [Finite Γ] in
theorem map_conj_eq_of_uniq627 {X L : Subgroup Γ}
    (huniq : ∀ L₁ L₂ : Subgroup Γ, IsSubnormal L₁ X → IsSubnormal L₂ X →
      CFSG.IsQuasisimple ↥L₁ → CFSG.IsQuasisimple ↥L₂ → 3 ∣ Nat.card L₁ → 3 ∣ Nat.card L₂ →
        L₁ = L₂)
    (hsn : IsSubnormal L X) (hq : CFSG.IsQuasisimple ↥L) (h3 : 3 ∣ Nat.card L) {g : Γ}
    (hg : X.map (MulAut.conj g).toMonoidHom = X) : L.map (MulAut.conj g).toMonoidHom = L := by
  have hsn' := A3.subnormal_map (MulAut.conj g).toMonoidHom hsn
  rw [hg] at hsn'
  refine huniq _ _ hsn' hsn ?_ hq ?_ h3
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (L.equivMapOfInjective _ (MulAut.conj g).injective) hq
  · rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective]

end Correspondence

section B53

variable {G : Type} [Group G] [Finite G] {Q : Type} [CommGroup Q] [Finite Q]

omit [Finite Q] in
theorem b53Hyp_ffJ627 {H : Subgroup G} (ρ : ↥H →* MulAut Q) (hS : SQTKGroup ↥H)
    {Y : Subgroup (MulAut Q)} (hY : Y ≤ ρ.range) (hO2 : pCoreOf 2 Y = ⊥) : B53Hyp (ffJ Y) := by
  set J := ffJ Y with hJ
  have hJY : J ≤ Y := B6.ffJ_le Y
  have hJn : (J.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).2 (B6.le_normalizer_ffJ Y)
  have hQ : pCoreOf 2 J = ⊥ := by
    have := CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 J Y hJY hJn
    rw [hO2] at this
    exact le_bot_iff.1 this
  set H' : Subgroup ↥H := J.comap ρ with hH'
  let f : ↥H' →* ↥J :=
    { toFun := fun h => ⟨ρ (h : ↥H), h.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨h, hh⟩ := hY (hJY hj)
    refine ⟨⟨h, ?_⟩, ?_⟩
    · show ρ h ∈ J
      rw [hh]
      exact hj
    · apply Subtype.ext
      exact hh
  refine ⟨hQ, (InternalSec.ffJ_ffJ _).symm, ↥H', inferInstance, inferInstance, f.ker,
    inferInstance, InternalSec.sqtkGroup_subgroup hS H',
    ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

end B53

end CFSG.Quasithin.H13
