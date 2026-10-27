module

public import CFSG.Quasithin.Background.D2Decomp
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native

private theorem ker_le_frattini_of_forall_map_eq_top {T Q : Type*} [Group T] [Group Q]
    (ψ : T →* Q) (hψ : Function.Surjective ψ)
    (hmin : ∀ H : Subgroup T, H.map ψ = ⊤ → H = ⊤) : ψ.ker ≤ frattini T := by
  refine le_iInf₂ fun H hH => ?_
  have hH' : IsCoatom H := hH
  by_contra hKH
  have hsup : H ⊔ ψ.ker = ⊤ := hH'.2 _ (left_lt_sup.mpr hKH)
  refine hH'.1 (hmin H (eq_top_iff.mpr fun q _ => ?_))
  obtain ⟨t, rfl⟩ := hψ q
  have ht : t ∈ H ⊔ ψ.ker := hsup ▸ Subgroup.mem_top t
  rw [← Subgroup.comap_map_eq] at ht
  exact ht

private theorem isSolvable_ker_lift_of_le_frattini {T Q : Type*} [Group T] [Finite T] [Group Q]
    (ψ : T →* Q) (P : Subgroup T) [P.Normal] (hP : P ≤ ψ.ker) (hψ : ψ.ker ≤ frattini T) :
    Group.IsSolvable (QuotientGroup.lift P ψ hP).ker := by
  have : Group.IsNilpotent ↥(frattini T) := frattini_nilpotent
  have hker : Group.IsSolvable ψ.ker :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hψ)
      (Subgroup.inclusion_injective hψ)
  rw [QuotientGroup.ker_lift]
  exact Group.isSolvable_of_surjective (f := (QuotientGroup.mk' P).subgroupMap ψ.ker)
    (MonoidHom.subgroupMap_surjective _ _)

theorem exists_sqtk_cover {Q : Type} [Group Q] [Finite Q] (hQ : IsQuotientOfSQTKTC Q)
    (hO2 : CFSG.pCore 2 Q = ⊥) {L : Subgroup Q} (hL : L ∈ cComp (⊤ : Subgroup Q)) :
    ∃ (Shat : Type) (_ : Group Shat) (φ : Shat →* Q), Function.Surjective φ ∧ SQTKHypCat Shat ∧
      ∃ Lhat : Subgroup Shat, Lhat ∈ cComp (⊤ : Subgroup Shat) ∧ Lhat.map φ = L := by
  obtain ⟨S, _, _, hSQT, hK, φ₀, hφ₀⟩ := hQ
  have hS : CFSG.SectionRank.IsSQTKCat S :=
    ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr hSQT, hK⟩
  obtain ⟨S₁, hS₁⟩ := (Set.toFinite {H : Subgroup S | H.map φ₀ = ⊤}).exists_minimal
    ⟨⊤, Subgroup.map_top_of_surjective φ₀ hφ₀⟩
  set ψ : ↥S₁ →* Q := φ₀.comp S₁.subtype with hψdef
  have hψ : Function.Surjective ψ := by
    intro q
    have hq : q ∈ S₁.map φ₀ := by rw [hS₁.prop]; exact Subgroup.mem_top q
    obtain ⟨s, hs, rfl⟩ := hq
    exact ⟨⟨s, hs⟩, rfl⟩
  have hmin : ∀ H : Subgroup ↥S₁, H.map ψ = ⊤ → H = ⊤ := by
    intro H hH
    have h1 : (H.map S₁.subtype).map φ₀ = ⊤ := by rw [Subgroup.map_map]; exact hH
    have h2 : H.map S₁.subtype = S₁ := hS₁.eq_of_le h1 (Subgroup.map_subtype_le H)
    refine Subgroup.map_injective S₁.subtype_injective ?_
    rw [h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfr : ψ.ker ≤ frattini ↥S₁ := ker_le_frattini_of_forall_map_eq_top ψ hψ hmin
  have hP : CFSG.pCore 2 ↥S₁ ≤ ψ.ker := by
    have h1 : (CFSG.pCore 2 ↥S₁).map ψ ≤ CFSG.pCore 2 Q :=
      le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥S₁)).map ψ hψ, CFSG.pCore_isPGroup.map ψ⟩
    rw [hO2, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
    exact h1
  let φ : (↥S₁ ⧸ CFSG.pCore 2 ↥S₁) →* Q := QuotientGroup.lift (CFSG.pCore 2 ↥S₁) ψ hP
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨s, rfl⟩ := hψ q
    exact ⟨QuotientGroup.mk s, rfl⟩
  have hker : Group.IsSolvable φ.ker := isSolvable_ker_lift_of_le_frattini ψ _ hP hfr
  have hhyp : SQTKHypCat (↥S₁ ⧸ CFSG.pCore 2 ↥S₁) :=
    SQTKHypCat.quotient_pCore ↥S₁ (hS.subgroup S₁)
  have := hhyp.finite
  obtain ⟨Lhat, hLhat, hmap⟩ := map_surjOn_cComp_top φ hφ hker hL
  exact ⟨_, inferInstance, φ, hφ, hhyp, Lhat, hLhat, hmap⟩

end CFSG.Quasithin
