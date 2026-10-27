module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.ClassicalInvolution.WeakCT.Exceptional
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld

section PresE67Aux

variable {G : Type} [Group G] [Finite G]

private theorem range_subtype_comp {K : Type} [Group K] {H : Subgroup G} (Ψ : K →* ↥H)
    (hs : Function.Surjective Ψ) : (H.subtype.comp Ψ).range = H := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs, Subgroup.map_top, Subgroup.range_subtype]

private theorem ker_subtype_comp {K : Type} [Group K] {H : Subgroup G} (Ψ : K →* ↥H) :
    (H.subtype.comp Ψ).ker = Ψ.ker :=
  MonoidHom.ker_comp_of_injective Ψ H.subtype (Subgroup.subtype_injective H)

private theorem map_subtype_comp {K : Type} [Group K] {H : Subgroup G} (Ψ : K →* ↥H)
    (S : Subgroup K) (T : Subgroup ↥H) (h : S.map Ψ = T) :
    S.map (H.subtype.comp Ψ) = T.map H.subtype := by
  rw [← Subgroup.map_map, h]

end PresE67Aux

section PresE67

variable {G : Type} [Group G] [Finite G]

theorem ggPresentsG0_typeE6_of_system_levi {f : ℕ} (hq : 4 ≤ 2 ^ f) {H : Subgroup G}
    {U : Fin 6 → Subgroup ↥H}
    (hcomm : ∀ i j : Fin 6, i ≠ j → ¬ edgeE 6 i j → ¬ edgeE 6 j i →
      ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin 6, edgeE 6 i j →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : (ggU .E6 0 f).K →* G,
      GGPresentsG0 H (ggU .E6 0 f).D .E6 0 f ψ ∧
        ∃ σ : Fin (ggU .E6 0 f).D.rank ≃ Fin 6, (∀ k, ((σ k : Fin 6) : ℕ) = k) ∧
          ∀ k, (CFSG.LieType.CurtisTits.rankOne (ggU .E6 0 f).D.rootGroup k).map ψ =
            (U (σ k)).map H.subtype := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0] at hq
    norm_num at hq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq' : 4 ≤ Nat.card (GaloisField 2 f) := by rw [hK]; exact hq
  have hadm : StatedLieAdmissible .E6 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  obtain ⟨Ψ₀, hsurj, hker, hqs, _hcenter, hmodel, hlevi⟩ :=
    weakCT_e6 2 f hadm (F := GaloisField 2 f) (X := ↥H) hK hq' U hgen hcomm hpair
  refine ⟨H.subtype.comp Ψ₀, ⟨⟨hadm, ?_⟩, ⟨?_, ?_⟩, ?_, hmodel⟩, Equiv.refl _, fun k => rfl,
    fun k => ?_⟩
  · show 2 ≤ 6
    norm_num
  · exact range_subtype_comp Ψ₀ hsurj
  · exact (ker_subtype_comp Ψ₀).le.trans hker
  · exact hqs.1.commutator_eq_top
  · exact map_subtype_comp Ψ₀ _ _ (hlevi k)

theorem ggPresentsG0_typeE7_of_system_levi {f : ℕ} (hq : 4 ≤ 2 ^ f) {H : Subgroup G}
    {U : Fin 7 → Subgroup ↥H}
    (hcomm : ∀ i j : Fin 7, i ≠ j → ¬ edgeE 7 i j → ¬ edgeE 7 j i →
      ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin 7, edgeE 7 i j →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : (ggU .E7 0 f).K →* G,
      GGPresentsG0 H (ggU .E7 0 f).D .E7 0 f ψ ∧
        ∃ σ : Fin (ggU .E7 0 f).D.rank ≃ Fin 7, (∀ k, ((σ k : Fin 7) : ℕ) = k) ∧
          ∀ k, (CFSG.LieType.CurtisTits.rankOne (ggU .E7 0 f).D.rootGroup k).map ψ =
            (U (σ k)).map H.subtype := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0] at hq
    norm_num at hq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq' : 4 ≤ Nat.card (GaloisField 2 f) := by rw [hK]; exact hq
  have hadm : StatedLieAdmissible .E7 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  obtain ⟨Ψ₀, hsurj, hker, hqs, _hcenter, hmodel, hlevi⟩ :=
    weakCT_e7 2 f hadm (F := GaloisField 2 f) (X := ↥H) hK hq' U hgen hcomm hpair
  refine ⟨H.subtype.comp Ψ₀, ⟨⟨hadm, ?_⟩, ⟨?_, ?_⟩, ?_, hmodel⟩, Equiv.refl _, fun k => rfl,
    fun k => ?_⟩
  · show 2 ≤ 7
    norm_num
  · exact range_subtype_comp Ψ₀ hsurj
  · exact (ker_subtype_comp Ψ₀).le.trans hker
  · exact hqs.1.commutator_eq_top
  · exact map_subtype_comp Ψ₀ _ _ (hlevi k)

end PresE67

end CFSG.StandardType

end
