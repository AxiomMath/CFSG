module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.ClassicalInvolution.WeakCT.Exceptional
public import CFSG.ClassicalInvolution.WeakCT.Main

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld

private theorem range_subtype_comp {G : Type} [Group G] {K : Type} [Group K] {H : Subgroup G}
    (Ψ : K →* ↥H) (hs : Function.Surjective Ψ) : (H.subtype.comp Ψ).range = H := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hs, Subgroup.map_top,
    Subgroup.range_subtype]

private theorem ker_subtype_comp {G : Type} [Group G] {K : Type} [Group K] {H : Subgroup G}
    (Ψ : K →* ↥H) : (H.subtype.comp Ψ).ker = Ψ.ker :=
  MonoidHom.ker_comp_of_injective Ψ H.subtype (Subgroup.subtype_injective H)

private theorem map_subtype_comp {G : Type} [Group G] {K : Type} [Group K] {H : Subgroup G}
    (Ψ : K →* ↥H) (S : Subgroup K) (T : Subgroup ↥H) (h : S.map Ψ = T) :
    S.map (H.subtype.comp Ψ) = T.map H.subtype := by
  rw [← Subgroup.map_map, h]

section PresE8

variable {G : Type} [Group G] [Finite G]

theorem ggPresentsG0_typeE8_of_system_levi {f : ℕ} (hq : 4 ≤ 2 ^ f) {H : Subgroup G}
    {U : Fin 8 → Subgroup ↥H}
    (hcomm : ∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
      ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x)
    (hpair : ∀ i j : Fin 8, edgeE 8 i j →
      ∃ W, LinearBlockStandardPair (GaloisField 2 f) W (U i) (U j))
    (hgen : ⨆ i, U i = ⊤) :
    ∃ ψ : (ggU .E8 0 f).K →* G,
      GGPresentsG0 H (ggU .E8 0 f).D .E8 0 f ψ ∧
        ∃ σ : Fin (ggU .E8 0 f).D.rank ≃ Fin 8, (∀ k, ((σ k : Fin 8) : ℕ) = k) ∧
          ∀ k, (CFSG.LieType.CurtisTits.rankOne (ggU .E8 0 f).D.rootGroup k).map ψ =
            (U (σ k)).map H.subtype := by
  have hf : 1 ≤ f := by
    by_contra h
    have h0 : f = 0 := by omega
    rw [h0] at hq
    norm_num at hq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq' : 4 ≤ Nat.card (GaloisField 2 f) := by rw [hK]; exact hq
  have hadm : StatedLieAdmissible .E8 0 2 f := ⟨Nat.prime_two, hf, rfl⟩
  obtain ⟨Ψ₀, hsurj, hker, hqs, _hcenter, hmodel, hlevi⟩ :=
    weakCT_e8 2 f hadm (F := GaloisField 2 f) (X := ↥H) hK hq' U hgen hcomm hpair
  refine ⟨H.subtype.comp Ψ₀, ?_, Equiv.refl _, fun k => rfl, ?_⟩
  · refine ⟨⟨hadm, ?_⟩, ⟨?_, ?_⟩, ?_, hmodel⟩
    ·
      have hrank : (ggU .E8 0 f).D.rank = 8 := rfl
      rw [hrank]
      norm_num
    · exact range_subtype_comp Ψ₀ hsurj
    · exact (ker_subtype_comp Ψ₀).le.trans hker
    · exact hqs.1.commutator_eq_top
  · intro k
    exact map_subtype_comp Ψ₀ _ _ (hlevi k)

end PresE8

end CFSG.StandardType

end
