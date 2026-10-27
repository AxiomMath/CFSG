module

public import CFSG.Quasithin.Background.A4Four
public import CFSG.GroupTheory.BaerSuzuki.Helpers
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_normal_above_pCoreOf {H : Subgroup G} (hsolv : Group.IsSolvable ↥H)
    (hlt : pCoreOf 2 H < H) :
    ∃ P : Subgroup G, P ≤ H ∧ pCoreOf 2 H < P ∧ H ≤ Subgroup.normalizer (P : Set G) ∧
      Odd ((pCoreOf 2 H).relIndex P) := by
  classical
  set Q₀ : Subgroup ↥H := CFSG.Open.pCore 2 ↥H with hQ₀
  have hQ₀n : Q₀.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set π : ↥H →* (↥H ⧸ Q₀) := QuotientGroup.mk' Q₀ with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Q₀
  have hQ : pCoreOf 2 H = Q₀.map H.subtype := rfl
  have : Group.IsSolvable ↥H := hsolv
  have hQ₀top : Q₀ ≠ ⊤ := by
    intro htop
    apply hlt.ne
    rw [hQ, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have : Nontrivial (↥H ⧸ Q₀) := QuotientGroup.nontrivial_iff.mpr hQ₀top
  obtain ⟨N, hNn, -, hNbot, hNmin⟩ := CFSG.exists_minimal_normal_le (⊤ : Subgroup (↥H ⧸ Q₀))
    Subgroup.normal_top top_ne_bot
  have : N.Normal := hNn
  have : CFSG.IsMinimalNormal N := ⟨fun K hK hKN => by
    by_cases hKb : K = ⊥
    · exact Or.inl hKb
    · exact Or.inr (hNmin K hK hKN hKb)⟩
  have : Group.IsSolvable ↥N := inferInstance
  obtain ⟨p, hp, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
  have : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p ↥N := CFSG.IsElementaryAbelian.isPGroup p ↥N
  have hp2 : p ≠ 2 := by
    rintro rfl
    have hle : N ≤ CFSG.pCore 2 (↥H ⧸ Q₀) :=
      CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hNn hpg
    have h0 : CFSG.pCore 2 (↥H ⧸ Q₀) = ⊥ := pCore_two_quot_eq_bot H
    exact hNbot (le_bot_iff.mp (h0 ▸ hle))
  set Y' : Subgroup ↥H := N.comap π with hY'
  have hY'n : Y'.Normal := Subgroup.Normal.comap hNn π
  set P : Subgroup G := Y'.map H.subtype with hP
  have hPH : P ≤ H := Subgroup.map_subtype_le _
  have hQ₀Y' : Q₀ ≤ Y' := by
    intro x hx
    rw [hY', Subgroup.mem_comap, hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact N.one_mem
  have hQP : pCoreOf 2 H ≤ P := by
    rw [hQ]
    exact Subgroup.map_mono hQ₀Y'
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
    have h1 : P.subgroupOf H = Y' := Subgroup.comap_map_eq_self_of_injective H.subtype_injective Y'
    have : (P.subgroupOf H).Normal := by rw [h1]; exact hY'n
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mp this
  have hker : (⊥ : Subgroup (↥H ⧸ Q₀)).comap π = Q₀ := QuotientGroup.ker_mk' Q₀
  have hrel0 : Q₀.relIndex Y' = Nat.card N := by
    have h1 := Subgroup.relIndex_comap (⊥ : Subgroup (↥H ⧸ Q₀)) π Y'
    rw [hker] at h1
    rw [h1, Subgroup.relIndex_bot_left, hY', Subgroup.map_comap_eq_self_of_surjective hπs]
  have hrel : (pCoreOf 2 H).relIndex P = Nat.card N := by
    rw [hQ, hP, Subgroup.relIndex_map_map_of_injective _ _ H.subtype_injective]
    exact hrel0
  obtain ⟨k, hk⟩ := hpg.exists_card_eq
  have hodd : Odd (Nat.card N) := by
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hlt' : pCoreOf 2 H < P := by
    refine lt_of_le_of_ne hQP fun heq => ?_
    have h1 : (pCoreOf 2 H).relIndex P = 1 := by
      rw [heq]
      exact Subgroup.relIndex_self _
    have h2 : 1 < Nat.card N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNbot
    omega
  exact ⟨P, hPH, hlt', hHP, hrel ▸ hodd⟩

end CFSG.Quasithin
