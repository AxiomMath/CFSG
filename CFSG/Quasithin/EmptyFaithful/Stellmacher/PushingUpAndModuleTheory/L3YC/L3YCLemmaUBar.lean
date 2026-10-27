module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCLemmaU
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.SBd7

namespace Stellmacher.PU.L3YC

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Qbar (H G₀ L : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  ((c134Q G₀ L).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

@[expose] noncomputable def Cbar (H G₀ L : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  ((c134CQ G₀ L).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

@[expose] noncomputable def toBar {H L : Subgroup G} (hLH : L ≤ H) : ↥L →* ↥H ⧸ CFSG.pCore 2 ↥H :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hLH)

omit [Finite G] in
theorem map_subgroupOf_toBar {H L X : Subgroup G} (hLH : L ≤ H) (hXL : X ≤ L) :
    (X.subgroupOf L).map (toBar hLH) =
      (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Subgroup.inclusion hLH x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, hXL hx⟩, hx, rfl⟩

omit [Finite G] in
theorem range_toBar {H L : Subgroup G} (hLH : L ≤ H) :
    (toBar hLH).range = modO2Image H L := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Subgroup.inclusion hLH x, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x.1, hx⟩, rfl⟩

theorem lemmaU_bar_U1 {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3)
    (h : MS93.IsC134Case4Corr G₀ R L) :
    Cbar H G₀ L ≤ Subgroup.centralizer (modO2Image H L : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ∧
      Nat.card ↥(Cbar H G₀ L) ≤ 4 ∧
      ⁅Qbar H G₀ L, (frattini ↥(Qbar H G₀ L)).map (Qbar H G₀ L).subtype⁆ ≤ Cbar H G₀ L := by
  have hQL : c134Q G₀ L ≤ L := (MS93.commutator_le_pCoreOf hLG hGL).trans (pCoreOf_le 2 L)
  have hCL : c134CQ G₀ L ≤ L := inf_le_left.trans hQL
  have hQe := map_subgroupOf_toBar hLH hQL
  have hCe := map_subgroupOf_toBar hLH hCL
  obtain ⟨h1, h2⟩ := lemmaU_C_central hLG hGL hq h (toBar hLH)
  have h3 := lemmaU_comm_frattini_le hLG hGL hq h (toBar hLH)
  rw [range_toBar] at h1
  unfold Qbar Cbar
  rw [← hQe, ← hCe]
  exact ⟨h1, h2, h3⟩

theorem lemmaU_bar_U2 {H G₀ R L : Subgroup G} (hLH : L ≤ H) (hLG : L ≤ G₀)
    (hGL : G₀ ≤ Subgroup.normalizer (L : Set G)) (hq : IsLnTwoQuot L 3)
    (h : MS93.IsC134Case4Corr G₀ R L) {D' : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hDn : ∀ b ∈ modO2Image H L, ∀ y ∈ D', b * y * b⁻¹ ∈ D')
    (hCD : Cbar H G₀ L ≤ D') (hDQ : D' ≤ Qbar H G₀ L) :
    ∃ j : ℕ, Nat.card ↥(Qbar H G₀ L) = Nat.card ↥D' * 8 ^ j := by
  have hQL : c134Q G₀ L ≤ L := (MS93.commutator_le_pCoreOf hLG hGL).trans (pCoreOf_le 2 L)
  have hCL : c134CQ G₀ L ≤ L := inf_le_left.trans hQL
  have hQe := map_subgroupOf_toBar hLH hQL
  have hCe := map_subgroupOf_toBar hLH hCL
  unfold Qbar Cbar at *
  rw [← hQe] at hDQ ⊢
  rw [← hCe] at hCD
  exact lemmaU_card_section hLG hGL hq h (toBar hLH)
    (fun l y hy => hDn _ ⟨Subgroup.inclusion hLH l, l.2, rfl⟩ y hy) hCD hDQ

end Stellmacher.PU.L3YC

end CFSG.Quasithin
