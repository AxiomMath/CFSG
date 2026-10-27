module

public import CFSG.Quasithin.Background.F6GoldschmidtListCat
public import CFSG.Quasithin.Background.F6CatIso
public import CFSG.Quasithin.Background.GoldschmidtAmalgamVBase
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

universe u

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

structure IsGoldschmidtVPair {G : Type*} [Group G] (I₁ I₂ : Subgroup G) : Prop where
  quotient₁ : Nonempty (↥I₁ ⧸ Open.pCore 2 ↥I₁ ≃* Equiv.Perm (Fin 3))
  quotient₂ : Nonempty (↥I₂ ⧸ Open.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3))
  sylow₁ : IsSylowTwoOf (I₁ ⊓ I₂) I₁
  sylow₂ : IsSylowTwoOf (I₁ ⊓ I₂) I₂
  pCore_eq_bot : pCoreOf 2 (I₁ ⊔ I₂) = ⊥

namespace GoldPair

variable {D : Type*} [Group D]

omit [Group D] in
theorem subgroupOf_inf {D : Type*} [Group D] (A A' B : Subgroup D) :
    (A ⊓ A').subgroupOf B = A.subgroupOf B ⊓ A'.subgroupOf B :=
  Subgroup.ext fun _ => Iff.rfl

theorem pCoreOf_top_eq : pCoreOf 2 (⊤ : Subgroup D) = Open.pCore 2 D := by
  unfold pCoreOf
  exact map_pCore_mulEquiv 2 (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D)

theorem isSylowTwoOf_subgroupOf {S H K : Subgroup D} (hHK : H ≤ K) (h : IsSylowTwoOf S H) :
    IsSylowTwoOf (S.subgroupOf K) (H.subgroupOf K) := by
  obtain ⟨hSH, hS2, hidx⟩ := h
  refine ⟨fun x hx => hSH hx, ?_, ?_⟩
  · exact hS2.of_equiv (Subgroup.subgroupOfEquivOfLe (hSH.trans hHK)).symm
  · have h2 : ((S.subgroupOf K).subgroupOf (H.subgroupOf K)).index = (S.subgroupOf H).index :=
      Subgroup.relIndex_subgroupOf (H := S) (K := H) (L := K) hHK
    rw [h2]
    exact hidx

end GoldPair

namespace IsGoldschmidtVAmalgam

variable {D : Type*} [Group D] {G₁ G₂ : Subgroup D}

theorem toVPair (h : IsGoldschmidtVAmalgam G₁ G₂) : IsGoldschmidtVPair G₁ G₂ where
  quotient₁ := h.quotient₁
  quotient₂ := h.quotient₂
  sylow₁ := h.sylow₁
  sylow₂ := h.sylow₂
  pCore_eq_bot := by rw [h.gen, GoldPair.pCoreOf_top_eq, h.pCore_eq_bot]

end IsGoldschmidtVAmalgam

namespace IsGoldschmidtVPair

variable {G : Type*} [Group G] {I₁ I₂ : Subgroup G}

theorem isPGroup_inf (h : IsGoldschmidtVPair I₁ I₂) : IsPGroup 2 ↥(I₁ ⊓ I₂) :=
  h.sylow₁.2.1

theorem symm (h : IsGoldschmidtVPair I₁ I₂) : IsGoldschmidtVPair I₂ I₁ where
  quotient₁ := h.quotient₂
  quotient₂ := h.quotient₁
  sylow₁ := by rw [inf_comm]; exact h.sylow₂
  sylow₂ := by rw [inf_comm]; exact h.sylow₁
  pCore_eq_bot := by rw [sup_comm]; exact h.pCore_eq_bot

theorem card_left [Finite G] (h : IsGoldschmidtVPair I₁ I₂) :
    Nat.card ↥I₁ = 3 * Nat.card ↥(I₁ ⊓ I₂) :=
  GoldPair.card_eq_three_mul h.quotient₁ h.sylow₁

theorem card_right [Finite G] (h : IsGoldschmidtVPair I₁ I₂) :
    Nat.card ↥I₂ = 3 * Nat.card ↥(I₁ ⊓ I₂) :=
  GoldPair.card_eq_three_mul h.quotient₂ h.sylow₂

theorem restrict (h : IsGoldschmidtVPair I₁ I₂) :
    IsGoldschmidtVAmalgam (I₁.subgroupOf (I₁ ⊔ I₂)) (I₂.subgroupOf (I₁ ⊔ I₂)) := by
  have hI₁ : I₁ ≤ I₁ ⊔ I₂ := le_sup_left
  have hI₂ : I₂ ≤ I₁ ⊔ I₂ := le_sup_right
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [← Subgroup.subgroupOf_sup hI₁ hI₂]
    exact Subgroup.subgroupOf_self _
  · obtain ⟨q⟩ := h.quotient₁
    exact ⟨(quotientPCoreCongr (Subgroup.subgroupOfEquivOfLe hI₁)).trans q⟩
  · obtain ⟨q⟩ := h.quotient₂
    exact ⟨(quotientPCoreCongr (Subgroup.subgroupOfEquivOfLe hI₂)).trans q⟩
  · rw [← GoldPair.subgroupOf_inf]
    exact GoldPair.isSylowTwoOf_subgroupOf hI₁ h.sylow₁
  · rw [← GoldPair.subgroupOf_inf]
    exact GoldPair.isSylowTwoOf_subgroupOf hI₂ h.sylow₂
  · have := h.pCore_eq_bot
    unfold pCoreOf at this
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp this

end IsGoldschmidtVPair

theorem _root_.CFSG.Quasithin.IsGoldschmidtAmalgam.toVPair {D : Type*} [Group D] [Finite D]
    {G₁ G₂ : Subgroup D} (h : IsGoldschmidtAmalgam G₁ G₂) : IsGoldschmidtVPair G₁ G₂ :=
  h.toVAmalgam.toVPair

section AmalgamIso

variable {D E : Type*} [Group D] [Group E]

theorem IsAmalgamIso.symm {H₁ H₂ : Subgroup D} {K₁ K₂ : Subgroup E}
    (h : IsAmalgamIso H₁ H₂ K₁ K₂) : IsAmalgamIso K₁ K₂ H₁ H₂ := by
  obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
  refine ⟨φ₁.symm, φ₂.symm, h₂, fun x hx₁ hx₂ => ?_⟩
  rw [MulEquiv.symm_symm, MulEquiv.symm_symm]
  exact h₁ x hx₁ hx₂

theorem IsAmalgamIso.swap {H₁ H₂ : Subgroup D} {K₁ K₂ : Subgroup E}
    (h : IsAmalgamIso H₁ H₂ K₁ K₂) : IsAmalgamIso H₂ H₁ K₂ K₁ := by
  obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
  exact ⟨φ₂, φ₁, fun x hx₂ hx₁ => (h₁ x hx₁ hx₂).symm, fun y hy₂ hy₁ => (h₂ y hy₁ hy₂).symm⟩

theorem IsAmalgamIso.trans {F : Type*} [Group F] {H₁ H₂ : Subgroup D} {K₁ K₂ : Subgroup E}
    {L₁ L₂ : Subgroup F} (h : IsAmalgamIso H₁ H₂ K₁ K₂) (h' : IsAmalgamIso K₁ K₂ L₁ L₂) :
    IsAmalgamIso H₁ H₂ L₁ L₂ := by
  obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
  obtain ⟨ψ₁, ψ₂, g₁, g₂⟩ := h'
  refine ⟨φ₁.trans ψ₁, φ₂.trans ψ₂, ?_, ?_⟩
  · intro x hx₁ hx₂
    have hy : (φ₁ ⟨x, hx₁⟩ : E) = φ₂ ⟨x, hx₂⟩ := h₁ x hx₁ hx₂
    have hmem : (φ₁ ⟨x, hx₁⟩ : E) ∈ K₂ := hy ▸ (φ₂ ⟨x, hx₂⟩).2
    have hb : (⟨(φ₁ ⟨x, hx₁⟩ : E), hmem⟩ : ↥K₂) = φ₂ ⟨x, hx₂⟩ := Subtype.ext hy
    calc ((φ₁.trans ψ₁) ⟨x, hx₁⟩ : F) = ψ₁ ⟨(φ₁ ⟨x, hx₁⟩ : E), (φ₁ ⟨x, hx₁⟩).2⟩ := rfl
      _ = ψ₂ ⟨(φ₁ ⟨x, hx₁⟩ : E), hmem⟩ := g₁ _ _ hmem
      _ = ψ₂ (φ₂ ⟨x, hx₂⟩) := by rw [hb]
      _ = ((φ₂.trans ψ₂) ⟨x, hx₂⟩ : F) := rfl
  · intro z hz₁ hz₂
    have hy : (ψ₁.symm ⟨z, hz₁⟩ : E) = ψ₂.symm ⟨z, hz₂⟩ := g₂ z hz₁ hz₂
    have hmem : (ψ₁.symm ⟨z, hz₁⟩ : E) ∈ K₂ := hy ▸ (ψ₂.symm ⟨z, hz₂⟩).2
    have hb : (⟨(ψ₁.symm ⟨z, hz₁⟩ : E), hmem⟩ : ↥K₂) = ψ₂.symm ⟨z, hz₂⟩ := Subtype.ext hy
    show ((φ₁.symm (ψ₁.symm ⟨z, hz₁⟩) : ↥H₁) : D) = φ₂.symm (ψ₂.symm ⟨z, hz₂⟩)
    calc ((φ₁.symm (ψ₁.symm ⟨z, hz₁⟩) : ↥H₁) : D)
        = φ₁.symm ⟨(ψ₁.symm ⟨z, hz₁⟩ : E), (ψ₁.symm ⟨z, hz₁⟩).2⟩ := rfl
      _ = ((φ₂.symm ⟨(ψ₁.symm ⟨z, hz₁⟩ : E), hmem⟩ : ↥H₂) : D) := h₂ _ _ hmem
      _ = ((φ₂.symm (ψ₂.symm ⟨z, hz₂⟩) : ↥H₂) : D) := by rw [hb]

theorem isAmalgamIso_subgroupOf {I₁ I₂ K : Subgroup E} (h₁ : I₁ ≤ K) (h₂ : I₂ ≤ K) :
    IsAmalgamIso (I₁.subgroupOf K) (I₂.subgroupOf K) I₁ I₂ :=
  ⟨Subgroup.subgroupOfEquivOfLe h₁, Subgroup.subgroupOfEquivOfLe h₂, fun _ _ _ => rfl,
    fun _ _ _ => rfl⟩

variable {H₁ H₂ : Subgroup D} {K₁ K₂ : Subgroup E}

theorem centerOf_inf_le_centralizer_left_imp (h : IsAmalgamIso H₁ H₂ K₁ K₂)
    (hH : centerOf (H₁ ⊓ H₂) ≤ Subgroup.centralizer (H₁ : Set D)) :
    centerOf (K₁ ⊓ K₂) ≤ Subgroup.centralizer (K₁ : Set E) := by
  obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
  intro y hy
  obtain ⟨hyT, hyc⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨hy₁, hy₂⟩ := Subgroup.mem_inf.mp hyT
  have hx₂ : ((φ₁.symm ⟨y, hy₁⟩ : ↥H₁) : D) ∈ H₂ := by
    rw [h₂ y hy₁ hy₂]
    exact (φ₂.symm ⟨y, hy₂⟩).2
  have hxT : ((φ₁.symm ⟨y, hy₁⟩ : ↥H₁) : D) ∈ centerOf (H₁ ⊓ H₂) := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨(φ₁.symm ⟨y, hy₁⟩).2, hx₂⟩, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨ht₁, ht₂⟩ := Subgroup.mem_inf.mp ht
    have ha₂ : ((φ₁ ⟨t, ht₁⟩ : ↥K₁) : E) ∈ K₂ := by
      rw [h₁ t ht₁ ht₂]
      exact (φ₂ ⟨t, ht₂⟩).2
    have hcomm := Subgroup.mem_centralizer_iff.mp hyc _
      (Subgroup.mem_inf.mpr ⟨(φ₁ ⟨t, ht₁⟩).2, ha₂⟩)
    have h3 : φ₁ ⟨t, ht₁⟩ * ⟨y, hy₁⟩ = ⟨y, hy₁⟩ * φ₁ ⟨t, ht₁⟩ := Subtype.ext hcomm
    have h4 := congrArg (fun z => ((φ₁.symm z : ↥H₁) : D)) h3
    simpa using h4
  have hxc := Subgroup.mem_centralizer_iff.mp (hH hxT)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h5 := hxc ((φ₁.symm ⟨k, hk⟩ : ↥H₁) : D) (φ₁.symm ⟨k, hk⟩).2
  have h6 : φ₁.symm ⟨k, hk⟩ * φ₁.symm ⟨y, hy₁⟩ = φ₁.symm ⟨y, hy₁⟩ * φ₁.symm ⟨k, hk⟩ :=
    Subtype.ext h5
  have h7 := congrArg (fun z => ((φ₁ z : ↥K₁) : E)) h6
  simpa using h7

theorem centerOf_inf_le_centralizer_left_iff (h : IsAmalgamIso H₁ H₂ K₁ K₂) :
    centerOf (H₁ ⊓ H₂) ≤ Subgroup.centralizer (H₁ : Set D) ↔
      centerOf (K₁ ⊓ K₂) ≤ Subgroup.centralizer (K₁ : Set E) :=
  ⟨centerOf_inf_le_centralizer_left_imp h, centerOf_inf_le_centralizer_left_imp h.symm⟩

theorem centerOf_inf_le_centralizer_right_iff (h : IsAmalgamIso H₁ H₂ K₁ K₂) :
    centerOf (H₁ ⊓ H₂) ≤ Subgroup.centralizer (H₂ : Set D) ↔
      centerOf (K₁ ⊓ K₂) ≤ Subgroup.centralizer (K₂ : Set E) := by
  have := centerOf_inf_le_centralizer_left_iff h.swap
  rwa [inf_comm H₂ H₁, inf_comm K₂ K₁] at this

theorem f112Convention_iff (h : IsAmalgamIso H₁ H₂ K₁ K₂) :
    F112Convention H₁ H₂ ↔ F112Convention K₁ K₂ := by
  unfold F112Convention
  rw [centerOf_inf_le_centralizer_left_iff h, centerOf_inf_le_centralizer_right_iff h]

theorem nonempty_equiv_triple_of_amalgamIso {A B C : Type*} [Group A] [Group B] [Group C]
    (h : IsAmalgamIso H₁ H₂ K₁ K₂)
    (hK : Nonempty (↥K₁ ≃* A) ∧ Nonempty (↥(K₁ ⊓ K₂) ≃* B) ∧ Nonempty (↥K₂ ≃* C)) :
    Nonempty (↥H₁ ≃* A) ∧ Nonempty (↥(H₁ ⊓ H₂) ≃* B) ∧ Nonempty (↥H₂ ≃* C) := by
  obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
  obtain ⟨⟨a⟩, ⟨b⟩, ⟨c⟩⟩ := hK
  exact ⟨⟨φ₁.trans a⟩, ⟨(infMulEquivOfAmalgamIso φ₁ φ₂ h₁ h₂).trans b⟩, ⟨φ₂.trans c⟩⟩

theorem IsYAmalgam.of_amalgamIso {IsY : ∀ (W : Type) [Group W], Prop}
    (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsYAmalgam IsY K₁ K₂) : IsYAmalgam IsY H₁ H₂ := by
  obtain ⟨W, hW, hF, L₁, L₂, hY, hL, hiso⟩ := hK
  exact ⟨W, hW, hF, L₁, L₂, hY, hL, h.trans hiso⟩

theorem IsGoldCaseI.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseI K₁ K₂) :
    IsGoldCaseI H₁ H₂ :=
  nonempty_equiv_triple_of_amalgamIso h hK

theorem IsGoldCaseII.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseII K₁ K₂) :
    IsGoldCaseII H₁ H₂ :=
  nonempty_equiv_triple_of_amalgamIso h hK

theorem IsGoldCaseIII.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseIII K₁ K₂) :
    IsGoldCaseIII H₁ H₂ :=
  nonempty_equiv_triple_of_amalgamIso h hK

theorem IsGoldCaseV.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseV K₁ K₂) :
    IsGoldCaseV H₁ H₂ :=
  nonempty_equiv_triple_of_amalgamIso h hK

theorem IsGoldCaseIV.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseIV K₁ K₂) :
    IsGoldCaseIV H₁ H₂ := by
  obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
  obtain ⟨⟨a⟩, ⟨b⟩, hc⟩ := hK
  exact ⟨⟨φ₁.trans a⟩, ⟨(infMulEquivOfAmalgamIso φ₁ φ₂ h₁ h₂).trans b⟩,
    isExtensionOf_of_mulEquiv φ₂ hc⟩

theorem IsGoldCaseL32.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseL32 K₁ K₂) :
    IsGoldCaseL32 H₁ H₂ := by
  obtain ⟨hY, hF, ⟨a⟩, ⟨b⟩⟩ := hK
  refine ⟨hY.of_amalgamIso h, (f112Convention_iff h).mpr hF, ?_, ?_⟩
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact ⟨φ₁.trans a⟩
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact ⟨φ₂.trans b⟩

theorem IsGoldCaseSp42.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseSp42 K₁ K₂) :
    IsGoldCaseSp42 H₁ H₂ := by
  obtain ⟨hY, hF, ⟨a⟩, ⟨b⟩⟩ := hK
  refine ⟨hY.of_amalgamIso h, (f112Convention_iff h).mpr hF, ?_, ?_⟩
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact ⟨φ₁.trans a⟩
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact ⟨φ₂.trans b⟩

theorem IsGoldCaseG22.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseG22 K₁ K₂) :
    IsGoldCaseG22 H₁ H₂ := by
  obtain ⟨hY, hF, hq₁, hq₂, hR, hc⟩ := hK
  refine ⟨hY.of_amalgamIso h, (f112Convention_iff h).mpr hF, ?_, ?_, ?_, ?_⟩
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact quotientPCoreIsL22_of_mulEquiv φ₁.symm hq₁
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact quotientPCoreIsL22_of_mulEquiv φ₂.symm hq₂
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact isSpecialTwoOnePlusFour_of_mulEquiv (pCoreOfCongr φ₁) hR
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact (Nat.card_congr (pCoreOfCongr φ₂).toEquiv).trans hc

theorem IsGoldCaseG22Prime.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂)
    (hK : IsGoldCaseG22Prime K₁ K₂) : IsGoldCaseG22Prime H₁ H₂ := by
  obtain ⟨hY, hF, hq₁, hq₂, hR, ⟨b⟩⟩ := hK
  refine ⟨hY.of_amalgamIso h, (f112Convention_iff h).mpr hF, ?_, ?_, ?_, ?_⟩
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact quotientPCoreIsL22_of_mulEquiv φ₁.symm hq₁
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact quotientPCoreIsL22_of_mulEquiv φ₂.symm hq₂
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact isCentralProduct₂_of_mulEquiv (pCoreOfCongr φ₁) hR
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact ⟨(pCoreOfCongr φ₂).trans b⟩

theorem IsGoldCaseM12.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseM12 K₁ K₂) :
    IsGoldCaseM12 H₁ H₂ := by
  obtain ⟨hY, hF, hq₁, hq₂, hR, hc⟩ := hK
  refine ⟨hY.of_amalgamIso h, (f112Convention_iff h).mpr hF, ?_, ?_, ?_, ?_⟩
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact quotientPCoreIsL22_of_mulEquiv φ₁.symm hq₁
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact quotientPCoreIsL22_of_mulEquiv φ₂.symm hq₂
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact isCentralProduct₂_of_mulEquiv (pCoreOfCongr φ₁) hR
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact (Nat.card_congr (pCoreOfCongr φ₂).toEquiv).trans hc

theorem IsGoldCaseAutM12Cat.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂)
    (hK : IsGoldCaseAutM12Cat K₁ K₂) : IsGoldCaseAutM12Cat H₁ H₂ := by
  obtain ⟨hY, hF, hq₁, hq₂, hext, hc₁, hz, hc₂⟩ := hK
  refine ⟨hY.of_amalgamIso h, (f112Convention_iff h).mpr hF, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact quotientPCoreIsL22_of_mulEquiv φ₁.symm hq₁
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact quotientPCoreIsL22_of_mulEquiv φ₂.symm hq₂
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact isExtensionWith_centralProduct_of_mulEquiv φ₁ hext
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact (Nat.card_congr (pCoreOfCongr φ₁).toEquiv).trans hc₁
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact (card_centerOf_eq (pCoreOfCongr φ₁)).trans hz
  · obtain ⟨φ₁, φ₂, h₁, h₂⟩ := h
    exact (Nat.card_congr (pCoreOfCongr φ₂).toEquiv).trans hc₂

theorem IsGoldCaseVICat.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseVICat K₁ K₂) :
    IsGoldCaseVICat H₁ H₂ := by
  rcases hK with hK | hK | hK | hK | hK | hK
  · exact Or.inl (IsGoldCaseL32.of_amalgamIso h hK)
  · exact Or.inr (Or.inl (IsGoldCaseSp42.of_amalgamIso h hK))
  · exact Or.inr (Or.inr (Or.inl (IsGoldCaseG22.of_amalgamIso h hK)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (IsGoldCaseG22Prime.of_amalgamIso h hK))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsGoldCaseM12.of_amalgamIso h hK)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (IsGoldCaseAutM12Cat.of_amalgamIso h hK)))))

theorem IsGoldCaseOrientedCat.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂)
    (hK : IsGoldCaseOrientedCat K₁ K₂) : IsGoldCaseOrientedCat H₁ H₂ := by
  rcases hK with hK | hK | hK | hK | hK | hK
  · exact Or.inl (IsGoldCaseI.of_amalgamIso h hK)
  · exact Or.inr (Or.inl (IsGoldCaseII.of_amalgamIso h hK))
  · exact Or.inr (Or.inr (Or.inl (IsGoldCaseIII.of_amalgamIso h hK)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (IsGoldCaseIV.of_amalgamIso h hK))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (IsGoldCaseV.of_amalgamIso h hK)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (IsGoldCaseVICat.of_amalgamIso h hK)))))

theorem IsGoldCaseCat.of_amalgamIso (h : IsAmalgamIso H₁ H₂ K₁ K₂) (hK : IsGoldCaseCat K₁ K₂) :
    IsGoldCaseCat H₁ H₂ := by
  rcases hK with hK | hK
  · exact Or.inl (IsGoldCaseOrientedCat.of_amalgamIso h hK)
  · exact Or.inr (IsGoldCaseOrientedCat.of_amalgamIso h.swap hK)

theorem IsGoldCaseCat.of_subgroupOf {I₁ I₂ K : Subgroup E} (h₁ : I₁ ≤ K) (h₂ : I₂ ≤ K)
    (h : IsGoldCaseCat (I₁.subgroupOf K) (I₂.subgroupOf K)) : IsGoldCaseCat I₁ I₂ :=
  IsGoldCaseCat.of_amalgamIso (isAmalgamIso_subgroupOf h₁ h₂).symm h

end AmalgamIso

section CardBound

variable {D : Type*} [Group D] {H₁ H₂ : Subgroup D}

theorem IsGoldCaseOrientedCat.card_inf_le (hc₁ : Nat.card ↥H₁ = 3 * Nat.card ↥(H₁ ⊓ H₂))
    (hc₂ : Nat.card ↥H₂ = 3 * Nat.card ↥(H₁ ⊓ H₂))
    (hd₂ : Nat.card ↥H₂ = 6 * Nat.card ↥(pCoreOf 2 H₂)) (h : IsGoldCaseOrientedCat H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) ≤ 2 ^ 7 := by
  rcases h with h | h | h | h | h | h
  · rw [h.card_inf]; norm_num
  · rw [h.card_inf]; norm_num
  · rw [h.card_inf]; norm_num
  · rw [h.card_inf]; norm_num
  · rw [h.card_inf]; norm_num
  · rcases h with h | h | h | h | h | h
    · obtain ⟨-, -, ⟨e⟩, -⟩ := h
      have h1 := hc₁
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card] at h1
      change 24 = _ at h1
      omega
    · obtain ⟨-, -, ⟨e⟩, -⟩ := h
      have h1 := hc₁
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card] at h1
      change 48 = _ at h1
      omega
    · rw [h.2.2.2.2.2] at hd₂
      omega
    · obtain ⟨-, -, -, -, -, ⟨e⟩⟩ := h
      have h3 : Nat.card (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) = 16 := by
        rw [Nat.card_eq_fintype_card]; rfl
      rw [Nat.card_congr e.toEquiv, h3] at hd₂
      omega
    · rw [h.2.2.2.2.2] at hd₂
      omega
    · rw [h.2.2.2.2.2.2.2] at hd₂
      omega

theorem IsGoldCaseCat.card_inf_le (hc₁ : Nat.card ↥H₁ = 3 * Nat.card ↥(H₁ ⊓ H₂))
    (hc₂ : Nat.card ↥H₂ = 3 * Nat.card ↥(H₁ ⊓ H₂))
    (hd₁ : Nat.card ↥H₁ = 6 * Nat.card ↥(pCoreOf 2 H₁))
    (hd₂ : Nat.card ↥H₂ = 6 * Nat.card ↥(pCoreOf 2 H₂)) (h : IsGoldCaseCat H₁ H₂) :
    Nat.card ↥(H₁ ⊓ H₂) ≤ 2 ^ 7 := by
  rcases h with h | h
  · exact h.card_inf_le hc₁ hc₂ hd₂
  · have hc₁' : Nat.card ↥H₁ = 3 * Nat.card ↥(H₂ ⊓ H₁) := by rwa [inf_comm]
    have hc₂' : Nat.card ↥H₂ = 3 * Nat.card ↥(H₂ ⊓ H₁) := by rwa [inf_comm]
    have := IsGoldCaseOrientedCat.card_inf_le hc₂' hc₁' hd₁ h
    rwa [inf_comm] at this

theorem card_inf_le_two_pow_seven {G : Type*} [Group G] [Finite G] {I₁ I₂ : Subgroup G}
    (hp : IsGoldschmidtVPair I₁ I₂) (h : IsGoldCaseCat I₁ I₂) :
    Nat.card ↥(I₁ ⊓ I₂) ≤ 2 ^ 7 :=
  h.card_inf_le hp.card_left hp.card_right (GoldPair.card_eq_six_mul_pCoreOf hp.quotient₁)
    (GoldPair.card_eq_six_mul_pCoreOf hp.quotient₂)

end CardBound

@[expose] def GoldschmidtCharTwoLargePair : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (I₁ I₂ : Subgroup G), IsGoldschmidtVPair I₁ I₂ →
    CharTwo I₁ → CharTwo I₂ → 32 ≤ Nat.card ↥(I₁ ⊓ I₂) → IsGoldCaseCat I₁ I₂

@[expose] def GoldschmidtCharTwoLargeV : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (G₁ G₂ : Subgroup D), IsGoldschmidtVAmalgam G₁ G₂ →
    CharTwo G₁ → CharTwo G₂ → 32 ≤ Nat.card ↥(G₁ ⊓ G₂) → IsGoldCaseCat G₁ G₂

namespace GoldPair

theorem le_sixteen_or_thirtytwo_of_pow {n k : ℕ} (h : n = 2 ^ k) : n ≤ 16 ∨ 32 ≤ n := by
  subst h
  rcases Nat.lt_or_ge k 5 with hk | hk
  · left
    calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 := by norm_num
  · right
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

theorem charTwo_subgroupOf_iff {E : Type*} [Group E] {I K : Subgroup E} (h : I ≤ K) :
    CharTwo (I.subgroupOf K) ↔ CharTwo I :=
  ⟨charTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h),
    charTwo_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h).symm⟩

theorem card_inf_subgroupOf {E : Type*} [Group E] {I₁ I₂ K : Subgroup E} (h₁ : I₁ ≤ K) :
    Nat.card ↥(I₁.subgroupOf K ⊓ I₂.subgroupOf K) = Nat.card ↥(I₁ ⊓ I₂) := by
  rw [← subgroupOf_inf]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h₁)).toEquiv

end GoldPair

theorem goldschmidtCharTwoLargePair_of_v (h : GoldschmidtCharTwoLargeV.{u}) :
    GoldschmidtCharTwoLargePair.{u} := by
  intro G _ _ I₁ I₂ hp c₁ c₂ hcard
  have hI₁ : I₁ ≤ I₁ ⊔ I₂ := le_sup_left
  have hI₂ : I₂ ≤ I₁ ⊔ I₂ := le_sup_right
  refine IsGoldCaseCat.of_subgroupOf hI₁ hI₂ (h _ _ _ hp.restrict ?_ ?_ ?_)
  · exact (GoldPair.charTwo_subgroupOf_iff hI₁).mpr c₁
  · exact (GoldPair.charTwo_subgroupOf_iff hI₂).mpr c₂
  · rwa [GoldPair.card_inf_subgroupOf hI₁]

theorem card_inf_le_two_pow_seven_of_charTwoLargePair (h : GoldschmidtCharTwoLargePair.{u})
    {G : Type u} [Group G] [Finite G] {I₁ I₂ : Subgroup G} (hp : IsGoldschmidtVPair I₁ I₂)
    (c₁ : CharTwo I₁) (c₂ : CharTwo I₂) : Nat.card ↥(I₁ ⊓ I₂) ≤ 2 ^ 7 := by
  obtain ⟨k, hk⟩ := hp.isPGroup_inf.exists_card_eq
  rcases GoldPair.le_sixteen_or_thirtytwo_of_pow hk with h16 | h32
  · exact h16.trans (by norm_num)
  · exact card_inf_le_two_pow_seven hp (h G I₁ I₂ hp c₁ c₂ h32)

end F6

end CFSG.Quasithin
