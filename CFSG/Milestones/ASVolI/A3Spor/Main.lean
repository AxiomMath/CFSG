module

public import CFSG.Milestones.ASVolI.A3Spor.Mathieu
public import CFSG.Milestones.ASVolI.A3Spor.Spor
public import CFSG.Milestones.ASVolI.A3Spor.J4
public import CFSG.Milestones.ASVolI.A3Spor.J1
public import CFSG.Milestones.ASVolI.A3Spor.Out

public section

namespace CFSG.ASVolI

open CFSG.Blueprint

theorem burnsideA315s_mem_of_allInner {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B)
    (hall : ∀ α : MulAut ↥L, ∃ l : ↥L, α = MulAut.conj l) (g : G) : g ∈ L := by
  haveI := burnsideA315x_normal h
  obtain ⟨l, hl⟩ := hall (MulAut.conjNormal (H := L) g)
  have hc : (l : G)⁻¹ * g ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : G)) hl
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at h1
    calc x * ((l : G)⁻¹ * g) = (l : G)⁻¹ * ((l : G) * x * (l : G)⁻¹) * g := by group
      _ = (l : G)⁻¹ * (g * x * g⁻¹) * g := by rw [← h1]
      _ = (l : G)⁻¹ * g * x := by group
  rw [burnsideA315x_centralizer_eq_bot h, Subgroup.mem_bot] at hc
  have : g = (l : G) := by
    have := congrArg (fun y => (l : G) * y) hc
    simpa using this
  rw [this]
  exact l.2

theorem burnsideA315s_le_normalizer_of_map {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {S B : Subgroup X}
    (h : B.map e.toMonoidHom ≤ Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup Y) : Set Y)) :
    B ≤ Subgroup.normalizer (S : Set X) := by
  intro b hb
  have hb' := h ⟨b, hb, rfl⟩
  rw [Subgroup.mem_normalizer_iff] at hb' ⊢
  intro x
  have := hb' (e x)
  have h1 : e x ∈ S.map e.toMonoidHom ↔ x ∈ S := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := e.injective hyx
      exact this ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have h2 : e.toMonoidHom b * e x * (e.toMonoidHom b)⁻¹ ∈ S.map e.toMonoidHom ↔
      b * x * b⁻¹ ∈ S := by
    have : e.toMonoidHom b * e x * (e.toMonoidHom b)⁻¹ = e (b * x * b⁻¹) := by simp
    rw [this]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = b * x * b⁻¹ := e.injective hyx
      exact this ▸ hy
    · intro hx
      exact ⟨_, hx, rfl⟩
  rw [← h1, ← h2]
  exact this

theorem burnsideA315s_false_of {X : Type} [Group X] {G : Type} [Group G] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) (e : ↥L ≃* X)
    (hout : ∀ α : MulAut ↥L, Odd (orderOf α) → ∃ l : ↥L, α = MulAut.conj l)
    (hno : ∀ S B : Subgroup X, ¬ burnsideA315x_Config X S B) : False := by
  obtain ⟨-, hcfg⟩ := burnsideA315x_config_of_hyp h hout
  exact hno _ _ (hcfg.map e)

theorem burnsideA315s_case4_J1
    {G : Type} [Group G] {L T B : Subgroup G} (h : CFSG.Quasithin.A315Hyp L T B)
    (e : ↥L ≃* NativeSporadic.Carrier .J1) : CFSG.Quasithin.A315Case4 L T B := by
  haveI := h.sqtk.finite
  haveI := burnsideA315x_normal h
  have hall := burnsideA315s_allInner_J1 e
  have hGL : ∀ g : G, g ∈ L := burnsideA315s_mem_of_allInner h hall
  obtain ⟨hBL, hcfg⟩ := burnsideA315x_config_of_hyp h fun α _ => hall α
  have e₂ : NativeSporadic.Carrier .J1 ≃* ↥CFSG.Sporadic.J1.J := CFSG.Sporadic.J1.nativeEquiv
  let e' : ↥L ≃* ↥CFSG.Sporadic.J1.J := e.trans e₂
  obtain ⟨h7, hN⟩ := burnsideA315s_config_J1Grp (hcfg.map e')
  have hN' := burnsideA315s_le_normalizer_of_map e' hN
  refine ⟨⟨e⟩, fun b hb => ⟨hBL hb, ?_⟩, ?_⟩
  · have hb' : (⟨b, hBL hb⟩ : ↥L) ∈ Subgroup.normalizer
        (((T ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) :=
      hN' (Subgroup.mem_subgroupOf.2 hb)
    show b ∈ Subgroup.normalizer (T : Set G)
    rw [Subgroup.mem_normalizer_iff] at hb' ⊢
    intro x
    have := hb' ⟨x, hGL x⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, InvMemClass.coe_inv,
      Subgroup.mem_inf] at this
    constructor
    · intro hx
      exact (this.1 ⟨hx, hGL x⟩).1
    · intro hx
      exact (this.2 ⟨hx, hGL _⟩).1
  · rw [Subgroup.card_map_of_injective e'.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv] at h7
    exact h7

theorem burnsideA315s_sporadicFact :
    CFSG.Quasithin.A315SporadicFact := by
  intro G _ L T B h hL
  haveI := h.sqtk.finite
  obtain ⟨s, hs, ⟨e⟩⟩ := hL
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_M11 e)
      burnsideA315s_noConfig_M11).elim
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_M12 e)
      burnsideA315s_noConfig_M12).elim
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_M22 e)
      burnsideA315s_noConfig_M22).elim
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_M23 e)
      burnsideA315s_noConfig_M23).elim
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_M24 e)
      burnsideA315s_noConfig_M24).elim
  · exact burnsideA315s_case4_J1 h e
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_J2 e)
      burnsideA315s_noConfig_J2).elim
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_J4 e)
      burnsideA315s_noConfig_J4).elim
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_HS e)
      burnsideA315s_noConfig_HS).elim
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_He e)
      burnsideA315s_noConfig_He).elim
  · exact (burnsideA315s_false_of h e (burnsideA315s_oddInner_Ru e)
      burnsideA315s_noConfig_Ru).elim

end CFSG.ASVolI
