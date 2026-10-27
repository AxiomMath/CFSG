module

public import CFSG.Quasithin.Background.C124YLTrans

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open

variable {V : Type*} [CommGroup V] {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
  {π : D.Gam →* ↥H}

theorem coordQuot_of_realizes (h : D.RealizesVia H U Z π) :
    ∃ β : ↥U →* (↥D.sec ⧸ D.ker.subgroupOf D.sec), IsCoord U Z β ∧
      ∀ (γ : D.Gam) (u : ↥U) (m : ↥D.sec) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U)
        (hm : D.act γ (m : D.Amb) ∈ D.sec), β u = QuotientGroup.mk m →
          β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩ := by
  obtain ⟨-, hZU, -, -, -, -, -, β, hβs, hβk, hβ⟩ := h
  exact ⟨β, ⟨hZU, hβs, hβk⟩, hβ⟩

section Fix

variable {β : ↥U →* (↥D.sec ⧸ D.ker.subgroupOf D.sec)} (hc : IsCoord U Z β)
  (hβ : ∀ (γ : D.Gam) (u : ↥U) (m : ↥D.sec) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U)
    (hm : D.act γ (m : D.Amb) ∈ D.sec), β u = QuotientGroup.mk m →
      β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩)
  (hsec : ∀ γ : D.Gam, ∀ m ∈ D.sec, D.act γ m ∈ D.sec)
  (hUst : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U) (hkerle : D.ker ≤ D.sec)

include hc hβ hsec in
theorem comm_mem_iff_model (γ : D.Gam) (u : ↥U) (m : ↥D.sec)
    (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U) (hum : β u = QuotientGroup.mk m) :
    ((((π γ : ↥H) : MulAut V) (u : V)) * (u : V)⁻¹ ∈ Z ↔
      D.act γ (m : D.Amb) * (m : D.Amb)⁻¹ ∈ D.ker) := by
  have h1 := hc.ker (⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ * u⁻¹)
  rw [map_mul, map_inv, mul_inv_eq_one, hβ γ u m hu (hsec γ m m.2) hum, hum,
    QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
  have e1 : (((⟨D.act γ (m : D.Amb), hsec γ m m.2⟩ : ↥D.sec)⁻¹ * m : ↥D.sec) : D.Amb) =
      (D.act γ (m : D.Amb) * (m : D.Amb)⁻¹)⁻¹ := by
    simp [mul_comm]
  rw [e1, inv_mem_iff] at h1
  exact h1.symm

include hc hβ hsec hUst in
theorem mem_fixImg_model (B : Subgroup D.Gam) (m : ↥D.sec) :
    (QuotientGroup.mk m : ↥D.sec ⧸ D.ker.subgroupOf D.sec) ∈
        fixImg U Z β (B.map (H.subtype.comp π)) ↔
      ∀ γ ∈ B, D.act γ (m : D.Amb) * (m : D.Amb)⁻¹ ∈ D.ker := by
  have key : ∀ (γ : D.Gam) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
      β u = QuotientGroup.mk m →
      ((((π γ : ↥H) : MulAut V) (u : V)) * (u : V)⁻¹ ∈ Z ↔
        D.act γ (m : D.Amb) * (m : D.Amb)⁻¹ ∈ D.ker) :=
    fun γ u hu hum => comm_mem_iff_model hc hβ hsec γ u m hu hum
  rw [mem_fixImg]
  constructor
  · rintro ⟨u, hu, hb⟩ γ hγ
    exact (key γ u (hUst _ _ u.2) hu).1 (hb _ (Subgroup.mem_map_of_mem _ hγ))
  · intro hcond
    obtain ⟨u, hu⟩ := hc.surj (QuotientGroup.mk m)
    refine ⟨u, hu, ?_⟩
    rintro b ⟨γ, hγ, rfl⟩
    exact (key γ u (hUst _ _ u.2) hu).2 (hcond γ hγ)

include hc hβ hsec hUst hkerle in
theorem card_fixImg_model [Finite D.Amb] (B : Subgroup D.Gam) :
    Nat.card ↥(fixImg U Z β (B.map (H.subtype.comp π))) * Nat.card ↥D.ker =
      Nat.card {m : D.Amb // m ∈ D.sec ∧ ∀ γ ∈ B, D.act γ m * m⁻¹ ∈ D.ker} := by
  set N : Subgroup ↥D.sec := D.ker.subgroupOf D.sec with hN
  set F := fixImg U Z β (B.map (H.subtype.comp π)) with hF
  set Fx : Subgroup ↥D.sec := F.comap (QuotientGroup.mk' N) with hFx
  have hmem : ∀ m : ↥D.sec, m ∈ Fx ↔ ∀ γ ∈ B, D.act γ (m : D.Amb) * (m : D.Amb)⁻¹ ∈ D.ker :=
    fun m => mem_fixImg_model hc hβ hsec hUst B m
  have hker : (QuotientGroup.mk' N).ker ≤ Fx := by
    intro x hx
    rw [hFx, Subgroup.mem_comap, (QuotientGroup.mk' N).mem_ker.1 hx]
    exact F.one_mem
  have h1 : (QuotientGroup.mk' N).ker.relIndex Fx = Nat.card F := by
    rw [Subgroup.relIndex_ker, hFx, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective N)]
  have h2 := Subgroup.relIndex_mul_card (QuotientGroup.mk' N).ker Fx
  rw [inf_eq_left.2 hker, h1, QuotientGroup.ker_mk'] at h2
  have h3 : Nat.card N = Nat.card ↥D.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hkerle).toEquiv
  rw [h3] at h2
  rw [h2]
  exact Nat.card_congr ⟨fun x => ⟨x.1.1, x.1.2, (hmem x.1).1 x.2⟩,
    fun y => ⟨⟨y.1, y.2.1⟩, (hmem ⟨y.1, y.2.1⟩).2 y.2.2⟩, fun x => rfl, fun y => rfl⟩

end Fix

end CFSG.Quasithin.C124.YL
