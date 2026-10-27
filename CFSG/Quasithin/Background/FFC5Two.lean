module

public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

section Two

variable {V : Type} [CommGroup V]

@[expose] def B510Offenders (G G₁ : Subgroup (MulAut V)) : Prop :=
  ∀ D : Subgroup (MulAut V), IsFFStarOffender G D →
    ∀ d ∈ D, ∃ g ∈ G₁, ∀ w ∈ commV G₁, d w = g w

structure B510Data (G G₁ G₂ : Subgroup (MulAut V)) : Prop where
  G₁_le : G₁ ≤ G
  G₂_le : G₂ ≤ G
  sup : G₁ ⊔ G₂ = G
  inf : G₁ ⊓ G₂ = ⊥
  comm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a
  triv₁ : ∀ b ∈ G₂, ∀ v ∈ commV G₁, b v = v

theorem b510_two [Finite V] {G G₁ : Subgroup (MulAut V)} (hJ : G = ffJ G) (hG₁G : G₁ ≤ G)
    (hfaith : ∀ x ∈ G₁, (∀ w ∈ commV G₁, x w = w) → x = 1)
    (hcent : ∀ c ∈ G, (∀ w ∈ commV G₁, c w = w) → ∀ x ∈ G₁, c * x = x * c)
    (hoff : B510Offenders G G₁) : B510Data G G₁ (G ⊓ centSub (commV G₁)) := by
  refine ⟨hG₁G, inf_le_left, ?_, ?_, ?_, ?_⟩
  · refine le_antisymm (sup_le hG₁G inf_le_left) ?_
    conv_lhs => rw [hJ]
    refine iSup₂_le fun D hD d hd => ?_
    obtain ⟨g, hg, hgd⟩ := hoff D hD d hd
    have hgG : g ∈ G := hG₁G hg
    have hdG : d ∈ G := hD.1 hd
    have h1 : g⁻¹ * d ∈ G ⊓ centSub (commV G₁) := by
      refine ⟨G.mul_mem (G.inv_mem hgG) hdG, fun w hw => ?_⟩
      show g⁻¹ (d w) = w
      rw [hgd w hw]
      simp
    have : d = g * (g⁻¹ * d) := by simp
    rw [this]
    exact Subgroup.mul_mem_sup hg h1
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2, hx3⟩
    exact Subgroup.mem_bot.2 (hfaith x hx1 hx3)
  · intro a ha b hb
    exact (hcent b hb.1 hb.2 a ha).symm
  · intro b hb v hv
    exact hb.2 v hv

theorem faithful_on_of_realizes {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    ∀ x ∈ H, (∀ u ∈ U, x u = u) → x = 1 := by
  intro x hx hxu
  obtain ⟨hπs, -, -, hHU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  obtain ⟨γ, hγ⟩ := hπs ⟨x, hx⟩
  have hγx : ((π γ : ↥H) : MulAut V) = x := congrArg Subtype.val hγ
  have hγ1 : γ = 1 := by
    apply hD
    intro m hm
    obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
    have hact : D.act γ m ∈ D.sec := hsec γ m hm
    have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
    have h1 := hβe γ u ⟨m, hm⟩ hu' hact hu
    have h2' : ((π γ : ↥H) : MulAut V) (u : V) = (u : V) := by rw [hγx]; exact hxu u u.2
    have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext h2'
    rw [h2, hu] at h1
    have h3 := QuotientGroup.eq.mp h1
    have h4 : m⁻¹ * D.act γ m ∈ D.ker := h3
    rw [mul_comm]
    exact h4
  rw [← hγx, hγ1, map_one]
  rfl

end Two

end FFC

end CFSG.Quasithin
