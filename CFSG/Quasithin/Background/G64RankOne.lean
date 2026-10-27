module

public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin

@[expose] def ModelTransvec (D : FFModel) (γ : D.Gam) : Prop :=
  ∃ m₁ ∈ D.sec, D.act γ m₁ * m₁⁻¹ ∉ D.ker ∧ ∀ m ∈ D.sec,
    D.act γ m * m⁻¹ ∈ D.ker ∨ D.act γ m * m⁻¹ * (D.act γ m₁ * m₁⁻¹)⁻¹ ∈ D.ker

variable {V : Type*} [CommGroup V]

@[expose] def IsTransvecSec (h : MulAut V) (U Z : Subgroup V) : Prop :=
  (∃ u ∈ U, h u * u⁻¹ ∉ Z) ∧ ∃ w : V, ∀ u ∈ U, h u * u⁻¹ ∈ Z ⊔ Subgroup.zpowers w

theorem isTransvecSec_of_card_two {h : MulAut V} (hcard : Nat.card (commV (Subgroup.zpowers h)) = 2)
    {U Z : Subgroup V} (hmove : ∃ u ∈ U, h u * u⁻¹ ∉ Z) : IsTransvecSec h U Z := by
  refine ⟨hmove, ?_⟩
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ commV (Subgroup.zpowers h), w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : commV (Subgroup.zpowers h) = ⊥ := eq_bot_iff.2 fun y hy => hcon y hy
    rw [this, Subgroup.card_bot] at hcard
    omega
  refine ⟨w, fun u _ => ?_⟩
  rcases eq_one_or_eq_of_card_two hcard hw hw1 (G6.mem_commV_of_mem (Subgroup.mem_zpowers h) u)
    with h1 | h1
  · rw [h1]
    exact Subgroup.one_mem _
  · rw [h1]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)

theorem RealizesVia.isTransvecOn (hV2 : ∀ v : V, v ^ 2 = 1) {D : FFModel} {H : Subgroup (MulAut V)}
    {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) {γ : D.Gam}
    (ht : IsTransvecSec ((π γ : ↥H) : MulAut V) U Z) : ModelTransvec D γ := by
  obtain ⟨⟨u₁, hu₁, hmv⟩, w, hw⟩ := ht
  obtain ⟨_, _, _, hHU, _, hsec, _, β, hβs, hβk, hβe⟩ := h
  set g : MulAut V := ((π γ : ↥H) : MulAut V) with hg
  have hgU : ∀ u ∈ U, g u ∈ U := fun u hu => hHU (π γ) u hu
  have hβc : ∀ (u : ↥U) (m : ↥D.sec), β u = QuotientGroup.mk m →
      β ⟨g u * (u : V)⁻¹, U.mul_mem (hgU u u.2) (U.inv_mem u.2)⟩ =
        QuotientGroup.mk (⟨D.act γ (m : D.Amb), hsec γ m m.2⟩ : ↥D.sec) *
          (QuotientGroup.mk m)⁻¹ := by
    intro u m hum
    have h1 := hβe γ u m (hgU u u.2) (hsec γ m m.2) hum
    calc β ⟨g u * (u : V)⁻¹, _⟩ = β (⟨g u, hgU u u.2⟩ * u⁻¹) := rfl
      _ = β ⟨g u, hgU u u.2⟩ * (β u)⁻¹ := by rw [map_mul, map_inv]
      _ = _ := by rw [h1, hum]
  obtain ⟨m₁, hm₁⟩ := QuotientGroup.mk_surjective (β ⟨u₁, hu₁⟩)
  have hker : ∀ x y : ↥D.sec, (QuotientGroup.mk x : D.Mod) = QuotientGroup.mk y ↔
      (y : D.Amb) * (x : D.Amb)⁻¹ ∈ D.ker := by
    intro x y
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [mul_comm]
  have hq1 : ∀ x : ↥D.sec, (QuotientGroup.mk x : D.Mod) = 1 ↔ (x : D.Amb) ∈ D.ker := by
    intro x
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : ∀ (u : ↥U) (m : ↥D.sec), β u = QuotientGroup.mk m →
      (QuotientGroup.mk (⟨D.act γ (m : D.Amb) * (m : D.Amb)⁻¹,
        D.sec.mul_mem (hsec γ m m.2) (D.sec.inv_mem m.2)⟩ : ↥D.sec) : D.Mod) =
        β ⟨g u * (u : V)⁻¹, U.mul_mem (hgU u u.2) (U.inv_mem u.2)⟩ := by
    intro u m hum
    rw [hβc u m hum, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  refine ⟨m₁, m₁.2, ?_, fun m hm => ?_⟩
  · intro hk
    apply hmv
    have h1 := hcomm ⟨u₁, hu₁⟩ m₁ hm₁.symm
    rw [(hq1 _).2 hk] at h1
    exact (hβk _).1 h1.symm
  · obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
    have hcu := hcomm u ⟨m, hm⟩ hu
    have hcu₁ := hcomm ⟨u₁, hu₁⟩ m₁ hm₁.symm
    obtain ⟨z, hz, x, hx, hzx⟩ := Subgroup.mem_sup.1 (hw u u.2)
    obtain ⟨z₁, hz₁, x₁, hx₁, hzx₁⟩ := Subgroup.mem_sup.1 (hw u₁ hu₁)
    rcases eq_one_or_eq_of_mem_zpowers' (hV2 w) hx with hx' | hx'
    · left
      have hZ : g u * (u : V)⁻¹ ∈ Z := by rw [← hzx, hx', mul_one]; exact hz
      have h1 := (hβk ⟨g u * (u : V)⁻¹, U.mul_mem (hgU u u.2) (U.inv_mem u.2)⟩).2 hZ
      rw [← hcu] at h1
      exact (hq1 _).1 h1
    · right
      rcases eq_one_or_eq_of_mem_zpowers' (hV2 w) hx₁ with hx₁' | hx₁'
      · exfalso
        apply hmv
        rw [← hzx₁, hx₁', mul_one]
        exact hz₁
      · have hdiff : (⟨g u * (u : V)⁻¹, U.mul_mem (hgU u u.2) (U.inv_mem u.2)⟩ *
            (⟨g u₁ * u₁⁻¹, U.mul_mem (hgU u₁ hu₁) (U.inv_mem hu₁)⟩ : ↥U)⁻¹ : ↥U).1 ∈ Z := by
          show (g u * (u : V)⁻¹) * (g u₁ * u₁⁻¹)⁻¹ ∈ Z
          rw [← hzx, ← hzx₁, hx', hx₁']
          have : z * w * (z₁ * w)⁻¹ = z * z₁⁻¹ := by group
          rw [this]
          exact Z.mul_mem hz (Z.inv_mem hz₁)
        have h0 := (hβk _).2 hdiff
        rw [map_mul, map_inv, mul_inv_eq_one, ← hcu, ← hcu₁] at h0
        exact (hker _ _).1 h0.symm
end CFSG.Quasithin.G64
