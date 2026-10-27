module

public import CFSG.Quasithin.EmptyFaithful.S153E55C
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddAvg

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement Pointwise

namespace S153E55

section Abstract

variable {G : Type*} [Group G]

theorem mem_sup_of_comm {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) {a : G}
    (ha : a ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, x * y = a := by
  have hle : Y ≤ Subgroup.normalizer (X : Set G) := le_sup_right.trans (sup_le_normalizer_left h)
  have e := Subgroup.coe_mul_of_right_le_normalizer_left X Y hle
  have ha' : a ∈ ((X ⊔ Y : Subgroup G) : Set G) := ha
  rw [e] at ha'
  exact ha'

theorem conj_commute_on_center {A P : Subgroup G} (hAP : ∀ a ∈ A, ∀ p ∈ P, a * p = p * a)
    {y y' : G} (hc : y * y' * y⁻¹ * y'⁻¹ ∈ P) (hy : y ∈ Subgroup.normalizer (A : Set G))
    (hy' : y' ∈ Subgroup.normalizer (A : Set G)) {a : G} (ha : a ∈ A) :
    y * (y' * a * y'⁻¹) * y⁻¹ = y' * (y * a * y⁻¹) * y'⁻¹ := by
  have hb : y' * (y * a * y⁻¹) * y'⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hy' _).mp ((Subgroup.mem_normalizer_iff.mp hy a).mp ha)
  have h1 := hAP _ hb _ hc
  have e : y * (y' * a * y'⁻¹) * y⁻¹ = (y * y' * y⁻¹ * y'⁻¹) * (y' * (y * a * y⁻¹) * y'⁻¹) *
      (y * y' * y⁻¹ * y'⁻¹)⁻¹ := by group
  rw [e, ← h1]
  group

theorem sq_eq_one_of_decomp [Finite G] {A V : Subgroup G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : IsPGroup 2 A) (hVA : V ≤ A)
    (hsq : ∀ a ∈ A, a * a ∈ V) (hV2 : ∀ v ∈ V, v * v = 1)
    {y₁ y₂ : G} (hy₂A : y₂ ∈ Subgroup.normalizer (A : Set G)) (ho₂ : Odd (orderOf y₂))
    (hf₁ : ∀ v ∈ V, y₁ * v * y₁⁻¹ = v → v = 1) (hf₂ : ∀ v ∈ V, y₂ * v * y₂⁻¹ = v → v = 1)
    (h3 : ∀ d ∈ ⁅A, Subgroup.zpowers y₂⁆, y₁ * d * y₁⁻¹ * d⁻¹ ∈ V) :
    ∀ a ∈ A, a * a = 1 := by
  intro a ha
  have hAN : Subgroup.zpowers y₂ ≤ Subgroup.normalizer (A : Set G) := Subgroup.zpowers_le.mpr hy₂A
  have hNab : ∀ x y : ↥A, x * y = y * x := fun x y => Subtype.ext (hAab x x.2 y y.2)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers y₂)) (Nat.card A) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hA2
    rw [Nat.card_zpowers, hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr ho₂)
  obtain ⟨hsup, -⟩ := CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp A
    (Subgroup.zpowers y₂) hAN hNab hcop
  have hdA : ∀ d ∈ ⁅A, Subgroup.zpowers y₂⁆, d ∈ A := fun d hd =>
    CFSG.QuasithinUnique.Setup.Layer.commutator_le_left hAN hd
  have hcomm : ∀ x ∈ A ⊓ Subgroup.centralizer (↑(Subgroup.zpowers y₂) : Set G),
      ∀ d ∈ ⁅A, Subgroup.zpowers y₂⁆, x * d = d * x := fun x hx d hd => hAab x hx.1 d (hdA d hd)
  obtain ⟨e, he, d, hd, rfl⟩ := mem_sup_of_comm hcomm (hsup ▸ ha)
  have heA : e ∈ A := he.1
  have hdA' : d ∈ A := hdA d hd
  have h1 : e * e = 1 := by
    have hv : e * e ∈ V := hsq e heA
    refine hf₂ _ hv ?_
    have hyc : y₂ * e * y₂⁻¹ = e := by
      have := Subgroup.mem_centralizer_iff.mp he.2 y₂ (Subgroup.mem_zpowers y₂)
      rw [this]
      group
    calc y₂ * (e * e) * y₂⁻¹ = (y₂ * e * y₂⁻¹) * (y₂ * e * y₂⁻¹) := by group
      _ = e * e := by rw [hyc]
  have h2 : d * d = 1 := by
    have hv : d * d ∈ V := hsq d hdA'
    refine hf₁ _ hv ?_
    have hw : y₁ * d * y₁⁻¹ * d⁻¹ ∈ V := h3 d hd
    have hwA : y₁ * d * y₁⁻¹ * d⁻¹ ∈ A := hVA hw
    have hdw : d * (y₁ * d * y₁⁻¹ * d⁻¹) = (y₁ * d * y₁⁻¹ * d⁻¹) * d := hAab d hdA' _ hwA
    have e2 : (y₁ * d * y₁⁻¹) * (y₁ * d * y₁⁻¹) =
        (y₁ * d * y₁⁻¹ * d⁻¹) * (d * (y₁ * d * y₁⁻¹ * d⁻¹)) * d := by group
    rw [hdw] at e2
    have e3 : y₁ * (d * d) * y₁⁻¹ = (y₁ * d * y₁⁻¹) * (y₁ * d * y₁⁻¹) := by group
    rw [e3, e2]
    calc (y₁ * d * y₁⁻¹ * d⁻¹) * ((y₁ * d * y₁⁻¹ * d⁻¹) * d) * d
        = ((y₁ * d * y₁⁻¹ * d⁻¹) * (y₁ * d * y₁⁻¹ * d⁻¹)) * (d * d) := by group
      _ = d * d := by rw [hV2 _ hw, one_mul]
  calc e * d * (e * d) = e * (d * e) * d := by group
    _ = e * (e * d) * d := by rw [hAab d hdA' e heA]
    _ = (e * e) * (d * d) := by group
    _ = 1 := by rw [h1, h2, one_mul]

theorem normalizer_le_normalizer_centerOf (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer ((centerOf P : Subgroup G) : Set G) :=
  B2F.le_normalizer_inf le_rfl (B2F.normalizer_le_normalizer_centralizer P)

theorem isElemAbelian_centerOf {P : Subgroup G} (h : ∀ a ∈ centerOf P, a * a = 1) :
    IsElemAbelian 2 (centerOf P) :=
  ⟨⟨⟨fun a b => Subtype.ext (Subgroup.mem_centralizer_iff.mp a.2.2 b b.2.1).symm⟩⟩,
    fun x hx => by rw [pow_two]; exact h x hx⟩

theorem mult_sq {s : ℕ} (a : Multiplicative (Fin s → Fin 2 → ZMod 2)) : a * a = 1 := by
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  rw [← ofAdd_toAdd a, ← ofAdd_add]
  have : Multiplicative.toAdd a + Multiplicative.toAdd a = 0 := by
    funext j k
    simp [h2]
  rw [this]
  rfl

theorem sq_mem_of_nat {G : Type} [Group G] {M Si S S₂ : Subgroup G} {s : ℕ} (h : IsSumOfNatSL2ModulesN153 s M Si S S₂) :
    ∀ x ∈ Si, x * x ∈ S₂ := by
  obtain ⟨β, φ, -, -, -, hφk, -⟩ := h
  intro x hx
  have h1 : φ ⟨x, hx⟩ * φ ⟨x, hx⟩ = 1 := mult_sq _
  rw [← map_mul] at h1
  exact (hφk _).1 h1

end Abstract

section Lifts

open CFSG.Quasithin.S153E CFSG.Quasithin.S1417 CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem exists_y12 (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t)
    {N₁ N₂ : Subgroup (MulAut ↥(VZ T M))} {g : G} {s : ℕ} (c : Chain15354 cx N₁ N₂ g s) :
    ∃ y₁ y₂ : G, y₁ ∈ Y153 Mc M ∧ y₂ ∈ Y153 Mc M ∧ Odd (orderOf y₁) ∧ Odd (orderOf y₂) ∧
      (∀ v ∈ VZ T M, y₁ * v * y₁⁻¹ = v → v = 1) ∧ (∀ v ∈ VZ T M, y₂ * v * y₂⁻¹ = v → v = 1) ∧
      y₁ ∈ Ni153 T Mc M V₁ N₁ ∧ y₂ ∈ Ni153 T Mc M V₁ N₂ ∧
      y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ Pgp153 T M V₁ Mc g ∧
      (∀ y ∈ Y153 Mc M, y * y₁ * y⁻¹ * y₁⁻¹ ∈ Pgp153 T M V₁ Mc g ∧
        y * y₂ * y⁻¹ * y₂⁻¹ ∈ Pgp153 T M V₁ Mc g) := by
  have hV := cx.c.hyp.elemAbelian
  have hI := c.h54.one
  have hΩYU := autI_YU_eq cx c.h53one
  obtain ⟨Ω, hΩ, -, hΩeq⟩ := c.h53one.omega
  have hN₁Ω : N₁ ≤ Ω := hΩeq ▸ le_sup_left
  have hN₂Ω : N₂ ≤ Ω := hΩeq ▸ le_sup_right
  have hN₁M : N₁ ≤ autI hV M := fun x hx => ((hΩ x).1 (hN₁Ω hx)).1
  have hN₂M : N₂ ≤ autI hV M := fun x hx => ((hΩ x).1 (hN₂Ω hx)).1
  have hN₁Y : N₁ ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := hΩYU ▸ le_sup_left
  have hN₂Y : N₂ ≤ autI hV (Y153 Mc M ⊔ UH153 T M V₁ Mc) := hΩYU ▸ le_sup_right
  obtain ⟨e₁⟩ := c.h53one.iso₁
  obtain ⟨e₂⟩ := c.h53one.iso₂
  obtain ⟨y₁, hy₁Y, hy₁o, hy₁N, hy₁f⟩ :=
    exists_lift h113 cx hN₁M e₁ (commV_eq_top cx hN₁Y c.h53one.comm₁)
  obtain ⟨y₂, hy₂Y, hy₂o, hy₂N, hy₂f⟩ :=
    exists_lift h113 cx hN₂M e₂ (commV_eq_top cx hN₂Y c.h53one.comm₂)
  have hy₁YU : y₁ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Y_le_YU hy₁Y
  have hy₂YU : y₂ ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Y_le_YU hy₂Y
  have hb₁ : bar cx hy₁YU ∈ N₁ := bar_mem_of_mem_Ni cx hy₁N hy₁YU
  have hb₂ : bar cx hy₂YU ∈ N₂ := bar_mem_of_mem_Ni cx hy₂N hy₂YU
  refine ⟨y₁, y₂, hy₁Y, hy₂Y, hy₁o, hy₂o, hy₁f, hy₂f, hy₁N, hy₂N, ?_, ?_⟩
  · exact comm_mem_P cx hI hy₁YU hy₂YU (c.h53one.comm _ hb₁ _ hb₂)
  · intro y hy
    have hyYU : y ∈ Y153 Mc M ⊔ UH153 T M V₁ Mc := Y_le_YU hy
    exact ⟨comm_mem_P cx hI hyYU hy₁YU
        (autI_Y_comm h113 cx (bar_mem_autI cx hyYU hy) (bar_mem_autI cx hy₁YU hy₁Y)),
      comm_mem_P cx hI hyYU hy₂YU
        (autI_Y_comm h113 cx (bar_mem_autI cx hyYU hy) (bar_mem_autI cx hy₂YU hy₂Y))⟩

end Lifts

end S153E55

end CFSG.Quasithin
