module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFHeis
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFT7Inv
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFT7Lift
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFT7SecMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtHSRuLocSimple

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
  {X : Subgroup G} {τ f : G}

omit [Finite G] in
theorem mem_center_iff_mem_V₁ (hV₁ : V₁ = centerOf L) (z : ↥L) :
    z ∈ Subgroup.center ↥L ↔ (z : G) ∈ V₁ := by
  rw [hV₁, centerOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_center_iff]
  constructor
  · intro hz
    exact ⟨z.2, fun l hl => congrArg Subtype.val (hz ⟨l, hl⟩)⟩
  · rintro ⟨-, hz⟩ y
    exact Subtype.ext (hz y y.2)

theorem KFHyp.core_center_eq_bot (h113 : StageLemma14113)
    (h : KFHyp T Mc M V₁ V₂ Yp I L t X τ f) {x : G} {Lx : Subgroup G}
    (hLx : SBd14.CoreProps L V₁ I Lx x) (hcard : Nat.card (↥Lx ⧸ Subgroup.center ↥Lx) = 168) :
    Subgroup.center ↥Lx = ⊥ := by
  classical
  obtain ⟨-, B, -, -, hBI, -, -, -, -, -, -, b, hbB, hb3, v₀, hv₀V, hbmove⟩ :=
    h.exists_threeOnePlusTwo h113
  have hbI : b ∈ I := hBI hbB
  have hbL : b ∈ Subgroup.normalizer (L : Set G) := h.r.hNL hbI
  have hbV : b ∈ Subgroup.normalizer (V₁ : Set G) := h.hI ▸ hbI
  have hV₁ : V₁ = centerOf L := h.r.V₁_eq_center h113
  have hmemZ := mem_center_iff_mem_V₁ hV₁
  have hV2 : ∀ v ∈ V₁, v * v = 1 := fun v hv => h.r.V_sq v (h.r.ctx.hyp.decomp.le₁ hv)
  have hV4 : Nat.card ↥V₁ = 4 := h.r.ctx.hyp.decomp.card₁
  have hbV' : ∀ v ∈ V₁, b * v * b⁻¹ ∈ V₁ := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hbV v).mp hv
  have hmove : ∃ v ∈ V₁, b * v ≠ v * b := by
    refine ⟨v₀, hv₀V, fun hc => hbmove ?_⟩
    rw [hc]
    group
  let β : ↥L ≃* ↥L := (Subgroup.normalizerMonoidHom L) ⟨b, hbL⟩
  have hβ : ∀ y : ↥L, ((β y : ↥L) : G) = b * y * b⁻¹ := fun y => rfl
  have hsqL : ∀ y : ↥L, y * y ∈ Subgroup.center ↥L → y * y = 1 := by
    refine sq_eq_one_of_lift (Z := Subgroup.center ↥L) le_rfl ?_ ?_ β ?_ ?_
    · intro z hz
      exact Subtype.ext (hV2 z ((hmemZ z).mp hz))
    · intro y₁ y₂ hy₁ hy₂ hy₁Z hy₂Z
      have hq₁ : (QuotientGroup.mk y₁ : ↥L ⧸ Subgroup.center ↥L) *
          (QuotientGroup.mk y₁ : ↥L ⧸ Subgroup.center ↥L) = 1 := by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
        exact hy₁
      have hq₂ : (QuotientGroup.mk y₂ : ↥L ⧸ Subgroup.center ↥L) *
          (QuotientGroup.mk y₂ : ↥L ⧸ Subgroup.center ↥L) = 1 := by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
        exact hy₂
      have hn₁ : (QuotientGroup.mk y₁ : ↥L ⧸ Subgroup.center ↥L) ≠ 1 := fun h1 =>
        hy₁Z ((QuotientGroup.eq_one_iff y₁).mp h1)
      have hn₂ : (QuotientGroup.mk y₂ : ↥L ⧸ Subgroup.center ↥L) ≠ 1 := fun h1 =>
        hy₂Z ((QuotientGroup.eq_one_iff y₂).mp h1)
      obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_involutions_psl34 h.r.hn2 hq₁ hq₂ hn₁ hn₂)
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
      have hc' : (QuotientGroup.mk (g * y₁ * g⁻¹) : ↥L ⧸ Subgroup.center ↥L) =
          QuotientGroup.mk y₂ := hc
      have hz : y₂⁻¹ * (g * y₁ * g⁻¹) ∈ Subgroup.center ↥L := by
        have := QuotientGroup.eq.mp hc'.symm
        exact this
      exact ⟨g, y₂⁻¹ * (g * y₁ * g⁻¹), hz, by group⟩
    · intro z
      rw [hmemZ, hmemZ, hβ]
      exact (Subgroup.mem_normalizer_iff.mp hbV (z : G)).symm
    · intro z hz hβz
      have hzV : (z : G) ∈ V₁ := (hmemZ z).mp hz
      have hbz : b * (z : G) = (z : G) * b := by
        have h1 : b * (z : G) * b⁻¹ = z := by rw [← hβ, hβz]
        calc b * (z : G) = (b * (z : G) * b⁻¹) * b := by group
          _ = (z : G) * b := by rw [h1]
      exact Subtype.ext (eq_one_of_fixed_klein hV2 hV4 hbV' hb3 hmove hzV hbz)
  have hperf : Group.IsPerfect ↥Lx := hLx.2.1.1
  have hL32 : IsPSL 3 2 1 (↥Lx ⧸ Subgroup.center ↥Lx) := by
    have : IsSimpleGroup (↥Lx ⧸ Subgroup.center ↥Lx) := hLx.2.1.2.1
    exact HSRuLoc.Mod.isPSL_three_two_of_simple_card_168 (H := ↥Lx ⧸ Subgroup.center ↥Lx) hcard
  have hLxL : Lx ≤ L := hLx.1
  refine center_eq_bot_of_sq_lifts (fun a ha => Subtype.ext (hV2 a (hLx.2.2.1 a ha))) hL32
    (fun y hy => ?_)
  have hyV : ((y * y : ↥Lx) : G) ∈ V₁ := hLx.2.2.1 _ hy
  have hŷ : (⟨y, hLxL y.2⟩ : ↥L) * ⟨y, hLxL y.2⟩ ∈ Subgroup.center ↥L :=
    (hmemZ _).mpr hyV
  have h1 := congrArg (fun z : ↥L => (z : G)) (hsqL _ hŷ)
  exact Subtype.ext (by simpa using h1)

end CFSG.Quasithin.SBd19F
