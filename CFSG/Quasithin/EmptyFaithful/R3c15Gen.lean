module

public import CFSG.Quasithin.EmptyFaithful.R3c14Red

public section

namespace CFSG.Quasithin.R3c15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14
open CFSG.ComponentClassification
open scoped commutatorElement

section Gen

variable {G : Type} [Group G] [Finite G]

theorem elConfig_of_data {S Q V₂ Yp L : Subgroup G} [Group.IsPerfect ↥L]
    (hZ : centerOf L = CFSG.Open.pCoreOf 2 L) (hQsyl : IsSylowTwoOf Q L)
    (hSfin : IsPGroup 2 ↥S) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hSN : S ≤ Subgroup.normalizer (Yp : Set G)) (hQS : Q ≤ S)
    (hYL : Yp ≤ L) (hV2Y : V₂ ≤ Yp) (hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G))
    (hQV : Q ≤ Subgroup.normalizer (V₂ : Set G)) (hVQ : V₂ ≤ Q)
    (hV4 : Nat.card V₂ = 4) (hV2sq : ∀ v ∈ V₂, v * v = 1)
    (hfix : ∀ x ∈ V₂, (∀ b ∈ Yp, b * x = x * b) → x = 1)
    (hy : ∃ y ∈ Yp, y ^ 3 = 1 ∧ ¬ ∀ v ∈ V₂, y * v = v * y)
    (hs : ∃ s ∈ S, s ∈ Subgroup.centralizer (Yp : Set G) ∧
      s ∉ Subgroup.centralizer (L : Set G)) :
    ElConfig (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQL : Q ≤ L := hQsyl.1
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hVz : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  obtain ⟨y₀, hy₀Y, hy₀3, hy₀n⟩ := hy
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQsyl
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  have hTsyl : IsSylowTwoOf ((Q.subgroupOf L).map π) ⊤ := by
    rw [← hT]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hcomm : ∀ (a₀ : ↥L) (v₀ : ↥L), (a₀ : G) ∈ Yp → (v₀ : G) ∈ V₂ →
      π a₀ * π v₀ = π v₀ * π a₀ → (a₀ : G) * v₀ = v₀ * a₀ := by
    intro a₀ v₀ ha hv hc
    have h1 : π (a₀ * v₀ * a₀⁻¹ * v₀⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have h2 : a₀ * v₀ * a₀⁻¹ * v₀⁻¹ ∈ Z := by
      rw [← hker]
      exact h1
    have h3 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) ∈ centerOf L :=
      SBc2.mem_centerOf_iff_center.mpr h2
    have h4 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) ∈ V₂ := by
      have h5 : (a₀ : G) * v₀ * (a₀ : G)⁻¹ ∈ V₂ :=
        (Subgroup.mem_normalizer_iff.mp (hYN ha) (v₀ : G)).mp hv
      have h6 : ((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) =
          ((a₀ : G) * v₀ * (a₀ : G)⁻¹) * (v₀ : G)⁻¹ := rfl
      rw [h6]
      exact V₂.mul_mem h5 (V₂.inv_mem hv)
    have h7 := hVz _ h4 h3
    calc (a₀ : G) * v₀ = (a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) * (v₀ * a₀) := by
          rw [show (((a₀ * v₀ * a₀⁻¹ * v₀⁻¹ : ↥L) : G) * ((v₀ : G) * a₀)) = (a₀ : G) * v₀ by
            simp [mul_assoc]]
      _ = v₀ * a₀ := by rw [h7, one_mul]
  have hKcard : Nat.card (V₂.subgroupOf L) = 4 := by
    rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV2L).toEquiv
  have hinj : Function.Injective (π.comp (V₂.subgroupOf L).subtype) := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hk' : π (k : ↥L) = 1 := hk
    have hkZ : (k : ↥L) ∈ Z := by
      rw [← hker]
      exact hk'
    have hkc : ((k : ↥L) : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hkZ
    have hkV : ((k : ↥L) : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp k.2
    exact Subtype.ext (Subtype.ext (hVz _ hkV hkc))
  have hVbar4 : Nat.card ((V₂.subgroupOf L).map π) = 4 := by
    have h1 : (π.comp (V₂.subgroupOf L).subtype).range = (V₂.subgroupOf L).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← h1]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm.trans hKcard
  have hVbar2 : ∀ v ∈ (V₂.subgroupOf L).map π, v * v = 1 := by
    rintro _ ⟨x₀, hx₀, rfl⟩
    rw [← map_mul]
    have hxV : (x₀ : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hx₀
    have : x₀ * x₀ = 1 := Subtype.ext (hV2sq _ hxV)
    rw [this, map_one]
  have hfixbar : ∀ v ∈ (V₂.subgroupOf L).map π,
      (∀ h ∈ (Yp.subgroupOf L).map π, h * v = v * h) → v = 1 := by
    rintro _ ⟨v₀, hv₀, rfl⟩ hc
    have hv : (v₀ : G) ∈ V₂ := Subgroup.mem_subgroupOf.mp hv₀
    have : v₀ = 1 := by
      have h1 : (v₀ : G) = 1 := by
        refine hfix _ hv fun b hb => ?_
        have := hcomm ⟨b, hYL hb⟩ v₀ hb hv (hc _ ⟨⟨b, hYL hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩)
        exact this
      exact Subtype.ext h1
    rw [this, map_one]
  have hybar : ∃ y ∈ (Yp.subgroupOf L).map π, y ^ 3 = 1 ∧
      ¬ ∀ v ∈ (V₂.subgroupOf L).map π, y * v = v * y := by
    refine ⟨π ⟨y₀, hYL hy₀Y⟩, ⟨⟨y₀, hYL hy₀Y⟩, Subgroup.mem_subgroupOf.mpr hy₀Y, rfl⟩, ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨y₀, hYL hy₀Y⟩ : ↥L) ^ 3 = 1 := Subtype.ext hy₀3
      rw [this, map_one]
    · intro hall
      apply hy₀n
      intro v hv
      exact hcomm ⟨y₀, hYL hy₀Y⟩ ⟨v, hV2L hv⟩ hy₀Y hv
        (hall _ ⟨⟨v, hV2L hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩)
  have hSq : S ≤ Subgroup.normalizer (L : Set G) := hSL
  let ρ : ↥(S) →* MulAut (↥L ⧸ Z) :=
    (PerfectAutomorphisms.centerQuotientHom ↥L).comp
      ((Subgroup.normalizerMonoidHom L).comp (Subgroup.inclusion hSq))
  have hρ : ∀ (s : ↥(S)) (l : ↥L),
      ρ s (π l) = π (Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) l) := fun s l =>
    PerfectAutomorphisms.onCenterQuotient_apply_mk _ l
  have hρcoe : ∀ (s : ↥(S)) (l : ↥L),
      ((Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) l : ↥L) : G) =
        (s : G) * l * (s : G)⁻¹ := fun s l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hSq s) l
  have hρne : ∀ s : ↥(S), (s : G) ∉ Subgroup.centralizer (L : Set G) → ρ s ≠ 1 := by
    intro s hs h1
    apply hs
    have h2 : Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq s) = 1 :=
      PerfectAutomorphisms.centerQuotientHom_injective ↥L (h1.trans (map_one _).symm)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h3 := DFunLike.congr_fun h2 ⟨l, hl⟩
    have h4 := congrArg Subtype.val h3
    rw [hρcoe] at h4
    simp only [MulAut.one_apply] at h4
    show l * (s : G) = (s : G) * l
    calc l * (s : G) = ((s : G) * l * (s : G)⁻¹) * (s : G) := by rw [h4]
      _ = (s : G) * l := by group
  obtain ⟨s₀, hs₀S, hs₀C, hs₀L⟩ := hs
  let W : Subgroup ↥(S) := (Subgroup.centralizer (Yp : Set G)).subgroupOf (S)
  have hWn : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hn' : (n : G) ∈ Subgroup.centralizer (Yp : Set G) := hn
    show ((g * n * g⁻¹ : ↥(S)) : G) ∈ Subgroup.centralizer (Yp : Set G)
    rw [Subgroup.mem_centralizer_iff] at hn' ⊢
    intro y hy
    have hy' : (g : G)⁻¹ * y * (g : G) ∈ Yp := by
      have := (Subgroup.mem_normalizer_iff.mp (hSN (g⁻¹ : ↥(S)).2) y).mp
      simpa using this hy
    have h1 := hn' _ hy'
    show y * ((g : G) * n * (g : G)⁻¹) = ((g : G) * n * (g : G)⁻¹) * y
    calc y * ((g : G) * n * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * y * (g : G)) * n) * (g : G)⁻¹ := by group
      _ = (g : G) * (n * ((g : G)⁻¹ * y * (g : G))) * (g : G)⁻¹ := by rw [h1]
      _ = ((g : G) * n * (g : G)⁻¹) * y := by group
  have hRp : IsPGroup 2 ↥ρ.range := hSfin.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have hRfin : Finite ↥ρ.range := Finite.of_surjective _ ρ.rangeRestrict_surjective
  have hRnil : Group.IsNilpotent ↥ρ.range := hRp.isNilpotent
  have hWpn : (W.map ρ.rangeRestrict).Normal := hWn.map _ ρ.rangeRestrict_surjective
  have hWpne : W.map ρ.rangeRestrict ≠ ⊥ := by
    intro hb
    have hmem : ρ.rangeRestrict ⟨s₀, hs₀S⟩ ∈ W.map ρ.rangeRestrict :=
      ⟨⟨s₀, hs₀S⟩, hs₀C, rfl⟩
    rw [hb, Subgroup.mem_bot] at hmem
    apply hρne ⟨s₀, hs₀S⟩ hs₀L
    exact congrArg Subtype.val hmem
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hWpne
  obtain ⟨⟨ζ', hζ'W, hζ'Z⟩, hζ'1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  obtain ⟨w, hwW, hwζ⟩ := hζ'W
  have hwC : (w : G) ∈ Subgroup.centralizer (Yp : Set G) := hwW
  have hζρ : (ζ' : MulAut (↥L ⧸ Z)) = ρ w := (congrArg Subtype.val hwζ).symm
  have hζne : (ζ' : MulAut (↥L ⧸ Z)) ≠ 1 := fun h1 => hζ'1 (Subtype.ext (Subtype.ext h1))
  have hζH : ∀ h ∈ (Yp.subgroupOf L).map π, (ζ' : MulAut (↥L ⧸ Z)) h = h := by
    rintro _ ⟨l₀, hl₀, rfl⟩
    have hl₀Y : (l₀ : G) ∈ Yp := Subgroup.mem_subgroupOf.mp hl₀
    rw [hζρ, hρ]
    congr 1
    refine Subtype.ext ?_
    rw [hρcoe]
    have hc := Subgroup.mem_centralizer_iff.mp hwC (l₀ : G) hl₀Y
    calc (w : G) * (l₀ : G) * (w : G)⁻¹ = (l₀ : G) * (w : G) * (w : G)⁻¹ := by rw [← hc]
      _ = (l₀ : G) := by group
  have hζT : ∀ t ∈ (Q.subgroupOf L).map π, (ζ' : MulAut (↥L ⧸ Z)) t = t := by
    rintro _ ⟨q₀, hq₀, rfl⟩
    have hq₀Q : (q₀ : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq₀
    let sq : ↥(S) := ⟨(q₀ : G), hQS hq₀Q⟩
    have hρsq : ∀ x : ↥L ⧸ Z, ρ sq x = π q₀ * x * (π q₀)⁻¹ := by
      intro x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Z x
      have e : Subgroup.normalizerMonoidHom L (Subgroup.inclusion hSq sq) l = q₀ * l * q₀⁻¹ :=
        Subtype.ext (hρcoe sq l)
      show ρ sq (π l) = π q₀ * π l * (π q₀)⁻¹
      rw [hρ, e, map_mul, map_mul, map_inv]
    have hcomm' := Subgroup.mem_center_iff.mp hζ'Z ⟨ρ sq, ⟨sq, rfl⟩⟩
    have hcomm'' : ρ sq * (ζ' : MulAut (↥L ⧸ Z)) = (ζ' : MulAut (↥L ⧸ Z)) * ρ sq :=
      congrArg Subtype.val hcomm'
    have hd : (π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) ∈ Subgroup.center (↥L ⧸ Z) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := DFunLike.congr_fun hcomm'' ((ζ' : MulAut (↥L ⧸ Z)).symm y)
      simp only [MulAut.mul_apply, hρsq, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
      calc y * ((π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀))
          = (π q₀)⁻¹ * (π q₀ * y * (π q₀)⁻¹) * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) := by group
        _ = (π q₀)⁻¹ * ((ζ' : MulAut (↥L ⧸ Z)) (π q₀) * y *
              ((ζ' : MulAut (↥L ⧸ Z)) (π q₀))⁻¹) * (ζ' : MulAut (↥L ⧸ Z)) (π q₀) := by
          rw [h1]
        _ = ((π q₀)⁻¹ * (ζ' : MulAut (↥L ⧸ Z)) (π q₀)) * y := by group
    rw [center_quot_eq_bot, Subgroup.mem_bot] at hd
    exact (inv_mul_eq_one.mp hd).symm
  refine ⟨(Q.subgroupOf L).map π, (V₂.subgroupOf L).map π, (Yp.subgroupOf L).map π,
    (ζ' : MulAut (↥L ⧸ Z)), hTsyl, ?_⟩
  exact ⟨Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hVQ (Subgroup.mem_subgroupOf.mp hx)), hVbar4, hVbar2,
    quot_normalizes hV2L hQV,
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hV2Y (Subgroup.mem_subgroupOf.mp hx)),
    quot_normalizes hV2L hYN,
    quot_normalizes hYL (fun q hq => hSN (hQS hq)), hybar, hfixbar, hζne, hζT, hζH⟩

end Gen

end CFSG.Quasithin.R3c15
