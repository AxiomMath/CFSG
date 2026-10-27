module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

namespace L32NSym

variable {G : Type} [Group G]

theorem mem_conjugate_iff' {X : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate X g ↔ g * x * g⁻¹ ∈ X := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [mul_assoc]⟩

theorem conjAct_coe (W : Subgroup G) (g : Subgroup.normalizer (W : Set G)) (w : W) :
    ((conjAct W g w : W) : G) = g * w * g⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe W (Subgroup.inclusion le_rfl g) w

theorem mem_zpowers_of_sq {w x : G} (hw2 : w * w = 1) (hx : x ∈ Subgroup.zpowers w) :
    x = 1 ∨ x = w := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.even_or_odd' n with ⟨k, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hw2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hw2, one_zpow, one_mul, zpow_one]

theorem conjugate_mul_of_mem_normalizer {X : Subgroup G} {x g : G}
    (hx : x ∈ Subgroup.normalizer (X : Set G)) :
    CFSG.conjugate X (x * g) = CFSG.conjugate X g := by
  ext y
  rw [mem_conjugate_iff', mem_conjugate_iff', show x * g * y * (x * g)⁻¹ =
    x * (g * y * g⁻¹) * x⁻¹ by group]
  exact (Subgroup.mem_normalizer_iff.mp hx _).symm

variable [Finite G]

theorem autOn_eq_top {X W : Subgroup G} [IsMulCommutative ↥W]
    (hnat : BinaryNaturalSL (V := ↥W) (autOn X W) ⊤ ⊥ 3 1) : autOn X W = ⊤ := by
  obtain ⟨hcard, hsq⟩ := card_and_sq_of_binaryNaturalSL hnat
  have hsq' : ∀ w ∈ W, w ^ 2 = 1 := fun w hw => by
    have := congrArg Subtype.val (hsq ⟨w, hw⟩)
    simpa using this
  apply Subgroup.eq_top_of_card_eq
  refine le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective) ?_
  rw [card_eq_of_binaryNaturalSL hnat (by norm_num)]
  exact card_mulAut_le hsq' hcard (by norm_num)

theorem sq_of_natural {X W : Subgroup G} [IsMulCommutative ↥W]
    (hnat : BinaryNaturalSL (V := ↥W) (autOn X W) ⊤ ⊥ 3 1) : ∀ w ∈ W, w ^ 2 = 1 := by
  obtain ⟨-, hsq⟩ := card_and_sq_of_binaryNaturalSL hnat
  intro w hw
  have := congrArg Subtype.val (hsq ⟨w, hw⟩)
  simpa using this

theorem card_of_natural {X W : Subgroup G} [IsMulCommutative ↥W]
    (hnat : BinaryNaturalSL (V := ↥W) (autOn X W) ⊤ ⊥ 3 1) : Nat.card W = 8 :=
  (card_and_sq_of_binaryNaturalSL hnat).1

theorem exists_conjugate_eq {X W : Subgroup G} [IsMulCommutative ↥W]
    (hsq : ∀ w ∈ W, w ^ 2 = 1) (htop : autOn X W = ⊤) {i : ℕ} {W₁ W₂ : Subgroup G}
    (hW₁ : W₁ ≤ W) (hW₂ : W₂ ≤ W) (h1 : Nat.card W₁ = 2 ^ i) (h2 : Nat.card W₂ = 2 ^ i) :
    ∃ x ∈ X, CFSG.conjugate W₁ x = W₂ := by
  let _ := zmodModuleOf hsq
  have : Module.Finite (ZMod 2) (Additive ↥W) := Module.Finite.of_finite
  have hf : Module.finrank (ZMod 2) (subOf (V := W) W₂) =
      Module.finrank (ZMod 2) (subOf (V := W) W₁) := by
    rw [finrank_subOf hW₂ h2, finrank_subOf hW₁ h1]
  obtain ⟨g, hg⟩ := exists_linearEquiv_map_eq hf
  have hαL : mulAutOfLin g ∈ autOn X W := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨⟨l, hlN⟩, hlL, hlα⟩ := hαL
  refine ⟨l, Subgroup.mem_subgroupOf.1 hlL, ?_⟩
  have hle : W₂ ≤ CFSG.conjugate W₁ l := by
    intro w hw
    rw [mem_conjugate_iff']
    have hwV := hW₂ hw
    have e : l * w * l⁻¹ = ((mulAutOfLin g ⟨w, hwV⟩ : ↥W) : G) := by
      rw [← hlα]
      rfl
    rw [e, mulAutOfLin_apply]
    have hmem : g (Additive.ofMul ⟨w, hwV⟩) ∈ subOf (V := W) W₁ := by
      rw [← hg]
      exact ⟨Additive.ofMul ⟨w, hwV⟩, mem_subOf.2 hw, rfl⟩
    exact mem_subOf.1 hmem
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [LinearS3.card_conjugate, h1, h2])).symm

theorem exists_conj_eq {X W : Subgroup G} [IsMulCommutative ↥W]
    (hsq : ∀ w ∈ W, w ^ 2 = 1) (htop : autOn X W = ⊤) {v w : G} (hv : v ∈ W) (hw : w ∈ W)
    (hv1 : v ≠ 1) (hw1 : w ≠ 1) : ∃ x ∈ X, x * v * x⁻¹ = w := by
  have hord : ∀ u ∈ W, u ≠ 1 → Nat.card (Subgroup.zpowers u) = 2 ^ 1 := fun u hu hu1 => by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (hsq u hu) hu1
  obtain ⟨x, hx, hxe⟩ := exists_conjugate_eq hsq htop (Subgroup.zpowers_le.mpr hv)
    (Subgroup.zpowers_le.mpr hw) (hord v hv hv1) (hord w hw hw1)
  have hxw : x * w * x⁻¹ ∈ Subgroup.zpowers v := by
    have hw' : w ∈ CFSG.conjugate (Subgroup.zpowers v) x := hxe ▸ Subgroup.mem_zpowers w
    exact mem_conjugate_iff'.mp hw'
  have hv2 : v * v = 1 := by rw [← pow_two]; exact hsq v hv
  rcases mem_zpowers_of_sq hv2 hxw with h | h
  · exfalso
    apply hw1
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  · refine ⟨x⁻¹, X.inv_mem hx, ?_⟩
    calc x⁻¹ * v * x⁻¹⁻¹ = x⁻¹ * (x * w * x⁻¹) * x := by rw [h, inv_inv]
      _ = w := by group

theorem isTwoReducedIn_of_trans {X Y W : Subgroup G} (hWY : W ≤ Y)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) (hel : IsElemAbelian 2 W) (hXY : X ≤ Y)
    (hW2 : 2 ∣ Nat.card W)
    (htrans : ∀ v ∈ W, ∀ w ∈ W, v ≠ 1 → w ≠ 1 → ∃ x ∈ X, x * v * x⁻¹ = w) :
    IsTwoReducedIn Y W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hWY, hYW, hel, fun D hDY hYD hD2 => ?_⟩
  have hP : IsPGroup 2 ↥(autOn D W) := by
    rintro ⟨φ, ⟨⟨d, hdN⟩, hdD, rfl⟩⟩
    obtain ⟨k, hk⟩ := hD2 d (Subgroup.mem_subgroupOf.mp hdD)
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow]
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [MulAut.one_apply, conjAct_coe]
    show d ^ 2 ^ k * w * (d ^ 2 ^ k)⁻¹ = w
    rw [(Subgroup.mem_centralizer_iff.mp hk w w.2).symm]
    group
  have h1fix : (1 : ↥W) ∈ MulAction.fixedPoints ↥(autOn D W) ↥W := fun φ => map_one _
  obtain ⟨w₀, hw₀, hw₀1⟩ := hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥W hW2 h1fix
  have hfix : ∀ d ∈ D, d * (w₀ : G) * d⁻¹ = w₀ := by
    intro d hd
    have hdN : d ∈ Subgroup.normalizer (W : Set G) := hYW (hDY hd)
    have h := hw₀ ⟨conjAct W ⟨d, hdN⟩, ⟨⟨d, hdN⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩⟩
    have h' := congrArg Subtype.val h
    exact (conjAct_coe W ⟨d, hdN⟩ w₀).symm.trans h'
  have hw₀1' : (w₀ : G) ≠ 1 := fun h => hw₀1 (Subtype.ext (by rw [h]; rfl)).symm
  refine fun d hd => Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  by_cases hv1 : v = 1
  · rw [hv1, one_mul, mul_one]
  obtain ⟨x, hx, hxv⟩ := htrans _ w₀.2 v hv hw₀1' hv1
  have hxD : x⁻¹ * d * x ∈ D := by
    have := (Subgroup.mem_normalizer_iff.mp (hYD (Y.inv_mem (hXY hx))) d).mp hd
    simpa using this
  have h2 := hfix _ hxD
  have h3 : d * v * d⁻¹ = v := by
    rw [← hxv]
    calc d * (x * w₀ * x⁻¹) * d⁻¹ = x * ((x⁻¹ * d * x) * w₀ * (x⁻¹ * d * x)⁻¹) * x⁻¹ := by
          group
      _ = x * w₀ * x⁻¹ := by rw [h2]
  calc v * d = d * v * d⁻¹ * d := by rw [h3]
    _ = d * v := by group

omit [Finite G] in
theorem comm_of_inf_ne_bot {U G₁ A B X Y : Subgroup G} {z : G}
    (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUG₁ : G₁ ≤ Subgroup.normalizer (U : Set G))
    (hzG₁ : ∀ c : G, c * z * c⁻¹ = z → c ∈ G₁) (hAU : A ≤ U) (hBU : B ≤ U)
    (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hYB : Y ≤ Subgroup.normalizer (B : Set G))
    (htA : ∀ v ∈ A, v ≠ 1 → ∃ x ∈ X, x * v * x⁻¹ = z)
    (htB : ∀ v ∈ B, v ≠ 1 → ∃ y ∈ Y, y * v * y⁻¹ = z) {g g' u : G}
    (huA : u ∈ CFSG.conjugate A g) (huB : u ∈ CFSG.conjugate B g') (hu1 : u ≠ 1) :
    ∀ a ∈ CFSG.conjugate A g, ∀ b ∈ CFSG.conjugate B g', a * b = b * a := by
  have hgu : g * u * g⁻¹ ∈ A := mem_conjugate_iff'.mp huA
  have hg'u : g' * u * g'⁻¹ ∈ B := mem_conjugate_iff'.mp huB
  have hne : ∀ c : G, c * u * c⁻¹ ≠ 1 := fun c h => hu1 (by
    calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
      _ = 1 := by rw [h]; group)
  obtain ⟨x, hx, hxu⟩ := htA _ hgu (hne g)
  obtain ⟨y, hy, hyu⟩ := htB _ hg'u (hne g')
  set h := x * g with hh
  set h' := y * g' with hh'
  have hhA : CFSG.conjugate A h = CFSG.conjugate A g := conjugate_mul_of_mem_normalizer (hXA hx)
  have hhB : CFSG.conjugate B h' = CFSG.conjugate B g' := conjugate_mul_of_mem_normalizer (hYB hy)
  have hhz : h * u * h⁻¹ = z := by rw [hh, ← hxu]; group
  have hh'z : h' * u * h'⁻¹ = z := by rw [hh', ← hyu]; group
  have hc : (h * h'⁻¹) * z * (h * h'⁻¹)⁻¹ = z := by
    calc (h * h'⁻¹) * z * (h * h'⁻¹)⁻¹ = (h * h'⁻¹) * (h' * u * h'⁻¹) * (h * h'⁻¹)⁻¹ := by
          rw [hh'z]
      _ = h * u * h⁻¹ := by group
      _ = z := hhz
  have hcG₁ := hzG₁ _ hc
  intro a ha b hb
  rw [← hhA] at ha
  rw [← hhB] at hb
  have haU : h * a * h⁻¹ ∈ U := hAU (mem_conjugate_iff'.mp ha)
  have hbU : h * b * h⁻¹ ∈ U := by
    have h1 : h' * b * h'⁻¹ ∈ U := hBU (mem_conjugate_iff'.mp hb)
    have h2 := (Subgroup.mem_normalizer_iff.mp (hUG₁ hcG₁) _).mp h1
    rwa [show h * h'⁻¹ * (h' * b * h'⁻¹) * (h * h'⁻¹)⁻¹ = h * b * h⁻¹ by group] at h2
  have hcomm := hU _ haU _ hbU
  calc a * b = h⁻¹ * ((h * a * h⁻¹) * (h * b * h⁻¹)) * h := by group
    _ = h⁻¹ * ((h * b * h⁻¹) * (h * a * h⁻¹)) * h := by rw [hcomm]
    _ = b * a := by group

end L32NSym

end CFSG.Quasithin.H13
