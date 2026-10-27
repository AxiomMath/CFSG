module

public import CFSG.Quasithin.Background.SmithB42G2Nat
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOffender
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenFieldInvolutions
public import CFSG.Quasithin.Background.SmithB42G2Id
public import CFSG.Quasithin.Background.SmithCurtisChevType

public section

namespace CFSG.Quasithin.B42G2F

open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Disp

variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Module.Finite (ZMod 2) M]

theorem dispRank_mul_le (s t : M ≃ₗ[ZMod 2] M) : dispRank (s * t) ≤ dispRank s + dispRank t := by
  unfold dispRank
  have hle : LinearMap.range ((s * t).toLinearMap - 1) ≤
      LinearMap.range (s.toLinearMap - 1) ⊔ LinearMap.range (t.toLinearMap - 1) := by
    rintro _ ⟨v, rfl⟩
    have e : ((s * t).toLinearMap - 1) v = (s.toLinearMap - 1) (t v) +
        (t.toLinearMap - 1) v := by
      simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearEquiv.mul_apply,
        Module.End.one_apply]
      abel
    rw [e]
    exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

omit [Module.Finite (ZMod 2) M] in
theorem dispRank_conj (u s : M ≃ₗ[ZMod 2] M) : dispRank (u * s * u⁻¹) = dispRank s := by
  unfold dispRank
  have hu : ∀ x, u (u⁻¹ x) = x := fun x => u.apply_symm_apply x
  have hu' : ∀ x, u⁻¹ (u x) = x := fun x => u.symm_apply_apply x
  have e : LinearMap.range ((u * s * u⁻¹).toLinearMap - 1) =
      (LinearMap.range (s.toLinearMap - 1)).map u.toLinearMap := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨s (u⁻¹ w) - u⁻¹ w, ⟨u⁻¹ w, rfl⟩, ?_⟩
      change u (s (u⁻¹ w) - u⁻¹ w) = u (s (u⁻¹ w)) - w
      rw [map_sub, hu]
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨u w, ?_⟩
      change u (s (u⁻¹ (u w))) - u w = u (s w - w)
      rw [hu', map_sub]
  rw [e, LinearEquiv.finrank_map_eq]

omit [Module.Finite (ZMod 2) M] in
theorem dispRank_inv_of_mul_self {s : M ≃ₗ[ZMod 2] M} (hs : s * s = 1) :
    dispRank s⁻¹ = dispRank s := by
  rw [inv_eq_of_mul_eq_one_right hs]

end Disp

section General

variable {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module (ZMod 2) M]
  {π : G →* (M ≃ₗ[ZMod 2] M)} (hπ : Function.Injective π)
  {A : Subgroup (M ≃ₗ[ZMod 2] M)} (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)

include hπ hnorm in
theorem mem_range_of_normAut_mem_inner (hZ : Subgroup.center G = ⊥) (hntM : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hsq : ∀ a ∈ A, a * a = 1) (a : A) (ha : normAut π hπ A hnorm a ∈ inner G) :
    ∃ g, π g = a.1 := by
  obtain ⟨g, hg⟩ := ha
  have hconj : ∀ x, a.1 * π x * a.1⁻¹ = π g * π x * (π g)⁻¹ := fun x => by
    rw [← π_normAut π hπ A hnorm a x, ← hg]
    simp [MulAut.conj_apply]
  have hgg : g * g = 1 := by
    have h1 : normAut π hπ A hnorm (a * a) = 1 := by
      have : a * a = 1 := Subtype.ext (hsq a.1 a.2)
      rw [this, map_one]
    rw [map_mul, ← hg, ← map_mul] at h1
    have h2 : g * g ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun φ : MulAut G => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc y * (g * g) = (g * g) * y * (g * g)⁻¹ * (g * g) := by rw [this]
        _ = (g * g) * y := by group
    rw [hZ] at h2
    exact (Subgroup.mem_bot.mp h2)
  have hpp : π g * π g = 1 := by rw [← map_mul, hgg, map_one]
  have hpinv : (π g)⁻¹ = π g := inv_eq_of_mul_eq_one_right hpp
  have hcomm : ∀ x, (π g * a.1) * π x = π x * (π g * a.1) := fun x => by
    calc (π g * a.1) * π x = π g * (a.1 * π x * a.1⁻¹) * a.1 := by group
      _ = π g * (π g * π x * (π g)⁻¹) * a.1 := by rw [hconj x]
      _ = (π g * π g) * π x * (π g * a.1) := by rw [hpinv]; group
      _ = π x * (π g * a.1) := by rw [hpp, one_mul]
  have h3 : π g * a.1 * π g = a.1 := by
    have := hcomm g
    rw [this]
    calc π g * (π g * a.1) = (π g * π g) * a.1 := by group
      _ = a.1 := by rw [hpp, one_mul]
  have hcc : (π g * a.1) * (π g * a.1) = 1 := by
    calc (π g * a.1) * (π g * a.1) = (π g * a.1 * π g) * a.1 := by group
      _ = a.1 * a.1 := by rw [h3]
      _ = 1 := hsq a.1 a.2
  have h4 : π g * a.1 = 1 :=
    eq_one_of_commute_simple_summands π (fun _ : Unit => (⊤ : Submodule (ZMod 2) M))
      (iSup_const) (fun _ => top_ne_bot) (fun _ _ _ _ => Submodule.mem_top)
      (fun _ W _ hW => hirr W hW) (π g * a.1) hcc hcomm (fun _ _ _ => Submodule.mem_top)
  refine ⟨g, ?_⟩
  have h5 : π g = a.1⁻¹ := eq_inv_of_mul_eq_one_left h4
  rw [h5]
  exact inv_eq_of_mul_eq_one_right (hsq a.1 a.2)

include hπ hnorm in
theorem card_le_two_mul [Finite M] (hZ : Subgroup.center G = ⊥) (hntM : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hsq : ∀ a ∈ A, a * a = 1) {Γ : Type} [Group Γ] (Θ : MulAut G →* Γ)
    (hΘ : Θ.ker = inner G)
    (hinv : ∀ x y : Γ, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y) :
    Nat.card A ≤ 2 * Nat.card (A.comap π) := by
  classical
  have : Finite (M ≃ₗ[ZMod 2] M) :=
    Finite.of_injective (fun e : M ≃ₗ[ZMod 2] M => (e : M → M)) DFunLike.coe_injective
  set Ψ : A →* Γ := Θ.comp (normAut π hπ A hnorm) with hΨ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Ψ.ker
  have h2 : Nat.card (A ⧸ Ψ.ker) = Nat.card Ψ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange Ψ).toEquiv
  have hker : Nat.card Ψ.ker ≤ Nat.card (A.comap π) := by
    have hmem : ∀ a : Ψ.ker, ∃ g, π g = a.1.1 := fun a => by
      refine mem_range_of_normAut_mem_inner hπ hnorm hZ hntM hirr hsq a.1 ?_
      rw [← hΘ, MonoidHom.mem_ker]
      exact a.2
    choose g hg using hmem
    have : Finite (A.comap π) := Finite.of_injective (fun x : A.comap π => (⟨π x, x.2⟩ : A))
      fun x y h => Subtype.ext (hπ (congrArg Subtype.val h))
    refine Nat.card_le_card_of_injective (fun a => ⟨g a, ?_⟩) fun a b h => ?_
    · show π (g a) ∈ A
      rw [hg a]
      exact a.1.2
    · have h3 : π (g a) = π (g b) := congrArg (fun x : A.comap π => π x.1) h
      rw [hg a, hg b] at h3
      exact Subtype.ext (Subtype.ext h3)
  have hrange : Nat.card Ψ.range ≤ 2 := by
    have hsq' : ∀ y ∈ Ψ.range, y * y = 1 := by
      rintro _ ⟨a, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (hsq a.1 a.2)
      rw [this, map_one]
    by_cases htriv : ∀ y ∈ Ψ.range, y = 1
    · have : Ψ.range = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr htriv
      rw [this, Subgroup.card_bot]
      norm_num
    · push Not at htriv
      obtain ⟨y₀, hy₀, hy₀1⟩ := htriv
      have hsub : (Ψ.range : Set Γ) ⊆ {1, y₀} := by
        intro y hy
        by_cases hy1 : y = 1
        · exact Or.inl hy1
        · exact Or.inr (hinv y y₀ (hsq' y hy) (hsq' y₀ hy₀) hy1 hy₀1)
      calc Nat.card Ψ.range = Nat.card (Ψ.range : Set Γ) := rfl
        _ ≤ Nat.card ({1, y₀} : Set Γ) := Nat.card_mono (Set.toFinite _) hsub
        _ ≤ 2 := by
          rw [Nat.card_coe_set_eq, Set.ncard_pair hy₀1.symm]
  rw [h1, h2]
  calc Nat.card Ψ.range * Nat.card Ψ.ker ≤ 2 * Nat.card (A.comap π) :=
    Nat.mul_le_mul hrange hker

include hπ hnorm in
theorem card_mul_card_fixed_lt_of_disp [Finite M] (hZ : Subgroup.center G = ⊥)
    (hntM : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {Γ : Type} [Group Γ] (Θ : MulAut G →* Γ) (hΘ : Θ.ker = inner G)
    (hinv : ∀ x y : Γ, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y) {r : ℕ}
    (hmax : ∀ E : Subgroup G, (∀ x ∈ E, x * x = 1) → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
      Nat.card E ≤ 2 ^ r)
    (hinner : ∀ z : G, z * z = 1 → z ≠ 1 → r + 2 ≤ dispRank (π z))
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥)
    (houter : ∀ a ∈ A, (¬ ∃ g, π g = a) → 2 ≤ dispRank a) :
    Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  classical
  have := hAe
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [_root_.sq] at this
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := A)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hcard := card_le_two_mul hπ hnorm hZ hntM hirr hsq Θ hΘ hinv
  set Ê := A.comap π with hÊ
  have hÊsq : ∀ x ∈ Ê, x * x = 1 := fun x hx => hπ (by rw [map_mul, map_one]; exact hsq _ hx)
  have hÊc : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y = y * x := fun x hx y hy =>
    hπ (by rw [map_mul, map_mul]; exact hcomm _ hx _ hy)
  have hÊr := hmax Ê hÊsq hÊc
  have hpowle : ∀ {m n : ℕ}, m ≤ n → 2 ^ m ≤ 2 ^ n := fun h =>
    Nat.pow_le_pow_right (by norm_num) h
  by_cases hÊbot : Ê = ⊥
  · have h1 : Nat.card Ê = 1 := by rw [hÊbot, Subgroup.card_bot]
    obtain ⟨⟨a, ha⟩, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
    have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hout : ¬ ∃ g, π g = a := by
      rintro ⟨g, rfl⟩
      have hg : g ∈ Ê := ha
      rw [hÊbot, Subgroup.mem_bot] at hg
      rw [hg, map_one] at ha1'
      exact ha1' rfl
    have h2 := houter a ha hout
    refine card_mul_card_fixed_lt A a ha ?_
    calc Nat.card A ≤ 2 * Nat.card Ê := hcard
      _ = 2 := by rw [h1]
      _ < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ dispRank a := hpowle h2
  · obtain ⟨⟨z, hzÊ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hÊbot
    have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
    have h2 := hinner z (hÊsq z hzÊ) hz1'
    refine card_mul_card_fixed_lt A (π z) hzÊ ?_
    calc Nat.card A ≤ 2 * Nat.card Ê := hcard
      _ ≤ 2 * 2 ^ r := Nat.mul_le_mul_left _ hÊr
      _ = 2 ^ (r + 1) := by rw [pow_succ, mul_comm]
      _ < 2 ^ (r + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      _ ≤ 2 ^ dispRank (π z) := hpowle h2

end General

section G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Quasithin.SmithCurtis.Chev CFSG.ComponentClassification.UnbalancedCatalog

variable {K : Type} [Field K] [Fintype K] [CharP K 2]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

abbrev nd0 : Fin Tag.G2.rank := ⟨0, by decide⟩

omit [Fintype K] in
theorem exists_involution_of_entrywise (α β ψ : MulAut (adjointGroup .G2 K)) (δ : K →+* K)
    (hβ : ∀ u, (β u : ModGL .G2 K) = Units.map (entrywiseHom δ) (u : ModGL .G2 K))
    (hψ : ψ * α * ψ⁻¹ = β) {c₀ : K} (hc₀ : δ c₀ ≠ c₀) :
    ∃ g : adjointGroup .G2 K, (α g * g⁻¹) * (α g * g⁻¹) = 1 ∧ α g * g⁻¹ ≠ 1 := by
  set x := xC .G2 K nd0 c₀ with hx
  have hβx : β x = xC .G2 K nd0 (δ c₀) :=
    Subtype.ext ((hβ x).trans (units_map_entrywiseHom_xUnit δ nd0 c₀))
  have hα : α = ψ⁻¹ * β * ψ := by
    rw [← hψ]
    group
  set y := xC .G2 K nd0 (δ c₀ - c₀) with hy
  have hyx : y * x = xC .G2 K nd0 (δ c₀) :=
    Subtype.ext (by
      change xUnit .G2 K nd0 (δ c₀ - c₀) * xUnit .G2 K nd0 c₀ = xUnit .G2 K nd0 (δ c₀)
      rw [← xUnit_add, sub_add_cancel])
  have hyy : y * y = 1 :=
    Subtype.ext (by
      change xUnit .G2 K nd0 (δ c₀ - c₀) * xUnit .G2 K nd0 (δ c₀ - c₀) = 1
      rw [← xUnit_add, CharTwo.add_self_eq_zero, xUnit_zero])
  have hy1 : y ≠ 1 := xC_ne_one nd0 (Units.mk0 (δ c₀ - c₀) (sub_ne_zero.mpr hc₀))
  have hαg : α (ψ⁻¹ x) = ψ⁻¹ (β x) := by
    rw [hα, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]
  have hyβ : y = β x * x⁻¹ := by
    rw [hβx, ← hyx, mul_inv_cancel_right]
  have e : α (ψ⁻¹ x) * (ψ⁻¹ x)⁻¹ = ψ⁻¹ y := by
    rw [hαg, hyβ, map_mul, map_inv]
  refine ⟨ψ⁻¹ x, ?_, ?_⟩
  · rw [e, ← map_mul, hyy, map_one]
  · rw [e]
    intro h
    apply hy1
    have := congrArg ψ h
    rwa [MulAut.apply_inv_self, map_one] at this

theorem g2_card_mul_card_fixed_lt {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 2 ≤ f)
    (π : ↥(cayleyGroup K) →* (M ≃ₗ[ZMod 2] M)) (hπ : Function.Injective π)
    (hntM : Nontrivial M)
    (hirr : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, π g u ∈ U) → U = ⊥ ∨ U = ⊤)
    (hdisp : ∀ z : ↥(cayleyGroup K), z * z = 1 → z ≠ 1 → 3 * f + 2 ≤ dispRank (π z))
    (A : Subgroup (M ≃ₗ[ZMod 2] M)) (hnorm : ∀ a ∈ A, ∀ x, ∃ y, a * π x * a⁻¹ = π y)
    (hAe : CFSG.IsElementaryAbelian 2 A) (hA1 : A ≠ ⊥) :
    Nat.card A * Nat.card {m : M // ∀ a ∈ A, a m = m} < Nat.card M := by
  classical
  have : Module.Finite (ZMod 2) M := Module.Finite.of_finite
  have hKn : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hK]
  obtain ⟨ψ, -, hsurj, hker⟩ := CFSG.Quasithin.B42G2Id.exists_adjointGroup_hom_cayleyGroup hKn hf
  have hZC : Subgroup.center (adjointGroup .G2 K) = ⊥ := center_adjointGroup_eq_bot
  have hinjψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, hker, hZC]
  set πC := π.comp ψ with hπCdef
  have hπC : Function.Injective πC := hπ.comp hinjψ
  have hnormC : ∀ a ∈ A, ∀ x, ∃ y, a * πC x * a⁻¹ = πC y := fun a ha x => by
    obtain ⟨y, hy⟩ := hnorm a ha (ψ x)
    obtain ⟨y', rfl⟩ := hsurj y
    exact ⟨y', hy⟩
  have hirrC : ∀ U : Submodule (ZMod 2) M, (∀ g, ∀ u ∈ U, πC g u ∈ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hirr U fun g u hu => by
      obtain ⟨g', rfl⟩ := hsurj g
      exact hU g' u hu
  have := hAe
  have hsq : ∀ a ∈ A, a * a = 1 := fun a ha => by
    have := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) a ha
    rwa [_root_.sq] at this
  obtain ⟨-, Θ, -, -, hΘker, hΘinv⟩ := even_G2_exact_automorphism_normal_form hf K hKn
  have hΘker' : Θ.ker = inner (adjointGroup .G2 K) := hΘker
  have hinv : ∀ x y : K ≃+* K, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 → x = y := by
    intro x y hx hy hx1 hy1
    have h1 : ∀ k, x (x k) = k := fun k => congrArg (fun σ : K ≃+* K => σ k) hx
    have h2 : ∀ k, y (y k) = k := fun k => congrArg (fun σ : K ≃+* K => σ k) hy
    have h1' : ∃ k, x k ≠ k := by
      by_contra h
      push Not at h
      exact hx1 (RingEquiv.ext h)
    have h2' : ∃ k, y k ≠ k := by
      by_contra h
      push Not at h
      exact hy1 (RingEquiv.ext h)
    exact CFSG.Quasithin.B42G2.ringEquiv_involution_unique hKn hf h1 h2 h1' h2'
  have hmax : ∀ E : Subgroup (adjointGroup .G2 K), (∀ x ∈ E, x * x = 1) →
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → Nat.card E ≤ 2 ^ (3 * f) := by
    intro E hE1 hEc
    have h1 := CFSG.Quasithin.B42G2.card_le_cube hKn (by omega) (Γ := E.map ψ)
      (by rintro _ ⟨x, hx, rfl⟩; rw [← map_mul, hE1 x hx, map_one])
      (by rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩; rw [← map_mul, ← map_mul, hEc x hx y hy])
    rw [Subgroup.card_map_of_injective hinjψ, hKn, ← pow_mul, mul_comm] at h1
    exact h1
  have hinner : ∀ z : adjointGroup .G2 K, z * z = 1 → z ≠ 1 → 3 * f + 2 ≤ dispRank (πC z) :=
    fun z hz hz1 => hdisp (ψ z) (by rw [← map_mul, hz, map_one])
      (fun h => hz1 (hinjψ (h.trans (map_one ψ).symm)))
  have houter : ∀ a ∈ A, (¬ ∃ g, πC g = a) → 2 ≤ dispRank a := by
    intro a ha hout
    set α := normAut πC hπC A hnormC ⟨a, ha⟩ with hαdef
    have hαinner : α ∉ inner (adjointGroup .G2 K) := fun h =>
      hout (mem_range_of_normAut_mem_inner hπC hnormC hZC hntM hirrC hsq ⟨a, ha⟩ h)
    have hαα : α ^ 2 = 1 := by
      rw [hαdef, ← map_pow]
      have : (⟨a, ha⟩ : A) ^ 2 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one, _root_.sq]
        exact hsq a ha)
      rw [this, map_one]
    have hα1 : α ≠ 1 := fun h => hαinner (h ▸ Subgroup.one_mem _)
    have hord : orderOf α = 2 := orderOf_eq_prime hαα hα1
    have hΘα : Θ α ≠ 1 := fun h => hαinner (by
      rw [← hΘker']
      exact MonoidHom.mem_ker.mpr h)
    obtain ⟨c₀, hc₀⟩ : ∃ c, Θ α c ≠ c := by
      by_contra h
      push Not at h
      exact hΘα (RingEquiv.ext h)
    have hδ : ∀ c, Θ α c = c ^ 2 ^ (f / 2) := by
      rcases hΘinv α hαα with h | ⟨-, h, -⟩
      · exact absurd h hΘα
      · exact h
    rcases even_G2_involution_inner_or_canonical_field hf K hKn α hord with h | ⟨-, hcan⟩
    · exact absurd h hαinner
    obtain ⟨β, ψ', hβ, hψ', -⟩ := hcan (Θ α).toRingHom hδ
    obtain ⟨g, hgg, hg1⟩ := exists_involution_of_entrywise α β ψ' (Θ α).toRingHom hβ hψ' hc₀
    have h1 := hinner _ hgg hg1
    have h2 : πC (α g * g⁻¹) = a * (πC g * a⁻¹ * (πC g)⁻¹) := by
      rw [map_mul, map_inv, hαdef, π_normAut]
      group
    rw [h2] at h1
    have h3 := dispRank_mul_le a (πC g * a⁻¹ * (πC g)⁻¹)
    rw [dispRank_conj, dispRank_inv_of_mul_self (hsq a ha)] at h3
    omega
  exact card_mul_card_fixed_lt_of_disp hπC hnormC hZC hntM hirrC Θ hΘker' hinv hmax hinner hAe
    hA1 houter

end G2

end CFSG.Quasithin.B42G2F
