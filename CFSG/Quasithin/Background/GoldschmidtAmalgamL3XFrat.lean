module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3GTrans
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D}

omit [Finite D] in
theorem exists_kernel_subgroup (A Y₁ Y₂ : Subgroup D)
    (hA₁ : A ≤ Subgroup.normalizer (Y₁ : Set D)) (hA₂ : A ≤ Subgroup.normalizer (Y₂ : Set D)) :
    ∃ K : Subgroup D, (∀ g, g ∈ K ↔ g ∈ A ∧ ∀ w ∈ Y₂, g * w * g⁻¹ * w⁻¹ ∈ Y₁) := by
  have c₂ : ∀ a ∈ A, ∀ w ∈ Y₂, a * w * a⁻¹ ∈ Y₂ := fun a ha w hw =>
    (Subgroup.mem_normalizer_iff.mp (hA₂ ha) w).mp hw
  have c₁ : ∀ a ∈ A, ∀ w ∈ Y₁, a * w * a⁻¹ ∈ Y₁ := fun a ha w hw =>
    (Subgroup.mem_normalizer_iff.mp (hA₁ ha) w).mp hw
  refine ⟨{ carrier := {g | g ∈ A ∧ ∀ w ∈ Y₂, g * w * g⁻¹ * w⁻¹ ∈ Y₁}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun g => Iff.rfl⟩
  · rintro g g' ⟨hg, hgw⟩ ⟨hg', hgw'⟩
    refine ⟨A.mul_mem hg hg', fun w hw => ?_⟩
    have h2 := hgw (g' * w * g'⁻¹) (c₂ g' hg' w hw)
    have e : g * g' * w * (g * g')⁻¹ * w⁻¹ = (g * (g' * w * g'⁻¹) * g⁻¹ * (g' * w * g'⁻¹)⁻¹) *
        (g' * w * g'⁻¹ * w⁻¹) := by group
    rw [e]
    exact Y₁.mul_mem h2 (hgw' w hw)
  · exact ⟨A.one_mem, fun w _ => by simp⟩
  · rintro g ⟨hg, hgw⟩
    refine ⟨A.inv_mem hg, fun w hw => ?_⟩
    have h2 := hgw (g⁻¹ * w * g⁻¹⁻¹) (c₂ g⁻¹ (A.inv_mem hg) w hw)
    have e : g⁻¹ * w * g⁻¹⁻¹ * w⁻¹ = (g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ * (g⁻¹ * w * g⁻¹⁻¹)⁻¹)⁻¹ := by
      group
    rw [e]
    exact Y₁.inv_mem h2

theorem GoldHyp.eq_bot_of_acts_trivially (h : GoldHyp A B) {Y₁ Z Y₂ : Subgroup D}
    (hYZ : Y₁ ≤ Z) (hZY : Z ≤ Y₂) (hZT : Z ≤ A ⊓ B)
    (hA₁ : A ≤ Subgroup.normalizer (Y₁ : Set D)) (hA₂ : A ≤ Subgroup.normalizer (Y₂ : Set D))
    (hZB : B ≤ Subgroup.normalizer (Z : Set D)) {u : D} (huT : u ∈ A ⊓ B)
    (huQ : u ∉ pCoreOf 2 A) (hu : ∀ w ∈ Y₂, u * w * u⁻¹ * w⁻¹ ∈ Y₁) :
    Z = ⊥ := by
  obtain ⟨K, hK⟩ := exists_kernel_subgroup A Y₁ Y₂ hA₁ hA₂
  have hKA : ∀ g ∈ K, g ∈ A := fun g hg => ((hK g).mp hg).1
  have hKw : ∀ g ∈ K, ∀ w ∈ Y₂, g * w * g⁻¹ * w⁻¹ ∈ Y₁ := fun g hg => ((hK g).mp hg).2
  have hQA : pCoreOf 2 A ≤ A := pCoreOf_le 2 A
  have hAN : A ≤ Subgroup.normalizer (pCoreOf 2 A : Set D) := le_normalizer_pCoreOf 2 A
  have hKconj : ∀ a ∈ A, ∀ g ∈ K, a * g * a⁻¹ ∈ K := by
    intro a ha g hg
    refine (hK _).mpr ⟨A.mul_mem (A.mul_mem ha (hKA g hg)) (A.inv_mem ha), fun w hw => ?_⟩
    have hw' : a⁻¹ * w * a⁻¹⁻¹ ∈ Y₂ :=
      (Subgroup.mem_normalizer_iff.mp (hA₂ (A.inv_mem ha)) w).mp hw
    have h1 := (Subgroup.mem_normalizer_iff.mp (hA₁ ha) _).mp (hKw g hg _ hw')
    have e : a * (g * (a⁻¹ * w * a⁻¹⁻¹) * g⁻¹ * (a⁻¹ * w * a⁻¹⁻¹)⁻¹) * a⁻¹ =
        a * g * a⁻¹ * w * (a * g * a⁻¹)⁻¹ * w⁻¹ := by group
    rw [e] at h1
    exact h1
  have huK : u ∈ K := (hK u).mpr ⟨huT.1, hu⟩
  have hTKQ : A ⊓ B ≤ K ⊔ pCoreOf 2 A := by
    intro t ht
    by_cases htQ : t ∈ pCoreOf 2 A
    · exact Subgroup.mem_sup_right htQ
    · have h1 : t * u⁻¹ ∈ pCoreOf 2 A :=
        GoldAmL3.mul_inv_mem_of_relIndex_eq_two h.vertex_left.relIndex_pCoreOf_T ht huT htQ huQ
      have e : t = (t * u⁻¹) * u := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left huK)
  obtain ⟨c, hcA, hcB⟩ : ∃ c ∈ A, c ∉ B := by
    by_contra hcon
    push Not at hcon
    have h1 := h.relIndex_left
    rw [inf_eq_left.mpr (fun a ha => hcon a ha), Subgroup.relIndex_self] at h1
    omega
  have hconjKQ : conjSub c (K ⊔ pCoreOf 2 A) ≤ K ⊔ pCoreOf 2 A := by
    rw [conjSub_sup]
    refine sup_le_sup ?_ ?_
    · intro y hy
      rw [mem_conjSub] at hy
      have := hKconj c hcA _ hy
      have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
      rwa [e] at this
    · intro y hy
      rw [mem_conjSub] at hy
      have := (Subgroup.mem_normalizer_iff.mp (hAN hcA) _).mp hy
      have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
      rwa [e] at this
  have hAKQ : A ≤ K ⊔ pCoreOf 2 A :=
    (h.sup_conjSub_inf_eq_left hcA hcB).symm.le.trans
      (sup_le hTKQ ((conjSub_mono c hTKQ).trans hconjKQ))
  obtain ⟨y, hyA, hy3⟩ := h.vertex_left.exists_order_three
  have hyB : y ∉ B := fun hyB => h.vertex_left.not_mem_of_orderOf hy3 ⟨hyA, hyB⟩
  have hyKQ : y ∈ ((K ⊔ pCoreOf 2 A : Subgroup D) : Set D) := hAKQ hyA
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K (pCoreOf 2 A)
    (fun g hg => hAN (hKA g hg))] at hyKQ
  obtain ⟨k, hkK, q, hqQ, hkq⟩ := Set.mem_mul.mp hyKQ
  have hqA : q ∈ A := hQA hqQ
  have hy3' : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  have hq3K : q ^ 3 ∈ K := by
    have e : q ^ 3 = (k * (q * k * q⁻¹) * (q ^ 2 * k * (q ^ 2)⁻¹))⁻¹ * y ^ 3 := by
      rw [← hkq, pow_three' (k * q)]
      group
    rw [e, hy3', mul_one]
    exact K.inv_mem (K.mul_mem (K.mul_mem hkK (hKconj q hqA k hkK))
      (hKconj (q ^ 2) (A.pow_mem hqA 2) k hkK))
  obtain ⟨n, hn⟩ := h.vertex_left.isPGroup ⟨q, h.vertex_left.pCoreOf_le hqQ⟩
  have hq2n : q ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  obtain ⟨a, b, hab⟩ : IsCoprime ((3 : ℕ) : ℤ) ((2 ^ n : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right n (by norm_num))
  have hqK : q ∈ K := by
    have e : q = (q ^ 3) ^ a * (q ^ (2 ^ n)) ^ b := by
      have h1 : q ^ (a * (3 : ℕ) + b * ((2 ^ n : ℕ) : ℤ)) = q := by
        rw [hab, zpow_one]
      calc q = q ^ (a * (3 : ℕ) + b * ((2 ^ n : ℕ) : ℤ)) := h1.symm
        _ = (q ^ 3) ^ a * (q ^ (2 ^ n)) ^ b := by
          rw [zpow_add, zpow_mul', zpow_mul']
          simp only [zpow_natCast]
    rw [e, hq2n, one_zpow, mul_one]
    exact K.zpow_mem hq3K a
  have hyK : y ∈ K := by
    rw [← hkq]
    exact K.mul_mem hkK hqK
  have hnorm : ∀ g ∈ K, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := by
    intro g hg z hz
    have e : g * z * g⁻¹ = (g * z * g⁻¹ * z⁻¹) * z := by group
    rw [e]
    exact Z.mul_mem (hYZ (hKw g hg z (hZY hz))) hz
  have hyN : y ∈ Subgroup.normalizer (Z : Set D) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨fun hz => hnorm y hyK z hz, fun hz => ?_⟩
    have := hnorm y⁻¹ (K.inv_mem hyK) _ hz
    have e : y⁻¹ * (y * z * y⁻¹) * y⁻¹⁻¹ = z := by group
    rwa [e] at this
  obtain ⟨x₃, hxB, hx3⟩ := h.vertex_right.exists_order_three
  have hxA : x₃ ∉ A := fun hxA => h.vertex_right.not_mem_of_orderOf hx3 ⟨hxA, hxB⟩
  exact h.eq_bot_of_normalizes_order_three hZT hxB hyA hx3 hy3 hxA hyB (hZB hxB) hyN

end GoldAmL

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem eq_bot_of_acts_trivially_A {x y : CosetGeom (A ⊔ B) A B}
    (hxy : (graph (A ⊔ B) A B).Adj x y) (hx : vtype x = false) {Y₁ Z Y₂ : Subgroup D}
    (hYZ : Y₁ ≤ Z) (hZY : Z ≤ Y₂) (hZT : Z ≤ stab x ⊓ stab y)
    (hA₁ : stab x ≤ Subgroup.normalizer (Y₁ : Set D))
    (hA₂ : stab x ≤ Subgroup.normalizer (Y₂ : Set D))
    (hZB : stab y ≤ Subgroup.normalizer (Z : Set D)) {u : D} (hux : u ∈ stab x ⊓ stab y)
    (huQ : u ∉ ballStab 1 x) (hu : ∀ w ∈ Y₂, u * w * u⁻¹ * w⁻¹ ∈ Y₁) : Z = ⊥ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hxy hx
  have hsA : stab (g • γ₀ (A ⊔ B) A B) = conjSub (g : D) A := by
    rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B)]
  have hsB : stab (g • γ₁ (A ⊔ B) A B) = conjSub (g : D) B := by
    rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B)]
  have hle := pCoreOf_stab_le_ballStab_one h.gold.amalgamHyp (γ₀ (A ⊔ B) A B)
  rw [stab_γ₀ (le_sup_left : A ≤ A ⊔ B)] at hle
  rw [hsA] at hA₁ hA₂
  rw [hsB] at hZB
  rw [hsA, hsB] at hZT hux
  refine (conjSub_eq_bot_iff ((g : D)⁻¹)).mp (h.gold.eq_bot_of_acts_trivially
    (Y₁ := conjSub ((g : D)⁻¹) Y₁) (Z := conjSub ((g : D)⁻¹) Z) (Y₂ := conjSub ((g : D)⁻¹) Y₂)
    (conjSub_mono _ hYZ) (conjSub_mono _ hZY) ?_ ?_ ?_ ?_ (u := (g : D)⁻¹ * u * g) ?_ ?_ ?_)
  · exact le_inf ((le_conjSub_iff _).mp (le_inf_iff.mp hZT).1)
      ((le_conjSub_iff _).mp (le_inf_iff.mp hZT).2)
  · have := conjSub_le_normalizer (g := (g : D)⁻¹) hA₁
    rwa [conjSub_conjSub_inv] at this
  · have := conjSub_le_normalizer (g := (g : D)⁻¹) hA₂
    rwa [conjSub_conjSub_inv] at this
  · have := conjSub_le_normalizer (g := (g : D)⁻¹) hZB
    rwa [conjSub_conjSub_inv] at this
  · exact ⟨mem_conjSub.mp hux.1, mem_conjSub.mp hux.2⟩
  · exact fun hq => huQ (by
      rw [ballStab_smul, mem_conjSub]
      exact hle hq)
  · intro w hw
    rw [mem_conjSub] at hw ⊢
    have e : ((g : D)⁻¹)⁻¹ * ((g : D)⁻¹ * u * g * w * ((g : D)⁻¹ * u * g)⁻¹ * w⁻¹) * (g : D)⁻¹ =
        u * (((g : D)⁻¹)⁻¹ * w * (g : D)⁻¹) * u⁻¹ * (((g : D)⁻¹)⁻¹ * w * (g : D)⁻¹)⁻¹ := by
      group
    rw [e]
    exact hu _ hw

theorem eq_bot_of_acts_trivially_B {x y : CosetGeom (A ⊔ B) A B}
    (hxy : (graph (A ⊔ B) A B).Adj x y) (hy : vtype y = true) {Y₁ Z Y₂ : Subgroup D}
    (hYZ : Y₁ ≤ Z) (hZY : Z ≤ Y₂) (hZT : Z ≤ stab x ⊓ stab y)
    (hB₁ : stab y ≤ Subgroup.normalizer (Y₁ : Set D))
    (hB₂ : stab y ≤ Subgroup.normalizer (Y₂ : Set D))
    (hZA : stab x ≤ Subgroup.normalizer (Z : Set D)) {u : D} (huy : u ∈ stab x ⊓ stab y)
    (huQ : u ∉ ballStab 1 y) (hu : ∀ w ∈ Y₂, u * w * u⁻¹ * w⁻¹ ∈ Y₁) : Z = ⊥ := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB hxy (vtype_eq_false_of_adj hxy.symm hy)
  have hsA : stab (g • γ₀ (A ⊔ B) A B) = conjSub (g : D) A := by
    rw [stab_smul, stab_γ₀ (le_sup_left : A ≤ A ⊔ B)]
  have hsB : stab (g • γ₁ (A ⊔ B) A B) = conjSub (g : D) B := by
    rw [stab_smul, stab_γ₁ (le_sup_right : B ≤ A ⊔ B)]
  have hle := pCoreOf_stab_le_ballStab_one h.gold.amalgamHyp (γ₁ (A ⊔ B) A B)
  rw [stab_γ₁ (le_sup_right : B ≤ A ⊔ B)] at hle
  rw [hsB] at hB₁ hB₂
  rw [hsA] at hZA
  rw [hsA, hsB] at hZT huy
  refine (conjSub_eq_bot_iff ((g : D)⁻¹)).mp (h.gold.symm.eq_bot_of_acts_trivially
    (Y₁ := conjSub ((g : D)⁻¹) Y₁) (Z := conjSub ((g : D)⁻¹) Z) (Y₂ := conjSub ((g : D)⁻¹) Y₂)
    (conjSub_mono _ hYZ) (conjSub_mono _ hZY) ?_ ?_ ?_ ?_ (u := (g : D)⁻¹ * u * g) ?_ ?_ ?_)
  · exact le_inf ((le_conjSub_iff _).mp (le_inf_iff.mp hZT).2)
      ((le_conjSub_iff _).mp (le_inf_iff.mp hZT).1)
  · have := conjSub_le_normalizer (g := (g : D)⁻¹) hB₁
    rwa [conjSub_conjSub_inv] at this
  · have := conjSub_le_normalizer (g := (g : D)⁻¹) hB₂
    rwa [conjSub_conjSub_inv] at this
  · have := conjSub_le_normalizer (g := (g : D)⁻¹) hZA
    rwa [conjSub_conjSub_inv] at this
  · exact ⟨mem_conjSub.mp huy.2, mem_conjSub.mp huy.1⟩
  · exact fun hq => huQ (by
      rw [ballStab_smul, mem_conjSub]
      exact hle hq)
  · intro w hw
    rw [mem_conjSub] at hw ⊢
    have e : ((g : D)⁻¹)⁻¹ * ((g : D)⁻¹ * u * g * w * ((g : D)⁻¹ * u * g)⁻¹ * w⁻¹) * (g : D)⁻¹ =
        u * (((g : D)⁻¹)⁻¹ * w * (g : D)⁻¹) * u⁻¹ * (((g : D)⁻¹)⁻¹ * w * (g : D)⁻¹)⁻¹ := by
      group
    rw [e]
    exact hu _ hw

theorem eq_bot_of_acts_trivially {x y : CosetGeom (A ⊔ B) A B}
    (hxy : (graph (A ⊔ B) A B).Adj x y) {Y₁ Z Y₂ : Subgroup D}
    (hYZ : Y₁ ≤ Z) (hZY : Z ≤ Y₂) (hZT : Z ≤ stab x ⊓ stab y)
    (hx₁ : stab x ≤ Subgroup.normalizer (Y₁ : Set D))
    (hx₂ : stab x ≤ Subgroup.normalizer (Y₂ : Set D))
    (hy : stab y ≤ Subgroup.normalizer (Z : Set D)) {u : D} (hu : u ∈ stab x ⊓ stab y)
    (huQ : u ∉ ballStab 1 x) (hY : ∀ w ∈ Y₂, u * w * u⁻¹ * w⁻¹ ∈ Y₁) : Z = ⊥ := by
  cases hvx : vtype x
  · exact h.eq_bot_of_acts_trivially_A hxy hvx hYZ hZY hZT hx₁ hx₂ hy hu huQ hY
  · have hZT' : Z ≤ stab y ⊓ stab x := by rwa [inf_comm]
    have hu' : u ∈ stab y ⊓ stab x := by rwa [inf_comm]
    exact h.eq_bot_of_acts_trivially_B hxy.symm hvx hYZ hZY hZT' hx₁ hx₂ hy hu' huQ hY

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
