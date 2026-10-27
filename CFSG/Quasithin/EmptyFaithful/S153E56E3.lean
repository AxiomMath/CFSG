module

public import CFSG.Quasithin.EmptyFaithful.S153E57A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417 CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise MatrixGroups

namespace S153E56e

section Abstract

variable {G : Type} [Group G]

abbrev MR (r : ℕ) : Type := Multiplicative (Fin r → Fin 2 → ZMod 2)

theorem card_MR (r : ℕ) : Nat.card (MR r) = 2 ^ (2 * r) := by
  have : Nat.card (MR r) = Nat.card (Fin r → Fin 2 → ZMod 2) :=
    Nat.card_congr Multiplicative.toAdd
  rw [this]
  simp [Nat.card_eq_fintype_card, ZMod.card, pow_mul]

theorem MR_sq {r : ℕ} (m : MR r) : m * m = 1 := by
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  rw [← ofAdd_toAdd m, ← ofAdd_add]
  have : Multiplicative.toAdd m + Multiplicative.toAdd m = 0 := by
    funext j k
    simp [h2]
  rw [this]
  rfl

theorem card_eq_card_mul_of_surj {A K : Subgroup G} {M' : Type*} [Group M'] (φ : ↥A →* M')
    (hs : Function.Surjective φ) (hk : ∀ x : ↥A, φ x = 1 ↔ (x : G) ∈ K) (hKA : K ≤ A) :
    Nat.card A = Nat.card K * Nat.card M' := by
  have hker : φ.ker = K.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, hk, Subgroup.mem_subgroupOf]
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hs, Subgroup.card_top] at h1
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKA).toEquiv] at h1
  exact h1.symm

structure NatStr (J R E : Subgroup G) (r : ℕ) (β : ↥J →* SL(2, ZMod 2)) (φ : ↥R →* MR r) : Prop where
  β_surj : Function.Surjective β
  β_ker : ∀ x : ↥J, β x = 1 ↔ (x : G) ∈ R
  φ_surj : Function.Surjective φ
  φ_ker : ∀ x : ↥R, φ x = 1 ↔ (x : G) ∈ E
  equiv : ∀ (m : ↥J) (x y : ↥R), (y : G) = (m : G) * (x : G) * (m : G)⁻¹ →
    φ y = Multiplicative.ofAdd (fun j => β m • Multiplicative.toAdd (φ x) j)

theorem exists_natStr {J R E : Subgroup G} {r : ℕ} (h : IsSumOfNatSL2ModulesN153 r J R R E) :
    ∃ (β : ↥J →* SL(2, ZMod 2)) (φ : ↥R →* MR r), NatStr J R E r β φ := by
  obtain ⟨β, φ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨β, φ, ⟨h1, h2, h3, h4, h5⟩⟩

theorem exists_sub_eq {r : ℕ} (b : SL(2, ZMod 2)) (hb : ∀ v : Fin 2 → ZMod 2, b • v = v → v = 0)
    (u : Fin r → Fin 2 → ZMod 2) :
    ∃ v : Fin r → Fin 2 → ZMod 2, (fun i => b • v i) - v = u := by
  let δ : (Fin r → Fin 2 → ZMod 2) →+ (Fin r → Fin 2 → ZMod 2) :=
    AddMonoidHom.mk' (fun v => (fun i => b • v i) - v) (fun v w => by
      funext i
      simp only [Pi.sub_apply, Pi.add_apply, smul_add]
      abel)
  have hinj : Function.Injective δ := by
    intro v w hvw
    obtain ⟨u, hu⟩ : ∃ u, u = v - w := ⟨_, rfl⟩
    have h0 : δ u = 0 := by
      rw [hu, map_sub, hvw]
      exact sub_self _
    have h1 : ∀ i, b • u i = u i := fun i => by
      have := congrFun h0 i
      simpa [δ, sub_eq_zero] using this
    have h2 : u = 0 := by
      funext i
      exact hb _ (h1 i)
    rw [h2] at hu
    exact sub_eq_zero.1 hu.symm
  obtain ⟨v, hv⟩ := Finite.injective_iff_surjective.1 hinj u
  exact ⟨v, hv⟩

namespace NatStr

variable {J R E : Subgroup G} {r : ℕ} {β : ↥J →* SL(2, ZMod 2)} {φ : ↥R →* MR r}

theorem comm_mem (h : NatStr J R E r β φ) {x y : G} (hx : x ∈ R) (hy : y ∈ R) :
    x * y * x⁻¹ * y⁻¹ ∈ E := by
  have h1 : φ (⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  simpa using (h.φ_ker _).1 h1

theorem sq_mem (h : NatStr J R E r β φ) {x : G} (hx : x ∈ R) : x * x ∈ E := by
  have h1 : φ (⟨x, hx⟩ * ⟨x, hx⟩) = 1 := by
    rw [map_mul]
    exact MR_sq _
  simpa using (h.φ_ker _).1 h1

theorem mem_E_of_eq (h : NatStr J R E r β φ) {ρ ρ' : G} (hρ : ρ ∈ R) (hρ' : ρ' ∈ R)
    (he : φ ⟨ρ, hρ⟩ = φ ⟨ρ', hρ'⟩) : ρ * ρ'⁻¹ ∈ E := by
  have h1 : φ (⟨ρ, hρ⟩ * ⟨ρ', hρ'⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, he]
    exact mul_inv_cancel _
  simpa using (h.φ_ker _).1 h1

theorem exists_comm (h : NatStr J R E r β φ) (hJR : ∀ j ∈ J, ∀ x ∈ R, j * x * j⁻¹ ∈ R)
    {j : G} (hj : j ∈ J) (hb : ∀ v : Fin 2 → ZMod 2, β ⟨j, hj⟩ • v = v → v = 0) :
    ∀ ρ ∈ R, ∃ x ∈ R, ρ * (j * x * j⁻¹ * x⁻¹)⁻¹ ∈ E := by
  intro ρ hρ
  obtain ⟨v, hv⟩ := exists_sub_eq (r := r) (β ⟨j, hj⟩) hb (Multiplicative.toAdd (φ ⟨ρ, hρ⟩))
  obtain ⟨x, hx⟩ := h.φ_surj (Multiplicative.ofAdd v)
  have hjx : j * (x : G) * j⁻¹ ∈ R := hJR j hj x x.2
  have hφjx : φ ⟨j * x * j⁻¹, hjx⟩ = Multiplicative.ofAdd (fun i => β ⟨j, hj⟩ • v i) := by
    have := h.equiv ⟨j, hj⟩ x ⟨j * x * j⁻¹, hjx⟩ rfl
    rw [this, hx]
    rfl
  refine ⟨x, x.2, ?_⟩
  have key : φ (⟨ρ, hρ⟩ * (⟨j * x * j⁻¹, hjx⟩ * x⁻¹)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_inv, hφjx, hx]
    have e : φ ⟨ρ, hρ⟩ = Multiplicative.ofAdd ((fun i => β ⟨j, hj⟩ • v i) - v) := by
      rw [hv]
      rfl
    rw [e, ofAdd_sub, div_eq_mul_inv]
    exact mul_inv_cancel _
  simpa using (h.φ_ker _).1 key

theorem eq_of_mem_E (h : NatStr J R E r β φ) {ρ ρ' : G} (hρ : ρ ∈ R) (hρ' : ρ' ∈ R)
    (hmem : ρ * ρ'⁻¹ ∈ E) : φ ⟨ρ, hρ⟩ = φ ⟨ρ', hρ'⟩ := by
  have h1 : φ (⟨ρ, hρ⟩ * ⟨ρ', hρ'⟩⁻¹) = 1 := (h.φ_ker _).2 (by simpa using hmem)
  rw [map_mul, map_inv] at h1
  exact mul_inv_eq_one.1 h1

theorem card_F [Finite G] (h : NatStr J R E r β φ) {F X : Subgroup G} (hFR : F ≤ R) (hXR : X ≤ R)
    (hFX : F ⊓ X = E) (hsup : F ⊔ X = R) (hcard : Nat.card F = Nat.card X) :
    Nat.card F = Nat.card E * 2 ^ r := by
  have hEF : E ≤ F := hFX ▸ inf_le_left
  have hEX : E ≤ X := hFX ▸ inf_le_right
  let φF : ↥F →* MR r := φ.comp (Subgroup.inclusion hFR)
  let φX : ↥X →* MR r := φ.comp (Subgroup.inclusion hXR)
  have hkF : ∀ x : ↥F, φF.rangeRestrict x = 1 ↔ (x : G) ∈ E := by
    intro x
    have h1 : φF.rangeRestrict x = 1 ↔ φF x = 1 := by
      constructor
      · intro h'
        have := congrArg Subtype.val h'
        simpa [MonoidHom.coe_rangeRestrict] using this
      · intro h'
        apply Subtype.ext
        simpa [MonoidHom.coe_rangeRestrict] using h'
    rw [h1]
    exact h.φ_ker (Subgroup.inclusion hFR x)
  have hkX : ∀ x : ↥X, φX.rangeRestrict x = 1 ↔ (x : G) ∈ E := by
    intro x
    have h1 : φX.rangeRestrict x = 1 ↔ φX x = 1 := by
      constructor
      · intro h'
        have := congrArg Subtype.val h'
        simpa [MonoidHom.coe_rangeRestrict] using this
      · intro h'
        apply Subtype.ext
        simpa [MonoidHom.coe_rangeRestrict] using h'
    rw [h1]
    exact h.φ_ker (Subgroup.inclusion hXR x)
  have hcF : Nat.card F = Nat.card E * Nat.card φF.range :=
    card_eq_card_mul_of_surj φF.rangeRestrict (MonoidHom.rangeRestrict_surjective φF) hkF hEF
  have hcX : Nat.card X = Nat.card E * Nat.card φX.range :=
    card_eq_card_mul_of_surj φX.rangeRestrict (MonoidHom.rangeRestrict_surjective φX) hkX hEX
  have hinf : φF.range ⊓ φX.range = ⊥ := by
    rw [eq_bot_iff]
    rintro m ⟨⟨f, rfl⟩, ⟨x, hxm⟩⟩
    rw [Subgroup.mem_bot]
    have hmem := h.mem_E_of_eq (ρ := (f : G)) (ρ' := (x : G)) (hFR f.2) (hXR x.2) hxm.symm
    have hfX : (f : G) ∈ X := by
      have e : (f : G) = ((f : G) * (x : G)⁻¹) * x := by group
      rw [e]
      exact X.mul_mem (hEX hmem) x.2
    have hfE : (f : G) ∈ E := by
      rw [← hFX]
      exact ⟨f.2, hfX⟩
    exact (h.φ_ker (Subgroup.inclusion hFR f)).2 hfE
  have hsup' : φF.range ⊔ φX.range = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨ρ, rfl⟩ := h.φ_surj m
    have h1 : F.subgroupOf R ⊔ X.subgroupOf R = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hFR hXR, hsup, Subgroup.subgroupOf_self]
    have h2 : F.subgroupOf R ⊔ X.subgroupOf R ≤ (φF.range ⊔ φX.range).comap φ := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · exact Subgroup.mem_sup_left ⟨⟨x, hx⟩, rfl⟩
      · exact Subgroup.mem_sup_right ⟨⟨x, hx⟩, rfl⟩
    have h3 : ρ ∈ F.subgroupOf R ⊔ X.subgroupOf R := by
      rw [h1]
      exact Subgroup.mem_top ρ
    exact h2 h3
  have hcard' : Nat.card ↥(φF.range ⊔ φX.range) = Nat.card φF.range * Nat.card φX.range :=
    S153E57.card_sup_of_inf_eq_bot hinf
  rw [hsup', Subgroup.card_top, card_MR] at hcard'
  have hpos : 0 < Nat.card E := Nat.card_pos
  have hAA : Nat.card φF.range = Nat.card φX.range :=
    Nat.eq_of_mul_eq_mul_left hpos (by rw [← hcF, ← hcX, hcard])
  have hsq : Nat.card φF.range * Nat.card φF.range = 2 ^ r * 2 ^ r := by
    rw [← pow_add, ← two_mul, hcard', hAA]
  rw [hcF, Nat.mul_self_inj.1 hsq]

theorem card_ge [Finite G] (h : NatStr J R E r β φ) {C V₀ : Subgroup G} (hCR : C ≤ R)
    (hC : ∀ ρ ∈ R, ∃ c ∈ C, ρ * c⁻¹ ∈ E) (hV₀ : V₀ ≤ C ⊓ E) :
    Nat.card V₀ * 2 ^ (2 * r) ≤ Nat.card C := by
  let ψ : ↥C →* MR r := φ.comp (Subgroup.inclusion hCR)
  have hsurj : Function.Surjective ψ := by
    intro m
    obtain ⟨ρ, rfl⟩ := h.φ_surj m
    obtain ⟨c, hc, hce⟩ := hC ρ ρ.2
    exact ⟨⟨c, hc⟩, (eq_of_mem_E h ρ.2 (hCR hc) hce).symm⟩
  have hk : ∀ x : ↥C, ψ x = 1 ↔ (x : G) ∈ C ⊓ E := by
    intro x
    rw [Subgroup.mem_inf]
    constructor
    · intro h1
      exact ⟨x.2, (h.φ_ker (Subgroup.inclusion hCR x)).1 h1⟩
    · intro h1
      exact (h.φ_ker (Subgroup.inclusion hCR x)).2 h1.2
  have hcard := card_eq_card_mul_of_surj ψ hsurj hk inf_le_left
  have hle : Nat.card V₀ ≤ Nat.card ↥(C ⊓ E) := Subgroup.card_le_of_le hV₀
  rw [hcard, card_MR]
  exact Nat.mul_le_mul_right _ hle

end NatStr

end Abstract

end S153E56e

end CFSG.Quasithin
