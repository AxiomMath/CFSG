module

public import CFSG.Quasithin.EmptyFaithful.SBc17BlkSpec
public import CFSG.Quasithin.EmptyFaithful.SBc17In
public import CFSG.Quasithin.EmptyFaithful.SBc13J1Aux
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc17

theorem charP_two_of_card_eq_pow {F : Type} [Field F] [Fintype F] {n : ℕ}
    (h : Fintype.card F = 2 ^ n) : CharP F 2 := by
  obtain ⟨p, hpc, m, hprime, hm⟩ := FiniteField.card' F
  have hdvd : p ∣ 2 ^ n := by
    rw [← h, hm]
    exact dvd_pow_self p m.pos.ne'
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hdvd)
  rwa [hp2] at hpc

theorem exists_mulAut_comp {L S : Type*} [Group L] [Group S] (α : L →* S)
    (hα : Function.Surjective α) (c : L ≃* L) (hc : ∀ x, α (c x) = 1 ↔ α x = 1) :
    ∃ φ : MulAut S, ∀ x, φ (α x) = α (c x) := by
  have hwd : ∀ d : L ≃* L, (∀ x, α (d x) = 1 ↔ α x = 1) → ∀ x y, α x = α y → α (d x) = α (d y) := by
    intro d hd x y h
    have h1 : α (d (x * y⁻¹)) = 1 := (hd _).mpr (by rw [map_mul, map_inv, h, mul_inv_cancel])
    rwa [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one] at h1
  have hc' : ∀ x, α (c.symm x) = 1 ↔ α x = 1 := by
    intro x
    rw [← hc (c.symm x), c.apply_symm_apply]
  obtain ⟨f, hf⟩ : ∃ f : S → S, ∀ x, f (α x) = α (c x) :=
    ⟨fun s => α (c (Function.surjInv hα s)), fun x => hwd c hc _ _ (Function.surjInv_eq hα (α x))⟩
  obtain ⟨f', hf'⟩ : ∃ f' : S → S, ∀ x, f' (α x) = α (c.symm x) :=
    ⟨fun s => α (c.symm (Function.surjInv hα s)),
      fun x => hwd c.symm hc' _ _ (Function.surjInv_eq hα (α x))⟩
  refine ⟨{ toFun := f, invFun := f', left_inv := ?_, right_inv := ?_, map_mul' := ?_ }, hf⟩
  · intro s
    obtain ⟨x, rfl⟩ := hα s
    simp only [hf, hf', MulEquiv.symm_apply_apply]
  · intro s
    obtain ⟨x, rfl⟩ := hα s
    simp only [hf, hf', MulEquiv.apply_symm_apply]
  · intro s t
    obtain ⟨x, rfl⟩ := hα s
    obtain ⟨y, rfl⟩ := hα t
    simp only [← map_mul, hf]

section Block

variable {G : Type} [Group G]

theorem map_eq_one_iff_mem_pCoreOf {L : Subgroup G} {S : Type*} [Group S] {α : ↥L →* S}
    (hker : α.ker = CFSG.pCore 2 ↥L) (x : ↥L) : α x = 1 ↔ (x : G) ∈ pCoreOf 2 L := by
  rw [← MonoidHom.mem_ker, hker, ← SBc13.pCoreOf_subgroupOf_eq_pCore_J1, Subgroup.mem_subgroupOf]

theorem coe_normalizerMonoidHom (L : Subgroup G) {k : G} (hk : k ∈ Subgroup.normalizer (L : Set G))
    (x : ↥L) : ((Subgroup.normalizerMonoidHom L ⟨k, hk⟩ x : ↥L) : G) = k * x * k⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨k, hk⟩ x

theorem map_normalizerMonoidHom_eq_one_iff {L : Subgroup G} {S : Type*} [Group S] {α : ↥L →* S}
    (hker : α.ker = CFSG.pCore 2 ↥L) {k : G} (hk : k ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    α (Subgroup.normalizerMonoidHom L ⟨k, hk⟩ x) = 1 ↔ α x = 1 := by
  rw [map_eq_one_iff_mem_pCoreOf hker, map_eq_one_iff_mem_pCoreOf hker, coe_normalizerMonoidHom]
  refine ⟨fun h => ?_, conj_mem_pCoreOf hk⟩
  simpa [mul_assoc] using conj_mem_pCoreOf (inv_mem hk) h

theorem mem_innerSub_of_std (hInn : InnerAutStatement) (hLe : LeUpperStatement)
    {L B W : Subgroup G} {k : G} {F : Type} [Field F] [Fintype F] [CharP F 2]
    (h4 : 4 ≤ Fintype.card F) {α : ↥L →* SL2 F} (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L)
    (hbor : ∀ g : SL2 F, g ∈ borelSub F ↔ ∃ (x : G) (hx : x ∈ L), x ∈ B ∧ α ⟨x, hx⟩ = g)
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hW : IsPGroup 2 W)
    (hBW : B ≤ Subgroup.normalizer (W : Set G)) (hcomm : ∀ b ∈ B, ⁅b, k⁆ ∈ W) :
    k ∈ innerSub L := by
  classical
  obtain ⟨φ, hφ⟩ := exists_mulAut_comp α hα (Subgroup.normalizerMonoidHom L ⟨k, hk⟩)
    (map_normalizerMonoidHom_eq_one_iff hker hk)
  have hWh2 : IsPGroup 2 ((W.subgroupOf L).map α) := (hW.comap_subtype (K := L)).map α
  have hconj : ∀ u ∈ upperSub F, ∀ w ∈ (W.subgroupOf L).map α,
      u * w * u⁻¹ ∈ (W.subgroupOf L).map α := by
    intro u hu w hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    obtain ⟨x, hxL, hxB, hxu⟩ := (hbor u).mp (upperSub_le_borelSub hu)
    refine Subgroup.mem_map.mpr ⟨⟨x, hxL⟩ * y * ⟨x, hxL⟩⁻¹, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hBW hxB) (y : G)).mp (Subgroup.mem_subgroupOf.mp hy)
    · rw [map_mul, map_mul, map_inv, hxu]
  have hnorm : upperSub F ≤
      Subgroup.normalizer (((W.subgroupOf L).map α : Subgroup (SL2 F)) : Set (SL2 F)) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hconj u hu w hw, fun hw => ?_⟩
    simpa [mul_assoc] using hconj u⁻¹ (inv_mem hu) _ hw
  have hle : (W.subgroupOf L).map α ≤ upperSub F := hLe h4 hWh2 hnorm
  have hφB : ∀ b ∈ borelSub F, φ b * b⁻¹ ∈ upperSub F := by
    intro b hb
    obtain ⟨x, hxL, hxB, rfl⟩ := (hbor b).mp hb
    refine hle (Subgroup.mem_map.mpr
      ⟨Subgroup.normalizerMonoidHom L ⟨k, hk⟩ ⟨x, hxL⟩ * ⟨x, hxL⟩⁻¹, ?_, ?_⟩)
    · rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, coe_normalizerMonoidHom, Subgroup.coe_inv]
      have h1 : ⁅k, x⁆ ∈ W := by
        rw [← commutatorElement_inv]
        exact inv_mem (hcomm x hxB)
      exact h1
    · rw [map_mul, map_inv, hφ]
  obtain ⟨g, hg⟩ := hInn h4 φ hφB
  obtain ⟨ℓ, hℓ⟩ := hα g
  have hcM : (ℓ : G)⁻¹ * k ∈ cMod L := by
    refine mem_cMod.mpr ⟨mul_mem (inv_mem (Subgroup.le_normalizer ℓ.2)) hk, fun x hx => ?_⟩
    have hY : α (⟨x, hx⟩ * ℓ⁻¹ * (Subgroup.normalizerMonoidHom L ⟨k, hk⟩ ⟨x, hx⟩)⁻¹ * ℓ) = 1 := by
      have h1 : α (Subgroup.normalizerMonoidHom L ⟨k, hk⟩ ⟨x, hx⟩) = g * α ⟨x, hx⟩ * g⁻¹ := by
        rw [← hφ, hg]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hℓ, h1]
      group
    have h2 := (map_eq_one_iff_mem_pCoreOf hker _).mp hY
    have e : ⁅x, (ℓ : G)⁻¹ * k⁆ =
        ((⟨x, hx⟩ * ℓ⁻¹ * (Subgroup.normalizerMonoidHom L ⟨k, hk⟩ ⟨x, hx⟩)⁻¹ * ℓ : ↥L) : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_normalizerMonoidHom, commutatorElement_def]
      group
    rw [e]
    exact h2
  exact mem_innerSub_iff.mpr ⟨ℓ, ℓ.2, _, hcM, (mul_inv_cancel_left (ℓ : G) k).symm⟩

end Block

theorem mem_innerSub_of_commutator_two (hStd : StdPositionStatement) (hInn : InnerAutStatement)
    (hLe : LeUpperStatement) {G : Type} [Group G] [Finite G] {L B W : Subgroup G} {k : G} {n : ℕ}
    (hn : 1 < n) (hlin : IsLin2Type L n) (hB : IsBorelOfBlock L B)
    (hk : k ∈ Subgroup.normalizer (L : Set G)) (hW : IsPGroup 2 W)
    (hBW : B ≤ Subgroup.normalizer (W : Set G)) (hcomm : ∀ b ∈ B, ⁅b, k⁆ ∈ W) :
    k ∈ innerSub L := by
  obtain ⟨F, hF, hFin, hcard, α, hα, hker, -⟩ := hlin
  classical
  have : CharP F 2 := charP_two_of_card_eq_pow hcard
  have h4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨g₀, hg₀, -, hbor⟩ := hStd h4 α hα hker hB
  have hk' : g₀⁻¹ * k * g₀ ∈ Subgroup.normalizer (L : Set G) :=
    mul_mem (mul_mem (inv_mem (Subgroup.le_normalizer hg₀)) hk) (Subgroup.le_normalizer hg₀)
  have hBW' : conjSub g₀⁻¹ B ≤ Subgroup.normalizer (conjSub g₀⁻¹ W : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' : g₀ * x * g₀⁻¹ ∈ B := by simpa [mem_conjSub] using hx
    have h1 := Subgroup.mem_normalizer_iff.mp (hBW hx') (g₀ * y * g₀⁻¹)
    rw [mem_conjSub, mem_conjSub]
    simp only [inv_inv]
    convert h1 using 2
    group
  have hcomm' : ∀ b ∈ conjSub g₀⁻¹ B, ⁅b, g₀⁻¹ * k * g₀⁆ ∈ conjSub g₀⁻¹ W := by
    intro b hb
    have hb' : g₀ * b * g₀⁻¹ ∈ B := by simpa [mem_conjSub] using hb
    have h1 := hcomm _ hb'
    rw [mem_conjSub, inv_inv]
    convert h1 using 1
    simp only [commutatorElement_def]
    group
  have key : g₀⁻¹ * k * g₀ ∈ innerSub L :=
    mem_innerSub_of_std hInn hLe h4 hα hker hbor hk' (hW.map _) hBW' hcomm'
  have h5 : g₀ * (g₀⁻¹ * k * g₀) * g₀⁻¹ = k := by group
  rw [← h5]
  exact mul_mem (mul_mem (mem_innerSub_of_mem_J hg₀) key) (inv_mem (mem_innerSub_of_mem_J hg₀))

end SBc17

end CFSG.Quasithin
