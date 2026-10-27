module

public import CFSG.RankThree.PartTwo.KFacts.KS10Wreath

public section

namespace CFSG.RankThree.PartTwo.Sec10.Item107Proof

open CFSG.RankThree.PartTwo.KFacts

section Generic

variable {W T : Type*} [Group W] [Group T]

theorem card_comap_of_surjective [Finite W] (π : W →* T) (hπ : Function.Surjective π)
    (H : Subgroup T) : Nat.card (H.comap π) = Nat.card π.ker * Nat.card H := by
  set φ : H.comap π →* T := π.comp (H.comap π).subtype with hφ
  have hrange : φ.range = H := by
    ext t
    constructor
    · rintro ⟨w, rfl⟩
      exact w.2
    · intro ht
      obtain ⟨w, rfl⟩ := hπ t
      exact ⟨⟨w, ht⟩, rfl⟩
  have hker : Nat.card φ.ker = Nat.card π.ker := by
    have : φ.ker.map (H.comap π).subtype = π.ker := by
      ext w
      constructor
      · rintro ⟨w', hw', rfl⟩
        exact hw'
      · intro hw
        have hw' : w ∈ H.comap π := by
          rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hw]
          exact H.one_mem
        exact ⟨⟨w, hw'⟩, hw, rfl⟩
    rw [← this, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  rw [card_eq_card_ker_mul_card_range φ, hker, hrange]

theorem card_le_card_map_mul [Finite W] (f : W →* T) (H : Subgroup W) :
    Nat.card H ≤ Nat.card (H.map f) * Nat.card f.ker := by
  set φ : H →* T := f.comp H.subtype with hφ
  have hrange : φ.range = H.map f := by rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : Nat.card φ.ker ≤ Nat.card f.ker := by
    have hinj : Function.Injective (fun k : φ.ker => (⟨((k : H) : W), k.2⟩ : f.ker)) := by
      intro k k' hk
      have h := congrArg Subtype.val hk
      exact Subtype.ext (Subtype.ext h)
    exact Nat.card_le_card_of_injective _ hinj
  rw [card_eq_card_ker_mul_card_range φ, hrange, mul_comm]
  exact Nat.mul_le_mul_left _ hker

theorem comap_le_of_le_map (π : W →* T) {K : Subgroup W} (hK : π.ker ≤ K) {J : Subgroup T}
    (hJ : J ≤ K.map π) : J.comap π ≤ K := by
  intro w hw
  obtain ⟨k, hkK, hk⟩ := hJ hw
  have h1 : k⁻¹ * w ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hk, inv_mul_cancel]
  have h2 := K.mul_mem hkK (hK h1)
  rwa [mul_inv_cancel_left] at h2

@[expose] def commHom (hcentral : ∀ u w v : W, (u * w * u⁻¹ * w⁻¹) * v = v * (u * w * u⁻¹ * w⁻¹))
    (u : W) : W →* W where
  toFun w := u * w * u⁻¹ * w⁻¹
  map_one' := by group
  map_mul' w w' := by
    have hz : w * (u * w' * u⁻¹ * w'⁻¹) * w⁻¹ = u * w' * u⁻¹ * w'⁻¹ := by
      rw [← hcentral u w' w, mul_inv_cancel_right]
    calc u * (w * w') * u⁻¹ * (w * w')⁻¹ =
          (u * w * u⁻¹ * w⁻¹) * (w * (u * w' * u⁻¹ * w'⁻¹) * w⁻¹) := by group
      _ = (u * w * u⁻¹ * w⁻¹) * (u * w' * u⁻¹ * w'⁻¹) := by rw [hz]

theorem commHom_apply (hcentral : ∀ u w v : W, (u * w * u⁻¹ * w⁻¹) * v = v * (u * w * u⁻¹ * w⁻¹))
    (u w : W) : commHom hcentral u w = u * w * u⁻¹ * w⁻¹ := rfl

theorem mem_ker_commHom (hcentral : ∀ u w v : W, (u * w * u⁻¹ * w⁻¹) * v = v * (u * w * u⁻¹ * w⁻¹))
    (u w : W) : w ∈ (commHom hcentral u).ker ↔ u * w = w * u := by
  rw [MonoidHom.mem_ker, commHom_apply, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

theorem false_of_center_eq_ker [Finite W] (π : W →* T) (hπ : Function.Surjective π)
    (hTcomm : ∀ s t : T, s * t = t * s) (hTexp : ∀ t : T, t ^ 3 = 1) (hW : Nat.card W = 81)
    (hT : Nat.card T = 27) (hkerZ : ∀ z ∈ π.ker, ∀ w : W, z * w = w * z)
    (hZker : ∀ z : W, (∀ w : W, z * w = w * z) → z ∈ π.ker) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkerc : Nat.card π.ker = 3 := by
    have h1 := card_eq_card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top, hT, hW] at h1
    omega
  have hW3 : IsPGroup 3 W := IsPGroup.of_card (n := 4) (by rw [hW]; norm_num)
  have hcommker : ∀ u w : W, u * w * u⁻¹ * w⁻¹ ∈ π.ker := by
    intro u w
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hTcomm (π u) (π w)]
    group
  have hcentral : ∀ u w v : W, (u * w * u⁻¹ * w⁻¹) * v = v * (u * w * u⁻¹ * w⁻¹) :=
    fun u w v => hkerZ _ (hcommker u w) v
  set f := commHom hcentral with hf
  have hfker : ∀ u w : W, w ∈ (f u).ker ↔ u * w = w * u := mem_ker_commHom hcentral
  have hfrange : ∀ u : W, (f u).range ≤ π.ker := by
    rintro u _ ⟨w, rfl⟩
    exact hcommker u w
  have hcent : ∀ u : W, u ∉ π.ker → Nat.card (f u).ker = 27 := by
    intro u hu
    have hr3 : Nat.card (f u).range = 3 := by
      have hdvd : Nat.card (f u).range ∣ 3 := hkerc ▸ Subgroup.card_dvd_of_le (hfrange u)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
      · exfalso
        apply hu
        apply hZker
        intro w
        have h2 : f u w = 1 := by
          have : f u w ∈ (f u).range := ⟨w, rfl⟩
          rw [Subgroup.eq_bot_of_card_eq _ h1] at this
          exact this
        exact (hfker u w).mp h2
      · exact h1
    have h1 := card_eq_card_ker_mul_card_range (f u)
    rw [hW, hr3] at h1
    omega
  have hspan : ∀ (K : Subgroup W), π.ker ≤ K → ∀ u₁ u₂ : W, u₁ ∈ K → u₂ ∈ K →
      (Subgroup.closure {π u₁, π u₂}).comap π ≤ K := by
    intro K hK u₁ u₂ h₁ h₂
    apply comap_le_of_le_map π hK
    rw [Subgroup.closure_le]
    intro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact ⟨u₁, h₁, rfl⟩
    · exact ⟨u₂, h₂, rfl⟩
  have hkerC : ∀ u : W, π.ker ≤ (f u).ker := fun u z hz => (hfker u z).mpr (hkerZ z hz u).symm
  obtain ⟨u₁, hu₁⟩ : ∃ u : W, u ∉ π.ker := by
    by_contra hall
    push Not at hall
    have : π.ker = ⊤ := eq_top_iff.mpr fun w _ => hall w
    rw [this, Subgroup.card_top, hW] at hkerc
    norm_num at hkerc
  have hπu₁ : π u₁ ≠ 1 := fun h1 => hu₁ (MonoidHom.mem_ker.mpr h1)
  have hπu₁3 : orderOf (π u₁) = 3 := orderOf_eq_prime (hTexp _) hπu₁
  obtain ⟨u₂, hu₂C, hu₂S⟩ : ∃ u ∈ (f u₁).ker, π u ∉ Subgroup.zpowers (π u₁) := by
    by_contra hall
    push Not at hall
    have hle : (f u₁).ker ≤ (Subgroup.zpowers (π u₁)).comap π := fun w hw => hall w hw
    have h1 := Subgroup.card_le_of_le hle
    rw [hcent u₁ hu₁, card_comap_of_surjective π hπ, hkerc, Nat.card_zpowers, hπu₁3] at h1
    norm_num at h1
  have hu₁u₂ : u₁ * u₂ = u₂ * u₁ := (hfker u₁ u₂).mp hu₂C
  set J := Subgroup.closure ({π u₁, π u₂} : Set T) with hJ
  set S := J.comap π with hS
  have : Finite T := Nat.finite_of_card_ne_zero (by rw [hT]; norm_num)
  have hT3 : IsPGroup 3 T := IsPGroup.of_card (n := 3) (by rw [hT]; norm_num)
  have hJ9 : 9 ≤ Nat.card J := by
    have hle : Subgroup.zpowers (π u₁) ≤ J :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hne : Subgroup.zpowers (π u₁) ≠ J := fun h1 =>
      hu₂S (h1 ▸ Subgroup.subset_closure (by simp))
    have h1 := prime_mul_card_le_of_le_of_ne hT3 hle hne
    rwa [Nat.card_zpowers, hπu₁3] at h1
  have hSC₁ : S ≤ (f u₁).ker := hspan _ (hkerC u₁) u₁ u₂ ((hfker u₁ u₁).mpr rfl) hu₂C
  have hSC₂ : S ≤ (f u₂).ker :=
    hspan _ (hkerC u₂) u₁ u₂ ((hfker u₂ u₁).mpr hu₁u₂.symm) ((hfker u₂ u₂).mpr rfl)
  have hScomm : ∀ w ∈ S, S ≤ (f w).ker := by
    intro w hw
    exact hspan _ (hkerC w) u₁ u₂ ((hfker w u₁).mpr ((hfker u₁ w).mp (hSC₁ hw)).symm)
      ((hfker w u₂).mpr ((hfker u₂ w).mp (hSC₂ hw)).symm)
  have hS27 : Nat.card S = 27 := by
    apply le_antisymm
    · rw [← hcent u₁ hu₁]
      exact Subgroup.card_le_of_le hSC₁
    · rw [hS, card_comap_of_surjective π hπ, hkerc]
      omega
  obtain ⟨u₃, hu₃⟩ : ∃ u : W, u ∉ S := by
    by_contra hall
    push Not at hall
    have : S = ⊤ := eq_top_iff.mpr fun w _ => hall w
    rw [this, Subgroup.card_top, hW] at hS27
    norm_num at hS27
  have hSC₃ : 9 ≤ Nat.card (S ⊓ (f u₃).ker : Subgroup W) := by
    set φ : S →* W := (f u₃).comp S.subtype with hφ
    have hker : Nat.card φ.ker = Nat.card (S ⊓ (f u₃).ker : Subgroup W) := by
      have : φ.ker.map S.subtype = S ⊓ (f u₃).ker := by
        ext w
        constructor
        · rintro ⟨w', hw', rfl⟩
          exact ⟨w'.2, hw'⟩
        · rintro ⟨hwS, hwC⟩
          exact ⟨⟨w, hwS⟩, hwC, rfl⟩
      rw [← this, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have hrange : Nat.card φ.range ≤ 3 := by
      have hle : φ.range ≤ π.ker := by
        rintro _ ⟨w, rfl⟩
        exact hcommker u₃ w
      rw [← hkerc]
      exact Subgroup.card_le_of_le hle
    have h1 := card_eq_card_ker_mul_card_range φ
    rw [hS27, hker] at h1
    nlinarith
  obtain ⟨w, hw, hwker⟩ : ∃ w ∈ (S ⊓ (f u₃).ker : Subgroup W), w ∉ π.ker := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show (S ⊓ (f u₃).ker : Subgroup W) ≤ π.ker from hall)
    rw [hkerc] at h1
    omega
  have hCw : S ≤ (f w).ker := hScomm w hw.1
  have hu₃w : u₃ ∈ (f w).ker := (hfker w u₃).mpr ((hfker u₃ w).mp hw.2).symm
  have hne : S ≠ (f w).ker := fun h1 => hu₃ (h1 ▸ hu₃w)
  have h1 := prime_mul_card_le_of_le_of_ne hW3 hCw hne
  rw [hS27, hcent w hwker] at h1
  norm_num at h1

theorem commutative_and_pow_three [Finite W] (π : W →* T) (hπ : Function.Surjective π)
    (hTcomm : ∀ s t : T, s * t = t * s) (hTexp : ∀ t : T, t ^ 3 = 1) (hW : Nat.card W = 81)
    (hT : Nat.card T = 27) (hkerZ : ∀ z ∈ π.ker, ∀ w : W, z * w = w * z) (σ : W ≃* W)
    (τ : T →* T) (hστ : ∀ w, π (σ w) = τ (π w))
    (hτ : ∀ V : Subgroup T, (∀ t ∈ V, τ t ∈ V) → V = ⊥ ∨ V = ⊤) :
    (∀ u w : W, u * w = w * u) ∧ ∀ w : W, w ^ 3 = 1 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hkerc : Nat.card π.ker = 3 := by
    have h1 := card_eq_card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top, hT, hW] at h1
    omega
  have hσZ : ∀ z : W, (∀ w, z * w = w * z) → ∀ w, σ z * w = w * σ z := by
    intro z hz w
    obtain ⟨w', rfl⟩ := σ.surjective w
    rw [← map_mul, ← map_mul, hz]
  have hcomm : ∀ u w : W, u * w = w * u := by
    set V := (Subgroup.center W).map π with hV
    have hVinv : ∀ t ∈ V, τ t ∈ V := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : z ∈ Subgroup.center W := hz
      refine ⟨σ z, (Subgroup.mem_center_iff.mpr fun w => ?_ : σ z ∈ Subgroup.center W), hστ z⟩
      exact (hσZ z (fun w => (Subgroup.mem_center_iff.mp hz' w).symm) w).symm
    rcases hτ V hVinv with hbot | htop
    · exfalso
      refine false_of_center_eq_ker π hπ hTcomm hTexp hW hT hkerZ fun z hz => ?_
      have h1 : π z ∈ V := ⟨z, Subgroup.mem_center_iff.mpr fun w => (hz w).symm, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact MonoidHom.mem_ker.mpr h1
    · have hall : ∀ w : W, w ∈ Subgroup.center W := by
        intro w
        have h1 : π w ∈ V := htop ▸ Subgroup.mem_top _
        obtain ⟨z, hz, hzw⟩ := h1
        have h2 : z⁻¹ * w ∈ π.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hzw, inv_mul_cancel]
        have h3 : z⁻¹ * w ∈ Subgroup.center W :=
          Subgroup.mem_center_iff.mpr fun v => (hkerZ _ h2 v).symm
        have h4 := (Subgroup.center W).mul_mem hz h3
        rwa [mul_inv_cancel_left] at h4
      intro u w
      exact (Subgroup.mem_center_iff.mp (hall u) w).symm
  refine ⟨hcomm, ?_⟩
  let p : W →* W :=
    { toFun := fun w => w ^ 3
      map_one' := one_pow 3
      map_mul' := fun u w => (Commute.mul_pow (hcomm u w) 3) }
  have hp : ∀ w, p w = w ^ 3 := fun _ => rfl
  have hpker : π.ker ≤ p.ker := by
    intro z hz
    rw [MonoidHom.mem_ker, hp]
    have h1 : orderOf (⟨z, hz⟩ : π.ker) ∣ 3 := hkerc ▸ orderOf_dvd_natCard _
    have h2 := pow_eq_one_iff_modEq.mpr ((Nat.modEq_zero_iff_dvd).mpr h1)
    exact congrArg Subtype.val h2
  set V := p.ker.map π with hV
  have hVinv : ∀ t ∈ V, τ t ∈ V := by
    rintro _ ⟨k, hk, rfl⟩
    have hk' : k ∈ p.ker := hk
    refine ⟨σ k, (?_ : σ k ∈ p.ker), hστ k⟩
    rw [MonoidHom.mem_ker, hp, ← map_pow, ← hp, MonoidHom.mem_ker.mp hk', map_one]
  rcases hτ V hVinv with hbot | htop
  · exfalso
    have hle : p.ker ≤ π.ker := fun k hk => by
      have h1 : π k ∈ V := ⟨k, hk, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact MonoidHom.mem_ker.mpr h1
    have hrange : p.range ≤ π.ker := by
      rintro _ ⟨w, rfl⟩
      rw [MonoidHom.mem_ker, hp, map_pow, hTexp]
    have h1 := card_eq_card_ker_mul_card_range p
    have h2 := Subgroup.card_le_of_le hle
    have h3 := Subgroup.card_le_of_le hrange
    rw [hW] at h1
    rw [hkerc] at h2 h3
    nlinarith
  · intro w
    have h1 : π w ∈ V := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkw⟩ := h1
    have h2 : k⁻¹ * w ∈ p.ker := by
      apply hpker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkw, inv_mul_cancel]
    have h3 := p.ker.mul_mem hk h2
    rw [mul_inv_cancel_left] at h3
    exact h3

theorem nine_le_card_fixed [Finite W] (hcomm : ∀ u w : W, u * w = w * u)
    (hexp : ∀ w : W, w ^ 3 = 1) (hW : Nat.card W = 81) (α : W →* W)
    (hα : ∀ w, α (α (α w)) = w) :
    ∃ F : Subgroup W, 9 ≤ Nat.card F ∧ ∀ w ∈ F, α w = w := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : CommGroup W := { (inferInstance : Group W) with mul_comm := hcomm }
  let f : W →* W :=
    { toFun := commMap α
      map_one' := by simp [commMap]
      map_mul' := fun x y => by
        simp only [commMap, map_mul, mul_inv_rev]
        rw [mul_comm y⁻¹ x⁻¹, mul_mul_mul_comm] }
  have hf : ∀ x, f x = α x * x⁻¹ := fun _ => rfl
  have hf3 : ∀ x, f (f (f x)) = 1 := by
    intro x
    change commMap α (commMap α (commMap α x)) = 1
    rw [cube_identity_mul, hα, inv_pow, hexp, inv_one, mul_one, hexp, mul_one, mul_inv_cancel]
  refine ⟨f.ker, ?_, fun w hw => mul_inv_eq_one.mp hw⟩
  by_contra hlt
  push Not at hlt
  have hk3 : Nat.card f.ker ≤ 3 := by
    have hW3 : IsPGroup 3 W := IsPGroup.of_card (n := 4) (by rw [hW]; norm_num)
    obtain ⟨j, hj⟩ := (hW3.to_subgroup f.ker).exists_card_eq
    rw [hj] at hlt ⊢
    have : j ≤ 1 := by
      by_contra hj1
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases j <;> norm_num
  have hR₃ : (((⊤ : Subgroup W).map f).map f).map f = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro _ ⟨_, ⟨_, ⟨x, -, rfl⟩, rfl⟩, rfl⟩
    exact hf3 x
  have h1 := card_le_card_map_mul f ⊤
  have h2 := card_le_card_map_mul f ((⊤ : Subgroup W).map f)
  have h3 := card_le_card_map_mul f (((⊤ : Subgroup W).map f).map f)
  rw [Subgroup.card_top, hW] at h1
  rw [hR₃, Subgroup.card_bot, one_mul] at h3
  have hk0 : 0 < Nat.card f.ker := Nat.card_pos
  set k := Nat.card f.ker with hk
  set r₁ := Nat.card ((⊤ : Subgroup W).map f) with hr₁
  set r₂ := Nat.card (((⊤ : Subgroup W).map f).map f) with hr₂
  have h4 : 81 ≤ k * k * k := by
    calc 81 ≤ r₁ * k := h1
      _ ≤ (r₂ * k) * k := Nat.mul_le_mul_right k h2
      _ ≤ (k * k) * k := Nat.mul_le_mul_right k (Nat.mul_le_mul_right k h3)
  have h5 : k * k * k ≤ 27 := by
    have := Nat.mul_le_mul (Nat.mul_le_mul hk3 hk3) hk3
    simpa using this
  omega

theorem exists_fixed_not_mem_ker [Finite W] (π : W →* T) (hπ : Function.Surjective π)
    (hTcomm : ∀ s t : T, s * t = t * s) (hTexp : ∀ t : T, t ^ 3 = 1) (hW : Nat.card W = 81)
    (hT : Nat.card T = 27) (hkerZ : ∀ z ∈ π.ker, ∀ w : W, z * w = w * z) (σ : W ≃* W)
    (τ : T →* T) (hστ : ∀ w, π (σ w) = τ (π w))
    (hτ : ∀ V : Subgroup T, (∀ t ∈ V, τ t ∈ V) → V = ⊥ ∨ V = ⊤) (α : W →* W)
    (hα : ∀ w, α (α (α w)) = w) : ∃ w : W, α w = w ∧ π w ≠ 1 := by
  have hkerc : Nat.card π.ker = 3 := by
    have h1 := card_eq_card_ker_mul_card_range π
    rw [MonoidHom.range_eq_top_of_surjective π hπ, Subgroup.card_top, hT, hW] at h1
    omega
  obtain ⟨hcomm, hexp⟩ :=
    commutative_and_pow_three π hπ hTcomm hTexp hW hT hkerZ σ τ hστ hτ
  obtain ⟨F, hF9, hFfix⟩ := nine_le_card_fixed hcomm hexp hW α hα
  by_contra hall
  push Not at hall
  have hle : F ≤ π.ker := fun w hw => MonoidHom.mem_ker.mpr (hall w (hFfix w hw))
  have h1 := Subgroup.card_le_of_le hle
  rw [hkerc] at h1
  omega

theorem exists_fixed_of_quotient {G : Type*} [Group G] [Finite G] {Q E : Subgroup G}
    (hEQ : E ≤ Q) (hQE : Q ≤ Subgroup.normalizer (E : Set G))
    (hEcomm : ∀ e e' : E, e * e' = e' * e) (hEexp : ∀ e : E, e ^ 3 = 1)
    (hE27 : Nat.card E = 27) (hQ : Nat.card Q = 81 * 27)
    (ψ : Q →* E) (hψsurj : Function.Surjective ψ) (hψE : ∀ q : Q, (q : G) ∈ E → ψ q = 1)
    (hcentral : ∀ q z : Q, ψ z = 1 → (q : G) * z * (q : G)⁻¹ * (z : G)⁻¹ ∈ E)
    {y : G} (hyQ : y ∈ Subgroup.normalizer (Q : Set G))
    (hyE : y ∈ Subgroup.normalizer (E : Set G))
    (τ : E →* E) (hψy : ∀ q q' : Q, (q' : G) = y * q * y⁻¹ → ψ q' = τ (ψ q))
    (hτ : ∀ V : Subgroup E, (∀ t ∈ V, τ t ∈ V) → V = ⊥ ∨ V = ⊤)
    {a : G} (haQ : a ∈ Subgroup.normalizer (Q : Set G))
    (haE : a ∈ Subgroup.normalizer (E : Set G)) (ha3 : a ^ 3 = 1) :
    ∃ u : Q, ψ u ≠ 1 ∧ (u : G)⁻¹ * (a * u * a⁻¹) ∈ E := by
  classical
  set E' := E.subgroupOf Q with hE'
  have : E'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEQ).mpr hQE
  have hE'ker : E' ≤ ψ.ker := fun q hq => hψE q (Subgroup.mem_subgroupOf.mp hq)
  set π : Q ⧸ E' →* E := QuotientGroup.lift E' ψ hE'ker with hπ
  have hπmk : ∀ q : Q, π (q : Q ⧸ E') = ψ q := fun q => rfl
  have hπsurj : Function.Surjective π := by
    intro t
    obtain ⟨q, rfl⟩ := hψsurj t
    exact ⟨q, rfl⟩
  have hE'card : Nat.card E' = 27 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEQ).toEquiv, hE27]
  have hW : Nat.card (Q ⧸ E') = 81 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup E'
    rw [hQ, hE'card] at h1
    omega
  have hkerZ : ∀ z ∈ π.ker, ∀ w : Q ⧸ E', z * w = w * z := by
    intro z hz w
    induction z using QuotientGroup.induction_on with | H z => ?_
    induction w using QuotientGroup.induction_on with | H q => ?_
    have hz1 : ψ z = 1 := hz
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hE',
      Subgroup.mem_subgroupOf]
    have h1 := hcentral q⁻¹ z⁻¹ (by rw [map_inv, hz1, inv_one])
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at h1 ⊢
    convert h1 using 1
    group
  set cy : Q ≃* Q := Q.normalizerMonoidHom ⟨y, hyQ⟩ with hcy
  have hcyapp : ∀ q : Q, ((cy q : Q) : G) = y * q * y⁻¹ := fun q => rfl
  have hcyE : E'.map (cy : Q →* Q) = E' := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨q, hq, rfl⟩
      have hq' : (q : G) ∈ E := by rw [hE'] at hq; exact Subgroup.mem_subgroupOf.mp hq
      rw [hE', Subgroup.mem_subgroupOf]
      change ((cy q : Q) : G) ∈ E
      rw [hcyapp]
      exact (Subgroup.mem_normalizer_iff.mp hyE q).mp hq'
    · rw [Subgroup.card_map_of_injective (f := (cy : Q →* Q)) cy.injective]
  set σ : (Q ⧸ E') ≃* (Q ⧸ E') := QuotientGroup.congr E' E' cy hcyE with hσ
  have hστ : ∀ w, π (σ w) = τ (π w) := by
    intro w
    induction w using QuotientGroup.induction_on with | H q => ?_
    rw [hσ, QuotientGroup.congr_mk, hπmk, hπmk]
    exact hψy q (cy q) (hcyapp q)
  set ca : Q ≃* Q := Q.normalizerMonoidHom ⟨a, haQ⟩ with hca
  have hcaapp : ∀ q : Q, ((ca q : Q) : G) = a * q * a⁻¹ := fun q => rfl
  have hcaE : E' ≤ E'.comap ca.toMonoidHom := by
    intro q hq
    have hq' : (q : G) ∈ E := by rw [hE'] at hq; exact Subgroup.mem_subgroupOf.mp hq
    rw [Subgroup.mem_comap, hE', Subgroup.mem_subgroupOf]
    change ((ca q : Q) : G) ∈ E
    rw [hcaapp]
    exact (Subgroup.mem_normalizer_iff.mp haE q).mp hq'
  set α : Q ⧸ E' →* Q ⧸ E' := QuotientGroup.map E' E' ca.toMonoidHom hcaE with hα
  have hαmk : ∀ q : Q, α (q : Q ⧸ E') = ((ca q : Q) : Q ⧸ E') := fun q => rfl
  have hα3 : ∀ w, α (α (α w)) = w := by
    intro w
    induction w using QuotientGroup.induction_on with | H q => ?_
    rw [hαmk, hαmk, hαmk]
    congr 1
    apply Subtype.ext
    rw [hcaapp, hcaapp, hcaapp]
    have h1 : a * (a * a) = 1 := by rw [← pow_three]; exact ha3
    calc a * (a * (a * (q : G) * a⁻¹) * a⁻¹) * a⁻¹ = (a * (a * a)) * q * (a * (a * a))⁻¹ := by
          group
      _ = q := by rw [h1, one_mul, inv_one, mul_one]
  obtain ⟨w, hwα, hwπ⟩ :=
    exists_fixed_not_mem_ker π hπsurj hEcomm hEexp hW hE27 hkerZ σ τ hστ hτ α hα3
  induction w using QuotientGroup.induction_on with | H u => ?_
  refine ⟨u, by rwa [hπmk] at hwπ, ?_⟩
  rw [hαmk, QuotientGroup.eq, hE', Subgroup.mem_subgroupOf] at hwα
  have h1 : ((a * u * a⁻¹)⁻¹ * u : G) ∈ E := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hcaapp] using hwα
  have h2 := E.inv_mem h1
  rwa [mul_inv_rev, inv_inv] at h2

end Generic

end CFSG.RankThree.PartTwo.Sec10.Item107Proof
