module

public import CFSG.Quasithin.Background.B3ThreeBasic
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.B3

variable {Γ : Type*} [Group Γ] {V : Type*} [CommGroup V]

@[expose] def IsIndec (ρ : Γ →* MulAut V) : Prop :=
  ∀ X Y : Subgroup V, IsInv ρ X → IsInv ρ Y → X ⊓ Y = ⊥ → X ⊔ Y = ⊤ → X = ⊥ ∨ Y = ⊥

structure ThreeStep (ρ : Γ →* MulAut V) (A B : Subgroup V) : Prop where
  le : A ≤ B
  invA : IsInv ρ A
  invB : IsInv ρ B
  trivA : ∀ g, ∀ a ∈ A, ρ g a = a
  trivQ : ∀ g v, ρ g v * v⁻¹ ∈ B
  irr : ∀ S : Subgroup V, IsInv ρ S → A ≤ S → S ≤ B → S = A ∨ S = B
  nontriv : ∃ g, ∃ b ∈ B, ρ g b * b⁻¹ ∉ A

theorem IsInv.sup {ρ : Γ →* MulAut V} {X Y : Subgroup V} (hX : IsInv ρ X) (hY : IsInv ρ Y) :
    IsInv ρ (X ⊔ Y) := by
  intro g z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hz
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hX g x hx) (hY g y hy)

theorem zpow_sq_one {c : V} (h : c ^ 2 = 1) (k : ℤ) : c ^ k = 1 ∨ c ^ k = c := by
  have h2 : c ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two]; exact h
  obtain ⟨j, hj | hj⟩ := Int.even_or_odd' k
  · left
    rw [hj, zpow_mul, h2, one_zpow]
  · right
    rw [hj, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem fixG_le_commG (hV : ∀ v : V, v ^ 2 = 1) {ρ : Γ →* MulAut V} (hindec : IsIndec ρ)
    (hM : commG ρ ≠ ⊥) : fixG ρ ≤ commG ρ := by
  intro c hc
  by_contra hcM
  obtain ⟨N, hMN, hcN, hNsup⟩ := exists_hyperplane hV (commG ρ) hcM
  have hNinv : IsInv ρ N := by
    intro g n hn
    have := N.mul_mem (hMN (mul_inv_mem_commG g n)) hn
    simpa [mul_assoc] using this
  have hCinv : IsInv ρ (Subgroup.zpowers c) := by
    intro g z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [map_zpow, hc g]
    exact Subgroup.zpow_mem_zpowers c k
  have hdisj : N ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzN, hzC⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hzC
    rcases zpow_sq_one (hV c) k with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h] at hzN
      exact absurd hzN hcN
  rcases hindec N _ hNinv hCinv hdisj hNsup with h | h
  · apply hM
    rw [eq_bot_iff]
    exact h ▸ hMN
  · apply hcM
    have : c = 1 := by
      have hc1 : c ∈ Subgroup.zpowers c := Subgroup.mem_zpowers c
      rw [h] at hc1
      exact Subgroup.mem_bot.1 hc1
    rw [this]
    exact Subgroup.one_mem _

theorem fixG_inf_le_of_threeStep {ρ : Γ →* MulAut V} {A B : Subgroup V} (hS : ThreeStep ρ A B) :
    fixG ρ ⊓ B ≤ A := by
  let S₂ : Subgroup V :=
    { carrier := {b | b ∈ B ∧ ∀ g, ρ g b * b⁻¹ ∈ A}
      one_mem' := ⟨B.one_mem, fun g => by simp⟩
      mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, fun g => by
        have := A.mul_mem (ha.2 g) (hb.2 g)
        simpa [map_mul, mul_inv, mul_comm, mul_left_comm, mul_assoc] using this⟩
      inv_mem' := fun {a} ha => ⟨B.inv_mem ha.1, fun g => by
        have := A.inv_mem (ha.2 g)
        simpa [map_inv, mul_inv, mul_comm, mul_left_comm, mul_assoc] using this⟩ }
  have hS₂inv : IsInv ρ S₂ := by
    intro h b hb
    refine ⟨hS.invB h b hb.1, fun g => ?_⟩
    have h1 := A.mul_mem (hb.2 (g * h)) (A.inv_mem (hb.2 h))
    have e : ρ g (ρ h b) * (ρ h b)⁻¹ = ρ (g * h) b * b⁻¹ * (ρ h b * b⁻¹)⁻¹ := by
      simp [map_mul, mul_comm, mul_left_comm, mul_assoc]
    rw [e]
    exact h1
  have hAS₂ : A ≤ S₂ := fun a ha =>
    ⟨hS.le ha, fun g => by rw [hS.trivA g a ha, mul_inv_cancel]; exact A.one_mem⟩
  have hS₂B : S₂ ≤ B := fun b hb => hb.1
  rcases hS.irr S₂ hS₂inv hAS₂ hS₂B with h | h
  · intro c hc
    have hcS : c ∈ S₂ := ⟨hc.2, fun g => by rw [hc.1 g, mul_inv_cancel]; exact A.one_mem⟩
    rw [h] at hcS
    exact hcS
  · exfalso
    obtain ⟨g, b, hb, hnot⟩ := hS.nontriv
    have : b ∈ S₂ := by rw [h]; exact hb
    exact hnot (this.2 g)

theorem commG_eq_of_threeStep (hV : ∀ v : V, v ^ 2 = 1) {ρ : Γ →* MulAut V} {A B : Subgroup V}
    (hS : ThreeStep ρ A B) (hindec : IsIndec ρ) : commG ρ = B ∧ fixG ρ = A := by
  have hMB : commG ρ ≤ B := commOn_le (fun g m _ => hS.trivQ g m)
  have hnotle : ¬ commG ρ ≤ A := by
    intro hle
    obtain ⟨g, b, hb, hnot⟩ := hS.nontriv
    exact hnot (hle (mul_inv_mem_commG g b))
  have hsup : commG ρ ⊔ A = B := by
    rcases hS.irr (commG ρ ⊔ A) ((isInv_commG ρ).sup hS.invA) le_sup_right
      (sup_le hMB hS.le) with h | h
    · exact absurd (h ▸ le_sup_left) hnotle
    · exact h
  have hMne : commG ρ ≠ ⊥ := fun h => hnotle (h ▸ bot_le)
  have hCM : fixG ρ ≤ commG ρ := fixG_le_commG hV hindec hMne
  have hAC : A ≤ fixG ρ := fun a ha g => hS.trivA g a ha
  have hMeq : commG ρ = B := by
    rw [← hsup]
    exact (sup_eq_left.2 (hAC.trans hCM)).symm
  refine ⟨hMeq, le_antisymm ?_ hAC⟩
  intro c hc
  exact fixG_inf_le_of_threeStep hS ⟨hc, hMeq ▸ hCM hc⟩

theorem commG_le_commOn (hperf : commutator Γ = ⊤) (hV : ∀ v : V, v ^ 2 = 1)
    (ρ : Γ →* MulAut V) : commG ρ ≤ commOn ρ (commG ρ) := by
  classical
  set M := commG ρ with hMdef
  set M' := commOn ρ M with hM'def
  by_contra hle
  obtain ⟨m, hmM, hmM'⟩ := IsConcreteLE.not_le_iff_exists.1 hle
  obtain ⟨N', hM'N', hmN', hsup'⟩ := exists_hyperplane hV M' hmM'
  set N₁ : Subgroup V := N' ⊓ M with hN₁
  have hMinv : IsInv ρ M := isInv_commG ρ
  have hcommN₁ : ∀ g, ∀ b ∈ M, ρ g b * b⁻¹ ∈ N₁ := fun g b hb =>
    ⟨hM'N' (mul_inv_mem_commOn g hb), mul_inv_mem_commG g b⟩
  have hdecomp : ∀ b ∈ M, b ∈ N₁ ∨ b * m ∈ N₁ := by
    intro b hb
    have hb' : b ∈ N' ⊔ Subgroup.zpowers m := by rw [hsup']; exact Subgroup.mem_top b
    obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup.1 hb'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    rcases zpow_sq_one (hV m) k with h | h
    · left
      rw [h, mul_one] at hb ⊢
      exact ⟨hn, hb⟩
    · right
      rw [h] at hb ⊢
      have e : n * m * m = n := by rw [mul_assoc, ← pow_two, hV m, mul_one]
      rw [e]
      refine ⟨hn, ?_⟩
      have := M.mul_mem hb (M.inv_mem hmM)
      have e2 : n * m * m⁻¹ = n := by simp
      rwa [e2] at this
  have hmulmem : ∀ b ∈ M, ∀ b' ∈ M, (b * b' ∈ N₁ ↔ (b ∈ N₁ ↔ b' ∈ N₁)) := by
    intro b hb b' hb'
    constructor
    · intro h
      constructor
      · intro hbN
        have := N₁.mul_mem (N₁.inv_mem hbN) h
        simpa using this
      · intro hb'N
        have := N₁.mul_mem h (N₁.inv_mem hb'N)
        simpa using this
    · intro h
      by_cases hbN : b ∈ N₁
      · exact N₁.mul_mem hbN (h.1 hbN)
      · have hb'N : b' ∉ N₁ := fun hh => hbN (h.2 hh)
        have h1 : b * m ∈ N₁ := (hdecomp b hb).resolve_left hbN
        have h2 : b' * m ∈ N₁ := (hdecomp b' hb').resolve_left hb'N
        have h3 := N₁.mul_mem h1 h2
        have e : b * m * (b' * m) = b * b' := by
          rw [show b * m * (b' * m) = b * b' * (m * m) by
            simp [mul_comm, mul_left_comm], ← pow_two, hV m, mul_one]
        rwa [e] at h3
  have hinvN₁ : ∀ g, ∀ b ∈ M, (ρ g b ∈ N₁ ↔ b ∈ N₁) := by
    intro g b hb
    have h1 := hcommN₁ g b hb
    constructor
    · intro h
      have := N₁.mul_mem (N₁.inv_mem h1) h
      simpa using this
    · intro h
      have := N₁.mul_mem h1 h
      simpa using this
  have key : ∀ s : V, ∀ x : Γ, ρ x s * s⁻¹ ∈ N₁ := by
    intro s
    let u : Γ → V := pder ρ s
    have hu : IsDer ρ u := isDer_pder ρ s
    have huM : ∀ x, u x ∈ M := fun x => mul_inv_mem_commG x s
    let f : Γ →* Multiplicative (ZMod 2) :=
      { toFun := fun x => Multiplicative.ofAdd (if u x ∈ N₁ then (0 : ZMod 2) else 1)
        map_one' := by
          have : u 1 = 1 := hu.map_one
          simp [this]
        map_mul' := fun x y => by
          have hxy : u (x * y) ∈ N₁ ↔ (u x ∈ N₁ ↔ u y ∈ N₁) := by
            rw [hu x y]
            have hρ : ρ x (u y) ∈ M := hMinv x _ (huM y)
            rw [hmulmem _ (huM x) _ hρ, hinvN₁ x _ (huM y)]
          by_cases h1 : u x ∈ N₁ <;> by_cases h2 : u y ∈ N₁ <;> simp [hxy, h1, h2]
          all_goals decide }
    intro x
    have h := eq_one_of_perfect hperf f x
    by_contra hnot
    have : (if u x ∈ N₁ then (0 : ZMod 2) else 1) = 0 := by
      have h' : Multiplicative.ofAdd (if u x ∈ N₁ then (0 : ZMod 2) else 1) = 1 := h
      exact ofAdd_eq_one.1 h'
    simp only [u, pder] at this hnot
    simp [hnot] at this
  have hMN₁ : M ≤ N₁ := by
    refine commOn_le (fun g m _ => key m g)
  exact hmN' (hMN₁ hmM).1

theorem commOn_commG (hperf : commutator Γ = ⊤) (hV : ∀ v : V, v ^ 2 = 1)
    (ρ : Γ →* MulAut V) : commOn ρ (commG ρ) = commG ρ :=
  le_antisymm (commOn_le (fun g m hm => by
    have : ρ g m * m⁻¹ ∈ commG ρ := mul_inv_mem_commG g m
    exact this)) (commG_le_commOn hperf hV ρ)

@[expose] def resAct (ρ : Γ →* MulAut V) (M : Subgroup V) (hM : IsInv ρ M) : Γ →* MulAut ↥M where
  toFun g := restrictEquiv ρ M hM g
  map_one' := by
    refine MulEquiv.ext fun m => ?_
    apply Subtype.ext
    show ρ 1 (m : V) = m
    rw [_root_.map_one]
    rfl
  map_mul' g h := by
    refine MulEquiv.ext fun m => ?_
    apply Subtype.ext
    show ρ (g * h) (m : V) = ρ g (ρ h (m : V))
    rw [map_mul]
    rfl

theorem coe_resAct {ρ : Γ →* MulAut V} {M : Subgroup V} (hM : IsInv ρ M) (g : Γ) (m : ↥M) :
    ((resAct ρ M hM g m : ↥M) : V) = ρ g (m : V) := rfl

@[expose] def dsM (ρ : Γ →* MulAut V) {M : Subgroup V} (hM : ∀ g v, ρ g v * v⁻¹ ∈ M) (s : V) :
    Γ → ↥M := fun x => ⟨ρ x s * s⁻¹, hM x s⟩

theorem isDer_dsM (ρ : Γ →* MulAut V) {M : Subgroup V} (hM : ∀ g v, ρ g v * v⁻¹ ∈ M) (s : V) :
    IsDer (resAct ρ M (isInv_of_trivQ hM)) (dsM ρ hM s) := by
  intro x y
  apply Subtype.ext
  have := isDer_pder ρ s x y
  simpa [dsM, pder, coe_resAct] using this

theorem exists_corr {X : Type*} [CommGroup X] {ρX : Γ →* MulAut X}
    {ρ : Γ →* MulAut V} {M : Subgroup V} (hM : ∀ g v, ρ g v * v⁻¹ ∈ M) (φ : ↥M ≃* X)
    (hφ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) ρX φ) (s : V) (e : Γ → X)
    (hp : IsPrin ρX (fun x => φ (dsM ρ hM s x) * e x)) :
    ∃ m : ↥M, ∀ x, ρ x (s * (m : V)⁻¹) * (s * (m : V)⁻¹)⁻¹ = ((φ.symm (e x) : ↥M) : V)⁻¹ := by
  obtain ⟨x₀, hx₀⟩ := hp
  refine ⟨φ.symm x₀, fun x => ?_⟩
  have h1 := congrFun hx₀ x
  simp only [pder] at h1
  have h2 : dsM ρ hM s x = (resAct ρ M (isInv_of_trivQ hM) x (φ.symm x₀)) * (φ.symm x₀)⁻¹ *
      (φ.symm (e x))⁻¹ := by
    apply φ.injective
    simp only [map_mul, map_inv, hφ x, MulEquiv.apply_symm_apply]
    exact eq_mul_inv_of_mul_eq h1
  have h3 := congrArg Subtype.val h2
  simp only [dsM, coe_resAct, Subgroup.coe_mul, Subgroup.coe_inv] at h3
  have e1 : ρ x (s * ((φ.symm x₀ : ↥M) : V)⁻¹) * (s * ((φ.symm x₀ : ↥M) : V)⁻¹)⁻¹ =
      (ρ x s * s⁻¹) * (ρ x ((φ.symm x₀ : ↥M) : V) * ((φ.symm x₀ : ↥M) : V)⁻¹)⁻¹ := by
    simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [e1, h3]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem mem_or_mul_mem (hV : ∀ v : V, v ^ 2 = 1) {M : Subgroup V} {s : V}
    (hVs : M ⊔ Subgroup.zpowers s = ⊤) (v : V) : v ∈ M ∨ v * s ∈ M := by
  have hv : v ∈ M ⊔ Subgroup.zpowers s := by rw [hVs]; exact Subgroup.mem_top v
  obtain ⟨m, hm, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  rcases zpow_sq_one (hV s) k with h | h
  · left
    rw [h, mul_one]
    exact hm
  · right
    rw [h, mul_assoc, ← pow_two, hV s, mul_one]
    exact hm

theorem exists_modIso_ext {V' : Type*} [CommGroup V'] (hV : ∀ v : V, v ^ 2 = 1)
    (hV' : ∀ v : V', v ^ 2 = 1) {ρ : Γ →* MulAut V} {ρ' : Γ →* MulAut V'}
    {M : Subgroup V} {M' : Subgroup V'} (hM : ∀ g v, ρ g v * v⁻¹ ∈ M)
    (hM' : ∀ g v, ρ' g v * v⁻¹ ∈ M') (φ : ↥M ≃* ↥M')
    (hφ : IsModIso (resAct ρ M (isInv_of_trivQ hM)) (resAct ρ' M' (isInv_of_trivQ hM')) φ)
    {s : V} {s' : V'} (hs : s ∉ M) (hs' : s' ∉ M')
    (hVs : M ⊔ Subgroup.zpowers s = ⊤) (hVs' : M' ⊔ Subgroup.zpowers s' = ⊤)
    (hcoc : ∀ x, ((φ (dsM ρ hM s x) : ↥M') : V') = ρ' x s' * s'⁻¹) :
    ∃ Φ : V ≃* V', IsModIso ρ ρ' Φ := by
  classical
  have hss : s * s = 1 := by rw [← pow_two]; exact hV s
  have hss' : s' * s' = 1 := by rw [← pow_two]; exact hV' s'
  have hsM : ∀ v, v ∉ M → v * s ∈ M := fun v hv => (mem_or_mul_mem hV hVs v).resolve_left hv
  have hsM' : ∀ v, v ∉ M' → v * s' ∈ M' := fun v hv => (mem_or_mul_mem hV' hVs' v).resolve_left hv
  have hnn : ∀ v w, v ∉ M → w ∉ M → v * w ∈ M := by
    intro v w hv hw
    have := M.mul_mem (hsM v hv) (hsM w hw)
    have e : v * s * (w * s) = v * w := by
      rw [show v * s * (w * s) = v * w * (s * s) by simp [mul_comm, mul_left_comm], hss, mul_one]
    rwa [e] at this
  have hmn : ∀ v w, v ∈ M → w ∉ M → v * w ∉ M := by
    intro v w hv hw h
    apply hw
    have := M.mul_mem (M.inv_mem hv) h
    simpa using this
  have hinvM : ∀ g v, v ∈ M → ρ g v ∈ M := fun g v hv => isInv_of_trivQ hM g v hv
  have hnotinvM : ∀ g v, v ∉ M → ρ g v ∉ M := by
    intro g v hv h
    apply hv
    have := M.mul_mem (M.inv_mem (hM g v)) h
    simpa using this
  let φ0 : V → V' := fun v => if h : v ∈ M then ((φ ⟨v, h⟩ : ↥M') : V') else 1
  have hφ0 : ∀ v (h : v ∈ M), φ0 v = ((φ ⟨v, h⟩ : ↥M') : V') := fun v h => by simp [φ0, h]
  have hφ0mul : ∀ a b : V, a ∈ M → b ∈ M → φ0 (a * b) = φ0 a * φ0 b := by
    intro a b ha hb
    rw [hφ0 (a * b) (M.mul_mem ha hb), hφ0 a ha, hφ0 b hb]
    have : (⟨a * b, M.mul_mem ha hb⟩ : ↥M) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]
    rfl
  have hφ0inv : ∀ a : V, a ∈ M → φ0 a⁻¹ = (φ0 a)⁻¹ := by
    intro a ha
    rw [hφ0 a⁻¹ (M.inv_mem ha), hφ0 a ha]
    have : (⟨a⁻¹, M.inv_mem ha⟩ : ↥M) = (⟨a, ha⟩ : ↥M)⁻¹ := rfl
    rw [this, map_inv]
    rfl
  have hφ0mem : ∀ a : V, (h : a ∈ M) → φ0 a ∈ M' := fun a h => by rw [hφ0 a h]; exact (φ ⟨a, h⟩).2
  let F : V → V' := fun v => if v ∈ M then φ0 v else φ0 (v * s) * s'
  have hFM : ∀ v, v ∈ M → F v = φ0 v := fun v h => by simp [F, h]
  have hFN : ∀ v, v ∉ M → F v = φ0 (v * s) * s' := fun v h => by simp [F, h]
  have hF_mul : ∀ v w, F (v * w) = F v * F w := by
    intro v w
    by_cases hv : v ∈ M <;> by_cases hw : w ∈ M
    · rw [hFM _ (M.mul_mem hv hw), hFM v hv, hFM w hw, hφ0mul v w hv hw]
    · have hvw : v * w ∉ M := hmn v w hv hw
      rw [hFN _ hvw, hFM v hv, hFN w hw, ← mul_assoc, mul_assoc v w s, hφ0mul v (w * s) hv (hsM w hw)]
    · have hvw : v * w ∉ M := by
        rw [mul_comm]
        exact hmn w v hw hv
      rw [hFN _ hvw, hFN v hv, hFM w hw]
      have : v * w * s = w * (v * s) := by simp [mul_comm, mul_left_comm]
      rw [this, hφ0mul w (v * s) hw (hsM v hv)]
      simp [mul_comm, mul_left_comm]
    · have hvw : v * w ∈ M := hnn v w hv hw
      rw [hFM _ hvw, hFN v hv, hFN w hw]
      have h1 : φ0 (v * w) = φ0 (v * s) * φ0 (w * s) := by
        rw [← hφ0mul _ _ (hsM v hv) (hsM w hw)]
        congr 1
        rw [show v * s * (w * s) = v * w * (s * s) by simp [mul_comm, mul_left_comm], hss, mul_one]
      rw [h1]
      have h2 : φ0 (v * s) * s' * (φ0 (w * s) * s') = φ0 (v * s) * φ0 (w * s) * (s' * s') := by
        ac_rfl
      rw [h2, hss', mul_one]
  have hF_one : F 1 = 1 := by
    rw [hFM 1 M.one_mem, hφ0 1 M.one_mem]
    have : (⟨1, M.one_mem⟩ : ↥M) = 1 := rfl
    rw [this, _root_.map_one]
    rfl
  let Fm : V →* V' := { toFun := F, map_one' := hF_one, map_mul' := hF_mul }
  have hFinj : Function.Injective Fm := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have hv' : F v = 1 := hv
    by_cases hvM : v ∈ M
    · rw [hFM v hvM, hφ0 v hvM] at hv'
      have : φ ⟨v, hvM⟩ = 1 := Subtype.ext hv'
      have h2 : (⟨v, hvM⟩ : ↥M) = 1 := by simpa using (map_eq_one_iff φ φ.injective).1 this
      exact congrArg Subtype.val h2
    · exfalso
      rw [hFN v hvM] at hv'
      apply hs'
      have : s' = (φ0 (v * s))⁻¹ := eq_inv_of_mul_eq_one_right hv'
      rw [this]
      exact M'.inv_mem (hφ0mem _ (hsM v hvM))
  have hFsurj : Function.Surjective Fm := by
    intro v'
    by_cases hv' : v' ∈ M'
    · refine ⟨((φ.symm ⟨v', hv'⟩ : ↥M) : V), ?_⟩
      show F _ = v'
      rw [hFM _ (φ.symm ⟨v', hv'⟩).2, hφ0 _ (φ.symm ⟨v', hv'⟩).2]
      simp
    · have h1 : v' * s' ∈ M' := hsM' v' hv'
      refine ⟨((φ.symm ⟨v' * s', h1⟩ : ↥M) : V) * s, ?_⟩
      show F _ = v'
      have hn : ((φ.symm ⟨v' * s', h1⟩ : ↥M) : V) * s ∉ M := by
        intro h
        apply hs
        have := M.mul_mem (M.inv_mem (φ.symm ⟨v' * s', h1⟩).2) h
        simpa using this
      rw [hFN _ hn]
      have e : ((φ.symm ⟨v' * s', h1⟩ : ↥M) : V) * s * s = ((φ.symm ⟨v' * s', h1⟩ : ↥M) : V) := by
        rw [mul_assoc, hss, mul_one]
      rw [e, hφ0 _ (φ.symm ⟨v' * s', h1⟩).2]
      simp [mul_assoc, hss']
  have hφ0g : ∀ g (a : V) (ha : a ∈ M), φ0 (ρ g a) = ρ' g (φ0 a) := by
    intro g a ha
    rw [hφ0 _ (hinvM g a ha), hφ0 a ha]
    exact congrArg Subtype.val (hφ g ⟨a, ha⟩)
  have hφ0c : ∀ g, φ0 (ρ g s * s⁻¹) = ρ' g s' * s'⁻¹ := by
    intro g
    rw [hφ0 _ (hM g s)]
    exact hcoc g
  refine ⟨MulEquiv.ofBijective Fm ⟨hFinj, hFsurj⟩, fun g v => ?_⟩
  show F (ρ g v) = ρ' g (F v)
  by_cases hv : v ∈ M
  · rw [hFM _ (hinvM g v hv), hFM v hv, hφ0g g v hv]
  · have hgv : ρ g v ∉ M := hnotinvM g v hv
    rw [hFN _ hgv, hFN v hv]
    have e1 : ρ g v * s = ρ g (v * s) * (ρ g s * s⁻¹)⁻¹ := by
      simp [map_mul, mul_comm, mul_left_comm, mul_assoc]
    have h1 : φ0 (ρ g v * s) = ρ' g (φ0 (v * s)) * (ρ' g s' * s'⁻¹)⁻¹ := by
      rw [e1, hφ0mul _ _ (hinvM g _ (hsM v hv)) (M.inv_mem (hM g s)), hφ0inv _ (hM g s),
        hφ0c g, hφ0g g _ (hsM v hv)]
    rw [h1, map_mul]
    have hs2 : (ρ' g s') * (ρ' g s') = 1 := by rw [← map_mul, hss', _root_.map_one]
    have e3 : (ρ' g s' * s'⁻¹)⁻¹ * s' = ρ' g s' := by
      have hgi : (ρ' g s')⁻¹ = ρ' g s' := inv_eq_of_mul_eq_one_right hs2
      rw [mul_inv, inv_inv, mul_assoc, hss', mul_one, hgi]
    rw [mul_assoc, e3]

end CFSG.Quasithin.B3
