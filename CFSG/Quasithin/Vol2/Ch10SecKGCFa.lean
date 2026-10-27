module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KG

variable {V : Type} [CommGroup V] {F : Type} [Field F]

structure IsScalarAct (sm : F → V →* V) : Prop where
  add : ∀ c d v, sm (c + d) v = sm c v * sm d v
  mul : ∀ c d v, sm (c * d) v = sm c (sm d v)
  one : ∀ v, sm 1 v = v

@[expose] def IsSemi (sm : F → V →* V) (g : MulAut V) (σ : F ≃+* F) : Prop :=
  ∀ c v, g (sm c v) = sm (σ c) (g v)

namespace IsScalarAct

variable {sm : F → V →* V}

theorem zero (hs : IsScalarAct sm) (v : V) : sm 0 v = 1 := by
  have h := hs.add 0 0 v
  rw [add_zero] at h
  exact mul_left_cancel (h.symm.trans (mul_one _).symm)

theorem neg (hs : IsScalarAct sm) (c : F) (v : V) : sm (-c) v = (sm c v)⁻¹ := by
  have h := hs.add c (-c) v
  rw [add_neg_cancel, hs.zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem eq_one_of_eq_one (hs : IsScalarAct sm) {c : F} (hc : c ≠ 0) {v : V} (h : sm c v = 1) :
    v = 1 := by
  rw [← hs.one v, ← inv_mul_cancel₀ hc, hs.mul, h, map_one]

theorem eq_of_eq (hs : IsScalarAct sm) {c d : F} {v : V} (hv : v ≠ 1) (h : sm c v = sm d v) :
    c = d := by
  by_contra hcd
  refine hv (hs.eq_one_of_eq_one (sub_ne_zero.mpr hcd) ?_)
  rw [sub_eq_add_neg, hs.add, hs.neg, h, mul_inv_cancel]

theorem sq_eq_one [CharP F 2] (hs : IsScalarAct sm) (v : V) : v ^ 2 = 1 := by
  have h := hs.add 1 1 v
  rw [CharTwo.add_self_eq_zero, hs.zero, hs.one] at h
  rw [pow_two, h]

end IsScalarAct

namespace IsSemi

variable {sm : F → V →* V} {g h : MulAut V} {σ τ : F ≃+* F}

theorem one' : IsSemi sm 1 1 := fun _ _ => rfl

theorem mul (hg : IsSemi sm g σ) (hh : IsSemi sm h τ) : IsSemi sm (g * h) (σ * τ) :=
  fun c v => by
    rw [MulAut.mul_apply, MulAut.mul_apply, hh, hg]
    rfl

theorem inv (hg : IsSemi sm g σ) : IsSemi sm g⁻¹ σ⁻¹ := fun c v => by
  have h1 := hg (σ⁻¹ c) (g⁻¹ v)
  rw [show σ (σ⁻¹ c) = c from σ.apply_symm_apply c, MulAut.apply_inv_self] at h1
  rw [← h1, MulAut.inv_apply_self]

theorem pow (hg : IsSemi sm g σ) (k : ℕ) : IsSemi sm (g ^ k) (σ ^ k) := by
  induction k with
  | zero => exact one'
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hg

theorem unique (hs : IsScalarAct sm) [Nontrivial V] (h1 : IsSemi sm g σ) (h2 : IsSemi sm g τ) :
    σ = τ := by
  obtain ⟨w, hw⟩ := exists_ne (1 : V)
  ext c
  have e1 := h1 c (g⁻¹ w)
  have e2 := h2 c (g⁻¹ w)
  rw [MulAut.apply_inv_self] at e1 e2
  exact hs.eq_of_eq hw (e1.symm.trans e2)

end IsSemi

theorem inv_conj_mem {G : Type*} [Group G] {H : Subgroup G} [Finite H] {g : G}
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) : ∀ h ∈ H, g⁻¹ * h * g ∈ H := by
  let φ : H → H := fun h => ⟨g * h * g⁻¹, hg h h.2⟩
  have hφ : Function.Injective φ := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    simp only [φ, mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext h1
  intro h hh
  obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.mp hφ) ⟨h, hh⟩
  have h1 : g * k * g⁻¹ = h := congrArg Subtype.val hk
  rw [← h1]
  simp [mul_assoc]

variable {sm : F → V →* V}

theorem exists_isSemi [Finite F] [Nontrivial V] (hs : IsScalarAct sm) {H : Subgroup (MulAut V)}
    (hsH : ∀ h ∈ H, ∀ c v, sm c (h v) = h (sm c v))
    (hcomm : ∀ f : V →* V, (∀ h ∈ H, ∀ v, f (h v) = h (f v)) → ∃ c, ∀ v, f v = sm c v)
    {g : MulAut V} (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H) : ∃ σ : F ≃+* F, IsSemi sm g σ := by
  obtain ⟨w, hw⟩ := exists_ne (1 : V)
  have key : ∀ c : F, ∃ d : F, ∀ v, g (sm c (g⁻¹ v)) = sm d v := by
    intro c
    refine hcomm ((g : V ≃* V).toMonoidHom.comp ((sm c).comp (g⁻¹ : V ≃* V).toMonoidHom))
      fun h hh v => ?_
    have e1 : g⁻¹ (h v) = (g⁻¹ * h * g) (g⁻¹ v) := by simp [MulAut.mul_apply]
    change g (sm c (g⁻¹ (h v))) = h (g (sm c (g⁻¹ v)))
    rw [e1, hsH _ (hg h hh) c]
    simp [MulAut.mul_apply]
  choose σf hσf using key
  have hsl : ∀ c v, g (sm c v) = sm (σf c) (g v) := fun c v => by
    have := hσf c (g v)
    rwa [MulAut.inv_apply_self] at this
  have huniq : ∀ a b : F, (∀ v, sm a (g v) = sm b (g v)) → a = b := fun a b h => by
    have := h (g⁻¹ w)
    rw [MulAut.apply_inv_self] at this
    exact hs.eq_of_eq hw this
  let σr : F →+* F :=
    { toFun := σf
      map_one' := huniq _ _ fun v => by rw [← hsl, hs.one, hs.one]
      map_mul' := fun a b => huniq _ _ fun v => by rw [← hsl, hs.mul a b, hsl, hsl, hs.mul]
      map_zero' := huniq _ _ fun v => by simp only [← hsl, hs.zero, map_one]
      map_add' := fun a b => huniq _ _ fun v => by
        rw [← hsl, hs.add a b, map_mul, hsl, hsl, hs.add] }
  have hinj : Function.Injective σr := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hc0
    have h1 := hsl c w
    rw [show σf c = 0 from hc, hs.zero, map_eq_one_iff _ (MulEquiv.injective g)] at h1
    exact hw (hs.eq_one_of_eq_one hc0 h1)
  exact ⟨RingEquiv.ofBijective σr ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hsl⟩

theorem exists_fixed [Finite V] [Nontrivial V] [CharP F 2] (hs : IsScalarAct sm)
    {R : Subgroup (MulAut V)} (hR : IsPGroup 2 R) :
    ∃ v₀ : V, (∀ ρ ∈ R, ρ v₀ = v₀) ∧ v₀ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : IsPGroup 2 V := fun v => ⟨1, by rw [pow_one]; exact hs.sq_eq_one v⟩
  obtain ⟨k, hk0, hk⟩ := hV2.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card V := by
    rw [hk]
    exact dvd_pow_self 2 hk0.ne'
  obtain ⟨b, hb, hne⟩ := hR.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hdvd
    (a := 1) fun ρ => show (ρ : MulAut V) 1 = 1 from map_one _
  exact ⟨b, fun ρ hρ => hb ⟨ρ, hρ⟩, hne.symm⟩

theorem mem_of_fix {p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hF : Nat.card F = p ^ n)
    {P : Subgroup (F ≃+* F)} {σ : F ≃+* F} (hσ : ∀ c, (∀ τ ∈ P, τ c = c) → σ c = c) : σ ∈ P := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero n hp.ne_zero)
  have : Finite (F ≃+* F) := Finite.of_injective (fun τ : F ≃+* F => (τ : F → F))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  set Q := P ⊔ Subgroup.zpowers σ with hQ
  have hQfix : ∀ c, (∀ τ ∈ P, τ c = c) → ∀ τ ∈ Q, τ c = c := by
    intro c hc
    have hle : Q ≤ MulAction.stabilizer (F ≃+* F) c :=
      sup_le (fun τ hτ => MulAction.mem_stabilizer_iff.mpr (hc τ hτ))
        (Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr (hσ c hc)))
    exact fun τ hτ => MulAction.mem_stabilizer_iff.mp (hle hτ)
  obtain ⟨-, -, -, -, -, hA⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp hn hF
  obtain ⟨hPn, SP, hSP, hcP⟩ := hA P
  obtain ⟨hQn, SQ, hSQ, hcQ⟩ := hA Q
  have hS : SP = SQ := SetLike.coe_injective (by
    rw [hSP, hSQ]
    ext c
    exact ⟨fun hc => hQfix c hc, fun hc τ hτ => hc τ (le_sup_left (a := P) hτ)⟩)
  have h1 : n / Nat.card P = n / Nat.card Q := by
    rw [hS] at hcP
    exact Nat.pow_right_injective hp.two_le (hcP.symm.trans hcQ)
  have hPpos : 0 < n / Nat.card P := Nat.div_pos (Nat.le_of_dvd (by omega) hPn) Nat.card_pos
  have hcard : Nat.card P = Nat.card Q := by
    have e1 := Nat.div_mul_cancel hPn
    have e2 := Nat.div_mul_cancel hQn
    rw [← h1] at e2
    exact Nat.eq_of_mul_eq_mul_left hPpos (e1.trans e2.symm)
  have hPQ : P = Q := Subgroup.eq_of_le_of_card_ge le_sup_left hcard.ge
  exact hPQ ▸ (le_sup_right (b := Subgroup.zpowers σ) (Subgroup.mem_zpowers σ))

theorem eq_one_of_isSemi_fix [Finite V] [Nontrivial V] [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hs : IsScalarAct sm) {R : Subgroup (MulAut V)}
    (hR : IsPGroup 2 R) (hRs : ∀ ρ ∈ R, ∃ τ, IsSemi sm ρ τ) {x : MulAut V} {σ : F ≃+* F}
    (hx : IsSemi sm x σ) {r : ℕ} (hr : Odd r) (hxr : x ^ r = 1)
    (hfix : ∀ v, (∀ ρ ∈ R, ρ v = v) → x v = v) : σ = 1 := by
  let P : Subgroup (F ≃+* F) :=
    { carrier := {τ | ∃ ρ ∈ R, IsSemi sm ρ τ}
      one_mem' := ⟨1, R.one_mem, IsSemi.one'⟩
      mul_mem' := fun ⟨ρ₁, h₁, e₁⟩ ⟨ρ₂, h₂, e₂⟩ => ⟨ρ₁ * ρ₂, R.mul_mem h₁ h₂, e₁.mul e₂⟩
      inv_mem' := fun ⟨ρ, h, e⟩ => ⟨ρ⁻¹, R.inv_mem h, e.inv⟩ }
  have hP2 : IsPGroup 2 P := by
    rintro ⟨τ, ρ, hρ, hτ⟩
    obtain ⟨k, hk⟩ := hR ⟨ρ, hρ⟩
    have hk' : ρ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 := hτ.pow (2 ^ k)
    rw [hk'] at h1
    exact ⟨k, Subtype.ext (h1.unique hs IsSemi.one')⟩
  have hσr : σ ^ r = 1 := by
    have h1 := hx.pow r
    rw [hxr] at h1
    exact h1.unique hs IsSemi.one'
  obtain ⟨v₀, hv₀, hv₀1⟩ := exists_fixed hs hR
  have hσP : σ ∈ P := by
    refine mem_of_fix Nat.prime_two hn hF fun c hc => ?_
    have hcv : ∀ ρ ∈ R, ρ (sm c v₀) = sm c v₀ := by
      intro ρ hρ
      obtain ⟨τ, hτ⟩ := hRs ρ hρ
      rw [hτ, hc τ ⟨ρ, hρ, hτ⟩, hv₀ ρ hρ]
    have h1 := hfix _ hcv
    rw [hx, hfix v₀ hv₀] at h1
    exact hs.eq_of_eq hv₀1 h1
  obtain ⟨k, hk⟩ := hP2 ⟨σ, hσP⟩
  have hk' : σ ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hco : Nat.Coprime (2 ^ k) r := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hr)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco (orderOf_dvd_of_pow_eq_one hk')
    (orderOf_dvd_of_pow_eq_one hσr))

theorem isSemi_one_of_fix [Finite V] [Nontrivial V] [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hs : IsScalarAct sm) {H R : Subgroup (MulAut V)}
    (hsH : ∀ h ∈ H, ∀ c v, sm c (h v) = h (sm c v))
    (hcomm : ∀ f : V →* V, (∀ h ∈ H, ∀ v, f (h v) = h (f v)) → ∃ c, ∀ v, f v = sm c v)
    (hR : IsPGroup 2 R) (hRH : ∀ ρ ∈ R, ∀ h ∈ H, ρ * h * ρ⁻¹ ∈ H) {x : MulAut V} {r : ℕ}
    (hr : Odd r) (hxr : x ^ r = 1) (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hfix : ∀ v, (∀ ρ ∈ R, ρ v = v) → x v = v) : IsSemi sm x 1 := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; positivity)
  have : Finite (MulAut V) := MulEquiv.finite_left
  have hRs : ∀ ρ ∈ R, ∃ τ, IsSemi sm ρ τ := fun ρ hρ =>
    exists_isSemi hs hsH hcomm (inv_conj_mem (hRH ρ hρ))
  obtain ⟨σ, hσ⟩ := exists_isSemi hs hsH hcomm (inv_conj_mem hxH)
  rwa [← eq_one_of_isSemi_fix hn hF hs hR hRs hσ hr hxr hfix]

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KG
