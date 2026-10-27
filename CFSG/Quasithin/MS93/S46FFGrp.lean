module

public import CFSG.Quasithin.MS93.S46FFExt

public section

namespace CFSG.Quasithin.MS93.S46

open CFSG.Quasithin
open scoped commutatorElement

section Index2

variable {G : Type*} [Group G]

theorem exists_char_of_relIndex_eq_two {K₀ K : Subgroup G} (h : K₀.relIndex K = 2) :
    ∃ χ : ↥K →* ℂˣ, (∀ k, χ k = 1 ↔ (k : G) ∈ K₀) ∧ ∀ k, χ k ^ 2 = 1 := by
  have hN : (K₀.subgroupOf K).index = 2 := h
  have : (K₀.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hN
  have hQ : Nat.card (↥K ⧸ K₀.subgroupOf K) = 2 := hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
  let e : (↥K ⧸ K₀.subgroupOf K) ≃* Multiplicative (ZMod 2) := mulEquivOfPrimeCardEq hQ hZ
  refine ⟨(zmodTwoUnits.comp e.toMonoidHom).comp (QuotientGroup.mk' _), fun k => ?_, fun k => ?_⟩
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_eq_one_iff _ zmodTwoUnits_injective,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  · have h2 : (QuotientGroup.mk' (K₀.subgroupOf K) k) ^ 2 = 1 := by
      rw [← hQ]
      exact pow_card_eq_one'
    rw [← map_pow, MonoidHom.comp_apply, map_pow (QuotientGroup.mk' _), h2, map_one]

end Index2

section Comm

variable {𝔾 : Type} [Group 𝔾]

theorem commutatorElement_mul_right_of_commute {a b c : 𝔾} (h : b * ⁅a, c⁆ = ⁅a, c⁆ * b) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  have hX : b⁻¹ * ⁅a, c⁆ = ⁅a, c⁆ * b⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h, mul_inv_cancel_right]
  calc ⁅a, b * c⁆ = a * b * a⁻¹ * (⁅a, c⁆ * b⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = a * b * a⁻¹ * (b⁻¹ * ⁅a, c⁆) := by rw [hX]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by
        simp only [commutatorElement_def]
        group

theorem commutatorElement_mul_left_of_commute {a b c : 𝔾} (h : a * ⁅b, c⁆ = ⁅b, c⁆ * a) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  calc ⁅a * b, c⁆ = (a * ⁅b, c⁆) * a⁻¹ * ⁅a, c⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅b, c⁆ * a * a⁻¹ * ⁅a, c⁆ := by rw [h]
    _ = ⁅b, c⁆ * ⁅a, c⁆ := by rw [mul_inv_cancel_right]

variable {V K' : Subgroup 𝔾}

theorem commutator_mem_of_le (hVV : ⁅V, V⁆ ≤ K') (v w : ↥V) : ⁅(v : 𝔾), (w : 𝔾)⁆ ∈ K' :=
  hVV (Subgroup.commutator_mem_commutator v.2 w.2)

theorem exists_commPairing (hK'c : K' ≤ Subgroup.centralizer (V : Set 𝔾)) (hVV : ⁅V, V⁆ ≤ K')
    (χ : ↥K' →* ℂˣ) :
    ∃ φ : ↥V →* (↥V →* ℂˣ), ∀ v w : ↥V,
      φ v w = χ ⟨⁅(v : 𝔾), (w : 𝔾)⁆, commutator_mem_of_le hVV v w⟩ := by
  have hc : ∀ (u : ↥V) (k : 𝔾), k ∈ K' → (u : 𝔾) * k = k * u := fun u k hk =>
    Subgroup.mem_centralizer_iff.mp (hK'c hk) u u.2
  let ψ : ↥V → ↥V →* ℂˣ := fun v =>
    { toFun := fun w => χ ⟨⁅(v : 𝔾), (w : 𝔾)⁆, commutator_mem_of_le hVV v w⟩
      map_one' := by
        rw [← map_one χ]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun w w' => by
        rw [← map_mul]
        congr 1
        exact Subtype.ext (by
          show ⁅(v : 𝔾), ((w * w' : ↥V) : 𝔾)⁆ = ⁅(v : 𝔾), (w : 𝔾)⁆ * ⁅(v : 𝔾), (w' : 𝔾)⁆
          rw [Subgroup.coe_mul]
          exact commutatorElement_mul_right_of_commute
            (hc w _ (commutator_mem_of_le hVV v w'))) }
  refine ⟨{ toFun := ψ, map_one' := ?_, map_mul' := ?_ }, fun v w => rfl⟩
  · refine MonoidHom.ext fun w => ?_
    show χ ⟨⁅((1 : ↥V) : 𝔾), (w : 𝔾)⁆, _⟩ = 1
    rw [← map_one χ]
    congr 1
    exact Subtype.ext (by simp)
  · intro v v'
    refine MonoidHom.ext fun w => ?_
    show χ ⟨⁅((v * v' : ↥V) : 𝔾), (w : 𝔾)⁆, _⟩ =
      χ ⟨⁅(v : 𝔾), (w : 𝔾)⁆, _⟩ * χ ⟨⁅(v' : 𝔾), (w : 𝔾)⁆, _⟩
    rw [mul_comm, ← map_mul]
    congr 1
    exact Subtype.ext (by
      show ⁅((v * v' : ↥V) : 𝔾), (w : 𝔾)⁆ = ⁅(v' : 𝔾), (w : 𝔾)⁆ * ⁅(v : 𝔾), (w : 𝔾)⁆
      rw [Subgroup.coe_mul]
      exact commutatorElement_mul_left_of_commute (hc v _ (commutator_mem_of_le hVV v' w)))

end Comm

section Model

variable {Vt : Type} [Group Vt] (φ : Vt →* (Vt →* ℂˣ))

theorem exists_rangeForm (hskew : ∀ v w, φ v w = 1 → φ w v = 1) :
    ∃ ω : ↥φ.range →* ↥φ.range →* ℂˣ, ∀ v w : Vt,
      ω ⟨φ v, mem_range_apply φ v⟩ ⟨φ w, mem_range_apply φ w⟩ = φ v w := by
  classical
  have hex : ∀ t : ↥φ.range, ∃ w, φ w = t := fun t => MonoidHom.mem_range.mp t.2
  choose pre hpre using hex
  have hfib : ∀ (s : ↥φ.range) (u u' : Vt), φ u = φ u' →
      (s : Vt →* ℂˣ) u = (s : Vt →* ℂˣ) u' := by
    intro s u u' h
    obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp s.2
    rw [← hv]
    have h1 : φ (u⁻¹ * u') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have h2 : φ v (u⁻¹ * u') = 1 := hskew _ _ (by rw [h1, MonoidHom.one_apply])
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  let ωs : ↥φ.range → (↥φ.range →* ℂˣ) := fun s =>
    { toFun := fun t => (s : Vt →* ℂˣ) (pre t)
      map_one' := by
        rw [hfib s (pre 1) 1 (by rw [hpre, map_one]; rfl), map_one]
      map_mul' := fun t t' => by
        rw [hfib s (pre (t * t')) (pre t * pre t') (by rw [hpre, map_mul, hpre, hpre]; rfl),
          map_mul] }
  refine ⟨{ toFun := ωs, map_one' := ?_, map_mul' := ?_ }, fun v w => ?_⟩
  · refine MonoidHom.ext fun t => ?_
    show ((1 : ↥φ.range) : Vt →* ℂˣ) (pre t) = 1
    rfl
  · intro s s'
    refine MonoidHom.ext fun t => ?_
    show ((s * s' : ↥φ.range) : Vt →* ℂˣ) (pre t) = (s : Vt →* ℂˣ) (pre t) * (s' : Vt →* ℂˣ) (pre t)
    rfl
  · show φ v (pre ⟨φ w, mem_range_apply φ w⟩) = φ v w
    exact hfib ⟨φ v, mem_range_apply φ v⟩ _ _ (by rw [hpre])

theorem exists_rangeAction {Xt : Type*} [Group Xt] (c : Xt →* MulAut Vt)
    (hc : ∀ x v w, φ (c x v) (c x w) = φ v w) :
    ∃ σ : Xt →* MulAut ↥φ.range, ∀ x v,
      σ x ⟨φ v, mem_range_apply φ v⟩ = ⟨φ (c x v), mem_range_apply φ _⟩ := by
  let ρ₀ : Xt →* MulAut (Vt →* ℂˣ) := MonoidHom.mk' (fun x => (c x).monoidHomCongrLeft)
    fun x y => by
      refine MulEquiv.ext fun f => MonoidHom.ext fun w => ?_
      rw [map_mul]
      rfl
  have hρ₀ : ∀ x v, ρ₀ x (φ v) = φ (c x v) := by
    intro x v
    refine MonoidHom.ext fun w => ?_
    show φ v ((c x).symm w) = φ (c x v) w
    have := hc x v ((c x).symm w)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  have hinv : ∀ x, ∀ s ∈ φ.range, ρ₀ x s ∈ φ.range := by
    rintro x _ ⟨v, rfl⟩
    rw [hρ₀]
    exact mem_range_apply φ _
  refine ⟨(resHom φ.range).comp (ρ₀.codRestrict (stabSub φ.range) fun x =>
    range_le_stabSub ρ₀ hinv (mem_range_apply ρ₀ x)), fun x v => ?_⟩
  apply Subtype.ext
  exact hρ₀ x v

end Model

section Core

variable {F : Type} [Field F] [Fintype F] {n : ℕ} {X : Type} [Group X]

theorem sd_core (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Fintype.card F = 2 ^ n) (π : X →* SL3 F) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 → ∃ e : ℕ, x ^ 2 ^ e = 1) {S : Type} [CommGroup S] [Finite S]
    (hS2 : ∀ s : S, s ^ 2 = 1) (σ : X →* MulAut S) (ω : S →* S →* ℂˣ)
    (halt : ∀ s, ω s s = 1) (hinvω : ∀ x s t, ω (σ x s) (σ x t) = ω s t)
    (hnd : ∀ s, (∀ t, ω s t = 1) → s = 1) (A : Subgroup X) (hA2 : ∀ a ∈ A, π a ^ 2 = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, π a * π b = π b * π a) (hA1 : ∃ a ∈ A, π a ≠ 1)
    (L : Subgroup X) (hL : ⁅L, L⁆ = L) {P C : Subgroup S} (hPinv : ∀ x, ∀ p ∈ P, σ x p ∈ P)
    (hPfix : ∀ l ∈ L, ∀ p ∈ P, σ l p = p) (hCP : ∀ x ∈ A, ∀ c ∈ C, σ x c * c⁻¹ ∈ P)
    (hcardS : Nat.card S ≤ Nat.card ↥(A.map π) * Nat.card C) : ∀ l ∈ L, ∀ s, σ l s = s := by
  have hωskew : ∀ s t, ω s t = 1 → ω t s = 1 := fun s t h => by
    have := mul_eq_one_of_alt ω halt s t
    rwa [h, one_mul] at this
  have hR : perpIn ω ⊤ ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro s hs
    exact hnd s fun t => hs.2 t trivial
  have hpp : ∀ U : Subgroup S, perpIn ω ⊤ (perpIn ω ⊤ U) = U := fun U =>
    perpIn_perpIn ω hωskew (by rw [hR]; exact bot_le) le_top
  set T := perpIn ω ⊤ P with hT
  set R₀ := P ⊓ T with hR₀
  have htop : ∀ x, ∀ s ∈ (⊤ : Subgroup S), σ x s ∈ (⊤ : Subgroup S) := fun _ _ _ => trivial
  have hTinv : ∀ x, ∀ s ∈ T, σ x s ∈ T := perpIn_inv σ ω hinvω htop hPinv
  have hR₀inv : ∀ x, ∀ s ∈ R₀, σ x s ∈ R₀ := fun x s hs => ⟨hPinv x s hs.1, hTinv x s hs.2⟩
  have hR₀T : R₀ ≤ T := inf_le_right
  have h1 : ∀ u ∈ R₀, ∀ w ∈ T, ω u w = 1 := fun u hu w hw => hωskew _ _ (hw.2 u hu.1)
  have h2 : ∀ w ∈ T, ∀ u ∈ R₀, ω w u = 1 := fun w hw u hu => hw.2 u hu.1
  have hradT : ∀ w ∈ T, (∀ w' ∈ T, ω w w' = 1) → w ∈ R₀ :=
    fun w hw h => ⟨by rw [← hpp P]; exact ⟨trivial, h⟩, hw⟩
  set a := Nat.card ↥(A.map π) with ha
  have hfixSec : T ⊓ C ≤ B5.fixSec (A.map σ) T R₀ := by
    rintro w ⟨hwT, hwC⟩
    refine ⟨hwT, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hCP x hx w hwC, T.mul_mem (hTinv x w hwT) (T.inv_mem hwT)⟩
  have hffS' : Nat.card (Sec T R₀) ≤ a * Nat.card (fixV (A.map (secRho σ hTinv hR₀inv))) := by
    rw [map_secRho]
    have hAσT : A.map σ ≤ stabSub T :=
      (Subgroup.map_le_range σ A).trans (range_le_stabSub σ hTinv)
    have hAσR : A.map σ ≤ stabSub R₀ :=
      (Subgroup.map_le_range σ A).trans (range_le_stabSub σ hR₀inv)
    have k1 := B5.card_fixV_autSec_mul hR₀T hAσT hAσR
    have k2 := card_sec_mul hR₀T
    have k3 := card_sup_mul_card_inf T C
    have k4 : Nat.card ↥(T ⊔ C) ≤ Nat.card S := Subgroup.card_le_card_group _
    have k5 := Subgroup.card_le_of_le hfixSec
    have hTc : Nat.card T ≤ a * Nat.card (B5.fixSec (A.map σ) T R₀) := by
      refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos : 0 < Nat.card C)
      calc Nat.card T * Nat.card C = Nat.card ↥(T ⊔ C) * Nat.card ↥(T ⊓ C) := k3.symm
        _ ≤ Nat.card S * Nat.card (B5.fixSec (A.map σ) T R₀) := Nat.mul_le_mul k4 k5
        _ ≤ (a * Nat.card C) * Nat.card (B5.fixSec (A.map σ) T R₀) :=
            Nat.mul_le_mul_right _ hcardS
        _ = a * Nat.card (B5.fixSec (A.map σ) T R₀) * Nat.card C := by ring
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos : 0 < Nat.card R₀)
    calc Nat.card (Sec T R₀) * Nat.card R₀ = Nat.card T := k2
      _ ≤ a * Nat.card (B5.fixSec (A.map σ) T R₀) := hTc
      _ = a * Nat.card (fixV (autSec (A.map σ) T R₀)) * Nat.card R₀ := by rw [← k1]; ring
  have hS'triv := sd_ext_aux h14 hSQ hsq hF π hπ hker A hA2 hAc hA1 L hL
    (ι := MonoidHom.id ℂˣ) (fun _ _ h => h) _ (Sec T R₀) rfl (sec_sq hS2)
    (secRho σ hTinv hR₀inv) (secForm ω h1 h2)
    (fun s => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
      rw [secForm_mk]
      exact halt w)
    (fun x s t => secForm_inv σ hTinv hR₀inv ω h1 h2 hinvω x s t)
    (fun s hs => by
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective s
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hradT w w.2 fun w' hw' => by
        have := hs (QuotientGroup.mk ⟨w', hw'⟩)
        rwa [secForm_mk] at this)
    hffS'
  have hLT : ∀ l ∈ L, ∀ w ∈ T, σ l w * w⁻¹ ∈ R₀ := by
    intro l hl w hw
    have := hS'triv l hl (QuotientGroup.mk ⟨w, hw⟩)
    rw [secRho_mk, mk_eq_mk_iff, Subgroup.mem_subgroupOf] at this
    simpa using this
  have hLfixT := fix_of_two_step σ hL (U₁ := R₀) (U₂ := T) (fun l hl u hu => hPfix l hl u hu.1)
    hLT
  have hLfixPT : ∀ l ∈ L, ∀ s ∈ P ⊔ T, σ l s = s := by
    intro l hl s hs
    obtain ⟨p, hp, t, ht, rfl⟩ := Subgroup.mem_sup.mp hs
    rw [map_mul, hPfix l hl p hp, hLfixT l hl t ht]
  have hperpR₀ : perpIn ω ⊤ R₀ = P ⊔ T := by
    have hsup : perpIn ω ⊤ (P ⊔ T) = R₀ := by
      ext s
      constructor
      · intro hs
        refine ⟨?_, ⟨trivial, fun p hp => hs.2 p (Subgroup.mem_sup_left hp)⟩⟩
        rw [← hpp P]
        exact ⟨trivial, fun t ht => hs.2 t (Subgroup.mem_sup_right ht)⟩
      · rintro ⟨hsP, hsT⟩
        refine ⟨trivial, fun u hu => ?_⟩
        obtain ⟨p, hp, t, ht, rfl⟩ := Subgroup.mem_sup.mp hu
        rw [map_mul, hsT.2 p hp, one_mul]
        exact hωskew _ _ (ht.2 s hsP)
    rw [← hsup, hpp]
  have hLS : ∀ l ∈ L, ∀ s ∈ (⊤ : Subgroup S), σ l s * s⁻¹ ∈ P ⊔ T := by
    intro l hl s _
    rw [← hperpR₀]
    refine ⟨trivial, fun r hr => ?_⟩
    rw [map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply]
    have := hinvω l s r
    rw [hPfix l hl r hr.1] at this
    rw [this, mul_inv_cancel]
  intro l hl s
  exact fix_of_two_step σ hL hLfixPT hLS l hl s trivial

end Core

section Grp

variable {F : Type} [Field F] [Fintype F] {n : ℕ} {𝔾 : Type} [Group 𝔾]

theorem sd_group (h14 : MS14AS) (hSQ : SQTKQuot) (hsq : SQTKGroup (SL3 F))
    (hF : Fintype.card F = 2 ^ n) {X V K' K'' Ut Bh A Lg C₀ : Subgroup 𝔾} [Finite ↥X]
    [Finite ↥V] (π : ↥X →* SL3 F) (hπ : Function.Surjective π)
    (hker : ∀ x : ↥X, π x = 1 → ∃ e : ℕ, x ^ 2 ^ e = 1)
    (hXV : X ≤ Subgroup.normalizer (V : Set 𝔾)) (_hK'V : K' ≤ V)
    (hK'c : K' ≤ Subgroup.centralizer (V : Set 𝔾)) (hVV : ⁅V, V⁆ ≤ K') (hK'' : K'' ≤ K')
    (_hXK'' : X ≤ Subgroup.normalizer (K'' : Set 𝔾)) (hidx : K''.relIndex K' = 2)
    (hXK' : ⁅K', X⁆ ≤ K'') (hUt : ∀ v, v ∈ Ut ↔ v ∈ V ∧ ∀ w ∈ V, ⁅v, w⁆ ∈ K'')
    (hBh : Bh ≤ V) (hXBh : X ≤ Subgroup.normalizer (Bh : Set 𝔾)) (hLX : Lg ≤ X)
    (hLperf : ⁅Lg, Lg⁆ = Lg) (hBL : ⁅Bh, Lg⁆ ≤ Ut) (_hAX : A ≤ X)
    (hA2 : ∀ a : ↥X, (a : 𝔾) ∈ A → π a ^ 2 = 1)
    (hAc : ∀ a b : ↥X, (a : 𝔾) ∈ A → (b : 𝔾) ∈ A → π a * π b = π b * π a)
    (hA1 : ∃ a : ↥X, (a : 𝔾) ∈ A ∧ π a ≠ 1) (hC₀ : Bh ⊔ Ut ≤ C₀) (hC₀V : C₀ ≤ V)
    (hC₀A : ⁅C₀, A⁆ ≤ Bh ⊔ Ut) (hff : C₀.relIndex V ≤ Nat.card ↥((A.subgroupOf X).map π)) :
    ⁅V, Lg⁆ ≤ Ut := by
  classical
  obtain ⟨χ, hχ1, hχ2⟩ := exists_char_of_relIndex_eq_two hidx
  set cV : ↥X →* MulAut ↥V := V.normalizerMonoidHom.comp (Subgroup.inclusion hXV) with hcVdef
  have hcV : ∀ (x : ↥X) (v : ↥V), ((cV x v : ↥V) : 𝔾) = x * v * (x : 𝔾)⁻¹ := fun x v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe V _ v
  have hXK'c : ∀ (x : ↥X) (k : 𝔾), k ∈ K' → ⁅(x : 𝔾), k⁆ ∈ K'' := fun x k hk =>
    hXK' (by rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mem_commutator x.2 hk)
  have hXK'mem : ∀ (x : ↥X) (k : 𝔾), k ∈ K' → (x : 𝔾) * k * (x : 𝔾)⁻¹ ∈ K' := by
    intro x k hk
    have e : (x : 𝔾) * k * (x : 𝔾)⁻¹ = ⁅(x : 𝔾), k⁆ * k := by
      rw [commutatorElement_def, inv_mul_cancel_right]
    rw [e]
    exact K'.mul_mem (hK'' (hXK'c x k hk)) hk
  have hχX : ∀ (x : ↥X) (k : ↥K'), χ ⟨_, hXK'mem x k k.2⟩ = χ k := by
    intro x k
    have h1 : χ (⟨_, hXK'mem x k k.2⟩ * k⁻¹) = 1 := by
      rw [hχ1]
      show (x : 𝔾) * k * (x : 𝔾)⁻¹ * (k : 𝔾)⁻¹ ∈ K''
      exact hXK'c x k k.2
    rwa [map_mul, map_inv, mul_inv_eq_one] at h1
  obtain ⟨φ, hφ⟩ := exists_commPairing hK'c hVV χ
  have hskewV : ∀ v w : ↥V, φ v w = 1 → φ w v = 1 := by
    intro v w h
    rw [hφ, hχ1] at h ⊢
    show ⁅(w : 𝔾), (v : 𝔾)⁆ ∈ K''
    rw [← commutatorElement_inv]
    exact K''.inv_mem h
  have hkerφ : ∀ v : ↥V, φ v = 1 ↔ (v : 𝔾) ∈ Ut := by
    intro v
    rw [hUt]
    constructor
    · intro h
      refine ⟨v.2, fun w hw => ?_⟩
      have := DFunLike.congr_fun h ⟨w, hw⟩
      rw [hφ, MonoidHom.one_apply, hχ1] at this
      exact this
    · rintro ⟨-, h⟩
      refine MonoidHom.ext fun w => ?_
      rw [hφ, MonoidHom.one_apply, hχ1]
      exact h w w.2
  have hφX : ∀ x v w, φ (cV x v) (cV x w) = φ v w := by
    intro x v w
    rw [hφ, hφ, ← hχX x ⟨_, commutator_mem_of_le hVV v w⟩]
    congr 1
    apply Subtype.ext
    show ⁅((cV x v : ↥V) : 𝔾), ((cV x w : ↥V) : 𝔾)⁆ = (x : 𝔾) * ⁅(v : 𝔾), (w : 𝔾)⁆ * (x : 𝔾)⁻¹
    rw [hcV, hcV]
    simp only [commutatorElement_def]
    group
  obtain ⟨ω, hω⟩ := exists_rangeForm φ hskewV
  obtain ⟨σ, hσ⟩ := exists_rangeAction φ cV hφX
  set rr : ↥V →* ↥φ.range := φ.rangeRestrict with hrr
  have hrr_surj : Function.Surjective rr := φ.rangeRestrict_surjective
  have hrr_eq : ∀ v v' : ↥V, rr v = rr v' ↔ (v : 𝔾) * (v' : 𝔾)⁻¹ ∈ Ut := by
    intro v v'
    have h := hkerφ (v * v'⁻¹)
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [← h, map_mul, map_inv, mul_inv_eq_one]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hkerrr : rr.ker = Ut.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hkerφ]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hωrr : ∀ v w, ω (rr v) (rr w) = φ v w := hω
  have hσrr : ∀ x v, σ x (rr v) = rr (cV x v) := hσ
  have hS2 : ∀ s : ↥φ.range, s ^ 2 = 1 := by
    intro s
    obtain ⟨v, rfl⟩ := hrr_surj s
    rw [← map_pow]
    refine Subtype.ext (MonoidHom.ext fun w => ?_)
    show φ (v ^ 2) w = 1
    rw [map_pow, MonoidHom.pow_apply, hφ, hχ2]
  have halt : ∀ s, ω s s = 1 := by
    intro s
    obtain ⟨v, rfl⟩ := hrr_surj s
    rw [hωrr, hφ, hχ1]
    show ⁅(v : 𝔾), (v : 𝔾)⁆ ∈ K''
    rw [commutatorElement_self]
    exact K''.one_mem
  have hinvω : ∀ x s t, ω (σ x s) (σ x t) = ω s t := by
    intro x s t
    obtain ⟨v, rfl⟩ := hrr_surj s
    obtain ⟨w, rfl⟩ := hrr_surj t
    rw [hσrr, hσrr, hωrr, hωrr, hφX]
  have hnd : ∀ s, (∀ t, ω s t = 1) → s = 1 := by
    intro s h
    obtain ⟨v, rfl⟩ := hrr_surj s
    refine Subtype.ext (MonoidHom.ext fun w => ?_)
    have := h (rr w)
    rw [hωrr] at this
    exact this
  set P : Subgroup ↥φ.range := (Bh.subgroupOf V).map rr with hPdef
  set Cb : Subgroup ↥φ.range := (C₀.subgroupOf V).map rr with hCbdef
  have hcVBh : ∀ (x : ↥X) (v : ↥V), (v : 𝔾) ∈ Bh → ((cV x v : ↥V) : 𝔾) ∈ Bh := by
    intro x v hv
    rw [hcV]
    exact (Subgroup.mem_normalizer_iff.mp (hXBh x.2) _).mp hv
  have hPinv : ∀ x, ∀ p ∈ P, σ x p ∈ P := by
    rintro x _ ⟨v, hv, rfl⟩
    rw [hσrr]
    exact ⟨cV x v, Subgroup.mem_subgroupOf.mpr (hcVBh x v hv), rfl⟩
  have hLcomm : ∀ (l : ↥X), (l : 𝔾) ∈ Lg → ∀ v : ↥V, (v : 𝔾) ∈ Bh → rr (cV l v) = rr v := by
    intro l hl v hv
    rw [hrr_eq, hcV]
    have : ⁅(l : 𝔾), (v : 𝔾)⁆ ∈ Ut := by
      apply hBL
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hl hv
    simpa [commutatorElement_def, mul_assoc] using this
  have hPfix : ∀ l ∈ Lg.subgroupOf X, ∀ p ∈ P, σ l p = p := by
    rintro l hl _ ⟨v, hv, rfl⟩
    rw [hσrr]
    exact hLcomm l (Subgroup.mem_subgroupOf.mp hl) v (Subgroup.mem_subgroupOf.mp hv)
  have hcardS : Nat.card ↥φ.range ≤ Nat.card ↥((A.subgroupOf X).map π) * Nat.card Cb := by
    have h3 := B1More.card_map_mul_card_inf_ker (⊤ : Subgroup ↥V) rr
    have h4 := B1More.card_map_mul_card_inf_ker (C₀.subgroupOf V) rr
    have hUtC : Ut.subgroupOf V ≤ C₀.subgroupOf V := fun v hv =>
      Subgroup.mem_subgroupOf.mpr (hC₀ (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hv)))
    rw [top_inf_eq, hkerrr, Subgroup.map_top_of_surjective rr hrr_surj, Subgroup.card_top,
      Subgroup.card_top] at h3
    rw [hkerrr, inf_eq_right.mpr hUtC] at h4
    have h5 := Subgroup.relIndex_mul_card C₀ V
    rw [inf_eq_left.mpr hC₀V] at h5
    have hcC : Nat.card ↥(C₀.subgroupOf V) = Nat.card C₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC₀V).toEquiv
    rw [hcC] at h4
    have hU : 0 < Nat.card ↥(Ut.subgroupOf V) := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hU
    calc Nat.card ↥φ.range * Nat.card ↥(Ut.subgroupOf V) = Nat.card ↥V := h3
      _ = C₀.relIndex V * Nat.card C₀ := h5.symm
      _ ≤ Nat.card ↥((A.subgroupOf X).map π) * Nat.card C₀ := Nat.mul_le_mul_right _ hff
      _ = Nat.card ↥((A.subgroupOf X).map π) * Nat.card Cb * Nat.card ↥(Ut.subgroupOf V) := by
          rw [← h4]; ring
  have himg : (Bh.subgroupOf V ⊔ Ut.subgroupOf V).map rr = P := by
    have hUt0 : (Ut.subgroupOf V).map rr = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr hkerrr.ge
    rw [Subgroup.map_sup, hUt0, sup_bot_eq]
  have hCbP : ∀ x ∈ A.subgroupOf X, ∀ c ∈ Cb, σ x c * c⁻¹ ∈ P := by
    rintro x hx _ ⟨c, hc, rfl⟩
    rw [hσrr, ← map_inv, ← map_mul]
    have hmem : ((cV x c * c⁻¹ : ↥V) : 𝔾) ∈ Bh ⊔ Ut := by
      have : ⁅(x : 𝔾), (c : 𝔾)⁆ ∈ Bh ⊔ Ut := by
        apply hC₀A
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mp hx)
          (Subgroup.mem_subgroupOf.mp hc)
      simpa [hcV, commutatorElement_def, mul_assoc] using this
    have hsup : (Bh ⊔ Ut).subgroupOf V = Bh.subgroupOf V ⊔ Ut.subgroupOf V :=
      Subgroup.subgroupOf_sup hBh fun u hu => ((hUt u).mp hu).1
    have hmem' : cV x c * c⁻¹ ∈ Bh.subgroupOf V ⊔ Ut.subgroupOf V := by
      rw [← hsup]
      exact Subgroup.mem_subgroupOf.mpr hmem
    rw [← himg]
    exact Subgroup.mem_map_of_mem rr hmem'
  have hL'perf : ⁅Lg.subgroupOf X, Lg.subgroupOf X⁆ = Lg.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLX, hLperf]
  have hLfix := sd_core h14 hSQ hsq hF π hπ hker hS2 σ ω halt hinvω hnd (A.subgroupOf X)
    (fun a ha => hA2 a (Subgroup.mem_subgroupOf.mp ha))
    (fun a ha b hb => hAc a b (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb))
    (by
      obtain ⟨a, ha, h⟩ := hA1
      exact ⟨a, Subgroup.mem_subgroupOf.mpr ha, h⟩)
    (Lg.subgroupOf X) hL'perf hPinv hPfix hCbP hcardS
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have h3 := hLfix ⟨l, hLX hl⟩ (Subgroup.mem_subgroupOf.mpr hl) (rr ⟨v, hv⟩)
  rw [hσrr, hrr_eq, hcV] at h3
  have h4 := Ut.inv_mem h3
  simpa [commutatorElement_def, mul_assoc] using h4

end Grp

end CFSG.Quasithin.MS93.S46
