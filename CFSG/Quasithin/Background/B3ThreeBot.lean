module

public import CFSG.Quasithin.Background.B3ThreeDual
public import CFSG.Quasithin.Background.B3ThreeGen

public section

namespace CFSG.Quasithin.B3

variable {n : ℕ}

abbrev WV (n : ℕ) : Type := Mod.V n Mod.ut0

theorem exists_section {M W : Type*} [CommGroup M] [CommGroup W] (hM2 : ∀ m : M, m ^ 2 = 1)
    (π : M →* W) (hπ : Function.Surjective π) : ∃ σ : W →* M, ∀ w, π (σ w) = w := by
  obtain ⟨S, hS1, hS2⟩ := exists_complement hM2 π.ker
  have hinj : Function.Injective (π.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have h1 : (s : M) ∈ π.ker ⊓ S := ⟨hs, s.2⟩
    rw [hS1, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hsurj : Function.Surjective (π.comp S.subtype) := by
    intro w
    obtain ⟨m, rfl⟩ := hπ w
    have hm : m ∈ π.ker ⊔ S := by rw [hS2]; exact Subgroup.mem_top m
    obtain ⟨k, hk, s, hs, rfl⟩ := Subgroup.mem_sup.1 hm
    refine ⟨⟨s, hs⟩, ?_⟩
    show π s = π (k * s)
    rw [map_mul, MonoidHom.mem_ker.1 hk, one_mul]
  let e : ↥S ≃* W := MulEquiv.ofBijective (π.comp S.subtype) ⟨hinj, hsurj⟩
  refine ⟨S.subtype.comp e.symm.toMonoidHom, fun w => ?_⟩
  show π ((e.symm w : ↥S) : M) = w
  have := e.apply_symm_apply w
  exact this

structure ExtBot (n : ℕ) {M : Type*} [CommGroup M] (ρ : LG n →* MulAut M) (A : Subgroup M)
    (π : M →* WV n) : Prop where
  sq : ∀ m : M, m ^ 2 = 1
  surj : Function.Surjective π
  equiv : ∀ g m, π (ρ g m) = actL n Mod.ut0 g (π m)
  ker : ∀ m, π m = 1 ↔ m ∈ A
  fix : ∀ g, ∀ a ∈ A, ρ g a = a

variable {M : Type*} [CommGroup M] {ρ : LG n →* MulAut M} {A : Subgroup M} {π : M →* WV n}

theorem actL_inv_apply (g : LG n) (w : WV n) : actL n Mod.ut0 g (actL n Mod.ut0 g⁻¹ w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem actL_inv_apply' (g : LG n) (w : WV n) : actL n Mod.ut0 g⁻¹ (actL n Mod.ut0 g w) = w := by
  rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

@[expose] noncomputable def dlt (ρ : LG n →* MulAut M) (σ : WV n →* M) (g : LG n) (w : WV n) : M :=
  ρ g (σ (actL n Mod.ut0 g⁻¹ w)) * (σ w)⁻¹

theorem dlt_mem (E : ExtBot n ρ A π) {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w) (g : LG n)
    (w : WV n) : dlt ρ σ g w ∈ A := by
  rw [← E.ker]
  have h1 : π ((σ w)⁻¹) = (π (σ w))⁻¹ := map_inv π _
  unfold dlt
  rw [map_mul, h1, E.equiv, hσ, hσ, actL_inv_apply]
  exact mul_inv_cancel _

theorem dlt_mul_right (σ : WV n →* M) (g : LG n) (w w' : WV n) :
    dlt ρ σ g (w * w') = dlt ρ σ g w * dlt ρ σ g w' := by
  simp only [dlt, map_mul, mul_inv]
  ac_rfl

theorem dlt_one (σ : WV n →* M) (g : LG n) : dlt ρ σ g 1 = 1 := by
  unfold dlt
  simp

theorem dlt_comp (E : ExtBot n ρ A π) {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w) (g h : LG n)
    (w : WV n) :
    dlt ρ σ (g * h) w = dlt ρ σ h (actL n Mod.ut0 g⁻¹ w) * dlt ρ σ g w := by
  have hA := dlt_mem E hσ h (actL n Mod.ut0 g⁻¹ w)
  have e1 : ρ g (dlt ρ σ h (actL n Mod.ut0 g⁻¹ w)) = dlt ρ σ h (actL n Mod.ut0 g⁻¹ w) :=
    E.fix g _ hA
  have e2 : actL n Mod.ut0 (g * h)⁻¹ w = actL n Mod.ut0 h⁻¹ (actL n Mod.ut0 g⁻¹ w) := by
    rw [mul_inv_rev, map_mul]
    rfl
  have e3 : ρ h (σ (actL n Mod.ut0 h⁻¹ (actL n Mod.ut0 g⁻¹ w))) =
      dlt ρ σ h (actL n Mod.ut0 g⁻¹ w) * σ (actL n Mod.ut0 g⁻¹ w) := by
    unfold dlt
    simp
  have e4 : ρ (g * h) (σ (actL n Mod.ut0 (g * h)⁻¹ w)) =
      ρ g (dlt ρ σ h (actL n Mod.ut0 g⁻¹ w) * σ (actL n Mod.ut0 g⁻¹ w)) := by
    rw [e2, map_mul]
    show ρ g (ρ h (σ _)) = _
    rw [e3]
  have e5 : ρ g (dlt ρ σ h (actL n Mod.ut0 g⁻¹ w) * σ (actL n Mod.ut0 g⁻¹ w)) =
      dlt ρ σ h (actL n Mod.ut0 g⁻¹ w) * ρ g (σ (actL n Mod.ut0 g⁻¹ w)) := by
    rw [map_mul, e1]
  have e6 : dlt ρ σ g w = ρ g (σ (actL n Mod.ut0 g⁻¹ w)) * (σ w)⁻¹ := rfl
  show ρ (g * h) (σ (actL n Mod.ut0 (g * h)⁻¹ w)) * (σ w)⁻¹ = _
  rw [e4, e5, e6, mul_assoc]

theorem theta_actL (g : LG n) (u w : WV n) :
    Theta n (actL n Mod.ut0 g u) w = Theta n u (actL n Mod.ut0 g⁻¹ w) := by
  have := Theta_act g.1 u (actL n Mod.ut0 g⁻¹ w)
  rw [show Mod.act n Mod.ut0 g.1 (actL n Mod.ut0 g⁻¹ w) = w from actL_inv_apply g w] at this
  exact this

@[expose] noncomputable def flam (E : ExtBot n ρ A π) {σ : WV n →* M}
    (hσ : ∀ w, π (σ w) = w) (lam : A →* ℤˣ) (g : LG n) : WV n →* ℤˣ where
  toFun w := lam ⟨dlt ρ σ g w, dlt_mem E hσ g w⟩
  map_one' := by
    have : (⟨dlt ρ σ g 1, dlt_mem E hσ g 1⟩ : A) = 1 := Subtype.ext (dlt_one σ g)
    rw [this, map_one]
  map_mul' w w' := by
    have : (⟨dlt ρ σ g (w * w'), dlt_mem E hσ g (w * w')⟩ : A) =
        ⟨dlt ρ σ g w, dlt_mem E hσ g w⟩ * ⟨dlt ρ σ g w', dlt_mem E hσ g w'⟩ :=
      Subtype.ext (dlt_mul_right σ g w w')
    rw [this, map_mul]

theorem flam_apply (E : ExtBot n ρ A π) {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w) (lam : A →* ℤˣ)
    (g : LG n) (w : WV n) :
    flam E hσ lam g w = lam ⟨dlt ρ σ g w, dlt_mem E hσ g w⟩ := rfl

theorem exists_D (hn : 5 ≤ n) (E : ExtBot n ρ A π) {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w)
    (lam : A →* ℤˣ) : ∃ D : LG n → WV n, ∀ g, Theta n (D g) = flam E hσ lam g := by
  have : ∀ g, ∃ u, Theta n u = flam E hσ lam g := fun g => (exists_unique_theta hn _).exists
  choose D hD using this
  exact ⟨D, hD⟩

theorem isDer_of_theta (hn : 5 ≤ n) (E : ExtBot n ρ A π) {σ : WV n →* M}
    (hσ : ∀ w, π (σ w) = w) (lam : A →* ℤˣ) {D : LG n → WV n}
    (hD : ∀ g, Theta n (D g) = flam E hσ lam g) : IsDer (actL n Mod.ut0) D := by
  intro g h
  apply Theta_injective (Nat.le_trans (by norm_num) hn)
  refine MonoidHom.ext fun w => ?_
  rw [hD (g * h), map_mul, MonoidHom.mul_apply, theta_actL, hD g, hD h, flam_apply, flam_apply,
    flam_apply]
  have : (⟨dlt ρ σ (g * h) w, dlt_mem E hσ (g * h) w⟩ : A) =
      ⟨dlt ρ σ h (actL n Mod.ut0 g⁻¹ w), dlt_mem E hσ h _⟩ * ⟨dlt ρ σ g w, dlt_mem E hσ g w⟩ :=
    Subtype.ext (dlt_comp E hσ g h w)
  rw [this, map_mul, mul_comm]

theorem flam_of_pder (E : ExtBot n ρ A π) {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w)
    (lam : A →* ℤˣ) {D : LG n → WV n} (hD : ∀ g, Theta n (D g) = flam E hσ lam g) {v : WV n}
    (hv : D = pder (actL n Mod.ut0) v) (g : LG n) (w : WV n) :
    lam ⟨dlt ρ σ g w, dlt_mem E hσ g w⟩ = Theta n v (actL n Mod.ut0 g⁻¹ w) * (Theta n v w)⁻¹ := by
  rw [← flam_apply E hσ lam g w, ← hD g, hv]
  simp only [pder, map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply]
  rw [theta_actL, map_inv]

theorem exists_invariant_of_prin (E : ExtBot n ρ A π) {σ : WV n →* M}
    (hσ : ∀ w, π (σ w) = w) (lam : A →* ℤˣ) {D : LG n → WV n}
    (hD : ∀ g, Theta n (D g) = flam E hσ lam g) {v : WV n}
    (hv : D = pder (actL n Mod.ut0) v) :
    ∃ Λ : M →* ℤˣ, (∀ g m, Λ (ρ g m) = Λ m) ∧ ∀ a (ha : a ∈ A), Λ a = lam ⟨a, ha⟩ := by
  have hmem : ∀ m : M, m * (σ (π m))⁻¹ ∈ A := fun m => by
    rw [← E.ker, map_mul, map_inv, hσ, mul_inv_cancel]
  let projA : M →* A := MonoidHom.mk' (fun m => ⟨m * (σ (π m))⁻¹, hmem m⟩) (fun m m' => by
    apply Subtype.ext
    show m * m' * (σ (π (m * m')))⁻¹ = (m * (σ (π m))⁻¹) * (m' * (σ (π m'))⁻¹)
    rw [map_mul, map_mul, mul_inv]
    ac_rfl)
  let α : WV n →* ℤˣ := Theta n v
  refine ⟨(lam.comp projA) * (α.comp π), fun g m => ?_, fun a ha => ?_⟩
  · show lam (projA (ρ g m)) * α (π (ρ g m)) = lam (projA m) * α (π m)
    rw [E.equiv]
    have hfix : ρ g (m * (σ (π m))⁻¹) = m * (σ (π m))⁻¹ := E.fix g _ (hmem m)
    rw [map_mul, map_inv] at hfix
    have hρ : ρ g m = (m * (σ (π m))⁻¹) * ρ g (σ (π m)) := mul_inv_eq_iff_eq_mul.1 hfix
    have hp : projA (ρ g m) = projA m *
        ⟨dlt ρ σ g (actL n Mod.ut0 g (π m)), dlt_mem E hσ g _⟩ := by
      apply Subtype.ext
      show ρ g m * (σ (π (ρ g m)))⁻¹ = (m * (σ (π m))⁻¹) * dlt ρ σ g (actL n Mod.ut0 g (π m))
      rw [E.equiv]
      unfold dlt
      rw [actL_inv_apply', hρ]
      ac_rfl
    rw [hp, map_mul]
    have hstar := flam_of_pder E hσ lam hD hv g (actL n Mod.ut0 g (π m))
    rw [actL_inv_apply'] at hstar
    show lam (projA m) * lam ⟨dlt ρ σ g (actL n Mod.ut0 g (π m)), _⟩ *
      α (actL n Mod.ut0 g (π m)) = lam (projA m) * α (π m)
    rw [hstar]
    show lam (projA m) * (Theta n v (π m) * (Theta n v (actL n Mod.ut0 g (π m)))⁻¹) *
      Theta n v (actL n Mod.ut0 g (π m)) = lam (projA m) * Theta n v (π m)
    rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
  · show lam (projA a) * α (π a) = lam ⟨a, ha⟩
    have h1 : π a = 1 := (E.ker a).2 ha
    rw [h1, map_one, mul_one]
    have : projA a = ⟨a, ha⟩ := by
      apply Subtype.ext
      show a * (σ (π a))⁻¹ = a
      rw [h1, map_one, inv_one, mul_one]
    rw [this]

theorem lam_eq_one_of_prin (E : ExtBot n ρ A π) {σ : WV n →* M}
    (hσ : ∀ w, π (σ w) = w) (lam : A →* ℤˣ) {D : LG n → WV n}
    (hD : ∀ g, Theta n (D g) = flam E hσ lam g) {v : WV n}
    (hv : D = pder (actL n Mod.ut0) v) (hcomm : A ≤ commG ρ) (a : A) : lam a = 1 := by
  obtain ⟨Λ, hΛ, hext⟩ := exists_invariant_of_prin E hσ lam hD hv
  have hker : commG ρ ≤ Λ.ker := commOn_le (fun g m _ => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hΛ, mul_inv_cancel])
  have := hker (hcomm a.2)
  rw [MonoidHom.mem_ker, hext a a.2] at this
  exact this

theorem hasEnough_sq (G : Type*) [CommGroup G] (hG : ∀ g : G, g ^ 2 = 1) :
    HasEnoughRootsOfUnity ℤ (Monoid.exponent G) := by
  have h2 : HasEnoughRootsOfUnity ℤ 2 :=
    { prim := ⟨-1, IsPrimitiveRoot.neg_one 0 (by norm_num)⟩
      cyc := rootsOfUnity.isCyclic ℤ 2 }
  exact HasEnoughRootsOfUnity.of_dvd ℤ (Monoid.exponent_dvd_of_forall_pow_eq_one hG)

theorem sq_subgroup (E : ExtBot n ρ A π) : ∀ a : A, a ^ 2 = 1 := fun a =>
  Subtype.ext (by simpa using E.sq (a : M))

theorem eq_bot_of_zeroClass [Finite M] (hn : 5 ≤ n) (E : ExtBot n ρ A π) (hcomm : A ≤ commG ρ)
    (hz : ZeroClass (actL n Mod.ut0)) : A = ⊥ := by
  obtain ⟨σ, hσ⟩ := exists_section E.sq π E.surj
  have := hasEnough_sq A (sq_subgroup E)
  rw [eq_bot_iff]
  intro a ha
  by_contra ha1
  have ha1' : (⟨a, ha⟩ : A) ≠ 1 := fun h => ha1 (by
    have := congrArg Subtype.val h
    simpa using this)
  obtain ⟨lam, hlam⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity A ℤ ha1'
  obtain ⟨D, hD⟩ := exists_D hn E hσ lam
  obtain ⟨v, hv⟩ := hz D (isDer_of_theta hn E hσ lam hD)
  exact hlam (lam_eq_one_of_prin E hσ lam hD hv hcomm ⟨a, ha⟩)

theorem flam_mul (E : ExtBot n ρ A π) {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w)
    (lam lam' : A →* ℤˣ) (g : LG n) :
    flam E hσ (lam * lam') g = flam E hσ lam g * flam E hσ lam' g := by
  refine MonoidHom.ext fun w => ?_
  rfl

theorem units_sq_one (u : ℤˣ) : u * u = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

theorem card_le_two_of_twoClass [Finite M] (hn : 5 ≤ n) (E : ExtBot n ρ A π)
    (hcomm : A ≤ commG ρ) (ht : TwoClass (actL n Mod.ut0) (d0 n Mod.ut0)) :
    Nat.card A ≤ 2 := by
  obtain ⟨σ, hσ⟩ := exists_section E.sq π E.surj
  have := hasEnough_sq A (sq_subgroup E)
  have hd0sq : ∀ g, d0 n Mod.ut0 g * d0 n Mod.ut0 g = 1 := fun g => by
    rw [← pow_two]
    exact V_sq _ _
  have hnp : ∀ lam : A →* ℤˣ, lam ≠ 1 → ∀ D : LG n → WV n,
      (∀ g, Theta n (D g) = flam E hσ lam g) → IsPrin (actL n Mod.ut0) (D * d0 n Mod.ut0) := by
    intro lam hlam D hD
    have hder := isDer_of_theta hn E hσ lam hD
    rcases ht.2.2 D hder with hp | hp
    · exfalso
      obtain ⟨v, hv⟩ := hp
      apply hlam
      refine MonoidHom.ext fun a => ?_
      rw [MonoidHom.one_apply]
      exact lam_eq_one_of_prin E hσ lam hD hv hcomm a
    · exact hp
  have key : ∀ lam lam' : A →* ℤˣ, lam ≠ 1 → lam' ≠ 1 → lam = lam' := by
    intro lam lam' h1 h2
    obtain ⟨D, hD⟩ := exists_D hn E hσ lam
    obtain ⟨D', hD'⟩ := exists_D hn E hσ lam'
    have hp := hnp lam h1 D hD
    have hp' := hnp lam' h2 D' hD'
    have hprod : IsPrin (actL n Mod.ut0) (D * D') := by
      have := hp.mul hp'
      have e : (D * d0 n Mod.ut0) * (D' * d0 n Mod.ut0) = D * D' := by
        funext g
        simp only [Pi.mul_apply]
        have := hd0sq g
        calc D g * d0 n Mod.ut0 g * (D' g * d0 n Mod.ut0 g)
            = D g * D' g * (d0 n Mod.ut0 g * d0 n Mod.ut0 g) := by ac_rfl
          _ = D g * D' g := by rw [this, mul_one]
      rwa [e] at this
    have hDD : ∀ g, Theta n ((D * D') g) = flam E hσ (lam * lam') g := fun g => by
      rw [Pi.mul_apply, map_mul, hD, hD', flam_mul]
    obtain ⟨v, hv⟩ := hprod
    refine MonoidHom.ext fun a => ?_
    have h3 := lam_eq_one_of_prin E hσ (lam * lam') hDD hv hcomm a
    rw [MonoidHom.mul_apply] at h3
    have h4 : lam a * lam a = 1 := units_sq_one _
    have h5 : lam' a = lam a := mul_left_cancel (a := lam a) (h3.trans h4.symm)
    exact h5.symm
  classical
  have hinj : Function.Injective (fun lam : A →* ℤˣ => decide (lam = 1)) := by
    intro lam lam' h
    have h' : lam = 1 ↔ lam' = 1 := decide_eq_decide.1 h
    by_cases h1 : lam = 1
    · rw [h1, (h'.1 h1)]
    · exact key lam lam' h1 (fun h2 => h1 (h'.2 h2))
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity A ℤ] at hcard
  simpa using hcard

theorem theta_pder_apply (g : LG n) (v w : WV n) :
    Theta n (pder (actL n Mod.ut0) v g) w = Theta n v (actL n Mod.ut0 g⁻¹ w) * (Theta n v w)⁻¹ := by
  simp only [pder, map_mul, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply]
  rw [theta_actL, map_inv]

@[expose] noncomputable def unitsTo (c : M) (hsq : c * c = 1) : ℤˣ →* M where
  toFun s := if s = 1 then 1 else c
  map_one' := by simp
  map_mul' s t := by
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl <;>
      simp [hsq]

theorem unitsTo_neg (c : M) (hsq : c * c = 1) : unitsTo c hsq (-1) = c := by
  simp [unitsTo]

theorem unitsTo_one (c : M) (hsq : c * c = 1) : unitsTo c hsq 1 = 1 := by
  simp [unitsTo]

theorem exists_section_adjust [Finite M] (hn : 5 ≤ n) (E : ExtBot n ρ A π) (hcomm : A ≤ commG ρ)
    (ht : TwoClass (actL n Mod.ut0) (d0 n Mod.ut0)) {c : M} (hc : c ∈ A) (hc1 : c ≠ 1) :
    ∃ (σ : WV n →* M) (hσ : ∀ w, π (σ w) = w) (lam : A →* ℤˣ), lam ⟨c, hc⟩ = -1 ∧
      ∀ g, Theta n (d0 n Mod.ut0 g) = flam E hσ lam g := by
  classical
  obtain ⟨σ₀, hσ₀⟩ := exists_section E.sq π E.surj
  have := hasEnough_sq A (sq_subgroup E)
  have hc1' : (⟨c, hc⟩ : A) ≠ 1 := fun h => hc1 (by simpa using congrArg Subtype.val h)
  obtain ⟨lam, hlam⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity A ℤ hc1'
  have hlamc : lam ⟨c, hc⟩ = -1 := by
    rcases Int.units_eq_one_or (lam ⟨c, hc⟩) with h | h
    · exact absurd h hlam
    · exact h
  have hcc : c * c = 1 := by rw [← pow_two]; exact E.sq c
  obtain ⟨D, hD⟩ := exists_D hn E hσ₀ lam
  have hder := isDer_of_theta hn E hσ₀ lam hD
  have hnp : ¬ IsPrin (actL n Mod.ut0) D := by
    rintro ⟨v, hv⟩
    have := lam_eq_one_of_prin E hσ₀ lam hD hv hcomm ⟨c, hc⟩
    rw [hlamc] at this
    exact absurd this (by decide)
  have hp : IsPrin (actL n Mod.ut0) (D * d0 n Mod.ut0) := by
    rcases ht.2.2 D hder with h | h
    · exact absurd h hnp
    · exact h
  obtain ⟨v, hv⟩ := hp
  let ε₁ : ℤˣ →* M := unitsTo c hcc
  let σ : WV n →* M := σ₀ * (ε₁.comp (Theta n v))
  have hε : ∀ s, ε₁ s ∈ A := by
    intro s
    rcases Int.units_eq_one_or s with rfl | rfl
    · rw [map_one]; exact A.one_mem
    · exact (unitsTo_neg c hcc) ▸ hc
  have hσ : ∀ w, π (σ w) = w := by
    intro w
    show π (σ₀ w * ε₁ (Theta n v w)) = w
    rw [map_mul, hσ₀, (E.ker _).2 (hε _), mul_one]
  refine ⟨σ, hσ, lam, hlamc, fun g => ?_⟩
  refine MonoidHom.ext fun w => ?_
  rw [flam_apply E hσ lam g w]
  have e1 : dlt ρ σ g w = dlt ρ σ₀ g w * (ε₁ (Theta n v (actL n Mod.ut0 g⁻¹ w)) *
      (ε₁ (Theta n v w))⁻¹) := by
    unfold dlt
    show ρ g (σ₀ (actL n Mod.ut0 g⁻¹ w) * ε₁ (Theta n v (actL n Mod.ut0 g⁻¹ w))) *
      (σ₀ w * ε₁ (Theta n v w))⁻¹ = _
    rw [map_mul, E.fix g _ (hε _), mul_inv]
    ac_rfl
  have e2 : (⟨dlt ρ σ g w, dlt_mem E hσ g w⟩ : A) =
      ⟨dlt ρ σ₀ g w, dlt_mem E hσ₀ g w⟩ *
        (⟨ε₁ (Theta n v (actL n Mod.ut0 g⁻¹ w)), hε _⟩ * ⟨ε₁ (Theta n v w), hε _⟩⁻¹) :=
    Subtype.ext e1
  have hlε : ∀ s : ℤˣ, lam ⟨ε₁ s, hε s⟩ = s := by
    intro s
    rcases Int.units_eq_one_or s with rfl | rfl
    · have : (⟨ε₁ 1, hε 1⟩ : A) = 1 := Subtype.ext (unitsTo_one c hcc)
      rw [this, map_one]
    · have : (⟨ε₁ (-1), hε (-1)⟩ : A) = ⟨c, hc⟩ := Subtype.ext (unitsTo_neg c hcc)
      rw [this, hlamc]
  rw [e2, map_mul, map_mul, map_inv lam, hlε, hlε, ← flam_apply E hσ₀ lam g w, ← hD g]
  have hDv : D g * pder (actL n Mod.ut0) v g = d0 n Mod.ut0 g := by
    have h1 := congrFun hv g
    simp only [Pi.mul_apply] at h1
    rw [← h1]
    have h2 : D g * D g = 1 := by
      rw [← pow_two]
      exact V_sq _ _
    calc D g * (D g * d0 n Mod.ut0 g) = (D g * D g) * d0 n Mod.ut0 g := by ac_rfl
      _ = d0 n Mod.ut0 g := by rw [h2, one_mul]
  have := congrArg (fun u => Theta n u w) hDv
  simp only [map_mul, MonoidHom.mul_apply, theta_pder_apply] at this
  rw [← this]

theorem proj_rho (E : ExtBot n ρ A π) {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w) (g : LG n)
    (m : M) :
    ρ g m * (σ (π (ρ g m)))⁻¹ =
      (m * (σ (π m))⁻¹) * dlt ρ σ g (actL n Mod.ut0 g (π m)) := by
  have hmem : m * (σ (π m))⁻¹ ∈ A := by
    rw [← E.ker, map_mul, map_inv, hσ, mul_inv_cancel]
  have hfix : ρ g (m * (σ (π m))⁻¹) = m * (σ (π m))⁻¹ := E.fix g _ hmem
  rw [map_mul, map_inv] at hfix
  have hρ : ρ g m = (m * (σ (π m))⁻¹) * ρ g (σ (π m)) := mul_inv_eq_iff_eq_mul.1 hfix
  rw [E.equiv]
  unfold dlt
  rw [actL_inv_apply', hρ]
  ac_rfl

theorem exists_iso_of_dlt {M' : Type*} [CommGroup M'] {ρ' : LG n →* MulAut M'}
    {A' : Subgroup M'} {π' : M' →* WV n} (E : ExtBot n ρ A π) (E' : ExtBot n ρ' A' π')
    {c : M} (hc : c ∈ A) (hc1 : c ≠ 1) (hA : ∀ a ∈ A, a = 1 ∨ a = c)
    {c' : M'} (hc' : c' ∈ A') (hc1' : c' ≠ 1) (hA' : ∀ a ∈ A', a = 1 ∨ a = c')
    {σ : WV n →* M} (hσ : ∀ w, π (σ w) = w) {σ' : WV n →* M'} (hσ' : ∀ w, π' (σ' w) = w)
    (hδ : ∀ g w, dlt ρ σ g w = 1 ↔ dlt ρ' σ' g w = 1) :
    ∃ Φ : M ≃* M', ∀ g m, Φ (ρ g m) = ρ' g (Φ m) := by
  classical
  have hcc : c * c = 1 := by rw [← pow_two]; exact E.sq c
  have hcc' : c' * c' = 1 := by rw [← pow_two]; exact E'.sq c'
  let eps : M → M' := fun a => if a = 1 then 1 else c'
  have heps_mul : ∀ a ∈ A, ∀ b ∈ A, eps (a * b) = eps a * eps b := by
    intro a ha b hb
    rcases hA a ha with rfl | rfl <;> rcases hA b hb with rfl | rfl
    · simp [eps]
    · simp [eps]
    · simp [eps]
    · simp [eps, hcc, hcc', hc1]
  have heps_mem : ∀ a, eps a ∈ A' := by
    intro a
    by_cases ha : a = 1
    · simp [eps, ha, A'.one_mem]
    · simp [eps, ha, hc']
  have heps_inj : ∀ a, eps a = 1 → a = 1 := by
    intro a h
    by_contra ha
    simp [eps, ha] at h
    exact hc1' h
  have hmem : ∀ m : M, m * (σ (π m))⁻¹ ∈ A := fun m => by
    rw [← E.ker, map_mul, map_inv, hσ, mul_inv_cancel]
  let Φ₀ : M →* M' := MonoidHom.mk' (fun m => σ' (π m) * eps (m * (σ (π m))⁻¹)) (fun m m' => by
    have e : m * m' * (σ (π (m * m')))⁻¹ = (m * (σ (π m))⁻¹) * (m' * (σ (π m'))⁻¹) := by
      rw [map_mul, map_mul, mul_inv]
      ac_rfl
    show σ' (π (m * m')) * eps (m * m' * (σ (π (m * m')))⁻¹) = _
    rw [e, heps_mul _ (hmem m) _ (hmem m'), map_mul, map_mul]
    ac_rfl)
  have hΦ₀ : ∀ m, Φ₀ m = σ' (π m) * eps (m * (σ (π m))⁻¹) := fun m => rfl
  have hinj : Function.Injective Φ₀ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : π' (Φ₀ m) = π m := by
      rw [hΦ₀, map_mul, hσ', (E'.ker _).2 (heps_mem _), mul_one]
    rw [hm, map_one] at h1
    have hπm : π m = 1 := h1.symm
    have h2 : Φ₀ m = eps m := by
      rw [hΦ₀, hπm, map_one, one_mul, map_one, inv_one, mul_one]
    rw [h2] at hm
    exact heps_inj m hm
  have hΦσ : ∀ w, Φ₀ (σ w) = σ' w := by
    intro w
    rw [hΦ₀, hσ, mul_inv_cancel, show eps 1 = 1 by simp [eps], mul_one]
  have hsurj : Function.Surjective Φ₀ := by
    intro m'
    have hmem' : m' * (σ' (π' m'))⁻¹ ∈ A' := by
      rw [← E'.ker, map_mul, map_inv, hσ', mul_inv_cancel]
    rcases hA' _ hmem' with h | h
    · refine ⟨σ (π' m'), ?_⟩
      rw [hΦσ]
      exact (mul_inv_eq_one.1 h).symm
    · refine ⟨σ (π' m') * c, ?_⟩
      have hπc : π c = 1 := (E.ker c).2 hc
      have e1 : π (σ (π' m') * c) = π' m' := by rw [map_mul, hσ, hπc, mul_one]
      have e2 : σ (π' m') * c * (σ (π' m'))⁻¹ = c := by
        rw [mul_comm (σ (π' m')) c, mul_assoc, mul_inv_cancel, mul_one]
      rw [hΦ₀, e1, e2, show eps c = c' by simp [eps, hc1]]
      rw [mul_inv_eq_iff_eq_mul] at h
      exact (mul_comm _ _).trans h.symm
  refine ⟨MulEquiv.ofBijective Φ₀ ⟨hinj, hsurj⟩, fun g m => ?_⟩
  show Φ₀ (ρ g m) = ρ' g (Φ₀ m)
  have hdl : eps (dlt ρ σ g (actL n Mod.ut0 g (π m))) =
      dlt ρ' σ' g (actL n Mod.ut0 g (π m)) := by
    by_cases h : dlt ρ σ g (actL n Mod.ut0 g (π m)) = 1
    · rw [h, show eps 1 = 1 by simp [eps], (hδ _ _).1 h]
    · have h' : ¬ dlt ρ' σ' g (actL n Mod.ut0 g (π m)) = 1 := fun h'' => h ((hδ _ _).2 h'')
      rw [show eps (dlt ρ σ g (actL n Mod.ut0 g (π m))) = c' by simp [eps, h]]
      exact ((hA' _ (dlt_mem E' hσ' g _)).resolve_left h').symm
  have hρ' : ρ' g (σ' (π m)) =
      dlt ρ' σ' g (actL n Mod.ut0 g (π m)) * σ' (actL n Mod.ut0 g (π m)) := by
    unfold dlt
    rw [actL_inv_apply']
    simp
  rw [hΦ₀, hΦ₀, proj_rho E hσ g m, E.equiv, heps_mul _ (hmem m) _ (dlt_mem E hσ g _), hdl,
    map_mul, E'.fix g _ (heps_mem _), hρ']
  ac_rfl

end CFSG.Quasithin.B3
