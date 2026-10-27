module

public import CFSG.Quasithin.Background.G117A6Norm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Canon

open CFSG.Quasithin CFSG.Quasithin.G11 G117.A6Norm

private theorem natCard_fixedPoints_of_mul_self (σ : Equiv.Perm (Fin 6)) (h2 : σ * σ = 1)
    (h1 : σ ≠ 1) (hs : ¬ σ.IsSwap) :
    (Nat.card (Function.fixedPoints σ) : ℤ) = 1 + ((Equiv.Perm.sign σ : ℤˣ) : ℤ) := by
  have hsq : σ ^ 2 = 1 := by rw [sq]; exact h2
  have hfix : Nat.card (Function.fixedPoints σ) = 6 - σ.support.card := by
    have h := Equiv.Perm.card_fixedPoints σ
    rw [Fintype.card_eq_nat_card, Equiv.Perm.sum_cycleType, Fintype.card_fin] at h
    exact h
  have hsign := Equiv.Perm.sign_of_pow_two_eq_one hsq
  rw [Fintype.card_fin, Fintype.card_eq_nat_card, hfix] at hsign
  have heven := Equiv.Perm.two_dvd_card_support hsq
  have hle : σ.support.card ≤ 6 := by
    simpa using Finset.card_le_univ σ.support
  have h0 : σ.support.card ≠ 0 := by
    rwa [Ne, Finset.card_eq_zero, Equiv.Perm.support_eq_empty_iff]
  have h2' : σ.support.card ≠ 2 := fun h => hs (Equiv.Perm.card_support_eq_two.1 h)
  obtain h | h : σ.support.card = 4 ∨ σ.support.card = 6 := by omega
  · rw [hfix, hsign, h]
    decide
  · rw [hfix, hsign, h]
    decide

theorem exists_swap_of_elemAbelian_order_eight (K : Subgroup (Equiv.Perm (Fin 6)))
    (hcard : Nat.card ↥K = 8) (hexp : ∀ k ∈ K, k * k = 1)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : ∃ k ∈ K, k.IsSwap := by
  classical
  by_contra hno
  push Not at hno
  let f : ↥K →* ℤ := (Units.coeHom ℤ).comp (Equiv.Perm.sign.comp K.subtype)
  have hfK : Fintype.card ↥K = 8 := by rw [Fintype.card_eq_nat_card]; exact hcard
  have hf : ∑ k : ↥K, f k = 0 ∨ ∑ k : ↥K, f k = 8 := by
    by_cases h : f = 1
    · right
      simp [h, hfK]
    · exact Or.inl (sum_hom_units_eq_zero f h)
  have hfix : ∀ k : ↥K, (Nat.card ↥(MulAction.fixedBy (Fin 6) k) : ℤ) =
      1 + f k + if k = 1 then 4 else 0 := by
    intro k
    by_cases hk : k = 1
    · subst hk
      simp [MulAction.fixedBy_one_eq_univ, Nat.card_univ]
    · rw [if_neg hk, add_zero]
      have hk' : (k : Equiv.Perm (Fin 6)) ≠ 1 := fun h => hk (Subtype.ext h)
      exact natCard_fixedPoints_of_mul_self (k : Equiv.Perm (Fin 6)) (hexp k k.2) hk' (hno k k.2)
  have hB := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group (↥K) (Fin 6)
  simp only [Fintype.card_eq_nat_card, hcard] at hB
  have hB' : (∑ k : ↥K, (Nat.card ↥(MulAction.fixedBy (Fin 6) k) : ℤ)) =
      (Nat.card (Quotient (MulAction.orbitRel (↥K) (Fin 6))) : ℤ) * 8 := by
    exact_mod_cast hB
  have hsum : ∑ k : ↥K, ((1 : ℤ) + f k + if k = 1 then 4 else 0) = 12 + ∑ k : ↥K, f k := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp [hfK]
    ring
  rw [Finset.sum_congr rfl fun k _ => hfix k, hsum] at hB'
  omega

section ActsAs

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U]

@[expose] def ActsAs (β : ↥(permCore 6) →ₗ[ZMod 2] U) (r : GLV U) (σ : Equiv.Perm (Fin 6)) :
    Prop :=
  ∀ u : ↥(permCore 6), r (β u) = β ⟨permAct σ u, permAct_mem σ u.2⟩

theorem ActsAs.one (β : ↥(permCore 6) →ₗ[ZMod 2] U) : ActsAs β 1 1 := fun _ => rfl

theorem ActsAs.mul {β : ↥(permCore 6) →ₗ[ZMod 2] U} {r r' : GLV U} {σ τ : Equiv.Perm (Fin 6)}
    (h : ActsAs β r σ) (h' : ActsAs β r' τ) : ActsAs β (r * r') (σ * τ) := fun u =>
  (congrArg r (h' u)).trans (h _)

theorem ActsAs.inv {β : ↥(permCore 6) →ₗ[ZMod 2] U} {r : GLV U} {σ : Equiv.Perm (Fin 6)}
    (h : ActsAs β r σ) : ActsAs β r⁻¹ σ⁻¹ := by
  intro u
  apply r.injective
  rw [h _]
  show r (r.symm (β u)) = _
  rw [LinearEquiv.apply_symm_apply]
  congr 1
  apply Subtype.ext
  funext i
  simp [permAct]

theorem actsAs_perm_unique {β : ↥(permCore 6) →ₗ[ZMod 2] U} (hsurj : Function.Surjective β)
    {r r' : GLV U} {σ : Equiv.Perm (Fin 6)} (h : ActsAs β r σ) (h' : ActsAs β r' σ) :
    r = r' := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, rfl⟩ := hsurj v
  rw [h u, h' u]

private theorem pairVec_apply (a b m : Fin 6) :
    pairVec a b m =
      (Pi.single m 1 : Fin 6 → ZMod 2) a + (Pi.single m 1 : Fin 6 → ZMod 2) b := by
  have h := dot_pairVec (Pi.single m 1) a b
  rwa [single_dotProduct, one_mul] at h

private theorem eq_or_eq_of_pairVec_eq {a b c d : Fin 6} (hab : a ≠ b)
    (h : pairVec a b = pairVec c d) : a = c ∨ a = d := by
  have h' := congrFun h a
  rw [pairVec_apply, pairVec_apply] at h'
  by_contra hne
  push Not at hne
  simp [Pi.single_apply, hab, hab.symm, hne.1, hne.2, hne.1.symm, hne.2.symm] at h'

private theorem exists_ne_four (a b c d : Fin 6) :
    ∃ m : Fin 6, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d := by
  revert a b c d
  decide

theorem ActsAs.unique {β : ↥(permCore 6) →ₗ[ZMod 2] U}
    (hker : ∀ u : ↥(permCore 6), β u = 0 ↔
      (u = 0 ∨ (Even 6 ∧ ∀ i, (u : Fin 6 → ZMod 2) i = 1)))
    {r : GLV U} {σ τ : Equiv.Perm (Fin 6)} (h1 : ActsAs β r σ) (h2 : ActsAs β r τ) : σ = τ := by
  have key : ∀ i j : Fin 6, pairVec (σ i) (σ j) = pairVec (τ i) (τ j) := by
    intro i j
    have e := (h1 ⟨pairVec i j, pairVec_mem i j⟩).symm.trans (h2 ⟨pairVec i j, pairVec_mem i j⟩)
    rw [← sub_eq_zero, ← map_sub, hker] at e
    rcases e with e | ⟨-, e⟩
    · have e' : permAct σ (pairVec i j) - permAct τ (pairVec i j) = 0 := congrArg Subtype.val e
      rw [permAct_pairVec, permAct_pairVec] at e'
      exact sub_eq_zero.1 e'
    · exfalso
      obtain ⟨m, h1m, h2m, h3m, h4m⟩ := exists_ne_four (σ i) (σ j) (τ i) (τ j)
      have e' : permAct σ (pairVec i j) m - permAct τ (pairVec i j) m = 1 := e m
      rw [permAct_pairVec, permAct_pairVec, pairVec_apply, pairVec_apply] at e'
      simp [Pi.single_apply, h1m.symm, h2m.symm, h3m.symm, h4m.symm] at e'
  refine Equiv.ext fun i => ?_
  obtain ⟨j, k, hji, hki, hjk⟩ : ∃ j k : Fin 6, j ≠ i ∧ k ≠ i ∧ j ≠ k := by
    revert i
    decide
  rcases eq_or_eq_of_pairVec_eq (σ.injective.ne hji.symm) (key i j) with h | h
  · exact h
  rcases eq_or_eq_of_pairVec_eq (σ.injective.ne hki.symm) (key i k) with h' | h'
  · exact h'
  exact absurd (τ.injective (h.symm.trans h')) hjk

private def pmap (σ : Equiv.Perm (Fin 6)) : ↥(permCore 6) →ₗ[ZMod 2] ↥(permCore 6) where
  toFun u := ⟨permAct σ u, permAct_mem σ u.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem pmap_apply (σ : Equiv.Perm (Fin 6)) (u : ↥(permCore 6)) :
    (pmap σ u : Fin 6 → ZMod 2) = permAct σ u := rfl

private theorem pmap_pmap_inv (σ : Equiv.Perm (Fin 6)) (u : ↥(permCore 6)) :
    pmap σ (pmap σ⁻¹ u) = u := by
  apply Subtype.ext
  funext i
  simp [pmap_apply, permAct]

private theorem pmap_inv_pmap (σ : Equiv.Perm (Fin 6)) (u : ↥(permCore 6)) :
    pmap σ⁻¹ (pmap σ u) = u := by
  apply Subtype.ext
  funext i
  simp [pmap_apply, permAct]

private theorem β_pmap_eq_zero {β : ↥(permCore 6) →ₗ[ZMod 2] U}
    (hker : ∀ u : ↥(permCore 6), β u = 0 ↔
      (u = 0 ∨ (Even 6 ∧ ∀ i, (u : Fin 6 → ZMod 2) i = 1)))
    (σ : Equiv.Perm (Fin 6)) {z : ↥(permCore 6)} (hz : β z = 0) : β (pmap σ z) = 0 := by
  rcases (hker z).1 hz with rfl | ⟨he, h1⟩
  · rw [map_zero, map_zero]
  · exact (hker _).2 (Or.inr ⟨he, fun i => h1 (σ⁻¹ i)⟩)

private theorem exists_actsAs_perm {β : ↥(permCore 6) →ₗ[ZMod 2] U}
    (hsurj : Function.Surjective β)
    (hker : ∀ u : ↥(permCore 6), β u = 0 ↔
      (u = 0 ∨ (Even 6 ∧ ∀ i, (u : Fin 6 → ZMod 2) i = 1)))
    (σ : Equiv.Perm (Fin 6)) : ∃ r : GLV U, ActsAs β r σ := by
  obtain ⟨s, hs⟩ :=
    LinearMap.exists_rightInverse_of_surjective β (LinearMap.range_eq_top.2 hsurj)
  have hβs : ∀ v, β (s v) = v := fun v => LinearMap.congr_fun hs v
  have hf : ∀ (τ : Equiv.Perm (Fin 6)) (u : ↥(permCore 6)),
      (β ∘ₗ pmap τ ∘ₗ s) (β u) = β (pmap τ u) := by
    intro τ u
    have h0 : β (s (β u) - u) = 0 := by rw [map_sub, hβs, sub_self]
    have h1 := β_pmap_eq_zero hker τ h0
    rw [map_sub, map_sub, sub_eq_zero] at h1
    exact h1
  refine ⟨LinearEquiv.ofLinear (β ∘ₗ pmap σ ∘ₗ s) (β ∘ₗ pmap σ⁻¹ ∘ₗ s) ?_ ?_, fun u => hf σ u⟩
  · apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := hsurj v
    rw [LinearMap.comp_apply, hf, hf, pmap_pmap_inv, LinearMap.id_apply]
  · apply LinearMap.ext
    intro v
    obtain ⟨u, rfl⟩ := hsurj v
    rw [LinearMap.comp_apply, hf, hf, pmap_inv_pmap, LinearMap.id_apply]

private def permImage (β : ↥(permCore 6) →ₗ[ZMod 2] U) : Subgroup (GLV U) where
  carrier := {r | ∃ σ, ActsAs β r σ}
  mul_mem' := by
    rintro a b ⟨σ, ha⟩ ⟨τ, hb⟩
    exact ⟨σ * τ, ha.mul hb⟩
  one_mem' := ⟨1, ActsAs.one β⟩
  inv_mem' := by
    rintro a ⟨σ, ha⟩
    exact ⟨σ⁻¹, ha.inv⟩

variable {H' : Subgroup (GLV U)} (φ : ↥H' ≃* ↥(alternatingGroup (Fin 6)))
  {β : ↥(permCore 6) →ₗ[ZMod 2] U} (hsurj : Function.Surjective β)
  (hker : ∀ u : ↥(permCore 6), β u = 0 ↔ (u = 0 ∨ (Even 6 ∧ ∀ i, (u : Fin 6 → ZMod 2) i = 1)))
  (hequ : ∀ (γ : ↥H') (u u' : ↥(permCore 6)),
    (u' : Fin 6 → ZMod 2) = permAct ((φ γ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6))
      (u : Fin 6 → ZMod 2) → β u' = (γ : GLV U) (β u))

include hequ in
theorem actsAs_phi (γ : ↥H') :
    ActsAs β (γ : GLV U) ((φ γ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) :=
  fun u => (hequ γ u _ rfl).symm

include hequ in
theorem actsAs_even_of_mem {r : GLV U} (hr : r ∈ H') :
    ∃ σ ∈ alternatingGroup (Fin 6), ActsAs β r σ :=
  ⟨_, (φ ⟨r, hr⟩).2, actsAs_phi φ hequ ⟨r, hr⟩⟩

include hsurj hequ in
theorem mem_of_actsAs_even {r : GLV U} {σ : Equiv.Perm (Fin 6)} (h : ActsAs β r σ)
    (hσ : σ ∈ alternatingGroup (Fin 6)) : r ∈ H' := by
  have h1 := actsAs_phi φ hequ (φ.symm ⟨σ, hσ⟩)
  rw [MulEquiv.apply_symm_apply] at h1
  rw [actsAs_perm_unique hsurj h h1]
  exact (φ.symm ⟨σ, hσ⟩).2

include hker hequ in
theorem phi_conj_of_actsAs {r : GLV U} {σ : Equiv.Perm (Fin 6)} (h : ActsAs β r σ)
    (hr : ∀ h ∈ H', r * h * r⁻¹ ∈ H') (g : ↥H') (hg : r * (g : GLV U) * r⁻¹ ∈ H') :
    ((φ ⟨r * g * r⁻¹, hg⟩ : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) =
      σ * ((φ g : ↥(alternatingGroup (Fin 6))) : Equiv.Perm (Fin 6)) * σ⁻¹ :=
  (((h.mul (actsAs_phi φ hequ g)).mul h.inv).unique hker (actsAs_phi φ hequ ⟨_, hg⟩)).symm

include hsurj hequ in
private theorem conj_mem_of_actsAs {p : GLV U} {σ : Equiv.Perm (Fin 6)} (hp : ActsAs β p σ)
    {h : GLV U} (hh : h ∈ H') : p * h * p⁻¹ ∈ H' :=
  mem_of_actsAs_even φ hsurj hequ ((hp.mul (actsAs_phi φ hequ ⟨h, hh⟩)).mul hp.inv)
    (alternatingGroup.normal.conj_mem _ (φ ⟨h, hh⟩).2 σ)

include hsurj hker hequ in
theorem exists_actsAs_of_normalizes [Finite U] (r : GLV U) (hr : ∀ h ∈ H', r * h * r⁻¹ ∈ H') :
    ∃ σ : Equiv.Perm (Fin 6), ActsAs β r σ := by
  classical
  have : Finite (GLV U) :=
    Finite.of_injective (fun e : GLV U => (e : U → U)) DFunLike.coe_injective
  have : Finite ↥H' := Finite.of_equiv _ φ.symm.toEquiv
  choose g hg using exists_actsAs_perm hsurj hker
  have hcard : 720 ≤ Nat.card ↥(permImage β) := by
    have hinj : Function.Injective
        fun σ : Equiv.Perm (Fin 6) => (⟨g σ, σ, hg σ⟩ : ↥(permImage β)) := by
      intro σ τ hστ
      have e : g σ = g τ := congrArg Subtype.val hστ
      have h2 : ActsAs β (g σ) τ := by rw [e]; exact hg τ
      exact (hg σ).unique hker h2
    have h6 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_perm, Nat.card_fin] at h6
    exact h6
  have hPN : permImage β ≤ Subgroup.normalizer H' := by
    rintro p ⟨σ, hσ⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => conj_mem_of_actsAs φ hsurj hequ hσ hh, fun hh => ?_⟩
    have := conj_mem_of_actsAs φ hsurj hequ hσ.inv hh
    simpa [mul_assoc] using this
  have hrN : r ∈ Subgroup.normalizer H' := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hr h, fun hh => ?_⟩
    have hc : Function.Injective fun x : ↥H' => (⟨r * x * r⁻¹, hr x x.2⟩ : ↥H') := by
      intro x y hxy
      apply Subtype.ext
      have := congrArg Subtype.val hxy
      simpa using this
    obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hc ⟨r * h * r⁻¹, hh⟩
    have hx' : r * (x : GLV U) * r⁻¹ = r * h * r⁻¹ := congrArg Subtype.val hx
    have hxh : (x : GLV U) = h := by simpa using hx'
    exact hxh ▸ x.2
  let R := permImage β ⊔ Subgroup.zpowers r
  have hRN : R ≤ Subgroup.normalizer H' := sup_le hPN (Subgroup.zpowers_le.2 hrN)
  have hbound : Nat.card ↥R ≤ 720 := G117.a6NormalizerBound U H' R ⟨φ, β, hsurj, hker, hequ⟩
    fun g hg h hh => (Subgroup.mem_normalizer_iff.1 (hRN hg) h).1 hh
  have heq : permImage β = R := Subgroup.eq_of_le_of_card_ge le_sup_left (hbound.trans hcard)
  have hrR : r ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  rw [← heq] at hrR
  exact hrR

end ActsAs

end CFSG.Quasithin.G11.Canon
