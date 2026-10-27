module

public import CFSG.Quasithin.EmptyFaithful.S152O4Iso
public import CFSG.Quasithin.EmptyFaithful.S152UOm4

public section

namespace CFSG.Quasithin

namespace S152O4

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section General

variable {Δ : Type*} [Group Δ]

theorem exists_eq_zpowers_of_card_two {B : Subgroup Δ} (hB : Nat.card B = 2) :
    ∃ b ∈ B, b ≠ 1 ∧ b * b = 1 ∧ B = Subgroup.zpowers b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite B := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 2 (by rw [hB])
  have hbo : orderOf (b : Δ) = 2 := by rw [Subgroup.orderOf_coe]; exact hb
  refine ⟨b, b.2, ?_, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hbo
    omega
  · have := pow_orderOf_eq_one (b : Δ)
    rw [hbo] at this
    rwa [pow_two] at this
  · refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr b.2) ?_).symm
    rw [Nat.card_zpowers, hbo, hB]

theorem eq_one_or_eq_of_mem_zpowers_two {b x : Δ} (hb : b * b = 1) (hx : x ∈ Subgroup.zpowers b) :
    x = 1 ∨ x = b := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; exact hb
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_ofNat, hb2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_ofNat, hb2, one_zpow, one_mul, zpow_one]

theorem card_sylow_two_eq_four {X Tb : Subgroup Δ} (hTb : IsSylowTwoOf Tb X)
    (hX : Nat.card X = 36) : Nat.card Tb = 4 := by
  obtain ⟨hle, hp, hidx⟩ := hTb
  have hfinX : Finite X := Nat.finite_of_card_ne_zero (by omega)
  have hfin : Finite Tb := Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Nat.card (Tb.subgroupOf X) * (Tb.subgroupOf X).index = Nat.card X :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (Tb.subgroupOf X) = Nat.card Tb :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h2, hX] at h1
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hp
  rw [hk] at h1
  have hk3 : k ≤ 2 := by
    by_contra hcon
    push Not at hcon
    have h8 : 8 ∣ 2 ^ k := by
      have : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 hcon
      simpa using this
    have : 8 ∣ 36 := by rw [← h1]; exact Dvd.dvd.mul_right h8 _
    omega
  interval_cases k
  · simp at h1
    exact absurd (by rw [h1]; decide) hidx
  · simp at h1
    exact absurd (by rw [show (Tb.subgroupOf X).index = 18 by omega]; decide) hidx
  · simpa using hk

theorem exists_klein_elements {T : Subgroup Δ} (hT : Nat.card T = 4)
    (hsq : ∀ x ∈ T, x * x = 1) :
    ∃ s ∈ T, ∃ s' ∈ T, s ≠ 1 ∧ s' ≠ 1 ∧ s ≠ s' ∧ s * s' = s' * s ∧
      ∀ x ∈ T, x = 1 ∨ x = s ∨ x = s' ∨ x = s * s' := by
  have hfin : Finite T := Nat.finite_of_card_ne_zero (by omega)
  have hcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    intro x hx y hy
    have h1 := hsq (x * y) (T.mul_mem hx hy)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
    have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
    have : x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
    rw [mul_inv_rev, hxinv, hyinv] at this
    exact this
  obtain ⟨s, hsT, hs1⟩ : ∃ s ∈ T, s ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : T = ⊥ := Subgroup.eq_bot_iff_forall T |>.mpr hcon
    rw [this, Subgroup.card_bot] at hT
    omega
  have hs2 : orderOf s = 2 := orderOf_eq_prime_iff.mpr ⟨by rw [pow_two]; exact hsq s hsT, hs1⟩
  have hz2 : Nat.card (Subgroup.zpowers s) = 2 := by rw [Nat.card_zpowers, hs2]
  have : Finite (Subgroup.zpowers s) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨s', hs'T, hs'z⟩ : ∃ s' ∈ T, s' ∉ Subgroup.zpowers s := by
    by_contra hcon
    push Not at hcon
    have hle : T ≤ Subgroup.zpowers s := fun x hx => hcon x hx
    have := Subgroup.card_le_of_le hle
    omega
  have hs'1 : s' ≠ 1 := fun h => hs'z (h ▸ Subgroup.one_mem _)
  have hss' : s ≠ s' := fun h => hs'z (h ▸ Subgroup.mem_zpowers s)
  have hmul1 : s * s' ≠ 1 := by
    intro h
    apply hss'
    have : s = s'⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [this, inv_eq_of_mul_eq_one_right (hsq s' hs'T)]
  have hmul2 : s * s' ≠ s := by
    intro h
    exact hs'1 (mul_eq_left.mp h)
  have hmul3 : s * s' ≠ s' := by
    intro h
    exact hs1 (mul_eq_right.mp h)
  refine ⟨s, hsT, s', hs'T, hs1, hs'1, hss', hcomm s hsT s' hs'T, ?_⟩
  classical
  let K : Finset Δ := {1, s, s', s * s'}
  have hKcard : K.card = 4 := by
    simp only [K]
    rw [Finset.card_insert_of_notMem (by simp [hs1.symm, hs'1.symm, hmul1.symm]),
      Finset.card_insert_of_notMem (by simp [hss', hmul2.symm]),
      Finset.card_insert_of_notMem (by simp [hmul3.symm]), Finset.card_singleton]
  have : Fintype T := Fintype.ofFinite T
  have hKsub : K ⊆ (T : Set Δ).toFinset := by
    intro y hy
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at hy
    rw [Set.mem_toFinset]
    rcases hy with rfl | rfl | rfl | rfl
    · exact T.one_mem
    · exact hsT
    · exact hs'T
    · exact T.mul_mem hsT hs'T
  have hTf : (T : Set Δ).toFinset.card = 4 := by
    rw [Set.toFinset_card, ← hT, Nat.card_eq_fintype_card]
    rfl
  have hEq : K = (T : Set Δ).toFinset :=
    Finset.eq_of_subset_of_card_le hKsub (by rw [hTf, hKcard])
  intro x hx
  have hxf : x ∈ (T : Set Δ).toFinset := by
    rw [Set.mem_toFinset]
    exact hx
  rw [← hEq] at hxf
  simpa [K] using hxf

end General

@[expose] def subP : Subgroup Gam where
  carrier := {γ | γ ^ 3 = 1}
  one_mem' := one_pow 3
  mul_mem' := fun {a b} ha hb => mul_pow_three a b ha hb
  inv_mem' := fun {a} ha => by
    show a⁻¹ ^ 3 = 1
    rw [inv_pow, show a ^ 3 = 1 from ha, inv_one]

theorem mem_subP {γ : Gam} : γ ∈ subP ↔ γ ^ 3 = 1 := Iff.rfl

theorem card_subP : Nat.card subP = 9 := by
  rw [show Nat.card subP = Nat.card {γ : Gam // γ ^ 3 = 1} from
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Iff.rfl), Nat.card_eq_fintype_card]
  exact card_pow_three

theorem pow_three_of_odd (γ : Gam) (h : Odd (orderOf γ)) : γ ^ 3 = 1 := by
  have h6 : orderOf γ ∣ 3 * 2 := orderOf_dvd_of_pow_eq_one (pow_six γ)
  have hc : Nat.Coprime (orderOf γ) 2 := Nat.coprime_two_right.mpr h
  exact orderOf_dvd_iff_pow_eq_one.mp (hc.dvd_of_dvd_mul_right h6)

section Facts

variable {V : Type} [CommGroup V]

theorem oTwoUpper_eq_map {X : Subgroup (MulAut V)} (c : V ≃* Vec) (hX : (rhoV c).range = X) :
    oTwoUpper X = subP.map (rhoV c) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxX, hodd⟩
    rw [← hX] at hxX
    obtain ⟨γ, rfl⟩ := hxX
    refine ⟨γ, ?_, rfl⟩
    have : orderOf (rhoV c γ) = orderOf γ := orderOf_injective _ (rhoV_injective c) γ
    exact pow_three_of_odd γ (this ▸ hodd)
  · rintro _ ⟨γ, hγ, rfl⟩
    have hmem : rhoV c γ ∈ X := by rw [← hX]; exact ⟨γ, rfl⟩
    refine mem_oTwoUpper_of_odd hmem ?_
    refine Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one ?_)
    rw [← map_pow, show γ ^ 3 = 1 from hγ, map_one]

theorem card_oTwoUpper_eq {X : Subgroup (MulAut V)} (c : V ≃* Vec) (hX : (rhoV c).range = X) :
    Nat.card (oTwoUpper X) = 9 := by
  rw [oTwoUpper_eq_map c hX, Subgroup.card_map_of_injective (rhoV_injective c), card_subP]

theorem card_eq_36 {X : Subgroup (MulAut V)} (c : V ≃* Vec) (hX : (rhoV c).range = X) :
    Nat.card X = 36 := by
  rw [← hX, ← card_Gam]
  exact (Nat.card_congr (MonoidHom.ofInjective (rhoV_injective c)).toEquiv).symm

theorem oddCoreIn_eq_map [Finite V] {X : Subgroup (MulAut V)} (c : V ≃* Vec) (hX : (rhoV c).range = X) :
    oddCoreIn X = subP.map (rhoV c) := by
  rw [← oTwoUpper_eq_map c hX]
  apply le_antisymm
  · intro x hx
    have hxX : x ∈ X := oddCoreIn_le X hx
    have hodd : Odd (orderOf x) :=
      (odd_card_oddCoreIn X).of_dvd_nat (Subgroup.orderOf_dvd_natCard (oddCoreIn X) hx)
    exact mem_oTwoUpper_of_odd hxX hodd
  · exact S152O.le_oddCoreIn_of_normalizes (oTwoUpper_le X) (le_normalizer_oTwoUpper X)
      (by rw [card_oTwoUpper_eq c hX]; decide)

theorem rhoV_mem {X : Subgroup (MulAut V)} (c : V ≃* Vec) (hX : (rhoV c).range = X) (γ : Gam) :
    rhoV c γ ∈ X := by
  rw [← hX]
  exact ⟨γ, rfl⟩

theorem exists_rhoV_eq {X : Subgroup (MulAut V)} (c : V ≃* Vec) (hX : (rhoV c).range = X)
    {x : MulAut V} (hx : x ∈ X) : ∃ γ : Gam, rhoV c γ = x := by
  rw [← hX] at hx
  exact hx

theorem rhoV_apply_of (c : V ≃* Vec) (γ : Gam) (u : V) : c (rhoV c γ u) = act γ (c u) :=
  rhoV_apply c γ u

theorem om4_iso [Finite V] {X : Subgroup (MulAut V)} (hX : IsOmegaFourPlus X) :
    Nonempty (↥X ≃* DihedralGroup 3 × DihedralGroup 3) := by
  obtain ⟨c, hc⟩ := om4_model hX
  exact ⟨((MonoidHom.ofInjective (rhoV_injective c)).trans (MulEquiv.subgroupCongr hc)).symm⟩

theorem om4_facts [Finite V] {X : Subgroup (MulAut V)} (hX : IsOmegaFourPlus X) : Om4Facts X := by
  obtain ⟨c, hc⟩ := om4_model hX
  refine ⟨card_eq_36 c hc, card_oTwoUpper_eq c hc, ?_⟩
  intro B A hBX hB2 hBE hAE hA hAn
  have hoT := oTwoUpper_eq_map c hc
  obtain ⟨b, hbB, hb1, hb2, hBz⟩ := exists_eq_zpowers_of_card_two hB2
  obtain ⟨β, hβb⟩ := exists_rhoV_eq c hc (hBX hbB)
  subst hβb
  have hβ1 : β ≠ 1 := fun h => hb1 (by rw [h, map_one])
  have hβ2 : β ^ 2 = 1 := by
    apply rhoV_injective c
    rw [map_pow, map_one, pow_two]
    exact hb2
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hA ((Subgroup.eq_bot_iff_forall A).mpr hcon)
  obtain ⟨α, hαP, hαa⟩ : a ∈ subP.map (rhoV c) := hoT ▸ hAE haA
  subst hαa
  have hα3 : α ^ 3 = 1 := hαP
  have hα1 : α ≠ 1 := fun h => ha1 (by rw [h, map_one])
  have hao : orderOf (rhoV c α) = 3 :=
    orderOf_eq_prime (by rw [← map_pow, hα3, map_one]) ha1
  have hz3 : Nat.card (Subgroup.zpowers (rhoV c α)) = 3 := by rw [Nat.card_zpowers, hao]
  have hzA : Subgroup.zpowers (rhoV c α) ≤ A := Subgroup.zpowers_le.mpr haA
  have hA9 : Nat.card A ∣ 3 ^ 2 := by
    have := Subgroup.card_dvd_of_le hAE
    rw [card_oTwoUpper_eq c hc] at this
    simpa using this
  have hA3 : 3 ∣ Nat.card A := by
    have := Subgroup.card_dvd_of_le hzA
    rwa [hz3] at this
  have hAeq : A = Subgroup.zpowers (rhoV c α) := by
    by_contra hne
    obtain ⟨i, hi, hiA⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hA9
    have hAfull : A = oTwoUpper X := by
      interval_cases i
      · rw [hiA] at hA3
        norm_num at hA3
      · exact absurd (Subgroup.eq_of_le_of_card_ge hzA (by rw [hiA, hz3]; rfl)).symm hne
      · exact Subgroup.eq_of_le_of_card_ge hAE (by rw [hiA, card_oTwoUpper_eq c hc]; norm_num)
    apply hAn
    intro g hg a' ha'
    rw [hAfull] at ha' ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper X hg) a').mp ha'
  have hcent : ∀ γ : Gam, γ ^ 3 = 1 → β * γ = γ * β → γ = 1 := by
    intro γ hγ3 hcomm
    have hmem : rhoV c γ ∈ oTwoUpper X := by
      rw [hoT]
      exact ⟨γ, hγ3, rfl⟩
    have := hBE (rhoV c β) hbB hb1 (rhoV c γ) hmem (by rw [← map_mul, ← map_mul, hcomm])
    exact rhoV_injective c (by rw [this, map_one])
  have hnn : ¬ ∀ γ : Gam, γ * α * γ⁻¹ = α ∨ γ * α * γ⁻¹ = α⁻¹ := by
    intro hall
    apply hAn
    intro g hg a' ha'
    obtain ⟨γ, rfl⟩ := exists_rhoV_eq c hc hg
    rw [hAeq] at ha' ⊢
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
    have hconj : rhoV c γ * rhoV c α * (rhoV c γ)⁻¹ ∈ Subgroup.zpowers (rhoV c α) := by
      have : rhoV c (γ * α * γ⁻¹) ∈ Subgroup.zpowers (rhoV c α) := by
        rcases hall γ with h | h
        · rw [h]
          exact Subgroup.mem_zpowers _
        · rw [h, map_inv]
          exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      simpa [map_mul, map_inv] using this
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ hconj k
  obtain ⟨z, hz1, ⟨v, hzv⟩, hstab, τ, hτβ, hτz⟩ := model_stab β α hβ2 hβ1 hα3 hα1 hcent hnn
  have hrho : ∀ (γ : Gam) (u : V), rhoV c γ u = u ↔ act γ (c u) = c u := by
    intro γ u
    constructor
    · intro h
      have := rhoV_apply c γ u
      rw [h] at this
      exact this.symm
    · intro h
      apply c.injective
      rw [rhoV_apply, h]
  refine ⟨c.symm z, ?_, ?_, ?_, rhoV c τ, rhoV_mem c hc τ, ?_, ?_⟩
  · intro h
    apply hz1
    simpa using congrArg c h
  · have hw : c.symm z = rhoV c β (c.symm v) * (c.symm v)⁻¹ := by
      apply c.injective
      rw [map_mul, map_inv, rhoV_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
        hzv]
      rfl
    rw [hw]
    exact Subgroup.subset_closure ⟨rhoV c β, hbB, c.symm v, rfl⟩
  · intro g hg
    obtain ⟨γ, rfl⟩ := exists_rhoV_eq c hc hg
    have hcz : c (c.symm z) = z := c.apply_symm_apply z
    constructor
    · intro h
      have h1 : act γ z = z := by
        have := (hrho γ (c.symm z)).mp h
        rwa [hcz] at this
      obtain ⟨i, j, hγ⟩ := (hstab γ).mp h1
      rw [hγ, map_mul, map_pow, map_pow, hBz, hAeq]
      exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    · intro h
      have hfixα : act α z = z := (hstab α).mpr ⟨1, 0, by simp⟩
      have hfixβ : act β z = z := (hstab β).mpr ⟨0, 1, by simp⟩
      let St : Subgroup (MulAut V) := MulAction.stabilizer (MulAut V) (c.symm z)
      have hαS : rhoV c α ∈ St := by
        show rhoV c α (c.symm z) = c.symm z
        exact (hrho α (c.symm z)).mpr (by rw [hcz]; exact hfixα)
      have hβS : rhoV c β ∈ St := by
        show rhoV c β (c.symm z) = c.symm z
        exact (hrho β (c.symm z)).mpr (by rw [hcz]; exact hfixβ)
      have hAS : A ≤ St := by
        rw [hAeq]
        exact Subgroup.zpowers_le.mpr hαS
      have hBS : B ≤ St := by
        rw [hBz]
        exact Subgroup.zpowers_le.mpr hβS
      exact sup_le hAS hBS h
  · intro b' hb'
    rw [hBz] at hb'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
    have hcom : Commute (rhoV c τ) (rhoV c β) := by
      show rhoV c τ * rhoV c β = rhoV c β * rhoV c τ
      rw [← map_mul, ← map_mul, hτβ]
    exact (hcom.zpow_right k).eq
  · intro h
    apply hτz
    have := (hrho τ (c.symm z)).mp h
    rwa [MulEquiv.apply_symm_apply] at this

theorem om4_Z152 [Finite V] {X Tb B₀ : Subgroup (MulAut V)} (hX : IsOmegaFourPlus X)
    (hTb : IsSylowTwoOf Tb X) (hB₀T : B₀ ≤ Tb) (hB₀2 : Nat.card B₀ = 2)
    (hodd : oddCoreIn X = ⁅oddCoreIn X, B₀⁆) :
    (¬ ∀ t ∈ Tb, ∀ z ∈ commV B₀, t z = z) ∧
      ∀ y ∈ X, y ^ 3 = 1 → (∀ z ∈ fixV Tb, y z = z) → y = 1 := by
  obtain ⟨c, hc⟩ := om4_model hX
  have hTbX : Tb ≤ X := hTb.1
  have hT4 : Nat.card Tb = 4 := card_sylow_two_eq_four hTb (card_eq_36 c hc)
  have hfinT : Finite Tb := Nat.finite_of_card_ne_zero (by omega)
  have hsq : ∀ x ∈ Tb, x * x = 1 := by
    intro x hx
    obtain ⟨γ, hγ⟩ := exists_rhoV_eq c hc (hTbX hx)
    have h4 : x ^ 4 = 1 := by
      have := pow_card_eq_one' (G := Tb) (x := ⟨x, hx⟩)
      rw [hT4] at this
      exact congrArg Subtype.val this
    have hγ4 : γ ^ 4 = 1 := by
      apply rhoV_injective c
      rw [map_pow, map_one, hγ]
      exact h4
    have hγ2 := pow_four_sq γ hγ4
    rw [← hγ, ← map_mul, ← pow_two, hγ2, map_one]
  obtain ⟨s, hsT, s', hs'T, hs1, hs'1, hss', hcomm, hall⟩ := exists_klein_elements hT4 hsq
  obtain ⟨σ, hσ⟩ := exists_rhoV_eq c hc (hTbX hsT)
  obtain ⟨σ', hσ'⟩ := exists_rhoV_eq c hc (hTbX hs'T)
  subst hσ
  subst hσ'
  have hσ1 : σ ≠ 1 := fun h => hs1 (by rw [h, map_one])
  have hσ'1 : σ' ≠ 1 := fun h => hs'1 (by rw [h, map_one])
  have hσσ' : σ ≠ σ' := fun h => hss' (by rw [h])
  have hσ2 : σ ^ 2 = 1 := by
    apply rhoV_injective c
    rw [map_pow, map_one, pow_two]
    exact hsq _ hsT
  have hσ'2 : σ' ^ 2 = 1 := by
    apply rhoV_injective c
    rw [map_pow, map_one, pow_two]
    exact hsq _ hs'T
  have hσcomm : σ * σ' = σ' * σ := by
    apply rhoV_injective c
    rw [map_mul, map_mul]
    exact hcomm
  obtain ⟨b₀, hb₀B, hb₀1, hb₀2, hB₀z⟩ := exists_eq_zpowers_of_card_two hB₀2
  have hb₀T : b₀ ∈ Tb := hB₀T hb₀B
  have hb₀X : b₀ ∈ X := hTbX hb₀T
  obtain ⟨β₀, hβ₀⟩ := exists_rhoV_eq c hc hb₀X
  have hβ₀cases : β₀ = σ ∨ β₀ = σ' ∨ β₀ = σ * σ' := by
    rcases hall b₀ hb₀T with h | h | h | h
    · exact absurd h hb₀1
    · left
      exact rhoV_injective c (hβ₀.trans h)
    · right
      left
      exact rhoV_injective c (hβ₀.trans h)
    · right
      right
      exact rhoV_injective c (by rw [hβ₀, h, map_mul])
  have hE : oddCoreIn X = subP.map (rhoV c) := oddCoreIn_eq_map c hc
  have hinv : ∀ γ : Gam, γ ^ 3 = 1 → β₀ * γ * β₀⁻¹ = γ⁻¹ := by
    have hbE : b₀ ∈ Subgroup.normalizer (oddCoreIn X : Set (MulAut V)) :=
      le_normalizer_oddCoreIn X hb₀X
    have hBb : ∀ x ∈ B₀, x = 1 ∨ x = b₀ := fun x hx => by
      rw [hB₀z] at hx
      exact eq_one_or_eq_of_mem_zpowers_two hb₀2 hx
    have hab : ∀ x ∈ oddCoreIn X, ∀ y ∈ oddCoreIn X, x * y = y * x := by
      intro x hx y hy
      rw [hE] at hx hy
      obtain ⟨ε, hε, rfl⟩ := hx
      obtain ⟨ε', hε', rfl⟩ := hy
      rw [← map_mul, ← map_mul, pow_three_comm ε ε' hε hε']
    have hinvE := S152O.inverts_of_commutator_eq (E := oddCoreIn X) (B := B₀) (b := b₀)
      (by rw [pow_two]; exact hb₀2) hbE hBb hab hodd.symm
    intro γ hγ
    have hmem : rhoV c γ ∈ oddCoreIn X := by
      rw [hE]
      exact ⟨γ, hγ, rfl⟩
    have := hinvE (rhoV c γ) hmem
    apply rhoV_injective c
    rw [map_mul, map_mul, map_inv, map_inv, hβ₀]
    exact this
  refine ⟨?_, ?_⟩
  · intro hall'
    obtain ⟨t, ht, v, hv⟩ := model_Z152_one σ σ' β₀ hσ2 hσ'2 hσ1 hσ'1 hσσ' hσcomm hβ₀cases hinv
    have htT : rhoV c t ∈ Tb := by
      rcases ht with h | h | h | h
      · rw [h, map_one]
        exact Tb.one_mem
      · rw [h]
        exact hsT
      · rw [h]
        exact hs'T
      · rw [h, map_mul]
        exact Tb.mul_mem hsT hs'T
    have hzB : c.symm (comm1 β₀ v) ∈ commV B₀ := by
      have hw : c.symm (comm1 β₀ v) = b₀ (c.symm v) * (c.symm v)⁻¹ := by
        apply c.injective
        rw [map_mul, map_inv, ← hβ₀, rhoV_apply, MulEquiv.apply_symm_apply,
          MulEquiv.apply_symm_apply]
        rfl
      rw [hw]
      exact Subgroup.subset_closure ⟨b₀, hb₀B, c.symm v, rfl⟩
    have h1 := hall' _ htT _ hzB
    apply hv
    have h2 := congrArg c h1
    rw [rhoV_apply, MulEquiv.apply_symm_apply] at h2
    exact h2
  · intro y hyX hy3 hfix
    obtain ⟨z₀, hσz, hσ'z, hα⟩ := model_Z152_two σ σ' hσ2 hσ'2 hσ1 hσ'1 hσσ' hσcomm
    have hrho_fix : ∀ (γ : Gam) (u : V), act γ (c u) = c u → rhoV c γ u = u := fun γ u h => by
      apply c.injective
      rw [rhoV_apply]
      exact h
    have hσfix : rhoV c σ (c.symm z₀) = c.symm z₀ :=
      hrho_fix σ _ (by rw [MulEquiv.apply_symm_apply]; exact hσz)
    have hσ'fix : rhoV c σ' (c.symm z₀) = c.symm z₀ :=
      hrho_fix σ' _ (by rw [MulEquiv.apply_symm_apply]; exact hσ'z)
    have hz₀ : ∀ x ∈ Tb, x (c.symm z₀) = c.symm z₀ := by
      intro x hx
      rcases hall x hx with h | h | h | h
      · rw [h]
        rfl
      · rw [h]
        exact hσfix
      · rw [h]
        exact hσ'fix
      · rw [h, MulAut.mul_apply, hσ'fix]
        exact hσfix
    have hyfix := hfix _ (mem_fixV.mpr hz₀)
    obtain ⟨α, rfl⟩ := exists_rhoV_eq c hc hyX
    have hα3 : α ^ 3 = 1 := by
      apply rhoV_injective c
      rw [map_pow, map_one]
      exact hy3
    have hactα : act α z₀ = z₀ := by
      have h2 := congrArg c hyfix
      rw [rhoV_apply, MulEquiv.apply_symm_apply] at h2
      exact h2
    rw [hα α hα3 hactα, map_one]

end Facts

end S152O4

end CFSG.Quasithin
