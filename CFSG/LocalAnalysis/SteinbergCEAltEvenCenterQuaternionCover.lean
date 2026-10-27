module

public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedAltSevenCover

public section

namespace CFSG.LocalAnalysis

namespace AltEvenCenter

open Subgroup

theorem eq_one_of_isPerfect {A B : Type*} [Group A] [Group B] [Group.IsPerfect A]
    (hB : ∀ x y : B, x * y = y * x) (f : A →* B) (a : A) : f a = 1 := by
  have h : commutator A ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hB _ _
  rw [Group.IsPerfect.commutator_eq_top] at h
  exact h (mem_top a)

theorem surjective_comp_commutator_subtype {F B : Type*} [Group F] [Group B] [Group.IsPerfect B]
    (p : F →* B) (hp : Function.Surjective p) :
    Function.Surjective (p.comp (commutator F).subtype) := by
  rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype, commutator_def,
    Subgroup.map_commutator, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hp,
    ← commutator_def, Group.IsPerfect.commutator_eq_top]

theorem existsUnique_mulEquiv_of_central_double_covers {n : ℕ} (hn : 5 ≤ n)
    {A E : Type*} [Group A] [Group E] [Finite A] [Finite E] [Group.IsPerfect A]
    [Group.IsPerfect E] {α : A →* alternatingGroup (Fin n)} (hα : Function.Surjective α)
    (hαZ : α.ker ≤ center A) (hα2 : Nat.card α.ker = 2) {π : E →* alternatingGroup (Fin n)}
    (hπ : Function.Surjective π) (hπZ : π.ker ≤ center E) (hπ2 : Nat.card π.ker = 2) :
    ∃! η : A ≃* E, ∀ a, π (η a) = α a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F : Subgroup (A × E) := (α.comp (MonoidHom.fst A E)).eqLocus (π.comp (MonoidHom.snd A E))
  have hmemF : ∀ x : A × E, x ∈ F ↔ α x.1 = π x.2 := fun _ => Iff.rfl
  let ψ : F →* alternatingGroup (Fin n) := (α.comp (MonoidHom.fst A E)).comp F.subtype
  have hψ : Function.Surjective ψ := by
    intro σ
    obtain ⟨a, ha⟩ := hα σ
    obtain ⟨e, he⟩ := hπ σ
    exact ⟨⟨(a, e), by rw [hmemF, ha, he]⟩, ha⟩
  have hKZ : ψ.ker ≤ center F := by
    intro x hx
    have h1 : α (x : A × E).1 = 1 := hx
    have h2 : π (x : A × E).2 = 1 := by rw [← (hmemF x).mp x.2]; exact h1
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact mem_center_iff.mp (hαZ h1) (y : A × E).1
    · exact mem_center_iff.mp (hπZ h2) (y : A × E).2
  have hK2 : IsPGroup 2 ψ.ker := by
    intro x
    refine ⟨1, ?_⟩
    have h1 : α (x : F).1.1 = 1 := x.2
    have h2 : π (x : F).1.2 = 1 := by rw [← (hmemF _).mp (x : F).2]; exact h1
    have ha2 : (x : F).1.1 ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := α.ker) (x := ⟨_, h1⟩)
      rw [hα2] at h
      exact congrArg Subtype.val h
    have he2 : (x : F).1.2 ^ 2 = 1 := by
      have h := pow_card_eq_one' (G := π.ker) (x := ⟨_, h2⟩)
      rw [hπ2] at h
      exact congrArg Subtype.val h
    rw [pow_one]
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext ha2 he2
  have : Group.IsPerfect (alternatingGroup (Fin n)) := Group.IsPerfect.ofSurjective hα
  have : Group.IsPerfect (F ⧸ ψ.ker) :=
    Group.IsPerfect.ofSurjective
      (f := (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.surjective
  obtain ⟨hsup, hFperf, -⟩ := ComponentInitial.central_extension_derived hKZ
  have : Group.IsPerfect (commutator F) := hFperf
  set F' := commutator F with hF'
  let ψ' : F' →* alternatingGroup (Fin n) := ψ.comp F'.subtype
  have hψ' : Function.Surjective ψ' := by
    rw [← MonoidHom.range_eq_top]
    have h1 : ψ'.range = F'.map ψ := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [h1]
    have h2 := congrArg (Subgroup.map ψ) hsup
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hψ] at h2
    exact h2
  have hψ'Z : ψ'.ker ≤ center F' := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp (hKZ hx) y)
  have hψ'2 : IsPGroup 2 ψ'.ker := by
    intro x
    obtain ⟨k, hk⟩ := hK2 ⟨((x : F') : F), x.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hker' : Nat.card ψ'.ker ≤ 2 :=
    ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two hn ψ' hψ' hψ'Z
      hψ'2
  have hcardF' : Nat.card F' ≤ 2 * Nat.card (alternatingGroup (Fin n)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ'.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ').toEquiv] at h1
    rw [h1, mul_comm]
    exact Nat.mul_le_mul_right _ hker'
  have hcardA : Nat.card A = 2 * Nat.card (alternatingGroup (Fin n)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv, hα2] at h1
    rw [h1, mul_comm]
  have hcardE : Nat.card E = 2 * Nat.card (alternatingGroup (Fin n)) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hπ).toEquiv, hπ2] at h1
    rw [h1, mul_comm]
  have hfst : Function.Surjective ((MonoidHom.fst A E).comp F.subtype) := by
    intro a
    obtain ⟨e, he⟩ := hπ (α a)
    exact ⟨⟨(a, e), by rw [hmemF]; exact he.symm⟩, rfl⟩
  have hsnd : Function.Surjective ((MonoidHom.snd A E).comp F.subtype) := by
    intro e
    obtain ⟨a, ha⟩ := hα (π e)
    exact ⟨⟨(a, e), by rw [hmemF]; exact ha⟩, rfl⟩
  have hbA := (surjective_comp_commutator_subtype _ hfst).bijective_of_nat_card_le
    (hcardF'.trans hcardA.ge)
  have hbE := (surjective_comp_commutator_subtype _ hsnd).bijective_of_nat_card_le
    (hcardF'.trans hcardE.ge)
  let eA : F' ≃* A := MulEquiv.ofBijective _ hbA
  let eE : F' ≃* E := MulEquiv.ofBijective _ hbE
  have hη₀ : ∀ a, π ((eA.symm.trans eE) a) = α a := by
    intro a
    have h1 : eA (eA.symm a) = a := eA.apply_symm_apply a
    change π (eE (eA.symm a)) = α a
    conv_rhs => rw [← h1]
    exact ((hmemF _).mp ((eA.symm a : F') : F).2).symm
  refine ⟨eA.symm.trans eE, hη₀, fun η hη => ?_⟩
  set η₀ := eA.symm.trans eE
  have hd : ∀ a, η a * (η₀ a)⁻¹ ∈ center E := fun a => hπZ (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hη a, hη₀ a, mul_inv_cancel])
  let d : A →* center E :=
    { toFun := fun a => ⟨η a * (η₀ a)⁻¹, hd a⟩
      map_one' := by
        apply Subtype.ext
        change η 1 * (η₀ 1)⁻¹ = 1
        rw [map_one, map_one, inv_one, mul_one]
      map_mul' := fun a b => by
        apply Subtype.ext
        change η (a * b) * (η₀ (a * b))⁻¹ = η a * (η₀ a)⁻¹ * (η b * (η₀ b)⁻¹)
        have hc : η b * (η₀ b)⁻¹ * (η₀ a)⁻¹ = (η₀ a)⁻¹ * (η b * (η₀ b)⁻¹) :=
          (mem_center_iff.mp (hd b) (η₀ a)⁻¹).symm
        rw [map_mul, map_mul]
        calc η a * η b * (η₀ a * η₀ b)⁻¹ = η a * (η b * (η₀ b)⁻¹ * (η₀ a)⁻¹) := by group
          _ = η a * ((η₀ a)⁻¹ * (η b * (η₀ b)⁻¹)) := by rw [hc]
          _ = η a * (η₀ a)⁻¹ * (η b * (η₀ b)⁻¹) := by group }
  apply MulEquiv.ext
  intro a
  have h0 : d a = 1 :=
    eq_one_of_isPerfect (fun x y => Subtype.ext (mem_center_iff.mp y.2 x)) d a
  have h1 : η a * (η₀ a)⁻¹ = 1 := congrArg Subtype.val h0
  exact mul_inv_eq_one.mp h1

section Restriction

open Equiv Equiv.Perm

variable {n : ℕ}

@[expose] def fixAbove (n : ℕ) : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {h | ∀ i : Fin 7, n ≤ i.val → (h : Perm (Fin 7)) i = i}
  mul_mem' {a b} ha hb i hi := by
    change (a : Perm (Fin 7)) ((b : Perm (Fin 7)) i) = i
    rw [hb i hi, ha i hi]
  one_mem' _ _ := rfl
  inv_mem' {a} ha i hi := by
    change (a : Perm (Fin 7))⁻¹ i = i
    rw [Perm.inv_eq_iff_eq]
    exact (ha i hi).symm

theorem mem_fixAbove {h : alternatingGroup (Fin 7)} :
    h ∈ fixAbove n ↔ ∀ i : Fin 7, n ≤ i.val → (h : Perm (Fin 7)) i = i :=
  Iff.rfl

@[expose] def altExtendLow (hn : n ≤ 7) : alternatingGroup (Fin n) →* alternatingGroup (Fin 7) :=
  ((extendDomainHom (Fin.castLEquiv hn)).comp (alternatingGroup (Fin n)).subtype).codRestrict
    (alternatingGroup (Fin 7)) fun σ => mem_alternatingGroup.mpr
      ((sign_extendDomain _ (Fin.castLEquiv hn)).trans (mem_alternatingGroup.mp σ.2))

theorem altExtendLow_injective (hn : n ≤ 7) : Function.Injective (altExtendLow hn) :=
  fun _ _ h => Subtype.ext (extendDomainHom_injective (Fin.castLEquiv hn) (congrArg Subtype.val h))

theorem altExtendLow_apply_low (hn : n ≤ 7) (σ : alternatingGroup (Fin n)) (i : Fin n) :
    (altExtendLow hn σ : Perm (Fin 7)) (Fin.castLE hn i) =
      Fin.castLE hn ((σ : Perm (Fin n)) i) :=
  extendDomain_apply_image (σ : Perm (Fin n)) (Fin.castLEquiv hn) i

theorem altExtendLow_apply_high (hn : n ≤ 7) (σ : alternatingGroup (Fin n)) {x : Fin 7}
    (hx : n ≤ x.val) : (altExtendLow hn σ : Perm (Fin 7)) x = x :=
  extendDomain_apply_not_subtype _ (Fin.castLEquiv hn) (by omega)

theorem lt_apply_iff_of_mem_fixAbove {h : alternatingGroup (Fin 7)} (hh : h ∈ fixAbove n)
    (x : Fin 7) : ((h : Perm (Fin 7)) x).val < n ↔ x.val < n := by
  constructor
  · intro hx
    by_contra hlt
    rw [not_lt] at hlt
    rw [hh x hlt] at hx
    omega
  · intro hx
    by_contra hlt
    rw [not_lt] at hlt
    have := hh _ hlt
    rw [(h : Perm (Fin 7)).injective this] at hlt
    omega

theorem range_altExtendLow (hn : n ≤ 7) : (altExtendLow hn).range = fixAbove n := by
  ext h
  constructor
  · rintro ⟨σ, rfl⟩ i hi
    exact altExtendLow_apply_high hn σ hi
  · intro hh
    set f : Perm (Fin 7) := (h : Perm (Fin 7))
    let τ : Perm {x : Fin 7 // x.val < n} := f.subtypePerm (lt_apply_iff_of_mem_fixAbove hh)
    let σ : Perm (Fin n) := ((Fin.castLEquiv hn).permCongr).symm τ
    have hσ : extendDomainHom (Fin.castLEquiv hn) σ = f := by
      refine Equiv.ext fun x => ?_
      by_cases hx : x.val < n
      · have hx' : x = (Fin.castLEquiv hn ((Fin.castLEquiv hn).symm ⟨x, hx⟩) : Fin 7) := by
          rw [Equiv.apply_symm_apply]
        rw [hx']
        change (σ.extendDomain (Fin.castLEquiv hn)) _ = _
        rw [extendDomain_apply_image]
        simp [σ, τ, Equiv.permCongr_apply]
      · rw [not_lt] at hx
        change (σ.extendDomain (Fin.castLEquiv hn)) x = _
        rw [extendDomain_apply_not_subtype _ _ (by omega), hh x hx]
    have hσA : σ ∈ alternatingGroup (Fin n) := by
      rw [mem_alternatingGroup, ← sign_extendDomain σ (Fin.castLEquiv hn)]
      change sign (extendDomainHom (Fin.castLEquiv hn) σ) = 1
      rw [hσ]
      exact mem_alternatingGroup.mp h.2
    exact ⟨⟨σ, hσA⟩, Subtype.ext hσ⟩

@[expose] noncomputable def restrictLow (hn : n ≤ 7) : fixAbove n ≃* alternatingGroup (Fin n) :=
  ((MonoidHom.ofInjective (altExtendLow_injective hn)).trans
    (MulEquiv.subgroupCongr (range_altExtendLow hn))).symm

theorem altExtendLow_restrictLow (hn : n ≤ 7) (h : fixAbove n) :
    altExtendLow hn (restrictLow hn h) = h := by
  have := (MonoidHom.ofInjective (altExtendLow_injective hn)).apply_symm_apply
    ((MulEquiv.subgroupCongr (range_altExtendLow hn)).symm h)
  exact congrArg Subtype.val this

theorem restrictLow_apply (hn : n ≤ 7) (h : fixAbove n) (i : Fin n) :
    (((restrictLow hn h : Perm (Fin n)) i : Fin n) : ℕ) =
      (((h : Perm (Fin 7)) (Fin.castLE hn i) : Fin 7) : ℕ) := by
  have e := congrArg (fun g : alternatingGroup (Fin 7) => (g : Perm (Fin 7)) (Fin.castLE hn i))
    (altExtendLow_restrictLow hn h)
  simp only [altExtendLow_apply_low] at e
  rw [← e]
  rfl

theorem restrictLow_altExtendLow (hn : n ≤ 7) (σ : alternatingGroup (Fin n)) :
    restrictLow hn ⟨altExtendLow hn σ, range_altExtendLow hn ▸ ⟨σ, rfl⟩⟩ = σ := by
  apply altExtendLow_injective hn
  rw [altExtendLow_restrictLow]

end Restriction

section OddCore

variable {Q : Type*} [Group Q] [Finite Q]

theorem mem_pPrimeCore_iff (hQ : CFSG.IsQuasisimple Q) (hZ : Even (Nat.card (center Q)))
    (x : Q) : x ∈ CFSG.pPrimeCore 2 Q ↔ x ∈ center Q ∧ Odd (orderOf x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOodd : Odd (Nat.card (CFSG.pPrimeCore 2 Q)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hOZ : CFSG.pPrimeCore 2 Q ≤ center Q := by
    rcases ComponentInitial.quasisimple_normal_subgroups hQ CFSG.pPrimeCore_normal with h | h
    · exfalso
      rw [h, card_top] at hOodd
      have h2 : 2 ∣ Nat.card Q := (even_iff_two_dvd.mp hZ).trans (card_subgroup_dvd_card _)
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h2)
    · exact h
  constructor
  · intro hx
    exact ⟨hOZ hx, hOodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)⟩
  · rintro ⟨hxZ, hxodd⟩
    have hle : zpowers x ≤ center Q := (zpowers_le).mpr hxZ
    have hcop : Nat.Coprime 2 (Nat.card (zpowers x)) := by
      rw [Nat.card_zpowers]
      exact Nat.coprime_two_left.mpr hxodd
    have hO : zpowers x ≤ CFSG.pPrimeCore 2 Q :=
      le_sSup (s := {K : Subgroup Q | K.Normal ∧ Nat.Coprime 2 (Nat.card K)})
        ⟨Subgroup.normal_of_le_center hle, hcop⟩
    exact hO (mem_zpowers x)

end OddCore

section Cover

open Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedAltSeven

variable {n : ℕ}

@[expose] noncomputable def altCoverE
    (n : ℕ) : Subgroup altSevenE :=
  (fixAbove n).comap altSevenPi

@[expose] noncomputable def altCoverPi
    (hn : n ≤ 7) : altCoverE n →* alternatingGroup (Fin n) :=
  (restrictLow hn).toMonoidHom.comp (altSevenPi.subgroupComap (fixAbove n))

theorem altCoverPi_apply
    (hn : n ≤ 7) (e : altCoverE n) (i : Fin n) :
    (((altCoverPi hn e : Perm (Fin n)) i : Fin n) : ℕ) =
      (((altSevenPi (e : altSevenE) : Perm (Fin 7)) (Fin.castLE hn i) : Fin 7) : ℕ) :=
  restrictLow_apply hn _ i

theorem altSevenPi_altSevenZ
    : altSevenPi altSevenZ = 1 := by
  rw [← MonoidHom.mem_ker, alternating_seven_cover_quasisimple_quaternion.2.1]
  exact mem_zpowers _

theorem altSevenZ_mem_altCoverE
    : altSevenZ ∈ altCoverE n := by
  change altSevenPi altSevenZ ∈ fixAbove n
  rw [altSevenPi_altSevenZ]
  exact one_mem _

@[expose] noncomputable def altCoverZ
    (n : ℕ) : altCoverE n :=
  ⟨altSevenZ, altSevenZ_mem_altCoverE⟩

theorem orderOf_altCoverZ
    : orderOf (altCoverZ n) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact alternating_seven_cover_quasisimple_quaternion.2.2.1

theorem altCoverZ_mem_center
    : altCoverZ n ∈ center (altCoverE n) :=
  mem_center_iff.2 fun g => Subtype.ext (mem_center_iff.1 altSevenZ_mem_center g)

theorem eq_altCoverZ_of_orderOf_eq_two
    {y : altCoverE n} (hy : orderOf y = 2) :
    y = altCoverZ n :=
  Subtype.ext (alternating_seven_cover_quasisimple_quaternion.2.2.2.2.2.2.2.1 (y : altSevenE)
    (by rw [Subgroup.orderOf_coe]; exact hy))

theorem altCoverPi_surjective
    (hn : n ≤ 7) : Function.Surjective (altCoverPi hn) := by
  intro σ
  obtain ⟨g, hg⟩ := alternating_seven_cover_quasisimple_quaternion.1 (altExtendLow hn σ)
  have hgE : g ∈ altCoverE n := by
    change altSevenPi g ∈ fixAbove n
    rw [hg, ← range_altExtendLow hn]
    exact ⟨σ, rfl⟩
  refine ⟨⟨g, hgE⟩, ?_⟩
  change restrictLow hn ⟨altSevenPi g, hgE⟩ = σ
  have h1 : (⟨altSevenPi g, hgE⟩ : fixAbove n) =
      ⟨altExtendLow hn σ, range_altExtendLow hn ▸ ⟨σ, rfl⟩⟩ := Subtype.ext hg
  rw [h1, restrictLow_altExtendLow]

theorem altCoverPi_ker
    (hn : n ≤ 7) : (altCoverPi hn).ker = zpowers (altCoverZ n) := by
  ext e
  rw [MonoidHom.mem_ker, mem_zpowers_of_orderOf_eq_two orderOf_altCoverZ]
  change restrictLow hn ⟨altSevenPi e, e.2⟩ = 1 ↔ _
  rw [MulEquiv.map_eq_one_iff]
  have h1 : (⟨altSevenPi e, e.2⟩ : fixAbove n) = 1 ↔ (e : altSevenE) ∈ altSevenPi.ker := by
    rw [MonoidHom.mem_ker, ← Subtype.val_inj]
    rfl
  rw [h1, alternating_seven_cover_quasisimple_quaternion.2.1,
    mem_zpowers_of_orderOf_eq_two alternating_seven_cover_quasisimple_quaternion.2.2.1]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem exists_two_involutions (h4 : 4 ≤ n) :
    ∃ τ₁ τ₂ : alternatingGroup (Fin n), orderOf τ₁ = 2 ∧ orderOf τ₂ = 2 ∧ τ₁ ≠ τ₂ := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  let d : Fin n := ⟨3, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have had : a ≠ d := by simp [a, d, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  have hbd : b ≠ d := by simp [b, d, Fin.ext_iff]
  have hcd : c ≠ d := by simp [c, d, Fin.ext_iff]
  have hmem : ∀ x y z w : Fin n, x ≠ y → z ≠ w →
      swap x y * swap z w ∈ alternatingGroup (Fin n) := fun x y z w hxy hzw => by
    rw [mem_alternatingGroup, map_mul, sign_swap hxy, sign_swap hzw]
    rfl
  have hord : ∀ (x y z w : Fin n) (hxy : x ≠ y) (hzw : z ≠ w), x ≠ z → x ≠ w → y ≠ z → y ≠ w →
      orderOf (⟨swap x y * swap z w, hmem x y z w hxy hzw⟩ : alternatingGroup (Fin n)) = 2 := by
    intro x y z w hxy hzw hxz hxw hyz hyw
    apply orderOf_eq_prime
    · apply Subtype.ext
      change (swap x y * swap z w) ^ 2 = 1
      have hcomm : Commute (swap x y) (swap z w) :=
        (Equiv.Perm.disjoint_iff_disjoint_support.mpr (by
          rw [support_swap hxy, support_swap hzw]
          simp [Finset.disjoint_iff_ne, hxz, hxw, hyz, hyw])).commute
      rw [hcomm.mul_pow, sq, sq, swap_mul_self, swap_mul_self, one_mul]
    · intro h
      have := congrArg (fun σ : alternatingGroup (Fin n) => (σ : Perm (Fin n)) x) h
      simp only [OneMemClass.coe_one, Perm.one_apply] at this
      change (swap x y * swap z w) x = x at this
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hxz hxw, swap_apply_left] at this
      exact hxy this.symm
  refine ⟨⟨_, hmem a b c d hab hcd⟩, ⟨_, hmem a c b d hac hbd⟩,
    hord a b c d hab hcd hac had hbc hbd, hord a c b d hac hbd hab had hbc.symm hcd, ?_⟩
  intro h
  have := congrArg (fun σ : alternatingGroup (Fin n) => (σ : Perm (Fin n)) a) h
  change (swap a b * swap c d) a = (swap a c * swap b d) a at this
  rw [Perm.mul_apply, Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left,
    swap_apply_of_ne_of_ne hab had, swap_apply_left] at this
  exact hbc this

theorem false_of_bijective_of_unique_involution {C : Type*} [Group C] (h4 : 4 ≤ n)
    (ψ : C →* alternatingGroup (Fin n)) (hinj : Function.Injective ψ)
    (hsurj : Function.Surjective ψ)
    (huniq : ∀ c₁ c₂ : C, orderOf c₁ = 2 → orderOf c₂ = 2 → c₁ = c₂) : False := by
  obtain ⟨τ₁, τ₂, h1, h2, h12⟩ := exists_two_involutions h4
  obtain ⟨c₁, rfl⟩ := hsurj τ₁
  obtain ⟨c₂, rfl⟩ := hsurj τ₂
  rw [orderOf_injective ψ hinj] at h1 h2
  exact h12 (by rw [huniq c₁ c₂ h1 h2])

theorem altCoverE_isPerfect
    (hn : n ≤ 7) (h5 : 5 ≤ n) : Group.IsPerfect (altCoverE n) := by
  have hZ : zpowers (altCoverZ n) ≤ center (altCoverE n) :=
    (zpowers_le).mpr altCoverZ_mem_center
  have hZn : (zpowers (altCoverZ n)).Normal := Subgroup.normal_of_le_center hZ
  have hker := altCoverPi_ker hn
  let e : altCoverE n ⧸ zpowers (altCoverZ n) ≃* alternatingGroup (Fin n) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (altCoverPi_surjective hn))
  have : Group.IsPerfect (alternatingGroup (Fin n)) :=
    ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_fin]; omega)⟩
  have : Group.IsPerfect (altCoverE n ⧸ zpowers (altCoverZ n)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hsup := (ComponentInitial.central_extension_derived hZ).1
  have hzc : altCoverZ n ∈ commutator (altCoverE n) := by
    by_contra hz
    have hinj : Function.Injective
        ((altCoverPi hn).comp (commutator (altCoverE n)).subtype) := by
      rw [injective_iff_map_eq_one]
      intro c hc
      have hc' : (c : altCoverE n) ∈ (altCoverPi hn).ker :=
        MonoidHom.mem_ker.mpr ((MonoidHom.comp_apply _ _ _).symm.trans hc)
      rw [hker, mem_zpowers_of_orderOf_eq_two orderOf_altCoverZ] at hc'
      rcases hc' with h | h
      · exact Subtype.ext h
      · exact absurd (h ▸ c.2) hz
    have hsurj : Function.Surjective
        ((altCoverPi hn).comp (commutator (altCoverE n)).subtype) := by
      intro σ
      refine Exists.elim (altCoverPi_surjective hn σ) fun x hx => ?_
      have hxs : x ∈ commutator (altCoverE n) ⊔ zpowers (altCoverZ n) := by
        rw [hsup]
        exact mem_top x
      refine Exists.elim ((Subgroup.mem_sup_of_normal_right (ht := hZn)).mp hxs)
        fun c hc => Exists.elim hc.2 fun w hw => ?_
      refine ⟨⟨c, hc.1⟩, ?_⟩
      have hwk : w ∈ (altCoverPi hn).ker := hker ▸ hw.1
      have h1 : altCoverPi hn c = σ := by
        rw [← hx, ← hw.2, map_mul, MonoidHom.mem_ker.mp hwk, mul_one]
      exact (MonoidHom.comp_apply _ _ _).trans h1
    refine false_of_bijective_of_unique_involution (by omega) _ hinj hsurj
      fun c₁ c₂ h1 h2 => Subtype.ext ?_
    rw [eq_altCoverZ_of_orderOf_eq_two (y := (c₁ : altCoverE n))
        (by rw [Subgroup.orderOf_coe]; exact h1),
      eq_altCoverZ_of_orderOf_eq_two (y := (c₂ : altCoverE n))
        (by rw [Subgroup.orderOf_coe]; exact h2)]
  refine ⟨?_⟩
  rw [eq_top_iff, ← hsup]
  exact sup_le le_rfl ((zpowers_le).mpr hzc)

end Cover

theorem factorization_two_eq {m u a : ℕ} (hm : Odd m) (hu : Odd u) :
    (m * (2 ^ a * u)).factorization 2 = a := by
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hu0 : u ≠ 0 := hu.pos.ne'
  have hm2 : ¬ 2 ∣ m := fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)
  have hu2 : ¬ 2 ∣ u := fun h => (Nat.not_even_iff_odd.mpr hu) (even_iff_two_dvd.mpr h)
  rw [Nat.factorization_mul hm0 (by positivity), Nat.factorization_mul (by positivity) hu0,
    Finsupp.add_apply, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hm2,
    Nat.factorization_eq_zero_of_not_dvd hu2, Nat.factorization_pow, Finsupp.smul_apply,
    Nat.prime_two.factorization_self, smul_eq_mul, mul_one, zero_add, add_zero]

theorem structure_of_double_cover {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7) {Q E : Type*} [Group Q]
    [Finite Q] [Group E] [Finite E] [Group.IsPerfect E] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Even (Nat.card (center Q))) (θ : Q ⧸ center Q ≃* alternatingGroup (Fin n))
    {π : E →* alternatingGroup (Fin n)} (hπ : Function.Surjective π) {z₀ : E}
    (hz₀ : orderOf z₀ = 2) (hz₀Z : z₀ ∈ center E) (hπker : π.ker = zpowers z₀)
    (huniqE : ∀ y : E, orderOf y = 2 → y = z₀) :
    (∀ x : Q, x ∈ CFSG.pPrimeCore 2 Q ↔ x ∈ center Q ∧ Odd (orderOf x)) ∧
    ∃ z : Q, orderOf z = 2 ∧ (∀ y : Q, orderOf y = 2 → y = z) ∧ z ∈ center Q ∧
      CFSG.pPrimeCore 2 Q ⊔ zpowers z = center Q ∧ CFSG.pPrimeCore 2 Q ⊓ zpowers z = ⊥ ∧
      (∃! η : Q ⧸ CFSG.pPrimeCore 2 Q ≃* E,
        ∀ q : Q, π (η (q : Q ⧸ CFSG.pPrimeCore 2 Q)) = θ (q : Q ⧸ center Q)) ∧
      (∀ η : Q ⧸ CFSG.pPrimeCore 2 Q ≃* E, η (z : Q ⧸ CFSG.pPrimeCore 2 Q) = z₀ ∧
        ∀ q : Q, η (q : Q ⧸ CFSG.pPrimeCore 2 Q) = 1 ↔ q ∈ CFSG.pPrimeCore 2 Q) ∧
      ∀ S : Sylow 2 Q, (n = 5 → Nonempty (S ≃* QuaternionGroup 2)) ∧
        (6 ≤ n → Nonempty (S ≃* QuaternionGroup 4)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pPrimeCore 2 Q with hOdef
  have hOiff := mem_pPrimeCore_iff hQ hZ
  have hOZ : O ≤ center Q := fun x hx => ((hOiff x).mp hx).1
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hnot2 : ¬ Odd 2 := by decide
  obtain ⟨hAq, hAcomap, -⟩ := ComponentInitial.quasisimple_central_quotient hQ hOZ
  have : Group.IsPerfect (Q ⧸ O) := hAq.1
  let α : Q ⧸ O →* alternatingGroup (Fin n) :=
    θ.toMonoidHom.comp (QuotientGroup.map O (center Q) (MonoidHom.id Q) fun x hx => hOZ hx)
  have hαmk : ∀ q : Q, α q = θ q := fun _ => rfl
  have hα : Function.Surjective α := by
    intro σ
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (θ.symm σ)
    exact ⟨q, by rw [hαmk, hq, MulEquiv.apply_symm_apply]⟩
  have hαker : α.ker = center (Q ⧸ O) := by
    ext a
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective a
    rw [MonoidHom.mem_ker, hαmk, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, ← hAcomap,
      Subgroup.mem_comap]
    exact Iff.rfl
  have hA2 : IsPGroup 2 α.ker := by
    rw [hαker]
    rintro ⟨a, ha⟩
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective a
    have hq : q ∈ center Q := by rw [← hAcomap]; exact ha
    obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos q).ne'
    have hqk : q ^ 2 ^ k ∈ O := by
      rw [hOiff]
      refine ⟨Subgroup.pow_mem _ hq _, ?_⟩
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨r, hkr⟩, hkr,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
      exact hr
    refine ⟨k, Subtype.ext ?_⟩
    change ((q : Q ⧸ O)) ^ 2 ^ k = 1
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hqk
  have hAker2 : Nat.card α.ker ≤ 2 :=
    ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two h5 α hα
      hαker.le hA2
  have hAker1 : Nat.card α.ker ≠ 1 := by
    intro h1
    rw [Subgroup.card_eq_one, hαker] at h1
    have h2 : center Q = O := by
      rw [← hAcomap, h1, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rw [h2] at hZ
    exact (Nat.not_even_iff_odd.mpr hOodd) hZ
  have hα2 : Nat.card α.ker = 2 := by
    have := Nat.card_pos (α := α.ker)
    omega
  have hπZ : π.ker ≤ center E := by
    rw [hπker]
    exact (zpowers_le).mpr hz₀Z
  have hπ2 : Nat.card π.ker = 2 := by
    rw [hπker, Nat.card_zpowers, hz₀]
  obtain ⟨η, hη, huniq⟩ :=
    existsUnique_mulEquiv_of_central_double_covers h5 hα hαker.le hα2 hπ hπZ hπ2
  obtain ⟨zc, hzc⟩ := exists_prime_orderOf_dvd_card' (G := center Q) 2 (even_iff_two_dvd.mp hZ)
  set z : Q := (zc : Q) with hzdef
  have hz2 : orderOf z = 2 := by rw [hzdef, Subgroup.orderOf_coe, hzc]
  have hzZ : z ∈ center Q := zc.2
  have hinv2 : ∀ y : Q, orderOf y = 2 → orderOf (y : Q ⧸ O) = 2 := by
    intro y hy
    have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, hy2, QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff]
      intro h
      have := ((hOiff y).mp h).2
      rw [hy] at this
      exact hnot2 this
  have hηz : ∀ η' : Q ⧸ O ≃* E, η' z = z₀ := fun η' =>
    huniqE _ (by rw [MulEquiv.orderOf_eq]; exact hinv2 z hz2)
  have huniqinv : ∀ y : Q, orderOf y = 2 → y = z := by
    intro y hy
    have h1 : η y = η z :=
      (huniqE _ (by rw [MulEquiv.orderOf_eq]; exact hinv2 y hy)).trans
        (hηz η).symm
    have h3 : y⁻¹ * z ∈ O := QuotientGroup.eq.mp (η.injective h1)
    have hc : Commute y⁻¹ z := mem_center_iff.mp hzZ y⁻¹
    have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
    have hz2' : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
    have h4 : (y⁻¹ * z) ^ 2 = 1 := by rw [hc.mul_pow, inv_pow, hy2, hz2', inv_one, one_mul]
    have h6 := Nat.eq_one_of_dvd_coprimes CFSG.pPrimeCore_coprime_card
      (orderOf_dvd_of_pow_eq_one h4) (Subgroup.orderOf_dvd_natCard O h3)
    exact inv_mul_eq_one.mp (orderOf_eq_one_iff.mp h6)
  have hzA : (z : Q ⧸ O) ∈ center (Q ⧸ O) := by
    have h := hzZ
    rw [← hAcomap] at h
    exact h
  have hcenA : zpowers (z : Q ⧸ O) = center (Q ⧸ O) := by
    apply Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hzA)
    rw [Nat.card_zpowers, hinv2 z hz2, ← hαker, hα2]
  have hsup : O ⊔ zpowers z = center Q := by
    rw [← hAcomap, ← hcenA,
      show zpowers (z : Q ⧸ O) = (zpowers z).map (QuotientGroup.mk' O) from
        (MonoidHom.map_zpowers (QuotientGroup.mk' O) z).symm,
      Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  have hinf : O ⊓ zpowers z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxO, hxz⟩
    rw [Subgroup.mem_bot]
    have h1 : orderOf x ∣ 2 := hz2 ▸ orderOf_dvd_of_mem_zpowers hxz
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes CFSG.pPrimeCore_coprime_card h1
      (Subgroup.orderOf_dvd_natCard O hxO))
  have hker : ∀ (η' : Q ⧸ O ≃* E) (q : Q), η' (q : Q ⧸ O) = 1 ↔ q ∈ O := by
    intro η' q
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hrank : CFSG.pRank 2 Q ≤ 1 :=
    CFSG.ComponentClassification.UnbalancedAltSeven.pRank_le_one_of_unique hz2 huniqinv
  have hQeven : Even (Nat.card Q) :=
    even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hZ).trans (card_subgroup_dvd_card _))
  have : Group.IsPerfect Q := hQ.1
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcardA : Nat.card (Q ⧸ O) = n.factorial := by
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv, hα2] at h3
    rw [h3, mul_comm, two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  have hcardQ : Nat.card Q = Nat.card O * n.factorial := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O, hcardA, mul_comm]
  have hsyl : ∀ S : Sylow 2 Q, ∃ k, Nat.card S = 2 ^ k ∧
      Nonempty (S ≃* QuaternionGroup (2 ^ (k - 2))) := by
    intro S
    obtain ⟨k, hk3, ⟨e⟩⟩ := ComponentInitial.perfect_rank_one_Sylow_quaternion hQeven hrank S
    have : NeZero (2 ^ (k - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
    refine ⟨k, ?_, ⟨e⟩⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card,
      show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, Nat.add_sub_cancel' (by omega)]
  refine ⟨hOiff, z, hz2, huniqinv, hzZ, hsup, hinf,
    ⟨η, fun q => (hη q).trans (hαmk q), fun η' hη' => huniq η' fun a => by
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective a
      exact (hη' q).trans (hαmk q).symm⟩,
    fun η' => ⟨hηz η', hker η'⟩, fun S => ⟨fun hn5 => ?_, fun hn6 => ?_⟩⟩
  · obtain ⟨k, hk, ⟨e⟩⟩ := hsyl S
    have h1 := S.card_eq_multiplicity
    rw [hcardQ, hn5, show Nat.factorial 5 = 2 ^ 3 * 15 by decide,
      factorization_two_eq hOodd (by decide), hk] at h1
    obtain rfl : k = 3 := Nat.pow_right_injective le_rfl h1
    exact ⟨e⟩
  · obtain ⟨k, hk, ⟨e⟩⟩ := hsyl S
    have h1 := S.card_eq_multiplicity
    have hfac : (Nat.card Q).factorization 2 = 4 := by
      rw [hcardQ]
      rcases (show n = 6 ∨ n = 7 by omega) with h | h
      · rw [h, show Nat.factorial 6 = 2 ^ 4 * 45 by decide, factorization_two_eq hOodd (by decide)]
      · rw [h, show Nat.factorial 7 = 2 ^ 4 * 315 by decide,
          factorization_two_eq hOodd (by decide)]
    rw [hfac, hk] at h1
    obtain rfl : k = 4 := Nat.pow_right_injective le_rfl h1
    exact ⟨e⟩

end AltEvenCenter

open Subgroup AltEvenCenter CFSG.ComponentClassification.UnbalancedAltSeven

theorem small_alternating_even_center_exact_quaternion_cover
    {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7)
    {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    (hZ : Even (Nat.card (center Q))) (θ : Q ⧸ center Q ≃* alternatingGroup (Fin n)) :
    (∀ x : Q, x ∈ CFSG.pPrimeCore 2 Q ↔ x ∈ center Q ∧ Odd (orderOf x)) ∧
    ∃ z : Q, orderOf z = 2 ∧ (∀ y : Q, orderOf y = 2 → y = z) ∧ z ∈ center Q ∧
      CFSG.pPrimeCore 2 Q ⊔ zpowers z = center Q ∧ CFSG.pPrimeCore 2 Q ⊓ zpowers z = ⊥ ∧
      Group.IsPerfect (altCoverE n) ∧ Function.Surjective (altCoverPi h7) ∧
      (altCoverPi h7).ker = zpowers (altCoverZ n) ∧
      (∃! η : Q ⧸ CFSG.pPrimeCore 2 Q ≃* altCoverE n,
        ∀ q : Q, altCoverPi h7 (η (q : Q ⧸ CFSG.pPrimeCore 2 Q)) = θ (q : Q ⧸ center Q)) ∧
      (∀ η : Q ⧸ CFSG.pPrimeCore 2 Q ≃* altCoverE n,
        (∀ q : Q, altCoverPi h7 (η (q : Q ⧸ CFSG.pPrimeCore 2 Q)) = θ (q : Q ⧸ center Q)) →
        η (z : Q ⧸ CFSG.pPrimeCore 2 Q) = altCoverZ n ∧
        ∀ q : Q, ((η (q : Q ⧸ CFSG.pPrimeCore 2 Q) : altCoverE n) : altSevenE) = 1 ↔
          q ∈ CFSG.pPrimeCore 2 Q) ∧
      ∀ S : Sylow 2 Q, (n = 5 → Nonempty (S ≃* QuaternionGroup 2)) ∧
        (6 ≤ n → Nonempty (S ≃* QuaternionGroup 4)) := by
  have : Group.IsPerfect (altCoverE n) := altCoverE_isPerfect h7 h5
  obtain ⟨hO, z, hz2, huniq, hzZ, hsup, hinf, hη, hηz, hsyl⟩ :=
    structure_of_double_cover h5 h7 hQ hZ θ (altCoverPi_surjective h7) orderOf_altCoverZ
      altCoverZ_mem_center (altCoverPi_ker h7) fun y hy => eq_altCoverZ_of_orderOf_eq_two hy
  exact ⟨hO, z, hz2, huniq, hzZ, hsup, hinf, this, altCoverPi_surjective h7, altCoverPi_ker h7,
    hη, fun η _ => ⟨(hηz η).1, fun q => by rw [OneMemClass.coe_eq_one]; exact (hηz η).2 q⟩,
    hsyl⟩

end CFSG.LocalAnalysis
