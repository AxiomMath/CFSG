module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.Quasithin.H13.Cor332

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

def omegaCenter (Q : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ Q ∧ (∀ q ∈ Q, q * g = g * q) ∧ g ^ 2 = 1}
  one_mem' := ⟨one_mem Q, fun q _ => by rw [mul_one, one_mul], one_pow 2⟩
  mul_mem' := by
    rintro a b ⟨haQ, hac, ha2⟩ ⟨hbQ, hbc, hb2⟩
    refine ⟨mul_mem haQ hbQ, fun q hq => ?_, ?_⟩
    · rw [← mul_assoc, hac q hq, mul_assoc, hbc q hq, mul_assoc]
    · have hab : Commute a b := hbc a haQ
      rw [hab.mul_pow, ha2, hb2, mul_one]
  inv_mem' := by
    rintro a ⟨haQ, hac, ha2⟩
    refine ⟨inv_mem haQ, fun q hq => ?_, ?_⟩
    · exact ((Commute.inv_right (hac q hq : Commute q a))).eq
    · rw [inv_pow, ha2, inv_one]

theorem mem_omegaCenter {Q : Subgroup G} {g : G} :
    g ∈ omegaCenter Q ↔ g ∈ Q ∧ (∀ q ∈ Q, q * g = g * q) ∧ g ^ 2 = 1 := Iff.rfl

theorem omegaCenter_le (Q : Subgroup G) : omegaCenter Q ≤ Q := fun _ h => h.1

theorem conj_mem_omegaCenter {Q : Subgroup G} {x g : G}
    (hx : x ∈ Subgroup.normalizer (Q : Set G)) (hg : g ∈ omegaCenter Q) :
    x * g * x⁻¹ ∈ omegaCenter Q := by
  obtain ⟨hgQ, hgc, hg2⟩ := hg
  have hxQ : ∀ q, q ∈ Q ↔ x * q * x⁻¹ ∈ Q := Subgroup.mem_normalizer_iff.mp hx
  have hx'Q : ∀ q, q ∈ Q ↔ x⁻¹ * q * x ∈ Q := by
    intro q
    have := Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q : Set G)).inv_mem hx) q
    simpa using this
  refine ⟨(hxQ g).mp hgQ, fun q hq => ?_, ?_⟩
  · have h1 : x⁻¹ * q * x ∈ Q := (hx'Q q).mp hq
    have h2 := hgc _ h1
    calc q * (x * g * x⁻¹) = x * ((x⁻¹ * q * x) * g) * x⁻¹ := by group
      _ = x * (g * (x⁻¹ * q * x)) * x⁻¹ := by rw [h2]
      _ = x * g * x⁻¹ * q := by group
  · rw [conj_pow, hg2, mul_one, mul_inv_cancel]


theorem five_le_of_prime_ne {r : ℕ} (hr : r.Prime) (h2 : r ≠ 2) (h3 : r ≠ 3) : 5 ≤ r := by
  have := hr.two_le
  by_contra h
  interval_cases r <;> simp_all
  norm_num at hr

theorem isSolvable_of_le_normalizer [Finite G] (k : ℕ)
    (hE : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 2 ^ k)
    (hr : ∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ Nat.card G → ∀ d : ℕ, 1 ≤ d → d ≤ k →
      ¬ r ∣ 2 ^ d - 1)
    (hC : ∀ x z : G, orderOf z = 2 → x * z = z * x → ∀ r : ℕ, r.Prime → 5 ≤ r → orderOf x ≠ r)
    {Q H : Subgroup G} (hQ : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q)
    (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) : Group.IsSolvable H := by
  classical
  have h2p : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
  have hsub : (Nat.card H).primeFactors ⊆ {2, 3} := by
    intro r hr'
    obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr'
    by_contra hne
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
    have h5 : 5 ≤ r := five_le_of_prime_ne hrp hne.1 hne.2
    have : Fact r.Prime := ⟨hrp⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) r hrd
    have hxN : (x : G) ∈ Subgroup.normalizer (Q : Set G) := hHQ x.2
    have hxo : orderOf (x : G) = r := by rw [Subgroup.orderOf_coe]; exact hx
    have hQne : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ
    have hZ0Q : omegaCenter Q ≤ Q := omegaCenter_le Q
    have hZ0p : IsPGroup 2 (omegaCenter Q) := hQ2.to_le hZ0Q
    obtain ⟨z, hzG, hz1, hz2⟩ : ∃ z : G, z ∈ omegaCenter Q ∧ z ≠ 1 ∧ orderOf z = 2 := by
      have hcen : Nontrivial (Subgroup.center Q) := hQ2.center_nontrivial
      have hcp : IsPGroup 2 (Subgroup.center Q) := hQ2.to_subgroup _
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hcp
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero, Nat.card_eq_one_iff_unique] at hn
        exact not_subsingleton _ hn.1
      have h2dvd : 2 ∣ Nat.card (Subgroup.center Q) := by rw [hn]; exact dvd_pow_self 2 hn0
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Q) 2 h2dvd
      let φ : Subgroup.center Q →* G := Q.subtype.comp (Subgroup.center Q).subtype
      have hφ : Function.Injective φ := fun a b hab => Subtype.ext (Subtype.ext hab)
      have hzo : orderOf (φ z) = 2 := by rw [orderOf_injective φ hφ z, hz]
      have hzsq : φ z ^ 2 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one _
      refine ⟨φ z, ⟨(z : Q).2, fun q hq => ?_, hzsq⟩, ?_, hzo⟩
      · have := Subgroup.mem_center_iff.mp z.2 ⟨q, hq⟩
        exact congrArg Subtype.val this
      · intro h
        rw [h, orderOf_one] at hzo
        omega
    obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hZ0p
    have hZ0ea : IsElemAbelian 2 (omegaCenter Q) :=
      ⟨⟨⟨fun a b => Subtype.ext (b.2.2.1 a a.2.1)⟩⟩, fun g hg => hg.2.2⟩
    have hdk : d ≤ k := by
      have := hE _ hZ0ea
      rw [hd] at this
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    have hd1 : 1 ≤ d := by
      by_contra h
      have hd0 : d = 0 := by omega
      rw [hd0, pow_zero] at hd
      have hbot : omegaCenter Q = ⊥ := Subgroup.card_eq_one.mp hd
      exact hz1 (Subgroup.mem_bot.mp (hbot ▸ hzG))
    have hrG : r ∣ Nat.card G := hrd.trans (Subgroup.card_subgroup_dvd_card H)
    have hnd := hr r hrp h5 hrG d hd1 hdk
    let c : Equiv.Perm G := MulAut.toPerm G (MulAut.conj (x : G))
    have hcapp : ∀ g, c g = (x : G) * g * (x : G)⁻¹ := fun g => rfl
    have hmem_iff : ∀ g, c g ∈ omegaCenter Q ↔ g ∈ omegaCenter Q := by
      intro g
      refine ⟨fun hg => ?_, fun hg => conj_mem_omegaCenter hxN hg⟩
      have h := conj_mem_omegaCenter ((Subgroup.normalizer (Q : Set G)).inv_mem hxN) hg
      rw [hcapp] at h
      simpa [mul_assoc] using h
    let p : G → Prop := fun g => g ∈ omegaCenter Q ∧ g ≠ 1
    have hp : ∀ g, p (c g) ↔ p g := by
      intro g
      refine and_congr (hmem_iff g) ?_
      rw [hcapp]
      simp
    let σ : Equiv.Perm {g // p g} := c.subtypePerm hp
    have hxr : (x : G) ^ r = 1 := by rw [← hxo]; exact pow_orderOf_eq_one _
    have hcr : c ^ r = 1 := by
      have : MulAut.toPerm G (MulAut.conj (x : G)) ^ r =
          MulAut.toPerm G (MulAut.conj ((x : G) ^ r)) := by
        rw [map_pow, map_pow]
      rw [this, hxr, map_one, map_one]
    have hσr : σ ^ r ^ 1 = 1 := by
      rw [pow_one]
      ext a
      have h1 : ((σ ^ r) a : G) = (c ^ r) a := by
        change (((c.subtypePerm hp) ^ r) a : G) = _
        rw [Equiv.Perm.subtypePerm_pow]
        rfl
      rw [h1, hcr]
      rfl
    have : Fintype {g // p g} := Fintype.ofFinite _
    have hcard : Fintype.card {g // p g} = 2 ^ d - 1 := by
      have e : {g : omegaCenter Q // (g : G) ≠ 1} ≃ {g // p g} :=
        Equiv.subtypeSubtypeEquivSubtypeInter (fun g : G => g ∈ omegaCenter Q)
          (fun g : G => g ≠ 1)
      have : Fintype (omegaCenter Q) := Fintype.ofFinite _
      rw [← Fintype.card_congr e]
      have h1 : Fintype.card {g : omegaCenter Q // (g : G) ≠ 1} =
          Fintype.card {g : omegaCenter Q // ¬ g = 1} :=
        Fintype.card_congr (Equiv.subtypeEquivRight fun g => by simp)
      have h2 : Fintype.card {g : omegaCenter Q // ¬ g = 1} =
          Fintype.card (omegaCenter Q) - Fintype.card {g : omegaCenter Q // g = 1} :=
        Fintype.card_subtype_compl _
      rw [h1, h2, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hd]
    obtain ⟨a, ha⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := r) (n := 1)
      (by rw [hcard]; exact hnd) hσr
    have hfix : (x : G) * a.1 * (x : G)⁻¹ = a.1 := congrArg Subtype.val ha
    have hcomm : (x : G) * a.1 = a.1 * (x : G) := by
      have := congrArg (· * (x : G)) hfix
      simpa [mul_assoc] using this
    have ha2 : orderOf a.1 = 2 := by
      have hsq : a.1 ^ 2 = 1 := a.2.1.2.2
      exact orderOf_eq_prime hsq a.2.2
    exact hC (x : G) a.1 ha2 hcomm r hrp h5 hxo
  exact (Finset.card_le_card hsub).trans (by simp)


@[expose] def TwoLocalsSolvable (G : Type*) [Group G] : Prop :=
  ∀ Q H : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q → H ≤ Subgroup.normalizer (Q : Set G) →
    Group.IsSolvable H

theorem TwoLocalsSolvable.of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (h : TwoLocalsSolvable G') : TwoLocalsSolvable G := by
  intro Q H hQ hQ2 hHQ
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hbij : Function.Bijective e.toMonoidHom := e.bijective
  have hQ' : Q.map e.toMonoidHom ≠ ⊥ := fun hbot =>
    hQ ((Subgroup.map_eq_bot_iff_of_injective Q hinj).mp hbot)
  have hHQ' : H.map e.toMonoidHom ≤
      Subgroup.normalizer ((Q.map e.toMonoidHom : Subgroup G') : Set G') := by
    rw [← Subgroup.map_normalizer_eq_of_bijective Q hbij]
    exact Subgroup.map_mono hHQ
  have := h _ _ hQ' (hQ2.map e.toMonoidHom) hHQ'
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective H e.toMonoidHom hinj).toMonoidHom)
    (MulEquiv.injective _)

theorem twoLocalsSolvable_of [Finite G] (k : ℕ)
    (hE : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 2 ^ k)
    (hr : ∀ r : ℕ, r.Prime → 5 ≤ r → r ∣ Nat.card G → ∀ d : ℕ, 1 ≤ d → d ≤ k →
      ¬ r ∣ 2 ^ d - 1)
    (hC : ∀ x z : G, orderOf z = 2 → x * z = z * x → ∀ r : ℕ, r.Prime → 5 ≤ r → orderOf x ≠ r) :
    TwoLocalsSolvable G :=
  fun _ _ hQ hQ2 hHQ => isSolvable_of_le_normalizer k hE hr hC hQ hQ2 hHQ

end CFSG.Quasithin.H13.Cor332
