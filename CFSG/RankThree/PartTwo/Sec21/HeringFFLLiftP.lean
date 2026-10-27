module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open (IsElemAbelian)

private theorem card_comap_mk_lift {X : Type} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (K : Subgroup (X ⧸ Z)) :
    Nat.card (K.comap (QuotientGroup.mk' Z)) = Nat.card K * Nat.card Z := by
  have h1 : (K.comap (QuotientGroup.mk' Z)).index = K.index :=
    Subgroup.index_comap_of_surjective K (QuotientGroup.mk'_surjective Z)
  have h2 := Subgroup.card_mul_index (K.comap (QuotientGroup.mk' Z))
  have h3 := Subgroup.card_mul_index K
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rw [h1] at h2
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h2, h4, ← h3]
  ring

theorem exists_elemAbelian_of_quotient {X : Type} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    {p : ℕ} [Fact p.Prime] (hZp : ¬ p ∣ Nat.card Z) {E : Subgroup (X ⧸ Z)}
    (hE : IsElemAbelian p E) : ∃ Q : Subgroup X, IsElemAbelian p Q ∧ Nat.card Q = Nat.card E := by
  obtain ⟨hEc, hEexp⟩ := hE
  have hEp : IsPGroup p E := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa using hEexp (g : X ⧸ Z) g.2
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hEp
  obtain ⟨K, hK⟩ : ∃ S : Subgroup X, S = E.comap (QuotientGroup.mk' Z) := ⟨_, rfl⟩
  have memK : ∀ x : X, x ∈ K ↔ QuotientGroup.mk' Z x ∈ E := fun x => by
    rw [hK, Subgroup.mem_comap]
  have hcardK : Nat.card K = p ^ n * Nat.card Z := by
    rw [hK, card_comap_mk_lift Z E, hn]
  obtain ⟨Q, hQK, hQcard⟩ : ∃ Q : Subgroup X, Q ≤ K ∧ Nat.card Q = p ^ n := by
    have hdvd : p ^ n ∣ Nat.card K := ⟨Nat.card Z, hcardK⟩
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd
    exact ⟨P.map K.subtype, Subgroup.map_subtype_le P,
      (Subgroup.card_map_of_injective K.subtype_injective).trans hP⟩
  have hQinj : ∀ x ∈ Q, QuotientGroup.mk' Z x = 1 → x = 1 := by
    intro x hx hxZ
    have hxZ' : x ∈ Z := (QuotientGroup.eq_one_iff (N := Z) x).mp hxZ
    have hpn : x ^ p ^ n = 1 := by
      have h := (pow_card_eq_one' : (⟨x, hx⟩ : ↥Q) ^ Nat.card ↥Q = 1)
      rw [hQcard] at h
      exact congrArg Subtype.val h
    have hZn : x ^ Nat.card Z = 1 := by
      have h := (pow_card_eq_one' : (⟨x, hxZ'⟩ : ↥Z) ^ Nat.card ↥Z = 1)
      exact congrArg Subtype.val h
    have hpZ : Nat.Coprime p (Nat.card Z) :=
      (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mpr hZp
    have hgcd : Nat.gcd (p ^ n) (Nat.card Z) = 1 :=
      Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left n hpZ)
    have hx1 := (pow_gcd_eq_one (a := x) (m := p ^ n) (n := Nat.card Z)).mpr ⟨hpn, hZn⟩
    rw [hgcd, pow_one] at hx1
    exact hx1
  have hπE : ∀ x ∈ Q, QuotientGroup.mk' Z x ∈ E := fun x hx => (memK x).mp (hQK hx)
  have hinj : ∀ x ∈ Q, ∀ y ∈ Q, QuotientGroup.mk' Z x = QuotientGroup.mk' Z y → x = y := by
    intro x hx y hy hxy
    have h1 : x * y⁻¹ = 1 := by
      apply hQinj _ (Q.mul_mem hx (Q.inv_mem hy))
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    exact mul_inv_eq_one.mp h1
  have hEcomm : ∀ u v : X ⧸ Z, u ∈ E → v ∈ E → u * v = v * u := by
    intro u v hu hv
    have h := hEc.is_comm.comm (⟨u, hu⟩ : ↥E) ⟨v, hv⟩
    exact congrArg Subtype.val h
  refine ⟨Q, ?_, hQcard.trans hn.symm⟩
  unfold IsElemAbelian
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · show a * b = b * a
    apply Subtype.ext
    show (a : X) * b = (b : X) * a
    apply hinj _ (Q.mul_mem a.2 b.2) _ (Q.mul_mem b.2 a.2)
    rw [map_mul, map_mul]
    exact hEcomm _ _ (hπE _ a.2) (hπE _ b.2)
  · apply hinj _ (Q.pow_mem hx p) 1 Q.one_mem
    rw [map_pow, hEexp _ (hπE x hx), map_one]

end CFSG.RankThree.PartTwo.Sec21
