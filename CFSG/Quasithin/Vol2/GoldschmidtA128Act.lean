module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.Quasithin.Vol2.A128

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm

variable {p : ℕ} [hp : Fact p.Prime] {Y : Type*} [Group Y] [Finite Y]
  {P : Subgroup Y} [P.Normal]

@[expose] noncomputable def action (D : Subgroup P) [D.Characteristic] :
    Y →* MulAut (D ⧸ frattini D) :=
  (frattiniAction D).comp (MulAut.conjNormal (H := P))

omit [Finite Y] in
theorem involution_eq_one_of_action_eq_one (hp2 : p ≠ 2) (D : Subgroup P) [D.Characteristic]
    (hker : IsPGroup p (frattiniAction D).ker)
    (hno : ∀ t : Y, t * t = 1 → t ≠ 1 → ∃ x ∈ P, t * x ≠ x * t)
    {t : Y} (ht : t * t = 1) (h1 : action D t = 1) : t = 1 := by
  by_contra ht1
  obtain ⟨x, hxP, hx⟩ := hno t ht ht1
  set c : MulAut P := MulAut.conjNormal t with hc
  have hmem : c ∈ (frattiniAction D).ker := by
    rw [MonoidHom.mem_ker]
    exact h1
  have hcc : c * c = 1 := by
    rw [hc, ← map_mul, ht, map_one]
  obtain ⟨k, hk⟩ := hker ⟨c, hmem⟩
  have hdvd1 : orderOf (⟨c, hmem⟩ : (frattiniAction D).ker) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one hk
  have hdvd2 : orderOf (⟨c, hmem⟩ : (frattiniAction D).ker) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using hcc
  have hcop : Nat.Coprime (p ^ k) 2 :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hp.out Nat.prime_two).2 hp2)
  have hdvd : orderOf (⟨c, hmem⟩ : (frattiniAction D).ker) ∣ 1 := by
    have := Nat.dvd_gcd hdvd1 hdvd2
    rwa [hcop.gcd_eq_one] at this
  rw [Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  have hc1 : c = 1 := congrArg Subtype.val hdvd
  apply hx
  have h2 := congrArg (fun σ : MulAut P => ((σ ⟨x, hxP⟩ : P) : Y)) hc1
  simp only [hc, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc t * x = t * x * t⁻¹ * t := by group
    _ = x * t := by rw [h2]

theorem odd_card_ker_action (hp2 : p ≠ 2) (D : Subgroup P) [D.Characteristic]
    (hker : IsPGroup p (frattiniAction D).ker)
    (hno : ∀ t : Y, t * t = 1 → t ≠ 1 → ∃ x ∈ P, t * x ≠ x * t) :
    Odd (Nat.card (action D).ker) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (action D).ker := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.mp hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := (action D).ker) 2 h2
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  have h1 : (t : Y) * t = 1 := by
    have := congrArg Subtype.val ht2
    simpa using this
  have h3 : action D (t : Y) = 1 := t.2
  have h4 := involution_eq_one_of_action_eq_one hp2 D hker hno h1 h3
  have : t = 1 := Subtype.ext h4
  rw [this, orderOf_one] at ht
  omega

end CFSG.Quasithin.Vol2.A128
