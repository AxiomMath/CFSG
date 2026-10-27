module

public import CFSG.Quasithin.EmptyFaithful.S146zWB
public import CFSG.Quasithin.EmptyFaithful.SBc16GAct

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem WreathData.no_elemAbelian_sq {H R J J' : Subgroup G} {ρ : G}
    (d : WreathData H R J J' ρ) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G}
    (hEJ : E ≤ J) (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ 2) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hEH : E ≤ H := hEJ.trans d.J_le_H
  set E' : Subgroup G := conjByElt ρ E with hE'
  have hE'J' : E' ≤ J' := by
    rw [d.eq]
    exact Subgroup.map_mono hEJ
  have hE'H : E' ≤ H := hE'J'.trans d.J'_le_H
  have hE'ab : IsElemAbelian p E' :=
    CFSG.SectionRank.isElemAbelian_map hE (MulAut.conj ρ).toMonoidHom
  have hE'card : Nat.card E' = p ^ 2 := by
    rw [← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective E (MulAut.conj ρ).toMonoidHom
      (MulAut.conj ρ).injective).toEquiv).symm
  have hO2 : ∀ x : G, x ∈ pCoreOf 2 H → x ^ p = 1 → x = 1 := by
    intro x hx hxp
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨x, hx⟩
    have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : orderOf x ∣ Nat.gcd (2 ^ k) p := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1)
      (orderOf_dvd_of_pow_eq_one hxp)
    have h3 : Nat.gcd (2 ^ k) p = 1 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
    rw [h3] at h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h2)
  set N : Subgroup ↥H := CFSG.Open.pCore 2 ↥H with hN
  let f₁ : ↥E →* ↥H ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hEH)
  let f₂ : ↥E' →* ↥H ⧸ N := (QuotientGroup.mk' N).comp (Subgroup.inclusion hE'H)
  have hmemN : ∀ x : ↥H, x ∈ N ↔ (x : G) ∈ pCoreOf 2 H := fun x =>
    SBc16.mem_pCore_iff_coe H x
  have hcomm : ∀ (a : ↥E) (b : ↥E'), Commute (f₁ a) (f₂ b) := by
    intro a b
    change (QuotientGroup.mk (Subgroup.inclusion hEH a) : ↥H ⧸ N) *
        QuotientGroup.mk (Subgroup.inclusion hE'H b) =
      QuotientGroup.mk (Subgroup.inclusion hE'H b) * QuotientGroup.mk (Subgroup.inclusion hEH a)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmemN]
    have h1 : ⁅(b : G)⁻¹, (a : G)⁻¹⁆ ∈ ⁅J', J⁆ :=
      Subgroup.commutator_mem_commutator (hE'J' (E'.inv_mem b.2)) (hEJ (E.inv_mem a.2))
    rw [Subgroup.commutator_comm] at h1
    have h2 := d.comm h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hf₁ : Function.Injective f₁ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : Subgroup.inclusion hEH a ∈ N := (QuotientGroup.eq_one_iff _).mp ha
    have h2 : (a : G) ∈ pCoreOf 2 H := (hmemN _).mp h1
    exact Subtype.ext (hO2 _ h2 (hE.2 a a.2))
  have hf₂ : Function.Injective f₂ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : Subgroup.inclusion hE'H a ∈ N := (QuotientGroup.eq_one_iff _).mp ha
    have h2 : (a : G) ∈ pCoreOf 2 H := (hmemN _).mp h1
    exact Subtype.ext (hO2 _ h2 (hE'ab.2 a a.2))
  have hdisj : Disjoint f₁.range f₂.range := by
    rw [Subgroup.disjoint_def]
    rintro x ⟨a, rfl⟩ ⟨b, hb⟩
    have h1 : (Subgroup.inclusion hEH a)⁻¹ * Subgroup.inclusion hE'H b ∈ N := by
      refine QuotientGroup.eq.mp ?_
      exact hb.symm
    have h2 : (a : G)⁻¹ * (b : G) ∈ pCoreOf 2 H := (hmemN _).mp h1
    have hbJ : (b : G) ∈ J ⊔ pCoreOf 2 H := by
      have : (b : G) = (a : G) * ((a : G)⁻¹ * (b : G)) := by group
      rw [this]
      exact Subgroup.mul_mem_sup (hEJ a.2) h2
    have hbJ' : (b : G) ∈ J' ⊔ pCoreOf 2 H := Subgroup.mem_sup_left (hE'J' b.2)
    have hb2 : (b : G) ∈ pCoreOf 2 H := by
      rw [← d.inter]
      exact ⟨hbJ, hbJ'⟩
    have hb1 : b = 1 := Subtype.ext (hO2 _ hb2 (hE'ab.2 b b.2))
    rw [← hb, hb1, map_one]
  let Φ := f₁.noncommCoprod f₂ hcomm
  have hΦ : Function.Injective Φ :=
    (MonoidHom.noncommCoprod_injective f₁ f₂ hcomm).mpr ⟨hf₁, hf₂, hdisj⟩
  have hrange : Nat.card Φ.range = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, Nat.card_prod, hcard, hE'card]
    ring
  have hE1 := hE.1
  have hE2 := hE'ab.1
  have habel : IsElemAbelian p Φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨y₁, hy₁⟩ := a.2
      obtain ⟨y₂, hy₂⟩ := b.2
      apply Subtype.ext
      change (a : ↥H ⧸ N) * b = b * a
      rw [← hy₁, ← hy₂, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (mul_comm' y₁.1 y₂.1) (mul_comm' y₁.2 y₂.2)
    · obtain ⟨y, rfl⟩ := hx
      rw [← map_pow]
      have : y ^ p = 1 := Prod.ext (Subtype.ext (hE.2 _ y.1.2)) (Subtype.ext (hE'ab.2 _ y.2.2))
      rw [this, map_one]
  have h2f : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ N)) ≤ 2 :=
    (sqt_iff.mp (sqt_quotient_two_group d.cfg.sqtk.1 N
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2))) p hp hp2
  have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ N)) :=
    CFSG.SectionRank.le_pRank hp.one_lt (le_top : Φ.range ≤ ⊤) habel hrange
  omega

end CFSG.Quasithin.S146zW
