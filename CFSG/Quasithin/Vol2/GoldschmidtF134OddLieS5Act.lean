module

public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieS5Rank

public section

namespace CFSG.Quasithin.H13.NQCore.S5

open Subgroup CFSG.OrderReductions.FrattiniAutomorphisms

variable {p : ℕ} [hp : Fact p.Prime]

theorem eq_one_of_sq_eq_one_of_trivial_mod_frattini (hp2 : p ≠ 2) {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) {τ : MulAut P} (hτ : τ ^ 2 = 1)
    (htriv : quotientAutomorphism (frattini P) τ = 1) : τ = 1 := by
  obtain ⟨-, hker⟩ := CFSG.GroupTheory.frattini_automorphism_kernel (p := p) hP
  obtain ⟨j, hj⟩ := hker ⟨τ, show τ ∈ (quotientAutomorphism (frattini P)).ker from htriv⟩
  have hj' : τ ^ (p ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hcop : Nat.Coprime 2 (p ^ j) :=
    Nat.Coprime.pow_right j ((Nat.coprime_primes Nat.prime_two hp.out).2 (Ne.symm hp2))
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hτ) (orderOf_dvd_of_pow_eq_one hj')
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h
  exact h

theorem card_le_eight_of_faithful {G : Type*} [Group G] [Finite G] (hp2 : p ≠ 2)
    {W E : Subgroup G} (hW : IsPGroup p W) (hWc : Nat.card W ∣ p ^ 3)
    (hEN : E ≤ normalizer (W : Set G)) (hE2 : ∀ x ∈ E, x * x = 1)
    (hfaith : ∀ x ∈ E, (∀ w ∈ W, w * x = x * w) → x = 1) : Nat.card E ≤ 8 := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 (by exact_mod_cast h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  let ρ : E →* MulAut W := W.normalizerMonoidHom.comp (Subgroup.inclusion hEN)
  let ψ : E →* MulAut (W ⧸ frattini W) := (quotientAutomorphism (frattini W)).comp ρ
  have hψ : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro e he
    have hτ : ρ e ^ 2 = 1 := by
      rw [← map_pow]
      have : e ^ 2 = 1 := Subtype.ext (by simpa [sq] using hE2 e e.2)
      rw [this, map_one]
    have hρ : ρ e = 1 := eq_one_of_sq_eq_one_of_trivial_mod_frattini hp2 hW hτ he
    refine Subtype.ext (hfaith e e.2 fun w hw => ?_)
    have h1 := congrArg (fun a : MulAut W => ((a ⟨w, hw⟩ : W) : G)) hρ
    simp only [ρ, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe,
      Subgroup.coe_inclusion, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  obtain ⟨-, hcomm, hpow, -, d, hd, -⟩ := CFSG.GroupTheory.frattini_elementary_quotient hW
  have hd3 : d ≤ 3 := by
    have h1 : p ^ d ∣ p ^ 3 :=
      (hd ▸ Subgroup.card_quotient_dvd_card (frattini W)).trans hWc
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 h1
  obtain ⟨e₀⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary
    (fun a b => hcomm.is_comm.comm a b) hpow hd
  let φ : E →* GL (Fin d) (ZMod p) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e₀).toMonoidHom.comp ψ
  have hφ : Function.Injective φ := fun a b h =>
    hψ ((CFSG.SectionRank.Ccomm.elemAutEquivGL e₀).injective h)
  have hF : Nat.card φ.range ≤ 8 := by
    refine card_le_eight_of_sq_eq_one h2 hd3 φ.range ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (hE2 x x.2)
    rw [this, map_one]
  calc Nat.card E = Nat.card φ.range := Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
    _ ≤ 8 := hF

end CFSG.Quasithin.H13.NQCore.S5
