module

public import CFSG.RankThree.PartOne.S12.Sec1511AutCore
public import CFSG.RankThree.PartOne.K159.AutL2Iso
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2NormalExtension
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import CFSG.RankThree.PartOne.CTP.OutEmbed

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.GorensteinWalter Matrix MatrixGroups CFSG.RankThree.PartOne.K159
  CFSG.RankThree.PartOne.StrongP

namespace Sec1511

section PSL

variable {K : Type} [Field K] [Finite K]

theorem card_aut_psl2_pk {p k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (hK : Nat.card K = p ^ k) (h4 : 3 < Nat.card K) :
    Nat.card (MulAut (PSL2 K)) = Nat.card K * (Nat.card K ^ 2 - 1) * k := by
  have hodd : IsOddPrimePower (Nat.card K) := ⟨p, k, Fact.out, (Fact.out : p.Prime).odd_of_ne_two hp2, hk, hK⟩
  have hsurj := pGammaL2ToMulAutPSL2_surjective K hK hodd h4
  let eAut := pGammaL2EquivMulAutPSL2 K hodd h4 hsurj
  rw [← Nat.card_congr eAut.toEquiv, Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hAut : Nat.card (K ≃+* K) = k := by
    obtain ⟨-, -, -, -, h, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        (p := p) (n := k) (Fact.out) hk hK
    exact h
  rw [pgl2_card_formula K, hAut]

theorem psl2_exactWit {p : ℕ} [CharP K p] (hodd : Odd (Nat.card K)) :
    ExactWit p (Nat.card K) ((Nat.card K - 1) / 2) PSL(2, K) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf a = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units]
  have hq1 : 2 ∣ Nat.card K - 1 := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  have hq3 : 3 ≤ Nat.card K := by
    have : Nat.card K ≠ 1 := by
      intro h1
      have := Finite.one_lt_card_iff_nontrivial.2 (inferInstance : Nontrivial K)
      omega
    obtain ⟨m, hm⟩ := hodd
    omega
  have hrpos : 0 < (Nat.card K - 1) / 2 := by omega
  refine ⟨(uHom (K := K)).range, QuotientGroup.mk (dHom a), ?_, card_range_uHom, ?_, hrpos, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact uHom_pow x
  · rintro _ ⟨x, rfl⟩
    refine ⟨Multiplicative.ofAdd ((a : K) ^ 2 * Multiplicative.toAdd x), ?_⟩
    have := dPSL_mul_uHom a (Multiplicative.toAdd x)
    simp only [ofAdd_toAdd] at this
    rw [eq_mul_inv_iff_mul_eq]
    exact this.symm
  · rintro _ ⟨x, rfl⟩
    have hg : (QuotientGroup.mk (dHom a) : PSL(2, K)) ^ ((Nat.card K - 1) / 2) =
        QuotientGroup.mk (dHom (a ^ ((Nat.card K - 1) / 2))) := by
      rw [map_pow, QuotientGroup.mk_pow]
    have h2 : (((a ^ ((Nat.card K - 1) / 2) : Kˣ) : K)) ^ 2 = 1 := by
      have h3 : a ^ (2 * ((Nat.card K - 1) / 2)) = 1 := by
        rw [Nat.mul_div_cancel' hq1, ← hord]
        exact pow_orderOf_eq_one a
      have h4 : (((a ^ ((Nat.card K - 1) / 2) : Kˣ) : K)) ^ 2 =
          ((a ^ (2 * ((Nat.card K - 1) / 2)) : Kˣ) : K) := by
        rw [Units.val_pow_eq_pow_val, ← pow_mul, mul_comm, Units.val_pow_eq_pow_val]
      rw [h4, h3, Units.val_one]
    have h5 := dPSL_mul_uHom (a ^ ((Nat.card K - 1) / 2)) (Multiplicative.toAdd x)
    simp only [ofAdd_toAdd] at h5
    rw [hg, mul_inv_eq_iff_eq_mul, h5, h2, one_mul]
    rfl
  · intro k hk0 hkr
    refine ⟨uHom (Multiplicative.ofAdd 1), ⟨_, rfl⟩, fun h => ?_⟩
    have hg : (QuotientGroup.mk (dHom a) : PSL(2, K)) ^ k = QuotientGroup.mk (dHom (a ^ k)) := by
      rw [map_pow, QuotientGroup.mk_pow]
    rw [hg, mul_inv_eq_iff_eq_mul, dPSL_mul_uHom (a ^ k) 1] at h
    have h3 := uHom_injective (mul_right_cancel h)
    have h4 : (((a ^ k : Kˣ) : K)) ^ 2 * 1 = 1 := by
      simpa using congrArg Multiplicative.toAdd h3
    have h5 : a ^ (2 * k) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_mul']
      simpa [Units.val_pow_eq_pow_val] using h4
    have h6 := orderOf_dvd_of_pow_eq_one h5
    rw [hord] at h6
    have := Nat.le_of_dvd (by omega) h6
    omega

end PSL

section Row

theorem card_sylow_le {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : k = 2 ∨ k = 3) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = p ^ k) {H : Type} [Group H] [Finite H] {S : Subgroup H} [S.Normal]
    (hC : Subgroup.centralizer (S : Set H) = ⊥) (e : ↥S ≃* PSL2 K) {P : Subgroup H}
    (hP : IsSylowOf p P ⊤) : Nat.card P ≤ p ^ k := by
  have : Fact p.Prime := ⟨hp⟩
  have hk1 : 1 ≤ k := by omega
  have h4 : 3 < Nat.card K := by
    rw [hK]
    calc 3 < 5 := by norm_num
      _ ≤ p := hp5
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk1
  have hcardA := card_aut_psl2_pk (K := K) (p := p) (by omega) hk1 hK h4
  let ρ₀ : H →* MulAut (PSL2 K) := (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := S))
  have hρ₀ : Function.Injective ρ₀ :=
    (MulAut.congr e).injective.comp (CTP.conjNormal_injective_of_centralizer S hC)
  have h2 : Nat.card H ∣ Nat.card (MulAut (PSL2 K)) := Subgroup.card_dvd_of_injective ρ₀ hρ₀
  have h1 : Nat.card P ∣ Nat.card H := Subgroup.card_subgroup_dvd_card P
  obtain ⟨a, ha⟩ := hP.2.1.exists_card_eq
  have hdvd : p ^ a ∣ p ^ k * (((p ^ k) ^ 2 - 1) * k) := by
    have := h1.trans h2
    rw [ha, hcardA, hK] at this
    simpa [mul_assoc] using this
  have hc1 : Nat.Coprime p ((p ^ k) ^ 2 - 1) := by
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have hpk : p ∣ (p ^ k) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
    have h5 : p ∣ (p ^ k) ^ 2 - ((p ^ k) ^ 2 - 1) := Nat.dvd_sub hpk hd
    have h6 : 1 ≤ (p ^ k) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos _)
    have h7 : (p ^ k) ^ 2 - ((p ^ k) ^ 2 - 1) = 1 := by omega
    rw [h7] at h5
    exact hp.one_lt.ne' (Nat.dvd_one.1 h5)
  have hc2 : Nat.Coprime p k := by
    rw [hp.coprime_iff_not_dvd]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hcop : Nat.Coprime (p ^ a) (((p ^ k) ^ 2 - 1) * k) := Nat.Coprime.pow_left a (hc1.mul_right hc2)
  have h8 : p ^ a ∣ p ^ k := hcop.dvd_of_dvd_mul_right hdvd
  have h9 : a ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h8
  rw [ha]
  exact Nat.pow_le_pow_right hp.pos h9

theorem l2_row {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hk : k = 2 ∨ k = 3) {H : Type} [Group H] [Finite H]
    {S : Subgroup H} [S.Normal] (hC : Subgroup.centralizer (S : Set H) = ⊥)
    (q : TauCeti.PrimePower) (hqp : q.p = p) (hq : q.exponent = k)
    (hiso : Census3.IsoLie ↥S (.A 1 q)) {P : Subgroup H} (hP : IsSylowOf p P ⊤) :
    Nat.card (omegaOne p P) = p ^ k ∧
      ∃ g ∈ Subgroup.normalizer ((omegaOne p P : Subgroup H) : Set H),
        OrderModC (omegaOne p P) g ((p ^ k - 1) / 2) := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  obtain ⟨e⟩ := nonempty_psl_two_of_isoLie q hiso
  subst hqp
  have hK : Nat.card (GaloisField q.p q.exponent) = q.p ^ k := by
    rw [GaloisField.card q.p q.exponent (by omega), hq]
  have hPle := card_sylow_le q.prime_p hp5 hk hK hC e hP
  have hΩle : Nat.card (omegaOne q.p P) ≤ q.p ^ k := by
    refine le_trans ?_ hPle
    exact Subgroup.card_le_of_le ((Subgroup.closure_le _).2 fun x hx => hx.1)
  have hodd : Odd (Nat.card (GaloisField q.p q.exponent)) := by
    rw [hK]
    exact (q.prime_p.odd_of_ne_two (by omega)).pow
  have hwit := psl2_exactWit (K := GaloisField q.p q.exponent) (p := q.p) hodd
  rw [hK] at hwit
  have hwit' : ExactWit q.p (q.p ^ k) ((q.p ^ k - 1) / 2) ↥S := ExactWit.of_mulEquiv e.symm hwit
  exact hwit'.row q.prime_p hP hΩle

end Row

end Sec1511

end CFSG.RankThree.PartOne
