module

public import CFSG.RankThree.PartOne.KF.SUGram
public import CFSG.RankThree.PartOne.KF.SpSylow
public import CFSG.GroupTheory.WeirSylow.Unitary

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Matrix

variable {p : ℕ} {K : Type} [Field K] {n f : ℕ}

theorem not_dvd_add_one_of_dvd_sub_one {q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hdvd : p ∣ q - 1) : ¬ p ∣ q + 1 := by
  intro h
  have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h hdvd
  have : (q + 1) - (q - 1) = 2 := by omega
  rw [this] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem padicValNat_sq_sub_one {q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 2 ≤ q)
    (hdvd : p ∣ q - 1) : padicValNat p (q ^ 2 - 1) = padicValNat p (q - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    zify [Nat.one_le_pow 2 q (by omega), (by omega : 1 ≤ q)]
    ring
  rw [h1, padicValNat.mul (by omega) (by omega),
    padicValNat.eq_zero_of_not_dvd (not_dvd_add_one_of_dvd_sub_one hp hp2 (by omega) hdvd),
    add_zero]

theorem factorization_card_statedGU_four_five [Finite K] {q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) (hdvd : p ∣ q - 1) (hn : n = 4 ∨ n = 5) :
    (Nat.card (CFSG.Quasithin.StatedGU n q K)).factorization p =
      2 * padicValNat p (q ^ 2 - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hqK : Fintype.card K = q ^ 2 := by rw [Fintype.card_eq_nat_card]; exact hK
  have hq1 : ((q : ℕ) : ZMod p) = 1 := by
    have h1 : (((q - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    rw [Nat.cast_sub (by omega), sub_eq_zero] at h1
    simpa using h1
  have hpq : ¬ p ∣ q := by
    intro h
    have h1 : ((q : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [hq1] at h1
    exact one_ne_zero h1
  have hord : orderOf (-((q : ℕ) : ZMod p)) = 2 := by
    have h := orderOf_neg_one (R := ZMod p)
    rw [ZMod.ringChar_zmod_n] at h
    rw [hq1]
    exact h.trans (by simp [hp2])
  rw [CFSG.GroupTheory.WeirSylow.factorization_card_statedGU (hp.odd_of_ne_two hp2) K hqK hpq
    (by omega : 1 ≤ n), hord]
  have h1 : padicValInt p ((q : ℤ) ^ 2 - 1) = padicValNat p (q ^ 2 - 1) := by
    have : (q : ℤ) ^ 2 - 1 = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (Nat.one_le_pow 2 q (by omega))]
      ring
    rw [this, padicValInt.of_nat]
  have h2 : padicValNat p 2 = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rw [neg_sq, h1]
  rcases hn with rfl | rfl <;> simp [h2, mul_comm]

theorem exists_conj_into_d8Tor_su [NeZero n] [Finite K] [CharP K 2] (hn : n = 4 ∨ n = 5)
    (hc : D8Comb n) (hK : Nat.card K = (2 ^ f) ^ 2) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ f - 1) :
    ∀ X : Subgroup ↥(SU (unitaryInvolution K 2 f) n), (∀ x ∈ X, x ^ p = 1) →
      ∃ g : ↥(SU (unitaryInvolution K 2 f) n), ∀ x ∈ X, g * x * g⁻¹ ∈
        (d8Tor p K n).subgroupOf (SU (unitaryInvolution K 2 f) n) := by
  have : Fact p.Prime := ⟨hp⟩
  set q : ℕ := 2 ^ f with hqdef
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    by_contra h
    have : q ≤ 1 := by omega
    nlinarith [Nat.zero_le q]
  have hKq : Nat.card K = q ^ 2 := hK
  set σ : K ≃+* K := unitaryInvolution K 2 f with hσdef
  have hσ : ∀ c : K, σ c = c ^ q := fun c => unitaryInvolution_apply K 2 f c
  let S : Sylow p Kˣ := default
  let Sg : Subgroup Kˣ := (S : Subgroup Kˣ)
  have hSg : Nat.card Sg = p ^ (Nat.card Kˣ).factorization p := Sylow.card_eq_multiplicity S
  have hKu : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units, hKq]
  have hva : (Nat.card Kˣ).factorization p = padicValNat p (q - 1) := by
    rw [hKu, Nat.factorization_def _ hp, padicValNat_sq_sub_one hp hp2 hq2 hdvd]
  have hfix : ∀ s : Sg, σ ((s : Kˣ) : K) = (s : Kˣ) := by
    intro s
    have h1 : s ^ Nat.card Sg = 1 := pow_card_eq_one'
    have h2 : Nat.card Sg ∣ q - 1 := by
      rw [hSg, hva]
      exact pow_padicValNat_dvd
    have h3 : s ^ (q - 1) = 1 := by
      obtain ⟨k, hk⟩ := h2
      rw [hk, pow_mul, h1, one_pow]
    have h4 : (s : Kˣ) ^ (q - 1) = 1 := by
      simpa using congrArg (fun z : ↥Sg => (z : Kˣ)) h3
    rw [hσ, ← Units.val_pow_eq_pow_val]
    have : (s : Kˣ) ^ q = (s : Kˣ) := by
      calc (s : Kˣ) ^ q = (s : Kˣ) ^ (q - 1) * (s : Kˣ) := by
            rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        _ = (s : Kˣ) := by rw [h4, one_mul]
    rw [this]
  have hd0 : dvecN n (1 : Kˣ) 1 = 1 := (dvecNHom n).map_one
  let suDiag : ↥Sg × ↥Sg →* ↥(SU σ n) :=
    MonoidHom.codRestrict ((diagUHom.comp (dvecNHom n)).comp (Sg.subtype.prodMap Sg.subtype))
      (SU σ n) (fun x => diagU_dvecN_mem_SU hn hc σ (hfix x.1) (hfix x.2))
  have hsuinj : Function.Injective suDiag := by
    intro x y h
    have h1 : dvecN n (x.1 : Kˣ) (x.2 : Kˣ) = dvecN n (y.1 : Kˣ) (y.2 : Kˣ) :=
      diagU_injective (congrArg (fun z : ↥(SU σ n) => (z : GL (Fin n) K)) h)
    have h0 : ∀ a b : Kˣ, dvecN n a b 0 = a := fun a b => by simp [dvecN, d8Cls, d8EvU]
    have h1' : ∀ a b : Kˣ, dvecN n a b 1 = b := fun a b => by
      simp [dvecN, d8Cls, d8EvU, hc.one_ne_zero]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · have := congrFun h1 0
      rwa [h0, h0] at this
    · have := congrFun h1 1
      rwa [h1', h1'] at this
  let P : Subgroup ↥(SU σ n) := suDiag.range
  have hPcard' : Nat.card P = p ^ (2 * padicValNat p (q - 1)) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hsuinj).toEquiv.symm, Nat.card_prod, hSg, hva,
      ← sq, ← pow_mul, mul_comm]
  have hMGU : Nat.card ↥(SU σ n) ∣ Nat.card (CFSG.Quasithin.StatedGU n q K) := by
    have hsub : StatedSU n q K ≤ CFSG.Quasithin.StatedGU n q K :=
      Subgroup.closure_mono (fun A hA => hA.2)
    rw [Nat.card_congr (equivStatedSU hK n).toEquiv]
    exact Subgroup.card_dvd_of_le hsub
  have hGU := factorization_card_statedGU_four_five (K := K) hp hp2 hq2 hKq hdvd hn
  have hv : (Nat.card ↥(SU σ n)).factorization p = 2 * padicValNat p (q - 1) := by
    have hle : (Nat.card ↥(SU σ n)).factorization p ≤ 2 * padicValNat p (q ^ 2 - 1) := by
      rw [← hGU]
      exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hMGU p
    rw [padicValNat_sq_sub_one hp hp2 hq2 hdvd] at hle
    have hge : 2 * padicValNat p (q - 1) ≤ (Nat.card ↥(SU σ n)).factorization p := by
      have hdvdP : Nat.card P ∣ Nat.card ↥(SU σ n) := Subgroup.card_subgroup_dvd_card P
      have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvdP p
      rwa [hPcard', Nat.Prime.factorization_pow hp, Finsupp.single_eq_same] at this
    omega
  have hPcard : Nat.card P = p ^ (Nat.card ↥(SU σ n)).factorization p := by
    rw [hv, hPcard']
  intro X hX
  obtain ⟨g, hg⟩ := exists_conj_le_sylow P hPcard X hX
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨⟨s, t⟩, hst⟩ := hg x hx
  have hxp : (g * x * g⁻¹) ^ p = 1 := by
    rw [conj_pow, hX x hx, mul_one, mul_inv_cancel]
  have hs : (s : Kˣ) ^ p = 1 ∧ (t : Kˣ) ^ p = 1 := by
    have h1 : suDiag (s, t) ^ p = 1 := by rw [hst]; exact hxp
    rw [← map_pow] at h1
    have h2 : (s, t) ^ p = 1 := hsuinj (h1.trans (map_one suDiag).symm)
    have h3 : s ^ p = 1 := congrArg Prod.fst h2
    have h4 : t ^ p = 1 := congrArg Prod.snd h2
    exact ⟨by simpa using congrArg (fun z : ↥Sg => (z : Kˣ)) h3,
      by simpa using congrArg (fun z : ↥Sg => (z : Kˣ)) h4⟩
  rw [Subgroup.mem_subgroupOf, ← hst]
  refine ⟨(⟨(s : Kˣ), (mem_rootsOfUnity p _).mpr hs.1⟩,
    ⟨(t : Kˣ), (mem_rootsOfUnity p _).mpr hs.2⟩), ?_⟩
  show diagU (d8Vec n _) = _
  rw [d8Vec_eq_dvecN]
  rfl

end CFSG.RankThree.PartOne.KFU
