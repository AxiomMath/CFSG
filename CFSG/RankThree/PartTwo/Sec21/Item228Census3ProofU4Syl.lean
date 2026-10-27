module

public import CFSG.RankThree.PartOne.KF.SUSylow

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof

open CFSG.RankThree.PartOne.KFU
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank Matrix

variable {r : ℕ} {K : Type} [Field K] {n f p : ℕ}

theorem exists_conj_into_d8Tor_su_prime [NeZero n] [Finite K] [Fact p.Prime] [CharP K p]
    (hn : n = 4 ∨ n = 5) (hc : D8Comb n) (hK : Nat.card K = (p ^ f) ^ 2) (hr : r.Prime)
    (hr2 : r ≠ 2) (hdvd : r ∣ p ^ f - 1) :
    ∀ X : Subgroup ↥(SU (unitaryInvolution K p f) n), (∀ x ∈ X, x ^ r = 1) →
      ∃ g : ↥(SU (unitaryInvolution K p f) n), ∀ x ∈ X, g * x * g⁻¹ ∈
        (d8Tor r K n).subgroupOf (SU (unitaryInvolution K p f) n) := by
  have : Fact r.Prime := ⟨hr⟩
  set q : ℕ := p ^ f with hqdef
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    by_contra h
    have : q ≤ 1 := by omega
    nlinarith [Nat.zero_le q]
  have hKq : Nat.card K = q ^ 2 := hK
  set σ : K ≃+* K := unitaryInvolution K p f with hσdef
  have hσ : ∀ c : K, σ c = c ^ q := fun c => unitaryInvolution_apply K p f c
  let S : Sylow r Kˣ := default
  let Sg : Subgroup Kˣ := (S : Subgroup Kˣ)
  have hSg : Nat.card Sg = r ^ (Nat.card Kˣ).factorization r := Sylow.card_eq_multiplicity S
  have hKu : Nat.card Kˣ = q ^ 2 - 1 := by rw [Nat.card_units, hKq]
  have hva : (Nat.card Kˣ).factorization r = padicValNat r (q - 1) := by
    rw [hKu, Nat.factorization_def _ hr, padicValNat_sq_sub_one hr hr2 hq2 hdvd]
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
  have hPcard' : Nat.card P = r ^ (2 * padicValNat r (q - 1)) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hsuinj).toEquiv.symm, Nat.card_prod, hSg, hva,
      ← sq, ← pow_mul, mul_comm]
  have hMGU : Nat.card ↥(SU σ n) ∣ Nat.card (CFSG.Quasithin.StatedGU n q K) := by
    have hsub : StatedSU n q K ≤ CFSG.Quasithin.StatedGU n q K :=
      Subgroup.closure_mono (fun A hA => hA.2)
    rw [Nat.card_congr (equivStatedSU hK n).toEquiv]
    exact Subgroup.card_dvd_of_le hsub
  have hGU := factorization_card_statedGU_four_five (K := K) hr hr2 hq2 hKq hdvd hn
  have hv : (Nat.card ↥(SU σ n)).factorization r = 2 * padicValNat r (q - 1) := by
    have hle : (Nat.card ↥(SU σ n)).factorization r ≤ 2 * padicValNat r (q ^ 2 - 1) := by
      rw [← hGU]
      exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hMGU r
    rw [padicValNat_sq_sub_one hr hr2 hq2 hdvd] at hle
    have hge : 2 * padicValNat r (q - 1) ≤ (Nat.card ↥(SU σ n)).factorization r := by
      have hdvdP : Nat.card P ∣ Nat.card ↥(SU σ n) := Subgroup.card_subgroup_dvd_card P
      have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr hdvdP r
      rwa [hPcard', Nat.Prime.factorization_pow hr, Finsupp.single_eq_same] at this
    omega
  have hPcard : Nat.card P = r ^ (Nat.card ↥(SU σ n)).factorization r := by
    rw [hv, hPcard']
  intro X hX
  obtain ⟨g, hg⟩ := exists_conj_le_sylow P hPcard X hX
  refine ⟨g, fun x hx => ?_⟩
  obtain ⟨⟨s, t⟩, hst⟩ := hg x hx
  have hxp : (g * x * g⁻¹) ^ r = 1 := by
    rw [conj_pow, hX x hx, mul_one, mul_inv_cancel]
  have hs : (s : Kˣ) ^ r = 1 ∧ (t : Kˣ) ^ r = 1 := by
    have h1 : suDiag (s, t) ^ r = 1 := by rw [hst]; exact hxp
    rw [← map_pow] at h1
    have h2 : (s, t) ^ r = 1 := hsuinj (h1.trans (map_one suDiag).symm)
    have h3 : s ^ r = 1 := congrArg Prod.fst h2
    have h4 : t ^ r = 1 := congrArg Prod.snd h2
    exact ⟨by simpa using congrArg (fun z : ↥Sg => (z : Kˣ)) h3,
      by simpa using congrArg (fun z : ↥Sg => (z : Kˣ)) h4⟩
  rw [Subgroup.mem_subgroupOf, ← hst]
  refine ⟨(⟨(s : Kˣ), (mem_rootsOfUnity r _).mpr hs.1⟩,
    ⟨(t : Kˣ), (mem_rootsOfUnity r _).mpr hs.2⟩), ?_⟩
  show diagU (d8Vec n _) = _
  rw [d8Vec_eq_dvecN]
  rfl

end CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof
