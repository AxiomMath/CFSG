module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverKer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

theorem s16g_lift_order_p {Y : Type} [Group Y] [Finite Y] (hperf : Group.IsPerfect Y)
    (hlayer : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Y ⧸ CFSG.pCore 2 Y)) = ⊤)
    (N : Subgroup Y) [N.Normal] (hN : Group.IsSolvable ↥N) {X : Type} [Group X] [Finite X]
    (e : Y ⧸ N ≃* X) (hX : CFSG.Open.IsQuasisimple X)
    (hz : Odd (Nat.card (Subgroup.center X))) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmult : ¬ p ∣ Nat.card (CFSG.Open.griessHopfMultiplier X)) {x : X} (hx : orderOf x = p) :
    ∃ y : Y, orderOf y = p ∧ e (QuotientGroup.mk y) = x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect Y := hperf
  haveI : Group.IsPerfect X := ⟨hX.1⟩
  let R : Subgroup Y := CFSG.pCore 2 Y
  let π : Y →* Y ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  let f : Y →* X := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hfker : f.ker = N := by
    ext y
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : QuotientGroup.mk' N y = 1 := by
        apply e.injective
        simpa [f] using h
      exact (QuotientGroup.eq_one_iff y).mp h1
    · intro h
      have h1 : QuotientGroup.mk' N y = 1 := (QuotientGroup.eq_one_iff y).mpr h
      show f y = 1
      rw [show f y = e (QuotientGroup.mk' N y) from rfl, h1, map_one]
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨w, hw⟩ := e.surjective z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N w
    exact ⟨y, hw⟩
  have hP2 : IsPGroup 2 ↥(R.map f) := (CFSG.pCore_isPGroup (p := 2) (G := Y)).map f
  have hP2n : (R.map f).Normal :=
    Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := Y)) f hf
  have hxne : x ≠ 1 := by
    intro h
    have h1 : orderOf x = 1 := by rw [h, orderOf_one]
    rw [hx] at h1
    exact hp.ne_one h1
  have hRle : R ≤ N := by
    rcases CFSG.ASVolI.A129Aux.normal_eq_top_or_le_center hX hP2n with htop | hcen
    · exfalso
      have h2X : IsPGroup 2 X := by
        have htop' : IsPGroup 2 ↥(⊤ : Subgroup X) := htop ▸ hP2
        exact htop'.of_equiv Subgroup.topEquiv
      have hdvd : 2 ∣ orderOf x := h2X.dvd_orderOf hxne
      rw [hx] at hdvd
      exact (hp.eq_two_or_odd'.resolve_left hp2).not_two_dvd_nat hdvd
    · intro y hy
      have hmem : f y ∈ R.map f := Subgroup.mem_map_of_mem f hy
      have hcent : f y ∈ Subgroup.center X := hcen hmem
      have h1 : orderOf (f y) = 1 := by
        obtain ⟨c, hc⟩ := hP2.exists_orderOf_eq_pow ⟨f y, hmem⟩
        have hord2 : orderOf (f y) = 2 ^ c := by
          rw [← Subgroup.orderOf_mk (f y) hmem]
          exact hc
        have hordZ : orderOf (f y) ∣ Nat.card (Subgroup.center X) := by
          have := Subgroup.orderOf_dvd_natCard (Subgroup.center X) hcent
          simpa using this
        have hcop : Nat.Coprime (2 ^ c) (Nat.card (Subgroup.center X)) :=
          hz.coprime_two_left.pow_left c
        have hdvd2 : orderOf (f y) ∣ 2 ^ c := by rw [hord2]
        exact Nat.eq_one_of_dvd_coprimes hcop hdvd2 hordZ
      have h1' : f y = 1 := orderOf_eq_one_iff.mp h1
      rw [← hfker, MonoidHom.mem_ker]
      exact h1'
  have hfR : ∀ y ∈ R, f y = 1 := by
    intro y hy
    have h1 : y ∈ f.ker := by
      rw [hfker]
      exact hRle hy
    exact (MonoidHom.mem_ker).mp h1
  let q : Y ⧸ R →* X := QuotientGroup.lift R f hfR
  have hqπ : ∀ y : Y, q (π y) = f y := fun y => rfl
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨y, hy⟩ := hf a
    exact ⟨π y, by rw [hqπ]; exact hy⟩
  have hkerS : q.ker = N.map π := by
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    rw [MonoidHom.mem_ker, hqπ, Subgroup.mem_map]
    constructor
    · intro hfx
      refine ⟨x, ?_, rfl⟩
      have h1 : QuotientGroup.mk' N x = 1 := by
        apply e.injective
        simpa [f] using hfx
      exact (QuotientGroup.eq_one_iff x).mp h1
    · rintro ⟨x', hx', hxx'⟩
      have hx'' : x'⁻¹ * x ∈ R := (QuotientGroup.eq).mp hxx'
      have hxN : x ∈ N := by
        have := N.mul_mem hx' (hRle hx'')
        simpa using this
      have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hxN
      simp only [f, MonoidHom.comp_apply, h1, map_one]
  have hSsolv : Group.IsSolvable ↥q.ker := by
    rw [hkerS]
    exact Group.isSolvable_of_surjective (f := π.subgroupMap N)
      (MonoidHom.subgroupMap_surjective π N)
  haveI : q.ker.Normal := MonoidHom.normal_ker q
  have hSc : q.ker ≤ Subgroup.center (Y ⧸ R) :=
    close16_le_center_of_isSolvable hlayer hSsolv
  haveI : Group.IsPerfect (Y ⧸ R) := Group.IsPerfect.ofSurjective hπ
  have hdvd : Nat.card q.ker ∣ Nat.card (CFSG.Open.griessHopfMultiplier X) := by
    obtain ⟨-, ⟨h, -, -, -, -, ⟨e', -⟩⟩, -, -⟩ :=
      CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_schur_multiplier
        q hq hSc
    rw [← Nat.card_congr e'.toEquiv]
    refine (Subgroup.card_quotient_dvd_card _).trans ?_
    rw [← Nat.card_congr
      (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess X).toEquiv]
  have hpk : ¬ p ∣ Nat.card q.ker := fun h => hmult (h.trans hdvd)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Y, e (QuotientGroup.mk y₀) = x := by
    obtain ⟨w, hw⟩ := e.surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N w
    exact ⟨y, hw⟩
  obtain ⟨a, m, hm, hn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y₀).ne' p hp.ne_one
  have hcopm : Nat.Coprime m p :=
    (hp.coprime_iff_not_dvd.mpr hm).symm
  obtain ⟨k, hkm, hkp⟩ := Nat.chineseRemainder hcopm 0 1
  have hmk : m ∣ k := Nat.modEq_zero_iff_dvd.mp hkm
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hxp : x ^ p = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hxk : x ^ k = x := by
    rw [← pow_mod_orderOf x k, hx, hkp, Nat.mod_eq_of_lt hp.one_lt, pow_one]
  let y : Y := y₀ ^ k
  have hbase : (y₀ ^ (p ^ a)) ^ m = 1 := by
    rw [← pow_mul, ← hn]
    exact pow_orderOf_eq_one y₀
  have hy_pow_a : y ^ (p ^ a) = 1 := by
    obtain ⟨t, ht⟩ := hmk
    calc (y₀ ^ k) ^ (p ^ a) = y₀ ^ (k * p ^ a) := (pow_mul y₀ k (p ^ a)).symm
      _ = y₀ ^ (p ^ a * k) := by rw [mul_comm]
      _ = (y₀ ^ (p ^ a)) ^ k := pow_mul y₀ (p ^ a) k
      _ = (y₀ ^ (p ^ a)) ^ (m * t) := by rw [ht]
      _ = ((y₀ ^ (p ^ a)) ^ m) ^ t := pow_mul (y₀ ^ (p ^ a)) m t
      _ = 1 := by rw [hbase, one_pow]
  have hyp_a : (y ^ p) ^ (p ^ a) = 1 := by
    calc ((y₀ ^ k) ^ p) ^ (p ^ a) = (y₀ ^ k) ^ (p * p ^ a) :=
        (pow_mul (y₀ ^ k) p (p ^ a)).symm
      _ = (y₀ ^ k) ^ (p ^ a * p) := by rw [mul_comm]
      _ = ((y₀ ^ k) ^ (p ^ a)) ^ p := pow_mul (y₀ ^ k) (p ^ a) p
      _ = (y ^ (p ^ a)) ^ p := rfl
      _ = 1 := by rw [hy_pow_a, one_pow]
  have hy₀' : e ((QuotientGroup.mk' N) y₀) = x := hy₀
  have hmk' : (QuotientGroup.mk' N) (y₀ ^ k) = ((QuotientGroup.mk' N) y₀) ^ k :=
    map_pow (QuotientGroup.mk' N) y₀ k
  have h_e_y' : e ((QuotientGroup.mk' N) (y₀ ^ k)) = x := by
    rw [hmk', map_pow, hy₀', hxk]
  have h_e_y : e (QuotientGroup.mk y) = x := h_e_y'
  have hy1 : y ≠ 1 := by
    intro h
    apply hxne
    rw [← h_e_y, h]
    simp
  have h_eyp' : e ((QuotientGroup.mk' N) (y ^ p)) = 1 := by
    have hmk2 : (QuotientGroup.mk' N) (y ^ p) = ((QuotientGroup.mk' N) y) ^ p :=
      map_pow (QuotientGroup.mk' N) y p
    rw [hmk2, map_pow, h_e_y', hxp]
  have h_eyp : e (QuotientGroup.mk (y ^ p)) = 1 := h_eyp'
  have hyN : y ^ p ∈ N := by
    have h1 : (QuotientGroup.mk' N) (y ^ p) = 1 :=
      e.injective (by rw [h_eyp', map_one])
    exact (QuotientGroup.eq_one_iff (y ^ p)).mp h1
  have hyR : y ^ p ∈ R := by
    have hmem : π (y ^ p) ∈ q.ker := by
      rw [hkerS]
      exact Subgroup.mem_map_of_mem π hyN
    have hord1 : orderOf (π (y ^ p)) = 1 := by
      refine Nat.eq_one_of_dvd_coprimes (a := p ^ a) (b := Nat.card q.ker) ?_ ?_ ?_
      · exact (hp.coprime_iff_not_dvd.mpr hpk).pow_left a
      · exact (orderOf_map_dvd π (y ^ p)).trans
          ((orderOf_dvd_iff_pow_eq_one).mpr hyp_a)
      · exact Subgroup.orderOf_dvd_natCard q.ker hmem
    exact (QuotientGroup.eq_one_iff (y ^ p)).mp (orderOf_eq_one_iff.mp hord1)
  have hpow : y ^ p = 1 := by
    obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)).exists_orderOf_eq_pow
      (⟨y ^ p, hyR⟩ : ↥R)
    have hordR : orderOf (y ^ p) = 2 ^ c := by
      rw [← Subgroup.orderOf_mk (y ^ p) hyR]
      exact hc
    have hcop : Nat.Coprime (2 ^ c) (p ^ a) :=
      (hpodd.coprime_two_left.pow_left c).pow_right a
    have hdvdR : orderOf (y ^ p) ∣ 2 ^ c := by rw [hordR]
    have hord1 : orderOf (y ^ p) = 1 :=
      Nat.eq_one_of_dvd_coprimes (a := 2 ^ c) (b := p ^ a) hcop hdvdR
        ((orderOf_dvd_iff_pow_eq_one).mpr hyp_a)
    exact orderOf_eq_one_iff.mp hord1
  exact ⟨y, orderOf_eq_prime hpow hy1, h_e_y⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
