module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.NoncommCoprod
import CFSG.CharacterTheory.Burnside
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofUnitary

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG

namespace Res417Seven

variable {H : Type*} [Group H]

theorem exists_card_nine_of_commute {x y : H} (hx : orderOf x = 3) (hy3 : y ^ 3 = 1)
    (hyx : y ∉ Subgroup.zpowers x) (hxy : x * y = y * x) :
    ∃ E : Subgroup H, Nat.card E = 9 ∧ ∀ e ∈ E, ∃ i j : ℤ, e = x ^ i * y ^ j := by
  have hy1 : y ≠ 1 := fun h => hyx (h ▸ one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have : Finite (Subgroup.zpowers y) :=
    finite_zpowers.mpr (orderOf_pos_iff.mp (by rw [hyo]; norm_num))
  have hcomm : ∀ (m : Subgroup.zpowers x) (n : Subgroup.zpowers y),
      Commute ((Subgroup.zpowers x).subtype m) ((Subgroup.zpowers y).subtype n) := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact Commute.zpow_zpow (show Commute x y from hxy) i j
  have hdisj : Disjoint (Subgroup.zpowers x) (Subgroup.zpowers y) := by
    rw [Subgroup.disjoint_def]
    intro g hgx hgy
    by_contra hg1
    have hg3 : orderOf g = 3 := by
      have hd : orderOf g ∣ 3 := by
        rw [← hyo]
        exact orderOf_dvd_of_pow_eq_one (by
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hgy
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
            one_zpow])
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hg1
      · exact h
    have heq : Subgroup.zpowers g = Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hgy)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hg3])
    apply hyx
    have hy : y ∈ Subgroup.zpowers g := heq ▸ Subgroup.mem_zpowers y
    exact Subgroup.zpowers_le.mpr hgx hy
  set f := MonoidHom.noncommCoprod (Subgroup.zpowers x).subtype (Subgroup.zpowers y).subtype
    hcomm with hf
  have hfinj : Function.Injective f :=
    (MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, by
        rw [Subgroup.range_subtype, Subgroup.range_subtype]
        exact hdisj⟩
  refine ⟨f.range, ?_, ?_⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hx, hyo]
  · rintro _ ⟨⟨⟨m, hm⟩, ⟨n, hn⟩⟩, rfl⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hm
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    exact ⟨i, j, rfl⟩

theorem isPGroup_two_of_coprime_three {a b : ℕ} (hcard : Nat.card H = 2 ^ a * 3 ^ b)
    {N : Subgroup H} (hN : Nat.Coprime 3 (Nat.card N)) : IsPGroup 2 N := by
  have hdvd : Nat.card N ∣ 2 ^ a * 3 ^ b := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have h2 : Nat.card N ∣ 2 ^ a := (Nat.Coprime.pow_right b hN.symm).dvd_of_dvd_mul_right hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  exact IsPGroup.of_card hk

theorem exists_central_involution [Finite H] {N : Subgroup H} (hNn : N.Normal)
    (hN2 : IsPGroup 2 N) (hN1 : N ≠ ⊥)
    (hinv : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v) :
    ∃ u : H, orderOf u = 2 ∧ ∀ g : H, g * u = u * g := by
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : Nontrivial (Subgroup.center N) := hN2.center_nontrivial
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp (hN2.to_subgroup (Subgroup.center N))
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hZ).ne' hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center N) 2
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  set u : H := ((z : N) : H) with hu
  have hu2 : orderOf u = 2 := by
    rw [hu, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have huN : u ∈ N := (z : N).2
  have huZ : ∀ n ∈ N, n * u = u * n := fun n hn =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨n, hn⟩)
  refine ⟨u, hu2, fun g => ?_⟩
  have hgu : g * u * g⁻¹ ∈ N := hNn.conj_mem u huN g
  have hgu2 : orderOf (g * u * g⁻¹) = 2 := by
    have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective u
    rw [hu2] at h
    simpa [MulAut.conj_apply] using h
  have h1 : g * u * g⁻¹ = u := hinv _ _ hgu2 hu2 (huZ _ hgu)
  calc g * u = (g * u * g⁻¹) * g := by group
    _ = u * g := by rw [h1]

theorem factorization_three_two_pow_mul (a b : ℕ) : (2 ^ a * 3 ^ b).factorization 3 = b := by
  rw [Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
    Nat.Prime.factorization_self Nat.prime_three,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
  simp

theorem exists_normal_of_central_three [Finite H] {x : H} (hxc : ∀ g : H, g * x = x * g)
    (hx3 : orderOf x = 3) {a b : ℕ} (hcard : Nat.card H = 2 ^ a * 3 ^ b) (hb : b ≤ 3)
    (hexp : ∀ y : H, (∃ k : ℕ, y ^ 3 ^ k = 1) → y ^ 3 = 1)
    (hinv : ∀ u v : H, orderOf u = 2 → orderOf v = 2 → u * v = v * u → u = v)
    (hfix : ∀ u y : H, orderOf u = 2 → y ^ 3 = 1 → y * u = u * y → y ∈ Subgroup.zpowers x)
    (hy : ∃ y : H, y ^ 3 = 1 ∧ y ∉ Subgroup.zpowers x) :
    ∃ P : Subgroup H, P.Normal ∧ IsPGroup 3 P ∧ ∀ y : H, y ^ 3 = 1 → y ∈ P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy3, hyx⟩ := hy
  have hsolv : Group.IsSolvable H := by
    have := Fintype.ofFinite H
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (a := a) (b := b) (by rw [← Nat.card_eq_fintype_card, hcard])
  have hcore : pPrimeCore 3 H = ⊥ := by
    refine sSup_eq_bot.mpr fun N hN => ?_
    by_contra hN1
    obtain ⟨u, hu2, huc⟩ :=
      exists_central_involution hN.1 (isPGroup_two_of_coprime_three hcard hN.2) hN1 hinv
    exact hyx (hfix u y hu2 hy3 (huc y))
  set R := pCore 3 H with hR
  have hFR : fittingSubgroup H = R := Fitting_eq_pcore H 3 hcore
  have hCR : Subgroup.centralizer (R : Set H) ≤ R := by
    have := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv
    rwa [hFR] at this
  have hRn : R.Normal := pCore_normal
  have hR3 : IsPGroup 3 R := pCore_isPGroup
  have hxpow : ∀ (g : H) (i : ℤ), g * x ^ i = x ^ i * g := fun g i =>
    (Commute.zpow_right (show Commute g x from hxc g) i).eq
  have hzx : (Subgroup.zpowers x).Normal := ⟨fun n hn g => by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [hxpow g i, mul_inv_cancel_right]
    exact hn⟩
  have hxR : Subgroup.zpowers x ≤ R :=
    le_sSup (α := Subgroup H) ⟨hzx, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3,
      pow_one])⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  have hRP : R ≤ P := fitting_pCore_le_sylow P
  have hPcard : Nat.card P = 3 ^ b := by
    rw [Sylow.card_eq_multiplicity, hcard, factorization_three_two_pow_mul]
  have hPn : (P : Subgroup H).Normal := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).mp hR3
    by_cases hRPeq : R = P
    · rw [← hRPeq]
      exact hRn
    have hkb : k < b := by
      by_contra hkb
      apply hRPeq
      refine Subgroup.eq_of_le_of_card_ge hRP ?_
      rw [hk, hPcard]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have hk1 : 1 ≤ k := by
      have h1 := Subgroup.card_le_of_le hxR
      rw [Nat.card_zpowers, hx3, hk] at h1
      by_contra h0
      rw [show k = 0 by omega, pow_zero] at h1
      omega
    have hk2 : k = 2 := by
      by_contra hk2
      have hk1' : k = 1 := by omega
      have hxReq : Subgroup.zpowers x = R :=
        Subgroup.eq_of_le_of_card_ge hxR (by rw [hk, hk1', Nat.card_zpowers, hx3, pow_one])
      apply hyx
      rw [hxReq]
      refine hCR (Subgroup.mem_centralizer_iff.mpr fun r hr => ?_)
      rw [← hxReq] at hr
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
      exact (hxpow y i).symm
    have hb3 : b = 3 := by omega
    obtain ⟨w, hwR, hwx⟩ : ∃ w ∈ R, w ∉ Subgroup.zpowers x := by
      by_contra h
      push Not at h
      have h1 := Subgroup.card_le_of_le (show R ≤ Subgroup.zpowers x from h)
      rw [hk, hk2, Nat.card_zpowers, hx3] at h1
      omega
    have hw3 : w ^ 3 = 1 := by
      refine hexp w ?_
      obtain ⟨j, hj⟩ := hR3 ⟨w, hwR⟩
      exact ⟨j, by simpa using congrArg Subtype.val hj⟩
    obtain ⟨E, hE9, hEgen⟩ := exists_card_nine_of_commute hx3 hw3 hwx (hxc w).symm
    have hER : E ≤ R := fun e he => by
      obtain ⟨i, j, rfl⟩ := hEgen e he
      exact mul_mem (zpow_mem (hxR (Subgroup.mem_zpowers x)) i) (zpow_mem hwR j)
    have hEReq : E = R := Subgroup.eq_of_le_of_card_ge hER (by rw [hk, hE9, hk2]; norm_num)
    have hCw : Subgroup.centralizer ({w} : Set H) ≤ R := fun g hg => by
      have hgw : g * w = w * g := (Subgroup.mem_centralizer_singleton_iff.mp hg)
      refine hCR (Subgroup.mem_centralizer_iff.mpr fun r hr => ?_)
      rw [← hEReq] at hr
      obtain ⟨i, j, rfl⟩ := hEgen r hr
      have hgwj : g * w ^ j = w ^ j * g := (Commute.zpow_right (show Commute g w from hgw) j).eq
      calc x ^ i * w ^ j * g = x ^ i * (g * w ^ j) := by rw [mul_assoc, hgwj]
        _ = g * (x ^ i * w ^ j) := by rw [← mul_assoc, ← hxpow g i, mul_assoc]
    have horb : MulAction.orbit (ConjAct H) w ⊆ (R : Set H) \ (Subgroup.zpowers x : Set H) := by
      rintro _ ⟨c, rfl⟩
      change c • w ∈ _
      rw [ConjAct.smul_def]
      refine ⟨hRn.conj_mem w hwR _, fun hc => hwx ?_⟩
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hc
      have : w = x ^ i := by
        calc w = (ConjAct.ofConjAct c)⁻¹ * (ConjAct.ofConjAct c * w * (ConjAct.ofConjAct c)⁻¹) *
              ConjAct.ofConjAct c := by group
          _ = (ConjAct.ofConjAct c)⁻¹ * x ^ i * ConjAct.ofConjAct c := by rw [hi]
          _ = x ^ i := by rw [hxpow, inv_mul_cancel_right]
      rw [this]
      exact zpow_mem (Subgroup.mem_zpowers x) i
    have hdiff : ((R : Set H) \ (Subgroup.zpowers x : Set H)).ncard = 6 := by
      rw [Set.ncard_sdiff (show (Subgroup.zpowers x : Set H) ⊆ R from hxR), ← Nat.card_coe_set_eq,
        ← Nat.card_coe_set_eq]
      change Nat.card R - Nat.card (Subgroup.zpowers x) = 6
      rw [hk, hk2, Nat.card_zpowers, hx3]
      norm_num
    have horb6 : (MulAction.orbit (ConjAct H) w).ncard ≤ 6 :=
      hdiff ▸ Set.ncard_le_ncard horb (Set.toFinite _)
    have hcardH : Nat.card H ≤ 54 := by
      have h1 := (MulAction.stabilizer (ConjAct H) w).card_mul_index
      rw [MulAction.index_stabilizer, ← Subgroup.nat_card_centralizer_nat_card_stabilizer] at h1
      have h2 : Nat.card (ConjAct H) = Nat.card H := Nat.card_congr ConjAct.ofConjAct.toEquiv
      have h3 := Subgroup.card_le_of_le hCw
      rw [hk, hk2] at h3
      rw [← h2, ← h1]
      calc Nat.card (Subgroup.centralizer ({w} : Set H)) *
            (MulAction.orbit (ConjAct H) w).ncard ≤ 9 * 6 := Nat.mul_le_mul (by simpa using h3)
              horb6
        _ = 54 := by norm_num
    have hidx : (P : Subgroup H).index ≤ 2 := by
      have h1 := (P : Subgroup H).card_mul_index
      rw [hPcard, hb3] at h1
      omega
    have hidx0 : (P : Subgroup H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (show (P : Subgroup H).index = 1 ∨ (P : Subgroup H).index = 2 by omega) with h | h
    · rw [Subgroup.index_eq_one.mp h]
      exact Subgroup.normal_top
    · exact Subgroup.normal_of_index_eq_two h
  refine ⟨P, hPn, P.isPGroup', fun z hz => ?_⟩
  have : (P : Subgroup H).Normal := hPn
  exact Res417Six.mem_of_coprime_index
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (Sylow.not_dvd_index P)) hz

end Res417Seven

end CFSG.RankThree.PartTwo.Sec4
