module

public import CFSG.Quasithin.Recognition.F112TitsFrob
public import CFSG.Quasithin.Recognition.RuTypeSz2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelCore

public section

namespace CFSG.Quasithin.Fan86.Model

open CFSG.Open CFSG.QuasithinUnique

theorem nonempty_mulEquiv_sz_zero_of_pCore {X : Type} [Group X] [Finite X]
    (hX : Nat.card X = 20) (hO : Open.pCore 2 X = ⊥) : Nonempty (X ≃* ↥(Sz 0)) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨N, hNn, hN⟩ := CFSG.Quasithin.F112T.exists_normal_five hX
  have hNbot : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hN
    omega
  obtain ⟨u', hu'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hNbot
  set u : X := (u' : X) with hu
  have huN : u ∈ N := u'.2
  have hu1 : u ≠ 1 := fun h => hu'1 (Subtype.ext h)
  have hu5 : u ^ 5 = 1 := by
    have h := pow_card_eq_one' (G := N) (x := u')
    rw [hN] at h
    simpa using congrArg Subtype.val h
  have hord : orderOf u = 5 := orderOf_eq_prime hu5 hu1
  have hzp : Subgroup.zpowers u = N := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 huN) ?_
    rw [Nat.card_zpowers, hord, hN]
  refine CFSG.Quasithin.RuType.nonempty_mulEquiv_sz_zero hX hord
    (fun x => hzp ▸ hNn.conj_mem u huN x) ?_
  intro x hx
  by_contra hxN'
  rw [hzp] at hxN'
  have hcomm : ∀ n ∈ N, n * x = x * n := by
    intro n hn
    rw [← hzp] at hn
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    exact (((Commute.symm (show Commute x u from hx)).zpow_left k).eq)
  set C : Subgroup X := Subgroup.centralizer (N : Set X) with hCdef
  have hxC : x ∈ C := Subgroup.mem_centralizer_iff.2 hcomm
  have hNC : N ≤ C := by
    intro n hn
    refine Subgroup.mem_centralizer_iff.2 fun m hm => ?_
    rw [← hzp] at hn hm
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
    exact (Commute.zpow_zpow_self u b a).eq
  have h5C : 5 ∣ Nat.card C := hN ▸ Subgroup.card_dvd_of_le hNC
  have hCdvd : Nat.card C ∣ 20 := hX ▸ Subgroup.card_subgroup_dvd_card C
  have hC5 : Nat.card C ≠ 5 := by
    intro h
    have hCN : N = C := Subgroup.eq_of_le_of_card_ge hNC (by rw [h, hN])
    exact hxN' (hCN ▸ hxC)
  have h2C : 2 ∣ Nat.card C := by
    obtain ⟨k, hk⟩ := h5C
    have hk4 : k ∣ 4 := by
      have h' : 5 * k ∣ 5 * 4 := by simpa [hk] using hCdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h'
    have hk4' : k ≤ 4 := Nat.le_of_dvd (by norm_num) hk4
    interval_cases k <;> omega
  obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' 2 h2C
  set z' : X := (z : X) with hz'
  have hz'ord : orderOf z' = 2 := by rw [hz', Subgroup.orderOf_coe, hz2]
  have hz'N : ∀ n ∈ N, n * z' = z' * n := Subgroup.mem_centralizer_iff.1 z.2
  have hzp2 : IsPGroup 2 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'ord]; norm_num)
  obtain ⟨Q, hzQ⟩ := hzp2.exists_le_sylow
  have hQ4 : Nat.card (Q : Subgroup X) = 2 ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hX]
    have h20 : (20 : ℕ).factorization 2 = 2 := by
      have : (20 : ℕ) = 2 ^ 2 * 5 := by norm_num
      rw [this, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two]
      simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 5 by norm_num)]
    rw [h20]
  have hQc : IsMulCommutative (Q : Subgroup X) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ4
  have hzQ' : z' ∈ (Q : Subgroup X) := hzQ (Subgroup.mem_zpowers z')
  set Z : Subgroup X := Subgroup.centralizer ({z'} : Set X) with hZdef
  have hQZ : (Q : Subgroup X) ≤ Z := by
    intro q hq
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff.1 hy]
    exact congrArg Subtype.val (hQc.is_comm.comm (⟨z', hzQ'⟩ : (Q : Subgroup X)) ⟨q, hq⟩)
  have hNZ : N ≤ Z := by
    intro n hn
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    rw [Set.mem_singleton_iff.1 hy]
    exact (hz'N n hn).symm
  have h5Z : 5 ∣ Nat.card Z := hN ▸ Subgroup.card_dvd_of_le hNZ
  have h4Z : 4 ∣ Nat.card Z := by
    have := Subgroup.card_dvd_of_le hQZ
    rwa [hQ4] at this
  have h20Z : 20 ∣ Nat.card Z := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5Z h4Z
  have hZtop : Z = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hX]
    exact Nat.dvd_antisymm (hX ▸ Subgroup.card_subgroup_dvd_card Z) h20Z
  have hcent : ∀ g : X, z' * g = g * z' := fun g => by
    have hg : g ∈ Z := by rw [hZtop]; exact Subgroup.mem_top g
    exact Subgroup.mem_centralizer_iff.1 hg z' (Set.mem_singleton z')
  have hzn : (Subgroup.zpowers z').Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g (z' ^ k) := ((Commute.symm (hcent g) : Commute g z').zpow_right k)
    rw [hc.eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers z' k
  have hle : Subgroup.zpowers z' ≤ Open.pCore 2 X :=
    CFSG.LieType.BorelTits.le_pCore 2 hzn hzp2
  rw [hO] at hle
  have : z' = 1 := Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers z'))
  rw [this, orderOf_one] at hz'ord
  omega

theorem nonempty_oTwoQuot_sz_zero {G : Type} [Group G] [Finite G]
    (h : Nat.card (oTwoQuot G) = 20) : Nonempty (oTwoQuot G ≃* ↥(Sz 0)) :=
  nonempty_mulEquiv_sz_zero_of_pCore h (pCore_quotient_pCore_eq_bot G)

end CFSG.Quasithin.Fan86.Model
