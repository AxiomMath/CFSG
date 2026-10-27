module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R38Gen
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79R1KBase

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv

namespace R38K

variable {H : Type} [Group H] [Finite H]

theorem pow_three_of_mem_zpowers {b y : H} (hb3 : b ^ 3 = 1) (hy : y ∈ Subgroup.zpowers b) :
    y ^ 3 = 1 := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]

theorem cen_of_ctl {b β : H} (hb3 : b ^ 3 = 1) (hbβ : b * β = β * b) (hC : CtlEq b β)
    (hO : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers β))))) {S : Subgroup H}
    (hS : IsPGroup 2 S) (hbS : b ∈ Nor S) {x : H} (hxS : x ∈ S) (hxβ : x * β = β * x) :
    x * b = b * x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxN : x ∈ Nor (Subgroup.zpowers β) := mem_Nor_zpowers_of_comm hxβ
  have hxmem : x ∈ setMul (Opp 3 (Nor (Subgroup.zpowers β)))
      (Nor (Subgroup.zpowers b) ⊓ Nor (Subgroup.zpowers β)) := by
    unfold CtlEq at hC
    rw [hC]
    exact hxN
  obtain ⟨q, hq, m, hm, hxqm⟩ := hxmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
    ((Subgroup.mem_normalizer_iff.mp hm.1 b).mp (Subgroup.mem_zpowers b))
  set b' : H := m * b * m⁻¹ with hb'
  have hb'mem : b' ∈ Subgroup.zpowers b := by
    rw [← hk]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
  have hcenβ : ∀ y ∈ Subgroup.zpowers b, y ∈ Nor (Subgroup.zpowers β) := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact mem_Nor_zpowers_of_comm (Commute.zpow_left (show Commute b β from hbβ) i).eq
  have hb'N := hcenβ b' hb'mem
  have heN : b' * b⁻¹ ∈ Nor (Subgroup.zpowers β) :=
    hcenβ _ (Subgroup.mul_mem _ hb'mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers b)))
  have he3 : (b' * b⁻¹) ^ 3 = 1 :=
    pow_three_of_mem_zpowers hb3
      (Subgroup.mul_mem _ hb'mem (Subgroup.inv_mem _ (Subgroup.mem_zpowers b)))
  set d : H := x * b * x⁻¹ * b⁻¹ with hd
  have hdS : d ∈ S := by
    have h1 : b * x⁻¹ * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hbS x⁻¹).mp (S.inv_mem hxS)
    have : d = x * (b * x⁻¹ * b⁻¹) := by rw [hd]; group
    rw [this]
    exact S.mul_mem hxS h1
  obtain ⟨j, hj⟩ := hS ⟨d, hdS⟩
  have hdj : d ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  set q₂ : H := q * (b' * q⁻¹ * b'⁻¹) with hq₂
  set e : H := b' * b⁻¹ with he
  have hq₂mem : q₂ ∈ Opp 3 (Nor (Subgroup.zpowers β)) :=
    (Opp 3 (Nor (Subgroup.zpowers β))).mul_mem hq
      (L14.Opp_conj_mem hb'N ((Opp 3 (Nor (Subgroup.zpowers β))).inv_mem hq))
  have hdqe : d = q₂ * e := by
    rw [hd, hq₂, he, hxqm, hb']
    group
  have hcube : d ^ 3 ∈ Opp 3 (Nor (Subgroup.zpowers β)) := by
    have h1 : e * q₂ * e⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers β)) := L14.Opp_conj_mem heN hq₂mem
    have h2 : e * (e * q₂ * e⁻¹) * e⁻¹ ∈ Opp 3 (Nor (Subgroup.zpowers β)) :=
      L14.Opp_conj_mem heN h1
    have e3 : d ^ 3 = q₂ * (e * q₂ * e⁻¹) * (e * (e * q₂ * e⁻¹) * e⁻¹) * e ^ 3 := by
      rw [hdqe, pow_three', pow_three']
      group
    rw [e3, he3, mul_one]
    exact (Opp 3 (Nor (Subgroup.zpowers β))).mul_mem
      ((Opp 3 (Nor (Subgroup.zpowers β))).mul_mem hq₂mem h1) h2
  have hcop2 : Nat.Coprime 2 (Nat.card (Opp 3 (Nor (Subgroup.zpowers β)))) :=
    Nat.coprime_two_left.mpr hO
  have hd3 : d ^ 3 = 1 := by
    refine eq_one_of_pow_prime_pow hcop2 hcube (m := j) ?_
    rw [← pow_mul, mul_comm, pow_mul, hdj, one_pow]
  have hd1 : d = 1 := by
    have h1 : orderOf d ∣ 3 := orderOf_dvd_of_pow_eq_one hd3
    have h2 : orderOf d ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hdj
    have h3 : Nat.Coprime 3 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h1 h2)
  have : x * b * x⁻¹ = b := by
    have h := hd1
    rw [hd] at h
    calc x * b * x⁻¹ = (x * b * x⁻¹ * b⁻¹) * b := by group
      _ = b := by rw [h, one_mul]
  calc x * b = (x * b * x⁻¹) * x := by group
    _ = b * x := by rw [this]



theorem exists_beta {b c : H} (hb : orderOf b = 3) (hc : orderOf c = 3) (hbc : b * c = c * b)
    {a : H} (ha : a ∈ Subgroup.closure ({b, c} : Set H)) (ha1 : a ≠ 1) :
    b ∈ Subgroup.zpowers a ∨ c ∈ Subgroup.zpowers a ∨ b * c ∈ Subgroup.zpowers a ∨
      b * c⁻¹ ∈ Subgroup.zpowers a := by
  have hbc' : Commute b c := hbc
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hb2 : (b ^ 2) ^ 2 = b := by
    rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_succ, hb3, one_mul]
  have hc2 : (c ^ 2) ^ 2 = c := by
    rw [← pow_mul, show (2 : ℕ) * 2 = 3 + 1 from rfl, pow_succ, hc3, one_mul]
  have hcinv : c⁻¹ = c ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact hc3)
  have hpow : ∀ (g t : H) (k : ℕ), t = g ^ k → t ∈ Subgroup.zpowers g := by
    intro g t k h
    rw [h]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(k : ℤ), zpow_natCast g k⟩
  have hred : ∀ (g : H), orderOf g = 3 → ∀ i : ℤ, ∃ n : ℕ, n < 3 ∧ g ^ i = g ^ n := by
    intro g hg i
    have h3 : ((orderOf g : ℕ) : ℤ) = 3 := by simp [hg]
    have h1 := zpow_mod_orderOf g i
    rw [h3] at h1
    have hr : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · exact ⟨0, by norm_num, by rw [pow_zero, ← h1, hr, zpow_zero]⟩
    · exact ⟨1, by norm_num, by rw [pow_one, ← h1, hr, zpow_one]⟩
    · exact ⟨2, by norm_num, by rw [← h1, hr, zpow_ofNat]⟩
  have hbcases : ∀ x ∈ Subgroup.zpowers b, x = 1 ∨ x = b ∨ x = b ^ 2 := by
    intro x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨n, hn, hin⟩ := hred b hb i
    rw [hin]
    interval_cases n <;> simp
  have hccases : ∀ y ∈ Subgroup.zpowers c, y = 1 ∨ y = c ∨ y = c ^ 2 := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    obtain ⟨n, hn, hin⟩ := hred c hc i
    rw [hin]
    interval_cases n <;> simp
  have hcomm : ∀ x ∈ Subgroup.zpowers b, ∀ y ∈ Subgroup.zpowers c, Commute x y := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_zpow hbc' i j
  rw [CFSG.RankThree.PartTwo.Sec21.FF81.closure_pair_eq_sup] at ha
  obtain ⟨x, hx, y, hy, hxy⟩ := (CFSG.mem_sup_of_commute hcomm).mp ha
  subst hxy
  rcases hbcases x hx with h1 | h1 | h1 <;> rcases hccases y hy with h2 | h2 | h2 <;>
    rw [h1, h2] at ha1 ⊢
  · exact absurd (mul_one (1 : H)) ha1
  · exact Or.inr (Or.inl (hpow (1 * c) c 1 (by rw [pow_one, one_mul])))
  · exact Or.inr (Or.inl (hpow (1 * c ^ 2) c 2 (by rw [one_mul, hc2])))
  · exact Or.inl (hpow (b * 1) b 1 (by rw [mul_one, pow_one]))
  · exact Or.inr (Or.inr (Or.inl (Subgroup.mem_zpowers (b * c))))
  · exact Or.inr (Or.inr (Or.inr (hpow (b * c ^ 2) (b * c⁻¹) 1 (by rw [pow_one, hcinv]))))
  · exact Or.inl (hpow (b ^ 2 * 1) b 2 (by rw [mul_one, hb2]))
  · exact Or.inr (Or.inr (Or.inr (hpow (b ^ 2 * c) (b * c⁻¹) 2
      (by rw [(Commute.pow_left hbc' 2).mul_pow 2, hb2, hcinv]))))
  · exact Or.inr (Or.inr (Or.inl (hpow (b ^ 2 * c ^ 2) (b * c) 2
      (by rw [(Commute.pow_pow hbc' 2 2).mul_pow 2, hb2, hc2]))))

theorem B_comm_gen {b c : H} (hbc : b * c = c * b) {u v : H}
    (hu : u ∈ Subgroup.closure ({b, c} : Set H)) (hv : v ∈ Subgroup.closure ({b, c} : Set H)) :
    u * v = v * u := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ Subgroup.zpowers c, Commute a x := by
    intro a ha x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_zpow hbc i j
  rw [closure_pair_eq_sup] at hu hv
  obtain ⟨a, ha, x, hx, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hu
  obtain ⟨a', ha', x', hx', rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hv
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  obtain ⟨i', rfl⟩ := Subgroup.mem_zpowers_iff.mp ha'
  obtain ⟨j', rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
  have h1 : Commute (b ^ i * c ^ j) (b ^ i' * c ^ j') := by
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_)
    · exact Commute.zpow_zpow_self b i i'
    · exact Commute.zpow_zpow (show Commute b c from hbc) i j'
    · exact (Commute.zpow_zpow (show Commute b c from hbc) i' j).symm
    · exact Commute.zpow_zpow_self c j j'
  exact h1.eq

theorem B_pow_three_gen {b c : H} (hb3 : b ^ 3 = 1) (hc3 : c ^ 3 = 1) (hbc : b * c = c * b)
    {u : H} (hu : u ∈ Subgroup.closure ({b, c} : Set H)) : u ^ 3 = 1 := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ Subgroup.zpowers c, Commute a x := by
    intro a ha x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_zpow hbc i j
  rw [closure_pair_eq_sup] at hu
  obtain ⟨a, ha, x, hx, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hu
  rw [(hcomm a ha x hx).mul_pow, pow_three_of_mem_zpowers hb3 ha, pow_three_of_mem_zpowers hc3 hx,
    mul_one]

theorem card_B_gen {b c : H} (hb : orderOf b = 3) (hc : orderOf c = 3) (hbc : b * c = c * b)
    (hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥) :
    Nat.card (Subgroup.closure ({b, c} : Set H)) = 9 := by
  have hcomm : ∀ a ∈ Subgroup.zpowers b, ∀ x ∈ Subgroup.zpowers c, Commute a x := by
    intro a ha x hx
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Commute.zpow_zpow hbc i j
  rw [closure_pair_eq_sup, CFSG.card_sup_eq_mul_of_commute _ _ hcomm hdisj, Nat.card_zpowers,
    Nat.card_zpowers, hb, hc]

theorem le_cen_of_e9 {b c : H} (hb : orderOf b = 3) (hc : orderOf c = 3) (hbc : b * c = c * b)
    (hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥)
    (hC₁ : CtlEq b c) (hC₂ : CtlEq b (b * c)) (hC₃ : CtlEq b (b * c⁻¹))
    (hO₁ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers c)))))
    (hO₂ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * c))))))
    (hO₃ : Odd (Nat.card (Opp 3 (Nor (Subgroup.zpowers (b * c⁻¹))))))
    {S : Subgroup H} (hS : IsPGroup 2 S) (hbS : b ∈ Nor S) (hcS : c ∈ Nor S) :
    ∀ x ∈ S, x * b = b * x := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 : b ^ 3 = 1 := by rw [← hb]; exact pow_orderOf_eq_one b
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  set B₀ : Subgroup H := Subgroup.closure ({b, c} : Set H) with hB₀
  have hB₀S : B₀ ≤ Nor S := by
    rw [hB₀, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hbS
    · exact hcS
  haveI : IsElementaryAbelian 3 ↥B₀ :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (B_comm_gen hbc x.2 y.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2
        (fun x => Subtype.ext (B_pow_three_gen hb3 hc3 hbc x.2)) }
  have hcard : Nat.card ↥B₀ = 9 := card_B_gen hb hc hbc hdisj
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have hp : ¬ 3 ∣ Nat.card ↥S := by
    rw [hn]
    intro h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  let _ : MulDistribMulAction ↥B₀ ↥S := Subgroup.conjMulDistribMulActionOfLeNormalizer B₀ S hB₀S
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 3) (A := ↥B₀) (H := ↥S)
    (by rw [hcard]; norm_num) hp
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥S) ∈ (⊤ : Subgroup ↥S) := Subgroup.mem_top _
  rw [← hgen] at hx'
  have hle : (⨆ (a : ↥B₀) (_ : a ≠ 1), CFSG.fixedPointSubgroup (Subgroup.zpowers a) ↥S) ≤
      (Cen b).comap S.subtype := by
    refine iSup₂_le fun a ha y hy => ?_
    have hax : a • y = y := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a y).mp hy
    have hya := congrArg Subtype.val hax
    change (a : H) * (y : H) * (a : H)⁻¹ = (y : H) at hya
    have hcomm : (y : H) * (a : H) = (a : H) * (y : H) := by
      calc (y : H) * (a : H) = ((a : H) * (y : H) * (a : H)⁻¹) * (a : H) := by rw [hya]
        _ = (a : H) * (y : H) := by group
    have hycomm : ∀ β ∈ Subgroup.zpowers (a : H), (y : H) * β = β * (y : H) := by
      intro β hβ
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hβ
      exact (Commute.zpow_right (show Commute (y : H) (a : H) from hcomm) k).eq
    have ha1 : (a : H) ≠ 1 := fun h1 => ha (Subtype.ext h1)
    show (y : H) ∈ Cen b
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyS : (y : H) ∈ S := y.2
    rcases exists_beta hb hc hbc a.2 ha1 with h1 | h1 | h1 | h1
    · exact hycomm b h1
    · exact cen_of_ctl hb3 hbc hC₁ hO₁ hS hbS hyS (hycomm c h1)
    · exact cen_of_ctl hb3 (by
          calc b * (b * c) = b * (c * b) := by rw [hbc]
            _ = (b * c) * b := by group) hC₂ hO₂ hS hbS hyS (hycomm _ h1)
    · exact cen_of_ctl hb3 (by
          calc b * (b * c⁻¹) = b * (c⁻¹ * b) := by
                rw [(Commute.inv_right (show Commute b c from hbc)).eq]
            _ = (b * c⁻¹) * b := by group) hC₃ hO₃ hS hbS hyS (hycomm _ h1)
  have := hle hx'
  exact Subgroup.mem_centralizer_singleton_iff.mp this

end R38K

end CFSG.RankThree.PartTwo.Sec21.FF81
