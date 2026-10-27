module

public import CFSG.Quasithin.Background.HNPrimeHall
public import CFSG.Quasithin.H13.A5M22HatAut
public import CFSG.Quasithin.H13.A5M12Chain
public import Certificates.Certificate7119
public import Certificates.Certificate7120

public section

namespace CFSG.Quasithin.H.MathieuLat

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat CFSG.Quasithin.H13.A5.M12
open CFSG.Quasithin.H.NPrimeHall CFSG.Quasithin.E3 CFSG.Monster.Code
open scoped Pointwise

theorem y22_cert :
    inAutOK y22 = true ∧ y22[0]! = 0 ∧ y22[1]! = 1 ∧ permThreeOK T22s2 y22 = true :=
  Certificates.certificate7119

theorem y12_cert :
    inAutOK y12 = true ∧ okPair y12 (invArr y12) = true ∧ permThreeOK T12s2 y12 = true :=
  Certificates.certificate7120

section Table

variable (T : PT 24) [Fact (T.check = true)]

abbrev ptRange : Subgroup (Equiv.Perm (Fin 24)) := T.toPerm.range

omit [Fact (T.check = true)] in
theorem eq_of_hasArr {σ τ : Equiv.Perm (Fin 24)} {a : Array ℕ} (hσ : HasArr σ a)
    (hτ : HasArr τ a) : σ = τ :=
  Equiv.ext fun i => Fin.ext ((hσ i).trans (hτ i).symm)

theorem mem_ptRange_of_contains {x : Array ℕ} (hx : T.elems.contains x = true)
    {σ : Equiv.Perm (Fin 24)} (hσ : HasArr σ x) : σ ∈ ptRange T := by
  obtain ⟨i, hi, hix⟩ := Array.mem_iff_getElem.mp (Array.contains_iff_mem.mp hx)
  have hin : i < T.n := by rwa [← T.size_elems]
  refine ⟨⟨i, hin⟩, ?_⟩
  rw [PT.toPerm_apply]
  refine eq_of_hasArr (T.hasArr_perm _) ?_
  have : T.arr ⟨i, hin⟩ = x := by
    rw [PT.arr, getElem!_pos T.elems i hi]
    exact hix
  rw [this]
  exact hσ

theorem permute_of_permThreeOK {a : Array ℕ} (h : permThreeOK T a = true) (hsize : a.size = 24)
    {y : Equiv.Perm (Fin 24)} (hy : HasArr y a) (hyi : HasArr y⁻¹ (invArr a)) :
    orderOf y = 3 ∧
      (Subgroup.zpowers y : Set (Equiv.Perm (Fin 24))) * ptRange T =
        ptRange T * Subgroup.zpowers y := by
  simp only [permThreeOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at h
  obtain ⟨⟨h3, h1⟩, hall⟩ := h
  have hy3 : y ^ 3 = 1 := by
    have := hasArr_pow hy 3
    rw [h3] at this
    exact eq_of_hasArr this hasArr_one_id24
  have hy1 : y ≠ 1 := by
    rintro rfl
    apply h1
    apply Array.ext
    · rw [hsize]
      simp [id24]
    · intro i hi _
      have h' := hy ⟨i, by omega⟩
      rw [getElem!_pos a i hi] at h'
      rw [← h']
      simp [id24]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  refine ⟨hord, ?_⟩
  have hstep : ∀ s ∈ ptRange T, y * s ∈ (ptRange T : Set (Equiv.Perm (Fin 24))) *
      (Subgroup.zpowers y : Set (Equiv.Perm (Fin 24))) := by
    rintro _ ⟨p, rfl⟩
    rw [PT.toPerm_apply]
    have harr := T.hasArr_perm p
    have hp := hall p.idx p.lt
    have hdef : T.arr p = T.elems[p.idx]! := rfl
    rw [← hdef] at hp
    rcases hp with (hp | hp) | hp
    · exact ⟨_, mem_ptRange_of_contains T hp (hasArr_mul hy harr), 1, Subgroup.one_mem _,
        mul_one _⟩
    · refine ⟨_, mem_ptRange_of_contains T hp (hasArr_mul (hasArr_mul hy harr) hyi), y,
        Subgroup.mem_zpowers y, ?_⟩
      change y * T.perm p * y⁻¹ * y = y * T.perm p
      group
    · refine ⟨_, mem_ptRange_of_contains T hp (hasArr_mul (hasArr_mul hy harr)
        (hasArr_pow hyi 2)), y ^ 2, Subgroup.pow_mem _ (Subgroup.mem_zpowers y) 2, ?_⟩
      change y * T.perm p * y⁻¹ ^ 2 * y ^ 2 = y * T.perm p
      group
  have hpow : ∀ n : ℕ, ∀ s ∈ ptRange T, y ^ n * s ∈ (ptRange T : Set (Equiv.Perm (Fin 24))) *
      (Subgroup.zpowers y : Set (Equiv.Perm (Fin 24))) := by
    intro n
    induction n with
    | zero => intro s hs; exact ⟨s, hs, 1, Subgroup.one_mem _, by simp⟩
    | succ n ih =>
      intro s hs
      obtain ⟨s', hs', z, hz, he⟩ := ih s hs
      obtain ⟨s'', hs'', z', hz', he'⟩ := hstep s' hs'
      refine ⟨s'', hs'', z' * z, Subgroup.mul_mem _ hz' hz, ?_⟩
      have he1 : s' * z = y ^ n * s := he
      have he2 : s'' * z' = y * s' := he'
      rw [pow_succ', mul_assoc, ← he1, ← mul_assoc, ← he2, mul_assoc]
  apply (SL3Pair.mul_comm_of_subset _).symm
  rintro _ ⟨z, hz, s, hs, rfl⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hk : y ^ k = y ^ (k % 3).toNat := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3, zpow_add, zpow_mul]
    rw [show y ^ (3 : ℤ) = 1 by rw [zpow_ofNat, hy3], one_zpow, mul_one]
  rw [hk]
  exact hpow _ s hs

theorem two_le_nPrime_of_permThreeOK {X : Subgroup (Equiv.Perm (Fin 24))}
    (hTX : IsSylowIn 2 (ptRange T) X) {a : Array ℕ} (h : permThreeOK T a = true)
    (hsize : a.size = 24) {y : Equiv.Perm (Fin 24)} (hy : HasArr y a)
    (hyi : HasArr y⁻¹ (invArr a)) (hyX : y ∈ X) : 2 ≤ nPrime X := by
  obtain ⟨hord, hperm⟩ := permute_of_permThreeOK T h hsize hy hyi
  have hcard : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hord]
  refine le_nPrime le_rfl ((Subgroup.zpowers_le).mpr hyX) inferInstance
    (by rw [hcard]; norm_num) (fun u hu v hv => ?_) (by rw [hcard]; decide) hTX hperm
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  rw [← zpow_add, ← zpow_add, add_comm]

theorem isSylowIn_ptRange {X : Subgroup (Equiv.Perm (Fin 24))} (hTX : ptRange T ≤ X) {k m : ℕ}
    (hT : T.n = 2 ^ k) (hX : Nat.card X = 2 ^ k * m) (hm : Odd m) :
    IsSylowIn 2 (ptRange T) X := by
  have hcard : Nat.card (ptRange T) = 2 ^ k := by
    rw [← hT, ← PT.card_elem]
    exact Nat.card_congr (MonoidHom.ofInjective T.toPerm_injective).toEquiv.symm
  refine ⟨hTX, IsPGroup.of_card hcard, ?_⟩
  have h1 := Subgroup.relIndex_mul_card (H := ptRange T) (K := X)
  rw [inf_of_le_left hTX, hcard, hX, mul_comm] at h1
  have h2 : (ptRange T).relIndex X = m := Nat.eq_of_mul_eq_mul_left (by positivity) h1
  rw [h2]
  exact fun h => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)

end Table

theorem mog22plus_two_le_nPrime :
    2 ≤ nPrime mog22plus := by
  obtain ⟨hok, h0, h1, hperm⟩ := y22_cert
  simp only [inAutOK, Bool.and_eq_true] at hok
  have hTX : ptRange T22s2 ≤ mog22plus := by
    rintro _ ⟨p, rfl⟩
    exact T22s2.mem_mog22plus T22s2_ok.2.2 p
  have hS := isSylowIn_ptRange T22s2 hTX (k := 8) (m := 3465) (by rw [T22s2_ok.2.1]; norm_num)
    (by rw [card_mog22plus]; norm_num) (by decide)
  have hy := hasArr_permOfArr hok.1
  refine two_le_nPrime_of_permThreeOK T22s2 hS hperm rfl hy (hasArr_permOfArr_inv hok.1) ?_
  exact mog22_le_mog22plus (mem_mog22_of_arr (mem_AutPerm_of_arr hok.1 hok.2) hy h0 h1)

theorem m24Pair_two_le_nPrime :
    2 ≤ nPrime m24Pair := by
  obtain ⟨hok, hpair, hperm⟩ := y12_cert
  simp only [inAutOK, Bool.and_eq_true] at hok
  have hTX : ptRange T12s2 ≤ m24Pair := by
    rintro _ ⟨p, rfl⟩
    exact mem_m24Pair_of_allOK T12s2 T12s2_ok.2.2 p
  have hS := isSylowIn_ptRange T12s2 hTX (k := 7) (m := 1485) (by rw [T12s2_ok.2.1]; norm_num)
    (by rw [card_m24Pair]; norm_num) (by decide)
  have hy := hasArr_permOfArr hok.1
  refine two_le_nPrime_of_permThreeOK T12s2 hS hperm rfl hy (hasArr_permOfArr_inv hok.1) ?_
  simp only [okPair, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hpair
  refine ⟨mem_AutPerm_of_arr hok.1 hpair.1, ?_⟩
  rcases hpair.2 with h0 | h1
  · exact Or.inl (permAct_dodecadE_of_arr hy h0)
  · right
    rw [permAct_dodecadE_of_arr hy h1, bvec_compl]
    rfl

end CFSG.Quasithin.H.MathieuLat
