module

public import CFSG.RankThree.PartTwo.Sec20.SimsFinalL2Statements
import CFSG.RankThree.PartTwo.Sec20.Item20Res8ProofL2Cent
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofL2KFact
import CFSG.Dihedral.Glauberman.DicksonMaxCases
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.GroupTheory.OrderBelowSixtySolvable
import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Glauberman.Dickson BenderSuzuki.MatrixGroups

private theorem padicValNat_three_two_pow_sub_one {k : ℕ} (hk : k ≠ 0) (h3 : 3 ∣ 2 ^ k - 1) :
    padicValNat 3 (2 ^ k - 1) = padicValNat 3 k + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' k
  · subst hr
    have hr0 : r ≠ 0 := by omega
    have h4 : (2 : ℕ) ^ (2 * r) = 4 ^ r := by rw [pow_mul]; norm_num
    have hlte := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) ⟨1, rfl⟩ (by norm_num)
      (by norm_num) (by norm_num) hr0
    rw [one_pow] at hlte
    have h33 : padicValNat 3 (4 - 1) = 1 := padicValNat_self (p := 3)
    rw [h4, hlte, h33, padicValNat.mul (by norm_num) hr0,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 2)]
    omega
  · exfalso
    subst hr
    have h2 : 2 ^ (2 * r + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    generalize 2 ^ (2 * r + 1) = a at h2 h3
    omega

private theorem padicValNat_three_two_pow_add_one {k : ℕ} (h3 : 3 ∣ 2 ^ k + 1) :
    padicValNat 3 (2 ^ k + 1) = padicValNat 3 k + 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' k
  · exfalso
    subst hr
    have h1 : 2 ^ (2 * r) % 3 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    generalize 2 ^ (2 * r) = a at h1 h3
    omega
  · have hlte := padicValNat.pow_add_pow (p := 3) (x := 2) (y := 1) ⟨1, rfl⟩ (by norm_num)
      (by norm_num) (⟨r, hr⟩ : Odd k)
    rw [one_pow] at hlte
    have h33 : padicValNat 3 (2 + 1) = 1 := padicValNat_self (p := 3)
    rw [hlte, h33]
    omega

private theorem padicValNat_three_torus {k n : ℕ} (hk : k ≠ 0)
    (hn : n = 2 ^ k - 1 ∨ n = 2 ^ k + 1) (h3 : 3 ∣ n) :
    padicValNat 3 n = padicValNat 3 k + 1 := by
  rcases hn with rfl | rfl
  · exact padicValNat_three_two_pow_sub_one hk h3
  · exact padicValNat_three_two_pow_add_one h3

private theorem sq_add_lt_two_pow {k : ℕ} (hk : 6 ≤ k) : k * k + 3 * k + 1 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    nlinarith

private theorem three_mul_add_one_lt_two_pow {k : ℕ} (hk : 4 ≤ k) : 3 * k + 1 < 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

private theorem three_pow_mul_lt {k j s : ℕ} (hj : 2 ≤ j) (hjk : 2 * j ≤ k) (hs : 3 ^ s ∣ k) :
    3 ^ s * (2 ^ j + 1) < 2 ^ k - 1 := by
  have hjj : 2 ^ j * 2 ^ j ≤ 2 ^ k := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h4 : 4 ≤ 2 ^ j := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  rcases Nat.eq_zero_or_pos s with rfl | hs0
  · have h4j : 4 * 2 ^ j ≤ 2 ^ j * 2 ^ j := Nat.mul_le_mul_right _ h4
    rw [pow_zero, one_mul]
    omega
  · have h3k : 3 ∣ k := (dvd_pow_self 3 hs0.ne').trans hs
    have hk6 : 6 ≤ k := by omega
    have hsk : 3 ^ s ≤ k := Nat.le_of_dvd (by omega) hs
    have hmain : k * (2 ^ j + 1) + 1 < 2 ^ k := by
      rcases lt_or_ge (2 ^ j) (k + 2) with h | h
      · have hsq := sq_add_lt_two_pow hk6
        have h' : k * 2 ^ j ≤ k * (k + 1) := Nat.mul_le_mul_left k (by omega)
        nlinarith
      · have h' : (k + 2) * (2 ^ j + 1) ≤ 2 ^ j * (2 ^ j + 1) := Nat.mul_le_mul_right _ h
        nlinarith
    calc 3 ^ s * (2 ^ j + 1) ≤ k * (2 ^ j + 1) := Nat.mul_le_mul_right _ hsk
      _ < 2 ^ k - 1 := by omega

private theorem le_three_of_two_pow_sub_one_le {k : ℕ} (h : 2 ^ k - 1 ≤ 3 * k) : k ≤ 3 := by
  by_contra hk
  have := three_mul_add_one_lt_two_pow (by omega : 4 ≤ k)
  omega

theorem kFactL2CentThreePrime_holds : KFactL2CentThreePrime := by
  intro m H hperf htop x hxH hx3
  by_contra hcon
  have hC : ∀ g ∈ Subgroup.centralizer ({x} : Set ↥(projSL 2 (GaloisField 2 m))),
      Nat.Coprime (orderOf g) 3 → g ∈ H := by
    intro g hg hg3
    by_contra hgH
    exact hcon ⟨g, hg, hg3, hgH⟩
  clear hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set F := GaloisField 2 m with hFdef
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨k, -, hk⟩ := FiniteField.card F 2
  set kk : ℕ := (k : ℕ) with hkk
  have hFk : Nat.card F = 2 ^ kk := by rw [Nat.card_eq_fintype_card]; exact hk
  have hk1 : 1 ≤ kk := k.pos
  have hq2 : 2 ≤ 2 ^ kk := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ kk := Nat.pow_le_pow_right (by norm_num) hk1
  set P := PSL2MatrixGroup F with hPdef
  set φ : ↥(projSL 2 F) ≃* P := Sec4.projSLEquivPSL F with hφ
  set H' : Subgroup P := H.map φ.toMonoidHom with hH'
  set x' : P := φ x with hx'
  have hperf' : ⁅H', H'⁆ = H' := by
    rw [hH', ← Subgroup.map_commutator, hperf]
  have htop' : H' ≠ ⊤ := by
    intro h
    apply htop
    rw [eq_top_iff]
    intro y _
    have hy : φ y ∈ H' := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨y', hy', hyy'⟩ := hy
    rwa [show y' = y from φ.injective hyy'] at hy'
  have hx'H : x' ∈ H' := ⟨x, hxH, rfl⟩
  have hx'3 : orderOf x' = 3 := by rw [hx', MulEquiv.orderOf_eq]; exact hx3
  have hx'1 : x' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx'3
    norm_num at hx'3
  have hC' : ∀ g ∈ Subgroup.centralizer ({x'} : Set P), Nat.Coprime (orderOf g) 3 → g ∈ H' := by
    intro z hz hz3
    have hy : φ.symm z ∈ Subgroup.centralizer ({x} : Set ↥(projSL 2 F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz
    refine ⟨φ.symm z, hC _ hy ?_, φ.apply_symm_apply z⟩
    rw [MulEquiv.orderOf_eq]
    exact hz3
  have hH'nt : Nontrivial H' := ⟨⟨⟨x', hx'H⟩, 1, fun h => hx'1 (congrArg Subtype.val h)⟩⟩
  have hH'perf : Group.IsPerfect H' := by
    refine ⟨?_⟩
    apply Subgroup.map_injective H'.subtype_injective
    rw [Subgroup.map_subtype_commutator, Subgroup.map_top, Subgroup.range_subtype]
    exact hperf'
  have hns : ¬ Group.IsSolvable H' := fun hs => Group.IsPerfect.not_isSolvable H' hs
  have hgcd : Nat.gcd (Nat.card F - 1) 2 = 1 := by
    rw [hFk]
    have hodd' : Odd (2 ^ kk - 1) := by
      have h2 : Even (2 ^ kk) := (Nat.even_pow' (by omega)).mpr even_two
      obtain ⟨r, hr⟩ := h2
      exact ⟨r - 1, by omega⟩
    exact Nat.Coprime.symm (Nat.coprime_two_left.mpr hodd')
  obtain ⟨P₂⟩ := (inferInstance : Nonempty (Sylow 2 P))
  obtain ⟨U, S, hUc, hUcard, hSc, hScard, hcover⟩ := huppert_II_8_5_a_psl2_cover hFk P₂
  obtain ⟨T, ⟨hxT, hTform⟩, -⟩ := hcover x' hx'1
  have hT : IsCyclic T ∧ (Nat.card T = 2 ^ kk - 1 ∨ Nat.card T = 2 ^ kk + 1) := by
    rcases hTform with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exfalso
      have h2 : IsPGroup 2 ((P₂ : Subgroup P).map (MulAut.conj g).toMonoidHom) :=
        P₂.isPGroup'.map _
      obtain ⟨a, ha⟩ := h2 ⟨x', hxT⟩
      have hdvd : orderOf x' ∣ 2 ^ a := by
        rw [← Subgroup.orderOf_mk x' hxT]
        exact orderOf_dvd_of_pow_eq_one ha
      rw [hx'3] at hdvd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow hdvd)
      omega
    · refine ⟨?_, Or.inl ?_⟩
      · exact isCyclic_of_surjective
          (U.equivMapOfInjective _ (MulAut.conj g).injective).toMonoidHom (MulEquiv.surjective _)
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hUcard, hgcd, Nat.div_one,
          hFk]
    · refine ⟨?_, Or.inr ?_⟩
      · exact isCyclic_of_surjective
          (S.equivMapOfInjective _ (MulAut.conj g).injective).toMonoidHom (MulEquiv.surjective _)
      · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hScard, hgcd, Nat.div_one,
          hFk]
  obtain ⟨hTcyc, hTcard⟩ := hT
  have hTodd : Odd (Nat.card T) := by
    have h2 : Even (2 ^ kk) := (Nat.even_pow' (by omega)).mpr even_two
    obtain ⟨r, hr⟩ := h2
    rcases hTcard with h | h
    · rw [h]
      exact ⟨r - 1, by omega⟩
    · rw [h]
      exact ⟨r, by omega⟩
  have hlow : 2 ^ kk - 1 ≤ Nat.card T := by rcases hTcard with h | h <;> omega
  obtain ⟨g₀, hg₀⟩ := hTcyc.exists_generator
  have hg₀ord : orderOf g₀ = Nat.card T := orderOf_eq_card_of_forall_mem_zpowers hg₀
  have hTcomm : ∀ a ∈ T, ∀ b ∈ T, Commute a b := by
    intro a ha b hb
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ ⟨b, hb⟩)
    have h := (Commute.zpow_zpow_self g₀ i j).eq
    rw [hi, hj] at h
    exact congrArg Subtype.val h
  have h3T : 3 ∣ Nat.card T := by
    have h := orderOf_dvd_natCard (⟨x', hxT⟩ : T)
    rwa [Subgroup.orderOf_mk, hx'3] at h
  have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
  obtain ⟨s, hs⟩ : ∃ s, padicValNat 3 kk = s := ⟨_, rfl⟩
  have hsk : 3 ^ s ∣ kk := by rw [← hs]; exact pow_padicValNat_dvd
  have hv : padicValNat 3 (Nat.card T) = s + 1 := by
    rw [← hs]; exact padicValNat_three_torus (by omega) hTcard h3T
  have hdvd : 3 ^ (s + 1) ∣ Nat.card T := by rw [← hv]; exact pow_padicValNat_dvd
  obtain ⟨n', hnn⟩ := hdvd
  have hn'3 : Nat.Coprime n' 3 := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h
    have h2 : 3 ^ (s + 1 + 1) ∣ Nat.card T := by
      rw [hnn, pow_succ 3 (s + 1)]
      exact Nat.mul_dvd_mul_left _ h
    have := (padicValNat_dvd_iff_le hT0).mp h2
    omega
  obtain ⟨t₁, ht₁⟩ : ∃ t : P, t = ((g₀ ^ 3 ^ (s + 1) : T) : P) := ⟨_, rfl⟩
  have ht₁T : t₁ ∈ T := ht₁ ▸ (g₀ ^ 3 ^ (s + 1)).2
  have ht₁ord : orderOf t₁ = n' := by
    rw [ht₁, Subgroup.orderOf_coe, orderOf_pow_of_dvd (by positivity) ⟨n', hg₀ord.trans hnn⟩,
      hg₀ord, hnn, Nat.mul_div_cancel_left _ (by positivity)]
  have ht₁H : t₁ ∈ H' := hC' t₁
    (Subgroup.mem_centralizer_singleton_iff.mpr (hTcomm _ ht₁T _ hxT).eq) (ht₁ord ▸ hn'3)
  have hzH : x' * t₁ ∈ H' := H'.mul_mem hx'H ht₁H
  have hzord : orderOf (x' * t₁) = 3 * n' := by
    rw [(hTcomm _ hxT _ ht₁T).orderOf_mul_eq_mul_orderOf_of_coprime
      (by rw [hx'3, ht₁ord]; exact hn'3.symm), hx'3, ht₁ord]
  have hZH : Subgroup.zpowers (x' * t₁) ≤ H' := Subgroup.zpowers_le.mpr hzH
  have hZodd : Odd (3 * n') := by
    have hT : Odd (3 ^ (s + 1) * n') := by rw [← hnn]; exact hTodd
    exact Odd.mul ⟨1, rfl⟩ (Odd.of_dvd_nat hT (dvd_mul_left n' _))
  have hZcard' : ∀ (Q : Type) [Group Q] (e : ↥H' ≃* Q),
      Nat.card (((Subgroup.zpowers (x' * t₁)).subgroupOf H').map e.toMonoidHom) = 3 * n' := by
    intro Q _ e
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv, Nat.card_zpowers, hzord]
  have hlow' : 2 ^ kk - 1 ≤ 3 ^ s * (3 * n') := by
    calc 2 ^ kk - 1 ≤ Nat.card T := hlow
      _ = 3 ^ s * (3 * n') := by rw [hnn, pow_succ, mul_assoc]
  have hPcard : Nat.card P = 2 ^ kk * ((2 ^ kk) ^ 2 - 1) := by
    rw [Nat.card_congr (Res6.pslEquivPgl_of_char_two F hchar).toEquiv,
      CFSG.GorensteinWalter.pgl2_card_formula, hFk]
  have hcardL : ∀ m' : ℕ, m' ≠ 0 → (↥H' ≃* PSL2MatrixGroup (GaloisField 2 m')) →
      Nat.card H' = 2 ^ m' * ((2 ^ m') ^ 2 - 1) := by
    intro m' hm' e
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (Res6.pslEquivPgl_of_char_two
      (GaloisField 2 m') (ringChar.eq _ 2)).toEquiv, CFSG.GorensteinWalter.pgl2_card_formula,
      GaloisField.card 2 m' hm']
  have key : ∀ m' : ℕ, m' ≠ 0 → 2 * m' ≤ kk →
      (↥H' ≃* PSL2MatrixGroup (GaloisField 2 m')) → False := by
    intro m' hm' hle e
    have hF' : Nat.card (GaloisField 2 m') = 2 ^ m' := GaloisField.card 2 m' hm'
    by_cases hm1 : m' = 1
    · subst hm1
      apply hns
      apply CFSG.GroupTheory.groups_order_below_sixty_solvable
      rw [hcardL 1 one_ne_zero e]
      norm_num
    ·
      have hbound := Res8.card_le_of_odd_psl2_char_two hF'
        (((Subgroup.zpowers (x' * t₁)).subgroupOf H').map e.toMonoidHom)
        (by rw [hZcard' _ e]; exact hZodd)
      rw [hZcard' _ e] at hbound
      have hlt := three_pow_mul_lt (by omega : 2 ≤ m') hle hsk
      have hle' : 3 ^ s * (3 * n') ≤ 3 ^ s * (2 ^ m' + 1) := Nat.mul_le_mul_left _ hbound
      omega
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification (p := 2) hFk H' with
    hEA | ⟨z, -, -, hcyc⟩ | ⟨z, -, hzc, ⟨hd⟩⟩ | ⟨-, ⟨ha4⟩⟩ | ⟨-, ⟨hs4⟩⟩ | ⟨-, ⟨ha5⟩⟩ |
      ⟨m', t, -, -, N₀, C, hN₀n, hN₀e, -, hCc, -, -, hN₀C⟩ | ⟨m', hm', hm'k, ⟨e⟩⟩ |
      ⟨m', hm', hm'k, ⟨e⟩⟩
  · exact hns (Group.isSolvable_of_comm fun a b => hEA.toIsMulCommutative.is_comm.comm a b)
  · obtain ⟨g, hg⟩ := hcyc.exists_generator
    refine hns (Group.isSolvable_of_comm fun a b => ?_)
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    exact (Commute.zpow_zpow_self g i j).eq
  · have hz : z ≠ 0 := by
      rintro rfl
      have := Nat.card_pos (α := H')
      rw [hzc] at this
      simp at this
    have : NeZero z := ⟨hz⟩
    have := CFSG.LinearGroups.isSolvable_dihedralGroup z
    exact hns (Group.isSolvable_of_surjective (f := hd.symm.toMonoidHom) (MulEquiv.surjective _))
  · have : Group.IsSolvable (alternatingGroup (Fin 4)) := alternatingGroup.isSolvable (by simp)
    exact hns (Group.isSolvable_of_surjective (f := ha4.symm.toMonoidHom)
      (MulEquiv.surjective _))
  · have : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    exact hns (Group.isSolvable_of_surjective (f := hs4.symm.toMonoidHom)
      (MulEquiv.surjective _))
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e5⟩ := MaxCases.nonempty_psl2_galoisField_five
    have hbound := Res8.card_le_five_of_odd_psl2_five
      (((Subgroup.zpowers (x' * t₁)).subgroupOf H').map (ha5.trans e5.symm).toMonoidHom)
      (by rw [hZcard' _ (ha5.trans e5.symm)]; exact hZodd)
    rw [hZcard' _ (ha5.trans e5.symm)] at hbound
    have hsk' : 3 ^ s ≤ kk := Nat.le_of_dvd (by omega) hsk
    have h3k : 2 ^ kk - 1 ≤ 3 * kk := by
      calc 2 ^ kk - 1 ≤ 3 ^ s * (3 * n') := hlow'
        _ ≤ 3 ^ s * (3 * 1) := Nat.mul_le_mul_left _ (by omega)
        _ = 3 ^ s * 3 := by rw [mul_one]
        _ ≤ kk * 3 := Nat.mul_le_mul_right 3 hsk'
        _ = 3 * kk := mul_comm _ _
    have hk3 := le_three_of_two_pow_sub_one_le h3k
    have h60 : Nat.card H' = 60 := by
      rw [Nat.card_congr ha5.toEquiv, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card]
      rfl
    have hdvd60 : 60 ∣ 2 ^ kk * ((2 ^ kk) ^ 2 - 1) := by
      rw [← h60, ← hPcard]
      exact Subgroup.card_subgroup_dvd_card H'
    have hk2 : kk = 2 := by
      rcases (by omega : kk = 1 ∨ kk = 2 ∨ kk = 3) with h | h | h
      · rw [h] at hdvd60
        norm_num at hdvd60
      · exact h
      · rw [h] at hdvd60
        norm_num at hdvd60
    exact htop' (Subgroup.eq_top_of_card_eq H' (by rw [h60, hPcard, hk2]; norm_num))
  · exact hns (Res6.isSolvable_of_semidirect hN₀n hN₀e.toIsMulCommutative hCc hN₀C)
  ·
    by_cases hmk : m' = kk
    · subst hmk
      exact htop' (Subgroup.eq_top_of_card_eq H' (by rw [hcardL _ hm' e, hPcard]))
    · obtain ⟨r, hr⟩ := hm'k
      have hr2 : 2 ≤ r := by
        rcases Nat.lt_or_ge r 2 with h | h
        · interval_cases r
          · omega
          · exact absurd (by rw [hr, mul_one]) hmk
        · exact h
      exact key m' hm' (by rw [hr]; exact Nat.mul_le_mul_left m' hr2 |>.trans_eq' (by ring)) e
  · exact key m' hm' (Nat.le_of_dvd (by omega) hm'k)
      (e.trans (Res6.pslEquivPgl_of_char_two (GaloisField 2 m') (ringChar.eq _ 2)).symm)

end CFSG.RankThree.PartTwo.Sec20
