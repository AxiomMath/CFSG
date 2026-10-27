module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1510Setup
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem bpow_mul_sq_pow_two {b s : G} (hbs : Commute b s) (hb3 : b ^ 3 = 1)
    (hs3 : s ^ 3 = 1) (k : ℕ) : b ^ k * (b ^ k * s ^ 2) ^ 2 = s := by
  have hcomm : Commute (b ^ k) (s ^ 2) := (hbs.pow_left k).pow_right 2
  have hs4 : s ^ 4 = s := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hs3, one_mul, pow_one]
  rw [hcomm.mul_pow, ← pow_mul, ← pow_mul,
    ← mul_assoc (b ^ k) (b ^ (k * 2)) (s ^ (2 * 2)), ← pow_add]
  have hbexp : k + k * 2 = 3 * k := by ring
  rw [hbexp, pow_mul b 3 k, hb3, one_pow, one_mul,
    show (2 : ℕ) * 2 = 4 by norm_num, hs4]

private theorem orders_and_sup_of_notMem {S : Subgroup G} {b s : G}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS9 : Nat.card S = 9)
    (hexp : ∀ x ∈ S, x ^ 3 = 1) (hbS : b ∈ S) (hb1 : b ≠ 1)
    (hsS : s ∈ S) (hsb : s ∉ Subgroup.zpowers b) :
    orderOf s = 3 ∧ S = Subgroup.zpowers b ⊔ Subgroup.zpowers s ∧
      Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  have hs1 : s ≠ 1 := fun h => hsb (h ▸ Subgroup.one_mem _)
  have hb3 : b ^ 3 = 1 := hexp b hbS
  have hs3 : s ^ 3 = 1 := hexp s hsS
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hob : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hos : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hbcard : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hob]
  have hscard : Nat.card (Subgroup.zpowers s) = 3 := by rw [Nat.card_zpowers, hos]
  have hcent : Subgroup.zpowers s ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x (Subgroup.zpowers_le.mpr hsS hx) y
      (Subgroup.zpowers_le.mpr hbS hy)).symm
  have hnormal : Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hdisj : Disjoint (Subgroup.zpowers b) (Subgroup.zpowers s) := by
    rw [disjoint_iff]
    apply Subgroup.eq_bot_of_card_eq
    have hdvd : Nat.card (Subgroup.zpowers b ⊓ Subgroup.zpowers s : Subgroup G) ∣ 3 := by
      simpa [hbcard] using
        Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers b ⊓ Subgroup.zpowers s ≤
          Subgroup.zpowers b)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exfalso
      have hinf : Subgroup.zpowers b ⊓ Subgroup.zpowers s = Subgroup.zpowers b := by
        apply Subgroup.eq_of_le_of_card_ge inf_le_left
        rw [hbcard, h]
      have hle : Subgroup.zpowers b ≤ Subgroup.zpowers s := hinf ▸ inf_le_right
      have heq : Subgroup.zpowers b = Subgroup.zpowers s := by
        apply Subgroup.eq_of_le_of_card_ge hle
        rw [hscard, hbcard]
      exact hsb (by rw [heq]; exact Subgroup.mem_zpowers s)
  have hsupcard : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers s : Subgroup G) = 9 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnormal hdisj,
      hbcard, hscard]
  have hsupS : Subgroup.zpowers b ⊔ Subgroup.zpowers s ≤ S :=
    sup_le (Subgroup.zpowers_le.mpr hbS) (Subgroup.zpowers_le.mpr hsS)
  have hSeq : S = Subgroup.zpowers b ⊔ Subgroup.zpowers s :=
    (Subgroup.eq_of_le_of_card_ge hsupS (by rw [hS9, hsupcard])).symm
  exact ⟨hos, hSeq, hnormal⟩

private theorem exists_pow_mul_pow_of_mem_normalizer {S : Subgroup G} {b s u : G}
    (hseq : S = Subgroup.zpowers b ⊔ Subgroup.zpowers s)
    (hnormal : Subgroup.zpowers s ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G))
    (hos : orderOf s = 3) (hu : u ∈ Subgroup.normalizer (S : Set G)) (hsS : s ∈ S) :
    ∃ k j : ℕ, j < 3 ∧ u * s * u⁻¹ = b ^ k * s ^ j := by
  classical
  have hmemS : u * s * u⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hu s).mp hsS
  have hmemT : u * s * u⁻¹ ∈ (Subgroup.zpowers b : Set G) *
      (Subgroup.zpowers s : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (Subgroup.zpowers b)
      (Subgroup.zpowers s) hnormal, ← hseq]
    exact hmemS
  obtain ⟨p, hp, q, hq, hpq⟩ := hmemT
  obtain ⟨k, -, hkp⟩ := Finset.mem_image.mp
    ((mem_zpowers_iff_mem_range_orderOf (x := b) (y := p)).mp hp)
  obtain ⟨j, hj, hjq⟩ := Finset.mem_image.mp
    ((mem_zpowers_iff_mem_range_orderOf (x := s) (y := q)).mp hq)
  have hj3 : j < 3 := by rw [hos] at hj; simpa using hj
  rw [← hkp, ← hjq] at hpq
  exact ⟨k, j, hj3, hpq.symm⟩

private theorem false_of_conj_eq_bpow_mul_sq {b s u : G} {k : ℕ}
    (hrep : u * s * u⁻¹ = b ^ k * s ^ 2) (hsb : s ∉ Subgroup.zpowers b)
    (hu3 : u ^ 3 = 1) (hub : u * b = b * u) (hbs : Commute b s)
    (hb3 : b ^ 3 = 1) (hs3 : s ^ 3 = 1) : False := by
  have hconjb : u * b * u⁻¹ = b := by rw [hub]; group
  have hconjbk : u * b ^ k * u⁻¹ = b ^ k := by rw [← conj_pow, hconjb]
  have hφ2 : u ^ 2 * s * (u ^ 2)⁻¹ = s := by
    calc u ^ 2 * s * (u ^ 2)⁻¹ = u * (u * s * u⁻¹) * u⁻¹ := by
          rw [pow_two, mul_inv_rev]
          group
      _ = u * (b ^ k * s ^ 2) * u⁻¹ := by rw [hrep]
      _ = (u * b ^ k * u⁻¹) * (u * s ^ 2 * u⁻¹) := by group
      _ = b ^ k * (u * s * u⁻¹) ^ 2 := by rw [hconjbk, ← conj_pow]
      _ = b ^ k * (b ^ k * s ^ 2) ^ 2 := by rw [hrep]
      _ = s := bpow_mul_sq_pow_two hbs hb3 hs3 k
  have hφs : u * s * u⁻¹ = s := by
    calc u * s * u⁻¹ = u * (u ^ 2 * s * (u ^ 2)⁻¹) * u⁻¹ := by rw [hφ2]
      _ = u ^ 3 * s * (u ^ 3)⁻¹ := by group
      _ = s := by simp [hu3]
  have hEq : s = b ^ k * s ^ 2 := hφs.symm.trans hrep
  have hs2s : s ^ 2 * s⁻¹ = s := by rw [pow_two, mul_assoc, mul_inv_cancel, mul_one]
  have hbk_s : b ^ k * s = 1 := by
    have h := congrArg (fun t => t * s⁻¹) hEq
    rw [mul_assoc, hs2s, mul_inv_cancel] at h
    exact h.symm
  have hs_eq : s = (b ^ k)⁻¹ := eq_inv_of_mul_eq_one_right hbk_s
  exact hsb (by
    rw [hs_eq]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k))

private theorem commutator_mem_zpowers_of_rep {b s u : G} {k j : ℕ}
    (hrep : u * s * u⁻¹ = b ^ k * s ^ j) (hj3 : j < 3)
    (hsb : s ∉ Subgroup.zpowers b) (hu3 : u ^ 3 = 1) (hub : u * b = b * u)
    (hbs : Commute b s) (hb3 : b ^ 3 = 1) (hs3 : s ^ 3 = 1) :
    u * s * u⁻¹ * s⁻¹ ∈ Subgroup.zpowers b := by
  have hcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · subst h0
    simp only [pow_zero, mul_one] at hrep
    have hconjb : u * b * u⁻¹ = b := by rw [hub]; group
    have hconjbk : u * b ^ k * u⁻¹ = b ^ k := by rw [← conj_pow, hconjb]
    have hconjbk' : u⁻¹ * b ^ k * u = b ^ k := by
      calc u⁻¹ * b ^ k * u = u⁻¹ * (u * b ^ k * u⁻¹) * u := by rw [hconjbk]
        _ = b ^ k := by group
    have hs_eq : s = b ^ k := by
      calc s = u⁻¹ * (u * s * u⁻¹) * u := by group
        _ = u⁻¹ * b ^ k * u := by rw [hrep]
        _ = b ^ k := hconjbk'
    exfalso
    exact hsb (by rw [hs_eq]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k)
  · subst h1
    simp only [pow_one] at hrep
    rw [hrep, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers b) k
  · subst h2
    have hrep' : u * s * u⁻¹ = b ^ k * s ^ 2 := by simpa using hrep
    exact (false_of_conj_eq_bpow_mul_sq hrep' hsb hu3 hub hbs hb3 hs3).elim

private theorem commutator_mem_zpowers_of_normalizes {S : Subgroup G} {b u : G}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hS9 : Nat.card S = 9)
    (hexp : ∀ x ∈ S, x ^ 3 = 1) (hbS : b ∈ S) (hb1 : b ≠ 1)
    (hu : u ∈ Subgroup.normalizer (S : Set G)) (hu3 : u ^ 3 = 1) (hub : u * b = b * u) :
    ∀ s ∈ S, u * s * u⁻¹ * s⁻¹ ∈ Subgroup.zpowers b := by
  classical
  intro s hsS
  by_cases hsb : s ∈ Subgroup.zpowers b
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsb
    have hcommu : u * s = s * u := by
      rw [← hk]
      exact (Commute.zpow_right (show Commute u b from hub) k).eq
    rw [hcommu]
    simp
  · obtain ⟨hos, hseq, hnormal⟩ :=
      orders_and_sup_of_notMem hcomm hS9 hexp hbS hb1 hsS hsb
    obtain ⟨k, j, hj3, hrep⟩ :=
      exists_pow_mul_pow_of_mem_normalizer hseq hnormal hos hu hsS
    exact commutator_mem_zpowers_of_rep hrep hj3 hsb hu3 hub
      (hcomm b hbS s hsS) (hexp b hbS) (hexp s hsS)

private theorem forall_commutator_mem_of_generators {P A N : Subgroup G} {y v : G}
    (hP : P = A ⊔ Subgroup.zpowers y)
    (hNcent : ∀ n ∈ N, ∀ p ∈ P, n * p = p * n)
    (hgen : ∀ x ∈ ((A : Set G) ∪ {y}), ⁅x, v⁆ ∈ N) :
    ∀ u ∈ P, ⁅u, v⁆ ∈ N := by
  classical
  have hPcl : P = Subgroup.closure ((A : Set G) ∪ {y}) := by
    have h : Subgroup.closure ((A : Set G) ∪ {y}) = A ⊔ Subgroup.zpowers y := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, ← Subgroup.zpowers_eq_closure y]
    rw [hP, ← h]
  intro u hu
  rw [hPcl] at hu
  refine Subgroup.closure_induction (p := fun u _ => ⁅u, v⁆ ∈ N) ?_ ?_ ?_ ?_ hu
  · intro x hx
    exact hgen x hx
  · simp [commutatorElement_def]
  · intro x z hx hz hpx hpz
    have hxP : x ∈ P := hPcl.symm ▸ hx
    have hzP : z ∈ P := hPcl.symm ▸ hz
    have hcz : x * ⁅z, v⁆ * x⁻¹ = ⁅z, v⁆ := by
      have hcomm := hNcent ⁅z, v⁆ hpz x hxP
      calc x * ⁅z, v⁆ * x⁻¹ = ⁅z, v⁆ * x * x⁻¹ := by rw [← hcomm]
        _ = ⁅z, v⁆ := by group
    have hcalc : ⁅x * z, v⁆ = ⁅z, v⁆ * ⁅x, v⁆ := by
      calc ⁅x * z, v⁆ = x * ⁅z, v⁆ * x⁻¹ * ⁅x, v⁆ := by
            rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
            group
        _ = ⁅z, v⁆ * ⁅x, v⁆ := by rw [hcz]
    rw [hcalc]
    exact N.mul_mem hpz hpx
  · intro x hx hpx
    have hxP : x ∈ P := hPcl.symm ▸ hx
    have hcommx : ⁅x, v⁆ * x = x * ⁅x, v⁆ := hNcent ⁅x, v⁆ hpx x hxP
    have hxv : x * v * x⁻¹ = ⁅x, v⁆ * v := by
      rw [commutatorElement_def]
      group
    have h1 : v = ⁅x, v⁆ * (x⁻¹ * v * x) := by
      calc v = x⁻¹ * (x * v * x⁻¹) * x := by group
        _ = x⁻¹ * (⁅x, v⁆ * v) * x := by rw [hxv]
        _ = (x⁻¹ * ⁅x, v⁆ * x) * (x⁻¹ * v * x) := by group
        _ = ⁅x, v⁆ * (x⁻¹ * v * x) := by
            have hcx : x⁻¹ * ⁅x, v⁆ * x = ⁅x, v⁆ := by
              calc x⁻¹ * ⁅x, v⁆ * x = x⁻¹ * (⁅x, v⁆ * x) := by group
                _ = x⁻¹ * (x * ⁅x, v⁆) := by rw [hcommx]
                _ = ⁅x, v⁆ := by group
            rw [hcx]
    have h2 : x⁻¹ * v * x = ⁅x, v⁆⁻¹ * v := by
      calc x⁻¹ * v * x = ⁅x, v⁆⁻¹ * (⁅x, v⁆ * (x⁻¹ * v * x)) := by group
        _ = ⁅x, v⁆⁻¹ * v := by rw [← h1]
    have hcalc : ⁅x⁻¹, v⁆ = ⁅x, v⁆⁻¹ := by
      calc ⁅x⁻¹, v⁆ = x⁻¹ * v * (x⁻¹)⁻¹ * v⁻¹ := by rw [commutatorElement_def]
        _ = x⁻¹ * v * x * v⁻¹ := by rw [inv_inv]
        _ = (⁅x, v⁆⁻¹ * v) * v⁻¹ := by rw [h2]
        _ = ⁅x, v⁆⁻¹ := by group
    rw [hcalc]
    exact N.inv_mem hpx

private theorem commutator_mem_zpowers_of_mem_A {A S : Subgroup G} {c y b : G}
    (hA : A = Subgroup.zpowers c ⊔ S)
    (hAcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x)
    (hyc : y * c = c * y)
    (hS9 : Nat.card S = 9) (hSexp : ∀ x ∈ S, x ^ 3 = 1)
    (hScomm : ∀ x ∈ S, ∀ z ∈ S, x * z = z * x)
    (hbS : b ∈ S) (hb1 : b ≠ 1)
    (hyS : y ∈ Subgroup.normalizer (S : Set G)) (hy3 : y ^ 3 = 1)
    (hyb : y * b = b * y)
    (hNcent : ∀ n ∈ Subgroup.zpowers b, ∀ p ∈ A, n * p = p * n) :
    ∀ a ∈ A, ⁅a, y⁆ ∈ Subgroup.zpowers b := by
  intro a ha
  have hcA : c ∈ A := by rw [hA]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hSN : Subgroup.zpowers c ≤ Subgroup.normalizer (S : Set G) := by
    refine (show Subgroup.zpowers c ≤ Subgroup.centralizer (S : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hAcomm x (by rw [hA]; exact Subgroup.mem_sup_left hx)
      z (by rw [hA]; exact Subgroup.mem_sup_right hz)).symm
  have hmem : a ∈ (Subgroup.zpowers c : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) S hSN, ← hA]
    exact ha
  obtain ⟨p, hp, s, hs, hps⟩ := hmem
  have hpy : p * y = y * p := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [← hi]
    exact (Commute.zpow_left (show Commute c y from hyc.symm) i).eq
  have hpy1 : ⁅p, y⁆ = 1 := by rw [commutatorElement_def, hpy]; group
  have hform : ⁅p * s, y⁆ = p * ⁅s, y⁆ * p⁻¹ * ⁅p, y⁆ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  have hsy : ⁅s, y⁆ ∈ Subgroup.zpowers b := by
    have h := commutator_mem_zpowers_of_normalizes hScomm hS9 hSexp hbS hb1 hyS hy3 hyb s hs
    have h' : ⁅y, s⁆ ∈ Subgroup.zpowers b := by
      simpa [commutatorElement_def] using h
    have := (Subgroup.zpowers b).inv_mem h'
    rwa [commutatorElement_inv y s] at this
  have hcent := hNcent ⁅s, y⁆ hsy p (by rw [hA]; exact Subgroup.mem_sup_left hp)
  have hEq : p * ⁅s, y⁆ * p⁻¹ = ⁅s, y⁆ := by
    calc p * ⁅s, y⁆ * p⁻¹ = ⁅s, y⁆ * p * p⁻¹ := by rw [← hcent]
      _ = ⁅s, y⁆ := by group
  rw [← hps, hform, hpy1, mul_one, hEq]
  exact hsy

private theorem notMem_A_of_houter {A L P S : Subgroup G} {c y : G}
    (hA : A = Subgroup.zpowers c ⊔ S) (hSA : S ≤ A)
    (hAcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x)
    (hcL : L ≤ Subgroup.centralizer ({c} : Set G))
    (hAP : A ≤ P) (hyP : y ∈ P)
    (houter : ∀ s ∈ S, s⁻¹ * y ∉ Late.sectionCentralizer P L
      (inSubgroup (aschbacherSolvableCore 3) L)) :
    y ∉ A := by
  intro hyA
  have hcP : c ∈ P := hAP (by rw [hA]; exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
  have hSN : Subgroup.zpowers c ≤ Subgroup.normalizer (S : Set G) := by
    refine (show Subgroup.zpowers c ≤ Subgroup.centralizer (S : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hAcomm x (by rw [hA]; exact Subgroup.mem_sup_left hx) z (hSA hz)).symm
  have hmem : y ∈ (Subgroup.zpowers c : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers c) S hSN, ← hA]
    exact hyA
  obtain ⟨p, hp, s, hs, hps⟩ := hmem
  have hpA : p ∈ A := by rw [hA]; exact Subgroup.mem_sup_left hp
  have hsA : s ∈ A := hSA hs
  have hsAinv : s⁻¹ ∈ A := A.inv_mem hsA
  have hsp : s⁻¹ * p = p * s⁻¹ := hAcomm s⁻¹ hsAinv p hpA
  have hsp' : s⁻¹ * y = p := by
    rw [← hps]
    calc s⁻¹ * (p * s) = (s⁻¹ * p) * s := by group
      _ = (p * s⁻¹) * s := by rw [hsp]
      _ = p := by group
  have hpK : p ∈ Late.sectionCentralizer P L
      (inSubgroup (aschbacherSolvableCore 3) L) := by
    refine ⟨hAP hpA, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hp
    have hcx : c * x = x * c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hcL hx)).symm
    have hpx : p * x = x * p := by
      rw [← hi]
      exact (Commute.zpow_left (show Commute c x from hcx) i).eq
    rw [hpx]
    group
    exact Subgroup.one_mem _
  exact houter s hs (hsp' ▸ hpK)

private theorem card_dvd_81_of_isSylowOf {B L P : Subgroup G} {c : G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G)))
    (hcB : c ∈ B)
    (hcN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hc3 : Nat.card (Subgroup.zpowers c) = 3)
    (hK : ∀ k ∈ Late.sectionCentralizer P L
      (inSubgroup (aschbacherSolvableCore 3) L), k ∈ Subgroup.zpowers c)
    (hcard : ∀ R : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)),
      IsPGroup 3 R → Nat.card R ∣ 27) :
    Nat.card P ∣ 81 := by
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hP.le hx) c hcB).symm
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := hPc.trans hcN
  have hsub : (P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ≤ Subgroup.zpowers c := by
    intro x hx
    apply hK x
    change x ∈ Late.sectionCentralizer P L
      (Subgroup.map L.subtype (aschbacherSolvableCore 3 ↥L))
    rw [Sec13.sectionCentralizer_eq_inf hPN]
    exact hx
  have hfirst : Nat.card (P ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) ∣ 3 := by
    have := Subgroup.card_dvd_of_le hsub
    rwa [hc3] at this
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have h1 : IsPGroup 3 ((P ⊓ Subgroup.normalizer (L : Set G)).subgroupOf
      (Subgroup.normalizer (L : Set G))) :=
    (hP3.to_le (inf_le_left : P ⊓ Subgroup.normalizer (L : Set G) ≤ P)).of_equiv
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : P ⊓ Subgroup.normalizer (L : Set G) ≤
          Subgroup.normalizer (L : Set G))).symm
  have h2 : IsPGroup 3 (Sec4.autIn P L) := h1.map L.normalizerMonoidHom
  have h3 : IsPGroup 3 (Sec4.autThetaQuot P L) := h2.map (Sec4.thetaQuotMulAut L)
  have hsecond : Nat.card (Sec4.autThetaQuot P L) ∣ 27 := hcard _ h3
  have hprod := Nat.mul_dvd_mul hfirst hsecond
  have hcardEq := Sec13.card_inf_mul_card_autThetaQuot (A := P) (L := L) hPN
  rw [hcardEq] at hprod
  norm_num at hprod
  exact hprod

private theorem eq_sup_zpowers_of_card_dvd_81 {A P : Subgroup G} {y : G}
    (hAP : A ≤ P) (hyP : y ∈ P) (hyA : y ∉ A)
    (hA27 : Nat.card A = 27) (hP81 : Nat.card P ∣ 81) :
    P = A ⊔ Subgroup.zpowers y ∧ Nat.card P = 81 := by
  have hlt : A < A ⊔ Subgroup.zpowers y := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    exact hyA (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hsup_le : A ⊔ Subgroup.zpowers y ≤ P :=
    sup_le hAP (Subgroup.zpowers_le.mpr hyP)
  have hsup_dvd_P : Nat.card ↥(A ⊔ Subgroup.zpowers y) ∣ Nat.card P :=
    Subgroup.card_dvd_of_le hsup_le
  have hsup_dvd : Nat.card ↥(A ⊔ Subgroup.zpowers y) ∣ 81 := hsup_dvd_P.trans hP81
  have hgt : 27 < Nat.card ↥(A ⊔ Subgroup.zpowers y) := by
    have := Subgroup.card_lt_of_lt hlt
    rwa [hA27] at this
  have hsup_dvd' : Nat.card ↥(A ⊔ Subgroup.zpowers y) ∣ 3 ^ 4 := by
    rwa [show (3 : ℕ) ^ 4 = 81 by norm_num]
  obtain ⟨k, hk_le, hk_eq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hsup_dvd'
  have h3 : (3 : ℕ) ^ 3 < 3 ^ k := by
    rw [hk_eq] at hgt
    rwa [show (3 : ℕ) ^ 3 = 27 by norm_num]
  have hk_gt : 3 < k := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp h3
  have hk4 : k = 4 := by omega
  have hsup81 : Nat.card ↥(A ⊔ Subgroup.zpowers y) = 81 := by
    rw [hk_eq, hk4]
    norm_num
  have hPcard : Nat.card P = 81 := by
    have hdvd : 81 ∣ Nat.card P := by rwa [hsup81] at hsup_dvd_P
    exact (Nat.dvd_antisymm hdvd hP81).symm
  refine ⟨(Subgroup.eq_of_le_of_card_ge hsup_le (by rw [hPcard, hsup81])).symm, hPcard⟩


private theorem commutator_mem_zpowers_of_mem_P {A P : Subgroup G} {y b : G}
    (hP : P = A ⊔ Subgroup.zpowers y)
    (hAcomm : ∀ a ∈ A, ∀ z ∈ A, a * z = z * a)
    (hAy : ∀ a ∈ A, ⁅a, y⁆ ∈ Subgroup.zpowers b)
    (hNcent : ∀ n ∈ Subgroup.zpowers b, ∀ p ∈ P, n * p = p * n) :
    ∀ u ∈ P, ∀ v ∈ P, ⁅u, v⁆ ∈ Subgroup.zpowers b := by
  have hfirst : ∀ u ∈ P, ∀ v ∈ ((A : Set G) ∪ {y}),
      ⁅u, v⁆ ∈ Subgroup.zpowers b := by
    intro u hu v hv
    rcases hv with hvA | hvy
    · have hgen : ∀ x ∈ ((A : Set G) ∪ {y}), ⁅x, v⁆ ∈ Subgroup.zpowers b := by
        intro x hx
        rcases hx with hxA | hxy
        · have hx1 : ⁅x, v⁆ = 1 := by
            rw [commutatorElement_def, hAcomm x hxA v hvA]
            group
          rw [hx1]
          exact (Subgroup.zpowers b).one_mem
        · have hxy' : x = y := by simpa using hxy
          subst x
          have h := (Subgroup.zpowers b).inv_mem (hAy v hvA)
          rwa [commutatorElement_inv v y] at h
      exact forall_commutator_mem_of_generators hP hNcent hgen u hu
    · have hvy' : v = y := by simpa using hvy
      subst v
      have hgen : ∀ x ∈ ((A : Set G) ∪ {y}), ⁅x, y⁆ ∈ Subgroup.zpowers b := by
        intro x hx
        rcases hx with hxA | hxy
        · exact hAy x hxA
        · have hxy' : x = y := by simpa using hxy
          subst x
          have h1 : ⁅y, y⁆ = 1 := by rw [commutatorElement_def]; group
          rw [h1]
          exact (Subgroup.zpowers b).one_mem
      exact forall_commutator_mem_of_generators hP hNcent hgen u hu
  intro u hu w hw
  have hgen' : ∀ x ∈ ((A : Set G) ∪ {y}), ⁅x, u⁆ ∈ Subgroup.zpowers b := by
    intro x hx
    have hxu : ⁅u, x⁆ ∈ Subgroup.zpowers b := hfirst u hu x hx
    have h := (Subgroup.zpowers b).inv_mem hxu
    rwa [commutatorElement_inv u x] at h
  have hwu : ⁅w, u⁆ ∈ Subgroup.zpowers b :=
    forall_commutator_mem_of_generators hP hNcent hgen' w hw
  have h := (Subgroup.zpowers b).inv_mem hwu
  rwa [commutatorElement_inv w u] at h

private theorem false_of_fixes_image {L S P : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hEcard : Nat.card E = 9)
    (hfixE : ∀ e ∈ E,
      (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hyN⟩)) e = e)
    (hρ3 : (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hyN⟩)) ^ 3 = 1)
    (hpre : ∀ e ∈ E, ∃ x : ↥L, (x : G) ∈ S ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) x = e)
    (hSL : S ≤ L) (hSP : S ≤ P) (hyP : y ∈ P)
    (houter : ∀ s ∈ S, s⁻¹ * y ∉ Late.sectionCentralizer P L
      (inSubgroup (aschbacherSolvableCore 3) L))
    (hcent : ∀ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Nat.card E = 9 →
      ∀ α : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), α ^ 3 = 1 →
        (∀ e ∈ E, α e = e) → ∃ e ∈ E, α = MulAut.conj e) : False := by
  let φ : ↥(Subgroup.normalizer (L : Set G)) →*
      MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom
  have hfixE' : ∀ e ∈ E, φ ⟨y, hyN⟩ e = e := by
    intro e he
    simpa [φ] using hfixE e he
  have hρ3' : (φ ⟨y, hyN⟩) ^ 3 = 1 := by simpa [φ] using hρ3
  obtain ⟨e, he, hαe⟩ := hcent E hEcard (φ ⟨y, hyN⟩) hρ3' hfixE'
  obtain ⟨x, hxS, hxe⟩ := hpre e he
  have hxN : (x : G) ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.le_normalizer (H := L) (hSL hxS)
  have hφx : φ ⟨x, hxN⟩ = MulAut.conj e := by
    rw [show φ ⟨x, hxN⟩ =
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) from rfl, ← hxe]
    exact CFSG.RankThree.PartTwo.KFacts.thetaQuotMulAut_compAction_of_mem x.2 hxN
  have hφeq : φ ⟨x, hxN⟩ = φ ⟨y, hyN⟩ := hφx.trans hαe.symm
  have hprod : φ (⟨x, hxN⟩⁻¹ * ⟨y, hyN⟩) = 1 := by
    rw [map_mul, map_inv, hφeq, inv_mul_cancel]
  have hmulN : x⁻¹ * y ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hxN) hyN
  have hφprod : Sec4.thetaQuotMulAut L
      (L.normalizerMonoidHom ⟨x⁻¹ * y, hmulN⟩) = 1 := by
    have hcoe : (⟨x⁻¹ * y, hmulN⟩ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨x, hxN⟩⁻¹ * ⟨y, hyN⟩ := by
      apply Subtype.ext
      rfl
    rw [hcoe]
    simpa [φ] using hprod
  have hKP : x⁻¹ * y ∈ Late.sectionCentralizer P L
      (inSubgroup (aschbacherSolvableCore 3) L) := by
    rw [mem_sectionCentralizer_iff hmulN]
    refine ⟨?_, hφprod⟩
    exact P.mul_mem (P.inv_mem (hSP hxS)) hyP
  exact houter x hxS hKP

private theorem exists_commutator_ne_one {L S P : Subgroup G} {y : G}
    (hS9 : Nat.card S = 9) (hSL : S ≤ L) (hSP : S ≤ P)
    (hyP : y ∈ P) (hy3 : y ^ 3 = 1)
    (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (houter : ∀ s ∈ S, s⁻¹ * y ∉ Late.sectionCentralizer P L
      (inSubgroup (aschbacherSolvableCore 3) L))
    (hcent : ∀ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Nat.card E = 9 →
      ∀ α : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), α ^ 3 = 1 →
        (∀ e ∈ E, α e = e) → ∃ e ∈ E, α = MulAut.conj e) :
    ∃ s ∈ S, y * s * y⁻¹ * s⁻¹ ≠ 1 := by
  classical
  by_contra h
  have h' : ∀ s ∈ S, y * s * y⁻¹ * s⁻¹ = 1 := by
    intro s hs
    by_contra hne
    exact h ⟨s, hs, hne⟩
  let θ := aschbacherSolvableCore 3 ↥L
  let E : Subgroup (↥L ⧸ θ) := (S.subgroupOf L).map (QuotientGroup.mk' θ)
  have hEcard : Nat.card E = 9 :=
    Proof1510Steps.card_map_mk_of_card_nine hSL hS9
  have hpre : ∀ e ∈ E, ∃ x : ↥L, (x : G) ∈ S ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) x = e := by
    intro e he
    obtain ⟨x, hx, hxe⟩ := Subgroup.mem_map.mp he
    exact ⟨x, Subgroup.mem_subgroupOf.mp hx, hxe⟩
  let φ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ θ) :=
    (Sec4.thetaQuotMulAut L).comp L.normalizerMonoidHom
  have hρ3 : (φ ⟨y, hyN⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have hy1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := by
      apply Subtype.ext
      exact hy3
    rw [hy1, map_one]
  have hfixE : ∀ e ∈ E, φ ⟨y, hyN⟩ e = e := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp he
    have hxS : (x : G) ∈ S := Subgroup.mem_subgroupOf.mp hx
    have hcomm : y * (x : G) = (x : G) * y := by
      have h1 := h' (x : G) hxS
      have h2 : y * (x : G) * y⁻¹ = (x : G) := by
        have := congrArg (fun t => t * (x : G)) h1
        simpa [mul_assoc] using this
      have h3 := congrArg (fun t => t * y) h2
      simpa [mul_assoc] using h3
    have hφy : φ ⟨y, hyN⟩ =
        Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨y, hyN⟩) := rfl
    rw [hφy, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    apply congrArg (fun z : ↥L => (z : ↥L ⧸ θ))
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, hcomm]
    group
  exact false_of_fixes_image hyN E hEcard (by simpa [φ] using hfixE)
    (by simpa [φ] using hρ3) hpre hSL hSP hyP houter hcent

private theorem exists_z_facts {L S P : Subgroup G} {y x b : G}
    (hS9 : Nat.card S = 9) (hSL : S ≤ L) (hSP : S ≤ P)
    (hyP : y ∈ P) (hy3 : y ^ 3 = 1)
    (hyN : y ∈ Subgroup.normalizer (L : Set G))
    (houter : ∀ s ∈ S, s⁻¹ * y ∉ Late.sectionCentralizer P L
      (inSubgroup (aschbacherSolvableCore 3) L))
    (hcent : ∀ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Nat.card E = 9 →
      ∀ α : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), α ^ 3 = 1 →
        (∀ e ∈ E, α e = e) → ∃ e ∈ E, α = MulAut.conj e)
    (hPP : ∀ u ∈ P, ∀ v ∈ P, ⁅u, v⁆ ∈ Subgroup.zpowers b)
    (hxP : x ∈ Subgroup.normalizer (P : Set G)) (hexp3 : ∀ u ∈ P, u ^ 3 = 1) :
    ∃ z : G, z ∈ Subgroup.zpowers b ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧
      x * z * x⁻¹ ∈ Subgroup.zpowers b ∧ x * z * x⁻¹ ≠ 1 ∧
      (x * z * x⁻¹) ^ 3 = 1 := by
  obtain ⟨s, hsS, hzs0⟩ := exists_commutator_ne_one hS9 hSL hSP hyP hy3 hyN houter hcent
  set z : G := y * s * y⁻¹ * s⁻¹ with hzdef
  have hzs : z ≠ 1 := by rw [hzdef]; exact hzs0
  have hzP : z ∈ P := by
    rw [hzdef]
    exact P.mul_mem (P.mul_mem (P.mul_mem hyP (hSP hsS)) (P.inv_mem hyP))
      (P.inv_mem (hSP hsS))
  have hz3 : z ^ 3 = 1 := hexp3 z hzP
  have hzN : z ∈ Subgroup.zpowers b := by
    rw [hzdef]
    exact hPP y hyP s (hSP hsS)
  have hzxP : x * z * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hxP z).mp hzP
  have hzx1 : x * z * x⁻¹ ≠ 1 := by
    intro h1
    apply hzs
    calc z = x⁻¹ * (x * z * x⁻¹) * x := by group
      _ = 1 := by rw [h1]; group
  have hzx3 : (x * z * x⁻¹) ^ 3 = 1 := hexp3 _ hzxP
  have hzxN : x * z * x⁻¹ ∈ Subgroup.zpowers b := by
    have hxyP : x * y * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hxP y).mp hyP
    have hxsP : x * s * x⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hxP s).mp (hSP hsS)
    have hcomm := hPP (x * y * x⁻¹) hxyP (x * s * x⁻¹) hxsP
    have hconj : ⁅x * y * x⁻¹, x * s * x⁻¹⁆ = x * z * x⁻¹ := by
      rw [hzdef, commutatorElement_def]
      group
    rwa [hconj] at hcomm
  exact ⟨z, hzN, hzs, hz3, hzxN, hzx1, hzx3⟩

private theorem zpowers_eq_of_mem_zpowers_of_pow_three {b w : G}
    (hw : w ∈ Subgroup.zpowers b) (hw1 : w ≠ 1) (hw3 : w ^ 3 = 1)
    (hbo : orderOf b = 3) : Subgroup.zpowers w = Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardN : Nat.card (Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hbo]
  have hwo : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hcardw : Nat.card (Subgroup.zpowers w) = 3 := by rw [Nat.card_zpowers, hwo]
  apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
  rw [hcardN, hcardw]

private theorem map_conj_zpowers_eq_of_z {b z x : G} (hbo : orderOf b = 3)
    (hzN : z ∈ Subgroup.zpowers b) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hzxN : x * z * x⁻¹ ∈ Subgroup.zpowers b) (hzx1 : x * z * x⁻¹ ≠ 1)
    (hzx3 : (x * z * x⁻¹) ^ 3 = 1) :
    (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers b := by
  have hzeq : Subgroup.zpowers z = Subgroup.zpowers b :=
    zpowers_eq_of_mem_zpowers_of_pow_three hzN hz1 hz3 hbo
  have hzeqx : Subgroup.zpowers (x * z * x⁻¹) = Subgroup.zpowers b :=
    zpowers_eq_of_mem_zpowers_of_pow_three hzxN hzx1 hzx3 hbo
  calc (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom
      = (Subgroup.zpowers z).map (MulAut.conj x).toMonoidHom := by rw [← hzeq]
    _ = Subgroup.zpowers ((MulAut.conj x) z) := MonoidHom.map_zpowers _ _
    _ = Subgroup.zpowers (x * z * x⁻¹) := by rw [MulAut.conj_apply]
    _ = Subgroup.zpowers b := hzeqx

private theorem facts_on_P {B L P : Subgroup G} {c b : G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G)))
    (hcB : c ∈ B) (hbB : b ∈ B)
    (hcenN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hc3 : Nat.card (Subgroup.zpowers c) = 3)
    (hK : ∀ k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L),
      k ∈ Subgroup.zpowers c)
    (hcard : ∀ R : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)), IsPGroup 3 R →
      Nat.card R ∣ 27) :
    P ≤ Subgroup.centralizer (B : Set G) ∧
      P ≤ Subgroup.centralizer ({c} : Set G) ∧
      P ≤ Subgroup.normalizer (L : Set G) ∧
      P ≤ Subgroup.centralizer ({b} : Set G) ∧ Nat.card P ∣ 81 := by
  have hPB : P ≤ Subgroup.centralizer (B : Set G) := hP.le
  have hPc : P ≤ Subgroup.centralizer ({c} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hPB hz) c hcB).symm
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := hPc.trans hcenN
  have hPb : P ≤ Subgroup.centralizer ({b} : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hPB hz) b hbB).symm
  have hP81 : Nat.card P ∣ 81 := card_dvd_81_of_isSylowOf hP hcB hcenN hc3 hK hcard
  exact ⟨hPB, hPc, hPN, hPb, hP81⟩

theorem map_conj_zpowers_eq {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hall : All1510 A) {B : Subgroup G} (hB : IsHyperplane A B) (hcB : c ∈ B) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.centralizer (B : Set G))) (hAP : A ≤ P)
    (houter : ∃ y ∈ P, ∀ s ∈ A ⊓ L,
      s⁻¹ * y ∉ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L))
    {x : G} (hxP : x ∈ Subgroup.normalizer (P : Set G))
    (hexp3 : ∀ u ∈ P, u ^ 3 = 1)
    (hK : ∀ k ∈ Late.sectionCentralizer P L (inSubgroup (aschbacherSolvableCore 3) L),
      k ∈ Subgroup.zpowers c)
    (hcard : ∀ R : Subgroup (MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L)), IsPGroup 3 R →
      Nat.card R ∣ 27)
    (hcent : ∀ E : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Nat.card E = 9 →
      ∀ α : MulAut (↥L ⧸ aschbacherSolvableCore 3 ↥L), α ^ 3 = 1 → (∀ e ∈ E, α e = e) →
        ∃ e ∈ E, α = MulAut.conj e)
    {b : G} (hbB : b ∈ B) (hbL : b ∈ L) (hb1 : b ≠ 1) :
    (Subgroup.zpowers b).map (MulAut.conj x).toMonoidHom = Subgroup.zpowers b := by
  classical
  have hD := h.toSec14Std.toSec13Data
  obtain ⟨⟨χ⟩, hS9raw, hcL, hAeqraw, hcenN⟩ := setting h hall
  let S : Subgroup G := A ⊓ L
  have hbS : b ∈ S := ⟨hB.1 hbB, hbL⟩
  have hP3 : IsPGroup 3 P := hP.isPGroup
  obtain ⟨hPB, hPc, hPN, hPb, hP81⟩ :=
    facts_on_P hP hcB hbB hcenN hD.card_zpowers hK hcard
  obtain ⟨y, hyP, hyouter⟩ := houter
  have hyA : y ∉ A :=
    notMem_A_of_houter hAeqraw inf_le_left (fun a ha z hz => hD.commute ha hz)
      hD.le_centralizer hAP hyP hyouter
  obtain ⟨hP_eq_Ay, hPcard⟩ :=
    eq_sup_zpowers_of_card_dvd_81 hAP hyP hyA hD.card_eq hP81
  have hSP : S ≤ P := inf_le_left.trans hAP
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hPN hyP
  have hy3 : y ^ 3 = 1 := hexp3 y hyP
  have hSexp : ∀ z ∈ S, z ^ 3 = 1 := fun z hz => hexp3 z (hSP hz)
  have hScomm : ∀ u ∈ S, ∀ z ∈ S, u * z = z * u :=
    fun u hu z hz => hD.commute ((inf_le_left : A ⊓ L ≤ A) hu)
      ((inf_le_left : A ⊓ L ≤ A) hz)
  have hyc : y * c = c * y := (Subgroup.mem_centralizer_iff.mp (hPB hyP) c hcB).symm
  have hyb : y * b = b * y := (Subgroup.mem_centralizer_iff.mp (hPB hyP) b hbB).symm
  have hPL : P ⊓ L = S :=
    Proof1510Steps.inf_eq_of_isPGroup inf_le_right hS9raw χ hbS hb1 hP3 hSP hPb
  have hyPnorm : y ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer (H := P) hyP
  have hyInf : y ∈ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hyPnorm, hyN⟩
  have hyS : y ∈ Subgroup.normalizer (S : Set G) := hPL ▸ hyInf
  have hNcentP : ∀ n ∈ Subgroup.zpowers b, ∀ p ∈ P, n * p = p * n := by
    intro n hn p hp
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hn
    rw [← hi]
    exact (Commute.zpow_left
      (show Commute b p from Subgroup.mem_centralizer_iff.mp (hPB hp) b hbB) i).eq
  have hNcentA : ∀ n ∈ Subgroup.zpowers b, ∀ p ∈ A, n * p = p * n :=
    fun n hn p hp => hNcentP n hn p (hAP hp)
  have hAy : ∀ a ∈ A, ⁅a, y⁆ ∈ Subgroup.zpowers b :=
    commutator_mem_zpowers_of_mem_A hAeqraw (fun a ha z hz => hD.commute ha hz) hyc hS9raw
      hSexp hScomm hbS hb1 hyS hy3 hyb hNcentA
  have hPP : ∀ u ∈ P, ∀ v ∈ P, ⁅u, v⁆ ∈ Subgroup.zpowers b :=
    commutator_mem_zpowers_of_mem_P hP_eq_Ay (fun a ha z hz => hD.commute ha hz) hAy hNcentP
  obtain ⟨z, hzN, hzs, hz3, hzxN, hzx1, hzx3⟩ :=
    exists_z_facts hS9raw inf_le_right hSP hyP hy3 hyN hyouter hcent hPP hxP hexp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hb3 : b ^ 3 = 1 := hexp3 b (hAP ((inf_le_left : A ⊓ L ≤ A) hbS))
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  exact map_conj_zpowers_eq_of_z hbo hzN hzs hz3 hzxN hzx1 hzx3

end CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse
