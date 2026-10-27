module

public import CFSG.LocalAnalysis.StandardType.TwE6MaxEleven.Defs
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import CFSG.Monster.Existence.StdOdd.Coprime
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.StandardType.TwE6MaxEleven

open Subgroup

variable {X : Type} [Group X] [Finite X]

theorem card_normalizer_zpowers_eleven_dvd (hX : LocalFacts X) {t : X} (ht : orderOf t = 11) :
    Nat.card (normalizer (zpowers t : Set X)) ∣ 660 := by
  obtain ⟨k, hk, hkdvd⟩ :=
    CFSG.Monster.Existence.StdOdd.exists_card_eq_mul_dvd_totient (zpowers t)
      (normalizer (zpowers t : Set X)) le_rfl
  rw [inf_eq_right.mpr (Subgroup.centralizer_le_normalizer (zpowers t : Set X)),
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hk
  rw [Nat.card_zpowers, ht, Nat.totient_prime (by norm_num : Nat.Prime 11)] at hkdvd
  rw [Subgroup.zpowers_eq_closure, hk]
  refine (Nat.mul_dvd_mul_left _ hkdvd).trans ?_
  calc Nat.card (Subgroup.centralizer ({t} : Set X)) * (11 - 1)
      ∣ (2 * 3 * 11) * (11 - 1) := Nat.mul_dvd_mul_right (hX.c11 t ht) _
    _ = 660 := by norm_num

theorem isSolvable_normalizer_zpowers_eleven (hX : LocalFacts X) {t : X} (ht : orderOf t = 11) :
    Group.IsSolvable (normalizer (zpowers t : Set X)) := by
  classical
  let H : Subgroup X := zpowers t
  let N : Subgroup X := normalizer (H : Set X)
  let C : Subgroup X := Subgroup.centralizer ({t} : Set X)
  have hCeq : C = Subgroup.centralizer (H : Set X) := by
    simp only [C, H, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hCN : C ≤ N := by
    rw [hCeq]
    exact Subgroup.centralizer_le_normalizer (H : Set X)
  haveI : (C.subgroupOf N).Normal := by
    rw [hCeq]
    exact Subgroup.normal_subgroupOf_centralizer_normalizer (H : Set X)
  have h66 : Squarefree 66 := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro x hx hdvd
    have hx2 : 2 ≤ x := hx.two_le
    have hle : x ≤ 8 := by
      nlinarith [Nat.le_of_dvd (by norm_num) hdvd]
    interval_cases x <;> norm_num at hdvd
  have hCsolv : Group.IsSolvable C := by
    haveI : IsZGroup C :=
      IsZGroup.of_squarefree (Squarefree.squarefree_of_dvd (hX.c11 t ht) h66)
    infer_instance
  haveI : Group.IsSolvable C := hCsolv
  let f : N →* MulAut H := Subgroup.normalizerMonoidHom (H := H)
  have hker : f.ker = C.subgroupOf N := by
    rw [show f = Subgroup.normalizerMonoidHom (H := H) from rfl,
      Subgroup.normalizerMonoidHom_ker, hCeq]
  haveI : IsCyclic H := Subgroup.isCyclic_zpowers t
  haveI : Group.IsSolvable (MulAut H) := by
    have e := IsCyclic.mulAutMulEquiv H
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI hCsub : Group.IsSolvable (C.subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hCN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hCN).injective
  haveI : Group.IsSolvable (N ⧸ f.ker) := by
    have e := QuotientGroup.quotientKerEquivRange f
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : Group.IsSolvable f.ker := hker.symm ▸ hCsub
  exact Group.isSolvable_of_subgroup_quotient f.ker

theorem card_normalizer_zpowers_seventeen_dvd (hX : LocalFacts X) {s : X} (hs : orderOf s = 17) :
    Nat.card (normalizer (zpowers s : Set X)) ∣ 272 := by
  obtain ⟨k, hk, hkdvd⟩ :=
    CFSG.Monster.Existence.StdOdd.exists_card_eq_mul_dvd_totient (zpowers s)
      (normalizer (zpowers s : Set X)) le_rfl
  rw [inf_eq_right.mpr (Subgroup.centralizer_le_normalizer (zpowers s : Set X)),
    Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at hk
  rw [Nat.card_zpowers, hs, Nat.totient_prime (by norm_num : Nat.Prime 17)] at hkdvd
  rw [Subgroup.zpowers_eq_closure, hk]
  refine (Nat.mul_dvd_mul_left _ hkdvd).trans ?_
  rw [hX.c17 s hs]

theorem mem_zpowers_of_commute_eleven (hX : LocalFacts X) {t y z : X} (ht : orderOf t = 11)
    (hy : orderOf y = 3) (hyt : Commute y t) (hz : orderOf z = 3) (hzt : Commute z t) :
    z ∈ zpowers y := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let C : Subgroup X := Subgroup.centralizer ({t} : Set X)
  have hyC : y ∈ C := by
    rw [show C = Subgroup.centralizer ({t} : Set X) from rfl, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hyt.symm
  have hzC : z ∈ C := by
    rw [show C = Subgroup.centralizer ({t} : Set X) from rfl, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hzt.symm
  have htC : t ∈ C := by
    rw [show C = Subgroup.centralizer ({t} : Set X) from rfl, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rfl
  have hCcard : Nat.card C ∣ 2 * 3 * 11 := hX.c11 t ht
  let P : Subgroup C := zpowers (⟨y, hyC⟩ : C)
  let Q : Subgroup C := zpowers (⟨z, hzC⟩ : C)
  let e : C := ⟨t, htC⟩
  let T : Subgroup C := zpowers e
  have hPcard : Nat.card P = 3 := by
    change Nat.card (zpowers (⟨y, hyC⟩ : C)) = 3
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy]
  have hQcard : Nat.card Q = 3 := by
    change Nat.card (zpowers (⟨z, hzC⟩ : C)) = 3
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hz]
  have hTcard : Nat.card T = 11 := by
    change Nat.card (zpowers e) = 11
    rw [Nat.card_zpowers]
    exact (Subgroup.orderOf_mk t htC).trans ht
  have hnormal : T ≤ Subgroup.normalizer (P : Set C) := by
    change zpowers e ≤ Subgroup.normalizer (P : Set C)
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro p
    have hconj : e * p * e⁻¹ = p := by
      apply Subtype.ext
      show (t : X) * (p : X) * t⁻¹ = (p : X)
      have hcomm := Subgroup.mem_centralizer_iff.mp p.2 t (Set.mem_singleton t)
      rw [hcomm]
      group
    rw [hconj]
  have hdisj : Disjoint P T :=
    IsPGroup.disjoint_of_coprime (p₁ := 3) (p₂ := 11)
      (IsPGroup.of_card (n := 1) (by rw [hPcard]; norm_num))
      (IsPGroup.of_card (n := 1) (by rw [hTcard]; norm_num)) (by norm_num)
  have h33 : 33 ∣ Nat.card (Subgroup.normalizer (P : Set C)) := by
    have hle : P ⊔ T ≤ Subgroup.normalizer (P : Set C) :=
      sup_le Subgroup.le_normalizer hnormal
    have h := Subgroup.card_dvd_of_le hle
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer P T hnormal hdisj,
      hPcard, hTcard, show (3 : ℕ) * 11 = 33 by norm_num] at h
    exact h
  have h3dvd : 3 ∣ Nat.card C := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hyC : zpowers y ≤ C)
    rwa [Nat.card_zpowers, hy] at h
  have h9 : ¬ 9 ∣ Nat.card C := by
    intro h
    exact absurd (h.trans hCcard) (by norm_num)
  haveI : Nonempty C := ⟨⟨t, htC⟩⟩
  have hfact : (Nat.card C).factorization 3 = 1 := by
    have hne : Nat.card C ≠ 0 := Nat.card_pos.ne'
    have hpos : 0 < (Nat.card C).factorization 3 :=
      Nat.prime_three.factorization_pos_of_dvd hne h3dvd
    have hle : (Nat.card C).factorization 3 ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ (Nat.card C).factorization 3 := by omega
      exact h9 ((Nat.prime_three.pow_dvd_iff_le_factorization hne).mpr h2)
    omega
  have hPcard' : Nat.card P = 3 ^ (Nat.card C).factorization 3 := by
    rw [hPcard, hfact, pow_one]
  have hQcard' : Nat.card Q = 3 ^ (Nat.card C).factorization 3 := by
    rw [hQcard, hfact, pow_one]
  let P' : Sylow 3 C := Sylow.ofCard P hPcard'
  let Q' : Sylow 3 C := Sylow.ofCard Q hQcard'
  have hidxle : (Subgroup.normalizer (P : Set C)).index ≤ 2 := by
    have hN33 : 33 ≤ Nat.card (Subgroup.normalizer (P : Set C)) :=
      Nat.le_of_dvd (by norm_num) h33
    have hCle : Nat.card C ≤ 66 := Nat.le_of_dvd (by norm_num) hCcard
    have h1 : (Subgroup.normalizer (P : Set C)).index * 33 ≤ 66 := by
      calc (Subgroup.normalizer (P : Set C)).index * 33
          ≤ (Subgroup.normalizer (P : Set C)).index *
              Nat.card (Subgroup.normalizer (P : Set C)) := Nat.mul_le_mul_left _ hN33
        _ = Nat.card C := Subgroup.index_mul_card _
        _ ≤ 66 := hCle
    omega
  have hn3 : Nat.card (Sylow 3 C) = 1 := by
    haveI : Nonempty (Sylow 3 C) := Sylow.nonempty
    have hmod : Nat.card (Sylow 3 C) % 3 = 1 := by
      have h := card_sylow_modEq_one 3 C
      simpa [Nat.ModEq] using h
    have hidx : Nat.card (Sylow 3 C) = (Subgroup.normalizer (P : Set C)).index := by
      have h := Sylow.card_eq_index_normalizer P'
      rwa [show (P' : Set C) = (P : Set C) from rfl] at h
    have hpos : 0 < Nat.card (Sylow 3 C) := Nat.card_pos
    have hle : Nat.card (Sylow 3 C) ≤ 2 := by rw [hidx]; exact hidxle
    omega
  have hsub : Subsingleton (Sylow 3 C) := by
    rw [← Finite.card_le_one_iff_subsingleton]
    omega
  have hQP : Q = P :=
    congrArg (fun S : Sylow 3 C => (S : Subgroup C)) (Subsingleton.elim Q' P')
  have hmem : (⟨z, hzC⟩ : C) ∈ zpowers (⟨y, hyC⟩ : C) := by
    have h : (⟨z, hzC⟩ : C) ∈ Q := Subgroup.mem_zpowers _
    rwa [hQP] at h
  rw [Subgroup.mem_zpowers_iff] at hmem ⊢
  obtain ⟨k, hk⟩ := hmem
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem eq_bot_of_isPGroup_of_mem_normalizer (hX : LocalFacts X) {t : X} (ht : orderOf t = 11)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hp11 : p ≠ 11) {R : Subgroup X}
    (hR : IsPGroup p R) (htR : t ∈ normalizer (R : Set X)) : R = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hFix : Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set X)) = 1 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hR.to_le inf_le_left)
    have hdvd : Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set X)) ∣ 2 * 3 * 11 :=
      (Subgroup.card_dvd_of_le inf_le_right).trans (hX.c11 t ht)
    have hk0 : k = 0 := by
      by_contra hk0
      have hpdvd : p ∣ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set X)) := by
        rw [hk]
        exact dvd_pow_self p hk0
      have hp66 : p ∣ 2 * 3 * 11 := hpdvd.trans hdvd
      rw [show (2 * 3 * 11 : ℕ) = 2 * (3 * 11) by norm_num] at hp66
      rcases hp.dvd_mul.mp hp66 with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (q := 2) (by norm_num)).mp h)
      rcases hp.dvd_mul.mp h with h | h
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (q := 3) (by norm_num)).mp h)
      · exact hp11 ((Nat.prime_dvd_prime_iff_eq hp (q := 11) (by norm_num)).mp h)
    rw [hk, hk0, pow_zero]
  have hmod : Nat.card R ≡ 1 [MOD 11] := by
    have h := CFSG.Monster.Existence.StdOdd.card_modEq_zpowers (p := 11) ht htR
    rwa [hFix] at h
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
  have hn_zero : n = 0 := by
    by_contra hn0
    have hpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hpX : p ∣ Nat.card X := by
      have h : p ∣ Nat.card R := by
        rw [hn]
        exact dvd_pow_self p hn0
      exact h.trans (Subgroup.card_subgroup_dvd_card R)
    rw [hX.card] at hpX
    have hclass : p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 17 ∨ p = 19 := by
      rcases hp.dvd_mul.mp hpX with h | h
      · rcases hp.dvd_mul.mp h with h | h
        · rcases hp.dvd_mul.mp h with h | h
          · rcases hp.dvd_mul.mp h with h | h
            · rcases hp.dvd_mul.mp h with h | h
              · rcases hp.dvd_mul.mp h with h | h
                · rcases hp.dvd_mul.mp h with h | h
                  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp (q := 2)
                      (by norm_num)).mp (hp.dvd_of_dvd_pow h)) hp2
                  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp (q := 3)
                      (by norm_num)).mp (hp.dvd_of_dvd_pow h)) hp3
                · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (q := 5)
                    (by norm_num)).mp (hp.dvd_of_dvd_pow h))
              · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (q := 7)
                  (by norm_num)).mp (hp.dvd_of_dvd_pow h)))
            · exact absurd ((Nat.prime_dvd_prime_iff_eq hp (q := 11) (by norm_num)).mp h) hp11
          · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (q := 13)
              (by norm_num)).mp h)))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (q := 17)
            (by norm_num)).mp h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (q := 19)
          (by norm_num)).mp h))))
    have hn5 : 5 ≤ n := by
      by_contra h
      have hn4 : n ≤ 4 := by omega
      rw [hn] at hmod
      rcases hclass with rfl | rfl | rfl | rfl | rfl <;>
        (interval_cases n <;> norm_num at hmod)
    have hp5dvd : p ^ 5 ∣ Nat.card X := by
      have h : p ^ 5 ∣ p ^ n := pow_dvd_pow p hn5
      exact (hn.symm ▸ h).trans (Subgroup.card_subgroup_dvd_card R)
    rw [hX.card] at hp5dvd
    rcases hclass with rfl | rfl | rfl | rfl | rfl <;> norm_num at hp5dvd
  exact Subgroup.card_eq_one.mp (by rw [hn, hn_zero, pow_zero])

theorem eq_zpowers_of_isPGroup_eleven (hX : LocalFacts X) {t : X} (ht : orderOf t = 11)
    {R : Subgroup X} (hR : IsPGroup 11 R) (hR1 : R ≠ ⊥) (htR : t ∈ normalizer (R : Set X)) :
    R = zpowers t := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hR
  have hRcard_dvd : Nat.card R ∣ Nat.card X := Subgroup.card_subgroup_dvd_card R
  rw [hX.card] at hRcard_dvd
  have hn1 : n ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have hd : 11 ^ 2 ∣ Nat.card R := by
      rw [hn]
      exact pow_dvd_pow 11 h2
    exact absurd (hd.trans hRcard_dvd) (by norm_num)
  have hcardR : Nat.card R = 11 := by
    interval_cases n
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hn]; norm_num)) hR1
    · rw [hn]; norm_num
  have hT : IsPGroup 11 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; norm_num)
  have hsup : IsPGroup 11 (R ⊔ zpowers t : Subgroup X) :=
    IsPGroup.to_sup_of_normal_left' hR hT (Subgroup.zpowers_le.mpr htR)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hsup
  have hsup_dvd : Nat.card (R ⊔ zpowers t : Subgroup X) ∣ Nat.card X :=
    Subgroup.card_subgroup_dvd_card _
  rw [hX.card] at hsup_dvd
  have hm1 : m ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ m := by omega
    have hd : 11 ^ 2 ∣ Nat.card (R ⊔ zpowers t : Subgroup X) := by
      rw [hm]
      exact pow_dvd_pow 11 h2
    exact absurd (hd.trans hsup_dvd) (by norm_num)
  have hm1' : m = 1 := by
    have h11 : 11 ∣ Nat.card (R ⊔ zpowers t : Subgroup X) := by
      have h := Subgroup.card_dvd_of_le (le_sup_left : R ≤ R ⊔ zpowers t)
      rwa [hcardR] at h
    rw [hm] at h11
    have hpos : 0 < m := by
      by_contra h0
      have h0' : m = 0 := by omega
      rw [h0', pow_zero] at h11
      norm_num at h11
    interval_cases m
    rfl
  have hsupR : R = (R ⊔ zpowers t : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hm, hm1', hcardR]; norm_num)
  have htR' : t ∈ R := by
    have h : t ∈ (R ⊔ zpowers t : Subgroup X) := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rwa [← hsupR] at h
  have hle : zpowers t ≤ R := Subgroup.zpowers_le.mpr htR'
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, ht, hcardR])).symm

theorem card_dvd_card_mul_card_normalizer {M N R : Subgroup X} (hNM : N ≤ M)
    (hMN : M ≤ normalizer (N : Set X)) {p : ℕ} [Fact p.Prime] (hRN : R ≤ N)
    (hR : Nat.card R = p ^ (Nat.card N).factorization p) :
    Nat.card M ∣ Nat.card N * Nat.card (normalizer (R : Set X)) := by
  classical
  have hRM : R ≤ M := hRN.trans hNM
  let N' : Subgroup M := N.subgroupOf M
  let R' : Subgroup M := R.subgroupOf M
  haveI : N'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  have hN'card : Nat.card N' = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  have hR'N' : R' ≤ N' := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hRN hx
  have hR'card : Nat.card R' = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv
  have hSyl : Nat.card (R'.subgroupOf N') = p ^ (Nat.card N').factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR'N').toEquiv, hR'card, hR, hN'card]
  let S : Subgroup N' := R'.subgroupOf N'
  let P : Sylow p N' := Sylow.ofCard S hSyl
  have hPR' : (P : Subgroup N').map N'.subtype = R' := by
    change S.map N'.subtype = R'
    rw [Subgroup.map_subgroupOf_eq_of_le hR'N']
  have hfr : Subgroup.normalizer ((P : Subgroup N').map N'.subtype) ⊔ N' = ⊤ :=
    Sylow.normalizer_sup_eq_top P
  have hsup : N' ⊔ Subgroup.normalizer (R' : Set M) = ⊤ := by
    rw [sup_comm, ← hPR']
    exact hfr
  have hrelmul : N'.relIndex (Subgroup.normalizer (R' : Set M)) * Nat.card N' = Nat.card M := by
    have h := Subgroup.relIndex_mul_card (H := N')
      (K := (N' ⊔ Subgroup.normalizer (R' : Set M) : Subgroup M))
    rw [Subgroup.relIndex_sup_left] at h
    rw [inf_of_le_left le_sup_left, hsup, Subgroup.card_top] at h
    exact h
  have hKdvd : Nat.card (Subgroup.normalizer (R' : Set M)) ∣
      Nat.card (normalizer (R : Set X)) := by
    have hK : Subgroup.normalizer (R' : Set M) = (normalizer (R : Set X)).subgroupOf M :=
      (Subgroup.subgroupOf_normalizer_eq hRM).symm
    have hKle : Subgroup.normalizer (R' : Set M) ≤ (normalizer (R : Set X)).subgroupOf M := by
      rw [hK]
    have hKmap : (Subgroup.normalizer (R' : Set M)).map M.subtype ≤ normalizer (R : Set X) := by
      rintro x ⟨m, hm, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (hKle hm)
    have h1 := Subgroup.card_dvd_of_le hKmap
    rwa [Subgroup.card_map_of_injective M.subtype_injective] at h1
  have hdvd : N'.relIndex (Subgroup.normalizer (R' : Set M)) ∣
      Nat.card (normalizer (R : Set X)) :=
    dvd_trans (Subgroup.relIndex_dvd_card (H := N')
      (K := Subgroup.normalizer (R' : Set M))) hKdvd
  rw [← hrelmul, ← hN'card]
  simpa [Nat.mul_comm] using Nat.mul_dvd_mul_right hdvd (Nat.card N')

end CFSG.StandardType.TwE6MaxEleven
