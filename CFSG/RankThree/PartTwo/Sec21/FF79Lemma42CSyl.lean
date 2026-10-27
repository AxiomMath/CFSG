module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CBase
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CYosh
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CSyl3
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma42CSyl2
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base
import CFSG.RankThree.Transfer.Yoshida

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

variable {G : Type} [Group G] [Finite G]

theorem OUp_le (M : Subgroup G) : OUp 3 M ≤ M := Subgroup.map_subtype_le _

theorem OUp_conj_mem {M : Subgroup G} {g z : G} (hg : g ∈ M) (hz : z ∈ OUp 3 M) :
    g * z * g⁻¹ ∈ OUp 3 M := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
  exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, Subgroup.normalClosure_normal.conj_mem y hy ⟨g, hg⟩, rfl⟩

abbrev NC (M : Subgroup G) : Subgroup ↥M :=
  Subgroup.normalClosure {g : M | Nat.Coprime 3 (orderOf g)}

theorem isPGroup_quot_NC (M : Subgroup G) : IsPGroup 3 (↥M ⧸ NC M) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : CFSG.GH74.GLS.oResidual 3 M ≤ NC M := by
    refine Subgroup.closure_le _ |>.mpr fun g hg => ?_
    exact Subgroup.subset_normalClosure (Nat.coprime_comm.mp hg)
  exact CFSG.RankThree.Transfer.isPGroup_quotient_of_oResidual_le (NC M) hL

theorem exists_pow_mem_OUp (M : Subgroup G) {n : G} (hn : n ∈ M) :
    ∃ k : ℕ, n ^ 3 ^ k ∈ OUp 3 M := by
  obtain ⟨k, hk⟩ := isPGroup_quot_NC M (QuotientGroup.mk ⟨n, hn⟩)
  have hN : (⟨n, hn⟩ : M) ^ 3 ^ k ∈ NC M := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hk
  exact ⟨k, ⟨_, hN, by simp⟩⟩

theorem mem_OUp_of_inv {M : Subgroup G} {n x : G} (hn : n ∈ M) (hx : x ∈ M) (hx3 : x ^ 3 = 1)
    (hinv : n * x * n⁻¹ = x⁻¹) : x ∈ OUp 3 M := by
  obtain ⟨k, hk⟩ := exists_pow_mem_OUp M hn
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  have hconj : ∀ m : ℕ, n ^ m * x * (n ^ m)⁻¹ = x ^ ((-1 : ℤ) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : n ^ (m + 1) * x * (n ^ (m + 1))⁻¹ = n * (n ^ m * x * (n ^ m)⁻¹) * n⁻¹ := by
        rw [pow_succ', mul_inv_rev]; group
      rw [h1, ih, ← conj_zpow, hinv, ← zpow_neg_one, ← zpow_mul]
      congr 1
      rw [pow_succ]
      ring
  have hc : n ^ 3 ^ k * x * (n ^ 3 ^ k)⁻¹ = x⁻¹ := by
    rw [hconj, hodd.neg_one_pow, zpow_neg_one]
  have hmem : n ^ 3 ^ k * (x * (n ^ 3 ^ k)⁻¹ * x⁻¹) ∈ OUp 3 M :=
    (OUp 3 M).mul_mem hk (OUp_conj_mem hx ((OUp 3 M).inv_mem hk))
  have heq : n ^ 3 ^ k * (x * (n ^ 3 ^ k)⁻¹ * x⁻¹) = x := by
    calc n ^ 3 ^ k * (x * (n ^ 3 ^ k)⁻¹ * x⁻¹)
        = (n ^ 3 ^ k * x * (n ^ 3 ^ k)⁻¹) * x⁻¹ := by group
      _ = x⁻¹ * x⁻¹ := by rw [hc]
      _ = x := by
        have : x * x * x = 1 := (pow_three' x).symm.trans hx3
        calc x⁻¹ * x⁻¹ = x⁻¹ * x⁻¹ * (x * x * x) := by rw [this, mul_one]
          _ = x := by group
  rwa [heq] at hmem

theorem sylow_cen_beta {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    IsSylowOf 3 B (Cen (b₁ * b₂)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB := bgen_of_sec4 h4
  obtain ⟨hEl, hcardB⟩ := h4.mono.1
  have hcomm : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hEl.toIsMulCommutative.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hβB : b₁ * b₂ ∈ B := B.mul_mem hB.bmem.2.1 hB.bmem.2.2
  have hBle : B ≤ Cen (b₁ * b₂) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact hcomm _ hβB _ hx
  refine isSylowOf_of_max hBle (IsPGroup.of_card hcardB) ?_
  rintro y hyC hyN ⟨k, hk⟩
  have hβ : y * (b₁ * b₂) * y⁻¹ = b₁ * b₂ := by
    have := (Subgroup.mem_centralizer_iff.mp hyC) (b₁ * b₂) rfl
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  obtain ⟨h1, h2⟩ := mono_fix_beta h4 hyN hβ
  have key : ∀ x : G, (y * x * y⁻¹ = x ∨ y * x * y⁻¹ = x⁻¹) →
      (y * y) * x * (y * y)⁻¹ = x := by
    intro x hx
    have e : (y * y) * x * (y * y)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by group
    rcases hx with hx | hx
    · rw [e, hx, hx]
    · rw [e, hx, ← conj_inv, hx, inv_inv]
  have hsw : ∀ x₁ x₂ : G, y * x₁ * y⁻¹ = x₂ → y * x₂ * y⁻¹ = x₁ →
      (y * y) * x₁ * (y * y)⁻¹ = x₁ := by
    intro x₁ x₂ ha hb
    have e : (y * y) * x₁ * (y * y)⁻¹ = y * (y * x₁ * y⁻¹) * y⁻¹ := by group
    rw [e, ha, hb]
  have hb : (y * y) * b * (y * y)⁻¹ = b := key b h1
  have hb₁ : (y * y) * b₁ * (y * y)⁻¹ = b₁ := by
    rcases h2 with ⟨ha, -⟩ | ⟨ha, hc⟩
    · exact key b₁ (Or.inl ha)
    · exact hsw b₁ b₂ ha hc
  have hb₂ : (y * y) * b₂ * (y * y)⁻¹ = b₂ := by
    rcases h2 with ⟨-, ha⟩ | ⟨hc, ha⟩
    · exact key b₂ (Or.inl ha)
    · exact hsw b₂ b₁ ha hc
  have hgen : B ≤ Subgroup.centralizer ({y * y} : Set G) := by
    rw [h4.mono.2.1, Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact mul_inv_eq_iff_eq_mul.mp hb
    · exact mul_inv_eq_iff_eq_mul.mp hb₁
    · exact mul_inv_eq_iff_eq_mul.mp hb₂
  obtain ⟨t, ht⟩ := (Odd.pow (by decide : Odd 3) : Odd (3 ^ k))
  have hyw : (y * y) ^ (t + 1) = y := by
    rw [← pow_two, ← pow_mul, show 2 * (t + 1) = 3 ^ k + 1 by omega, pow_succ, hk, one_mul]
  have hybc : y ∈ Cen b := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have hc : Commute b (y * y) :=
      (Subgroup.mem_centralizer_iff.mp (hgen hB.bmem.1) (y * y) rfl).symm
    have := (hc.pow_right (t + 1)).eq
    rw [hyw] at this
    exact this
  exact mem_of_normalizes h4.sylB hybc hyN hk

theorem cen_beta_aux {b : G} {J B : Subgroup G} {b₁ b₂ : G} (h4 : FF79Sec4 b J B b₁ b₂) :
    b₁ * b₂ ∉ OUp 3 (Cen (b₁ * b₂)) ∧
    Subgroup.closure {b, b₁ ^ 2 * b₂} ≤ OUp 3 (Cen (b₁ * b₂)) ∧
    Nat.card (↥(Cen (b₁ * b₂)) ⧸ NC (Cen (b₁ * b₂))) = 3 ∧
    (Nat.card (OUp 3 (Cen (b₁ * b₂)))).factorization 3 = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB := bgen_of_sec4 h4
  obtain ⟨hEl, hcardB⟩ := h4.mono.1
  have hSyl := sylow_cen_beta h4
  have hBM : B ≤ Cen (b₁ * b₂) := hSyl.1
  have hβB : b₁ * b₂ ∈ B := B.mul_mem hB.bmem.2.1 hB.bmem.2.2
  have hγB : b₁ ^ 2 * b₂ ∈ B := B.mul_mem (B.pow_mem hB.bmem.2.1 2) hB.bmem.2.2
  have hβH : b₁ * b₂ ∉ OUp 3 (Cen (b₁ * b₂)) := by
    refine not_mem_OUp_of_hom (Cen (b₁ * b₂)) B hSyl hEl (psi hB) ?_ ⟨b₁ * b₂, hβB⟩
      (psi_beta hB)
    intro n hn x y hxy
    refine psi_invariant h4 hn.2 ?_ x y hxy
    have := (Subgroup.mem_centralizer_iff.mp hn.1) (b₁ * b₂) rfl
    exact mul_inv_eq_iff_eq_mul.mpr this.symm
  obtain ⟨n₀, -, hn₀C, hn₀⟩ := exists_inv_b h4
  obtain ⟨t, htC, ht⟩ := exists_inv_gamma h4
  have hγ3 : (b₁ ^ 2 * b₂) ^ 3 = 1 := by
    have hg : b₁ ^ 2 * b₂ = crd b b₁ b₂ (0, 2, 1) := by simp [crd]
    rw [hg, pow_three', hB.crd_mul, hB.crd_mul, ← hB.crd_zero]
    exact hB.crd_eq_of_dvd ⟨by simp, by simp, by simp⟩
  have hbH : b ∈ OUp 3 (Cen (b₁ * b₂)) :=
    mem_OUp_of_inv hn₀C (hBM hB.bmem.1) hB.cube.1 hn₀
  have hγH : b₁ ^ 2 * b₂ ∈ OUp 3 (Cen (b₁ * b₂)) :=
    mem_OUp_of_inv htC (hBM hγB) hγ3 ht
  have hAH : Subgroup.closure {b, b₁ ^ 2 * b₂} ≤ OUp 3 (Cen (b₁ * b₂)) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hbH
    · exact hγH
  have hA9 := card_closure hB hcardB
  obtain ⟨s, hs⟩ := (isPGroup_quot_NC (Cen (b₁ * b₂))).exists_card_eq
  have hNH : Nat.card (OUp 3 (Cen (b₁ * b₂))) = Nat.card (NC (Cen (b₁ * b₂))) :=
    Subgroup.card_map_of_injective (Cen (b₁ * b₂)).subtype_injective
  have hmul := Subgroup.card_mul_index (NC (Cen (b₁ * b₂)))
  rw [Subgroup.index_eq_card, hs] at hmul
  have hMv : (Nat.card (Cen (b₁ * b₂))).factorization 3 = 3 := by
    have := L14.isSylowOf_card hSyl
    rw [hcardB] at this
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) this).symm
  have hc0 : Nat.card (NC (Cen (b₁ * b₂))) ≠ 0 := Nat.card_pos.ne'
  have hfac : (Nat.card (Cen (b₁ * b₂))).factorization 3 =
      (Nat.card (NC (Cen (b₁ * b₂)))).factorization 3 + s := by
    rw [← hmul, Nat.factorization_mul hc0 (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  have h9 : 9 ∣ Nat.card (NC (Cen (b₁ * b₂))) := by
    have := Subgroup.card_dvd_of_le hAH
    rwa [hA9, hNH] at this
  have hv2 : 2 ≤ (Nat.card (NC (Cen (b₁ * b₂)))).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hc0).mp
      (by simpa using h9)
  have hs0 : s ≠ 0 := by
    rintro rfl
    have h1 : (NC (Cen (b₁ * b₂))).index = 1 := by
      rw [Subgroup.index_eq_card, hs]; rfl
    rw [Subgroup.index_eq_one] at h1
    have hmemN : (⟨b₁ * b₂, hBM hβB⟩ : ↥(Cen (b₁ * b₂))) ∈ NC (Cen (b₁ * b₂)) := by
      rw [h1]; trivial
    exact hβH ⟨_, hmemN, rfl⟩
  have hs1 : s = 1 := by omega
  subst hs1
  refine ⟨hβH, hAH, by simpa using hs, ?_⟩
  rw [hNH]
  omega

theorem cen_beta_decomp {b : G} {J B : Subgroup G} {b₁ b₂ : G}
    (h4 : FF79Sec4 b J B b₁ b₂) :
    (Subgroup.zpowers (b₁ * b₂) ⊔ OUp 3 (Cen (b₁ * b₂)) = Cen (b₁ * b₂) ∧
      Subgroup.zpowers (b₁ * b₂) ⊓ OUp 3 (Cen (b₁ * b₂)) = ⊥) ∧
    IsSylowOf 3 (Subgroup.closure {b, b₁ ^ 2 * b₂}) (OUp 3 (Cen (b₁ * b₂))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB := bgen_of_sec4 h4
  obtain ⟨hβH, hAH, hQ, hv⟩ := cen_beta_aux h4
  have hA9 := card_closure hB h4.mono.1.2
  have hβ3 : (b₁ * b₂) ^ 3 = 1 := by
    have hg : b₁ * b₂ = crd b b₁ b₂ (0, 1, 1) := by simp [crd]
    rw [hg, pow_three', hB.crd_mul, hB.crd_mul, ← hB.crd_zero]
    exact hB.crd_eq_of_dvd ⟨by simp, by simp, by simp⟩
  have hβM : b₁ * b₂ ∈ Cen (b₁ * b₂) := Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
  refine ⟨⟨?_, ?_⟩, L14.isSylowOf_of_card hAH (by rw [hA9, hv]; norm_num)⟩
  · refine le_antisymm (sup_le ?_ (OUp_le _)) fun m hm => ?_
    · rw [Subgroup.zpowers_le]; exact hβM
    · have hgen := zpowers_eq_top_of_prime_card hQ
        (g := (QuotientGroup.mk ⟨b₁ * b₂, hβM⟩ : ↥(Cen (b₁ * b₂)) ⧸ NC (Cen (b₁ * b₂))))
        (by
          intro h
          exact hβH ⟨⟨b₁ * b₂, hβM⟩, by rwa [QuotientGroup.eq_one_iff] at h, rfl⟩)
      have hm' := Subgroup.mem_top (QuotientGroup.mk ⟨m, hm⟩ :
        ↥(Cen (b₁ * b₂)) ⧸ NC (Cen (b₁ * b₂)))
      rw [← hgen, Subgroup.mem_zpowers_iff] at hm'
      obtain ⟨i, hi⟩ := hm'
      have hmem : (⟨b₁ * b₂, hβM⟩ : ↥(Cen (b₁ * b₂))) ^ (-i) * ⟨m, hm⟩ ∈ NC (Cen (b₁ * b₂)) := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_zpow, zpow_neg,
          ← hi]
        simp
      have hy : (b₁ * b₂) ^ (-i) * m ∈ OUp 3 (Cen (b₁ * b₂)) := ⟨_, hmem, rfl⟩
      have := Subgroup.mul_mem_sup (Subgroup.zpow_mem_zpowers (b₁ * b₂) i) hy
      rwa [show (b₁ * b₂) ^ i * ((b₁ * b₂) ^ (-i) * m) = m by group] at this
  · rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx1
    rw [Subgroup.mem_bot]
    have hmod : (b₁ * b₂) ^ i = (b₁ * b₂) ^ (i % 3) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv i 3, zpow_add, zpow_mul]
      have : (b₁ * b₂) ^ (3 : ℤ) = 1 := by exact_mod_cast hβ3
      rw [this, one_zpow, mul_one]
    rw [hmod] at hx2 ⊢
    have h3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h3 with h | h | h
    · rw [h]; simp
    · rw [h] at hx2; exact absurd (by simpa using hx2) hβH
    · rw [h] at hx2
      refine absurd ?_ hβH
      have := (OUp 3 (Cen (b₁ * b₂))).zpow_mem hx2 2
      rwa [← zpow_mul, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, show (3 : ℤ) = ((3 : ℕ) : ℤ)
        by norm_num, zpow_natCast, hβ3, one_mul, zpow_one] at this

theorem perfect_le_OUp_cen_beta {b : G} {J B : Subgroup G} {b₁ b₂ : G}
    (h4 : FF79Sec4 b J B b₁ b₂) {S : Subgroup G} (hS : S ≤ Cen (b₁ * b₂))
    (hP : Group.IsPerfect ↥S) : S ≤ OUp 3 (Cen (b₁ * b₂)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hβH, -, hQ, -⟩ := cen_beta_aux h4
  have hβM : b₁ * b₂ ∈ Cen (b₁ * b₂) := Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
  have hgen := zpowers_eq_top_of_prime_card hQ
    (g := (QuotientGroup.mk ⟨b₁ * b₂, hβM⟩ : ↥(Cen (b₁ * b₂)) ⧸ NC (Cen (b₁ * b₂))))
    (by
      intro h
      exact hβH ⟨⟨b₁ * b₂, hβM⟩, by rwa [QuotientGroup.eq_one_iff] at h, rfl⟩)
  have hcomm : ∀ q r : ↥(Cen (b₁ * b₂)) ⧸ NC (Cen (b₁ * b₂)), q * r = r * q := by
    intro q r
    have hq := Subgroup.mem_top q
    have hr := Subgroup.mem_top r
    rw [← hgen, Subgroup.mem_zpowers_iff] at hq hr
    obtain ⟨i, rfl⟩ := hq
    obtain ⟨j, rfl⟩ := hr
    exact ((Commute.refl _).zpow_zpow i j).eq
  have h1 : ⁅S, S⁆ = S := Subgroup.isPerfect_iff.mp hP
  rw [← h1]
  refine Subgroup.commutator_le.mpr fun s hs t ht => ?_
  have hmem : (⟨s * t * s⁻¹ * t⁻¹, by
      exact (Cen (b₁ * b₂)).mul_mem ((Cen (b₁ * b₂)).mul_mem ((Cen (b₁ * b₂)).mul_mem (hS hs)
        (hS ht)) ((Cen (b₁ * b₂)).inv_mem (hS hs))) ((Cen (b₁ * b₂)).inv_mem (hS ht))⟩ :
      ↥(Cen (b₁ * b₂))) ∈ NC (Cen (b₁ * b₂)) := by
    rw [← QuotientGroup.eq_one_iff]
    have := hcomm (QuotientGroup.mk ⟨s, hS hs⟩) (QuotientGroup.mk ⟨t, hS ht⟩)
    show (QuotientGroup.mk ((⟨s, hS hs⟩ : ↥(Cen (b₁ * b₂))) * ⟨t, hS ht⟩ * ⟨s, hS hs⟩⁻¹ *
      ⟨t, hS ht⟩⁻¹) : ↥(Cen (b₁ * b₂)) ⧸ NC (Cen (b₁ * b₂))) = 1
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [this]
    group
  exact ⟨_, hmem, rfl⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
