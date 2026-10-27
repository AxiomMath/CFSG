module

public import CFSG.RankThree.PartTwo.Sec10.Item107ProofGood

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item107Proof

section General

variable {G : Type} [Group G]

theorem conj_pow_eq_of_conj_eq {y z : G} (h : y * z * y⁻¹ = z) (n : ℕ) :
    y ^ n * z * (y ^ n)⁻¹ = z := by
  have hc : Commute y z := mul_inv_eq_iff_eq_mul.mp h
  rw [(hc.pow_left n).eq, mul_inv_cancel_right]

theorem exists_pow_eq_of_mem_zpowers {d y : G} (hd3 : d ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers d) : ∃ i : ℕ, y = d ^ i := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rcases zpow_cases_of_pow_three hd3 k with h | h | h
  · exact ⟨0, by rw [h, pow_zero]⟩
  · exact ⟨1, by rw [h, pow_one]⟩
  · exact ⟨2, h⟩

theorem mem_normalizer_of_closure_three [Finite G] {A : Subgroup G} {x y z : G}
    (hA : A = Subgroup.closure {x, y, z}) {w : G} (hx : w * x * w⁻¹ ∈ A)
    (hy : w * y * w⁻¹ ∈ A) (hz : w * z * w⁻¹ ∈ A) : w ∈ Subgroup.normalizer (A : Set G) := by
  apply mem_normalizer_of_conj_mem
  have hle : A ≤ A.comap (MulAut.conj w).toMonoidHom := by
    conv_lhs => rw [hA]
    rw [Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  intro q hq
  exact hle hq

theorem mulAut_ext_of_closure_three {A : Subgroup G} {x y z : G}
    (hA : A = Subgroup.closure {x, y, z}) (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (σ ρ : MulAut A) (h₁ : σ ⟨x, hx⟩ = ρ ⟨x, hx⟩) (h₂ : σ ⟨y, hy⟩ = ρ ⟨y, hy⟩)
    (h₃ : σ ⟨z, hz⟩ = ρ ⟨z, hz⟩) : σ = ρ := by
  set K := (MonoidHom.eqLocus σ.toMonoidHom ρ.toMonoidHom).map A.subtype with hK
  have hAK : A ≤ K := by
    conv_lhs => rw [hA]
    rw [Subgroup.closure_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl
    · exact ⟨⟨_, hx⟩, h₁, rfl⟩
    · exact ⟨⟨_, hy⟩, h₂, rfl⟩
    · exact ⟨⟨_, hz⟩, h₃, rfl⟩
  ext q
  obtain ⟨q', hq', hqq'⟩ := hAK q.2
  have : q' = q := Subtype.ext hqq'
  rw [← this]
  exact congrArg Subtype.val hq'

end General

end Item107Proof

section Std


theorem Item107Proof.exists_transvection_D (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h98 : Sec9.Item98) {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} {a : G} {R : Subgroup G} (h : Sec10Std G A c L a R) :
    ∀ e ∈ R ⊓ L, ∃ m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G),
      (∀ e' ∈ R ⊓ L, m * e' * m⁻¹ = e') ∧ m * c * m⁻¹ = c * e := by
  obtain ⟨x, hxL, hxN, hxo, hxfix⟩ := Item107Proof.exists_orderOf_thirteen h
  have hx13 : x ^ 13 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  rcases Item107Proof.good_or_bad h hxL hxN hx13 hxfix with hgood | hbad
  · exact hgood
  · exact (Item107Proof.false_of_bad h45 h97 h98 h hbad).elim

theorem item107_of (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h98 : Sec9.Item98) : Item107 := by
  intro G _ _ A c L a R h d hd hdL
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd3 : orderOf d = 3 := by
    rw [← Nat.card_zpowers, ← hdL, (h97 G A c L a R h.toHyp91).1]
  have hd3' : d ^ 3 = 1 := by rw [← hd3]; exact pow_orderOf_eq_one d
  have hd1 : d ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hd3; norm_num at hd3
  have hA : A = Subgroup.closure {c, a, d} := (h97 G A c L a R h.toHyp91).2 d hdL
  have hdE : d ∈ R ⊓ L := h.d_mem_inf hdL
  have hcomm : ∀ u v : G, u ∈ A → v ∈ A → u * v = v * u := fun u v hu hv => h.comm hu hv
  obtain ⟨v, hva, hvd, hvc⟩ := Item107Proof.exists_transvection_ad h45 h97 h hdL
    (Item107Proof.exists_transvection_D h45 h97 h98 h)
  have ha3 : a ^ 3 = 1 := h.pow_three h.a_mem
  have hda : a * d * a⁻¹ = d := by rw [hcomm a d h.a_mem hd, mul_inv_cancel_right]
  have hC : ∀ y ∈ R ⊓ L, a * y * a⁻¹ = y → y ∈ Subgroup.zpowers d := by
    intro y hy hya
    rw [← h.inf_centralizer_a hdL hA]
    refine ⟨hy, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc y * a = a * y * a⁻¹ * a := by rw [hya]
      _ = a * y := by group
  obtain ⟨x₁, hx₁E, hx₁d, hx₁1⟩ := KFacts.exists_commMap_mem_zpowers h.isElemAbelian_inf
    h.card_inf ha3 h.a_mem_normalizer_inf hdE hd1 hda hC
  set ε := (a * x₁ * a⁻¹ * x₁⁻¹)⁻¹ with hε
  have hεd : ε ∈ Subgroup.zpowers d := Subgroup.inv_mem _ hx₁d
  have hε1 : ε ≠ 1 := fun h1 => hx₁1 (inv_eq_one.mp h1)
  have hεA : ε ∈ A := Subgroup.zpowers_le.mpr hd hεd
  have hx₁a : x₁ * a * x₁⁻¹ = a * ε := by
    rw [hε, hcomm a _ h.a_mem (A.inv_mem (Subgroup.zpowers_le.mpr hd hx₁d))]
    group
  have hx₁c : x₁ * c * x₁⁻¹ = c := by
    rw [(h.commute_c_of_mem_inf hx₁E), mul_inv_cancel_right]
  have hEcomm : ∀ u v : G, u ∈ R ⊓ L → v ∈ R ⊓ L → u * v = v * u := fun u v hu hv =>
    congrArg Subtype.val (h.isElemAbelian_inf.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hεE : ε ∈ R ⊓ L := by
    rw [← h.inf_centralizer_a hdL hA] at hεd
    exact hεd.1
  have hx₁ε : x₁ * ε * x₁⁻¹ = ε := by rw [hEcomm _ _ hx₁E hεE, mul_inv_cancel_right]
  have hx₁d' : x₁ * d * x₁⁻¹ = d := by rw [hEcomm _ _ hx₁E hdE, mul_inv_cancel_right]
  intro σ hσ
  rw [Sec12.mem_transvectionGroup_iff] at hσ
  obtain ⟨hσd, hσA⟩ := hσ
  have hmem : ∀ q : A, q * (σ q)⁻¹ ∈ Subgroup.zpowers (⟨d, hd⟩ : A) →
      ((σ q : A) : G) * (q : G)⁻¹ ∈ Subgroup.zpowers d := by
    intro q hq
    have h1 := Subgroup.inv_mem _ hq
    rw [mul_inv_rev, inv_inv] at h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    have h2 := congrArg Subtype.val hk
    simp only [Subgroup.coe_zpow, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [← h2]
    exact Subgroup.zpow_mem_zpowers d k
  have hσc : ((σ ⟨c, h.mem_A⟩ : A) : G) * c⁻¹ ∈ Subgroup.zpowers d := by
    have h1 := hσA ⟨c, h.mem_A⟩
    have h2 : ((σ ⟨c, h.mem_A⟩ : A) : G) * c⁻¹ = (((σ ⟨c, h.mem_A⟩) * (⟨c, h.mem_A⟩ : A)⁻¹ : A) :
        G) := rfl
    rw [h2]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← hk]
    exact ⟨k, by simp⟩
  have hσa : ((σ ⟨a, h.a_mem⟩ : A) : G) * a⁻¹ ∈ Subgroup.zpowers d := by
    have h1 := hσA ⟨a, h.a_mem⟩
    have h2 : ((σ ⟨a, h.a_mem⟩ : A) : G) * a⁻¹ = (((σ ⟨a, h.a_mem⟩) * (⟨a, h.a_mem⟩ : A)⁻¹ : A) :
        G) := rfl
    rw [h2]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← hk]
    exact ⟨k, by simp⟩
  obtain ⟨i, hi⟩ := Item107Proof.exists_pow_eq_of_mem_zpowers hd3' hσc
  have hdε : d ∈ Subgroup.zpowers ε := KFacts.mem_zpowers_of_mem_zpowers_of_ne_one' hd3 hεd hε1
  have hε3 : ε ^ 3 = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hεd
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd3', one_zpow]
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ((σ ⟨a, h.a_mem⟩ : A) : G) * a⁻¹ = ε ^ t := by
    have h1 : ((σ ⟨a, h.a_mem⟩ : A) : G) * a⁻¹ ∈ Subgroup.zpowers ε :=
      (Subgroup.zpowers_le.mpr hdε) hσa
    exact Item107Proof.exists_pow_eq_of_mem_zpowers hε3 h1
  set g := v ^ i * x₁ ^ t with hg
  have hvt : v ^ i * c * (v ^ i)⁻¹ = c * d ^ i := conj_pow_iterate_eq hvc hvd i
  have hva' : ∀ n : ℕ, v ^ n * a * (v ^ n)⁻¹ = a := Item107Proof.conj_pow_eq_of_conj_eq hva
  have hvd' : ∀ n : ℕ, v ^ n * d * (v ^ n)⁻¹ = d := Item107Proof.conj_pow_eq_of_conj_eq hvd
  have hvε : ∀ n : ℕ, v ^ n * ε * (v ^ n)⁻¹ = ε := by
    intro n
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hεd
    rw [← hk, ← conj_zpow, hvd' n]
  have hx₁t : x₁ ^ t * a * (x₁ ^ t)⁻¹ = a * ε ^ t := conj_pow_iterate_eq hx₁a hx₁ε t
  have hx₁c' : x₁ ^ t * c * (x₁ ^ t)⁻¹ = c := Item107Proof.conj_pow_eq_of_conj_eq hx₁c t
  have hx₁d'' : x₁ ^ t * d * (x₁ ^ t)⁻¹ = d := Item107Proof.conj_pow_eq_of_conj_eq hx₁d' t
  have hgc : g * c * g⁻¹ = c * d ^ i := by
    calc g * c * g⁻¹ = v ^ i * (x₁ ^ t * c * (x₁ ^ t)⁻¹) * (v ^ i)⁻¹ := by rw [hg]; group
      _ = c * d ^ i := by rw [hx₁c', hvt]
  have hga : g * a * g⁻¹ = a * ε ^ t := by
    calc g * a * g⁻¹ = v ^ i * (x₁ ^ t * a * (x₁ ^ t)⁻¹) * (v ^ i)⁻¹ := by rw [hg]; group
      _ = (v ^ i * a * (v ^ i)⁻¹) * (v ^ i * ε * (v ^ i)⁻¹) ^ t := by
          rw [hx₁t, conj_pow]; group
      _ = a * ε ^ t := by rw [hva', hvε]
  have hgd : g * d * g⁻¹ = d := by
    calc g * d * g⁻¹ = v ^ i * (x₁ ^ t * d * (x₁ ^ t)⁻¹) * (v ^ i)⁻¹ := by rw [hg]; group
      _ = d := by rw [hx₁d'', hvd']
  have hgN : g ∈ Subgroup.normalizer (A : Set G) := by
    apply Item107Proof.mem_normalizer_of_closure_three hA
    · rw [hgc]
      exact A.mul_mem h.mem_A (A.pow_mem hd i)
    · rw [hga]
      exact A.mul_mem h.a_mem (A.pow_mem hεA t)
    · rw [hgd]
      exact hd
  have hσg : σ = A.normalizerMonoidHom ⟨g, hgN⟩ := by
    apply Item107Proof.mulAut_ext_of_closure_three hA h.mem_A h.a_mem hd
    · apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe, hgc, ← hi, ← mul_assoc,
        hcomm c _ h.mem_A (σ ⟨c, h.mem_A⟩).2, mul_inv_cancel_right]
    · apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe, hga, ← ht, ← mul_assoc,
        hcomm a _ h.a_mem (σ ⟨a, h.a_mem⟩).2, mul_inv_cancel_right]
    · apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe, hgd]
      exact congrArg Subtype.val hσd
  rw [hσg]
  exact Sec4.mem_autIn_iff.mpr ⟨g, hgN, Subgroup.mem_top g, rfl⟩

end Std

end CFSG.RankThree.PartTwo.Sec10
