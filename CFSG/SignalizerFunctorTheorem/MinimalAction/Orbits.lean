module

public import CFSG.SignalizerFunctorTheorem.MinimalAction.HallHigman

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

section Auxiliary

variable {G : Type*} [Group G]

private theorem mem_normalizer_commutator_self {P : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (P : Set G)) :
    n ∈ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hn
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, hn]

private theorem commutatorElement_mul_mul_of_commute {z₁ z₂ a b : G} (h₁a : Commute z₁ a)
    (h₁b : Commute z₁ b) (h₂a : Commute z₂ a) (h₂b : Commute z₂ b) (h₁₂ : Commute z₁ z₂) :
    ⁅z₁ * a, z₂ * b⁆ = ⁅a, b⁆ := by
  have hcomm : ∀ {z : G}, Commute z a → Commute z b → Commute z ⁅a, b⁆ := by
    intro z hza hzb
    rw [commutatorElement_def]
    exact ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  have h2 : ⁅a, z₂ * b⁆ = ⁅a, b⁆ := by
    rw [commutatorElement_mul_right_eq_mul_conj, h₂a.symm.commutator_eq, one_mul,
      (hcomm h₂a h₂b).mul_inv_cancel]
  rw [commutatorElement_mul_left_eq_conj_mul, h2, (h₁₂.mul_right h₁b).commutator_eq, mul_one,
    (hcomm h₁a h₁b).mul_inv_cancel]

private theorem dvd_card_of_forall_dvd_index_stabilizer {B X : Type*} [Group B] [MulAction B X]
    [Finite X] {n : ℕ} (hn : ∀ a : X, n ∣ (MulAction.stabilizer B a).index) :
    n ∣ Nat.card X := by
  have : Fintype (MulAction.orbitRel.Quotient B X) := Fintype.ofFinite _
  rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits B X), Nat.card_sigma]
  refine Finset.dvd_sum fun ω _ => ?_
  have h1 := hn ω.out
  rw [MulAction.index_stabilizer] at h1
  exact h1

end Auxiliary

variable {G : Type*} [Group G] [Finite G]

namespace MinimalThree

variable {P : Subgroup G} {x : G}

theorem centralizes_of_fixed (h : MinimalThree P x) {y g : G} (hy : y ∈ Subgroup.zpowers x)
    (hg : g ∈ P) (hg' : g ∉ ⁅P, P⁆) (hyg : y * g = g * y) {c : G} (hc : c ∈ P) :
    y * c = c * y := by
  have hxy : x * y = y * x := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.refl x).zpow_right k).eq
  have hP'P : ⁅P, P⁆ ≤ P := Subgroup.commutator_le_of_le le_rfl le_rfl
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = P ⊓ Subgroup.centralizer {y} := ⟨_, rfl⟩
  have hCP : C ≤ P := by rw [hC]; exact inf_le_left
  have hCy : ∀ k ∈ C, y * k = k * y := by
    intro k hk
    rw [hC] at hk
    exact (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk).2).symm
  have hgC : g ∈ C := by
    rw [hC]
    exact Subgroup.mem_inf.mpr ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hyg.symm⟩
  have hxC : x ∈ Subgroup.normalizer (C : Set G) := by
    rw [hC]
    exact Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.mpr
      ⟨h.normalizes, Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hxy)⟩)
  have hxD : x ∈ Subgroup.normalizer ((⁅P, P⁆ ⊔ C : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr
      ⟨mem_normalizer_commutator_self h.normalizes, hxC⟩)
  have hCnorm : C ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) :=
    hCP.trans (Subgroup.normalizer_commutator_ge_left P P)
  rcases h.eq_commutator_or_eq le_sup_left (sup_le hP'P hCP) hxD with hD | hD
  · have hgD : g ∈ (⁅P, P⁆ ⊔ C : Subgroup G) := Subgroup.mem_sup_right hgC
    rw [hD] at hgD
    exact absurd hgD hg'
  ·
    have hdec : ∀ a ∈ P, ∃ z ∈ ⁅P, P⁆, ∃ k ∈ C, z * k = a := by
      intro a ha
      have ha' : a ∈ ((⁅P, P⁆ ⊔ C : Subgroup G) : Set G) := by
        rw [hD]
        exact ha
      rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCnorm] at ha'
      obtain ⟨z, hz, k, hk, hzk⟩ := Set.mem_mul.mp ha'
      exact ⟨z, hz, k, hk, hzk⟩
    have hcen : ∀ {z c : G}, z ∈ ⁅P, P⁆ → c ∈ P → Commute z c :=
      fun hz hc => h.commutator_central hz hc
    have hP'C : ⁅P, P⁆ ≤ C := by
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      obtain ⟨z₁, hz₁, c₁, hc₁, rfl⟩ := hdec a ha
      obtain ⟨z₂, hz₂, c₂, hc₂, rfl⟩ := hdec b hb
      rw [commutatorElement_mul_mul_of_commute (hcen hz₁ (hCP hc₁)) (hcen hz₁ (hCP hc₂))
        (hcen hz₂ (hCP hc₁)) (hcen hz₂ (hCP hc₂)) (hcen hz₁ (hP'P hz₂)), commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hc₁ hc₂) (C.inv_mem hc₁)) (C.inv_mem hc₂)
    obtain ⟨z, hz, k, hk, rfl⟩ := hdec c hc
    exact hCy _ (C.mul_mem (hP'C hz) hk)

theorem nine_dvd_index_centralizer (h : MinimalThree P x) :
    9 ∣ ((Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.zpowers x)).index := by
  obtain ⟨K, hK⟩ : ∃ K : Subgroup (Subgroup.zpowers x),
      K = (Subgroup.centralizer (P : Set G)).subgroupOf (Subgroup.zpowers x) := ⟨_, rfl⟩
  rw [← hK]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨m, hm⟩ := h.threeGroup.exists_card_eq
  have hdvd : K.index ∣ 3 ^ m := by
    rw [← hm]
    exact K.index_dvd_card
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hnot : ¬ K.index ∣ 3 := by
    rintro ⟨t, ht⟩
    obtain ⟨g, hg, hne⟩ := h.nontrivial
    apply hne
    have hmem : (⟨x, Subgroup.mem_zpowers x⟩ : Subgroup.zpowers x) ^ 3 ∈ K := by
      rw [ht, pow_mul]
      exact pow_mem (K.pow_index_mem _) t
    rw [hK, Subgroup.mem_subgroupOf] at hmem
    exact (Subgroup.mem_centralizer_iff.mp hmem g hg).symm
  have he2 : 2 ≤ e := by
    by_contra hlt
    have he01 : e = 0 ∨ e = 1 := by omega
    apply hnot
    rw [he]
    rcases he01 with rfl | rfl <;> simp
  rw [he]
  exact (by norm_num : (9 : ℕ) ∣ 3 ^ 2).trans (pow_dvd_pow 3 he2)

theorem card_modEq_nine (h : MinimalThree P x) :
    Nat.card P ≡ Nat.card (⁅P, P⁆ : Subgroup G) [MOD 9] := by
  have hP'P : ⁅P, P⁆ ≤ P := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hBP : Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.zpowers_le.mpr h.normalizes
  have hBP' : Subgroup.zpowers x ≤ Subgroup.normalizer ((⁅P, P⁆ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_commutator_self h.normalizes)
  obtain ⟨X, hX⟩ : ∃ X : Set G, X = (P : Set G) \ ((⁅P, P⁆ : Subgroup G) : Set G) := ⟨_, rfl⟩
  have hXmem : ∀ a, a ∈ X ↔ a ∈ P ∧ a ∉ ⁅P, P⁆ := by
    intro a
    rw [hX]
    exact Iff.rfl
  have hXstable : ∀ b ∈ Subgroup.zpowers x, ∀ a ∈ X, b * a * b⁻¹ ∈ X := by
    intro b hb a ha
    rw [hXmem] at ha ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hBP hb) a).mp ha.1,
      fun h' => ha.2 ((Subgroup.mem_normalizer_iff.mp (hBP' hb) a).mpr h')⟩
  let _ : MulAction (Subgroup.zpowers x) X :=
    { smul := fun b a => ⟨(b : G) * (a : G) * (b : G)⁻¹, hXstable b b.2 a a.2⟩
      one_smul := fun a => Subtype.ext (by
        show ((1 : Subgroup.zpowers x) : G) * (a : G) * ((1 : Subgroup.zpowers x) : G)⁻¹ = a
        simp)
      mul_smul := fun b b' a => Subtype.ext (by
        show ((b * b' : Subgroup.zpowers x) : G) * (a : G) *
            ((b * b' : Subgroup.zpowers x) : G)⁻¹ =
          (b : G) * ((b' : G) * (a : G) * (b' : G)⁻¹) * (b : G)⁻¹
        simp [mul_assoc]) }
  have hdvd : 9 ∣ Nat.card X := by
    refine dvd_card_of_forall_dvd_index_stabilizer (B := Subgroup.zpowers x) fun a => ?_
    refine (nine_dvd_index_centralizer h).trans (Subgroup.index_dvd_of_le fun b hb => ?_)
    have hba : (b : G) * a * (b : G)⁻¹ = a :=
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hb)
    have ha := (hXmem a).mp a.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro c hc
    exact (h.centralizes_of_fixed b.2 ha.1 ha.2 (mul_inv_eq_iff_eq_mul.mp hba) hc).symm
  have hcard : Nat.card X + Nat.card (⁅P, P⁆ : Subgroup G) = Nat.card P := by
    rw [hX]
    exact Set.ncard_sdiff_add_ncard_of_subset (s := ((⁅P, P⁆ : Subgroup G) : Set G))
      (t := (P : Set G)) hP'P
  calc Nat.card P = Nat.card X + Nat.card (⁅P, P⁆ : Subgroup G) := hcard.symm
    _ ≡ 0 + Nat.card (⁅P, P⁆ : Subgroup G) [MOD 9] :=
        (Nat.modEq_zero_iff_dvd.mpr hdvd).add_right _
    _ = Nat.card (⁅P, P⁆ : Subgroup G) := zero_add _

end MinimalThree

end CFSG.SignalizerFunctorTheorem.MinimalAction
