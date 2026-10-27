module

public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.KFacts.L34

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.Asc83Table

variable {k : Type*} [Field k]

section Transitive

variable {u : kˣ}

theorem conj_conj_eq {G : Type*} [Group G] (m n y : G) :
    m * n * y * (m * n)⁻¹ = m * (n * y * n⁻¹) * m⁻¹ := by group

theorem conj_inv_eq {G : Type*} [Group G] (n y : G) : n * y⁻¹ * n⁻¹ = (n * y * n⁻¹)⁻¹ := by
  group

variable (hk : Nat.card k = 4) (hu : u ≠ 1)
include hk hu

theorem fP_sq_conj_aP : fP hk hu * fP hk hu * aP u * (fP hk hu * fP hk hu)⁻¹ = (aP u)⁻¹ := by
  rw [conj_conj_eq, fP_conj_aP hk hu, fP_conj_bP hk hu]

theorem fP_inv_conj_bP : (fP hk hu)⁻¹ * bP * fP hk hu = aP u := by
  rw [← fP_conj_aP hk hu]
  group

theorem fP_inv_conj_aP : (fP hk hu)⁻¹ * aP u * fP hk hu = bP⁻¹ := by
  calc (fP hk hu)⁻¹ * aP u * fP hk hu = ((fP hk hu)⁻¹ * (aP u)⁻¹ * fP hk hu)⁻¹ := by group
    _ = ((fP hk hu)⁻¹ * (fP hk hu * bP * (fP hk hu)⁻¹) * fP hk hu)⁻¹ := by
        rw [fP_conj_bP hk hu]
    _ = bP⁻¹ := by group

theorem fP_inv_jP_conj_aP :
    (fP hk hu)⁻¹ * jP hk hu * aP u * ((fP hk hu)⁻¹ * jP hk hu)⁻¹ = aP u * bP := by
  have h1 := fP_inv_conj_bP hk hu
  have h2 := fP_inv_conj_aP hk hu
  rw [conj_conj_eq, jP_conj_aP hk hu]
  calc (fP hk hu)⁻¹ * (bP * (aP u)⁻¹) * (fP hk hu)⁻¹⁻¹ =
        ((fP hk hu)⁻¹ * bP * fP hk hu) * ((fP hk hu)⁻¹ * aP u * fP hk hu)⁻¹ := by group
    _ = aP u * bP := by rw [h1, h2, inv_inv]

theorem exists_mem_normalizer_conj_eq {x : projectiveSL 3 k} (hx : x ∈ eZero k) (hx1 : x ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)), n * aP u * n⁻¹ = x := by
  have hf := fP_mem_normalizer hk hu
  have hj := jP_mem_normalizer hk hu
  have ha3 : aP u ^ 3 = 1 := pow_three_of_mem_eZero hk aP_mem_eZero
  have hb3 : (bP : projectiveSL 3 k) ^ 3 = 1 := pow_three_of_mem_eZero hk bP_mem_eZero
  have hab : Commute (aP u) bP := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hff := mul_mem hf hf
  have hfj := mul_mem (inv_mem hf) hj
  obtain ⟨i, j, hi, hj', rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hx
  interval_cases i <;> interval_cases j
  · simp at hx1
  · exact ⟨_, hf, by rw [fP_conj_aP hk hu]; simp⟩
  · refine ⟨_, mul_mem hf hff, ?_⟩
    rw [conj_conj_eq, fP_sq_conj_aP hk hu, conj_inv_eq, fP_conj_aP hk hu,
      sq_eq_inv_of_pow_three hb3]
    simp
  · exact ⟨1, one_mem _, by simp⟩
  · exact ⟨_, hfj, by rw [fP_inv_jP_conj_aP hk hu]; simp⟩
  · refine ⟨_, mul_mem hj hff, ?_⟩
    rw [conj_conj_eq, fP_sq_conj_aP hk hu, conj_inv_eq, jP_conj_aP hk hu,
      sq_eq_inv_of_pow_three hb3]
    group
  · refine ⟨_, hff, ?_⟩
    rw [fP_sq_conj_aP hk hu, sq_eq_inv_of_pow_three ha3]
    simp
  · refine ⟨_, hj, ?_⟩
    rw [jP_conj_aP hk hu, sq_eq_inv_of_pow_three ha3, pow_one]
    exact (hab.inv_left).eq.symm
  · refine ⟨_, mul_mem hfj hff, ?_⟩
    rw [conj_conj_eq, fP_sq_conj_aP hk hu, conj_inv_eq, fP_inv_jP_conj_aP hk hu,
      sq_eq_inv_of_pow_three ha3, sq_eq_inv_of_pow_three hb3, ← _root_.mul_inv_rev, ← hab.eq]

theorem fP_inv_jP_conj_bP :
    (fP hk hu)⁻¹ * jP hk hu * bP * ((fP hk hu)⁻¹ * jP hk hu)⁻¹ = aP u * bP ^ 2 := by
  have h1 := fP_inv_conj_bP hk hu
  have h2 := fP_inv_conj_aP hk hu
  have hab : Commute (aP u) bP := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  rw [conj_conj_eq, jP_conj_bP hk hu]
  calc (fP hk hu)⁻¹ * ((aP u)⁻¹ * bP * (aP u)⁻¹) * (fP hk hu)⁻¹⁻¹ =
        ((fP hk hu)⁻¹ * aP u * fP hk hu)⁻¹ * ((fP hk hu)⁻¹ * bP * fP hk hu) *
          ((fP hk hu)⁻¹ * aP u * fP hk hu)⁻¹ := by group
    _ = bP * aP u * bP := by rw [h1, h2, inv_inv]
    _ = aP u * bP ^ 2 := by rw [← hab.eq, sq, mul_assoc]

end Transitive

section Automizer

theorem centralizer_eZero (hk : Nat.card k = 4) :
    Subgroup.centralizer (eZero k : Set (projectiveSL 3 k)) = eZero k := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  apply le_antisymm
  · exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr aP_mem_eZero)).trans
      (centralizer_aP hk hu).le
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact commute_of_mem_eZero hk hy hx

variable {u : kˣ}

theorem qI_mem_range (hk : Nat.card k = 4) (hu : u ≠ 1) : qI ∈ (eZeroBasis hk hu).rhoE.range := by
  have hb3 : (bP : projectiveSL 3 k) ^ 3 = 1 := pow_three_of_mem_eZero hk bP_mem_eZero
  refine (eZeroBasis hk hu).mem_range_of_conj (g := fP hk hu) 0 2 1 0 ?_ ?_ (by decide)
  · change fP hk hu * aP u * (fP hk hu)⁻¹ = aP u ^ 0 * bP ^ 1
    rw [fP_conj_aP hk hu]
    simp
  · change fP hk hu * bP * (fP hk hu)⁻¹ = aP u ^ 2 * bP ^ 0
    rw [fP_conj_bP hk hu, sq_eq_inv_of_pow_three (pow_three_of_mem_eZero hk aP_mem_eZero)]
    simp

theorem qJ_mem_range (hk : Nat.card k = 4) (hu : u ≠ 1) : qJ ∈ (eZeroBasis hk hu).rhoE.range := by
  refine (eZeroBasis hk hu).mem_range_of_conj (g := (fP hk hu)⁻¹ * jP hk hu) 1 1 1 2 ?_ ?_
    (by decide)
  · change (fP hk hu)⁻¹ * jP hk hu * aP u * ((fP hk hu)⁻¹ * jP hk hu)⁻¹ = aP u ^ 1 * bP ^ 1
    rw [fP_inv_jP_conj_aP hk hu]
    simp
  · change (fP hk hu)⁻¹ * jP hk hu * bP * ((fP hk hu)⁻¹ * jP hk hu)⁻¹ = aP u ^ 1 * bP ^ 2
    rw [fP_inv_jP_conj_bP hk hu, pow_one]

theorem card_normalizer_eq_mul (hk : Nat.card k = 4) (hu : u ≠ 1) :
    Nat.card (Subgroup.normalizer (eZero k : Set (projectiveSL 3 k))) =
      Nat.card (eZeroBasis hk hu).rhoE.range * 9 := by
  set E := eZeroBasis hk hu
  have hsub : E.sub = eZero k := eZeroBasis_sub hk hu
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Subgroup.centralizer (E.sub : Set (projectiveSL 3 k))).subgroupOf
      (Subgroup.normalizer (E.sub : Set (projectiveSL 3 k))))
  have h2 : Nat.card (Automizer E.sub) = Nat.card E.rhoE.range :=
    Nat.card_congr E.automizerEquiv.toEquiv
  change Nat.card _ = Nat.card (Automizer E.sub) * _ at h1
  rw [h2, hsub, centralizer_eZero hk] at h1
  have hle : eZero k ≤ Subgroup.normalizer (eZero k : Set (projectiveSL 3 k)) :=
    Subgroup.le_normalizer
  rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_eZero hk]

theorem quatHom_range_le (hk : Nat.card k = 4) (hu : u ≠ 1) :
    quatHom.range ≤ (eZeroBasis hk hu).rhoE.range := by
  rw [range_quatHom, Subgroup.closure_le]
  rintro _ (rfl | rfl)
  · exact qI_mem_range hk hu
  · exact qJ_mem_range hk hu

theorem card_range_quatHom : Nat.card quatHom.range = 8 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective quatHom_injective).toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem card_range_rhoE (hk : Nat.card k = 4) (hu : u ≠ 1) :
    Nat.card (eZeroBasis hk hu).rhoE.range = 8 := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h8 : 8 ∣ Nat.card (eZeroBasis hk hu).rhoE.range :=
    card_range_quatHom ▸ Subgroup.card_dvd_of_le (quatHom_range_le hk hu)
  have h48 : Nat.card (eZeroBasis hk hu).rhoE.range ∣ 48 := (eZeroBasis hk hu).card_range_dvd
  set N := Subgroup.normalizer (eZero k : Set (projectiveSL 3 k))
  have hidx : Nat.card (projectiveSL 3 k) = Nat.card N * N.index :=
    (Subgroup.card_mul_index N).symm
  have hsyl := card_sylow_modEq_one 3 (projectiveSL 3 k)
  rw [Sylow.card_eq_index_normalizer (eZeroSylow hk)] at hsyl
  change N.index ≡ 1 [MOD 3] at hsyl
  rw [card_projectiveSL hk, card_normalizer_eq_mul hk hu] at hidx
  have hmod : N.index % 3 = 1 := hsyl
  obtain ⟨m, hm⟩ := h8
  have hm6 : m ∣ 6 := by
    rw [hm, show (48 : ℕ) = 8 * 6 by norm_num] at h48
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h48
  have hm6' : m ≤ 6 := Nat.le_of_dvd (by norm_num) hm6
  rw [hm] at hidx ⊢
  interval_cases m <;> omega

theorem card_normalizer_eZero (hk : Nat.card k = 4) :
    Nat.card (Subgroup.normalizer (eZero k : Set (projectiveSL 3 k))) = 72 := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  rw [card_normalizer_eq_mul hk hu, card_range_rhoE hk hu]

theorem nonempty_automizer_eZero (hk : Nat.card k = 4) :
    Nonempty (Automizer (eZero k) ≃* QuaternionGroup 2) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have heq : quatHom.range = (eZeroBasis hk hu).rhoE.range :=
    Subgroup.eq_of_le_of_card_ge (quatHom_range_le hk hu)
      (by rw [card_range_quatHom, card_range_rhoE hk hu])
  obtain ⟨e⟩ := (eZeroBasis hk hu).nonempty_quaternion (qI_mem_range hk hu) (qJ_mem_range hk hu)
    heq.ge
  exact ⟨(automizerOfEq (eZeroBasis_sub hk hu)).symm.trans e⟩

theorem nonempty_automizer_of_card_eq_nine (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) : Nonempty (Automizer E ≃* QuaternionGroup 2) := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  obtain ⟨e₁⟩ := e9_automizer (eZeroBasis hk hu) (factorization_card hk) E hE
  obtain ⟨e₂⟩ := nonempty_automizer_eZero hk
  exact ⟨e₁.trans ((automizerOfEq (eZeroBasis_sub hk hu)).trans e₂)⟩

@[expose] noncomputable def automizerEquivAutIn {G : Type*} [Group G] (X : Subgroup G) :
    Automizer X ≃* Sec4.autIn ⊤ X :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.normalizerMonoidHom_ker X).symm).trans
    ((QuotientGroup.quotientKerEquivRange X.normalizerMonoidHom).trans
      (MulEquiv.subgroupCongr (by
        rw [Sec4.autIn, top_inf_eq, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map])))

theorem nonempty_autIn_of_card_eq_nine (hk : Nat.card k = 4) {E : Subgroup (projectiveSL 3 k)}
    (hE : Nat.card E = 9) : Nonempty (Sec4.autIn ⊤ E ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := nonempty_automizer_of_card_eq_nine hk hE
  exact ⟨(automizerEquivAutIn E).symm.trans e⟩

end Automizer

section General

variable {E : Subgroup (projectiveSL 3 k)}

theorem conj_mem_normalizer_map {G : Type*} [Group G] {B : Subgroup G} {g n : G}
    (hn : n ∈ Subgroup.normalizer (B : Set G)) :
    g * n * g⁻¹ ∈
      Subgroup.normalizer ((B.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨n * b * n⁻¹, (Subgroup.mem_normalizer_iff.mp hn b).mp hb, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨b, hb, hbz⟩
    refine ⟨n⁻¹ * b * n, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hn) b).mp hb
      simpa using this
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hbz ⊢
      calc g * (n⁻¹ * b * n) * g⁻¹ = (g * n * g⁻¹)⁻¹ * (g * b * g⁻¹) * (g * n * g⁻¹) := by group
        _ = (g * n * g⁻¹)⁻¹ * (g * n * g⁻¹ * z * (g * n * g⁻¹)⁻¹) * (g * n * g⁻¹) := by rw [hbz]
        _ = z := by group

theorem exists_mem_normalizer_conj_eq_of_card_eq_nine (hk : Nat.card k = 4)
    (hE : Nat.card E = 9) {x y : projectiveSL 3 k} (hx : x ∈ E) (hx1 : x ≠ 1) (hy : y ∈ E)
    (hy1 : y ≠ 1) : ∃ n ∈ Subgroup.normalizer (E : Set (projectiveSL 3 k)), n * x * n⁻¹ = y := by
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_eZero hk hE
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hx1 hy1 ⊢
  have hx₀1 : x₀ ≠ 1 := by rintro rfl; simp at hx1
  have hy₀1 : y₀ ≠ 1 := by rintro rfl; simp at hy1
  obtain ⟨n₁, hn₁, h₁⟩ := exists_mem_normalizer_conj_eq hk hu hx₀ hx₀1
  obtain ⟨n₂, hn₂, h₂⟩ := exists_mem_normalizer_conj_eq hk hu hy₀ hy₀1
  refine ⟨g * (n₂ * n₁⁻¹) * g⁻¹, conj_mem_normalizer_map (mul_mem hn₂ (inv_mem hn₁)), ?_⟩
  rw [← h₁, ← h₂]
  group

theorem exists_mem_normalizer_conj_not_mem (hk : Nat.card k = 4) (hE : Nat.card E = 9)
    {B : Subgroup (projectiveSL 3 k)} (hBE : B ≤ E) (hB : Nat.card B = 3) :
    ∃ n ∈ Subgroup.normalizer (E : Set (projectiveSL 3 k)), ∃ x ∈ B, n * x * n⁻¹ ∉ B := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B, x ≠ 1 := by
    by_contra h
    push Not at h
    have : B = ⊥ := eq_bot_iff.mpr fun x hx => h x hx
    rw [this, Subgroup.card_bot] at hB
    norm_num at hB
  obtain ⟨y, hyE, hyB⟩ : ∃ y ∈ E, y ∉ B := by
    by_contra h
    push Not at h
    have := Subgroup.card_le_of_le (fun y hy => h y hy : E ≤ B)
    omega
  have hy1 : y ≠ 1 := by rintro rfl; exact hyB (one_mem _)
  obtain ⟨n, hn, hnxy⟩ :=
    exists_mem_normalizer_conj_eq_of_card_eq_nine hk hE (hBE hxB) hx1 hyE hy1
  exact ⟨n, hn, x, hxB, by rw [hnxy]; exact hyB⟩

end General


end CFSG.RankThree.PartTwo.KFacts.L34
