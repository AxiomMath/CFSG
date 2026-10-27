module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofKG
public import CFSG.LocalAnalysis.StandardType.GGHypSixD4BstarRankTri
public import CFSG.RankThree.PartOne.KFOUT3.Galois
public import CFSG.RankThree.PartOne.KFOUT3.Torus

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGD4TrialityAutRank {R : Type} [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ A : Subgroup (MulAut R), IsElemAbelian 3 A → ∀ φ ∈ A,
    (¬ ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) → Nat.card A ≤ 81

@[expose] def GGD4TrialityAutRankNF {R : Type} [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ A : Subgroup (MulAut R), IsElemAbelian 3 A → ∀ φ ∈ A,
    (¬ ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f) → Nat.card A ≤ 27

namespace NbrGraphD4

section Count

variable {M : Type*} [Group M] [Finite M]

theorem card_le_three_mul {A S : Subgroup M} {c : M} (hc : c ∈ A)
    (h : ∀ a ∈ A, ∃ j < 3, a * c ^ j ∈ S) : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ S) := by
  have h' : ∀ a : A, ∃ j : Fin 3, (a : M) * c ^ (j : ℕ) ∈ A ⊓ S := fun a => by
    obtain ⟨j, hj3, hj⟩ := h a a.2
    exact ⟨⟨j, hj3⟩, mul_mem a.2 (pow_mem hc j), hj⟩
  choose j hj using h'
  have hinj : Function.Injective fun a : A =>
      ((⟨(a : M) * c ^ (j a : ℕ), hj a⟩ : ↥(A ⊓ S)), j a) := by
    intro a a' haa
    simp only [Prod.mk.injEq] at haa
    obtain ⟨h1, h2⟩ := haa
    have h1' : (a : M) * c ^ (j a : ℕ) = (a' : M) * c ^ (j a' : ℕ) := congrArg Subtype.val h1
    rw [h2] at h1'
    exact Subtype.ext (mul_right_cancel h1')
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_fin] at hle
  rw [mul_comm]
  exact hle

theorem exists_eq_pow_of_cube {C : Type*} [Group C] [Finite C] [IsCyclic C] {x y : C}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hy1 : y ≠ 1) : ∃ i < 3, x = y ^ i := by
  classical
  have := Fintype.ofFinite C
  by_contra hne
  push Not at hne
  have h0 : x ≠ 1 := by simpa using hne 0 (by norm_num)
  have h1 : x ≠ y := by simpa using hne 1 (by norm_num)
  have h2 : x ≠ y ^ 2 := hne 2 (by norm_num)
  have hy2 : (1 : C) ≠ y ^ 2 := fun h => hy1 (by
    have e : y = y ^ 3 * (y ^ 2)⁻¹ := by group
    rw [e, hy, ← h, inv_one, one_mul])
  have hyy : y ≠ y ^ 2 := fun h => hy1 (by
    have e : y * 1 = y * y := by rw [mul_one, ← pow_two]; exact h
    exact (mul_left_cancel e).symm)
  have hsub : ({x, 1, y, y ^ 2} : Finset C) ⊆ Finset.univ.filter fun a : C => a ^ 3 = 1 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hz with rfl | rfl | rfl | rfl
    · exact hx
    · exact one_pow 3
    · exact hy
    · rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have hcard : ({x, 1, y, y ^ 2} : Finset C).card = 4 := by
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h0, h1, h2⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨hy1.symm, hy2⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]; exact hyy), Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  have h3 := IsCyclic.card_pow_eq_one_le (α := C) (n := 3) (by norm_num)
  omega

theorem card_le_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {n : ℕ} {P : Y → Prop}
    (hY : ∀ A : Subgroup Y, IsElemAbelian 3 A → ∀ y ∈ A, P y → Nat.card A ≤ n)
    {A : Subgroup X} (hA : IsElemAbelian 3 A) {x : X} (hx : x ∈ A) (hP : P (e x)) :
    Nat.card A ≤ n := by
  have hA' : IsElemAbelian 3 (A.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := a
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := b
      apply Subtype.ext
      change e a * e b = e b * e a
      rw [← map_mul, ← map_mul,
        show a * b = b * a from congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)]
    · rintro _ ⟨a, ha, rfl⟩
      change e a ^ 3 = 1
      rw [← map_pow, hA.2 a ha, map_one]
  have h := hY _ hA' (e x) ⟨x, hx, rfl⟩ hP
  rwa [Subgroup.card_map_of_injective e.injective] at h

end Count

section Gamma

open CFSG.StandardType.Triality CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem conj_injective : Function.Injective (MulAut.conj : Om8 K →* MulAut (Om8 K)) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨z, rfl⟩ := (modelEquiv8 (K := K)).surjective γ
  have hz : z ∈ Subgroup.center (Sp8 K) := Subgroup.mem_center_iff.2 fun w => by
    apply (modelEquiv8 (K := K)).injective
    have h := congrArg (fun φ : MulAut (Om8 K) => φ (modelEquiv8 w)) hγ
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [map_mul, map_mul]
    calc modelEquiv8 w * modelEquiv8 z
        = modelEquiv8 z * modelEquiv8 w * (modelEquiv8 z)⁻¹ * modelEquiv8 z := by rw [h]
      _ = modelEquiv8 z * modelEquiv8 w := by group
  rw [RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := K) (n := 4) (by norm_num)]
    at hz
  rw [Subgroup.mem_bot.1 hz, map_one]

theorem fieldAutP_eq_one_of_mem_inner {σ : K ≃+* K} (h : AutOm.fieldAutP 4 σ ∈ Inn (Om8 K)) :
    AutOm.fieldAutP 4 σ = 1 :=
  (theta_pow_mul_mem_inner 0 ⟨σ, Or.inl rfl⟩ (by rwa [pow_zero, one_mul])).2

theorem isTriPart_zero_of_mem {a : MulAut (Om8 K)}
    (h : a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) : D4Bstar.IsTriPart 0 a := by
  obtain ⟨_, ⟨γ, rfl⟩, _, ⟨σ, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 h
  exact ⟨γ, σ, by rw [pow_zero, one_mul]⟩

theorem mem_of_isTriPart_zero {a : MulAut (Om8 K)} (h : D4Bstar.IsTriPart 0 a) :
    a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range := by
  obtain ⟨γ, σ, rfl⟩ := h
  rw [pow_zero, one_mul]
  exact Subgroup.mul_mem_sup ⟨γ, rfl⟩ ⟨σ, rfl⟩

theorem exists_isTriPart {a : MulAut (Om8 K)} (ha : a ^ 3 = 1) :
    ∃ k < 3, D4Bstar.IsTriPart k a := by
  by_cases hs : ∃ g : similarityPairs (coordinateQuadPlus 4 K), conjAct _ g = a
  · obtain ⟨g, hg⟩ := hs
    exact ⟨0, by norm_num, isTriPart_zero_of_mem (mem_inner_sup_of_conjAct ha hg)⟩
  · push Not at hs
    obtain ⟨γ, k, σ, hk, h⟩ := D4Rank.exists_conj_theta_pow_fieldAutP a ha hs
    exact ⟨k, by omega, γ, σ, h⟩

theorem exists_isTriPart_of_not_mem {α : MulAut (Om8 K)} (hα3 : α ^ 3 = 1)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    ∃ k, (k = 1 ∨ k = 2) ∧ D4Bstar.IsTriPart k α := by
  obtain ⟨γ, k, σ, hk, h⟩ := D4Rank.exists_conj_theta_pow_fieldAutP α hα3
    (fun g hg => hα (mem_inner_sup_of_conjAct hα3 hg))
  exact ⟨k, hk, γ, σ, h⟩

theorem exists_mul_pow_mem_sup {a α : MulAut (Om8 K)} (ha : a ^ 3 = 1) (hα3 : α ^ 3 = 1)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    ∃ j < 3, a * α ^ j ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range := by
  obtain ⟨k, hk3, hk⟩ := exists_isTriPart ha
  obtain ⟨kα, hkα, hTα⟩ := exists_isTriPart_of_not_mem hα3 hα
  have hj : (k + (3 - k) * kα % 3 * kα) % 3 = 0 := by
    rcases hkα with rfl | rfl <;> interval_cases k <;> norm_num
  refine ⟨(3 - k) * kα % 3, Nat.mod_lt _ (by norm_num), mem_of_isTriPart_zero ?_⟩
  have h := (hk.mul (hTα.pow ((3 - k) * kα % 3))).mod_three
  rwa [hj] at h

theorem fieldAutP_cube_eq_one {ι : MulAut (Om8 K)} (hι : ι ∈ Inn (Om8 K)) {σ : K ≃+* K}
    (h : (ι * AutOm.fieldAutP 4 σ) ^ 3 = 1) : AutOm.fieldAutP 4 σ ^ 3 = 1 := by
  obtain ⟨d, hd, hpow⟩ :=
    RecipeFieldOmega.exists_mul_pow_eq (Inn (Om8 K)) (f := AutOm.fieldAutP 4 σ) hι 3
  rw [h] at hpow
  have hmem : AutOm.fieldAutP 4 (σ ^ 3) ∈ Inn (Om8 K) := by
    rw [map_pow, eq_inv_mul_of_mul_eq hpow.symm, mul_one]
    exact inv_mem hd
  rw [← map_pow]
  exact fieldAutP_eq_one_of_mem_inner hmem

theorem exists_mul_pow_mem_inner [IsCyclic (K ≃+* K)] {a c : MulAut (Om8 K)}
    (ha : a ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)
    (hc : c ∈ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (hcI : c ∉ Inn (Om8 K)) : ∃ j < 3, a * c ^ j ∈ Inn (Om8 K) := by
  obtain ⟨ιa, hιa, _, ⟨σ, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 ha
  obtain ⟨ιc, hιc, _, ⟨τ, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hc
  have hfa3 := fieldAutP_cube_eq_one hιa ha3
  have hfc3 := fieldAutP_cube_eq_one hιc hc3
  have hfc1 : AutOm.fieldAutP 4 τ ≠ 1 := fun h => hcI (by
    change ιc * AutOm.fieldAutP 4 τ ∈ Inn (Om8 K)
    rw [h, mul_one]
    exact hιc)
  have : IsCyclic (AutOm.fieldAutP (K := K) 4).range :=
    isCyclic_of_surjective (AutOm.fieldAutP (K := K) 4).rangeRestrict
      (AutOm.fieldAutP (K := K) 4).rangeRestrict_surjective
  set Φ := (AutOm.fieldAutP (K := K) 4).range
  have hx : (⟨AutOm.fieldAutP 4 σ, σ, rfl⟩ : Φ) ^ 3 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hfa3)
  have hy : (⟨AutOm.fieldAutP 4 τ, τ, rfl⟩ : Φ) ^ 3 = 1 :=
    Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one]; exact hfc3)
  have hy1 : (⟨AutOm.fieldAutP 4 τ, τ, rfl⟩ : Φ) ≠ 1 := fun h => hfc1 (by
    have h' := congrArg Subtype.val h
    rwa [OneMemClass.coe_one] at h')
  obtain ⟨i, hi3, hi⟩ := exists_eq_pow_of_cube hx hy hy1
  have hi' : AutOm.fieldAutP 4 σ = AutOm.fieldAutP 4 τ ^ i := by
    have h' := congrArg Subtype.val hi
    rwa [SubgroupClass.coe_pow] at h'
  refine ⟨(3 - i) % 3, Nat.mod_lt _ (by norm_num), ?_⟩
  obtain ⟨d, hd, hpow⟩ := RecipeFieldOmega.exists_mul_pow_eq (Inn (Om8 K))
    (f := AutOm.fieldAutP 4 τ) hιc ((3 - i) % 3)
  rw [hpow, hi']
  set fc := AutOm.fieldAutP (K := K) 4 τ
  have hij : fc ^ i * fc ^ ((3 - i) % 3) = 1 := by
    rw [← pow_add]
    interval_cases i
    · rw [show (0 + (3 - 0) % 3) = 0 by norm_num, pow_zero]
    · rw [show (1 + (3 - 1) % 3) = 3 by norm_num, hfc3]
    · rw [show (2 + (3 - 2) % 3) = 3 by norm_num, hfc3]
  have e : ιa * fc ^ i * (d * fc ^ ((3 - i) % 3)) =
      ιa * (fc ^ i * d * (fc ^ i)⁻¹) * (fc ^ i * fc ^ ((3 - i) % 3)) := by
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [e, hij, mul_one]
  exact mul_mem hιa ((CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _).conj_mem
    d hd _)

end Gamma

section Bound

open CFSG.StandardType.Triality

local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_inf_inner_le_nine {A : Subgroup (MulAut (Om8 K))} (hA : IsElemAbelian 3 A)
    {α : MulAut (Om8 K)} (hαA : α ∈ A) (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) :
    Nat.card ↥(A ⊓ Inn (Om8 K)) ≤ 9 := by
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE : IsElemAbelian 3 (A.comap (MulAut.conj : Om8 K →* MulAut (Om8 K))) := by
    refine ⟨⟨⟨fun u v => Subtype.ext (conj_injective ?_)⟩⟩, fun γ hγ => conj_injective ?_⟩
    · change MulAut.conj ((u : Om8 K) * v) = MulAut.conj ((v : Om8 K) * u)
      rw [map_mul, map_mul]
      exact hcomm _ u.2 _ v.2
    · rw [map_pow, map_one]
      exact hA.2 _ hγ
  have hfix : ∀ γ ∈ A.comap (MulAut.conj : Om8 K →* MulAut (Om8 K)), α γ = γ := by
    intro γ hγ
    apply conj_injective
    have h2 := hcomm α hαA _ hγ
    rw [D4Rank.mulAut_mul_conj α γ] at h2
    exact mul_right_cancel h2
  have h9 := card_le_nine_of_not_mem (hA.2 α hαA) hα hE hfix
  have heq : A ⊓ Inn (Om8 K) =
      (A.comap (MulAut.conj : Om8 K →* MulAut (Om8 K))).map MulAut.conj := by
    ext a
    constructor
    · rintro ⟨haA, γ, rfl⟩
      exact ⟨γ, haA, rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact ⟨hγ, γ, rfl⟩
  rw [heq, Subgroup.card_map_of_injective conj_injective]
  exact h9

theorem card_le_81 [IsCyclic (K ≃+* K)] {A : Subgroup (MulAut (Om8 K))}
    (hA : IsElemAbelian 3 A) {α : MulAut (Om8 K)} (hαA : α ∈ A)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) : Nat.card A ≤ 81 := by
  have hα3 : α ^ 3 = 1 := hA.2 α hαA
  have h1 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) :=
    card_le_three_mul hαA fun a ha => exists_mul_pow_mem_sup (hA.2 a ha) hα3 hα
  have h9 := card_inf_inner_le_nine hA hαA hα
  have h2 : Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) ≤
      3 * Nat.card ↥(A ⊓ Inn (Om8 K)) := by
    by_cases hc : ∃ c ∈ A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range), c ∉ Inn (Om8 K)
    · obtain ⟨c, hcAS, hcI⟩ := hc
      have h := card_le_three_mul (S := Inn (Om8 K)) hcAS fun a ha =>
        exists_mul_pow_mem_inner ha.2 hcAS.2 (hA.2 a ha.1) (hA.2 c hcAS.1) hcI
      refine h.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le ?_))
      intro a ha
      exact ⟨ha.1.1, ha.2⟩
    · push Not at hc
      calc Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range))
          ≤ Nat.card ↥(A ⊓ Inn (Om8 K)) :=
            Subgroup.card_le_of_le fun a ha => ⟨ha.1, hc a ha⟩
        _ ≤ 3 * Nat.card ↥(A ⊓ Inn (Om8 K)) := Nat.le_mul_of_pos_left _ (by norm_num)
  omega

theorem ggD4TrialityAutRank_omegaPlus [IsCyclic (K ≃+* K)] :
    GGD4TrialityAutRank (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro A hA φ hφA hnot
  exact card_le_of_equiv (MulAut.congr (RecipeFieldOmega.plusEquiv (K := K) one_le_four))
    (P := fun α => α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)
    (fun A' hA' α hα hP => card_le_81 hA' hα hP) hA hφA
    (fun h => hnot (exists_inner_mul_field_of_mem h))

omit [Finite K] [CharP K 2] in
theorem fieldAutP_eq_one_of_cube (h3 : ¬ 3 ∣ Nat.card (K ≃+* K)) {σ : K ≃+* K}
    (h : AutOm.fieldAutP 4 σ ^ 3 = 1) : AutOm.fieldAutP 4 σ = 1 := by
  have h1 : orderOf (AutOm.fieldAutP 4 σ) ∣ 3 := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf (AutOm.fieldAutP 4 σ) ∣ orderOf σ := orderOf_map_dvd _ σ
  have h3' : orderOf σ ∣ Nat.card (K ≃+* K) := orderOf_dvd_natCard σ
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (h ▸ h2.trans h3') h3

theorem card_le_27 (h3 : ¬ 3 ∣ Nat.card (K ≃+* K)) {A : Subgroup (MulAut (Om8 K))}
    (hA : IsElemAbelian 3 A) {α : MulAut (Om8 K)} (hαA : α ∈ A)
    (hα : α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range) : Nat.card A ≤ 27 := by
  have hα3 : α ^ 3 = 1 := hA.2 α hαA
  have h1 : Nat.card A ≤ 3 * Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) :=
    card_le_three_mul hαA fun a ha => exists_mul_pow_mem_sup (hA.2 a ha) hα3 hα
  have h9 := card_inf_inner_le_nine hA hαA hα
  have h2 : Nat.card ↥(A ⊓ (Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)) ≤
      Nat.card ↥(A ⊓ Inn (Om8 K)) := by
    refine Subgroup.card_le_of_le fun a ha => ⟨ha.1, ?_⟩
    obtain ⟨ι, hι, _, ⟨σ, rfl⟩, hιa⟩ := Subgroup.mem_sup_of_normal_left.1 ha.2
    have hc := fieldAutP_cube_eq_one hι (by rw [hιa]; exact hA.2 a ha.1)
    rw [← hιa, fieldAutP_eq_one_of_cube h3 hc, mul_one]
    exact hι
  omega

theorem ggD4TrialityAutRankNF_omegaPlus (h3 : ¬ 3 ∣ Nat.card (K ≃+* K)) :
    GGD4TrialityAutRankNF
      (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))))
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenOmega (LargeEvenQPlus K 4)))) := by
  intro A hA φ hφA hnot
  exact card_le_of_equiv (MulAut.congr (RecipeFieldOmega.plusEquiv (K := K) one_le_four))
    (P := fun α => α ∉ Inn (Om8 K) ⊔ (AutOm.fieldAutP 4).range)
    (fun A' hA' α hα hP => card_le_27 h3 hA' hα hP) hA hφA
    (fun h => hnot (exists_inner_mul_field_of_mem h))

end Bound



end NbrGraphD4

theorem largeEvenLabelAll_d4TrialityAutRank {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : lab.rank = 4) (hn : 1 ≤ lab.n) :
    LargeEvenLabelAll lab fun _ _ I F => GGD4TrialityAutRank I F := by
  refine largeEvenLabelAll_omegaPlus ht (by omega) fun K _ _ _ hK => ?_
  have : IsCyclic (K ≃+* K) := CFSG.RankThree.PartOne.KFOUT3.isCyclic_aut hn hK
  rw [h4]
  exact NbrGraphD4.ggD4TrialityAutRank_omegaPlus

theorem largeEvenLabelAll_d4TrialityAutRankNF {lab : LargeEvenLabel} (ht : lab.tag = .D)
    (h4 : lab.rank = 4) (hn : 1 ≤ lab.n) :
    LargeEvenLabelAll lab fun _ _ I F => ¬ 3 ∣ lab.n → GGD4TrialityAutRankNF I F := by
  refine largeEvenLabelAll_omegaPlus ht (by omega) fun K _ _ _ hK h3 => ?_
  obtain ⟨-, -, -, hcard⟩ := CFSG.RankThree.PartOne.KFOUT3.exists_frobenius hn hK
  rw [h4]
  exact NbrGraphD4.ggD4TrialityAutRankNF_omegaPlus (by rwa [hcard])

end CFSG.StandardType
