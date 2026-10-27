module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeEndNode

public section

namespace CFSG.StandardType.TwoThree

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.CALinearPlane CFSG.Assembly CFSG.StandardType.TypeA

variable {K : Type} [Field K]

section Proj

variable {n : ℕ} (E : Matrix (Fin n) (Fin n) K)

@[expose] def commSub : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | E * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * E}
  mul_mem' {a b} ha hb := by
    change E * ((a : Matrix (Fin n) (Fin n) K) * b) = ((a : Matrix (Fin n) (Fin n) K) * b) * E
    rw [← Matrix.mul_assoc, ha, Matrix.mul_assoc, hb, Matrix.mul_assoc]
  one_mem' := by
    change E * ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = _ * E
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, Matrix.one_mul]
  inv_mem' {a} ha := by
    change E * ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = _ * E
    have h1 : ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (a : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (a : Matrix (Fin n) (Fin n) K) *
        ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    set ai := ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    calc E * ai = ai * (a : Matrix (Fin n) (Fin n) K) * E * ai := by rw [h1, Matrix.one_mul]
      _ = ai * (E * (a : Matrix (Fin n) (Fin n) K)) * ai := by
        rw [Matrix.mul_assoc ai, ← ha]
      _ = ai * E * ((a : Matrix (Fin n) (Fin n) K) * ai) := by simp only [Matrix.mul_assoc]
      _ = ai * E := by rw [h2, Matrix.mul_one]

theorem mem_commSub {g : SpecialLinearGroup (Fin n) K} :
    g ∈ commSub E ↔ E * (g : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K) * E :=
  Iff.rfl

@[expose] def unipSub : Subgroup (SpecialLinearGroup (Fin n) K) where
  carrier := {g | (g : Matrix (Fin n) (Fin n) K) * E = E ∧
    (1 - E) * (g : Matrix (Fin n) (Fin n) K) = 1 - E}
  mul_mem' {a b} ha hb := by
    change ((a : Matrix (Fin n) (Fin n) K) * b) * E = E ∧
      (1 - E) * ((a : Matrix (Fin n) (Fin n) K) * b) = 1 - E
    exact ⟨by rw [Matrix.mul_assoc, hb.1, ha.1], by rw [← Matrix.mul_assoc, ha.2, hb.2]⟩
  one_mem' := by
    change ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * E = E ∧
      (1 - E) * ((1 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - E
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.mul_one]
    exact ⟨rfl, rfl⟩
  inv_mem' {a} ha := by
    change ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * E = E ∧
      (1 - E) * ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 - E
    have h1 : ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        (a : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    have h2 : (a : Matrix (Fin n) (Fin n) K) *
        ((a⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← ha.1]
      rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    · conv_lhs => rw [← ha.2]
      rw [Matrix.mul_assoc, h2, Matrix.mul_one]

theorem commSub_le_normalizer_unipSub :
    commSub E ≤
      Subgroup.normalizer ((unipSub E : Subgroup _) : Set (SpecialLinearGroup (Fin n) K)) := by
  apply CFSG.StandardType.le_normalizer_of_map_conj_le
  rintro t ht _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
  have hti : t⁻¹ ∈ commSub E := (commSub E).inv_mem ht
  rw [mem_commSub] at ht hti
  change (((t * u * t⁻¹ : SpecialLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) * E = E ∧
    (1 - E) * (((t * u * t⁻¹ : SpecialLinearGroup (Fin n) K)) : Matrix (Fin n) (Fin n) K) = 1 - E
  have htt : (t : Matrix (Fin n) (Fin n) K) *
      ((t⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have ht' : (1 - E) * (t : Matrix (Fin n) (Fin n) K) =
      (t : Matrix (Fin n) (Fin n) K) * (1 - E) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, ht]
  have hti' : (1 - E) * ((t⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((t⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 - E) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hti]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  set T := (t : Matrix (Fin n) (Fin n) K)
  set Ti := ((t⁻¹ : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set Uu := (u : Matrix (Fin n) (Fin n) K)
  refine ⟨?_, ?_⟩
  · calc T * Uu * Ti * E = T * Uu * (Ti * E) := by simp only [Matrix.mul_assoc]
      _ = T * Uu * (E * Ti) := by rw [hti]
      _ = T * (Uu * E) * Ti := by simp only [Matrix.mul_assoc]
      _ = E * T * Ti := by rw [hu1, ← ht]
      _ = E := by rw [Matrix.mul_assoc, htt, Matrix.mul_one]
  · calc (1 - E) * (T * Uu * Ti) = ((1 - E) * T) * Uu * Ti := by simp only [Matrix.mul_assoc]
      _ = T * ((1 - E) * Uu) * Ti := by rw [ht']; simp only [Matrix.mul_assoc]
      _ = T * ((1 - E) * Ti) := by rw [hu2, Matrix.mul_assoc]
      _ = T * (Ti * (1 - E)) := by rw [hti']
      _ = 1 - E := by rw [← Matrix.mul_assoc, htt, Matrix.one_mul]

theorem sq_eq_one_of_mem_unipSub [CharP K 2] {g : SpecialLinearGroup (Fin n) K}
    (hg : g ∈ unipSub E) : g ^ 2 = 1 := by
  obtain ⟨h1, h2⟩ := hg
  set G := (g : Matrix (Fin n) (Fin n) K) with hG
  set N := G - 1 with hN
  have hNE : N * E = 0 := by rw [hN, Matrix.sub_mul, h1, Matrix.one_mul, sub_self]
  have hEN : (1 - E) * N = 0 := by rw [hN, Matrix.mul_sub, h2, Matrix.mul_one, sub_self]
  have hNN : N * N = 0 := by
    have h3 : N = E * N := by
      calc N = (1 - E) * N + E * N := by rw [Matrix.sub_mul, Matrix.one_mul, sub_add_cancel]
        _ = E * N := by rw [hEN, zero_add]
    calc N * N = N * (E * N) := by rw [← h3]
      _ = 0 := by rw [← Matrix.mul_assoc, hNE, Matrix.zero_mul]
  have h2N : N + N = 0 := by
    ext i j
    rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, sq, ← hG]
  have hGN : G = N + 1 := by rw [hN, sub_add_cancel]
  rw [hGN, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hNN, Matrix.mul_one, Matrix.one_mul,
    Matrix.one_mul, zero_add, ← add_assoc, h2N, zero_add]

theorem isPGroup_unipSub [CharP K 2] : IsPGroup 2 (unipSub E) := fun g =>
  ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, sq_eq_one_of_mem_unipSub E g.2]; rfl)⟩

end Proj

section Torus

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem g0_mem_commSub {m : ℕ} : g0 m K ∈ commSub (compIndicator K (J01 m)) :=
  compIndicator_commute_of_mem (Subgroup.mem_centralizer_singleton_iff.mpr rfl)

omit [Finite K] [CharP K 2] in
theorem coordBlockSL_le_commSub {m : ℕ} :
    coordBlockSL K (J01 m) ≤ commSub (compIndicator K (J01 m)) := by
  rintro s ⟨h1, h2⟩
  rw [mem_commSub, h1, h2]

omit [Finite K] [CharP K 2] in
theorem unipSub_ne_bot {m : ℕ} (hm : 1 ≤ m) : unipSub (compIndicator K (J01 m)) ≠ ⊥ := by
  set i2 : Fin (m + 2) := ⟨2, by omega⟩ with hi2
  have h02 : (0 : Fin (m + 2)) ≠ i2 := by
    intro h
    have := congrArg Fin.val h
    simp [hi2] at this
  have hi2J : i2 ∈ J01 m := by
    rw [mem_J01]
    refine ⟨Ne.symm h02, ?_⟩
    intro h
    have := congrArg Fin.val h
    simp [hi2] at this
  have h0J : (0 : Fin (m + 2)) ∉ J01 m := by
    rw [mem_J01]
    tauto
  intro hbot
  have hmem : SpecialLinearGroup.transvection h02 (1 : K) ∈ unipSub (compIndicator K (J01 m)) := by
    refine ⟨?_, ?_⟩
    · ext a b
      rw [mul_compIndicator_apply, compIndicator_apply, CFSG.LinearGroups.coe_transvection,
        Matrix.add_apply, one_apply, single_apply]
      by_cases hb : b ∈ J01 m
      · have hab : ¬ (a ∉ J01 m ∧ a = b) := fun h => h.1 (h.2 ▸ hb)
        rw [ite_eq_left hb, ite_eq_right hab]
      · have hbi : b ≠ i2 := fun h => hb (h ▸ hi2J)
        rw [ite_eq_right hb]
        by_cases hab : a = b
        · subst hab
          simp [hb, Ne.symm hbi]
        · simp [hab, Ne.symm hbi]
    · ext a b
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, compIndicator_mul_apply,
        Matrix.sub_apply, one_apply, compIndicator_apply, CFSG.LinearGroups.coe_transvection,
        Matrix.add_apply, one_apply, single_apply]
      by_cases ha : a ∈ J01 m
      · have ha0 : a ≠ 0 := fun h => h0J (h ▸ ha)
        simp [ha, Ne.symm ha0]
      · simp [ha]
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun g : SpecialLinearGroup (Fin (m + 2)) K =>
    (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 i2) hmem
  simp [CFSG.LinearGroups.coe_transvection, h02] at this

theorem torus_step {m : ℕ} {T' : Subgroup (SpecialLinearGroup (Fin (J01 m).card) K)}
    (hT' : IsElemAbelian 3 T') :
    IsElemAbelian 3 (Subgroup.zpowers (g0 m K) ⊔ T'.map (blockSLOn K (J01 m))) ∧
      Nat.card (Subgroup.zpowers (g0 m K) ⊔ T'.map (blockSLOn K (J01 m)) :
        Subgroup (SpecialLinearGroup (Fin (m + 2)) K)) = 3 * Nat.card T' ∧
      Subgroup.zpowers (g0 m K) ⊔ T'.map (blockSLOn K (J01 m)) ≤
        commSub (compIndicator K (J01 m)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T'' := T'.map (blockSLOn K (J01 m)) with hT''
  have hT''J : T'' ≤ coordBlockSL K (J01 m) := by
    rw [hT'', ← range_blockSLOn]
    exact Subgroup.map_le_range _ _
  have hg0 : IsElemAbelian 3 (Subgroup.zpowers (g0 m K)) :=
    isElemAbelian_zpowers g0_pow_three
  have hcomm : ∀ a ∈ Subgroup.zpowers (g0 m K), ∀ c ∈ T'', a * c = c * a := by
    intro a ha c hc
    have hc' := Subgroup.mem_centralizer_singleton_iff.mp
      (coordBlockSL_le_centralizer_g0 (hT''J hc))
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ((Commute.zpow_left hc'.symm k)).eq
  refine ⟨TableB.isElemAbelian_sup hg0 (TableB.isElemAbelian_map hT' _) hcomm, ?_, ?_⟩
  · have hN : T'' ≤ Subgroup.normalizer ((Subgroup.zpowers (g0 m K) : Subgroup _) :
        Set (SpecialLinearGroup (Fin (m + 2)) K)) := fun c hc =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun a ha =>
        (hcomm a ha c hc))
    have hdisj : Disjoint (Subgroup.zpowers (g0 m K)) T'' := by
      rw [Subgroup.disjoint_def]
      intro x hx hxT
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      by_contra hne
      have hk : g0 m K ∈ Subgroup.zpowers (g0 m K ^ k) := by
        have hord : orderOf (g0 m K ^ k) = 3 := orderOf_eq_prime (by
          rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
            g0_pow_three, _root_.one_zpow]) hne
        have hsub : Subgroup.zpowers (g0 m K ^ k) ≤ Subgroup.zpowers (g0 m K) :=
          Subgroup.zpowers_le.mpr (Subgroup.zpow_mem_zpowers _ _)
        have heq := Subgroup.eq_of_le_of_card_ge hsub (by
          rw [Nat.card_zpowers, Nat.card_zpowers, hord,
            orderOf_eq_prime g0_pow_three g0_ne_one])
        rw [heq]
        exact Subgroup.mem_zpowers _
      have hg0J : g0 m K ∈ coordBlockSL K (J01 m) :=
        (Subgroup.zpowers_le.mpr (hT''J hxT)) hk
      have h1 := entry_of_mem_J0 hg0J (a := 0) (b := 0) (Or.inl rfl)
      rw [coe_g0_apply] at h1
      simp at h1
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hN hdisj,
      Nat.card_zpowers, orderOf_eq_prime g0_pow_three g0_ne_one,
      ← Nat.card_congr (T'.equivMapOfInjective _ (blockSLOn_injective (J01 m))).toEquiv]
  · exact sup_le (Subgroup.zpowers_le.mpr g0_mem_commSub) (hT''J.trans coordBlockSL_le_commSub)

theorem exists_torus : ∀ m : ℕ, ∃ T : Subgroup (SpecialLinearGroup (Fin m) K),
    IsElemAbelian 3 T ∧ Nat.card T = 3 ^ (m / 2) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.lt_or_ge m 2 with hm | hm
  · exact ⟨⊥, isElemAbelian_bot, by rw [Subgroup.card_bot, show m / 2 = 0 by omega, pow_zero]⟩
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
    obtain ⟨T', hT', hcard⟩ := ih (J01 m').card (by rw [card_J01]; omega)
    obtain ⟨h1, h2, -⟩ := torus_step hT'
    refine ⟨_, h1, ?_⟩
    rw [h2, hcard, card_J01, show (m' + 2) / 2 = m' / 2 + 1 by omega, pow_succ, mul_comm]

theorem exists_torus_commSub (m : ℕ) : ∃ T : Subgroup (SpecialLinearGroup (Fin (m + 2)) K),
    IsElemAbelian 3 T ∧ Nat.card T = 3 ^ ((m + 2) / 2) ∧
      T ≤ commSub (compIndicator K (J01 m)) := by
  obtain ⟨T', hT', hcard⟩ := exists_torus (K := K) (J01 m).card
  obtain ⟨h1, h2, h3⟩ := torus_step hT'
  refine ⟨_, h1, ?_, h3⟩
  rw [h2, hcard, card_J01, show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ, mul_comm]

end Torus

theorem ggTorusLift_of_normalizes {d p r : ℕ} [Finite K] (hK : Nat.card K = 2)
    (hsec : SLHasSections d K) {E₀ U₀ : Subgroup (SpecialLinearGroup (Fin d) K)}
    (hE₀ : IsElemAbelian p E₀) (hcard : Nat.card E₀ = p ^ r) (hU₀ : U₀ ≠ ⊥)
    (hU₂ : IsPGroup 2 U₀)
    (hN : E₀ ≤ Subgroup.normalizer (U₀ : Set (SpecialLinearGroup (Fin d) K))) :
    GGTorusLift p r (projectiveSL d K) := by
  intro L' _ _ ψ hψ hker hperf
  obtain ⟨φ, -, hφ⟩ := exists_sl_cover hsec ψ hψ hker hperf
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    apply eq_one_of_mem_scalars hK
    rw [← proj_eq_one_iff, ← hφ, hg, map_one]
  refine ⟨U₀.map φ, E₀.map φ, ?_, hU₂.map φ, ?_, TableB.isElemAbelian_map hE₀ φ, ?_, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hφinj]
  · exact (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map φ)
  · rw [← hcard]
    exact (Nat.card_congr (E₀.equivMapOfInjective φ hφinj).toEquiv).symm
  · rw [eq_bot_iff]
    rintro x ⟨⟨g, -, rfl⟩, hx⟩
    have h1 : proj d K g = 1 := by rw [← hφ]; exact hx
    rw [eq_one_of_mem_scalars hK (proj_eq_one_iff.mp h1), map_one]
    exact Subgroup.one_mem _

theorem ggTorusLift_two [Finite K] [CharP K 2] {d : ℕ} (hK : Nat.card K = 2) (hd : 5 ≤ d) :
    GGTorusLift 3 (d / 2) (projectiveSL d K) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 2 := ⟨d - 2, by omega⟩
  obtain ⟨T, hT, hcard, hTE⟩ := exists_torus_commSub (K := K) m
  exact ggTorusLift_of_normalizes hK (slHasSections_of_five_le hd) hT hcard
    (unipSub_ne_bot (by omega)) (isPGroup_unipSub _)
    (hTE.trans (commSub_le_normalizer_unipSub _))

end CFSG.StandardType.TwoThree
