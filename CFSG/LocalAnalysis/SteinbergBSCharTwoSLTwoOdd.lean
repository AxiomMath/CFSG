module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.LocalAnalysis.SteinbergBS

open Matrix

theorem exists_two_common_fixed_points {H Ω : Type*} [Group H] [Finite H] [MulAction H Ω]
    (hodd : Odd (Nat.card H)) [Nontrivial H] (S : Set Ω)
    (hS : ∀ (g : H) (z : Ω), z ∈ S → g • z ∈ S)
    (hfix : ∀ h : H, h ≠ 1 → ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ∀ z ∈ S, h • z = z ↔ z = x ∨ z = y) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ ∀ h : H, h • x = x ∧ h • y = y := by
  classical
  have : Nonempty Ω := by
    obtain ⟨h, hh⟩ := exists_ne (1 : H)
    obtain ⟨x, -, -⟩ := hfix h hh
    exact ⟨x⟩
  choose! fx hfxS fy hfyS hne hiff using hfix
  let T : SubMulAction H Ω :=
    { carrier := {z | z ∈ S ∧ ∃ h : H, h ≠ 1 ∧ h • z = z}
      smul_mem' := by
        rintro g z ⟨hzS, h, hh1, hhz⟩
        refine ⟨hS g z hzS, g * h * g⁻¹, fun h' => hh1 ?_, ?_⟩
        · have h'' := congrArg (fun u => g⁻¹ * u * g) h'
          simpa [mul_assoc] using h''
        · rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one, mul_smul, hhz] }
  have hfxT : ∀ h : H, h ≠ 1 → fx h ∈ T := fun h hh =>
    ⟨hfxS h hh, h, hh, (hiff h hh (fx h) (hfxS h hh)).2 (Or.inl rfl)⟩
  have hfyT : ∀ h : H, h ≠ 1 → fy h ∈ T := fun h hh =>
    ⟨hfyS h hh, h, hh, (hiff h hh (fy h) (hfyS h hh)).2 (Or.inr rfl)⟩
  have hTfin : Set.Finite (T : Set Ω) := by
    refine (Set.finite_iUnion fun h : H => (Set.toFinite ({fx h, fy h} : Set Ω))).subset ?_
    rintro z ⟨hzS, h, hh1, hhz⟩
    exact Set.mem_iUnion.2 ⟨h, (hiff h hh1 z hzS).1 hhz⟩
  have : Finite T := hTfin.to_subtype
  let := Fintype.ofFinite T
  let := Fintype.ofFinite H
  set n := Nat.card H with hn
  set s := Nat.card T with hs
  set r := Nat.card (MulAction.orbitRel.Quotient H T) with hr
  have hburn : ∑ g : H, Nat.card (MulAction.fixedBy T g) = r * n := by
    have := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group H T
    simp only [hr, hn, Nat.card_eq_fintype_card]
    exact this
  have hfixcard : ∀ g : H, g ≠ 1 → Nat.card (MulAction.fixedBy T g) = 2 := by
    intro g hg
    have heq : MulAction.fixedBy T g = {⟨fx g, hfxT g hg⟩, ⟨fy g, hfyT g hg⟩} := by
      ext z
      simp only [MulAction.mem_fixedBy, Set.mem_insert_iff, Set.mem_singleton_iff,
        Subtype.ext_iff, SubMulAction.val_smul]
      exact hiff g hg z z.2.1
    rw [heq, Nat.card_coe_set_eq, Set.ncard_pair]
    intro h
    exact hne g hg (congrArg Subtype.val h)
  have hsum : ∑ g : H, Nat.card (MulAction.fixedBy T g) = s + 2 * (n - 1) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : H))]
    have h1 : Nat.card (MulAction.fixedBy T (1 : H)) = s := by
      rw [MulAction.fixedBy_one_eq_univ, Nat.card_coe_set_eq, Set.ncard_univ]
    rw [h1, Finset.sum_congr rfl (fun g hg => hfixcard g (Finset.ne_of_mem_erase hg)),
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, smul_eq_mul, mul_comm]
  have hstab : ∀ x : T, 3 ≤ Nat.card (MulAction.stabilizer H x) := by
    intro x
    obtain ⟨-, h, hh1, hhx⟩ := x.2
    have hne' : MulAction.stabilizer H x ≠ ⊥ := by
      intro hbot
      have hmem : h ∈ MulAction.stabilizer H x := by
        rw [MulAction.mem_stabilizer_iff]
        exact Subtype.ext hhx
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hh1 hmem
    have h1 : 1 < Nat.card (MulAction.stabilizer H x) := by
      rwa [Subgroup.one_lt_card_iff_ne_bot]
    obtain ⟨k, hk⟩ := Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card
      (MulAction.stabilizer H x))
    omega
  have hdc : ∑ g : H, Nat.card (MulAction.fixedBy T g) =
      ∑ x : T, Nat.card (MulAction.stabilizer H x) := by
    rw [← Nat.card_sigma, ← Nat.card_sigma]
    exact Nat.card_congr (((Equiv.subtypeProdEquivSigmaSubtype _).symm.trans
      ((Equiv.prodComm H T).subtypeEquiv fun _ => Iff.rfl)).trans
      (Equiv.subtypeProdEquivSigmaSubtype fun (b : T) a => a ∈ MulAction.stabilizer H b))
  have h3s : 3 * s ≤ s + 2 * (n - 1) := by
    rw [← hsum, hdc]
    calc 3 * s = ∑ _x : T, 3 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, hs,
            Nat.card_eq_fintype_card]
      _ ≤ ∑ x : T, Nat.card (MulAction.stabilizer H x) := Finset.sum_le_sum fun x _ => hstab x
  have hn3 : 3 ≤ n := by
    have h1 : 1 < n := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hodd
    omega
  have hrn : r * n = s + 2 * (n - 1) := hburn.symm.trans hsum
  have hr2 : r = 2 := by
    rcases Nat.lt_or_ge r 2 with hr1 | hr1
    · interval_cases r <;> omega
    · rcases Nat.lt_or_ge r 3 with hr3 | hr3
      · omega
      · have h3n := Nat.mul_le_mul_right n hr3
        omega
  have hs2 : s = 2 := by
    rw [hr2] at hrn
    omega
  obtain ⟨a, b, hab, huniv⟩ := Nat.card_eq_two_iff.1 hs2
  have hmem : ∀ z : T, z = a ∨ z = b := fun z => by
    have hz : z ∈ ({a, b} : Set T) := huniv ▸ Set.mem_univ z
    simpa using hz
  refine ⟨a, a.2.1, b, b.2.1, fun h => hab (Subtype.ext h), fun h => ?_⟩
  by_cases hh : h = 1
  · subst hh
    simp
  · have hfa := hiff h hh a a.2.1
    have hfb := hiff h hh b b.2.1
    have hxy : fx h ≠ fy h := hne h hh
    rcases hmem ⟨fx h, hfxT h hh⟩ with hx | hx <;> rcases hmem ⟨fy h, hfyT h hh⟩ with hy | hy
    · exact absurd ((congrArg Subtype.val hx).trans (congrArg Subtype.val hy).symm) hxy
    · exact ⟨hfa.2 (Or.inl (congrArg Subtype.val hx).symm),
        hfb.2 (Or.inr (congrArg Subtype.val hy).symm)⟩
    · exact ⟨hfa.2 (Or.inr (congrArg Subtype.val hy).symm),
        hfb.2 (Or.inl (congrArg Subtype.val hx).symm)⟩
    · exact absurd ((congrArg Subtype.val hx).trans (congrArg Subtype.val hy).symm) hxy

theorem det_sub_smul_one_char_two {K : Type*} [Field K] [CharP K 2]
    (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 1) (c : K) :
    (M - c • (1 : Matrix (Fin 2) (Fin 2) K)).det = c ^ 2 + M.trace * c + 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, sub_zero]
  linear_combination hdet - (M 0 0 + M 1 1) * c * h2

theorem mem_span_of_mulVec_eq_zero {K : Type*} [Field K] {N : Matrix (Fin 2) (Fin 2) K}
    (hN : N ≠ 0) {v u : Fin 2 → K} (hv : v ≠ 0) (hNv : N *ᵥ v = 0) (hNu : N *ᵥ u = 0) :
    u ∈ K ∙ v := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
  rw [Module.finrank_fin_fun] at hrank
  have hrange : 1 ≤ Module.finrank K (LinearMap.range (Matrix.toLin' N)) := by
    rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero, LinearMap.range_eq_bot]
    intro hf
    exact hN (Matrix.toLin'.injective (hf.trans (map_zero _).symm))
  have hvker : v ∈ LinearMap.ker (Matrix.toLin' N) := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply]
    exact hNv
  have hker1 : Module.finrank K (LinearMap.ker (Matrix.toLin' N)) = 1 := by
    have h1 : 1 ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' N)) := by
      rw [Nat.one_le_iff_ne_zero, Ne, Submodule.finrank_eq_zero]
      intro hbot
      rw [hbot, Submodule.mem_bot] at hvker
      exact hv hvker
    omega
  rw [← eq_span_singleton_of_mem_of_finrank_eq_one hker1 hvker hv, LinearMap.mem_ker,
    Matrix.toLin'_apply]
  exact hNu

theorem map_toLin'_eq_self_iff {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M.det ≠ 0) {L : Submodule K (Fin 2 → K)} (hL : Module.finrank K L = 1)
    {u : Fin 2 → K} (hu : u ∈ L) (hu0 : u ≠ 0) :
    L.map (Matrix.toLin' M) = L ↔ M *ᵥ u ∈ L := by
  have hLu := eq_span_singleton_of_mem_of_finrank_eq_one hL hu hu0
  have hMu0 : M *ᵥ u ≠ 0 := by
    intro h
    apply hu0
    calc u = (M⁻¹ * M) *ᵥ u := by
          rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.one_mulVec]
      _ = M⁻¹ *ᵥ (M *ᵥ u) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [h, Matrix.mulVec_zero]
  constructor
  · intro h
    rw [← h]
    simpa using Submodule.mem_map_of_mem (f := Matrix.toLin' M) hu
  · intro h
    have h2 := eq_span_singleton_of_mem_of_finrank_eq_one hL h hMu0
    rw [hLu, Submodule.map_span, Set.image_singleton, Matrix.toLin'_apply, ← hLu]
    exact h2.symm

theorem finrank_map_toLin' {K : Type*} [Field K] {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M.det ≠ 0) {L : Submodule K (Fin 2 → K)} (hL : Module.finrank K L = 1) :
    Module.finrank K (L.map (Matrix.toLin' M)) = 1 := by
  have hL0 : L ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hL
    exact zero_ne_one hL
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
  have hMu0 : M *ᵥ u ≠ 0 := by
    intro h
    apply hu0
    calc u = (M⁻¹ * M) *ᵥ u := by
          rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.one_mulVec]
      _ = M⁻¹ *ᵥ (M *ᵥ u) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [h, Matrix.mulVec_zero]
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hL hu hu0, Submodule.map_span,
    Set.image_singleton, Matrix.toLin'_apply]
  exact finrank_span_singleton hMu0

theorem exists_two_invariant_lines {K : Type*} [Field K] [IsAlgClosed K] [CharP K 2]
    (M : Matrix (Fin 2) (Fin 2) K) (hdet : M.det = 1) (htr : M.trace ≠ 0) :
    ∃ L₁ L₂ : Submodule K (Fin 2 → K), Module.finrank K L₁ = 1 ∧ Module.finrank K L₂ = 1 ∧
      L₁ ≠ L₂ ∧ ∀ L : Submodule K (Fin 2 → K), Module.finrank K L = 1 →
        (L.map (Matrix.toLin' M) = L ↔ L = L₁ ∨ L = L₂) := by
  set t := M.trace with ht
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hchar := det_sub_smul_one_char_two M hdet
  obtain ⟨l, hl⟩ : ∃ l : K, l ^ 2 + t * l + 1 = 0 := by
    obtain ⟨l, hl⟩ := IsAlgClosed.exists_root (Polynomial.C 1 * Polynomial.X ^ 2 +
      Polynomial.C t * Polynomial.X + Polynomial.C 1)
      (by rw [Polynomial.degree_quadratic one_ne_zero]; decide)
    refine ⟨l, ?_⟩
    simpa [Polynomial.IsRoot] using hl
  have hμ : (l + t) ^ 2 + t * (l + t) + 1 = 0 := by
    linear_combination hl + (l * t + t ^ 2) * h2
  have hlμ : l ≠ l + t := fun h => htr (by linear_combination -h)
  have hfac : ∀ c : K, c ^ 2 + t * c + 1 = (c - l) * (c - (l + t)) := by
    intro c
    linear_combination (-1 : K) * hl + (1 + c * t + c * l) * h2
  have heig : ∀ c : K, c ^ 2 + t * c + 1 = 0 → ∃ v : Fin 2 → K, v ≠ 0 ∧ M *ᵥ v = c • v := by
    intro c hc
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (by rw [hchar, hc])
    refine ⟨v, hv, ?_⟩
    rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
  have hNne : ∀ c : K, M - c • (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro c hc
    apply htr
    rw [ht, sub_eq_zero.1 hc, Matrix.trace_fin_two]
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    linear_combination c * h2
  have hsub : ∀ c : K, ∀ u : Fin 2 → K, M *ᵥ u = c • u →
      (M - c • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ u = 0 := by
    intro c u h
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h, sub_self]
  obtain ⟨v, hv, hMv⟩ := heig l hl
  obtain ⟨w, hw, hMw⟩ := heig (l + t) hμ
  have hdet0 : M.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  refine ⟨K ∙ v, K ∙ w, finrank_span_singleton hv, finrank_span_singleton hw, ?_, ?_⟩
  · intro heq
    have hwv : w ∈ K ∙ v := heq ▸ Submodule.mem_span_singleton_self w
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hwv
    have hMw' : M *ᵥ w = l • w := by rw [← ha, Matrix.mulVec_smul, hMv, smul_comm]
    have : (l - (l + t)) • w = 0 := by rw [sub_smul, ← hMw', hMw, sub_self]
    rcases smul_eq_zero.1 this with h | h
    · exact hlμ (sub_eq_zero.1 h)
    · exact hw h
  · intro L hL
    have hL0 : L ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hL
      exact zero_ne_one hL
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
    have hLu := eq_span_singleton_of_mem_of_finrank_eq_one hL hu hu0
    rw [map_toLin'_eq_self_iff hdet0 hL hu hu0]
    constructor
    · intro hfix
      rw [hLu] at hfix
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hfix
      have hc2 : c ^ 2 + t * c + 1 = 0 := by
        rw [← hchar]
        exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨u, hu0, hsub c u hc.symm⟩
      rw [hfac] at hc2
      rcases mul_eq_zero.1 hc2 with h | h
      · left
        rw [sub_eq_zero] at h
        rw [h] at hc
        have huv := mem_span_of_mulVec_eq_zero (hNne l) hv (hsub _ _ hMv) (hsub l u hc.symm)
        rw [hLu]
        exact (eq_span_singleton_of_mem_of_finrank_eq_one (finrank_span_singleton hv) huv
          hu0).symm
      · right
        rw [sub_eq_zero] at h
        rw [h] at hc
        have huw := mem_span_of_mulVec_eq_zero (hNne _) hw (hsub _ _ hMw) (hsub _ u hc.symm)
        rw [hLu]
        exact (eq_span_singleton_of_mem_of_finrank_eq_one (finrank_span_singleton hw) huw
          hu0).symm
    · rintro (h | h)
      · rw [h] at hu ⊢
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hu
        rw [← ha, Matrix.mulVec_smul, hMv, smul_comm]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      · rw [h] at hu ⊢
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hu
        rw [← ha, Matrix.mulVec_smul, hMw, smul_comm]
        exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem sq_eq_one_of_trace_eq_zero {k : Type*} [CommRing k] [CharP k 2]
    (g : Matrix.SpecialLinearGroup (Fin 2) k)
    (htr : Matrix.trace (g : Matrix (Fin 2) (Fin 2) k) = 0) : g * g = 1 := by
  have h2 : (2 : k) = 0 := CharP.cast_eq_zero k 2
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (g 0 0 : k) * htr - hdet - h2
  · linear_combination (g 0 1 : k) * htr
  · linear_combination (g 1 0 : k) * htr
  · linear_combination (g 1 1 : k) * htr - hdet - h2

@[expose] noncomputable def sl2LinAlgClosure {k : Type*} [Field k]
    (g : Matrix.SpecialLinearGroup (Fin 2) k) :
    (Fin 2 → AlgebraicClosure k) →ₗ[AlgebraicClosure k] (Fin 2 → AlgebraicClosure k) :=
  Matrix.toLin' ((g : Matrix (Fin 2) (Fin 2) k).map (algebraMap k (AlgebraicClosure k)))

theorem sl2LinAlgClosure_mul {k : Type*} [Field k] (g h : Matrix.SpecialLinearGroup (Fin 2) k) :
    sl2LinAlgClosure (g * h) = sl2LinAlgClosure g ∘ₗ sl2LinAlgClosure h := by
  rw [sl2LinAlgClosure, sl2LinAlgClosure, sl2LinAlgClosure, ← Matrix.toLin'_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]

theorem sl2LinAlgClosure_one {k : Type*} [Field k] :
    sl2LinAlgClosure (1 : Matrix.SpecialLinearGroup (Fin 2) k) = LinearMap.id := by
  rw [sl2LinAlgClosure, Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ (map_zero _)
    (map_one _), Matrix.toLin'_one]

theorem trace_eq_zero_of_mulVec_eq_self {K : Type*} [Field K] [CharP K 2]
    {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) {v : Fin 2 → K} (hv : v ≠ 0)
    (hMv : M *ᵥ v = v) : M.trace = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h := det_sub_smul_one_char_two M hdet 1
  have h0 : (M - (1 : K) • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.1
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, one_smul, hMv, sub_self]
  rw [h0] at h
  linear_combination -h - h2

theorem char_two_sl2_odd_subgroup_cyclic {k : Type*} [Field k] [CharP k 2]
    (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) k)) [Finite H] (hodd : Odd (Nat.card H)) :
    IsCyclic H ∧
      (H ≠ ⊥ → ∃ L₁ L₂ : Submodule (AlgebraicClosure k) (Fin 2 → AlgebraicClosure k),
        Module.finrank (AlgebraicClosure k) L₁ = 1 ∧
        Module.finrank (AlgebraicClosure k) L₂ = 1 ∧ L₁ ≠ L₂ ∧
        (∀ L : Submodule (AlgebraicClosure k) (Fin 2 → AlgebraicClosure k),
          Module.finrank (AlgebraicClosure k) L = 1 →
          ((∀ h ∈ H, L.map (sl2LinAlgClosure h) = L) ↔ L = L₁ ∨ L = L₂)) ∧
        ∀ h ∈ H, h ≠ 1 → ∀ L : Submodule (AlgebraicClosure k) (Fin 2 → AlgebraicClosure k),
          Module.finrank (AlgebraicClosure k) L = 1 → L.map (sl2LinAlgClosure h) = L →
          L = L₁ ∨ L = L₂) := by
  classical
  have hodd1 : ∀ h : H, h * h = 1 → h = 1 := by
    intro h hh
    have h1 : orderOf h ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hh)
    exact orderOf_eq_one_iff.1
      (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.2 hodd) h1 (orderOf_dvd_natCard h))
  have htr : ∀ h : H, h ≠ 1 →
      Matrix.trace ((h : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) ≠ 0 :=
    fun h hh h0 => hh (hodd1 h (Subtype.ext (sq_eq_one_of_trace_eq_zero _ h0)))
  set K := AlgebraicClosure k with hK
  let M : Matrix.SpecialLinearGroup (Fin 2) k → Matrix (Fin 2) (Fin 2) K :=
    fun g => (g : Matrix (Fin 2) (Fin 2) k).map (algebraMap k K)
  have hMlin : ∀ g, sl2LinAlgClosure g = Matrix.toLin' (M g) := fun g => rfl
  have hMdet : ∀ g, (M g).det = 1 := by
    intro g
    change ((g : Matrix (Fin 2) (Fin 2) k).map (algebraMap k K)).det = 1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, g.2, map_one]
  have hMdet0 : ∀ g, (M g).det ≠ 0 := fun g => by rw [hMdet]; exact one_ne_zero
  have hMtr : ∀ g, (M g).trace =
      algebraMap k K (Matrix.trace (g : Matrix (Fin 2) (Fin 2) k)) := by
    intro g
    simp only [M, Matrix.trace_fin_two, Matrix.map_apply, map_add]
  have hMmul : ∀ g h, M (g * h) = M g * M h := by
    intro g h
    simp only [M, Matrix.SpecialLinearGroup.coe_mul, Matrix.map_mul]
  have hMone : M 1 = 1 := by
    simp only [M, Matrix.SpecialLinearGroup.coe_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let : MulAction H (Submodule K (Fin 2 → K)) :=
    { smul := fun h L => L.map (sl2LinAlgClosure (h : Matrix.SpecialLinearGroup (Fin 2) k))
      one_smul := fun L => by
        change L.map (sl2LinAlgClosure ((1 : H) : Matrix.SpecialLinearGroup (Fin 2) k)) = L
        rw [OneMemClass.coe_one, sl2LinAlgClosure_one, Submodule.map_id]
      mul_smul := fun g h L => by
        change L.map (sl2LinAlgClosure ((g * h : H) : Matrix.SpecialLinearGroup (Fin 2) k)) =
          (L.map (sl2LinAlgClosure (h : Matrix.SpecialLinearGroup (Fin 2) k))).map
            (sl2LinAlgClosure (g : Matrix.SpecialLinearGroup (Fin 2) k))
        rw [MulMemClass.coe_mul, sl2LinAlgClosure_mul, Submodule.map_comp] }
  have hlines : H ≠ ⊥ → ∃ L₁ L₂ : Submodule K (Fin 2 → K), Module.finrank K L₁ = 1 ∧
      Module.finrank K L₂ = 1 ∧ L₁ ≠ L₂ ∧
      ∀ h : H, h ≠ 1 → ∀ L : Submodule K (Fin 2 → K), Module.finrank K L = 1 →
        (L.map (sl2LinAlgClosure h) = L ↔ L = L₁ ∨ L = L₂) := by
    intro hH
    have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hH
    have hinv : ∀ h : H, h ≠ 1 → ∃ L₁ L₂ : Submodule K (Fin 2 → K), Module.finrank K L₁ = 1 ∧
        Module.finrank K L₂ = 1 ∧ L₁ ≠ L₂ ∧ ∀ L : Submodule K (Fin 2 → K),
          Module.finrank K L = 1 → (L.map (sl2LinAlgClosure h) = L ↔ L = L₁ ∨ L = L₂) :=
      fun h hh => exists_two_invariant_lines (M h) (hMdet h)
        (by rw [hMtr]; exact (map_ne_zero _).2 (htr h hh))
    obtain ⟨L₁, hL₁, L₂, hL₂, hne, hfix⟩ := exists_two_common_fixed_points hodd
      {L : Submodule K (Fin 2 → K) | Module.finrank K L = 1}
      (fun g L hL => finrank_map_toLin' (hMdet0 _) hL)
      (fun h hh => by
        obtain ⟨L₁, L₂, h1, h2, hne, hiff⟩ := hinv h hh
        exact ⟨L₁, h1, L₂, h2, hne, fun L hL => hiff L hL⟩)
    refine ⟨L₁, L₂, hL₁, hL₂, hne, fun h hh L hL => ?_⟩
    obtain ⟨L₁', L₂', -, -, -, hiff⟩ := hinv h hh
    have hf1 : L₁ = L₁' ∨ L₁ = L₂' := (hiff L₁ hL₁).1 (hfix h).1
    have hf2 : L₂ = L₁' ∨ L₂ = L₂' := (hiff L₂ hL₂).1 (hfix h).2
    rw [hiff L hL]
    rcases hf1 with rfl | rfl <;> rcases hf2 with rfl | rfl
    · exact absurd rfl hne
    · exact Iff.rfl
    · exact Or.comm
    · exact absurd rfl hne
  refine ⟨?_, fun hH => ?_⟩
  · by_cases hH : H = ⊥
    · have : Subsingleton H := by
        rw [hH]
        infer_instance
      exact isCyclic_of_subsingleton
    obtain ⟨L₁, L₂, hL₁, hL₂, hne, hall⟩ := hlines hH
    have hfixall : ∀ h : H, L₁.map (sl2LinAlgClosure h) = L₁ := by
      intro h
      by_cases hh : h = 1
      · rw [hh, OneMemClass.coe_one, sl2LinAlgClosure_one, Submodule.map_id]
      · exact (hall h hh L₁ hL₁).2 (Or.inl rfl)
    have hL0 : L₁ ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hL₁
      exact zero_ne_one hL₁
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
    have hL₁v := eq_span_singleton_of_mem_of_finrank_eq_one hL₁ hv hv0
    have hα : ∀ h : H, ∃ c : K, c • v = M h *ᵥ v := by
      intro h
      apply Submodule.mem_span_singleton.1
      rw [← hL₁v]
      have hmem := Submodule.mem_map_of_mem (f := sl2LinAlgClosure h) hv
      rw [hfixall h, hMlin, Matrix.toLin'_apply] at hmem
      exact hmem
    choose α hα using hα
    have hαmul : ∀ g h : H, α (g * h) = α g * α h := by
      intro g h
      apply smul_left_injective K hv0
      change α (g * h) • v = (α g * α h) • v
      rw [hα, MulMemClass.coe_mul, hMmul, ← Matrix.mulVec_mulVec, ← hα h, Matrix.mulVec_smul,
        ← hα g, smul_smul, mul_comm]
    have hαone : α 1 = 1 := by
      apply smul_left_injective K hv0
      change α 1 • v = (1 : K) • v
      rw [hα, one_smul, OneMemClass.coe_one, hMone, Matrix.one_mulVec]
    let f : H →* K := { toFun := α, map_one' := hαone, map_mul' := hαmul }
    have hker : ∀ h : H, α h = 1 → h = 1 := by
      intro h hh
      by_contra hne1
      apply htr h hne1
      have hMv : M h *ᵥ v = v := by rw [← hα h, hh, one_smul]
      have h0 := trace_eq_zero_of_mulVec_eq_self (hMdet h) hv0 hMv
      rw [hMtr] at h0
      exact (map_eq_zero _).1 h0
    refine isCyclic_of_injective_ringHom f fun g h hgh => ?_
    have h1 : α (g * h⁻¹) = 1 := by
      change f (g * h⁻¹) = 1
      rw [map_mul, hgh, ← map_mul, mul_inv_cancel, map_one]
    exact mul_inv_eq_one.1 (hker _ h1)
  · obtain ⟨L₁, L₂, hL₁, hL₂, hne, hall⟩ := hlines hH
    obtain ⟨h0, hne1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH
    refine ⟨L₁, L₂, hL₁, hL₂, hne, fun L hL => ⟨fun hfix => ?_, ?_⟩,
      fun h hh hh1 L hL hfix => ?_⟩
    · exact (hall h0 hne1 L hL).1 (hfix h0 h0.2)
    · intro hLL h hh
      by_cases hh1 : (⟨h, hh⟩ : H) = 1
      · rw [show h = 1 from congrArg Subtype.val hh1, sl2LinAlgClosure_one, Submodule.map_id]
      · exact (hall ⟨h, hh⟩ hh1 L hL).2 hLL
    · exact (hall ⟨h, hh⟩ (fun h' => hh1 (congrArg Subtype.val h')) L hL).1 hfix

end CFSG.LocalAnalysis.SteinbergBS
