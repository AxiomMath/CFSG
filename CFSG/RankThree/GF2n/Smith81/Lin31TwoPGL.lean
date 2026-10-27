module

public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.SteinbergBSCharTwoSLTwoOdd
public import TauCeti.LinearAlgebra.Matrix.CharpolyFinTwo
public import TauCeti.LinearAlgebra.Matrix.Trace.FinTwo

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.Open
open scoped Matrix

section TwoByTwo

variable {F : Type} [Field F]

private lemma det_sub_smul_one (A : Matrix (Fin 2) (Fin 2) F) (μ : F) :
    (A - μ • 1).det = μ ^ 2 - A.trace * μ + A.det := by
  have h := TauCeti.Matrix.det_smul_sub_smul_one_fin_two A 1 μ
  rw [one_smul] at h
  rw [h]
  ring

private lemma vecMul_sub_smul_one_eq_zero_iff {u : Fin 2 → F} {A : Matrix (Fin 2) (Fin 2) F}
    {μ : F} : Matrix.vecMul u (A - μ • 1) = 0 ↔ Matrix.vecMul u A = μ • u := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, sub_eq_zero]

private lemma eigenvalue_sq_sub_trace_mul_add_det {A : Matrix (Fin 2) (Fin 2) F}
    {u : Fin 2 → F} (hu : u ≠ 0) {μ : F} (h : Matrix.vecMul u A = μ • u) :
    μ ^ 2 - A.trace * μ + A.det = 0 := by
  rw [← det_sub_smul_one]
  exact Matrix.exists_vecMul_eq_zero_iff.mp ⟨u, hu, vecMul_sub_smul_one_eq_zero_iff.mpr h⟩

private lemma exists_eq_smul_of_vecMul_eq_zero {M : Matrix (Fin 2) (Fin 2) F} (hM : M ≠ 0)
    {u v : Fin 2 → F} (hv : v ≠ 0) (hu : Matrix.vecMul u M = 0)
    (hv' : Matrix.vecMul v M = 0) : ∃ c : F, u = c • v := by
  have h := CFSG.LocalAnalysis.SteinbergBS.mem_span_of_mulVec_eq_zero (N := M.transpose)
    (Matrix.transpose_eq_zero.not.mpr hM) hv (by rw [Matrix.mulVec_transpose, hv'])
    (by rw [Matrix.mulVec_transpose, hu])
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h
  exact ⟨c, hc.symm⟩

theorem trace_ne_zero_of_odd_orderOf {a : GL (Fin 2) F} (hao : Odd (orderOf a))
    (hna : ∀ c : F, (a : Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) c) :
    (a : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := by
  intro ht
  set A := (a : Matrix (Fin 2) (Fin 2) F) with hA
  have hCH := Matrix.sq_eq_trace_smul_sub_det_smul_one_fin_two A
  rw [ht, zero_smul, zero_sub, ← neg_smul] at hCH
  obtain ⟨k, hk⟩ := hao
  have hpow : A ^ orderOf a = 1 := by
    rw [hA, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  rw [hk, pow_succ, pow_mul, hCH, smul_pow, one_pow, smul_mul_assoc, one_mul] at hpow
  set c := (-A.det) ^ k
  have hc : c ≠ 0 := by
    rintro hc
    rw [hc, zero_smul] at hpow
    exact zero_ne_one hpow
  apply hna c⁻¹
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← hpow, smul_smul, inv_mul_cancel₀ hc,
    one_smul]

end TwoByTwo

section GroupTheory

private lemma eq_of_mem_of_card_dvd_two {G : Type*} [Group G] {P : Subgroup G}
    (hP : Nat.card P ∣ 2) {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    x = y := by
  by_contra hxy
  have hfin : (P : Set G).Finite := by
    have : Finite P := Nat.finite_of_card_ne_zero (by rintro h; rw [h] at hP; simp at hP)
    exact Set.toFinite _
  have h3 : ({1, x, y} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem, Set.ncard_pair hxy]
    rintro (h | h)
    exacts [hx1 h.symm, hy1 h.symm]
  have hle : ({1, x, y} : Set G).ncard ≤ (P : Set G).ncard := by
    refine Set.ncard_le_ncard ?_ hfin
    rintro z (rfl | rfl | rfl)
    exacts [P.one_mem, hx, hy]
  rw [← Nat.card_coe_set_eq (P : Set G)] at hle
  have := Nat.le_of_dvd two_pos hP
  change _ ≤ Nat.card P at hle
  omega

theorem exists_odd_subgroup_of_card_dvd_two_mul {G : Type*} [Group G] [Finite G] {m : ℕ}
    (hm : Odd m) (hG : Nat.card G ∣ 2 * m) :
    ∃ N : Subgroup G, Odd (Nat.card N) ∧ ∀ x : G, Odd (orderOf x) → x ∈ N := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 G) := Sylow.nonempty
  have hP2 : Nat.card P ∣ 2 := by
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    have h1 : 2 ^ k ∣ 2 * m := hk ▸ (Subgroup.card_subgroup_dvd_card _).trans hG
    have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hm)
    rw [hk]
    exact hcop.dvd_of_dvd_mul_right h1
  have hP : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    by_cases h1 : h = 1
    · simp [h1]
    have hc : g * h * g⁻¹ ∈ (P : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hg h).mp hh
    have hc1 : g * h * g⁻¹ ≠ 1 := by
      intro e
      apply h1
      calc h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group
    have := eq_of_mem_of_card_dvd_two hP2 hc hh hc1 h1
    calc h * g = g * h * g⁻¹ * g := by rw [this]
      _ = g * h := by group
  refine ⟨(MonoidHom.transferSylow P hP).ker, ?_, ?_⟩
  · have := MonoidHom.not_dvd_card_ker_transferSylow P hP
    exact Nat.not_even_iff_odd.mp fun he => this (even_iff_two_dvd.mp he)
  · intro x hx
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]
    have h1 : orderOf (MonoidHom.transferSylow P hP x) ∣ orderOf x := orderOf_map_dvd _ _
    have h2 : orderOf (MonoidHom.transferSylow P hP x) ∣ 2 := (orderOf_dvd_natCard _).trans hP2
    have h3 : Odd (orderOf (MonoidHom.transferSylow P hP x)) := Odd.of_dvd_nat hx h1
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at h3
      exact absurd h3 (by decide)

end GroupTheory

section PGL

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_second_eigen {a : GL (Fin 2) F} (hao : Odd (orderOf a))
    (hna : ∀ c : F, (a : Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) c)
    {u₁ : Fin 2 → F} (hu₁ : u₁ ≠ 0) {μ₁ : F}
    (h₁ : Matrix.vecMul u₁ (a : Matrix (Fin 2) (Fin 2) F) = μ₁ • u₁) :
    ∃ (u₂ : Fin 2 → F) (μ₂ : F), u₂ ≠ 0 ∧
      Matrix.vecMul u₂ (a : Matrix (Fin 2) (Fin 2) F) = μ₂ • u₂ ∧ μ₁ ≠ μ₂ ∧
      ∀ (u : Fin 2 → F) (μ : F), u ≠ 0 → Matrix.vecMul u (a : Matrix (Fin 2) (Fin 2) F) = μ • u →
        ∃ c : F, c ≠ 0 ∧ (u = c • u₁ ∨ u = c • u₂) := by
  set A := (a : Matrix (Fin 2) (Fin 2) F) with hA
  have ht : A.trace ≠ 0 := trace_ne_zero_of_odd_orderOf hao hna
  have hχ₁ := eigenvalue_sq_sub_trace_mul_add_det hu₁ h₁
  set μ₂ := A.trace - μ₁ with hμ₂
  have hdet₂ : (A - μ₂ • 1).det = 0 := by
    rw [det_sub_smul_one, hμ₂]
    linear_combination hχ₁
  obtain ⟨u₂, hu₂, h₂⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet₂
  rw [vecMul_sub_smul_one_eq_zero_iff] at h₂
  have hM : ∀ ν : F, A - ν • 1 ≠ 0 := by
    intro ν hν
    apply hna ν
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← sub_eq_zero, hν]
  refine ⟨u₂, μ₂, hu₂, h₂, ?_, ?_⟩
  · intro h
    apply ht
    have : A.trace = μ₁ + μ₁ := by rw [hμ₂] at h; linear_combination -h
    rw [this, CharTwo.add_self_eq_zero]
  · intro u μ hu h
    have hχ := eigenvalue_sq_sub_trace_mul_add_det hu h
    have hprod : (μ - μ₁) * (μ - μ₂) = 0 := by rw [hμ₂]; linear_combination hχ - hχ₁
    have key : ∀ {w : Fin 2 → F} {ν : F}, w ≠ 0 → Matrix.vecMul w A = ν • w → μ = ν →
        ∃ c : F, c ≠ 0 ∧ u = c • w := by
      intro w ν hw hwν hμν
      subst hμν
      obtain ⟨c, hc⟩ := exists_eq_smul_of_vecMul_eq_zero (hM μ) hw
        (vecMul_sub_smul_one_eq_zero_iff.mpr h) (vecMul_sub_smul_one_eq_zero_iff.mpr hwν)
      refine ⟨c, ?_, hc⟩
      rintro rfl
      exact hu (by rw [hc, zero_smul])
    rcases mul_eq_zero.mp hprod with h' | h'
    · obtain ⟨c, hc, hc'⟩ := key hu₁ h₁ (sub_eq_zero.mp h')
      exact ⟨c, hc, Or.inl hc'⟩
    · obtain ⟨c, hc, hc'⟩ := key hu₂ h₂ (sub_eq_zero.mp h')
      exact ⟨c, hc, Or.inr hc'⟩

private lemma two_dvd_card : 2 ∣ Nat.card F := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  exact dvd_pow_self 2 n.ne_zero

private noncomputable def toSL : GL (Fin 2) F →* GL (Fin 2) F where
  toFun g := Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Matrix.GeneralLinearGroup.det g ^ (Nat.card F / 2))⁻¹ * g
  map_one' := by simp
  map_mul' g h := by
    have hc : ∀ (c : Fˣ) (k : GL (Fin 2) F),
        Matrix.GeneralLinearGroup.scalar (Fin 2) c * k =
          k * Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
      intro c k
      have hmem : Matrix.GeneralLinearGroup.scalar (Fin 2) c ∈ Subgroup.center (GL (Fin 2) F) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨c, rfl⟩
      exact (Subgroup.mem_center_iff.mp hmem k).symm
    simp only [map_mul, mul_pow, mul_inv, mul_assoc]
    rw [← mul_assoc _ g h, hc _ g, mul_assoc]

private lemma toSL_coe (g : GL (Fin 2) F) :
    ((toSL g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      (((Matrix.GeneralLinearGroup.det g ^ (Nat.card F / 2))⁻¹ : Fˣ) : F) •
        (g : Matrix (Fin 2) (Fin 2) F) := by
  show ((Matrix.GeneralLinearGroup.scalar (Fin 2) _ * g : GL (Fin 2) F) :
    Matrix (Fin 2) (Fin 2) F) = _
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_eq_diagonal_mul]

private lemma toSL_mem (g : GL (Fin 2) F) : toSL g ∈ StatedSL 2 F := by
  apply StatedAPI.mem_statedSL_of_det
  rw [toSL_coe, Matrix.det_smul, Fintype.card_fin]
  have hδ : (g : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  have hq : Nat.card F / 2 * 2 = Nat.card F := Nat.div_mul_cancel two_dvd_card
  have hpow : (g : Matrix (Fin 2) (Fin 2) F).det ^ Nat.card F =
      (g : Matrix (Fin 2) (Fin 2) F).det := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _
  rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
    Matrix.GeneralLinearGroup.val_det_apply, inv_pow, ← pow_mul, hq, hpow, inv_mul_cancel₀ hδ]

private lemma card_map_toSL_dvd (Γ : Subgroup (GL (Fin 2) F))
    (hΓ : Nat.card ↥(Γ ⊓ StatedSL 2 F) ∣ 2 * (Nat.card F - 1)) :
    Nat.card (Γ.map toSL) ∣ 2 * ((Nat.card F - 1) * (Nat.card F - 1)) := by
  have hnormal : (StatedSL 2 F).Normal := by
    rw [StatedAPI.statedSL_eq_ker_det]
    infer_instance
  refine (Subgroup.card_map_dvd Γ toSL).trans ?_
  have hrel := Subgroup.relIndex_mul_card (StatedSL 2 F) Γ
  rw [inf_comm] at hrel
  rw [← hrel, show 2 * ((Nat.card F - 1) * (Nat.card F - 1)) =
    (Nat.card F - 1) * (2 * (Nat.card F - 1)) by ring]
  refine Nat.mul_dvd_mul ?_ hΓ
  refine (Subgroup.relIndex_dvd_index_of_normal _ _).trans ?_
  rw [StatedAPI.statedSL_eq_ker_det, Subgroup.index_ker, ← Nat.card_units F]
  exact Subgroup.card_subgroup_dvd_card _

theorem commute_of_odd_orderOf (Γ : Subgroup (GL (Fin 2) F))
    (hΓ : Nat.card ↥(Γ ⊓ StatedSL 2 F) ∣ 2 * (Nat.card F - 1))
    {a b : GL (Fin 2) F} (ha : a ∈ Γ) (hb : b ∈ Γ) (hao : Odd (orderOf a))
    (hbo : Odd (orderOf b)) : Commute a b := by
  have hq1 : Odd (Nat.card F - 1) := by
    obtain ⟨k, hk⟩ := two_dvd_card (F := F)
    have : 0 < Nat.card F := Nat.card_pos
    exact ⟨k - 1, by omega⟩
  obtain ⟨N, hNodd, hNmem⟩ :=
    exists_odd_subgroup_of_card_dvd_two_mul (hq1.mul hq1) (card_map_toSL_dvd Γ hΓ)
  set K := N.map (Γ.map toSL).subtype
  have hmemK : ∀ g ∈ Γ, Odd (orderOf g) → toSL g ∈ K := by
    intro g hg hgo
    refine ⟨⟨toSL g, Subgroup.mem_map_of_mem _ hg⟩, hNmem _ ?_, rfl⟩
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hgo (orderOf_map_dvd _ _)
  have hKSL : K ≤ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) F →* GL (Fin 2) F).range := by
    rw [← StatedAPI.statedSL_eq_range_toGL]
    rintro _ ⟨⟨_, ⟨g, -, rfl⟩⟩, -, rfl⟩
    exact toSL_mem g
  set K' := K.comap Matrix.SpecialLinearGroup.toGL
  have hK'map : K'.map Matrix.SpecialLinearGroup.toGL = K := Subgroup.map_comap_eq_self hKSL
  have hK'card : Nat.card K' = Nat.card N := by
    rw [← Subgroup.card_map_of_injective Matrix.SpecialLinearGroup.toGL_injective, hK'map,
      Subgroup.card_map_of_injective (Γ.map toSL).subtype_injective]
  have : Finite K' := Nat.finite_of_card_ne_zero (by rw [hK'card]; exact hNodd.pos.ne')
  obtain ⟨hcyc, -⟩ := CFSG.LocalAnalysis.SteinbergBS.char_two_sl2_odd_subgroup_cyclic K'
    (hK'card ▸ hNodd)
  have hpre : ∀ g ∈ Γ, Odd (orderOf g) →
      ∃ x ∈ K', Matrix.SpecialLinearGroup.toGL x = toSL g := by
    intro g hg hgo
    have h := hmemK g hg hgo
    rw [← hK'map] at h
    exact h
  obtain ⟨x, hx, hxa⟩ := hpre a ha hao
  obtain ⟨y, hy, hyb⟩ := hpre b hb hbo
  have hxy : x * y = y * x :=
    congrArg Subtype.val ((IsCyclic.commGroup (α := K')).mul_comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hcomm : toSL a * toSL b = toSL b * toSL a := by
    rw [← hxa, ← hyb, ← map_mul, ← map_mul, hxy]
  have hm := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hcomm
  simp only [Units.val_mul, toSL_coe] at hm
  rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (((Matrix.GeneralLinearGroup.det b ^
    (Nat.card F / 2))⁻¹ : Fˣ) : F)] at hm
  show a * b = b * a
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact smul_right_injective _ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) hm

theorem odd_eigen_common (Γ : Subgroup (GL (Fin 2) F))
    (hΓ : Nat.card ↥(Γ ⊓ StatedSL 2 F) ∣ 2 * (Nat.card F - 1))
    {a b : GL (Fin 2) F} (ha : a ∈ Γ) (hb : b ∈ Γ) (hao : Odd (orderOf a))
    (hbo : Odd (orderOf b))
    (hna : ∀ c : F, (a : Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) c)
    (hnb : ∀ c : F, (b : Matrix (Fin 2) (Fin 2) F) ≠ Matrix.scalar (Fin 2) c)
    {u : Fin 2 → F} (hu : u ≠ 0) {μ : F}
    (hub : Matrix.vecMul u (b : Matrix (Fin 2) (Fin 2) F) = μ • u) :
    ∃ μ' : F, Matrix.vecMul u (a : Matrix (Fin 2) (Fin 2) F) = μ' • u := by
  have hAB : (a : Matrix (Fin 2) (Fin 2) F) * b = b * a := by
    rw [← Units.val_mul, (commute_of_odd_orderOf Γ hΓ ha hb hao hbo).eq, Units.val_mul]
  have hw : Matrix.vecMul (Matrix.vecMul u a) (b : Matrix (Fin 2) (Fin 2) F) =
      μ • Matrix.vecMul u a := by
    rw [Matrix.vecMul_vecMul, hAB, ← Matrix.vecMul_vecMul, hub, Matrix.smul_vecMul]
  have hM : (b : Matrix (Fin 2) (Fin 2) F) - μ • 1 ≠ 0 := by
    intro h
    apply hnb μ
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, ← sub_eq_zero, h]
  exact exists_eq_smul_of_vecMul_eq_zero hM hu (vecMul_sub_smul_one_eq_zero_iff.mpr hw)
    (vecMul_sub_smul_one_eq_zero_iff.mpr hub)

end PGL

end CFSG.RankThree.GF2n.Smith81
