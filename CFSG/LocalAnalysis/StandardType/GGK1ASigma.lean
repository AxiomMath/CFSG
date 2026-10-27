module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.LocalAnalysis.StandardType.GGK1ALift
public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
public import CFSG.LocalAnalysis.StandardType.GGK1SigmaAbs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlockPair
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.DualPoly

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.CALinearPrimary
open CFSG.LieType.SemisimpleCentralizers.Held CFSG.LieType.SemisimpleCentralizers.HeldLang

private theorem ggK1As_blockA_qs_false {r nf d : ℕ}
    (h : (ggMultBlockA r nf d).qs = false) :
    nf = 1 ∧ ((ggMultBlockA r nf d).lab = ⟨.A, 1, 1⟩ ∨
      (ggMultBlockA r nf d).lab = ⟨.twA, 2, 1⟩) := by
  by_cases hd : d = 1
  · rw [ggMultBlockA, if_pos hd] at h ⊢
    simp only [decide_eq_false_iff_not, not_not] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, Or.inl rfl⟩
  · rw [ggMultBlockA, if_neg hd] at h ⊢
    by_cases hr : 2 ≤ r
    · rw [if_pos hr] at h ⊢
      simp only [decide_eq_false_iff_not, not_not] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, Or.inr rfl⟩
    · rw [if_neg hr] at h ⊢
      simp only [decide_eq_false_iff_not, not_not] at h
      subst h
      exact ⟨rfl, Or.inl rfl⟩

private theorem ggK1As_datumA_qs_false {p nf d : ℕ} {tw : Bool} {m : List ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA p nf d tw m).orbits) (hqs : o.qs = false) :
    nf = 1 ∧ (o.lab = ⟨.A, 1, 1⟩ ∨ o.lab = ⟨.twA, 2, 1⟩) := by
  by_cases htriv : (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
  · rw [ggMultDatumA, if_pos htriv] at ho
    simp only [List.mem_map, List.mem_filter, List.mem_range] at ho
    obtain ⟨j, ⟨-, -⟩, rfl⟩ := ho
    exact ggK1As_blockA_qs_false hqs
  · rw [ggMultDatumA, if_neg htriv] at ho
    simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range,
      List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with ho | ho
    ·
      by_cases hm0 : 2 ≤ m.headD 0
      · rw [if_pos hm0] at ho
        by_cases htw : tw = false
        · rw [if_pos htw] at ho
          obtain rfl := List.mem_singleton.mp ho
          simp only [decide_eq_false_iff_not, not_not] at hqs
          obtain ⟨hr, hnf⟩ := hqs
          subst hnf
          exact ⟨rfl, Or.inl (by rw [hr])⟩
        · rw [if_neg htw] at ho
          obtain rfl := List.mem_singleton.mp ho
          exact ggK1As_blockA_qs_false hqs
      · rw [if_neg hm0] at ho
        exact absurd ho (List.not_mem_nil)
    ·
      obtain ⟨j, ⟨-, -⟩, rfl⟩ := ho
      simp at hqs

theorem ggK1A_qs_false_corner {p nf : ℕ} {tw : Bool} {m : List ℕ} {o : GGKacOrbit}
    (hp : p.Prime) (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (ho : o ∈ (ggMultDatumA p nf (ggMultOrd p nf) tw m).orbits) (hqs : o.qs = false) :
    nf = 1 ∧ p = 3 ∧ (o.lab = ⟨.A, 1, 1⟩ ∨ o.lab = ⟨.twA, 2, 1⟩) := by
  obtain ⟨hnf, hlab⟩ := ggK1As_datumA_qs_false ho hqs
  subst hnf
  have hp3 : p ∣ 3 := by
    rcases hdvd with h | h
    · have h1 : p ∣ 1 := by simpa using h
      exact absurd h1 hp.not_dvd_one
    · simpa using h
  have hle : p ≤ 3 := Nat.le_of_dvd (by norm_num) hp3
  have hge : 2 ≤ p := hp.two_le
  refine ⟨rfl, ?_, hlab⟩
  interval_cases p
  · exact absurd hp3 (by norm_num)
  · rfl

private theorem ggK1As_qs_false_dim {m : List ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA 3 1 (ggMultOrd 3 1) true m).orbits) (hqs : o.qs = false) :
    ∃ j, j < 3 ∧ (m.getD j 0 = 2 ∨ m.getD j 0 = 3) := by
  have hd : ggMultOrd 3 1 = 2 := by decide
  rw [hd] at ho
  rw [ggMultDatumA] at ho
  rw [if_pos (by decide : (true = false ∧ 2 = 1) ∨ (true = true ∧ 2 = 2))] at ho
  simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at ho
  obtain ⟨j, hj, rfl⟩ := ho
  obtain ⟨hj3, hj2⟩ := hj
  have hblk := (ggK1As_blockA_qs_false (r := m.getD j 0 - 1) (nf := 1) (d := 2) hqs).2
  refine ⟨j, hj3, ?_⟩
  rcases hblk with h | h
  · left
    by_cases hge : 2 ≤ m.getD j 0 - 1
    · rw [ggMultBlockA, if_neg (by decide : ¬ ((2 : ℕ) = 1)), if_pos hge] at h
      dsimp only at h
      exact absurd (congrArg LargeEvenLabel.tag h) (fun htag => by cases htag)
    · rw [ggMultBlockA, if_neg (by decide : ¬ ((2 : ℕ) = 1)), if_neg hge] at h
      have hlt : m.getD j 0 - 1 < 2 := not_le.mp hge
      omega
  · right
    by_cases hge : 2 ≤ m.getD j 0 - 1
    · rw [ggMultBlockA, if_neg (by decide : ¬ ((2 : ℕ) = 1)), if_pos hge] at h
      dsimp only at h
      have hr : m.getD j 0 - 1 = 2 := congrArg LargeEvenLabel.rank h
      omega
    · rw [ggMultBlockA, if_neg (by decide : ¬ ((2 : ℕ) = 1)), if_neg hge] at h
      dsimp only at h
      exact absurd (congrArg LargeEvenLabel.tag h) (fun htag => by cases htag)

private theorem ggK1As_units_subsingleton {K : Type} [Field K] (hK : Nat.card K = 2) :
    Subsingleton Kˣ := by
  have h : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.mp h).1

private theorem ggK1As_matrix_det_eq_one {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2)
    (A : GL (Fin N) K) : (A : Matrix (Fin N) (Fin N) K).det = 1 := by
  haveI := ggK1As_units_subsingleton hK
  have h1 : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
  have h2 := congrArg Units.val h1
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h2

private theorem ggK1As_SL_eq_top {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) :
    LargeEvenSLGroup (Fin N) K = ⊤ := by
  rw [eq_top_iff]
  intro A _
  rw [CFSG.StandardType.TypeA.mem_largeEvenSLGroup_iff]
  exact ggK1As_matrix_det_eq_one hK A

private theorem ggK1As_scalars_subgroupOf_bot {N : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) :
    (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSLGroup (Fin N) K) = ⊥ := by
  haveI := ggK1As_units_subsingleton hK
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  rw [← hc, show c = 1 from Subsingleton.elim c 1, map_one]
  rfl

private theorem ggK1As_projMk_injective {N : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2) :
    Function.Injective (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker :=
    MonoidHom.mem_ker.mpr hg
  rw [QuotientGroup.ker_mk', ggK1As_scalars_subgroupOf_bot hK] at hmem
  exact Subgroup.mem_bot.mp hmem

private noncomputable def ggK1As_eG {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) :
    ↥(LargeEvenSLGroup (Fin N) K) ≃* LinearMap.GeneralLinearGroup K (Fin N → K) :=
  (MulEquiv.subgroupCongr (ggK1As_SL_eq_top hK)).trans
    ((Subgroup.topEquiv).trans Matrix.GeneralLinearGroup.toLin)

private noncomputable def ggK1As_eR {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) :
    ↥(LargeEvenSLGroup (Fin N) K) ≃* LargeEvenProj (LargeEvenSLGroup (Fin N) K) :=
  MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
    ⟨ggK1As_projMk_injective hK, QuotientGroup.mk'_surjective _⟩

private noncomputable def ggK1As_e {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) :
    LargeEvenProj (LargeEvenSLGroup (Fin N) K) ≃*
      LinearMap.GeneralLinearGroup K (Fin N → K) :=
  (ggK1As_eR hK).symm.trans (ggK1As_eG hK)

private noncomputable def ggK1As_eM {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) :
    LargeEvenProj (LargeEvenSLGroup (Fin N) K) ≃* GL (Fin N) K :=
  (ggK1As_eR hK).symm.trans
    ((MulEquiv.subgroupCongr (ggK1As_SL_eq_top hK)).trans Subgroup.topEquiv)

private theorem ggK1As_e_projMk {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2)
    (g : ↥(LargeEvenSLGroup (Fin N) K)) :
    ggK1As_e hK (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) g) = ggK1As_eG hK g := by
  show ggK1As_eG hK ((ggK1As_eR hK).symm ((ggK1As_eR hK) g)) = ggK1As_eG hK g
  rw [MulEquiv.symm_apply_apply]

private theorem ggK1As_centre_bot {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) :
    Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) = ⊥ := by
  haveI := ggK1As_units_subsingleton hK
  have hcent : Subgroup.center (GL (Fin N) K) = ⊥ := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar, eq_bot_iff]
    rintro _ ⟨c, rfl⟩
    rw [show c = 1 from Subsingleton.elim c 1, map_one]
    exact Subgroup.mem_bot.mpr rfl
  rw [eq_bot_iff]
  intro z hz
  have hzmap : ggK1As_eM hK z ∈ Subgroup.center (GL (Fin N) K) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨r, rfl⟩ := (ggK1As_eM hK).surjective y
    rw [← map_mul, ← map_mul, hz r]
  rw [hcent] at hzmap
  have h1 : ggK1As_eM hK z = 1 := Subgroup.mem_bot.mp hzmap
  apply (ggK1As_eM hK).injective
  rw [h1, map_one]

private theorem ggK1As_conj_injective {R : Type} [Group R]
    (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  intro s t hst
  have h1 : MulAut.conj (t⁻¹ * s) = 1 := by
    rw [map_mul, map_inv, hst, inv_mul_cancel]
  have h2 : t⁻¹ * s ∈ Subgroup.center R := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h3 : (t⁻¹ * s) * g * (t⁻¹ * s)⁻¹ = g := by
      have h := congrFun (congrArg (fun e : MulAut R => (e : R → R)) h1) g
      rw [MulAut.conj_apply] at h
      simpa using h
    have hzg : (t⁻¹ * s) * g = g * (t⁻¹ * s) := by
      calc (t⁻¹ * s) * g = ((t⁻¹ * s) * g * (t⁻¹ * s)⁻¹) * (t⁻¹ * s) := by group
        _ = g * (t⁻¹ * s) := by rw [h3]
    exact hzg.symm
  rw [hZ] at h2
  have h3 : t⁻¹ * s = 1 := Subgroup.mem_bot.mp h2
  calc s = t * (t⁻¹ * s) := by group
    _ = t := by rw [h3, mul_one]

private theorem ggK1As_conjImage_inner {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2) :
    ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
      (Set.univ : Set (GL (Fin N) K)),
      ∃ s : LargeEvenProj (LargeEvenSLGroup (Fin N) K), φ = MulAut.conj s := by
  rintro φ ⟨A, -, hA⟩
  let gA : ↥(LargeEvenSLGroup (Fin N) K) :=
    ⟨A, by
      rw [CFSG.StandardType.TypeA.mem_largeEvenSLGroup_iff]
      exact ggK1As_matrix_det_eq_one hK A⟩
  refine ⟨LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) gA, ?_⟩
  ext l
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective _ l
  have hmem : A * (h : GL (Fin N) K) * A⁻¹ ∈ LargeEvenSLGroup (Fin N) K := by
    rw [CFSG.StandardType.TypeA.mem_largeEvenSLGroup_iff]
    exact ggK1As_matrix_det_eq_one hK _
  let h' : ↥(LargeEvenSLGroup (Fin N) K) := ⟨A * (h : GL (Fin N) K) * A⁻¹, hmem⟩
  have hrel : (h' : GL (Fin N) K) = A * (h : GL (Fin N) K) * A⁻¹ := rfl
  have hφ := hA h h' hrel
  rw [hφ, MulAut.conj_apply]
  have hgm : gA * h * gA⁻¹ = h' := by
    apply Subtype.ext
    show (gA : GL (Fin N) K) * (h : GL (Fin N) K) * (gA : GL (Fin N) K)⁻¹ =
      (h' : GL (Fin N) K)
    rw [hrel]
  calc LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h'
      = LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (gA * h * gA⁻¹) := by rw [hgm]
    _ = LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) gA *
          LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h *
          (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) gA)⁻¹ := by
          rw [map_mul, map_mul, map_inv]

private theorem ggK1As_datumA_head_eq_two {m : List ℕ} {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA 3 1 2 false m).orbits) (hqs : o.qs = false) :
    m.headD 0 = 2 := by
  unfold ggMultDatumA at ho
  rw [if_neg (by decide : ¬ ((false = false ∧ 2 = 1) ∨ (false = true ∧ 2 = 2)))] at ho
  simp only [List.mem_append, List.mem_map, List.mem_filter, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false] at ho
  rcases ho with ho | ho
  · by_cases hm0 : 2 ≤ m.headD 0
    · rw [if_pos hm0] at ho
      simp only [if_true] at ho
      obtain rfl := List.mem_singleton.mp ho
      simp only [decide_eq_false_iff_not, not_not, Bool.false_eq_true] at hqs
      obtain ⟨hr, -⟩ := hqs
      omega
    · rw [if_neg hm0] at ho
      exact absurd ho (List.not_mem_nil)
  · obtain ⟨j, ⟨-, -⟩, rfl⟩ := ho
    exact Bool.noConfusion hqs

private theorem ggK1As_mem_primaryFactors_X_sub_one {K : Type} [Field K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {T : Module.End K V}
    (hV0 : Module.finrank K (primaryComponent T ((Polynomial.X : K[X]) - 1)) = 2) :
    ((Polynomial.X : K[X]) - 1) ∈ primaryFactors T := by
  have hirr : Irreducible ((Polynomial.X : K[X]) - 1) := by
    simpa using (irreducible_X_sub_C (1 : K))
  have hmon : ((Polynomial.X : K[X]) - 1).Monic := monic_X_sub_C 1
  have hne : primaryComponent T ((Polynomial.X : K[X]) - 1) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hV0
    simp at hV0
  obtain ⟨w, hw⟩ : ∃ w ∈ primaryComponent T ((Polynomial.X : K[X]) - 1), w ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Submodule.eq_bot_iff _ |>.mpr fun v hv => h v hv)
  exact CFSG.StandardType.SUTB.mem_primaryFactors_of_ker hirr hmon hw.2
    (mem_primaryComponent.mp hw.1)

private theorem ggK1As_char_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    (2 : K) = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [Fintype.card_eq_nat_card, hK]; norm_num)
  exact CharP.cast_eq_zero K 2

private theorem ggK1As_squarefree_X_pow_three_sub_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) : Squarefree (((Polynomial.X : K[X]) ^ 3 - 1)) := by
  have h2 : (2 : K) = 0 := ggK1As_char_two hK
  have hder : (((Polynomial.X : K[X]) ^ 3 - 1)).derivative = (Polynomial.X : K[X]) ^ 2 := by
    simp only [derivative_sub, derivative_pow, derivative_one, derivative_X, mul_one, pow_one]
    ring_nf
    have h3 : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    rw [show (C (3 : K) : K[X]) = 1 from by rw [h3, map_one], one_mul]
  have hsep : (((Polynomial.X : K[X]) ^ 3 - 1)).Separable := by
    rw [Polynomial.separable_def, hder]
    refine ⟨-1, Polynomial.X, ?_⟩
    ring
  exact hsep.squarefree

private theorem ggK1As_squarefree_X_pow_three_char2 {K : Type} [Field K] (h2 : (2 : K) = 0) :
    Squarefree (((Polynomial.X : K[X]) ^ 3 - 1)) := by
  have hder : (((Polynomial.X : K[X]) ^ 3 - 1)).derivative = (Polynomial.X : K[X]) ^ 2 := by
    simp only [derivative_sub, derivative_pow, derivative_one, derivative_X, mul_one, pow_one]
    ring_nf
    have h3 : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    rw [show (C (3 : K) : K[X]) = 1 from by rw [h3, map_one], one_mul]
  have hsep : (((Polynomial.X : K[X]) ^ 3 - 1)).Separable := by
    rw [Polynomial.separable_def, hder]
    refine ⟨-1, Polynomial.X, ?_⟩
    ring
  exact hsep.squarefree

private theorem ggK1As_squarefree_minpoly_of_pow_three {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : LinearMap.GeneralLinearGroup K V} (hK : Nat.card K = 2) (hT : T ^ 3 = 1) :
    Squarefree (minpoly K (T : Module.End K V)) := by
  apply squarefree_minpoly_of_aeval_eq_zero (ggK1As_squarefree_X_pow_three_sub_one hK)
  have hx : (T : Module.End K V) ^ 3 = 1 := by
    have := congrArg Units.val hT
    simpa using this
  rw [map_sub, map_pow, aeval_X, hx]
  simp

private theorem ggK1As_glEquivPerm {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 2) :
    Nonempty (GL (Fin 2) E ≃* Equiv.Perm (Fin 3)) := by
  haveI hsub : Subsingleton Eˣ := by
    have h : Nat.card Eˣ = 1 := by rw [Nat.card_units, hE]
    exact (Nat.card_eq_one_iff_unique.mp h).1
  obtain ⟨eP⟩ := CFSG.StandardType.RCSPSL.nonempty_sl2_equiv_perm (F := E) hE
  let f : Matrix.SpecialLinearGroup (Fin 2) E →* GL (Fin 2) E := Matrix.SpecialLinearGroup.toGL
  have hinj : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    have h' := congrArg (fun x : GL (Fin 2) E => (x : Matrix (Fin 2) (Fin 2) E)) h
    rw [show ((f a : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      (a : Matrix (Fin 2) (Fin 2) E) from rfl,
      show ((f b : GL (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
      (b : Matrix (Fin 2) (Fin 2) E) from rfl] at h'
    exact h'
  have hsurj : Function.Surjective f := by
    intro g
    have hdet : (g : Matrix (Fin 2) (Fin 2) E).det = 1 := by
      have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
      have h2 := congrArg Units.val h1
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using h2
    refine ⟨⟨g, hdet⟩, ?_⟩
    exact Units.ext rfl
  exact ⟨(MulEquiv.ofBijective f ⟨hinj, hsurj⟩).symm.trans eP⟩

private theorem ggK1As_exists_three_GL {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = 2) (V0 : Type) [AddCommGroup V0] [Module E V0]
    [FiniteDimensional E V0] (hV0 : Module.finrank E V0 = 2) :
    ∃ R0 : (Module.End E V0)ˣ, R0 ^ 3 = 1 ∧ R0 ≠ 1 ∧
      ∀ γ : (Module.End E V0)ˣ, γ ^ 3 = 1 → Commute γ R0 := by
  obtain ⟨eGLm⟩ := ggK1As_glEquivPerm hE
  let b : Module.Basis (Fin 2) E V0 := (Module.finBasis E V0).reindex (finCongr hV0)
  let eA : Module.End E V0 ≃ₐ[E] Matrix (Fin 2) (Fin 2) E := LinearMap.toMatrixAlgEquiv b
  let eGL : (Module.End E V0)ˣ ≃* GL (Fin 2) E := Units.mapEquiv eA.toMulEquiv
  let c : Equiv.Perm (Fin 3) := finRotate 3
  have hc3 : c ^ 3 = 1 := by decide
  have hcne : c ≠ 1 := by decide
  have hcomm : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = (1 : Equiv.Perm (Fin 3)) →
      τ * c = c * τ := by decide
  let R0u : (Module.End E V0)ˣ := eGL.symm (eGLm.symm c)
  have hR0u3 : R0u ^ 3 = 1 := by
    simp only [R0u]
    rw [← map_pow, ← map_pow, hc3, map_one, map_one]
  have hR0une : R0u ≠ 1 := by
    intro h
    have h1 : eGLm.symm c = 1 := by
      have := congrArg eGL h
      simpa [R0u] using this
    have h2 : c = 1 := by
      have := congrArg eGLm h1
      simpa using this
    exact hcne h2
  refine ⟨R0u, hR0u3, hR0une, ?_⟩
  intro γ hγ3
  have hτ3 : (eGLm (eGL γ)) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, hγ3, map_one, map_one]
  have hc := hcomm (eGLm (eGL γ)) hτ3
  have h2 : eGL γ * (eGLm.symm c) = (eGLm.symm c) * eGL γ := by
    have h1 : eGLm (eGL γ) * c = c * eGLm (eGL γ) := hc
    have := congrArg eGLm.symm h1
    simpa only [map_mul, MulEquiv.symm_apply_apply] using this
  have h3 : γ * R0u = R0u * γ := by
    have := congrArg eGL.symm h2
    simpa only [map_mul, MulEquiv.symm_apply_apply, R0u] using this
  exact h3

private theorem ggK1As_three_witness {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : LinearMap.GeneralLinearGroup K V} (hK : Nat.card K = 2) (hT : T ^ 3 = 1)
    (hV0K : Module.finrank K
      (primaryComponent (T : Module.End K V) ((Polynomial.X : K[X]) - 1)) = 2) :
    ∃ t : LinearMap.GeneralLinearGroup K V,
      t ^ 3 = 1 ∧ t ≠ 1 ∧ Commute (t : Module.End K V) (T : Module.End K V) ∧
      (∀ b ∈ primaryFactors (T : Module.End K V), b ≠ ((Polynomial.X : K[X]) - 1) →
        ∀ v ∈ primaryComponent (T : Module.End K V) b, (t : Module.End K V) v = v) ∧
      (∃ v ∈ primaryComponent (T : Module.End K V) ((Polynomial.X : K[X]) - 1),
        (t : Module.End K V) v ≠ v) ∧
      (∀ w : LinearMap.GeneralLinearGroup K V,
        Commute (w : Module.End K V) (T : Module.End K V) → w ^ 3 = 1 →
        Commute (t : Module.End K V) (w : Module.End K V)) := by
  have hsq := ggK1As_squarefree_minpoly_of_pow_three hK hT
  have h0 := ggK1As_mem_primaryFactors_X_sub_one hV0K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [Fintype.card_eq_nat_card, hK]; norm_num)
  let xE : K[X] := (Polynomial.X : K[X]) - 1
  let V0 : Submodule K V := primaryComponent (T : Module.End K V) xE
  obtain ⟨R0, hR03, hR0ne, hR0comm⟩ :=
    ggK1As_exists_three_GL (E := K) hK V0 hV0K
  let p0 : Module.End K V := primaryProjection (T : Module.End K V) xE
  have hp0_mem : ∀ v, p0 v ∈ V0 := fun v => primaryProjection_mem hsq h0 v
  have hp0_on : ∀ v ∈ V0, p0 v = v := fun v hv => primaryProjection_of_mem hsq h0 hv
  have hp0_off : ∀ b ∈ primaryFactors (T : Module.End K V), b ≠ xE →
      ∀ v ∈ primaryComponent (T : Module.End K V) b, p0 v = 0 :=
    fun b hb hne v hv => primaryProjection_of_mem_ne hsq h0 hb hne hv
  let p0' : V →ₗ[K] V0 := p0.codRestrict V0 hp0_mem
  let e : Module.End K V := V0.subtype ∘ₗ (R0 : Module.End K V0) ∘ₗ p0'
  let ei : Module.End K V :=
    V0.subtype ∘ₗ ((R0⁻¹ : (Module.End K V0)ˣ) : Module.End K V0) ∘ₗ p0'
  have he_on : ∀ v : V0, e (v : V) = ((R0 : Module.End K V0) v : V) := by
    intro v
    show V0.subtype ((R0 : Module.End K V0) (p0' (v : V))) = _
    have h1 : p0' (v : V) = v := by
      apply Subtype.ext
      exact hp0_on (v : V) v.2
    rw [h1]
    rfl
  have he_off : ∀ b ∈ primaryFactors (T : Module.End K V), b ≠ xE →
      ∀ v ∈ primaryComponent (T : Module.End K V) b, e v = 0 := by
    intro b hb hne v hv
    show V0.subtype ((R0 : Module.End K V0) (p0' v)) = 0
    have h1 : p0' v = 0 := by
      apply Subtype.ext
      exact hp0_off b hb hne v hv
    rw [h1, map_zero]
    rfl
  have hei_on : ∀ v : V0, ei (v : V) =
      ((((R0⁻¹ : (Module.End K V0)ˣ) : Module.End K V0) v : V0) : V) := by
    intro v
    show V0.subtype (((R0⁻¹ : (Module.End K V0)ˣ) : Module.End K V0) (p0' (v : V))) = _
    have h1 : p0' (v : V) = v := by
      apply Subtype.ext
      exact hp0_on (v : V) v.2
    rw [h1]
    rfl
  have hei_off : ∀ b ∈ primaryFactors (T : Module.End K V), b ≠ xE →
      ∀ v ∈ primaryComponent (T : Module.End K V) b, ei v = 0 := by
    intro b hb hne v hv
    show V0.subtype (((R0⁻¹ : (Module.End K V0)ˣ) : Module.End K V0) (p0' v)) = 0
    have h1 : p0' v = 0 := by
      apply Subtype.ext
      exact hp0_off b hb hne v hv
    rw [h1, map_zero]
    rfl
  let tEnd : Module.End K V := 1 - p0 + e
  let tInv : Module.End K V := 1 - p0 + ei
  have htEnd_on : ∀ v : V0, tEnd (v : V) = ((R0 : Module.End K V0) v : V) := by
    intro v
    show ((1 : Module.End K V) - p0 + e) (v : V) = _
    change (v : V) - p0 (v : V) + e (v : V) = _
    rw [hp0_on (v : V) v.2, he_on v]
    abel
  have htEnd_off : ∀ b ∈ primaryFactors (T : Module.End K V), b ≠ xE →
      ∀ v ∈ primaryComponent (T : Module.End K V) b, tEnd v = v := by
    intro b hb hne v hv
    show ((1 : Module.End K V) - p0 + e) v = v
    change v - p0 v + e v = v
    rw [hp0_off b hb hne v hv, he_off b hb hne v hv]
    abel
  have htInv_on : ∀ v : V0, tInv (v : V) =
      (((R0⁻¹ : (Module.End K V0)ˣ) : Module.End K V0) v : V) := by
    intro v
    show ((1 : Module.End K V) - p0 + ei) (v : V) = _
    change (v : V) - p0 (v : V) + ei (v : V) = _
    rw [hp0_on (v : V) v.2, hei_on v]
    abel
  have htInv_off : ∀ b ∈ primaryFactors (T : Module.End K V), b ≠ xE →
      ∀ v ∈ primaryComponent (T : Module.End K V) b, tInv v = v := by
    intro b hb hne v hv
    show ((1 : Module.End K V) - p0 + ei) v = v
    change v - p0 v + ei v = v
    rw [hp0_off b hb hne v hv, hei_off b hb hne v hv]
    abel
  have htInv_mul : tEnd * tInv = 1 := by
    apply ext_primaryComponent hsq
    intro b hb v hv
    show tEnd (tInv v) = v
    by_cases hb0 : b = xE
    · subst hb0
      rw [htInv_on ⟨v, hv⟩, htEnd_on (((R0⁻¹ : (Module.End K V0)ˣ) : Module.End K V0) ⟨v, hv⟩)]
      have h1 : (R0 : Module.End K V0) (((R0⁻¹ : (Module.End K V0)ˣ) : Module.End K V0)
          ⟨v, hv⟩) = ⟨v, hv⟩ := by
        rw [← Module.End.mul_apply, Units.mul_inv]
        rfl
      exact congrArg Subtype.val h1
    · rw [htInv_off b hb hb0 v hv, htEnd_off b hb hb0 v hv]
  have htEnd3 : tEnd ^ 3 = 1 := by
    apply ext_primaryComponent hsq
    intro b hb v hv
    show (tEnd ^ 3) v = (1 : Module.End K V) v
    by_cases hb0 : b = xE
    · subst hb0
      show tEnd (tEnd (tEnd v)) = v
      rw [htEnd_on ⟨v, hv⟩]
      rw [htEnd_on ((R0 : Module.End K V0) ⟨v, hv⟩)]
      rw [htEnd_on ((R0 : Module.End K V0) ((R0 : Module.End K V0) ⟨v, hv⟩))]
      show (((R0 : Module.End K V0) ((R0 : Module.End K V0)
        ((R0 : Module.End K V0) ⟨v, hv⟩))) : V) = _
      have h := congrArg (fun u : (Module.End K V0)ˣ =>
        ((u : Module.End K V0) ⟨v, hv⟩ : V0)) hR03
      simpa [pow_succ, pow_one, Module.End.mul_apply] using congrArg Subtype.val h
    · show tEnd (tEnd (tEnd v)) = v
      rw [htEnd_off b hb hb0 v hv]
      rw [htEnd_off b hb hb0 v hv]
      rw [htEnd_off b hb hb0 v hv]
  let tU : LinearMap.GeneralLinearGroup K V := Units.mkOfMulEqOne tEnd tInv htInv_mul
  have htU_val : (tU : Module.End K V) = tEnd := Units.val_mkOfMulEqOne .. |>.trans rfl
  have htU3 : tU ^ 3 = 1 := by
    apply Units.ext
    change (tU : Module.End K V) ^ 3 = 1
    rw [htU_val, htEnd3]
  have htUne : tU ≠ 1 := by
    intro h
    have h1 : tEnd = 1 := by
      have := congrArg Units.val h
      simpa [htU_val] using this
    have h2 : (R0 : Module.End K V0) = 1 := by
      ext v
      have := congrArg (fun f : Module.End K V => f (v : V)) h1
      rw [htEnd_on v] at this
      simpa using this
    exact hR0ne (Units.ext h2)
  have hT_on : ∀ v ∈ V0, (T : Module.End K V) v = v := by
    intro v hv
    have h := mem_primaryComponent.mp hv
    have h' : (T : Module.End K V) v - v = 0 := by simpa [xE] using h
    exact sub_eq_zero.mp h'
  have htT : Commute tEnd (T : Module.End K V) := by
    apply ext_primaryComponent hsq
    intro b hb v hv
    show tEnd ((T : Module.End K V) v) = (T : Module.End K V) (tEnd v)
    by_cases hb0 : b = xE
    · subst hb0
      have hTv : (T : Module.End K V) v = v := hT_on v hv
      have htEv : tEnd v = ((R0 : Module.End K V0) ⟨v, hv⟩ : V) := htEnd_on ⟨v, hv⟩
      have hTe : (T : Module.End K V) ((R0 : Module.End K V0) ⟨v, hv⟩ : V) =
          ((R0 : Module.End K V0) ⟨v, hv⟩ : V) :=
        hT_on ((R0 : Module.End K V0) ⟨v, hv⟩) ((R0 : Module.End K V0) ⟨v, hv⟩).2
      rw [hTv, htEv, hTe]
    · rw [htEnd_off b hb hb0 ((T : Module.End K V) v)
        (apply_mem_primaryComponent (Commute.refl (T : Module.End K V)) hv),
        htEnd_off b hb hb0 v hv]
  have ht_nondec : ∃ v ∈ V0, tEnd v ≠ v := by
    have hne : ∃ v : V0, (R0 : Module.End K V0) v ≠ v := by
      by_contra h
      push Not at h
      exact hR0ne (Units.ext (LinearMap.ext h))
    obtain ⟨v, hv⟩ := hne
    refine ⟨(v : V), v.2, ?_⟩
    rw [htEnd_on v]
    intro h
    exact hv (Subtype.ext h)
  refine ⟨tU, htU3, htUne, ?_, ?_, ht_nondec, ?_⟩
  · rw [show (tU : Module.End K V) = tEnd from htU_val]
    exact htT
  · intro b hb hb0 v hv
    rw [show (tU : Module.End K V) = tEnd from htU_val]
    exact htEnd_off b hb hb0 v hv
  · intro w hwT hw3
    let w0 : V0 →ₗ[K] V0 :=
      { toFun := fun v => ⟨(w : Module.End K V) v, apply_mem_primaryComponent hwT v.2⟩
        map_add' := by
          intro a b
          apply Subtype.ext
          exact map_add (w : Module.End K V) (a : V) (b : V)
        map_smul' := by
          intro c a
          apply Subtype.ext
          exact map_smul (w : Module.End K V) c (a : V) }
    let wi0 : V0 →ₗ[K] V0 :=
      { toFun := fun v => ⟨((w⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) v,
          apply_mem_primaryComponent (Commute.units_inv_left hwT) v.2⟩
        map_add' := by
          intro a b
          apply Subtype.ext
          exact map_add ((w⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) (a : V) (b : V)
        map_smul' := by
          intro c a
          apply Subtype.ext
          exact map_smul ((w⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) c (a : V) }
    have hw0_mul : w0 * wi0 = 1 := by
      ext v
      show (w : Module.End K V) (((w⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) (v :
          V))
        = (v : V)
      rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
      rfl
    let wU : (Module.End K V0)ˣ := Units.mkOfMulEqOne w0 wi0 hw0_mul
    have hwU_val : (wU : Module.End K V0) = w0 := rfl
    have hwU3 : wU ^ 3 = 1 := by
      apply Units.ext
      change (wU : Module.End K V0) ^ 3 = 1
      rw [hwU_val]
      show w0 ^ 3 = 1
      have hcoe : ∀ n : ℕ, ∀ v : V0, (((w0 ^ n) v : V0) : V) =
          ((w : Module.End K V) ^ n) (v : V) := by
        intro n
        induction n with
        | zero => intro v; simp
        | succ n ih =>
          intro v
          rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply]
          exact ih (w0 v)
      ext v
      rw [hcoe 3 v]
      have h : ((w : Module.End K V) ^ 3) (v : V) = (v : V) := by
        have h1 : (w : Module.End K V) ^ 3 = 1 := by
          have := congrArg Units.val hw3
          simpa using this
        rw [h1]
        rfl
      exact h
    have hcomm0 : Commute wU R0 := hR0comm wU hwU3
    apply ext_primaryComponent hsq
    intro b hb v hv
    show tEnd ((w : Module.End K V) v) = (w : Module.End K V) (tEnd v)
    by_cases hb0 : b = xE
    · subst hb0
      have hc := congrArg (fun u : (Module.End K V0)ˣ =>
        ((u : Module.End K V0) ⟨v, hv⟩ : V0)) hcomm0.eq
      have hc' : ((w0 ((R0 : Module.End K V0) ⟨v, hv⟩) : V0) : V) =
          (((R0 : Module.End K V0) (w0 ⟨v, hv⟩) : V0) : V) := by
        simpa [Module.End.mul_apply, hwU_val] using congrArg Subtype.val hc
      have hwv : (w : Module.End K V) v = (w0 ⟨v, hv⟩ : V) := rfl
      rw [hwv, htEnd_on (w0 ⟨v, hv⟩), htEnd_on ⟨v, hv⟩]
      show (((R0 : Module.End K V0) (w0 ⟨v, hv⟩)) : V) =
        (w : Module.End K V) (((R0 : Module.End K V0) ⟨v, hv⟩) : V)
      rw [show (w : Module.End K V) (((R0 : Module.End K V0) ⟨v, hv⟩) : V) =
        ((w0 ((R0 : Module.End K V0) ⟨v, hv⟩)) : V) from rfl]
      exact hc'.symm
    · rw [htEnd_off b hb hb0 ((w : Module.End K V) v)
        (apply_mem_primaryComponent hwT hv), htEnd_off b hb hb0 v hv]

private theorem ggK1As_isSolvable_GL_two {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (V0 : Type) [AddCommGroup V0] [Module K V0]
    [FiniteDimensional K V0] (hV0 : Module.finrank K V0 = 2) :
    Group.IsSolvable (Module.End K V0)ˣ := by
  obtain ⟨eP⟩ := ggK1As_glEquivPerm hK
  let b : Module.Basis (Fin 2) K V0 := (Module.finBasis K V0).reindex (finCongr hV0)
  let eA : Module.End K V0 ≃ₐ[K] Matrix (Fin 2) (Fin 2) K := LinearMap.toMatrixAlgEquiv b
  let eGL : (Module.End K V0)ˣ ≃* GL (Fin 2) K := Units.mapEquiv eA.toMulEquiv
  haveI : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by norm_num)
  exact Group.isSolvable_of_surjective
    (f := eGL.symm.toMonoidHom.comp eP.symm.toMonoidHom)
    ((eGL.symm.surjective).comp eP.symm.surjective)

private theorem ggK1As_perfect_subgroup_trivial {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) (V0 : Type) [AddCommGroup V0] [Module K V0]
    [FiniteDimensional K V0] (hV0 : Module.finrank K V0 = 2)
    (H : Subgroup (Module.End K V0)ˣ) (hH : Group.IsPerfect ↥H) : H = ⊥ := by
  haveI : Group.IsSolvable (Module.End K V0)ˣ := ggK1As_isSolvable_GL_two hK V0 hV0
  haveI : Group.IsPerfect ↥H := hH
  by_contra hne
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  exact Group.IsPerfect.not_isSolvable ↥H inferInstance

private theorem ggK1As_component_trivial_on_V0 {K : Type} [Field K] [Finite K] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {T : LinearMap.GeneralLinearGroup K V}
    (hK : Nat.card K = 2)
    (hV0K : Module.finrank K
      (primaryComponent (T : Module.End K V) ((Polynomial.X : K[X]) - 1)) = 2)
    {J : Subgroup (LinearMap.GeneralLinearGroup K V)}
    (hJ : CFSG.Assembly.IsQuasisimple ↥J)
    (hJle : J ≤ Subgroup.centralizer ({T} : Set (LinearMap.GeneralLinearGroup K V))) :
    ∀ j ∈ J, ∀ v ∈ primaryComponent (T : Module.End K V) ((Polynomial.X : K[X]) - 1),
      (j : Module.End K V) v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [Fintype.card_eq_nat_card, hK]; norm_num)
  let xE : K[X] := (Polynomial.X : K[X]) - 1
  let V0 : Submodule K V := primaryComponent (T : Module.End K V) xE
  let res : ↥J →* (Module.End K V0)ˣ :=
    { toFun := fun j =>
        let jc : Commute (j.1 : Module.End K V) (T : Module.End K V) := by
          have h := Subgroup.mem_centralizer_singleton_iff.mp (hJle j.2)
          show (j.1 : Module.End K V) * (T : Module.End K V) =
            (T : Module.End K V) * (j.1 : Module.End K V)
          simpa using congrArg (fun u : LinearMap.GeneralLinearGroup K V =>
            (u : Module.End K V)) h
        let rj : V0 →ₗ[K] V0 := (j.1 : Module.End K V).restrict (p := V0) (q := V0)
          (fun v hv => apply_mem_primaryComponent jc hv)
        let jic : Commute ((j.1⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
            (T : Module.End K V) := by
          have h := Commute.units_inv_left jc
          exact h
        let rji : V0 →ₗ[K] V0 :=
          ((j.1⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V).restrict (p := V0) (q := V0)
            (fun v hv => apply_mem_primaryComponent jic hv)
        Units.mkOfMulEqOne rj rji (by
          ext v
          show (j.1 : Module.End K V) (((j.1⁻¹ : LinearMap.GeneralLinearGroup K V) :
            Module.End K V) (v : V)) = (v : V)
          rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
          rfl)
      map_one' := Units.ext (LinearMap.ext fun v => rfl)
      map_mul' := fun a b => Units.ext (LinearMap.ext fun v => rfl) }
  haveI : Group.IsPerfect ↥J := Group.IsPerfect.mk hJ.1
  have hrange : res.range = ⊥ := by
    haveI : Group.IsPerfect ↥res.range := Group.IsPerfect.range (f := res)
    exact ggK1As_perfect_subgroup_trivial hK V0 hV0K res.range inferInstance
  intro j hj v hv
  have hres : res ⟨j, hj⟩ = 1 := by
    have hmem : res ⟨j, hj⟩ ∈ res.range := ⟨⟨j, hj⟩, rfl⟩
    rw [hrange] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h1 : ((res ⟨j, hj⟩ : (Module.End K V0)ˣ) : Module.End K V0) = 1 := by rw [hres]; rfl
  have h2 := congrArg (fun w : V0 => (w : V))
    (congrArg (fun f : Module.End K V0 => f ⟨v, hv⟩) h1)
  simpa [res, LinearMap.restrict_apply] using h2

private theorem ggK1As_commute_units_coe {M : Type*} [Monoid M] {u v : Mˣ}
    (h : Commute u v) : Commute (u : M) (v : M) := by
  have h' : u * v = v * u := h
  show (u : M) * (v : M) = (v : M) * (u : M)
  exact congrArg (fun x : Mˣ => (x : M)) h'

private theorem ggK1As_commute_units_of_coe {M : Type*} [Monoid M] {u v : Mˣ}
    (h : Commute (u : M) (v : M)) : Commute u v := by
  have h' : (u : M) * (v : M) = (v : M) * (u : M) := h
  show u * v = v * u
  exact Units.ext h'

private theorem ggK1As_commute_map {M N : Type*} [Monoid M] [Monoid N] (e : M ≃* N)
    {a b : M} (h : Commute a b) : Commute (e a) (e b) := by
  have h' : a * b = b * a := h
  show e a * e b = e b * e a
  rw [← map_mul, ← map_mul, h']

theorem ggK1A_sigma_two_lin {N : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 1)
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ 3 = 1) {m : List ℕ}
    (hm : GGK1AMultOf 3 1 N false K (xhat : GL (Fin N) K) m) :
    GGKacSigmaClause 3
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (Set.univ : Set (GL (Fin N) K)))
      (ggMultDatumA 3 1 (ggMultOrd 3 1) false m) (LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      (MonoidHom.id _) (MulAut.conj (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat)) := by
  intro o ho hqs A hxA hA hAI
  have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
  let T : LinearMap.GeneralLinearGroup K (Fin N → K) := Matrix.GeneralLinearGroup.toLin xhat.1
  have hT3 : T ^ 3 = 1 := by
    have h : (ggK1As_eG hK2 xhat) ^ 3 = 1 := by rw [← map_pow, hxp, map_one]
    simpa [T, ggK1As_eG] using h
  have hd : ggMultOrd 3 1 = 2 := by decide
  rw [hd] at ho
  have hm0 : m.headD 0 = 2 := ggK1As_datumA_head_eq_two ho hqs
  have hV0K : Module.finrank K
      (primaryComponent (T : Module.End K (Fin N → K)) ((Polynomial.X : K[X]) - 1)) = 2 := by
    have h1 := hm.head_eq
    have h2 : m.getD 0 0 = 2 := by
      cases m with
      | nil => simp [List.headD] at hm0
      | cons a t => simpa [List.headD] using hm0
    rw [h2] at h1
    exact h1.symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by
    rw [Fintype.card_eq_nat_card, hK2]; norm_num)
  have hsqT := ggK1As_squarefree_minpoly_of_pow_three hK2 hT3
  obtain ⟨t, ht3, htne, htT, ht_off, ht_nondec, htcomm⟩ :=
    ggK1As_three_witness (K := K) (V := Fin N → K) (T := T) hK2 hT3 hV0K
  let xR : LargeEvenProj (LargeEvenSLGroup (Fin N) K) :=
    LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat
  let tSL : ↥(LargeEvenSLGroup (Fin N) K) := (ggK1As_eG hK2).symm t
  let tR : LargeEvenProj (LargeEvenSLGroup (Fin N) K) :=
    LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) tSL
  have he_tR : ggK1As_e hK2 tR = t := by
    rw [ggK1As_e_projMk hK2 tSL, MulEquiv.apply_symm_apply]
  have he_xR : ggK1As_e hK2 xR = T := by
    show ggK1As_e hK2 (LargeEvenProjMk _ xhat) = T
    rw [ggK1As_e_projMk hK2 xhat]
    rfl
  have htR3 : tR ^ 3 = 1 := by
    have h1 : tSL ^ 3 = 1 := by
      apply (ggK1As_eG hK2).injective
      rw [map_pow, map_one, MulEquiv.apply_symm_apply, ht3]
    show tR ^ 3 = 1
    rw [show tR = LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) tSL from rfl, ← map_pow, h1,
      map_one]
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenSLGroup (Fin N) K)) = ⊥ :=
    ggK1As_centre_bot hK2
  have hconj_inj := ggK1As_conj_injective hZ
  have hT_on : ∀ v ∈ primaryComponent (T : Module.End K (Fin N → K))
      ((Polynomial.X : K[X]) - 1), (T : Module.End K (Fin N → K)) v = v := by
    intro v hv
    have h := mem_primaryComponent.mp hv
    have h' : (T : Module.End K (Fin N → K)) v - v = 0 := by simpa using h
    exact sub_eq_zero.mp h'
  have hmain : ∀ a ∈ A, a tR = tR := by
    intro a ha
    obtain ⟨φ, hφI, hφa⟩ := hAI a ha
    obtain ⟨s, hs⟩ := ggK1As_conjImage_inner hK2 φ hφI
    have haeq : a = MulAut.conj s := by
      ext l
      have hφa' : φ l = a l := by simpa using hφa l
      rw [← hφa', hs]
    have hs_mem : s ∈ A.comap (MulAut.conj : LargeEvenProj (LargeEvenSLGroup (Fin N) K) →*
        MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))) := by
      rw [Subgroup.mem_comap, ← haeq]
      exact ha
    have hs3 : s ^ 3 = 1 := by
      have h1 : (MulAut.conj s) ^ 3 = 1 := by rw [← haeq]; exact hA.2 a ha
      have h2 : MulAut.conj (s ^ 3) = 1 := by rw [map_pow, h1]
      exact hconj_inj (by rw [h2, map_one])
    have hsx : s * xR = xR * s := by
      have hxmem : MulAut.conj xR ∈ A := hxA
      have hcomm := hA.1.is_comm.comm ⟨MulAut.conj s, hs_mem⟩ ⟨MulAut.conj xR, hxmem⟩
      have h1 : (⟨MulAut.conj s, hs_mem⟩ : ↥A) * ⟨MulAut.conj xR, hxmem⟩ =
          ⟨MulAut.conj xR, hxmem⟩ * ⟨MulAut.conj s, hs_mem⟩ := hcomm
      have h2 : MulAut.conj s * MulAut.conj xR = MulAut.conj xR * MulAut.conj s :=
        congrArg Subtype.val h1
      rw [← map_mul, ← map_mul] at h2
      exact hconj_inj h2
    let w : LinearMap.GeneralLinearGroup K (Fin N → K) := ggK1As_e hK2 s
    have hw3 : w ^ 3 = 1 := by rw [show w = ggK1As_e hK2 s from rfl, ← map_pow, hs3, map_one]
    have hwT : Commute (w : Module.End K (Fin N → K)) (T : Module.End K (Fin N → K)) := by
      have h2 : (ggK1As_e hK2) s * (ggK1As_e hK2) xR =
          (ggK1As_e hK2) xR * (ggK1As_e hK2) s := by
        rw [← map_mul, ← map_mul, hsx]
      have hu : Commute ((ggK1As_e hK2) s) ((ggK1As_e hK2) xR) := h2
      have huT : Commute ((ggK1As_e hK2) s) T := by simpa [he_xR] using hu
      have := ggK1As_commute_units_coe huT
      simpa [w] using this
    have hcomm_gl := htcomm w hwT hw3
    have hcommR : tR * s = s * tR := by
      apply (ggK1As_e hK2).injective
      rw [map_mul, map_mul, he_tR]
      have h' : (t : Module.End K (Fin N → K)) * (w : Module.End K (Fin N → K)) =
          (w : Module.End K (Fin N → K)) * (t : Module.End K (Fin N → K)) := hcomm_gl
      exact Units.ext (by simpa [w] using h')
    rw [haeq, MulAut.conj_apply]
    rw [show s * tR = tR * s from hcommR.symm]
    group
  have hcomp : ∀ J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) K)),
      CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj xR)) →
      ∀ j ∈ J, tR * j = j * tR := by
    intro J hJ j hj
    let J' : Subgroup (LinearMap.GeneralLinearGroup K (Fin N → K)) :=
      J.map (ggK1As_e hK2).toMonoidHom
    have hJ'q : CFSG.Assembly.IsQuasisimple ↥J' := by
      have eJ : ↥J ≃* ↥J' := Subgroup.equivMapOfInjective J (ggK1As_e hK2).toMonoidHom
        (ggK1As_e hK2).injective
      exact (CFSG.Assembly.IsQuasisimple.congr eJ).mp hJ.2.2
    have hJ'le : J' ≤ Subgroup.centralizer ({T} : Set (LinearMap.GeneralLinearGroup K (Fin N → K)))
        := by
      intro j' hj'
      obtain ⟨j0, hj0, hj0eq⟩ := Subgroup.mem_map.mp hj'
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : j0 ∈ ggFixSub (MulAut.conj xR) := hJ.1 hj0
      rw [mem_ggFixSub] at hfix
      have hxcomm : xR * j0 = j0 * xR := by
        rw [MulAut.conj_apply] at hfix
        calc xR * j0 = (xR * j0 * xR⁻¹) * xR := by group
          _ = j0 * xR := by rw [hfix]
      have h1 := congrArg (ggK1As_e hK2) hxcomm
      rw [map_mul, map_mul, he_xR] at h1
      rw [← hj0eq]
      exact h1.symm
    have htriv := ggK1As_component_trivial_on_V0 hK2 hV0K hJ'q hJ'le
    have hj' : ggK1As_e hK2 j ∈ J' := Subgroup.mem_map_of_mem _ hj
    have huT : Commute ((ggK1As_e hK2) j) T :=
      Subgroup.mem_centralizer_singleton_iff.mp (hJ'le hj')
    have hj'T : Commute ((ggK1As_e hK2 j) : Module.End K (Fin N → K))
        (T : Module.End K (Fin N → K)) := ggK1As_commute_units_coe huT
    have hEqEnd : (t : Module.End K (Fin N → K)) * ((ggK1As_e hK2) j) =
        ((ggK1As_e hK2) j) * (t : Module.End K (Fin N → K)) := by
      apply ext_primaryComponent hsqT
      intro b hb v hv
      show (t : Module.End K (Fin N → K)) ((ggK1As_e hK2 j : Module.End K (Fin N → K)) v) =
        (ggK1As_e hK2 j : Module.End K (Fin N → K)) ((t : Module.End K (Fin N → K)) v)
      by_cases hb0 : b = ((Polynomial.X : K[X]) - 1)
      · subst hb0
        have hfix : (ggK1As_e hK2 j : Module.End K (Fin N → K)) v = v :=
          htriv (ggK1As_e hK2 j) hj' v hv
        rw [hfix]
        have hfix2 : (ggK1As_e hK2 j : Module.End K (Fin N → K)) ((t : Module.End K (Fin N → K)) v)
            =
            (t : Module.End K (Fin N → K)) v :=
          htriv (ggK1As_e hK2 j) hj' _ (apply_mem_primaryComponent htT hv)
        rw [hfix2]
      · rw [ht_off b hb hb0 v hv]
        exact (ht_off b hb hb0 ((ggK1As_e hK2 j : Module.End K (Fin N → K)) v)
          (apply_mem_primaryComponent hj'T hv))
    have hu : Commute t ((ggK1As_e hK2) j) := ggK1As_commute_units_of_coe hEqEnd
    have hcommR := ggK1As_commute_map (ggK1As_e hK2).symm hu
    have htRs : (ggK1As_e hK2).symm t = tR := by
      rw [← he_tR, MulEquiv.symm_apply_apply]
    have h3 : tR * j = j * tR := by
      have hh : Commute ((ggK1As_e hK2).symm t) ((ggK1As_e hK2).symm ((ggK1As_e hK2) j)) := hcommR
      have hh2 : ((ggK1As_e hK2).symm t) * ((ggK1As_e hK2).symm ((ggK1As_e hK2) j)) =
          ((ggK1As_e hK2).symm ((ggK1As_e hK2) j)) * ((ggK1As_e hK2).symm t) := hh
      simpa [htRs, MulEquiv.symm_apply_apply] using hh2
    exact h3
  have htnot : (MulAut.conj tR : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) K))) ∉
      Subgroup.zpowers (MulAut.conj xR) := by
    intro hmem
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hk' : MulAut.conj (xR ^ k) = MulAut.conj tR := by
      rw [map_zpow]; exact hk
    have hEq : xR ^ k = tR := hconj_inj hk'
    obtain ⟨v, hv, hvt⟩ := ht_nondec
    have h1 : (t : Module.End K (Fin N → K)) v = v := by
      have h2 := congrArg (ggK1As_e hK2) hEq
      rw [map_zpow, he_xR, he_tR] at h2
      have hfixT : (T : Module.End K (Fin N → K)) v = v := hT_on v hv
      let H' : Subgroup (LinearMap.GeneralLinearGroup K (Fin N → K)) :=
        { carrier := {g | (g : Module.End K (Fin N → K)) v = v}
          one_mem' := rfl
          mul_mem' := by
            intro a b ha hb
            show ((a * b : LinearMap.GeneralLinearGroup K (Fin N → K)) :
              Module.End K (Fin N → K)) v = v
            rw [Units.val_mul, Module.End.mul_apply, hb, ha]
          inv_mem' := by
            intro a ha
            show ((a⁻¹ : LinearMap.GeneralLinearGroup K (Fin N → K)) :
              Module.End K (Fin N → K)) v = v
            have hh : ((a⁻¹ : LinearMap.GeneralLinearGroup K (Fin N → K)) :
                Module.End K (Fin N → K)) (((a : LinearMap.GeneralLinearGroup K (Fin N → K)) :
                Module.End K (Fin N → K)) v) = v := by
              rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
              rfl
            rw [ha] at hh
            exact hh }
      let Tk : LinearMap.GeneralLinearGroup K (Fin N → K) := T ^ k
      have hTk : ((Tk : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) v = v := by
        have hmem : (T ^ k) ∈ H' := Subgroup.zpow_mem H' hfixT k
        change (((T ^ k : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) v = v) at hmem
        simpa [Tk] using hmem
      have ht_eq : (t : Module.End K (Fin N → K)) =
          ((Tk : LinearMap.GeneralLinearGroup K (Fin N → K)) :
            Module.End K (Fin N → K)) := by
        have h3 : t = Tk := by simpa [Tk] using h2.symm
        exact congrArg (fun u : LinearMap.GeneralLinearGroup K (Fin N → K) =>
          (u : Module.End K (Fin N → K))) h3
      rw [ht_eq]
      exact hTk
    exact hvt h1
  exact ⟨tR, htR3, hmain, hcomp, htnot⟩

private theorem ggK1As_su_scalars_bot {N : ℕ} {K : Type} [Field K] (hK : Nat.card K = 2 ^ 2)
    (hN : ¬ 3 ∣ N) :
    (LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSUGroup (Fin N) K 2) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_subgroupOf] at hg
  obtain ⟨c, hc⟩ := hg
  have hn : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; exact absurd (dvd_zero 3) hN
    · exact h
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin N) c ∈ StatedSU N 2 K := by
    rw [hc]; exact g.2
  have hsc := (CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := 1) Nat.prime_two
    (by rw [hK]; norm_num) (n := N) hn c).mp hmem
  obtain ⟨hcN, hc3⟩ := hsc
  have hdvd1 : orderOf c ∣ N := orderOf_dvd_of_pow_eq_one hcN
  have hdvd2 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
  have hcop : Nat.Coprime N 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN).symm
  have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

private theorem ggK1As_su_projMk_injective {N : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ 2) (hN : ¬ 3 ∣ N) :
    Function.Injective (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hmem : g ∈ (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2)).ker :=
    MonoidHom.mem_ker.mpr hg
  rw [QuotientGroup.ker_mk', ggK1As_su_scalars_bot hK hN] at hmem
  exact Subgroup.mem_bot.mp hmem

private theorem ggK1As_su_group_centre_bot {N : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) (hN : ¬ 3 ∣ N) :
    Subgroup.center ↥(LargeEvenSUGroup (Fin N) K 2) = ⊥ := by
  rcases Nat.eq_zero_or_pos N with h0 | hNpos
  · subst h0
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subsingleton.elim (z : GL (Fin 0) K) 1)
  · have h : UnitaryFieldData 2 1 K := TableBU.unitaryFieldData_of_card (n := 1) hK (by norm_num)
    rw [eq_bot_iff]
    intro z hz
    have hcomm : ∀ g ∈ ClassicalGroups.UnitaryFlag.unitarySU 2 1 K N,
        (z : GL (Fin N) K) * g = g * (z : GL (Fin N) K) := by
      intro g hg
      have h1 := Subgroup.mem_center_iff.mp hz (⟨g, hg⟩ : ↥(LargeEvenSUGroup (Fin N) K 2))
      exact (congrArg Subtype.val h1).symm
    have hscal := TableBUE.mem_scalars_of_commute (n := 1) (d := N) (p := 3) h
      Nat.prime_three (by norm_num) hcomm
    rw [largeEvenScalars_def, MonoidHom.mem_range] at hscal
    obtain ⟨c, hc⟩ := hscal
    have hmem : Matrix.GeneralLinearGroup.scalar (Fin N) c ∈ StatedSU N 2 K := by
      rw [hc]; exact z.2
    obtain ⟨hcN, hc3⟩ :=
      (CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := 1) Nat.prime_two hK hNpos c).mp hmem
    have hdvd1 : orderOf c ∣ N := orderOf_dvd_of_pow_eq_one hcN
    have hdvd2 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
    have hcop : Nat.Coprime N 3 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN).symm
    have h1 : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
    have hc1 : c = 1 := orderOf_eq_one_iff.mp h1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hc, hc1, map_one]
    rfl

private theorem ggK1As_su_centre_bot {N : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) (hN : ¬ 3 ∣ N) :
    Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)) = ⊥ := by
  have hinj := ggK1As_su_projMk_injective hK hN
  have hZ := ggK1As_su_group_centre_bot (N := N) hK hN
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
    ((LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSUGroup (Fin N) K 2)) z
  have hgcent : g ∈ Subgroup.center ↥(LargeEvenSUGroup (Fin N) K 2) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hinj
    have h1 := Subgroup.mem_center_iff.mp hz
      (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) y)
    simpa only [map_mul] using h1
  rw [hZ] at hgcent
  have hg1 : g = 1 := Subgroup.mem_bot.mp hgcent
  rw [Subgroup.mem_bot, hg1, map_one]

private theorem ggK1As_su_conjImage_inner_three {N : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) (hN : ¬ 3 ∣ N) :
    ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2))
      (LargeEvenGUSet (Fin N) K 2), φ ^ 3 = 1 →
      ∃ s : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2), φ = MulAut.conj s := by
  intro φ hφ hφ3
  obtain ⟨xhat, -, hconj⟩ := ggK1A_uni_exists_lift (p := 3) (nf := 1) (N := N)
    Nat.prime_three (Or.inr (by norm_num)) hK (fun h => hN h.1) φ hφ hφ3
  exact ⟨LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat, hconj.symm⟩

private lemma ggK1As_ker_aeval_X_sub_C {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (a : K) :
    (Polynomial.aeval f (Polynomial.X - Polynomial.C a)).ker = f.eigenspace a := by
  simp only [Module.End.eigenspace, Module.End.genEigenspace_one, map_sub, Polynomial.aeval_X,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]

private lemma ggK1As_coprime_sub_C {K : Type} [Field K] {a b : K} (h : a ≠ b) :
    IsCoprime (Polynomial.X - Polynomial.C a : K[X]) (Polynomial.X - Polynomial.C b) :=
  Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.mpr h))

private lemma ggK1As_eigenspace_sup_eq_top {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : f ^ 3 = 1) {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    f.eigenspace 1 ⊔ f.eigenspace ζ ⊔ f.eigenspace (ζ ^ 2) = ⊤ := by
  have hfac : (Polynomial.X ^ 3 - 1 : K[X]) =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C ζ) *
        (Polynomial.X - Polynomial.C (ζ ^ 2)) := by
    have h := X_pow_sub_C_eq_prod hζ (α := (1 : K)) (a := (1 : K))
      (by norm_num) (by norm_num)
    simpa [Finset.prod_range_succ, map_one] using h
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by norm_num)
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => by
    have h23 := hζ.dvd_of_pow_eq_one 2 h
    norm_num at h23
  have hζne : ζ ≠ ζ ^ 2 := fun h => by
    have h2 : ζ ^ 2 = ζ ^ 1 := by rw [pow_one]; exact h.symm
    exact absurd (hζ.pow_inj (by norm_num) (by norm_num) h2) (by norm_num)
  have hc1 : IsCoprime (Polynomial.X - Polynomial.C 1) (Polynomial.X - Polynomial.C ζ) :=
    ggK1As_coprime_sub_C hζ1.symm
  have hc2 : IsCoprime (Polynomial.X - Polynomial.C 1) (Polynomial.X - Polynomial.C (ζ ^ 2)) :=
    ggK1As_coprime_sub_C (fun h => hζ2 h.symm)
  have hc3 : IsCoprime (Polynomial.X - Polynomial.C ζ) (Polynomial.X - Polynomial.C (ζ ^ 2)) :=
    ggK1As_coprime_sub_C hζne
  have hc12 : IsCoprime ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C ζ))
      (Polynomial.X - Polynomial.C (ζ ^ 2)) := hc2.mul_left hc3
  have hsup1 := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hc1
  have hsup2 := Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hc12
  rw [← ggK1As_ker_aeval_X_sub_C f 1, ← ggK1As_ker_aeval_X_sub_C f ζ,
    ← ggK1As_ker_aeval_X_sub_C f (ζ ^ 2), hsup1, hsup2]
  have hprod : ((Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C ζ)) *
      (Polynomial.X - Polynomial.C (ζ ^ 2)) = Polynomial.X ^ 3 - 1 := by
    rw [← hfac]
  rw [hprod]
  have hzero : Polynomial.aeval f (Polynomial.X ^ 3 - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hf, sub_self]
  rw [hzero, LinearMap.ker_zero]

private lemma ggK1As_iSup_eigenspace_eq_top {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : f ^ 3 = 1) {ζ : K} (hζ : IsPrimitiveRoot ζ 3) :
    (⨆ μ : K, f.eigenspace μ) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← ggK1As_eigenspace_sup_eq_top f hf hζ]
  exact sup_le (sup_le (le_iSup _ 1) (le_iSup _ ζ)) (le_iSup _ (ζ ^ 2))

private theorem ggK1As_det_eq_one_of_sq_eq_one {E : Type} [Field E] [CharP E 2] {x : E}
    (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
  have h1 : (x - 1) ^ 2 = 0 := by
    have e : (x - 1) ^ 2 = x ^ 2 + 1 := by
      calc (x - 1) ^ 2 = x ^ 2 - 2 * x + 1 := by ring
        _ = x ^ 2 - 0 * x + 1 := by rw [h2]
        _ = x ^ 2 + 1 := by ring
    rw [e, h, show (1 : E) + 1 = 0 by rw [show (1 : E) + 1 = 2 by norm_num, h2]]
  have hzero : x - 1 = 0 := by
    rw [pow_two] at h1
    exact mul_self_eq_zero.mp h1
  exact sub_eq_zero.mp hzero

private theorem ggK1As_swap_witness
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E} (hBsym : B.IsSymm)
    {n : ℕ} {b : Module.Basis (Fin n) E W}
    (hborth : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (θ : Fin n → E) (t : LinearMap.GeneralLinearGroup E W)
    (ht : ∀ i, (t : Module.End E W) (b i) = θ i • b i)
    {i₀ i₁ : Fin n} (hne : θ i₀ ≠ θ i₁) :
    ∃ a₀ ∈ sesqSpecialUnitaryGroup B, a₀ * t ≠ t * a₀ := by
  classical
  let σ : Equiv.Perm (Fin n) := Equiv.swap i₀ i₁
  let aEnd : Module.End E W := b.constr E (fun i => b (σ i))
  have ha_b : ∀ i, aEnd (b i) = b (σ i) := fun i => b.constr_basis E (fun i => b (σ i)) i
  have hperm : ∀ i j, B (aEnd (b i)) (aEnd (b j)) = B (b i) (b j) := by
    intro i j
    rw [ha_b i, ha_b j, hborth, hborth]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (fun h : σ i = σ j => hij (σ.injective h))]
  have hinv : aEnd * aEnd = 1 := by
    apply b.ext
    intro i
    rw [Module.End.mul_apply, ha_b i, ha_b (σ i), Module.End.one_apply]
    exact congrArg b (Equiv.swap_apply_self i₀ i₁ i)
  let a₀ : LinearMap.GeneralLinearGroup E W := ⟨aEnd, aEnd, hinv, hinv⟩
  have ha₀_coe : (a₀ : Module.End E W) = aEnd := rfl
  have ha₀U : a₀ ∈ sesqUnitaryGroup B := by
    rw [mem_sesqUnitaryGroup]
    intro x y
    rw [ha₀_coe]
    let Φ : W →ₛₗ[hE.bar] W →ₗ[E] E :=
      { toFun := fun v => (B (aEnd v)).comp aEnd
        map_add' := by
          intro x y
          ext w
          simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
        map_smul' := by
          intro c x
          ext w
          simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smulₛₗ, RingHom.id_apply] }
    have hmap : Φ = B := by
      apply b.ext
      intro i
      apply b.ext
      intro j
      exact hperm i j
    have h1 : Φ x = B x := DFunLike.congr_fun hmap x
    exact DFunLike.congr_fun h1 y
  have hdet : LinearMap.det aEnd = 1 := by
    have hsq : (LinearMap.det aEnd) ^ 2 = 1 := by
      have h := congrArg LinearMap.det hinv
      simpa only [map_mul, map_one, pow_two] using h
    haveI : CharP E 2 := hE.charP
    exact ggK1As_det_eq_one_of_sq_eq_one hsq
  have ha₀SU : a₀ ∈ sesqSpecialUnitaryGroup B := by
    rw [mem_sesqSpecialUnitaryGroup]
    exact ⟨ha₀U, by rw [ha₀_coe]; exact hdet⟩
  refine ⟨a₀, ha₀SU, ?_⟩
  intro hcomm
  have h := congrArg (fun u : LinearMap.GeneralLinearGroup E W =>
    (u : Module.End E W) (b i₀)) hcomm
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    ha₀_coe, ht, map_smul, ha_b, ht] at h
  have hσ0 : σ i₀ = i₁ := by simp [σ]
  rw [hσ0] at h
  have h0 : θ i₀ = θ i₁ := by
    have hsub : (θ i₀ - θ i₁) • b i₁ = 0 := by rw [sub_smul, h, sub_self]
    rcases smul_eq_zero.mp hsub with hh | hh
    · exact sub_eq_zero.mp hh
    · exact absurd hh (b.ne_zero i₁)
  exact hne h0

private theorem ggK1As_exists_primitiveRoot {E : Type} [Field E] (hE : UnitaryFieldData 2 1 E) :
    ∃ ω : E, IsPrimitiveRoot ω 3 := by
  haveI : Finite E := hE.finite
  haveI : Fintype E := Fintype.ofFinite E
  have hcard : Nat.card Eˣ = 3 := by rw [Nat.card_units, hE.card]; norm_num
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Eˣ)
  have hord : orderOf g = 3 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  refine ⟨(g : E), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff]
  rw [← hord]
  exact IsPrimitiveRoot.orderOf g

private lemma ggK1As_sesq_smul_smul {E W : Type} [Field E] [AddCommMonoid W] [Module E W]
    {σ : E →+* E} {B : W →ₛₗ[σ] W →ₗ[E] E} (c d : E) (v w : W) :
    B (c • v) (d • w) = (d * σ c) • B v w := by
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_smul]

private theorem ggK1As_uni_orthonormal_diag
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (hBsym : B.IsSymm) (hBsep : B.SeparatingLeft)
    (P : Subgroup (LinearMap.GeneralLinearGroup E W)) (hP : IsElemAbelian 3 P)
    (hPle : P ≤ sesqUnitaryGroup B) :
    ∃ b : Module.Basis (Fin (Module.finrank E W)) E W,
      (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧
      (∀ a ∈ P, ∀ i, ∃ μ : E, μ ^ 3 = 1 ∧ (a : Module.End E W) (b i) = μ • b i) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := hE.charP
  obtain ⟨ζ, hζ⟩ := ggK1As_exists_primitiveRoot hE
  let f : P → Module.End E W := fun a => ((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)
  have hf_pow : ∀ a : P, f a ^ 3 = 1 := by
    intro a
    show (((a : LinearMap.GeneralLinearGroup E W) : Module.End E W)) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, hP.2 a a.2, Units.val_one]
  have hmax : ∀ a : P, ⨆ μ : E, (f a).maxGenEigenspace μ = ⊤ := by
    intro a
    rw [eq_top_iff, ← ggK1As_iSup_eigenspace_eq_top (f a) (hf_pow a) hζ]
    exact iSup_le fun μ =>
      (Module.End.eigenspace_le_maxGenEigenspace (f := f a) (μ := μ)).trans (le_iSup _ μ)
  have hcommEnd : Pairwise fun i j : P => Commute (f i) (f j) := by
    intro i j hij
    show f i * f j = f j * f i
    have h : (i : LinearMap.GeneralLinearGroup E W) * j =
        (j : LinearMap.GeneralLinearGroup E W) * i :=
      congrArg Subtype.val (hP.1.is_comm.comm i j)
    simpa only [f, Units.val_mul] using
      congrArg (fun u : LinearMap.GeneralLinearGroup E W => (u : Module.End E W)) h
  have htop_max : ⨆ χ : P → E, ⨅ a, (f a).maxGenEigenspace (χ a) = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      f hcommEnd hmax
  have hind_max : iSupIndep fun χ : P → E => ⨅ a, (f a).maxGenEigenspace (χ a) :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f (fun i j φ => by
      rcases eq_or_ne i j with rfl | hij
      · exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) φ
      · exact Module.End.mapsTo_maxGenEigenspace_of_comm (hcommEnd hij).symm φ)
  have hsemisimple : ∀ a : P, (f a).IsSemisimple := by
    intro a
    have h3ne : (3 : E) ≠ 0 := by
      have h2 : (2 : E) = 0 := CharP.cast_eq_zero E 2
      have h31 : (3 : E) = 1 := by rw [show (3 : E) = 2 + 1 by norm_num, h2, zero_add]
      rw [h31]; exact one_ne_zero
    have hsep : (Polynomial.X ^ 3 - Polynomial.C (1 : E) : Polynomial E).Separable :=
      Polynomial.separable_X_pow_sub_C (1 : E) h3ne one_ne_zero
    have hsq : Squarefree (Polynomial.X ^ 3 - 1 : Polynomial E) := by simpa using hsep.squarefree
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hf_pow a, sub_self]
  have hmge : ∀ (a : P) (μ : E), (f a).maxGenEigenspace μ = (f a).eigenspace μ :=
    fun a μ => (hsemisimple a).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ
  have htop : (⨆ χ : P → E, ⨅ a, (f a).eigenspace (χ a)) = ⊤ := by
    have h := htop_max; simp_rw [hmge] at h; exact h
  have hind : iSupIndep fun χ : P → E => ⨅ a, (f a).eigenspace (χ a) := by
    have h := hind_max; simp_rw [hmge] at h; exact h
  let joint : (P → E) → Submodule E W := fun χ => ⨅ a, (f a).eigenspace (χ a)
  have hdecomp : DirectSum.IsInternal joint :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have htop' : (⨆ χ : P → E, joint χ) = ⊤ := by simpa only [joint] using htop
  have hmem_joint : ∀ {χ : P → E} {v : W}, v ∈ joint χ → ∀ a : P, (f a) v = χ a • v := by
    intro χ v hv a
    exact Module.End.mem_eigenspace_iff.mp
      ((Submodule.mem_iInf (fun b : P => (f b).eigenspace (χ b))).mp hv a)
  have hroot : ∀ {χ : P → E} {v : W}, v ≠ 0 → v ∈ joint χ → ∀ a : P, (χ a) ^ 3 = 1 := by
    intro χ v hv0 hv a
    have hev := hmem_joint hv a
    have hpow : ((f a) ^ 3) v = (χ a) ^ 3 • v := by
      have h : ∀ n : ℕ, ((f a) ^ n) v = (χ a) ^ n • v := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [pow_succ, Module.End.mul_apply, hev, map_smul, ih, smul_smul, pow_succ']
      exact h 3
    rw [hf_pow a, Module.End.one_apply] at hpow
    have hz : ((χ a) ^ 3 - 1) • v = 0 := by rw [sub_smul, one_smul, ← hpow, sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv0
  have horth : ∀ χ χ' : P → E, χ ≠ χ' → ∀ v ∈ joint χ, ∀ w ∈ joint χ', B v w = 0 := by
    intro χ χ' hne v hv w hw
    by_cases hv0 : v = 0
    · rw [hv0, map_zero, LinearMap.zero_apply]
    by_cases hw0 : w = 0
    · rw [hw0, map_zero]
    obtain ⟨a, ha⟩ : ∃ a : P, χ a ≠ χ' a := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hB : B ((f a) v) ((f a) w) = B v w :=
      (mem_sesqUnitaryGroup.mp (hPle a.2)) v w
    have hv' : (f a) v = χ a • v := hmem_joint hv a
    have hw' : (f a) w = χ' a • w := hmem_joint hw a
    have hc3 : (χ a) ^ 3 = 1 := hroot hv0 hv a
    have hc : χ' a * hE.bar (χ a) ≠ 1 := by
      have hbar2 : hE.bar (χ a) = (χ a) ^ 2 := by rw [hE.bar_apply]; norm_num
      intro h1
      rw [hbar2] at h1
      rw [mul_comm] at h1
      have hc0 : χ a ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by norm_num)] at hc3
        exact one_ne_zero hc3.symm
      have hcc : (χ a) ^ 2 * (χ a) = 1 := by
        have h := hc3
        rw [show (χ a) ^ 3 = (χ a) ^ 2 * (χ a) by rw [pow_succ]] at h
        exact h
      have h3 : (χ a) ^ 2 * χ' a = (χ a) ^ 2 * χ a := by rw [h1, hcc]
      exact ha (mul_left_cancel₀ (pow_ne_zero 2 hc0) h3).symm
    have hB' : (χ' a * hE.bar (χ a)) * B v w = B v w := by
      have h := hB
      rw [hv', hw'] at h
      rw [ggK1As_sesq_smul_smul] at h
      simpa only [smul_eq_mul] using h
    have hzero : ((χ' a * hE.bar (χ a)) - 1) * B v w = 0 := by
      rw [sub_mul, one_mul, hB', sub_self]
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd (sub_eq_zero.mp h) hc
    · exact h
  have hnondeg : ∀ χ : P → E, ∀ v ∈ joint χ, (∀ w ∈ joint χ, B v w = 0) → v = 0 := by
    intro χ v hv hvorth
    apply hBsep v
    intro w
    have hw : w ∈ (⨆ χ' : P → E, joint χ') := by rw [htop']; trivial
    refine Submodule.iSup_induction (motive := fun z => B v z = 0) joint hw ?_ ?_ ?_
    · intro χ' w' hw'
      by_cases hχ : χ' = χ
      · subst hχ; exact hvorth w' hw'
      · exact horth χ χ' (Ne.symm hχ) v hv w' hw'
    · rw [map_zero]
    · intro x y hx hy
      rw [map_add, hx, hy, add_zero]
  have horthbasis : ∀ χ : P → E,
      ∃ e : Module.Basis (Fin (Module.finrank E (joint χ))) E (joint χ),
        ∀ i j, B (e i : W) (e j : W) = if i = j then 1 else 0 := by
    intro χ
    let Bχ : (joint χ) →ₛₗ[hE.bar] (joint χ) →ₗ[E] E :=
      { toFun := fun x => (B (x : W)).comp (joint χ).subtype
        map_add' := by
          intro x y
          ext w
          simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_add, map_add]
        map_smul' := by
          intro c x
          ext w
          simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_smul, map_smulₛₗ] }
    have hBχsym : Bχ.IsSymm :=
      LinearMap.IsSymm.mk fun x y => hBsym.eq (x : W) (y : W)
    have hBχsep : Bχ.SeparatingLeft := fun x hx =>
      Subtype.ext (hnondeg χ x x.2 fun w hw => hx ⟨w, hw⟩)
    obtain ⟨e, he⟩ := hE.exists_orthonormal_basis (B := Bχ) hBχsym hBχsep
    refine ⟨e, fun i j => ?_⟩
    have h := he i j
    change B (e i : W) (e j : W) = (if i = j then 1 else 0) at h
    exact h
  choose e he using horthbasis
  let b' : Module.Basis (Σ χ : P → E, Fin (Module.finrank E (joint χ))) E W :=
    hdecomp.collectedBasis e
  letI : Fintype (Σ χ : P → E, Fin (Module.finrank E (joint χ))) :=
    FiniteDimensional.fintypeBasisIndex b'
  have hcard : Fintype.card (Σ χ : P → E, Fin (Module.finrank E (joint χ))) =
      Fintype.card (Fin (Module.finrank E W)) := by
    have h1 : Fintype.card (Σ χ : P → E, Fin (Module.finrank E (joint χ))) =
        Module.finrank E W := (Module.finrank_eq_card_basis b').symm
    rw [h1, Fintype.card_fin]
  let ee : (Σ χ : P → E, Fin (Module.finrank E (joint χ))) ≃ Fin (Module.finrank E W) :=
    Fintype.equivOfCardEq hcard
  let b : Module.Basis (Fin (Module.finrank E W)) E W := b'.reindex ee
  have hb'orth : ∀ x y : (Σ χ : P → E, Fin (Module.finrank E (joint χ))),
      B (b' x) (b' y) = if x = y then 1 else 0 := by
    intro x y
    rw [DirectSum.IsInternal.collectedBasis_coe]
    obtain ⟨χ, i⟩ := x
    obtain ⟨χ', j⟩ := y
    by_cases hxy : χ = χ'
    · subst hxy
      by_cases h2 : i = j
      · subst h2; simp [he]
      · have hne : (⟨χ, i⟩ : Σ χ : P → E, Fin (Module.finrank E (joint χ))) ≠ ⟨χ, j⟩ :=
          fun h => h2 (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
        rw [if_neg hne]
        have h := he χ i j
        rwa [if_neg h2] at h
    · have hne : (⟨χ, i⟩ : Σ χ : P → E, Fin (Module.finrank E (joint χ))) ≠ ⟨χ', j⟩ :=
        fun h => hxy (Sigma.mk.inj_iff.mp h).1
      rw [if_neg hne]
      exact horth χ χ' hxy (e χ i) (e χ i).2 (e χ' j) (e χ' j).2
  refine ⟨b, ?_, ?_⟩
  · intro i j
    rw [show b i = b' (ee.symm i) from Module.Basis.reindex_apply b' ee i,
      show b j = b' (ee.symm j) from Module.Basis.reindex_apply b' ee j, hb'orth]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (fun h => hij (ee.symm.injective h))]
  · intro a ha i
    refine ⟨(ee.symm i).1 ⟨a, ha⟩, ?_, ?_⟩
    · have hmem : ((e (ee.symm i).1 (ee.symm i).2 : joint (ee.symm i).1) : W) ∈
          joint (ee.symm i).1 := (e (ee.symm i).1 (ee.symm i).2).2
      have hvne : ((e (ee.symm i).1 (ee.symm i).2 : joint (ee.symm i).1) : W) ≠ 0 :=
        fun h => (e (ee.symm i).1).ne_zero (ee.symm i).2 (Subtype.ext h)
      exact hroot hvne hmem ⟨a, ha⟩
    · have hmem : ((e (ee.symm i).1 (ee.symm i).2 : joint (ee.symm i).1) : W) ∈
          joint (ee.symm i).1 := (e (ee.symm i).1 (ee.symm i).2).2
      have := hmem_joint hmem ⟨a, ha⟩
      rw [show b i = b' (ee.symm i) from Module.Basis.reindex_apply b' ee i]
      rw [DirectSum.IsInternal.collectedBasis_coe]
      exact this

private theorem ggK1As_diag_unit
    {E W ι : Type} [Field E] [AddCommGroup W] [Module E W] [Fintype ι] [DecidableEq ι]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E} (hBsym : B.IsSymm)
    {b : Module.Basis ι E W} (hborth : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (θ : ι → E) (hθ0 : ∀ i, θ i ≠ 0) (hθ3 : ∀ i, θ i ^ 3 = 1)
    (hθprod : ∏ i, θ i = 1) :
    ∃ t : LinearMap.GeneralLinearGroup E W,
      t ∈ sesqSpecialUnitaryGroup B ∧ t ^ 3 = 1 ∧
      ∀ i, (t : Module.End E W) (b i) = θ i • b i := by
  classical
  let tEnd : Module.End E W := b.constr E (fun i => θ i • b i)
  let tInv : Module.End E W := b.constr E (fun i => (θ i)⁻¹ • b i)
  have htEnd_b : ∀ i, tEnd (b i) = θ i • b i :=
    fun i => b.constr_basis E (fun i => θ i • b i) i
  have htInv_b : ∀ i, tInv (b i) = (θ i)⁻¹ • b i :=
    fun i => b.constr_basis E (fun i => (θ i)⁻¹ • b i) i
  have hmul : tEnd * tInv = 1 := by
    apply b.ext
    intro i
    rw [Module.End.mul_apply, htInv_b i, map_smul, htEnd_b i, smul_smul,
      inv_mul_cancel₀ (hθ0 i), one_smul, Module.End.one_apply]
  have hmul' : tInv * tEnd = 1 := by
    apply b.ext
    intro i
    rw [Module.End.mul_apply, htEnd_b i, map_smul, htInv_b i, smul_smul,
      mul_inv_cancel₀ (hθ0 i), one_smul, Module.End.one_apply]
  let t : LinearMap.GeneralLinearGroup E W := ⟨tEnd, tInv, hmul, hmul'⟩
  have ht_coe : (t : Module.End E W) = tEnd := rfl
  have htb : ∀ i, (t : Module.End E W) (b i) = θ i • b i := by
    intro i; rw [ht_coe]; exact htEnd_b i
  have htEnd_pow : ∀ n i, (tEnd ^ n) (b i) = (θ i) ^ n • b i := by
    intro n
    induction n with
    | zero => intro i; simp
    | succ n ih =>
      intro i
      rw [pow_succ, Module.End.mul_apply, htEnd_b i, map_smul, ih i, smul_smul, pow_succ']
  have ht3 : t ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ht_coe, Units.val_one]
    apply b.ext
    intro i
    rw [htEnd_pow 3 i, hθ3 i, one_smul, Module.End.one_apply]
  have hbar : ∀ i, hE.bar (θ i) * θ i = 1 := by
    intro i
    have hb : hE.bar (θ i) = (θ i) ^ 2 := by rw [hE.bar_apply]; norm_num
    rw [hb, show (θ i) ^ 2 * θ i = (θ i) ^ 3 by rw [← pow_succ]]
    exact hθ3 i
  have hpair : ∀ i j, B (tEnd (b i)) (tEnd (b j)) = B (b i) (b j) := by
    intro i j
    rw [htEnd_b i, htEnd_b j, ggK1As_sesq_smul_smul, hborth i j]
    by_cases hij : i = j
    · subst hij
      have hbar' : θ i * hE.bar (θ i) = 1 := by rw [mul_comm]; exact hbar i
      rw [hbar', one_smul]
    · rw [if_neg hij, smul_zero]
  have hform : ∀ i, (B (tEnd (b i))).comp tEnd = B (b i) := by
    intro i
    apply b.ext
    intro j
    exact hpair i j
  have hisom : ∀ v w, B (tEnd v) (tEnd w) = B v w := by
    let Φ : W →ₛₗ[hE.bar] W →ₗ[E] E :=
      { toFun := fun v => (B (tEnd v)).comp tEnd
        map_add' := by
          intro x y
          ext w
          simp only [LinearMap.comp_apply, LinearMap.add_apply, map_add]
        map_smul' := by
          intro c x
          ext w
          simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smulₛₗ, RingHom.id_apply] }
    have hmap : Φ = B := by
      apply b.ext
      intro i
      exact hform i
    intro v w
    have h1 : Φ v = B v := DFunLike.congr_fun hmap v
    exact DFunLike.congr_fun h1 w
  have hmemU : t ∈ sesqUnitaryGroup B := by
    rw [mem_sesqUnitaryGroup]
    intro x y
    rw [ht_coe]
    exact hisom x y
  have hdet : LinearMap.det tEnd = 1 := by
    rw [← LinearMap.det_toMatrix b tEnd]
    have hmat : LinearMap.toMatrix b b tEnd = Matrix.diagonal θ := by
      ext i j
      rw [LinearMap.toMatrix_apply, htEnd_b j, map_smul, Finsupp.smul_apply, smul_eq_mul,
        Module.Basis.repr_self_apply]
      by_cases hij : i = j
      · subst hij; simp
      · have hji : ¬ j = i := fun h => hij h.symm
        simp [Matrix.diagonal, hij, hji]
    rw [hmat, Matrix.det_diagonal]
    exact hθprod
  have hmemSU : t ∈ sesqSpecialUnitaryGroup B := by
    rw [mem_sesqSpecialUnitaryGroup]
    exact ⟨hmemU, by rw [ht_coe]; exact hdet⟩
  exact ⟨t, hmemSU, ht3, htb⟩

private theorem ggK1As_uni_three_witness_extra
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E} (hBsym : B.IsSymm)
    (P : Subgroup (LinearMap.GeneralLinearGroup E W))
    {n : ℕ} (b : Module.Basis (Fin n) E W)
    (hborth : ∀ i j, B (b i) (b j) = if i = j then 1 else 0)
    (hbdiag : ∀ a ∈ P, ∀ i, ∃ μ : E, μ ^ 3 = 1 ∧
      (a : Module.End E W) (b i) = μ • b i)
    (θ : Fin n → E) (hθ0 : ∀ i, θ i ≠ 0) (hθ3 : ∀ i, θ i ^ 3 = 1)
    (hθprod : ∏ i, θ i = 1) (hθne : ∃ i j, θ i ≠ θ j) :
    ∃ t : LinearMap.GeneralLinearGroup E W,
      t ∈ sesqSpecialUnitaryGroup B ∧ t ^ 3 = 1 ∧
      (∀ p ∈ P, Commute p t) ∧
      ∃ a₀ ∈ sesqSpecialUnitaryGroup B, a₀ * t ≠ t * a₀ := by
  obtain ⟨t, htSU, ht3, htdiag⟩ := ggK1As_diag_unit hE hBsym hborth θ hθ0 hθ3 hθprod
  obtain ⟨i₀, i₁, hne⟩ := hθne
  obtain ⟨a₀, ha₀SU, ha₀ne⟩ := ggK1As_swap_witness hE hBsym hborth θ t htdiag hne
  refine ⟨t, htSU, ht3, ?_, a₀, ha₀SU, ha₀ne⟩
  intro p hp
  apply Units.ext
  apply b.ext
  intro i
  obtain ⟨μ, -, hμ⟩ := hbdiag p hp i
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply, htdiag i,
    map_smul, hμ, map_smul, htdiag i, smul_smul, smul_smul, mul_comm]

private theorem ggK1As_uni_three_witness
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (hBsym : B.IsSymm) (hBsep : B.SeparatingLeft)
    (P : Subgroup (LinearMap.GeneralLinearGroup E W)) (hP : IsElemAbelian 3 P)
    (hPle : P ≤ sesqUnitaryGroup B)
    (hm : Module.finrank E W = 2 ∨ Module.finrank E W = 3) :
    ∃ t : LinearMap.GeneralLinearGroup E W,
      t ∈ sesqSpecialUnitaryGroup B ∧ t ^ 3 = 1 ∧
      (∀ p ∈ P, Commute p t) ∧
      ∃ a₀ ∈ sesqSpecialUnitaryGroup B, a₀ * t ≠ t * a₀ := by
  classical
  obtain ⟨b, hborth, hbdiag⟩ := ggK1As_uni_orthonormal_diag hE hBsym hBsep P hP hPle
  generalize hfn : Module.finrank E W = n at b hborth hbdiag hm
  obtain ⟨ω, hω⟩ := ggK1As_exists_primitiveRoot hE
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω0 : ω ≠ 0 := hω.ne_zero (by norm_num)
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hωne : ω ≠ ω ^ 2 := by
    intro h
    have h2 : ω ^ 2 = ω ^ 1 := by rw [pow_one]; exact h.symm
    exact absurd (hω.pow_inj (by norm_num) (by norm_num) h2) (by norm_num)
  rcases hm with hn | hn
  · subst hn
    let θ : Fin 2 → E := ![ω, ω ^ 2]
    have hθ0 : ∀ i, θ i ≠ 0 := by
      intro i; fin_cases i <;> simp [θ, hω0, pow_ne_zero]
    have hθ3 : ∀ i, θ i ^ 3 = 1 := by
      intro i; fin_cases i
      · simp [θ, hω3]
      · change (![ω, ω ^ 2] : Fin 2 → E) 1 ^ 3 = 1
        rw [show (![ω, ω ^ 2] : Fin 2 → E) 1 = ω ^ 2 from rfl,
          ← pow_mul, show (2 : ℕ) * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
    have hθprod : ∏ i : Fin 2, θ i = 1 := by
      rw [Fin.prod_univ_two]
      simp only [θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [← pow_succ', show (2 : ℕ) + 1 = 3 by norm_num, hω3]
    have hθne : ∃ i j : Fin 2, θ i ≠ θ j :=
      ⟨0, 1, by simp only [θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]; exact
          hωne⟩
    exact ggK1As_uni_three_witness_extra hE hBsym P b hborth hbdiag θ hθ0 hθ3 hθprod hθne
  · subst hn
    let θ : Fin 3 → E := ![1, ω, ω ^ 2]
    have hθ0 : ∀ i, θ i ≠ 0 := by
      intro i; fin_cases i <;> simp [θ, hω0, pow_ne_zero]
    have hθ3 : ∀ i, θ i ^ 3 = 1 := by
      intro i; fin_cases i
      · simp [θ]
      · simp [θ, hω3]
      · change (![1, ω, ω ^ 2] : Fin 3 → E) 2 ^ 3 = 1
        rw [show (![1, ω, ω ^ 2] : Fin 3 → E) 2 = ω ^ 2 from rfl,
          ← pow_mul, show (2 : ℕ) * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
    have hθprod : ∏ i : Fin 3, θ i = 1 := by
      rw [Fin.prod_univ_three]
      simp only [θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      rw [one_mul, ← pow_succ', show (2 : ℕ) + 1 = 3 by norm_num, hω3]
    have hθne : ∃ i j : Fin 3, θ i ≠ θ j := by
      refine ⟨0, 1, ?_⟩
      simp only [θ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      exact fun h => hω1 h.symm
    exact ggK1As_uni_three_witness_extra hE hBsym P b hborth hbdiag θ hθ0 hθ3 hθprod hθne

private theorem ggK1As_card_primeFactors_two_three (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (2 ^ a * 3 ^ b).primeFactors.card ≤ 2 := by
  rw [Nat.primeFactors_mul (by positivity) (by positivity),
    Nat.primeFactors_prime_pow ha Nat.prime_two, Nat.primeFactors_prime_pow hb Nat.prime_three]
  exact (Finset.card_union_le _ _).trans (by simp)

private theorem ggK1As_sesqUnitary_solvable
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (hBsym : B.IsSymm) (hBsep : B.SeparatingLeft)
    (hm : Module.finrank E W = 2 ∨ Module.finrank E W = 3) :
    Group.IsSolvable ↥(sesqUnitaryGroup B) := by
  haveI : Finite ↥(sesqUnitaryGroup B) := by
    haveI : Finite E := hE.finite
    haveI : Finite W := Module.finite_of_finite E
    haveI : Finite (Module.End E W) :=
      Finite.of_injective _ (DFunLike.coe_injective (F := W →ₗ[E] W))
    exact Finite.of_injective
      (fun g : ↥(sesqUnitaryGroup B) => ((g : (Module.End E W)ˣ) : Module.End E W))
      (fun a b h => Subtype.ext (Units.ext h))
  obtain ⟨hcard, -⟩ := CFSG.LinearGroups.unitary_full_group_order hE hBsym hBsep
    (n := Module.finrank E W) rfl (by omega)
  rcases hm with hn | hn
  · rw [hn] at hcard
    have e : (↑(2 ^ 1) : ℤ) ^ (2 * (2 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 2, ((↑(2 ^ 1) : ℤ) ^ i - (-1) ^ i) = 18 := by
      norm_num [Finset.prod_Icc_succ_top]
    have h18 : Nat.card ↥(sesqUnitaryGroup B) = 18 := by
      exact_mod_cast hcard.trans e
    refine isSolvable_of_card_primeFactors_le_two ?_
    rw [h18]
    exact ggK1As_card_primeFactors_two_three 1 2 (by norm_num) (by norm_num)
  · rw [hn] at hcard
    have e : (↑(2 ^ 1) : ℤ) ^ (3 * (3 - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 3, ((↑(2 ^ 1) : ℤ) ^ i - (-1) ^ i) = 648 := by
      norm_num [Finset.prod_Icc_succ_top]
    have h648 : Nat.card ↥(sesqUnitaryGroup B) = 648 := by
      exact_mod_cast hcard.trans e
    refine isSolvable_of_card_primeFactors_le_two ?_
    rw [h648]
    exact ggK1As_card_primeFactors_two_three 3 4 (by norm_num) (by norm_num)

private theorem ggK1As_perfect_subgroup_sesqUnitary_trivial
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (hBsym : B.IsSymm) (hBsep : B.SeparatingLeft)
    (hm : Module.finrank E W = 2 ∨ Module.finrank E W = 3)
    (H : Subgroup ↥(sesqUnitaryGroup B)) (hH : Group.IsPerfect ↥H) : H = ⊥ := by
  haveI : Group.IsSolvable ↥(sesqUnitaryGroup B) := ggK1As_sesqUnitary_solvable hE hBsym hBsep hm
  haveI : Group.IsPerfect ↥H := hH
  by_contra hne
  haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hne
  exact Group.IsPerfect.not_isSolvable ↥H inferInstance

private noncomputable def ggK1As_su_projEquiv {N : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ 2) (hN : ¬ 3 ∣ N) :
    ↥(LargeEvenSUGroup (Fin N) K 2) ≃* LargeEvenProj (LargeEvenSUGroup (Fin N) K 2) :=
  MulEquiv.ofBijective (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2))
    ⟨ggK1As_su_projMk_injective hK hN, QuotientGroup.mk'_surjective _⟩

private theorem ggK1As_su_map_centralizer {N : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ 2) (hN : ¬ 3 ∣ N)
    (x : ↥(LargeEvenSUGroup (Fin N) K 2)) :
    (Subgroup.centralizer ({x} : Set ↥(LargeEvenSUGroup (Fin N) K 2))).map
        (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2)) =
      Subgroup.centralizer ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) x} : Set
        (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2))) := by
  have hb := ggK1As_su_projMk_injective hK hN
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := Subgroup.mem_centralizer_singleton_iff.mp hz
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    rw [← map_mul, ← map_mul, hz']
  · intro hy
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective
      ((LargeEvenScalars (Fin N) K).subgroupOf (LargeEvenSUGroup (Fin N) K 2)) y
    refine ⟨z, ?_, rfl⟩
    have hy' := Subgroup.mem_centralizer_singleton_iff.mp hy
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    apply hb
    rw [map_mul, map_mul]
    exact hy'

private noncomputable def ggK1As_su_centralizer_equiv {N : ℕ} {K : Type} [Field K]
    (hK : Nat.card K = 2 ^ 2) (hN : ¬ 3 ∣ N)
    (x : ↥(LargeEvenSUGroup (Fin N) K 2)) :
    ↥(Subgroup.centralizer ({x} : Set ↥(LargeEvenSUGroup (Fin N) K 2))) ≃*
      ↥(Subgroup.centralizer ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) x} : Set
        (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)))) :=
  (Subgroup.equivMapOfInjective _
    (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2))
    (ggK1As_su_projMk_injective hK hN)).trans
    (MulEquiv.subgroupCongr (ggK1As_su_map_centralizer hK hN x))

private noncomputable def ggK1As_restrictHom
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (V : Submodule E W) (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (hVcomm : ∀ g ∈ H,
      Set.MapsTo (g : Module.End E W) V V) :
    ↥H →*
      LinearMap.GeneralLinearGroup E V where
  toFun g :=
    { val := LinearMap.restrict (g.1 : Module.End E W) (hVcomm g.1 g.2)
      inv := LinearMap.restrict (((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W)
        (hVcomm _ (H.inv_mem g.2))
      val_inv := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        show (g.1 : Module.End E W) ((((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E
            W) (v : W)) =
          (v : W)
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]
        rfl
      inv_val := by
        apply LinearMap.ext
        intro v
        apply Subtype.ext
        show (((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W) ((g.1 : Module.End E
            W) (v : W)) =
          (v : W)
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
        rfl }
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show ((1 : LinearMap.GeneralLinearGroup E W) : Module.End E W) (v : W) = (v : W)
    rfl
  map_mul' := by
    intro a b
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show (a.1 : Module.End E W) ((b.1 : Module.End E W) (v : W)) =
      ((a.1 * b.1 : LinearMap.GeneralLinearGroup E W) : Module.End E W) (v : W)
    rw [Units.val_mul, Module.End.mul_apply]

private noncomputable def ggK1As_restrictForm {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) (B : W →ₛₗ[hE.bar] W →ₗ[E] E) (V : Submodule E W) :
    V →ₛₗ[hE.bar] V →ₗ[E] E :=
  { toFun := fun x => (B (x : W)).comp V.subtype
    map_add' := by
      intro x y
      ext w
      simp only [LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_add, map_add]
    map_smul' := by
      intro c x
      ext w
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_smul, map_smulₛₗ,
          RingHom.id_apply] }

private theorem ggK1As_restrictForm_apply {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) (B : W →ₛₗ[hE.bar] W →ₗ[E] E) (V : Submodule E W)
    (x y : V) : ggK1As_restrictForm hE B V x y = B (x : W) (y : W) := rfl

private theorem ggK1As_restrictHom_mem_unitary
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (V : Submodule E W) (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (hVcomm : ∀ g ∈ H,
      Set.MapsTo (g : Module.End E W) V V)
    (hU : ∀ g ∈ H,
      (g : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup B) :
    ∀ g, ggK1As_restrictHom V H hVcomm g ∈ sesqUnitaryGroup (ggK1As_restrictForm hE B V) := by
  intro g
  rw [mem_sesqUnitaryGroup]
  intro a b
  change B (((g.1 : LinearMap.GeneralLinearGroup E W) : Module.End E W) (a : W))
    (((g.1 : LinearMap.GeneralLinearGroup E W) : Module.End E W) (b : W)) = B (a : W) (b : W)
  exact (mem_sesqUnitaryGroup.mp (hU g g.2)) (a : W) (b : W)

private noncomputable def ggK1As_uniRho
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (V : Submodule E W) (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (hVcomm : ∀ g ∈ H,
      Set.MapsTo (g : Module.End E W) V V)
    (hU : ∀ g ∈ H,
      (g : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup B) :
    ↥H →*
      ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V)) :=
  (ggK1As_restrictHom V H hVcomm).codRestrict _
    (ggK1As_restrictHom_mem_unitary hE V H hVcomm hU)

private noncomputable def ggK1As_uniS
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (V : Submodule E W) (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (hVcomm : ∀ g ∈ H,
      Set.MapsTo (g : Module.End E W) V V)
    (hU : ∀ g ∈ H,
      (g : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup B) :
    Subgroup ↥H where
  carrier := {g | (∀ w : W, ((g.1 : Module.End E W) - 1) w ∈ V) ∧
    ((ggK1As_uniRho hE V H hVcomm hU g : ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V))) :
      LinearMap.GeneralLinearGroup E V) ∈ sesqSpecialUnitaryGroup (ggK1As_restrictForm hE B V)}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro w; simp
    · rw [map_one]; exact (sesqSpecialUnitaryGroup _).one_mem
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨?_, ?_⟩
    · intro w
      show ((a.1 : Module.End E W) * (b.1 : Module.End E W)) w - w ∈ V
      have h1 : ((b.1 : Module.End E W) - 1) w ∈ V := hb1 w
      have h2 : ((a.1 : Module.End E W) - 1) w ∈ V := ha1 w
      have h3 : (a.1 : Module.End E W) (((b.1 : Module.End E W) - 1) w) ∈ V :=
        hVcomm a.1 a.2 h1
      have hsum := V.add_mem h3 h2
      have heq : ((a.1 : Module.End E W) * (b.1 : Module.End E W)) w - w =
          (a.1 : Module.End E W) (((b.1 : Module.End E W) - 1) w) +
            ((a.1 : Module.End E W) w - w) := by
        simp only [Module.End.mul_apply, map_sub, LinearMap.sub_apply, Module.End.one_apply]
        abel
      rwa [heq]
    · rw [map_mul, Subgroup.coe_mul]
      exact (sesqSpecialUnitaryGroup _).mul_mem ha2 hb2
  inv_mem' := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ?_⟩
    · intro w
      show (((a.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W) w - w ∈ V
      have h1 : ((a.1 : Module.End E W) - 1) w ∈ V := ha1 w
      have h2 : (((a.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W)
          (((a.1 : Module.End E W) - 1) w) ∈ V :=
        hVcomm _ (H.inv_mem a.2) h1
      have hneg : -(((a.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W)
          (((a.1 : Module.End E W) - 1) w) ∈ V := V.neg_mem h2
      have hcancel : (((a.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W)
          ((a.1 : Module.End E W) w) = w := by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]; rfl
      have heq : (((a.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W) w - w =
          -(((a.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W)
            (((a.1 : Module.End E W) - 1) w) := by
        rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, hcancel]
        abel
      rwa [heq]
    · rw [map_inv, Subgroup.coe_inv]
      exact (sesqSpecialUnitaryGroup _).inv_mem ha2

private theorem ggK1As_sesqSpecial_mul_conj
    {E V : Type} [Field E] [AddCommGroup V] [Module E V] {σ : E →+* E}
    {B : V →ₛₗ[σ] V →ₗ[E] E} {a b : LinearMap.GeneralLinearGroup E V}
    (ha : a ∈ sesqUnitaryGroup B) (hb : b ∈ sesqSpecialUnitaryGroup B) :
    a * b * a⁻¹ ∈ sesqSpecialUnitaryGroup B := by
  rw [mem_sesqSpecialUnitaryGroup] at hb ⊢
  refine ⟨(sesqUnitaryGroup B).mul_mem ((sesqUnitaryGroup B).mul_mem ha hb.1)
    ((sesqUnitaryGroup B).inv_mem ha), ?_⟩
  have hbU : Units.map LinearMap.det b = 1 := Units.ext hb.2
  have h1 : Units.map LinearMap.det (a * b * a⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hbU, mul_one, mul_inv_cancel]
  exact congrArg Units.val h1

private theorem ggK1As_uniS_normal
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (V : Submodule E W) (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (hVcomm : ∀ g ∈ H,
      Set.MapsTo (g : Module.End E W) V V)
    (hU : ∀ g ∈ H,
      (g : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup B) :
    (ggK1As_uniS hE V H hVcomm hU).Normal :=
  Subgroup.Normal.mk fun n hn g => by
    obtain ⟨hn1, hn2⟩ := hn
    refine ⟨?_, ?_⟩
    · intro w
      show ((g.1 : Module.End E W) * (n.1 : Module.End E W) *
        ((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W)) w - w ∈ V
      have h1 : ((n.1 : Module.End E W) - 1)
          ((((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W) w) ∈ V := hn1 _
      have h2 : (g.1 : Module.End E W) (((n.1 : Module.End E W) - 1)
          ((((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W) w)) ∈ V :=
        hVcomm g.1 g.2 h1
      have hcancel : (g.1 : Module.End E W)
          ((((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W) w) = w := by
        rw [← Module.End.mul_apply, ← Units.val_mul, mul_inv_cancel]; rfl
      have heq : ((g.1 : Module.End E W) * (n.1 : Module.End E W) *
          ((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W)) w - w =
          (g.1 : Module.End E W) (((n.1 : Module.End E W) - 1)
            ((((g.1)⁻¹ : LinearMap.GeneralLinearGroup E W) : Module.End E W) w)) := by
        simp only [Module.End.mul_apply, map_sub, LinearMap.sub_apply, Module.End.one_apply,
          hcancel]
      rwa [heq]
    · have hcoe : ((ggK1As_uniRho hE V H hVcomm hU (g * n * g⁻¹) :
            ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V))) :
            LinearMap.GeneralLinearGroup E V) =
          ((ggK1As_uniRho hE V H hVcomm hU g :
            ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V))) :
            LinearMap.GeneralLinearGroup E V) *
          ((ggK1As_uniRho hE V H hVcomm hU n :
            ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V))) :
            LinearMap.GeneralLinearGroup E V) *
          (((ggK1As_uniRho hE V H hVcomm hU g :
            ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V))) :
            LinearMap.GeneralLinearGroup E V))⁻¹ := by
        rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcoe]
      exact ggK1As_sesqSpecial_mul_conj
        ((ggK1As_uniRho hE V H hVcomm hU g).2) hn2

private theorem ggK1As_compl_bot
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    {V : Submodule E W} {π : Module.End E W} (hπfix : ∀ v ∈ V, π v = v) :
    V ⊓ π.ker = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro z hz
  obtain ⟨hzV, hzker⟩ := Submodule.mem_inf.mp hz
  rw [LinearMap.mem_ker] at hzker
  exact (hπfix z hzV).symm.trans hzker

private theorem ggK1As_uniRho_eq_one_apply
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (V : Submodule E W) (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (hVcomm : ∀ g ∈ H,
      Set.MapsTo (g : Module.End E W) V V)
    (hU : ∀ g ∈ H,
      (g : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup B)
    {g : ↥H}
    (hg : ggK1As_uniRho hE V H hVcomm hU g = 1) :
    ∀ v ∈ V, (g.1 : Module.End E W) v = v := by
  intro v hv
  have h1 : (ggK1As_restrictHom V H hVcomm g : LinearMap.GeneralLinearGroup E V) = 1 := by
    have := congrArg (fun z : ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V)) =>
      (z : LinearMap.GeneralLinearGroup E V)) hg
    simpa only [ggK1As_uniRho, MonoidHom.codRestrict_apply, Subgroup.coe_one] using this
  have h2 : (ggK1As_restrictHom V H hVcomm g : Module.End E V) ⟨v, hv⟩ = ⟨v, hv⟩ := by
    have := congrArg (fun z : LinearMap.GeneralLinearGroup E V =>
      (z : Module.End E V) ⟨v, hv⟩) h1
    simpa using this
  have h3 : ((ggK1As_restrictHom V H hVcomm g : Module.End E V) ⟨v, hv⟩ : W) = v :=
    congrArg Subtype.val h2
  show (g.1 : Module.End E W) v = v
  exact h3

private theorem ggK1As_uniS_injective
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (V : Submodule E W) (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (π : Module.End E W)
    (hVcomm : ∀ g ∈ H,
      Set.MapsTo (g : Module.End E W) V V)
    (hU : ∀ g ∈ H,
      (g : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup B)
    (hπidem : π * π = π)
    (hπmem : ∀ w : W, π w ∈ V)
    (hπfix : ∀ v ∈ V, π v = v)
    (hπcomm : ∀ g ∈ H,
      Commute (g.1 : Module.End E W) π) :
    Function.Injective ((ggK1As_uniRho hE V H hVcomm hU).comp
      (ggK1As_uniS hE V H hVcomm hU).subtype) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨ha1, -⟩ := a.2
  have hfixV : ∀ v ∈ V, (a.1.1 : Module.End E W) v = v :=
    ggK1As_uniRho_eq_one_apply hE V H hVcomm hU (g := a.1) (by simpa using ha)
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  apply LinearMap.ext
  intro w
  have hπw : π w ∈ V := hπmem w
  have hπker : π (w - π w) = 0 := by
    have h := congrArg (fun f : Module.End E W => f w) hπidem
    simp only [Module.End.mul_apply] at h
    rw [map_sub, h, sub_self]
  have hfixπ : (a.1.1 : Module.End E W) (π w) = π w := hfixV _ hπw
  have hfixker : (a.1.1 : Module.End E W) (w - π w) = w - π w := by
    have hmem : (a.1.1 : Module.End E W) (w - π w) - (w - π w) ∈ V := ha1 (w - π w)
    have hker : (a.1.1 : Module.End E W) (w - π w) ∈ π.ker := by
      rw [LinearMap.mem_ker]
      have hc := (hπcomm a.1.1 a.1.2).eq
      rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply, hπker, map_zero]
    have hwk : w - π w ∈ π.ker := LinearMap.mem_ker.mpr hπker
    have hker' : (a.1.1 : Module.End E W) (w - π w) - (w - π w) ∈ π.ker :=
      Submodule.sub_mem _ hker hwk
    have hbot : (a.1.1 : Module.End E W) (w - π w) - (w - π w) ∈ (⊥ : Submodule E W) := by
      rw [← ggK1As_compl_bot hπfix]
      exact Submodule.mem_inf.mpr ⟨hmem, hker'⟩
    exact sub_eq_zero.mp ((Submodule.mem_bot E).mp hbot)
  change (a.1.1 : Module.End E W) w = w
  have hsplit : w = π w + (w - π w) := by abel
  conv_lhs => rw [hsplit]
  rw [map_add, hfixπ, hfixker]
  exact hsplit.symm

private theorem ggK1As_restrictForm_isSymm
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E} (hBsym : B.IsSymm)
    (V : Submodule E W) : (ggK1As_restrictForm hE B V).IsSymm :=
  LinearMap.IsSymm.mk fun x y => hBsym.eq (x : W) (y : W)

private theorem ggK1As_restrictForm_separating
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E} (hBsep : B.SeparatingLeft)
    (V : Submodule E W) (π : Module.End E W)
    (hπmem : ∀ w : W, π w ∈ V) (hπfix : ∀ v ∈ V, π v = v)
    (horth : ∀ w w' : W, B (π w) (w' - π w') = 0 ∧ B (w - π w) (π w') = 0) :
    (ggK1As_restrictForm hE B V).SeparatingLeft := by
  intro v hv
  apply Subtype.ext
  apply hBsep
  intro w
  have hsplit : w = π w + (w - π w) := by abel
  have h1 : B (v : W) (π w) = 0 := hv ⟨π w, hπmem w⟩
  have h2 : B (v : W) (w - π w) = 0 := by
    have := (horth (v : W) w).1
    rwa [hπfix (v : W) v.2] at this
  rw [hsplit, map_add, h1, h2, add_zero]

private theorem ggK1As_uniS_commute
    {E W : Type} [Field E] [AddCommGroup W] [Module E W]
    (H : Subgroup (LinearMap.GeneralLinearGroup E W)) (V : Submodule E W) (π : Module.End E W)
    (hπidem : π * π = π) (hπmem : ∀ w : W, π w ∈ V) (hπfix : ∀ v ∈ V, π v = v)
    (hπcomm : ∀ g ∈ H, Commute (g : Module.End E W) π)
    {a j : LinearMap.GeneralLinearGroup E W} (ha : a ∈ H) (hj : j ∈ H)
    (hatriv : ∀ w : W, ((a : Module.End E W) - 1) w ∈ V)
    (hjV : ∀ v ∈ V, (j : Module.End E W) v = v) :
    a * j = j * a := by
  apply Units.ext
  apply LinearMap.ext
  intro w
  rw [Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hv : π w ∈ V := hπmem w
  have hu : w - π w ∈ π.ker := by
    rw [LinearMap.mem_ker]
    have h := congrArg (fun f : Module.End E W => f w) hπidem
    simp only [Module.End.mul_apply] at h
    rw [map_sub, h, sub_self]
  have haw : (a : Module.End E W) (π w) ∈ V := by
    have hc := (hπcomm a ha).eq
    have h := congrArg (fun f : Module.End E W => f w) hc
    simp only [Module.End.mul_apply] at h
    rw [h]
    exact hπmem ((a : Module.End E W) w)
  have haker : ∀ u ∈ π.ker, (a : Module.End E W) u = u := by
    intro u hu'
    have hu'V : (a : Module.End E W) u - u ∈ V := by
      have := hatriv u
      rwa [LinearMap.sub_apply, Module.End.one_apply] at this
    have hu'ker : (a : Module.End E W) u ∈ π.ker := by
      rw [LinearMap.mem_ker]
      have hc := (hπcomm a ha).eq
      rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply, LinearMap.mem_ker.mp hu', map_zero]
    have hbot : (a : Module.End E W) u - u ∈ (⊥ : Submodule E W) := by
      rw [← ggK1As_compl_bot hπfix]
      exact Submodule.mem_inf.mpr ⟨hu'V, Submodule.sub_mem _ hu'ker hu'⟩
    exact sub_eq_zero.mp ((Submodule.mem_bot E).mp hbot)
  have hjker : (j : Module.End E W) (w - π w) ∈ π.ker := by
    rw [LinearMap.mem_ker]
    have hc := (hπcomm j hj).eq
    rw [← Module.End.mul_apply, ← hc, Module.End.mul_apply, LinearMap.mem_ker.mp hu, map_zero]
  have h1 : (a : Module.End E W) ((j : Module.End E W) w) =
      (a : Module.End E W) (π w) + (j : Module.End E W) (w - π w) := by
    have hjw : (j : Module.End E W) w = π w + (j : Module.End E W) (w - π w) := by
      conv_lhs => rw [show w = π w + (w - π w) by abel]
      rw [map_add, hjV (π w) hv]
    rw [hjw, map_add, haker _ hjker]
  have h2 : (j : Module.End E W) ((a : Module.End E W) w) =
      (a : Module.End E W) (π w) + (j : Module.End E W) (w - π w) := by
    have haw' : (a : Module.End E W) w = (a : Module.End E W) (π w) + (w - π w) := by
      conv_lhs => rw [show w = π w + (w - π w) by abel]
      rw [map_add, haker _ hu]
    rw [haw', map_add, hjV _ haw]
  rw [h1, h2]

private theorem ggK1As_perfect_fixes
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (V : Submodule E W) (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (hVcomm : ∀ g ∈ H, Set.MapsTo (g : Module.End E W) V V)
    (hU : ∀ g ∈ H, (g : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup B)
    (hsymV : (ggK1As_restrictForm hE B V).IsSymm)
    (hsepV : (ggK1As_restrictForm hE B V).SeparatingLeft)
    (hm : Module.finrank E V = 2 ∨ Module.finrank E V = 3)
    (J : Subgroup (LinearMap.GeneralLinearGroup E W)) (hJH : J ≤ H) (hJ : Group.IsPerfect ↥J) :
    ∀ j ∈ J, ∀ v ∈ V, (j : Module.End E W) v = v := by
  intro j hj v hv
  haveI : Group.IsPerfect ↥J := hJ
  let φ : ↥J →* ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V)) :=
    (ggK1As_uniRho hE V H hVcomm hU).comp (Subgroup.inclusion hJH)
  have hperf : Group.IsPerfect ↥φ.range := Group.IsPerfect.range (f := φ)
  have hbot : φ.range = ⊥ :=
    ggK1As_perfect_subgroup_sesqUnitary_trivial hE hsymV hsepV hm φ.range hperf
  have h1 : φ ⟨j, hj⟩ = 1 := by
    have hmem : φ ⟨j, hj⟩ ∈ φ.range := ⟨⟨j, hj⟩, rfl⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have h2 : ggK1As_uniRho hE V H hVcomm hU ⟨j, hJH hj⟩ = 1 := h1
  exact ggK1As_uniRho_eq_one_apply hE V H hVcomm hU (g := ⟨j, hJH hj⟩) h2 v hv

private theorem ggK1As_uni_abstract_data
    {E W : Type} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (hE : UnitaryFieldData 2 1 E) {B : W →ₛₗ[hE.bar] W →ₗ[E] E}
    (hBsym : B.IsSymm) (hBsep : B.SeparatingLeft)
    (H : Subgroup (LinearMap.GeneralLinearGroup E W))
    (V : Submodule E W) (π : Module.End E W)
    (hπidem : π * π = π) (hπmem : ∀ w : W, π w ∈ V) (hπfix : ∀ v ∈ V, π v = v)
    (horth : ∀ w w' : W, B (π w) (w' - π w') = 0 ∧ B (w - π w) (π w') = 0)
    (hHπ : ∀ g ∈ H, Commute (g : Module.End E W) π)
    (hHU : ∀ g ∈ H, (g : LinearMap.GeneralLinearGroup E W) ∈ sesqUnitaryGroup B)
    (hHlift : ∀ s ∈ sesqSpecialUnitaryGroup (ggK1As_restrictForm hE B V),
      ∃ g ∈ H, (∀ w : W, ((g : Module.End E W) - 1) w ∈ V) ∧
        ∀ v : V, (g : Module.End E W) (v : W) =
          (((s : LinearMap.GeneralLinearGroup E V) : Module.End E V) v : W))
    (hm : Module.finrank E V = 2 ∨ Module.finrank E V = 3) :
    ∃ (S : Subgroup ↥H) (_ : S.Normal) (F : Type) (_ : Group F) (ρ : ↥H →* F),
      Function.Injective (ρ.comp S.subtype) ∧
      (∀ J : Subgroup (LinearMap.GeneralLinearGroup E W), J ≤ H → Group.IsPerfect ↥J →
        ∀ j ∈ J, ∀ a ∈ S, (a : LinearMap.GeneralLinearGroup E W) * j =
          j * (a : LinearMap.GeneralLinearGroup E W)) ∧
      (∀ P : Subgroup F, IsElemAbelian 3 P →
        ∃ t : ↥H, t ∈ S ∧ t ^ 3 = 1 ∧ (∀ u ∈ P, u * ρ t = ρ t * u) ∧
          ∃ a₀ : ↥H, a₀ * t ≠ t * a₀) := by
  have hVcomm : ∀ g ∈ H, Set.MapsTo (g : Module.End E W) V V := by
    intro g hg v hv
    have hπv : π v = v := hπfix v hv
    have hc := (hHπ g hg).eq
    have hcomm := congrArg (fun f : Module.End E W => f v) hc
    simp only [Module.End.mul_apply] at hcomm
    rw [hπv] at hcomm
    rw [hcomm]
    exact hπmem ((g : Module.End E W) v)
  have hsymV : (ggK1As_restrictForm hE B V).IsSymm := ggK1As_restrictForm_isSymm hE hBsym V
  have hsepV : (ggK1As_restrictForm hE B V).SeparatingLeft :=
    ggK1As_restrictForm_separating hE hBsep V π hπmem hπfix horth
  let S : Subgroup ↥H := ggK1As_uniS hE V H hVcomm hHU
  have hSn : S.Normal := ggK1As_uniS_normal hE V H hVcomm hHU
  let F : Type := ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V))
  let ρ : ↥H →* F := ggK1As_uniRho hE V H hVcomm hHU
  have hinj : Function.Injective (ρ.comp S.subtype) :=
    ggK1As_uniS_injective hE V H π hVcomm hHU hπidem hπmem hπfix hHπ
  have hliftρ : ∀ {g : ↥H} {s : LinearMap.GeneralLinearGroup E V},
      (∀ v : V, (g.1 : Module.End E W) (v : W) = ((s : Module.End E V) v : W)) →
      ((ρ g : F) : LinearMap.GeneralLinearGroup E V) = s := by
    intro g s hs
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have h1 : ((ggK1As_restrictHom V H hVcomm g : Module.End E V) v : W) =
        (g.1 : Module.End E W) (v : W) := rfl
    change ((ggK1As_restrictHom V H hVcomm g : Module.End E V) v : W) = _
    rw [h1, hs v]
  refine ⟨S, hSn, F, inferInstance, ρ, hinj, ?_, ?_⟩
  · intro J hJH hJ j hj a ha
    have hjV := ggK1As_perfect_fixes hE V H hVcomm hHU hsymV hsepV hm J hJH hJ j hj
    exact ggK1As_uniS_commute H V π hπidem hπmem hπfix hHπ (a := a.1) (j := j)
      a.2 (hJH hj) ha.1 hjV
  · intro P hP
    let P' : Subgroup (LinearMap.GeneralLinearGroup E V) := P.map (Subgroup.subtype _)
    have hP'le : P' ≤ sesqUnitaryGroup (ggK1As_restrictForm hE B V) := by
      rintro x ⟨s, hs, rfl⟩
      exact s.2
    have hP' : IsElemAbelian 3 P' := by
      refine ⟨?_, ?_⟩
      · refine ⟨⟨fun x y => ?_⟩⟩
        obtain ⟨x', hx', hx'eq⟩ := Subgroup.mem_map.mp x.2
        obtain ⟨y', hy', hy'eq⟩ := Subgroup.mem_map.mp y.2
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx'eq, ← hy'eq]
        have h := congrArg (fun z : ↥P => ((z : ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V))) :
            LinearMap.GeneralLinearGroup E V)) (hP.1.is_comm.comm ⟨x', hx'⟩ ⟨y', hy'⟩)
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
        exact h
      · rintro x hx
        obtain ⟨x', hx', hx'eq⟩ := Subgroup.mem_map.mp hx
        rw [← hx'eq]
        change ((x' ^ 3 : ↥(sesqUnitaryGroup (ggK1As_restrictForm hE B V))) :
          LinearMap.GeneralLinearGroup E V) = 1
        rw [hP.2 x' hx', Subgroup.coe_one]
    obtain ⟨t₀, ht₀SU, ht₀3, ht₀comm, a₀', ha₀'SU, ha₀'ne⟩ :=
      ggK1As_uni_three_witness hE hsymV hsepV P' hP' hP'le hm
    obtain ⟨g, hgH, hgtriv, hgV⟩ := hHlift t₀ ht₀SU
    obtain ⟨g₀, hg₀H, -, hg₀V⟩ := hHlift a₀' ha₀'SU
    have hρg : ((ρ ⟨g, hgH⟩ : F) : LinearMap.GeneralLinearGroup E V) = t₀ := hliftρ hgV
    have hρg₀ : ((ρ ⟨g₀, hg₀H⟩ : F) : LinearMap.GeneralLinearGroup E V) = a₀' := hliftρ hg₀V
    have hgS : (⟨g, hgH⟩ : ↥H) ∈ S := ⟨hgtriv, by rw [hρg]; exact ht₀SU⟩
    have ht3 : (⟨g, hgH⟩ : ↥H) ^ 3 = 1 := by
      have hρt3GL : ((ρ (⟨g, hgH⟩ : ↥H) ^ 3 : F) : LinearMap.GeneralLinearGroup E V) = 1 := by
        rw [Subgroup.coe_pow, hρg, ht₀3]
      have hρt3 : ρ ((⟨g, hgH⟩ : ↥H) ^ 3) = 1 := by
        rw [map_pow]
        exact Subtype.ext hρt3GL
      have heq : (⟨(⟨g, hgH⟩ : ↥H) ^ 3, S.pow_mem hgS 3⟩ : ↥S) = ⟨1, S.one_mem⟩ := by
        apply hinj
        show ρ ((⟨g, hgH⟩ : ↥H) ^ 3) = ρ 1
        rw [hρt3, map_one]
      exact congrArg Subtype.val heq
    refine ⟨⟨g, hgH⟩, hgS, ht3, ?_, ⟨g₀, hg₀H⟩, ?_⟩
    · intro u hu
      have hu' : (u : LinearMap.GeneralLinearGroup E V) ∈ P' :=
        Subgroup.mem_map_of_mem _ hu
      have hcomm := ht₀comm _ hu'
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hρg]
      exact hcomm.eq
    · intro heq
      apply ha₀'ne
      have hcong := congrArg
        (fun z : ↥H => ((ρ z : F) : LinearMap.GeneralLinearGroup E V)) heq
      rw [map_mul, map_mul] at hcong
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hρg, hρg₀] at hcong
      exact hcong

private noncomputable abbrev ggK1As_idForm {N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 1 K) : (Fin N → K) →ₛₗ[h.bar] (Fin N → K) →ₗ[K] K :=
  CFSG.ClassicalGroups.UnitaryFlag.gramForm h ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)

private theorem ggK1As_idForm_isSymm {N : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) :
    (ggK1As_idForm (N := N) h).IsSymm := by
  refine CFSG.ClassicalGroups.UnitaryFlag.gramForm_isSymm h ?_
  simp

private theorem ggK1As_idForm_separatingLeft {N : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 1 K) : (ggK1As_idForm (N := N) h).SeparatingLeft := by
  refine CFSG.ClassicalGroups.UnitaryFlag.gramForm_separatingLeft h ?_
  simp

private noncomputable def ggK1As_iota (N : ℕ) (K : Type) [Field K] :
    ↥(LargeEvenSUGroup (Fin N) K 2) →* LinearMap.GeneralLinearGroup K (Fin N → K) :=
  (Matrix.GeneralLinearGroup.toLin :
    GL (Fin N) K ≃* LinearMap.GeneralLinearGroup K (Fin N → K)).toMonoidHom.comp
      (LargeEvenSUGroup (Fin N) K 2).subtype

private theorem ggK1As_iota_injective (N : ℕ) (K : Type) [Field K] :
    Function.Injective (ggK1As_iota N K) :=
  Matrix.GeneralLinearGroup.toLin.injective.comp Subtype.val_injective

private theorem ggK1As_range_iota {N : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 1 K) :
    (ggK1As_iota N K).range = sesqSpecialUnitaryGroup (ggK1As_idForm (N := N) h) := by
  have heq : LargeEvenSUGroup (Fin N) K 2 =
      CFSG.ClassicalGroups.UnitaryFlag.gramSU h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) :=
    InndiagSU.largeEvenSUGroup_eq_gramSU (d := N) (n := 1) h
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    have hx : (x : GL (Fin N) K) ∈ CFSG.ClassicalGroups.UnitaryFlag.gramSU h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) := heq ▸ x.2
    exact (CFSG.ClassicalGroups.UnitaryFlag.toLin_mem_sesqSpecialUnitaryGroup_iff h
      ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) (x : GL (Fin N) K)).mpr hx
  · intro hg
    refine ⟨⟨(Matrix.GeneralLinearGroup.toLin :
        GL (Fin N) K ≃* LinearMap.GeneralLinearGroup K (Fin N → K)).symm g, ?_⟩, ?_⟩
    · rw [heq, ← CFSG.ClassicalGroups.UnitaryFlag.toLin_mem_sesqSpecialUnitaryGroup_iff h
        ((1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K), MulEquiv.apply_symm_apply]
      exact hg
    · change Matrix.GeneralLinearGroup.toLin ((Matrix.GeneralLinearGroup.toLin :
        GL (Fin N) K ≃* LinearMap.GeneralLinearGroup K (Fin N → K)).symm g) = g
      exact MulEquiv.apply_symm_apply _ _

private theorem ggK1As_linear_of_mem_primaryFactors
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hE : UnitaryFieldData 2 1 K) {T : Module.End K V} (hT : T ^ 3 = 1)
    {b : K[X]} (hb : b ∈ primaryFactors T) :
    ∃ c : K, c ^ 3 = 1 ∧ b = Polynomial.X - Polynomial.C c := by
  obtain ⟨ω, hω⟩ := ggK1As_exists_primitiveRoot hE
  obtain ⟨hirr, hmon, hdvd⟩ := mem_primaryFactors.mp hb
  have hmin : minpoly K T ∣ Polynomial.X ^ 3 - 1 := by
    refine minpoly.dvd K T ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hT, sub_self]
  have hbdvd : b ∣ Polynomial.X ^ 3 - 1 := hdvd.trans hmin
  have hfac : (Polynomial.X ^ 3 - 1 : K[X]) =
      (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C ω) *
        (Polynomial.X - Polynomial.C (ω ^ 2)) := by
    have hh := X_pow_sub_C_eq_prod hω (α := (1 : K)) (a := (1 : K)) (by norm_num) (by norm_num)
    simpa [Finset.prod_range_succ, map_one] using hh
  have key : ∀ c : K, b ∣ Polynomial.X - Polynomial.C c →
      ∃ c' : K, c' ^ 3 = 1 ∧ b = Polynomial.X - Polynomial.C c' := by
    intro c hdiv
    have hle : b.natDegree ≤ 1 := by
      have := Polynomial.natDegree_le_of_dvd hdiv (monic_X_sub_C c).ne_zero
      rwa [Polynomial.natDegree_X_sub_C] at this
    have hdeg : b.natDegree = 1 := by
      rcases Nat.lt_or_ge b.natDegree 1 with h | h
      · exfalso
        have h0 : b.natDegree = 0 := by omega
        have hbC : b = Polynomial.C (b.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h0
        have hcoeff : IsUnit (b.coeff 0) :=
          isUnit_iff_ne_zero.mpr (fun hc0 => hirr.ne_zero (by rw [hbC, hc0, Polynomial.C_0]))
        exact hirr.not_isUnit (hbC ▸ Polynomial.isUnit_C.mpr hcoeff)
      · omega
    have hb1 : b.coeff 1 = 1 := by
      have h := hmon
      rw [Polynomial.Monic, Polynomial.leadingCoeff] at h
      rwa [hdeg] at h
    have hd := Polynomial.eq_X_add_C_of_natDegree_le_one hle
    have hbX : b = Polynomial.X + Polynomial.C (b.coeff 0) := by
      conv_lhs => rw [hd, hb1]
      simp
    refine ⟨-(b.coeff 0), ?_, ?_⟩
    · have hroot : (Polynomial.X ^ 3 - 1 : K[X]).IsRoot (-(b.coeff 0)) := by
        rw [← Polynomial.dvd_iff_isRoot]
        rw [show Polynomial.X - Polynomial.C (-(b.coeff 0)) = b from by
          conv_rhs => rw [hbX]
          simp only [Polynomial.C_neg, sub_neg_eq_add]]
        exact hbdvd
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, Polynomial.eval_C] at hroot
      exact sub_eq_zero.mp hroot
    · conv_lhs => rw [hbX]
      simp only [Polynomial.C_neg, sub_neg_eq_add]
  rw [hfac] at hbdvd
  rcases (hirr.prime.dvd_mul).mp hbdvd with h | h
  · rcases (hirr.prime.dvd_mul).mp h with h | h
    · exact key (1 : K) h
    · exact key ω h
  · exact key (ω ^ 2) h

private theorem ggK1As_glEnd_mul {N : ℕ} {K : Type} [Field K] (g g' : GL (Fin N) K) :
    ggK1A_glEnd (g * g') = ggK1A_glEnd g * ggK1A_glEnd g' := by
  unfold ggK1A_glEnd
  rw [Units.val_mul, Matrix.toLin'_mul]
  rfl

private theorem ggK1As_glEnd_one {N : ℕ} {K : Type} [Field K] :
    ggK1A_glEnd (1 : GL (Fin N) K) = 1 := by
  unfold ggK1A_glEnd
  rw [Units.val_one, Matrix.toLin'_one]
  rfl

private theorem ggK1As_glEnd_pow {N : ℕ} {K : Type} [Field K] (g : GL (Fin N) K) (n : ℕ) :
    ggK1A_glEnd (g ^ n) = (ggK1A_glEnd g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ggK1As_glEnd_one]
  | succ n ih => rw [pow_succ, ggK1As_glEnd_mul, ih, pow_succ]

private theorem ggK1As_glEnd_pow_eq_one {p N : ℕ} {K : Type} [Field K]
    {g : GL (Fin N) K} (hg : g ^ p = 1) : (ggK1A_glEnd g) ^ p = 1 := by
  rw [← ggK1As_glEnd_pow, hg, ggK1As_glEnd_one]

private theorem ggK1As_glEnd_cube {N : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSUGroup (Fin N) K 2)} (hxp : xhat ^ 3 = 1) :
    (ggK1A_glEnd xhat.1) ^ 3 = 1 :=
  ggK1As_glEnd_pow_eq_one (p := 3) (by simpa using congrArg Subtype.val hxp)

private theorem ggK1As_getD_three (a b c : ℕ) :
    ([a, b, c].getD 0 0 = a) ∧ ([a, b, c].getD 1 0 = b) ∧ ([a, b, c].getD 2 0 = c) :=
  ⟨rfl, rfl, rfl⟩

private theorem ggK1As_exists_eigenspace_dim
    {N : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 1 K)
    {xhat : ↥(LargeEvenSUGroup (Fin N) K 2)} (hxp : xhat ^ 3 = 1) {m : List ℕ}
    (hm : GGK1AMultOf 3 1 N true K (xhat : GL (Fin N) K) m)
    {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA 3 1 (ggMultOrd 3 1) true m).orbits) (hqs : o.qs = false) :
    ∃ c : K, c ^ 3 = 1 ∧
      (Module.finrank K (primaryComponent (ggK1A_glEnd xhat.1)
          (Polynomial.X - Polynomial.C c)) = 2 ∨
       Module.finrank K (primaryComponent (ggK1A_glEnd xhat.1)
          (Polynomial.X - Polynomial.C c)) = 3) := by
  classical
  let T : Module.End K (Fin N → K) := ggK1A_glEnd xhat.1
  have hT3 : T ^ 3 = 1 := ggK1As_glEnd_cube hxp
  obtain ⟨j, hj3, hmj⟩ := ggK1As_qs_false_dim ho hqs
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    refine ⟨1, by norm_num, ?_⟩
    have h1 : Module.finrank K (primaryComponent (ggK1A_glEnd xhat.1) (X - 1)) = m.getD 0 0 :=
      hm.head_eq.symm
    simp only [Polynomial.C_1]
    exact h1 ▸ hmj
  · have hlen : m.length = 3 := by rw [hm.length_eq]
    obtain ⟨m0, m1, m2, hm3⟩ : ∃ a b c, m = [a, b, c] := by
      match m, hlen with
      | [a, b, c], _ => exact ⟨a, b, c, rfl⟩
    subst hm3
    rcases hm.blocks_eq with ⟨⟨-, hf⟩, -⟩ | ⟨-, -, hmult⟩
    · exact absurd hf (by decide)
    · have hmem : ([m0, m1, m2] : List ℕ).getD j 0 ∈
          (ggK1A_selfDualFactors (xhat.1)).val.map (primaryMultiplicity (ggK1A_glEnd xhat.1)) := by
        rw [← hmult]
        have hj12 : j = 1 ∨ j = 2 := by omega
        rcases hj12 with rfl | rfl
        · have hmj1 : m1 = 2 ∨ m1 = 3 := by
            have := hmj
            rwa [(ggK1As_getD_three m0 m1 m2).2.1] at this
          show m1 ∈ (([m1, m2].filter (fun x => decide (x ≠ 0))) : Multiset ℕ)
          rw [Multiset.mem_coe, List.mem_filter]
          exact ⟨by simp, by simp only [decide_eq_true_eq]; omega⟩
        · have hmj2 : m2 = 2 ∨ m2 = 3 := by
            have := hmj
            rwa [(ggK1As_getD_three m0 m1 m2).2.2] at this
          show m2 ∈ (([m1, m2].filter (fun x => decide (x ≠ 0))) : Multiset ℕ)
          rw [Multiset.mem_coe, List.mem_filter]
          exact ⟨by simp, by simp only [decide_eq_true_eq]; omega⟩
      obtain ⟨b, hb, hbval⟩ := Multiset.mem_map.mp hmem
      obtain ⟨hbpf, hbne⟩ := Finset.mem_filter.mp hb
      obtain ⟨c, hc3, hbX⟩ := ggK1As_linear_of_mem_primaryFactors h hT3 hbpf
      refine ⟨c, hc3, ?_⟩
      have hfin : Module.finrank K (primaryComponent T (Polynomial.X - Polynomial.C c)) =
          primaryMultiplicity T (Polynomial.X - Polynomial.C c) := by
        haveI : Fact (Irreducible (Polynomial.X - Polynomial.C c : K[X])) :=
          ⟨Polynomial.irreducible_X_sub_C c⟩
        have hhh := finrank_primaryComponent T (Polynomial.X - Polynomial.C c)
        rwa [Polynomial.natDegree_X_sub_C, one_mul] at hhh
      rw [hfin, show (Polynomial.X - Polynomial.C c : K[X]) = b from hbX.symm]
      rw [hbval]
      exact hmj

private theorem ggK1As_uni_hom_data {N : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 2) (hN : ¬ 3 ∣ N)
    {xhat : ↥(LargeEvenSUGroup (Fin N) K 2)} (hxp : xhat ^ 3 = 1) {m : List ℕ}
    (hm : GGK1AMultOf 3 1 N true K (xhat : GL (Fin N) K) m)
    {o : GGKacOrbit}
    (ho : o ∈ (ggMultDatumA 3 1 (ggMultOrd 3 1) true m).orbits) (hqs : o.qs = false) :
    ∃ (S : Subgroup ↥(Subgroup.centralizer
        ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat} : Set
          (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)))))
      (_ : S.Normal)
      (F : Type) (_ : Group F)
      (ρ : ↥(Subgroup.centralizer
        ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat} : Set
          (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)))) →* F),
      Function.Injective (ρ.comp S.subtype) ∧
      (∀ J : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)),
        CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj
          (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat))) →
        ∀ j ∈ J, ∀ a ∈ S, (a : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)) * j =
          j * (a : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2))) ∧
      (∀ P : Subgroup F, IsElemAbelian 3 P →
        ∃ t : ↥(Subgroup.centralizer
            ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat} : Set
              (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)))),
          t ∈ S ∧ t ^ 3 = 1 ∧ (∀ u ∈ P, u * ρ t = ρ t * u) ∧
          ∃ a₀ : ↥(Subgroup.centralizer
            ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat} : Set
              (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)))), a₀ * t ≠ t * a₀) := by
  have h : UnitaryFieldData 2 1 K := ⟨Nat.prime_two, by norm_num, by rw [hK]⟩
  let B : (Fin N → K) →ₛₗ[h.bar] (Fin N → K) →ₗ[K] K := ggK1As_idForm (N := N) h
  let x : LinearMap.GeneralLinearGroup K (Fin N → K) := ggK1As_iota N K xhat
  let H : Subgroup (LinearMap.GeneralLinearGroup K (Fin N → K)) :=
    Subgroup.centralizer ({x} : Set (LinearMap.GeneralLinearGroup K (Fin N → K))) ⊓
      sesqSpecialUnitaryGroup B
  have hBsym : B.IsSymm := ggK1As_idForm_isSymm h
  have hBsep : B.SeparatingLeft := ggK1As_idForm_separatingLeft h
  have hHU : ∀ g ∈ H, (g : LinearMap.GeneralLinearGroup K (Fin N → K)) ∈ sesqUnitaryGroup B :=
    fun g hg => (sesqSpecialUnitaryGroup_le B) hg.2
  have hHmap : H = (Subgroup.centralizer ({xhat} : Set ↥(LargeEvenSUGroup (Fin N) K 2))).map
      (ggK1As_iota N K) := by
    ext g
    constructor
    · rintro ⟨hgcent, hgSU⟩
      have hgmem : g ∈ (ggK1As_iota N K).range := by
        rw [ggK1As_range_iota h]; exact hgSU
      obtain ⟨y, rfl⟩ := MonoidHom.mem_range.mp hgmem
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      apply ggK1As_iota_injective N K
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hgcent
    · rintro ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        change (ggK1As_iota N K y) * (ggK1As_iota N K xhat) =
          (ggK1As_iota N K xhat) * (ggK1As_iota N K y)
        rw [← map_mul, ← map_mul]
        exact congrArg (ggK1As_iota N K) (Subgroup.mem_centralizer_singleton_iff.mp hy)
      · rw [← ggK1As_range_iota h]
        exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
  let e : ↥H ≃* ↥(Subgroup.centralizer
      ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat} : Set
        (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)))) :=
    (((MulEquiv.subgroupCongr hHmap).trans
      (Subgroup.equivMapOfInjective _
        (ggK1As_iota N K) (ggK1As_iota_injective N K)).symm).trans
      (ggK1As_su_centralizer_equiv hK hN xhat))
  obtain ⟨c, hc3, hcdim⟩ := ggK1As_exists_eigenspace_dim h hxp hm ho hqs
  haveI : CharP K 2 := h.charP
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hxpow : x ^ 3 = 1 := by
    change (ggK1As_iota N K xhat) ^ 3 = 1
    rw [← map_pow, hxp, map_one]
  let T : Module.End K (Fin N → K) := ↑x
  have hT3 : T ^ 3 = 1 := by
    have := congrArg (fun z : LinearMap.GeneralLinearGroup K (Fin N → K) =>
      (z : Module.End K (Fin N → K))) hxpow
    simpa [T] using this
  have hcdim' : Module.finrank K (primaryComponent T (Polynomial.X - Polynomial.C c)) = 2 ∨
      Module.finrank K (primaryComponent T (Polynomial.X - Polynomial.C c)) = 3 := hcdim
  have hsqT : Squarefree (minpoly K T) := by
    refine CFSG.RankThree.PartOne.KCPrimary.squarefree_minpoly_of_aeval_eq_zero
      (ggK1As_squarefree_X_pow_three_char2 h2K) ?_
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hT3, sub_self]
  haveI : Fact (Irreducible (Polynomial.X - Polynomial.C c : K[X])) :=
    ⟨Polynomial.irreducible_X_sub_C c⟩
  have hcf : (Polynomial.X - Polynomial.C c : K[X]) ∈ primaryFactors T := by
    have hne : primaryComponent T (Polynomial.X - Polynomial.C c) ≠ ⊥ := by
      intro hbot
      rw [hbot] at hcdim'
      simp at hcdim'
    obtain ⟨w, hwmem, hwne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    exact CFSG.StandardType.SUTB.mem_primaryFactors_of_ker
      (Polynomial.irreducible_X_sub_C c) (Polynomial.monic_X_sub_C c) hwne
      (mem_primaryComponent.mp hwmem)
  let V : Submodule K (Fin N → K) := primaryComponent T (Polynomial.X - Polynomial.C c)
  let π : Module.End K (Fin N → K) := primaryProjection T (Polynomial.X - Polynomial.C c)
  have hπmem : ∀ w, π w ∈ V := fun w => primaryProjection_mem hsqT hcf w
  have hπfix : ∀ v ∈ V, π v = v := fun v hv => primaryProjection_of_mem hsqT hcf hv
  have hπidem : π * π = π := by
    apply LinearMap.ext
    intro w
    rw [Module.End.mul_apply]
    exact hπfix (π w) (hπmem w)
  have hTV : ∀ v ∈ V, T v = c • v := by
    intro v hv
    have hh := mem_primaryComponent.mp hv
    have hh' : T v - c • v = 0 := by
      simpa only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
        LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] using hh
    exact sub_eq_zero.mp hh'
  have hbar_c : h.bar c = c ^ 2 := by rw [UnitaryFieldData.bar_apply]; norm_num
  have hbar_mul : h.bar c * c = 1 := by
    rw [hbar_c, ← pow_succ, show 2 + 1 = 3 by norm_num, hc3]
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0] at hc3; norm_num at hc3
  have hdual : CFSG.RankThree.PartOne.KCUnitary.dualPoly h.bar
      (Polynomial.X - Polynomial.C c) = Polynomial.X - Polynomial.C c := by
    rw [CFSG.AGLEmbedding.UnitaryLevi.dualPoly_X_sub_C h.bar (l := c) hc0]
    rw [show (h.bar c)⁻¹ = c from inv_eq_of_mul_eq_one_right hbar_mul]
  have hHup : CFSG.RankThree.PartOne.KCUnitary.UnitaryPrimaryData h.bar B x :=
    { invol := UnitaryFieldData.bar_bar h
      symm := hBsym
      sep := hBsep
      isom := (sesqSpecialUnitaryGroup_le B) (by
        rw [← ggK1As_range_iota h]; exact MonoidHom.mem_range.mpr ⟨xhat, rfl⟩)
      squarefree := hsqT }
  have hpar : ∀ v w : Fin N → K, B (π v) w = B (π v) (π w) := by
    intro v w
    rw [CFSG.RankThree.PartOne.KCUnitary.B_eq_sum hHup (π v) w]
    rw [Finset.sum_eq_single (Polynomial.X - Polynomial.C c)]
    · rw [hdual]
      rw [show primaryProjection T (Polynomial.X - Polynomial.C c) (π v) = π v from
        hπfix (π v) (hπmem v)]
    · intro b hb hbne
      have hzero : primaryProjection T b (π v) = 0 :=
        primaryProjection_of_mem_ne hsqT (a := b) (b := Polynomial.X - Polynomial.C c)
          hb hcf (fun hh => hbne hh.symm) (primaryProjection_mem hsqT hcf v)
      rw [hzero, map_zero, LinearMap.zero_apply]
    · intro hnot
      exact absurd hcf hnot
  have horth : ∀ w w' : Fin N → K, B (π w) (w' - π w') = 0 ∧ B (w - π w) (π w') = 0 := by
    intro w w'
    constructor
    · rw [map_sub, hpar w w', sub_self]
    · rw [map_sub, LinearMap.sub_apply]
      have h1 : B w (π w') = B (π w) (π w') := by
        rw [← hBsym.eq (π w') w, hpar w' w, hBsym.eq (π w') (π w)]
      rw [h1, sub_self]
  have hHπ : ∀ g ∈ H, Commute (g : Module.End K (Fin N → K)) π := by
    intro g hg
    have hgx : Commute (g : Module.End K (Fin N → K)) T := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg.1
      have h2 : (g : LinearMap.GeneralLinearGroup K (Fin N → K)) * x =
          x * (g : LinearMap.GeneralLinearGroup K (Fin N → K)) := h1
      have h3 : (((g : LinearMap.GeneralLinearGroup K (Fin N → K))) : Module.End K (Fin N → K)) *
          (x : Module.End K (Fin N → K)) =
          (x : Module.End K (Fin N → K)) *
            ((g : LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) :=
        congrArg (fun z : LinearMap.GeneralLinearGroup K (Fin N → K) =>
          (z : Module.End K (Fin N → K))) h2
      exact h3
    change Commute (g : Module.End K (Fin N → K))
      (aeval T (primaryIdempotent T (Polynomial.X - Polynomial.C c)))
    exact commute_aeval hgx (primaryIdempotent T (Polynomial.X - Polynomial.C c))
  have hmemker : ∀ w : Fin N → K, w - π w ∈ π.ker := by
    intro w
    rw [LinearMap.mem_ker, map_sub]
    have h := congrArg (fun f : Module.End K (Fin N → K) => f w) hπidem
    simp only [Module.End.mul_apply] at h
    rw [h, sub_self]
  have horthVL : ∀ v ∈ V, ∀ u ∈ π.ker, B v u = 0 := by
    intro v hv u hu
    have h := (horth v u).1
    rw [hπfix v hv, LinearMap.mem_ker.mp hu, sub_zero] at h
    exact h
  have horthLV : ∀ u ∈ π.ker, ∀ v ∈ V, B u v = 0 := by
    intro u hu v hv
    have h := (horth u v).2
    rw [hπfix v hv, LinearMap.mem_ker.mp hu, sub_zero] at h
    exact h
  have hxH : x ∈ H := ⟨Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x),
    by rw [← ggK1As_range_iota h]; exact MonoidHom.mem_range.mpr ⟨xhat, rfl⟩⟩
  have hTπ : Commute T π := by simpa [T] using hHπ x hxH
  have hsupp : V ⊔ π.ker = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro w
    exact Submodule.mem_sup.mpr ⟨π w, hπmem w, w - π w, hmemker w, by abel⟩
  have hdisj : V ⊓ π.ker = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hv, hu⟩ := Submodule.mem_inf.mp hw
    rw [← hπfix w hv, LinearMap.mem_ker.mp hu]
    exact Submodule.zero_mem _
  have hcompl : IsCompl V π.ker := ⟨disjoint_iff.mpr hdisj, codisjoint_iff.mpr hsupp⟩
  have hHlift : ∀ s ∈ sesqSpecialUnitaryGroup (ggK1As_restrictForm h B V),
      ∃ g ∈ H, (∀ w : Fin N → K, ((g : Module.End K (Fin N → K)) - 1) w ∈ V) ∧
        ∀ v : V, (g : Module.End K (Fin N → K)) (v : Fin N → K) =
          (((s : LinearMap.GeneralLinearGroup K V) : Module.End K V) v : Fin N → K) := by
    intro s hs
    let sEnd : Module.End K V := (s : LinearMap.GeneralLinearGroup K V)
    let πV : (Fin N → K) →ₗ[K] V := π.codRestrict V hπmem
    let gEnd : Module.End K (Fin N → K) := V.subtype.comp (sEnd.comp πV) + (1 - π)
    have hgEnd_apply : ∀ w : Fin N → K, gEnd w = ((sEnd (πV w) : V) : Fin N → K) + (w - π w) := by
      intro w
      simp only [gEnd, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype,
        Module.End.one_apply, LinearMap.sub_apply]
    have hB1 : ∀ w w', B ((sEnd (πV w) : V) : Fin N → K) ((sEnd (πV w') : V) : Fin N → K) =
        B (π w) (π w') := by
      intro w w'
      have h := (mem_sesqUnitaryGroup.mp hs.1) (πV w) (πV w')
      rw [ggK1As_restrictForm_apply, ggK1As_restrictForm_apply] at h
      have h2 : ((πV w : V) : Fin N → K) = π w := rfl
      have h3 : ((πV w' : V) : Fin N → K) = π w' := rfl
      rwa [h2, h3] at h
    have hB2 : ∀ w w', B ((sEnd (πV w) : V) : Fin N → K) (w' - π w') = 0 := fun w w' =>
      horthVL _ (sEnd (πV w)).2 _ (hmemker w')
    have hB3 : ∀ w w', B (w - π w) ((sEnd (πV w') : V) : Fin N → K) = 0 := fun w w' =>
      horthLV _ (hmemker w) _ (sEnd (πV w')).2
    have hB2' : ∀ w w', B (π w) (w' - π w') = 0 := fun w w' => horthVL _ (hπmem w) _ (hmemker w')
    have hB3' : ∀ w w', B (w - π w) (π w') = 0 := fun w w' => horthLV _ (hmemker w) _ (hπmem w')
    have hUni : ∀ w w', B (gEnd w) (gEnd w') = B w w' := by
      intro w w'
      have hdecomp : B w w' = B (π w) (π w') + B (w - π w) (w' - π w') := by
        have hw : w = π w + (w - π w) := by abel
        have hw' : w' = π w' + (w' - π w') := by abel
        rw [hw, hw']
        rw [map_add B (π w) (w - π w), LinearMap.add_apply,
          map_add (B (π w)) (π w') (w' - π w'),
          map_add (B (w - π w)) (π w') (w' - π w')]
        rw [hB2' w w', hB3' w w']
        abel_nf
      calc B (gEnd w) (gEnd w')
          = B (((sEnd (πV w) : V) : Fin N → K) + (w - π w))
              (((sEnd (πV w') : V) : Fin N → K) + (w' - π w')) := by rw [hgEnd_apply, hgEnd_apply]
        _ = B ((sEnd (πV w) : V) : Fin N → K) ((sEnd (πV w') : V) : Fin N → K)
              + B ((sEnd (πV w) : V) : Fin N → K) (w' - π w')
              + B (w - π w) ((sEnd (πV w') : V) : Fin N → K)
              + B (w - π w) (w' - π w') := by
            simp only [map_add, LinearMap.add_apply, map_sub, LinearMap.sub_apply]
            abel
        _ = B (π w) (π w') + B (w - π w) (w' - π w') := by
            rw [hB1 w w', hB2 w w', hB3 w w']
            abel
        _ = B w w' := hdecomp.symm
    have hdetg : LinearMap.det gEnd = 1 := by
      let eExp : (V × π.ker) ≃ₗ[K] (Fin N → K) :=
        { toFun := fun p => (p.1 : Fin N → K) + (p.2 : Fin N → K)
          invFun := fun w => (πV w, ⟨w - π w, hmemker w⟩)
          left_inv := by
            rintro ⟨v, u⟩
            apply Prod.ext
            · apply Subtype.ext
              show π ((v : Fin N → K) + (u : Fin N → K)) = (v : Fin N → K)
              rw [map_add, hπfix v v.2, LinearMap.mem_ker.mp u.2, add_zero]
            · apply Subtype.ext
              show ((v : Fin N → K) + (u : Fin N → K)) -
                π ((v : Fin N → K) + (u : Fin N → K)) = (u : Fin N → K)
              rw [map_add, hπfix v v.2, LinearMap.mem_ker.mp u.2, add_zero]
              abel
          right_inv := by
            intro w
            show π w + (w - π w) = w
            abel
          map_add' := by
            rintro ⟨v, u⟩ ⟨v', u'⟩
            simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
            abel
          map_smul' := by
            rintro a ⟨v, u⟩
            show a • (v : Fin N → K) + a • (u : Fin N → K) =
              a • ((v : Fin N → K) + (u : Fin N → K))
            rw [smul_add] }
      have hconj : gEnd = ↑eExp ∘ₗ LinearMap.prodMap sEnd (1 : Module.End K π.ker) ∘ₗ ↑eExp.symm :=
          by
        apply LinearMap.ext
        intro w
        have he : eExp.symm w = (πV w, ⟨w - π w, hmemker w⟩) := rfl
        simp only [LinearMap.comp_apply, he, LinearMap.prodMap_apply, Module.End.one_apply]
        rw [hgEnd_apply]
        rfl
      rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, map_one LinearMap.det, mul_one]
      exact (mem_sesqSpecialUnitaryGroup.mp hs).2
    let sInv : Module.End K V := ((s⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V)
    let gInv : Module.End K (Fin N → K) := V.subtype.comp (sInv.comp πV) + (1 - π)
    have hgInv_apply : ∀ w : Fin N → K, gInv w = ((sInv (πV w) : V) : Fin N → K) + (w - π w) := by
      intro w
      simp only [gInv, LinearMap.add_apply, LinearMap.comp_apply, Submodule.coe_subtype,
        Module.End.one_apply, LinearMap.sub_apply]
    have hsEnd_sInv : sEnd * sInv = 1 := by
      show (s : Module.End K V) * ((s⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) = 1
      rw [← Units.val_mul, mul_inv_cancel]; rfl
    have hsInv_sEnd : sInv * sEnd = 1 := by
      show ((s⁻¹ : LinearMap.GeneralLinearGroup K V) : Module.End K V) * (s : Module.End K V) = 1
      rw [← Units.val_mul, inv_mul_cancel]; rfl
    have hπV_apply : ∀ w : Fin N → K, πV w = ⟨π w, hπmem w⟩ := fun w => rfl
    have hπ_gInv : ∀ w : Fin N → K, πV (gInv w) = sInv (πV w) := by
      intro w
      rw [hgInv_apply]
      apply Subtype.ext
      show π (↑(sInv (πV w)) + (w - π w)) = ↑(sInv (πV w))
      rw [map_add, hπfix _ (sInv (πV w)).2, LinearMap.mem_ker.mp (hmemker w), add_zero]
    have hπ_gEnd : ∀ w : Fin N → K, πV (gEnd w) = sEnd (πV w) := by
      intro w
      rw [hgEnd_apply]
      apply Subtype.ext
      show π (↑(sEnd (πV w)) + (w - π w)) = ↑(sEnd (πV w))
      rw [map_add, hπfix _ (sEnd (πV w)).2, LinearMap.mem_ker.mp (hmemker w), add_zero]
    have hmul1 : gEnd * gInv = 1 := by
      apply LinearMap.ext
      intro w
      rw [Module.End.mul_apply, hgInv_apply]
      show gEnd (↑(sInv (πV w)) + (w - π w)) = w
      rw [hgEnd_apply]
      have hx : πV (↑(sInv (πV w)) + (w - π w)) = sInv (πV w) := by
        apply Subtype.ext
        show π (↑(sInv (πV w)) + (w - π w)) = ↑(sInv (πV w))
        rw [map_add, hπfix _ (sInv (πV w)).2, LinearMap.mem_ker.mp (hmemker w), add_zero]
      have hpx : π (↑(sInv (πV w)) + (w - π w)) = ↑(sInv (πV w)) := by
        show π (↑(sInv (πV w)) + (w - π w)) = ↑(sInv (πV w))
        rw [map_add, hπfix _ (sInv (πV w)).2, LinearMap.mem_ker.mp (hmemker w), add_zero]
      rw [hx, hpx]
      have hs1 : sEnd (sInv (πV w)) = πV w := by
        have h := congrArg (fun f : Module.End K V => f (πV w)) hsEnd_sInv
        simpa only [Module.End.mul_apply, Module.End.one_apply] using h
      rw [hs1, show ((πV w : V) : Fin N → K) = π w from rfl]
      abel
    have hmul2 : gInv * gEnd = 1 := by
      apply LinearMap.ext
      intro w
      rw [Module.End.mul_apply, hgEnd_apply]
      show gInv (↑(sEnd (πV w)) + (w - π w)) = w
      rw [hgInv_apply]
      have hx : πV (↑(sEnd (πV w)) + (w - π w)) = sEnd (πV w) := by
        apply Subtype.ext
        show π (↑(sEnd (πV w)) + (w - π w)) = ↑(sEnd (πV w))
        rw [map_add, hπfix _ (sEnd (πV w)).2, LinearMap.mem_ker.mp (hmemker w), add_zero]
      have hpx : π (↑(sEnd (πV w)) + (w - π w)) = ↑(sEnd (πV w)) := by
        show π (↑(sEnd (πV w)) + (w - π w)) = ↑(sEnd (πV w))
        rw [map_add, hπfix _ (sEnd (πV w)).2, LinearMap.mem_ker.mp (hmemker w), add_zero]
      rw [hx, hpx]
      have hs2 : sInv (sEnd (πV w)) = πV w := by
        have h := congrArg (fun f : Module.End K V => f (πV w)) hsInv_sEnd
        simpa only [Module.End.mul_apply, Module.End.one_apply] using h
      rw [hs2, show ((πV w : V) : Fin N → K) = π w from rfl]
      abel
    let g : LinearMap.GeneralLinearGroup K (Fin N → K) := ⟨gEnd, gInv, hmul1, hmul2⟩
    have hg_coe : (g : Module.End K (Fin N → K)) = gEnd := rfl
    refine ⟨g, ?_, ?_, ?_⟩
    · refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · apply ggK1As_commute_units_of_coe
        change Commute gEnd T
        rw [Commute]
        apply LinearMap.ext
        intro w
        rw [Module.End.mul_apply, Module.End.mul_apply, hgEnd_apply, hgEnd_apply]
        have h2 : π (T w) = T (π w) := by
          have hh := congrArg (fun f : Module.End K (Fin N → K) => f w) hTπ.eq
          simpa only [Module.End.mul_apply] using hh.symm
        have h1 : πV (T w) = c • πV w := by
          apply Subtype.ext
          show π (T w) = ↑(c • πV w)
          rw [h2, hTV (π w) (hπmem w)]
          rfl
        rw [h1, map_smul]
        have h4 : π (T w) = c • π w := by rw [h2, hTV (π w) (hπmem w)]
        rw [h4, map_add, hTV (↑(sEnd (πV w))) (sEnd (πV w)).2]
        rw [map_sub, hTV (π w) (hπmem w)]
        simp only [Submodule.coe_smul]
      · change g ∈ sesqSpecialUnitaryGroup B
        rw [mem_sesqSpecialUnitaryGroup]
        refine ⟨?_, ?_⟩
        · rw [mem_sesqUnitaryGroup]
          intro w w'
          simpa only [hg_coe] using hUni w w'
        · simpa only [hg_coe] using hdetg
    · intro w
      rw [LinearMap.sub_apply, Module.End.one_apply, hg_coe, hgEnd_apply]
      have : ((sEnd (πV w) : V) : Fin N → K) + (w - π w) - w =
          ((sEnd (πV w) : V) : Fin N → K) - π w := by abel
      rw [this]
      exact Submodule.sub_mem V (sEnd (πV w)).2 (hπmem w)
    · intro v
      rw [hg_coe, hgEnd_apply]
      have hπv : πV (v : Fin N → K) = v := by
        apply Subtype.ext
        exact hπfix v v.2
      rw [hπv, show (v : Fin N → K) - π (v : Fin N → K) = 0 from by
        rw [hπfix v v.2, sub_self], add_zero]
  obtain ⟨S_H, hS_H_n, F, hF, ρ_H, hinj_H, hcomp_H, hP_H⟩ :=
    ggK1As_uni_abstract_data h hBsym hBsep H V π hπidem hπmem hπfix horth hHπ hHU hHlift hcdim'
  refine ⟨S_H.map e.toMonoidHom, ?_, F, hF, ρ_H.comp e.symm.toMonoidHom, ?_, ?_, ?_⟩
  · exact hS_H_n.map e.toMonoidHom e.surjective
  · intro a b hab
    obtain ⟨a', ha', haeq⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hbeq⟩ := Subgroup.mem_map.mp b.2
    have ha'e : e a' = a.1 := haeq
    have hb'e : e b' = b.1 := hbeq
    have h1 : (ρ_H.comp S_H.subtype) ⟨a', ha'⟩ = (ρ_H.comp S_H.subtype) ⟨b', hb'⟩ := by
      have h := hab
      change (ρ_H.comp e.symm.toMonoidHom) a.1 = (ρ_H.comp e.symm.toMonoidHom) b.1 at h
      change ρ_H (e.symm a.1) = ρ_H (e.symm b.1) at h
      rw [← ha'e, ← hb'e, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at h
      exact h
    have h2 := hinj_H h1
    have h3 : a' = b' := congrArg Subtype.val h2
    apply Subtype.ext
    rw [← ha'e, ← hb'e, h3]
  · intro J hJ j hj a ha
    have hJleC : J ≤ Subgroup.centralizer
        ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat} : Set
          (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2))) := by
      intro j hj
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hfix : MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat) j = j :=
        hJ.1 hj
      rw [MulAut.conj_apply] at hfix
      have h' : LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat * j =
          j * LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat := by
        calc LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat * j
            = LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat * j *
                (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat)⁻¹ *
                LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat := by group
          _ = j * LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat := by rw [hfix]
      exact h'.symm
    let Cq : Subgroup (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)) :=
      Subgroup.centralizer ({LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat} : Set
        (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)))
    have hJleC' : J ≤ Cq := hJleC
    let Jc : Subgroup ↥Cq := J.subgroupOf Cq
    let Jg : Subgroup (LinearMap.GeneralLinearGroup K (Fin N → K)) :=
      Jc.map ((Subgroup.subtype H).comp e.symm.toMonoidHom)
    have hJcperf : Group.IsPerfect ↥Jc := by
      haveI : Group.IsPerfect ↥J := ⟨hJ.2.2.1⟩
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hJleC').symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hJleC').symm.surjective
    have hJgH : Jg ≤ H := by
      rintro x ⟨c, hc, rfl⟩
      exact (e.symm c).2
    have hJgperf : Group.IsPerfect ↥Jg := by
      haveI : Group.IsPerfect ↥Jc := hJcperf
      exact Group.IsPerfect.map (H := Jc) ((Subgroup.subtype H).comp e.symm.toMonoidHom)
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    let c : ↥Cq := ⟨j, hJleC hj⟩
    let jH : ↥H := e.symm c
    let jg : LinearMap.GeneralLinearGroup K (Fin N → K) := (Subgroup.subtype H) jH
    have hjg : jg ∈ Jg := by
      refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr hj
    have hcommH : a' * jH = jH * a' :=
      Subtype.ext (hcomp_H Jg hJgH hJgperf jg hjg a' ha')
    have hje : (e jH : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)) = j := by
      change (e (e.symm c) : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)) = j
      rw [MulEquiv.apply_symm_apply]
    have heq : e (a' * jH) = e (jH * a') := congrArg e hcommH
    rw [map_mul, map_mul] at heq
    show (e a' : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)) * j =
      j * (e a' : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2))
    rw [← hje]
    exact congrArg (fun z : ↥Cq =>
      (z : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2))) heq
  · intro P hP
    obtain ⟨t_H, ht_H, ht3_H, hcomm_H, a₀_H, ha₀_H⟩ := hP_H P hP
    refine ⟨e.toMonoidHom t_H, Subgroup.mem_map_of_mem _ ht_H, ?_, ?_,
      e.toMonoidHom a₀_H, ?_⟩
    · rw [← map_pow, ht3_H, map_one]
    · intro u hu
      have he : (ρ_H.comp e.symm.toMonoidHom) (e.toMonoidHom t_H) = ρ_H t_H := by
        change ρ_H (e.symm (e t_H)) = ρ_H t_H
        rw [MulEquiv.symm_apply_apply]
      rw [he]
      exact hcomm_H u hu
    · intro heq
      apply ha₀_H
      have h := congrArg e.symm heq
      have hsymm_a : e.symm (e.toMonoidHom a₀_H) = a₀_H := by
        change e.symm (e a₀_H) = a₀_H
        rw [MulEquiv.symm_apply_apply]
      have hsymm_t : e.symm (e.toMonoidHom t_H) = t_H := by
        change e.symm (e t_H) = t_H
        rw [MulEquiv.symm_apply_apply]
      rw [map_mul, map_mul, hsymm_a, hsymm_t] at h
      exact h

theorem ggK1A_sigma_two_uni {N : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 2)
    (hN : ¬ 3 ∣ N)
    {xhat : ↥(LargeEvenSUGroup (Fin N) K 2)} (hxp : xhat ^ 3 = 1) {m : List ℕ}
    (hm : GGK1AMultOf 3 1 N true K (xhat : GL (Fin N) K) m) :
    GGKacSigmaClause 3
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2))
        (LargeEvenGUSet (Fin N) K 2))
      (ggMultDatumA 3 1 (ggMultOrd 3 1) true m) (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2))
      (MonoidHom.id _) (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat)) := by
  intro o ho hqs A hxA hA hAI
  have hZ : ∀ z : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2),
      (∀ g : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2), g * z = z * g) → z = 1 := by
    intro z hz
    have hzc : z ∈ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2)) :=
      Subgroup.mem_center_iff.mpr hz
    rw [ggK1As_su_centre_bot (N := N) hK hN] at hzc
    exact Subgroup.mem_bot.mp hzc
  let I' : Set (MulAut (LargeEvenProj (LargeEvenSUGroup (Fin N) K 2))) :=
    {φ | φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2))
        (LargeEvenGUSet (Fin N) K 2) ∧ φ ^ 3 = 1}
  have hI' : ∀ φ ∈ I', ∃ s : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2),
      φ = MulAut.conj s :=
    fun φ hφ => ggK1As_su_conjImage_inner_three hK hN φ hφ.1 hφ.2
  have hAI' : ∀ a ∈ A, ∃ φ ∈ I', ∀ l : LargeEvenProj (LargeEvenSUGroup (Fin N) K 2),
      φ l = a l := by
    intro a ha
    obtain ⟨φ, hφI, hφa⟩ := hAI a ha
    refine ⟨φ, ⟨hφI, ?_⟩, hφa⟩
    have hφeq : φ = a := MulEquiv.ext hφa
    rw [hφeq, hA.2 a ha]
  obtain ⟨S, hSn, F, _, ρ, hinj, hcomp, hP⟩ :=
    ggK1As_uni_hom_data hK hN hxp hm ho hqs
  exact ggK1_sigma_abstract_hom hZ I' hI'
    (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K 2) xhat) S hSn ρ hinj hcomp hP A hxA hA hAI'

theorem ggK1A_core_sigma {p nf N : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hK : Nat.card K = 2 ^ nf)
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1) {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m) :
    GGKacSigmaClause p
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (Set.univ : Set (GL (Fin N) K)))
      (ggMultDatumA p nf (ggMultOrd p nf) false m) (LargeEvenProj (LargeEvenSLGroup (Fin N) K))
      (MonoidHom.id _) (MulAut.conj (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) xhat)) := by
  intro o ho hqs A hxA hA hAI
  obtain ⟨hnf, hp3, -⟩ := ggK1A_qs_false_corner hp hdvd ho hqs
  subst hnf hp3
  exact ggK1A_sigma_two_lin hK hxp hm o ho hqs A hxA hA hAI

theorem ggK1A_uni_core_sigma {p nf N : ℕ} {K : Type} [Field K] [Finite K] (hp : p.Prime)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) (hK : Nat.card K = (2 ^ nf) ^ 2) (hnotRAu : ¬ (p ∣ N ∧
        p ∣ 2 ^ nf + 1))
    {xhat : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))} (hxp : xhat ^ p = 1) {m : List ℕ}
    (hm : GGK1AMultOf p nf N true K (xhat : GL (Fin N) K) m) :
    GGKacSigmaClause p
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)))
        (LargeEvenGUSet (Fin N) K (2 ^ nf)))
      (ggMultDatumA p nf (ggMultOrd p nf) true m)
      (LargeEvenProj (LargeEvenSUGroup (Fin N) K (2 ^ nf))) (MonoidHom.id _)
      (MulAut.conj (LargeEvenProjMk (LargeEvenSUGroup (Fin N) K (2 ^ nf)) xhat)) := by
  intro o ho hqs A hxA hA hAI
  obtain ⟨hnf, hp3, -⟩ := ggK1A_qs_false_corner hp hdvd ho hqs
  subst hnf hp3
  have hN : ¬ 3 ∣ N := fun h => hnotRAu ⟨h, by norm_num⟩
  exact ggK1A_sigma_two_uni hK hN hxp hm o ho hqs A hxA hA hAI

end CFSG.StandardType

end
