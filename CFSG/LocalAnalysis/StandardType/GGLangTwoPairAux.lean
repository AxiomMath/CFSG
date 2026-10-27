module

public import CFSG.LieType.Chevalley.CorootCoordinates

public import CFSG.LocalAnalysis.StandardType.GGLangOrbitTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGLangCorootPair
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Count
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.WeylTorusAct

open Polynomial

public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement

theorem j4e_exists_cubeRoot
    {L : Type} [Field L] [IsAlgClosed L] (h2 : (2 : L) = 0) :
    ∃ ω : L, ω ^ 2 + ω + 1 = 0 := by
  have hp : (Polynomial.X ^ 2 + Polynomial.X + 1 : L[X]).degree ≠ 0 := by
    have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : L[X]).degree = 2 := by
      have e : (Polynomial.X ^ 2 + Polynomial.X + 1 : L[X]) =
          Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C 1 * Polynomial.X + Polynomial.C 1 := by
        simp
      rw [e]
      exact Polynomial.degree_quadratic (by norm_num : (1 : L) ≠ 0)
    rw [hdeg]
    norm_num
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root _ hp
  refine ⟨ω, ?_⟩
  simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one] at hω
  exact hω

theorem j4e_rootSL2_HSL_eq_rootDiagUnit {τ : Tag} {L : Type} [Field L]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (t : Lˣ) :
    rootSL2 τ L γ (HSL t) =
      rootDiagUnit τ (fun j => t ^ corootPair γ (Pi.single j 1)) := by
  change rootTorusSL2 τ L γ t = _
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair hγ t]
  rfl

theorem j4e_rootSL2_HSL_conj_pinnedX_self {τ : Tag} {L : Type} [Field L]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (t : Lˣ) (c : L) :
    rootSL2 τ L γ (HSL t) * pinnedX τ L γ c * (rootSL2 τ L γ (HSL t))⁻¹ =
      pinnedX τ L γ ((t : L) ^ 2 * c) := by
  rw [j4e_rootSL2_HSL_eq_rootDiagUnit hγ t, rootDiagUnit_conj_pinnedX _ hγ c,
    j4e_rootChar_corootTuple hγ t γ]
  have hpair : corootPair γ γ = 2 := by
    rw [corootPair, Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hγ).ne']
  rw [hpair]
  congr 1

theorem j4e_rootSL2_HSL_conj_pinnedX_of_orthogonal {τ : Tag} {L : Type} [Field L]
    {γ β : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hβ : IsRoot τ β) (h0 : iform γ β = 0)
    (t : Lˣ) (c : L) :
    rootSL2 τ L γ (HSL t) * pinnedX τ L β c * (rootSL2 τ L γ (HSL t))⁻¹ =
      pinnedX τ L β c := by
  rw [j4e_rootSL2_HSL_eq_rootDiagUnit hγ t, rootDiagUnit_conj_pinnedX _ hβ c,
    j4e_rootChar_corootTuple hγ t β]
  have hpair : corootPair γ β = 0 := by
    rw [corootPair, h0, mul_zero, Int.zero_ediv]
  rw [hpair]
  simp

theorem j4e_step_pinnedX_of_q_two
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq : S.D.q = 2) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (c : L) :
    S.D.step (pinnedX τ L γ c) = pinnedX τ L (S.ρ γ) (c ^ 2) := by
  obtain ⟨μ, hμ0, hμ⟩ := step_pinnedX S hγ
  have h1 := hμ 1
  rw [step_pinnedX_one_of_charTwo S hγ] at h1
  have hμ1 : μ = 1 := by
    apply pinnedX_injective (τ := τ) (R := L) (S.ρ γ)
    simpa using h1.symm
  rw [hμ c, hμ1, hq]
  congr 1
  ring

theorem j4e_step_rootSL2_HSL_swap
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (hq : S.D.q = 2) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (t : Lˣ) :
    S.D.step (rootSL2 τ L γ (HSL t)) = rootSL2 τ L (S.ρ γ) (HSL (t ^ 2)) := by
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow (f := 1) S (by rw [hq]; norm_num)
  have hstep : ∀ {δ : Fin τ.rank → ℤ}, IsRoot τ δ → ∀ c : L,
      S.D.step (pinnedX τ L δ c) = pinnedX τ L (S.ρ δ) (c ^ 2) :=
    fun hδ c => j4e_step_pinnedX_of_q_two S hq hδ c
  have hβ : IsRoot τ (S.ρ γ) := (S.frob.isRoot_iff γ).2 hγ
  have hu : ∀ c, S.D.step (rootSL2 τ L γ (uSL c)) = rootSL2 τ L (S.ρ γ) (uSL (c ^ 2)) := by
    intro c
    rw [CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hγ,
      CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hβ, hstep hγ c]
  have hv : ∀ c, S.D.step (rootSL2 τ L γ (vSL c)) = rootSL2 τ L (S.ρ γ) (vSL (c ^ 2)) := by
    intro c
    rw [CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hγ,
      CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hβ, ← S.frob.neg_eq γ,
      hstep (IsRoot.neg hγ) c]
  rw [HSL_eq_uvu_two t]
  simp only [map_mul, hu, hv]
  conv_rhs => rw [HSL_eq_uvu_two (t ^ 2)]
  simp only [map_mul, one_pow]
  rw [← inv_pow]
  simp only [Units.val_pow_eq_pow_val]

theorem j4e_linIndepPair_of_orthogonal
    {τ : Tag} {γ β : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hβ : IsRoot τ β) (h0 : iform γ β = 0) : LinIndepPair γ β := by
  intro a b hab
  have h1 : iform γ (a • γ + b • β) = 0 := by rw [hab]; simp [iform]
  rw [iform_add_right, iform_smul_right, iform_smul_right, h0, mul_zero, add_zero] at h1
  have hpos := iform_self_pos_of_isRoot hγ
  have ha : a = 0 := (mul_eq_zero.1 h1).resolve_right (ne_of_gt hpos)
  have hbβ : b • β = 0 := by
    have h2 : a • γ + b • β = b • β := by rw [ha, zero_smul, zero_add]
    rw [h2] at hab
    exact hab
  have hb : b = 0 := (smul_eq_zero.1 hbβ).resolve_right hβ.ne_zero
  exact ⟨ha, hb⟩

theorem j4e_pinnedX_mul_injective_of_linIndep
    {τ : Tag} {L : Type} [Field L] (h2 : (2 : L) = 0)
    {γ β : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hβ : IsRoot τ β)
    (hlin : LinIndepPair γ β) {a b c d : L}
    (h : pinnedX τ L γ a * pinnedX τ L β b = pinnedX τ L γ c * pinnedX τ L β d) :
    a = c ∧ b = d := by
  have hne : γ ≠ β := by
    intro e
    have h1 := hlin 1 (-1) (by rw [e]; simp)
    norm_num at h1
  obtain ⟨w, hwγ, hwβ⟩ := exists_weyl_height_pos hγ hβ hlin
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have hwne : w • γ ≠ w • β := fun e => hne (MulAction.injective w e)
  have hleft : n * (pinnedX τ L γ a * pinnedX τ L β b) * n⁻¹ =
      pinnedX τ L (w • γ) a * pinnedX τ L (w • β) b := by
    calc n * (pinnedX τ L γ a * pinnedX τ L β b) * n⁻¹ =
        (n * pinnedX τ L γ a * n⁻¹) * (n * pinnedX τ L β b * n⁻¹) := by group
      _ = _ := by
        rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hγ a,
          canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hβ b]
  have hright : n * (pinnedX τ L γ c * pinnedX τ L β d) * n⁻¹ =
      pinnedX τ L (w • γ) c * pinnedX τ L (w • β) d := by
    calc n * (pinnedX τ L γ c * pinnedX τ L β d) * n⁻¹ =
        (n * pinnedX τ L γ c * n⁻¹) * (n * pinnedX τ L β d * n⁻¹) := by group
      _ = _ := by
        rw [canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hγ c,
          canonicalRep_mul_pinnedX_mul_inv_of_two h2 w hβ d]
  have hmain : pinnedX τ L (w • γ) a * pinnedX τ L (w • β) b =
      pinnedX τ L (w • γ) c * pinnedX τ L (w • β) d := by
    rw [← hleft, ← hright, h]
  let f : (Fin τ.rank → ℤ) → L := fun δ => if δ = w • γ then a else if δ = w • β then b else 0
  let g : (Fin τ.rank → ℤ) → L := fun δ => if δ = w • γ then c else if δ = w • β then d else 0
  have hmap : (([w • γ, w • β].map fun δ => pinnedX τ L δ (f δ))).prod =
      (([w • γ, w • β].map fun δ => pinnedX τ L δ (g δ))).prod := by
    simpa [f, g, hwne, hwne.symm] using hmain
  have hnd : ([w • γ, w • β] : List (Fin τ.rank → ℤ)).Nodup := by
    simp [hwne]
  have hroot : ∀ α ∈ ([w • γ, w • β] : List (Fin τ.rank → ℤ)),
      IsRoot τ α ∧ 0 < height α := by
    intro α hα
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
    rcases hα with rfl | rfl
    · exact ⟨IsRoot.smul hγ w, hwγ⟩
    · exact ⟨IsRoot.smul hβ w, hwβ⟩
  have hc := pinnedX_list_prod_injective (R := L) [w • γ, w • β] hnd hroot f g hmap
  constructor
  · have := hc (w • γ) (by simp)
    simpa [f, g, hwne, hwne.symm] using this
  · have := hc (w • β) (by simp)
    simpa [f, g, hwne, hwne.symm] using this

theorem j4e_pair_detects
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    {a b : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a)) {j : KernelComponent (rootCharHom a)}
    (hji : j ≠ i)
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer {rootDiagUnit τ b})
    {γ β : Fin τ.rank → ℤ} (hγcomp : γ ∈ componentRoots (rootCharHom a) i)
    (hβcomp : β ∈ componentRoots (rootCharHom a) j)
    (hργ : S.ρ γ = β) (hρβ : S.ρ β = γ) (horth : iform γ β = 0) :
    rootChar b γ = 1 ∧ rootChar b β = 1 := by
  classical
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow (f := 1) S (by rw [hq]; norm_num)
  have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hγr : IsRoot τ γ := hγcomp.1.1
  have hβr : IsRoot τ β := hβcomp.1.1
  obtain ⟨w, hw⟩ := j4e_exists_cubeRoot h2L
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; norm_num at hw
  let ω : Lˣ := Units.mk0 w hw0
  have hωcoe : (ω : L) = w := rfl
  have hω0 : (ω : L) ≠ 0 := by rw [hωcoe]; exact hw0
  have hω2ne : ((ω ^ 2 : Lˣ) : L) ≠ 0 := by
    rw [Units.val_pow_eq_pow_val]
    exact pow_ne_zero 2 hω0
  have hωa : (ω : L) ^ 2 + 1 = (ω : L) := by
    rw [hωcoe]
    have h : w ^ 2 + 1 - w = 0 := by linear_combination hw - w * h2L
    exact sub_eq_zero.1 h
  have hωb : (ω : L) + 1 = (ω : L) ^ 2 := by
    rw [hωcoe]
    have h : w + 1 - w ^ 2 = 0 := by linear_combination hw - w ^ 2 * h2L
    exact sub_eq_zero.1 h
  have hω3 : ω ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hωcoe, Units.val_one]
    have h : w ^ 3 - 1 = (w - 1) * (w ^ 2 + w + 1) := by ring
    rw [hw, mul_zero] at h
    exact sub_eq_zero.1 h
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hω4 : (ω ^ 2) ^ 2 = ω := by
    rw [← pow_mul]
    norm_num
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hω3, one_mul]
  have hβrat : β ∈ rationalRoots S.ρ (rootCharHom a) i := by
    refine ⟨1, γ, hγcomp, ?_⟩
    rw [Function.iterate_one, hργ]
  have hq1 : S.D.q = 2 ^ 1 := by rw [hq]; norm_num
  have hstepα : S.D.step (rootSL2 τ L γ (HSL ω)) = rootSL2 τ L β (HSL (ω ^ 2)) := by
    rw [j4e_step_rootSL2_HSL_swap S hq hγr ω, hργ]
  have hstepβ : S.D.step (rootSL2 τ L β (HSL (ω ^ 2))) = rootSL2 τ L γ (HSL ω) := by
    rw [j4e_step_rootSL2_HSL_swap S hq hβr (ω ^ 2), hρβ, hω4]
  have hstepWα : S.D.step (rootSL2 τ L γ WSL) = rootSL2 τ L β WSL := by
    rw [step_rootSL2_WSL_of_charTwo S hγr, hργ]
  have hstepWβ : S.D.step (rootSL2 τ L β WSL) = rootSL2 τ L γ WSL := by
    rw [step_rootSL2_WSL_of_charTwo S hβr, hρβ]
  have hdR : rootDiagUnit τ (fun k => ω ^ corootPair γ (Pi.single k 1) *
      (ω ^ 2) ^ corootPair β (Pi.single k 1)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    rootDiagUnit_mul_corootPair_mem_rationalComponent_of_step S hτ hq1 hAlg i hγcomp hβrat horth
      (t := ω) (t' := ω ^ 2) (m := 3) (by norm_num) hω3 hω23 hstepα hstepβ hstepWα hstepWβ
  let x : ModGL τ L := rootSL2 τ L γ (HSL ω)
  let y : ModGL τ L := rootSL2 τ L β (HSL (ω ^ 2))
  have hx : x = rootDiagUnit τ (fun k => ω ^ corootPair γ (Pi.single k 1)) :=
    j4e_rootSL2_HSL_eq_rootDiagUnit hγr ω
  have hy : y = rootDiagUnit τ (fun k => (ω ^ 2) ^ corootPair β (Pi.single k 1)) :=
    j4e_rootSL2_HSL_eq_rootDiagUnit hβr (ω ^ 2)
  have hhR : x * y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [hx, hy, ← rootDiagUnit_mul]
    exact hdR
  have hhH : x * y ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    (Subgroup.commutator_le_self (rationalSpan S.ρ S.Γ (rootCharHom a) i)) hhR
  have hneq : (⟦⟨γ, hγcomp.1⟩⟧ : KernelComponent (rootCharHom a)) ≠
      ⟦⟨β, hβcomp.1⟩⟧ := by
    rw [hγcomp.2, hβcomp.2]
    exact Ne.symm hji
  have hcommRoots : ∀ u ∈ rootSubgroup τ L γ, ∀ v ∈ rootSubgroup τ L β, Commute u v :=
    commute_of_mk_ne (τ := τ) (χ := rootCharHom a) (K := L) hneq
  let Xγ : L → ModGL τ L := pinnedX τ L γ
  let Xβ : L → ModGL τ L := pinnedX τ L β
  have hcommXY : Commute (Xγ 1) (Xβ 1) :=
    hcommRoots _ (Subgroup.subset_closure ⟨1, rfl⟩) _
      (Subgroup.subset_closure ⟨1, rfl⟩)
  let e1 : ModGL τ L := Xγ 1 * Xβ 1
  have hγrat : γ ∈ rationalRoots S.ρ (rootCharHom a) i := ⟨0, γ, hγcomp, rfl⟩
  have he1rootSpan : e1 ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    refine mul_mem ?_ ?_
    · exact pinnedX_mem_rootSpan hγrat 1
    · exact pinnedX_mem_rootSpan hβrat 1
  have he1M : e1 ∈ S.D.model := by
    refine ⟨?_, ?_⟩
    · exact mul_mem (pinnedX_mem_adjointGroup γ 1) (pinnedX_mem_adjointGroup β 1)
    · change S.D.step (Xγ 1 * Xβ 1) = Xγ 1 * Xβ 1
      rw [map_mul, j4e_step_pinnedX_of_q_two S hq hγr 1,
        j4e_step_pinnedX_of_q_two S hq hβr 1, hργ, hρβ]
      simpa using hcommXY.eq.symm
  have he1sq : e1 ^ 2 = 1 := by
    have hX : Xγ 1 * Xγ 1 = 1 := by
      rw [← pinnedX_add, show (1 : L) + 1 = 0 by rw [← two_mul, h2L, zero_mul], pinnedX_zero]
    have hY : Xβ 1 * Xβ 1 = 1 := by
      rw [← pinnedX_add, show (1 : L) + 1 = 0 by rw [← two_mul, h2L, zero_mul], pinnedX_zero]
    simp only [e1, pow_two]
    calc (Xγ 1 * Xβ 1) * (Xγ 1 * Xβ 1)
        = Xγ 1 * (Xβ 1 * Xγ 1) * Xβ 1 := by group
      _ = Xγ 1 * (Xγ 1 * Xβ 1) * Xβ 1 := by rw [hcommXY.eq]
      _ = (Xγ 1 * Xγ 1) * (Xβ 1 * Xβ 1) := by group
      _ = 1 := by rw [hX, hY, one_mul]
  have he1Γ : e1 ∈ S.Γ :=
    langModel_mem_Γ_of_sq_mem S hτ hq1 hAlg he1M (by rw [he1sq]; exact one_mem _)
  have he1H : e1 ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := ⟨he1rootSpan, he1Γ⟩
  have hω4L : (((ω : L) ^ 2) ^ 2) = (ω : L) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hω4]
  have hx_self : x * Xγ 1 * x⁻¹ = Xγ (ω ^ 2) := by
    have h := j4e_rootSL2_HSL_conj_pinnedX_self hγr ω 1
    simpa [mul_one] using h
  have hx_orth : ∀ c : L, x * Xβ c * x⁻¹ = Xβ c := fun c =>
    j4e_rootSL2_HSL_conj_pinnedX_of_orthogonal hγr hβr horth ω c
  have horth' : iform β γ = 0 := by rw [iform_comm]; exact horth
  have hy_self : y * Xβ 1 * y⁻¹ = Xβ (ω : L) := by
    have h := j4e_rootSL2_HSL_conj_pinnedX_self hβr (ω ^ 2) 1
    simpa [hω4L, mul_one] using h
  have hy_orth : ∀ c : L, y * Xγ c * y⁻¹ = Xγ c := fun c =>
    j4e_rootSL2_HSL_conj_pinnedX_of_orthogonal hβr hγr horth' (ω ^ 2) c
  have hyconj : y * e1 * y⁻¹ = Xγ 1 * Xβ (ω : L) := by
    rw [show y * e1 * y⁻¹ = (y * Xγ 1 * y⁻¹) * (y * Xβ 1 * y⁻¹) by
      simp only [e1]; group]
    rw [hy_orth, hy_self]
  have hxconj : x * (Xγ 1 * Xβ (ω : L)) * x⁻¹ = Xγ (ω ^ 2) * Xβ (ω : L) := by
    rw [show x * (Xγ 1 * Xβ (ω : L)) * x⁻¹ =
      (x * Xγ 1 * x⁻¹) * (x * Xβ (ω : L) * x⁻¹) by group]
    rw [hx_self, hx_orth]
  have hconj : (x * y) * e1 * (x * y)⁻¹ = Xγ (ω ^ 2) * Xβ (ω : L) := by
    calc (x * y) * e1 * (x * y)⁻¹ = x * (y * e1 * y⁻¹) * x⁻¹ := by group
      _ = x * (Xγ 1 * Xβ (ω : L)) * x⁻¹ := by rw [hyconj]
      _ = Xγ (ω ^ 2) * Xβ (ω : L) := hxconj
  have he1inv : e1⁻¹ = e1 := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact he1sq)
  have hcommEq : ⁅x * y, e1⁆ = Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := by
    rw [commutatorElement_def, hconj, he1inv]
    simp only [e1]
    have hc : Commute (Xβ (ω : L)) (Xγ 1) :=
      (hcommRoots _ (Subgroup.subset_closure ⟨1, rfl⟩) _
        (Subgroup.subset_closure ⟨(ω : L), rfl⟩)).symm
    calc Xγ (ω ^ 2) * Xβ (ω : L) * (Xγ 1 * Xβ 1)
        = Xγ (ω ^ 2) * (Xβ (ω : L) * Xγ 1) * Xβ 1 := by group
      _ = Xγ (ω ^ 2) * (Xγ 1 * Xβ (ω : L)) * Xβ 1 := by rw [hc.eq]
      _ = (Xγ (ω ^ 2) * Xγ 1) * (Xβ (ω : L) * Xβ 1) := by group
      _ = Xγ ((ω : L) ^ 2 + 1) * Xβ ((ω : L) + 1) := by
          rw [← pinnedX_add, ← pinnedX_add]
      _ = Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := by
          rw [hωa, hωb, Units.val_pow_eq_pow_val]
  have hmem : ⁅x * y, e1⁆ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_mem_commutator hhH he1H
  rw [hcommEq] at hmem
  have hdcomm : Commute (rootDiagUnit τ b) (Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L)) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)).symm
  have hfixed : rootDiagUnit τ b * (Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L)) *
      (rootDiagUnit τ b)⁻¹ = Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := by
    rw [hdcomm.eq]
    group
  have hEq : Xγ ((rootChar b γ : L) * (ω : L)) *
      Xβ ((rootChar b β : L) * ((ω ^ 2 : Lˣ) : L)) =
      Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := by
    calc Xγ ((rootChar b γ : L) * (ω : L)) *
          Xβ ((rootChar b β : L) * ((ω ^ 2 : Lˣ) : L))
        = (rootDiagUnit τ b * Xγ (ω : L) * (rootDiagUnit τ b)⁻¹) *
            (rootDiagUnit τ b * Xβ ((ω ^ 2 : Lˣ) : L) * (rootDiagUnit τ b)⁻¹) := by
          rw [rootDiagUnit_conj_pinnedX b hγr (ω : L),
            rootDiagUnit_conj_pinnedX b hβr ((ω ^ 2 : Lˣ) : L)]
      _ = rootDiagUnit τ b * (Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L)) *
            (rootDiagUnit τ b)⁻¹ := by group
      _ = Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := hfixed
  have hlin : LinIndepPair γ β := j4e_linIndepPair_of_orthogonal hγr hβr horth
  have huniq := j4e_pinnedX_mul_injective_of_linIndep h2L hγr hβr hlin hEq
  constructor
  · have hval : (rootChar b γ : L) = 1 := by
      apply mul_right_cancel₀ hω0
      simpa using huniq.1
    exact Units.ext hval
  · have hval : (rootChar b β : L) = 1 := by
      apply mul_right_cancel₀ hω2ne
      simpa using huniq.2
    exact Units.ext hval

end CFSG.StandardType.LangRat

end
