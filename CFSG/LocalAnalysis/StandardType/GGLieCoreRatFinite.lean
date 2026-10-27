module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

private theorem ggLieRatFin_frobenius_pow {L : Type} [Semiring L] {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (k : ℕ) (c : L) : (Fr ^ k) c = c ^ (q ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, ih, hFr, ← pow_mul, pow_succ]

private theorem ggLieRatFin_units_map_entrywiseHom_comp {τ : Tag} {L : Type} [Field L]
    (σ σ' : L →+* L) (g : ModGL τ L) :
    Units.map (entrywiseHom σ) (Units.map (entrywiseHom σ') g) =
      Units.map (entrywiseHom (σ.comp σ')) g := by
  refine Units.ext ?_
  simp only [Units.coe_map]
  exact entrywise_entrywise σ σ' (g : Module.End L (RootModule τ L))

private theorem ggLieRatFin_entrywise_eq_self {τ : Tag} {L : Type} [Field L] (σ : L →+* L)
    {P : ModGL τ L} (hP : IsDiagramTwistMatrix τ L P) :
    Units.map (entrywiseHom σ) P = P := by
  rcases hP with rfl | ⟨t, j, h, rfl⟩
  · simp
  · subst τ
    rw [map_zpow, units_map_entrywiseHom_diagramMap]

private theorem ggLieRatFin_exists_pow_eq_one
    {τ : Tag} {L : Type} [Field L] {P : ModGL τ L} (hP : IsDiagramTwistMatrix τ L P) :
    ∃ m : ℕ, 0 < m ∧ P ^ m = 1 := by
  rcases hP with rfl | ⟨t, j, h, rfl⟩
  · exact ⟨1, Nat.one_pos, one_pow 1⟩
  · subst τ
    refine ⟨t.order, ?_, ?_⟩
    · cases t <;> decide
    · simp only [eqRec_eq_cast, cast_eq]
      rw [← zpow_natCast, ← zpow_mul, zpow_mul', zpow_natCast, diagramMap_pow_order t L,
        one_zpow]

private theorem ggLieRatFin_iterate {τ : Tag} {L : Type} [Field L] (σ : L →+* L)
    {P : ModGL τ L} (hP : Units.map (entrywiseHom σ) P = P) (k : ℕ) (g : ModGL τ L) :
    (fun x : ModGL τ L => P * Units.map (entrywiseHom σ) x * P⁻¹)^[k] g =
      P ^ k * Units.map (entrywiseHom (σ ^ k)) g * (P ^ k)⁻¹ := by
  induction k with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, pow_zero, inv_one, one_mul, mul_one]
    exact (Units.ext (entrywise_id (g : Module.End L (RootModule τ L)))).symm
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [map_mul, map_inv, map_pow, hP, ggLieRatFin_units_map_entrywiseHom_comp,
      pow_succ', RingHom.mul_def]
    group

theorem finite_ratPoints

    {τ : Tag} {L : Type} [Field L] {q : ℕ} (hq : 1 < q)
    {Φ : ModGL τ L →* ModGL τ L} (hΦ : IsSteinbergEndZ τ L q Φ) : Finite ↥(ratPoints Φ) := by
  obtain ⟨Fr, hFr, P, hPmat, hΦeq⟩ := hΦ
  have hPFr : Units.map (entrywiseHom Fr) P = P := ggLieRatFin_entrywise_eq_self Fr hPmat
  obtain ⟨m, hmpos, hPm⟩ := ggLieRatFin_exists_pow_eq_one hPmat
  have hiter : ∀ g : ModGL τ L,
      (fun x : ModGL τ L => P * Units.map (entrywiseHom Fr) x * P⁻¹)^[m] g =
        Units.map (entrywiseHom (Fr ^ m)) g := by
    intro g
    rw [ggLieRatFin_iterate Fr hPFr m g, hPm, one_mul, inv_one, mul_one]
  let R : Set L := {c | c ^ (q ^ m) = c}
  have hRfin : R.Finite := by
    have hNpos : 0 < q ^ m - 1 := by
      have hN : 1 < q ^ m := one_lt_pow' hq (Nat.pos_iff_ne_zero.mp hmpos)
      omega
    refine (Set.finite_singleton (0 : L)).union
      (Finset.finite_toSet (Polynomial.nthRootsFinset (q ^ m - 1) (1 : L))) |>.subset ?_
    intro c hc
    change c ^ (q ^ m) = c at hc
    by_cases h0 : c = 0
    · exact Or.inl h0
    · right
      rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hNpos]
      have h1 : c ^ (q ^ m - 1) * c = c := by
        rw [show q ^ m = (q ^ m - 1) + 1 by omega, pow_succ] at hc
        simpa using hc
      exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h1)
  haveI : Finite R := hRfin
  let f : ↥(ratPoints Φ) → Label τ → Label τ → R := fun g a b =>
    ⟨((g : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b (1 : L)) a, by
      have hgΦ : Φ (g : ModGL τ L) = (g : ModGL τ L) := by
        have hmem := (Subgroup.mem_inf.mp g.2).2
        simpa using hmem
      have hFg : P * Units.map (entrywiseHom Fr) (g : ModGL τ L) * P⁻¹ =
          (g : ModGL τ L) := by
        rw [← hΦeq (g : ModGL τ L)]
        exact hgΦ
      have hfix : (fun x : ModGL τ L => P * Units.map (entrywiseHom Fr) x * P⁻¹)^[m]
          (g : ModGL τ L) = (g : ModGL τ L) := by
        have hk : ∀ k, (fun x : ModGL τ L => P * Units.map (entrywiseHom Fr) x * P⁻¹)^[k]
            (g : ModGL τ L) = (g : ModGL τ L) := by
          intro k
          induction k with
          | zero => rfl
          | succ k ih => rw [Function.iterate_succ_apply', ih]; exact hFg
        exact hk m
      have hunit : Units.map (entrywiseHom (Fr ^ m)) (g : ModGL τ L) = (g : ModGL τ L) := by
        rw [← hiter (g : ModGL τ L)]
        exact hfix
      have hentry : entrywise (Fr ^ m)
          ((g : ModGL τ L) : Module.End L (RootModule τ L)) =
            ((g : ModGL τ L) : Module.End L (RootModule τ L)) := by
        have := congrArg (fun u : ModGL τ L => (u : Module.End L (RootModule τ L))) hunit
        exact this
      have h1 := congrArg (fun A : Module.End L (RootModule τ L) =>
        A (Finsupp.single b (1 : L))) hentry
      have h2 := congrArg (fun v : RootModule τ L => v a) h1
      rw [entrywise_single, Finsupp.mapRange_apply] at h2
      rw [ggLieRatFin_frobenius_pow hFr m
        (((g : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b (1 : L)) a)] at h2
      exact h2⟩
  refine Finite.of_injective f ?_
  intro g₁ g₂ hfg
  have hbasis : ∀ b : Label τ,
      ((g₁ : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b (1 : L)) =
        ((g₂ : ModGL τ L) : Module.End L (RootModule τ L)) (Finsupp.single b (1 : L)) := by
    intro b
    apply Finsupp.ext
    intro a
    have h := congrFun (congrFun hfg a) b
    exact Subtype.ext_iff.mp h
  apply Subtype.ext
  apply Units.ext
  apply Finsupp.lhom_ext
  intro b r
  have hs : Finsupp.single b r = r • (Finsupp.single b (1 : L) : RootModule τ L) := by
    rw [Finsupp.smul_single', mul_one]
  rw [hs, map_smul, map_smul, hbasis b]

end CFSG.StandardType.LieCore
