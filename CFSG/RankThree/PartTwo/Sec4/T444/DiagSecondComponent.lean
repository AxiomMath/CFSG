module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagSetting

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)


theorem ys03_I02_isComponent_eq_of_le {X : Type} [Group X] [Finite X] {T S : Subgroup X}
    (hT : CFSG.IsComponent T) (hS : CFSG.IsComponent S) (hTS : T ≤ S) : T = S := by
  by_contra hne
  rcases CFSG.LocalCores.distinct_components_commute hT hS with hEq | hcomm
  · exact hne hEq
  · have hTC : T ≤ Subgroup.centralizer (S : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hcomm_T : ∀ x y : T, x * y = y * x := by
      intro x y
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_iff.mp (hTC x.2) (y : X) (hTS y.2)
      simp only [Subgroup.coe_mul]
      exact h1.symm
    rcases hT.1 with ⟨_, _, a, b, hab⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm_T x y])

open scoped commutatorElement in
theorem ys03_I02_le_of_le_sup_commute {X : Type} [Group X] {S E I : Subgroup X}
    (hSE : ∀ s ∈ S, ∀ e ∈ E, s * e = e * s)
    (hIE : ∀ i ∈ I, ∀ e ∈ E, i * e = e * i)
    (hIS : I ≤ S ⊔ E) (hperf : ⁅I, I⁆ = I) : I ≤ S := by
  have hP : ∀ x ∈ S ⊔ E, ∃ s ∈ S, ∃ e ∈ E, x = s * e := by
    let P : Subgroup X :=
      { carrier := {x | ∃ s ∈ S, ∃ e ∈ E, x = s * e}
        mul_mem' := by
          rintro _ _ ⟨s1, hs1, e1, he1, rfl⟩ ⟨s2, hs2, e2, he2, rfl⟩
          refine ⟨s1 * s2, S.mul_mem hs1 hs2, e1 * e2, E.mul_mem he1 he2, ?_⟩
          calc s1 * e1 * (s2 * e2) = s1 * (e1 * s2) * e2 := by group
            _ = s1 * (s2 * e1) * e2 := by rw [hSE s2 hs2 e1 he1]
            _ = s1 * s2 * (e1 * e2) := by group
        one_mem' := ⟨1, S.one_mem, 1, E.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨s, hs, e, he, rfl⟩
          refine ⟨s⁻¹, S.inv_mem hs, e⁻¹, E.inv_mem he, ?_⟩
          rw [hSE s hs e he, mul_inv_rev] }
    have hle : S ⊔ E ≤ P := by
      refine sup_le ?_ ?_
      · intro s hs
        exact ⟨s, hs, 1, E.one_mem, by simp⟩
      · intro e he
        exact ⟨1, S.one_mem, e, he, by simp⟩
    intro x hx
    exact hle hx
  have hinv : ∀ s ∈ S, ∀ e ∈ E, s⁻¹ * e = e * s⁻¹ := by
    intro s hs e he
    calc s⁻¹ * e = s⁻¹ * (e * s) * s⁻¹ := by group
      _ = s⁻¹ * (s * e) * s⁻¹ := by rw [hSE s hs e he]
      _ = e * s⁻¹ := by group
  have hcentral : ∀ x ∈ I, ∀ s ∈ S, ∀ e ∈ E, x = s * e → ∀ e' ∈ E, e * e' = e' * e := by
    intro x hx s hs e he hxse e' he'
    have he_eq : e = s⁻¹ * x := by rw [hxse, ← mul_assoc, inv_mul_cancel, one_mul]
    calc e * e' = s⁻¹ * (x * e') := by rw [he_eq, mul_assoc]
      _ = s⁻¹ * (e' * x) := by rw [hIE x hx e' he']
      _ = (s⁻¹ * e') * x := by rw [mul_assoc]
      _ = (e' * s⁻¹) * x := by rw [hinv s hs e' he']
      _ = e' * (s⁻¹ * x) := by rw [mul_assoc]
      _ = e' * e := by rw [he_eq]
  have hcomm : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ S := by
    intro x hx y hy
    obtain ⟨s1, hs1, e1, he1, hx1⟩ := hP x (hIS hx)
    obtain ⟨s2, hs2, e2, he2, hy2⟩ := hP y (hIS hy)
    have hc12 : e1 * e2 = e2 * e1 := hcentral x hx s1 hs1 e1 he1 hx1 e2 he2
    have hxy : x * y = (s1 * s2) * (e1 * e2) := by
      rw [hx1, hy2]
      calc s1 * e1 * (s2 * e2) = s1 * (e1 * s2) * e2 := by group
        _ = s1 * (s2 * e1) * e2 := by rw [hSE s2 hs2 e1 he1]
        _ = (s1 * s2) * (e1 * e2) := by group
    have hyx : y * x = (s2 * s1) * (e1 * e2) := by
      rw [hx1, hy2]
      calc s2 * e2 * (s1 * e1) = s2 * (e2 * s1) * e1 := by group
        _ = s2 * (s1 * e2) * e1 := by rw [hSE s1 hs1 e2 he2]
        _ = (s2 * s1) * (e2 * e1) := by group
        _ = (s2 * s1) * (e1 * e2) := by rw [hc12]
    have hcomm_eq : ⁅x, y⁆ = (x * y) * (y * x)⁻¹ := by
      rw [commutatorElement_def]
      group
    have hfinal : (x * y) * (y * x)⁻¹ = s1 * s2 * s1⁻¹ * s2⁻¹ := by
      rw [hxy, hyx]
      group
    rw [hcomm_eq, hfinal]
    exact S.mul_mem (S.mul_mem (S.mul_mem hs1 hs2) (S.inv_mem hs1)) (S.inv_mem hs2)
  have hsub : ⁅I, I⁆ ≤ S := Subgroup.commutator_le.mpr fun x hx y hy => hcomm x hx y hy
  rw [hperf] at hsub
  exact hsub

section Certs


theorem ys03_I02_exists_J {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {s : G}
    {L : Subgroup G}
    (hSz : KFacts.KPSz) (hS : SchreierFor CFSG.Assembly.InCatalog) (h45 : Item4_5)
    (h : DiagSetting G A M H s L) :
    ∃ J ∈ thetaComponents 3 G, 3 ∣ Nat.card J ∧ A ≤ Subgroup.normalizer (J : Set G) ∧
      inSubgroup perfectResidual H ≤ Subgroup.normalizer (J : Set G) ∧
      ⁅J, inSubgroup perfectResidual H⁆ = J ∧
      ¬ J.map (starQuot G) ≤ L.map (starQuot G) := by
  by_contra hcon
  have hSc : CFSG.IsComponent (L.map (starQuot G)) :=
    isComponent_map_starQuot h.mem h.three_dvd
  have hmoved_le : ∀ K : Subgroup (G ⧸ CFSG.pPrimeCore 3 G), CFSG.IsComponent K →
      ¬ (inSubgroup perfectResidual H).map (starQuot G) ≤
        Subgroup.centralizer (K : Set (G ⧸ CFSG.pPrimeCore 3 G)) →
      K ≤ L.map (starQuot G) := by
    intro K hK hmov
    obtain ⟨J, hJ, hJK, h3, hA, hI, hc⟩ := exists_thetaComponent_lift_of_moved hSz h45 h hK hmov
    by_contra hKle
    exact hcon ⟨J, hJ, h3, hA, hI, hc, by rw [hJK]; exact hKle⟩
  have hcompT : ∀ T : Subgroup (G ⧸ CFSG.pPrimeCore 3 G), CFSG.IsComponent T →
      T ≠ L.map (starQuot G) →
      (inSubgroup perfectResidual H).map (starQuot G) ≤
        Subgroup.centralizer (T : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    intro T hT hTS
    by_contra hmov
    exact hTS (ys03_I02_isComponent_eq_of_le hT hSc (hmoved_le T hT hmov))
  obtain ⟨hEC, hlayer⟩ := CFSG.WholeGroup.layer_eq_sup_others hSc
  have hIS := DiagSetting.I_le_layer hSz hS h45 h
  rw [hlayer] at hIS
  set E := sSup {T : Subgroup (G ⧸ CFSG.pPrimeCore 3 G) | CFSG.IsComponent T ∧
    T ≠ L.map (starQuot G)} with hE_def
  have hEI : E ≤ Subgroup.centralizer
      ((inSubgroup perfectResidual H).map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
    rw [hE_def]
    refine sSup_le fun T hT => ?_
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro i hi
    exact ((Subgroup.mem_centralizer_iff.mp (hcompT T hT.1 hT.2 hi)) t ht).symm
  have hSE : ∀ s ∈ L.map (starQuot G), ∀ e ∈ E, s * e = e * s := fun s hs e he =>
    (Subgroup.mem_centralizer_iff.mp (hEC he)) s hs
  have hIE : ∀ i ∈ (inSubgroup perfectResidual H).map (starQuot G), ∀ e ∈ E, i * e = e * i :=
    fun i hi e he => (Subgroup.mem_centralizer_iff.mp (hEI he)) i hi
  have hperf : ⁅(inSubgroup perfectResidual H).map (starQuot G),
      (inSubgroup perfectResidual H).map (starQuot G)⁆ =
        (inSubgroup perfectResidual H).map (starQuot G) := by
    rw [← Subgroup.map_commutator, DiagSetting.commutator_I_eq H]
  exact h.I_not_le (ys03_I02_le_of_le_sup_commute hSE hIE hIS hperf)

end Certs

end CFSG.RankThree.PartTwo.Sec4

end
