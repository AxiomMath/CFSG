module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5PSp4A
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Equiv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup CFSG.Quasithin.H13.F431

theorem autStab_normalizer {K : Type} [Group K] {α : MulAut K} {R : Subgroup K}
    (h : AutStab α R) : AutStab α (Subgroup.normalizer (R : Set K)) := by
  intro x
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  have e : ∀ n : K, α x * α n * (α x)⁻¹ = α (x * n * x⁻¹) := by
    intro n
    simp
  constructor
  · intro hx n
    have h1 := hx (α n)
    rw [h n, e n, h] at h1
    exact h1
  · intro hx m
    obtain ⟨n, rfl⟩ := α.surjective m
    rw [h n, e n, h]
    exact hx n

theorem eq_P_of_card
    {H : Subgroup U42.Y} (hB : U42.B0 ≤ H) :
    (Nat.card H = 576 → H = U42.P1) ∧ (Nat.card H = 960 → H = U42.P2) := by
  have h192 := U42.card_B0
  have h576 := U42.card_P1
  have h960 := U42.card_P2
  have hY : Nat.card U42.Y = 25920 := U42.card_Xs
  have htop : Nat.card (⊤ : Subgroup U42.Y) = 25920 := by
    rw [Subgroup.card_top]
    exact hY
  rcases U42.lattice hB with h | h | h | h
  · exact ⟨fun hc => by rw [h] at hc; omega, fun hc => by rw [h] at hc; omega⟩
  · exact ⟨fun _ => h, fun hc => by rw [h] at hc; omega⟩
  · exact ⟨fun hc => by rw [h] at hc; omega, fun _ => h⟩
  · exact ⟨fun hc => by rw [h] at hc; omega, fun hc => by rw [h] at hc; omega⟩

theorem autStab_P1_P2
    {α : MulAut U42.Y} (hα : AutStab α U42.T) :
    AutStab α U42.P1 ∧ AutStab α U42.P2 := by
  have hB : AutStab α U42.B0 := by
    have := autStab_normalizer hα
    rwa [U42.normalizer_T] at this
  have hcard : ∀ P : Subgroup U42.Y, Nat.card (P.comap α.toMonoidHom) = Nat.card P := by
    intro P
    rw [Subgroup.comap_equiv_eq_map_symm']
    exact Subgroup.card_map_of_injective α.symm.injective
  have hle : ∀ P : Subgroup U42.Y, U42.B0 ≤ P → U42.B0 ≤ P.comap α.toMonoidHom :=
    fun P hP b hb => hP ((hB b).2 hb)
  constructor
  · intro x
    have h1 := (eq_P_of_card (hle _ U42.B0_le_P1)).1 (by rw [hcard, U42.card_P1])
    simpa using Subgroup.ext_iff.1 h1 x
  · intro x
    have h1 := (eq_P_of_card (hle _ U42.B0_le_P2)).2 (by rw [hcard, U42.card_P2])
    simpa using Subgroup.ext_iff.1 h1 x

theorem canonFor_T :
    CanonFor U42.T := by
  have hY : Nat.card U42.Y = 25920 := U42.card_Xs
  refine ⟨U42.P1, U42.P2, U42.T_le_B0.trans U42.B0_le_P1, U42.T_le_B0.trans U42.B0_le_P2,
    ?_, ?_, U42.P1_sup_P2, fun α hα => autStab_P1_P2 hα⟩
  · refine lt_top_iff_ne_top.2 fun h => ?_
    have h1 := U42.card_P1
    rw [h, Subgroup.card_top] at h1
    omega
  · refine lt_top_iff_ne_top.2 fun h => ?_
    have h1 := U42.card_P2
    rw [h, Subgroup.card_top] at h1
    omega

theorem sylowCanon_Y :
    SylowCanon U42.Y := by
  intro R hR
  obtain ⟨c, hc⟩ := U42.exists_conj_isSylowTwoOf_top U42.isSylow_T hR
  refine canonFor_of_equiv (MulAut.conj c) ?_ canonFor_T
  intro x
  rw [← hc]
  exact Subgroup.mem_map_iff_mem (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective

theorem asch5_PSp4Three_holds :
    Asch5_PSp4Three := by
  intro L₀ _ _ hL A S hA
  obtain ⟨e₁⟩ := CFSG.ComponentClassification.CatFactsSmall.PSp43.equiv_of_lieModel hL
  let eYL : U42.Y ≃* L₀ := (MulEquiv.subgroupCongr U42.Xs_eq).trans e₁.symm
  have hZY : Subgroup.center U42.Y = ⊥ := (U42.f431ModelFacts_psu U42.Y U42.lieModel_Y).2
  have hZ : Subgroup.center L₀ = ⊥ := by
    rw [← CFSG.ComponentClassification.OuterAutomorphisms.center_map_equiv eYL, hZY,
      Subgroup.map_bot]
  refine exists_overgroups_of_sylowCanon ?_ hA
  intro R₀ hR₀
  let φ : U42.Y ≃* ↥(innAutOf L₀) := eYL.trans (CFSG.Quasithin.H13.P31Sec.innEquiv hZ)
  exact canonFor_of_equiv φ (R := R₀.comap φ.toMonoidHom) (fun x => Iff.rfl)
    (sylowCanon_Y _ (isSylowIn_top_comap_equiv φ hR₀))

end CFSG.LocalAnalysis.WeakClosure81
