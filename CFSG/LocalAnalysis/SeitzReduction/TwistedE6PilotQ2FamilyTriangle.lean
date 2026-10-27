module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotQ2FamilyPair
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSwapParam

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore perfectCore_le perfectCore_perfect le_perfectCore_of_perfect)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Conj

variable {G M : Type*} [Group G] [Group M]

@[expose] def QCover.IsConj (c c' : QCover G M) (g : G) (n : M) : Prop :=
  ∀ y (hy : y ∈ c.E), ∃ hy' : g * y * g⁻¹ ∈ c'.E, c'.p ⟨g * y * g⁻¹, hy'⟩ = n * c.p ⟨y, hy⟩ * n⁻¹

theorem QCover.TwistOn.conj {c₁ c₂ c₁' c₂' : QCover G M} {Q : Subgroup G} {ε : M →* M}
    (h : c₁.TwistOn c₂ Q ε) {g : G} {n : M} (h₁ : c₁.IsConj c₁' g n) (h₂ : c₂.IsConj c₂' g n)
    (hε : ∀ x, ε (n * x * n⁻¹) = n * ε x * n⁻¹) :
    c₁'.TwistOn c₂' (Q.map (MulAut.conj g).toMonoidHom) ε := by
  obtain ⟨hQ, hQ', h⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact (h₁ y (hQ hy)).1
  · rintro _ ⟨y, hy, rfl⟩
    exact (h₂ y (hQ' hy)).1
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨hy₁, e₁⟩ := h₁ y (hQ hy)
    obtain ⟨hy₂, e₂⟩ := h₂ y (hQ' hy)
    change c₂'.p ⟨g * y * g⁻¹, _⟩ = ε (c₁'.p ⟨g * y * g⁻¹, _⟩)
    rw [e₂, e₁, h y hy, hε]

theorem map_conj_perfectCore_inf_centralizer [Finite G] (g : G) (X Y : Subgroup G) :
    (perfectCore (centralizer (X : Set G) ⊓ centralizer (Y : Set G))).map
        (MulAut.conj g).toMonoidHom =
      perfectCore (centralizer ((X.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ⊓
        centralizer ((Y.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) := by
  rw [CFSG.Quasithin.map_perfectCore, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
    ← centralizer_map_mulAut_ovl, ← centralizer_map_mulAut_ovl]

theorem map_conj_mul {N : Type*} [Group N] (H : Subgroup N) (a b : N) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun x => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end Conj

section Data


variable {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def triN2 (σ : K →+* K) : graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨twistedE6RelWeyl K triWord2, twistedE6RelWeyl_mem σ triWord2⟩

@[expose] noncomputable def triN3 (σ : K →+* K) : graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨twistedE6RelWeyl K triWord3, twistedE6RelWeyl_mem σ triWord3⟩

theorem ovlRoot_eq_tri :
    ovlRoot 2 = triRootA4 ∧ ovlRoot 1 = triRootG3 ∧ ovlRoot 0 = triRootEps := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> fin_cases i <;> rfl

theorem map_conj_inv_eq_of_map_conj_eq {M : Type*} [Group M] {H H' : Subgroup M} {n : M}
    (h : H.map (MulAut.conj n).toMonoidHom = H') : H'.map (MulAut.conj n⁻¹).toMonoidHom = H := by
  rw [← h, Subgroup.map_map, conj_inv_comp_conj, Subgroup.map_id]

variable {k : Type} [Field k] (ι : k →+* K) {A : Subgroup (ModGL TwistTag.E6.tag K)}
  (hA : A ≤ thetaRankOneGroup ι)

include hA in
theorem triN2_facts (σ : K →+* K) :
    A.map (MulAut.conj (triN2 σ : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
        TwistedE6Pilot.rootRankOneGroup ι (ovlRoot 2) ∧
      A.map (MulAut.conj (triN2 σ : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤
        TwistedE6Pilot.rootRankOneGroup ι (ovlRoot 0) := by
  obtain ⟨⟨t2, t2'⟩, -, ⟨e2, e2'⟩, -⟩ := triTransport_check
  obtain ⟨h2', -, h0'⟩ := ovlRoot_eq_tri
  have hrE := isRoot_of_triRootB triIsRoot_check.2.2.1
  refine ⟨?_, ?_⟩
  · rw [h2']
    exact map_conj_le_rootRankOneGroup_tri hA triWord2 t2 t2'
  · rw [h0', ← map_conj_inv_eq_of_map_conj_eq (map_conj_rootRankOneGroup_tri ι triWord2 hrE e2 e2'),
      ← thetaRankOneGroup_eq_rootRankOneGroup_tri]
    exact Subgroup.map_mono hA

include hA in
theorem triN3_facts (σ : K →+* K) :
    A.map (MulAut.conj (triN3 σ : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
        TwistedE6Pilot.rootRankOneGroup ι (ovlRoot 1) ∧
      A.map (MulAut.conj (triN3 σ : ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤
        TwistedE6Pilot.rootRankOneGroup ι (ovlRoot 0) := by
  obtain ⟨-, ⟨t3, t3'⟩, -, ⟨e3, e3'⟩, -⟩ := triTransport_check
  obtain ⟨-, h1', h0'⟩ := ovlRoot_eq_tri
  have hrE := isRoot_of_triRootB triIsRoot_check.2.2.1
  refine ⟨?_, ?_⟩
  · rw [h1']
    exact map_conj_le_rootRankOneGroup_tri hA triWord3 t3 t3'
  · rw [h0', ← map_conj_inv_eq_of_map_conj_eq (map_conj_rootRankOneGroup_tri ι triWord3 hrE e3 e3'),
      ← thetaRankOneGroup_eq_rootRankOneGroup_tri]
    exact Subgroup.map_mono hA

include hA in
theorem triN23_facts (σ : K →+* K) :
    A.map (MulAut.conj (((triN2 σ)⁻¹ * triN3 σ : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K)).toMonoidHom ≤ TwistedE6Pilot.rootRankOneGroup ι (ovlRoot 2) ∧
      A.map (MulAut.conj (((triN2 σ)⁻¹ * triN3 σ : graphFixedRootGroup TwistTag.E6 K σ) :
        ModGL TwistTag.E6.tag K)⁻¹).toMonoidHom ≤
          TwistedE6Pilot.rootRankOneGroup ι (ovlRoot 2) := by
  obtain ⟨⟨t2, t2'⟩, ⟨t3, t3'⟩, -, -, ⟨a2, a2'⟩, -, ⟨a3, a3'⟩, -⟩ := triTransport_check
  obtain ⟨h2', h1', -⟩ := ovlRoot_eq_tri
  have hrA4 := isRoot_of_triRootB triIsRoot_check.1
  have hN2 := triN2_facts ι hA σ
  have hN3 := triN3_facts ι hA σ
  have hJ2 : (TwistedE6Pilot.rootRankOneGroup ι triRootA4).map
      (MulAut.conj (triN2 σ : ModGL TwistTag.E6.tag K)).toMonoidHom =
        TwistedE6Pilot.rootRankOneGroup ι triRootG3 :=
    map_conj_rootRankOneGroup_tri ι triWord2 hrA4 a2 a2'
  have hJ3 : (TwistedE6Pilot.rootRankOneGroup ι triRootA4).map
      (MulAut.conj (triN3 σ : ModGL TwistTag.E6.tag K)).toMonoidHom =
        TwistedE6Pilot.rootRankOneGroup ι triRootA4 :=
    map_conj_rootRankOneGroup_tri ι triWord3 hrA4 a3 a3'
  refine ⟨?_, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, map_conj_mul, h2',
      ← map_conj_inv_eq_of_map_conj_eq hJ2]
    refine Subgroup.map_mono ?_
    rw [← h1']
    exact hN3.1
  · rw [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, map_conj_mul, h2',
      ← map_conj_inv_eq_of_map_conj_eq hJ3]
    refine Subgroup.map_mono ?_
    rw [← h2']
    exact hN2.1

end Data

section ConjCovers

variable
  {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {σ : K →+* K}

theorem highCover_isConj (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (m : graphFixedRootGroup TwistTag.E6 K σ) :
    (highCover h2 Φ hΦ).IsConj (nbCover e h2 Φ hΦ m) (nbElt e m) (m : ModGL TwistTag.E6.tag K) := by
  rintro _ ⟨B, rfl⟩
  refine ⟨⟨B, rfl⟩, ?_⟩
  have h1 := QCover.ofParam_p' (nbParam e Φ m) (nbModel h2 m) (ker_nbParam_le e h2 Φ hΦ m)
    (ker_nbModel_le h2 m) (x := B) rfl ⟨B, rfl⟩
  have h3 := QCover.ofParam_p' Φ (realize h2) (hΦ.trans (center_le_ker_realize h2))
    (ker_realize_le_center' h2) (x := B) rfl ⟨B, rfl⟩
  exact h1.trans (congrArg (fun x => (m : ModGL TwistTag.E6.tag K) * x *
    (m : ModGL TwistTag.E6.tag K)⁻¹) h3.symm)

theorem nbCover_isConj (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (h2 : (2 : K) = 0)
    (Φ : SpecialLinearGroup (Fin 6) K →* G) (hΦ : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) K))
    (a b : graphFixedRootGroup TwistTag.E6 K σ) :
    (nbCover e h2 Φ hΦ b).IsConj (nbCover e h2 Φ hΦ (a * b)) (nbElt e a)
      (a : ModGL TwistTag.E6.tag K) := by
  rintro _ ⟨B, rfl⟩
  have hab : nbElt e a * nbParam e Φ b B * (nbElt e a)⁻¹ = nbParam e Φ (a * b) B := by
    change ((e.symm a : L) : G) * (((e.symm b : L) : G) * Φ B * ((e.symm b : L) : G)⁻¹) *
      ((e.symm a : L) : G)⁻¹ = ((e.symm (a * b) : L) : G) * Φ B * ((e.symm (a * b) : L) : G)⁻¹
    rw [map_mul, L.coe_mul]
    group
  refine ⟨⟨B, hab.symm⟩, ?_⟩
  have h1 := QCover.ofParam_p' (nbParam e Φ (a * b)) (nbModel h2 (a * b))
    (ker_nbParam_le e h2 Φ hΦ (a * b)) (ker_nbModel_le h2 (a * b)) hab.symm ⟨B, hab.symm⟩
  have h3 := QCover.ofParam_p' (nbParam e Φ b) (nbModel h2 b) (ker_nbParam_le e h2 Φ hΦ b)
    (ker_nbModel_le h2 b) (x := B) rfl ⟨B, rfl⟩
  refine h1.trans (Eq.trans ?_ (congrArg (fun x => (a : ModGL TwistTag.E6.tag K) * x *
    (a : ModGL TwistTag.E6.tag K)⁻¹) h3.symm))
  change ((a * b : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K) * realize h2 B *
      ((a * b : graphFixedRootGroup TwistTag.E6 K σ) : ModGL TwistTag.E6.tag K)⁻¹ =
    (a : ModGL TwistTag.E6.tag K) * ((b : ModGL TwistTag.E6.tag K) * realize h2 B *
      (b : ModGL TwistTag.E6.tag K)⁻¹) * (a : ModGL TwistTag.E6.tag K)⁻¹
  rw [Subgroup.coe_mul]
  group

end ConjCovers

section Twists


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

abbrev triOverlap {σ : K →+* K} (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (A : Subgroup (ModGL TwistTag.E6.tag K)) (a b : ModGL TwistTag.E6.tag K) : Subgroup G :=
  perfectCore (centralizer (modelToG e (A.map (MulAut.conj a).toMonoidHom) : Set G) ⊓
    centralizer (modelToG e (A.map (MulAut.conj b).toMonoidHom) : Set G))

theorem twistOn_pair_n23 [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 3) (h2 : (2 : K) = 0)
    (hX : FieldCoverParamX σ h2 e t (modelToG e A)) :
    (nbCover e h2 hX.Φ hX.ker_le (triN2 σ)).TwistOn (nbCover e h2 hX.Φ hX.ker_le (triN3 σ))
        (triOverlap e A (triN2 σ : ModGL TwistTag.E6.tag K) (triN3 σ : ModGL TwistTag.E6.tag K))
        (MonoidHom.id _) ∨
      (nbCover e h2 hX.Φ hX.ker_le (triN2 σ)).TwistOn (nbCover e h2 hX.Φ hX.ker_le (triN3 σ))
        (triOverlap e A (triN2 σ : ModGL TwistTag.E6.tag K) (triN3 σ : ModGL TwistTag.E6.tag K))
        (twistHom TwistTag.E6 K σ) := by
  set m := (triN2 σ)⁻¹ * triN3 σ with hm
  obtain ⟨hm1, hm2⟩ := triN23_facts (algebraMap k K) hAJ σ
  have hc₁ := highCover_isConj e h2 hX.Φ hX.ker_le (triN2 σ)
  have hc₂ := nbCover_isConj e h2 hX.Φ hX.ker_le (triN2 σ) m
  have hn : triN2 σ * m = triN3 σ := by rw [hm, mul_inv_cancel_left]
  rw [hn] at hc₂
  have hQ : (perfectCore (centralizer (modelToG e A : Set G) ⊓
      centralizer (modelToG e (A.map (MulAut.conj (m : ModGL TwistTag.E6.tag K)).toMonoidHom) :
        Set G))).map (MulAut.conj (nbElt e (triN2 σ))).toMonoidHom =
      triOverlap e A (triN2 σ : ModGL TwistTag.E6.tag K) (triN3 σ : ModGL TwistTag.E6.tag K) := by
    have hn' : (triN2 σ : ModGL TwistTag.E6.tag K) * (m : ModGL TwistTag.E6.tag K) =
        (triN3 σ : ModGL TwistTag.E6.tag K) := by rw [← Subgroup.coe_mul, hn]
    rw [map_conj_perfectCore_inf_centralizer, ← modelToG_map_conj, ← modelToG_map_conj,
      ← map_conj_mul, hn', triOverlap]
  have hF : ∀ x, twistHom TwistTag.E6 K σ ((triN2 σ : ModGL TwistTag.E6.tag K) * x *
      (triN2 σ : ModGL TwistTag.E6.tag K)⁻¹) = (triN2 σ : ModGL TwistTag.E6.tag K) *
        twistHom TwistTag.E6 K σ x * (triN2 σ : ModGL TwistTag.E6.tag K)⁻¹ := fun x => by
    rw [map_mul, map_mul, map_inv, twistHom_coe_C0]
  rcases twistOn_high_nbCover hk hK hσ e hAJ hA h2 hX m 2 2 hm1 hm2 with h | h
  · left
    rw [← hQ]
    exact h.conj hc₁ hc₂ fun x => rfl
  · right
    rw [← hQ]
    exact h.conj hc₁ hc₂ hF

end Twists

section Aligned


variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {k K : Type} [Field k] [Field K]
  [Algebra k K]

theorem twistHom_twistHom_E6 {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    (g : ModGL TwistTag.E6.tag K) :
    twistHom TwistTag.E6 K σ (twistHom TwistTag.E6 K σ g) = g := by
  rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp]
  have hσ1 : σ.comp σ = RingHom.id K := RingHom.ext hσσ
  have hid : Units.map (entrywiseHom (RingHom.id K)) g = g := Units.ext (entrywise_id _)
  rw [hσ1, hid]
  have hP2 : diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 K
    rwa [show TwistTag.E6.order = 2 from rfl, pow_two] at h
  calc diagramMap TwistTag.E6 K * (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
        (diagramMap TwistTag.E6 K)⁻¹ =
      (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K) * g *
        (diagramMap TwistTag.E6 K * diagramMap TwistTag.E6 K)⁻¹ := by group
    _ = g := by rw [hP2]; group

noncomputable abbrev tripleCoreModel [CharP K 2] (h2 : (2 : K) = 0) :
    Subgroup (ModGL TwistTag.E6.tag K) :=
  (LinearPilot.blockSpecialLinear (K := K) ({0, 5} : Finset (Fin 6))).map (realize h2)

theorem tripleCoreModel_le_ovlLevi [CharP K 2] (h2 : (2 : K) = 0) {p : Fin 3} (hp : p ≠ 0) :
    tripleCoreModel h2 ≤ ovlLevi h2 p :=
  Subgroup.map_mono (LinearPilot.blockSpecialLinear_mono (by revert p; decide))

theorem tripleCoreModel_perfect [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (h2 : (2 : K) = 0) :
    ⁅tripleCoreModel h2, tripleCoreModel h2⁆ = tripleCoreModel h2 := by
  have hP := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  have e := LinearPilot.blockSpecialLinearEquivOfCardTwo (K := K)
    (I := ({0, 5} : Finset (Fin 6))) (by decide)
  have hB : ⁅LinearPilot.blockSpecialLinear (K := K) ({0, 5} : Finset (Fin 6)),
      LinearPilot.blockSpecialLinear (K := K) ({0, 5} : Finset (Fin 6))⁆ =
        LinearPilot.blockSpecialLinear (K := K) ({0, 5} : Finset (Fin 6)) := by
    have : Group.IsPerfect (LinearPilot.blockSpecialLinear (K := K) ({0, 5} : Finset (Fin 6))) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Subgroup.isPerfect_iff.1 this
  rw [← Subgroup.map_commutator, hB]

theorem unitaryTwist_transvection_zero_five [CharP K 2] (σ : K →+* K) (h2 : (2 : K) = 0) (c : K) :
    unitaryTwist σ (SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) c) =
      SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) (σ c) := by
  change graphSL K (Matrix.SpecialLinearGroup.map σ _) = _
  rw [map_transvection, graphSL_transvection h2]

theorem exists_triangle_elt [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (h2 : (2 : K) = 0)
    (hX : FieldCoverParamX σ h2 e t (modelToG e A)) :
    ∃ y : G, ∃ hyE : y ∈ (highCover h2 hX.Φ hX.ker_le).E,
      y ∈ perfectCore (centralizer (modelToG e A : Set G) ⊓ centralizer (modelToG e
        (A.map (MulAut.conj (triN2 σ : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)) ∧
      y ∈ perfectCore (centralizer (modelToG e A : Set G) ⊓ centralizer (modelToG e
        (A.map (MulAut.conj (triN3 σ : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)) ∧
      y ∈ triOverlap e A (triN2 σ : ModGL TwistTag.E6.tag K) (triN3 σ : ModGL TwistTag.E6.tag K) ∧
      twistHom TwistTag.E6 K σ ((highCover h2 hX.Φ hX.ker_le).p ⟨y, hyE⟩) ≠
        (highCover h2 hX.Φ hX.ker_le).p ⟨y, hyE⟩ := by
  have hK4 : 4 ≤ Nat.card K := by rw [hK]; norm_num
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have hι : ∀ c, σ (algebraMap k K c) = algebraMap k K c :=
    E6GraphLevi.fixed_algebraMap (sigma_eq_pow_card (f := 1) (by rw [hk]; rfl) hσ)
  obtain ⟨hN2, -⟩ := triN2_facts (algebraMap k K) hAJ σ
  obtain ⟨hN3, -⟩ := triN3_facts (algebraMap k K) hAJ σ
  have hY2D := hN2.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι 2)
  have hY3D := hN3.trans (rootRankOneGroup_ovlRoot_le_su6Levi hι 1)
  obtain ⟨s, hs, -⟩ := QCover.exists_isSection_ofParam hX.Φ (realize h2)
    (hX.ker_le.trans (center_le_ker_realize h2)) (ker_realize_le_center' h2)
    (realize_comp_blockSL_injective h2 2) (H := tripleCoreModel h2)
    (tripleCoreModel_le_ovlLevi h2 (by decide))
  have hs' : (highCover h2 hX.Φ hX.ker_le).IsSection s := hs
  have hperf := tripleCoreModel_perfect hK4 h2
  have hEX : (highCover h2 hX.Φ hX.ker_le).E ≤ centralizer (modelToG e A : Set G) := by
    rw [show (highCover h2 hX.Φ hX.ker_le).E = centralizerPerfectCore (modelToG e A) from
      hX.range_eq]
    exact F4Pilot.centralizerPerfectCore_le_centralizer _
  have hC : ∀ (p : Fin 3) (hp : p ≠ 0) {Y : Subgroup (ModGL TwistTag.E6.tag K)},
      Y ≤ TwistedE6Pilot.rootRankOneGroup (algebraMap k K) (ovlRoot p) → Y ≤ su6Levi σ →
        ∀ h, s h ∈ centralizer (modelToG e Y : Set G) := by
    intro p hp Y hYJ hYD h
    refine hs'.mem_centralizer hperf (X := modelToG e Y)
      (fun x hx => (mem_highCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 hYD hx).1)
      (fun x hx h' => ?_) h
    have h1 := (mem_highCover_of_mem_modelToG hK hσ e h2 hX.Φ hX.ker_le hX.N1 hYD hx).2
    exact mem_centralizer_iff.1 ((ovlLevi_le_centralizer_rootRankOneGroup h2 p (algebraMap k K))
      (tripleCoreModel_le_ovlLevi h2 hp h'.2)) _ (hYJ h1)
  have hrange : ⁅s.range, s.range⁆ = s.range := range_perfect_of_perfect hperf s
  obtain ⟨ω, hω0, hω1⟩ := CFSG.ClassicalModels.exists_ne_zero_sq_ne_one_of_four_le_card K hK4
  have hωσ : σ ω ≠ ω := by
    intro h
    rw [hσ, pow_one] at h
    apply hω1
    have : ω = 1 := by
      have h' : ω * (ω - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h, sub_self]
      rcases mul_eq_zero.1 h' with h0 | h0
      · exact absurd h0 hω0
      · exact sub_eq_zero.1 h0
    rw [this, one_pow]
  set B := SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) ω with hB
  have hBT : B ∈ LinearPilot.blockSpecialLinear (K := K) ({0, 5} : Finset (Fin 6)) :=
    LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) ω
  set h₀ : tripleCoreModel h2 := ⟨realize h2 B, B, hBT, rfl⟩ with hh₀
  refine ⟨s h₀, hs'.mem h₀, ?_, ?_, ?_, ?_⟩
  · refine le_perfectCore_of_perfect (le_inf ?_ ?_) hrange ⟨h₀, rfl⟩
    · rintro _ ⟨h, rfl⟩
      exact hEX (hs'.mem h)
    · rintro _ ⟨h, rfl⟩
      exact hC 2 (by decide) hN2 hY2D h
  · refine le_perfectCore_of_perfect (le_inf ?_ ?_) hrange ⟨h₀, rfl⟩
    · rintro _ ⟨h, rfl⟩
      exact hEX (hs'.mem h)
    · rintro _ ⟨h, rfl⟩
      exact hC 1 (by decide) hN3 hY3D h
  · refine le_perfectCore_of_perfect (le_inf ?_ ?_) hrange ⟨h₀, rfl⟩
    · rintro _ ⟨h, rfl⟩
      exact hC 2 (by decide) hN2 hY2D h
    · rintro _ ⟨h, rfl⟩
      exact hC 1 (by decide) hN3 hY3D h
  · rw [hs'.p_apply h₀, hh₀]
    change twistHom TwistTag.E6 K σ (realize h2 B) ≠ realize h2 B
    rw [E6GraphLevi.twistHom_realize σ h2, hB, unitaryTwist_transvection_zero_five σ h2]
    intro h
    have hBT' : SpecialLinearGroup.transvection (show (0 : Fin 6) ≠ 5 by decide) (σ ω) ∈
        LinearPilot.blockSpecialLinear (K := K) (ovlSet 2) :=
      LinearPilot.transvection_mem_blockSpecialLinear _ (by decide) (by decide) _
    have hBT2 : B ∈ LinearPilot.blockSpecialLinear (K := K) (ovlSet 2) :=
      LinearPilot.blockSpecialLinear_mono (by decide) hBT
    have h1 := realize_comp_blockSL_injective h2 2 (a₁ := ⟨_, hBT'⟩) (a₂ := ⟨_, hBT2⟩) h
    have h3 := congrArg (fun x : LinearPilot.blockSpecialLinear (K := K) (ovlSet 2) =>
      ((x : SpecialLinearGroup (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) 0 5) h1
    simp only [hB, SpecialLinearGroup.transvection_coe, Matrix.add_apply, Matrix.single_apply_same,
      Matrix.one_apply_ne (show (0 : Fin 6) ≠ 5 by decide), zero_add] at h3
    exact hωσ h3

theorem exists_aligned_covers [Finite K] [CharP K 2] (hk : Nat.card k = 2)
    (hK : Nat.card K = (2 ^ 1) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ 1)
    (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) {t : G} {A : Subgroup (ModGL TwistTag.E6.tag K)}
    (hAJ : A ≤ thetaRankOneGroup (algebraMap k K)) (hA : Nat.card A = 3) (h2 : (2 : K) = 0)
    (hX : FieldCoverParamX σ h2 e t (modelToG e A)) (hσσ : ∀ c, σ (σ c) = c) :
    ∃ c₂ c₃ : QCover G (ModGL TwistTag.E6.tag K),
      (c₂ = nbCover e h2 hX.Φ hX.ker_le (triN2 σ) ∨
        c₂ = nbCoverF e h2 hX.Φ hX.ker_le hσσ (triN2 σ)) ∧
      (c₃ = nbCover e h2 hX.Φ hX.ker_le (triN3 σ) ∨
        c₃ = nbCoverF e h2 hX.Φ hX.ker_le hσσ (triN3 σ)) ∧
      (highCover h2 hX.Φ hX.ker_le).TwistOn c₂
        (perfectCore (centralizer (modelToG e A : Set G) ⊓ centralizer (modelToG e
          (A.map (MulAut.conj (triN2 σ : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)))
        (MonoidHom.id _) ∧
      (highCover h2 hX.Φ hX.ker_le).TwistOn c₃
        (perfectCore (centralizer (modelToG e A : Set G) ⊓ centralizer (modelToG e
          (A.map (MulAut.conj (triN3 σ : ModGL TwistTag.E6.tag K)).toMonoidHom) : Set G)))
        (MonoidHom.id _) ∧
      c₂.TwistOn c₃ (triOverlap e A (triN2 σ : ModGL TwistTag.E6.tag K)
        (triN3 σ : ModGL TwistTag.E6.tag K)) (MonoidHom.id _) := by
  obtain ⟨y, hyE, hy₁₂, hy₁₃, hy₂₃, hFy⟩ := exists_triangle_elt hk hK hσ e hAJ h2 hX
  obtain ⟨hm2, hm2'⟩ := triN2_facts (algebraMap k K) hAJ σ
  obtain ⟨hm3, hm3'⟩ := triN3_facts (algebraMap k K) hAJ σ
  have h₁₂ := twistOn_high_nbCover hk hK hσ e hAJ hA h2 hX (triN2 σ) 2 0 hm2 hm2'
  have h₁₃ := twistOn_high_nbCover hk hK hσ e hAJ hA h2 hX (triN3 σ) 1 0 hm3 hm3'
  have h₂₃ := twistOn_pair_n23 hk hK hσ e hAJ hA h2 hX
  obtain ⟨c₂, c₃, hc₂, hc₃, a₁₂, a₁₃, a₂₃⟩ := QCover.exists_aligned_triangle
    (twistHom_twistHom_E6 hσσ) (twistOn_nbCover_nbCoverF e h2 hX.Φ hX.ker_le hσσ (triN2 σ))
    (twistOn_nbCover_nbCoverF e h2 hX.Φ hX.ker_le hσσ (triN3 σ)) h₁₂ h₁₃ h₂₃ hy₁₂ hy₁₃ hy₂₃ hyE hFy
  exact ⟨c₂, c₃, hc₂, hc₃, a₁₂, a₁₃, a₂₃⟩

end Aligned

end CFSG.SeitzReduction.TwistedE6Pilot
