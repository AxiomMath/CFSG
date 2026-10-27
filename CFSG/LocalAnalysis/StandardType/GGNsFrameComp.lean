module

public import CFSG.LocalAnalysis.StandardType.GGNsFrameCompBasic

public section

namespace CFSG.StandardType

namespace NsFrameComp

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCUnitary
open scoped commutatorElement

section Helpers

variable {f n : ℕ} {K : Type} [Field K]

theorem lin_mem_primaryComponent {x y : ↥(unitarySU 2 f K n)} (hy : y ∈ Subgroup.centralizer {x})
    {c : K[X]} {v : Fin n → K}
    (hv : v ∈ primaryComponent ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) c) :
    lin y v ∈ primaryComponent ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) c := by
  have h1 : y * x = x * y := Subgroup.mem_centralizer_singleton_iff.mp hy
  have hc : Commute (lin y) ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) := by
    rw [coe_toUnitHom, Commute, SemiconjBy, ← lin_mul, ← lin_mul, h1]
  exact apply_mem_primaryComponent hc hv

theorem lin_mul_inv_apply (y : ↥(unitarySU 2 f K n)) (v : Fin n → K) : lin y (lin y⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← lin_mul, mul_inv_cancel, lin_one]
  rfl

theorem lin_commutator_apply {x y y' : ↥(unitarySU 2 f K n)} (hy : y ∈ Subgroup.centralizer {x})
    (hy' : y' ∈ Subgroup.centralizer {x}) {c : K[X]}
    (hcomm : ∀ w ∈ primaryComponent ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) c, lin y (lin y' w) = lin y' (lin y w))
    {v : Fin n → K}
    (hv : v ∈ primaryComponent ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)) c) : lin ⁅y, y'⁆ v = v := by
  have hw := lin_mem_primaryComponent (Subgroup.inv_mem _ hy') hv
  have hu := lin_mem_primaryComponent (Subgroup.inv_mem _ hy) hw
  rw [commutatorElement_def, lin_mul, lin_mul, lin_mul, Module.End.mul_apply, Module.End.mul_apply,
    Module.End.mul_apply, hcomm _ hu, lin_mul_inv_apply, lin_mul_inv_apply]

theorem three_lt_of_bad {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ f + 1) {m d : ℕ}
    (hbad : (m, 2 ^ (f * d)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))) : 3 < p := by
  have hQ : 2 ^ (f * d) = 2 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hbad
    rcases hbad with ⟨-, h2⟩ | ⟨-, h3⟩ | ⟨-, h2⟩
    · exact h2
    · exfalso
      rcases Nat.eq_zero_or_pos (f * d) with h0 | hpos
      · rw [h0, pow_zero] at h3
        omega
      · have h2d : (2 : ℕ) ∣ 2 ^ (f * d) := dvd_pow_self 2 hpos.ne'
        rw [h3] at h2d
        omega
    · exact h2
  have hfd : f * d = 1 := Nat.pow_right_injective (le_refl 2) (hQ.trans (pow_one 2).symm)
  have hf : f = 1 := Nat.eq_one_of_mul_eq_one_right hfd
  subst hf
  have h3 : p ≠ 3 := fun h => hpq (by rw [h]; norm_num)
  have := hp.two_le
  omega

end Helpers

section Classification

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {x : ↥(unitarySU 2 f K n)} {G : Type} [Group G] {φ : ↥(unitarySU 2 f K n) →* G}

theorem map_sb_normal (a : K[X]) :
    (((sb h x a).map φ).subgroupOf ((Subgroup.centralizer {x}).map φ)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono sb_le_centralizer)]
  rintro _ _ ⟨j, hj, rfl⟩ ⟨c, hc, rfl⟩
  exact ⟨c * j * c⁻¹, conj_mem_sb hc hj, by rw [map_mul, map_mul, map_inv]⟩

variable (h) in
@[expose] def nonExc (x : ↥(unitarySU 2 f K n)) : Set K[X] :=
  {c | ∀ hc : c ∈ primaryFactors ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)),
    IsGoodBlock h (toUnitHom x) ⟨c, hc⟩ ∨
      primaryMultiplicity ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
        Module.End K (Fin n → K)) c ≤ 1}

theorem exists_eq_map_sb_of_isComponentOf [Finite K] [Finite G] (hker : SURep.GGFrameKer φ)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ 2 ^ f + 1) (hx : x ^ p = 1) {L₁ : Subgroup G}
    (hL : CFSG.Assembly.IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer {φ x}))
    (hpL : p ∣ Nat.card L₁) :
    ∃ a : primaryFactors ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
      Module.End K (Fin n → K)), IsGoodBlock h (toUnitHom x) a ∧ L₁ = (sb h x a).map φ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have H := primaryData h hp hp2 hx
  rw [SUNS.range_inf_centralizer_eq_map h hker hp hpq hx] at hL
  set C := Subgroup.centralizer ({x} : Set ↥(unitarySU 2 f K n)) with hC
  by_cases hex : ∃ a, IsGoodBlock h (toUnitHom x) a ∧ L₁ ≤ (sb h x a).map φ
  · obtain ⟨a, ha, hle⟩ := hex
    refine ⟨a, ha, ?_⟩
    have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hL hle
      (Subgroup.map_mono sb_le_centralizer)
    have hrange : (sb h x a).map φ = (φ.comp (sb h x a).subtype).range := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [hrange] at hc' ⊢
    exact CoordSL.eq_of_isComponentOf_range (isQuasisimple_sb hp hp2 hx a ha) _ hc'
  exfalso
  push Not at hex
  have hcomm : ∀ a, IsGoodBlock h (toUnitHom x) a → ⁅L₁, (sb h x (a : K[X])).map φ⁆ = ⊥ :=
    fun a ha => (CoordSL.le_or_commutator_eq_bot_of_normal hL
      (Subgroup.map_mono sb_le_centralizer) (map_sb_normal (a : K[X]))).resolve_left (hex a ha)
  set Lt := L₁.comap φ ⊓ C with hLtdef
  have hLt : Lt.map φ = L₁ := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.1
    · intro g hg
      obtain ⟨y, hyC, rfl⟩ := hL.1 hg
      exact ⟨y, ⟨hg, hyC⟩, rfl⟩
  have hscal : ∀ y ∈ Lt, ∀ a, IsGoodBlock h (toUnitHom x) a →
      ∃ c : AdjoinRoot (a : K[X]), ∀ v : primaryComponent ((toUnitHom x :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X]),
        lin y (v : Fin n → K) = ((c • v : primaryComponent ((toUnitHom x :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) (a : K[X])) :
            Fin n → K) := by
    intro y hy a ha
    refine exists_smul_of_commute_sb hp hp2 hx a ha hy.2
      (commute_of_map_commute hker hp hp2 hx a ha fun g hg => ?_)
    have hmem : ⁅φ y, φ g⁆ ∈ ⁅L₁, (sb h x (a : K[X])).map φ⁆ :=
      Subgroup.commutator_mem_commutator hy.1 ⟨g, hg, rfl⟩
    rw [hcomm a ha, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  set T : Subgroup ↥(unitarySU 2 f K n) :=
    (trivialOn (toUnitHom x) (nonExc h x)).comap toUnitHom ⊓ C with hT
  have hDT : ⁅Lt, Lt⁆ ≤ T := by
    refine Subgroup.commutator_le.mpr fun y hy y' hy' => ⟨fun c hc hcO v hv => ?_,
      C.mul_mem (C.mul_mem (C.mul_mem hy.2 hy'.2) (C.inv_mem hy.2)) (C.inv_mem hy'.2)⟩
    change lin ⁅y, y'⁆ v = v
    refine lin_commutator_apply hy.2 hy'.2 (fun w hw => ?_) hv
    rcases hcO hc with hgood | hm1
    · obtain ⟨c₁, hc₁⟩ := hscal y hy ⟨c, hc⟩ hgood
      obtain ⟨c₂, hc₂⟩ := hscal y' hy' ⟨c, hc⟩ hgood
      have e1 := hc₁ (c₂ • ⟨w, hw⟩)
      have e2 := hc₂ (c₁ • ⟨w, hw⟩)
      have e3 := hc₂ ⟨w, hw⟩
      have e4 := hc₁ ⟨w, hw⟩
      simp only at e3 e4
      rw [e3, e1, e4, e2, smul_smul, smul_smul, mul_comm]
    · have : Fact (Irreducible c) := ⟨irreducible_of_mem_primaryFactors hc⟩
      have hYc : ∀ z ∈ C, (lin z : Module.End K (Fin n → K)) ∈
          commutant ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
            Module.End K (Fin n → K)) := by
        intro z hz
        refine (mem_commutant _).mpr ?_
        have h1 : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hz
        rw [coe_toUnitHom, Commute, SemiconjBy, ← lin_mul, ← lin_mul, h1]
      have hcm := End_commute_of_finrank_le_one (E := AdjoinRoot c)
        (W := primaryComponent ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
          Module.End K (Fin n → K)) c) hm1
        (commutantRestrict c ⟨lin y, hYc y hy.2⟩) (commutantRestrict c ⟨lin y', hYc y' hy'.2⟩)
      exact congrArg (fun S : Module.End (AdjoinRoot c) (primaryComponent ((toUnitHom x :
        LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) c) =>
          ((S ⟨w, hw⟩ : primaryComponent ((toUnitHom x :
            LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) c) :
              Fin n → K)) hcm.eq
  have hperf : ⁅L₁, L₁⁆ = L₁ := Subgroup.isPerfect_iff.mp
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hL.2.2).1
  have hD : (⁅Lt, Lt⁆ : Subgroup ↥(unitarySU 2 f K n)).map φ = L₁ := by
    rw [Subgroup.map_commutator, hLt, hperf]
  have hpD : p ∣ Nat.card (⁅Lt, Lt⁆ : Subgroup ↥(unitarySU 2 f K n)) := by
    refine hpL.trans ?_
    conv_lhs => rw [← hD]
    exact Subgroup.card_map_dvd _ φ
  have : Finite ↥(unitarySU 2 f K n) := Subtype.finite
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(⁅Lt, Lt⁆ : Subgroup
    ↥(unitarySU 2 f K n))) p hpD
  have hdT := hDT d.2
  have hdord : orderOf (d : ↥(unitarySU 2 f K n)) = p := by rw [Subgroup.orderOf_coe, hd]
  have hdp : (d : ↥(unitarySU 2 f K n)) ^ p = 1 := hdord ▸ pow_orderOf_eq_one _
  have hdU := toUnitHom_mem_unitaryCentralizer (h := h) hdT.2
  have hdUp : toUnitHom (d : ↥(unitarySU 2 f K n)) ^ p = 1 := by rw [← map_pow, hdp, map_one]
  have hd1 : toUnitHom (d : ↥(unitarySU 2 f K n)) = 1 := by
    refine eq_one_of_forall_apply_eq H.squarefree fun c hc v hv => ?_
    by_cases hcO : c ∈ nonExc h x
    · exact hdT.1 c hc hcO v hv
    · have hcO' : ¬ IsGoodBlock h (toUnitHom x) ⟨c, hc⟩ ∧ ¬ primaryMultiplicity ((toUnitHom x :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) c ≤ 1 := by
        by_contra hcon
        apply hcO
        intro hc'
        by_cases hg : IsGoodBlock h (toUnitHom x) ⟨c, hc'⟩
        · exact Or.inl hg
        · exact Or.inr (by_contra fun hm => hcon ⟨hg, hm⟩)
      obtain ⟨hng, hm⟩ := hcO'
      have hm2 : 2 ≤ primaryMultiplicity ((toUnitHom x :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) c := by omega
      have hself : dualPoly h.bar c = c := by
        by_contra hne
        exact hng ⟨hm2, fun h' => absurd h' hne⟩
      have hbad : (primaryMultiplicity ((toUnitHom x :
          LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) c,
          2 ^ (f * c.natDegree)) ∈ ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ)) := by
        by_contra hnot
        exact hng ⟨hm2, fun _ => hnot⟩
      exact apply_eq_of_exceptional H hp (three_lt_of_bad hp hp2 hpq hbad) hdU hdUp ⟨c, hc⟩
        hself hbad v hv
  have hd1' : (d : ↥(unitarySU 2 f K n)) = 1 := toUnitHom_injective (by rw [hd1, map_one])
  rw [hd1', orderOf_one] at hdord
  exact hp.one_lt.ne hdord

end Classification

end NsFrameComp

end CFSG.StandardType
