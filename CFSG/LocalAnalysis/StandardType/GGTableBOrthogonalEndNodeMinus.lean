module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusTenBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBOrth

open TableBSymp

variable {K : Type} [Field K]

section Split

@[expose] def minusSplit (k : ℕ) :
    LargeEvenMinusIdx (k + 1) ≃ LargeEvenMinusIdx k ⊕ (Fin 1 ⊕ Fin 1) :=
  (Equiv.sumCongr (plusSplit k) (Equiv.refl (Fin 2))).trans ((Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans (Equiv.sumAssoc _ _ _).symm))

theorem minusSplit_symm_inl_inl_inl (k : ℕ) (x : Fin k) :
    (minusSplit k).symm (Sum.inl (Sum.inl (Sum.inl x))) = Sum.inl (Sum.inl (Fin.castSucc x)) := by
  simp [minusSplit, ← plusSplit_symm_inl_inl]

theorem minusSplit_symm_inl_inl_inr (k : ℕ) (x : Fin k) :
    (minusSplit k).symm (Sum.inl (Sum.inl (Sum.inr x))) = Sum.inl (Sum.inr (Fin.castSucc x)) := by
  simp [minusSplit, ← plusSplit_symm_inl_inr]

theorem minusSplit_symm_inl_inr (k : ℕ) (a : Fin 2) :
    (minusSplit k).symm (Sum.inl (Sum.inr a)) = Sum.inr a := by
  simp [minusSplit]

theorem minusSplit_symm_inr_inl (k : ℕ) (a : Fin 1) :
    (minusSplit k).symm (Sum.inr (Sum.inl a)) = Sum.inl (Sum.inl (Fin.last k)) := by
  simp [minusSplit, ← plusSplit_symm_inr_inl k a]

theorem minusSplit_symm_inr_inr (k : ℕ) (a : Fin 1) :
    (minusSplit k).symm (Sum.inr (Sum.inr a)) = Sum.inl (Sum.inr (Fin.last k)) := by
  simp [minusSplit, ← plusSplit_symm_inr_inr k a]

theorem largeEvenQMinus_split (k : ℕ) (b c : K) (v : LargeEvenMinusIdx (k + 1) → K) :
    LargeEvenQMinus (k + 1) b c v =
      LargeEvenQMinus k b c (fun x => v ((minusSplit k).symm (Sum.inl x))) +
        v ((minusSplit k).symm (Sum.inr (Sum.inl 0))) *
          v ((minusSplit k).symm (Sum.inr (Sum.inr 0))) := by
  simp only [LargeEvenQMinus, minusSplit_symm_inl_inl_inl, minusSplit_symm_inl_inl_inr,
    minusSplit_symm_inl_inr, minusSplit_symm_inr_inl, minusSplit_symm_inr_inr]
  rw [Fin.sum_univ_castSucc]
  ring

theorem isPairTorus_minus {k : ℕ} {ζ : Kˣ} (hζ2 : ζ * ζ ≠ 1) :
    IsPairTorus (minusSplit k) (Sum.elim (pairedUnits (Pi.mulSingle (Fin.last k) ζ)) 1) ζ where
  rest x := by
    rcases x with (x | x) | x
    · rw [minusSplit_symm_inl_inl_inl]
      simp [pairedUnits, Pi.mulSingle_apply, Fin.castSucc_ne_last]
    · rw [minusSplit_symm_inl_inl_inr]
      simp [pairedUnits, Pi.mulSingle_apply, Fin.castSucc_ne_last]
    · rw [minusSplit_symm_inl_inr]
      rfl
  left := by
    rw [minusSplit_symm_inr_inl]
    simp [pairedUnits]
  right := by
    rw [minusSplit_symm_inr_inr]
    simp [pairedUnits]
  sq_ne_one := hζ2

theorem isQuasisimple_omegaMinus [Finite K] [CharP K 2] {k : ℕ} (hk : 2 ≤ k) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    CFSG.IsQuasisimple (LargeEvenOmega (LargeEvenQMinus k b c)) := by
  rw [← coe_qMinusForm]
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv (omegaEquivOrthDerived (qMinusForm K k b c)).symm
    ?_
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
  · refine (CFSG.SeitzReduction.OmegaPilot.isQuasisimple_orthDerived_of_six
      (nondegenerate_qMinusForm 2 hirr) ?_ fun U hU => ?_).1
    · rw [Module.finrank_fintype_fun_eq_card]
      rfl
    · by_contra h
      push Not at h
      have := finrank_le_of_singular_qMinus hirr U h
      omega
  · obtain ⟨T, hT3, hT0⟩ :=
      (CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := k + 1) (by omega) hirr).2
    refine CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived
      (nondegenerate_qMinusForm k hirr)
      ⟨T.map (qMinusIsometry (K := K) k b c).symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hT3]
    · rintro _ ⟨w, hw, rfl⟩
      change qMinusForm K k b c ((qMinusIsometry k b c).symm w) = 0
      rw [QuadraticMap.IsometryEquiv.map_app]
      exact hT0 w hw

end Split

section MinusEndNode

theorem blockInl_injective {m : ℕ} : Function.Injective (blockInl (K := K) (m := m)) := by
  intro g g' h
  apply Units.ext
  have := congrArg (fun g : GL (LargeEvenMinusIdx m) K =>
    (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) K).toBlocks₁₁) h
  simpa [coe_blockInl] using this

variable [Finite K] [CharP K 2]

theorem ggEndNodeElt_omegaMinusGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) {k : ℕ} (hk : 2 ≤ k) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGEndNodeElt p (k + 1) (LargeEvenOmega (LargeEvenQMinus (k + 1) b c)) := by
  rw [ggEndNodeElt_iff]
  intro A hA hr _
  have := Fact.mk hp
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζo, hζ, hζ1, hζ2⟩ := exists_zeta (K := K) hp hp2 hpq
  have hAGO : A.map (LargeEvenOmega (LargeEvenQMinus (k + 1) b c)).subtype ≤
      LargeEvenOrthGroup (LargeEvenQMinus (k + 1) b c) :=
    (Subgroup.map_subtype_le A).trans (omega_le_orth _)
  have hAGc : Nat.card (A.map (LargeEvenOmega (LargeEvenQMinus (k + 1) b c)).subtype) =
      Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  have hAGe : IsElemAbelian p (A.map (LargeEvenOmega (LargeEvenQMinus (k + 1) b c)).subtype) :=
    TableB.isElemAbelian_map hA _
  obtain ⟨g, hgO, χ, hχ, hsurj⟩ := exists_orth_conj_minus hp2 hζo hirr hAGO hAGe (hAGc ▸ hr)
  have hu₀p : ∀ j, (Pi.mulSingle (Fin.last k) ζ : Fin (k + 1) → Kˣ) j ^ p = 1 := fun j => by
    rw [Pi.mulSingle_apply]
    split_ifs
    · exact hζ
    · exact one_pow p
  obtain ⟨x₀, hx₀⟩ := hsurj _ hu₀p
  obtain ⟨a₀, ha₀A, ha₀⟩ := Subgroup.mem_map.mp x₀.2
  have hcA : ∀ (a : LargeEvenOmega (LargeEvenQMinus (k + 1) b c)) (ha : a ∈ A),
      ((conjOmega hgO a : LargeEvenOmega (LargeEvenQMinus (k + 1) b c)) :
        GL (LargeEvenMinusIdx (k + 1)) K) =
      blockInl (TauCeti.diagGL
        (pairedUnits fun j => χ j ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩)) := by
    intro a ha
    have h1 := hχ ⟨(a : GL _ K), Subgroup.mem_map_of_mem _ ha⟩
    rw [coe_conjOmega]
    rw [← h1]
  set u₀ : Fin (k + 1) → Kˣ := Pi.mulSingle (Fin.last k) ζ with hu₀
  have hPT : IsPairTorus (minusSplit k) (Sum.elim (pairedUnits u₀) 1) ζ := isPairTorus_minus hζ2
  have hx₀' : x₀ = ⟨(a₀ : GL _ K), Subgroup.mem_map_of_mem _ ha₀A⟩ := Subtype.ext ha₀.symm
  have hct : ((conjOmega hgO a₀ : LargeEvenOmega (LargeEvenQMinus (k + 1) b c)) :
      GL (LargeEvenMinusIdx (k + 1)) K) = blockInl (TauCeti.diagGL (pairedUnits u₀)) := by
    rw [hcA a₀ ha₀A, ← hx₀']
    congr 3
    funext j
    exact hx₀ j
  suffices hend : IsEndNode (A.map (conjOmega hgO).toMonoidHom) (conjOmega hgO a₀) by
    refine ⟨a₀, ?_⟩
    have h1 := hend.map (conjOmega hgO).symm
    rwa [Subgroup.map_map, show (conjOmega hgO).symm.toMonoidHom.comp (conjOmega hgO).toMonoidHom =
      MonoidHom.id _ from MonoidHom.ext fun x => (conjOmega hgO).symm_apply_apply x,
      Subgroup.map_id, MulEquiv.symm_apply_apply] at h1
  have hmemCent : ∀ y : LargeEvenOmega (LargeEvenQMinus (k + 1) b c),
      y ∈ Subgroup.centralizer
        ({conjOmega hgO a₀} : Set (LargeEvenOmega (LargeEvenQMinus (k + 1) b c))) ↔
        (y : GL (LargeEvenMinusIdx (k + 1)) K) ∈
          Subgroup.centralizer ({TauCeti.diagGL (Sum.elim (pairedUnits u₀) 1)} :
            Set (GL (LargeEvenMinusIdx (k + 1)) K)) := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
      ← blockInl_diagGL, ← hct]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcentB : ∀ {π : Equiv.Perm (Fin (k + 1) ⊕ Fin (k + 1))},
      pairedUnits u₀ ∘ ⇑π⁻¹ = pairedUnits u₀ →
      blockInl (TauCeti.permutationGL (k := K) π) ∈
        Subgroup.centralizer ({TauCeti.diagGL (Sum.elim (pairedUnits u₀) 1)} :
          Set (GL (LargeEvenMinusIdx (k + 1)) K)) := by
    intro π hπ
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp
      (permutationGL_mem_centralizer_diagGL (K := K) hπ)
    rw [Subgroup.mem_centralizer_singleton_iff, ← blockInl_diagGL, ← map_mul, ← map_mul, h1]
  set D : Subgroup (LargeEvenOmega (LargeEvenQMinus (k + 1) b c)) :=
    ((LargeEvenOmega (LargeEvenQMinus k b c)).map (embHom (minusSplit k))).subgroupOf
      (LargeEvenOmega (LargeEvenQMinus (k + 1) b c)) with hD
  have hDle : D ≤ Subgroup.centralizer
      ({conjOmega hgO a₀} : Set (LargeEvenOmega (LargeEvenQMinus (k + 1) b c))) := by
    intro y hy
    rw [hmemCent]
    rw [hD, Subgroup.mem_subgroupOf] at hy
    obtain ⟨h, _, hh⟩ := hy
    rw [← hh]
    exact hPT.embHom_mem_centralizer h
  have hcomm : ∀ a ∈ Subgroup.centralizer
      ({conjOmega hgO a₀} : Set (LargeEvenOmega (LargeEvenQMinus (k + 1) b c))),
      ∀ b' ∈ Subgroup.centralizer
        ({conjOmega hgO a₀} : Set (LargeEvenOmega (LargeEvenQMinus (k + 1) b c))),
      a * b' * a⁻¹ * b'⁻¹ ∈ D := by
    intro a ha b' hb
    rw [hD, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hPT.commutator_mem_map_embHom_omega (largeEvenQMinus_split k b c) ((hmemCent a).mp ha)
      ((hmemCent b').mp hb) (omega_le_orth _ a.2) (omega_le_orth _ b'.2)
  have hq : CFSG.IsQuasisimple D := by
    have e1 : D ≃* ((LargeEvenOmega (LargeEvenQMinus k b c)).map (embHom (minusSplit k))) :=
      Subgroup.subgroupOfEquivOfLe (map_embHom_omega_le (largeEvenQMinus_split k b c))
    have e2 := (LargeEvenOmega (LargeEvenQMinus k b c)).equivMapOfInjective _
      (embHom_injective (minusSplit k))
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e1.trans e2.symm).symm
      (isQuasisimple_omegaMinus hk hirr)
  obtain ⟨hlay, hcompD⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem hDle hcomm hq
  refine ⟨⟨a₀, ha₀A, rfl⟩, ?_, ?_, ?_⟩
  · intro h1
    have h2 := congrArg (fun y : LargeEvenOmega (LargeEvenQMinus (k + 1) b c) =>
      ((y : GL (LargeEvenMinusIdx (k + 1)) K) :
        Matrix (LargeEvenMinusIdx (k + 1)) (LargeEvenMinusIdx (k + 1)) K)
        (Sum.inl (Sum.inl (Fin.last k))) (Sum.inl (Sum.inl (Fin.last k)))) h1
    simp only [hct, OneMemClass.coe_one, Units.val_one, Matrix.one_apply_eq, coe_blockInl,
      Matrix.fromBlocks_apply₁₁, TauCeti.diagGL_coe, Matrix.diagonal_apply_eq, pairedUnits,
      Sum.elim_inl, hu₀, Pi.mulSingle_eq_same] at h2
    exact hζ1 (Units.ext h2)
  · rw [hlay]
    exact hcompD
  · rintro _ ⟨s, hs, rfl⟩
    rw [hlay]
    have hcs := hcA s hs
    set us : Fin (k + 1) → Kˣ :=
      fun j => χ j ⟨(s : GL _ K), Subgroup.mem_map_of_mem _ hs⟩ with hus
    have husp : ∀ j, us j ^ p = 1 := fun j => by
      rw [hus, ← map_pow]
      have h1 : (⟨(s : GL _ K), Subgroup.mem_map_of_mem _ hs⟩ :
          A.map (LargeEvenOmega (LargeEvenQMinus (k + 1) b c)).subtype) ^ p = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val (hA.2 s hs))
      rw [h1, map_one]
    constructor
    · intro hcomm'
      have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have hj : ∀ j : Fin k, us (Fin.castSucc j) = 1 := by
        intro j
        obtain ⟨j', hj'⟩ := exists_ne j
        have hjj : Fin.castSucc j ≠ Fin.castSucc j' :=
          fun h => hj' (Fin.castSucc_injective _ h).symm
        have hwΩ : blockInl (TauCeti.permutationGL (k := K)
            (pairSwap (Fin.castSucc j) * pairSwap (Fin.castSucc j'))) ∈
            LargeEvenOmega (LargeEvenQMinus (k + 1) b c) :=
          blockInl_mem_omegaMinus b c permutationGL_pairSwap_mul_mem_omegaPlus
        have hwD : (⟨_, hwΩ⟩ : LargeEvenOmega (LargeEvenQMinus (k + 1) b c)) ∈ D := by
          rw [hD, Subgroup.mem_subgroupOf]
          change blockInl (TauCeti.permutationGL (k := K)
            (pairSwap (Fin.castSucc j) * pairSwap (Fin.castSucc j'))) ∈ _
          rw [← permutationGL_commutator_pairSwap, map_mul, map_mul, map_mul, map_inv, map_inv]
          refine hPT.commutator_mem_map_embHom_omega (largeEvenQMinus_split k b c) ?_ ?_
            (map_blockInl_orth_le b c ⟨_, sumCongr_mem_orthPlus _, rfl⟩)
            (map_blockInl_orth_le b c ⟨_, pairSwap_mem_orthPlus _, rfl⟩)
          · apply hcentB
            apply pairedUnits_comp_sumCongr_inv
            funext i
            have hlast : ∀ i, (Equiv.swap (Fin.castSucc j) (Fin.castSucc j')) i = Fin.last k ↔
                i = Fin.last k := fun i => by
              rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_of_ne_of_ne
                (Fin.castSucc_ne_last j).symm (Fin.castSucc_ne_last j').symm]
            simp only [Function.comp_apply, Equiv.swap_inv, hu₀, Pi.mulSingle_apply, hlast]
          · apply hcentB
            apply pairedUnits_comp_pairSwap_inv
            rw [hu₀, Pi.mulSingle_eq_of_ne (Fin.castSucc_ne_last j')]
        have h2 := congrArg Subtype.val (hcomm' _ hwD)
        simp only [Subgroup.coe_mul, MulEquiv.coe_toMonoidHom] at h2
        rw [hcs, ← map_mul, ← map_mul] at h2
        exact eq_one_of_commute_pairSwap_mul hp hp2 husp hjj (blockInl_injective h2)
      obtain ⟨n, hn⟩ := exists_pow_eq_mulSingle hζo husp hj
      refine Subgroup.mem_zpowers_iff.mpr ⟨(n : ℤ), Subtype.ext ?_⟩
      rw [zpow_natCast, SubgroupClass.coe_pow, hct, ← map_pow, hu₀,
        diagGL_pairedUnits_mulSingle_pow, hn, MulEquiv.coe_toMonoidHom, hcs]
    · intro hmem j hj
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hjt := Subgroup.mem_centralizer_singleton_iff.mp (hDle hj)
      rw [← hn]
      exact (Commute.zpow_left hjt.symm n).eq

theorem ggEndNode_omegaMinus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {m : ℕ} (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGEndNode p m (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) (LargeEvenInnSet _) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact ggEndNode_of_elt subset_rfl (center_omegaMinus_eq_bot hp hp2 hpq hm hirr)
    (ggEndNodeElt_of_mulEquiv (projMkEquiv (scalars_subgroupOf_omegaMinus_eq_bot b c))
      (ggEndNodeElt_omegaMinusGroup hp hp2 hpq (by omega) hirr))

end MinusEndNode

end TableBOrth

end CFSG.StandardType
