module

public import CFSG.LocalAnalysis.StandardType.GGHalfCentDefs

public section

namespace CFSG.StandardType.GGHalf

open CFSG.StandardType CFSG.StandardType.CoordSL CFSG.RankThree.CALinearPlane Matrix

private theorem centStruct_aligned {s : ℕ} (β : Fin s → ZMod 3)
    (hβ : ∀ i, β i = 0 ∨ β i = 1) :
    Aligned (g := phi3) (p := 3) root_phi3_pow_three β := by
  intro i j hj u _hu h
  rcases hβ j with hj0 | hj1
  · exact absurd hj0 hj
  · rw [hj1, mul_one] at h
    rcases hβ i with hi0 | hi1
    · rw [hi0] at h
      exact absurd h.symm (Units.ne_zero u)
    · rw [hi1, hj1]

theorem comp_eq_zeroBlk_or_classBlk {n s r : ℕ}
    (ε : Fin (n + 1) ≃ (Fin (rootPB phi3).dim × Fin s) ⊕ Fin r) (k : Fin s → ℕ)
    (hk : ∀ i, k i = 0 ∨ k i = 1) {J : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({SLNS.nsSL ε det_rootMat_phi3 k} :
        Set (SpecialLinearGroup (Fin (n + 1)) F2)))) :
    J = zeroBlk ε k ∨ J = classBlk ε k := by
  classical
  set β : Fin s → ZMod 3 := fun i => (k i : ZMod 3) with hβdef
  have hβ : ∀ i, β i = 0 ∨ β i = 1 := by
    intro i
    change (k i : ZMod 3) = 0 ∨ (k i : ZMod 3) = 1
    rcases hk i with h | h <;> simp [h]
  have hβval : ∀ i, (β i).val = k i := by
    intro i
    change ((k i : ZMod 3)).val = k i
    rcases hk i with h | h <;> rw [h, ZMod.val_natCast]
  have hYeq : SLNS.nsSL ε det_rootMat_phi3 k =
      SLNS.nsSL ε det_rootMat_phi3 (fun i => (β i).val) := by
    refine SLNS.nsSL_congr ε det_rootMat_phi3 rootMat_phi3_pow_three ?_
    intro i
    rw [hβval i]
  rw [hYeq] at hJ
  set φ : Matrix.SpecialLinearGroup (Fin (n + 1)) F2 →*
      Matrix.SpecialLinearGroup (Fin (n + 1)) F2 := MonoidHom.id _ with hφdef
  have hmapφ : ∀ N : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2), N.map φ = N := by
    intro N
    rw [hφdef]
    exact Subgroup.map_id N
  have hkerφ : φ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (n + 1)) F2) := by
    rw [hφdef]
    simp
  set Y := SLNS.nsSL ε det_rootMat_phi3 (fun i => (β i).val) with hY
  set C₀ := Subgroup.centralizer ({Y} : Set (Matrix.SpecialLinearGroup (Fin (n + 1)) F2))
    with hC₀
  have hcomp : CFSG.Assembly.IsComponentOf J (C₀.map φ) := by
    rw [hmapφ]
    exact hJ
  have hmemC₀ : ∀ u, u ∈ C₀ ↔ u * Y = Y * u := fun u =>
    Subgroup.mem_centralizer_singleton_iff
  set Jz := zeroCoords ε β with hJz
  set KC : ZMod 3 → Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2) := fun c =>
    (coordBlockSL (AdjoinRoot phi3) (classSet β c)).map (theta phi3 ε) with hKC
  have hprim : IsPrimitiveRoot (AdjoinRoot.root phi3) 3 :=
    root_isPrimitiveRoot (g := phi3) Nat.prime_three natCast_three_ne_zero phi3_dvd_cyclotomic
  have hal : Aligned root_phi3_pow_three β := centStruct_aligned β hβ
  have hKZC : coordBlockSL F2 Jz ≤ C₀ := fun M hM => (hmemC₀ M).mpr
    (comm_zeroBlock_of_torus (k := fun i => (β i).val)
      (fun i hi => by rw [hi, ZMod.val_zero]) hM).symm
  have hKCC : ∀ c, KC c ≤ C₀ := by
    rintro c _ ⟨M, hM, rfl⟩
    exact (hmemC₀ _).mpr (comm_classBlock_of_torus (k := fun i => (β i).val)
      (fun i j hi hj => by rw [hi, hj]) hM)
  have hKZn : (((coordBlockSL F2 Jz).map φ).subgroupOf (C₀.map φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hKZC)]
    rintro _ _ ⟨M, hM, rfl⟩ ⟨u, hu, rfl⟩
    exact ⟨u * M * u⁻¹, conj_mem_zeroBlock hprim hal ((hmemC₀ u).mp hu) hM,
      by rw [map_mul, map_mul, map_inv]⟩
  have hKCn : ∀ c, c ≠ 0 → (((KC c).map φ).subgroupOf (C₀.map φ)).Normal := by
    intro c hc
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (hKCC c))]
    rintro _ _ ⟨_, ⟨M, hM, rfl⟩, rfl⟩ ⟨u, hu, rfl⟩
    obtain ⟨M', hM', hM'eq⟩ := conj_mem_classBlock hprim hal hc ((hmemC₀ u).mp hu) hM
    exact ⟨theta phi3 ε M', ⟨M', hM', rfl⟩, by rw [hM'eq, map_mul, map_mul, map_inv]⟩
  have hq := hcomp.2.2
  have hdZ := le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono hKZC) hKZn
  by_cases hZ : J ≤ (coordBlockSL F2 Jz).map φ
  ·
    left
    have hQ := quasisimple_of_le_map_coordBlockSL φ hq hZ
    have hrange : (coordBlockSL F2 Jz).map φ = (φ.comp (blockSLOn F2 Jz)).range := by
      rw [MonoidHom.range_comp, range_blockSLOn]
    have hL₁ : J = (coordBlockSL F2 Jz).map φ := by
      have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hZ
        (Subgroup.map_mono hKZC)
      rw [hrange] at hc' ⊢
      exact eq_of_isComponentOf_range hQ _ hc'
    rw [hL₁, hmapφ]
    rfl
  · by_cases hCex : ∃ c, c ≠ 0 ∧ J ≤ (KC c).map φ
    ·
      right
      obtain ⟨c, hc, hLc⟩ := hCex
      have : CharP (AdjoinRoot phi3) 2 :=
        charP_of_injective_algebraMap (algebraMap F2 (AdjoinRoot phi3)).injective 2
      have : Finite (AdjoinRoot phi3) := finite_adjoinRoot
      have hmap : (KC c).map φ =
          (coordBlockSL (AdjoinRoot phi3) (classSet β c)).map (φ.comp (theta phi3 ε)) :=
        Subgroup.map_map _ _ _
      rw [hmap] at hLc
      have hQ := quasisimple_of_le_map_coordBlockSL (φ.comp (theta phi3 ε)) hq hLc
      have hS2 := two_le_card_of_le_map_coordBlockSL (φ.comp (theta phi3 ε)) hq hLc
      have hS : (classSet β c).Nonempty := Finset.card_pos.mp (by omega)
      have hrange : (coordBlockSL (AdjoinRoot phi3) (classSet β c)).map
            (φ.comp (theta phi3 ε)) =
          ((φ.comp (theta phi3 ε)).comp (blockSLOn (AdjoinRoot phi3) (classSet β c))).range := by
        rw [MonoidHom.range_comp, range_blockSLOn]
      have hL₁ : J = (KC c).map φ := by
        have hc' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp hLc
          (hmap ▸ Subgroup.map_mono (hKCC c))
        rw [hmap, hrange]
        rw [hrange] at hc'
        exact eq_of_isComponentOf_range hQ _ hc'
      obtain ⟨i₀, hi₀⟩ := hS
      have hi₀' : β i₀ = c := mem_classSet.mp hi₀
      have hc1 : c = 1 := by
        rcases hβ i₀ with h | h
        · exact absurd (hi₀'.symm.trans h) hc
        · exact hi₀'.symm.trans h
      rw [hL₁, hc1, hmapφ]
      rfl
    ·
      exfalso
      push Not at hCex
      have hZb : ⁅J, (coordBlockSL F2 Jz).map φ⁆ = ⊥ := hdZ.resolve_left hZ
      have hCb : ∀ c, c ≠ 0 → ⁅J, (KC c).map φ⁆ = ⊥ := fun c hc =>
        (le_or_commutator_eq_bot_of_normal hcomp (Subgroup.map_mono (hKCC c))
          (hKCn c hc)).resolve_left (hCex c hc)
      have hcommN : ∀ {N : Subgroup (Matrix.SpecialLinearGroup (Fin (n + 1)) F2)},
          ⁅J, N⁆ = ⊥ → ∀ x ∈ J, ∀ y ∈ N, x * y = y * x := by
        intro N hN x hx y hy
        have h1 := Subgroup.commutator_mem_commutator hx hy
        rw [hN, Subgroup.mem_bot] at h1
        exact commutatorElement_eq_one_iff_mul_comm.mp h1
      have hZw : ∀ w, φ w ∈ J → ∀ x y (hxy : x ≠ y), x ∈ Jz → y ∈ Jz →
          w * Matrix.SpecialLinearGroup.transvection hxy (1 : F2) =
            Matrix.SpecialLinearGroup.transvection hxy 1 * w := by
        intro w hw x y hxy hx hy
        have ht := SLRep.transvection_mem_coordBlockSL hx hy hxy (1 : F2)
        exact commute_of_map_commute_of_mul_self hkerφ (LinSemisimple.transvection_one_mul_self hxy)
          (hcommN hZb _ hw _ (Subgroup.mem_map_of_mem φ ht))
      have hcw : ∀ w, φ w ∈ J → ∀ i j (hij : i ≠ j), β i = β j → β i ≠ 0 →
          ∀ c' : AdjoinRoot phi3,
            w * theta phi3 ε (Matrix.SpecialLinearGroup.transvection hij c') =
              theta phi3 ε (Matrix.SpecialLinearGroup.transvection hij c') * w := by
        intro w hw i j hij hβij hβi c'
        have hT := SLRep.transvection_mem_coordBlockSL (mem_classSet.mpr rfl)
          (mem_classSet.mpr hβij.symm) hij c'
        have hθT : theta phi3 ε (Matrix.SpecialLinearGroup.transvection hij c') ∈ KC (β i) :=
          ⟨_, hT, rfl⟩
        exact commute_of_map_commute_of_mul_self hkerφ (theta_transvection_mul_self ε hij c')
          (hcommN (hCb (β i) hβi) _ hw _ (Subgroup.mem_map_of_mem φ hθT))
      refine LinSemisimple.false_of_isQuasisimple_of_commute hq fun x hx y hy => ?_
      obtain ⟨u, hu, rfl⟩ := hcomp.1 hx
      obtain ⟨v, hv, rfl⟩ := hcomp.1 hy
      rw [← map_mul, ← map_mul, commute_of_comm_blocks hprim hal ((hmemC₀ u).mp hu)
        ((hmemC₀ v).mp hv) (hZw u hx) (hZw v hy) (hcw u hx) (hcw v hy)]

end CFSG.StandardType.GGHalf

end
