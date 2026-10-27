module

public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Derived
public import CFSG.OddTranspositions.PartThree.Eleven.OneOne.Lift
import CFSG.OddTranspositions.FusionStep
import CFSG.OddTranspositions.SixFiveInputs
import TauCeti.Algebra.Group.Subgroup.TwoTorsionClosure
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.GroupTheory.CardSupInf
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
import CFSG.OddTranspositions.CommutatorSize
import CFSG.OddTranspositions.SecondKindCoset
import CFSG.OddTranspositions.WidthOne

public section

namespace CFSG.OddTranspositions.PartThree

open scoped Function
open scoped IsMulCommutative
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity


variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_sylow_frame (hC : HypothesisC D) (T : Sylow 2 (Halpha D hC.alpha)) :
    ∃ S : Sylow 2 G,
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S ∧
        hC.d ∈ (S : Subgroup G) := by
  classical
  have huP : IsPGroup 2 (Subgroup.zpowers hC.d) := by
    rw [isPGroup_iff_card_dvd_pow]
    exact ⟨1, by rw [Nat.card_zpowers, hC.setup.oddT.1 hC.d hC.hd]; norm_num⟩
  have hVp : IsPGroup 2
      ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :=
    T.isPGroup'.map _
  have hcent : ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) ≤
      Subgroup.centralizer (Subgroup.zpowers hC.d : Set G) := by
    rw [Subgroup.le_centralizer_iff, Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.mp ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_d hC t'.2)
  have hnorm : ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) ≤
      Subgroup.normalizer (Subgroup.zpowers hC.d : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer (Subgroup.zpowers hC.d : Set G))
  have hPp : IsPGroup 2 ((Subgroup.zpowers hC.d ⊔
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) : Subgroup G) :=
    huP.to_sup_of_normal_left' hVp hnorm
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hPp
  exact ⟨S, le_trans le_sup_right hS,
    hS (Subgroup.mem_sup_left (Subgroup.mem_zpowers hC.d))⟩

theorem prod_frameLift_mem {hC : HypothesisC D}
    {T : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) T r) {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i) :
    w 0 * w 1 * w 2 * w 3 ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
  rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
  rw [map_mul, map_mul, map_mul, hwr 0, hwr 1, hwr 2, hwr 3, O4PlusFrame.prod_eq hr]

private theorem card_closure_range_le {n : ℕ} (x : Fin n → G)
    (hsq : ∀ i, x i * x i = 1) (hcomm : ∀ i j, Commute (x i) (x j)) :
    Nat.card (Subgroup.closure (Set.range x)) ≤ 2 ^ n := by
  classical
  let X : Subgroup G := Subgroup.closure (Set.range x)
  have hpair : (Set.range x).Pairwise (Commute on id) := by
    intro a ha b hb _
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    exact hcomm i j
  letI : IsMulCommutative X := Subgroup.isMulCommutative_closure hpair
  let z : Fin n → X := fun i => ⟨x i, Subgroup.subset_closure ⟨i, rfl⟩⟩
  have hsqz : ∀ i ∈ (Finset.univ : Finset (Fin n)), z i ^ 2 = 1 := by
    intro i _
    apply Subtype.ext
    simpa [z, pow_two] using hsq i
  have hcl := TauCeti.closure_image_eq_image_powerset (Finset.univ : Finset (Fin n)) z hsqz
  have hle : Nat.card (Subgroup.closure (z '' (Finset.univ : Finset (Fin n)) : Set X)) ≤ 2 ^ n := by
    change Set.ncard (Subgroup.closure (z '' (Finset.univ : Finset (Fin n)) : Set X) : Set X)
      ≤ 2 ^ n
    rw [hcl]
    calc Set.ncard ((fun T : Finset (Fin n) => ∏ i ∈ T, z i) ''
            ((Finset.univ.powerset : Finset (Finset (Fin n))) : Set (Finset (Fin n))))
        ≤ Set.ncard (((Finset.univ.powerset : Finset (Finset (Fin n))) : Set (Finset (Fin n)))) :=
          Set.ncard_image_le
      _ = 2 ^ n := by
          rw [Set.ncard_coe_finset, Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  have himg : X.subtype '' (z '' (Finset.univ : Finset (Fin n)) : Set X) = Set.range x := by
    ext g; constructor
    · rintro ⟨-, ⟨i, -, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨z i, ⟨i, Finset.mem_univ i, rfl⟩, rfl⟩
  have hmap : (Subgroup.closure (z '' (Finset.univ : Finset (Fin n)) : Set X)).map X.subtype
      = X := by
    rw [MonoidHom.map_closure, himg]
  have hcard : Nat.card (Subgroup.closure (z '' (Finset.univ : Finset (Fin n)) : Set X))
      = Nat.card X := by
    have h := Subgroup.card_map_of_injective (K := Subgroup.closure
      (z '' (Finset.univ : Finset (Fin n)) : Set X)) (f := X.subtype) Subtype.coe_injective
    exact h.symm.trans (congrArg (fun K : Subgroup G => Nat.card K) hmap)
  change Nat.card X ≤ 2 ^ n
  exact hcard ▸ hle

namespace ElevenOneHyp

variable {hC : HypothesisC D}

theorem exists_frame_map (h : ElevenOneHyp hC) (T : Sylow 2 (Halpha D hC.alpha)) :
    ∃ r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha),
      O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r := by
  classical
  let Tb : Sylow 2 (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
    T.mapSurjective (QuotientGroup.mk'_surjective _)
  obtain ⟨r, hr⟩ := h.facts.frame Tb
  refine ⟨r, ?_⟩
  rwa [Sylow.coe_mapSurjective] at hr

theorem exists_frameLift (h : ElevenOneHyp hC) (T : Sylow 2 (Halpha D hC.alpha))
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r) :
    ∃ w : Fin 4 → Halpha D hC.alpha,
      (∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i) ∧
        (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w := by
  classical
  have hri : ∀ i, r i ∈ imageClass hC := by
    intro i
    have hmem : r i ∈ ((T : Subgroup (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) : Set _)
        ∩ imageClass hC := by
      rw [O4PlusFrame.inter_eq hr]
      exact Set.mem_range_self i
    exact hmem.2
  choose w hw using fun i => hri i
  have hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i)
      = r i := fun i => (hw i).2
  have hwD : ∀ i, w i ∈ DstarH hC := fun i => (hw i).1
  obtain ⟨A, B, hAB⟩ := h.facts.factors
  have hKM : Nat.card (Malpha D hC.alpha) ≤ 2 := (h.derived hAB).2.2.2.2.2
  have hMmap : Malpha D hC.alpha = (CFSG.solvableRadical (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype := rfl
  have hKcard : Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) ≤ 2 := by
    have hc : Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) =
        Nat.card (Malpha D hC.alpha) := by
      rw [hMmap]
      exact Nat.card_congr (Subgroup.equivMapOfInjective _
        (Halpha D hC.alpha).subtype Subtype.coe_injective).toEquiv
    omega
  have hKp : IsPGroup 2 (CFSG.solvableRadical (Halpha D hC.alpha)) := by
    rw [isPGroup_iff_card_dvd_pow]
    have hpos : 0 < Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) := Nat.card_pos
    rcases (by omega : Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) = 1 ∨
      Nat.card (CFSG.solvableRadical (Halpha D hC.alpha)) = 2) with h1 | h1
    · exact ⟨0, by rw [h1]; norm_num⟩
    · exact ⟨1, by rw [h1]; norm_num⟩
  have hKT : CFSG.solvableRadical (Halpha D hC.alpha) ≤ (T : Subgroup _) :=
    IsPGroup.le_sylow_of_normal hKp T
  refine ⟨w, hwr, ?_⟩
  ext x
  constructor
  · rintro ⟨hxT, hxD⟩
    have hxΘ : (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) x
        ∈ imageClass hC := ⟨x, hxD, rfl⟩
    have hxTb : (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) x
        ∈ ((T : Subgroup (Halpha D hC.alpha)).map
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) : Set _) :=
      Subgroup.mem_map.mpr ⟨x, hxT, rfl⟩
    have hxr : (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) x
        ∈ Set.range r := by
      rw [← O4PlusFrame.inter_eq hr]
      exact ⟨hxTb, hxΘ⟩
    obtain ⟨i, hi⟩ := hxr
    refine Set.mem_range.mpr ⟨i, ?_⟩
    exact (h.injOn hxD (hwD i) (by rw [← hi, hwr i])).symm
  · rintro ⟨i, rfl⟩
    have hriTb : r i ∈ ((T : Subgroup (Halpha D hC.alpha)).map
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) : Set _) := by
      have hmem : r i ∈ ((T : Subgroup (Halpha D hC.alpha)).map
          (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) : Set _)
          ∩ imageClass hC := by
        rw [O4PlusFrame.inter_eq hr]
        exact Set.mem_range_self i
      exact hmem.1
    refine ⟨?_, hwD i⟩
    have hriTb' : r i ∈ Subgroup.map (QuotientGroup.mk' (CFSG.solvableRadical
        (Halpha D hC.alpha))) (T : Subgroup (Halpha D hC.alpha)) := hriTb
    rw [Subgroup.mem_map] at hriTb'
    obtain ⟨t, htT, htπ⟩ := hriTb'
    have hmemK : t⁻¹ * w i ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
      rw [map_mul, map_inv, htπ, hwr i, inv_mul_cancel]
    have hmul : t * (t⁻¹ * w i) ∈ (T : Subgroup _) := T.mul_mem htT (hKT hmemK)
    have heq : t * (t⁻¹ * w i) = w i := by group
    rwa [heq] at hmul

theorem inter_D_eq_of_frameLift (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {w : Fin 4 → Halpha D hC.alpha}
    (hw : (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w) {S : Subgroup G}
    (hS : IsPGroup 2 S)
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    (hd : hC.d ∈ S) :
    (S : Set G) ∩ D = insert hC.d (Set.range fun i => (w i : G)) := by
  classical
  have hD : IsOddTransp D := hC.setup.oddT
  have huD : hC.d ∈ D := hC.hd
  ext x
  constructor
  · rintro ⟨hxS, hxD⟩
    by_cases hxu : x = hC.d
    · exact Or.inl hxu
    · refine Or.inr ?_
      have hcomm : Commute x hC.d :=
        commute_of_mul_mem_of_isPGroup hD hS hxD huD (S.mul_mem hxS hd)
      have hxE : x ∈ DalphaStar D hC.alpha := by
        have hxD' := hxD
        rw [hC.eq_alpha_union] at hxD'
        rcases hxD' with (hxα | hxE) | hxA
        · rw [h.alpha_eq] at hxα
          exact absurd (by simpa using hxα) hxu
        · exact hxE
        · rw [hC.AalphaStar_eq_diff_alpha] at hxA
          exact absurd hcomm hxA.1.2
      have hxH : x ∈ Halpha D hC.alpha := Subgroup.subset_closure hxE
      let Q : Subgroup G := S ⊓ Halpha D hC.alpha
      have hQp : IsPGroup 2 Q := hS.to_le inf_le_left
      have hQH : Q ≤ Halpha D hC.alpha := inf_le_right
      have hTleQ : (T : Subgroup (Halpha D hC.alpha)) ≤ Q.subgroupOf
          (Halpha D hC.alpha) := by
        intro t ht
        rw [Subgroup.mem_subgroupOf]
        exact ⟨hTS (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩), t.2⟩
      have hQsp : IsPGroup 2 (Q.subgroupOf (Halpha D hC.alpha)) :=
        hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
      have hTeq : Q.subgroupOf (Halpha D hC.alpha) = T := T.is_maximal' hQsp hTleQ
      have hxQ : x ∈ Q := ⟨hxS, hxH⟩
      have hxT : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈ (T : Subgroup (Halpha D hC.alpha)) := by
        rw [← hTeq]
        exact Subgroup.mem_subgroupOf.mpr hxQ
      have hxint : (⟨x, hxH⟩ : Halpha D hC.alpha) ∈
          (T : Set (Halpha D hC.alpha)) ∩ DstarH hC :=
        ⟨hxT, (mem_DstarH_iff hC).mpr hxE⟩
      rw [hw] at hxint
      obtain ⟨i, hi⟩ := hxint
      exact ⟨i, by simpa using congrArg Subtype.val hi⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact ⟨hd, huD⟩
    · have hwiT : w i ∈ (T : Set (Halpha D hC.alpha)) := by
        have : w i ∈ (T : Set (Halpha D hC.alpha)) ∩ DstarH hC := by
          rw [hw]
          exact Set.mem_range_self i
        exact this.1
      have hwiD : (w i : G) ∈ D :=
        DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp ((hw ▸ Set.mem_range_self i).2))
      exact ⟨hTS (Subgroup.mem_map.mpr ⟨w i, hwiT, rfl⟩), hwiD⟩

theorem prod_frameLift_ne_one (h : ElevenOneHyp hC) {T : Sylow 2 (Halpha D hC.alpha)}
    {r : Fin 4 → Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hr : O4PlusFrame (imageClass hC) ((T : Subgroup (Halpha D hC.alpha)).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))) r)
    {w : Fin 4 → Halpha D hC.alpha}
    (hwr : ∀ i, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (w i) = r i)
    (hw : (T : Set (Halpha D hC.alpha)) ∩ DstarH hC = Set.range w) {S : Sylow 2 G}
    (hTS : (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ≤ S)
    (hd : hC.d ∈ (S : Subgroup G)) :
    w 0 * w 1 * w 2 * w 3 ≠ 1 := by
  classical
  intro hp
  have hD : IsOddTransp D := hC.setup.oddT
  let x : Fin 4 → G := fun i => (w i : G)
  let X : Subgroup G := Subgroup.closure (Set.range x)
  have hx_in_D : ∀ i, x i ∈ D := fun i =>
    DalphaStar_subset hC.isBlock_alpha
      ((mem_DstarH_iff hC).mp ((hw ▸ Set.mem_range_self i).2))
  have hx_sq : ∀ i, x i * x i = 1 := fun i => hD.mul_self_eq_one (hx_in_D i)
  have hxS : ∀ i, x i ∈ S := fun i =>
    hTS (Subgroup.mem_map.mpr ⟨w i, (hw ▸ Set.mem_range_self i).1, rfl⟩)
  have hxSD : ∀ i, x i ∈ (S : Set G) ∩ D := fun i => ⟨hxS i, hx_in_D i⟩
  have hxcomm : ∀ i j, Commute (x i) (x j) := fun i j =>
    commute_of_mul_mem_of_isPGroup hD S.isPGroup' (hx_in_D i) (hx_in_D j)
      (S.mul_mem (hxS i) (hxS j))
  have hpG : x 0 * x 1 * x 2 * x 3 = 1 := by
    have h := congrArg Subtype.val hp
    simpa [x, Subgroup.coe_mul] using h
  have hx0_eq : x 0 = (x 1 * x 2 * x 3)⁻¹ := by
    have h1 : x 0 * (x 1 * x 2 * x 3) = 1 := by simpa [mul_assoc] using hpG
    exact eq_inv_of_mul_eq_one_left h1
  have hx0clos : x 0 ∈ Subgroup.closure ({x 1, x 2, x 3} : Set G) := by
    rw [hx0_eq]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp)))
  have hXeq : X = Subgroup.closure ({x 1, x 2, x 3} : Set G) := by
    change Subgroup.closure (Set.range x) = Subgroup.closure ({x 1, x 2, x 3} : Set G)
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro g ⟨i, rfl⟩
      fin_cases i
      · exact hx0clos
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      rintro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl <;> exact Subgroup.subset_closure ⟨_, rfl⟩
  have hxH : ∀ i, x i ∈ Halpha D hC.alpha := fun i =>
    Subgroup.subset_closure ((mem_DstarH_iff hC).mp ((hw ▸ Set.mem_range_self i).2))
  have hXH : X ≤ Halpha D hC.alpha := by
    change Subgroup.closure (Set.range x) ≤ Halpha D hC.alpha
    rw [Subgroup.closure_le]
    rintro g ⟨i, rfl⟩
    exact hxH i
  have hSint : (S : Set G) ∩ D = insert hC.d (Set.range fun i => (w i : G)) := by
    simpa only [Sylow.coe_coe] using inter_D_eq_of_frameLift h hw S.isPGroup' hTS hd
  obtain ⟨n, hn, hnu⟩ := sylow_inter_D_transitive hC.setup.isClass hD S
    (hxSD 0) ⟨hd, hC.hd⟩
  have hxi_ne : ∀ i, i ≠ 0 → x i ≠ x 0 := by
    intro i hi h
    have hwi : w i = w 0 := Subtype.ext h
    exact hi (hr.injective (by rw [← hwr i, ← hwr 0, hwi]))
  have hconj_gen : ∀ i, i ≠ 0 → n * x i * n⁻¹ ∈ X := by
    intro i hi
    have hci : n * x i * n⁻¹ ∈ (S : Set G) ∩ D :=
      (Subgroup.mem_set_normalizer_iff.mp hn (x i)).mp (hxSD i)
    have hne : n * x i * n⁻¹ ≠ hC.d := by
      intro hcon
      have h2 : n * x i * n⁻¹ = n * x 0 * n⁻¹ := by rw [hcon, hnu]
      exact hxi_ne i hi (mul_left_cancel (mul_right_cancel h2))
    rw [hSint] at hci
    rcases Set.mem_insert_iff.mp hci with h | h
    · exact absurd h hne
    · obtain ⟨j, hj⟩ := h
      rw [← hj]
      exact Subgroup.subset_closure ⟨j, rfl⟩
  have hconjX : (Subgroup.closure ({x 1, x 2, x 3} : Set G)).map
      (MulAut.conj n).toMonoidHom ≤ X := by
    rw [MonoidHom.map_closure]
    rw [Subgroup.closure_le]
    rintro g ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · simpa using hconj_gen 1 (by decide)
    · simpa using hconj_gen 2 (by decide)
    · simpa using hconj_gen 3 (by decide)
  have huX : hC.d ∈ X := by
    have hmem : (MulAut.conj n) (x 0) ∈ (Subgroup.closure ({x 1, x 2, x 3} : Set G)).map
        (MulAut.conj n).toMonoidHom := Subgroup.mem_map.mpr ⟨x 0, hx0clos, rfl⟩
    rw [show (MulAut.conj n) (x 0) = hC.d from hnu] at hmem
    exact hconjX hmem
  have huH : hC.d ∈ Halpha D hC.alpha := hXH huX
  have huK : (⟨hC.d, huH⟩ : Halpha D hC.alpha) ∈ CFSG.solvableRadical (Halpha D hC.alpha) := by
    rw [h.center, Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    simpa using Subgroup.mem_centralizer_singleton_iff.mp (Halpha_le_centralizer_d hC y.2)
  let y : Fin 3 → G := fun i => x i.succ
  have hy_range : Set.range y = ({x 1, x 2, x 3} : Set G) := by
    ext g; constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp [y]
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  have hcardX : Nat.card X ≤ 8 := by
    have h := card_closure_range_le y (fun i => by simpa [y] using hx_sq i.succ)
      (fun i j => by simpa [y] using hxcomm i.succ j.succ)
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h
    rwa [hXeq, ← hy_range]
  let XH : Subgroup (Halpha D hC.alpha) := X.subgroupOf (Halpha D hC.alpha)
  have hXHcl : XH = Subgroup.closure (Set.range w) := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_subgroupOf] at hz
      have hzX : (z : G) ∈ Subgroup.closure (Set.range x) := hz
      have hmem : (⟨(z : G), hXH hz⟩ : Halpha D hC.alpha) ∈
          Subgroup.closure (Set.range w) := by
        refine Subgroup.closure_induction
          (p := fun g hg => (⟨g, hXH hg⟩ : Halpha D hC.alpha) ∈
            Subgroup.closure (Set.range w)) ?_ ?_ ?_ ?_ hzX
        · intro g hg
          obtain ⟨i, rfl⟩ := hg
          exact Subgroup.subset_closure ⟨i, rfl⟩
        · exact Subgroup.one_mem _
        · intro a b ha hb iha ihb
          simpa using Subgroup.mul_mem _ iha ihb
        · intro a ha iha
          exact Subgroup.inv_mem _ iha
      simpa using hmem
    · rw [Subgroup.closure_le]
      rintro z ⟨i, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure ⟨i, rfl⟩)
  have hXF : Nat.card XH = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  let f : XH →* (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) :=
    (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))).comp XH.subtype
  have hrange8 : Nat.card f.range = 8 := by
    have h1 : f.range = XH.map (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) := by
      rw [MonoidHom.range_eq_map]
      rw [← Subgroup.map_map (K := (⊤ : Subgroup XH))
        (g := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)))
        (f := XH.subtype)]
      congr 1
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1, hXHcl, MonoidHom.map_closure]
    have himg : (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) ''
        Set.range w = Set.range r := by
      ext b; constructor
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, (hwr i).symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨w i, ⟨i, rfl⟩, hwr i⟩
    rw [himg]
    have hr0 : r 0 ∈ Subgroup.closure (Set.range r \ {r 0}) := by
      have h1 : r 0 = (r 1 * r 2 * r 3)⁻¹ := by
        have h2 : r 0 * (r 1 * r 2 * r 3) = 1 := by simpa [mul_assoc] using hr.prod_eq
        exact eq_inv_of_mul_eq_one_left h2
      have hmem : (r 1 * r 2 * r 3)⁻¹ ∈ Subgroup.closure (Set.range r \ {r 0}) := by
        refine Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_)
        · exact Subgroup.subset_closure ⟨⟨1, rfl⟩,
            by simpa using hr.injective.ne (show (1 : Fin 4) ≠ 0 by decide)⟩
        · exact Subgroup.subset_closure ⟨⟨2, rfl⟩,
            by simpa using hr.injective.ne (show (2 : Fin 4) ≠ 0 by decide)⟩
        · exact Subgroup.subset_closure ⟨⟨3, rfl⟩,
            by simpa using hr.injective.ne (show (3 : Fin 4) ≠ 0 by decide)⟩
      exact h1.symm ▸ hmem
    have hclr : Subgroup.closure (Set.range r) =
        Subgroup.closure (Set.range r \ {r 0}) := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro b ⟨i, rfl⟩
        fin_cases i
        · exact hr0
        · exact Subgroup.subset_closure ⟨⟨1, rfl⟩,
            by simpa using hr.injective.ne (show (1 : Fin 4) ≠ 0 by decide)⟩
        · exact Subgroup.subset_closure ⟨⟨2, rfl⟩,
            by simpa using hr.injective.ne (show (2 : Fin 4) ≠ 0 by decide)⟩
        · exact Subgroup.subset_closure ⟨⟨3, rfl⟩,
            by simpa using hr.injective.ne (show (3 : Fin 4) ≠ 0 by decide)⟩
      · exact Subgroup.closure_mono Set.sdiff_subset
    rw [hclr, hr.card_closure 0]
  have hker1 : Nat.card f.ker = 1 := by
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hrange8, hXF] at hcard
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    have := hcardX
    omega
  have hfker : f.ker = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall f.ker).mpr
    intro a ha
    haveI : Subsingleton f.ker := (Nat.card_eq_one_iff_unique.mp hker1).1
    exact congrArg Subtype.val (Subsingleton.elim (⟨a, ha⟩ : f.ker) ⟨1, f.ker.one_mem⟩)
  let uH : XH := ⟨⟨hC.d, huH⟩, Subgroup.mem_subgroupOf.mpr huX⟩
  have huKer : uH ∈ f.ker := by
    exact MonoidHom.mem_ker.mpr ((QuotientGroup.eq_one_iff _).mpr huK)
  rw [hfker] at huKer
  have hu1 : uH = 1 := Subgroup.mem_bot.mp huKer
  have hu2 : (⟨hC.d, huH⟩ : Halpha D hC.alpha) = 1 := by
    simpa [uH] using congrArg (fun y : XH => (y : Halpha D hC.alpha)) hu1
  exact hD.ne_one hC.hd (Subtype.ext_iff.mp hu2)

end ElevenOneHyp

end CFSG.OddTranspositions.PartThree
end
