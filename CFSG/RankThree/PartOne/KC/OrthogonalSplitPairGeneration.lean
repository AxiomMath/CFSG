module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitCompletion
import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2 CFSG.Timmesfeld.ClassicalOrders
  CFSG.AGLEmbeddingD2.SquareSpinMinus CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted

private theorem eichler_cross_mem
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) {u v a a' : V}
    (_hu : Q u = 0) (hv : Q v = 0)
    (huv : polar Q u v = 0) (hua : polar Q u a = 0)
    (hua' : polar Q u a' = 0) (hva : polar Q v a = 0)
    (hva' : polar Q v a' = 0) (haa' : polar Q a a' ≠ 0)
    (H : Subgroup (V ≃ₗ[K] V))
    (ha : eichler Q u a ∈ H)
    (ha' : ∀ t : K, eichler Q v (t • a') ∈ H) (c : K) :
    eichler Q u (c • v) ∈ H := by
  let t : K := -(c / polar Q a a')
  let g := eichler Q v (t • a')
  have hvt : polar Q v (t • a') = 0 := by
    rw [polar_smul_right, hva', smul_zero]
  have hgu : g u = u := by
    dsimp only [g]
    rw [eichler_apply hv hvt, huv, polar_smul_right, hua']
    simp
  have hga : g a = a + c • v := by
    have hav : polar Q a v = 0 := by rw [polar_comm]; exact hva
    have ht : -(t * polar Q a a') = c := by
      dsimp [t]
      field_simp [haa']
    dsimp only [g]
    rw [eichler_apply hv hvt, hav, polar_smul_right, smul_eq_mul]
    simp only [zero_smul, add_zero, mul_zero]
    rw [sub_eq_add_neg, ← neg_smul, ht]
  have hgH : g ∈ H := ha' t
  have hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q (eichler_mem_elementaryGroup Q v (t • a'))
  have hconj : eichler Q u (a + c • v) ∈ H := by
    have h := H.mul_mem (H.mul_mem hgH ha) (H.inv_mem hgH)
    rwa [eichler_conj hgO, hgu, hga] at h
  have huc : polar Q u (c • v) = 0 := by
    rw [polar_smul_right, huv, smul_zero]
  rw [← eichler_mul hua huc] at hconj
  have h := H.mul_mem (H.inv_mem ha) hconj
  simpa only [inv_mul_cancel_left] using h

private theorem finrank_coordinate_support
    {F ι : Type*} [Field F] [Fintype ι] (T : Finset ι) :
    finrank F (supp F (T : Set ι)) = T.card := by
  classical
  let f : supp F (T : Set ι) →ₗ[F] (T → F) :=
    { toFun := fun v i => v.1 i.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro v w h
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ T
      · exact congrFun h ⟨i, hi⟩
      · rw [v.2 i (by simpa using hi), w.2 i (by simpa using hi)]
    · intro g
      let v : ι → F := fun i => if hi : i ∈ T then g ⟨i, hi⟩ else 0
      have hv : v ∈ supp F (T : Set ι) := by
        intro i hi
        simp only [v, dif_neg (show i ∉ T from hi)]
      refine ⟨⟨v, hv⟩, ?_⟩
      funext i
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, v, dif_pos i.2]
  calc
    _ = finrank F (T → F) := (LinearEquiv.ofBijective f hf).finrank_eq
    _ = T.card := by simp [Module.finrank_fintype_fun_eq_card]

private theorem finrank_anchored_pair
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (i j : Fin (n - 1)) (hij : i ≠ j) :
    finrank F (anchoredSupport F n {i, j}) = 6 := by
  rw [anchoredSupport, finrank_coordinate_support]
  simp [activeCoords, eCoords, fCoords, planeCoords, hij, hij.symm]

private theorem orthExtend_eichler_eq
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) {P : Submodule F V}
    (hP : IsCompl P (suppPerp Q P)) (u w : P)
    (hu : Q (u : V) = 0) (huw : polar Q (u : V) (w : V) = 0) :
    orthExtend hP (eichler (Q.comp P.subtype) u w) =
      eichler Q (u : V) (w : V) := by
  have hu' : (Q.comp P.subtype) u = 0 := hu
  have huw' : polar (Q.comp P.subtype) u w = 0 := by
    simpa only [polar_comp_subtype_eq] using huw
  have happly (a : P) :
      ((eichler (Q.comp P.subtype) u w) a : V) =
        eichler Q (u : V) (w : V) (a : V) := by
    rw [eichler_apply hu' huw', eichler_apply hu huw]
    simp only [polar_comp_subtype_eq, QuadraticMap.comp_apply,
      Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, Submodule.subtype_apply]
  ext x
  obtain ⟨a, ha, z, hz, rfl⟩ := suppExists_add_of_isCompl hP x
  have hz' : eichler Q (u : V) (w : V) z = z :=
    eichler_apply_of_polar_eq_zero
      (by rw [polar_comm]; exact mem_suppPerp.mp hz _ u.2)
      (by rw [polar_comm]; exact mem_suppPerp.mp hz _ w.2)
  rw [orthExtend_apply hP _ ⟨a, ha⟩ ⟨z, hz⟩, map_add, hz', happly]

private theorem eichler_mem_anchored
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 4 ≤ Nat.card F) {S : Finset (Fin (n - 1))} {u w : Vm n F}
    (hu : u ∈ anchoredSupport F n S) (hw : w ∈ anchoredSupport F n S)
    (hQu : quadMinus n F b c u = 0) (huw : polar (quadMinus n F b c) u w = 0) :
    eichler (quadMinus n F b c) u w ∈
      supportedDerived (quadMinus n F b c) (anchoredSupport F n S) := by
  obtain ⟨a, ha0, ha1⟩ :=
    CFSG.RankThree.GF2n.Stroth80.Satz5.exists_ne_zero_one (K := F) (by omega)
  refine eichler_mem_supportedDerived hu hw hQu huw ?_
  exact CFSG.SeitzReduction.OmegaPilot.eichler_mem_orthDerived_of_ne_zero_ne_one
    (nondegenerate_polarBilin_restrict (polarNondegOn_anchoredSupport hirr S)) ha0 ha1 _ _

private theorem anchored_pair_perp_decompose
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (i j : Fin (n - 1)) (hij : i ≠ j) (w : Vm n F)
    (hw : w ∈ anchoredSupport F n {i, j})
    (hei : w (.inl i) = 0) (hfi : w (.inr (.inl i)) = 0) :
    w = planeVec n (fun t => w (.inr (.inr t))) +
      w (.inl j) • eVec n j + w (.inr (.inl j)) • fVec n j := by
  funext a
  rcases a with k | k | t
  · by_cases hki : k = i
    · subst k
      simp [planeVec, eVec, fVec, Pi.single_apply, hij, hei]
    · by_cases hkj : k = j
      · subst k
        simp [planeVec, eVec, fVec, Pi.single_apply]
      · have hwk : w (.inl k) = 0 := hw _ (by
          simp [activeCoords, eCoords, fCoords, planeCoords, hki, hkj])
        simp [planeVec, eVec, fVec, Pi.single_apply, hkj, hwk]
  · by_cases hki : k = i
    · subst k
      simp [planeVec, eVec, fVec, Pi.single_apply, hij, hfi]
    · by_cases hkj : k = j
      · subst k
        simp [planeVec, eVec, fVec, Pi.single_apply]
      · have hwk : w (.inr (.inl k)) = 0 := hw _ (by
          simp [activeCoords, eCoords, fCoords, planeCoords, hki, hkj])
        simp [planeVec, eVec, fVec, Pi.single_apply, hkj, hwk]
  · simp [planeVec, eVec, fVec, Pi.single_apply]

private theorem eichler_pair_perp_mem
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 4 ≤ Nat.card F) (i j : Fin (n - 1)) (hij : i ≠ j)
    (w : Vm n F) (hw : w ∈ anchoredSupport F n {i, j})
    (hei : w (.inl i) = 0) (hfi : w (.inr (.inl i)) = 0) :
    eichler (quadMinus n F b c) (eVec n i) w ∈
      supportedDerived (quadMinus n F b c) (anchoredSupport F n {i}) ⊔
        supportedDerived (quadMinus n F b c) (anchoredSupport F n {j}) := by
  classical
  let Q := quadMinus n F b c
  let H := supportedDerived Q (anchoredSupport F n {i}) ⊔
    supportedDerived Q (anchoredSupport F n {j})
  let a : Vm n F := planeVec n (Pi.single 0 1)
  let a' : Vm n F := planeVec n (Pi.single 1 1)
  have hb : b ≠ 0 := by
    have h := discr_ne_zero_of_finite (K := F) hirr
    have h4 : (4 : F) = 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num, CharTwo.two_eq_zero, zero_mul]
    rw [h4, zero_mul, sub_zero] at h
    exact (pow_ne_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h
  have hui : Q (eVec n i) = 0 := quadMinus_eVec n b c i
  have huA (p : Fin 2 → F) : polar Q (eVec n i) (planeVec n p) = 0 := by
    simp [Q, eVec, planeVec, polar_quadMinus, Pi.single_apply]
  have huiS : eVec n i ∈ anchoredSupport F n {i} := by
    simpa [eVec, minusPos] using
      (single_mem_anchoredSupport (n := n) (F := F) (S := {i}) (by simp) true 1)
  have hanchor (p : Fin 2 → F) : eichler Q (eVec n i) (planeVec n p) ∈ H :=
    (show supportedDerived Q (anchoredSupport F n {i}) ≤ H from le_sup_left)
      (eichler_mem_anchored hirr hcard huiS (planeVec_mem_anchoredSupport {i} p)
      hui (huA p))
  have hcross (s : Bool) (d : F) : eichler Q (eVec n i) (d • minusVec n j s) ∈ H := by
    have hv : Q (minusVec n j s) = 0 := quadMinus_minusVec n b c j s
    have hUV : polar Q (eVec n i) (minusVec n j s) = 0 := by
      cases s <;> simp [Q, eVec, minusVec_eq_single, minusPos,
        polar_quadMinus, Pi.single_apply, hij, hij.symm]
    have hVA (p : Fin 2 → F) : polar Q (minusVec n j s) (planeVec n p) = 0 :=
      polar_minusVec_planeVec n b c j s p
    have hVS : minusVec n j s ∈ anchoredSupport F n {j} := by
      rw [minusVec_eq_single]
      exact single_mem_anchoredSupport (by simp) s 1
    have hAB : polar Q a a' ≠ 0 := by
      simpa [Q, a, a', planeVec, polar_quadMinus, Pi.single_apply] using hb
    refine eichler_cross_mem Q hui hv hUV (huA _) (huA _) (hVA _) (hVA _) hAB H
      (hanchor _) ?_ d
    intro t
    apply (show supportedDerived Q (anchoredSupport F n {j}) ≤ H from le_sup_right)
    refine eichler_mem_anchored hirr hcard hVS
      ((anchoredSupport F n {j}).smul_mem t (planeVec_mem_anchoredSupport {j} _)) hv ?_
    rw [polar_smul_right, hVA, smul_zero]
  have hUe : polar Q (eVec n i) (w (.inl j) • eVec n j) = 0 := by
    simp [Q, eVec, polar_quadMinus, Pi.single_apply, hij, hij.symm]
  have hUf : polar Q (eVec n i) (w (.inr (.inl j)) • fVec n j) = 0 := by
    simp [Q, eVec, fVec, polar_quadMinus, Pi.single_apply, hij, hij.symm]
  rw [anchored_pair_perp_decompose i j hij w hw hei hfi,
    ← eichler_mul (by rw [polar_add_right, huA, hUe, add_zero]) hUf,
    ← eichler_mul (huA _) hUe]
  exact H.mul_mem (H.mul_mem (hanchor _)
    (by simpa [minusVec_eq_single, minusPos, eVec] using hcross true (w (.inl j))))
    (by simpa [minusVec_eq_single, minusPos, fVec] using hcross false (w (.inr (.inl j))))

private theorem supported_anchored_pair_generation
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 4 ≤ Nat.card F) (i j : Fin (n - 1)) (hij : i ≠ j) :
    supportedDerived (quadMinus n F b c) (anchoredSupport F n {i, j}) =
      supportedDerived (quadMinus n F b c) (anchoredSupport F n {i}) ⊔
        supportedDerived (quadMinus n F b c) (anchoredSupport F n {j}) := by
  classical
  let Q := quadMinus n F b c
  let P := anchoredSupport F n {i, j}
  let R := Q.comp P.subtype
  let H := supportedDerived Q (anchoredSupport F n {i}) ⊔
    supportedDerived Q (anchoredSupport F n {j})
  have hreg : PolarNondegOn Q P := polarNondegOn_anchoredSupport hirr {i, j}
  have hnd : (polarBilin R).Nondegenerate := nondegenerate_polarBilin_restrict hreg
  let hP := isCompl_suppPerp hreg
  let ρ : Gom R →* (Vm n F ≃ₗ[F] Vm n F) :=
    (orthExtend hP).comp (elementaryGroup R).subtype
  let T := H.comap ρ
  have heiP : eVec n i ∈ P := by
    simpa [eVec, minusPos] using
      (single_mem_anchoredSupport (n := n) (F := F) (S := {i, j}) (by simp) true 1)
  have hfiP : fVec n i ∈ P := by
    simpa [fVec, minusPos] using
      (single_mem_anchoredSupport (n := n) (F := F) (S := {i, j}) (by simp) false 1)
  let e : P := ⟨eVec n i, heiP⟩
  let f : P := ⟨fVec n i, hfiP⟩
  let a : P := ⟨planeVec n (Pi.single 0 1), planeVec_mem_anchoredSupport {i, j} _⟩
  have he : R e = 0 := quadMinus_eVec n b c i
  have hf : R f = 0 := quadMinus_fVec n b c i
  have hef : polar R f e ≠ 0 := by
    simp [R, Q, f, e, fVec, eVec, polar_comp_subtype_eq, polar_quadMinus, Pi.single_apply]
  have hfa : polar R f a = 0 := by
    simp [R, Q, f, a, fVec, planeVec, polar_comp_subtype_eq, polar_quadMinus, Pi.single_apply]
  have hQa : R a ≠ 0 := by
    change quadMinus n F b c (planeVec n (Pi.single 0 1)) ≠ 0
    rw [quadMinus_planeVec]
    simp [Pi.single_apply]
  have hρ (u w : P) (hu : R u = 0) (huw : polar R u w = 0) :
      ρ (eichlerG R u w) = eichler Q (u : Vm n F) (w : Vm n F) := by
    change orthExtend hP (eichler R u w) = _
    exact orthExtend_eichler_eq Q hP u w hu
      (by simpa only [R, polar_comp_subtype_eq] using huw)
  have hL : Lom R e ≤ T := by
    intro g hg
    obtain ⟨w, hew, hwg⟩ := mem_rootGroup.mp hg
    have hg' : g = eichlerG R e w := Subtype.ext hwg.symm
    rw [hg']
    obtain ⟨w', hfw', hew', -, hEq⟩ :=
      exists_perp_eichlerG_eq (Q := R) (e := f) (f := e) he hef hew
    rw [← hEq]
    change ρ (eichlerG R e w') ∈ H
    rw [hρ e w' he hew']
    have hwi : (w' : Vm n F) (.inl i) = 0 := by
      simpa [R, Q, f, fVec, polar_comp_subtype_eq, polar_quadMinus, Pi.single_apply] using hfw'
    have hwfi : (w' : Vm n F) (.inr (.inl i)) = 0 := by
      simpa [R, Q, e, eVec, polar_comp_subtype_eq, polar_quadMinus, Pi.single_apply] using hew'
    exact eichler_pair_perp_mem hirr hcard i j hij w' w'.2 hwi hwfi
  have hA : eichlerG R f a ∈ T := by
    change ρ (eichlerG R f a) ∈ H
    rw [hρ f a hf hfa]
    apply (show supportedDerived Q (anchoredSupport F n {i}) ≤ H from le_sup_left)
    refine eichler_mem_anchored hirr hcard ?_ (planeVec_mem_anchoredSupport {i} _) ?_ ?_
    · simpa [f, fVec, minusPos] using
        (single_mem_anchoredSupport (n := n) (F := F) (S := {i}) (by simp) false 1)
    · exact hf
    · simpa only [R, polar_comp_subtype_eq] using hfa
  have hT : T = ⊤ := by
    apply top_unique
    rw [← closure_Lom_union_eichlerG hnd he hf
      (by rwa [polar_comm]) hfa hQa]
    exact (Subgroup.closure_le T).mpr (Set.union_subset hL (Set.singleton_subset_iff.mpr hA))
  have hE : orthDerived R = elementaryGroup R :=
    CFSG.LocalAnalysis.GLTheoremA.T173U.orthDerived_eq_elementaryGroup_of_three_le hnd
      (by decide : 3 ≤ (3 : ℕ)) (by simpa [R, P] using finrank_anchored_pair i j hij)
  apply le_antisymm
  · change supportedDerived Q P ≤ H
    rw [← map_orthDerived_orthExtend_eq_supportedDerived hP, hE]
    rintro x ⟨g, hg, rfl⟩
    have h : (⟨g, hg⟩ : Gom R) ∈ T := by rw [hT]; trivial
    exact h
  · refine sup_le ?_ ?_
    · exact supportedDerived_le_supportedDerived_of_le
        (anchoredSupport_mono (by simp : ({i} : Finset (Fin (n - 1))) ⊆ {i, j}))
        (nondegenerate_polarBilin_restrict (polarNondegOn_anchoredSupport hirr {i})) hnd
    · exact supportedDerived_le_supportedDerived_of_le
        (anchoredSupport_mono (by simp : ({j} : Finset (Fin (n - 1))) ⊆ {i, j}))
        (nondegenerate_polarBilin_restrict (polarNondegOn_anchoredSupport hirr {j})) hnd

theorem chartSubgroup_pair_eq_sup_singletons
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {r : ℕ} {b c : F} (hcard : 4 ≤ Nat.card F)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) {i, j} =
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) {i} ⊔
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) {j} := by
  let Q := quadMinus (r + 2) F b c
  have hle (S : Finset (Fin (r + 1))) :
      supportedDerived Q (anchoredSupport F (r + 2) S) ≤ orthDerived Q :=
    supportedDerived_le_orthDerived_of_regular (Q := Q)
      (A := anchoredSupport F (r + 2) S)
      (nondegenerate_polarBilin_restrict
        (polarNondegOn_anchoredSupport (n := r + 2) (F := F) (b := b) (c := c) hirr S))
  change (supportedDerived Q (anchoredSupport F (r + 2) {i, j})).subgroupOf
      (orthDerived Q) =
    (supportedDerived Q (anchoredSupport F (r + 2) {i})).subgroupOf (orthDerived Q) ⊔
      (supportedDerived Q (anchoredSupport F (r + 2) {j})).subgroupOf (orthDerived Q)
  exact (congrArg
    (fun S : Subgroup (Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) => S.subgroupOf (orthDerived Q))
    (supported_anchored_pair_generation (n := r + 2) (F := F) (b := b) (c := c)
      hirr hcard i j hij)).trans
      (Subgroup.subgroupOf_sup (hle {i}) (hle {j}))

end CFSG.RankThree.PartOne.KCOrthogonal

end
