module

public import CFSG.OddTranspositions.PartThree.Twelve.Eight
public import CFSG.OddTranspositions.PartThree.Twelve.EightChart
public import CFSG.OddTranspositions.PartThree.Twelve.SevenForm
public import CFSG.OddTranspositions.PartThree.Twelve.Branches
import CFSG.OddTranspositions.PartThree.Twelve.EightQuadForm
import CFSG.OddTranspositions.PartThree.Twelve.FourU
import CFSG.OddTranspositions.PartThree.Nine.Setup

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.PartFour
open CFSG.Timmesfeld.Connectivity
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK CFSG.Open
open CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem mem_compSet_map_iff (φ : G ≃* G) (hφ : ∀ z, φ z ∈ D ↔ z ∈ D) {x y d z : G} :
    φ z ∈ compSet D (φ x) (φ y) (φ d) ↔ z ∈ compSet D x y d := by
  have hmaps : ∀ w ∈ commSet D x ∩ commSet D y,
      φ w ∈ commSet D (φ x) ∩ commSet D (φ y) := fun w hw =>
    ⟨(mem_commSet_map_iff φ hφ).mpr hw.1, (mem_commSet_map_iff φ hφ).mpr hw.2⟩
  have hmaps' : ∀ w ∈ commSet D (φ x) ∩ commSet D (φ y),
      φ.symm w ∈ commSet D x ∩ commSet D y := fun w hw =>
    ⟨(mem_commSet_map_iff φ hφ).mp (by simpa using hw.1),
      (mem_commSet_map_iff φ hφ).mp (by simpa using hw.2)⟩
  unfold compSet
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_inter_iff,
    mem_commSet_map_iff φ hφ, mem_commSet_map_iff φ hφ]
  constructor
  · rintro ⟨hz, hreach⟩
    exact ⟨hz, by simpa using reach_map_of_mapsTo φ.symm.toMonoidHom hmaps' hreach⟩
  · rintro ⟨hz, hreach⟩
    exact ⟨hz, by simpa using reach_map_of_mapsTo φ.toMonoidHom hmaps hreach⟩

theorem isOrthMarked_compSet_pivot_u (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {x y : G} (hx : x ∈ commSet D hC.d) (hy : y ∈ commSet D hC.d) (hxy : ¬ Commute x y) :
    IsOrthMarked (compSet D x y hC.d) 4 f := by
  have hd := d_mem_commSet_inter hC hx hy
  obtain ⟨-, t, ht, hOt⟩ := twelveSix_u_component hIH hC hMZ hα hs hn hf hU hx hy hxy
  exact isOrthMarked_compSet_of_isOrthReflection hC.setup.normal hC.setup.oddT
    (fun v hv => localPivot_of_mem_u hC hMZ hα hs hn hf hU hv.1.1.1
      ⟨hx.1, hv.1.1.2.1.symm, fun h => hv.1.1.2.2 h.symm⟩
      ⟨hy.1, hv.1.2.2.1.symm, fun h => hv.1.2.2.2 h.symm⟩ hxy)
    (not_isSolvable_closure_of_subset_u hC hMZ hα hs hn hf hU hx hy hxy
      (gammaAt_self_subset_compSet hd)) ht hOt

theorem isOrthMarked_compSet_u (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {v w : G} (hv : v ∈ commSet D hC.d) (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hwv : Commute w v) :
    IsOrthMarked (compSet D hC.d w v) 4 f := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hv.1 hC.hd)
  set φ := MulAut.conj g with hφdef
  have hφD : ∀ z, φ z ∈ D ↔ z ∈ D := by
    intro z
    rw [MulAut.conj_apply]
    refine ⟨fun h => ?_, fun h => hC.setup.conj_mem g h⟩
    have := hC.setup.conj_mem g⁻¹ h
    simpa [mul_assoc] using this
  have hφv : φ v = hC.d := by rw [MulAut.conj_apply, hg]
  have hwv' : w ≠ v := by
    rintro rfl
    exact hwd hv.2.1
  have hx : φ hC.d ∈ commSet D hC.d := by
    have h := (mem_commSet_map_iff φ hφD (a := v) (z := hC.d)).mpr
      ⟨hC.hd, hv.2.1.symm, fun h => hv.2.2 h.symm⟩
    rwa [hφv] at h
  have hy : φ w ∈ commSet D hC.d := by
    have h := (mem_commSet_map_iff φ hφD (a := v) (z := w)).mpr ⟨hw, hwv, hwv'⟩
    rwa [hφv] at h
  have hxy : ¬ Commute (φ hC.d) (φ w) := fun h => hwd ((commute_map_iff φ).mp h).symm
  have hM := (isOrthMarked_compSet_pivot_u hIH hC hMZ hα hs hn hf hU hx hy hxy).preimage φ
  have hset : φ ⁻¹' compSet D (φ hC.d) (φ w) hC.d = compSet D hC.d w v := by
    rw [show compSet D (φ hC.d) (φ w) hC.d = compSet D (φ hC.d) (φ w) (φ v) from
      congrArg (compSet D (φ hC.d) (φ w)) hφv.symm]
    ext z
    rw [Set.mem_preimage, mem_compSet_map_iff φ hφD]
  rwa [hset] at hM

private theorem uChart_kFactsSuProjTv_smul {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {v : Fin 4 → F}
    (hv : herm (unitaryInvolution F 2 f) v v = 0) {μ : F}
    (hμ : unitaryInvolution F 2 f μ * μ = 1) :
    kFactsSuProjTv hF 4 (μ • v) 1 = kFactsSuProjTv hF 4 v 1 := by
  calc kFactsSuProjTv hF 4 (μ • v) 1
      = kFactsSuProjTv hF 4 v (unitaryInvolution F 2 f μ * μ * 1) :=
        kFacts_suProjTv_smul_vec hF hv
          (by rw [map_one]; exact CharTwo.add_self_eq_zero 1) μ
    _ = kFactsSuProjTv hF 4 v 1 := by rw [hμ, mul_one]

omit [Finite G] in
theorem isMarkedComponentU_of_isOrthMarked {hC : HypothesisC D} {hα : hC.alpha = {hC.d}}
    {f : ℕ} (hf : 2 ≤ f) {F : Type} [Field F] [Finite F] [CharP F 2]
    {hF : Nat.card F = (2 ^ f) ^ 2} (c : UChart hC hα f F hF) {Γ : Set G}
    (hΓsub : Γ ⊆ commSet D hC.d) (hΓ : IsOrthMarked Γ 4 f) :
    IsMarkedComponentU hC f Γ := by
  classical
  obtain ⟨K, hK, hKf, hK2, Q₀, ι, hcard, hQ₀, h1, hsurj, hinj, hconj, hcomm, hgen⟩ := hΓ
  choose! zOf hzOfΓ hzOfι using hsurj
  let a : (Fin 4 → K) → (Fin 4 → F) := fun x => c.vec (zOf x)
  have hzOf : ∀ z ∈ Γ, zOf (ι z) = z := fun z hz =>
    hinj (hzOfΓ _ (h1 z hz)) hz (hzOfι _ (h1 z hz))
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hA1 : ∀ y, Q₀ y = 1 → a y ≠ 0 ∧
      herm (unitaryInvolution F 2 f) (a y) (a y) = 0 := by
    intro y hy
    have hyD := hΓsub (hzOfΓ y hy)
    exact ⟨c.vec_ne_zero _ hyD, c.herm_self _ hyD⟩
  have hA2 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 →
      (herm (unitaryInvolution F 2 f) (a x) (a y) = 0 ↔ QuadraticMap.polar Q₀ x y = 0) := by
    intro x hx y hy
    have hxΓ := hzOfΓ x hx
    have hyΓ := hzOfΓ y hy
    rw [← c.commute_iff (zOf x) (hΓsub hxΓ) (zOf y) (hΓsub hyΓ),
      hcomm (zOf x) hxΓ (zOf y) hyΓ, hzOfι x hx, hzOfι y hy]
  have hA3 : ∀ x, Q₀ x = 1 → ∀ y, Q₀ y = 1 → ∃ μ : F,
      unitaryInvolution F 2 f μ * μ = 1 ∧
        a (CFSG.ClassicalGroups.Orthogonal.reflect Q₀ x y) =
          μ • (a y + herm (unitaryInvolution F 2 f) (a x) (a y) • a x) := by
    intro x hx y hy
    have hxΓ := hzOfΓ x hx
    have hyΓ := hzOfΓ y hy
    have hxD := hΓsub hxΓ
    have hyD := hΓsub hyΓ
    obtain ⟨hmem, he⟩ := hconj (zOf x) hxΓ (zOf y) hyΓ
    have hz : zOf (CFSG.ClassicalGroups.Orthogonal.reflect Q₀ x y) = zOf x * zOf y * (zOf x)⁻¹ := by
      rw [← hzOfι x hx, ← hzOfι y hy, ← he, hzOfι x hx, hzOfι y hy, hzOf _ hmem]
    obtain ⟨μ, hμ, hvec⟩ := c.conj_vec hxD hyD
    exact ⟨μ, hμ, by
      show c.vec (zOf (CFSG.ClassicalGroups.Orthogonal.reflect Q₀ x y)) =
        μ • (c.vec (zOf y) + herm (unitaryInvolution F 2 f) (c.vec (zOf x))
          (c.vec (zOf y)) • c.vec (zOf x))
      rw [hz, hvec]⟩
  obtain ⟨U, Q, hUQ, hcentres, hcv⟩ :=
    exists_isFixedQuadForm_of_unitaryMarked hcard hF hK4 hQ₀ hA1 hA2 hA3 hgen
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, c.e, U, Q, hUQ, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hxΓ, rfl⟩
    have hzD : (x : G) ∈ commSet D hC.d := hΓsub hxΓ
    have hxmap : c.e (QuotientGroup.mk (QuotientGroup.mk x)) =
        kFactsSuProjTv hF 4 (c.vec (x : G)) 1 := by
      have hsub : (⟨(x : G), mem_Halpha_of_mem_commSet hC hα hzD⟩ :
          Halpha D hC.alpha) = x := Subtype.ext rfl
      have h := c.map_eq (x : G) hzD
      rwa [hsub] at h
    obtain ⟨μ, hμ, hμU, hQμ⟩ := hcentres (ι (x : G)) (h1 _ hxΓ)
    have haz : a (ι (x : G)) = c.vec (x : G) := by
      show c.vec (zOf (ι (x : G))) = c.vec (x : G)
      rw [hzOf (x : G) hxΓ]
    refine ⟨μ • c.vec (x : G), by simpa only [haz] using hμU,
      by simpa only [haz] using hQμ, ?_⟩
    rw [uChart_kFactsSuProjTv_smul hF (c.herm_self (x : G) hzD) hμ]
    exact hxmap
  · rintro ⟨a', ha', hQa', rfl⟩
    obtain ⟨v, hv, μ, hμ, hav⟩ := hcv a' ha' hQa'
    have hzD : zOf v ∈ commSet D hC.d := hΓsub (hzOfΓ v hv)
    refine ⟨⟨zOf v, mem_Halpha_of_mem_commSet hC hα hzD⟩, hzOfΓ v hv, ?_⟩
    have hmap := c.map_eq (zOf v) hzD
    have hav' : a' = μ • c.vec (zOf v) := by
      rw [hav]
    dsimp only
    rw [hmap, hav']
    exact (uChart_kFactsSuProjTv_smul hF (c.herm_self (zOf v) hzD) hμ).symm

theorem isMarkedComponentU_compSet (hIH : Theorem4Below (Nat.card G)) (hC : HypothesisC D)
    (hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha))
    (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {n f : ℕ} (hn : 4 ≤ n) (hf : 2 ≤ f)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) n f s)
    {v w : G} (hv : v ∈ commSet D hC.d) (hw : w ∈ D) (hwd : ¬ Commute w hC.d)
    (hwv : Commute w v) :
    IsMarkedComponentU hC f (compSet D hC.d w v) := by
  obtain rfl := eq_four_of_isUnitaryTransvection hIH hC hMZ hα hs hn hf hU
  obtain ⟨F, _, _, _, hF, ⟨c⟩⟩ := exists_uChart hC hMZ hα hs hU
  exact isMarkedComponentU_of_isOrthMarked hf c
    (Set.Subset.trans (compSet_subset D hC.d w v) Set.inter_subset_left)
    (isOrthMarked_compSet_u hIH hC hMZ hα hs le_rfl hf hU hv hw hwd hwv)

theorem exists_not_commute_commonNeighbour (hC : HypothesisC D) (hα : hC.alpha = {hC.d})
    {s : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)} (hs : s ∈ imageClass hC)
    {m f : ℕ} (hm : 4 ≤ m)
    (hU : IsUnitaryTransvection
      (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) m f s) :
    ∃ w ∈ D, ¬ Commute w hC.d ∧ ∃ v ∈ commSet D hC.d, Commute w v := by
  have hZ := center_Hbar_eq_bot hC
  have hne := (subset_rootBlock_and_ne_of_isUnitaryTransvection (imageClass_isClass hC) hZ hs
    hm hU).2
  obtain ⟨b, hb, hsb⟩ := exists_not_commute_of_rootBlock_ne (imageClass_isClass hC) hs hne s hs
  obtain ⟨xH, hxH, rfl⟩ := hs
  obtain ⟨yH, hyH, rfl⟩ := hb
  have hx : (xH : G) ∈ commSet D hC.d :=
    (Nine.DalphaStar_eq_commSet hC hα).subset ((mem_DstarH_iff hC).mp hxH)
  have hy : (yH : G) ∈ commSet D hC.d :=
    (Nine.DalphaStar_eq_commSet hC hα).subset ((mem_DstarH_iff hC).mp hyH)
  have hxy : ¬ Commute (xH : G) (yH : G) := fun h =>
    hsb ((show Commute xH yH from Subtype.ext h.eq).map
      (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))))
  obtain ⟨g, hg⟩ := isConj_iff.mp (hC.setup.isConj hx.1 hC.hd)
  refine ⟨g * (yH : G) * g⁻¹, hC.setup.conj_mem g hy.1, ?_, g * hC.d * g⁻¹, ?_, ?_⟩
  · intro h
    rw [← hg] at h
    exact (fun h' => hxy h'.symm) ((Commute.conj_iff g).1 h)
  · refine ⟨hC.setup.conj_mem g hC.hd, ?_, ?_⟩
    · have h1 := (Commute.conj_iff g).2 hx.2.1
      rw [hg] at h1
      exact h1.symm
    · intro h
      apply hx.2.2
      have h1 : g * (xH : G) * g⁻¹ = g * hC.d * g⁻¹ := by rw [hg, h]
      exact mul_left_cancel (mul_right_cancel h1)
  · exact (Commute.conj_iff g).2 hy.2.1

theorem twelveEightU_holds : TwelveEightU := by
  intro G _ _ D hC hIH _ _ hMZ _ hα s hs f hf hU
  obtain ⟨w, hw, hwd, v, hv, hwv⟩ := exists_not_commute_commonNeighbour hC hα hs le_rfl hU
  exact twelveEight hC hMZ hα hs hf hU hw hwd
    (isMarkedComponentU_compSet hIH hC hMZ hα hs le_rfl hf hU hv hw hwd hwv)

end CFSG.OddTranspositions.PartThree

end
