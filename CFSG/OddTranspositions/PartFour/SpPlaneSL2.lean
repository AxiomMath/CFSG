module

public import CFSG.OddTranspositions.PartFour.SeventeenFourSp
public import CFSG.LieType.SeitzGeneration.RootPairSpBlock
import CFSG.GroupTheory.SteinbergBKLinearPlaneSL2
import CFSG.LieType.SeitzGeneration.RootPairSp
import CFSG.LocalAnalysis.StandardType.GGRankOneSl2
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Inv
import CFSG.LocalAnalysis.SeitzReduction.F4PilotNonsplitSL2
public import CFSG.RankThree.PartOne.CTP.SeitzSpClosure

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.PartOne.CTP
open CFSG.RankThree.Classical
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LieType.SeitzGeneration Matrix
open scoped Matrix

variable {k : ℕ} {F : Type} [Field F]

theorem spForm_single_inl_zero_inr_zero (hk : 0 < k) :
    spForm k F (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1) = 1 := by
  rw [RootPair.spForm_lr]
  simp

noncomputable def planeSL2 (hk : 0 < k) : Subgroup ↥(StatedSp k F) :=
  (RootPair.spSL2Hom (spForm_single_inl_zero_inr_zero (F := F) hk)).range

private noncomputable abbrev spPlaneSL2Hom (hk : 0 < k) :
    SpecialLinearGroup (Fin 2) F →* ↥(StatedSp k F) :=
  RootPair.spSL2Hom (spForm_single_inl_zero_inr_zero (F := F) hk)

private theorem spPlane_spSL2Hom_planeEmb {r : ℕ} {K : Type} [Field K]
    {e f : Fin r ⊕ Fin r → K} (hef : spForm r K e f = 1)
    (g : SpecialLinearGroup (Fin 2) K) (a : Fin 2 → K) :
    spEnd (RootPair.spSL2Hom hef g) (RootPair.planeEmb e f a) =
      RootPair.planeEmb e f ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ a) := by
  rw [RootPair.spEnd_spSL2Hom, RootPair.planeExt, RootPair.planeProj_emb hef,
    ← RootPair.planeEmb_add]
  congr 1
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

theorem spPlane_spSL2Hom_injective {r : ℕ} {K : Type} [Field K]
    {e f : Fin r ⊕ Fin r → K} (hef : spForm r K e f = 1) :
    Function.Injective (RootPair.spSL2Hom hef) := by
  intro g h hgh
  have hcol : ∀ y : Fin 2 → K,
      (g : Matrix (Fin 2) (Fin 2) K) *ᵥ y = (h : Matrix (Fin 2) (Fin 2) K) *ᵥ y := by
    intro y
    have h1 : RootPair.planeProj e f
        (spEnd (RootPair.spSL2Hom hef g) (RootPair.planeEmb e f y)) =
        (g : Matrix (Fin 2) (Fin 2) K) *ᵥ y := by
      rw [RootPair.spEnd_spSL2Hom, RootPair.planeProj_ext hef, RootPair.planeProj_emb hef]
    have h2 : RootPair.planeProj e f
        (spEnd (RootPair.spSL2Hom hef h) (RootPair.planeEmb e f y)) =
        (h : Matrix (Fin 2) (Fin 2) K) *ᵥ y := by
      rw [RootPair.spEnd_spSL2Hom, RootPair.planeProj_ext hef, RootPair.planeProj_emb hef]
    have h3 := congrArg (fun s => RootPair.planeProj e f
      (spEnd s (RootPair.planeEmb e f y))) hgh
    rw [h1, h2] at h3
    exact h3
  apply Subtype.ext
  ext i j
  fin_cases j
  · simpa [Matrix.mulVec_single_one, Matrix.col] using congrFun (hcol (Pi.single 0 1)) i
  · simpa [Matrix.mulVec_single_one, Matrix.col] using congrFun (hcol (Pi.single 1 1)) i

private theorem spPlane_planeEmb_zero {r : ℕ} {K : Type} [Field K]
    (e f : Fin r ⊕ Fin r → K) : RootPair.planeEmb e f (0 : Fin 2 → K) = 0 := by
  simp [RootPair.planeEmb]

private theorem spPlane_planeEmb_eq_zero {r : ℕ} {K : Type} [Field K]
    {e f : Fin r ⊕ Fin r → K} (hef : spForm r K e f = 1) {a : Fin 2 → K}
    (h : RootPair.planeEmb e f a = 0) : a = 0 := by
  have h1 := congrArg (RootPair.planeProj e f) h
  rw [RootPair.planeProj_emb hef] at h1
  ext i
  have h2 := congrFun h1 i
  fin_cases i <;> simpa [RootPair.planeProj] using h2

private theorem spPlane_eq_zero_of_forall_spForm_eq_zero {u : Fin k ⊕ Fin k → F}
    (h : ∀ b, spForm k F b u = 0) : u = 0 :=
  CFSG.RankThree.Classical.spForm_nondegenerate.1 u (fun b => by
    rw [RootPair.spForm_antisymm, h b, neg_zero])

private theorem spPlane_exists_spForm_ne_zero {b : Fin k ⊕ Fin k → F} (hb : b ≠ 0) :
    ∃ y : Fin k ⊕ Fin k → F, spForm k F y b ≠ 0 := by
  by_contra h
  push Not at h
  exact hb (spPlane_eq_zero_of_forall_spForm_eq_zero h)

private theorem spPlane_exists_smul_of_forall_spForm_eq_zero {z u : Fin k ⊕ Fin k → F}
    (hz : z ≠ 0) (h : ∀ b, spForm k F b z = 0 → spForm k F b u = 0) :
    ∃ mu : F, u = mu • z := by
  obtain ⟨b₀, hb₀⟩ := spPlane_exists_spForm_ne_zero hz
  refine ⟨spForm k F b₀ u / spForm k F b₀ z, ?_⟩
  have hzero : u - (spForm k F b₀ u / spForm k F b₀ z) • z = 0 := by
    apply spPlane_eq_zero_of_forall_spForm_eq_zero
    intro b
    have hbz : spForm k F b z - (spForm k F b z / spForm k F b₀ z) * spForm k F b₀ z = 0 := by
      rw [div_mul_cancel₀ _ hb₀, sub_self]
    have hbz' : spForm k F (b - (spForm k F b z / spForm k F b₀ z) • b₀) z = 0 := by
      rw [map_sub, map_smul]
      change spForm k F b z - (spForm k F b z / spForm k F b₀ z) * spForm k F b₀ z = 0
      exact hbz
    have hu := h _ hbz'
    rw [map_sub, map_smul] at hu
    change spForm k F b u - (spForm k F b z / spForm k F b₀ z) * spForm k F b₀ u = 0 at hu
    rw [map_sub, map_smul]
    change spForm k F b u - (spForm k F b₀ u / spForm k F b₀ z) * spForm k F b z = 0
    rw [sub_eq_zero] at hu ⊢
    rw [hu]
    field_simp
  exact sub_eq_zero.mp hzero

private theorem spPlane_planeEmb_single_zero {r : ℕ} {K : Type} [Field K]
    (e f : Fin r ⊕ Fin r → K) :
    RootPair.planeEmb e f (Pi.single (0 : Fin 2) 1) = e := by
  simp [RootPair.planeEmb]

private theorem spPlane_planeEmb_single_one {r : ℕ} {K : Type} [Field K]
    (e f : Fin r ⊕ Fin r → K) :
    RootPair.planeEmb e f (Pi.single (1 : Fin 2) 1) = f := by
  simp [RootPair.planeEmb]

private theorem spPlane_exists_sl2_spEnd_eq (hk : 0 < k) {v w : Fin k ⊕ Fin k → F}
    (hv : ∃ a, v = RootPair.planeEmb
      (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1) a)
    (hw : ∃ a, w = RootPair.planeEmb
      (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1) a)
    (hv0 : v ≠ 0) (hw0 : w ≠ 0) :
    ∃ s : SpecialLinearGroup (Fin 2) F, spEnd (spPlaneSL2Hom hk s) v = w := by
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨a', rfl⟩ := hw
  have ha : a ≠ 0 := fun h => hv0 (by rw [h, spPlane_planeEmb_zero])
  have ha' : a' ≠ 0 := fun h => hw0 (by rw [h, spPlane_planeEmb_zero])
  obtain ⟨s, hs⟩ := CFSG.GroupTheory.SteinbergBK.exists_sl2_mulVec_eq a a' ha ha'
  refine ⟨s, ?_⟩
  change spEnd (RootPair.spSL2Hom (spForm_single_inl_zero_inr_zero (F := F) hk) s)
    (RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a) =
    RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1) a'
  rw [spPlane_spSL2Hom_planeEmb (spForm_single_inl_zero_inr_zero (F := F) hk) s a, hs]

private theorem spPlane_spTransvection_mem_of_planeEmb (hk : 0 < k) {a : Fin 2 → F} {c : F}
    (ha : a ≠ 0) :
    spTransvection (RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a) c ∈ planeSL2 hk := by
  have he : ∃ a₀ : Fin 2 → F, (Pi.single (Sum.inl ⟨0, hk⟩) 1 : Fin k ⊕ Fin k → F) =
      RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1) a₀ :=
    ⟨Pi.single (0 : Fin 2) 1, (spPlane_planeEmb_single_zero _ _).symm⟩
  have hene : (Pi.single (Sum.inl ⟨0, hk⟩) 1 : Fin k ⊕ Fin k → F) ≠ 0 :=
    Pi.single_ne_zero_iff.2 one_ne_zero
  have hane : RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a ≠ 0 := fun h =>
    ha (spPlane_planeEmb_eq_zero (spForm_single_inl_zero_inr_zero (F := F) hk) h)
  obtain ⟨s, hs⟩ := spPlane_exists_sl2_spEnd_eq hk he ⟨a, rfl⟩ hene hane
  have hconj : spTransvection (RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a) c =
      spPlaneSL2Hom hk s * spTransvection (Pi.single (Sum.inl ⟨0, hk⟩) 1) c *
        (spPlaneSL2Hom hk s)⁻¹ := by
    rw [spTransvection_conj, hs]
  rw [hconj]
  have hu : spTransvection (Pi.single (Sum.inl ⟨0, hk⟩) 1) c = spPlaneSL2Hom hk (u2 (-c)) := by
    change spTransvection (Pi.single (Sum.inl ⟨0, hk⟩) 1) c =
      RootPair.spSL2Hom (spForm_single_inl_zero_inr_zero (F := F) hk) (u2 (-c))
    rw [RootPair.spSL2Hom_u2]
    simp
  rw [hu]
  have heq : spPlaneSL2Hom hk s * spPlaneSL2Hom hk (u2 (-c)) * (spPlaneSL2Hom hk s)⁻¹ =
      spPlaneSL2Hom hk (s * u2 (-c) * s⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [heq]
  exact MonoidHom.mem_range.mpr ⟨_, rfl⟩

private theorem spPlane_mem_plane_of_spTransvection_mem (hk : 0 < k) {b : Fin k ⊕ Fin k → F}
    {c : F} (hb : b ≠ 0) (hc : c ≠ 0) (h : spTransvection b c ∈ planeSL2 hk) :
    ∃ a : Fin 2 → F, b = RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a := by
  obtain ⟨y, hy⟩ := spPlane_exists_spForm_ne_zero hb
  change spTransvection b c ∈ (spPlaneSL2Hom hk).range at h
  rw [MonoidHom.mem_range] at h
  obtain ⟨g, hg⟩ := h
  have h1 : spEnd (spTransvection b c) y - y = (c * spForm k F y b) • b := by
    rw [spEnd_spTransvection]
    abel
  have h2 : spEnd (spPlaneSL2Hom hk g) y - y =
      RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1)
        (((g : Matrix (Fin 2) (Fin 2) F) - 1) *ᵥ
          RootPair.planeProj (Pi.single (Sum.inl ⟨0, hk⟩) 1)
            (Pi.single (Sum.inr ⟨0, hk⟩) 1) y) := by
    rw [spPlaneSL2Hom, RootPair.spEnd_spSL2Hom, RootPair.planeExt]
    abel
  have h3 : (c * spForm k F y b) • b =
      RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1)
        (((g : Matrix (Fin 2) (Fin 2) F) - 1) *ᵥ
          RootPair.planeProj (Pi.single (Sum.inl ⟨0, hk⟩) 1)
            (Pi.single (Sum.inr ⟨0, hk⟩) 1) y) := by
    rw [← h1, ← h2, hg]
  have hne : c * spForm k F y b ≠ 0 := mul_ne_zero hc hy
  refine ⟨(c * spForm k F y b)⁻¹ • (((g : Matrix (Fin 2) (Fin 2) F) - 1) *ᵥ
    RootPair.planeProj (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) y), ?_⟩
  rw [RootPair.planeEmb_smul, ← h3, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem exists_conj_eq_of_mem_planeSL2 (hk : 0 < k) {c : F} (hc : c ≠ 0) :
    ∀ x ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}, x ∈ planeSL2 hk →
      ∀ y ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}, y ∈ planeSL2 hk →
        ∃ g ∈ planeSL2 hk, g * x * g⁻¹ = y := by
  intro x hxS hxP y hyS hyP
  obtain ⟨b, hb, rfl⟩ := hxS
  obtain ⟨b', hb', rfl⟩ := hyS
  obtain ⟨a, ha⟩ := spPlane_mem_plane_of_spTransvection_mem hk hb hc hxP
  obtain ⟨a', ha'⟩ := spPlane_mem_plane_of_spTransvection_mem hk hb' hc hyP
  obtain ⟨s, hs⟩ := spPlane_exists_sl2_spEnd_eq hk ⟨a, ha⟩ ⟨a', ha'⟩ hb hb'
  refine ⟨spPlaneSL2Hom hk s, MonoidHom.mem_range.mpr ⟨s, rfl⟩, ?_⟩
  rw [ha] at hs
  rw [ha, spTransvection_conj, hs]

private theorem spPlaneSL2Hom_u2 (hk : 0 < k) (x : F) :
    spPlaneSL2Hom hk (u2 x) = spTransvection (Pi.single (Sum.inl ⟨0, hk⟩) 1) (-x) :=
  RootPair.spSL2Hom_u2 (spForm_single_inl_zero_inr_zero (F := F) hk) x

private theorem spPlaneSL2Hom_l2 (hk : 0 < k) (x : F) :
    spPlaneSL2Hom hk (l2 x) = spTransvection (Pi.single (Sum.inr ⟨0, hk⟩) 1) x :=
  RootPair.spSL2Hom_l2 (spForm_single_inl_zero_inr_zero (F := F) hk) x

private theorem spPlaneSL2Hom_injective (hk : 0 < k) :
    Function.Injective (spPlaneSL2Hom (F := F) hk) :=
  spPlane_spSL2Hom_injective (spForm_single_inl_zero_inr_zero (F := F) hk)

private theorem spPlaneSL2Hom_planeEmb (hk : 0 < k) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (a : Fin 2 → F) :
    spEnd (spPlaneSL2Hom hk g) (RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a) =
      RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1)
        ((g : Matrix (Fin 2) (Fin 2) F) *ᵥ a) :=
  spPlane_spSL2Hom_planeEmb (spForm_single_inl_zero_inr_zero (F := F) hk) g a

private theorem spPlane_exists_smul_of_perpMem_eq (hk : 0 < k) {c : F} (hc : c ≠ 0)
    {z u : Fin k ⊕ Fin k → F} (hz : z ≠ 0)
    (hperp : perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection u c) =
      perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c)) :
    ∃ mu : F, u = mu • z := by
  apply spPlane_exists_smul_of_forall_spForm_eq_zero hz
  intro b
  by_cases hb : b = 0
  · simp [hb]
  · have hmS : spTransvection b c ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} := ⟨b, hb, rfl⟩
    have hiff : Commute (spTransvection b c) (spTransvection u c) ↔
        Commute (spTransvection b c) (spTransvection z c) := by
      have h1 : spTransvection b c ∈
          perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection u c) ↔
          spTransvection b c ∈
            perpMem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c) := by
        rw [hperp]
      constructor
      · intro h
        exact (mem_perpMem.mp (h1.mp (mem_perpMem.mpr ⟨hmS, h⟩))).2
      · intro h
        exact (mem_perpMem.mp (h1.mpr (mem_perpMem.mpr ⟨hmS, h⟩))).2
    rw [commute_spTransvection_iff hc hc, commute_spTransvection_iff hc hc] at hiff
    intro hbz
    exact hiff.mpr hbz

private theorem spPlane_Vmem_eq (hk : 0 < k) {c : F} (hc : c ≠ 0)
    {z : Fin k ⊕ Fin k → F} (hz : z ≠ 0) :
    Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c) =
      {x | ∃ mu : F, mu ≠ 0 ∧ x = spTransvection (mu • z) c} := by
  ext x
  constructor
  · intro hx
    rw [mem_Vmem] at hx
    obtain ⟨hxS, hperp⟩ := hx
    obtain ⟨u, hu, rfl⟩ := hxS
    obtain ⟨mu, hmu⟩ := spPlane_exists_smul_of_perpMem_eq hk hc hz hperp
    have hmu0 : mu ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hmu
      exact hu hmu
    exact ⟨mu, hmu0, by rw [hmu]⟩
  · rintro ⟨mu, hmu0, rfl⟩
    refine mem_Vmem.mpr ⟨⟨mu • z, smul_ne_zero hmu0 hz, rfl⟩, ?_⟩
    ext e
    rw [mem_perpMem, mem_perpMem]
    constructor
    · rintro ⟨heS, he⟩
      exact ⟨heS, (commute_spTransvection_smul_iff e z hmu0 hc).mp he⟩
    · rintro ⟨heS, he⟩
      exact ⟨heS, (commute_spTransvection_smul_iff e z hmu0 hc).mpr he⟩

private theorem spPlane_exists_sl2_pair {a a' : Fin 2 → F}
    (h : a 0 * a' 1 - a 1 * a' 0 ≠ 0) :
    ∃ (s : Matrix.SpecialLinearGroup (Fin 2) F) (mu : F), mu ≠ 0 ∧
      (s : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single 0 1 = a ∧
      (s : Matrix (Fin 2) (Fin 2) F) *ᵥ Pi.single 1 1 = mu • a' := by
  set D : F := a 0 * a' 1 - a 1 * a' 0 with hD
  set mu : F := D⁻¹ with hmu
  have hmu0 : mu ≠ 0 := inv_ne_zero h
  have hdet : (!![a 0, mu * a' 0; a 1, mu * a' 1] : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    have h1 : (!![a 0, mu * a' 0; a 1, mu * a' 1] : Matrix (Fin 2) (Fin 2) F).det =
        a 0 * (mu * a' 1) - mu * a' 0 * a 1 := by
      rw [Matrix.det_fin_two]
      simp
    rw [h1]
    have hD' : a 0 * (mu * a' 1) - mu * a' 0 * a 1 = mu * D := by
      rw [hD]; ring
    rw [hD', hmu, inv_mul_cancel₀ h]
  refine ⟨⟨!![a 0, mu * a' 0; a 1, mu * a' 1], hdet⟩, mu, hmu0, ?_, ?_⟩
  · rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [Matrix.col]
  · rw [Matrix.mulVec_single_one]
    funext i
    fin_cases i <;> simp [Matrix.col]

private theorem spPlane_exists_sl2_map_pair (hk : 0 < k) {z z' : Fin k ⊕ Fin k → F}
    {a a' : Fin 2 → F}
    (hz : z = RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a)
    (hz' : z' = RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a')
    (hdet : a 0 * a' 1 - a 1 * a' 0 ≠ 0) :
    ∃ (s : Matrix.SpecialLinearGroup (Fin 2) F) (mu : F), mu ≠ 0 ∧
      spEnd (spPlaneSL2Hom hk s) (Pi.single (Sum.inl ⟨0, hk⟩) 1) = z ∧
      spEnd (spPlaneSL2Hom hk s) (Pi.single (Sum.inr ⟨0, hk⟩) 1) = mu • z' := by
  obtain ⟨s, mu, hmu0, hs1, hs2⟩ := spPlane_exists_sl2_pair hdet
  refine ⟨s, mu, hmu0, ?_, ?_⟩
  · rw [hz]
    conv_lhs =>
      rw [← spPlane_planeEmb_single_zero (Pi.single (Sum.inl ⟨0, hk⟩) 1)
        (Pi.single (Sum.inr ⟨0, hk⟩) 1)]
    rw [spPlaneSL2Hom_planeEmb, hs1]
  · rw [hz']
    conv_lhs =>
      rw [← spPlane_planeEmb_single_one (Pi.single (Sum.inl ⟨0, hk⟩) 1)
        (Pi.single (Sum.inr ⟨0, hk⟩) 1)]
    rw [spPlaneSL2Hom_planeEmb, hs2, RootPair.planeEmb_smul]

private theorem spPlane_closure_le_planeSL2 [Finite F] [CharP F 2] (hk : 0 < k) {c : F}
    (hc : c ≠ 0) {z w : Fin k ⊕ Fin k → F} (hz : z ≠ 0)
    (hxP : spTransvection z c ∈ planeSL2 hk) (hyP : spTransvection w c ∈ planeSL2 hk) :
    Subgroup.closure (insert (spTransvection w c)
      (Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c))) ≤ planeSL2 hk := by
  obtain ⟨a, ha⟩ := spPlane_mem_plane_of_spTransvection_mem hk hz hc hxP
  have ha0 : a ≠ 0 := fun h => hz (by rw [ha, h, spPlane_planeEmb_zero])
  have hVmem : Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c) =
      {x | ∃ mu : F, mu ≠ 0 ∧ x = spTransvection (mu • z) c} :=
    spPlane_Vmem_eq hk hc hz
  refine (Subgroup.closure_le (planeSL2 hk)).mpr ?_
  intro e he
  rcases he with rfl | heV
  · exact hyP
  · rw [hVmem] at heV
    obtain ⟨mu, hmu0, heq⟩ := heV
    rw [heq, ha, ← RootPair.planeEmb_smul]
    exact spPlane_spTransvection_mem_of_planeEmb hk (smul_ne_zero hmu0 ha0)

private theorem spPlane_rootGroup_le_closure [Finite F] [CharP F 2] (hk : 0 < k) {c : F}
    (hc : c ≠ 0) {z w : Fin k ⊕ Fin k → F} (hz : z ≠ 0) :
    ∀ d : F, spTransvection z d ∈ Subgroup.closure (insert (spTransvection w c)
      (Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c))) := by
  intro d
  have hVmem : Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c) =
      {x | ∃ mu : F, mu ≠ 0 ∧ x = spTransvection (mu • z) c} :=
    spPlane_Vmem_eq hk hc hz
  have hVmem_le : Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c) ⊆
      Subgroup.closure (insert (spTransvection w c)
        (Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c))) :=
    fun e he => Subgroup.subset_closure (by simp [he])
  by_cases hd : d = 0
  · rw [hd, borel86_spn_spTransvection_param_zero]
    exact Subgroup.one_mem _
  · obtain ⟨mu, hmu⟩ := (isSquare_iff_exists_sq (d / c)).mp (isSquare_of_charTwo' (d / c))
    have hdc : d / c ≠ 0 := div_ne_zero hd hc
    have hmu0 : mu ≠ 0 := by
      rintro rfl
      rw [pow_two, zero_mul] at hmu
      exact hdc hmu
    have hdmu : d = mu * mu * c := by
      conv_lhs => rw [← div_mul_cancel₀ d hc]
      rw [hmu, pow_two]
    refine hVmem_le ?_
    rw [hVmem]
    exact ⟨mu, hmu0, by rw [hdmu, ← spTransvection_smul]⟩

private theorem spPlane_rootGroup_image_le_closure (hk : 0 < k) {c : F}
    {z w : Fin k ⊕ Fin k → F} {C : Subgroup ↥(StatedSp k F)} (hyC : spTransvection w c ∈ C)
    (hXz : ∀ d : F, spTransvection z d ∈ C) :
    ∀ d : F, spTransvection (spEnd (spTransvection w c) z) d ∈ C := by
  intro d
  rw [← spTransvection_conj (spTransvection w c) z d]
  exact C.mul_mem (C.mul_mem hyC (hXz d)) (C.inv_mem hyC)

private theorem spPlane_closure_range_u2_l2 :
    Subgroup.closure (Set.range (u2 : F → Matrix.SpecialLinearGroup (Fin 2) F) ∪
      Set.range (l2 : F → Matrix.SpecialLinearGroup (Fin 2) F)) = ⊤ := by
  have hu : (u2 : F → Matrix.SpecialLinearGroup (Fin 2) F) =
      CFSG.LieType.Steinberg.sl2Upper := by
    funext d
    apply Subtype.ext
    rw [u2_coe]
    rfl
  have hl : (l2 : F → Matrix.SpecialLinearGroup (Fin 2) F) =
      CFSG.LieType.Steinberg.sl2Lower := by
    funext d
    apply Subtype.ext
    rw [l2_coe]
    rfl
  rw [hu, hl]
  exact CFSG.StandardType.RankOneXfer.closure_sl2Upper_sl2Lower_eq_top

private theorem spPlane_planeSL2_le_closure_of_map (hk : 0 < k) {c : F}
    {z z' : Fin k ⊕ Fin k → F} {s : Matrix.SpecialLinearGroup (Fin 2) F} {mu : F}
    (hse : spEnd (spPlaneSL2Hom hk s) (Pi.single (Sum.inl ⟨0, hk⟩) 1) = z)
    (hsf : spEnd (spPlaneSL2Hom hk s) (Pi.single (Sum.inr ⟨0, hk⟩) 1) = mu • z')
    {C : Subgroup ↥(StatedSp k F)}
    (hzC : ∀ d : F, spTransvection z d ∈ C) (hz'C : ∀ d : F, spTransvection z' d ∈ C) :
    planeSL2 hk ≤ C := by
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
    C.comap ((spPlaneSL2Hom hk).comp (MulAut.conj s).toMonoidHom)
  have hu2mem : ∀ d : F, u2 d ∈ H := by
    intro d
    rw [Subgroup.mem_comap]
    change spPlaneSL2Hom hk (s * u2 d * s⁻¹) ∈ C
    rw [map_mul, map_mul, map_inv, spPlaneSL2Hom_u2, spTransvection_conj, hse]
    exact hzC (-d)
  have hl2mem : ∀ d : F, l2 d ∈ H := by
    intro d
    rw [Subgroup.mem_comap]
    change spPlaneSL2Hom hk (s * l2 d * s⁻¹) ∈ C
    rw [map_mul, map_mul, map_inv, spPlaneSL2Hom_l2, spTransvection_conj, hsf,
      spTransvection_smul]
    exact hz'C (mu * mu * d)
  have hHle : Subgroup.closure (Set.range (u2 : F → Matrix.SpecialLinearGroup (Fin 2) F) ∪
      Set.range (l2 : F → Matrix.SpecialLinearGroup (Fin 2) F)) ≤ H := by
    refine (Subgroup.closure_le H).mpr ?_
    rintro g (hg | hg)
    · obtain ⟨d, rfl⟩ := hg
      exact hu2mem d
    · obtain ⟨d, rfl⟩ := hg
      exact hl2mem d
  have htop : H = ⊤ := by
    rw [spPlane_closure_range_u2_l2] at hHle
    exact le_antisymm le_top hHle
  intro kk hkk
  change kk ∈ (spPlaneSL2Hom hk).range at hkk
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hkk
  have hmemH : s⁻¹ * h * s ∈ H := by
    rw [htop]; exact Subgroup.mem_top _
  rw [Subgroup.mem_comap] at hmemH
  change spPlaneSL2Hom hk (s * (s⁻¹ * h * s) * s⁻¹) ∈ C at hmemH
  have heq : spPlaneSL2Hom hk (s * (s⁻¹ * h * s) * s⁻¹) = spPlaneSL2Hom hk h := by
    congr 1
    group
  rwa [heq] at hmemH

private theorem spPlane_planeSL2_le_closure [Finite F] [CharP F 2] (hk : 0 < k) {c : F}
    (hc : c ≠ 0) {z w : Fin k ⊕ Fin k → F} (hz : z ≠ 0) (hw : w ≠ 0)
    (hzw : spForm k F z w ≠ 0)
    (hxP : spTransvection z c ∈ planeSL2 hk) (hyP : spTransvection w c ∈ planeSL2 hk) :
    planeSL2 hk ≤ Subgroup.closure (insert (spTransvection w c)
      (Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} (spTransvection z c))) := by
  obtain ⟨a, ha⟩ := spPlane_mem_plane_of_spTransvection_mem hk hz hc hxP
  obtain ⟨a₂, ha₂⟩ := spPlane_mem_plane_of_spTransvection_mem hk hw hc hyP
  let z' : Fin k ⊕ Fin k → F := spEnd (spTransvection w c) z
  have hz'eq : z' = z + (c * spForm k F z w) • w := by
    change spEnd (spTransvection w c) z = z + (c * spForm k F z w) • w
    rw [spEnd_spTransvection]
  let a' : Fin 2 → F := a + (c * spForm k F z w) • a₂
  have hz'a' : z' = RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
      (Pi.single (Sum.inr ⟨0, hk⟩) 1) a' := by
    rw [hz'eq]
    change z + (c * spForm k F z w) • w = RootPair.planeEmb
      (Pi.single (Sum.inl ⟨0, hk⟩) 1) (Pi.single (Sum.inr ⟨0, hk⟩) 1)
      (a + (c * spForm k F z w) • a₂)
    rw [ha, ha₂, RootPair.planeEmb_add, RootPair.planeEmb_smul]
  have hzz' : spForm k F z z' ≠ 0 := by
    rw [hz'eq, map_add, map_smul, spForm_isAlt.self_eq_zero, zero_add, smul_eq_mul]
    exact mul_ne_zero (mul_ne_zero hc hzw) hzw
  have hdet : a 0 * a' 1 - a 1 * a' 0 ≠ 0 := by
    have h := RootPair.spForm_planeEmb_planeEmb
      (spForm_single_inl_zero_inr_zero (F := F) hk) a a'
    have h2 : spForm k F (RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
        (Pi.single (Sum.inr ⟨0, hk⟩) 1) a)
        (RootPair.planeEmb (Pi.single (Sum.inl ⟨0, hk⟩) 1)
          (Pi.single (Sum.inr ⟨0, hk⟩) 1) a') ≠ 0 := by
      rwa [← ha, ← hz'a']
    rwa [h] at h2
  obtain ⟨s, mu, hmu0, hse, hsf⟩ := spPlane_exists_sl2_map_pair hk ha hz'a' hdet
  refine spPlane_planeSL2_le_closure_of_map (c := c) hk hse hsf
    (spPlane_rootGroup_le_closure hk hc hz) ?_
  exact spPlane_rootGroup_image_le_closure hk (c := c) (z := z) (w := w)
    (Subgroup.subset_closure (by simp)) (spPlane_rootGroup_le_closure hk hc hz)

theorem closure_insert_Vmem_eq_planeSL2 [Finite F] [CharP F 2] (hk : 0 < k) {c : F}
    (hc : c ≠ 0) :
    ∀ x ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}, x ∈ planeSL2 hk →
      ∀ y ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}, y ∈ planeSL2 hk → ¬ Commute x y →
        Subgroup.closure (insert y (Vmem {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} x)) =
          planeSL2 hk := by
  set S : Set ↥(StatedSp k F) := {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} with hS
  intro x hxS hxP y hyS hyP hnc
  obtain ⟨z, hz, rfl⟩ := hxS
  obtain ⟨w, hw, rfl⟩ := hyS
  have hzw : spForm k F z w ≠ 0 := fun h0 => hnc ((commute_spTransvection_iff hc hc).mpr h0)
  exact le_antisymm (spPlane_closure_le_planeSL2 hk hc hz hxP hyP)
    (spPlane_planeSL2_le_closure hk hc hz hw hzw hxP hyP)

private theorem spPlane_spEnd_ne_zero {g : ↥(StatedSp k F)} {v : Fin k ⊕ Fin k → F}
    (hv : v ≠ 0) : spEnd g v ≠ 0 := by
  intro h
  apply hv
  calc v = spEnd g⁻¹ (spEnd g v) := (spEnd_spEnd_inv g⁻¹ v).symm
    _ = 0 := by rw [h, map_zero]

private theorem spPlane_involution_eq_spTransvection [Finite F] [CharP F 2] (hk : 0 < k)
    {c : F} (hc : c ≠ 0) {g : Matrix.SpecialLinearGroup (Fin 2) F} {d : F} (hd : d ≠ 0) :
    ∃ p : Fin k ⊕ Fin k → F, p ≠ 0 ∧
      spPlaneSL2Hom hk (g * u2 d * g⁻¹) = spTransvection p c := by
  obtain ⟨mu, hmu⟩ := (isSquare_iff_exists_sq (d / c)).mp (isSquare_of_charTwo' (d / c))
  have hdc : d / c ≠ 0 := div_ne_zero hd hc
  have hmu0 : mu ≠ 0 := by
    rintro rfl
    rw [pow_two, zero_mul] at hmu
    exact hdc hmu
  have hdmu : d = mu * mu * c := by
    conv_lhs => rw [← div_mul_cancel₀ d hc]
    rw [hmu, pow_two]
  set v : Fin k ⊕ Fin k → F := spEnd (spPlaneSL2Hom hk g) (Pi.single (Sum.inl ⟨0, hk⟩) 1) with hv
  have hv0 : v ≠ 0 := spPlane_spEnd_ne_zero (by simp)
  refine ⟨mu • v, smul_ne_zero hmu0 hv0, ?_⟩
  have h1 : spPlaneSL2Hom hk (g * u2 d * g⁻¹) = spTransvection v (-d) := by
    rw [map_mul, map_mul, map_inv, spPlaneSL2Hom_u2, spTransvection_conj, ← hv]
  rw [h1, CharTwo.neg_eq d, hdmu, ← spTransvection_smul]

private theorem spPlane_exists_two_involutions [Finite F] [CharP F 2] :
    ∃ a b : Matrix.SpecialLinearGroup (Fin 2) F,
      a * a = 1 ∧ b * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧
        orderOf (a * b) = Nat.card F + 1 := by
  obtain ⟨A, hA⟩ := CFSG.SeitzReduction.F4Pilot.exists_orderOf_eq_natCard_add_one (K := F)
  obtain ⟨a, haa, haA⟩ := CFSG.CGT.Timmesfeld75.exists_mul_self_eq_one_conj_eq_inv A
  let b : Matrix.SpecialLinearGroup (Fin 2) F := a * A
  have hbb : b * b = 1 := by
    show (a * A) * (a * A) = 1
    rw [← mul_assoc (a * A) a A, haA, inv_mul_cancel]
  have hAab : A = a * b := by
    show A = a * (a * A)
    rw [← mul_assoc, haa, one_mul]
  have h3 : 3 ≤ orderOf A := by
    rw [hA]
    have := Finite.one_lt_card (α := F)
    omega
  have hAne : A * A ≠ 1 := by
    intro h2
    have hdvd : orderOf A ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hle : orderOf A ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have ha1 : a ≠ 1 := by
    intro h
    apply hAne
    rw [show b = a * A from rfl, h, one_mul] at hbb
    exact hbb
  have hb1 : b ≠ 1 := by
    intro h
    apply hAne
    rw [hAab, h, mul_one]
    exact haa
  exact ⟨a, b, haa, hbb, ha1, hb1, by rw [← hAab, hA]⟩

private theorem spPlane_uE_eq_u2 (d : F) :
    CFSG.OddStandard.Seitz77.Nat16.uE d = u2 d := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CFSG.OddStandard.Seitz77.Nat16.uE, u2_coe]

theorem exists_orderOf_mul_eq_card_add_one_planeSL2 [Finite F] [CharP F 2] (hk : 0 < k)
    {c : F} (hc : c ≠ 0) :
    ∃ x ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}, x ∈ planeSL2 hk ∧
      ∃ y ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c}, y ∈ planeSL2 hk ∧
        orderOf (x * y) = Nat.card F + 1 := by
  obtain ⟨a, b, haa, hbb, ha1, hb1, hab⟩ := spPlane_exists_two_involutions (F := F)
  obtain ⟨g, d, hd, haeq⟩ :=
    CFSG.OddStandard.Seitz77.Nat16.exists_conj_uE_of_involution a ha1 haa
  obtain ⟨g', d', hd', hbeq⟩ :=
    CFSG.OddStandard.Seitz77.Nat16.exists_conj_uE_of_involution b hb1 hbb
  have haeq2 : a = g * u2 d * g⁻¹ := by rw [haeq, spPlane_uE_eq_u2]
  have hbeq2 : b = g' * u2 d' * g'⁻¹ := by rw [hbeq, spPlane_uE_eq_u2]
  obtain ⟨p, hp0, hpT⟩ := spPlane_involution_eq_spTransvection hk hc hd
  obtain ⟨p', hp'0, hp'T⟩ := spPlane_involution_eq_spTransvection hk hc hd'
  refine ⟨spPlaneSL2Hom hk a, ⟨p, hp0, ?_⟩, MonoidHom.mem_range.mpr ⟨a, rfl⟩,
    spPlaneSL2Hom hk b, ⟨p', hp'0, ?_⟩, MonoidHom.mem_range.mpr ⟨b, rfl⟩, ?_⟩
  · rw [haeq2]
    exact hpT
  · rw [hbeq2]
    exact hp'T
  · have h1 : orderOf (spPlaneSL2Hom hk a * spPlaneSL2Hom hk b) = orderOf (a * b) := by
      rw [← map_mul]
      exact orderOf_injective (f := spPlaneSL2Hom (F := F) hk) (spPlaneSL2Hom_injective hk) (a * b)
    rw [h1, hab]

theorem pos_of_isSymplecticTransvection {X : Type} [Group X] {s : X} {m f : ℕ}
    (hs : IsSymplecticTransvection X m f s) : 0 < f := by
  obtain ⟨k, -, F, hF, hFfin, hFcard, e, he⟩ := hs
  letI : Finite F := hFfin
  letI : Field F := hF
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  rw [hFcard] at h2
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, pow_zero] at h2
    omega
  exact Nat.pos_of_ne_zero hf0

theorem Vmem_image_mulEquiv {X Y : Type} [Group X] [Group Y]
    (φ : X ≃* Y) (S : Set X) (u : X) :
    Vmem (φ '' S) (φ u) = φ '' Vmem S u := by
  ext y
  constructor
  · rintro ⟨⟨x, hxS, rfl⟩, hperp⟩
    refine ⟨x, ⟨hxS, ?_⟩, rfl⟩
    have h2 : φ '' perpMem S x = φ '' perpMem S u := by
      rw [← perpMem_image_mulEquiv φ S x, ← perpMem_image_mulEquiv φ S u]
      exact hperp
    exact Set.image_injective.mpr φ.injective h2
  · rintro ⟨x, ⟨hxS, hperp⟩, rfl⟩
    refine ⟨⟨x, hxS, rfl⟩, ?_⟩
    rw [perpMem_image_mulEquiv, perpMem_image_mulEquiv, hperp]

private theorem spPlane_transport_closure [Finite F] [CharP F 2] {X : Type} [Group X]
    {c : F} (hk : 0 < k) (hc : c ≠ 0) (φ : X ≃* ↥(StatedSp k F))
    {S : Set X} (hclass : φ '' S = {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c})
    {K0 : Subgroup X} (hK0 : K0 = (planeSL2 hk).map φ.symm.toMonoidHom) :
    ∀ x ∈ S, x ∈ K0 → ∀ y ∈ S, y ∈ K0 → ¬ Commute x y →
      Subgroup.closure (insert y (Vmem S x)) = K0 := by
  intro x hxS hxK y hyS hyK hnc
  rw [hK0] at hxK hyK
  have hx' : φ x ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} := by
    rw [← hclass]; exact Set.mem_image_of_mem φ hxS
  have hy' : φ y ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} := by
    rw [← hclass]; exact Set.mem_image_of_mem φ hyS
  have hxpl : φ x ∈ planeSL2 hk := by
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxK
    rw [← hzx]
    simpa using hz
  have hypl : φ y ∈ planeSL2 hk := by
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyK
    rw [← hzy]
    simpa using hz
  have hnc' : ¬ Commute (φ x) (φ y) := by
    intro h
    exact hnc (by simpa using h.map φ.symm.toMonoidHom)
  have hpl := closure_insert_Vmem_eq_planeSL2 hk hc (φ x) hx' hxpl (φ y) hy' hypl hnc'
  have h1 : Subgroup.map φ.toMonoidHom (Subgroup.closure (insert y (Vmem S x))) = planeSL2 hk := by
    change Subgroup.map (φ : X →* ↥(StatedSp k F))
      (Subgroup.closure (insert y (Vmem S x))) = planeSL2 hk
    rw [CFSG.Fischer.map_closure_image φ, Set.image_insert_eq,
      ← Vmem_image_mulEquiv φ S x, hclass, hpl]
  have h2 : Subgroup.map φ.toMonoidHom K0 = planeSL2 hk := by
    rw [hK0, Subgroup.map_map]
    have hid : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id _ := by
      ext z; simp
    rw [hid, Subgroup.map_id]
  exact Subgroup.map_injective (f := φ.toMonoidHom) φ.injective (h1.trans h2.symm)

private theorem spPlane_transport_conj {X : Type} [Group X] {c : F} (hk : 0 < k)
    (hc : c ≠ 0) (φ : X ≃* ↥(StatedSp k F))
    {S : Set X} (hclass : φ '' S = {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c})
    {K0 : Subgroup X} (hK0 : K0 = (planeSL2 hk).map φ.symm.toMonoidHom) :
    ∀ x ∈ S, x ∈ K0 → ∀ y ∈ S, y ∈ K0 → ∃ g ∈ K0, g * x * g⁻¹ = y := by
  intro x hxS hxK y hyS hyK
  rw [hK0] at hxK hyK ⊢
  have hx' : φ x ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} := by
    rw [← hclass]; exact Set.mem_image_of_mem φ hxS
  have hy' : φ y ∈ {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} := by
    rw [← hclass]; exact Set.mem_image_of_mem φ hyS
  have hxpl : φ x ∈ planeSL2 hk := by
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxK
    rw [← hzx]
    simpa using hz
  have hypl : φ y ∈ planeSL2 hk := by
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hyK
    rw [← hzy]
    simpa using hz
  obtain ⟨g', hg'pl, hg'⟩ :=
    exists_conj_eq_of_mem_planeSL2 hk hc (φ x) hx' hxpl (φ y) hy' hypl
  refine ⟨φ.symm g', Subgroup.mem_map.mpr ⟨g', hg'pl, rfl⟩, ?_⟩
  apply φ.injective
  rw [map_mul, map_mul, map_inv, φ.apply_symm_apply]
  exact hg'

private theorem spPlane_transport_order [Finite F] [CharP F 2] {X : Type} [Group X]
    {c : F} (hk : 0 < k) (hc : c ≠ 0) (φ : X ≃* ↥(StatedSp k F))
    {S : Set X} (hclass' : φ.symm '' {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} = S)
    {K0 : Subgroup X} (hK0 : K0 = (planeSL2 hk).map φ.symm.toMonoidHom) {f : ℕ}
    (hFcard : Nat.card F = 2 ^ f) :
    ∃ x ∈ S, x ∈ K0 ∧ ∃ y ∈ S, y ∈ K0 ∧ orderOf (x * y) = 2 ^ f + 1 := by
  obtain ⟨x', hx'S, hx'pl, y', hy'S, hy'pl, hord⟩ :=
    exists_orderOf_mul_eq_card_add_one_planeSL2 hk hc
  rw [hK0]
  refine ⟨φ.symm x', ?_, Subgroup.mem_map.mpr ⟨x', hx'pl, rfl⟩,
    φ.symm y', ?_, Subgroup.mem_map.mpr ⟨y', hy'pl, rfl⟩, ?_⟩
  · rw [← hclass']; exact Set.mem_image_of_mem φ.symm hx'S
  · rw [← hclass']; exact Set.mem_image_of_mem φ.symm hy'S
  · have h1 : orderOf (φ.symm x' * φ.symm y') = orderOf (x' * y') := by
      rw [← map_mul]
      exact orderOf_injective (f := φ.symm.toMonoidHom) φ.symm.injective (x' * y')
    rw [h1, hord, hFcard]

theorem exists_subgroup_of_isSymplecticTransvection {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {k f : ℕ} (hk : 0 < k)
    (hs : IsSymplecticTransvection X (2 * k) f s) :
    ∃ K0 : Subgroup X,
      (∀ x ∈ {x | IsConj s x}, x ∈ K0 → ∀ y ∈ {x | IsConj s x}, y ∈ K0 → ¬ Commute x y →
        Subgroup.closure (insert y (Vmem {x | IsConj s x} x)) = K0) ∧
      (∀ x ∈ {x | IsConj s x}, x ∈ K0 → ∀ y ∈ {x | IsConj s x}, y ∈ K0 →
        ∃ g ∈ K0, g * x * g⁻¹ = y) ∧
      ∃ x ∈ {x | IsConj s x}, x ∈ K0 ∧ ∃ y ∈ {x | IsConj s x}, y ∈ K0 ∧
        orderOf (x * y) = 2 ^ f + 1 := by
  obtain ⟨k', hk', F, hF, hFfin, hFcard, e, he⟩ := hs
  obtain rfl : k = k' := by omega
  letI : Finite F := hFfin
  letI : Field F := hF
  haveI : CharP F 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hFcard
  set S : Set X := {x | IsConj s x} with hS
  let ψ : X ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientBot (G := X)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have hψ : ∀ x : X, ψ x = QuotientGroup.mk x := by intro x; simp [ψ]
  let φ : X ≃* ↥(StatedSp k F) := ψ.trans e
  have hφ : φ s = e (QuotientGroup.mk s) := by simp [φ, hψ s]
  let t₀ : ↥(StatedSp k F) := e (QuotientGroup.mk s)
  have ht : IsSymplecticTransvectionIn k t₀ := by simpa [t₀] using he
  obtain ⟨a₀, c, ha₀, hc, ht₀⟩ := borel86_spn_eq_spTransvection ht
  have ht₀' : e (QuotientGroup.mk s) = spTransvection a₀ c := by simpa [t₀] using ht₀
  have hclass : φ '' S = {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} := by
    rw [hS, CFSG.Fischer.image_setOf_isConj φ s, hφ, ht₀',
      setOf_isConj_spTransvection ha₀ c]
  have hclass' : φ.symm '' {x | ∃ b, b ≠ 0 ∧ x = spTransvection b c} = S := by
    rw [← hclass, CFSG.Fischer.image_symm_image]
  let K0 : Subgroup X := (planeSL2 hk).map φ.symm.toMonoidHom
  exact ⟨K0, spPlane_transport_closure hk hc φ hclass rfl,
    spPlane_transport_conj hk hc φ hclass rfl,
    spPlane_transport_order hk hc φ hclass' rfl hFcard⟩

end CFSG.OddTranspositions.PartFour
