module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneBlocks
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightModel
import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.LocalAnalysis.StandardType.GGSpJoinCentralizerLam
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphE6
public import CFSG.LocalAnalysis.SeitzReduction.EPilotEndGraphTwistedXi
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndField
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourFix
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNeighbourLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotInnerField
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Field
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2FieldAlign
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4PointwiseInner

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG.Open (StatedSp)
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam statedSp_ext)
open scoped MatrixGroups

variable {F : Type} [Field F] {n : ℕ}

theorem spBlock_empty : spBlock F (∅ : Finset (Fin n)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  apply statedSp_ext
  ext a b
  exact (mem_spBlock.mp hx) a b fun h => (Finset.notMem_empty (planeOf a) h.1).elim

theorem spBlock_univ : spBlock F (Finset.univ : Finset (Fin n)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  exact mem_spBlock.mpr fun a b hab =>
    (hab ⟨mem_planeCoords.mpr (Finset.mem_univ _), mem_planeCoords.mpr (Finset.mem_univ _)⟩).elim

theorem lam_mem_spBlock_singleton (k : Fin n) (g : SL(2, F)) : lam k g ∈ spBlock F {k} := by
  rw [spBlock_singleton]
  exact ⟨g, statedSp_ext rfl⟩

theorem eq_one_of_commute_of_mul_self_eq_one [CharP F 2] {g h : SL(2, F)}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) (hgh : h * g = g * h) (hh : h * h = 1) :
    h = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hM : (h : Matrix (Fin 2) (Fin 2) F) * h = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hh, Matrix.SpecialLinearGroup.coe_one]
  have hC : (h : Matrix (Fin 2) (Fin 2) F) * g = g * h := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hgh, Matrix.SpecialLinearGroup.coe_mul]
  have hdet : (h : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe h
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  have e00 := congrFun (congrFun hM 0) 0
  have e11 := congrFun (congrFun hM 1) 1
  have c01 := congrFun (congrFun hC 0) 1
  have c10 := congrFun (congrFun hC 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at e00 e11 c01 c10
  have hps : ((h : Matrix (Fin 2) (Fin 2) F) 0 0 - (h : Matrix (Fin 2) (Fin 2) F) 1 1) ^ 2 = 0 := by
    linear_combination e00 + e11 - 2 * hdet -
      2 * (h : Matrix (Fin 2) (Fin 2) F) 0 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 0 * h2
  have hpeq : (h : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 1 1 :=
    sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hps)
  have hq : (h : Matrix (Fin 2) (Fin 2) F) 0 1 *
      ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + (g : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
    linear_combination c01 - (g : Matrix (Fin 2) (Fin 2) F) 0 1 * hpeq +
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 1 * h2
  have hr : (h : Matrix (Fin 2) (Fin 2) F) 1 0 *
      ((g : Matrix (Fin 2) (Fin 2) F) 0 0 + (g : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
    linear_combination c10 + (g : Matrix (Fin 2) (Fin 2) F) 1 0 * hpeq +
      (g : Matrix (Fin 2) (Fin 2) F) 1 1 * (h : Matrix (Fin 2) (Fin 2) F) 1 0 * h2
  have hq0 := (mul_eq_zero.mp hq).resolve_right htr
  have hr0 := (mul_eq_zero.mp hr).resolve_right htr
  have hp1 : (h : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have hsq : ((h : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) ^ 2 = 0 := by
      linear_combination hdet + (h : Matrix (Fin 2) (Fin 2) F) 0 0 * hpeq +
        (h : Matrix (Fin 2) (Fin 2) F) 1 0 * hq0 + ((h : Matrix (Fin 2) (Fin 2) F) 0 0 + 1) * h2
    have h0 := (pow_eq_zero_iff two_ne_zero).mp hsq
    rwa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h0
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using hp1
  · simpa using hq0
  · simpa using hr0
  · simpa [← hpeq] using hp1

theorem mem_spBlock_compl_singleton_of_commute_lam [CharP F 2] {i : Fin n} {g : SL(2, F)}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {u : StatedSp n F}
    (hu : u * lam i g = lam i g * u) (hu2 : u * u = 1) :
    u ∈ spBlock F ({i}ᶜ : Finset (Fin n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  obtain ⟨h, s, hus, hhg⟩ := CFSG.StandardType.exists_lam_mul_spEmbed_succAbove_of_commute htr hu
  set e := spEmbed (K := F) i.succAbove (Fin.succAbove_right_injective (p := i)) s with he_def
  have he : e ∈ spBlock F ({i}ᶜ : Finset (Fin (m + 1))) := by
    have hr : Set.range i.succAbove = (({i}ᶜ : Finset (Fin (m + 1))) : Set (Fin (m + 1))) := by
      rw [Fin.range_succAbove, Finset.coe_compl, Finset.coe_singleton]
    rw [spBlock, ← range_sumMap_eq_planeCoords hr,
      ← range_spEmbed (K := F) (Fin.succAbove_right_injective (p := i))]
    exact ⟨s, rfl⟩
  have hcomm : Commute (lam i h) e :=
    commute_of_mem_spBlock_of_disjoint disjoint_compl_right
      (lam_mem_spBlock_singleton i h) he
  have hsq : lam i (h * h) * (e * e) = 1 := by
    rw [map_mul, ← hu2, hus]
    calc lam i h * lam i h * (e * e) = lam i h * (lam i h * e) * e := by group
      _ = lam i h * (e * lam i h) * e := by rw [hcomm.eq]
      _ = lam i h * e * (lam i h * e) := by group
  have hmem : lam i (h * h) ∈
      spBlock F ({i} : Finset (Fin (m + 1))) ⊓ spBlock F ({i}ᶜ : Finset (Fin (m + 1))) := by
    refine ⟨lam_mem_spBlock_singleton i _, ?_⟩
    rw [eq_inv_of_mul_eq_one_left hsq]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ he he)
  rw [spBlock_inf_spBlock, Finset.inter_compl, spBlock_empty, Subgroup.mem_bot] at hmem
  have hlam : ∀ x : SL(2, F), lam i x = longBlock F (m + 1) i x := fun x => statedSp_ext rfl
  have hh1 : h * h = 1 := longBlock_injective i (by rw [← hlam, ← hlam, hmem, map_one])
  rw [hus, eq_one_of_commute_of_mul_self_eq_one htr hhg hh1, map_one, one_mul]
  exact he

theorem mem_spBlock_compl_of_commute_lam [CharP F 2] {g : SL(2, F)}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {J : Finset (Fin n)} {u : StatedSp n F}
    (hu : ∀ j ∈ J, u * lam j g = lam j g * u) (hu2 : u * u = 1) : u ∈ spBlock F Jᶜ := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    rw [Finset.compl_empty, spBlock_univ]
    exact Subgroup.mem_top u
  | @insert j J hj ih =>
    have h1 := ih fun j' hj' => hu j' (Finset.mem_insert_of_mem hj')
    have h2 := mem_spBlock_compl_singleton_of_commute_lam htr
      (hu j (Finset.mem_insert_self j J)) hu2
    have h3 : u ∈ spBlock F Jᶜ ⊓ spBlock F ({j}ᶜ : Finset (Fin n)) := ⟨h1, h2⟩
    rwa [spBlock_inf_spBlock, ← Finset.compl_union, Finset.union_comm, ← Finset.insert_eq] at h3

theorem spPlaneTorus_mem_spBlock {p : ℕ} (ζ : Multiplicative (ZMod p) →* SL(2, F))
    {J : Finset (Fin n)} {v : Fin n → Multiplicative (ZMod p)} (hv : ∀ m, m ∉ J → v m = 1) :
    CFSG.StandardType.SpJoin.spPlaneTorus n ζ v ∈ spBlock F J := by
  classical
  rw [← Finset.univ_prod_mulSingle v]
  refine Finset.prod_induction _
    (fun x => CFSG.StandardType.SpJoin.spPlaneTorus n ζ x ∈ spBlock F J)
    (fun a b ha hb => by rw [map_mul]; exact mul_mem ha hb) (by rw [map_one]; exact one_mem _) ?_
  intro m _
  rw [CFSG.StandardType.SpJoin.spPlaneTorus_mulSingle]
  by_cases hm : m ∈ J
  · exact spBlock_mono (Finset.singleton_subset_iff.mpr hm) (lam_mem_spBlock_singleton m _)
  · rw [hv m hm, map_one, map_one]
    exact one_mem _

theorem range_le_closure_mul_self_eq_one [CharP F 2] {H : Type*} [Group H] (φ : SL(2, F) →* H) :
    φ.range ≤ Subgroup.closure {w : H | w * w = 1} := by
  rintro _ ⟨A, rfl⟩
  have hA := CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A
  have hU : ∀ c : F, CFSG.LieType.Steinberg.sl2Upper c * CFSG.LieType.Steinberg.sl2Upper c = 1 := by
    intro c
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    show !![1, c; 0, 1] * !![1, c; 0, 1] = (1 : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [CharTwo.add_self_eq_zero]
  have hL : ∀ c : F, CFSG.LieType.Steinberg.sl2Lower c * CFSG.LieType.Steinberg.sl2Lower c = 1 := by
    intro c
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    show !![1, 0; c, 1] * !![1, 0; c, 1] = (1 : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [CharTwo.add_self_eq_zero]
  have hle : Subgroup.closure (Set.range (CFSG.LieType.Steinberg.sl2Upper (k := F)) ∪
      Set.range CFSG.LieType.Steinberg.sl2Lower) ≤
        (Subgroup.closure {w : H | w * w = 1}).comap φ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ?_)
      show φ _ * φ _ = 1
      rw [← map_mul, hU, map_one]
    · refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ?_)
      show φ _ * φ _ = 1
      rw [← map_mul, hL, map_one]
  exact hle hA

theorem closure_mul_self_eq_one_statedSp [CharP F 2] {k : ℕ} (hk : k ≤ 2) :
    Subgroup.closure {w : StatedSp k F | w * w = 1} = ⊤ := by
  interval_cases k
  · rw [eq_top_iff]
    intro x _
    have hx : x = 1 := statedSp_ext (Matrix.ext fun a _ => by rcases a with a | a <;> exact a.elim0)
    rw [hx]
    exact one_mem _
  · rw [eq_top_iff]
    intro x _
    have hcoords : ∀ a : Fin 1 ⊕ Fin 1, a ∈ coords (0 : Fin 1) := by
      rintro (a | a)
      · rw [Fin.fin_one_eq_zero a]
        exact inl_mem_coords 0
      · rw [Fin.fin_one_eq_zero a]
        exact inr_mem_coords 0
    have hx : x ∈ (longBlock F 1 0).range := by
      rw [range_longBlock]
      exact mem_suppGroup.mpr fun a b hab => (hab ⟨hcoords a, hcoords b⟩).elim
    exact range_le_closure_mul_self_eq_one _ hx
  · rw [eq_top_iff, ← shortBlock_sup_longBlock_eq_top F]
    exact sup_le (range_le_closure_mul_self_eq_one _) (range_le_closure_mul_self_eq_one _)

theorem closure_mul_self_eq_one_spBlock [CharP F 2] {I : Finset (Fin n)} (hI : I.card ≤ 2) :
    Subgroup.closure {x | x ∈ spBlock F I ∧ x * x = 1} = spBlock F I := by
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
  have hrange := spBlock_eq_range_spEmbed (F := F) I
  calc spBlock F I
      = (Subgroup.closure {w : StatedSp I.card F | w * w = 1}).map
          (spEmbed (K := F) (planeEnum I) (planeEnum_injective I)) := by
        rw [closure_mul_self_eq_one_statedSp hI, ← MonoidHom.range_eq_map, hrange]
    _ ≤ Subgroup.closure {x | x ∈ spBlock F I ∧ x * x = 1} := by
        rw [MonoidHom.map_closure]
        refine Subgroup.closure_mono ?_
        rintro _ ⟨w, hw, rfl⟩
        refine ⟨?_, ?_⟩
        · rw [hrange]
          exact ⟨w, rfl⟩
        · rw [← map_mul, show w * w = 1 from hw, map_one]

end CFSG.SeitzReduction.SymplecticPilot

namespace CFSG.StandardType

open CFSG.Open (StatedSp)
open CFSG.SeitzReduction.SymplecticPilot
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed range_spEmbed)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (lam)
open scoped MatrixGroups

variable {G : Type} [Group G] {p n : ℕ}

@[expose] def ggQTwoSmallBlock (Bs : Subgroup G) (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (S T : Set (Fin n)) : Subgroup G :=
  Subgroup.closure {x | x ∈ ggBlockComm Bs eta T ⊓
    Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G) ∧ x * x = 1}

private theorem map_conj_centralizer (H : Subgroup G) (g : G) :
    (Subgroup.centralizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := Subgroup.mem_centralizer_iff.mp hy
    refine Subgroup.mem_centralizer_iff.mpr ?_
    rintro _ ⟨h, hh, rfl⟩
    show g * h * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * h * g⁻¹)
    calc g * h * g⁻¹ * (g * y * g⁻¹) = g * (h * y) * g⁻¹ := by group
      _ = g * (y * h) * g⁻¹ := by rw [hy' h hh]
      _ = g * y * g⁻¹ * (g * h * g⁻¹) := by group
  · intro hx
    have hx' := Subgroup.mem_centralizer_iff.mp hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      have hc := hx' (g * h * g⁻¹) ⟨h, hh, rfl⟩
      calc h * (g⁻¹ * x * g) = g⁻¹ * ((g * h * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * h * g⁻¹)) * g := by rw [hc]
        _ = g⁻¹ * x * g * h := by group
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

theorem ggQTwoSmallBlock_map_conj {Bs : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {τ : Equiv.Perm (Fin n)}
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut τ) (S T : Set (Fin n)) :
    (ggQTwoSmallBlock Bs eta S T).map (MulAut.conj g).toMonoidHom =
      ggQTwoSmallBlock Bs eta (τ '' S) (τ '' T) := by
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  have hM : (ggBlockComm Bs eta T ⊓ Subgroup.centralizer (ggBsCoordZeroOn Bs eta S : Set G)).map
      (MulAut.conj g).toMonoidHom = ggBlockComm Bs eta (τ '' T) ⊓
        Subgroup.centralizer (ggBsCoordZeroOn Bs eta (τ '' S) : Set G) := by
    rw [Subgroup.map_inf _ _ _ hinj, ggBlockComm_map_conj hg hτ, map_conj_centralizer,
      ggBsCoordZeroOn_map_conj hg hτ]
  rw [ggQTwoSmallBlock, ggQTwoSmallBlock, MonoidHom.map_closure, ← hM]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, by rw [← map_mul, hx2, map_one]⟩
  · rintro ⟨⟨x, hx, rfl⟩, hy2⟩
    exact ⟨x, ⟨hx, hinj (by rw [map_mul, hy2, map_one])⟩, rfl⟩

variable {r : ℕ} {F : Type} [Field F]

theorem GGSpPlaneFrameOn.ggQTwoSmallBlock_eq_map_spBlock [Fact p.Prime] (hp2 : p ≠ 2)
    [CharP F 2] {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {ι : Fin (r + 1) → Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)} (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ)
    {N I : Finset (Fin (r + 1))} (hIN : I ⊆ N) (hI : I.card ≤ 2)
    (hY : ggBlockComm Bs eta (ι '' (N : Set (Fin (r + 1)))) = (spBlock F N).map κ) :
    ggQTwoSmallBlock Bs eta (ι '' (I : Set (Fin (r + 1)))) (ι '' (N : Set (Fin (r + 1)))) =
      (spBlock F I).map κ := by
  classical
  have hframe := hκ.2.2.2.2
  have hcoordI : ∀ j : Fin (r + 1), j ∉ I → ∀ k ∈ ι '' (I : Set _),
      k ≠ ι j := by
    rintro j hj _ ⟨i, hi, rfl⟩ h
    exact hj (hκ.1 h ▸ hi)
  apply le_antisymm
  · rw [ggQTwoSmallBlock, Subgroup.closure_le]
    rintro x ⟨⟨hxY, hxC⟩, hx2⟩
    rw [hY] at hxY
    obtain ⟨u, hu, rfl⟩ := hxY
    have hu2 : u * u = 1 := hκ.2.1 (by rw [map_mul, hx2, map_one])
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    have hone : (Multiplicative.ofAdd (1 : ZMod p)) ≠ 1 := by
      rw [Ne, ofAdd_eq_one]
      exact one_ne_zero
    have hg1 : ζ (Multiplicative.ofAdd 1) ≠ 1 := fun h =>
      hone (hκ.2.2.2.1 (by rw [h, map_one]))
    have hgp : ζ (Multiplicative.ofAdd 1) ^ p = 1 := by
      rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_self, ofAdd_zero, map_one]
    have htr := SpJoin.trace_ne_zero_of_pow_eq_one hg1 hodd hgp
    have hcomm : ∀ j ∈ N \ I, u * lam j (ζ (Multiplicative.ofAdd 1)) =
        lam j (ζ (Multiplicative.ofAdd 1)) * u := by
      intro j hj
      have hjI := (Finset.mem_sdiff.mp hj).2
      let b : ↥Bs := eta.symm (Pi.mulSingle (ι j) (Multiplicative.ofAdd 1))
      have hbH : (b : G) ∈
          ggBsCoordZeroOn Bs eta (ι '' (I : Set _)) := by
        rw [mem_ggBsCoordZeroOn]
        refine ⟨b.2, fun k hk => ?_⟩
        simp only [Subtype.coe_eta, b, MulEquiv.apply_symm_apply]
        exact Pi.mulSingle_eq_of_ne (hcoordI j hjI k hk) _
      have hb := Subgroup.mem_centralizer_iff.mp hxC (b : G) hbH
      have hT : SpJoin.spPlaneTorus (r + 1) ζ (fun m => eta b (ι m)) =
          lam j (ζ (Multiplicative.ofAdd 1)) := by
        have hv : (fun m => eta b (ι m)) = Pi.mulSingle j (Multiplicative.ofAdd 1) := by
          funext m
          simp only [b, MulEquiv.apply_symm_apply, Pi.mulSingle_apply, hκ.1.eq_iff]
        rw [hv, SpJoin.spPlaneTorus_mulSingle]
      have hconj := hframe b u
      rw [hT] at hconj
      have hfix : κ (lam j (ζ (Multiplicative.ofAdd 1)) * u *
          (lam j (ζ (Multiplicative.ofAdd 1)))⁻¹) = κ u := by
        rw [← hconj, hb, mul_inv_cancel_right]
      have h' := hκ.2.1 hfix
      calc u * lam j (ζ (Multiplicative.ofAdd 1))
          = (lam j (ζ (Multiplicative.ofAdd 1)) * u * (lam j (ζ (Multiplicative.ofAdd 1)))⁻¹) *
              lam j (ζ (Multiplicative.ofAdd 1)) := by rw [h']
        _ = lam j (ζ (Multiplicative.ofAdd 1)) * u := by group
    have hmem : u ∈ spBlock F N ⊓ spBlock F (N \ I)ᶜ :=
      ⟨hu, mem_spBlock_compl_of_commute_lam htr hcomm hu2⟩
    have hNI : N ∩ (N \ I)ᶜ = I := by
      ext m
      simp only [Finset.mem_inter, Finset.mem_compl, Finset.mem_sdiff, not_and, not_not]
      exact ⟨fun h => h.2 h.1, fun h => ⟨hIN h, fun _ => h⟩⟩
    rw [spBlock_inf_spBlock, hNI] at hmem
    exact ⟨u, hmem, rfl⟩
  · rw [← closure_mul_self_eq_one_spBlock hI, MonoidHom.map_closure, ggQTwoSmallBlock]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨z, ⟨hzI, hz2⟩, rfl⟩
    refine ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, by rw [← map_mul, show z * z = 1 from hz2, map_one]⟩
    · rw [hY]
      exact ⟨z, spBlock_mono hIN hzI, rfl⟩
    · refine Subgroup.mem_centralizer_iff.mpr ?_
      intro b hb
      obtain ⟨hbB, hbI⟩ := mem_ggBsCoordZeroOn.mp hb
      have hT : SpJoin.spPlaneTorus (r + 1) ζ (fun m => eta ⟨b, hbB⟩ (ι m)) ∈ spBlock F Iᶜ :=
        spPlaneTorus_mem_spBlock ζ fun m hm =>
          hbI _ ⟨m, Finset.mem_coe.mpr (by simpa using hm), rfl⟩
      have hTz := commute_of_mem_spBlock_of_disjoint disjoint_compl_left hT hzI
      have hconj := hframe ⟨b, hbB⟩ z
      rw [hTz.eq, mul_inv_cancel_right] at hconj
      calc b * κ z = (b * κ z * b⁻¹) * b := by group
        _ = κ z * b := by rw [show b * κ z * b⁻¹ = κ z from hconj]

theorem GGSpPlaneFrameOn.ggBlockComm_image_eq_map_spBlock_of_or [Finite G]
    [Fact p.Prime] (hp2 : p ≠ 2) [Finite F] [CharP F 2] {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin (r + 1) → Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) {N : Finset (Fin (r + 1))}
    (hF : 4 ≤ Nat.card F ∨ 3 ≤ N.card) (hN : N.Nonempty) (hNu : N ≠ Finset.univ) :
    ggBlockComm Bs eta (ι '' (N : Set (Fin (r + 1)))) = (spBlock F N).map κ := by
  let k := N.card - 1
  have hk : N.card = k + 1 := by
    have hpos : 0 < N.card := Finset.card_pos.mpr hN
    dsimp [k]
    omega
  let σ : Fin (k + 1) → Fin (r + 1) := N.orderEmbOfFin hk
  have hσ : Function.Injective σ := (N.orderEmbOfFin hk).injective
  have hσr : Set.range σ = (N : Set (Fin (r + 1))) := Finset.range_orderEmbOfFin N hk
  have hσs : ¬ Function.Surjective σ := by
    intro hsurj
    have huniv : (N : Set (Fin (r + 1))) = Set.univ := by
      rw [← hσr, Set.range_eq_univ.mpr hsurj]
    exact hNu (Finset.coe_injective (by simpa [Finset.coe_univ] using huniv))
  have h := hκ.ggBlockComm_eq_range_of_or (p := p) (n := n) (r := r) (k := k)
    hp2 (hF.imp_right fun h => by omega) hBs hyB hK σ hσ hσs
  have hleft : Set.range (fun l : Fin (k + 1) => ι (σ l)) =
      ι '' (N : Set (Fin (r + 1))) := by
    change Set.range (ι ∘ σ) = _
    rw [Set.range_comp, hσr]
  rw [hleft] at h
  rw [h, MonoidHom.range_comp, range_spEmbed, range_sumMap_eq_planeCoords hσr, spBlock]

theorem GGSpPlaneFrameOn.ggQTwoSmallBlock_eq_map_spBlock_of_three_le [Finite G]
    [Fact p.Prime] (hp2 : p ≠ 2) [Finite F] [CharP F 2] {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {ι : Fin (r + 1) → Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSpPlaneFrameOn Bs K eta ι κ ζ) {N I : Finset (Fin (r + 1))}
    (hN : 3 ≤ N.card) (hNu : N ≠ Finset.univ) (hIN : I ⊆ N) (hI : I.card ≤ 2) :
    ggQTwoSmallBlock Bs eta (ι '' (I : Set (Fin (r + 1)))) (ι '' (N : Set (Fin (r + 1)))) =
      (spBlock F I).map κ :=
  hκ.ggQTwoSmallBlock_eq_map_spBlock hp2 hIN hI
    (hκ.ggBlockComm_image_eq_map_spBlock_of_or hp2 hBs hyB hK (Or.inr hN)
      (Finset.card_pos.mp (by omega)) hNu)

theorem GGSecFiveBPermSpPlaneFrame.ggQTwoSmallBlock_eq_map_spBlock [Fact p.Prime] (hp2 : p ≠ 2)
    [CharP F 2] {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 2) ≃ Fin n} {κ : StatedSp (r + 1) F →* G}
    {ζ : Multiplicative (ZMod p) →* SL(2, F)} (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ)
    {N I : Finset (Fin (r + 1))} (hIN : I ⊆ N) (hI : I.card ≤ 2)
    (hY : ggBlockComm Bs eta ((fun m : Fin (r + 1) => π m.succ) '' (N : Set (Fin (r + 1)))) =
      (spBlock F N).map κ) :
    ggQTwoSmallBlock Bs eta ((fun m : Fin (r + 1) => π m.succ) '' (I : Set (Fin (r + 1))))
        ((fun m : Fin (r + 1) => π m.succ) '' (N : Set (Fin (r + 1)))) =
      (spBlock F I).map κ := by
  exact GGSpPlaneFrameOn.ggQTwoSmallBlock_eq_map_spBlock hp2 hκ.planeFrameOn hIN hI hY

theorem GGSecFiveBPermSpPlaneFrame.ggBlockComm_image_succ_eq_map_spBlock_of_or [Finite G]
    [Fact p.Prime] (hp2 : p ≠ 2) [Finite F] [CharP F 2] {Bs K : Subgroup G} {y : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : CFSG.Open.IsComponentOf K (Subgroup.centralizer ({y} : Set G)))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : StatedSp (r + 1) F →* G} {ζ : Multiplicative (ZMod p) →* SL(2, F)}
    (hκ : GGSecFiveBPermSpPlaneFrame Bs K eta π κ ζ) {N : Finset (Fin (r + 1))}
    (hF : 4 ≤ Nat.card F ∨ 3 ≤ N.card) (hN : N.Nonempty) (hNu : N ≠ Finset.univ) :
    ggBlockComm Bs eta ((fun m : Fin (r + 1) => π m.succ) '' (N : Set (Fin (r + 1)))) =
      (spBlock F N).map κ := by
  exact GGSpPlaneFrameOn.ggBlockComm_image_eq_map_spBlock_of_or hp2 hBs hyB hK
    hκ.planeFrameOn hF hN hNu

end CFSG.StandardType

end
