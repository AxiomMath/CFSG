module

public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredSpin
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportCharts
public import CFSG.RankThree.PartOne.KC.OrthogonalDeletionSpin
public import CFSG.RankThree.PartOne.KC.OrthogonalSpinPermutations
public import CFSG.Timmesfeld.Orders.ClassicalHypSum
public import CFSG.Permutation.SymmetricCoxeter
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityFieldNormalForm
public import CFSG.LieType.Universal.Spin.Twisted.Extras
public import CFSG.LieType.Universal.SpinOmega.CommutatorEquiv
public import CFSG.LieType.Steinberg.Presentation
import CFSG.RankThree.PartOne.S15K.FamilyForms
import CFSG.GroupTheory.WeirSylow.OrthogonalTori
import CFSG.ClassicalInvolution.WeakCT.TwistedSpinModel
import CFSG.LocalAnalysis.SeitzReduction.F4PilotTwistLevi
import CFSG.Timmesfeld.RankTwo.SimplyLaced
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Timmesfeld.ClassicalOrders
open CFSG.AGLEmbeddingD2.SquareSpinMinus
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Permutation.ProperSupportMaps
open CFSG.GroupTheory.WeirSylow
open scoped MatrixGroups

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}

theorem activeCoords_mono {S T : Finset (Fin (n - 1))} (hST : S ⊆ T) :
    activeCoords n S ⊆ activeCoords n T := by
  intro a ha
  rw [activeCoords] at ha ⊢
  rcases Finset.mem_union.mp ha with hEf | hP
  · rcases Finset.mem_union.mp hEf with hE | hF
    · rw [eCoords] at hE ⊢
      obtain ⟨k, hkS, rfl⟩ := Finset.mem_image.mp hE
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨k, hST hkS, rfl⟩))
    · rw [fCoords] at hF ⊢
      obtain ⟨k, hkS, rfl⟩ := Finset.mem_image.mp hF
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨k, hST hkS, rfl⟩))
  · exact Finset.mem_union_right _ hP

theorem anchoredSupport_mono {S T : Finset (Fin (n - 1))} (hST : S ⊆ T) :
    anchoredSupport F n S ≤ anchoredSupport F n T := by
  intro v hv
  rw [mem_anchoredSupport_iff] at hv ⊢
  exact fun a ha => hv a fun h => ha (activeCoords_mono hST h)

noncomputable abbrev chartSubgroup (S : Finset (Fin (n - 1))) :
    Subgroup (orthDerived (quadMinus n F b c)) :=
  (supportedDerived (quadMinus n F b c) (anchoredSupport F n S)).subgroupOf
    (orthDerived (quadMinus n F b c))

theorem chartSubgroup_mono (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {S T : Finset (Fin (n - 1))} (hST : S ⊆ T) :
    chartSubgroup (F := F) (b := b) (c := c) S ≤
      chartSubgroup (F := F) (b := b) (c := c) T := by
  intro x hx
  exact supportedDerived_le_supportedDerived_of_le (anchoredSupport_mono hST)
    (nondegenerate_polarBilin_restrict (polarNondegOn_anchoredSupport (F := F) hirr S))
    (nondegenerate_polarBilin_restrict (polarNondegOn_anchoredSupport (F := F) hirr T)) hx

@[expose] noncomputable def leviLocalOmega (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F) (hn4 : 4 ≤ n)
    (J : {J : Finset (Fin (n - 1)) // J.card ≤ 2}) :
    (Twisted.minusDatum n hirr).leviAmalgam J →*
      chartSubgroup (F := F) (b := b) (c := c) (totalCoords n J.1) where
  toFun x :=
    ⟨(spinEquivCommutatorQuadMinus (n := n) hn4 hirr
        (CharTwo.two_eq_zero : (2 : F) = 0)) x, by
      change (((spinEquivCommutatorQuadMinus (n := n) hn4 hirr
        (CharTwo.two_eq_zero : (2 : F) = 0)) x :
          orthDerived (quadMinus n F b c)) : Vm n F ≃ₗ[F] Vm n F) ∈
        supportedDerived (quadMinus n F b c) (anchoredSupport F n (totalCoords n J.1))
      rw [coe_spinEquivCommutatorQuadMinus_apply]
      have hle := leviM_map_spinAction_le_supportedDerived (F := F) hirr hcard
        (J.1 : Set (Fin (n - 1))) (totalCoords n J.1) (fun k hk =>
          ⟨Finset.mem_union_left _ hk,
            fun hk' => Finset.mem_union_right _
              (succ_mem_coordsF (I := (J.1 : Set (Fin (n - 1)))) hk hk')⟩)
      exact hle (Subgroup.mem_map_of_mem (spinAction (quadMinus n F b c)) x.2)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem leviLocalOmega_apply_coe (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F) (hn4 : 4 ≤ n)
    (J : {J : Finset (Fin (n - 1)) // J.card ≤ 2})
    (x : (Twisted.minusDatum n hirr).leviAmalgam J) :
    ((leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J x :
        chartSubgroup (F := F) (b := b) (c := c) (totalCoords n J.1)) :
      orthDerived (quadMinus n F b c)) =
      (spinEquivCommutatorQuadMinus (n := n) hn4 hirr
        (CharTwo.two_eq_zero : (2 : F) = 0)) x :=
  rfl

theorem isCompatible_comp_of_subgroupMaps
    {I X Y H : Type} [Preorder I] [Group X] [Group Y] [Group H]
    {A : I → Subgroup X} {B : I → Subgroup Y} (hB : Monotone B)
    (e : X →* Y) (f : ∀ i, A i →* B i)
    (hf : ∀ (i : I) (x : A i), ((f i x : B i) : Y) = e x)
    (g : ∀ i, B i →* H)
    (hg : ∀ (i j : I) (hij : i ≤ j) (x : B i),
      g j (Subgroup.inclusion (hB hij) x) = g i x) :
    IsCompatible A (fun i => (g i).comp (f i)) := by
  intro i j hij x y hxy
  have hsub : Subgroup.inclusion (hB hij) (f i x) = f j y := by
    apply Subtype.ext
    calc
      ((Subgroup.inclusion (hB hij) (f i x) : B j) : Y) = ((f i x : B i) : Y) :=
        Subgroup.coe_inclusion _ _
      _ = e x := hf i x
      _ = e y := congrArg e hxy
      _ = ((f j y : B j) : Y) := (hf j y).symm
  calc
    ((g i).comp (f i)) x = g i (f i x) := rfl
    _ = g j (Subgroup.inclusion (hB hij) (f i x)) := (hg i j hij (f i x)).symm
    _ = g j (f j y) := congrArg (g j) hsub
    _ = ((g j).comp (f j)) y := rfl

theorem isCompatible_leviLocalOmegaCharts (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F) (hn4 : 4 ≤ n) (hn : 5 ≤ n - 1)
    {H : Type} [Group H]
    (φ : ∀ S : Finset (Fin (n - 1)), S ≠ Finset.univ →
      chartSubgroup (F := F) (b := b) (c := c) S →* H)
    (hφ : ∀ (S T : Finset (Fin (n - 1))) (hS : S ≠ Finset.univ) (hT : T ≠ Finset.univ)
      (hST : S ⊆ T) (x : chartSubgroup (F := F) (b := b) (c := c) S),
      φ T hT ⟨(x : orthDerived (quadMinus n F b c)),
          chartSubgroup_mono (F := F) (b := b) (c := c) hirr hST x.2⟩ = φ S hS x) :
    IsCompatible (Twisted.minusDatum n hirr).leviAmalgam
      (fun J => (φ (totalCoords n J.1)
          (totalCoords_ne_univ (n := n) J.2 hn)).comp
        (leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J)) := by
  classical
  let A : {J : Finset (Fin (n - 1)) // J.card ≤ 2} →
      Subgroup (spinGroup (quadMinus n F b c)) :=
    fun J => (Twisted.minusDatum n hirr).leviAmalgam J
  let B : {J : Finset (Fin (n - 1)) // J.card ≤ 2} →
      Subgroup (orthDerived (quadMinus n F b c)) :=
    fun J => chartSubgroup (F := F) (b := b) (c := c) (totalCoords n J.1)
  have hB : Monotone B := fun i j hij =>
    chartSubgroup_mono (F := F) (b := b) (c := c) hirr (totalCoords_mono hij)
  let e : spinGroup (quadMinus n F b c) →* orthDerived (quadMinus n F b c) :=
    (spinEquivCommutatorQuadMinus (n := n) hn4 hirr
      (CharTwo.two_eq_zero : (2 : F) = 0)).toMonoidHom
  let f : ∀ J, A J →* B J := fun J =>
    leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J
  have hf : ∀ (J : {J : Finset (Fin (n - 1)) // J.card ≤ 2}) (x : A J),
      ((f J x : B J) : orthDerived (quadMinus n F b c)) = e x :=
    fun J x => leviLocalOmega_apply_coe (F := F) (b := b) (c := c) hirr hcard hn4 J x
  let g : ∀ J, B J →* H := fun J =>
    φ (totalCoords n J.1) (totalCoords_ne_univ (n := n) J.2 hn)
  have hg : ∀ (i j : {J : Finset (Fin (n - 1)) // J.card ≤ 2}) (hij : i ≤ j)
      (x : B i), g j (Subgroup.inclusion (hB hij) x) = g i x :=
    fun i j hij x => hφ (totalCoords n i.1) (totalCoords n j.1)
      (totalCoords_ne_univ (n := n) i.2 hn) (totalCoords_ne_univ (n := n) j.2 hn)
      (totalCoords_mono hij) x
  exact isCompatible_comp_of_subgroupMaps hB e f hf g hg

theorem existsUnique_levi_completion_of_coherent_charts
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    (hn4 : 4 ≤ n) (hn : 5 ≤ n - 1)
    {H : Type} [Group H]
    (φ : ∀ S : Finset (Fin (n - 1)), S ≠ Finset.univ →
      chartSubgroup (F := F) (b := b) (c := c) S →* H)
    (hφ : ∀ (S T : Finset (Fin (n - 1))) (hS : S ≠ Finset.univ) (hT : T ≠ Finset.univ)
      (hST : S ⊆ T) (x : chartSubgroup (F := F) (b := b) (c := c) S),
      φ T hT ⟨(x : orthDerived (quadMinus n F b c)),
          chartSubgroup_mono (F := F) (b := b) (c := c) hirr hST x.2⟩ = φ S hS x) :
    ∃! Φ : orthDerived (quadMinus n F b c) →* H,
      ∀ (J : {J : Finset (Fin (n - 1)) // J.card ≤ 2})
        (x : (Twisted.minusDatum n hirr).leviAmalgam J),
        Φ ((spinEquivCommutatorQuadMinus (n := n) hn4 hirr
            (CharTwo.two_eq_zero : (2 : F) = 0)) x) =
          φ (totalCoords n J.1) (totalCoords_ne_univ (n := n) J.2 hn)
            (leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J x) := by
  classical
  let Δ := Twisted.minusDatum n hirr
  let Ψ : ∀ J : {J : Finset (Fin (n - 1)) // J.card ≤ 2},
      Δ.leviAmalgam J →* H := fun J =>
    (φ (totalCoords n J.1) (totalCoords_ne_univ (n := n) J.2 hn)).comp
      (leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J)
  have hΨ : IsCompatible Δ.leviAmalgam Ψ :=
    isCompatible_leviLocalOmegaCharts (F := F) (b := b) (c := c) hirr hcard hn4 hn φ hφ
  have hct := Twisted.minusDatum_isCTGroupDatum (n := n) (K := F) hirr hn4
  have hU : IsUniversalCompletion.{0, 0, 0} Δ.leviAmalgam :=
    Δ.isUniversalCompletion_of_steinbergPresentation hct
      (steinbergPresentation_of_extras hct
        (Twisted.minusDatum_steinbergExtras (n := n) (K := F) hirr))
  let eΩ := spinEquivCommutatorQuadMinus (n := n) hn4 hirr
    (CharTwo.two_eq_zero : (2 : F) = 0)
  obtain ⟨Fhom, hFhom, hFhomuniq⟩ := hU H Ψ hΨ
  refine ⟨Fhom.comp eΩ.symm.toMonoidHom, ?_, ?_⟩
  · intro J x
    calc (Fhom.comp eΩ.symm.toMonoidHom) (eΩ x)
        = Fhom (eΩ.symm (eΩ x)) := rfl
      _ = Fhom x := by rw [MulEquiv.symm_apply_apply]
      _ = Ψ J x := hFhom J x
  · intro Φ hΦ
    have h1 : Φ.comp eΩ.toMonoidHom = Fhom := by
      apply hFhomuniq
      intro J x
      exact hΦ J x
    have h2 : (Fhom.comp eΩ.symm.toMonoidHom).comp eΩ.toMonoidHom = Fhom := by
      apply hFhomuniq
      intro J x
      calc ((Fhom.comp eΩ.symm.toMonoidHom).comp eΩ.toMonoidHom) x
          = Fhom (eΩ.symm (eΩ x)) := rfl
        _ = Fhom x := by rw [MulEquiv.symm_apply_apply]
        _ = Ψ J x := hFhom J x
    apply MonoidHom.ext
    intro x
    have h := congrArg
      (fun g : spinGroup (quadMinus n F b c) →* H => g (eΩ.symm x)) (h1.trans h2.symm)
    simpa [MonoidHom.comp_apply] using h

theorem totalCoords_singleton_ne_univ (k : Fin (n - 1)) (hn : 3 ≤ n - 1) :
    totalCoords n {k} ≠ Finset.univ := by
  intro h
  have hcard := card_totalCoords_le (n := n) ({k} : Finset (Fin (n - 1)))
  rw [h, Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hcard
  omega

theorem mem_totalCoords_singleton {k i : Fin (n - 1)} (h : i ∈ totalCoords n {k}) :
    i = k ∨ i.val = k.val + 1 := by
  rw [totalCoords, Finset.mem_union] at h
  rcases h with h | h
  · exact Or.inl (Finset.mem_singleton.mp h)
  · obtain ⟨j, hj, -, hij | hval⟩ := mem_coordsF.1 h
    · have hjk : j = k := by simpa using hj
      exact Or.inl (hij.trans hjk)
    · have hjk : j = k := by simpa using hj
      exact Or.inr (hjk ▸ hval)

theorem totalCoords_five_ne_univ {J : Finset (Fin 4)} (hJ : J.card ≤ 2) (hJ02 : J ≠ {0, 2}) :
    totalCoords 5 J ≠ Finset.univ := by
  classical
  let sp : Fin 4 → Fin 4 := fun i => if h : i.val + 1 < 4 then ⟨i.val + 1, h⟩ else i
  have hsub : totalCoords 5 J ⊆ J ∪ J.image sp := by
    intro a ha
    rw [totalCoords, Finset.mem_union] at ha
    rcases ha with haJ | haC
    · exact Finset.mem_union_left _ haJ
    · obtain ⟨i, hi, hk, rfl | hval⟩ := mem_coordsF.1 haC
      · exact Finset.mem_union_left _ hi
      · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, hi, ?_⟩)
        apply Fin.ext
        have hk' : i.val + 1 < 4 := hk
        simp [sp, hk', hval]
  have key : ∀ J : Finset (Fin 4), J.card ≤ 2 → J ≠ {0, 2} → J ∪ J.image sp ≠ Finset.univ := by
    decide
  intro h
  exact key J hJ hJ02 (Finset.eq_univ_of_forall fun a => hsub (h ▸ Finset.mem_univ a))

theorem totalCoords_five_zero_two : totalCoords 5 ({0, 2} : Finset (Fin 4)) = Finset.univ := by
  classical
  refine Finset.eq_univ_of_forall fun a => ?_
  rw [totalCoords, Finset.mem_union]
  right
  rw [mem_coordsF]
  fin_cases a
  · exact ⟨0, by simp, by decide, Or.inl rfl⟩
  · exact ⟨0, by simp, by decide, Or.inr rfl⟩
  · exact ⟨2, by simp, by decide, Or.inl rfl⟩
  · exact ⟨2, by simp, by decide, Or.inr rfl⟩

private theorem subset_zero_two {J : Finset (Fin 4)} (h : J ⊆ {0, 2}) (hne : J ≠ {0, 2}) :
    J = ∅ ∨ J = {0} ∨ J = {2} := by
  have key : ∀ J : Finset (Fin 4), J ⊆ {0, 2} → J ≠ {0, 2} → J = ∅ ∨ J = {0} ∨ J = {2} := by
    decide
  exact key J h hne

private theorem eq_zero_two_of_subset {J : Finset (Fin 4)} (hJ : J.card ≤ 2)
    (h : ({0, 2} : Finset (Fin 4)) ⊆ J) : J = {0, 2} := by
  have hc : ({0, 2} : Finset (Fin 4)).card = 2 := by decide
  exact (Finset.eq_of_subset_of_card_le h (by omega)).symm

section Five

variable (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

local notation "Δ" => minusDatum 5 hirr

omit [Finite F] [CharP F 2] in
private theorem commute_rankOne_zero_two :
    ∀ x ∈ rankOne (Δ).rootGroup (0 : Fin 4),
      ∀ y ∈ rankOne (Δ).rootGroup (2 : Fin 4), x * y = y * x := by
  intro x hx y hy
  have h0 : (0 : Fin (5 - 1)).val + 1 < 5 - 1 := by decide
  have h2 : (2 : Fin (5 - 1)).val + 1 < 5 - 1 := by decide
  rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr h0] at hx
  rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr h2] at hy
  obtain ⟨A, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := hy
  exact (CFSG.ClassicalInvolution.WeakCT.commute_rLong_rLong h0 h2 (by decide) A B).eq

omit [CharP F 2] in
private theorem rankOne_zero_inf_two :
    rankOne (Δ).rootGroup (0 : Fin 4) ⊓
      rankOne (Δ).rootGroup (2 : Fin 4) = ⊥ :=
  CFSG.SeitzReduction.F4Pilot.rankOne_inf_rankOne_eq_bot
    (minusDatum_isCTGroupDatum 5 hirr (by norm_num)) (minusDatum_steinbergExtras 5 hirr)
    (show (0 : Fin 4) ≠ 2 by decide) fun x hx y hy => commute_rankOne_zero_two hirr x hx y hy

omit [Finite F] [CharP F 2] in
private theorem levi_zero_two :
    levi (Δ).rootGroup ({0, 2} : Finset (Fin 4)) =
      rankOne (Δ).rootGroup (0 : Fin 4) ⊔
        rankOne (Δ).rootGroup (2 : Fin 4) := by
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    rcases Finset.mem_insert.mp hj with rfl | hj2
    · exact le_sup_left
    · rw [Finset.mem_singleton.mp hj2]
      exact le_sup_right
  · exact sup_le (le_iSup₂_of_le (0 : Fin 4) (Finset.mem_insert_self (0 : Fin 4) {2}) le_rfl)
      (le_iSup₂_of_le (2 : Fin 4)
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self (2 : Fin 4))) le_rfl)

theorem existsUnique_levi_completion_of_coherent_charts_five (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (φ : ∀ S : Finset (Fin 4), S ≠ Finset.univ →
      chartSubgroup (n := 5) (F := F) (b := b) (c := c) S →* H)
    (hφ : ∀ (S T : Finset (Fin 4)) (hS : S ≠ Finset.univ) (hT : T ≠ Finset.univ)
      (hST : S ⊆ T) (x : chartSubgroup (n := 5) (F := F) (b := b) (c := c) S),
      φ T hT ⟨(x : orthDerived (quadMinus 5 F b c)),
          chartSubgroup_mono (n := 5) (F := F) (b := b) (c := c) hirr hST x.2⟩ = φ S hS x)
    (hdisj : ∀ (x : (Δ).leviAmalgam ⟨({0} : Finset (Fin 4)),
      (Finset.card_singleton (0 : Fin 4)).trans_le (by norm_num)⟩)
      (y : (Δ).leviAmalgam ⟨({2} : Finset (Fin 4)),
      (Finset.card_singleton (2 : Fin 4)).trans_le (by norm_num)⟩),
      Commute
        (φ (totalCoords 5 ({0} : Finset (Fin 4))) (totalCoords_five_ne_univ (by decide) (by decide))
          (leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard (by norm_num)
            ⟨({0} : Finset (Fin 4)), (Finset.card_singleton (0 : Fin 4)).trans_le (by norm_num)⟩ x))
        (φ (totalCoords 5 ({2} : Finset (Fin 4))) (totalCoords_five_ne_univ (by decide) (by decide))
          (leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard (by norm_num)
            ⟨({2} : Finset (Fin 4)), (Finset.card_singleton (2 : Fin 4)).trans_le (by norm_num)⟩
            y))) :
    ∃! Φ : orthDerived (quadMinus 5 F b c) →* H,
      ∀ (J : {J : Finset (Fin 4) // J.card ≤ 2}) (hJ : totalCoords 5 J.1 ≠ Finset.univ)
        (x : (Δ).leviAmalgam J),
        Φ ((spinEquivCommutatorQuadMinus (n := 5) (by norm_num) hirr
            (CharTwo.two_eq_zero : (2 : F) = 0)) x) =
          φ (totalCoords 5 J.1) hJ
            (leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard (by norm_num) J x) := by
  classical
  have hn4 : 4 ≤ 5 := by norm_num
  let eΩ := spinEquivCommutatorQuadMinus (n := 5) hn4 hirr (CharTwo.two_eq_zero : (2 : F) = 0)
  let J0 : {J : Finset (Fin 4) // J.card ≤ 2} := ⟨{0}, by decide⟩
  let J2 : {J : Finset (Fin 4) // J.card ≤ 2} := ⟨{2}, by decide⟩
  let JB : {J : Finset (Fin 4) // J.card ≤ 2} := ⟨{0, 2}, by decide⟩
  let ψ0 : rankOne (Δ).rootGroup (0 : Fin 4) →* H :=
    ((φ (totalCoords 5 J0.1) (totalCoords_five_ne_univ (by decide) (by decide))).comp
      (leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard hn4 J0)).comp
      (Subgroup.inclusion (rankOne_le_levi (X := (Δ).rootGroup) (Finset.mem_singleton_self _)))
  let ψ2 : rankOne (Δ).rootGroup (2 : Fin 4) →* H :=
    ((φ (totalCoords 5 J2.1) (totalCoords_five_ne_univ (by decide) (by decide))).comp
      (leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard hn4 J2)).comp
      (Subgroup.inclusion (rankOne_le_levi (X := (Δ).rootGroup) (Finset.mem_singleton_self _)))
  have hψc : ∀ u v, Commute (ψ0 u) (ψ2 v) := fun u v => hdisj _ _
  let P : rankOne (Δ).rootGroup (0 : Fin 4) × rankOne (Δ).rootGroup (2 : Fin 4) →*
      spinGroup (quadMinus 5 F b c) :=
    (rankOne (Δ).rootGroup (0 : Fin 4)).subtype.noncommCoprod
      (rankOne (Δ).rootGroup (2 : Fin 4)).subtype
      (fun u v => commute_rankOne_zero_two hirr u u.2 v v.2)
  have hPinj : Function.Injective P := by
    refine (MonoidHom.noncommCoprod_injective _ _ _).mpr
      ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, ?_⟩
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact disjoint_iff.mpr (rankOne_zero_inf_two hirr)
  have hPrange : P.range = (Δ).leviAmalgam JB := by
    refine (MonoidHom.noncommCoprod_range _ _ _).trans ?_
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact (levi_zero_two hirr).symm
  let e := (MonoidHom.ofInjective hPinj).trans (MulEquiv.subgroupCongr hPrange)
  let badHom : (Δ).leviAmalgam JB →* H := (ψ0.noncommCoprod ψ2 hψc).comp e.symm.toMonoidHom
  have hbad0 : ∀ (z : (Δ).leviAmalgam JB) (u : rankOne (Δ).rootGroup (0 : Fin 4)),
      (z : spinGroup (quadMinus 5 F b c)) = u → badHom z = ψ0 u := by
    intro z u hzu
    have he : e.symm z = (u, 1) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change (z : spinGroup (quadMinus 5 F b c)) =
        (u : spinGroup (quadMinus 5 F b c)) * ((1 : rankOne (Δ).rootGroup (2 : Fin 4)) :
          spinGroup (quadMinus 5 F b c))
      rw [Subgroup.coe_one, mul_one, hzu]
    change (ψ0.noncommCoprod ψ2 hψc) (e.symm z) = _
    rw [he, MonoidHom.noncommCoprod_apply, map_one, mul_one]
  have hbad2 : ∀ (z : (Δ).leviAmalgam JB) (v : rankOne (Δ).rootGroup (2 : Fin 4)),
      (z : spinGroup (quadMinus 5 F b c)) = v → badHom z = ψ2 v := by
    intro z v hzv
    have he : e.symm z = (1, v) := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      change (z : spinGroup (quadMinus 5 F b c)) =
        ((1 : rankOne (Δ).rootGroup (0 : Fin 4)) : spinGroup (quadMinus 5 F b c)) *
          (v : spinGroup (quadMinus 5 F b c))
      rw [Subgroup.coe_one, one_mul, hzv]
    change (ψ0.noncommCoprod ψ2 hψc) (e.symm z) = _
    rw [he, MonoidHom.noncommCoprod_apply, map_one, one_mul]
  let Ψ : ∀ J : {J : Finset (Fin 4) // J.card ≤ 2}, (Δ).leviAmalgam J →* H := fun J =>
    if h : J.1 = {0, 2} then
      badHom.comp (Subgroup.inclusion (show (Δ).leviAmalgam J ≤ (Δ).leviAmalgam JB by
        show levi (Δ).rootGroup J.1 ≤ levi (Δ).rootGroup ({0, 2} : Finset (Fin 4))
        rw [h]))
    else
      (φ (totalCoords 5 J.1) (totalCoords_five_ne_univ J.2 h)).comp
        (leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard hn4 J)
  have hΨ : IsCompatible (fun J : {J : Finset (Fin 4) // J.card ≤ 2} => (Δ).leviAmalgam J) Ψ := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ hIJ x y hxy
    have hIJ' : I ⊆ J := hIJ
    by_cases hJB : J = ({0, 2} : Finset (Fin 4))
    · subst hJB
      by_cases hIB : I = ({0, 2} : Finset (Fin 4))
      · subst hIB
        simp only [Ψ, dif_pos rfl, MonoidHom.comp_apply]
        congr 1
        exact Subtype.ext hxy
      · simp only [Ψ, dif_neg hIB, dif_pos rfl, MonoidHom.comp_apply]
        rcases subset_zero_two hIJ' hIB with rfl | rfl | rfl
        · have hx1 : x = 1 := by
            have hx : (x : spinGroup (quadMinus 5 F b c)) ∈
                levi (Δ).rootGroup (∅ : Finset (Fin 4)) := x.2
            have hle : levi (Δ).rootGroup (∅ : Finset (Fin 4)) ≤ ⊥ :=
              iSup₂_le fun j hj => absurd hj (Finset.notMem_empty _)
            exact Subtype.ext (Subgroup.mem_bot.mp (hle hx))
          have hy1 : y = 1 := by
            apply Subtype.ext
            rw [← hxy, hx1]
            rfl
          rw [hx1, hy1]
          simp only [map_one]
        · have hx0 : (x : spinGroup (quadMinus 5 F b c)) ∈ rankOne (Δ).rootGroup (0 : Fin 4) := by
            have hx : (x : spinGroup (quadMinus 5 F b c)) ∈
                levi (Δ).rootGroup ({0} : Finset (Fin 4)) := x.2
            exact (levi_singleton (Δ).rootGroup (0 : Fin 4)).le hx
          refine Eq.trans ?_ (hbad0 _ ⟨x, hx0⟩ ?_).symm
          · simp only [ψ0, J0, MonoidHom.comp_apply]
            congr 1
          · rw [Subgroup.coe_inclusion, ← hxy]
        · have hx2 : (x : spinGroup (quadMinus 5 F b c)) ∈ rankOne (Δ).rootGroup (2 : Fin 4) := by
            have hx : (x : spinGroup (quadMinus 5 F b c)) ∈
                levi (Δ).rootGroup ({2} : Finset (Fin 4)) := x.2
            exact (levi_singleton (Δ).rootGroup (2 : Fin 4)).le hx
          refine Eq.trans ?_ (hbad2 _ ⟨x, hx2⟩ ?_).symm
          · simp only [ψ2, J2, MonoidHom.comp_apply]
            congr 1
          · rw [Subgroup.coe_inclusion, ← hxy]
    · have hIB : I ≠ ({0, 2} : Finset (Fin 4)) := by
        rintro rfl
        exact hJB (eq_zero_two_of_subset hJ hIJ')
      simp only [Ψ, dif_neg hIB, dif_neg hJB, MonoidHom.comp_apply]
      have hsub : Subgroup.inclusion (chartSubgroup_mono (n := 5) (F := F) (b := b) (c := c) hirr
          (totalCoords_mono (n := 5) hIJ'))
          (leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard hn4 ⟨I, hI⟩ x) =
          leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard hn4 ⟨J, hJ⟩ y := by
        apply Subtype.ext
        change eΩ (x : spinGroup (quadMinus 5 F b c)) = eΩ (y : spinGroup (quadMinus 5 F b c))
        rw [hxy]
      rw [← hsub]
      exact (hφ _ _ _ _ (totalCoords_mono (n := 5) hIJ') _).symm
  have hct := minusDatum_isCTGroupDatum (n := 5) (K := F) hirr hn4
  have hU : IsUniversalCompletion.{0, 0, 0} (Δ).leviAmalgam :=
    (Δ).isUniversalCompletion_of_steinbergPresentation hct
      (steinbergPresentation_of_extras hct (minusDatum_steinbergExtras (n := 5) (K := F) hirr))
  obtain ⟨Fhom, hFhom, -⟩ := hU H Ψ hΨ
  have hval : ∀ (J : {J : Finset (Fin 4) // J.card ≤ 2}) (hJ : totalCoords 5 J.1 ≠ Finset.univ)
      (x : (Δ).leviAmalgam J), Fhom x = φ (totalCoords 5 J.1) hJ
        (leviLocalOmega (n := 5) (F := F) (b := b) (c := c) hirr hcard hn4 J x) := by
    intro J hJ x
    have hJB : J.1 ≠ {0, 2} := by
      intro h
      exact hJ (h ▸ totalCoords_five_zero_two)
    rw [hFhom J x]
    simp only [Ψ, dif_neg hJB, MonoidHom.comp_apply]
  refine ⟨Fhom.comp eΩ.symm.toMonoidHom, ?_, ?_⟩
  · intro J hJ x
    change Fhom (eΩ.symm (eΩ x)) = _
    rw [MulEquiv.symm_apply_apply]
    exact hval J hJ x
  · intro Φ hΦ
    have hgen : ⨆ k : Fin 4, rankOne (Δ).rootGroup k = ⊤ :=
      CFSG.ClassicalInvolution.WeakCT.iSup_rankOne_minusDatum hirr hn4
    have huse : ∀ (k : Fin 4) (u : spinGroup (quadMinus 5 F b c)),
        u ∈ rankOne (Δ).rootGroup k → Φ (eΩ u) = Fhom u := by
      intro k u hu
      have hk1 : ({k} : Finset (Fin 4)).card ≤ 2 :=
        (Finset.card_singleton k).trans_le (by norm_num)
      have hk02 : ({k} : Finset (Fin 4)) ≠ {0, 2} := by
        intro h
        have h' := congrArg Finset.card h
        rw [Finset.card_singleton] at h'
        exact absurd h' (by decide)
      let Jk : {J : Finset (Fin 4) // J.card ≤ 2} := ⟨{k}, hk1⟩
      have hJk : totalCoords 5 ({k} : Finset (Fin 4)) ≠ Finset.univ :=
        totalCoords_five_ne_univ hk1 hk02
      have hle : rankOne (Δ).rootGroup k ≤ (Δ).leviAmalgam Jk :=
        rankOne_le_levi (X := (Δ).rootGroup) (Finset.mem_singleton_self _)
      exact (hΦ Jk hJk ⟨u, hle hu⟩).trans (hval Jk hJk ⟨u, hle hu⟩).symm
    have hext : ∀ z : spinGroup (quadMinus 5 F b c), Φ (eΩ z) = Fhom z := by
      intro z
      have hz : z ∈ ⨆ k : Fin 4, rankOne (Δ).rootGroup k := hgen ▸ Subgroup.mem_top z
      refine Subgroup.iSup_induction (fun k : Fin 4 => rankOne (Δ).rootGroup k)
        (C := fun z => Φ (eΩ z) = Fhom z) hz (fun k u hu => huse k u hu) ?_ ?_
      · simp only [map_one]
      · intro u v hu hv
        simp only [map_mul, hu, hv]
    apply MonoidHom.ext
    intro x
    calc Φ x = Φ (eΩ (eΩ.symm x)) := by rw [MulEquiv.apply_symm_apply]
      _ = Fhom (eΩ.symm x) := hext _
      _ = (Fhom.comp eΩ.symm.toMonoidHom) x := rfl

end Five

theorem existsUnique_levi_completion_of_coherent_charts_of_three_le (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (φ : ∀ S : Finset (Fin (r + 1)), S ≠ Finset.univ →
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S →* H)
    (hφ : ∀ (S T : Finset (Fin (r + 1))) (hS : S ≠ Finset.univ) (hT : T ≠ Finset.univ)
      (hST : S ⊆ T) (x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S),
      φ T hT ⟨(x : orthDerived (quadMinus (r + 2) F b c)),
          chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr hST x.2⟩ = φ S hS x)
    (hdisj : 4 ≤ r ∨
      ∀ (x : (minusDatum (r + 2) hirr).leviAmalgam
          ⟨({⟨0, by omega⟩} : Finset (Fin (r + 1))),
            (Finset.card_singleton _).trans_le (by norm_num)⟩)
        (y : (minusDatum (r + 2) hirr).leviAmalgam
          ⟨({⟨2, by omega⟩} : Finset (Fin (r + 1))),
            (Finset.card_singleton _).trans_le (by norm_num)⟩),
        Commute
          (φ (totalCoords (r + 2) {⟨0, by omega⟩}) (totalCoords_singleton_ne_univ _ (by omega))
            (leviLocalOmega (n := r + 2) (F := F) (b := b) (c := c) hirr hcard (by omega)
              ⟨({⟨0, by omega⟩} : Finset (Fin (r + 1))),
                (Finset.card_singleton _).trans_le (by norm_num)⟩ x))
          (φ (totalCoords (r + 2) {⟨2, by omega⟩}) (totalCoords_singleton_ne_univ _ (by omega))
            (leviLocalOmega (n := r + 2) (F := F) (b := b) (c := c) hirr hcard (by omega)
              ⟨({⟨2, by omega⟩} : Finset (Fin (r + 1))),
                (Finset.card_singleton _).trans_le (by norm_num)⟩ y))) :
    ∃! Φ : orthDerived (quadMinus (r + 2) F b c) →* H,
      ∀ (J : {J : Finset (Fin (r + 1)) // J.card ≤ 2})
        (hJ : totalCoords (r + 2) J.1 ≠ Finset.univ)
        (x : (minusDatum (r + 2) hirr).leviAmalgam J),
        Φ ((spinEquivCommutatorQuadMinus (n := r + 2) (by omega) hirr
            (CharTwo.two_eq_zero : (2 : F) = 0)) x) =
          φ (totalCoords (r + 2) J.1) hJ
            (leviLocalOmega (n := r + 2) (F := F) (b := b) (c := c) hirr hcard (by omega) J x) := by
  by_cases hr4 : 4 ≤ r
  · obtain ⟨Φ, hΦ, huniq⟩ := existsUnique_levi_completion_of_coherent_charts
      (n := r + 2) (F := F) (b := b) (c := c) hirr hcard (by omega) (by omega) φ hφ
    exact ⟨Φ, fun J _ x => hΦ J x, fun Ψ hΨ => huniq Ψ fun J x => hΨ J _ x⟩
  · obtain rfl : r = 3 := by omega
    exact existsUnique_levi_completion_of_coherent_charts_five hirr hcard φ hφ
      (hdisj.resolve_left hr4)

theorem quadMinus_eq_binaryForm_add_minusPlaneCoordinates (r : ℕ)
    (v : Vm (r + 2) F) :
    quadMinus (r + 2) F b c v =
      binaryForm F b c (minusPlaneCoordinates (n := r + 2) (F := F) v).1 +
        ∑ i, hypPlane F ((minusPlaneCoordinates (n := r + 2) (F := F) v).2 i) := by
  simp only [minusPlaneCoordinates_apply, quadMinus_apply, binaryForm_apply, hypPlane_apply]
  ring_nf

theorem hypPlane_polarBilin_nondegenerate :
    (polarBilin (hypPlane F)).Nondegenerate := by
  refine nondegenerate_polarBilin_of_forall (Q := hypPlane F) fun p hp => ?_
  have hpolar : ∀ p q : F × F, polar (hypPlane F) p q = p.1 * q.2 + q.1 * p.2 := by
    intro p q
    simp only [QuadraticMap.polar, hypPlane_apply, Prod.fst_add, Prod.snd_add]
    ring
  have h1 := hp (0, 1)
  have h2 := hp (1, 0)
  rw [hpolar] at h1 h2
  simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] at h1 h2
  exact Prod.ext h1 h2

section CalibratedDeletionChart

variable {r : ℕ} {G : Type} [Group G] {u : Fin (r + 1)}

local notation "I" => Fin (r + 1)
local notation "C" =>
  chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
local notation "D0" => deletionPlanes r
local notation "Du" => (Finset.univ.erase u : Finset I)
local notation "O" => (D0 ∩ Du)

private noncomputable def coordPlaneIsometry
    (ψ : Vm (r + 2) F ≃ₗ[F] (Fin 2 → F) × (Fin (r + 1) → F × F))
    (hψ : ∀ v : Vm (r + 2) F,
      quadMinus (r + 2) F b c v =
        binaryForm F b c (ψ v).1 + ∑ i, hypPlane F ((ψ v).2 i))
    (i : Fin (r + 1)) :
    (hypPlane F).IsometryEquiv
      ((quadMinus (r + 2) F b c).comp (coordPlane ψ i).subtype) :=
  let L : (F × F) →ₗ[F] ((Fin 2 → F) × (Fin (r + 1) → F × F)) :=
    (0 : (F × F) →ₗ[F] (Fin 2 → F)).prod
      (LinearMap.single F (fun _ : Fin (r + 1) => F × F) i)
  { toLinearEquiv :=
    { toFun := fun z => ⟨ψ.symm (L z), by
        have hL : L z = (0, Pi.single i z) := by simp [L, LinearMap.single_apply]
        rw [hL]
        exact mem_coordPlane.mpr ⟨z, rfl⟩⟩
      invFun := fun x => (ψ (x : Vm (r + 2) F)).2 i
      left_inv := by
        intro z
        simp [L, LinearMap.single_apply]
      right_inv := by
        intro x
        apply Subtype.ext
        obtain ⟨z, hz⟩ := mem_coordPlane.mp x.2
        change ψ.symm (L ((ψ (x : Vm (r + 2) F)).2 i)) = (x : Vm (r + 2) F)
        have hLx : L ((ψ (x : Vm (r + 2) F)).2 i) =
            (0, Pi.single i ((ψ (x : Vm (r + 2) F)).2 i)) := by
          simp [L, LinearMap.single_apply]
        rw [hLx]
        have hpsi : ψ (x : Vm (r + 2) F) = (0, Pi.single i z) := by
          rw [← hz, LinearEquiv.apply_symm_apply]
        rw [hpsi]
        simp only [Prod.snd, Pi.single_eq_same]
        exact hz
      map_add' := by
        intro x y
        apply Subtype.ext
        change ψ.symm (L (x + y)) = ψ.symm (L x) + ψ.symm (L y)
        rw [map_add, map_add]
      map_smul' := by
        intro c x
        apply Subtype.ext
        change ψ.symm (L (c • x)) = c • ψ.symm (L x)
        rw [map_smul, map_smul] }
    map_app' := by
      intro z
      change quadMinus (r + 2) F b c (ψ.symm (L z)) = hypPlane F z
      have hL : L z = (0, Pi.single i z) := by simp [L, LinearMap.single_apply]
      rw [hL, hψ]
      simp only [LinearEquiv.apply_symm_apply]
      have hsum : (∑ t, hypPlane F ((Pi.single i z : Fin (r + 1) → F × F) t)) =
          hypPlane F z := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Pi.single_eq_of_ne hji, hypPlane_apply]
        · simp
      rw [hsum]
      simp [binaryForm_apply, hypPlane_apply] }

private theorem map_subgroupOfEquivOfLe_symm
    {G : Type} [Group G] {A B D : Subgroup G} (hBD : B ≤ D) :
    (A.subgroupOf B).map (Subgroup.subgroupOfEquivOfLe hBD).symm.toMonoidHom =
      (A.subgroupOf D).subgroupOf (B.subgroupOf D) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    refine ⟨⟨x.1, x.2⟩, ?_, ?_⟩
    · have hx' : ((x.1 : D) : G) ∈ A := hx
      exact hx'
    · rfl

private theorem coordAnchor_anisotropic_and_notPlus
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (ψ : Vm (r + 2) F ≃ₗ[F] (Fin 2 → F) × (Fin (r + 1) → F × F))
    (hψ : ∀ v : Vm (r + 2) F,
      quadMinus (r + 2) F b c v =
        binaryForm F b c (ψ v).1 + ∑ i, hypPlane F ((ψ v).2 i))
    (hW0dim : finrank F (coordAnchor ψ) = 2) :
    (∀ v ∈ coordAnchor ψ, quadMinus (r + 2) F b c v = 0 → v = 0) ∧
      ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
        ((quadMinus (r + 2) F b c).comp (coordAnchor ψ).subtype) := by
  have hWaniso : ∀ v ∈ coordAnchor ψ, quadMinus (r + 2) F b c v = 0 → v = 0 := by
    intro v hv hQv
    obtain ⟨w, hw⟩ := mem_coordAnchor.mp hv
    have hψv : ψ v = (w, 0) := by
      rw [← hw, LinearEquiv.apply_symm_apply]
    have hbin : binaryForm F b c w = 0 := by
      have h := hψ v
      rw [hψv, hQv] at h
      simpa using h.symm
    rw [binaryForm_apply] at hbin
    obtain ⟨h0, h1⟩ :=
      CFSG.ClassicalGroups.Orthogonal.binary_eq_zero_of_irreducible
        (b := b) (c := c) hirr (u := w 0) (v := w 1) hbin
    have hw0 : w = 0 := by
      funext t
      fin_cases t
      · simpa using h0
      · simpa using h1
    rw [← hw, hw0]
    simp
  refine ⟨hWaniso, ?_⟩
  exact CFSG.RankThree.PartOne.S15K.not_isPlusType_of_aniso_plane
    (Q := quadMinus (r + 2) F b c) (P := coordAnchor ψ) hW0dim hWaniso

private theorem orthDerivedEquiv_apply_coe
    {K V V' : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (e : Q.IsometryEquiv Q') (g : orthDerived Q) :
    ((CFSG.RankThree.PartOne.orthDerivedEquiv e g : orthDerived Q') :
        V' ≃ₗ[K] V') =
      CFSG.RankThree.PartOne.linConj e.toLinearEquiv (g : V ≃ₗ[K] V) := by
  rfl

private theorem orthExtend_linConj_prod_eq
    {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {A E B P T : Submodule K V}
    (hAP : IsCompl A P) (hBT : IsCompl B T)
    (hEP : E ≤ P) (hTP : T ≤ P)
    (J : (A × E) ≃ₗ[K] B)
    (hJ : ∀ (a : A) (e : E), (J (a, e) : V) = (a : V) + (e : V))
    (g : A ≃ₗ[K] A) :
    orthExtend hBT
      (CFSG.RankThree.PartOne.linConj J
        (g.prodCongr (LinearEquiv.refl K E))) =
      orthExtend hAP g := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨b, t, hx⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hBT x
  obtain ⟨⟨a, e⟩, hb⟩ := J.surjective b
  have hx' : x = (J (a, e) : V) + (t : V) := by simpa only [hb] using hx
  rw [hx', orthExtend_apply hBT _ (J (a, e)) t]
  simp only [CFSG.RankThree.PartOne.linConj_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, hJ]
  simpa only [add_assoc] using
    (orthExtend_apply hAP g a
      ⟨(e : V) + (t : V), P.add_mem (hEP e.2) (hTP t.2)⟩).symm

private theorem supportedChartEquiv_apply_coe
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {A : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hAle : supportedDerived Q A ≤ orthDerived Q)
    (x : orthDerived (Q.comp A.subtype)) :
    (((((orthDerivedSupportedEquiv hA).trans
        (Subgroup.subgroupOfEquivOfLe hAle).symm) x :
        (supportedDerived Q A).subgroupOf (orthDerived Q)) :
        orthDerived Q) : V ≃ₗ[K] V) =
      ((orthDerivedSupportedEquiv hA x : supportedDerived Q A) : V ≃ₗ[K] V) := by
  rfl

private theorem supportedEquiv_prodIncl_coe
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {A E B : Submodule K V}
    (hA : (polarBilin (Q.comp A.subtype)).Nondegenerate)
    (hB : (polarBilin (Q.comp B.subtype)).Nondegenerate)
    (hAB : A ≤ B) (hEA : E ≤ suppPerp Q A)
    (J : ((Q.comp A.subtype).prod (Q.comp E.subtype)).IsometryEquiv
      (Q.comp B.subtype))
    (hJ : ∀ (a : A) (e : E), (J (a, e) : V) = (a : V) + (e : V))
    (g : orthDerived (Q.comp A.subtype)) :
    ((orthDerivedSupportedEquiv hB
        (CFSG.RankThree.PartOne.orthDerivedEquiv J
          (orthDerivedProdIncl (Q := Q.comp A.subtype) (R := Q.comp E.subtype) g)) :
      supportedDerived Q B) : V ≃ₗ[K] V) =
    ((orthDerivedSupportedEquiv hA g : supportedDerived Q A) : V ≃ₗ[K] V) := by
  rw [orthDerivedSupportedEquiv_apply hB, orthDerivedSupportedEquiv_apply hA]
  have hT : suppPerp Q B ≤ suppPerp Q A := by
    intro x hx
    rw [mem_suppPerp] at hx ⊢
    intro a ha
    exact hx a (hAB ha)
  have hcomp : ((CFSG.RankThree.PartOne.orthDerivedEquiv J
      (orthDerivedProdIncl (Q := Q.comp A.subtype) (R := Q.comp E.subtype) g) :
        orthDerived (Q.comp B.subtype)) : B ≃ₗ[K] B) =
      CFSG.RankThree.PartOne.linConj J.toLinearEquiv
        ((g : A ≃ₗ[K] A).prodCongr (LinearEquiv.refl K E)) := by
    rw [orthDerivedEquiv_apply_coe, coe_orthDerivedProdIncl]
  rw [hcomp]
  exact orthExtend_linConj_prod_eq
    (isCompl_suppPerp (polarNondegOn_of_nondegenerate hA))
    (isCompl_suppPerp (polarNondegOn_of_nondegenerate hB))
    hEA hT J.toLinearEquiv hJ g

private theorem autCongr_eq_linConj
    {K V V' : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (e : V ≃ₗ[K] V') :
    LinearEquiv.autCongr e = CFSG.RankThree.PartOne.linConj e := by
  apply MulEquiv.ext
  intro g
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.autCongr_apply_apply, CFSG.RankThree.PartOne.linConj_apply]

private theorem map_orthDerivedEquiv_supportedSubgroup
    {K V V' : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V] [FiniteDimensional K V']
    {Q : QuadraticForm K V} {Q' : QuadraticForm K V'}
    (e : Q.IsometryEquiv Q') {R : Submodule K V}
    (hR : (polarBilin (Q.comp R.subtype)).Nondegenerate)
    (hR' : (polarBilin (Q'.comp (R.map e.toLinearEquiv.toLinearMap).subtype)).Nondegenerate) :
    ((supportedDerived Q R).subgroupOf (orthDerived Q)).map
        (CFSG.RankThree.PartOne.orthDerivedEquiv e).toMonoidHom =
      (supportedDerived Q' (R.map e.toLinearEquiv.toLinearMap)).subgroupOf
        (orthDerived Q') := by
  apply Subgroup.map_injective (f := (orthDerived Q').subtype) (Subtype.coe_injective)
  rw [Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le (supportedDerived_le_orthDerived_of_regular hR')]
  have hcomp : ((orthDerived Q').subtype.comp
      (CFSG.RankThree.PartOne.orthDerivedEquiv e).toMonoidHom) =
      (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom.comp
        (orthDerived Q).subtype := by
    apply MonoidHom.ext
    intro g
    apply LinearEquiv.ext
    intro v
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    change ((CFSG.RankThree.PartOne.orthDerivedEquiv e g :
        orthDerived Q') : V' ≃ₗ[K] V') v =
      (LinearEquiv.autCongr e.toLinearEquiv (g : V ≃ₗ[K] V)) v
    rw [orthDerivedEquiv_apply_coe, autCongr_eq_linConj]
  rw [hcomp, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le (supportedDerived_le_orthDerived_of_regular hR)]
  exact map_supportedDerived_isometryEquiv e

private theorem map_supported_subgroup_through_isometry_chart
    {K V1 V2 H : Type} [Field K]
    [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1]
    [AddCommGroup V2] [Module K V2] [FiniteDimensional K V2] [Group H]
    {Q1 : QuadraticForm K V1} {Q2 : QuadraticForm K V2}
    (J : Q1.IsometryEquiv Q2) (e2 : orthDerived Q2 ≃* H)
    (P1 : Submodule K V1) (P2 : Submodule K V2)
    (hP1 : (polarBilin (Q1.comp P1.subtype)).Nondegenerate)
    (hP2 : (polarBilin (Q2.comp P2.subtype)).Nondegenerate)
    (hmap : P1.map J.toLinearEquiv.toLinearMap = P2)
    (D : Subgroup H)
    (hD : ((supportedDerived Q2 P2).subgroupOf (orthDerived Q2)).map
      e2.toMonoidHom = D) :
    ((supportedDerived Q1 P1).subgroupOf (orthDerived Q1)).map
      ((CFSG.RankThree.PartOne.orthDerivedEquiv J).trans e2).toMonoidHom = D := by
  change ((supportedDerived Q1 P1).subgroupOf (orthDerived Q1)).map
      (e2.toMonoidHom.comp (CFSG.RankThree.PartOne.orthDerivedEquiv J).toMonoidHom) = D
  rw [← Subgroup.map_map]
  have hP2' :
      (polarBilin (Q2.comp (P1.map J.toLinearEquiv.toLinearMap).subtype)).Nondegenerate := by
    rw [hmap]
    exact hP2
  rw [map_orthDerivedEquiv_supportedSubgroup J hP1 hP2', hmap, hD]

private theorem map_prod_bot_eq
    {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {A E B : Submodule K V}
    (J : (A × E) ≃ₗ[K] B)
    (hJ : ∀ (a : A) (e : E), (J (a, e) : V) = (a : V) + (e : V))
    (P : Submodule K A) :
    (P.prod (⊥ : Submodule K E)).map J.toLinearMap =
      (P.map A.subtype).comap B.subtype := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_comap]
    refine Submodule.mem_map.mpr ⟨y.1, hy.1, ?_⟩
    have hy2 : (y.2 : E) = 0 := by simpa using hy.2
    have hval : (J (y.1, y.2) : V) = (y.1 : V) := by
      rw [hJ]
      simp [hy2]
    simpa using hval.symm
  · intro hx
    rw [Submodule.mem_comap] at hx
    obtain ⟨p, hp, hpv⟩ := Submodule.mem_map.mp hx
    exact ⟨(p, 0), ⟨hp, Submodule.zero_mem _⟩,
      Subtype.ext (α := V) (p := fun v => v ∈ B) (a1 := J (p, (0 : E))) (a2 := x) (by
        calc (J (p, (0 : E)) : V) = (p : V) + (0 : V) := hJ p (0 : E)
          _ = (p : V) := by simp
          _ = (x : V) := hpv)⟩

private theorem map_prod_top_eq
    {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    {A E B : Submodule K V}
    (J : (A × E) ≃ₗ[K] B)
    (hJ : ∀ (a : A) (e : E), (J (a, e) : V) = (a : V) + (e : V))
    (P : Submodule K A) :
    (P.prod (⊤ : Submodule K E)).map J.toLinearMap =
      ((P.map A.subtype) ⊔ E).comap B.subtype := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Submodule.mem_comap]
    have hsum := Submodule.add_mem_sup
      (Submodule.mem_map_of_mem (f := A.subtype) hy.1) y.2.2
    simpa [hJ] using hsum
  · intro hx
    rw [Submodule.mem_comap] at hx
    obtain ⟨p, hp, e, he, hpe⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p0, hp0, hp0v⟩ := Submodule.mem_map.mp hp
    exact ⟨(p0, ⟨e, he⟩), ⟨hp0, trivial⟩,
      Subtype.ext (α := V) (p := fun v => v ∈ B) (a1 := J (p0, (⟨e, he⟩ : E))) (a2 := x) (by
        calc (J (p0, (⟨e, he⟩ : E)) : V) = (p0 : V) + (e : V) := hJ p0 ⟨e, he⟩
          _ = p + e := congrArg (fun z : V => z + (e : V)) hp0v
          _ = (x : V) := hpe)⟩

private theorem nondegenerate_polarBilin_prod_bot
    {K V E : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup E] [Module K E]
    {Q : QuadraticForm K V} {R : QuadraticForm K E} {P : Submodule K V}
    (hP : (polarBilin (Q.comp P.subtype)).Nondegenerate) :
    (polarBilin ((Q.prod R).comp (P.prod (⊥ : Submodule K E)).subtype)).Nondegenerate := by
  let e : ↥(P.prod (⊥ : Submodule K E)) ≃ₗ[K] (↥P × ↥(⊥ : Submodule K E)) :=
    Submodule.prodEquiv P ⊥
  have hiso : ((Q.prod R).comp (P.prod (⊥ : Submodule K E)).subtype).IsometryEquiv
      ((Q.comp P.subtype).prod (R.comp (⊥ : Submodule K E).subtype)) :=
    { toLinearEquiv := e, map_app' := fun _ => rfl }
  exact CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv hiso.symm
    (CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_prod hP
      (nondegenerate_polarBilin_of_forall fun v _ => Subsingleton.elim v 0))

private theorem nondegenerate_polarBilin_prod_top
    {K V E : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup E] [Module K E]
    {Q : QuadraticForm K V} {R : QuadraticForm K E} {P : Submodule K V}
    (hP : (polarBilin (Q.comp P.subtype)).Nondegenerate)
    (hR : (polarBilin R).Nondegenerate) :
    (polarBilin ((Q.prod R).comp (P.prod (⊤ : Submodule K E)).subtype)).Nondegenerate := by
  let e : ↥(P.prod (⊤ : Submodule K E)) ≃ₗ[K] (↥P × E) :=
    (Submodule.prodEquiv P ⊤).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl K ↥P) (Submodule.topEquiv (R := K) (M := E)))
  have hiso : ((Q.prod R).comp (P.prod (⊤ : Submodule K E)).subtype).IsometryEquiv
      ((Q.comp P.subtype).prod R) :=
    { toLinearEquiv := e, map_app' := fun _ => rfl }
  exact CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_of_isometryEquiv hiso.symm
    (CFSG.GroupTheory.WeirSylow.nondegenerate_polarBilin_prod hP hR)

private theorem map_supported_product_chart_images
    {K V CK : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Group CK]
    (Q : QuadraticForm K V) (A0 E B S0 S1 : Submodule K V)
    (J : ((Q.comp A0.subtype).prod (Q.comp E.subtype)).IsometryEquiv
      (Q.comp B.subtype))
    (hJ : ∀ (x : A0) (y : E), (J (x, y) : V) = (x : V) + (y : V))
    (sB : orthDerived (Q.comp B.subtype) ≃* CK)
    (P : Submodule K A0)
    (hPmap : P.map A0.subtype = S0)
    (hS1 : S1 = S0 ⊔ E)
    (hS0B : S0 ≤ B) (hS1B : S1 ≤ B)
    (hP : (polarBilin ((Q.comp A0.subtype).comp P.subtype)).Nondegenerate)
    (hE : (polarBilin (Q.comp E.subtype)).Nondegenerate)
    (hS0 : (polarBilin (Q.comp S0.subtype)).Nondegenerate)
    (hS1reg : (polarBilin (Q.comp S1.subtype)).Nondegenerate)
    (E0 E1 : Subgroup CK)
    (hE0 : ((supportedDerived (Q.comp B.subtype) (S0.comap B.subtype)).subgroupOf
      (orthDerived (Q.comp B.subtype))).map sB.toMonoidHom = E0)
    (hE1 : ((supportedDerived (Q.comp B.subtype) (S1.comap B.subtype)).subgroupOf
      (orthDerived (Q.comp B.subtype))).map sB.toMonoidHom = E1) :
    (((supportedDerived ((Q.comp A0.subtype).prod (Q.comp E.subtype))
        (P.prod (⊥ : Submodule K E))).subgroupOf
        (orthDerived ((Q.comp A0.subtype).prod (Q.comp E.subtype)))).map
        (((CFSG.RankThree.PartOne.orthDerivedEquiv J).trans sB).toMonoidHom) = E0) ∧
      (((supportedDerived ((Q.comp A0.subtype).prod (Q.comp E.subtype))
        ((P.prod (⊥ : Submodule K E)) ⊔
          ((⊥ : Submodule K A0).prod (⊤ : Submodule K E)))).subgroupOf
        (orthDerived ((Q.comp A0.subtype).prod (Q.comp E.subtype)))).map
        (((CFSG.RankThree.PartOne.orthDerivedEquiv J).trans sB).toMonoidHom) = E1) := by
  let Q0 : QuadraticForm K A0 := Q.comp A0.subtype
  let R : QuadraticForm K E := Q.comp E.subtype
  have hbot :
      ((supportedDerived (Q0.prod R) (P.prod (⊥ : Submodule K E))).subgroupOf
        (orthDerived (Q0.prod R))).map
        (((CFSG.RankThree.PartOne.orthDerivedEquiv J).trans sB).toMonoidHom) = E0 := by
    have hmapJ : (P.prod (⊥ : Submodule K E)).map J.toLinearEquiv.toLinearMap =
        S0.comap B.subtype := by
      rw [map_prod_bot_eq (A := A0) (E := E) (B := B) (J := J.toLinearEquiv) hJ,
        hPmap]
    have hreg1 : (polarBilin ((Q0.prod R).comp
        (P.prod (⊥ : Submodule K E)).subtype)).Nondegenerate :=
      nondegenerate_polarBilin_prod_bot (Q := Q0) (R := R) (P := P) hP
    have hreg2 : (polarBilin ((Q.comp B.subtype).comp
        (S0.comap B.subtype).subtype)).Nondegenerate :=
      nondegenerate_comap_of_le (Q := Q) (A := S0) (B := B) hS0B hS0
    exact map_supported_subgroup_through_isometry_chart J sB
      (P.prod (⊥ : Submodule K E)) (S0.comap B.subtype) hreg1 hreg2 hmapJ E0 hE0
  refine ⟨hbot, ?_⟩
  have hProdsup : (P.prod (⊥ : Submodule K E)) ⊔
      ((⊥ : Submodule K A0).prod (⊤ : Submodule K E)) =
      P.prod (⊤ : Submodule K E) := by
    rw [Submodule.prod_sup_prod]
    simp
  rw [hProdsup]
  have hmapJ : (P.prod (⊤ : Submodule K E)).map J.toLinearEquiv.toLinearMap =
      S1.comap B.subtype := by
    rw [map_prod_top_eq (A := A0) (E := E) (B := B) (J := J.toLinearEquiv) hJ,
      hPmap, ← hS1]
  have hreg1 : (polarBilin ((Q0.prod R).comp
      (P.prod (⊤ : Submodule K E)).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_prod_top (Q := Q0) (R := R) (P := P) hP hE
  have hreg2 : (polarBilin ((Q.comp B.subtype).comp
      (S1.comap B.subtype).subtype)).Nondegenerate :=
    nondegenerate_comap_of_le (Q := Q) (A := S1) (B := B) hS1B hS1reg
  exact map_supported_subgroup_through_isometry_chart J sB
    (P.prod (⊤ : Submodule K E)) (S1.comap B.subtype) hreg1 hreg2 hmapJ E1 hE1

private theorem map_conj_mulAut_normalizes
    {A B : Type} [Group A] [Group B] (e : A ≃* B) (b0 : MulAut A) :
    ∀ H : Subgroup A, H.map b0.toMonoidHom = H →
      (H.map e.toMonoidHom).map ((e.symm.trans b0).trans e).toMonoidHom =
        H.map e.toMonoidHom := by
  intro H hH
  have hcomp : ((e.symm.trans b0).trans e).toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp b0.toMonoidHom := by
    ext x
    simp [MulEquiv.trans_apply]
  calc
    (H.map e.toMonoidHom).map ((e.symm.trans b0).trans e).toMonoidHom
        = H.map (((e.symm.trans b0).trans e).toMonoidHom.comp e.toMonoidHom) :=
          Subgroup.map_map H ((e.symm.trans b0).trans e).toMonoidHom e.toMonoidHom
    _ = H.map (e.toMonoidHom.comp b0.toMonoidHom) := by rw [hcomp]
    _ = (H.map b0.toMonoidHom).map e.toMonoidHom :=
          (Subgroup.map_map H e.toMonoidHom b0.toMonoidHom).symm
    _ = H.map e.toMonoidHom := by rw [hH]

private theorem hmark_prod_of_subgroups
    {G G0 C0 CD0 CDu GP : Type} [Group G] [Group G0] [Group C0] [Group CD0]
    [Group CDu] [Group GP]
    (a : CD0 →* G) (k : CDu →* G)
    (eO : G0 ≃* C0) (eK : GP ≃* CDu) (incl : G0 →* GP)
    (iOL : C0 →* CD0) (iOK : C0 →* CDu)
    (H : Subgroup G0) (CS : Subgroup C0) (C0D : Subgroup CD0) (C0u : Subgroup CDu)
    (hEO : H.map eO.toMonoidHom = CS)
    (hLmap : CS.map iOL = C0D) (hRmap : CS.map iOK = C0u)
    (hSmark : C0D.map a = C0u.map k)
    (hsquare : eK.toMonoidHom.comp incl = iOK.comp eO.toMonoidHom) :
    H.map (a.comp (iOL.comp eO.toMonoidHom)) =
      H.map ((k.comp eK.toMonoidHom).comp incl) := by
  have hL : H.map (a.comp (iOL.comp eO.toMonoidHom)) = C0D.map a := by
    calc H.map (a.comp (iOL.comp eO.toMonoidHom))
        = (H.map (iOL.comp eO.toMonoidHom)).map a := by simp only [Subgroup.map_map]
      _ = ((H.map eO.toMonoidHom).map iOL).map a := by simp only [Subgroup.map_map]
      _ = (CS.map iOL).map a := by rw [hEO]
      _ = C0D.map a := by rw [hLmap]
  have hR : H.map ((k.comp eK.toMonoidHom).comp incl) = C0u.map k := by
    have hkc : (k.comp eK.toMonoidHom).comp incl =
        k.comp (iOK.comp eO.toMonoidHom) := by
      rw [MonoidHom.comp_assoc, hsquare, ← MonoidHom.comp_assoc]
    calc H.map ((k.comp eK.toMonoidHom).comp incl)
        = H.map (k.comp (iOK.comp eO.toMonoidHom)) := by rw [hkc]
      _ = (H.map (iOK.comp eO.toMonoidHom)).map k := by simp only [Subgroup.map_map]
      _ = ((H.map eO.toMonoidHom).map iOK).map k := by simp only [Subgroup.map_map]
      _ = (CS.map iOK).map k := by rw [hEO]
      _ = C0u.map k := by rw [hRmap]
  exact hL.trans (hSmark.trans hR.symm)

private theorem map_marked_supports_through_product_chart
    {X G P0 P CK : Type} [Group X] [Group G] [Group P0] [Group P] [Group CK]
    {Idx : Type} [DecidableEq Idx] {m : ℕ}
    (CS : Finset Idx → Subgroup X) (hC : Monotone CS)
    (Ovr DL Dun : Finset Idx) (hOL : Ovr ⊆ DL) (hOK : Ovr ⊆ Dun)
    (a : CS DL →* G) (k : CS Dun →* G)
    (eO : P0 ≃* CS Ovr) (eK : P ≃* CS Dun) (incl : P0 →* P)
    (hsquare : eK.toMonoidHom.comp incl =
      (Subgroup.inclusion (hC hOK)).comp eO.toMonoidHom)
    (iota : Fin m → Idx) (hiotaO : ∀ j, iota j ∈ Ovr)
    (H : Finset (Fin m) → Subgroup P0)
    (hEO : ∀ T : Finset (Fin m), (H T).map eO.toMonoidHom =
      (CS (T.image iota)).subgroupOf (CS Ovr))
    (hmark : ∀ S : Finset Idx, S.Nonempty → S.card ≤ 2 → S ⊆ Ovr →
      ((CS S).subgroupOf (CS DL)).map a = ((CS S).subgroupOf (CS Dun)).map k) :
    ∀ T : Finset (Fin m), T.Nonempty → T.card ≤ 2 →
      (H T).map (a.comp ((Subgroup.inclusion (hC hOL)).comp eO.toMonoidHom)) =
        (H T).map ((k.comp eK.toMonoidHom).comp incl) := by
  intro T hTne hTcard
  let S : Finset Idx := T.image iota
  have hSsubO : S ⊆ Ovr := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact hiotaO j
  have hSne : S.Nonempty := hTne.image iota
  have hScard : S.card ≤ 2 := by
    dsimp [S]
    exact (Finset.card_image_le (s := T) (f := iota)).trans hTcard
  have hSmark := hmark S hSne hScard hSsubO
  have hLmap : ((CS S).subgroupOf (CS Ovr)).map
      (Subgroup.inclusion (hC hOL)) = (CS S).subgroupOf (CS DL) := by
    rw [← Subgroup.comap_inclusion_subgroupOf (K₁ := CS Ovr) (K₂ := CS DL)
      (H := CS S) (hC hOL)]
    exact Subgroup.map_comap_eq_self (by
      rw [Subgroup.inclusion_range]
      exact Subgroup.subgroupOf_mono (CS DL) (hC hSsubO))
  have hRmap : ((CS S).subgroupOf (CS Ovr)).map
      (Subgroup.inclusion (hC hOK)) = (CS S).subgroupOf (CS Dun) := by
    rw [← Subgroup.comap_inclusion_subgroupOf (K₁ := CS Ovr) (K₂ := CS Dun)
      (H := CS S) (hC hOK)]
    exact Subgroup.map_comap_eq_self (by
      rw [Subgroup.inclusion_range]
      exact Subgroup.subgroupOf_mono (CS Dun) (hC hSsubO))
  exact hmark_prod_of_subgroups a k eO eK incl
    (Subgroup.inclusion (hC hOL)) (Subgroup.inclusion (hC hOK))
    (H T) ((CS S).subgroupOf (CS Ovr)) ((CS S).subgroupOf (CS DL))
    ((CS S).subgroupOf (CS Dun)) (hEO T) hLmap hRmap hSmark hsquare

private theorem calibrate_through_product_chart
    {G P0 P C0 CL CK Idx : Type}
    [Group G] [Group P0] [Group P] [Group C0] [Group CL] [Group CK]
    [DecidableEq Idx] {m : ℕ}
    (a : CL →* G) (k : CK →* G) (hk : Function.Injective k)
    (eO : P0 ≃* C0) (eK : P ≃* CK) (incl : P0 →* P)
    (iOL : C0 →* CL) (iOK : C0 →* CK)
    (hsquare : eK.toMonoidHom.comp incl = iOK.comp eO.toMonoidHom)
    (beta0 : MulAut P)
    (hagree : ((k.comp eK.toMonoidHom).comp beta0.toMonoidHom).comp incl =
      a.comp (iOL.comp eO.toMonoidHom))
    (d : Idx) (Ovr Dun : Finset Idx) (hDu : Dun = insert d Ovr)
    (iota : Fin m → Idx) (hiota : Finset.univ.image iota = Ovr)
    (Hbot Htop : Finset (Fin m) → Subgroup P)
    (Supp : Finset Idx → Subgroup CK)
    (hbot : ∀ T, (Hbot T).map eK.toMonoidHom = Supp (T.image iota))
    (htop : ∀ T, (Htop T).map eK.toMonoidHom = Supp (insert d (T.image iota)))
    (hnorm : ∀ T,
      (Hbot T).map beta0.toMonoidHom = Hbot T ∧
      (Htop T).map beta0.toMonoidHom = Htop T) :
    ∃ beta : MulAut CK,
      (k.comp beta.toMonoidHom).comp iOK = a.comp iOL ∧
      Function.Injective (k.comp beta.toMonoidHom) ∧
      (k.comp beta.toMonoidHom).range = k.range ∧
      ∀ S : Finset Idx, S ⊆ Dun → (Supp S).map beta.toMonoidHom = Supp S := by
  let beta : MulAut CK := eK.symm.trans (beta0.trans eK)
  have hbeta_eK : ∀ y : P, beta (eK y) = eK (beta0 y) := by
    intro y
    simp [beta]
  have hbeta_apply : ∀ y : P, k (beta (eK y)) = k (eK (beta0 y)) :=
    fun y => congrArg k (hbeta_eK y)
  have hagree' : (k.comp beta.toMonoidHom).comp iOK = a.comp iOL := by
    ext x
    obtain ⟨g, rfl⟩ := eO.surjective x
    have hsq : eK (incl g) = iOK (eO g) := by
      change (eK.toMonoidHom.comp incl) g = (iOK.comp eO.toMonoidHom) g
      exact DFunLike.congr_fun hsquare g
    change k (beta (iOK (eO g))) = a (iOL (eO g))
    rw [← hsq, hbeta_apply (incl g)]
    have h := DFunLike.congr_fun hagree g
    simpa [MonoidHom.comp_apply] using h
  have hinj : Function.Injective (k.comp beta.toMonoidHom) := hk.comp beta.injective
  have hrange : (k.comp beta.toMonoidHom).range = k.range := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective beta.toMonoidHom beta.surjective,
      Subgroup.map_top]
  refine ⟨beta, hagree', hinj, hrange, ?_⟩
  intro S hSDu
  let T : Finset (Fin m) := Finset.univ.filter (fun i => iota i ∈ S.erase d)
  have hSdO : S.erase d ⊆ Ovr := by
    intro x hx
    rw [Finset.mem_erase] at hx
    have hxS : x ∈ S := hx.2
    have hxd : x ≠ d := hx.1
    have hxDu : x ∈ Dun := hSDu hxS
    rw [hDu, Finset.mem_insert] at hxDu
    rcases hxDu with hxd' | hxO
    · exact absurd hxd' hxd
    · exact hxO
  have hT : T.image iota = S.erase d := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at hi
      subst x
      exact hi.2
    · intro hx
      have hxO : x ∈ Ovr := hSdO hx
      have hxim : x ∈ Finset.univ.image iota := by
        rw [hiota]
        exact hxO
      obtain ⟨i, -, hix⟩ := Finset.mem_image.mp hxim
      refine Finset.mem_image.mpr ⟨i, ?_, hix⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ i, by rw [hix]; exact hx⟩
  by_cases hdS : d ∈ S
  · have hS : S = insert d (T.image iota) := by
      rw [hT, Finset.insert_erase hdS]
    have hSupp : Supp S = (Htop T).map eK.toMonoidHom := by
      rw [hS, ← htop T]
    rw [hSupp]
    exact map_conj_mulAut_normalizes eK beta0 (Htop T) ((hnorm T).2)
  · have hS : S = T.image iota := by
      rw [hT, Finset.erase_eq_self.mpr hdS]
    have hSupp : Supp S = (Hbot T).map eK.toMonoidHom := by
      rw [hS, ← hbot T]
    rw [hSupp]
    exact map_conj_mulAut_normalizes eK beta0 (Hbot T) ((hnorm T).1)

private theorem comapped_orthogonal_family_geometry
    {K V Idx : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq Idx] {m : ℕ}
    (Q : QuadraticForm K V)
    (A0 W0 : Submodule K V) (U0 : Idx → Submodule K V)
    (iota : Fin m → Idx)
    (hWA : W0 ≤ A0) (hUA : ∀ j, U0 (iota j) ≤ A0)
    (hWreg : (polarBilin (Q.comp W0.subtype)).Nondegenerate)
    (hUreg : ∀ j,
      (polarBilin (Q.comp (U0 (iota j)).subtype)).Nondegenerate)
    (hWdim : finrank K W0 = 2)
    (hUdim : ∀ j, finrank K (U0 (iota j)) = 2)
    (hWU : ∀ j, ∀ w ∈ W0, ∀ u ∈ U0 (iota j), polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U0 (iota i),
      ∀ v ∈ U0 (iota j), polar Q u v = 0)
    (hspan0 : W0 ⊔ (⨆ j : Fin m, U0 (iota j)) = A0) :
    let W := W0.comap A0.subtype
    let U := fun j : Fin m => (U0 (iota j)).comap A0.subtype
    (polarBilin ((Q.comp A0.subtype).comp W.subtype)).Nondegenerate ∧
    finrank K W = 2 ∧
    (∀ j, (polarBilin ((Q.comp A0.subtype).comp (U j).subtype)).Nondegenerate) ∧
    (∀ j, finrank K (U j) = 2) ∧
    (∀ j, ∀ w ∈ W, ∀ u ∈ U j, polar (Q.comp A0.subtype) w u = 0) ∧
    (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j,
      polar (Q.comp A0.subtype) u v = 0) ∧
    (∀ T : Finset (Fin m), W ⊔ T.sup U =
      (W0 ⊔ (T.image iota).sup U0).comap A0.subtype) ∧
    W ⊔ (⨆ j : Fin m, U j) = ⊤ := by
  dsimp only
  have hT : ∀ T : Finset (Fin m),
      (W0.comap A0.subtype) ⊔
          T.sup (fun j : Fin m => (U0 (iota j)).comap A0.subtype) =
        (W0 ⊔ (T.image iota).sup U0).comap A0.subtype := by
    intro T
    apply Submodule.map_injective_of_injective (f := A0.subtype) A0.subtype_injective
    rw [Submodule.map_sup]
    have hWmap : (W0.comap A0.subtype).map A0.subtype = W0 := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hWA]
    have hUmap : ∀ j : Fin m,
        ((U0 (iota j)).comap A0.subtype).map A0.subtype = U0 (iota j) := by
      intro j
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr (hUA j)]
    have hTU : (T.sup (fun j : Fin m =>
        (U0 (iota j)).comap A0.subtype)).map A0.subtype =
        T.sup (fun j => U0 (iota j)) := by
      induction T using Finset.induction with
      | empty => simp
      | insert j T hj ih =>
          rw [Finset.sup_insert, Submodule.map_sup, ih, Finset.sup_insert, hUmap j]
    have hsup : (T.image iota).sup U0 = T.sup (fun j => U0 (iota j)) := by
      rw [Finset.sup_image]
      rfl
    rw [hWmap, hTU, ← hsup]
    have hAleT : W0 ⊔ (T.image iota).sup U0 ≤ A0 := by
      rw [hsup]
      exact sup_le hWA (Finset.sup_le fun j _ => hUA j)
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hAleT]
  refine ⟨nondegenerate_comap_of_le (Q := Q) hWA hWreg, ?_, ?_, ?_, ?_, ?_, hT, ?_⟩
  · exact (Submodule.comapSubtypeEquivOfLe hWA).finrank_eq.trans hWdim
  · intro j
    exact nondegenerate_comap_of_le (Q := Q) (hUA j) (hUreg j)
  · intro j
    exact (Submodule.comapSubtypeEquivOfLe (hUA j)).finrank_eq.trans (hUdim j)
  · intro j w hw u hu
    rw [polar_comp_subtype_eq]
    exact hWU j (w : V) (show (w : V) ∈ W0 from hw) (u : V)
      (show (u : V) ∈ U0 (iota j) from hu)
  · intro i j hij u hu v hv
    rw [polar_comp_subtype_eq]
    exact hUU i j hij (u : V) (show (u : V) ∈ U0 (iota i) from hu) (v : V)
      (show (v : V) ∈ U0 (iota j) from hv)
  · have h := hT Finset.univ
    have hleft : Finset.univ.sup (fun j : Fin m =>
        (U0 (iota j)).comap A0.subtype) =
        ⨆ j : Fin m, (U0 (iota j)).comap A0.subtype := by
      rw [Finset.sup_eq_iSup]
      simp
    rw [hleft] at h
    have huniv : (Finset.univ.image iota).sup U0 = ⨆ j : Fin m, U0 (iota j) := by
      rw [Finset.sup_image, Finset.sup_eq_iSup]
      simp
    rw [huniv, hspan0, Submodule.comap_subtype_self] at h
    exact h

private theorem exists_calibrated_mapped_prod_chart_of_marked_supports
    {F V E G X Idx : Type}
    [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup E] [Module F E] [FiniteDimensional F E]
    [Group G] [Group X] [DecidableEq Idx]
    {m : ℕ}
    (Q : QuadraticForm F V) (W : Submodule F V)
    (U : Fin m → Submodule F V) (hm : 2 ≤ m) (hF : 2 < Nat.card F)
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hWdim : finrank F W = 2)
    (hU : ∀ i, (polarBilin (Q.comp (U i).subtype)).Nondegenerate)
    (hUdim : ∀ i, finrank F (U i) = 2)
    (hWU : ∀ i, ∀ w ∈ W, ∀ u ∈ U i, polar Q w u = 0)
    (hUU : ∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, polar Q u v = 0)
    (hspan : W ⊔ (⨆ i, U i) = ⊤)
    (htype : ∀ i, IsPlusType (Q.comp (U i).subtype) ↔
      ¬ IsPlusType (Q.comp W.subtype))
    (R : QuadraticForm F E) (o : Fin m)
    (j : R.IsometryEquiv (Q.comp (U o).subtype))
    (CS : Finset Idx → Subgroup X) (hC : Monotone CS)
    (d : Idx) (Ovr DL Dun : Finset Idx)
    (hOL : Ovr ⊆ DL) (hOK : Ovr ⊆ Dun) (hDu : Dun = insert d Ovr)
    (iota : Fin m → Idx) (hiota : Finset.univ.image iota = Ovr)
    (a : CS DL →* G) (k : CS Dun →* G)
    (ha : Function.Injective a) (hk : Function.Injective k)
    (eO : orthDerived Q ≃* CS Ovr) (eK : orthDerived (Q.prod R) ≃* CS Dun)
    (hsquare : eK.toMonoidHom.comp (orthDerivedProdIncl (Q := Q) (R := R)) =
      (Subgroup.inclusion (hC hOK)).comp eO.toMonoidHom)
    (hEO : ∀ T : Finset (Fin m),
      ((supportedDerived Q (W ⊔ T.sup U)).subgroupOf (orthDerived Q)).map
        eO.toMonoidHom = (CS (T.image iota)).subgroupOf (CS Ovr))
    (hbot : ∀ T : Finset (Fin m),
      ((supportedDerived (Q.prod R) ((W ⊔ T.sup U).prod (⊥ : Submodule F E))).subgroupOf
        (orthDerived (Q.prod R))).map eK.toMonoidHom =
        (CS (T.image iota)).subgroupOf (CS Dun))
    (htop : ∀ T : Finset (Fin m),
      ((supportedDerived (Q.prod R)
        (((W ⊔ T.sup U).prod (⊥ : Submodule F E)) ⊔
          ((⊥ : Submodule F V).prod (⊤ : Submodule F E)))).subgroupOf
        (orthDerived (Q.prod R))).map eK.toMonoidHom =
        (CS (insert d (T.image iota))).subgroupOf (CS Dun))
    (hmark : ∀ S : Finset Idx, S.Nonempty → S.card ≤ 2 → S ⊆ Ovr →
      ((CS S).subgroupOf (CS DL)).map a =
        ((CS S).subgroupOf (CS Dun)).map k) :
    ∃ beta : MulAut (CS Dun),
      (k.comp beta.toMonoidHom).comp (Subgroup.inclusion (hC hOK)) =
        a.comp (Subgroup.inclusion (hC hOL)) ∧
      Function.Injective (k.comp beta.toMonoidHom) ∧
      (k.comp beta.toMonoidHom).range = k.range ∧
      ∀ S : Finset Idx, S ⊆ Dun →
        ((CS S).subgroupOf (CS Dun)).map beta.toMonoidHom =
          (CS S).subgroupOf (CS Dun) := by
  classical
  let incl : orthDerived Q →* orthDerived (Q.prod R) :=
    orthDerivedProdIncl (Q := Q) (R := R)
  let iOL : CS Ovr →* CS DL := Subgroup.inclusion (hC hOL)
  let iOK : CS Ovr →* CS Dun := Subgroup.inclusion (hC hOK)
  have hiotaO : ∀ j : Fin m, iota j ∈ Ovr := by
    intro j
    rw [← hiota]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩
  let a0 : orthDerived Q →* G := a.comp (iOL.comp eO.toMonoidHom)
  let k0 : orthDerived (Q.prod R) →* G := k.comp eK.toMonoidHom
  have hmarkProd : ∀ T : Finset (Fin m), T.Nonempty → T.card ≤ 2 →
      ((supportedDerived Q (W ⊔ T.sup U)).subgroupOf (orthDerived Q)).map a0 =
        ((supportedDerived Q (W ⊔ T.sup U)).subgroupOf (orthDerived Q)).map
          (k0.comp incl) := by
    intro T hTne hTcard
    exact map_marked_supports_through_product_chart
      (X := X) (Idx := Idx) (G := G)
      (P0 := orthDerived Q) (P := orthDerived (Q.prod R)) (CK := CS Dun)
      (CS := CS) (hC := hC)
      (Ovr := Ovr) (DL := DL) (Dun := Dun)
      hOL hOK (a := a) (k := k) (eO := eO) (eK := eK) (incl := incl)
      (hsquare := hsquare) (iota := iota) (hiotaO := hiotaO)
      (H := fun T => ((supportedDerived Q (W ⊔ T.sup U)).subgroupOf (orthDerived Q)))
      (hEO := hEO) (hmark := hmark) T hTne hTcard
  have hiOe : Function.Injective (iOL.comp eO.toMonoidHom) := by
    intro x y hxy
    exact eO.injective (Subgroup.inclusion_injective (hC hOL) hxy)
  have ha0 : Function.Injective a0 := by
    intro x y hxy
    exact hiOe (ha hxy)
  have hk0 : Function.Injective k0 := by
    intro x y hxy
    exact eK.injective (hk hxy)
  obtain ⟨beta0, hbeta0_incl, hbeta0_inj, hbeta0_range, hbeta0_norm⟩ :=
    exists_calibrated_prod_chart_of_marked_supports
      (F := F) (V := V) (E := E) (G := G)
      (Q := Q) (W := W) (U := U) (hm := hm) (hF := hF)
      (hW := hW) (hWdim := hWdim) (hU := hU) (hUdim := hUdim)
      (hWU := hWU) (hUU := hUU) (hspan := hspan) (htype := htype)
      (R := R) (o := o) (j := j) (a := a0) (k := k0)
      (ha := ha0) (hk := hk0) (hmark := hmarkProd)
  let Supp : Finset Idx → Subgroup (CS Dun) := fun S => (CS S).subgroupOf (CS Dun)
  let Hbot : Finset (Fin m) → Subgroup (orthDerived (Q.prod R)) :=
    fun T => ((supportedDerived (Q.prod R)
      ((W ⊔ T.sup U).prod (⊥ : Submodule F E))).subgroupOf
      (orthDerived (Q.prod R)))
  let Htop : Finset (Fin m) → Subgroup (orthDerived (Q.prod R)) :=
    fun T => ((supportedDerived (Q.prod R)
      (((W ⊔ T.sup U).prod (⊥ : Submodule F E)) ⊔
        ((⊥ : Submodule F V).prod (⊤ : Submodule F E)))).subgroupOf
      (orthDerived (Q.prod R)))
  have hbeta0_agree :
      ((k.comp eK.toMonoidHom).comp beta0.toMonoidHom).comp incl =
        a.comp (iOL.comp eO.toMonoidHom) := by
    simpa [a0, k0] using hbeta0_incl
  obtain ⟨beta, hbeta_agree, hbeta_inj, hbeta_range, hbeta_supp⟩ :=
    calibrate_through_product_chart (a := a) (k := k) (hk := hk)
      (eO := eO) (eK := eK) (incl := incl) (iOL := iOL) (iOK := iOK)
      (hsquare := hsquare) (beta0 := beta0) (hagree := hbeta0_agree)
      (d := d) (Ovr := Ovr) (Dun := Dun) (hDu := hDu)
      (iota := iota) (hiota := hiota)
      (Hbot := Hbot) (Htop := Htop) (Supp := Supp)
      (hbot := hbot) (htop := htop) (hnorm := hbeta0_norm)
  exact ⟨beta, hbeta_agree, hbeta_inj, hbeta_range, hbeta_supp⟩

theorem exists_calibrated_deletion_chart_of_marked_supports_of_three_le
    (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F) (h0u : (0 : I) ≠ u)
    (a : C D0 →* G) (k : C Du →* G)
    (ha : Function.Injective a) (hk : Function.Injective k)
    (hmark : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ O →
      ((C S).subgroupOf (C D0)).map a =
        ((C S).subgroupOf (C Du)).map k) :
    ∃ beta : MulAut (C Du),
      (k.comp beta.toMonoidHom).comp
          (Subgroup.inclusion (chartSubgroup_mono hirr
            (show O ⊆ Du from Finset.inter_subset_right))) =
        a.comp
          (Subgroup.inclusion (chartSubgroup_mono hirr
            (show O ⊆ D0 from Finset.inter_subset_left))) ∧
      Function.Injective (k.comp beta.toMonoidHom) ∧
      (k.comp beta.toMonoidHom).range = k.range ∧
      (∀ S : Finset I, S ⊆ Du →
        ((C S).subgroupOf (C Du)).map beta.toMonoidHom =
          (C S).subgroupOf (C Du)) := by
  classical
  have h0notD0 : (0 : I) ∉ D0 := by simp [deletionPlanes]
  have h0Du : (0 : I) ∈ Du := by simp [h0u]
  have huD0 : u ∈ D0 := by simp [deletionPlanes, Ne.symm h0u]
  have h0notO : (0 : I) ∉ D0 ∩ Du := by simp [deletionPlanes, h0u]
  have huO : u ∉ D0 ∩ Du := by simp [deletionPlanes, Ne.symm h0u]
  have hOeq : (D0 ∩ Du) = (Finset.univ.erase u).erase 0 := by
    ext x
    simp only [deletionPlanes, Finset.mem_inter, Finset.mem_erase, Finset.mem_univ,
      true_and]
    tauto
  have hDu_eq : Du = insert 0 (D0 ∩ Du) := by
    rw [hOeq, Finset.insert_erase h0Du]
  have hOcard : (D0 ∩ Du).card = r - 1 := by
    rw [hOeq, Finset.card_erase_of_mem h0Du]
    simp
  let m : ℕ := (D0 ∩ Du).card
  have hm : 2 ≤ m := by
    dsimp [m]
    omega
  let enumO : Fin m ≃ ↥(D0 ∩ Du) := (Finset.equivFin (D0 ∩ Du)).symm
  let iota : Fin m → I := fun j => (enumO j : I)
  have hiota_inj : Function.Injective iota := by
    intro j k hjk
    exact enumO.injective (Subtype.ext hjk)
  have hiota_mem : ∀ j : Fin m, iota j ∈ D0 ∩ Du := fun j => (enumO j).2
  have hiota_image : Finset.univ.image iota = D0 ∩ Du := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, rfl⟩
      exact hiota_mem j
    · intro hx
      obtain ⟨j, hj⟩ := enumO.surjective ⟨x, hx⟩
      exact ⟨j, congrArg Subtype.val hj⟩
  let ψ := minusPlaneCoordinates (n := r + 2) (F := F)
  let A : Finset I → Submodule F (Vm (r + 2) F) :=
    fun S => anchoredSupport F (r + 2) S
  have hA_coord : ∀ S : Finset I, A S = coordSupport ψ S := fun S =>
    (coordSupport_minusPlaneCoordinates_eq_anchoredSupport
      (n := r + 2) (F := F) S).symm
  let Q := quadMinus (r + 2) F b c
  have hψ : ∀ v : Vm (r + 2) F,
      Q v = binaryForm F b c (ψ v).1 + ∑ i, hypPlane F ((ψ v).2 i) :=
    fun v => quadMinus_eq_binaryForm_add_minusPlaneCoordinates (r := r) (F := F) v
  have hQ : (polarBilin Q).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite (r + 2) F hirr
  have hQE : (polarBilin (hypPlane F)).Nondegenerate :=
    hypPlane_polarBilin_nondegenerate
  let W0 : Submodule F (Vm (r + 2) F) := coordAnchor ψ
  let U0 : I → Submodule F (Vm (r + 2) F) := fun i => coordPlane ψ i
  let E : Submodule F (Vm (r + 2) F) := U0 0
  let A0 : Submodule F (Vm (r + 2) F) := A O
  let AK : Submodule F (Vm (r + 2) F) := A Du
  have hA0reg : (polarBilin (Q.comp A0.subtype)).Nondegenerate := by
    refine K159.nondegenerate_of_regOn (Q := quadMinus (r + 2) F b c)
      (U := anchoredSupport F (r + 2) O) ?_
    exact polarNondegOn_anchoredSupport (n := r + 2) (F := F) (b := b) (c := c) hirr O
  have hAKreg : (polarBilin (Q.comp AK.subtype)).Nondegenerate := by
    refine K159.nondegenerate_of_regOn (Q := quadMinus (r + 2) F b c)
      (U := anchoredSupport F (r + 2) Du) ?_
    exact polarNondegOn_anchoredSupport (n := r + 2) (F := F) (b := b) (c := c) hirr Du
  have hW0reg : (polarBilin (Q.comp W0.subtype)).Nondegenerate :=
    coordAnchor_nondegenerate ψ hψ hQ hQE
  have hU0reg : ∀ i : I, (polarBilin (Q.comp (U0 i).subtype)).Nondegenerate := by
    intro i
    refine K159.nondegenerate_of_regOn (Q := quadMinus (r + 2) F b c)
      (U := coordPlane ψ i) ?_
    exact coordPlane_polarNondegOn ψ hψ hQE i
  have hAreg : ∀ S : Finset I,
      (polarBilin (Q.comp (A S).subtype)).Nondegenerate := by
    intro S
    exact K159.nondegenerate_of_regOn (Q := Q) (U := A S)
      (fun x hx h =>
        polarNondegOn_anchoredSupport (n := r + 2) (F := F) (b := b) (c := c) hirr S x hx h)
  have hAle : ∀ S : Finset I, supportedDerived Q (A S) ≤ orthDerived Q :=
    fun S => supportedDerived_le_orthDerived_of_regular (hAreg S)
  have hW0_le_A0 : W0 ≤ A0 := by
    rw [show A0 = coordSupport ψ O from hA_coord O]
    exact le_sup_left
  have hU0_le_A0 : ∀ i : I, i ∈ O → U0 i ≤ A0 := by
    intro i hi
    rw [show A0 = coordSupport ψ O from hA_coord O]
    exact le_trans (Finset.le_sup (s := O) (f := fun i => coordPlane ψ i) hi)
      le_sup_right
  have hAK_eq : AK = A0 ⊔ E := by
    rw [show AK = coordSupport ψ Du from hA_coord Du, hDu_eq,
      coordSupport_insert ψ h0notO, show coordSupport ψ O = A0 from (hA_coord O).symm]
  have hA0_le_AK : A0 ≤ AK := by rw [hAK_eq]; exact le_sup_left
  have hE_le_AK : E ≤ AK := by rw [hAK_eq]; exact le_sup_right
  have hEperp : E ≤ suppPerp Q A0 := by
    intro e he
    rw [mem_suppPerp]
    intro a ha
    have ha' : a ∈ coordSupport ψ O := by
      rwa [show A0 = coordSupport ψ O from hA_coord O] at ha
    exact polar_coordSupport_plane ψ hψ O h0notO ha' he
  have hcomplA0 : IsCompl A0 (suppPerp Q A0) :=
    isCompl_suppPerp (polarNondegOn_of_nondegenerate hA0reg)
  have hdisj : Disjoint A0 E := hcomplA0.disjoint.mono_right hEperp
  have horth : ∀ a ∈ A0, ∀ e ∈ E, polar Q a e = 0 := fun a ha e he =>
    mem_suppPerp.mp (hEperp he) a ha
  have hsum : A0 ⊔ E = AK := hAK_eq.symm
  have hW0dim : finrank F W0 = 2 := by
    have hinj : Function.Injective
        (ψ.symm.toLinearMap.comp
          (LinearMap.inl F (Fin 2 → F) (Fin (r + 1) → F × F))) :=
      ψ.symm.injective.comp LinearMap.inl_injective
    have hdim : finrank F W0 = finrank F (Fin 2 → F) := by
      dsimp [W0, coordAnchor]
      exact LinearMap.finrank_range_of_inj hinj
    rw [hdim, Module.finrank_fintype_fun_eq_card]
    simp
  have hU0dim : ∀ i : I, finrank F (U0 i) = 2 := by
    intro i
    calc
      finrank F (U0 i) = finrank F (F × F) :=
        (coordPlaneIsometry ψ hψ i).toLinearEquiv.finrank_eq.symm
      _ = 2 := by rw [Module.finrank_prod]; simp
  let W : Submodule F A0 := W0.comap A0.subtype
  let U : Fin m → Submodule F A0 := fun j => (U0 (iota j)).comap A0.subtype
  have hspan0 : W0 ⊔ (⨆ j : Fin m, U0 (iota j)) = A0 := by
    have hsup : (Finset.univ.image iota).sup U0 =
        ⨆ j : Fin m, U0 (iota j) := by
      rw [Finset.sup_image, Finset.sup_eq_iSup]
      simp
    rw [← hsup, hiota_image, show A0 = coordSupport ψ O from hA_coord O]
    dsimp [W0, U0, coordSupport]
  have hAcoord : ∀ S : Finset I, W0 ⊔ S.sup U0 = A S := by
    intro S
    rw [hA_coord S]
    dsimp [W0, U0, coordSupport]
  obtain ⟨hWreg, hWdim, hUreg, hUdim, hWU, hUU, hP_eq_raw, hspan⟩ :=
    comapped_orthogonal_family_geometry (Q := Q) (A0 := A0) (W0 := W0) (U0 := U0)
      (iota := iota) hW0_le_A0
      (fun j => hU0_le_A0 (iota j) (hiota_mem j)) hW0reg
      (fun j => hU0reg (iota j)) hW0dim (fun j => hU0dim (iota j))
      (fun j w hw u hu => polar_coordAnchor_plane ψ hψ hw hu)
      (fun i j hij u hu v hv =>
        polar_coordPlane_plane ψ hψ (fun h => hij (hiota_inj h)) hu hv)
      hspan0

  have hTsubO : ∀ T : Finset (Fin m), T.image iota ⊆ O := by
    intro T x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact hiota_mem j
  have hTsubDu : ∀ T : Finset (Fin m), T.image iota ⊆ Du := fun T =>
    (hTsubO T).trans Finset.inter_subset_right
  have hAleT : ∀ T : Finset (Fin m), A (T.image iota) ≤ A0 := by
    intro T
    dsimp [A0, A]
    exact anchoredSupport_mono (hTsubO T)
  have hPreg : ∀ T : Finset (Fin m),
      PolarNondegOn (Q.comp A0.subtype) (W ⊔ T.sup U) := by
    intro T
    have hTUreg : PolarNondegOn (Q.comp A0.subtype) (T.sup U) :=
      polarNondegOn_finset_sup U (fun j => polarNondegOn_of_nondegenerate (hUreg j))
        (fun i j hij => hUU i j hij) T
    refine CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
      (polarNondegOn_of_nondegenerate hWreg) hTUreg ?_
    intro w hw u hu
    have hle : T.sup U ≤ suppPerp (Q.comp A0.subtype) W := by
      refine Finset.sup_le fun j _ => ?_
      intro x hx
      rw [mem_suppPerp]
      intro y hy
      exact hWU j y hy x hx
    exact mem_suppPerp.mp (hle hu) w hw
  have hPnd := fun (T : Finset (Fin m)) =>
    K159.nondegenerate_of_regOn (Q := Q.comp A0.subtype) (U := W ⊔ T.sup U)
      (fun x hx h => hPreg T x hx h)

  have hP_eq : ∀ T : Finset (Fin m),
      W ⊔ T.sup U = (A (T.image iota)).comap A0.subtype := by
    intro T
    rw [hP_eq_raw T, hAcoord (T.image iota)]

  obtain ⟨hWaniso, hWnotplus0⟩ :=
    coordAnchor_anisotropic_and_notPlus (r := r) (F := F) (b := b) (c := c)
      hirr ψ hψ hW0dim
  let Q0 : QuadraticForm F ↥A0 :=
    QuadraticMap.comp (M := ↥A0) (N := Vm (r + 2) F) Q A0.subtype
  let QU (i : Fin m) : QuadraticForm F ↥(U i) :=
    QuadraticMap.comp (M := ↥(U i)) (N := ↥A0) Q0 (U i).subtype
  let QW : QuadraticForm F ↥W :=
    QuadraticMap.comp (M := ↥W) (N := ↥A0) Q0 W.subtype
  let zetaU (i : Fin m) : (QU i).IsometryEquiv
      (Q.comp (U0 (iota i)).subtype) :=
    { Submodule.comapSubtypeEquivOfLe (hU0_le_A0 (iota i) (hiota_mem i)) with
      map_app' := fun _ => rfl }
  let zetaW : QW.IsometryEquiv (Q.comp W0.subtype) :=
    { Submodule.comapSubtypeEquivOfLe hW0_le_A0 with
      map_app' := fun _ => rfl }
  have hWnotplus : ¬ IsPlusType (K := F) (V := ↥W) QW := by
    intro h
    have hw0 := IsPlusType.of_isometryEquiv
      (K := F) (V := ↥W) (V' := ↥W0)
      (Q := QW) (Q' := Q.comp W0.subtype) zetaW h
    exact hWnotplus0 hw0
  let eHyp : (hypQuadForm (LinearMap.id : F →ₗ[F] F)).IsometryEquiv (hypPlane F) :=
    { toLinearEquiv := LinearEquiv.refl F (F × F)
      map_app' := by
        intro v
        rw [hypQuadForm_apply, hypPlane_apply]
        rfl }
  have hUplus (i : Fin m) : IsPlusType (K := F) (V := ↥(U i)) (QU i) :=
    IsPlusType.of_isometryEquiv
      (K := F) (V := F × F) (V' := ↥(U i))
      (Q := hypQuadForm (LinearMap.id : F →ₗ[F] F)) (Q' := QU i)
      (eHyp.trans ((coordPlaneIsometry ψ hψ (iota i)).trans (zetaU i).symm))
      (isPlusType_hypQuadForm (LinearMap.id : F →ₗ[F] F))
  let o : Fin m := ⟨0, by omega⟩
  let R : QuadraticForm F E := Q.comp E.subtype
  let j : R.IsometryEquiv (QU o) := (coordPlaneIsometry ψ hψ 0).symm.trans
    ((coordPlaneIsometry ψ hψ (iota o)).trans (zetaU o).symm)

  let J : ((Q.comp A0.subtype).prod R).IsometryEquiv (Q.comp AK.subtype) :=
    { toLinearEquiv := (K159.supEquiv A0 E hdisj).trans
        (LinearEquiv.ofEq (A0 ⊔ E) AK hsum)
      map_app' := by
        intro z
        obtain ⟨x, y⟩ := z
        let A0E : Submodule F (Vm (r + 2) F) := A0 ⊔ E
        change Q (((K159.supEquiv A0 E hdisj) (x, y) : A0E) : Vm (r + 2) F) =
          (Q.comp A0.subtype) x + (Q.comp E.subtype) y
        rw [K159.supEquiv_apply]
        simp only [QuadraticMap.comp_apply, QuadraticMap.prod_apply,
          Submodule.subtype_apply]
        rw [QuadraticMap.map_add (⇑Q) _ _, horth x x.2 y y.2, add_zero] }
  have hJ_apply : ∀ (x : A0) (y : E),
      (J (x, y) : Vm (r + 2) F) = (x : Vm (r + 2) F) + (y : Vm (r + 2) F) := by
    intro x y
    let A0E : Submodule F (Vm (r + 2) F) := A0 ⊔ E
    change (((K159.supEquiv A0 E hdisj) (x, y) : A0E) : Vm (r + 2) F) =
      (x : Vm (r + 2) F) + (y : Vm (r + 2) F)
    exact K159.supEquiv_apply (A := A0) (B := E) (hAB := hdisj) x y
  let sS : ∀ S : Finset I, orthDerived (Q.comp (A S).subtype) ≃* C S := fun S =>
    (orthDerivedSupportedEquiv (hAreg S)).trans
      (Subgroup.subgroupOfEquivOfLe (hAle S)).symm
  let eO := sS O
  let eK := (CFSG.RankThree.PartOne.orthDerivedEquiv J).trans (sS Du)
  let iOL : C O →* C D0 :=
    Subgroup.inclusion (chartSubgroup_mono hirr (Finset.inter_subset_left))
  let iOK : C O →* C Du :=
    Subgroup.inclusion (chartSubgroup_mono hirr (Finset.inter_subset_right))

  have hSmap : ∀ {S T : Finset I} (hST : S ⊆ T),
      ((supportedDerived (Q.comp (A T).subtype) ((A S).comap (A T).subtype)).subgroupOf
        (orthDerived (Q.comp (A T).subtype))).map (sS T).toMonoidHom =
        (C S).subgroupOf (C T) := by
    intro S T hST
    have hAT : A S ≤ A T := anchoredSupport_mono hST
    have hmapT := orthDerivedSupportedEquiv_map_supportedDerived (Q := Q)
      (A := A S) (B := A T) hAT (hAreg S) (hAreg T)
    rw [show (sS T).toMonoidHom =
        (Subgroup.subgroupOfEquivOfLe (hAle T)).symm.toMonoidHom.comp
          (orthDerivedSupportedEquiv (hAreg T)).toMonoidHom from rfl]
    rw [← Subgroup.map_map]
    rw [hmapT]
    exact map_subgroupOfEquivOfLe_symm (A := supportedDerived Q (A S))
      (B := supportedDerived Q (A T)) (D := orthDerived Q) (hBD := hAle T)

  have hEO : ∀ T : Finset (Fin m),
      ((supportedDerived (Q.comp A0.subtype) (W ⊔ T.sup U)).subgroupOf
        (orthDerived (Q.comp A0.subtype))).map (sS O).toMonoidHom =
        (C (T.image iota)).subgroupOf (C O) := by
    intro T
    have hTsub : T.image iota ⊆ O := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      exact hiota_mem j
    rw [hP_eq T]
    exact hSmap (S := T.image iota) (T := O) hTsub

  let incl : orthDerived (Q.comp A0.subtype) →*
      orthDerived ((Q.comp A0.subtype).prod R) :=
    orthDerivedProdIncl (Q := Q.comp A0.subtype) (R := R)
  have hsquare : eK.toMonoidHom.comp incl = iOK.comp eO.toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change eK (incl g) = iOK (eO g)
    apply Subtype.ext
    apply Subtype.ext
    change (((eK (incl g) : C Du) : orthDerived Q) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) =
      (((iOK (eO g) : C Du) : orthDerived Q) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F)
    change ((sS Du ((CFSG.RankThree.PartOne.orthDerivedEquiv J) (incl g)) : C Du) :
        Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) =
      ((sS O g : C O) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F)
    rw [supportedChartEquiv_apply_coe (hA := hAreg Du) (hAle := hAle Du)]
    rw [supportedChartEquiv_apply_coe (hA := hAreg O) (hAle := hAle O)]
    exact supportedEquiv_prodIncl_coe (Q := Q) (A := A0) (E := E) (B := AK)
      (hAreg O) (hAreg Du) hA0_le_AK hEperp J hJ_apply g

  have htype := fun (i : Fin m) => iff_of_true (hUplus i) hWnotplus
  let Supp : Finset I → Subgroup (C Du) := fun S => (C S).subgroupOf (C Du)
  let Hbot : Finset (Fin m) → Subgroup (orthDerived ((Q.comp A0.subtype).prod R)) :=
    fun T => ((supportedDerived ((Q.comp A0.subtype).prod R)
      ((W ⊔ T.sup U).prod (⊥ : Submodule F E))).subgroupOf
      (orthDerived ((Q.comp A0.subtype).prod R)))
  let Htop : Finset (Fin m) → Subgroup (orthDerived ((Q.comp A0.subtype).prod R)) :=
    fun T => ((supportedDerived ((Q.comp A0.subtype).prod R)
      (((W ⊔ T.sup U).prod (⊥ : Submodule F E)) ⊔
        ((⊥ : Submodule F A0).prod (⊤ : Submodule F E)))).subgroupOf
      (orthDerived ((Q.comp A0.subtype).prod R)))
  have hsupp : ∀ T : Finset (Fin m),
      (Hbot T).map eK.toMonoidHom = Supp (T.image iota) ∧
      (Htop T).map eK.toMonoidHom = Supp (insert 0 (T.image iota)) := by
    intro T
    have h0notS : (0 : I) ∉ T.image iota := fun h0 => h0notO (hTsubO T h0)
    have hAinsert : A (insert 0 (T.image iota)) = A (T.image iota) ⊔ E := by
      rw [show A (insert 0 (T.image iota)) =
            coordSupport ψ (insert (0 : I) (T.image iota)) from hA_coord _,
        show A (T.image iota) = coordSupport ψ (T.image iota) from hA_coord _,
        show E = coordPlane ψ (0 : I) from rfl]
      exact coordSupport_insert ψ h0notS
    have hinsertSubDu : insert 0 (T.image iota) ⊆ Du := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hxS
      · exact h0Du
      · exact hTsubDu T hxS
    have hPmap : (W ⊔ T.sup U).map A0.subtype = A (T.image iota) := by
      rw [hP_eq T, Submodule.map_comap_subtype, inf_eq_right.mpr (hAleT T)]
    have hS0B : A (T.image iota) ≤ AK := (hAleT T).trans hA0_le_AK
    have hS1B : A (insert 0 (T.image iota)) ≤ AK := by
      dsimp [AK, A]
      exact anchoredSupport_mono hinsertSubDu
    have hpair := map_supported_product_chart_images
      (Q := Q) (A0 := A0) (E := E) (B := AK) (CK := C Du)
      (S0 := A (T.image iota)) (S1 := A (insert 0 (T.image iota)))
      J hJ_apply (sS Du) (W ⊔ T.sup U) hPmap hAinsert
      hS0B hS1B (hPnd T) (hU0reg 0)
      (hAreg (T.image iota)) (hAreg (insert 0 (T.image iota)))
      (Supp (T.image iota)) (Supp (insert 0 (T.image iota)))
      (hSmap (S := T.image iota) (T := Du) (hTsubDu T))
      (hSmap (S := insert 0 (T.image iota)) (T := Du) hinsertSubDu)
    exact ⟨hpair.1, hpair.2⟩
  exact exists_calibrated_mapped_prod_chart_of_marked_supports
    (F := F) (V := ↥A0) (E := ↥E) (G := G) (X := orthDerived Q) (Idx := I)
    (Q := Q.comp A0.subtype) (W := W) (U := U) (hm := hm) (hF := hcard)
    (hW := hWreg) (hWdim := hWdim) (hU := hUreg) (hUdim := hUdim)
    (hWU := hWU) (hUU := hUU) (hspan := hspan) (htype := htype)
    (R := R) (o := o) (j := j)
    (CS := C) (hC := fun {S T} hST => chartSubgroup_mono hirr hST)
    (d := 0) (Ovr := O) (DL := D0) (Dun := Du)
    (hOL := Finset.inter_subset_left) (hOK := Finset.inter_subset_right)
    (hDu := hDu_eq) (iota := iota) (hiota := hiota_image)
    (a := a) (k := k) (ha := ha) (hk := hk)
    (eO := eO) (eK := eK) (hsquare := hsquare)
    (hEO := hEO) (hbot := fun T => (hsupp T).1) (htop := fun T => (hsupp T).2)
    (hmark := hmark)

theorem exists_calibrated_deletion_chart_of_marked_supports
    (hr : 4 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hcard : 2 < Nat.card F) (h0u : (0 : I) ≠ u)
    (a : C D0 →* G) (k : C Du →* G)
    (ha : Function.Injective a) (hk : Function.Injective k)
    (hmark : ∀ S : Finset I, S.Nonempty → S.card ≤ 2 → S ⊆ O →
      ((C S).subgroupOf (C D0)).map a =
        ((C S).subgroupOf (C Du)).map k) :
    ∃ beta : MulAut (C Du),
      (k.comp beta.toMonoidHom).comp
          (Subgroup.inclusion (chartSubgroup_mono hirr
            (show O ⊆ Du from Finset.inter_subset_right))) =
        a.comp
          (Subgroup.inclusion (chartSubgroup_mono hirr
            (show O ⊆ D0 from Finset.inter_subset_left))) ∧
      Function.Injective (k.comp beta.toMonoidHom) ∧
      (k.comp beta.toMonoidHom).range = k.range ∧
      (∀ S : Finset I, S ⊆ Du →
        ((C S).subgroupOf (C Du)).map beta.toMonoidHom =
          (C S).subgroupOf (C Du)) :=
  exists_calibrated_deletion_chart_of_marked_supports_of_three_le (r := r)
    (by omega) hirr hcard h0u a k ha hk hmark
end CalibratedDeletionChart

noncomputable def splitMinusRhoOfTwoLe (r : ℕ)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 2 ≤ r) :
    Equiv.Perm (Fin (r + 1)) →* orthDerived (quadMinus (r + 2) F b c) :=
  codRestrictedρ (Q := quadMinus (r + 2) F b c) (QR := binaryForm F b c) (QE := hypPlane F)
    (R := Fin 2 → F) (E := F × F) (m := r + 1)
    (minusPlaneCoordinates (n := r + 2) (F := F))
    (nondegenerate_polarBilin_quadMinus_of_finite (r + 2) F hirr)
    hypPlane_polarBilin_nondegenerate
    (by
      intro v
      exact quadMinus_eq_binaryForm_add_minusPlaneCoordinates r v)
    (by
      have hdim : finrank F (Vm (r + 2) F) = 2 * r + 4 := by
        dsimp [Vm]
        rw [Module.finrank_fintype_fun_eq_card]
        simp only [Fintype.card_sum, Fintype.card_fin]
        omega
      rw [hdim]
      omega)

noncomputable def splitMinusRho (r : ℕ)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 4 ≤ r) :
    Equiv.Perm (Fin (r + 1)) →* orthDerived (quadMinus (r + 2) F b c) :=
  splitMinusRhoOfTwoLe r hirr (by omega)

@[simp] theorem coe_splitMinusRhoOfTwoLe_apply (r : ℕ)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 2 ≤ r)
    (σ : Equiv.Perm (Fin (r + 1))) :
    (((splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr) σ :
        orthDerived (quadMinus (r + 2) F b c)) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) =
      coordPermHom (minusPlaneCoordinates (n := r + 2) (F := F)) σ := by
  rw [splitMinusRhoOfTwoLe]
  exact coe_codRestrictedρ_apply _ _ _ _ _ σ

@[simp] theorem coe_splitMinusRho_apply (r : ℕ)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 4 ≤ r)
    (σ : Equiv.Perm (Fin (r + 1))) :
    (((splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr) σ :
        orthDerived (quadMinus (r + 2) F b c)) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) =
      coordPermHom (minusPlaneCoordinates (n := r + 2) (F := F)) σ :=
  coe_splitMinusRhoOfTwoLe_apply r hirr (by omega) σ

theorem chartSubgroup_map_conj_splitMinusRhoOfTwoLe
    (r : ℕ) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hr : 2 ≤ r)
    (σ : Equiv.Perm (Fin (r + 1))) (S : Finset (Fin (r + 1))) :
    (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).map
        (MulAut.conj
          (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ)).toMonoidHom =
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (S.image σ) := by
  classical
  unfold chartSubgroup
  rw [← coordSupport_minusPlaneCoordinates_eq_anchoredSupport
        (n := r + 2) (F := F) S,
      ← coordSupport_minusPlaneCoordinates_eq_anchoredSupport
        (n := r + 2) (F := F) (S.image σ)]
  unfold splitMinusRhoOfTwoLe
  exact map_coordSupport_subgroup _ _ _ _ _ σ S

theorem chartSubgroup_eq_iSup_pair
    (r : ℕ) (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (S : Finset (Fin (r + 1))) (hS : 2 ≤ S.card) :
    chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S =
      ⨆ P : PairBelow S,
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (P : Finset (Fin (r + 1))) := by
  classical
  let Q := quadMinus (r + 2) F b c
  let X := orthDerived Q
  let ψ := minusPlaneCoordinates (n := r + 2) (F := F)
  let B : Finset (Fin (r + 1)) → Subgroup X := fun T =>
    chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) T
  have hQ : (polarBilin Q).Nondegenerate := by
    dsimp [Q]
    exact nondegenerate_polarBilin_quadMinus_of_finite (r + 2) F hirr
  have hQE : (polarBilin (hypPlane F)).Nondegenerate :=
    hypPlane_polarBilin_nondegenerate
  have hψ : ∀ v : Vm (r + 2) F,
      Q v = binaryForm F b c (ψ v).1 + ∑ i, hypPlane F ((ψ v).2 i) := by
    intro v
    exact quadMinus_eq_binaryForm_add_minusPlaneCoordinates r v
  have hle : ∀ T : Finset (Fin (r + 1)),
      supportedDerived Q (anchoredSupport F (r + 2) T) ≤ X := by
    intro T
    refine supportedDerived_le_orthDerived_of_regular ?_
    have hW : PolarNondegOn (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) T) :=
      polarNondegOn_anchoredSupport (n := r + 2) (F := F) (b := b) (c := c) hirr T
    exact CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (Q := quadMinus (r + 2) F b c)
      (U := anchoredSupport F (r + 2) T)
      (fun x hx h => hW x hx h)
  have hWdim : finrank F (coordAnchor ψ) = 2 := by
    have hinj : Function.Injective
        (ψ.symm.toLinearMap.comp
          (LinearMap.inl F (Fin 2 → F) (Fin (r + 1) → F × F))) :=
      ψ.symm.injective.comp LinearMap.inl_injective
    have hdim : finrank F (coordAnchor ψ) = finrank F (Fin 2 → F) := by
      dsimp [coordAnchor]
      exact LinearMap.finrank_range_of_inj hinj
    rw [hdim, Module.finrank_fintype_fun_eq_card]
    simp
  have hUdim : ∀ i : Fin (r + 1), finrank F (coordPlane ψ i) = 2 := by
    intro i
    let L : (F × F) →ₗ[F] Vm (r + 2) F :=
      ψ.symm.toLinearMap.comp
        ((LinearMap.inr F (Fin 2 → F) (Fin (r + 1) → F × F)).comp
          (LinearMap.single F (fun _ => F × F) i))
    have hinj : Function.Injective L := by
      intro x y hxy
      have h' : (Pi.single i x : Fin (r + 1) → F × F) =
          (Pi.single i y : Fin (r + 1) → F × F) := by
        simpa [L] using congrArg (fun z => (ψ z).2) hxy
      have := congrFun h' i
      simpa using this
    have hdim : finrank F (coordPlane ψ i) = finrank F (F × F) := by
      dsimp [coordPlane]
      exact LinearMap.finrank_range_of_inj hinj
    rw [hdim, Module.finrank_prod]
    simp
  have hpairGenV : supportedDerived Q (coordSupport ψ S) =
      ⨆ P : PairBelow S,
        supportedDerived Q (coordSupport ψ (P : Finset (Fin (r + 1)))) := by
    simpa only [coordSupport] using
      supportedDerived_anchor_finset_sup_eq_iSup_pair (K := F) (V := Vm (r + 2) F)
        (Q := Q) (I := Fin (r + 1)) (U := coordPlane ψ) (W := coordAnchor ψ)
        (hWreg := coordAnchor_nondegenerate ψ hψ hQ hQE)
        (hWdim := hWdim)
        (hWU := fun i w hw u hu => polar_coordAnchor_plane ψ hψ hw hu)
        (hUreg := fun i =>
          CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
            (Q := Q) (U := coordPlane ψ i)
            (fun x hx h => (coordPlane_polarNondegOn ψ hψ hQE i) x hx h))
        (hUdim := hUdim)
        (hUorth := fun i j hij u hu v hv => polar_coordPlane_plane ψ hψ hij hu hv)
        S hS
  have hpairGenA : supportedDerived Q (anchoredSupport F (r + 2) S) =
      ⨆ P : PairBelow S,
        supportedDerived Q (anchoredSupport F (r + 2) (P : Finset (Fin (r + 1)))) := by
    simpa only [ψ, Vm, coordSupport_minusPlaneCoordinates_eq_anchoredSupport] using hpairGenV
  apply Subgroup.map_injective (f := (orthDerived Q).subtype) (orthDerived Q).subtype_injective
  calc
    (B S).map (orthDerived Q).subtype =
        supportedDerived Q (anchoredSupport F (r + 2) S) := by
      dsimp [B]
      rw [chartSubgroup, Subgroup.map_subgroupOf_eq_of_le (hle S)]
    _ = ⨆ P : PairBelow S,
          supportedDerived Q (anchoredSupport F (r + 2) (P : Finset (Fin (r + 1)))) :=
      hpairGenA
    _ = (⨆ P : PairBelow S, B (P : Finset (Fin (r + 1)))).map
          (orthDerived Q).subtype := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun P => ?_
      dsimp [B]
      rw [chartSubgroup, Subgroup.map_subgroupOf_eq_of_le (hle P.1)]

omit [Finite F] [CharP F 2] in
theorem coordPermHom_minusVec (r : ℕ) (σ : Equiv.Perm (Fin (r + 1))) (k : Fin (r + 1))
    (s : Bool) :
    coordPermHom (minusPlaneCoordinates (n := r + 2) (F := F)) σ (minusVec (r + 2) k s) =
      minusVec (r + 2) (σ k) s := by
  cases s
  · rw [← minusPlaneCoordinates_symm_single_false (n := r + 2) (F := F) k, coordPermHom_plane,
      minusPlaneCoordinates_symm_single_false]
  · rw [← minusPlaneCoordinates_symm_single_true (n := r + 2) (F := F) k, coordPermHom_plane,
      minusPlaneCoordinates_symm_single_true]

@[expose] noncomputable def nodeOmega (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (k : Fin (r + 1)) :
    Subgroup (orthDerived (quadMinus (r + 2) F b c)) :=
  (rankOne (minusDatum (r + 2) hirr).rootGroup k).map
    (spinEquivCommutatorQuadMinus (n := r + 2) (by omega) hirr
      (CharTwo.two_eq_zero : (2 : F) = 0)).toMonoidHom

theorem conj_splitMinusRhoOfTwoLe_mem_nodeOmega_two (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (σ : Equiv.Perm (Fin (r + 1)))
    (h0 : σ ⟨0, by omega⟩ = ⟨2, by omega⟩) (h1 : σ ⟨1, by omega⟩ = ⟨3, by omega⟩)
    {z : spinGroup (quadMinus (r + 2) F b c)}
    (hz : z ∈ rankOne (minusDatum (r + 2) hirr).rootGroup (⟨0, by omega⟩ : Fin (r + 1))) :
    splitMinusRhoOfTwoLe r hirr (by omega) σ *
        spinEquivCommutatorQuadMinus (n := r + 2) (by omega) hirr
          (CharTwo.two_eq_zero : (2 : F) = 0) z *
        (splitMinusRhoOfTwoLe r hirr (by omega) σ)⁻¹ ∈
      nodeOmega r (by omega) hirr ⟨2, by omega⟩ := by
  classical
  have hn4 : 4 ≤ r + 2 := by omega
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let eΩ := spinEquivCommutatorQuadMinus (n := r + 2) hn4 hirr h2
  let ρσ := splitMinusRhoOfTwoLe (F := F) (b := b) (c := c) r hirr (by omega) σ
  let w := eΩ.symm ρσ
  have hw : eΩ w = ρσ := eΩ.apply_symm_apply _
  have hact : spinAction (quadMinus (r + 2) F b c) w =
      coordPermHom (minusPlaneCoordinates (n := r + 2) (F := F)) σ := by
    rw [← coe_spinEquivCommutatorQuadMinus_apply hn4 hirr h2 w]
    change ((eΩ w : orthDerived (quadMinus (r + 2) F b c)) :
      Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) = _
    rw [hw]
    exact coe_splitMinusRhoOfTwoLe_apply r hirr (by omega) σ
  have hvec : ∀ (k : Fin (r + 1)) (s : Bool),
      spinAction (quadMinus (r + 2) F b c) w ((minusFrame (r + 2) b c).vec k s) =
        (1 : F) • (minusFrame (r + 2) b c).vec (σ k) s := by
    intro k s
    rw [hact, minusFrame_vec, one_smul]
    exact coordPermHom_minusVec r σ k s
  have hk0 : (⟨0, by omega⟩ : Fin (r + 1)).val + 1 < r + 2 - 1 := by simp; omega
  have hk2 : (⟨2, by omega⟩ : Fin (r + 1)).val + 1 < r + 2 - 1 := by simp; omega
  have hconj : (MulAut.conj w).toMonoidHom.comp
      (CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hk0) =
      CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hk2 := by
    apply MonoidHom.eq_of_eqOn_dense (CFSG.Timmesfeld.closure_tv_two (F := F))
    rintro g (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · rw [MonoidHom.comp_apply, CFSG.ClassicalInvolution.WeakCT.rLong_tv01,
        CFSG.ClassicalInvolution.WeakCT.rLong_tv01, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulAut.conj_apply]
      have h := (minusFrame (r + 2) b c).conj_longRoot w (succ_ne_of_lt (r + 2) hk0) true false
        (succ_ne_of_lt (r + 2) hk2) true false (hvec _ true |>.trans (by rw [h0]))
        (hvec _ false |>.trans (by rw [show σ ⟨(⟨0, by omega⟩ : Fin (r + 1)).val + 1, hk0⟩ =
          ⟨(⟨2, by omega⟩ : Fin (r + 1)).val + 1, hk2⟩ from h1])) x
      rw [h, one_mul, one_mul]
    · rw [MonoidHom.comp_apply, CFSG.ClassicalInvolution.WeakCT.rLong_tv10,
        CFSG.ClassicalInvolution.WeakCT.rLong_tv10, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, MulAut.conj_apply]
      have h := (minusFrame (r + 2) b c).conj_longRoot w (succ_ne_of_lt (r + 2) hk0).symm true
        false (succ_ne_of_lt (r + 2) hk2).symm true false
        (hvec _ true |>.trans (by rw [show σ ⟨(⟨0, by omega⟩ : Fin (r + 1)).val + 1, hk0⟩ =
          ⟨(⟨2, by omega⟩ : Fin (r + 1)).val + 1, hk2⟩ from h1]))
        (hvec _ false |>.trans (by rw [h0])) x
      rw [h, one_mul, one_mul]
  have hz' : z ∈ (CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hk0).range := by
    rw [← CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hk0]
    exact hz
  obtain ⟨A, rfl⟩ := hz'
  have hmem : w * CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hk0 A * w⁻¹ ∈
      rankOne (minusDatum (r + 2) hirr).rootGroup (⟨2, by omega⟩ : Fin (r + 1)) := by
    have h := congrArg (fun f : SL(2, F) →* spinGroup (quadMinus (r + 2) F b c) => f A) hconj
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply] at h
    rw [h]
    exact (congrArg (fun H : Subgroup (spinGroup (quadMinus (r + 2) F b c)) =>
      CFSG.ClassicalInvolution.WeakCT.rLong (r + 2) b c hk2 A ∈ H)
      (CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_long hirr hk2)).mpr ⟨A, rfl⟩
  unfold nodeOmega
  refine Subgroup.mem_map.mpr ⟨_, hmem, ?_⟩
  change eΩ (w * _ * w⁻¹) = _
  rw [map_mul, map_mul, map_inv, hw]

theorem splitMinusRhoOfTwoLe_mul_comm_of_fix_pair (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {u v : Fin (r + 1)} (huv : u ≠ v)
    (σ : Equiv.Perm (Fin (r + 1))) (hu : σ u = u) (hv : σ v = v)
    (x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) ({u, v} : Finset (Fin (r + 1)))) :
    splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ *
        (x : orthDerived (quadMinus (r + 2) F b c)) =
      (x : orthDerived (quadMinus (r + 2) F b c)) *
        splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ := by
  have hx : (x : orthDerived (quadMinus (r + 2) F b c)) ∈
      (supportedDerived (quadMinus (r + 2) F b c)
        (coordSupport (minusPlaneCoordinates (n := r + 2) (F := F))
          ({u, v} : Finset (Fin (r + 1))))).subgroupOf (orthDerived (quadMinus (r + 2) F b c)) := by
    rw [coordSupport_minusPlaneCoordinates_eq_anchoredSupport]
    exact x.2
  have hcen : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ *
      (x : orthDerived (quadMinus (r + 2) F b c)) *
      (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ)⁻¹ = x := by
    unfold splitMinusRhoOfTwoLe
    exact codRestrictedρ_centralizes_pair _ _ _ _ _ huv σ hu hv _ hx
  calc _ = (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ *
          (x : orthDerived (quadMinus (r + 2) F b c)) *
          (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ)⁻¹) *
        splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr σ := by group
    _ = _ := by rw [hcen]

theorem spinEquivCommutatorQuadMinus_mem_chartSubgroup_deletionPlanes (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F) (k : Fin r)
    {y : spinGroup (quadMinus (r + 2) F b c)}
    (hy : y ∈ rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k)) :
    spinEquivCommutatorQuadMinus (n := r + 2) (by omega) hirr
        (CharTwo.two_eq_zero : (2 : F) = 0) y ∈
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) := by
  rw [chartSubgroup]
  refine Subgroup.mem_subgroupOf.mpr ?_
  rw [coe_spinEquivCommutatorQuadMinus_apply,
    supportedDerived_anchoredSupport_eq_iSup_rankOne_map_spinAction (F := F) r b c hirr hcard hr]
  exact Subgroup.mem_iSup_of_mem k (Subgroup.mem_map_of_mem _ hy)

theorem chartSubgroup_deletionPlanes_eq_iSup_map_rankOne (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F) :
    chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) =
      ⨆ k : Fin r, (rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k)).map
        (spinEquivCommutatorQuadMinus (n := r + 2) (by omega) hirr
          (CharTwo.two_eq_zero : (2 : F) = 0)).toMonoidHom := by
  have hle : supportedDerived (quadMinus (r + 2) F b c)
      (anchoredSupport F (r + 2) (deletionPlanes r)) ≤ orthDerived (quadMinus (r + 2) F b c) := by
    refine supportedDerived_le_orthDerived_of_regular ?_
    have hW : PolarNondegOn (quadMinus (r + 2) F b c)
        (anchoredSupport F (r + 2) (deletionPlanes r)) :=
      polarNondegOn_anchoredSupport (n := r + 2) (F := F) (b := b) (c := c) hirr _
    exact CFSG.RankThree.PartOne.K159.nondegenerate_of_regOn
      (Q := quadMinus (r + 2) F b c) (U := anchoredSupport F (r + 2) (deletionPlanes r))
      (fun x hx h => hW x hx h)
  have hcomp : (orthDerived (quadMinus (r + 2) F b c)).subtype.comp
      (spinEquivCommutatorQuadMinus (n := r + 2) (by omega) hirr
        (CharTwo.two_eq_zero : (2 : F) = 0)).toMonoidHom =
      spinAction (quadMinus (r + 2) F b c) := by
    apply MonoidHom.ext
    intro x
    exact coe_spinEquivCommutatorQuadMinus_apply _ hirr _ x
  apply Subgroup.map_injective (f := (orthDerived (quadMinus (r + 2) F b c)).subtype)
    (orthDerived (quadMinus (r + 2) F b c)).subtype_injective
  calc
    (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r)).map
        (orthDerived (quadMinus (r + 2) F b c)).subtype =
        supportedDerived (quadMinus (r + 2) F b c)
          (anchoredSupport F (r + 2) (deletionPlanes r)) := by
      rw [chartSubgroup, Subgroup.map_subgroupOf_eq_of_le hle]
    _ = ⨆ k : Fin r, (rankOne (minusDatum (r + 2) hirr).rootGroup (Fin.succ k)).map
          (spinAction (quadMinus (r + 2) F b c)) :=
      supportedDerived_anchoredSupport_eq_iSup_rankOne_map_spinAction (F := F) r b c hirr hcard hr
    _ = _ := by
      rw [Subgroup.map_iSup]
      refine iSup_congr fun k => ?_
      rw [Subgroup.map_map, hcomp]

theorem spinEquivCommutatorQuadMinus_minusWeyl (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {k : Fin (r + 1)} (hk : k.val + 1 < r + 1) :
    spinEquivCommutatorQuadMinus (n := r + 2) (by omega) hirr
        (CharTwo.two_eq_zero : (2 : F) = 0) (minusWeyl (r + 2) hirr k) =
      splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr hr
        (Equiv.swap k ⟨k.val + 1, hk⟩) := by
  have hij : k ≠ ⟨k.val + 1, hk⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hw : minusWeyl (r + 2) hirr k = (minusFrame (r + 2) b c).longWeyl hij true false := by
    rw [minusWeyl_of_lt (n := r + 2) (b := b) (c := c) (hirr := hirr) (k := k) hk]
  apply Subtype.ext
  rw [coe_spinEquivCommutatorQuadMinus_apply, coe_splitMinusRhoOfTwoLe_apply, hw,
    spinAction_longWeyl_eq_coordPermHom (n := r + 2) (F := F) (b := b) (c := c) hij]

theorem commute_properSupportPhi_zero_two (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r) →* H)
    (t : Equiv.Perm (Fin (r + 1)) →* H)
    (hBmap : ∀ (σ : Equiv.Perm (Fin (r + 1))) (S : Finset (Fin (r + 1))),
      (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S).map
          (MulAut.conj (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr
            (by omega) σ)).toMonoidHom =
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (S.image σ))
    (hgen : ∀ S : Finset (Fin (r + 1)), S ⊆ deletionSet 0 → 2 ≤ S.card →
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S =
        ⨆ P : PairBelow S,
          chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (P : Finset (Fin (r + 1))))
    (hpair : ∀ (P : Finset (Fin (r + 1))) (σ : Equiv.Perm (Fin (r + 1))) (_ : P.card = 2)
      (hPD : P ⊆ deletionSet 0) (hPσD : P.image σ ⊆ deletionSet 0)
      (x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) P),
        a (Subgroup.inclusion
            (chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr hPσD)
            (conjMapHom (B := fun S => chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S)
              (ρ := splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega))
              hBmap σ P x)) =
          t σ * a (Subgroup.inclusion
            (chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr hPD) x) * (t σ)⁻¹)
    {σ : Equiv.Perm (Fin (r + 1))}
    (hσ0 : σ ⟨0, by omega⟩ = ⟨2, by omega⟩) (hσ1 : σ ⟨1, by omega⟩ = ⟨3, by omega⟩)
    (hfarσ : ∀ x y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
      (x : orthDerived (quadMinus (r + 2) F b c)) ∈
          nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
        (y : orthDerived (quadMinus (r + 2) F b c)) ∈
          nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
        Commute ((t σ)⁻¹ * a x * t σ) (a y))
    (x : (minusDatum (r + 2) hirr).leviAmalgam ⟨({⟨0, by omega⟩} : Finset (Fin (r + 1))),
      (Finset.card_singleton _).trans_le (by norm_num)⟩)
    (y : (minusDatum (r + 2) hirr).leviAmalgam ⟨({⟨2, by omega⟩} : Finset (Fin (r + 1))),
      (Finset.card_singleton _).trans_le (by norm_num)⟩) :
    Commute
      (properSupportPhi (d := (0 : Fin (r + 1)))
        (B := fun S => chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S)
        (hB := fun _ _ hST => chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr hST)
        (ρ := splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega))
        (a := a) (t := t) hBmap (totalCoords (r + 2) {⟨0, by omega⟩})
        (totalCoords_singleton_ne_univ _ (by omega))
        (leviLocalOmega (n := r + 2) (F := F) (b := b) (c := c) hirr hcard (by omega)
          ⟨({⟨0, by omega⟩} : Finset (Fin (r + 1))),
            (Finset.card_singleton _).trans_le (by norm_num)⟩ x))
      (properSupportPhi (d := (0 : Fin (r + 1)))
        (B := fun S => chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S)
        (hB := fun _ _ hST => chartSubgroup_mono (n := r + 2) (F := F) (b := b) (c := c) hirr hST)
        (ρ := splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega))
        (a := a) (t := t) hBmap (totalCoords (r + 2) {⟨2, by omega⟩})
        (totalCoords_singleton_ne_univ _ (by omega))
        (leviLocalOmega (n := r + 2) (F := F) (b := b) (c := c) hirr hcard (by omega)
          ⟨({⟨2, by omega⟩} : Finset (Fin (r + 1))),
            (Finset.card_singleton _).trans_le (by norm_num)⟩ y)) := by
  classical
  have hI : 4 ≤ Fintype.card (Fin (r + 1)) := by
    rw [Fintype.card_fin]
    omega
  have hne : ∀ i : Fin (r + 1), 2 ≤ i.val → i ∈ deletionSet (0 : Fin (r + 1)) := fun i hi =>
    Finset.mem_erase.mpr ⟨fun h => by simp [h] at hi, Finset.mem_univ i⟩
  have hσS0 : (totalCoords (r + 2) ({⟨0, by omega⟩} : Finset (Fin (r + 1)))).image σ ⊆
      deletionSet (0 : Fin (r + 1)) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    rcases mem_totalCoords_singleton hj with rfl | hj1
    · rw [hσ0]
      exact hne _ (by simp)
    · rw [show j = ⟨1, by omega⟩ from Fin.ext hj1, hσ1]
      exact hne _ (by simp)
  have hS2D : totalCoords (r + 2) ({⟨2, by omega⟩} : Finset (Fin (r + 1))) ⊆
      deletionSet (0 : Fin (r + 1)) := by
    intro i hi
    rcases mem_totalCoords_singleton hi with rfl | hi3
    · exact hne _ (by simp)
    · exact hne _ (by simp at hi3; omega)
  have hx0 : (x : spinGroup (quadMinus (r + 2) F b c)) ∈
      rankOne (minusDatum (r + 2) hirr).rootGroup (⟨0, by omega⟩ : Fin (r + 1)) := by
    have hx : (x : spinGroup (quadMinus (r + 2) F b c)) ∈ levi (minusDatum (r + 2) hirr).rootGroup
        ({⟨0, by omega⟩} : Finset (Fin (r + 1))) := x.2
    exact (levi_singleton _ _).le hx
  have hy2 : (y : spinGroup (quadMinus (r + 2) F b c)) ∈
      rankOne (minusDatum (r + 2) hirr).rootGroup (⟨2, by omega⟩ : Fin (r + 1)) := by
    have hy : (y : spinGroup (quadMinus (r + 2) F b c)) ∈ levi (minusDatum (r + 2) hirr).rootGroup
        ({⟨2, by omega⟩} : Finset (Fin (r + 1))) := y.2
    exact (levi_singleton _ _).le hy
  rw [properSupportPhi_apply_of_image_subset hBmap hgen hpair hI _ _ σ hσS0,
    properSupportPhi_apply_of_subset hBmap hgen hpair hI _ _ hS2D]
  refine hfarσ _ _ ?_ ?_
  · exact conj_splitMinusRhoOfTwoLe_mem_nodeOmega_two r hr hirr σ hσ0 hσ1 hx0
  · exact Subgroup.mem_map.mpr ⟨_, hy2, rfl⟩

theorem existsUnique_extends_deletion_and_permutation_of_three_le
    (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r) →* H)
    (t : Equiv.Perm (Fin (r + 1)) →* H)
    {u v cc : Fin (r + 1)}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : Fin (r + 1)) ≠ u) (h0v : (0 : Fin (r + 1)) ≠ v)
    (hcc0 : cc ≠ 0)
    (hcommon : ∀ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 →
      ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        a ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩ = t σ)
    (hcross : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        ({u, v} : Finset (Fin (r + 1))),
      t (Equiv.swap cc (0 : Fin (r + 1))) *
          a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) =
        a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) *
          t (Equiv.swap cc (0 : Fin (r + 1))))
    (hfar : 4 ≤ r ∨ ∃ σ : Equiv.Perm (Fin (r + 1)),
      σ ⟨0, by omega⟩ = ⟨2, by omega⟩ ∧ σ ⟨1, by omega⟩ = ⟨3, by omega⟩ ∧
      ∀ x y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        (x : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          (y : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          Commute ((t σ)⁻¹ * a x * t σ) (a y)) :
    ∃! Φ : orthDerived (quadMinus (r + 2) F b c) →* H,
      Φ.comp (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r)).subtype = a ∧
      Φ.comp (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)) = t := by
  classical
  let Q := quadMinus (r + 2) F b c
  let X := orthDerived Q
  let ψ := minusPlaneCoordinates (n := r + 2) (F := F)
  let B : Finset (Fin (r + 1)) → Subgroup X := fun S =>
    chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S
  let D : Finset (Fin (r + 1)) := deletionPlanes r
  let ρ : Equiv.Perm (Fin (r + 1)) →* X :=
    splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)
  let Δ := Twisted.minusDatum (r + 2) hirr
  have hn4 : 4 ≤ r + 2 := by omega
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let eΩ : spinGroup Q ≃* X :=
    spinEquivCommutatorQuadMinus (n := r + 2) hn4 hirr h2
  have hB : Monotone B := fun S T hST =>
    chartSubgroup_mono (F := F) (b := b) (c := c) hirr hST
  have hBmap : ∀ (σ : Equiv.Perm (Fin (r + 1))) (S : Finset (Fin (r + 1))),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ) := by
    intro σ S
    exact chartSubgroup_map_conj_splitMinusRhoOfTwoLe
      (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ S
  have hgenPB : ∀ (S : Finset (Fin (r + 1))), S ⊆ D → 2 ≤ S.card →
      B S = ⨆ P : PairBelow S, B (P : Finset (Fin (r + 1))) := by
    intro S _ hScard
    exact chartSubgroup_eq_iSup_pair
      (r := r) (F := F) (b := b) (c := c) hirr S hScard
  have hbase : ∀ (σ : Equiv.Perm (Fin (r + 1)))
      (x : B ({u, v} : Finset (Fin (r + 1)))),
      σ u = u → σ v = v → ρ σ * (x : X) = (x : X) * ρ σ := fun σ x hu hv =>
    splitMinusRhoOfTwoLe_mul_comm_of_fix_pair r (by omega) hirr huv σ hu hv x
  have hpair : ∀ (P : Finset (Fin (r + 1))) (σ : Equiv.Perm (Fin (r + 1)))
      (hPcard : P.card = 2) (hPD : P ⊆ deletionSet (0 : Fin (r + 1)))
      (hPσD : P.image σ ⊆ deletionSet (0 : Fin (r + 1))) (x : B P),
      a (Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P x)) =
        t σ * a (Subgroup.inclusion (hB hPD) x) * (t σ)⁻¹ := by
    exact pairCovariance_of_cross (hB := hB) (ρ := ρ) (a := a) (t := t)
      hBmap huv hcu hcv h0u h0v hcc0 hcommon hbase hcross
  have hI : 4 ≤ Fintype.card (Fin (r + 1)) := by
    rw [Fintype.card_fin]
    omega
  let φ : ∀ S : Finset (Fin (r + 1)), S ≠ Finset.univ → B S →* H :=
    fun S hS => properSupportPhi (hB := hB) (a := a) (t := t) hBmap S hS
  have hφ : ∀ (S T : Finset (Fin (r + 1))) (hS : S ≠ Finset.univ)
      (hT : T ≠ Finset.univ) (hST : S ⊆ T) (x : B S),
      φ T hT (Subgroup.inclusion (hB hST) x) = φ S hS x := by
    intro S T hS hT hST x
    have hcomp := properSupportPhi_comp_inclusion (hB := hB) (a := a) (t := t)
      hBmap hgenPB hpair hI S T hS hT hST
    simpa [φ, MonoidHom.comp_apply] using congrArg (fun f : B S →* H => f x) hcomp
  obtain ⟨Φ, hΦLevi, huniq⟩ :=
    existsUnique_levi_completion_of_coherent_charts_of_three_le (F := F) (b := b) (c := c)
      r hr hirr hcard φ hφ (hfar.imp id fun ⟨_, hσ0, hσ1, hfarσ⟩ =>
        commute_properSupportPhi_zero_two r hr hirr hcard a t hBmap hgenPB hpair hσ0 hσ1 hfarσ)
  have hSkD : ∀ k : Fin r, totalCoords (r + 2) {Fin.succ k} ⊆ D := by
    intro k
    dsimp [D]
    intro a ha
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ a⟩
    intro ha0
    subst ha0
    rw [totalCoords, Finset.mem_union] at ha
    rcases ha with hsingle | hcoords
    · rw [Finset.mem_singleton] at hsingle
      exact Fin.succ_ne_zero k hsingle.symm
    · obtain ⟨i, hi, _hk, hji | hval⟩ := mem_coordsF.1 hcoords
      · have hik : i = k.succ := by simpa using hi
        exact Fin.succ_ne_zero k (hji.trans hik).symm
      · exact (Nat.succ_ne_zero i.val) hval.symm
  have hmemD : ∀ (k : Fin r) (y : rankOne Δ.rootGroup (Fin.succ k)),
      eΩ y ∈ B D := fun k y =>
    spinEquivCommutatorQuadMinus_mem_chartSubgroup_deletionPlanes r hr hirr hcard k y.2
  have hsing : ∀ (k : Fin r) (y : rankOne Δ.rootGroup (Fin.succ k)),
      Φ (eΩ y) = a ⟨eΩ y, hmemD k y⟩ := by
    intro k y
    let J : {J : Finset (Fin (r + 1)) // J.card ≤ 2} := ⟨{Fin.succ k}, by simp⟩
    have hrank : rankOne Δ.rootGroup (Fin.succ k) ≤ Δ.leviAmalgam J :=
      rankOne_le_levi (X := Δ.rootGroup) (J := ({Fin.succ k} : Finset (Fin (r + 1))))
        (Finset.mem_singleton_self _)
    let x : Δ.leviAmalgam J := Subgroup.inclusion hrank y
    have hxval : ((x : Δ.leviAmalgam J) : spinGroup Q) = (y : spinGroup Q) := rfl
    have hCJne : totalCoords (r + 2) J.1 ≠ Finset.univ :=
      totalCoords_singleton_ne_univ (n := r + 2) (Fin.succ k) (by omega)
    have hLevi := hΦLevi J hCJne x
    have hCJD : totalCoords (r + 2) J.1 ⊆ D := by
      dsimp [J, D]
      exact hSkD k
    have hsub := properSupportPhi_apply_of_subset (hB := hB) (a := a) (t := t)
      hBmap hgenPB hpair hI (totalCoords (r + 2) J.1) hCJne hCJD
      (leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J x)
    have harg : Subgroup.inclusion (hB hCJD)
        (leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J x) =
          ⟨eΩ y, hmemD k y⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion, leviLocalOmega_apply_coe, hxval]
    calc
      Φ (eΩ y) = Φ (eΩ x) := rfl
      _ = φ (totalCoords (r + 2) J.1) hCJne
            (leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J x) := hLevi
      _ = a (Subgroup.inclusion (hB hCJD)
            (leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J x)) := hsub
      _ = a ⟨eΩ y, hmemD k y⟩ := congrArg a harg
  have hBDgen : B D = ⨆ k : Fin r,
      (rankOne Δ.rootGroup (Fin.succ k)).map eΩ.toMonoidHom :=
    chartSubgroup_deletionPlanes_eq_iSup_map_rankOne r hr hirr hcard
  have ha : Φ.comp (B D).subtype = a := by
    let Kfam : Fin r → Subgroup (B D) := fun k =>
      ((rankOne Δ.rootGroup (Fin.succ k)).map eΩ.toMonoidHom).subgroupOf (B D)
    have hKle : ∀ k : Fin r,
        (rankOne Δ.rootGroup (Fin.succ k)).map eΩ.toMonoidHom ≤ B D := by
      intro k
      rw [hBDgen]
      exact le_iSup (fun k : Fin r =>
        (rankOne Δ.rootGroup (Fin.succ k)).map eΩ.toMonoidHom) k
    have hgenK : ⨆ k : Fin r, Kfam k = ⊤ :=
      CFSG.RankThree.PartOne.iSup_subgroupOf_eq_top hKle hBDgen.symm
    apply CFSG.LieType.CurtisTits.hom_ext_of_iSup_eq_top (L := Kfam) hgenK
    intro k x
    have hxL : ((x : B D) : X) ∈
        (rankOne Δ.rootGroup (Fin.succ k)).map eΩ.toMonoidHom :=
      Subgroup.mem_subgroupOf.mp x.2
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hxL
    let y' : rankOne Δ.rootGroup (Fin.succ k) := ⟨y, hy⟩
    have hxy' : eΩ y' = ((x : B D) : X) := hxy
    have hxeq : (x : B D) = ⟨eΩ y', hmemD k y'⟩ := by
      apply Subtype.ext
      exact hxy'.symm
    change Φ ((x : B D) : X) = a (x : B D)
    rw [hxeq]
    exact hsing k y'
  have ht_adj : ∀ i : Fin r,
      Φ (ρ (Equiv.swap i.castSucc i.succ)) = t (Equiv.swap i.castSucc i.succ) := by
    intro i
    let k : Fin (r + 1) := i.castSucc
    have hklt : k.val + 1 < r + 1 := by
      dsimp [k, Fin.castSucc]
      omega
    let J : {J : Finset (Fin (r + 1)) // J.card ≤ 2} := ⟨{k}, by simp⟩
    let S : Finset (Fin (r + 1)) := totalCoords (r + 2) {k}
    let w : spinGroup Q := minusWeyl (r + 2) hirr k
    have hw_mem : w ∈ rankOne Δ.rootGroup k :=
      minusDatum_n_mem (n := r + 2) (b := b) (c := c) hirr k
    let y : rankOne Δ.rootGroup k := ⟨w, hw_mem⟩
    have heΩ : eΩ (y : spinGroup Q) = ρ (Equiv.swap k (Fin.succ i)) :=
      spinEquivCommutatorQuadMinus_minusWeyl r (by omega) hirr hklt
    have hrank : rankOne Δ.rootGroup k ≤ Δ.leviAmalgam J :=
      rankOne_le_levi (X := Δ.rootGroup) (J := ({k} : Finset (Fin (r + 1))))
        (Finset.mem_singleton_self _)
    have hSne : S ≠ Finset.univ :=
      totalCoords_singleton_ne_univ (n := r + 2) k (by omega)
    have hLevi := hΦLevi J hSne (Subgroup.inclusion hrank y)
    have hkS : k ∈ S := by
      simp [S, totalCoords]
    have hsuccS : Fin.succ i ∈ S := by
      have hks : Fin.succ i = (⟨k.val + 1, hklt⟩ : Fin (r + 1)) := by
        apply Fin.ext
        rfl
      rw [hks]
      dsimp [S, totalCoords]
      exact Finset.mem_insert_of_mem
        (succ_mem_coordsF (n := r + 2)
          (I := (↑({k} : Finset (Fin (r + 1))) : Set (Fin (r + 1))))
          (by exact Finset.mem_coe.mpr (Finset.mem_singleton_self k)) hklt)
    have hfix : ∀ x : Fin (r + 1), x ∉ S → Equiv.swap k (Fin.succ i) x = x := by
      intro x hx
      rw [Equiv.swap_apply_def]
      by_cases hxk : x = k
      · exact absurd (hxk ▸ hkS) hx
      · by_cases hxs : x = Fin.succ i
        · exact absurd (hxs ▸ hsuccS) hx
        · rw [if_neg hxk, if_neg hxs]
    have hmemS : ρ (Equiv.swap k (Fin.succ i)) ∈ B S := by
      change splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)
        (Equiv.swap k (Fin.succ i)) ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) S
      rw [chartSubgroup]
      refine Subgroup.mem_subgroupOf.mpr ?_
      rw [coe_splitMinusRhoOfTwoLe_apply]
      exact coordPermHom_swap_mem_supportedDerived (n := r + 2) (F := F) (b := b) (c := c)
        hirr hcard S hkS hsuccS
    have hcommonΦ := properSupportPhi_apply_common (hB := hB) (a := a) (t := t)
      hBmap hgenPB hpair hI S hSne (Equiv.swap k (Fin.succ i)) hfix hmemS hcommon
    have hval : ((leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J
          (Subgroup.inclusion hrank y) : B (totalCoords (r + 2) J.1)) : X) =
        ρ (Equiv.swap k (Fin.succ i)) := by
      rw [leviLocalOmega_apply_coe]
      exact heΩ
    have heΩx : eΩ (Subgroup.inclusion hrank y) = ρ (Equiv.swap k (Fin.succ i)) := by
      rw [← leviLocalOmega_apply_coe (F := F) (b := b) (c := c) hirr hcard hn4 J
        (Subgroup.inclusion hrank y)]
      exact hval
    have hLevi' : Φ (ρ (Equiv.swap k (Fin.succ i))) =
        φ S hSne ⟨ρ (Equiv.swap k (Fin.succ i)), hmemS⟩ :=
      (congrArg Φ heΩx.symm).trans (hLevi.trans (congrArg (φ S hSne) (Subtype.ext hval)))
    exact hLevi'.trans hcommonΦ
  have ht : Φ.comp ρ = t := by
    apply MonoidHom.eq_of_eqOn_dense
      (s := CFSG.Permutation.SymmetricCoxeter.adjSwap r '' Set.Iio r)
      (CFSG.Permutation.SymmetricCoxeter.closure_adjSwap r)
    rintro σ ⟨a, ha, rfl⟩
    have hlt : a < r := ha
    rw [MonoidHom.comp_apply, CFSG.Permutation.SymmetricCoxeter.adjSwap_of_lt hlt]
    have hcast : (⟨a, by omega⟩ : Fin (r + 1)) = (⟨a, hlt⟩ : Fin r).castSucc := by
      apply Fin.ext
      rfl
    have hsucc : (⟨a + 1, by omega⟩ : Fin (r + 1)) = (⟨a, hlt⟩ : Fin r).succ := by
      apply Fin.ext
      rfl
    rw [hcast, hsucc]
    exact ht_adj ⟨a, hlt⟩
  have hagree : ∀ (Ψ : X →* H), Ψ.comp (B D).subtype = a → Ψ.comp ρ = t →
      ∀ (S : Finset (Fin (r + 1))) (hS : S ≠ Finset.univ) (x : B S),
        Ψ x = φ S hS x := by
    intro Ψ haΨ htΨ S hS x
    obtain ⟨σ, hσ⟩ := exists_perm_image_subset_deletionSet
      (d := (0 : Fin (r + 1))) S hS
    have hσD : S.image σ ⊆ D := hσ
    let y : B (S.image σ) := conjMapHom hBmap σ S x
    let yD : B D := Subgroup.inclusion (hB hσD) y
    have hX : (yD : X) = ρ σ * (x : X) * (ρ σ)⁻¹ := by
      dsimp [yD, y]
      rw [show ((Subgroup.inclusion (hB hσD)
            (conjMapHom hBmap σ S x) : B D) : X) =
          (conjMapHom hBmap σ S x : X) from rfl,
        conjMapHom_apply_coe]
      rfl
    have hΨyD : Ψ (yD : X) = t σ * Ψ (x : X) * (t σ)⁻¹ := by
      rw [hX, map_mul, map_mul, map_inv]
      have hρ : Ψ (ρ σ) = t σ := by
        simpa using congrArg (fun f : Equiv.Perm (Fin (r + 1)) →* H => f σ) htΨ
      rw [hρ]
    have ha_yD : a yD = Ψ (yD : X) := by
      have := congrArg (fun f : B D →* H => f yD) haΨ
      simpa [MonoidHom.comp_apply] using this.symm
    rw [properSupportPhi_apply_of_image_subset (hB := hB) hBmap hgenPB hpair hI
      S hS σ hσD x]
    change Ψ x = (t σ)⁻¹ * a yD * t σ
    rw [ha_yD.trans hΨyD]
    group
  refine ⟨Φ, ⟨ha, ht⟩, ?_⟩
  intro Ψ hΨ
  apply huniq Ψ
  intro J hCJne x
  have hΨval := hagree Ψ hΨ.1 hΨ.2 (totalCoords (r + 2) J.1) hCJne
    (leviLocalOmega (F := F) (b := b) (c := c) hirr hcard hn4 J x)
  rw [← leviLocalOmega_apply_coe (F := F) (b := b) (c := c) hirr hcard hn4 J x]
  exact hΨval

theorem existsUnique_extends_deletion_and_permutation
    (r : ℕ) (hr : 4 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r) →* H)
    (t : Equiv.Perm (Fin (r + 1)) →* H)
    {u v cc : Fin (r + 1)}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : Fin (r + 1)) ≠ u) (h0v : (0 : Fin (r + 1)) ≠ v)
    (hcc0 : cc ≠ 0)
    (hcommon : ∀ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 →
      ∃ h : splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        a ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr σ, h⟩ = t σ)
    (hcross : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        ({u, v} : Finset (Fin (r + 1))),
      t (Equiv.swap cc (0 : Fin (r + 1))) *
          a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) =
        a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) *
          t (Equiv.swap cc (0 : Fin (r + 1)))) :
    ∃! Φ : orthDerived (quadMinus (r + 2) F b c) →* H,
      Φ.comp (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r)).subtype = a ∧
      Φ.comp (splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr) = t :=
  existsUnique_extends_deletion_and_permutation_of_three_le r (by omega) hirr hcard a t huv hcu
    hcv h0u h0v hcc0 hcommon hcross (Or.inl hr)

theorem range_eq_sup_of_extends_of_three_le
    (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r) →* H)
    (t : Equiv.Perm (Fin (r + 1)) →* H)
    {u v cc : Fin (r + 1)}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : Fin (r + 1)) ≠ u) (h0v : (0 : Fin (r + 1)) ≠ v)
    (hcc0 : cc ≠ 0)
    (hcommon : ∀ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 →
      ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        a ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩ = t σ)
    (hcross : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        ({u, v} : Finset (Fin (r + 1))),
      t (Equiv.swap cc (0 : Fin (r + 1))) *
          a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) =
        a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) *
          t (Equiv.swap cc (0 : Fin (r + 1))))
    (hfar : 4 ≤ r ∨ ∃ σ : Equiv.Perm (Fin (r + 1)),
      σ ⟨0, by omega⟩ = ⟨2, by omega⟩ ∧ σ ⟨1, by omega⟩ = ⟨3, by omega⟩ ∧
      ∀ x y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        (x : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          (y : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          Commute ((t σ)⁻¹ * a x * t σ) (a y))
    {Φ : orthDerived (quadMinus (r + 2) F b c) →* H}
    (haΦ : Φ.comp (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r)).subtype = a)
    (htΦ : Φ.comp (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)) = t) :
    Φ.range = a.range ⊔ t.range := by
  classical
  let S : Subgroup H := a.range ⊔ t.range
  let aS : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r) →* S :=
    a.codRestrict S fun x =>
      Subgroup.mem_sup_left (show a x ∈ a.range from ⟨x, rfl⟩)
  let tS : Equiv.Perm (Fin (r + 1)) →* S :=
    t.codRestrict S fun σ =>
      Subgroup.mem_sup_right (show t σ ∈ t.range from ⟨σ, rfl⟩)
  have hcommonS : ∀ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 →
      ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        aS ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩ =
          tS σ := by
    intro σ hσ
    obtain ⟨h, hval⟩ := hcommon σ hσ
    refine ⟨h, ?_⟩
    apply Subtype.ext
    simpa [aS, tS, MonoidHom.codRestrict_apply] using hval
  have hcrossS : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      ({u, v} : Finset (Fin (r + 1))),
      tS (Equiv.swap cc (0 : Fin (r + 1))) *
          aS (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) =
        aS (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) *
          tS (Equiv.swap cc (0 : Fin (r + 1))) := by
    intro x
    apply Subtype.ext
    simpa [aS, tS, MonoidHom.codRestrict_apply] using hcross x
  have hfarS : 4 ≤ r ∨ ∃ σ : Equiv.Perm (Fin (r + 1)),
      σ ⟨0, by omega⟩ = ⟨2, by omega⟩ ∧ σ ⟨1, by omega⟩ = ⟨3, by omega⟩ ∧
      ∀ x y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        (x : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          (y : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          Commute ((tS σ)⁻¹ * aS x * tS σ) (aS y) := by
    rcases hfar with h4 | ⟨σ, hσ0, hσ1, hc⟩
    · exact Or.inl h4
    · refine Or.inr ⟨σ, hσ0, hσ1, fun x y hx hy => ?_⟩
      have h := (hc x y hx hy).eq
      exact Subtype.ext (by simpa [aS, tS, MonoidHom.codRestrict_apply] using h)
  obtain ⟨ΦS, hΦS, -⟩ :=
    existsUnique_extends_deletion_and_permutation_of_three_le
      (r := r) (hr := hr) (hirr := hirr) (hcard := hcard)
      (a := aS) (t := tS) (huv := huv) (hcu := hcu) (hcv := hcv)
      (h0u := h0u) (h0v := h0v) (hcc0 := hcc0)
      (hcommon := hcommonS) (hcross := hcrossS) (hfar := hfarS)
  obtain ⟨hΦSa, hΦSt⟩ := hΦS
  obtain ⟨Φ0, -, huniq0⟩ :=
    existsUnique_extends_deletion_and_permutation_of_three_le
      (r := r) (hr := hr) (hirr := hirr) (hcard := hcard)
      (a := a) (t := t) (huv := huv) (hcu := hcu) (hcv := hcv)
      (h0u := h0u) (h0v := h0v) (hcc0 := hcc0)
      (hcommon := hcommon) (hcross := hcross) (hfar := hfar)
  have hΦ0eq : Φ = Φ0 := huniq0 Φ ⟨haΦ, htΦ⟩
  have hSext_a : (S.subtype.comp ΦS).comp
      (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r)).subtype = a := by
    apply MonoidHom.ext
    intro x
    change S.subtype (ΦS (x : orthDerived (quadMinus (r + 2) F b c))) = a x
    have hx := congrArg
      (fun f : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (deletionPlanes r) →* S => f x) hΦSa
    rw [show ΦS (x : orthDerived (quadMinus (r + 2) F b c)) = aS x from hx]
    rfl
  have hSext_t : (S.subtype.comp ΦS).comp
      (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)) = t := by
    apply MonoidHom.ext
    intro σ
    change S.subtype (ΦS (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c)
      hirr (by omega) σ)) = t σ
    have hσ := congrArg
      (fun f : Equiv.Perm (Fin (r + 1)) →* S => f σ) hΦSt
    rw [show ΦS (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ) =
        tS σ from hσ]
    rfl
  have hcomp : S.subtype.comp ΦS = Φ :=
    (huniq0 (S.subtype.comp ΦS) ⟨hSext_a, hSext_t⟩).trans hΦ0eq.symm
  have hle : Φ.range ≤ S := by
    rw [← hcomp]
    rintro y ⟨x, rfl⟩
    exact (ΦS x).2
  have hale : a.range ≤ Φ.range := by
    rintro y ⟨x, rfl⟩
    refine ⟨(x : orthDerived (quadMinus (r + 2) F b c)), ?_⟩
    have hx := congrArg
      (fun f : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
          (deletionPlanes r) →* H => f x) haΦ
    simpa [MonoidHom.comp_apply] using hx
  have htle : t.range ≤ Φ.range := by
    rintro y ⟨σ, rfl⟩
    refine ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, ?_⟩
    have hσ := congrArg
      (fun f : Equiv.Perm (Fin (r + 1)) →* H => f σ) htΦ
    simpa [MonoidHom.comp_apply] using hσ
  have hSle : S ≤ Φ.range := sup_le hale htle
  simpa [S] using le_antisymm hle hSle

theorem isSimpleGroup_orthDerived_quadMinus_of_two_le (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    IsSimpleGroup (orthDerived (quadMinus (r + 2) F b c)) := by
  have hdim : finrank F (Vm (r + 2) F) = 2 * (r + 2) := by
    have h : finrank F (Vm (r + 2) F) = 2 * r + 4 := by
      dsimp [Vm]
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    omega
  exact (CFSG.ComponentClassification.UnbalancedCatalog.derived_simple_even
    (k := F) (W := Vm (r + 2) F) (n := r + 2) (by omega)
    (quadMinus (r + 2) F b c)
    (nondegenerate_polarBilin_quadMinus_of_finite (r + 2) F hirr) hdim).2.1

theorem injective_of_nontrivial_chart_of_two_le
    (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {H : Type} [Group H]
    {a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r) →* H}
    {Φ : orthDerived (quadMinus (r + 2) F b c) →* H}
    (haΦ : Φ.comp (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r)).subtype = a)
    (hne : ∃ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r), a x ≠ 1) :
    Function.Injective Φ := by
  have hΩ : IsSimpleGroup (orthDerived (quadMinus (r + 2) F b c)) :=
    isSimpleGroup_orthDerived_quadMinus_of_two_le (r := r) (F := F) (b := b) (c := c) hr
      hirr
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Φ.ker with hker | hker
  · exact hker
  · exfalso
    obtain ⟨x, hx⟩ := hne
    have hxker : (x : orthDerived (quadMinus (r + 2) F b c)) ∈ Φ.ker :=
      hker ▸ Subgroup.mem_top _
    have hΦx : Φ (x : orthDerived (quadMinus (r + 2) F b c)) = 1 :=
      MonoidHom.mem_ker.1 hxker
    have hax : a x = 1 := by
      have h := congrArg
        (fun f : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
            (deletionPlanes r) →* H => f x) haΦ
      have h' : Φ (x : orthDerived (quadMinus (r + 2) F b c)) = a x := by
        simpa [MonoidHom.comp_apply] using h
      rw [hΦx] at h'
      exact h'.symm
    exact hx hax

theorem exists_nontrivial_of_injective_a_of_two_le
    (r : ℕ) (hr : 2 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    {H : Type} [Group H]
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r) →* H)
    (t : Equiv.Perm (Fin (r + 1)) →* H)
    {u v : Fin (r + 1)} (huv : u ≠ v)
    (h0u : (0 : Fin (r + 1)) ≠ u) (h0v : (0 : Fin (r + 1)) ≠ v)
    (hcommon : ∀ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 →
      ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        a ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩ = t σ)
    (hinj : Function.Injective a) :
    ∃ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r), a x ≠ 1 := by
  classical
  let ψ := minusPlaneCoordinates (n := r + 2) (F := F)
  let σ : Equiv.Perm (Fin (r + 1)) := Equiv.swap u v
  have hσ0 : σ 0 = 0 := by
    dsimp [σ]
    exact Equiv.swap_apply_of_ne_of_ne h0u h0v
  obtain ⟨h, hval⟩ := hcommon σ hσ0
  refine ⟨⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩, ?_⟩
  have hρne : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ ≠ 1 := by
    intro hρ1
    let v0 : Vm (r + 2) F := ψ.symm (0, Pi.single u ((1, 0) : F × F))
    have h_eval : ((splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ :
        orthDerived (quadMinus (r + 2) F b c)) : Vm (r + 2) F ≃ₗ[F] Vm (r + 2) F) v0 =
        v0 := by
      rw [hρ1]
      rfl
    have h_coe := coe_splitMinusRhoOfTwoLe_apply (r := r) (F := F) (b := b) (c := c) hirr
      (by omega) σ
    rw [h_coe] at h_eval
    have hσu : σ u = v := by
      dsimp [σ]
      exact Equiv.swap_apply_left u v
    have h_plane : coordPermHom ψ σ v0 = ψ.symm (0, Pi.single v ((1, 0) : F × F)) := by
      change coordPermHom ψ σ (ψ.symm (0, Pi.single u ((1, 0) : F × F))) =
        ψ.symm (0, Pi.single v ((1, 0) : F × F))
      rw [coordPermHom_plane, hσu]
    rw [h_plane] at h_eval
    have hpair : (0, (Pi.single v ((1, 0) : F × F) : Fin (r + 1) → F × F)) =
        (0, (Pi.single u ((1, 0) : F × F) : Fin (r + 1) → F × F)) := by
      have h := congrArg ψ h_eval
      simpa [v0] using h
    have hcoord : (Pi.single v ((1, 0) : F × F) : Fin (r + 1) → F × F) u =
        (Pi.single u ((1, 0) : F × F) : Fin (r + 1) → F × F) u :=
      congrFun (congrArg Prod.snd hpair) u
    rw [Pi.single_eq_of_ne huv] at hcoord
    have hfst : (0 : F) = 1 := by
      simpa using congrArg Prod.fst hcoord
    exact zero_ne_one hfst
  have hxne : (⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩ :
      chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r)) ≠ 1 := by
    intro hx
    apply hρne
    simpa using congrArg
      (fun y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        (deletionPlanes r) => (y : orthDerived (quadMinus (r + 2) F b c))) hx
  intro ha1
  apply hxne
  exact hinj (by simpa using ha1)

theorem injective_range_of_injective_a_of_three_le
    (r : ℕ) (hr : 3 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r) →* H)
    (t : Equiv.Perm (Fin (r + 1)) →* H)
    {u v cc : Fin (r + 1)}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : Fin (r + 1)) ≠ u) (h0v : (0 : Fin (r + 1)) ≠ v)
    (hcc0 : cc ≠ 0)
    (hcommon : ∀ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 →
      ∃ h : splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        a ⟨splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega) σ, h⟩ = t σ)
    (hcross : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        ({u, v} : Finset (Fin (r + 1))),
      t (Equiv.swap cc (0 : Fin (r + 1))) *
          a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) =
        a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) *
          t (Equiv.swap cc (0 : Fin (r + 1))))
    (hfar : 4 ≤ r ∨ ∃ σ : Equiv.Perm (Fin (r + 1)),
      σ ⟨0, by omega⟩ = ⟨2, by omega⟩ ∧ σ ⟨1, by omega⟩ = ⟨3, by omega⟩ ∧
      ∀ x y : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        (x : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          (y : orthDerived (quadMinus (r + 2) F b c)) ∈
            nodeOmega (F := F) (b := b) (c := c) r (by omega) hirr ⟨2, by omega⟩ →
          Commute ((t σ)⁻¹ * a x * t σ) (a y))
    (hinj_a : Function.Injective a)
    {Φ : orthDerived (quadMinus (r + 2) F b c) →* H}
    (haΦ : Φ.comp (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r)).subtype = a)
    (htΦ : Φ.comp (splitMinusRhoOfTwoLe (r := r) (F := F) (b := b) (c := c) hirr (by omega)) = t) :
    Function.Injective Φ ∧ Φ.range = a.range ⊔ t.range := by
  have hne := exists_nontrivial_of_injective_a_of_two_le
    (r := r) (hr := by omega) (hirr := hirr) (a := a) (t := t)
    (huv := huv) (h0u := h0u) (h0v := h0v) (hcommon := hcommon) (hinj := hinj_a)
  exact ⟨injective_of_nontrivial_chart_of_two_le (r := r) (hr := by omega) (hirr := hirr)
      (a := a) (Φ := Φ) (haΦ := haΦ) (hne := hne),
    range_eq_sup_of_extends_of_three_le (r := r) (hr := hr) (hirr := hirr) (hcard := hcard)
      (a := a) (t := t) (huv := huv) (hcu := hcu) (hcv := hcv)
      (h0u := h0u) (h0v := h0v) (hcc0 := hcc0)
      (hcommon := hcommon) (hcross := hcross) (hfar := hfar) (Φ := Φ) (haΦ := haΦ)
      (htΦ := htΦ)⟩

theorem injective_range_of_injective_a
    (r : ℕ) (hr : 4 ≤ r)
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    {H : Type} [Group H]
    (a : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r) →* H)
    (t : Equiv.Perm (Fin (r + 1)) →* H)
    {u v cc : Fin (r + 1)}
    (huv : u ≠ v) (hcu : cc ≠ u) (hcv : cc ≠ v)
    (h0u : (0 : Fin (r + 1)) ≠ u) (h0v : (0 : Fin (r + 1)) ≠ v)
    (hcc0 : cc ≠ 0)
    (hcommon : ∀ σ : Equiv.Perm (Fin (r + 1)), σ 0 = 0 →
      ∃ h : splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr σ ∈
        chartSubgroup (n := r + 2) (F := F) (b := b) (c := c) (deletionPlanes r),
        a ⟨splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr σ, h⟩ = t σ)
    (hcross : ∀ x : chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
        ({u, v} : Finset (Fin (r + 1))),
      t (Equiv.swap cc (0 : Fin (r + 1))) *
          a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) =
        a (Subgroup.inclusion
            (chartSubgroup_mono (F := F) (b := b) (c := c) hirr
              (pair_subset_deletionSet (d := (0 : Fin (r + 1))) h0u.symm h0v.symm)) x) *
          t (Equiv.swap cc (0 : Fin (r + 1))))
    (hinj_a : Function.Injective a)
    {Φ : orthDerived (quadMinus (r + 2) F b c) →* H}
    (haΦ : Φ.comp (chartSubgroup (n := r + 2) (F := F) (b := b) (c := c)
      (deletionPlanes r)).subtype = a)
    (htΦ : Φ.comp (splitMinusRho (r := r) (F := F) (b := b) (c := c) hirr hr) = t) :
    Function.Injective Φ ∧ Φ.range = a.range ⊔ t.range :=
  injective_range_of_injective_a_of_three_le r (by omega) hirr hcard a t huv hcu hcv h0u
    h0v hcc0 hcommon hcross (Or.inl hr) hinj_a haΦ htΦ

end CFSG.RankThree.PartOne.KCOrthogonal
