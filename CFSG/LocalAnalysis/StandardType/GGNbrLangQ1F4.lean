module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1RLevel
public import CFSG.LocalAnalysis.StandardType.GGE0ExcAdjHolds
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Basic
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynO2
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM2Marking
import CFSG.GroupTheory.ConjKerCenter
import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.StandardType.S2MathAs51642Interfaces
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynO (ClassicalOr360)

theorem largeEvenMarking_of_classicalOr360
    {X : Type} [Group X] (hX : commutator X = ⊤) (h : ClassicalOr360 X) :
    LargeEvenMarking X (fun _ _ _ _ _ _ => True) := by
  rcases h with ⟨t, r, e, ht, hm⟩ | h
  · exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (largeEvenMarking_of_lieModel_centerQuot hX hm)
  · obtain ⟨e⟩ := h
    exact largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial)
      (CFSG.LocalAnalysis.GLTheoremA.I2015.marking_b2der_n_one hX e)

theorem largeEvenMarking_component_adjointF4
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {s : ↥(adjointGroup .F4 K)} (hs1 : s ≠ 1) (hsp : s ^ p = 1)
    {X : Subgroup ↥(adjointGroup .F4 K)}
    (hX : CFSG.Open.IsComponentOf X (Subgroup.centralizer {s})) :
    LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) := by
  classical
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hZ : Subgroup.center ↥(adjointGroup .F4 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := K)
  have hβmem : MulAut.conj s ∈
      CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived ↥(adjointGroup .F4 K) :=
    Subgroup.mem_sup_left ⟨s, rfl⟩
  have hβp : (MulAut.conj s) ^ p = 1 := by
    rw [← map_pow, hsp, map_one]
  have hβ1 : MulAut.conj s ≠ 1 := by
    intro h
    have hs : s ∈ (MulAut.conj :
        ↥(adjointGroup .F4 K) →* MulAut ↥(adjointGroup .F4 K)).ker :=
      MonoidHom.mem_ker.2 h
    rw [CFSG.GroupTheory.ker_conj_eq_center, hZ, Subgroup.mem_bot] at hs
    exact hs1 hs
  have hX' : CFSG.Open.IsComponentOf X
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (MulAut.conj s)) := by
    rw [CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup_conj s]
    exact hX
  exact largeEvenMarking_of_classicalOr360 hX.2.2.1
    (CFSG.LocalAnalysis.GLTheoremA.S265C.DynO.classicalOr360_adjointF4 hchar hp hp2 hβmem hβp
      hβ1 hX')

private theorem q1F4_action_transport
    {R C : Type*} [Group R] [Group C] (e : R ≃* C)
    {A : Subgroup (MulAut R)}
    (rA : ↥A → R) (hrA : ∀ a : ↥A, MulAut.conj (rA a) = (a : MulAut R))
    {J : Subgroup R} {E : Subgroup C}
    (hEa : ∀ a : ↥A, e (rA a) ∈ E)
    (hmarkGE : LargeEvenMarking ↥(J.map e.toMonoidHom)
      (fun lab _ _ I _ θ => GGChevStTag lab ∧ ∀ ε ∈ E, ∃ φ ∈ I,
        LargeEvenInduces θ (fun x x' : ↥(J.map e.toMonoidHom) =>
          (x' : C) = ε⁻¹ * x * ε) φ))
    (hAnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J) :
    LargeEvenMarking ↥J (fun _ _ _ I _ θ =>
      (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θ I) := by
  classical
  let X : Subgroup C := J.map e.toMonoidHom
  have hmarkX' : LargeEvenMarking ↥X (fun _ _ _ I _ θ =>
      ∀ a : ↥A, ∃ φ ∈ I,
        LargeEvenInduces θ (fun x x' : ↥X =>
          (x' : C) = e (rA a) * x * (e (rA a))⁻¹) φ) :=
    largeEvenMarking_mono (fun lab R' _ I F θ hθ => by
      intro a
      obtain ⟨φ, hφ, hind⟩ := hθ.2 ((e (rA a))⁻¹) (Subgroup.inv_mem _ (hEa a))
      exact ⟨φ, hφ, fun x x' hxx => hind x x' (by rw [inv_inv]; exact hxx)⟩) hmarkGE
  let eJ : ↥J ≃* ↥X := Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  have hrel : ∀ a : ↥A, ∀ j j' : ↥J,
      ((a : MulAut R) (j : R) = (j' : R)) ↔
        ((eJ j' : C) = e (rA a) * (eJ j : C) * (e (rA a))⁻¹) := by
    intro a j j'
    change ((a : MulAut R) (j : R) = (j' : R)) ↔
      (e (j' : R) = e (rA a) * e (j : R) * (e (rA a))⁻¹)
    constructor
    · intro h
      rw [← h, ← hrA a]
      simp only [MulAut.conj_apply, map_mul, map_inv]
    · intro h
      apply e.injective
      rw [← hrA a]
      simp only [MulAut.conj_apply, map_mul, map_inv]
      exact h.symm
  have hmJind : LargeEvenMarking ↥J (fun _ _ _ I _ θ => GGAutsInduceOn A J θ I) :=
    largeEvenMarking_congr eJ (fun lab R' _ I F θ hθ => by
      intro a ha
      obtain ⟨φ, hφ, hind⟩ := hθ ⟨a, ha⟩
      exact ⟨φ, hφ, (largeEvenInduces_congr_equiv eJ θ
        (fun j j' : ↥J => ((⟨a, ha⟩ : ↥A) : MulAut R) (j : R) = (j' : R))
        (fun x x' : ↥X => (x' : C) = e (rA ⟨a, ha⟩) * x * (e (rA ⟨a, ha⟩))⁻¹)
        (hrel ⟨a, ha⟩) φ).2 hind⟩) hmarkX'
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨hAnorm, h⟩) hmJind

section Q1F4Proof

private theorem q1F4_marking_component
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A : Subgroup (MulAut (TableBF4.RecipeGroup K))} (hAab : CFSG.Open.IsElemAbelian p A)
    (hAI : ∀ a ∈ A, a ∈ TableBF4.RecipeID K)
    {u : MulAut (TableBF4.RecipeGroup K)} (huA : u ∈ A) (huord : orderOf u = p)
    {J : Subgroup (TableBF4.RecipeGroup K)}
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup u)) :
    LargeEvenMarking ↥J (fun _ _ _ I _ θJ =>
      (∀ a ∈ A, ∀ j ∈ J, a j ∈ J) ∧ GGAutsInduceOn A J θJ I) := by
  classical
  let C := ↥(adjointGroup .F4 K)
  let e : TableBF4.RecipeGroup K ≃* C := TableBF4.recipeEquiv K
  have hfin : Finite ↥(adjointGroup .F4 K) :=
    CFSG.LieType.Chevalley.generated_group_finite .F4 K
  have hcj : Function.Injective (MulAut.conj : C →* MulAut C) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := K))
  have hcjR : Function.Injective
      (MulAut.conj : TableBF4.RecipeGroup K →* MulAut (TableBF4.RecipeGroup K)) :=
    CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (TableBF4.center_recipeGroup_eq_bot K)
  have hcongr : ∀ x : TableBF4.RecipeGroup K,
      MulAut.conj (e x) = MulAut.congr e (MulAut.conj x) := by
    intro x
    ext y
    simp [MulAut.conj_apply, MulAut.congr_apply]
  have hAinn : ∀ a : ↥A, (a : MulAut (TableBF4.RecipeGroup K)) ∈ Set.range
      (MulAut.conj : TableBF4.RecipeGroup K →* MulAut (TableBF4.RecipeGroup K)) :=
    fun a => TableBF4.idImage_subset_inn K (hAI a a.2)
  let rA : ↥A → TableBF4.RecipeGroup K := fun a => Classical.choose (hAinn a)
  have hrA : ∀ a : ↥A, MulAut.conj (rA a) = (a : MulAut (TableBF4.RecipeGroup K)) :=
    fun a => Classical.choose_spec (hAinn a)
  let ru := rA ⟨u, huA⟩
  have hru : MulAut.conj ru = u := hrA ⟨u, huA⟩
  have hup : u ^ p = 1 := by
    rw [← huord]
    exact pow_orderOf_eq_one u
  have hrp : ru ^ p = 1 := by
    apply hcjR
    rw [map_pow, hru, hup, map_one]
  set s : C := e ru with hs_def
  have hs1 : s ≠ 1 := by
    intro hs
    have hru1 : ru = 1 := e.injective (by rw [map_one, ← hs_def, hs])
    have hu1 : u = 1 := by rw [← hru, hru1, map_one]
    exact hp.ne_one (by rw [← huord, hu1, orderOf_one])
  have hsp : s ^ p = 1 := by
    rw [hs_def, ← map_pow, hrp, map_one]
  have hcommA : ∀ a : ↥A, (a : MulAut (TableBF4.RecipeGroup K)) * u = u * a := by
    intro a
    exact congrArg Subtype.val (isMulCommutative_iff.mp hAab.1 a ⟨u, huA⟩)
  let E : Subgroup C :=
    (A.map (MulAut.congr e).toMonoidHom).comap (MulAut.conj : C →* MulAut C)
  have hse : MulAut.conj s = MulAut.congr e u := by
    rw [hs_def, hcongr ru, hru]
  have hEa : ∀ a : ↥A, e (rA a) ∈ E := by
    intro a
    rw [Subgroup.mem_comap]
    refine Subgroup.mem_map.mpr ⟨(a : MulAut (TableBF4.RecipeGroup K)), a.2, ?_⟩
    change (MulAut.congr e) (a : MulAut (TableBF4.RecipeGroup K)) =
      MulAut.conj (e (rA a))
    exact ((hcongr (rA a)).trans (by rw [hrA a])).symm
  have hcent : E ≤ Subgroup.centralizer ({s} : Set C) := by
    intro ε hε
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨a0, ha0, haeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hε)
    let a : ↥A := ⟨a0, ha0⟩
    apply hcj
    rw [map_mul, map_mul, ← haeq, hse]
    change (MulAut.congr e) a0 * (MulAut.congr e) u =
      (MulAut.congr e) u * (MulAut.congr e) a0
    rw [← map_mul, ← map_mul, hcommA a]
  have hEexp : ∀ ε ∈ E, ε ^ p = 1 := by
    intro ε hε
    obtain ⟨a0, ha0, haeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hε)
    let a : ↥A := ⟨a0, ha0⟩
    apply hcj
    rw [map_pow, map_one, ← haeq]
    change ((MulAut.congr e) a0) ^ p = 1
    rw [← map_pow, hAab.2 a a.2, map_one]
  let X : Subgroup C := J.map e.toMonoidHom
  have hJ_asm : CFSG.Assembly.IsComponentOf J (ggAutFixedSubgroup u) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hJ
  have hmap : CFSG.Assembly.IsComponentOf X
      ((ggAutFixedSubgroup u).map e.toMonoidHom) :=
    CFSG.ComponentClassification.SymmetricLocal.isComponentOf_map_of_injective
      e.toMonoidHom e.injective hJ_asm
  have hfix : ggAutFixedSubgroup (MulAut.conj ru) = Subgroup.centralizer ({ru} : Set _) := by
    ext x
    rw [mem_ggAutFixedSubgroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    constructor
    · intro h
      have hx := congrArg (fun z => z * ru) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hx.symm
    · intro h
      calc ru * x * ru⁻¹ = x * ru * ru⁻¹ := by rw [← h]
        _ = x := by group
  have hfixmap : (ggAutFixedSubgroup u).map e.toMonoidHom =
      Subgroup.centralizer ({s} : Set C) := by
    rw [← hru, hfix, hs_def]
    exact CFSG.Walter.map_centralizer_singleton_mulEquiv e ru
  have hX_asm : CFSG.Assembly.IsComponentOf X (Subgroup.centralizer ({s} : Set C)) := by
    rw [← hfixmap]
    exact hmap
  have hX_open : CFSG.Open.IsComponentOf X (Subgroup.centralizer ({s} : Set C)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hX_asm
  have hN : E ≤ Subgroup.normalizer (X : Set C) :=
    fun ε hε => ggE0_adjoint_normalizes (Or.inl rfl) hp hp2 hs1 hsp hX_asm (hcent hε)
  have hI : LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) →
      ∀ ε ∈ E, CFSG.LocalAnalysis.GLTheoremA.S10.InnDiagOn 2 (Subgroup.zpowers ε) X :=
    fun hm ε hε => ggE0_adjoint_innDiagOn (Or.inl rfl) hp hp2 hs1 hsp
      (hEexp ε hε) (hcent hε) hX_asm hm
  have hS2 : LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) →
      LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GGChevStTag lab) :=
    fun hm => excNoSuzukiReeAdj_holds (Or.inl rfl) K p hp hp2 s hsp X hX_asm hm
  have hGGE0 : GGE0Concl E X :=
    ggE0Concl_of_innDiagOn_family (G := C) hp hp2 hEexp hN hS2 hI
  have hmarkX : LargeEvenMarking ↥X (fun _ _ _ _ _ _ => True) :=
    largeEvenMarking_component_adjointF4 hp hp2 hs1 hsp hX_open
  have hmarkGE : LargeEvenMarking ↥X (fun lab _ _ I _ θ => GGChevStTag lab ∧
      ∀ ε ∈ E, ∃ φ ∈ I, LargeEvenInduces θ
        (fun x x' : ↥X => (x' : C) = ε⁻¹ * x * ε) φ) := hGGE0.2 hmarkX
  have hAnormA : ∀ a : ↥A, ∀ j ∈ J, (a : MulAut _) j ∈ J := by
    intro a j hj
    have hNmem : X.map (MulAut.conj (e (rA a))).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hN (hEa a))
    have hconjX : MulAut.conj (e (rA a)) (e j) ∈ X := by
      rw [← hNmem]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem e.toMonoidHom hj)
    have heq : MulAut.conj (e (rA a)) (e j) = e ((a : MulAut _) j) := by
      rw [hcongr (rA a), hrA a]
      simp [MulAut.congr_apply]
    rw [heq] at hconjX
    obtain ⟨j', hj', heq'⟩ := Subgroup.mem_map.mp hconjX
    rw [e.injective heq'] at hj'
    exact hj'
  have hAnorm : ∀ a ∈ A, ∀ j ∈ J, a j ∈ J := fun a ha => hAnormA ⟨a, ha⟩
  exact q1F4_action_transport e rA hrA hEa hmarkGE hAnorm

theorem q1RToral_F4 :
    Q1RToralTransfer (fun _ _ _ => True) (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .F4)
      (fun _ _ _ => True) := by
  intro p hp hp2 lab hlab hS
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, ht⟩ := hS
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, ?_⟩
  intro A hAab hAI hTor u huA huord J hJ
  have hchar : CharP K 2 := charP_two_of_card hK
  exact largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩)
    (q1F4_marking_component hp hp2 hAab hAI huA huord hJ)

theorem q1On_centerPrimeTo_F4 :
    GGBstarInnerDiagJInputOn (fun p lab => CenterPrimeTo p lab ∧ lab.tag = .F4) :=
  q1On_of_selectedTransfer (q1SelectedTransfer_of_toral (q1ToralActionTransfer_of_rToral q1RToral_F4)
    fun _ _ _ _ _ _ _ _ _ _ _ _ hP =>
      largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h, fun _ _ _ => trivial⟩) hP)

theorem ggBstarInnerDiagJInputOn_of_not_F4 {S : ℕ → LargeEvenLabel → Prop}
    (hrest : GGBstarInnerDiagJInputOn (fun p lab => S p lab ∧ lab.tag ≠ .F4)) :
    GGBstarInnerDiagJInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hmark
  refine (q1On_or hrest q1On_centerPrimeTo_F4) G p B Bs x L D J hcfg ?_
  refine largeEvenMarking_mono (fun lab R _ I F θ h => ⟨?_, h.2⟩) hmark
  by_cases hF : lab.tag = .F4
  · exact Or.inr ⟨by simp [CenterPrimeTo, SmallDerived, hF], hF⟩
  · exact Or.inl ⟨h.1, hF⟩

end Q1F4Proof
end CFSG.StandardType
