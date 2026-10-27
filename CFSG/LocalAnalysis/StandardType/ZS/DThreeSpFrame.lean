module

public import CFSG.LocalAnalysis.StandardType.ZS.DThreeConfig
public import CFSG.Fischer.Classification.Orthogonal2.SpModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryBasis
public import CFSG.LargeExtraspecial.S2Three
public import CFSG.LocalAnalysis.ComponentClassification.ExcSelectorEvenTriality
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2PositionWork
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenExc
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusIota
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphUnitaryNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2RowNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SixRevCommBasic
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14LUUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14ModelUnitary
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerCoset
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14SpAMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindUnitaryGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphFix
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBMain
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaBShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCTRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaRowStepOneMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaClass
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowOmegaUnitaryRows
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotInvolutionTwoPartEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph
public import CFSG.Monster.B.TwoA.Unitary.Orbit1408Points
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Module CFSG.Fischer.Classification.Orth2

private def frameCoeff (i : Fin 8) (k : Fin 4) : ZMod 2 :=
  if k = 0 then 1 else if i.val.testBit (k.val - 1) then 1 else 0

private lemma frameCoeff_sum (k : Fin 4) : ∑ i : Fin 8, frameCoeff i k = 0 := by
  fin_cases k <;> decide

private lemma frameCoeff_injective {i j : Fin 8}
    (h : ∀ k : Fin 4, frameCoeff i k = frameCoeff j k) : i = j := by
  revert i j
  decide

private def frameComb {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (c : Fin 4 → V)
    (i : Fin 8) : V :=
  frameCoeff i 0 • c 0 + frameCoeff i 1 • c 1 + frameCoeff i 2 • c 2 + frameCoeff i 3 • c 3

private lemma frameComb_repr {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {e : Basis (Fin m ⊕ Fin m) (ZMod 2) V} {ii : Fin 4 → Fin m} (hii : Function.Injective ii)
    {c : Fin 4 → V} (hc : ∀ p, c p = e (Sum.inl (ii p))) (i : Fin 8) (k : Fin 4) :
    e.repr (frameComb c i) (Sum.inl (ii k)) = frameCoeff i k := by
  have hik : ∀ p : Fin 4, (ii p = ii k) ↔ p = k := fun p =>
    ⟨fun h => hii h, fun h => by rw [h]⟩
  simp only [frameComb, map_add, map_smul, hc, Finsupp.add_apply, Finsupp.smul_apply,
    Module.Basis.repr_self_apply, Sum.inl.injEq, hik, smul_eq_mul]
  fin_cases k <;> simp [frameCoeff]

private lemma frameComb_repr_inr {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {e : Basis (Fin m ⊕ Fin m) (ZMod 2) V} {ii : Fin 4 → Fin m}
    {c : Fin 4 → V} (hc : ∀ p, c p = e (Sum.inl (ii p))) (i : Fin 8) (j : Fin m) :
    e.repr (frameComb c i) (Sum.inr j) = 0 := by
  simp [frameComb, hc]

private lemma frameComb_orthogonal {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {b : LinearMap.BilinForm (ZMod 2) V} (c : Fin 4 → V)
    (hzero : ∀ p q : Fin 4, b (c p) (c q) = 0) (i j : Fin 8) :
    b (frameComb c i) (frameComb c j) = 0 := by
  simp [frameComb, hzero]

private lemma frameComb_apply_f0 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {b : LinearMap.BilinForm (ZMod 2) V} (c : Fin 4 → V) (f0 : V)
    (h0 : b f0 (c 0) = 1) (hk : ∀ k : Fin 4, k ≠ 0 → b f0 (c k) = 0) (i : Fin 8) :
    b f0 (frameComb c i) = 1 := by
  simp only [frameComb, map_add, map_smul]
  rw [h0, hk (1 : Fin 4) (by decide), hk (2 : Fin 4) (by decide),
    hk (3 : Fin 4) (by decide)]
  simp [frameCoeff]

private lemma frameComb_sum {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (c : Fin 4 → V) :
    ∑ i : Fin 8, frameComb c i = 0 := by
  simp only [frameComb, Finset.sum_add_distrib, ← Finset.sum_smul, frameCoeff_sum (0 : Fin 4),
    frameCoeff_sum (1 : Fin 4), frameCoeff_sum (2 : Fin 4), frameCoeff_sum (3 : Fin 4), zero_smul,
    add_zero]

private lemma bilin_list_sum_left_eq_zero {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {b : LinearMap.BilinForm (ZMod 2) V} (v : V) :
    ∀ L : List V, (∀ u ∈ L, b u v = 0) → b L.sum v = 0 := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons u L ih =>
    intro h
    rw [List.sum_cons, map_add, LinearMap.add_apply, h u (List.mem_cons_self ..), zero_add]
    exact ih fun w hw => h w (List.mem_cons_of_mem u hw)

private lemma list_prod_spT_apply {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {b : LinearMap.BilinForm (ZMod 2) V} (hb : b.IsAlt) :
    ∀ {L : List V} {x : V}, (∀ v ∈ L, ∀ w ∈ L, b v w = 0) → (∀ v ∈ L, b x v = 1) →
      (((L.map (spT (f := b) hb)).prod : TauCeti.BilinForm.isometryGroup b) :
        V ≃ₗ[ZMod 2] V) x = x + L.sum := by
  intro L
  induction L with
  | nil => intro x _ _; simp
  | cons v L ih =>
    intro x horth hx
    have hv : v ∈ v :: L := List.mem_cons_self ..
    have hx' : ∀ u ∈ L, b x u = 1 := fun u hu => hx u (List.mem_cons_of_mem v hu)
    have horth' : ∀ p ∈ L, ∀ q ∈ L, b p q = 0 := fun p hp q hq =>
      horth p (List.mem_cons_of_mem v hp) q (List.mem_cons_of_mem v hq)
    have hLv : b L.sum v = 0 :=
      bilin_list_sum_left_eq_zero v L fun u hu => horth u (List.mem_cons_of_mem v hu) v hv
    have hb1 : b (x + L.sum) v = 1 := by
      rw [map_add, LinearMap.add_apply, hx v hv, hLv, add_zero]
    rw [List.map_cons, List.prod_cons, List.sum_cons]
    change ((spT (f := b) hb v : TauCeti.BilinForm.isometryGroup b) : V ≃ₗ[ZMod 2] V)
      ((((L.map (spT (f := b) hb)).prod : TauCeti.BilinForm.isometryGroup b) :
        V ≃ₗ[ZMod 2] V) x) = x + (v + L.sum)
    rw [ih (x := x) horth' hx', spT_apply (f := b) hb, hb1, one_smul]
    abel

private lemma repr_basis_inr_self {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {e : Basis (Fin m ⊕ Fin m) (ZMod 2) V} (ii : Fin 4 → Fin m) :
    e.repr (e (Sum.inr (ii 0))) (Sum.inr (ii 0)) = 1 := by
  rw [Module.Basis.repr_self_apply, if_pos rfl]

private lemma f0_ne_zero {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {e : Basis (Fin m ⊕ Fin m) (ZMod 2) V} (ii : Fin 4 → Fin m) :
    e (Sum.inr (ii 0)) ≠ 0 := by
  intro h0
  have h1 : e.repr (e (Sum.inr (ii 0))) (Sum.inr (ii 0)) = 1 := repr_basis_inr_self ii
  rw [h0, map_zero] at h1
  simp at h1

private lemma frameComb_ne_zero {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {e : Basis (Fin m ⊕ Fin m) (ZMod 2) V} {ii : Fin 4 → Fin m} (hii : Function.Injective ii)
    {c : Fin 4 → V} (hc : ∀ p, c p = e (Sum.inl (ii p))) (i : Fin 8) :
    frameComb c i ≠ 0 := by
  intro h0
  have h := frameComb_repr (e := e) (ii := ii) hii (c := c) hc i (0 : Fin 4)
  rw [h0, map_zero] at h
  have hz : frameCoeff i (0 : Fin 4) = 1 := by simp [frameCoeff]
  rw [hz] at h
  simp at h

private lemma frameComb_injective {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {e : Basis (Fin m ⊕ Fin m) (ZMod 2) V} {ii : Fin 4 → Fin m} (hii : Function.Injective ii)
    {c : Fin 4 → V} (hc : ∀ p, c p = e (Sum.inl (ii p))) :
    Function.Injective (fun i : Fin 8 => frameComb c i) := by
  intro i j hij
  change frameComb c i = frameComb c j at hij
  exact frameCoeff_injective fun k => by
    have h1 := frameComb_repr (e := e) (ii := ii) hii (c := c) hc i k
    have h2 := frameComb_repr (e := e) (ii := ii) hii (c := c) hc j k
    rw [hij] at h1
    exact h1.symm.trans h2

private lemma frameComb_ne_f0 {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {e : Basis (Fin m ⊕ Fin m) (ZMod 2) V} {ii : Fin 4 → Fin m}
    {c : Fin 4 → V} (hc : ∀ p, c p = e (Sum.inl (ii p))) (i : Fin 8) :
    e (Sum.inr (ii 0)) ≠ frameComb c i := by
  intro h
  have h1 : e.repr (e (Sum.inr (ii 0))) (Sum.inr (ii 0)) = 1 := repr_basis_inr_self ii
  have h2 : e.repr (frameComb c i) (Sum.inr (ii 0)) = 0 := frameComb_repr_inr hc i (ii 0)
  rw [h, h2] at h1
  exact (zero_ne_one (α := ZMod 2)) h1

private lemma apply_f0_basis {m : ℕ}
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (e : Basis (Fin m ⊕ Fin m) (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hpairs : ∀ i j, b (e (Sum.inl i)) (e (Sum.inr j)) = if i = j then 1 else 0)
    (ii : Fin 4 → Fin m) (hii : Function.Injective ii) :
    b (e (Sum.inr (ii 0))) (e (Sum.inl (ii 0))) = 1 ∧
      ∀ k : Fin 4, k ≠ 0 → b (e (Sum.inr (ii 0))) (e (Sum.inl (ii k))) = 0 := by
  constructor
  · have h := hpairs (ii 0) (ii 0)
    rw [if_pos rfl] at h
    rwa [CFSG.LargeExtraspecial.OrthoF2.isAlt_symm (f := b) halt] at h
  · intro k hk
    have h := hpairs (ii k) (ii 0)
    rw [if_neg (fun hik => hk (hii hik)),
      CFSG.LargeExtraspecial.OrthoF2.isAlt_symm (f := b) halt] at h
    exact h

private lemma commute_list_prod_spT {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {b : LinearMap.BilinForm (ZMod 2) V} (hb : b.IsAlt)
    (w : Fin 8 → V) (x : V)
    (horth : ∀ i j, b (w i) (w j) = 0) (hpair : ∀ i, b x (w i) = 1)
    (hsum : (List.ofFn w).sum = 0) :
    Commute (spT (f := b) hb x) (List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod := by
  have hLorth : ∀ v ∈ List.ofFn w, ∀ u ∈ List.ofFn w, b v u = 0 := by
    intro v hv u hu
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hu
    exact horth i j
  have hLpair : ∀ v ∈ List.ofFn w, b x v = 1 := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact hpair i
  have hfix_w : ((((List.ofFn w).map (spT (f := b) hb)).prod :
      TauCeti.BilinForm.isometryGroup b) : V ≃ₗ[ZMod 2] V) x = x := by
    rw [list_prod_spT_apply (b := b) hb hLorth hLpair, hsum, add_zero]
  have hfix : (((List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod :
      TauCeti.BilinForm.isometryGroup b) : V ≃ₗ[ZMod 2] V) x = x := by
    rw [List.ofFn_comp' w (fun v => spT (f := b) hb v)]
    exact hfix_w
  rw [commute_iff_eq]
  have hconj : (List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod *
      spT (f := b) hb x *
      ((List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod)⁻¹ =
      spT (f := b) hb x := by
    rw [spT_conj (f := b) hb, hfix]
  have h2 : (List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod *
      spT (f := b) hb x =
      spT (f := b) hb x *
        (List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod := by
    calc (List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod * spT (f := b) hb x
        = (List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod * spT (f := b) hb x *
            ((List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod)⁻¹ *
            (List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod := by group
      _ = spT (f := b) hb x *
            (List.ofFn (fun i : Fin 8 => spT (f := b) hb (w i))).prod := by rw [hconj]
  exact h2.symm

private lemma scalarFrame_frameComb {m : ℕ} (hm : 4 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)}
    (halt : ∀ x, b x x = 0) (hbn : b.Nondegenerate)
    (e : Basis (Fin m ⊕ Fin m) (ZMod 2) (Fin (2 * m) → ZMod 2))
    (hinl : ∀ i j, b (e (Sum.inl i)) (e (Sum.inl j)) = 0)
    (hpairs : ∀ i j, b (e (Sum.inl i)) (e (Sum.inr j)) = if i = j then 1 else 0) :
    ∃ (d : Fin 8 → TauCeti.BilinForm.isometryGroup b) (g : TauCeti.BilinForm.isometryGroup b),
      ScalarFrame {h | ∃ v, v ≠ 0 ∧ h = spT (f := b) halt v} d g ∧ ∀ i, ¬ Commute g (d i) := by
  let ii : Fin 4 → Fin m := fun k => ⟨k.val, by omega⟩
  have hii : Function.Injective ii := fun p q h => Fin.ext (by simpa using congrArg Fin.val h)
  let c : Fin 4 → (Fin (2 * m) → ZMod 2) := fun k => e (Sum.inl (ii k))
  let f0 : (Fin (2 * m) → ZMod 2) := e (Sum.inr (ii 0))
  have hc : ∀ p, c p = e (Sum.inl (ii p)) := fun _ => rfl
  have hzero : ∀ p q : Fin 4, b (c p) (c q) = 0 := fun p q => hinl (ii p) (ii q)
  have hne : ∀ i, frameComb c i ≠ 0 := fun i =>
    frameComb_ne_zero (e := e) (ii := ii) hii (c := c) hc i
  have hinj : Function.Injective (fun i : Fin 8 => frameComb c i) :=
    frameComb_injective (e := e) (ii := ii) hii (c := c) hc
  obtain ⟨hf0, hf0_c⟩ := apply_f0_basis halt e hpairs ii hii
  have hf0_ne : f0 ≠ 0 := f0_ne_zero (e := e) ii
  have hpair : ∀ i, b f0 (frameComb c i) = 1 := fun i =>
    frameComb_apply_f0 c f0 hf0 hf0_c i
  have hsum : (List.ofFn (fun i : Fin 8 => frameComb c i)).sum = 0 := by
    rw [List.sum_ofFn]
    exact frameComb_sum c
  have hcomm := commute_list_prod_spT (b := b) halt (fun i : Fin 8 => frameComb c i) f0
    (fun i j => frameComb_orthogonal c hzero i j) hpair hsum
  refine ⟨fun i => spT (f := b) halt (frameComb c i), spT (f := b) halt f0, ?_, ?_⟩
  · refine ⟨fun i => ⟨frameComb c i, hne i, rfl⟩, ?_, ?_, ⟨f0, hf0_ne, rfl⟩, ?_, ?_⟩
    · intro i j hij
      exact hinj (eq_of_spT_eq (f := b) halt hbn (hne i) hij)
    · intro i j hij
      exact (commute_iff_eq _ _).mpr
        ((spT_mul_comm_iff (f := b) halt hbn (hne i)).mpr (frameComb_orthogonal c hzero i j))
    · intro i h
      exact frameComb_ne_f0 (e := e) (ii := ii) (c := c) hc i
        (eq_of_spT_eq (f := b) halt hbn hf0_ne h)
    · exact hcomm
  · intro i hcommi
    have h1 : spT (f := b) halt f0 * spT (f := b) halt (frameComb c i) =
        spT (f := b) halt (frameComb c i) * spT (f := b) halt f0 := hcommi.eq
    have h2 : b f0 (frameComb c i) = 0 := (spT_mul_comm_iff (f := b) halt hbn hf0_ne).mp h1
    exact (zero_ne_one (α := ZMod 2)) (h2.symm.trans (hpair i))

theorem exists_scalarFrame_spT {m : ℕ} (hm : 4 ≤ m)
    {b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2)} (halt : ∀ x, b x x = 0)
    (hnd : ∀ x, (∀ y, b x y = 0) → x = 0) :
    ∃ (d : Fin 8 → TauCeti.BilinForm.isometryGroup b) (e : TauCeti.BilinForm.isometryGroup b),
      ScalarFrame {g | ∃ v, v ≠ 0 ∧ g = spT (f := b) halt v} d e ∧ ∀ i, ¬ Commute e (d i) := by
  have hbn : b.Nondegenerate := nondegenerate_of_isAlt halt hnd
  have hdim : Module.finrank (ZMod 2) (Fin (2 * m) → ZMod 2) = 2 * m :=
    Module.finrank_fin_fun _
  obtain ⟨m', e, hdim', hinl, -, hpairs⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_blueprint_symplectic_basis
      b halt hbn
  have hm' : m' = m := by omega
  subst hm'
  exact scalarFrame_frameComb hm halt hbn e hinl hpairs

end CFSG.StandardType.ZS
