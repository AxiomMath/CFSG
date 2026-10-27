module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeFullCentre1585RowCoker

public section

namespace CFSG.StandardType.E6Centralizer1585

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private lemma ltrv4c2_finite_cyclic_quotient
    {M : Type*} [AddCommGroup M] (p : Submodule ℤ M) (g : M) (N : ℤ)
    (hN : N ≠ 0) (hspan : p ⊔ Submodule.span ℤ {g} = ⊤) (hNmem : N • g ∈ p) :
    Finite (M ⧸ p) ∧ IsAddCyclic (M ⧸ p) := by
  have hmap : Submodule.map (Submodule.mkQ p) (Submodule.span ℤ {g}) =
      Submodule.span ℤ {Submodule.mkQ p g} := by
    rw [Submodule.map_span]
    simp
  have hspan' : Submodule.span ℤ ({Submodule.mkQ p g} : Set (M ⧸ p)) = ⊤ := by
    rw [← hmap, Submodule.map_mkQ_eq_top]
    exact hspan
  have hsurj : Function.Surjective (fun k : ℤ => k • (Submodule.mkQ p g)) := by
    intro y
    have hy : y ∈ Submodule.span ℤ ({Submodule.mkQ p g} : Set (M ⧸ p)) := by
      rw [hspan']; trivial
    exact Submodule.mem_span_singleton.mp hy
  have hgen : AddSubgroup.zmultiples (Submodule.mkQ p g) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨k, rfl⟩ := hsurj y
    exact AddSubgroup.zsmul_mem_zmultiples _ k
  have hNq : N • (Submodule.mkQ p g) = 0 := by
    rw [← map_zsmul, ← LinearMap.mem_ker, Submodule.ker_mkQ]
    exact hNmem
  haveI hfin : Finite (AddSubgroup.zmultiples (Submodule.mkQ p g)) := by
    rw [finite_zmultiples]
    exact isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨N, hN, hNq⟩
  refine ⟨?_, IsAddCyclic.mk ⟨_, hsurj⟩⟩
  exact Finite.of_surjective
    (Subtype.val : AddSubgroup.zmultiples (Submodule.mkQ p g) → M ⧸ p)
    (fun y => ⟨⟨y, by rw [hgen]; trivial⟩, rfl⟩)

private lemma ltrv4c2_mem_sup_span_singleton {M : Type*} [AddCommGroup M] [Module ℤ M]
    {p : Submodule ℤ M} {a g : M} {k : ℤ} (h : a - k • g ∈ p) :
    a ∈ p ⊔ Submodule.span ℤ ({g} : Set M) :=
  Submodule.mem_sup.mpr ⟨a - k • g, h, k • g,
    zsmul_mem (Submodule.subset_span (Set.mem_singleton g)) k, by abel⟩

private lemma ltrv4c2_mem_sup_of_le_left {M : Type*} [AddCommGroup M] [Module ℤ M]
    {p q : Submodule ℤ M} {x : M} (h : x ∈ p) : x ∈ p ⊔ q :=
  Submodule.mem_sup.mpr ⟨x, h, 0, Submodule.zero_mem _, by simp⟩

private lemma ltrv4c2_mem_sup_of_le_right {M : Type*} [AddCommGroup M] [Module ℤ M]
    {p q : Submodule ℤ M} {x : M} (h : x ∈ q) : x ∈ p ⊔ q :=
  Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, x, h, by simp⟩

private lemma ltrv4c2_lin_mem {M : Type*} [AddCommGroup M] [Module ℤ M]
    {p : Submodule ℤ M} {v w : M} (a b : ℤ) (hv : v ∈ p) (hw : w ∈ p) : a • v + b • w ∈ p :=
  add_mem (zsmul_mem hv a) (zsmul_mem hw b)

private lemma ltrv4c2_eps_of_rel {M : Type*} [AddCommGroup M] [Module ℤ M]
    {p : Submodule ℤ M} {ε q : ℤ} (hε : ε = 1 ∨ ε = -1) {x y : M}
    (h : ε • y - q • x ∈ p) : y - (ε * q) • x ∈ p := by
  have key : ε • (ε • y - q • x) = y - (ε * q) • x := by
    rw [zsmul_sub, ← mul_zsmul, ← mul_zsmul]
    rcases hε with rfl | rfl
    · rw [one_mul, one_smul]
    · rw [show (-1 : ℤ) * (-1 : ℤ) = 1 by norm_num, one_smul]
  rw [← key]
  exact zsmul_mem h ε

private lemma ltrv4c2_spanMarks_le_nodeSub {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (ε q : ℤ) : Submodule.span ℤ {nodeMarks row} ≤ nodeSub row ε q :=
  fun v hv => Submodule.mem_sup.mpr
    ⟨v, Submodule.mem_sup.mpr ⟨v, hv, 0, zero_mem _, by simp⟩, 0, zero_mem _, by simp⟩

private lemma ltrv4c2_zero_le_nodeSub {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (ε q : ℤ) : zeroNodeLattice row ≤ nodeSub row ε q :=
  fun v hv => Submodule.mem_sup.mpr
    ⟨v, Submodule.mem_sup.mpr ⟨0, zero_mem _, v, hv, by simp⟩, 0, zero_mem _, by simp⟩

private lemma ltrv4c2_defect_le_nodeSub {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (ε q : ℤ) : nodeDefect row ε q ≤ nodeSub row ε q :=
  fun v hv => Submodule.mem_sup.mpr ⟨0, zero_mem _, v, hv, by simp⟩

private lemma ltrv4c2_marks_mem {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (ε q : ℤ) :
    nodeMarks row ∈ nodeSub row ε q :=
  ltrv4c2_spanMarks_le_nodeSub row ε q (Submodule.subset_span (Set.mem_singleton _))

private lemma ltrv4c2_zero_mem {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (ε q : ℤ)
    (i : Fin row.diagram.marks.length) (hi : row.s.getD i.val 0 = 0) :
    (Pi.single i (1 : ℤ) : NodeLat row) ∈ nodeSub row ε q :=
  ltrv4c2_zero_le_nodeSub row ε q (Submodule.subset_span ⟨i, hi, rfl⟩)

private lemma ltrv4c2_nodePermMap_single {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (i : Fin row.diagram.marks.length) :
    nodePermMap row (Pi.single i (1 : ℤ)) =
      (Pi.single (row.nodePerm i) (1 : ℤ) : NodeLat row) := by
  funext j
  rw [nodePermMap, LinearMap.funLeft_apply]
  by_cases h : j = row.nodePerm i
  · subst h; simp
  · have h' : row.nodePerm.symm j ≠ i := by
      intro hh
      exact h (by rw [← hh, Equiv.apply_symm_apply])
    rw [Pi.single_eq_of_ne h', Pi.single_eq_of_ne h]

private lemma ltrv4c2_nodePerm_eq_of {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (i : Fin row.diagram.marks.length) (r : ℕ) (h : row.rho.getD i.val 0 = r) :
    row.nodePerm i = ⟨r, by
      have he : row.rho.getD i.val 0 = (row.nodePerm i).val := row.rho_apply i
      have hlt : row.rho.getD i.val 0 < row.diagram.marks.length := by
        rw [he]; exact (row.nodePerm i).isLt
      rwa [h] at hlt⟩ := by
  apply Fin.ext
  exact (row.rho_apply i).symm.trans h

private lemma ltrv4c2_defect_rel {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (ε q : ℤ)
    (i j : Fin row.diagram.marks.length) (hP : row.nodePerm i = j) :
    ε • (Pi.single j (1 : ℤ) : NodeLat row) - q • (Pi.single i (1 : ℤ)) ∈ nodeSub row ε q := by
  have h : (ε • nodePermMap row - q • (LinearMap.id : NodeLat row →ₗ[ℤ] NodeLat row))
      (Pi.single i (1 : ℤ)) ∈ nodeSub row ε q := by
    refine ltrv4c2_defect_le_nodeSub row ε q ?_
    rw [nodeDefect]
    exact LinearMap.mem_range.mpr ⟨Pi.single i (1 : ℤ), rfl⟩
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    ltrv4c2_nodePermMap_single, hP] using h

private lemma ltrv4c2_defect_rel' {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (ε q : ℤ)
    (hε : ε = 1 ∨ ε = -1) (i j : Fin row.diagram.marks.length) (hP : row.nodePerm i = j) :
    (Pi.single j (1 : ℤ) : NodeLat row) - (ε * q) • (Pi.single i (1 : ℤ)) ∈ nodeSub row ε q :=
  ltrv4c2_eps_of_rel hε (ltrv4c2_defect_rel row ε q i j hP)

private lemma ltrv4c2_R16 {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (hT : row.T = .E6)
    (hs : row.s = [1, 1, 0, 0, 0, 0, 1])
    (hrho : row.rho = [1, 6, 3, 5, 4, 2, 0] ∨ row.rho = [6, 0, 5, 2, 4, 3, 1])
    (ε q : ℤ) (hε : ε = 1 ∨ ε = -1) (hq : 2 ≤ q) :
    Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q) := by
  rcases row with ⟨T, tw, type_eq, d, d_eq, s, s_length, s_mem, s_min, base, base_eq, rho,
    rho_length, rho_mem, nodePerm, rho_apply, D, D_eq, valid⟩
  subst hT
  let row' : KacRow lab p :=
    { T := .E6, tw := tw, type_eq := type_eq, d := d, d_eq := d_eq, s := s, s_length := s_length,
      s_mem := s_mem, s_min := s_min, base := base, base_eq := base_eq, rho := rho,
      rho_length := rho_length, rho_mem := rho_mem, nodePerm := nodePerm, rho_apply := rho_apply,
      D := D, D_eq := D_eq, valid := valid }
  change Finite (nodeCoker row' ε q) ∧ IsAddCyclic (nodeCoker row' ε q)
  have hs' : row'.s = [1, 1, 0, 0, 0, 0, 1] := hs
  have hrho' : row'.rho = [1, 6, 3, 5, 4, 2, 0] ∨ row'.rho = [6, 0, 5, 2, 4, 3, 1] := hrho
  have hlen : row'.diagram.marks.length = 7 := rfl
  have h0 : 0 < row'.diagram.marks.length := by omega
  have h1 : 1 < row'.diagram.marks.length := by omega
  have h2 : 2 < row'.diagram.marks.length := by omega
  have h3 : 3 < row'.diagram.marks.length := by omega
  have h4 : 4 < row'.diagram.marks.length := by omega
  have h5 : 5 < row'.diagram.marks.length := by omega
  have h6 : 6 < row'.diagram.marks.length := by omega
  let e0 : NodeLat row' := Pi.single ⟨0, h0⟩ 1
  let e1 : NodeLat row' := Pi.single ⟨1, h1⟩ 1
  let e2 : NodeLat row' := Pi.single ⟨2, h2⟩ 1
  let e3 : NodeLat row' := Pi.single ⟨3, h3⟩ 1
  let e4 : NodeLat row' := Pi.single ⟨4, h4⟩ 1
  let e5 : NodeLat row' := Pi.single ⟨5, h5⟩ 1
  let e6 : NodeLat row' := Pi.single ⟨6, h6⟩ 1
  have hz2 : row'.s.getD 2 0 = 0 := by rw [hs']; rfl
  have hz3 : row'.s.getD 3 0 = 0 := by rw [hs']; rfl
  have hz4 : row'.s.getD 4 0 = 0 := by rw [hs']; rfl
  have hz5 : row'.s.getD 5 0 = 0 := by rw [hs']; rfl
  have hmarks : nodeMarks row' ∈ nodeSub row' ε q := ltrv4c2_marks_mem row' ε q
  have hZ : (2 : ℤ) • e2 + (2 : ℤ) • e3 + (3 : ℤ) • e4 + (2 : ℤ) • e5 ∈ nodeSub row' ε q :=
    add_mem (add_mem (add_mem
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨2, h2⟩ hz2) 2)
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨3, h3⟩ hz3) 2))
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨4, h4⟩ hz4) 3))
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨5, h5⟩ hz5) 2)
  have h016 : e0 + e1 + e6 ∈ nodeSub row' ε q := by
    have hkey : nodeMarks row' - ((2 : ℤ) • e2 + (2 : ℤ) • e3 + (3 : ℤ) • e4 + (2 : ℤ) • e5) =
        e0 + e1 + e6 := by
      funext j
      fin_cases j <;> rfl
    rw [← hkey]
    exact sub_mem hmarks hZ
  have hN : (1 + ε * q + q ^ 2 : ℤ) ≠ 0 := by
    rcases hε with hε | hε <;> subst hε <;> (apply ne_of_gt; nlinarith [hq])
  rcases hrho' with hrho' | hrho'
  ·
    have hP0 : row'.nodePerm ⟨0, h0⟩ = ⟨1, h1⟩ :=
      ltrv4c2_nodePerm_eq_of row' ⟨0, h0⟩ 1 (by rw [hrho']; rfl)
    have hP1 : row'.nodePerm ⟨1, h1⟩ = ⟨6, h6⟩ :=
      ltrv4c2_nodePerm_eq_of row' ⟨1, h1⟩ 6 (by rw [hrho']; rfl)
    have hP6 : row'.nodePerm ⟨6, h6⟩ = ⟨0, h0⟩ :=
      ltrv4c2_nodePerm_eq_of row' ⟨6, h6⟩ 0 (by rw [hrho']; rfl)
    have hA : e1 - (ε * q) • e0 ∈ nodeSub row' ε q :=
      ltrv4c2_defect_rel' row' ε q hε ⟨0, h0⟩ ⟨1, h1⟩ hP0
    have hB : e6 - (ε * q) • e1 ∈ nodeSub row' ε q :=
      ltrv4c2_defect_rel' row' ε q hε ⟨1, h1⟩ ⟨6, h6⟩ hP1
    have hD : e6 - q ^ 2 • e0 ∈ nodeSub row' ε q := by
      have hkey : e6 - q ^ 2 • e0 =
          (1 : ℤ) • (e6 - (ε * q) • e1) + (ε * q) • (e1 - (ε * q) • e0) := by
        rcases hε with hε | hε <;> subst hε <;> module
      rw [hkey]
      exact ltrv4c2_lin_mem 1 (ε * q) hB hA
    have hNmem : (1 + ε * q + q ^ 2) • e0 ∈ nodeSub row' ε q := by
      have hkey : (1 + ε * q + q ^ 2) • e0 =
          (e0 + e1 + e6) - (e1 - (ε * q) • e0) - (e6 - q ^ 2 • e0) := by
        rcases hε with hε | hε <;> subst hε <;> module
      rw [hkey]
      exact sub_mem (sub_mem h016 hA) hD
    have hgen : ∀ i : Fin row'.diagram.marks.length,
        (Pi.single i (1 : ℤ) : NodeLat row') ∈
          nodeSub row' ε q ⊔ Submodule.span ℤ ({e0} : Set (NodeLat row')) := by
      intro i
      fin_cases i
      · exact ltrv4c2_mem_sup_of_le_right (Submodule.subset_span (Set.mem_singleton e0))
      · exact ltrv4c2_mem_sup_span_singleton hA
      · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨2, h2⟩ hz2)
      · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨3, h3⟩ hz3)
      · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨4, h4⟩ hz4)
      · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨5, h5⟩ hz5)
      · exact ltrv4c2_mem_sup_span_singleton hD
    have hspan : nodeSub row' ε q ⊔ Submodule.span ℤ ({e0} : Set (NodeLat row')) = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin row'.diagram.marks.length)).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rw [Pi.basisFun_apply]
      exact hgen i
    exact ltrv4c2_finite_cyclic_quotient (nodeSub row' ε q) e0 (1 + ε * q + q ^ 2) hN hspan hNmem
  ·
    have hP0 : row'.nodePerm ⟨0, h0⟩ = ⟨6, h6⟩ :=
      ltrv4c2_nodePerm_eq_of row' ⟨0, h0⟩ 6 (by rw [hrho']; rfl)
    have hP1 : row'.nodePerm ⟨1, h1⟩ = ⟨0, h0⟩ :=
      ltrv4c2_nodePerm_eq_of row' ⟨1, h1⟩ 0 (by rw [hrho']; rfl)
    have hP6 : row'.nodePerm ⟨6, h6⟩ = ⟨1, h1⟩ :=
      ltrv4c2_nodePerm_eq_of row' ⟨6, h6⟩ 1 (by rw [hrho']; rfl)
    have hA : e6 - (ε * q) • e0 ∈ nodeSub row' ε q :=
      ltrv4c2_defect_rel' row' ε q hε ⟨0, h0⟩ ⟨6, h6⟩ hP0
    have hB : e0 - (ε * q) • e1 ∈ nodeSub row' ε q :=
      ltrv4c2_defect_rel' row' ε q hε ⟨1, h1⟩ ⟨0, h0⟩ hP1
    have hC : e1 - (ε * q) • e6 ∈ nodeSub row' ε q :=
      ltrv4c2_defect_rel' row' ε q hε ⟨6, h6⟩ ⟨1, h1⟩ hP6
    have hD : e1 - q ^ 2 • e0 ∈ nodeSub row' ε q := by
      have hkey : e1 - q ^ 2 • e0 =
          (1 : ℤ) • (e1 - (ε * q) • e6) + (ε * q) • (e6 - (ε * q) • e0) := by
        rcases hε with hε | hε <;> subst hε <;> module
      rw [hkey]
      exact ltrv4c2_lin_mem 1 (ε * q) hC hA
    have hNmem : (1 + ε * q + q ^ 2) • e0 ∈ nodeSub row' ε q := by
      have hkey : (1 + ε * q + q ^ 2) • e0 =
          (e0 + e1 + e6) - (e6 - (ε * q) • e0) - (e1 - q ^ 2 • e0) := by
        rcases hε with hε | hε <;> subst hε <;> module
      rw [hkey]
      exact sub_mem (sub_mem h016 hA) hD
    have hgen : ∀ i : Fin row'.diagram.marks.length,
        (Pi.single i (1 : ℤ) : NodeLat row') ∈
          nodeSub row' ε q ⊔ Submodule.span ℤ ({e0} : Set (NodeLat row')) := by
      intro i
      fin_cases i
      · exact ltrv4c2_mem_sup_of_le_right (Submodule.subset_span (Set.mem_singleton e0))
      · exact ltrv4c2_mem_sup_span_singleton hD
      · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨2, h2⟩ hz2)
      · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨3, h3⟩ hz3)
      · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨4, h4⟩ hz4)
      · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨5, h5⟩ hz5)
      · exact ltrv4c2_mem_sup_span_singleton hA
    have hspan : nodeSub row' ε q ⊔ Submodule.span ℤ ({e0} : Set (NodeLat row')) = ⊤ := by
      rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin row'.diagram.marks.length)).span_eq]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      rw [Pi.basisFun_apply]
      exact hgen i
    exact ltrv4c2_finite_cyclic_quotient (nodeSub row' ε q) e0 (1 + ε * q + q ^ 2) hN hspan hNmem

private lemma ltrv4c2_R4Opp {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p) (hT : row.T = .E6)
    (hs : row.s = [0, 0, 0, 0, 0, 1, 1]) (hrho : row.rho = [1, 0, 3, 2, 4, 5, 6])
    (ε q : ℤ) (hε : ε = 1 ∨ ε = -1) (hq : 2 ≤ q) :
    Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q) := by
  rcases row with ⟨T, tw, type_eq, d, d_eq, s, s_length, s_mem, s_min, base, base_eq, rho,
    rho_length, rho_mem, nodePerm, rho_apply, D, D_eq, valid⟩
  subst hT
  let row' : KacRow lab p :=
    { T := .E6, tw := tw, type_eq := type_eq, d := d, d_eq := d_eq, s := s, s_length := s_length,
      s_mem := s_mem, s_min := s_min, base := base, base_eq := base_eq, rho := rho,
      rho_length := rho_length, rho_mem := rho_mem, nodePerm := nodePerm, rho_apply := rho_apply,
      D := D, D_eq := D_eq, valid := valid }
  change Finite (nodeCoker row' ε q) ∧ IsAddCyclic (nodeCoker row' ε q)
  have hs' : row'.s = [0, 0, 0, 0, 0, 1, 1] := hs
  have hrho' : row'.rho = [1, 0, 3, 2, 4, 5, 6] := hrho
  have hlen : row'.diagram.marks.length = 7 := rfl
  have h0 : 0 < row'.diagram.marks.length := by omega
  have h1 : 1 < row'.diagram.marks.length := by omega
  have h2 : 2 < row'.diagram.marks.length := by omega
  have h3 : 3 < row'.diagram.marks.length := by omega
  have h4 : 4 < row'.diagram.marks.length := by omega
  have h5 : 5 < row'.diagram.marks.length := by omega
  have h6 : 6 < row'.diagram.marks.length := by omega
  let e0 : NodeLat row' := Pi.single ⟨0, h0⟩ 1
  let e1 : NodeLat row' := Pi.single ⟨1, h1⟩ 1
  let e2 : NodeLat row' := Pi.single ⟨2, h2⟩ 1
  let e3 : NodeLat row' := Pi.single ⟨3, h3⟩ 1
  let e4 : NodeLat row' := Pi.single ⟨4, h4⟩ 1
  let e5 : NodeLat row' := Pi.single ⟨5, h5⟩ 1
  let e6 : NodeLat row' := Pi.single ⟨6, h6⟩ 1
  have hz0 : row'.s.getD 0 0 = 0 := by rw [hs']; rfl
  have hz1 : row'.s.getD 1 0 = 0 := by rw [hs']; rfl
  have hz2 : row'.s.getD 2 0 = 0 := by rw [hs']; rfl
  have hz3 : row'.s.getD 3 0 = 0 := by rw [hs']; rfl
  have hz4 : row'.s.getD 4 0 = 0 := by rw [hs']; rfl
  have hmarks : nodeMarks row' ∈ nodeSub row' ε q := ltrv4c2_marks_mem row' ε q
  have hZ : e0 + e1 + (2 : ℤ) • e2 + (2 : ℤ) • e3 + (3 : ℤ) • e4 ∈ nodeSub row' ε q :=
    add_mem (add_mem (add_mem (add_mem
      (ltrv4c2_zero_mem row' ε q ⟨0, h0⟩ hz0)
      (ltrv4c2_zero_mem row' ε q ⟨1, h1⟩ hz1))
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨2, h2⟩ hz2) 2))
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨3, h3⟩ hz3) 2))
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨4, h4⟩ hz4) 3)
  have h26 : (2 : ℤ) • e5 + e6 ∈ nodeSub row' ε q := by
    have hkey : nodeMarks row' - (e0 + e1 + (2 : ℤ) • e2 + (2 : ℤ) • e3 + (3 : ℤ) • e4) =
        (2 : ℤ) • e5 + e6 := by
      funext j
      fin_cases j <;> rfl
    rw [← hkey]
    exact sub_mem hmarks hZ
  have h26' : e6 - (-2 : ℤ) • e5 ∈ nodeSub row' ε q := by
    have hkey : e6 - (-2 : ℤ) • e5 = (2 : ℤ) • e5 + e6 := by module
    rw [hkey]
    exact h26
  have hP5 : row'.nodePerm ⟨5, h5⟩ = ⟨5, h5⟩ :=
    ltrv4c2_nodePerm_eq_of row' ⟨5, h5⟩ 5 (by rw [hrho']; rfl)
  have hNmem : (ε - q) • e5 ∈ nodeSub row' ε q := by
    have h := ltrv4c2_defect_rel row' ε q ⟨5, h5⟩ ⟨5, h5⟩ hP5
    simpa [sub_smul] using h
  have hN : (ε - q : ℤ) ≠ 0 := by
    rcases hε with hε | hε <;> subst hε <;> omega
  have hgen : ∀ i : Fin row'.diagram.marks.length,
      (Pi.single i (1 : ℤ) : NodeLat row') ∈
        nodeSub row' ε q ⊔ Submodule.span ℤ ({e5} : Set (NodeLat row')) := by
    intro i
    fin_cases i
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨0, h0⟩ hz0)
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨1, h1⟩ hz1)
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨2, h2⟩ hz2)
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨3, h3⟩ hz3)
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨4, h4⟩ hz4)
    · exact ltrv4c2_mem_sup_of_le_right (Submodule.subset_span (Set.mem_singleton e5))
    · exact ltrv4c2_mem_sup_span_singleton h26'
  have hspan : nodeSub row' ε q ⊔ Submodule.span ℤ ({e5} : Set (NodeLat row')) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin row'.diagram.marks.length)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact hgen i
  exact ltrv4c2_finite_cyclic_quotient (nodeSub row' ε q) e5 (ε - q) hN hspan hNmem

private lemma ltrv4c2_R16Opp {lab : LargeEvenLabel} {p : ℕ} (row : KacRow lab p)
    (hT : row.T = .E6) (hs : row.s = [1, 1, 0, 0, 0, 0, 1])
    (hrho : row.rho = [0, 6, 2, 5, 4, 3, 1]) (ε q : ℤ) (hε : ε = 1 ∨ ε = -1) (hq : 2 ≤ q) :
    Finite (nodeCoker row ε q) ∧ IsAddCyclic (nodeCoker row ε q) := by
  rcases row with ⟨T, tw, type_eq, d, d_eq, s, s_length, s_mem, s_min, base, base_eq, rho,
    rho_length, rho_mem, nodePerm, rho_apply, D, D_eq, valid⟩
  subst hT
  let row' : KacRow lab p :=
    { T := .E6, tw := tw, type_eq := type_eq, d := d, d_eq := d_eq, s := s, s_length := s_length,
      s_mem := s_mem, s_min := s_min, base := base, base_eq := base_eq, rho := rho,
      rho_length := rho_length, rho_mem := rho_mem, nodePerm := nodePerm, rho_apply := rho_apply,
      D := D, D_eq := D_eq, valid := valid }
  change Finite (nodeCoker row' ε q) ∧ IsAddCyclic (nodeCoker row' ε q)
  have hs' : row'.s = [1, 1, 0, 0, 0, 0, 1] := hs
  have hrho' : row'.rho = [0, 6, 2, 5, 4, 3, 1] := hrho
  have hlen : row'.diagram.marks.length = 7 := rfl
  have h0 : 0 < row'.diagram.marks.length := by omega
  have h1 : 1 < row'.diagram.marks.length := by omega
  have h2 : 2 < row'.diagram.marks.length := by omega
  have h3 : 3 < row'.diagram.marks.length := by omega
  have h4 : 4 < row'.diagram.marks.length := by omega
  have h5 : 5 < row'.diagram.marks.length := by omega
  have h6 : 6 < row'.diagram.marks.length := by omega
  let e0 : NodeLat row' := Pi.single ⟨0, h0⟩ 1
  let e1 : NodeLat row' := Pi.single ⟨1, h1⟩ 1
  let e2 : NodeLat row' := Pi.single ⟨2, h2⟩ 1
  let e3 : NodeLat row' := Pi.single ⟨3, h3⟩ 1
  let e4 : NodeLat row' := Pi.single ⟨4, h4⟩ 1
  let e5 : NodeLat row' := Pi.single ⟨5, h5⟩ 1
  let e6 : NodeLat row' := Pi.single ⟨6, h6⟩ 1
  have hz2 : row'.s.getD 2 0 = 0 := by rw [hs']; rfl
  have hz3 : row'.s.getD 3 0 = 0 := by rw [hs']; rfl
  have hz4 : row'.s.getD 4 0 = 0 := by rw [hs']; rfl
  have hz5 : row'.s.getD 5 0 = 0 := by rw [hs']; rfl
  have hmarks : nodeMarks row' ∈ nodeSub row' ε q := ltrv4c2_marks_mem row' ε q
  have hZ : (2 : ℤ) • e2 + (2 : ℤ) • e3 + (3 : ℤ) • e4 + (2 : ℤ) • e5 ∈ nodeSub row' ε q :=
    add_mem (add_mem (add_mem
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨2, h2⟩ hz2) 2)
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨3, h3⟩ hz3) 2))
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨4, h4⟩ hz4) 3))
      (zsmul_mem (ltrv4c2_zero_mem row' ε q ⟨5, h5⟩ hz5) 2)
  have h016 : e0 + e1 + e6 ∈ nodeSub row' ε q := by
    have hkey : nodeMarks row' - ((2 : ℤ) • e2 + (2 : ℤ) • e3 + (3 : ℤ) • e4 + (2 : ℤ) • e5) =
        e0 + e1 + e6 := by
      funext j
      fin_cases j <;> rfl
    rw [← hkey]
    exact sub_mem hmarks hZ
  have hP1 : row'.nodePerm ⟨1, h1⟩ = ⟨6, h6⟩ :=
    ltrv4c2_nodePerm_eq_of row' ⟨1, h1⟩ 6 (by rw [hrho']; rfl)
  have hP6 : row'.nodePerm ⟨6, h6⟩ = ⟨1, h1⟩ :=
    ltrv4c2_nodePerm_eq_of row' ⟨6, h6⟩ 1 (by rw [hrho']; rfl)
  have hA : e6 - (ε * q) • e1 ∈ nodeSub row' ε q :=
    ltrv4c2_defect_rel' row' ε q hε ⟨1, h1⟩ ⟨6, h6⟩ hP1
  have hB : e1 - (ε * q) • e6 ∈ nodeSub row' ε q :=
    ltrv4c2_defect_rel' row' ε q hε ⟨6, h6⟩ ⟨1, h1⟩ hP6
  have h0rel : e0 - (-(1 + ε * q)) • e1 ∈ nodeSub row' ε q := by
    have hkey : e0 - (-(1 + ε * q)) • e1 = (e0 + e1 + e6) - (e6 - (ε * q) • e1) := by
      module
    rw [hkey]
    exact sub_mem h016 hA
  have hNmem : (q ^ 2 - 1) • e1 ∈ nodeSub row' ε q := by
    have hkey : (q ^ 2 - 1) • e1 =
        - (e1 - (ε * q) • e6) - (ε * q) • (e6 - (ε * q) • e1) := by
      rcases hε with hε | hε <;> subst hε <;> module
    rw [hkey]
    exact sub_mem (neg_mem hB) (zsmul_mem hA (ε * q))
  have hN : (q ^ 2 - 1 : ℤ) ≠ 0 := by
    apply ne_of_gt
    nlinarith [hq]
  have hgen : ∀ i : Fin row'.diagram.marks.length,
      (Pi.single i (1 : ℤ) : NodeLat row') ∈
        nodeSub row' ε q ⊔ Submodule.span ℤ ({e1} : Set (NodeLat row')) := by
    intro i
    fin_cases i
    · exact ltrv4c2_mem_sup_span_singleton h0rel
    · exact ltrv4c2_mem_sup_of_le_right (Submodule.subset_span (Set.mem_singleton e1))
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨2, h2⟩ hz2)
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨3, h3⟩ hz3)
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨4, h4⟩ hz4)
    · exact ltrv4c2_mem_sup_of_le_left (ltrv4c2_zero_mem row' ε q ⟨5, h5⟩ hz5)
    · exact ltrv4c2_mem_sup_span_singleton hA
  have hspan : nodeSub row' ε q ⊔ Submodule.span ℤ ({e1} : Set (NodeLat row')) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℤ (Fin row'.diagram.marks.length)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [Pi.basisFun_apply]
    exact hgen i
  exact ltrv4c2_finite_cyclic_quotient (nodeSub row' ε q) e1 (q ^ 2 - 1) hN hspan hNmem

theorem nodeCokerCyclicR16_holds : NodeCokerCyclicR16 := by
  intro lab p row hT hdata ε q hε hq
  rcases hdata with ⟨hs, hrho⟩
  exact ltrv4c2_R16 row hT hs hrho ε q hε hq

theorem nodeCokerCyclicR4Opp_holds : NodeCokerCyclicR4Opp := by
  intro lab p row hT hdata ε q hε hq
  rcases hdata with ⟨hs, hrho⟩
  exact ltrv4c2_R4Opp row hT hs hrho ε q hε hq

theorem nodeCokerCyclicR16Opp_holds : NodeCokerCyclicR16Opp := by
  intro lab p row hT hdata ε q hε hq
  rcases hdata with ⟨hs, hrho⟩
  exact ltrv4c2_R16Opp row hT hs hrho ε q hε hq

end CFSG.StandardType.E6Centralizer1585

end
