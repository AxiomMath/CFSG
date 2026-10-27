module

public import CFSG.Sporadic.SuzRecog.Q3A
public import CFSG.Sporadic.SuzRecog.ModelGroupsDefs
public import CFSG.Sporadic.Co1Patterson.TitsMulti
public import Certificates.Certificate15089

public section

namespace CFSG.Sporadic.SuzRecog.Q3A

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.Co1Patterson CFSG.Monster.B.Recog
open CFSG.Sporadic.SuzRecog.Q3A.TitsCheck
open scoped Pointwise

structure IndexLayer where
  vtx : ℕ → Vtx
  exists_vtx : ∀ x : Vtx, ∃ i < 22880, vtx i = x
  smul_vtx : ∀ {g : ↥suzM} {a : Array ℕ}, Rep 1782 a (g : Equiv.Perm (Fin 1782)) → ∀ {i : ℕ},
    i < 22880 → g • vtx i = vtx (Check.actIdx a i) ∧ Check.actIdx a i < 22880
  adj_vtx_iff : ∀ {i j : ℕ}, i < 22880 → j < 22880 →
    (a4Graph.Adj (vtx i) (vtx j) ↔ Check.adjIdx i j = true)
  vtx_zero : vtx 0 = v0

@[expose] def triT (S : Set Vtx) : Prop :=
  ∃ x y z : Vtx, S = {x, y, z} ∧ a4Graph.Adj x y ∧ a4Graph.Adj y z ∧ a4Graph.Adj z x

theorem triT_smul (g : ↥suzM) (S : Set Vtx) (h : triT S) : triT ((g • ·) '' S) := by
  obtain ⟨x, y, z, rfl, hxy, hyz, hzx⟩ := h
  exact ⟨g • x, g • y, g • z, by simp [Set.image_insert_eq, Set.image_singleton],
    a4Graph_adj_smul g hxy, a4Graph_adj_smul g hyz, a4Graph_adj_smul g hzx⟩

section Check

theorem titsCheck_parts :
    (∀ a ∈ gensT, isInvA 1782 a (invCand 1782 a) = true ∧ inM a = true) ∧
    isInvA 1782 LevelTwoData.rhoArr (invCand 1782 LevelTwoData.rhoArr) = true ∧
    iv1 < 22880 ∧ iu0 < 22880 ∧ iu1 < 22880 ∧ Check.adjIdx 0 iv1 = true ∧
    Check.actIdx LevelTwoData.w0Arr iv1 = 0 ∧
    Check.actIdx Q3ATitsData.tau0Arr 0 = iv1 ∧ Check.actIdx Q3ATitsData.tau0Arr iv1 = 0 ∧
    Check.actIdx Q3ATitsData.tau0Arr iu0 = iu0 ∧
    Check.actIdx Q3ATitsData.rho0Arr 0 = iv1 ∧ Check.actIdx Q3ATitsData.rho0Arr iu0 = 0 ∧
    Check.actIdx ModelGroupsData.s1Arr 0 = 0 ∧ Check.actIdx ModelGroupsData.s1Arr iu1 = iv1 ∧
    Check.actIdx ModelGroupsData.s2Arr 0 = iv1 ∧ Check.actIdx ModelGroupsData.s2Arr iv1 = 0 ∧
    Check.actIdx ModelGroupsData.s2Arr iu1 = iu1 ∧
    (∀ k < 3, Check.actIdx (stabA k) 0 = 0 ∧ Check.actIdx (stabA k) iv1 = iv1) ∧
    eqA 1782 (compA 1782 (compA 1782 Q3ATitsData.rho0Arr
      (compA 1782 rho2A (invCand 1782 Q3ATitsData.rho0Arr))) (compA 1782 rho2A LevelTwoData.rhoArr))
      (idA 1782) = true ∧
    forestCheck = true ∧
    (∀ y < 22880, Check.adjIdx 0 y = true → Check.adjIdx iv1 y = true → opar[y]! < 22880) := by
  have h := Certificates.certificate15089
  simp only [titsCheck, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.mem_range, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, fun y hy h0 h1' => ?_⟩
  have := (allLt_iff.1 h21) y hy
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq] at this
  rcases this with (h | h) | h
  · rw [h0] at h; exact absurd h (by simp)
  · exact absurd h1' (by rw [Check.adjIdx]; simpa [Check.adjWith] using h)
  · exact h

end Check

theorem w0_mem : LevelTwoData.w0Arr ∈ gensT := by simp [gensT]
theorem tau0_mem : Q3ATitsData.tau0Arr ∈ gensT := by simp [gensT]
theorem rho0_mem : Q3ATitsData.rho0Arr ∈ gensT := by simp [gensT]
theorem s1_mem : ModelGroupsData.s1Arr ∈ gensT := by simp [gensT]
theorem s2_mem : ModelGroupsData.s2Arr ∈ gensT := by simp [gensT]
theorem stabA_mem {k : ℕ} (hk : k < 3) : stabA k ∈ gensT := by
  interval_cases k <;> simp [stabA, gensT]

section Elements

theorem rep_gensT {a : Array ℕ} (ha : a ∈ gensT) : Rep 1782 a (permC 1782 a) :=
  (rep_permC (titsCheck_parts.1 a ha).1).1

theorem permC_mem_suzM {a : Array ℕ} (ha : a ∈ gensT) : permC 1782 a ∈ suzM :=
  (mem_suzM_iff_siftA (rep_gensT ha)).1 (titsCheck_parts.1 a ha).2

@[expose] noncomputable def elt {a : Array ℕ} (ha : a ∈ gensT) : ↥suzM :=
  ⟨permC 1782 a, permC_mem_suzM ha⟩

theorem coe_elt {a : Array ℕ} (ha : a ∈ gensT) :
    (elt ha : Equiv.Perm (Fin 1782)) = permC 1782 a := rfl

end Elements

theorem triple_swap12 {α : Type*} (a b c : α) : ({b, a, c} : Set α) = {a, b, c} :=
  Set.insert_comm b a {c}

theorem triple_swap23 {α : Type*} (a b c : α) : ({a, c, b} : Set α) = {a, b, c} := by
  rw [Set.pair_comm c b]

theorem triple_cycle {α : Type*} (a b c : α) : ({b, c, a} : Set α) = {a, b, c} := by
  rw [Set.pair_comm c a, Set.insert_comm b a]

theorem conjMap_val (g : ↥suzM) (x : Vtx) :
    ModelGroups.conjMap (g : Equiv.Perm (Fin 1782)) x.1 = (g • x).1 := rfl

theorem image_val_triple (x y z : Vtx) :
    Subtype.val '' ({x, y, z} : Set Vtx) = {x.1, y.1, z.1} := by
  simp [Set.image_insert_eq, Set.image_singleton]

theorem conjMap_image_pair (g : ↥suzM) (x y : Vtx) :
    ModelGroups.conjMap (g : Equiv.Perm (Fin 1782)) '' {x.1, y.1} = {(g • x).1, (g • y).1} := by
  simp [Set.image_insert_eq, Set.image_singleton, conjMap_val]

theorem conjMap_image_triple (g : ↥suzM) (x y z : Vtx) :
    ModelGroups.conjMap (g : Equiv.Perm (Fin 1782)) '' {x.1, y.1, z.1} =
      {(g • x).1, (g • y).1, (g • z).1} := by
  simp [Set.image_insert_eq, Set.image_singleton, conjMap_val]

theorem mem_pairStab_iff (g : ↥suzM) (x y : Vtx) :
    (g : Equiv.Perm (Fin 1782)) ∈ ModelGroups.conjSetStab ({x.1, y.1} : Set _) ↔
      (g • x = x ∧ g • y = y) ∨ (g • x = y ∧ g • y = x) := by
  rw [ModelGroups.mem_conjSetStab, conjMap_image_pair, Set.pair_eq_pair_iff]
  simp only [← Subtype.ext_iff]

theorem smul_mem_of_mem_triStab {g : ↥suzM} {x y z : Vtx}
    (hg : (g : Equiv.Perm (Fin 1782)) ∈ ModelGroups.conjSetStab ({x.1, y.1, z.1} : Set _)) :
    g • x = x ∨ g • x = y ∨ g • x = z := by
  rw [ModelGroups.mem_conjSetStab, conjMap_image_triple] at hg
  have h : (g • x).1 ∈ ({(g • x).1, (g • y).1, (g • z).1} : Set (Subgroup _)) := by simp
  rw [hg] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, ← Subtype.ext_iff] at h
  exact h

theorem mem_triStab_of_perm {g : ↥suzM} {x y z : Vtx}
    (h : ({g • x, g • y, g • z} : Set Vtx) = {x, y, z}) :
    (g : Equiv.Perm (Fin 1782)) ∈ ModelGroups.conjSetStab ({x.1, y.1, z.1} : Set _) := by
  rw [ModelGroups.mem_conjSetStab, conjMap_image_triple, ← image_val_triple, ← image_val_triple,
    h]

section Data

variable
  (L : IndexLayer)

theorem smul_vtx_gen {a : Array ℕ} (ha : a ∈ gensT) {i : ℕ} (hi : i < 22880) :
    elt ha • L.vtx i = L.vtx (Check.actIdx a i) :=
  (L.smul_vtx (g := elt ha) (rep_gensT ha) hi).1

theorem exists_stab_of_reached : ∀ (n y : ℕ), odep[y]! = n → y < 22880 → opar[y]! < 22880 →
    ∃ h : ↥suzM, h • v0 = v0 ∧ h • L.vtx iv1 = L.vtx iv1 ∧
      (h • L.vtx iu0 = L.vtx y ∨ h • L.vtx iu1 = L.vtx y) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hstab, -, hfor, -⟩ := titsCheck_parts
  simp only [forestCheck, Bool.and_eq_true, beq_iff_eq] at hfor
  obtain ⟨⟨⟨-, -⟩, -⟩, hall⟩ := hfor
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro y hdep hy hr
    have hc := (allLt_iff.1 hall) y hy
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    rcases hc with hc | hc
    · omega
    · by_cases h0 : odep[y]! = 0
      · rw [ite_eq_left (by simpa using h0)] at hc
        simp only [Bool.or_eq_true, beq_iff_eq] at hc
        refine ⟨1, one_smul _ _, one_smul _ _, ?_⟩
        rcases hc with rfl | rfl
        · exact Or.inl (one_smul _ _)
        · exact Or.inr (one_smul _ _)
      · rw [ite_eq_right (by simpa using h0)] at hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        obtain ⟨⟨⟨⟨hp, hpp⟩, hd⟩, hl⟩, he⟩ := hc
        obtain ⟨h, h0', h1', h2'⟩ := ih _ (hdep ▸ hd) _ rfl hp hpp
        have hs := hstab _ hl
        set g := elt (stabA_mem hl)
        have hgv0 : g • v0 = v0 := by
          rw [← L.vtx_zero, smul_vtx_gen L (stabA_mem hl) (by norm_num), hs.1]
        have hgv1 : g • L.vtx iv1 = L.vtx iv1 := by
          rw [smul_vtx_gen L (stabA_mem hl) titsCheck_parts.2.2.1, hs.2]
        have hgy : g • L.vtx opar[y]! = L.vtx y := by
          rw [smul_vtx_gen L (stabA_mem hl) hp, he]
        refine ⟨g * h, by rw [mul_smul, h0', hgv0], by rw [mul_smul, h1', hgv1], ?_⟩
        rcases h2' with h2' | h2'
        · exact Or.inl (by rw [mul_smul, h2', hgy])
        · exact Or.inr (by rw [mul_smul, h2', hgy])

include L in
theorem smul_v0_gen {a : Array ℕ} (ha : a ∈ gensT) :
    elt ha • v0 = L.vtx (Check.actIdx a 0) := by
  rw [← L.vtx_zero, smul_vtx_gen L ha (by norm_num)]

theorem val_v1 : (L.vtx iv1).1 = zpowers ModelGroups.rho2 := by
  have h := smul_v0_gen L w0_mem
  rw [show Check.actIdx LevelTwoData.w0Arr 0 = iv1 from rfl] at h
  rw [← h, coe_smul_v0]
  rfl

theorem val_u0 : (L.vtx iu0).1 = zpowers (ModelGroups.rho2 * Model.rho1) := by
  obtain ⟨hg, hr, h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ := titsCheck_parts
  have h := smul_vtx_gen L rho0_mem h1
  rw [show Check.actIdx Q3ATitsData.rho0Arr iv1 = iu0 from rfl] at h
  rw [← h, ← conjMap_val, val_v1, ModelGroups.conjMap_zpowers]
  have hw := rep_permC (hg _ w0_mem).1
  have hρ := rep_permC (hg _ rho0_mem).1
  have hr1 := (rep_permC hr).1
  have e2 : ModelGroups.rho2 = permC 1782 LevelTwoData.w0Arr *
      (permC 1782 LevelTwoData.rhoArr * (permC 1782 LevelTwoData.w0Arr)⁻¹) := by
    rw [ModelGroups.rho2, mul_assoc]
    rfl
  have hρ2 : Rep 1782 rho2A ModelGroups.rho2 := by
    rw [e2]
    exact rep_compA hw.1 (rep_compA hr1 hw.2)
  have hprod := eq_of_eqA (rep_compA (rep_compA hρ.1 (rep_compA hρ2 hρ.2))
    (rep_compA hρ2 hr1)) rep_idA he
  have : permC 1782 Q3ATitsData.rho0Arr * ModelGroups.rho2 *
      (permC 1782 Q3ATitsData.rho0Arr)⁻¹ = (ModelGroups.rho2 * Model.rho1)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, show Model.rho1 = permC 1782 LevelTwoData.rhoArr from rfl]
    simpa [mul_assoc] using hprod
  rw [coe_elt, this, zpowers_inv]

theorem exists_titsData (hconn : a4Graph.Preconnected) (htri0 : Triangulable a4Graph)
    (hloc0 : ∀ y, a4Graph.Adj v0 y → ∃ g : ↥suzM, g • v0 = v0 ∧ g • L.vtx iv1 = y) :
    ∃ D : TitsDataBy a4Graph triT ↥suzM (Fin 2),
      D.v = v0 ∧ D.w = L.vtx iv1 ∧
      D.Xv = ModelGroups.Nrho1.subgroupOf suzM ∧ D.Xe = ModelGroups.pairStab.subgroupOf suzM ∧
      D.Xt 0 = (ModelGroups.triStab (ModelGroups.rho2 * Model.rho1)).subgroupOf suzM ∧
      D.Xt 1 = (closure {ModelGroups.s1, ModelGroups.s2}).subgroupOf suzM := by
  obtain ⟨-, -, h1, h2, h3, hadj01, hw0, ht0, ht1, htu, hr0, hru, hs10, hs1u, hs20, hs21, hs2u,
    -, -, -, hcov⟩ := titsCheck_parts
  set v1 := L.vtx iv1 with hv1
  set u0 := L.vtx iu0 with hu0
  set u1 := L.vtx iu1 with hu1
  have hv0z : v0 = L.vtx 0 := L.vtx_zero.symm
  set W := elt w0_mem
  set τ := elt tau0_mem
  set ρ := elt rho0_mem
  set σ₁ := elt s1_mem
  set σ₂ := elt s2_mem
  have hWv0 : W • v0 = v1 := smul_v0_gen L w0_mem
  have hWv1 : W • v1 = v0 := by rw [smul_vtx_gen L w0_mem h1, hw0, hv0z]
  have hτv0 : τ • v0 = v1 := by rw [smul_v0_gen L tau0_mem, ht0]
  have hτv1 : τ • v1 = v0 := by rw [smul_vtx_gen L tau0_mem h1, ht1, hv0z]
  have hτu0 : τ • u0 = u0 := by rw [smul_vtx_gen L tau0_mem h2, htu]
  have hρv0 : ρ • v0 = v1 := by rw [smul_v0_gen L rho0_mem, hr0]
  have hρv1 : ρ • v1 = u0 := smul_vtx_gen L rho0_mem h1
  have hρu0 : ρ • u0 = v0 := by rw [smul_vtx_gen L rho0_mem h2, hru, hv0z]
  have hσ₁v0 : σ₁ • v0 = v0 := by rw [smul_v0_gen L s1_mem, hs10, hv0z]
  have hσ₁v1 : σ₁ • v1 = u1 := smul_vtx_gen L s1_mem h1
  have hσ₁u1 : σ₁ • u1 = v1 := by rw [smul_vtx_gen L s1_mem h3, hs1u]
  have hσ₂v0 : σ₂ • v0 = v1 := by rw [smul_v0_gen L s2_mem, hs20]
  have hσ₂v1 : σ₂ • v1 = v0 := by rw [smul_vtx_gen L s2_mem h1, hs21, hv0z]
  have hσ₂u1 : σ₂ • u1 = u1 := by rw [smul_vtx_gen L s2_mem h3, hs2u]
  have hvw : a4Graph.Adj v0 v1 := by
    rw [hv0z]
    exact (L.adj_vtx_iff (by norm_num) h1).2 hadj01
  have hT1 : closure {ModelGroups.s1, ModelGroups.s2} ≤
      (MulAction.stabilizer ↥suzM ({v0, v1, u1} : Set Vtx)).map suzM.subtype := by
    rw [closure_le]
    have hst : ∀ g : ↥suzM, ({g • v0, g • v1, g • u1} : Set Vtx) = {v0, v1, u1} →
        g ∈ MulAction.stabilizer ↥suzM ({v0, v1, u1} : Set Vtx) := fun g hg => by
      rw [MulAction.mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_insert,
        Set.smul_set_singleton, hg]
    rintro _ (rfl | rfl)
    · exact ⟨σ₁, hst σ₁ (by rw [hσ₁v0, hσ₁v1, hσ₁u1, triple_swap23]), rfl⟩
    · exact ⟨σ₂, hst σ₂ (by rw [hσ₂v0, hσ₂v1, hσ₂u1, triple_swap12]), rfl⟩
  refine ⟨{
    v := v0
    w := v1
    u := ![u0, u1]
    Xv := ModelGroups.Nrho1.subgroupOf suzM
    Xe := ModelGroups.pairStab.subgroupOf suzM
    Xt := ![(ModelGroups.triStab (ModelGroups.rho2 * Model.rho1)).subgroupOf suzM,
      (closure {ModelGroups.s1, ModelGroups.s2}).subgroupOf suzM]
    hadj := fun g _ _ h => a4Graph_adj_smul g h
    hTinv := fun g S hS => triT_smul g S hS
    hconn := hconn
    hΓ := TriangulableBy.of_triangulable htri0 fun x y z hxy hyz hzx =>
      homotopicBy_triangle_nil hxy hyz hzx ⟨x, y, z, rfl, hxy, hyz, hzx⟩
    hvw := hvw
    hloc := hloc0
    hswap := ⟨W, hWv0, hWv1⟩
    hXv := fun g => by
      rw [mem_subgroupOf, smul_v0_eq_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, g.2⟩⟩
    hXe := fun g => by
      rw [mem_subgroupOf, ModelGroups.pairStab, mem_inf,
        show ({zpowers Model.rho1, zpowers ModelGroups.rho2} : Set _) = {v0.1, v1.1} from by
          rw [val_v1]; rfl, mem_pairStab_iff]
      exact ⟨fun h => h.1, fun h => ⟨h, g.2⟩⟩
    hXt := fun j g hg => by
      match j with
      | 0 =>
        have h' := (mem_inf.1 (mem_subgroupOf.1 hg)).1
        rw [show ({zpowers Model.rho1, zpowers ModelGroups.rho2,
          zpowers (ModelGroups.rho2 * Model.rho1)} : Set _) = {v0.1, v1.1, u0.1} from by
            rw [val_v1, val_u0]; rfl] at h'
        exact smul_mem_of_mem_triStab h'
      | 1 =>
        obtain ⟨h, hh, hhg⟩ := hT1 (mem_subgroupOf.1 hg)
        have : h = g := Subtype.ext hhg
        subst this
        have hm : h • v0 ∈ h • ({v0, v1, u1} : Set Vtx) := Set.smul_mem_smul_set (by simp)
        rw [MulAction.mem_stabilizer_iff.1 hh] at hm
        simpa using hm
    hτ := fun j => by
      match j with
      | 0 =>
        refine ⟨τ, mem_subgroupOf.2 (mem_inf.2 ⟨?_, τ.2⟩), hτv0, hτv1⟩
        rw [show ({zpowers Model.rho1, zpowers ModelGroups.rho2,
          zpowers (ModelGroups.rho2 * Model.rho1)} : Set _) = {v0.1, v1.1, u0.1} from by
            rw [val_v1, val_u0]; rfl]
        exact mem_triStab_of_perm (by rw [hτv0, hτv1, hτu0, triple_swap12])
      | 1 => exact ⟨σ₂, mem_subgroupOf.2 (subset_closure (Or.inr rfl)), hσ₂v0, hσ₂v1⟩
    hρ := fun j => by
      match j with
      | 0 =>
        refine ⟨ρ, mem_subgroupOf.2 (mem_inf.2 ⟨?_, ρ.2⟩), hρv0, hρv1, hρu0⟩
        rw [show ({zpowers Model.rho1, zpowers ModelGroups.rho2,
          zpowers (ModelGroups.rho2 * Model.rho1)} : Set _) = {v0.1, v1.1, u0.1} from by
            rw [val_v1, val_u0]; rfl]
        exact mem_triStab_of_perm (by rw [hρv0, hρv1, hρu0, triple_cycle])
      | 1 =>
        refine ⟨σ₂ * σ₁, mem_subgroupOf.2 (mul_mem (subset_closure (Or.inr rfl))
          (subset_closure (Or.inl rfl))), ?_, ?_, ?_⟩
        · rw [mul_smul, hσ₁v0, hσ₂v0]
        · show (σ₂ * σ₁) • v1 = u1
          rw [mul_smul, hσ₁v1, hσ₂u1]
        · show (σ₂ * σ₁) • u1 = v0
          rw [mul_smul, hσ₁u1, hσ₂v1]
    htri := fun y₁ y₂ hy₁ hy₁₂ hy₂ _ => by
      obtain ⟨g, hg0, hg1⟩ := hloc0 y₁ hy₁
      set z := g⁻¹ • y₂
      have hz0 : a4Graph.Adj v0 z := by
        have := a4Graph_adj_smul g⁻¹ hy₂
        rw [← hg0, inv_smul_smul] at this
        exact this.symm
      have hz1 : a4Graph.Adj v1 z := by
        have := a4Graph_adj_smul g⁻¹ hy₁₂
        rwa [← hg1, inv_smul_smul] at this
      obtain ⟨k, hk, hkz⟩ := L.exists_vtx z
      have hk0 : Check.adjIdx 0 k = true := (L.adj_vtx_iff (by norm_num) hk).1 (by
        rw [L.vtx_zero, hkz]; exact hz0)
      have hk1 : Check.adjIdx iv1 k = true := (L.adj_vtx_iff h1 hk).1 (by rw [hkz]; exact hz1)
      obtain ⟨h, hh0, hh1, hh2⟩ := exists_stab_of_reached L _ k rfl hk (hcov k hk hk0 hk1)
      rcases hh2 with hh2 | hh2
      · refine ⟨0, g * h, by rw [mul_smul, hh0, hg0], by rw [mul_smul, hh1, hg1], ?_⟩
        show (g * h) • u0 = y₂
        rw [mul_smul, hh2, hkz, smul_inv_smul]
      · refine ⟨1, g * h, by rw [mul_smul, hh0, hg0], by rw [mul_smul, hh1, hg1], ?_⟩
        show (g * h) • u1 = y₂
        rw [mul_smul, hh2, hkz, smul_inv_smul] }, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Data

end CFSG.Sporadic.SuzRecog.Q3A
