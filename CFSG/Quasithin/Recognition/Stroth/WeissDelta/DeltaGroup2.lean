module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.DeltaGroup

public section

open Classical CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth
  CFSG.Geometry.GeneralizedPolygons CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {X : Type} [Group X] {P1 P2 : Subgroup X} {Y : Type} [Group Y]
variable {c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y}
variable {Good : ∀ s : ℕ, GPath c.graph s → Prop} {n : ℕ}

theorem hatX_apply_of_dist_le (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) {u : ↥(edgeBall (n - 1) c)}
    (hu : c.graph.dist c.xv (u : c.Γ) ≤ n - 1) :
    ((hatX hn hgirth hG a u : ↥(edgeBall (n - 1) c)) : c.Γ) =
      (a : c.G0) • (u : c.Γ) := by
  rw [hatX_apply, hatFun_of_dist_le hu]

theorem hatY_apply_of_dist_le (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) {u : ↥(edgeBall (n - 1) c)}
    (hu : c.graph.dist c.lv (u : c.Γ) ≤ n - 1) :
    ((hatY hn hgirth hG a u : ↥(edgeBall (n - 1) c)) : c.Γ) =
      (a : c.G0) • (u : c.Γ) := by
  rw [hatY_apply, hatFun_of_dist_le hu]

theorem hatX_inv (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) :
    (hatX hn hgirth hG a)⁻¹ = hatX hn hgirth hG a⁻¹ :=
  hatPerm_inv hn hgirth hG c.lv (Or.inl ⟨rfl, rfl⟩) a

theorem hatY_inv (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) :
    (hatY hn hgirth hG a)⁻¹ = hatY hn hgirth hG a⁻¹ :=
  hatPerm_inv hn hgirth hG c.xv (Or.inr ⟨rfl, rfl⟩) a

@[expose] noncomputable def hatXHom (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    ↥(MulAction.stabilizer c.G0 c.xv) →* Equiv.Perm ↥(edgeBall (n - 1) c) where
  toFun a := hatX hn hgirth hG a
  map_one' := by
    refine eq_one_of_fix_of_delta hn hgirth hG hdeg (z := c.xv) (z' := c.lv)
      (Or.inl ⟨rfl, rfl⟩) (hatX_mem_deltaAut hn hgirth hG 1) ?_
    intro u hu
    apply Subtype.ext
    rw [hatX_apply_of_dist_le hn hgirth hG (a := 1) hu]
    exact one_smul _ _
  map_mul' a b := by
    have hconn : c.graph.Connected := CosetGeom.connected rfl
    have hfix : ∀ u : ↥(edgeBall (n - 1) c), c.graph.dist c.xv (u : c.Γ) ≤ n - 1 →
        ((hatX hn hgirth hG (a * b) *
          (hatX hn hgirth hG a * hatX hn hgirth hG b)⁻¹) u) = u := by
      intro u hu
      set u1 : ↥(edgeBall (n - 1) c) := ((hatX hn hgirth hG a)⁻¹) u with hu1def
      set u2 : ↥(edgeBall (n - 1) c) := ((hatX hn hgirth hG b)⁻¹) u1 with hu2def
      have hu1 : c.graph.dist c.xv (u1 : c.Γ) ≤ n - 1 := by
        rw [hu1def, hatX_inv,
          hatX_apply_of_dist_le hn hgirth hG (a := a⁻¹) hu,
          GPath.dist_smul_fix hconn (MulAction.mem_stabilizer_iff.mp (a⁻¹).2)]
        exact hu
      have hu2 : c.graph.dist c.xv (u2 : c.Γ) ≤ n - 1 := by
        rw [hu2def, hatX_inv,
          hatX_apply_of_dist_le hn hgirth hG (a := b⁻¹) hu1,
          GPath.dist_smul_fix hconn (MulAction.mem_stabilizer_iff.mp (b⁻¹).2)]
        exact hu1
      have hcalc : ((hatX hn hgirth hG (a * b) *
          (hatX hn hgirth hG a * hatX hn hgirth hG b)⁻¹) u) =
          hatX hn hgirth hG (a * b) u2 := by
        rw [Equiv.Perm.mul_apply, mul_inv_rev, Equiv.Perm.mul_apply, hu2def, hu1def]
      rw [hcalc]
      apply Subtype.ext
      rw [hatX_apply_of_dist_le hn hgirth hG (a := a * b) hu2]
      have h1 : (u1 : c.Γ) = ((a⁻¹ : ↥(MulAction.stabilizer c.G0 c.xv)) : c.G0) • (u : c.Γ) := by
        rw [hu1def, hatX_inv, hatX_apply_of_dist_le hn hgirth hG (a := a⁻¹) hu]
      have h2 : (u2 : c.Γ) =
          ((b⁻¹ : ↥(MulAction.stabilizer c.G0 c.xv)) : c.G0) • (u1 : c.Γ) := by
        rw [hu2def, hatX_inv, hatX_apply_of_dist_le hn hgirth hG (a := b⁻¹) hu1]
      rw [h2, h1, ← mul_smul, ← mul_smul]
      have hcoe : (((a * b : ↥(MulAction.stabilizer c.G0 c.xv)) : c.G0) *
          ((b⁻¹ : ↥(MulAction.stabilizer c.G0 c.xv)) : c.G0)) *
            ((a⁻¹ : ↥(MulAction.stabilizer c.G0 c.xv)) : c.G0) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        group
      rw [hcoe, one_smul]
    have hmem : hatX hn hgirth hG (a * b) *
        (hatX hn hgirth hG a * hatX hn hgirth hG b)⁻¹ ∈ deltaAut c Good n := by
      refine (deltaAut c Good n).mul_mem (hatX_mem_deltaAut hn hgirth hG (a * b)) ?_
      exact (deltaAut c Good n).inv_mem ((deltaAut c Good n).mul_mem
        (hatX_mem_deltaAut hn hgirth hG a) (hatX_mem_deltaAut hn hgirth hG b))
    have hone := eq_one_of_fix_of_delta hn hgirth hG hdeg (z := c.xv) (z' := c.lv)
      (Or.inl ⟨rfl, rfl⟩) hmem hfix
    calc hatX hn hgirth hG (a * b)
        = (hatX hn hgirth hG (a * b) *
            (hatX hn hgirth hG a * hatX hn hgirth hG b)⁻¹) *
            (hatX hn hgirth hG a * hatX hn hgirth hG b) := by group
      _ = 1 * (hatX hn hgirth hG a * hatX hn hgirth hG b) := by rw [hone]
      _ = hatX hn hgirth hG a * hatX hn hgirth hG b := one_mul _

@[expose] noncomputable def hatYHom (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    ↥(MulAction.stabilizer c.G0 c.lv) →* Equiv.Perm ↥(edgeBall (n - 1) c) where
  toFun a := hatY hn hgirth hG a
  map_one' := by
    refine eq_one_of_fix_of_delta hn hgirth hG hdeg (z := c.lv) (z' := c.xv)
      (Or.inr ⟨rfl, rfl⟩) (hatY_mem_deltaAut hn hgirth hG 1) ?_
    intro u hu
    apply Subtype.ext
    rw [hatY_apply_of_dist_le hn hgirth hG (a := 1) hu]
    exact one_smul _ _
  map_mul' a b := by
    have hconn : c.graph.Connected := CosetGeom.connected rfl
    have hfix : ∀ u : ↥(edgeBall (n - 1) c), c.graph.dist c.lv (u : c.Γ) ≤ n - 1 →
        ((hatY hn hgirth hG (a * b) *
          (hatY hn hgirth hG a * hatY hn hgirth hG b)⁻¹) u) = u := by
      intro u hu
      set u1 : ↥(edgeBall (n - 1) c) := ((hatY hn hgirth hG a)⁻¹) u with hu1def
      set u2 : ↥(edgeBall (n - 1) c) := ((hatY hn hgirth hG b)⁻¹) u1 with hu2def
      have hu1 : c.graph.dist c.lv (u1 : c.Γ) ≤ n - 1 := by
        rw [hu1def, hatY_inv,
          hatY_apply_of_dist_le hn hgirth hG (a := a⁻¹) hu,
          GPath.dist_smul_fix hconn (MulAction.mem_stabilizer_iff.mp (a⁻¹).2)]
        exact hu
      have hu2 : c.graph.dist c.lv (u2 : c.Γ) ≤ n - 1 := by
        rw [hu2def, hatY_inv,
          hatY_apply_of_dist_le hn hgirth hG (a := b⁻¹) hu1,
          GPath.dist_smul_fix hconn (MulAction.mem_stabilizer_iff.mp (b⁻¹).2)]
        exact hu1
      have hcalc : ((hatY hn hgirth hG (a * b) *
          (hatY hn hgirth hG a * hatY hn hgirth hG b)⁻¹) u) =
          hatY hn hgirth hG (a * b) u2 := by
        rw [Equiv.Perm.mul_apply, mul_inv_rev, Equiv.Perm.mul_apply, hu2def, hu1def]
      rw [hcalc]
      apply Subtype.ext
      rw [hatY_apply_of_dist_le hn hgirth hG (a := a * b) hu2]
      have h1 : (u1 : c.Γ) = ((a⁻¹ : ↥(MulAction.stabilizer c.G0 c.lv)) : c.G0) • (u : c.Γ) := by
        rw [hu1def, hatY_inv, hatY_apply_of_dist_le hn hgirth hG (a := a⁻¹) hu]
      have h2 : (u2 : c.Γ) =
          ((b⁻¹ : ↥(MulAction.stabilizer c.G0 c.lv)) : c.G0) • (u1 : c.Γ) := by
        rw [hu2def, hatY_inv, hatY_apply_of_dist_le hn hgirth hG (a := b⁻¹) hu1]
      rw [h2, h1, ← mul_smul, ← mul_smul]
      have hcoe : (((a * b : ↥(MulAction.stabilizer c.G0 c.lv)) : c.G0) *
          ((b⁻¹ : ↥(MulAction.stabilizer c.G0 c.lv)) : c.G0)) *
            ((a⁻¹ : ↥(MulAction.stabilizer c.G0 c.lv)) : c.G0) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
        group
      rw [hcoe, one_smul]
    have hmem : hatY hn hgirth hG (a * b) *
        (hatY hn hgirth hG a * hatY hn hgirth hG b)⁻¹ ∈ deltaAut c Good n := by
      refine (deltaAut c Good n).mul_mem (hatY_mem_deltaAut hn hgirth hG (a * b)) ?_
      exact (deltaAut c Good n).inv_mem ((deltaAut c Good n).mul_mem
        (hatY_mem_deltaAut hn hgirth hG a) (hatY_mem_deltaAut hn hgirth hG b))
    have hone := eq_one_of_fix_of_delta hn hgirth hG hdeg (z := c.lv) (z' := c.xv)
      (Or.inr ⟨rfl, rfl⟩) hmem hfix
    calc hatY hn hgirth hG (a * b)
        = (hatY hn hgirth hG (a * b) *
            (hatY hn hgirth hG a * hatY hn hgirth hG b)⁻¹) *
            (hatY hn hgirth hG a * hatY hn hgirth hG b) := by group
      _ = 1 * (hatY hn hgirth hG a * hatY hn hgirth hG b) := by rw [hone]
      _ = hatY hn hgirth hG a * hatY hn hgirth hG b := one_mul _

theorem hatXHom_apply (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) :
    hatXHom hn hgirth hG hdeg a = hatX hn hgirth hG a := rfl

theorem hatYHom_apply (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) :
    hatYHom hn hgirth hG hdeg a = hatY hn hgirth hG a := rfl

theorem hatXHom_injective (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) (hW : WeissFree c.G0 c.graph n)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    Function.Injective (hatXHom hn hgirth hG hdeg) := by
  intro a b hab
  have hhom : hatXHom hn hgirth hG hdeg (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hfix : ∀ w : c.Γ, c.graph.dist c.xv w ≤ n - 1 →
      ((a * b⁻¹ : ↥(MulAction.stabilizer c.G0 c.xv)) : c.G0) • w = w := by
    intro w hw
    have hwmem : w ∈ edgeBall (n - 1) c :=
      (mem_edgeBall_iff (Or.inl ⟨rfl, rfl⟩) (n - 1) w).mpr (Or.inl hw)
    have h1 : ((hatX hn hgirth hG (a * b⁻¹)) ⟨w, hwmem⟩ : ↥(edgeBall (n - 1) c)) =
        ⟨w, hwmem⟩ := by
      rw [← hatXHom_apply hn hgirth hG hdeg (a * b⁻¹), hhom]
      rfl
    have h2 := congrArg (fun x : ↥(edgeBall (n - 1) c) => (x : c.Γ)) h1
    rw [hatX_apply_of_dist_le hn hgirth hG (a := a * b⁻¹) hw] at h2
    exact h2
  have hcab : (a * b⁻¹ : ↥(MulAction.stabilizer c.G0 c.xv)) = 1 := by
    apply Subtype.ext
    exact eq_one_of_fix_ball (H := c.G0) (Γ := c.graph) hn hW hdeg
      (x := c.xv) ⟨c.lv, adj_base_edge (c := c) (z := c.xv) (z' := c.lv) (Or.inl ⟨rfl, rfl⟩)⟩ hfix
  have h : a * b⁻¹ * b = 1 * b := congrArg (fun x : ↥(MulAction.stabilizer c.G0 c.xv) =>
    x * b) hcab
  simpa [mul_assoc] using h

theorem hatYHom_injective (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) (hW : WeissFree c.G0 c.graph n)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    Function.Injective (hatYHom hn hgirth hG hdeg) := by
  intro a b hab
  have hhom : hatYHom hn hgirth hG hdeg (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hfix : ∀ w : c.Γ, c.graph.dist c.lv w ≤ n - 1 →
      ((a * b⁻¹ : ↥(MulAction.stabilizer c.G0 c.lv)) : c.G0) • w = w := by
    intro w hw
    have hwmem : w ∈ edgeBall (n - 1) c :=
      (mem_edgeBall_iff (Or.inl ⟨rfl, rfl⟩) (n - 1) w).mpr (Or.inr hw)
    have h1 : ((hatY hn hgirth hG (a * b⁻¹)) ⟨w, hwmem⟩ : ↥(edgeBall (n - 1) c)) =
        ⟨w, hwmem⟩ := by
      rw [← hatYHom_apply hn hgirth hG hdeg (a * b⁻¹), hhom]
      rfl
    have h2 := congrArg (fun x : ↥(edgeBall (n - 1) c) => (x : c.Γ)) h1
    rw [hatY_apply_of_dist_le hn hgirth hG (a := a * b⁻¹) hw] at h2
    exact h2
  have hcab : (a * b⁻¹ : ↥(MulAction.stabilizer c.G0 c.lv)) = 1 := by
    apply Subtype.ext
    exact eq_one_of_fix_ball (H := c.G0) (Γ := c.graph) hn hW hdeg
      (x := c.lv) ⟨c.xv, adj_base_edge (c := c) (z := c.lv) (z' := c.xv) (Or.inr ⟨rfl, rfl⟩)⟩ hfix
  have h : a * b⁻¹ * b = 1 * b := congrArg (fun x : ↥(MulAction.stabilizer c.G0 c.lv) =>
    x * b) hcab
  simpa [mul_assoc] using h

@[expose] noncomputable def deltaGroup (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    Subgroup (Equiv.Perm ↥(edgeBall (n - 1) c)) :=
  Subgroup.closure ((hatXHom hn hgirth hG hdeg).range ∪ (hatYHom hn hgirth hG hdeg).range)

theorem deltaGroup_le_deltaAut (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    deltaGroup hn hgirth hG hdeg ≤ deltaAut c Good n := by
  rw [deltaGroup, Subgroup.closure_le]
  rintro f (hf | hf)
  · obtain ⟨a, rfl⟩ := hf
    exact hatX_mem_deltaAut hn hgirth hG a
  · obtain ⟨a, rfl⟩ := hf
    exact hatY_mem_deltaAut hn hgirth hG a

@[expose] instance graphAction_deltaGroup (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    GraphAction ↥(deltaGroup hn hgirth hG hdeg) (delta c Good n) where
  adj_smul g u v := by
    have hg := deltaGroup_le_deltaAut hn hgirth hG hdeg g.2
    have h := (mem_deltaAut_iff.mp hg) u v
    simpa only [Subgroup.smul_def, Equiv.Perm.smul_def] using h

instance finite_deltaGroup [Finite Y] (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    Finite ↥(deltaGroup hn hgirth hG hdeg) :=
  Subtype.finite

instance faithfulSMul_deltaGroup (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    FaithfulSMul ↥(deltaGroup hn hgirth hG hdeg) ↥(edgeBall (n - 1) c) :=
  Subgroup.instFaithfulSMulSubtypeMem _

@[expose] def deltaXv (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (n : ℕ) :
    ↥(edgeBall (n - 1) c) :=
  ⟨c.xv, Or.inl (by simp)⟩

@[expose] def deltaLv (c : (RankTwoAmalgam.ofSubgroups P1 P2).Completion Y) (n : ℕ) :
    ↥(edgeBall (n - 1) c) :=
  ⟨c.lv, Or.inr (by simp)⟩

theorem delta_adj_deltaXv_deltaLv (hn : 3 ≤ n) :
    (delta c Good n).Adj (deltaXv c n) (deltaLv c n) := by
  have hne : (deltaXv c n : ↥(edgeBall (n - 1) c)) ≠ deltaLv c n := by
    intro h
    exact (adj_base_edge (Or.inl ⟨rfl, rfl⟩)).ne (congrArg Subtype.val h)
  rw [delta_unfold]
  refine ⟨hne, Or.inl (Or.inl ⟨adj_base_edge (Or.inl ⟨rfl, rfl⟩), Or.inl ?_⟩)⟩
  exact Or.inl (by simp [deltaXv])

@[expose] noncomputable def f1Stab : ↥P1 →* ↥(MulAction.stabilizer c.G0 c.xv) :=
  (RankTwoAmalgam.Completion.f1 (c := c)).codRestrict _
    (fun a => MulAction.mem_stabilizer_iff.mpr (RankTwoAmalgam.Completion.f1_smul_xv a))

@[expose] noncomputable def f2Stab : ↥P2 →* ↥(MulAction.stabilizer c.G0 c.lv) :=
  (RankTwoAmalgam.Completion.f2 (c := c)).codRestrict _
    (fun a => MulAction.mem_stabilizer_iff.mpr (RankTwoAmalgam.Completion.f2_smul_lv a))

@[expose] noncomputable def psiOne (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    ↥P1 →* ↥(deltaGroup hn hgirth hG hdeg) :=
  ((hatXHom hn hgirth hG hdeg).comp (f1Stab (c := c))).codRestrict _
    (fun a => Subgroup.subset_closure (Or.inl ⟨f1Stab (c := c) a, rfl⟩))

@[expose] noncomputable def psiTwo (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    ↥P2 →* ↥(deltaGroup hn hgirth hG hdeg) :=
  ((hatYHom hn hgirth hG hdeg).comp (f2Stab (c := c))).codRestrict _
    (fun a => Subgroup.subset_closure (Or.inr ⟨f2Stab (c := c) a, rfl⟩))

theorem psiOne_apply (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (a : ↥P1) :
    ((psiOne hn hgirth hG hdeg a : ↥(deltaGroup hn hgirth hG hdeg)) :
        Equiv.Perm ↥(edgeBall (n - 1) c)) =
      hatX hn hgirth hG (f1Stab (c := c) a) := rfl

theorem psiTwo_apply (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (a : ↥P2) :
    ((psiTwo hn hgirth hG hdeg a : ↥(deltaGroup hn hgirth hG hdeg)) :
        Equiv.Perm ↥(edgeBall (n - 1) c)) =
      hatY hn hgirth hG (f2Stab (c := c) a) := rfl

theorem hatX_smul_deltaXv (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.xv)) :
    hatX hn hgirth hG a (deltaXv c n) = deltaXv c n := by
  apply Subtype.ext
  rw [hatX_apply_of_dist_le hn hgirth hG (a := a) (u := deltaXv c n) (by simp [deltaXv])]
  exact MulAction.mem_stabilizer_iff.mp a.2

theorem hatY_smul_deltaLv (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (a : ↥(MulAction.stabilizer c.G0 c.lv)) :
    hatY hn hgirth hG a (deltaLv c n) = deltaLv c n := by
  apply Subtype.ext
  rw [hatY_apply_of_dist_le hn hgirth hG (a := a) (u := deltaLv c n) (by simp [deltaLv])]
  exact MulAction.mem_stabilizer_iff.mp a.2

theorem psiOne_smul_deltaXv (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (a : ↥P1) :
    (psiOne hn hgirth hG hdeg a) • (deltaXv c n) = deltaXv c n := by
  rw [Subgroup.smul_def]
  change (hatX hn hgirth hG (f1Stab (c := c) a)) (deltaXv c n) = deltaXv c n
  exact hatX_smul_deltaXv hn hgirth hG (f1Stab (c := c) a)

theorem psiTwo_smul_deltaLv (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (a : ↥P2) :
    (psiTwo hn hgirth hG hdeg a) • (deltaLv c n) = deltaLv c n := by
  rw [Subgroup.smul_def]
  change (hatY hn hgirth hG (f2Stab (c := c) a)) (deltaLv c n) = deltaLv c n
  exact hatY_smul_deltaLv hn hgirth hG (f2Stab (c := c) a)

theorem psiOne_injective (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) (hW : WeissFree c.G0 c.graph n)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (hc : c.IsFaithful) : Function.Injective (psiOne hn hgirth hG hdeg) := by
  intro a b hab
  have h1 : f1Stab (c := c) a = f1Stab (c := c) b := by
    apply hatXHom_injective hn hgirth hG hW hdeg
    have h := congrArg (fun x : ↥(deltaGroup hn hgirth hG hdeg) =>
      (x : Equiv.Perm ↥(edgeBall (n - 1) c))) hab
    simpa only [psiOne_apply, hatXHom_apply] using h
  have h2 : ((RankTwoAmalgam.Completion.f1 (c := c) a : c.G0) : Y) =
      ((RankTwoAmalgam.Completion.f1 (c := c) b : c.G0) : Y) :=
    congrArg (fun x : c.G0 => (x : Y)) (congrArg Subtype.val h1)
  exact hc.1 h2

theorem psiTwo_injective (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good) (hW : WeissFree c.G0 c.graph n)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w)
    (hc : c.IsFaithful) : Function.Injective (psiTwo hn hgirth hG hdeg) := by
  intro a b hab
  have h1 : f2Stab (c := c) a = f2Stab (c := c) b := by
    apply hatYHom_injective hn hgirth hG hW hdeg
    have h := congrArg (fun x : ↥(deltaGroup hn hgirth hG hdeg) =>
      (x : Equiv.Perm ↥(edgeBall (n - 1) c))) hab
    simpa only [psiTwo_apply, hatYHom_apply] using h
  have h2 : ((RankTwoAmalgam.Completion.f2 (c := c) a : c.G0) : Y) =
      ((RankTwoAmalgam.Completion.f2 (c := c) b : c.G0) : Y) :=
    congrArg (fun x : c.G0 => (x : Y)) (congrArg Subtype.val h1)
  exact hc.2.2 h2

theorem psiOne_range_le_stabilizer (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    (psiOne hn hgirth hG hdeg).range ≤
      MulAction.stabilizer ↥(deltaGroup hn hgirth hG hdeg) (deltaXv c n) := by
  rintro g ⟨a, rfl⟩
  exact MulAction.mem_stabilizer_iff.mpr (psiOne_smul_deltaXv hn hgirth hG hdeg a)

theorem psiTwo_range_le_stabilizer (hn : 3 ≤ n)
    (hgirth : ((2 * n + 2 : ℕ) : ℕ∞) ≤ c.graph.egirth)
    (hG : GoodPathSystem c.G0 c.graph n Good)
    (hdeg : ∀ v w : c.Γ, c.graph.Adj v w → ∃ u, c.graph.Adj v u ∧ u ≠ w) :
    (psiTwo hn hgirth hG hdeg).range ≤
      MulAction.stabilizer ↥(deltaGroup hn hgirth hG hdeg) (deltaLv c n) := by
  rintro g ⟨a, rfl⟩
  exact MulAction.mem_stabilizer_iff.mpr (psiTwo_smul_deltaLv hn hgirth hG hdeg a)

end CFSG.Quasithin.Stroth.WeissDelta

end
