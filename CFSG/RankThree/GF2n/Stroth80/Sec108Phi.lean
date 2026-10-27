module

public import CFSG.RankThree.GF2n.Stroth80.Sec108End
public import CFSG.RankThree.GF2n.Stroth80.Sec108Ncard

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

noncomputable def Sec108Data.bV (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Module.Basis (Fin 3) AM.K ↥(AM.Vsp hc t) :=
  (SLMNat.exists_basis_statedSL D.h34 D.hspread D.hyp D.good.1 D.slm (by norm_num) AM.glob AM.φ
    AM.φ_π).choose

theorem Sec108Data.bV_spec (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (A : Matrix.SpecialLinearGroup (Fin 3) AM.K) :
    ∃ r ∈ Rt M (LB M Q B) t ⊓ Subgroup.centralizer ({t} : Set G), ∃ hr : r ∈ H0 M Z,
      ∀ j, AM.φ ⟨r, hr⟩ (D.bV AM j) =
        ∑ i, (A : Matrix (Fin 3) (Fin 3) AM.K) i j • (D.bV AM i : AM.M₀.E) :=
  (SLMNat.exists_basis_statedSL D.h34 D.hspread D.hyp D.good.1 D.slm (by norm_num) AM.glob AM.φ
    AM.φ_π).choose_spec A

private theorem B_antisymm (AM : Smith81.Smith23E1.ActionModel M Q Z) (x y : AM.M₀.E) :
    AM.M₀.B x y = -AM.M₀.B y x :=
  (LinearMap.IsAlt.neg AM.M₀.alt y x).symm

private theorem B_phi (AM : Smith81.Smith23E1.ActionModel M Q Z) (m : ↥(H0 M Z))
    (e f : AM.M₀.E) : AM.M₀.B (AM.φ m e) (AM.φ m f) = AM.M₀.B e f :=
  quadModel_B_iso AM.M₀ (AM.φ m) (AM.φ_Qf m) e f

theorem Sec108Data.exists_eV (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ∃ e : Fin 3 → AM.M₀.E, ∀ i j, AM.M₀.B (e i) (D.bV AM j) = if i = j then 1 else 0 := by
  have hinj : Function.Injective AM.M₀.B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro e he
    exact AM.M₀.nondeg e fun f => by rw [he, LinearMap.zero_apply]
  have hsurj : Function.Surjective AM.M₀.B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp hinj
  have hres : Function.Surjective (AM.Vsp hc t).subtype.dualMap :=
    LinearMap.dualMap_surjective_of_injective (Submodule.injective_subtype _)
  choose e he using fun i => (hres.comp hsurj) ((D.bV AM).coord i)
  refine ⟨e, fun i j => ?_⟩
  have h := congrArg (fun f : Module.Dual AM.K ↥(AM.Vsp hc t) => f (D.bV AM j)) (he i)
  simp only [Function.comp_apply, LinearMap.dualMap_apply, Submodule.subtype_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self] at h
  rw [h]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Finsupp.single_apply, hij, Ne.symm hij]

noncomputable def Sec108Data.eV (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Fin 3 → AM.M₀.E :=
  (D.exists_eV AM).choose

theorem Sec108Data.B_eV_bV (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (i j : Fin 3) : AM.M₀.B (D.eV AM i) (D.bV AM j) = if i = j then 1 else 0 :=
  (D.exists_eV AM).choose_spec i j

private theorem B_bV_eV (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (i j : Fin 3) : AM.M₀.B (D.bV AM i) (D.eV AM j) = -(if j = i then 1 else 0) := by
  rw [B_antisymm AM, D.B_eV_bV]

private theorem B_eq_zero_of_basis (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {x : AM.M₀.E}
    (h : ∀ k, AM.M₀.B (D.bV AM k) x = 0) {v : AM.M₀.E} (hv : v ∈ AM.Vsp hc t) :
    AM.M₀.B v x = 0 := by
  have hf : AM.M₀.B.flip x ∘ₗ (AM.Vsp hc t).subtype = 0 :=
    (D.bV AM).ext fun k => by simpa using h k
  simpa using LinearMap.congr_fun hf ⟨v, hv⟩

private theorem coord_Vsp (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {x : AM.M₀.E} (hx : x ∈ AM.Vsp hc t) :
    x = ∑ l, AM.M₀.B (D.eV AM l) x • (D.bV AM l : AM.M₀.E) := by
  have h := congrArg Subtype.val ((D.bV AM).sum_repr ⟨x, hx⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul, Subtype.coe_mk] at h
  have hc : ∀ l, AM.M₀.B (D.eV AM l) x = (D.bV AM).repr ⟨x, hx⟩ l := by
    intro l
    conv_lhs => rw [← h]
    simp [map_sum, map_smul, D.B_eV_bV]
  simp_rw [hc]
  exact h.symm

private theorem eq_zero_of_coord (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {x : AM.M₀.E} (hx : x ∈ AM.Vsp hc t) (h : ∀ l, AM.M₀.B (D.eV AM l) x = 0) : x = 0 := by
  rw [coord_Vsp D AM hx]
  simp [h]

theorem Sec108Data.exists_coord (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {u : AM.M₀.E} (hu : u ∈ LinearMap.range (D.nu AM)) :
    ∃ w : Fin 3 → AM.K, u - ∑ j, w j • D.nu AM (D.eV AM j) ∈ AM.Vsp hc t := by
  obtain ⟨e, rfl⟩ := hu
  refine ⟨fun j => AM.M₀.B e (D.bV AM j), ?_⟩
  have hk : ∀ k, AM.M₀.B (D.bV AM k) (e - ∑ j, AM.M₀.B e (D.bV AM j) • D.eV AM j) = 0 := by
    intro k
    rw [B_antisymm AM, map_sub, LinearMap.sub_apply, map_sum, LinearMap.sum_apply]
    simp [D.B_eV_bV]
  have hmem : e - ∑ j, AM.M₀.B e (D.bV AM j) • D.eV AM j ∈
      AM.M₀.B.orthogonal (AM.Vsp hc t) :=
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun v hv => B_eq_zero_of_basis D AM hk hv
  rw [D.orthogonal_Vsp_eq_comap AM, Submodule.mem_comap] at hmem
  simpa [map_sub, map_sum, map_smul] using hmem

noncomputable def Sec108Data.phiMat (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) (m : ↥(H0 M Z)) : Matrix (Fin 3) (Fin 3) AM.K :=
  Matrix.of fun i j =>
    AM.M₀.B (D.eV AM i) (AM.φ m (D.nu AM (D.eV AM j)) - D.nu AM (D.eV AM j))

theorem Sec108Data.phiMat_apply (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (m : ↥(H0 M Z)) (i j : Fin 3) :
    D.phiMat AM m i j =
      AM.M₀.B (D.eV AM i) (AM.φ m (D.nu AM (D.eV AM j)) - D.nu AM (D.eV AM j)) := by
  simp only [Sec108Data.phiMat, Matrix.of_apply]

section D0

variable (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) {m m' : ↥(H0 M Z)}

private theorem B_sub_eq_zero (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e) {v : AM.M₀.E}
    (hv : v ∈ AM.Vsp hc t) (e : AM.M₀.E) : AM.M₀.B v (AM.φ m e - e) = 0 := by
  rw [map_sub, ← B_phi AM m v e, hV v hv, sub_self]

theorem Sec108Data.phi_sub_mem_Vsp (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e)
    (ht : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e))
    {u : AM.M₀.E} (hu : u ∈ LinearMap.range (D.nu AM)) : AM.φ m u - u ∈ AM.Vsp hc t := by
  obtain ⟨e, rfl⟩ := hu
  have hmem : AM.φ m e - e ∈ AM.M₀.B.orthogonal (AM.Vsp hc t) :=
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun v hv => B_sub_eq_zero AM hV hv e
  rw [D.orthogonal_Vsp_eq_comap AM, Submodule.mem_comap, map_sub, D.nu_phi AM ht] at hmem
  exact hmem

private theorem B_sub_symm (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e)
    (ht : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e))
    (a b : AM.M₀.E) :
    AM.M₀.B a (AM.φ m (D.nu AM b) - D.nu AM b) =
      AM.M₀.B b (AM.φ m (D.nu AM a) - D.nu AM a) := by
  have hxb := D.phi_sub_mem_Vsp AM hV ht (LinearMap.mem_range_self (D.nu AM) b)
  have h1 := B_phi AM m a (D.nu AM b)
  have h2 : AM.M₀.B (AM.φ m a - a) (AM.φ m (D.nu AM b) - D.nu AM b) = 0 := by
    rw [B_antisymm AM, B_sub_eq_zero AM hV hxb a, neg_zero]
  have h3 : AM.M₀.B (AM.φ m a - a) (D.nu AM b) =
      AM.M₀.B (AM.φ m (D.nu AM a) - D.nu AM a) b := by
    calc AM.M₀.B (AM.φ m a - a) (D.nu AM b) = AM.M₀.B (D.nu AM (AM.φ m a - a)) b :=
          (D.B_nu AM _ _).symm
      _ = AM.M₀.B (AM.φ m (D.nu AM a) - D.nu AM a) b := by
          rw [map_sub (D.nu AM), D.nu_phi AM ht]
  have h4a := B_antisymm AM (AM.φ m (D.nu AM a)) b
  have h4b := B_antisymm AM (D.nu AM a) b
  simp only [map_sub, LinearMap.sub_apply] at h2 h3 ⊢
  linear_combination h1 - h2 - h3 - h4a + h4b

theorem Sec108Data.phiMat_transpose (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e)
    (ht : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e)) :
    (D.phiMat AM m)ᵀ = D.phiMat AM m := by
  ext i j
  rw [Matrix.transpose_apply, D.phiMat_apply, D.phiMat_apply]
  exact B_sub_symm D AM hV ht _ _

theorem Sec108Data.phiMat_mul (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e)
    (hV' : ∀ e ∈ AM.Vsp hc t, AM.φ m' e = e)
    (ht' : ∀ e, AM.φ m' (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m' e)) :
    D.phiMat AM (m * m') = D.phiMat AM m + D.phiMat AM m' := by
  ext i j
  have hx := D.phi_sub_mem_Vsp AM hV' ht' (LinearMap.mem_range_self (D.nu AM) (D.eV AM j))
  have h2 := hV _ hx
  rw [map_sub, sub_eq_iff_eq_add'] at h2
  rw [Matrix.add_apply, D.phiMat_apply, D.phiMat_apply, D.phiMat_apply, ← map_add, map_mul,
    LinearEquiv.mul_apply, h2]
  congr 1
  abel

private theorem coord_phi {r : ↥(H0 M Z)} {A : Matrix (Fin 3) (Fin 3) AM.K}
    (hA : ∀ j, AM.φ r (D.bV AM j) = ∑ i, A i j • (D.bV AM i : AM.M₀.E)) {x : AM.M₀.E}
    (hx : x ∈ AM.Vsp hc t) (i : Fin 3) :
    AM.M₀.B (D.eV AM i) (AM.φ r x) = ∑ l, A i l * AM.M₀.B (D.eV AM l) x := by
  conv_lhs => rw [coord_Vsp D AM hx]
  simp [map_sum, map_smul, hA, D.B_eV_bV, mul_comm]

private theorem phi_phi_inv (r : ↥(H0 M Z)) (x : AM.M₀.E) : AM.φ r (AM.φ r⁻¹ x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

private theorem inv_comm_t {r : ↥(H0 M Z)}
    (hr : ∀ e, AM.φ r (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ r e)) (e : AM.M₀.E) :
    AM.φ r⁻¹ (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ r⁻¹ e) := by
  have h := hr (AM.φ r⁻¹ e)
  rw [phi_phi_inv AM] at h
  apply (AM.φ r).injective
  rw [h, phi_phi_inv AM]

private theorem nu_inv_eV_sub_mem {r : ↥(H0 M Z)} {A : Matrix (Fin 3) (Fin 3) AM.K}
    (hA : ∀ j, AM.φ r (D.bV AM j) = ∑ i, A i j • (D.bV AM i : AM.M₀.E)) (j : Fin 3) :
    D.nu AM (AM.φ r⁻¹ (D.eV AM j) - ∑ k, A j k • D.eV AM k) ∈ AM.Vsp hc t := by
  have hk : ∀ l, AM.M₀.B (D.bV AM l) (AM.φ r⁻¹ (D.eV AM j) - ∑ k, A j k • D.eV AM k) = 0 := by
    intro l
    have hiso := B_phi AM r (D.bV AM l) (AM.φ r⁻¹ (D.eV AM j))
    rw [phi_phi_inv AM, hA l] at hiso
    rw [map_sub, ← hiso]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      B_bV_eV D AM]
    simp
  have hmem : AM.φ r⁻¹ (D.eV AM j) - ∑ k, A j k • D.eV AM k ∈
      AM.M₀.B.orthogonal (AM.Vsp hc t) :=
    LinearMap.BilinForm.mem_orthogonal_iff.mpr fun v hv => B_eq_zero_of_basis D AM hk hv
  rw [D.orthogonal_Vsp_eq_comap AM, Submodule.mem_comap] at hmem
  exact hmem

private theorem conj_sub_eq {r : ↥(H0 M Z)}
    (hr : ∀ e, AM.φ r (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ r e))
    {A : Matrix (Fin 3) (Fin 3) AM.K}
    (hA : ∀ j, AM.φ r (D.bV AM j) = ∑ i, A i j • (D.bV AM i : AM.M₀.E))
    (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e) (j : Fin 3) :
    AM.φ (r * m * r⁻¹) (D.nu AM (D.eV AM j)) - D.nu AM (D.eV AM j) =
      AM.φ r (∑ k, A j k • (AM.φ m (D.nu AM (D.eV AM k)) - D.nu AM (D.eV AM k))) := by
  have hnu : AM.φ r⁻¹ (D.nu AM (D.eV AM j)) =
      ∑ k, A j k • D.nu AM (D.eV AM k) +
        D.nu AM (AM.φ r⁻¹ (D.eV AM j) - ∑ k, A j k • D.eV AM k) := by
    rw [map_sub (D.nu AM), map_sum, ← D.nu_phi AM (inv_comm_t D AM hr)]
    simp only [map_smul]
    abel
  have hfix := hV _ (nu_inv_eV_sub_mem D AM hA j)
  have hsum : AM.φ m (∑ k, A j k • D.nu AM (D.eV AM k)) - ∑ k, A j k • D.nu AM (D.eV AM k) =
      ∑ k, A j k • (AM.φ m (D.nu AM (D.eV AM k)) - D.nu AM (D.eV AM k)) := by
    simp only [map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
  have hy : D.nu AM (D.eV AM j) = AM.φ r (∑ k, A j k • D.nu AM (D.eV AM k) +
      D.nu AM (AM.φ r⁻¹ (D.eV AM j) - ∑ k, A j k • D.eV AM k)) := by
    rw [← hnu, phi_phi_inv AM]
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hnu, map_add, hfix]
  conv_lhs => arg 2; rw [hy]
  rw [← map_sub, ← hsum]
  congr 1
  abel

theorem Sec108Data.phiMat_conj {r : ↥(H0 M Z)}
    (hr : ∀ e, AM.φ r (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ r e))
    {A : Matrix (Fin 3) (Fin 3) AM.K}
    (hA : ∀ j, AM.φ r (D.bV AM j) = ∑ i, A i j • (D.bV AM i : AM.M₀.E))
    (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e)
    (ht : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e)) :
    D.phiMat AM (r * m * r⁻¹) = A * D.phiMat AM m * Aᵀ := by
  ext i j
  have hxV : ∀ k, AM.φ m (D.nu AM (D.eV AM k)) - D.nu AM (D.eV AM k) ∈ AM.Vsp hc t := fun k =>
    D.phi_sub_mem_Vsp AM hV ht (LinearMap.mem_range_self (D.nu AM) (D.eV AM k))
  rw [D.phiMat_apply, conj_sub_eq D AM hr hA hV j, coord_phi D AM hA (Submodule.sum_mem _
    fun k _ => Submodule.smul_mem _ _ (hxV k)) i]
  simp only [map_sum, map_smul, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply,
    D.phiMat_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem Sec108Data.phiMat_eq_zero_iff (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e)
    (ht : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e)) :
    D.phiMat AM m = 0 ↔ ∀ u ∈ LinearMap.range (D.nu AM), AM.φ m u = u := by
  constructor
  · intro h0 u hu
    obtain ⟨w, hw⟩ := D.exists_coord AM hu
    have hcol : ∀ j, AM.φ m (D.nu AM (D.eV AM j)) = D.nu AM (D.eV AM j) := by
      intro j
      refine sub_eq_zero.mp (eq_zero_of_coord D AM
        (D.phi_sub_mem_Vsp AM hV ht (LinearMap.mem_range_self _ _)) fun l => ?_)
      rw [← D.phiMat_apply, h0, Matrix.zero_apply]
    have hsplit : u = (u - ∑ j, w j • D.nu AM (D.eV AM j)) + ∑ j, w j • D.nu AM (D.eV AM j) := by
      abel
    rw [hsplit, map_add, hV _ hw, map_sum]
    simp only [map_smul, hcol]
  · intro hU
    ext i j
    rw [D.phiMat_apply, hU _ (LinearMap.mem_range_self _ _), sub_self, map_zero,
      Matrix.zero_apply]

theorem Sec108Data.phiMat_mulVec_eq_zero_iff (hV : ∀ e ∈ AM.Vsp hc t, AM.φ m e = e)
    (ht : ∀ e, AM.φ m (AM.φ ⟨t, D.t_mem_H0⟩ e) = AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ m e))
    (w : Fin 3 → AM.K) :
    D.phiMat AM m *ᵥ w = 0 ↔
      AM.φ m (∑ j, w j • D.nu AM (D.eV AM j)) = ∑ j, w j • D.nu AM (D.eV AM j) := by
  have hmem : AM.φ m (∑ j, w j • D.nu AM (D.eV AM j)) - ∑ j, w j • D.nu AM (D.eV AM j) ∈
      AM.Vsp hc t :=
    D.phi_sub_mem_Vsp AM hV ht (Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _))
  have hcoord : ∀ i, (D.phiMat AM m *ᵥ w) i = AM.M₀.B (D.eV AM i)
      (AM.φ m (∑ j, w j • D.nu AM (D.eV AM j)) - ∑ j, w j • D.nu AM (D.eV AM j)) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, D.phiMat_apply, map_sum, map_smul, smul_sub,
      Finset.sum_sub_distrib, smul_eq_mul, map_sub]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  constructor
  · intro h0
    refine sub_eq_zero.mp (eq_zero_of_coord D AM hmem fun l => ?_)
    rw [← hcoord, h0, Pi.zero_apply]
  · intro hfix
    funext i
    rw [hcoord, hfix, sub_self, map_zero, Pi.zero_apply]

end D0

noncomputable def Sec108Data.matV (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (m : ↥(H0 M Z)) : Matrix (Fin 3) (Fin 3) AM.K :=
  Matrix.of fun i j => AM.M₀.B (D.eV AM i) (AM.φ m (D.bV AM j))

theorem Sec108Data.matV_apply (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (m : ↥(H0 M Z)) (i j : Fin 3) :
    D.matV AM m i j = AM.M₀.B (D.eV AM i) (AM.φ m (D.bV AM j)) := by
  simp only [Sec108Data.matV, Matrix.of_apply]

theorem Sec108Data.phi_bV_eq_sum (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m : ↥(H0 M Z)}
    (hm : ∀ e ∈ AM.Vsp hc t, AM.φ m e ∈ AM.Vsp hc t) (j : Fin 3) :
    AM.φ m (D.bV AM j) = ∑ i, D.matV AM m i j • (D.bV AM i : AM.M₀.E) := by
  conv_lhs => rw [coord_Vsp D AM (hm _ (D.bV AM j).2)]
  simp only [D.matV_apply]

theorem Sec108Data.matV_eq_of_forall (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m : ↥(H0 M Z)} {A : Matrix (Fin 3) (Fin 3) AM.K}
    (hA : ∀ j, AM.φ m (D.bV AM j) = ∑ i, A i j • (D.bV AM i : AM.M₀.E)) : D.matV AM m = A := by
  ext i j
  rw [D.matV_apply, hA j]
  simp [map_sum, map_smul, D.B_eV_bV]

theorem Sec108Data.matV_one (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    D.matV AM 1 = 1 := by
  refine D.matV_eq_of_forall AM fun j => ?_
  rw [map_one, LinearEquiv.coe_one, id_eq]
  simp [Matrix.one_apply]

theorem Sec108Data.matV_mul (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    {m m' : ↥(H0 M Z)} (hm' : ∀ e ∈ AM.Vsp hc t, AM.φ m' e ∈ AM.Vsp hc t) :
    D.matV AM (m * m') = D.matV AM m * D.matV AM m' := by
  ext i j
  rw [D.matV_apply, map_mul, LinearEquiv.mul_apply, D.phi_bV_eq_sum AM hm' j, Matrix.mul_apply]
  simp only [map_sum, map_smul, smul_eq_mul, D.matV_apply]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

theorem Sec108Data.matV_eq_one_iff (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {m : ↥(H0 M Z)}
    (hm : ∀ e ∈ AM.Vsp hc t, AM.φ m e ∈ AM.Vsp hc t) :
    D.matV AM m = 1 ↔ ∀ e ∈ AM.Vsp hc t, AM.φ m e = e := by
  constructor
  · intro h1 e he
    rw [coord_Vsp D AM he]
    simp only [map_sum, map_smul, D.phi_bV_eq_sum AM hm, h1, Matrix.one_apply, ite_smul, one_smul,
      zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · intro hfix
    refine D.matV_eq_of_forall AM fun j => ?_
    rw [hfix _ (D.bV AM j).2]
    simp [Matrix.one_apply]

theorem Sec108Data.CN_le_H0 (D : Sec108Data hc t Y) : hc.CN t ≤ H0 M Z := fun _ hn =>
  D.Rt_le_H0 (Ctx.mem_CN.mp hn).1

theorem Sec108Data.comm_CN_mem (D : Sec108Data hc t Y) {n n' : G} (hn : n ∈ hc.CN t)
    (hn' : n' ∈ hc.CN t) : ⁅n, n'⁆ ∈ Q := by
  haveI := hc.normal_Q_in_M
  have hnM : n ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hn).1
  have hn'M : n' ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hn').1
  have hmem : ∀ x (hx : x ∈ hc.CN t) (hxM : x ∈ M),
      QuotientGroup.mk' (Q.subgroupOf M) ⟨x, hxM⟩ ∈ bar M Q (hc.CN t) :=
    fun x hx hxM => Subgroup.mem_map_of_mem _ hx
  haveI := D.isElemAbelian_bar_CN.1
  have h := Subgroup.mul_comm_of_mem_isMulCommutative (bar M Q (hc.CN t)) (hmem n hn hnM)
    (hmem n' hn' hn'M)
  have h2 : QuotientGroup.mk' (Q.subgroupOf M) ⁅(⟨n, hnM⟩ : ↥M), ⟨n', hn'M⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact h
  have h3 := (QuotientGroup.eq_one_iff _).mp h2
  simpa [Subgroup.mem_subgroupOf, commutatorElement_def] using h3

theorem Sec108Data.t_mem_CN (D : Sec108Data hc t Y) : t ∈ hc.CN t := by
  rw [D.CN_eq]
  obtain ⟨g, hg⟩ := D.sit.conj
  exact Subgroup.mem_sup_right
    ⟨IsZConjugate.le_QB_self hc.hyp ⟨g, hg⟩ D.sit.mem, D.sit.memM⟩

theorem Sec108Data.fix_Vsp_of_mem_CN (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n : G} (hn : n ∈ hc.CN t) {e : AM.M₀.E}
    (he : e ∈ AM.Vsp hc t) : AM.φ ⟨n, D.CN_le_H0 hn⟩ e = e := by
  obtain ⟨w, hwV, hwQ, hw⟩ := AM.M₀.mem_img.mp (mem_imgSub.mp he)
  rw [← hw]
  exact (comm_mem_iff_fix (M₀ := AM.M₀) (T := AM.φ ⟨n, D.CN_le_H0 hn⟩)
    (hc.conj_mem_Q_of_mem_M (hc.Rt_le_M t (Ctx.mem_CN.mp hn).1)).1
    (fun z hz => AM.φ_π ⟨n, D.CN_le_H0 hn⟩ z hz) hwQ).mp ((Ctx.mem_CN.mp hn).2 w hwV)

theorem Sec108Data.comm_t_of_mem_CN (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {n : G} (hn : n ∈ hc.CN t) (e : AM.M₀.E) :
    AM.φ ⟨n, D.CN_le_H0 hn⟩ (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨n, D.CN_le_H0 hn⟩ e) :=
  Sec108Data.phi_comm_of_comm_mem AM (D.comm_CN_mem hn D.t_mem_CN) e

theorem Sec108Data.conj_mem_CN (D : Sec108Data hc t Y) {r n : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hn : n ∈ hc.CN t) : r * n * r⁻¹ ∈ hc.CN t :=
  mem_CN_conj_of_normalizes hc (hc.Rt_le_M t hr)
    (conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hr))
    (conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt D.good.1.mem_LB hr)) hn

noncomputable def Sec108Data.phiHom (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    ↥(hc.CN t) →* Multiplicative (Matrix (Fin 3) (Fin 3) AM.K) where
  toFun n := Multiplicative.ofAdd (D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩)
  map_one' := by
    have h := (D.phiMat_eq_zero_iff AM (m := 1) (fun e _ => by rw [map_one]; rfl)
      (fun e => by rw [map_one]; rfl)).mpr (fun u _ => by rw [map_one]; rfl)
    exact congrArg Multiplicative.ofAdd h
  map_mul' n n' := by
    have h := D.phiMat_mul AM (m := ⟨n, D.CN_le_H0 n.2⟩) (m' := ⟨n', D.CN_le_H0 n'.2⟩)
      (fun e he => D.fix_Vsp_of_mem_CN AM n.2 he) (fun e he => D.fix_Vsp_of_mem_CN AM n'.2 he)
      (D.comm_t_of_mem_CN AM n'.2)
    exact congrArg Multiplicative.ofAdd h

theorem Sec108Data.phiHom_apply (D : Sec108Data hc t Y) (AM : Smith81.Smith23E1.ActionModel M Q Z)
    (n : ↥(hc.CN t)) :
    Multiplicative.toAdd (D.phiHom AM n) = D.phiMat AM ⟨n, D.CN_le_H0 n.2⟩ := by
  simp only [Sec108Data.phiHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]

end CFSG.RankThree.GF2n.Stroth80
