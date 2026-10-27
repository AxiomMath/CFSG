module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L : Subgroup G} {F0 : Type} [Field F0] [Finite F0]
  [CharP F0 2] {m : ℕ} {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)}

private theorem qtwoDB3_a1_diag_val (c : Fin m → F0ˣ) :
    ((qTwoChartTwoThree_diag c : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
      Matrix.diagonal fun i => (c i : F0) := rfl

private theorem qtwoDB3_a1_diag_mul (c c' : Fin m → F0ˣ) :
    qTwoChartTwoThree_diag (c * c') =
      qTwoChartTwoThree_diag c * qTwoChartTwoThree_diag c' := by
  apply Units.ext
  simp only [Units.val_mul, qTwoChartTwoThree_diag]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1

private theorem qtwoDB3_a1_diag_one :
    qTwoChartTwoThree_diag (fun _ : Fin m => (1 : F0ˣ)) = 1 := by
  apply Units.ext
  simp only [Units.val_one, qTwoChartTwoThree_diag]
  rw [← Matrix.diagonal_one]

private theorem qtwoDB3_a1_diag_inv (c : Fin m → F0ˣ) :
    (qTwoChartTwoThree_diag c)⁻¹ = qTwoChartTwoThree_diag (fun j => (c j)⁻¹) := rfl

private theorem qtwoDB3_a1_diag_inv_diag (c : Fin m → F0ˣ) :
    qTwoChartTwoThree_diag c⁻¹ = (qTwoChartTwoThree_diag c)⁻¹ := rfl

private theorem qtwoDB3_a1_diag_const_comm (l : F0ˣ) (u : GL (Fin m) F0) :
    qTwoChartTwoThree_diag (fun _ : Fin m => l) * u =
      u * qTwoChartTwoThree_diag (fun _ : Fin m => l) := by
  apply Units.ext
  simp only [Units.val_mul, qTwoChartTwoThree_diag]
  ext i j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

private theorem qtwoDB3_a1_diag_const_conj (l : F0ˣ) (u : GL (Fin m) F0) :
    qTwoChartTwoThree_diag (fun _ : Fin m => l) * u *
      (qTwoChartTwoThree_diag (fun _ : Fin m => l))⁻¹ = u := by
  rw [qtwoDB3_a1_diag_const_comm l u]
  group

private theorem qtwoDB3_a1_diag_injective {c c' : Fin m → F0ˣ}
    (h : qTwoChartTwoThree_diag c = qTwoChartTwoThree_diag c') : c = c' := by
  funext i
  apply Units.ext
  have hmat := congrArg (fun g : GL (Fin m) F0 => (g : Matrix (Fin m) (Fin m) F0)) h
  have hii := congrArg (fun M : Matrix (Fin m) (Fin m) F0 => M i i) hmat
  rw [qtwoDB3_a1_diag_val, qtwoDB3_a1_diag_val, Matrix.diagonal_apply_eq,
    Matrix.diagonal_apply_eq] at hii
  exact hii

private theorem qtwoDB3_a1_perm_mulVec (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    Matrix.mulVec
      (((ggPermSU (K := F0) (f := 1) (n := m) σ : Su F0 2 1 m) : GL (Fin m) F0) :
        Matrix (Fin m) (Fin m) F0) (Pi.single i 1) = Pi.single (σ⁻¹ i) 1 := by
  have hcoe : (((ggPermSU (K := F0) (f := 1) (n := m) σ : Su F0 2 1 m) :
      GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = σ.permMatrix F0 := rfl
  rw [hcoe, Matrix.permMatrix_mulVec]
  funext j
  simp only [Function.comp_apply, Pi.single_apply]
  exact if_congr (Equiv.eq_symm_apply σ).symm rfl rfl

private theorem qtwoDB3_a1_perm_mul_anti (σ τ : Equiv.Perm (Fin m)) :
    (ggPermSU (K := F0) (f := 1) (n := m) (σ * τ) : GL (Fin m) F0) =
      (ggPermSU (K := F0) (f := 1) (n := m) τ : GL (Fin m) F0) *
        (ggPermSU (K := F0) (f := 1) (n := m) σ : GL (Fin m) F0) := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul]
  change (σ * τ).permMatrix F0 i j = (τ.permMatrix F0 * σ.permMatrix F0) i j
  rw [Matrix.permMatrix_mul]

private theorem qtwoDB3_a1_perm_one :
    ggPermSU (K := F0) (f := 1) (n := m) (1 : Equiv.Perm (Fin m)) = 1 := by
  apply Subtype.ext
  apply Units.ext
  show (1 : Equiv.Perm (Fin m)).permMatrix F0 = (1 : Matrix (Fin m) (Fin m) F0)
  simp

private theorem qtwoDB3_a1_perm_inv (σ : Equiv.Perm (Fin m)) :
    (ggPermSU (K := F0) (f := 1) (n := m) σ)⁻¹ =
      ggPermSU (K := F0) (f := 1) (n := m) σ⁻¹ := by
  have h := qtwoDB3_a1_perm_mul_anti (F0 := F0) σ σ⁻¹
  rw [mul_inv_cancel, qtwoDB3_a1_perm_one] at h
  apply Subtype.ext
  exact (eq_inv_of_mul_eq_one_left h.symm).symm

private theorem qtwoDB3_a1_perm_inv_mulVec (σ : Equiv.Perm (Fin m)) (i : Fin m) :
    Matrix.mulVec
      ((((ggPermSU (K := F0) (f := 1) (n := m) σ : Su F0 2 1 m)⁻¹ :
        Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
      (Pi.single i 1) = Pi.single (σ i) 1 := by
  rw [qtwoDB3_a1_perm_inv]
  rw [qtwoDB3_a1_perm_mulVec]
  simp

private theorem qtwoDB3_a1_perm_key (π : Equiv.Perm (Fin m)) (e : Fin m → F0ˣ)
    (u : Su F0 2 1 m)
    (hu : (u : GL (Fin m) F0) =
      qTwoChartTwoThree_diag e * (ggPermSU (K := F0) (f := 1) (n := m) π :
        GL (Fin m) F0) * (qTwoChartTwoThree_diag e)⁻¹) :
    ((u⁻¹ * ggPermSU (K := F0) (f := 1) (n := m) π : Su F0 2 1 m) :
        GL (Fin m) F0) =
      qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) := by
  let P : Su F0 2 1 m := ggPermSU (K := F0) (f := 1) (n := m) π
  have huP : (u : GL (Fin m) F0) =
      qTwoChartTwoThree_diag e * (P : GL (Fin m) F0) * (qTwoChartTwoThree_diag e)⁻¹ := hu
  have huinv : (u : GL (Fin m) F0)⁻¹ =
      qTwoChartTwoThree_diag e * (P : GL (Fin m) F0)⁻¹ *
        (qTwoChartTwoThree_diag e)⁻¹ := by
    rw [huP]
    group
  have hP : (P : GL (Fin m) F0)⁻¹ * qTwoChartTwoThree_diag e * (P : GL (Fin m) F0) =
      qTwoChartTwoThree_diag (fun a => e (π⁻¹ a)) := by
    have hu' : ∀ i : Fin m, Matrix.mulVec
        ((((P⁻¹ : Su F0 2 1 m) : GL (Fin m) F0)) :
          Matrix (Fin m) (Fin m) F0) (Pi.single i 1) = Pi.single (π i) 1 :=
      fun i => by simpa [P] using qtwoDB3_a1_perm_inv_mulVec (F0 := F0) π i
    have h := qTwoChartTwoThree_perm_conj_diag (u := P⁻¹) (σ := π) hu' e
    simpa [Subgroup.coe_inv, Function.comp_def] using h
  have hcoe : ((u⁻¹ * ggPermSU (K := F0) (f := 1) (n := m) π : Su F0 2 1 m) :
      GL (Fin m) F0) = (u : GL (Fin m) F0)⁻¹ * (P : GL (Fin m) F0) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe, huinv]
  calc qTwoChartTwoThree_diag e * (P : GL (Fin m) F0)⁻¹ * (qTwoChartTwoThree_diag e)⁻¹ *
        (P : GL (Fin m) F0)
      = qTwoChartTwoThree_diag e *
          ((P : GL (Fin m) F0)⁻¹ * (qTwoChartTwoThree_diag e)⁻¹ *
            (P : GL (Fin m) F0)) := by group
    _ = qTwoChartTwoThree_diag e *
          ((P : GL (Fin m) F0)⁻¹ * qTwoChartTwoThree_diag e *
            (P : GL (Fin m) F0))⁻¹ := by
        congr 1
        group
    _ = qTwoChartTwoThree_diag e * (qTwoChartTwoThree_diag (fun a => e (π⁻¹ a)))⁻¹ := by
        rw [hP]
    _ = qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) := by
        rw [qtwoDB3_a1_diag_inv, ← qtwoDB3_a1_diag_mul]
        congr 1

private theorem qtwoDB3_a1_const_of_induces_one (hm : 3 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) {e : Fin m → F0ˣ}
    (he : qTwoChartTwoThree_induces ψ (1 : G) e) :
    ∃ l : F0ˣ, ∀ i, e i = l := by
  classical
  have hpair : ∀ i j : Fin m, i ≠ j → e i = e j := by
    intro i j hij
    have hproper : ({i, j} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
      have hle : ({i, j} : Finset (Fin m)).card ≤ 2 := by
        calc ({i, j} : Finset (Fin m)).card ≤ ({i} : Finset (Fin m)).card + 1 :=
              Finset.card_insert_le _ _
          _ = 2 := by simp
      rw [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨k, -, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card hproper
    have hki : k ≠ i := by rintro rfl; exact hk (by simp)
    have hkj : k ≠ j := by rintro rfl; exact hk (by simp)
    let π : Equiv.Perm (Fin m) := Equiv.swap i j
    let π' : Equiv.Perm (Fin m) := Equiv.swap i k
    have hπinv : π⁻¹ = π := by
      apply inv_eq_of_mul_eq_one_right
      change (Equiv.swap i j) * (Equiv.swap i j) = 1
      exact Equiv.swap_mul_self i j
    have hπ'inv : (π' : Equiv.Perm (Fin m))⁻¹ = π' := by
      apply inv_eq_of_mul_eq_one_right
      change (Equiv.swap i k) * (Equiv.swap i k) = 1
      exact Equiv.swap_mul_self i k
    let P : Su F0 2 1 m := ggPermSU (K := F0) (f := 1) (n := m) π
    let P' : Su F0 2 1 m := ggPermSU (K := F0) (f := 1) (n := m) π'
    obtain ⟨u, hu_mat, hu_ψ⟩ := he P
    have hmem : u⁻¹ * P ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hu_ψ]
      simp
    have hz : u⁻¹ * P ∈ Subgroup.center (Su F0 2 1 m) := hker hmem
    have hkey : ((u⁻¹ * P : Su F0 2 1 m) : GL (Fin m) F0) =
        qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) :=
      qtwoDB3_a1_perm_key π e u (by simpa [P] using hu_mat)
    have hcomm : (u⁻¹ * P) * P' = P' * (u⁻¹ * P) :=
      (Subgroup.mem_center_iff.mp hz P').symm
    have hcommGL : ((u⁻¹ * P : Su F0 2 1 m) : GL (Fin m) F0) * (P' : GL (Fin m) F0) =
        (P' : GL (Fin m) F0) * ((u⁻¹ * P : Su F0 2 1 m) : GL (Fin m) F0) :=
      congrArg (fun z : Su F0 2 1 m => (z : GL (Fin m) F0)) hcomm
    have hconj : (P' : GL (Fin m) F0)⁻¹ *
        qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) * (P' : GL (Fin m) F0) =
        qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) := by
      rw [← hkey, mul_assoc, hcommGL, ← mul_assoc, inv_mul_cancel, one_mul]
    have hcommP' : qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) *
          (P' : GL (Fin m) F0) =
        (P' : GL (Fin m) F0) * qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) := by
      calc qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) * (P' : GL (Fin m) F0)
          = (P' : GL (Fin m) F0) *
              ((P' : GL (Fin m) F0)⁻¹ *
                qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) *
                (P' : GL (Fin m) F0)) := by group
        _ = (P' : GL (Fin m) F0) *
              qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) := by rw [hconj]
    have hfix : (P' : GL (Fin m) F0) *
        qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) * (P' : GL (Fin m) F0)⁻¹ =
        qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) := by
      rw [← hcommP', mul_assoc, mul_inv_cancel, mul_one]
    have hP'fix : (P' : GL (Fin m) F0) *
        qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) * (P' : GL (Fin m) F0)⁻¹ =
        qTwoChartTwoThree_diag
          (fun a => e ((π')⁻¹ a) * (e (π⁻¹ ((π')⁻¹ a)))⁻¹) := by
      have hu' : ∀ i : Fin m, Matrix.mulVec
          (((ggPermSU (K := F0) (f := 1) (n := m) π' :
            Su F0 2 1 m) : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
          (Pi.single i 1) = Pi.single (π' i) 1 := fun i => by
        rw [qtwoDB3_a1_perm_mulVec π' i, hπ'inv]
      have h := qTwoChartTwoThree_perm_conj_diag (u := P') (σ := π') hu'
        (fun a => e a * (e (π⁻¹ a))⁻¹)
      simpa [P', Function.comp_def] using h
    have hDw : qTwoChartTwoThree_diag
          (fun a => e ((π')⁻¹ a) * (e (π⁻¹ ((π')⁻¹ a)))⁻¹) =
        qTwoChartTwoThree_diag (fun a => e a * (e (π⁻¹ a))⁻¹) := by
      rw [← hP'fix, hfix]
    have hw := qtwoDB3_a1_diag_injective hDw
    have hwk : (fun a => e a * (e (π⁻¹ a))⁻¹) k = (fun a => e a * (e (π⁻¹ a))⁻¹) i := by
      have hcongr := congrFun hw i
      rwa [show (π' : Equiv.Perm (Fin m))⁻¹ i = k by
        rw [hπ'inv]
        simpa [π'] using Equiv.swap_apply_left] at hcongr
    have hwi : (fun a => e a * (e (π⁻¹ a))⁻¹) i = e i * (e j)⁻¹ := by
      show e i * (e (π⁻¹ i))⁻¹ = e i * (e j)⁻¹
      rw [show π⁻¹ i = j by
        rw [hπinv]
        simpa [π] using Equiv.swap_apply_left]
    have hwk1 : (fun a => e a * (e (π⁻¹ a))⁻¹) k = 1 := by
      show e k * (e (π⁻¹ k))⁻¹ = 1
      rw [show π⁻¹ k = k by
        rw [hπinv]
        simpa [π] using Equiv.swap_apply_of_ne_of_ne hki hkj, mul_inv_cancel]
    have hone : e i * (e j)⁻¹ = 1 := by rw [← hwi, hwk.symm, hwk1]
    exact eq_of_mul_inv_eq_one hone
  refine ⟨e ⟨0, by omega⟩, fun i => ?_⟩
  by_cases hi : i = ⟨0, by omega⟩
  · rw [hi]
  · exact hpair i ⟨0, by omega⟩ hi

theorem qtwoDB3_ind_exists (hbase : QTwoUnitBase p B Bs x L ψ ε) {s : G} (hs : s ∈ Bs) :
    ∃ c : Fin m → F0ˣ, qTwoChartTwoThree_induces ψ s c := by
  rcases hbase.diag s hs with ⟨g, ⟨d, hgd⟩, hU⟩
  rcases hU with ⟨-, hind⟩
  have hdet : (∏ i, d i) ≠ 0 := by
    intro hzero
    have h := congrArg Matrix.det (show (g : Matrix (Fin m) (Fin m) F0) *
        ((g⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = 1 from by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    rw [Matrix.det_mul, Matrix.det_one, hgd, Matrix.det_diagonal, hzero, zero_mul] at h
    exact one_ne_zero h.symm
  let c : Fin m → F0ˣ :=
    fun i => Units.mk0 (d i) (Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i))
  refine ⟨c, ?_⟩
  have hdiag : qTwoChartTwoThree_diag c = g := by
    apply Units.ext
    rw [qtwoDB3_a1_diag_val, hgd]
    rfl
  intro u
  rcases hind u with ⟨u', hu'mat, hu'ψ⟩
  exact ⟨u', by rw [hdiag, hu'mat], hu'ψ.symm⟩

theorem qtwoDB3_ind_mul {s s' : G} {c c' : Fin m → F0ˣ}
    (h : qTwoChartTwoThree_induces ψ s c) (h' : qTwoChartTwoThree_induces ψ s' c') :
    qTwoChartTwoThree_induces ψ (s * s') (c * c') := by
  intro u
  obtain ⟨u₁, hu₁mat, hu₁ψ⟩ := h' u
  obtain ⟨u₂, hu₂mat, hu₂ψ⟩ := h u₁
  refine ⟨u₂, ?_, ?_⟩
  · rw [hu₂mat, hu₁mat, qtwoDB3_a1_diag_mul]
    group
  · rw [hu₂ψ, hu₁ψ]
    group

theorem qtwoDB3_ind_inv {s : G} {c : Fin m → F0ˣ} (h : qTwoChartTwoThree_induces ψ s c) :
    qTwoChartTwoThree_induces ψ s⁻¹ c⁻¹ := by
  classical
  haveI : Finite (Su F0 2 1 m) := inferInstance
  intro u
  let f : Su F0 2 1 m → Su F0 2 1 m := fun w => Classical.choose (h w)
  have hf_spec : ∀ w : Su F0 2 1 m,
      (f w : GL (Fin m) F0) = qTwoChartTwoThree_diag c * (w : GL (Fin m) F0) *
          (qTwoChartTwoThree_diag c)⁻¹ ∧
        ψ (f w) = s * ψ w * s⁻¹ := fun w => Classical.choose_spec (h w)
  have hf_inj : Function.Injective f := by
    intro w w' hww
    have hgl : (f w : GL (Fin m) F0) = (f w' : GL (Fin m) F0) :=
      congrArg (fun z : Su F0 2 1 m => (z : GL (Fin m) F0)) hww
    rw [(hf_spec w).1, (hf_spec w').1] at hgl
    exact Subtype.ext (mul_left_cancel (mul_right_cancel hgl))
  have hf_surj : Function.Surjective f := (Finite.injective_iff_surjective).mp hf_inj
  obtain ⟨w, hw⟩ := hf_surj u
  refine ⟨w, ?_, ?_⟩
  · have hcoe : (u : GL (Fin m) F0) = qTwoChartTwoThree_diag c * (w : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag c)⁻¹ := by rw [← hw, (hf_spec w).1]
    rw [hcoe, qtwoDB3_a1_diag_inv_diag]
    group
  · have hψ : ψ u = s * ψ w * s⁻¹ := by rw [← hw, (hf_spec w).2]
    rw [hψ]
    group

theorem qtwoDB3_ind_one : qTwoChartTwoThree_induces ψ (1 : G) (fun _ => 1) := by
  intro u
  refine ⟨u, ?_, ?_⟩
  · rw [qtwoDB3_a1_diag_one, one_mul, inv_one, mul_one]
  · simp

theorem qtwoDB3_ind_scalar (hF0 : Nat.card F0 = 4) (hm : 3 ≤ m)
    (hker : ψ.ker ≤ Subgroup.center (Su F0 2 1 m)) {s : G} {c c' : Fin m → F0ˣ}
    (h : qTwoChartTwoThree_induces ψ s c) (h' : qTwoChartTwoThree_induces ψ s c') :
    ∃ l : F0ˣ, ∀ i, c' i = l * c i := by
  have hone : qTwoChartTwoThree_induces ψ (1 : G) (c' * c⁻¹) := by
    have h1 := qtwoDB3_ind_mul h' (qtwoDB3_ind_inv h)
    rwa [mul_inv_cancel] at h1
  obtain ⟨l, hl⟩ := qtwoDB3_a1_const_of_induces_one hm hker hone
  refine ⟨l, fun i => ?_⟩
  have hi := hl i
  have hmul : c' i * (c i)⁻¹ = l := hi
  rw [← hmul]
  group

theorem qtwoDB3_ind_ker (hbase : QTwoUnitBase p B Bs x L ψ ε) (hm : 3 ≤ m) {s : G}
    (hs : s ∈ Bs) {c : Fin m → F0ˣ} (h : qTwoChartTwoThree_induces ψ s c) :
    (∃ l : F0ˣ, ∀ i, c i = l) ↔ s ∈ Subgroup.zpowers x := by
  constructor
  · rintro ⟨l, hl⟩
    have hconst : c = fun _ : Fin m => l := funext hl
    have hcent : s ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hs, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro hL hhL
      have hrange : hL ∈ ψ.range := by rw [hbase.range]; exact hhL
      obtain ⟨u, rfl⟩ := hrange
      obtain ⟨u', hu'mat, hu'ψ⟩ := h u
      have hD : qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
          (qTwoChartTwoThree_diag c)⁻¹ = (u : GL (Fin m) F0) := by
        rw [hconst, qtwoDB3_a1_diag_const_comm l (u : GL (Fin m) F0)]
        group
      have hu' : u' = u := Subtype.ext (by rw [hu'mat, hD])
      rw [hu'] at hu'ψ
      rw [show ψ u * s = (s * ψ u * s⁻¹) * s from congrArg (· * s) hu'ψ]
      group
    rwa [hbase.cent] at hcent
  · intro hsx
    have hsc : s ∈ Subgroup.centralizer (L : Set G) := by
      have : s ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by rw [hbase.cent]; exact hsx
      exact (Subgroup.mem_inf.mp this).2
    rw [Subgroup.mem_centralizer_iff] at hsc
    have htriv : qTwoChartTwoThree_induces ψ s (fun _ => 1) := by
      intro u
      refine ⟨u, ?_, ?_⟩
      · rw [qtwoDB3_a1_diag_one, one_mul, inv_one, mul_one]
      · have hmemL : ψ u ∈ L := by rw [← hbase.range]; exact ⟨u, rfl⟩
        have hcomm := hsc (ψ u) hmemL
        rw [← hcomm]
        group
    obtain ⟨l, hl⟩ := qtwoDB3_ind_scalar hbase.card_field hm hbase.hyp.ker h htriv
    refine ⟨l⁻¹, fun i => ?_⟩
    exact eq_inv_of_mul_eq_one_right (hl i).symm

theorem qtwoDB3_bs_le_normalizer (hbase : QTwoUnitBase p B Bs x L ψ ε) :
    Bs ≤ Subgroup.normalizer (L : Set G) := by
  have hfwd : ∀ t ∈ Bs, ∀ h ∈ L, t * h * t⁻¹ ∈ L := by
    intro t ht h hh
    have hrange : h ∈ ψ.range := by rw [hbase.range]; exact hh
    obtain ⟨u, rfl⟩ := hrange
    obtain ⟨c, hc⟩ := qtwoDB3_ind_exists hbase ht
    obtain ⟨u', -, hu'ψ⟩ := hc u
    rw [← hbase.range]
    exact ⟨u', hu'ψ⟩
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hfwd s hs h hh
  · intro hh
    have h2 := hfwd s⁻¹ (inv_mem hs) (s * h * s⁻¹) hh
    simpa [mul_assoc] using h2

theorem qtwoDB3_ind_smul {s : G} {c : Fin m → F0ˣ} (l : F0ˣ)
    (h : qTwoChartTwoThree_induces ψ s c) :
    qTwoChartTwoThree_induces ψ s (fun i => l * c i) := by
  intro u
  obtain ⟨u', hu'mat, hu'ψ⟩ := h u
  refine ⟨u', ?_, hu'ψ⟩
  have hD : qTwoChartTwoThree_diag (fun i => l * c i) =
      qTwoChartTwoThree_diag (fun _ : Fin m => l) * qTwoChartTwoThree_diag c := by
    rw [← qtwoDB3_a1_diag_mul]
    rfl
  have hconj : (qTwoChartTwoThree_diag (fun _ : Fin m => l) * qTwoChartTwoThree_diag c) *
        (u : GL (Fin m) F0) *
        (qTwoChartTwoThree_diag (fun _ : Fin m => l) * qTwoChartTwoThree_diag c)⁻¹ =
      qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹ := by
    rw [mul_inv_rev]
    calc (qTwoChartTwoThree_diag (fun _ : Fin m => l) * qTwoChartTwoThree_diag c) *
          (u : GL (Fin m) F0) *
          ((qTwoChartTwoThree_diag c)⁻¹ * (qTwoChartTwoThree_diag (fun _ : Fin m => l))⁻¹)
        = qTwoChartTwoThree_diag (fun _ : Fin m => l) *
            (qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) *
              (qTwoChartTwoThree_diag c)⁻¹) *
            (qTwoChartTwoThree_diag (fun _ : Fin m => l))⁻¹ := by group
      _ = qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹ :=
          qtwoDB3_a1_diag_const_conj l
            (qTwoChartTwoThree_diag c * (u : GL (Fin m) F0) * (qTwoChartTwoThree_diag c)⁻¹)
  rw [hu'mat, hD, hconj]

end CFSG.StandardType.QTwo

end
