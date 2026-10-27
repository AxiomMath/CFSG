module

public import CFSG.Quasithin.Vol2.Ch11SecAKB2
public import CFSG.Quasithin.Vol2.KGNatSL3ParIn

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

namespace PointStab

theorem inv_conj_mem_of_pow {G : Type*} [Group G] {S : Subgroup G} {τ : G} {k : ℕ}
    (hτ : τ ^ 2 ^ k = 1) (hS : ∀ x ∈ S, τ * x * τ⁻¹ ∈ S) : ∀ x ∈ S, τ⁻¹ * x * τ ∈ S := by
  have hj : ∀ j : ℕ, ∀ x ∈ S, τ ^ j * x * (τ ^ j)⁻¹ ∈ S := by
    intro j
    induction j with
    | zero => intro x hx; simpa using hx
    | succ j ih =>
      intro x hx
      have h1 := hS _ (ih x hx)
      rw [pow_succ', _root_.mul_inv_rev]
      simpa only [mul_assoc] using h1
  have h1 : τ ^ (2 ^ k - 1) = τ⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ, Nat.sub_add_cancel Nat.one_le_two_pow, hτ])
  intro x hx
  simpa only [h1, inv_inv] using hj (2 ^ k - 1) x hx

section Low

variable {K : Type} [Field K]

@[expose] def lowSL : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 1, 1], by simp [Matrix.det_fin_three]⟩

theorem lowSL_mulVec (x : Fin 3 → K) :
    ((lowSL : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      ![x 0, x 1, x 1 + x 2] := by
  show !![(1 : K), 0, 0; 0, 1, 0; 0, 1, 1] *ᵥ x = _
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem mulVec_apply3 (M : Matrix (Fin 3) (Fin 3) K) (x : Fin 3 → K) (i : Fin 3) :
    (M *ᵥ x) i = M i 0 * x 0 + M i 1 * x 1 + M i 2 * x 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

end Low

section Core

variable {K : Type} [Field K] [Finite K] {W : Type*} [CommGroup W]
  {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem mul_inv_mem_of_mem_P1 (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    {x : MulAut W} (hx : x ∈ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)))
    {u : W} (hu : u ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup) : x u * u⁻¹ ∈ Z := by
  obtain ⟨B, hB, rfl⟩ := (mem_perfectCore_HU1_iff hSL hf g x).mp hx
  have hu' : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u ∈
      flagSpace 3 K 1 := mem_gmap.mp hu
  rw [← hf.ker, hf.map_mul_inv, hf.act3, gconj_mulVec, mulVec_eq_of_fix_e0 hB hu',
    g_ginv_mulVec, sub_self]

theorem mem_U1_of_fix (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    {w : W} (hw : ∀ x ∈ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)), x w * w⁻¹ ∈ Z) :
    w ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
  have hfix : ∀ a b : K, uMat a b 0 *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ f w) =
        ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w := by
    intro a b
    have h1 := hw _ ((mem_perfectCore_HU1_iff hSL hf g _).mpr
      ⟨uSL a b 0, uSL_mem_stabE0 a b 0, rfl⟩)
    rw [← hf.ker, hf.map_mul_inv, hf.act3, gconj_mulVec, sub_eq_zero] at h1
    have h2 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) h1
    simp only [ginv_g_mulVec] at h2
    rwa [coe_uSL] at h2
  have e1 := congrFun (hfix 1 0) 0
  have e2 := congrFun (hfix 0 1) 0
  rw [uMat_mulVec] at e1 e2
  simp at e1 e2
  exact (mem_U1_iff hf g w).mpr ⟨e1, e2⟩

theorem map_U1 (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    {s : MulAut W} (hsZ : ∀ z ∈ Z, s z ∈ Z)
    (hsP : ∀ x ∈ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)), s⁻¹ * x * s ∈ perfectCore (H ⊓
        Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)))
    {u : W} (hu : u ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup) :
    s u ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
  refine mem_U1_of_fix hSL hf g fun x hx => ?_
  have h1 := hsZ _ (mul_inv_mem_of_mem_P1 hSL hf g (hsP x hx) hu)
  rwa [map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self] at h1

variable [CharP K 2]

theorem exists_uMat_of_centralizes (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : SpecialLinearGroup (Fin 3) K)
    {τ : MulAut W} (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1) (hτZ : τ ∈ Ch11.SecA.stabW Z)
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H)
    (hτP : ∀ x ∈ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)), τ * x * τ⁻¹ ∈ perfectCore (H ⊓
        Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)))
    (hτc : ∀ x : ↥(perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))), ∃ y : ↥(perfectCore (H ⊓
        Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))),
      y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))) ∧
        τ * (x : MulAut W) * τ⁻¹ = (y : MulAut W) * x) :
    ∃ a b : K, ∀ w : W, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f (τ w) = uMat a b 0 *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ f w) := by
  obtain ⟨k, hk⟩ := hτ2
  have hsZ : ∀ z ∈ Z, τ z ∈ Z := fun z hz => (Ch11.SecA.mem_stabW.mp hτZ z).mp hz
  have hsZ' : ∀ z ∈ Z, τ⁻¹ z ∈ Z := fun z hz =>
    (Ch11.SecA.mem_stabW.mp hτZ _).mpr (by rwa [MulAut.apply_inv_self])
  have hτP' := inv_conj_mem_of_pow hk hτP
  have hτU : τ ∈ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup) := by
    refine Ch11.SecA.mem_stabW.mpr fun u => ⟨map_U1 hSL hf g hsZ hτP', fun hu => ?_⟩
    have h1 := map_U1 hSL hf g hsZ' (fun x hx => by rw [inv_inv]; exact hτP x hx) hu
    rwa [MulAut.inv_apply_self] at h1
  have hcomm : ∀ x ∈ perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)), τ * x * τ⁻¹ * x⁻¹ ∈
        pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
          (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hτc ⟨x, hx⟩
    have hyx' : τ * x * τ⁻¹ = (y : MulAut W) * x := hyx
    refine Subgroup.mem_map.mpr ⟨y, by exact hy, ?_⟩
    show (y : MulAut W) = τ * x * τ⁻¹ * x⁻¹
    rw [hyx', mul_inv_cancel_right]
  have he0 : (![1, 0, 0] : Fin 3 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    he0 τ hsZ hsZ' (inv_conj_mem_of_pow hk hτH)
  have hσid := sigma_eq_id_of_centralizes hSL hf g hsZ hτU hcomm hσ
  set T := hf.autMap τ hsZ with hTdef
  have hTf : ∀ w, T (f w) = f (τ w) := hf.autMap_apply τ hsZ
  let TL : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := T
      map_add' := map_add T
      map_smul' := fun c v => by rw [hσ, hσid]; rfl }
  obtain ⟨M, hMdef⟩ : ∃ M : Matrix (Fin 3) (Fin 3) K, M =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        LinearMap.toMatrix' TL * (g : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hM : ∀ w, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f (τ w) =
      M *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w) := by
    intro w
    rw [hMdef, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, g_ginv_mulVec,
      ← Matrix.toLin'_apply (LinearMap.toMatrix' TL), Matrix.toLin'_toMatrix']
    show _ = ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ T (f w)
    rw [hTf]
  obtain ⟨w₀, hw₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  obtain ⟨w₁, hw₁⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0])
  have hg₀ : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w₀ =
      ![1, 0, 0] := by rw [hw₀, ginv_g_mulVec]
  have hg₁ : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w₁ =
      ![0, 1, 0] := by rw [hw₁, ginv_g_mulVec]
  have hM0 : M 1 0 = 0 ∧ M 2 0 = 0 := by
    have hw₀U := (mem_U1_iff hf g w₀).mpr (by rw [hg₀]; simp)
    have h1 := (mem_U1_iff hf g _).mp ((Ch11.SecA.mem_stabW.mp hτU w₀).mp hw₀U)
    rw [hM, hg₀, mulVec_apply3, mulVec_apply3] at h1
    simpa using h1
  have hcommB : ∀ B : SpecialLinearGroup (Fin 3) K,
      (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] → ∀ v : Fin 3 → K,
        ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ (M *ᵥ v)) 1 =
          (M *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) 1 := by
    intro B hB v
    obtain ⟨x, hx⟩ : ∃ x : MulAut W, ((rho3 π (g * B * g⁻¹) : ↥H) : MulAut W) = x := ⟨_, rfl⟩
    have hxf : ∀ u, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f (x u) = (B : Matrix (Fin 3) (Fin 3) K) *ᵥ (((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ f u) := fun u => by rw [← hx, ginv_f_rho hf g B u]
    have hkL : x ∈ perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) := by
      rw [← hx]
      exact (mem_perfectCore_HU1_iff hSL hf g _).mpr ⟨B, hB, rfl⟩
    obtain ⟨C, hC, hCeq⟩ := levi_of_mem_pCoreOf_HU1 hSL hf g (hcomm x hkL)
    obtain ⟨w, hw⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
    have hgw : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w = v := by
      rw [hw, ginv_g_mulVec]
    have hid : (τ * x * τ⁻¹ * x⁻¹) (x (τ w)) = τ (x w) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    have e1 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f ((τ * x * τ⁻¹ * x⁻¹) (x (τ w))) = (C : Matrix (Fin 3) (Fin 3) K) *ᵥ
          ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ (M *ᵥ v)) := by
      rw [hCeq, ginv_f_rho hf g C, hxf, hM, hgw]
    have e2 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f (τ (x w)) = M *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
      rw [hM, hxf, hgw]
    have h1 : (C : Matrix (Fin 3) (Fin 3) K) *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ (M *ᵥ v)) =
        M *ᵥ ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
      rw [← e1, ← e2, hid]
    have h2 := (hC ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ (M *ᵥ v))).1
    rwa [h1, eq_comm] at h2
  have c1 := hcommB (uSL 0 0 1) (uMat_mulVec_e0 0 0 1) ![0, 1, 0]
  have c2 := hcommB (uSL 0 0 1) (uMat_mulVec_e0 0 0 1) ![0, 0, 1]
  have c3 := hcommB lowSL (by rw [lowSL_mulVec]; exact vec3_eq (by simp) (by simp) (by simp))
    ![0, 1, 0]
  simp only [coe_uSL, uMat_mulVec, lowSL_mulVec] at c1 c2 c3
  simp only [mulVec_apply3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at c1 c2 c3
  have h21 : M 2 1 = 0 := by linear_combination c1
  have h22 : M 2 2 = M 1 1 := by linear_combination c2
  have h12 : M 1 2 = 0 := by linear_combination (-1 : K) * c3
  have hMe0 : M *ᵥ ![1, 0, 0] = M 0 0 • ![1, 0, 0] :=
    vec3_eq (by simp [mulVec_apply3]) (by simp [mulVec_apply3, hM0.1])
      (by simp [mulVec_apply3, hM0.2])
  have hiter0 : ∀ j : ℕ, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f ((τ ^ j) w₀) = M 0 0 ^ j • ![1, 0, 0] := by
    intro j
    induction j with
    | zero => simp only [pow_zero, MulAut.one_apply, hg₀, one_smul]
    | succ j ih =>
      rw [pow_succ' τ j, MulAut.mul_apply, hM, ih, Matrix.mulVec_smul, hMe0, smul_smul,
        ← pow_succ]
  have hl1 : M 0 0 = 1 := by
    have h1 := congrFun (hiter0 (2 ^ k)) 0
    rw [hk, MulAut.one_apply, hg₀] at h1
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one] at h1
    exact eq_one_of_pow_two_pow h1.symm
  have hMe1 : ∀ y : Fin 3 → K, (M *ᵥ y) 1 = M 1 1 * y 1 := fun y => by
    rw [mulVec_apply3, hM0.1, h12]
    ring
  have hiter1 : ∀ j : ℕ, (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f ((τ ^ j) w₁)) 1 = M 1 1 ^ j := by
    intro j
    induction j with
    | zero => simp only [pow_zero, MulAut.one_apply, hg₁, Matrix.cons_val_one,
        Matrix.cons_val_zero]
    | succ j ih =>
      rw [pow_succ' τ j, MulAut.mul_apply, hM, hMe1, ih]
      ring
  have hm1 : M 1 1 = 1 := by
    have h1 := hiter1 (2 ^ k)
    rw [hk, MulAut.one_apply, hg₁] at h1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
    exact eq_one_of_pow_two_pow h1.symm
  refine ⟨M 0 1, M 0 2, fun w => ?_⟩
  have hMu : M = uMat (M 0 1) (M 0 2) 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat, hl1, hm1, h21, h22, h12, hM0.1, hM0.2]
  rw [hM]
  exact congrFun (congrArg Matrix.mulVec hMu) _

end Core

end PointStab

open PointStab in
theorem factRadicalPointSL3_holds : Ch11.SecA.FactRadicalPointSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagW hW hf hg hU]
  intro τ hτ2 hτZ hτH hτP hτc u hu
  obtain ⟨a, b, hab⟩ := exists_uMat_of_centralizes hSL hf g hτ2 hτZ hτH hτP hτc
  have hu' : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u ∈
      flagSpace 3 K 1 := mem_gmap.mp hu
  have h1 := hab u
  rw [mulVec_eq_of_fix_e0 (uMat_mulVec_e0 a b 0) hu'] at h1
  have h2 := congrArg (fun x => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ x) h1
  exact (hf.eq_iff _ _).mp (by simpa only [g_ginv_mulVec] using h2)

end CFSG.Quasithin.Vol2.KGNat
