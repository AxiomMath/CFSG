module

public import CFSG.Quasithin.Vol2.KGNatSL3Lev
public import CFSG.Quasithin.Vol2.KGNatPointT
public import CFSG.Quasithin.Vol2.KGNatSL3Torus
public import CFSG.Quasithin.Vol2.Ch11SecEFacts3

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type*} [CommGroup W]
  {H : Subgroup (MulAut W)} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem mem_of_linear_two (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ π f) {s : MulAut W}
    {m : ℕ} (hm : s ^ 2 ^ m = 1) (TL : (Fin 3 → K) →ₗ[K] (Fin 3 → K))
    (hTL : ∀ w, TL (f w) = f (s w)) : s ∈ H := by
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h =>
    mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))
  set A := LinearMap.toMatrix' TL with hA
  have hAv : ∀ v, A *ᵥ v = TL v := fun v => by
    rw [hA, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have hpow : ∀ j : ℕ, ∀ w, (A ^ j) *ᵥ f w = f ((s ^ j) w) := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, pow_zero, Matrix.one_mulVec, MulAut.one_apply]
    | succ j ih =>
      intro w
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ih, hAv, hTL, MulAut.mul_apply]
  have hA1 : A ^ 2 ^ m = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := hf.surj v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hpow, hm, MulAut.one_apply, Matrix.one_mulVec]
  have hdet : A.det = 1 :=
    eq_one_of_pow_two_pow (by rw [← Matrix.det_pow, hA1, Matrix.det_one])
  set B : SpecialLinearGroup (Fin 3) K := ⟨A, hdet⟩
  have hsB : s = ((rho3 π B : ↥H) : MulAut W) := by
    ext w
    apply hinj
    rw [hf.act3, ← hTL]
    exact (hAv (f w)).symm
  rw [hsB]
  exact (rho3 π B).2

omit [Finite K] [CharP K 2] in
theorem uMat_mulVec_e2 (t : K) : uMat 0 0 t *ᵥ ![0, 0, 1] = ![0, 0, 1] + t • ![0, 1, 0] := by
  rw [uMat_mulVec]
  exact vec3_eq (by simp) (by simp) (by simp)

theorem sigma_eq_id_of_centralizes (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    {Z : Subgroup W} (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) {s : MulAut W} (hsZ : ∀ z ∈ Z, s z ∈ Z)
    (hsU : s ∈ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))
    (hcomm : ∀ k ∈ perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)),
      s * k * s⁻¹ * k⁻¹ ∈ pCoreOf 2 (perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup))))
    {σ : K →+* K}
    (hσ : ∀ (c : K) (x : Fin 3 → K), hf.autMap s hsZ (c • x) = σ c • hf.autMap s hsZ x) :
    ∀ c, σ c = c := by
  set T := hf.autMap s hsZ with hTdef
  have hTf : ∀ w, T (f w) = f (s w) := hf.autMap_apply s hsZ
  have hUmem : ∀ w, w ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup ↔
      ∃ t : K, f w = t • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := fun w => by
    rw [← stdLine_eq_flagSpace]
    exact mem_gmap_stdLine_iff
  obtain ⟨y, hydef⟩ : ∃ y : Fin 3 → K, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0]) = y :=
    ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : Fin 3 → K, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) = z :=
    ⟨_, rfl⟩
  have key : ∀ t : K, σ t * y 1 = t * z 2 ∧ σ t * y 2 = 0 := by
    intro t
    have hkL : ((rho3 π (g * uSL 0 0 t * g⁻¹) : ↥H) : MulAut W) ∈ perfectCore (H ⊓
        Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) :=
      (mem_perfectCore_HU1_iff hSL hf g _).mpr ⟨uSL 0 0 t, uMat_mulVec_e0 0 0 t, rfl⟩
    obtain ⟨B, hB, hBeq⟩ := levi_of_mem_pCoreOf_HU1 hSL hf g (hcomm _ hkL)
    obtain ⟨w₀, hw₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1])
    set k := ((rho3 π (g * uSL 0 0 t * g⁻¹) : ↥H) : MulAut W) with hk
    have hid : (s * k * s⁻¹ * k⁻¹) (k (s w₀)) = s (k w₀) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self,
        MulAut.inv_apply_self]
    have hLHS : f ((s * k * s⁻¹ * k⁻¹) (k (s w₀))) = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((B : Matrix (Fin 3) (Fin 3) K) *ᵥ (uMat 0 0 t *ᵥ z)) := by
      rw [hBeq, hf.act3, hk, hf.act3, ← hTf, hw₀, gconj_mulVec, gconj_mulVec, ginv_g_mulVec,
        coe_uSL, hzdef]
    have hRHS : f (s (k w₀)) = T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) +
        σ t • T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0]) := by
      rw [← hTf, hk, hf.act3, hw₀, gconj_mulVec, ginv_g_mulVec, coe_uSL, uMat_mulVec_e2,
        Matrix.mulVec_add, Matrix.mulVec_smul, map_add, hσ]
    have h1 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) (hLHS.symm.trans ((congrArg f hid).trans hRHS))
    simp only [ginv_g_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, hydef, hzdef] at h1
    obtain ⟨hB1, hB2⟩ := hB (uMat 0 0 t *ᵥ z)
    rw [h1, uMat_mulVec] at hB1 hB2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hB1 hB2
    exact ⟨by linear_combination hB1, by linear_combination hB2⟩
  obtain ⟨h11, h12⟩ := key 1
  simp only [map_one, one_mul] at h11 h12
  have hy1 : y 1 ≠ 0 := by
    intro h0
    have hy' : y = y 0 • ![1, 0, 0] := vec3_eq (by simp) (by simp [h0]) (by simp [h12])
    obtain ⟨w₁, hw₁⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0])
    have hsw : s w₁ ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
      refine (hUmem _).mpr ⟨y 0, ?_⟩
      rw [← hTf, hw₁, ← g_ginv_mulVec g (T ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 1, 0])),
        hydef]
      conv_lhs => rw [hy']
      rw [Matrix.mulVec_smul]
    obtain ⟨t', ht'⟩ := (hUmem w₁).mp ((Ch11.SecA.mem_stabW.mp hsU w₁).mpr hsw)
    rw [hw₁] at ht'
    have h2 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) ht'
    simp only [ginv_g_mulVec, Matrix.mulVec_smul] at h2
    have h3 := congrFun h2 1
    simp at h3
  intro c
  obtain ⟨hc, -⟩ := key c
  rw [← h11] at hc
  exact mul_right_cancel₀ hy1 hc

theorem factParInSL3_holds : Ch11.SecE.FactParInSL3 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU S hS2 hSH hSU _ s hs hcomm
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  have hUeq := eq_U1_of_isFlagW hW hf hg hU
  subst hUeq
  have hs' : ∀ h ∈ H, s⁻¹ * h * s ∈ H := fun h hh => by
    have := hSH s⁻¹ (S.inv_mem hs) h hh
    rwa [inv_inv] at this
  have he0 : (![1, 0, 0] : Fin 3 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    he0 s (bot_maps s) (bot_maps s⁻¹) hs'
  have hσid := sigma_eq_id_of_centralizes hSL hf g (bot_maps s) (hSU hs) hcomm hσ
  set T := hf.autMap s (bot_maps s) with hTdef
  let TL : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := T
      map_add' := map_add T
      map_smul' := fun c v => by rw [hσ, hσid]; rfl }
  obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
  have hm' : s ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
  exact mem_of_linear_two hf hm' TL (hf.autMap_apply s (bot_maps s))

end CFSG.Quasithin.Vol2.KGNat
