module

public import CFSG.Quasithin.Vol2.KGNatSL3Row
public import CFSG.Quasithin.Vol2.KGNatSL3Par

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Assembly.LowTwoRank (StatedSL specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open scoped MatrixGroups

variable {K : Type} [Field K]

variable (K) in
@[expose] def p01 [CharP K 2] : SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    rw [show (0 : K) * 0 * 1 - 0 * 0 * 0 - 1 * 1 * 1 + 1 * 0 * 0 + 0 * 1 * 0 - 0 * 0 * 0 = -1 by
      ring]
    exact CharTwo.neg_eq 1⟩

theorem p01_mulVec [CharP K 2] (x : Fin 3 → K) :
    (p01 K : Matrix (Fin 3) (Fin 3) K) *ᵥ x = ![x 1, x 0, x 2] := by
  ext i
  fin_cases i <;> simp [p01, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem p01_inv [CharP K 2] : (p01 K)⁻¹ = p01 K := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  apply Matrix.toLin'.injective
  refine LinearMap.ext fun x => ?_
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, p01_mulVec, p01_mulVec,
    Matrix.one_mulVec]
  exact vec3_eq (by simp) (by simp) (by simp)

variable (K) in
@[expose] def sl2Up : SL(2, K) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

variable (K) in
@[expose] def sl2Low : SL(2, K) := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩

theorem blockSL_up_mulVec (x : Fin 3 → K) :
    (blockSL (sl2Up K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = ![x 0 + x 1, x 1, x 2] := by
  rw [blockSL_mulVec]
  exact vec3_eq (by simp [sl2Up]) (by simp [sl2Up]) (by simp)

theorem blockSL_low_mulVec (x : Fin 3 → K) :
    (blockSL (sl2Low K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x = ![x 0, x 0 + x 1, x 2] := by
  rw [blockSL_mulVec]
  exact vec3_eq (by simp [sl2Low]) (by simp [sl2Low]) (by simp)

section Coord

variable [Finite K] {W : Type*} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

omit [Finite K] [Finite W] in
theorem mem_pre_line_iff (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) (w : W) :
    w ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup ↔
      ∃ t : K, f w = t • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := by
  rw [← stdLine_eq_flagSpace]
  exact mem_gmap_stdLine_iff

omit [Finite K] [Finite W] in
theorem mem_pre_plane_iff (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    (g : SpecialLinearGroup (Fin 3) K) (w : W) :
    w ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup ↔
      (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f w) 2 = 0 := by
  rw [← stdPlane_eq_flagSpace]
  exact mem_gmap

theorem fix_HU1 (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : SpecialLinearGroup (Fin 3) K) :
    ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)),
      ∀ u ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup, h u = u := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  refine fix_of_perfect (Z := Z) (perfectCore_perfect _)
    (fun h hh z hz => hZ h (perfectCore_le _ hh).1 z hz) ?_
  intro h hh u hu
  obtain ⟨B, hB, rfl⟩ := (mem_perfectCore_HU1_iff hSL hf g h).mp hh
  have hu' : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u ∈
      flagSpace 3 K 1 := mem_gmap.mp hu
  rw [← hf.ker, hf.map_mul_inv, hf.act3, gconj_mulVec, mulVec_eq_of_fix_e0 hB hu',
    g_ginv_mulVec, sub_self]

omit [Finite W] in
theorem fixed_plane_iff (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : SpecialLinearGroup (Fin 3) K) {u : W}
    (hu : u ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup) :
    (∀ s ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)),
      s u = u) ↔ u ∈ Z := by
  refine ⟨fun hfix => ?_, fun hz s hs => hZ s (perfectCore_le _ hs).1 u hz⟩
  have hx2 := (mem_pre_plane_iff hf g u).mp hu
  have key : ∀ A : SL(2, K), (blockSL A : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u) =
      ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u := by
    intro A
    have h1 := congrArg f (hfix _ ((mem_perfectCore_HU2_iff hSL hf g _).mpr
      ⟨blockSL A, blockSL_mem A, rfl⟩))
    rw [hf.act3, gconj_mulVec] at h1
    have h2 := congrArg (fun v => ((g⁻¹ : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) h1
    simp only [ginv_g_mulVec] at h2
    exact h2
  have k1 := congrFun (key (sl2Up K)) 0
  have k2 := congrFun (key (sl2Low K)) 1
  rw [blockSL_up_mulVec] at k1
  rw [blockSL_low_mulVec] at k2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_eq_left, add_eq_right] at k1 k2
  have hx0 : ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u = 0 :=
    vec3_eq (by simpa using k2) (by simpa using k1) (by simpa using hx2)
  rw [← hf.ker, ← g_ginv_mulVec g (f u), hx0, Matrix.mulVec_zero]

omit [Finite W] in
theorem exists_scalar_line (hSL : commutator (SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : SpecialLinearGroup (Fin 3) K) {θ : W → W}
    (hθU : ∀ u ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup,
      θ u ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)
    (hθm : ∀ u ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup,
      ∀ v ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup, θ (u * v) = θ u * θ v)
    (hθS : ∀ s ∈ perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup)),
      ∀ u ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup, θ (s u) = s (θ u)) :
    ∃ c : K, ∀ u ∈ hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup, f (θ u) = c • f u := by
  set U₂ := hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup with hU₂
  have hZU : Z ≤ U₂ := hf.le_pre _
  have hθZ : ∀ z ∈ Z, θ z ∈ Z := fun z hz =>
    (fixed_plane_iff hSL hf hZ g (hθU z (hZU hz))).mp fun s hs => by
      rw [← hθS s hs z (hZU hz), hZ s (perfectCore_le _ hs).1 z hz]
  have hθf : ∀ u ∈ U₂, ∀ v ∈ U₂, f u = f v → f (θ u) = f (θ v) := by
    intro u hu v hv h
    have hz : u * v⁻¹ ∈ Z := (hf.eq_iff u v).mp h
    have h1 : θ u = θ (u * v⁻¹) * θ v := by
      rw [← hθm _ (U₂.mul_mem hu (U₂.inv_mem hv)) _ hv, inv_mul_cancel_right]
    rw [h1, hf.map_mul, (hf.ker _).mpr (hθZ _ hz), zero_add]
  have hsec : ∀ x : Fin 2 → K, ∃ u ∈ U₂,
      f u = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![x 0, x 1, 0] := fun x => by
    obtain ⟨u, hu⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![x 0, x 1, 0])
    refine ⟨u, (mem_pre_plane_iff hf g u).mpr ?_, hu⟩
    rw [hu, ginv_g_mulVec]
    rfl
  choose sec hsecU hsecf using hsec
  have hθsec : ∀ x, ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f (θ (sec x)) = ![(((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f (θ (sec x))) 0, (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        f (θ (sec x))) 1, 0] := fun x =>
    vec3_eq rfl rfl (((mem_pre_plane_iff hf g _).mp (hθU _ (hsecU x))).trans rfl)
  let T : (Fin 2 → K) →+ (Fin 2 → K) := AddMonoidHom.mk'
    (fun x => ![(((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f (θ (sec x))) 0, (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f (θ (sec x))) 1]) fun x y => by
      have h1 : f (sec (x + y)) = f (sec x * sec y) := by
        rw [hf.map_mul, hsecf, hsecf, hsecf, ← Matrix.mulVec_add]
        congr 1
        exact vec3_eq (by simp) (by simp) (by simp)
      have h2 := hθf _ (hsecU _) _ (U₂.mul_mem (hsecU x) (hsecU y)) h1
      rw [h2, hθm _ (hsecU x) _ (hsecU y), hf.map_mul, Matrix.mulVec_add]
      ext i
      fin_cases i <;> rfl
  have hT : ∀ x, T x = ![(((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f (θ (sec x))) 0, (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      f (θ (sec x))) 1] := fun x => rfl
  obtain ⟨c, hc⟩ := commutant_statedSL (le_refl 2) T fun γ x => by
    rw [linModelNat_lin, linModelNat_lin]
    set A : SL(2, K) := (specialLinearGroupEquivStatedSL 2 K).symm γ with hA
    have hAγ : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) := by
      rw [hA, ← specialLinearGroupEquivStatedSL_coe, MulEquiv.apply_symm_apply]
    rw [hAγ]
    set s := ((rho3 π (g * blockSL A * g⁻¹) : ↥H) : MulAut W) with hs
    have hsS : s ∈ perfectCore (H ⊓ Ch11.SecA.stabW U₂) :=
      (mem_perfectCore_HU2_iff hSL hf g _).mpr ⟨blockSL A, blockSL_mem A, rfl⟩
    have hsU : s (sec x) ∈ U₂ :=
      (Ch11.SecA.mem_stabW.mp (perfectCore_le _ hsS).2 _).mp (hsecU x)
    have h1 : f (sec ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x)) = f (s (sec x)) := by
      rw [hsecf, hs, hf.act3, gconj_mulVec, hsecf, ginv_g_mulVec, blockSL_mulVec]
      congr 1
      exact vec3_eq (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two])
        (by simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]) (by simp)
    have h2 := hθf _ (hsecU _) _ hsU h1
    rw [hθS s hsS _ (hsecU x), hs, hf.act3, gconj_mulVec] at h2
    rw [hT, hT, h2, ginv_g_mulVec, hθsec x, blockSL_mulVec]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨c, fun u hu => ?_⟩
  have hu2 := (mem_pre_plane_iff hf g u).mp hu
  set x : Fin 2 → K := ![(((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
    f u) 0, (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f u) 1]
    with hx
  have hfu : f u = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![x 0, x 1, 0] := by
    conv_lhs => rw [← g_ginv_mulVec g (f u)]
    congr 1
    exact vec3_eq rfl rfl (hu2.trans rfl)
  have h1 := hθf _ hu _ (hsecU x) (hfu.trans (hsecf x).symm)
  have h2 : T x = c • x := hc x
  rw [h1, ← g_ginv_mulVec g (f (θ (sec x))), hθsec x, hfu, ← Matrix.mulVec_smul]
  congr 1
  have e0 := congrFun h2 0
  have e1 := congrFun h2 1
  rw [hT] at e0 e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul] at e0 e1
  exact vec3_eq (by rw [e0]; rfl) (by rw [e1]; rfl) (by simp)

end Coord

end CFSG.Quasithin.Vol2.KGNat
