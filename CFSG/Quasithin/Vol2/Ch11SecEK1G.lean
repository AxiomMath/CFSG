module

public import CFSG.Quasithin.Vol2.Ch11SecEK1F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Quasithin CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Open (pCoreOf)
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)

namespace EK1

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem mem_of_linear_root (hf : IsCoord (linModelNat (StatedSL 3 K)) H ⊥ π f) {s : MulAut W}
    {m : ℕ} (hm : s ^ m = 1) (hroot : ∀ x : K, x ^ m = 1 → x = 1)
    (TL : (Fin 3 → K) →ₗ[K] (Fin 3 → K)) (hTL : ∀ w, TL (f w) = f (s w)) : s ∈ H := by
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
  have hA1 : A ^ m = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, rfl⟩ := hf.surj v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hpow, hm, MulAut.one_apply, Matrix.one_mulVec]
  have hdet : A.det = 1 := hroot _ (by rw [← Matrix.det_pow, hA1, Matrix.det_one])
  set B : Matrix.SpecialLinearGroup (Fin 3) K := ⟨A, hdet⟩
  have hsB : s = ((rho3 π B : ↥H) : MulAut W) := by
    ext w
    apply injective_of_bot hf
    rw [hf.act3, ← hTL]
    exact (hAv (f w)).symm
  rw [hsB]
  exact (rho3 π B).2

end EK1

open EK1 in
theorem factCentLeviSL3_holds : FactCentLeviSL3 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU β hβH _ hc ⟨m, hmo, hmc, hβm⟩
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hroot : ∀ x : K, x ^ m = 1 → x = 1 := fun x hx =>
    eq_one_of_pow_coprime hK hmo.pos.ne' hmc hx
  have hSL := commutator_SL2_eq_top (four_le_card hn hK)
  have hfix := factRadicalFixedSL3_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hpt := factPointSL3_holds K n hn hK W hW H ⊥ π hπ P hP U hU
  have hβU := mem_stabW_of_comm hfix hpt hc
  have htorus := factTorusPointSL3_holds K n hn hK W hW H π hπ P hP U hU
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK] at hU
  have hUeq := eq_U1_of_isFlagW hW hf hg hU
  subst hUeq
  have he0 : (![1, 0, 0] : Fin 3 → K) ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear (fun T hT => commutant_statedSL (by norm_num) T hT)
    he0 β (bot_maps β) (bot_maps β⁻¹) (inv_conj_mem_of_conj_mem hβH)
  have hσid := sigma_eq_id_of_centralizes hSL hf g (bot_maps β) hβU hc hσ
  set T := hf.autMap β (bot_maps β) with hTdef
  have hTf : ∀ w, T (f w) = f (β w) := hf.autMap_apply β (bot_maps β)
  have hTs : ∀ (c : K) v, T (c • v) = c • T v := fun c v => by rw [hσ, hσid]
  let TL : (Fin 3 → K) →ₗ[K] (Fin 3 → K) :=
    { toFun := T
      map_add' := map_add T
      map_smul' := hTs }
  have hβH' : β ∈ H := mem_of_linear_root hf hβm hroot TL hTf
  have hβS : β ∈ H ⊓ SecA.stabW (hf.pre (gmap g (stdLine K)).toAddSubgroup) := by
    rw [stdLine_eq_flagSpace]
    exact ⟨hβH', hβU⟩
  obtain ⟨c, hcU⟩ := exists_scalar_of_mem_stab hf g hβS
  obtain ⟨w₀, hw₀⟩ := hf.surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0])
  have hw₀U : f w₀ ∈ gmap g (stdLine K) := mem_gmap_stdLine_iff.mpr ⟨1, by rw [hw₀, one_smul]⟩
  have hv0 : f w₀ ≠ 0 := by
    rw [hw₀]
    intro h
    have h1 := congrArg (fun v => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) *ᵥ v) h
    simp only [ginv_g_mulVec, Matrix.mulVec_zero] at h1
    exact he0 h1
  have hpow : ∀ j : ℕ, f ((β ^ j) w₀) = ((c : K) ^ j) • f w₀ := by
    intro j
    induction j with
    | zero => rw [pow_zero, pow_zero, one_smul, MulAut.one_apply]
    | succ j ih =>
      rw [pow_succ' β j, MulAut.mul_apply, ← hTf, ih, hTs, hTf, hcU w₀ hw₀U, smul_smul,
        pow_succ (c : K) j]
  have hcm : (c : K) ^ m = 1 := by
    have h1 := hpow m
    rw [hβm, MulAut.one_apply] at h1
    have h2 : ((c : K) ^ m - 1) • f w₀ = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)
  have hβw₀ : β w₀ = w₀ := injective_of_bot hf (by rw [hcU w₀ hw₀U, hroot _ hcm, one_smul])
  have hw₀U' : w₀ ∈ hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
    show f w₀ ∈ gmap g (flagSpace 3 K 1)
    rw [← stdLine_eq_flagSpace]
    exact hw₀U
  have hw₀1 : w₀ ≠ 1 := by
    rintro rfl
    exact hv0 hf.map_one
  obtain ⟨a, ha⟩ := htorus β hβH' w₀ hw₀U' hw₀1 hβw₀ hc
  exact eq_one_of_odd_of_two_pow hmo hβm ha

end CFSG.Quasithin.Vol2.Ch11.SecE
