module

public import CFSG.Quasithin.Vol2.Ch11SecAKA15
public import CFSG.Quasithin.Vol2.KGNatSL3LineFacts

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp StatedSL specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spLevi_mem_perfectCore)

namespace KA

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem exists_scalar_line_sp (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : StatedSp 2 K) {θ : W → W}
    (hθU : ∀ u ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup,
      θ u ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup)
    (hθm : ∀ u ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup,
      ∀ v ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup, θ (u * v) = θ u * θ v)
    (hθS : ∀ s ∈ perfectCore (H ⊓ Ch11.SecA.stabW
        (hf.pre (gmapSp g (spPlane K)).toAddSubgroup)),
      ∀ u ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup, θ (s u) = s (θ u)) :
    ∃ c : K, ∀ u ∈ hf.pre (gmapSp g (spPlane K)).toAddSubgroup, f (θ u) = c • f u := by
  set U₂ := hf.pre (gmapSp g (spPlane K)).toAddSubgroup with hU₂
  have hZU : Z ≤ U₂ := hf.le_pre _
  have hθZ : ∀ z ∈ Z, θ z ∈ Z := fun z hz =>
    (line_fixed hK4 hf hZ g _ (hθU z (hZU hz))).mp fun s hs => by
      rw [← hθS s hs z (hZU hz), hZ s (perfectCore_le _ hs).1 z hz]
  have hθf : ∀ u ∈ U₂, ∀ v ∈ U₂, f u = f v → f (θ u) = f (θ v) := by
    intro u hu v hv h
    have hz : u * v⁻¹ ∈ Z := (hf.eq_iff u v).mp h
    have h1 : θ u = θ (u * v⁻¹) * θ v := by
      rw [← hθm _ (U₂.mul_mem hu (U₂.inv_mem hv)) _ hv, inv_mul_cancel_right]
    rw [h1, hf.map_mul, (hf.ker _).mpr (hθZ _ hz), zero_add]
  have hsec : ∀ x : Fin 2 → K, ∃ u ∈ U₂, mat 2 K g⁻¹ *ᵥ f u = vec4 (x 0) (x 1) 0 0 :=
    fun x => by
      obtain ⟨u, hu⟩ := hf.surj (mat 2 K g *ᵥ vec4 (x 0) (x 1) 0 0)
      refine ⟨u, ?_, by rw [hu, mat_inv_mulVec]⟩
      show f u ∈ gmapSp g (spPlane K)
      rw [hu, mem_gmapSp, mat_inv_mulVec]
      exact ⟨rfl, rfl⟩
  choose sec hsecU hsecf using hsec
  have hθP : ∀ x, mat 2 K g⁻¹ *ᵥ f (θ (sec x)) ∈ spPlane K := fun x =>
    mem_gmapSp.mp (hθU _ (hsecU x))
  let T : (Fin 2 → K) →+ (Fin 2 → K) := AddMonoidHom.mk'
    (fun x => ![(mat 2 K g⁻¹ *ᵥ f (θ (sec x))) (.inl 0),
      (mat 2 K g⁻¹ *ᵥ f (θ (sec x))) (.inl 1)]) fun x y => by
      have h1 : f (sec (x + y)) = f (sec x * sec y) := by
        have e : mat 2 K g⁻¹ *ᵥ f (sec (x + y)) = mat 2 K g⁻¹ *ᵥ f (sec x * sec y) := by
          rw [hsecf, hf.map_mul, Matrix.mulVec_add, hsecf, hsecf]
          exact vec4_eq (by simp [vec4]) (by simp [vec4]) (by simp [vec4]) (by simp [vec4])
        have e2 := congrArg (fun v => mat 2 K g *ᵥ v) e
        simpa only [mat_mulVec_inv] using e2
      have h2 := hθf _ (hsecU _) _ (U₂.mul_mem (hsecU x) (hsecU y)) h1
      rw [h2, hθm _ (hsecU x) _ (hsecU y), hf.map_mul, Matrix.mulVec_add]
      ext i
      fin_cases i <;> rfl
  have hT : ∀ x, T x = ![(mat 2 K g⁻¹ *ᵥ f (θ (sec x))) (.inl 0),
      (mat 2 K g⁻¹ *ᵥ f (θ (sec x))) (.inl 1)] := fun x => rfl
  obtain ⟨c, hc⟩ := commutant_statedSL (le_refl 2) T fun γ x => by
    rw [linModelNat_lin, linModelNat_lin]
    set A : Matrix.SpecialLinearGroup (Fin 2) K :=
      (specialLinearGroupEquivStatedSL 2 K).symm γ with hA
    have hAγ : ((γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) := by
      rw [hA, ← specialLinearGroupEquivStatedSL_coe, MulEquiv.apply_symm_apply]
    rw [hAγ]
    set s := psiSp π g (spLevi 1 A) with hs
    have hsS : s ∈ perfectCore (H ⊓ Ch11.SecA.stabW U₂) := by
      rw [gamma2_eq hf g]
      exact ⟨_, spLevi_mem_perfectCore hK4 1 A, rfl⟩
    have hsU : s (sec x) ∈ U₂ :=
      (Ch11.SecA.mem_stabW.mp (perfectCore_le _ hsS).2 _).mp (hsecU x)
    have h1 : f (sec ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x)) = f (s (sec x)) := by
      have e : mat 2 K g⁻¹ *ᵥ f (sec ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x)) =
          mat 2 K g⁻¹ *ᵥ f (s (sec x)) := by
        rw [hsecf, hs, act_levi1 hf g A, hsecf, spLevi1_mulVec_plane A ⟨rfl, rfl⟩]
        exact vec4_eq (by simp [vec4, Matrix.mulVec, dotProduct, Fin.sum_univ_two])
          (by simp [vec4, Matrix.mulVec, dotProduct, Fin.sum_univ_two]) rfl rfl
      have e2 := congrArg (fun v => mat 2 K g *ᵥ v) e
      simpa only [mat_mulVec_inv] using e2
    have h2 := hθf _ (hsecU _) _ hsU h1
    rw [hθS s hsS _ (hsecU x)] at h2
    have h3 : mat 2 K g⁻¹ *ᵥ f (θ (sec ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x))) =
        mat 2 K (spLevi 1 A) *ᵥ (mat 2 K g⁻¹ *ᵥ f (θ (sec x))) := by
      rw [h2, hs, act_levi1 hf g A]
    rw [hT, hT, h3, spLevi1_mulVec_plane A (hθP x)]
    ext i
    fin_cases i <;> simp [vec4, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  refine ⟨c, fun u hu => ?_⟩
  have hu' : mat 2 K g⁻¹ *ᵥ f u ∈ spPlane K := mem_gmapSp.mp hu
  set x : Fin 2 → K := ![(mat 2 K g⁻¹ *ᵥ f u) (.inl 0), (mat 2 K g⁻¹ *ᵥ f u) (.inl 1)] with hx
  have hfu : f u = f (sec x) := by
    have e : mat 2 K g⁻¹ *ᵥ f u = mat 2 K g⁻¹ *ᵥ f (sec x) := by
      rw [hsecf]
      exact vec4_eq rfl rfl hu'.1 hu'.2
    have e2 := congrArg (fun v => mat 2 K g *ᵥ v) e
    simpa only [mat_mulVec_inv] using e2
  have h1 := hθf _ hu _ (hsecU x) hfu
  have h2 : T x = c • x := hc x
  have e0 := congrFun h2 0
  have e1 := congrFun h2 1
  rw [hT] at e0 e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul] at e0 e1
  have e : mat 2 K g⁻¹ *ᵥ f (θ u) = mat 2 K g⁻¹ *ᵥ (c • f u) := by
    rw [h1, Matrix.mulVec_smul]
    refine vec4_eq ?_ ?_ ((hθP x).1.trans ?_) ((hθP x).2.trans ?_)
    · rw [e0, Pi.smul_apply, smul_eq_mul]
      rfl
    · rw [e1, Pi.smul_apply, smul_eq_mul]
      rfl
    · rw [Pi.smul_apply, hu'.1, smul_zero]
    · rw [Pi.smul_apply, hu'.2, smul_zero]
  have e2 := congrArg (fun v => mat 2 K g *ᵥ v) e
  simpa only [mat_mulVec_inv] using e2

variable [Finite K] [CharP K 2] [Finite W]

theorem lineFacts_sp (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : StatedSp 2 K) :
    Ch11.SecA.LineFacts H Z (hf.pre (gmapSp g (spPlane K)).toAddSubgroup) := by
  set U₂ := hf.pre (gmapSp g (spPlane K)).toAddSubgroup with hU₂
  refine ⟨line_radical hK4 hf hZ g, line_moves hK4 hf g, line_fixed hK4 hf hZ g,
    line_comm hK4 hf g, ?_⟩
  intro φ ψ hφU hψU hφm hψm hφS hψS
  obtain ⟨c, hc⟩ := exists_scalar_line_sp hK4 hf hZ g hφU hφm hφS
  obtain ⟨d, hd⟩ := exists_scalar_line_sp hK4 hf hZ g hψU hψm hψS
  have hχZ : ∀ u ∈ U₂, φ (ψ u) * (ψ (φ u))⁻¹ ∈ Z := fun u hu => (hf.eq_iff _ _).mp (by
    rw [hc _ (hψU u hu), hd u hu, hd _ (hφU u hu), hc u hu, smul_smul, smul_smul, mul_comm])
  let C : Subgroup W :=
    { carrier := {y | y ∈ U₂ ∧ φ (ψ y) = ψ (φ y)}
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
        rw [hψm _ ha.1 _ hb.1, hφm _ (hψU _ ha.1) _ (hψU _ hb.1), ha.2, hb.2,
          hφm _ ha.1 _ hb.1, hψm _ (hφU _ ha.1) _ (hφU _ hb.1)]⟩
      one_mem' := ⟨Subgroup.one_mem _, by
        rw [map_one_of_mul hψm, map_one_of_mul hφm, map_one_of_mul hψm]⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
        rw [map_inv_of_mul hψm ha.1, map_inv_of_mul hφm (hψU _ ha.1), ha.2,
          map_inv_of_mul hφm ha.1, map_inv_of_mul hψm (hφU _ ha.1)]⟩ }
  have hle : Ch11.SecA.commS (perfectCore (H ⊓ Ch11.SecA.stabW U₂)) U₂ ≤ C := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨s, hs, u, hu, rfl⟩
    have hst := Ch11.SecA.mem_stabW.mp (perfectCore_le _ hs).2
    have hsu := (hst u).mp hu
    have hψu := hψU u hu
    have hφu := hφU u hu
    refine ⟨Subgroup.mul_mem _ hsu (Subgroup.inv_mem _ hu), ?_⟩
    rw [hψm _ hsu _ (Subgroup.inv_mem _ hu), map_inv_of_mul hψm hu, hψS s hs u hu,
      hφm _ ((hst _).mp hψu) _ (Subgroup.inv_mem _ hψu), map_inv_of_mul hφm hψu,
      hφS s hs _ hψu, hφm _ hsu _ (Subgroup.inv_mem _ hu), map_inv_of_mul hφm hu,
      hφS s hs u hu, hψm _ ((hst _).mp hφu) _ (Subgroup.inv_mem _ hφu),
      map_inv_of_mul hψm hφu, hψS s hs _ hφu]
    obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ Z, φ (ψ u) = z * ψ (φ u) := ⟨_, hχZ u hu, by group⟩
    rw [hzdef, map_mul, hZ s (perfectCore_le _ hs).1 z hz, mul_comm z, _root_.mul_inv_rev,
      mul_comm (ψ (φ u))⁻¹, mul_assoc, mul_inv_cancel_left]
  intro y hy
  exact (hle hy).2

end KA

end CFSG.Quasithin.Vol2.KGNat
