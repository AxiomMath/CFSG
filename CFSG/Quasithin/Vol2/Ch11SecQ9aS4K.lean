module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4J
public import CFSG.Quasithin.Vol2.Ch11SecQ9aSp4P

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Quasithin.Vol2.KGNat (IsCoord linModelNat psiSp psiSp_apply psiSp_injective
  map_stabilizer_eq flag_one_eq spLine gmapSp vec4 mem_gmapSp_spLine_iff v0_ne_zero
  exists_scalar_of_stab_sp)

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem lSp_dGL_eq (t : Kˣ × Kˣ) : lSp K (dGL t) = torusHom ![t.1, t.2] := by
  apply statedSp_ext
  change mat 2 K (lSp K (dGL t)) = spMat (torusHom ![t.1, t.2])
  rw [mat_lSp, spMat_torusHom, ← map_inv, coe_dGL, coe_dGL]
  ext (i | i) (k | k) <;> fin_cases i <;> fin_cases k <;> simp

theorem torus_mem_stabW (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    (a : Kˣ) : ((π (g * lSp K (dGL (a, 1)) * g⁻¹) : ↥H) : MulAut W) ∈
      Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup) := by
  have hmem : lSp K (dGL (a, 1)) ∈ stabilizer 2 K (spLine K) := by
    rw [← flag_one_eq, lSp_dGL_eq]
    exact torusHom_mem_Q2 0 _
  exact ((map_stabilizer_eq hf g (spLine K)).le ⟨_, hmem, rfl⟩).2

variable [Finite K] [CharP K 2]

theorem act_eq_pow_of_mem_stab (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    [Finite (MulAut W)] (g : StatedSp 2 K) {a : Kˣ} (ha : ∀ x : Kˣ, x ∈ Subgroup.zpowers a)
    {h : MulAut W}
    (hh : h ∈ H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) :
    ∃ k : ℕ, ∀ u ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup,
      h u = (((π (g * lSp K (dGL (a, 1)) * g⁻¹) : ↥H) : MulAut W) ^ k) u := by
  set U₁ := hf.pre (gmapSp g (spLine K)).toAddSubgroup with hU₁
  set t := ((π (g * lSp K (dGL (a, 1)) * g⁻¹) : ↥H) : MulAut W) with ht
  have htH : t ∈ H := (π _).2
  have htS : t ∈ Ch11.SecA.stabW U₁ := torus_mem_stabW hf g a
  have htf : ∀ u ∈ U₁, f (t u) = (a : K) • f u := fun u hu => act_diag_sp hf g a hu
  have htk : ∀ k : ℕ, ∀ u ∈ U₁, (t ^ k) u ∈ U₁ ∧ f ((t ^ k) u) = ((a : K) ^ k) • f u := by
    intro k
    induction k with
    | zero => intro u hu; rw [pow_zero, MulAut.one_apply, pow_zero, one_smul]; exact ⟨hu, rfl⟩
    | succ k ih =>
      intro u hu
      obtain ⟨h1, h2⟩ := ih u hu
      rw [pow_succ', MulAut.mul_apply]
      refine ⟨(Ch11.SecA.mem_stabW.mp htS _).mp h1, ?_⟩
      rw [htf _ h1, h2, smul_smul, pow_succ']
  obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
  have hu₀U : u₀ ∈ U₁ := hf.mem_pre.mpr (mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩)
  obtain ⟨M, hM⟩ : ∃ M : ↥(StatedSp 2 K), π M = ⟨h, hh.1⟩ := hf.onto ⟨h, hh.1⟩
  have hhM : h = ((π M : ↥H) : MulAut W) := by rw [hM]
  obtain ⟨c, hc⟩ := exists_scalar_of_stab_sp hf (g := g) (γ := M) fun w hw => by
    rw [← hhM]
    exact (Ch11.SecA.mem_stabW.mp hh.2 w).mp hw
  have hcU : ∀ u ∈ U₁, f (h u) = c • f u := fun u hu => by
    rw [hhM]
    exact hc u hu
  have hc0 : c ≠ 0 := by
    intro hc0
    have h1 := hcU u₀ hu₀U
    rw [hc0, zero_smul, hf.ker] at h1
    have h2 : u₀ ∈ Z := by
      have := hZ h⁻¹ (H.inv_mem hh.1) _ h1
      rw [MulAut.inv_apply_self] at this
      rw [this]
      exact h1
    rw [← hf.ker, hu₀] at h2
    exact v0_ne_zero g h2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (a : K) ^ k = c := by
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (ha (Units.mk0 c hc0)) :
      Units.mk0 c hc0 ∈ Submonoid.powers a)
    exact ⟨k, by
      rw [← Units.val_pow_eq_pow_val, show a ^ k = Units.mk0 c hc0 from hk, Units.val_mk0]⟩
  refine ⟨k, fun u hu => ?_⟩
  have htkH : (t ^ k)⁻¹ ∈ H := H.inv_mem (H.pow_mem htH k)
  have htkS : (t ^ k)⁻¹ ∈ Ch11.SecA.stabW U₁ :=
    (Ch11.SecA.stabW U₁).inv_mem ((Ch11.SecA.stabW U₁).pow_mem htS k)
  have hfix : ∀ v ∈ U₁, f (((t ^ k)⁻¹ * h) v) = f v := by
    intro v hv
    have h1 : f (h v) = f ((t ^ k) v) := by rw [hcU v hv, ← hk, (htk k v hv).2]
    have h2 := (hf.eq_iff _ _).mp h1
    have h3 := hZ _ htkH _ h2
    apply (hf.eq_iff _ _).mpr
    have e : ((t ^ k)⁻¹ * h) v * v⁻¹ = (t ^ k)⁻¹ (h v * ((t ^ k) v)⁻¹) := by
      rw [MulAut.mul_apply, map_mul, map_inv, MulAut.inv_apply_self]
    rw [e, h3]
    exact h2
  have hx := mem_gammaW_one_of_fix hK4 hf g (H.mul_mem htkH hh.1)
    ((Ch11.SecA.stabW U₁).mul_mem htkS hh.2) hfix
  have hxu := fix_gammaW_one hf hZ g _ hx u hu
  rw [MulAut.mul_apply] at hxu
  calc h u = (t ^ k) ((t ^ k)⁻¹ (h u)) := (MulAut.apply_inv_self W _ _).symm
    _ = (t ^ k) u := by rw [hxu]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
