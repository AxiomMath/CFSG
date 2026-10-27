module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.MultNatCoords
public import CFSG.Quasithin.Background.HMultFix
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136FixCount

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mult

theorem exists_coords_of_iSup_realizesVia {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {W : Type} [CommGroup W] [Finite W] (Γ : Subgroup (GL ι K))
    {L : Subgroup (MulAut W)} {π : ↥Γ →* ↥L} (𝒮 : Set (Subgroup W)) (hsup : ⨆ I ∈ 𝒮, I = ⊤)
    (hirr : ∀ I ∈ 𝒮, IsIrrOn L I ⊥)
    (hreal : ∀ I ∈ 𝒮, (FFModel.nat Γ).RealizesVia L I ⊥ π) :
    ∃ (m : ℕ) (e : W ≃* StdMod (Fin m × ι) K), ∀ (γ : ↥Γ) (w : W),
      e (((π γ : ↥L) : MulAut W) w) = matAut (diagGL m (γ : GL ι K)) (e w) := by
  classical
  obtain ⟨k, J, hJmem, hind, hsupJ⟩ :=
    CFSG.LocalAnalysis.WeakClosure81.GF2Reps136.w1369_exists_indep_family (L := L) (C := ⊥)
      𝒮 (Set.toFinite 𝒮) fun M hM => ⟨bot_le, hirr M hM⟩
  have hsup' : (⊥ ⊔ ⨆ i, J i) = ⊤ := by rw [hsupJ, bot_sup_eq, hsup]
  obtain ⟨-, e, -, he, -⟩ :=
    exists_coords_of_sumOfNatVia (K := K) Γ (H := L) (k := k) (π := π)
      ⟨J, fun _ => bot_le, hind, hsup', fun i => hreal (J i) (hJmem i)⟩
  exact ⟨k, e, he⟩

theorem exists_hom_kronGL_of_commute {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {K : Type} [Field K] [Finite K] {W : Type} [CommGroup W] (Γ : Subgroup (GL ι K))
    (hΓ : HasScalarCommutant Γ) {L : Subgroup (MulAut W)} {π : ↥Γ →* ↥L}
    (hπ : Function.Surjective π) {m : ℕ} (e : W ≃* StdMod (Fin m × ι) K)
    (he : ∀ (γ : ↥Γ) (w : W),
      e (((π γ : ↥L) : MulAut W) w) = matAut (diagGL m (γ : GL ι K)) (e w))
    {L₂ : Subgroup (MulAut W)} (hcomm : ∀ x ∈ L, ∀ y ∈ L₂, x * y = y * x) :
    ∃ ψ : ↥L₂ →* GL (Fin m) K, Function.Injective ψ ∧
      ∀ (y : ↥L₂) (w : W), e ((y : MulAut W) w) = matAut (kronGL ι m (ψ y)) (e w) := by
  classical
  have hmap : L.map (congrHom e) = natImage (diagSub m Γ) :=
    map_congrHom_eq_natImage_diag Γ hπ e he
  let κ : GL (Fin m) K →* MulAut (StdMod (Fin m × ι) K) :=
    (matHom (ι := Fin m × ι) (K := K)).comp (kronGL (ι := ι) (K := K) m)
  have hκinj : Function.Injective κ := fun B C hBC =>
    kronGL_injective (ι := ι) (K := K) m (matHom_injective hBC)
  have hcen : ∀ y : ↥L₂, congrHom e ((y : ↥L₂) : MulAut W) ∈
      Subgroup.centralizer (natImage (diagSub m Γ) : Set (MulAut (StdMod (Fin m × ι) K))) := by
    intro y
    rw [← hmap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y y.2]
  have hex : ∀ y : ↥L₂, ∃ B : GL (Fin m) K,
      congrHom e ((y : ↥L₂) : MulAut W) = κ B := by
    intro y
    obtain ⟨B, hB⟩ :=
      (mem_centralizer_diag_iff (k := m) (Γ := Γ) hΓ).mp (hcen y)
    exact ⟨B, hB⟩
  let B : ↥L₂ → GL (Fin m) K := fun y => Classical.choose (hex y)
  have hB : ∀ y : ↥L₂, congrHom e ((y : ↥L₂) : MulAut W) = κ (B y) :=
    fun y => Classical.choose_spec (hex y)
  have hBone : B 1 = 1 := by
    apply hκinj
    have h1 : congrHom e ((1 : ↥L₂) : MulAut W) = 1 := by
      rw [Subgroup.coe_one, map_one (congrHom e)]
    rw [← hB 1, h1]
    exact (map_one κ).symm
  have hBmul : ∀ y y' : ↥L₂, B (y * y') = B y * B y' := by
    intro y y'
    apply hκinj
    have h1 : congrHom e (((y * y' : ↥L₂)) : MulAut W) =
        congrHom e ((y : ↥L₂) : MulAut W) * congrHom e ((y' : ↥L₂) : MulAut W) := by
      rw [Subgroup.coe_mul, map_mul (congrHom e)]
    rw [← hB (y * y'), h1, hB y, hB y', ← map_mul κ]
  refine ⟨{ toFun := B, map_one' := hBone, map_mul' := hBmul }, ?_, ?_⟩
  ·
    intro y y' hyy'
    have h1 : ((y : ↥L₂) : MulAut W) = ((y' : ↥L₂) : MulAut W) := by
      apply congrHom_injective e
      rw [hB y, hB y']
      exact congrArg κ hyy'
    exact Subtype.ext h1
  ·
    intro y w
    have h := congrArg (fun g : MulAut (StdMod (Fin m × ι) K) => g (e w)) (hB y)
    rw [congrHom_apply, MulEquiv.symm_apply_apply] at h
    exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
