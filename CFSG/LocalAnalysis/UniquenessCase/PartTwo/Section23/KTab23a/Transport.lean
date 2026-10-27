module

public import CFSG.Quasithin.Background.B4Models
import CFSG.Quasithin.Background.FFC4Zmod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Quasithin
open scoped Matrix

private lemma exists_equiv_intertwining {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    {π : ↥Γ →* ↥H} (hR : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) :
    ∃ Φ : W ≃ (ι → K), ∀ (γ : ↥Γ) (w : W),
      Φ (((π γ : ↥H) : MulAut W) w) =
        (((γ : GL ι K) : Matrix ι ι K)).mulVec (Φ w) := by
  classical
  obtain ⟨f, hfs, hfk, hfe⟩ := CFSG.Quasithin.FFC.exists_natMap (V := W) hR
  have hf_inj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (by simpa using (Subgroup.mem_bot.1 ((hfk u).1 hu)))
  let g : W →* Multiplicative (ι → K) :=
    f.comp (Subgroup.topEquiv (G := W)).symm.toMonoidHom
  have hg_inj : Function.Injective g := by
    intro a b hab
    exact (Subgroup.topEquiv (G := W)).symm.injective (hf_inj (by simpa [g] using hab))
  have hg_surj : Function.Surjective g :=
    hfs.comp (Subgroup.topEquiv (G := W)).symm.surjective
  let Φ : W ≃ (ι → K) :=
    (MulEquiv.ofBijective g ⟨hg_inj, hg_surj⟩).toEquiv.trans Multiplicative.toAdd
  have hΦ_apply : ∀ w : W, Φ w = (g w).toAdd := fun w => rfl
  have hg_smul : ∀ (γ : ↥Γ) (w : W),
      g (((π γ : ↥H) : MulAut W) w) = natAct Γ γ (g w) := by
    intro γ w
    have h := hfe γ ((Subgroup.topEquiv (G := W)).symm w) (Subgroup.mem_top _)
    have hg1 : g (((π γ : ↥H) : MulAut W) w) =
        f ⟨((π γ : ↥H) : MulAut W) w, Subgroup.mem_top _⟩ := by
      show f ((Subgroup.topEquiv (G := W)).symm (((π γ : ↥H) : MulAut W) w)) =
        f ⟨((π γ : ↥H) : MulAut W) w, Subgroup.mem_top _⟩
      exact congrArg f (Subtype.ext (Subgroup.topEquiv_symm_apply_coe _))
    have hg2 : g w = f ((Subgroup.topEquiv (G := W)).symm w) := rfl
    have hsub : (⟨((π γ : ↥H) : MulAut W) w, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        ⟨((π γ : ↥H) : MulAut W) ((Subgroup.topEquiv (G := W)).symm w : W),
          Subgroup.mem_top _⟩ := by
      refine Subtype.ext ?_
      rw [Subgroup.topEquiv_symm_apply_coe]
    rw [hg1, hg2, hsub]
    exact h
  refine ⟨Φ, ?_⟩
  intro γ w
  rw [hΦ_apply, hΦ_apply, hg_smul γ w]
  simp [natAct]

private lemma mem_fixedPointSubgroup_iff {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    {π : ↥Γ →* ↥H} {S : Subgroup ↥H} (hsurj : Function.Surjective π) (Φ : W ≃ (ι → K))
    (hΦ : ∀ (γ : ↥Γ) (w : W), Φ (((π γ : ↥H) : MulAut W) w) =
      (((γ : GL ι K) : Matrix ι ι K)).mulVec (Φ w)) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp S.subtype)
    ∀ w : W, (w ∈ CFSG.fixedPointSubgroup ↥S W) ↔
      (∀ s ∈ S.comap π, (((s : GL ι K) : Matrix ι ι K)).mulVec (Φ w) = Φ w) := by
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp S.subtype)
  intro w
  rw [FixedPoints.mem_subgroup]
  constructor
  · intro hw s hs
    have hsp : (π s : ↥H) ∈ S := Subgroup.mem_comap.1 hs
    have h1 : (((π s : ↥H) : MulAut W)) w = w := by
      have h := hw ⟨π s, hsp⟩
      simpa [MulAction.compHom_smul_def, Subgroup.smul_def, MulAut.smul_def] using h
    have h2 := congrArg Φ h1
    rwa [hΦ s w] at h2
  · intro hw s
    obtain ⟨t, ht⟩ := hsurj (S.subtype s)
    have htmem : t ∈ S.comap π := Subgroup.mem_comap.2 (ht.symm ▸ s.2)
    have h1 : (((t : GL ι K) : Matrix ι ι K)).mulVec (Φ w) = Φ w := hw t htmem
    have h2 : Φ (((π t : ↥H) : MulAut W) w) = Φ w := by
      rw [hΦ t w]
      exact h1
    have h3 : (((π t : ↥H) : MulAut W)) w = w := Φ.injective h2
    have hs' : s • w = (((S.subtype s : ↥H) : MulAut W)) w := by
      simp [MulAction.compHom_smul_def, Subgroup.smul_def, MulAut.smul_def]
    calc s • w = (((S.subtype s : ↥H) : MulAut W)) w := hs'
      _ = (((π t : ↥H) : MulAut W)) w :=
            congrArg (fun x : ↥H => ((x : MulAut W) w)) ht.symm
      _ = w := h3

theorem card_fixedPointSubgroup_eq_of_realizesVia {W : Type} [CommGroup W] {ι : Type} [Fintype ι]
    [DecidableEq ι] {K : Type} [Field K] {Γ : Subgroup (GL ι K)} {H : Subgroup (MulAut W)}
    {π : ↥Γ →* ↥H} (hR : (FFModel.nat Γ).RealizesVia H ⊤ ⊥ π) (S : Subgroup ↥H) :
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp S.subtype)
    Nat.card (CFSG.fixedPointSubgroup ↥S W) =
      Nat.card {v : ι → K // ∀ s ∈ S.comap π, ((s : GL ι K) : Matrix ι ι K) *ᵥ v = v} := by
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp S.subtype)
  have hsurj : Function.Surjective π := hR.1
  obtain ⟨Φ, hΦ⟩ := exists_equiv_intertwining hR
  have hmem := mem_fixedPointSubgroup_iff (S := S) hsurj Φ hΦ
  exact Nat.card_congr (Equiv.subtypeEquiv Φ hmem)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
