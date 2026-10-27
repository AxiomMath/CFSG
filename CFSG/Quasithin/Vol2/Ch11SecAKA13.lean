module

public import CFSG.Quasithin.Vol2.Ch11SecAKA12
public import CFSG.Quasithin.H13.NQCatParabolicSp4
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAKA2

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.Quasithin.H13.NQCat (up2)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkQ spLevi spMat spLevi_mem spLevi_mem_perfectCore
  spMat_inl_zero_eq_one_of_perfectCore sl2_isSimple)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (gammaW_pre_eq det_blkQ_zero entry_mul_Q0
  mem_unipotent_of_mem_Q0 blkQ_spLevi_inv)

namespace KA

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem iSup_conj_eq_top (hK : ∃ k : ℕ, Nat.card K = 2 ^ k)
    (hK4 : ∃ s : Finset K, s.card = 4) :
    (⨆ γ ∈ perfectCore (Q2 K 0), (perfectCore (Q2 K 1)).map (MulAut.conj γ).toMonoidHom) =
      ⊤ := by
  set M₀ := ⨆ γ ∈ perfectCore (Q2 K 0), (perfectCore (Q2 K 1)).map (MulAut.conj γ).toMonoidHom
    with hM₀
  have hQ1 : perfectCore (Q2 K 1) ≤ M₀ := by
    refine le_trans ?_ (le_iSup₂_of_le (1 : StatedSp 2 K) (one_mem _) le_rfl)
    intro x hx
    exact ⟨x, hx, by simp⟩
  have hU : unipotent 2 K ≤ M₀ :=
    (CFSG.Quasithin.H13.NQCat.Sp4.unipotent_le_perfectCore hK4 1).trans hQ1
  have hnorm : ∀ γ ∈ perfectCore (Q2 K 0), ∀ m ∈ M₀, γ * m * γ⁻¹ ∈ M₀ := by
    intro γ hγ m hm
    have hle : M₀.map (MulAut.conj γ).toMonoidHom ≤ M₀ := by
      rw [hM₀, Subgroup.map_iSup]
      refine iSup_le fun δ => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hδ => ?_
      rw [Subgroup.map_map]
      refine le_trans (le_of_eq ?_) (le_iSup₂_of_le (γ * δ) (mul_mem hγ hδ) le_rfl)
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    exact hle ⟨m, hm, rfl⟩
  have hL : ∀ A, spLevi 0 A ∈ M₀ := by
    have := sl2_isSimple hK4
    have hN₀ : (M₀.comap (spLevi (K := K) 0)).Normal := ⟨fun n hn A => by
      show spLevi 0 (A * n * A⁻¹) ∈ M₀
      rw [map_mul, map_mul, map_inv]
      exact hnorm _ (spLevi_mem_perfectCore hK4 0 A) _ hn⟩
    rcases hN₀.eq_bot_or_eq_top with h | h
    · exfalso
      have h1 : up2 (1 : K) ∈ M₀.comap (spLevi (K := K) 0) := by
        show spLevi 0 (up2 1) ∈ M₀
        rw [CFSG.Quasithin.H13.NQCat.Sp4.spLevi_zero_up2]
        exact hU (CFSG.Quasithin.H13.NQCat.Sp4.xB_mem 1)
      rw [h, Subgroup.mem_bot] at h1
      have h2 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K =>
        (A : Matrix (Fin 2) (Fin 2) K) 0 1) h1
      simp [up2] at h2
    · intro A
      show A ∈ M₀.comap (spLevi (K := K) 0)
      rw [h]
      exact Subgroup.mem_top A
  have hQ0 : perfectCore (Q2 K 0) ≤ M₀ := by
    intro M hM
    have hMQ := perfectCore_le _ hM
    let A : Matrix.SpecialLinearGroup (Fin 2) K := ⟨blkQ 0 ⟨M, hMQ⟩, det_blkQ_zero hMQ⟩
    have hli : (spLevi 0 A)⁻¹ ∈ Q2 K 0 := inv_mem (spLevi_mem 0 A)
    have hM'Q : M * (spLevi 0 A)⁻¹ ∈ Q2 K 0 := mul_mem hMQ hli
    have hχ' : spMat (M * (spLevi 0 A)⁻¹) (Sum.inl 0) (Sum.inl 0) = 1 := by
      rw [entry_mul_Q0 hli, spMat_inl_zero_eq_one_of_perfectCore hM,
        spMat_inl_zero_eq_one_of_perfectCore (inv_mem (spLevi_mem_perfectCore hK4 0 A)),
        one_mul]
    have hB' : blkQ 0 ⟨M * (spLevi 0 A)⁻¹, hM'Q⟩ = 1 := by
      have e : (⟨M * (spLevi 0 A)⁻¹, hM'Q⟩ : ↥(Q2 K 0)) = ⟨M, hMQ⟩ * ⟨(spLevi 0 A)⁻¹, hli⟩ :=
        rfl
      rw [e, map_mul, blkQ_spLevi_inv]
      show ((A * A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1
      rw [mul_inv_cancel]
      rfl
    have h := mul_mem (hU (mem_unipotent_of_mem_Q0 hM'Q hχ' hB')) (hL A)
    rwa [inv_mul_cancel_right] at h
  rw [eq_top_iff, ← CFSG.Quasithin.H13.NQCat.Sp4.perfectCore_sup_eq_top hK hK4]
  exact sup_le hQ0 hQ1

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

omit [Finite K] [CharP K 2] in
theorem map_pre_eq (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g γ : StatedSp 2 K)
    (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) :
    (hf.pre (gmapSp g S).toAddSubgroup).map (psiSp π g γ).toMonoidHom =
      hf.pre (gmapSp (g * γ) S).toAddSubgroup := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : mat 2 K g⁻¹ *ᵥ f u ∈ S := mem_gmapSp.mp hu
    show f (psiSp π g γ u) ∈ gmapSp (g * γ) S
    rw [psiSp_apply, hf.act4, mem_gmapSp, Matrix.mulVec_mulVec, ← map_mul,
      show (g * γ)⁻¹ * (g * γ * g⁻¹) = g⁻¹ by group]
    exact hu'
  · intro hw
    have hw' : mat 2 K (g * γ)⁻¹ *ᵥ f w ∈ S := mem_gmapSp.mp hw
    refine ⟨(psiSp π g γ)⁻¹ w, ?_, MulAut.apply_inv_self W _ w⟩
    show f ((psiSp π g γ)⁻¹ w) ∈ gmapSp g S
    rw [← map_inv, psiSp_apply, hf.act4, mem_gmapSp, Matrix.mulVec_mulVec, ← map_mul,
      show g⁻¹ * (g * γ⁻¹ * g⁻¹) = (g * γ)⁻¹ by group]
    exact hw'

variable [Finite W]

theorem delta_gen (hK : ∃ k : ℕ, Nat.card K = 2 ^ k) (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) :
    (⨆ x ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)),
      perfectCore (H ⊓ Ch11.SecA.stabW
        ((hf.pre (gmapSp g (spPlane K)).toAddSubgroup).map x.toMonoidHom))) = H := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have hΓ : ∀ γ : StatedSp 2 K, perfectCore (H ⊓ Ch11.SecA.stabW
      ((hf.pre (gmapSp g (spPlane K)).toAddSubgroup).map (psiSp π g γ).toMonoidHom)) =
      ((perfectCore (Q2 K 1)).map (MulAut.conj γ).toMonoidHom).map (psiSp π g) := by
    intro γ
    rw [map_pre_eq hf g γ, show perfectCore (H ⊓ Ch11.SecA.stabW
      (hf.pre (gmapSp (g * γ) (spPlane K)).toAddSubgroup)) = Ch11.SecS.gammaW H
        (hf.pre (gmapSp (g * γ) (spPlane K)).toAddSubgroup) from rfl,
      gammaW_pre_eq hf (g * γ) 1 _ flag_two_eq, Subgroup.map_map]
    congr 1
    ext δ
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, psiSp_apply]
    rw [show g * γ * δ * (g * γ)⁻¹ = g * (γ * δ * γ⁻¹) * g⁻¹ by group]
  have hH : H = (⊤ : Subgroup (StatedSp 2 K)).map (psiSp π g) := by
    ext x
    constructor
    · intro hx
      obtain ⟨δ, hδ⟩ : ∃ δ : ↥(StatedSp 2 K), π δ = ⟨x, hx⟩ := hf.onto ⟨x, hx⟩
      refine ⟨g⁻¹ * δ * g, Subgroup.mem_top _, ?_⟩
      rw [psiSp_apply, show g * (g⁻¹ * δ * g) * g⁻¹ = δ by group, hδ]
    · rintro ⟨γ, -, rfl⟩
      exact (π _).2
  apply le_antisymm
  · exact iSup₂_le fun x _ => (perfectCore_le _).trans inf_le_left
  · conv_lhs => rw [hH, ← iSup_conj_eq_top hK hK4, Subgroup.map_iSup]
    refine iSup_le fun γ => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hγ => ?_
    have hx : psiSp π g γ ∈
        perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) := by
      rw [show perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) =
        Ch11.SecS.gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup) from rfl,
        gammaW_pre_eq hf g 0 _ flag_one_eq]
      exact ⟨γ, hγ, rfl⟩
    rw [← hΓ γ]
    exact le_iSup₂_of_le (psiSp π g γ) hx le_rfl

end KA

theorem factDeltaSp4_holds : Ch11.SecA.FactDeltaSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ P hP U₁ U₂ U₃ hU₁ hU₂ hU₃
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hfix := factRadicalFixedSp4_holds K n hn hK W hW H Z π hπ P hP U₁ hU₁
  have hPΓ := factSylowLeviSp4_holds K n hn hK W hW H Z π hπ P hP U₁ hU₁
  obtain ⟨f, hf, g, hg, rfl, rfl, rfl⟩ := KA.exists_flag_coords hn hK hW hπ hP hU₁ hU₂ hU₃
  refine ⟨KA.delta_fix hf hZ g hfix _, ?_, KA.delta_gen ⟨n, hK⟩ hK4 hf g⟩
  rw [← hK]
  exact KA.delta_line hf hg hP.2.1 hPΓ

end CFSG.Quasithin.Vol2.KGNat
