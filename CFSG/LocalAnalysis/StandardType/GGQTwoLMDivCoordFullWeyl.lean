module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordFullPhi
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.UCoord Matrix CFSG.ClassicalInvolution.Phan
  CFSG.RankThree.Classical

variable {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {m : ℕ}
  {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
  {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
  {hN : Bs ≤ Subgroup.normalizer (L : Set G)}

theorem qTwoLMDivF_ggPermSU_coe (σ : Equiv.Perm (Fin m)) :
    ((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) = permGL σ := by
  apply Units.ext
  rw [show (((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) :
      Matrix (Fin m) (Fin m) F0) = (σ⁻¹).permMatrix F0 from rfl]
  simp only [CFSG.RankThree.Classical.permGL, MonoidHom.coe_toHomUnits,
    Matrix.permMatrixHom_apply]

theorem qTwoLMDivF_scalar_ne_zero (hm : 0 < m) {Z : GL (Fin m) F0} {z : F0}
    (hZ : (Z : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => z) : z ≠ 0 := by
  intro h0
  have hdet : IsUnit (Matrix.det (Z : Matrix (Fin m) (Fin m) F0)) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit Z)
  rw [hZ, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h0,
    zero_pow hm.ne'] at hdet
  exact not_isUnit_zero hdet

theorem qTwoLMDivF_scalar_inv {Z : GL (Fin m) F0} {z : F0} (hz : z ≠ 0)
    (hZ : (Z : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => z) :
    ((Z⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => z⁻¹ := by
  have h1 : (Z : Matrix (Fin m) (Fin m) F0) * Matrix.diagonal (fun _ : Fin m => z⁻¹) = 1 := by
    rw [hZ, Matrix.diagonal_mul_diagonal]
    simp [hz]
  calc ((Z⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)
      = ((Z⁻¹ : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          ((Z : Matrix (Fin m) (Fin m) F0) * Matrix.diagonal (fun _ : Fin m => z⁻¹)) := by
        rw [h1, mul_one]
    _ = Matrix.diagonal fun _ => z⁻¹ := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

theorem qTwoLMDivF_conjAut_eq (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    (hsurj : Function.Surjective (qTwoLMDivF_phi hm hU hF0 hδ))
    {n : ↥L} {u : Su F0 2 1 m} (hnu : c n = π u) (σ : Equiv.Perm (Fin m))
    (hu : ∀ f, (u : GL (Fin m) F0) * δ f * (u : GL (Fin m) F0)⁻¹ =
      δ (SpCoord.permAut σ f))
    (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))) :
    ggConjAut (ggGamma L hN).range hn =
      MulAut.congr (qTwoLMDivF_theta hm hperf hU hF0 hδ hsurj) (qTwoLMDivF_permQ m σ) := by
  apply MulEquiv.ext
  intro w
  obtain ⟨q, rfl⟩ := (qTwoLMDivF_theta hm hperf hU hF0 hδ hsurj).surjective w
  obtain ⟨b, rfl⟩ := hsurj q
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    qTwoLMDivF_theta_phi hm hperf hU hF0 hδ hsurj b]
  obtain ⟨b', hb'⟩ := qTwoLMDivF_wnorm_fwd hm hperf hU hF0 hδ hsurj hnu σ hu b
  have hφ := qTwoLMDivF_phi_conj hm hU hF0 hδ hnu σ hu hb'
  have hperm : qTwoLMDivF_permQ m σ (qTwoLMDivF_phi hm hU hF0 hδ b) =
      qTwoLMDivF_phi hm hU hF0 hδ b' := by
    rw [qTwoLMDivF_phi_apply hm hU hF0 hδ b, qTwoLMDivF_permQ_mk, hφ]
  rw [hperm, qTwoLMDivF_theta_phi hm hperf hU hF0 hδ hsurj b']
  apply Subtype.ext
  rw [ggConjAut_apply]
  exact hb'.symm

theorem qTwoLMDivF_weyl_ind (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    (hsurj : Function.Surjective (qTwoLMDivF_phi hm hU hF0 hδ)) (σ : Equiv.Perm (Fin m)) :
    ∃ (n : ↥L) (hn : MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
      ggConjAut (ggGamma L hN).range hn =
        MulAut.congr (qTwoLMDivF_theta hm hperf hU hF0 hδ hsurj) (qTwoLMDivF_permQ m σ) := by
  obtain ⟨n, hnu⟩ := hU.c_surj (π (ggPermSU (K := F0) (f := 1) σ⁻¹))
  have hu : ∀ f, ((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0) * δ f *
      ((ggPermSU (K := F0) (f := 1) σ⁻¹ : Su F0 2 1 m) : GL (Fin m) F0)⁻¹ =
        δ (SpCoord.permAut σ f) := by
    intro f
    rw [qTwoLMDivF_ggPermSU_coe]
    exact hδ.perm σ f
  have hn := qTwoLMDivF_wnorm_full hm hperf hU hF0 hδ hsurj hnu σ hu
  exact ⟨n, hn, qTwoLMDivF_conjAut_eq hm hperf hU hF0 hδ hsurj hnu σ hu hn⟩

theorem qTwoLMDivF_weyl_norm (hm : 4 ≤ m) (hperf : commutator ↥L = ⊤)
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) (hF0 : Nat.card F0 = 4)
    {δ : (Fin m → Multiplicative (ZMod 3)) →* GL (Fin m) F0} (hδ : QTwoDivFullTorus hF0 δ)
    (hsurj : Function.Surjective (qTwoLMDivF_phi hm hU hF0 hδ)) (n : ↥L)
    (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))) :
    ∃ σ : Equiv.Perm (Fin m),
      ggConjAut (ggGamma L hN).range hn =
        MulAut.congr (qTwoLMDivF_theta hm hperf hU hF0 hδ hsurj) (qTwoLMDivF_permQ m σ) := by
  obtain ⟨u, hu0⟩ := hU.π_surj (c n)
  have hnu : c n = π u := hu0.symm
  have hb : ∀ b : ↥Bs, ∃ b' : ↥Bs,
      ggGamma L hN b' = MulAut.conj n * ggGamma L hN b * (MulAut.conj n)⁻¹ := fun b =>
    (Subgroup.mem_normalizer_iff.mp hn (ggGamma L hN b)).mp ⟨b, rfl⟩
  have hm0 : 0 < m := by omega
  have hmono : ∀ f, ∃ f', ∃ z : F0, z ≠ 0 ∧
      ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          ((δ f : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) =
        z • ((δ f' : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) *
          ((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0) := by
    intro f
    obtain ⟨b, hbf⟩ := hsurj (QuotientGroup.mk f)
    obtain ⟨b', hb'⟩ := hb b
    obtain ⟨z, hz⟩ := qTwoLMDivF_scalar_of_gamma_eq hm hU hnu hb'
    have hbf' : (QuotientGroup.mk (qTwoLMDivF_coord hU hF0 hδ b) : QTwoQm m) =
        QuotientGroup.mk f := by
      rw [← qTwoLMDivF_phi_apply hm hU hF0 hδ]
      exact hbf
    have hk : f / qTwoLMDivF_coord hU hF0 hδ b ∈ Subgroup.zpowers (qTwoLMDivF_oneVec m) :=
      (QuotientGroup.eq_iff_div_mem).mp hbf'.symm
    obtain ⟨y, hy⟩ := (hδ.scalar _).mpr hk
    obtain ⟨Y, hYdef⟩ : ∃ Y : GL (Fin m) F0, Y = δ (f / qTwoLMDivF_coord hU hF0 hδ b) :=
      ⟨_, rfl⟩
    have hy' : (Y : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => y := by
      rw [hYdef]
      exact hy
    obtain ⟨g, hg⟩ : ∃ g : GL (Fin m) F0,
        g = (u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹ := ⟨_, rfl⟩
    obtain ⟨Z, hZdef⟩ : ∃ Z : GL (Fin m) F0, Z = qTwoLMDivF_rep hU b' * g⁻¹ := ⟨_, rfl⟩
    have hz' : (Z : Matrix (Fin m) (Fin m) F0) = Matrix.diagonal fun _ => z := by
      rw [hZdef, hg]
      exact hz
    have hz0 : z ≠ 0 := qTwoLMDivF_scalar_ne_zero hm0 hz'
    have hy0 : y ≠ 0 := qTwoLMDivF_scalar_ne_zero hm0 hy'
    have hZinv := qTwoLMDivF_scalar_inv hz0 hz'
    have hδf : δ f = Y * qTwoLMDivF_rep hU b := by
      rw [hYdef, map_div, qTwoLMDivF_coord_spec]
      exact (div_mul_cancel _ _).symm
    have hYu : Y * (u : GL (Fin m) F0) = (u : GL (Fin m) F0) * Y := by
      have := qTwoLMDivF_scalar_conj hy' (u : GL (Fin m) F0)
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this
    have hgZ : g = Z⁻¹ * qTwoLMDivF_rep hU b' := by
      rw [hZdef]
      group
    have hmain : (u : GL (Fin m) F0) * δ f =
        (Y * Z⁻¹) * qTwoLMDivF_rep hU b' * (u : GL (Fin m) F0) := by
      calc (u : GL (Fin m) F0) * δ f
          = (u : GL (Fin m) F0) * (Y * qTwoLMDivF_rep hU b) := by rw [hδf]
        _ = (Y * (u : GL (Fin m) F0)) * qTwoLMDivF_rep hU b := by rw [hYu]; group
        _ = Y * ((u : GL (Fin m) F0) * qTwoLMDivF_rep hU b * (u : GL (Fin m) F0)⁻¹) *
              (u : GL (Fin m) F0) := by group
        _ = Y * g * (u : GL (Fin m) F0) := by rw [hg]
        _ = (Y * Z⁻¹) * qTwoLMDivF_rep hU b' * (u : GL (Fin m) F0) := by rw [hgZ]; group
    refine ⟨qTwoLMDivF_coord hU hF0 hδ b', y * z⁻¹, mul_ne_zero hy0 (inv_ne_zero hz0), ?_⟩
    have hm1 := congrArg (fun x : GL (Fin m) F0 => (x : Matrix (Fin m) (Fin m) F0)) hmain
    simp only [Units.val_mul, hZinv, hy'] at hm1
    rw [hm1, qTwoLMDivF_coord_spec hU hF0 hδ b', Matrix.smul_eq_diagonal_mul,
      Matrix.diagonal_mul_diagonal]
  obtain ⟨σ, hσ⟩ := hδ.mono (u : GL (Fin m) F0) hmono
  have hu' : ∀ f, (u : GL (Fin m) F0) * δ f * (u : GL (Fin m) F0)⁻¹ =
      δ (SpCoord.permAut σ f) := fun f => by
    rw [hσ f, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨σ, qTwoLMDivF_conjAut_eq hm hperf hU hF0 hδ hsurj hnu σ hu' hn⟩

end CFSG.StandardType.QTwo

end
