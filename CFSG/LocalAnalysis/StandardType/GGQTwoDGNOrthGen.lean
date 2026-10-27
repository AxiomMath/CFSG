module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthBlock
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNOrthRefl
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNUnitGen

public section

namespace CFSG.StandardType.OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}

@[expose] noncomputable def OrthFrameCore.rank2Join (Φ : OrthFrameCore p Bs X) :
    Subgroup (Φ.V ≃ₗ[Φ.F] Φ.V) :=
  ⨆ (x : OmPlusIdx Φ.r) (y : OmPlusIdx Φ.r)
    (_ : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x), Φ.rank2 x y

theorem OrthFrameCore.rank2_le_orth (Φ : OrthFrameCore p Bs X) (x y : OmPlusIdx Φ.r) :
    Φ.rank2 x y ≤ TauCeti.QuadraticMap.orthogonalGroup Φ.Q :=
  (((ggOTwoPrime_le _).trans inf_le_left).trans
    (CFSG.RankThree.Classical.orthDerived_le_orthogonalGroup Φ.Q))

theorem OrthFrameCore.rank2_le_orthDerived' (Φ : OrthFrameCore p Bs X)
    (x y : OmPlusIdx Φ.r) : Φ.rank2 x y ≤ orthDerived Φ.Q :=
  (ggOTwoPrime_le _).trans inf_le_left

theorem OrthFrameCore.rank2Join_le_orth (Φ : OrthFrameCore p Bs X) :
    Φ.rank2Join ≤ TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
  unfold OrthFrameCore.rank2Join
  exact iSup₂_le fun x y => iSup_le fun _ => Φ.rank2_le_orth x y

end CFSG.StandardType.OrthTorus

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.RankThree.Classical2 (orthDerived)

local notation "𝔽₄" => GaloisField 2 2

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}

theorem noncomm_omTog {r : ℕ} (hp : p.Prime) (i : Fin r) {x y : OmPlusIdx r}
    (h : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x) :
    omPlusRefl p (omTog i x) * omPlusRefl p (omTog i y) ≠
      omPlusRefl p (omTog i y) * omPlusRefl p (omTog i x) := by
  rw [omPlusRefl_not_comm_iff_supp hp] at h ⊢
  simpa only [omSupp_omTog] using h

section Gen

variable {Φ : OrthFrameCore p Bs X} [Algebra Φ.F 𝔽₄] (N : OrthNormData Φ)

theorem OrthNormData.tauV_conj_mem_rank2Join (i : Fin Φ.r) {h : Φ.V ≃ₗ[Φ.F] Φ.V}
    (hh : h ∈ Φ.rank2Join) : N.tauV i * h * (N.tauV i)⁻¹ ∈ Φ.rank2Join := by
  have hle : Φ.rank2Join.map (MulAut.conj (N.tauV i)).toMonoidHom ≤ Φ.rank2Join := by
    unfold OrthFrameCore.rank2Join
    rw [Subgroup.map_iSup]
    refine iSup_le fun x => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun y => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hxy => ?_
    rw [← qtwoOrth_rank2_conj Φ (N.tauV_mem_orth i) (N.tauV_conj_tau i) (omTog_refl i x)
      (omTog_refl i y)]
    exact le_iSup₂_of_le (omTog i x) (omTog i y)
      (le_iSup_of_le (noncomm_omTog (Fact.out) i hxy) le_rfl)
  have h1 := hle ⟨h, hh, rfl⟩
  simpa [MulAut.conj_apply] using h1

end Gen

end CFSG.StandardType.QTwo

namespace CFSG.StandardType.OrthTorus

open CFSG.StandardType.QTwo CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalGroups.Unitary
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.ClassicalInvolution.Models.OrthogonalPairs Multiplicative
open CFSG.RankThree.Classical2 (orthDerived)

local notation "𝔽₄" => GaloisField 2 2

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}

theorem OrthFrameCore.orthDerived_le_rank2Join (Φ : OrthFrameCore p Bs X)
    (hF : Nat.card Φ.F = 2) : orthDerived Φ.Q ≤ Φ.rank2Join := by
  classical
  obtain ⟨alg, ⟨N⟩⟩ := qTwoD_exists_normData Φ hF
  letI := alg
  have hr4 : 4 ≤ Φ.r := Φ.hr
  have hK4 : Nat.card (GaloisField 2 2) = 4 := by rw [qTwoD_card_gf4]; norm_num
  have hSU : N.rep.range ≤ Φ.rank2Join := by
    rw [range_eq_iSup_coordBlockSU_three hK4 hr4 N.rep]
    refine iSup₂_le fun I hI => ?_
    obtain ⟨x, y, hxy, hle⟩ := N.block_le_rank2 hr4 hI
    exact hle.trans (le_iSup₂_of_le x y (le_iSup_of_le hxy le_rfl))
  set i₀ : Fin Φ.r := ⟨0, by omega⟩ with hi₀
  set H' : Subgroup ((Fin Φ.r → 𝔽₄) ≃ₗ[Φ.F] (Fin Φ.r → 𝔽₄)) :=
    Φ.rank2Join.map N.cχ.toMonoidHom with hH'
  have hH'O : H' ≤ TauCeti.QuadraticMap.orthogonalGroup (Qn N.E Φ.r) := by
    rintro _ ⟨h, hh, rfl⟩
    exact (N.cχ_mem_iff h).mpr (Φ.rank2Join_le_orth hh)
  haveI : FiniteDimensional Φ.F 𝔽₄ := Module.Finite.of_finite
  have hQ := Qn_polarBilin_nondegenerate N.E Φ.r
  have h6 : 6 ≤ Module.finrank Φ.F (Fin Φ.r → 𝔽₄) := by
    rw [Module.finrank_pi_fintype]
    simp only [N.E.finrank_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    omega
  have hv₀ : Qn N.E Φ.r (Pi.single i₀ 1) = 1 := Qn_single_one N.E i₀
  have hrH : ∀ h' ∈ H', CFSG.ClassicalGroups.Orthogonal.reflect (Qn N.E Φ.r) (Pi.single i₀ 1) *
      h' * CFSG.ClassicalGroups.Orthogonal.reflect (Qn N.E Φ.r) (Pi.single i₀ 1) ∈ H' := by
    intro h' hh'
    rw [← tauAt_eq_reflect N.E i₀]
    obtain ⟨h, hh, rfl⟩ := hh'
    show tauAt N.E i₀ * N.cχ h * tauAt N.E i₀ ∈ H'
    have hinv : (tauAt N.E i₀)⁻¹ = tauAt N.E i₀ :=
      inv_eq_of_mul_eq_one_right (tauAt_mul_self N.E i₀)
    have e : tauAt N.E i₀ * N.cχ h * tauAt N.E i₀ =
        N.cχ (N.tauV i₀ * h * (N.tauV i₀)⁻¹) := by
      rw [map_mul, map_mul, map_inv, N.cχ_tauV, hinv]
    rw [e]
    exact ⟨_, N.tauV_conj_mem_rank2Join i₀ hh, rfl⟩
  have htr : ∀ w, Qn N.E Φ.r w = 1 → ∃ h' ∈ H', h' (Pi.single i₀ 1) = w := by
    intro w hw
    obtain ⟨t, ht⟩ := N.exists_su_smul_eq hr4 hv₀ hw
    refine ⟨N.cχ (N.rep t), ⟨N.rep t, hSU ⟨t, rfl⟩, rfl⟩, ?_⟩
    rw [N.cχ_rep, suEndN_apply, ht]
  have key := orthDerived_le_of_reflect hQ h6 hH'O hv₀ hrH htr
  intro z hz
  have hmap : (TauCeti.QuadraticMap.orthogonalGroup Φ.Q).map N.cχ.toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (Qn N.E Φ.r) := by
    rintro _ ⟨g, hg, rfl⟩
    exact (N.cχ_mem_iff g).mpr hg
  have hz' : N.cχ z ∈ orthDerived (Qn N.E Φ.r) := by
    have h1 : (orthDerived Φ.Q).map N.cχ.toMonoidHom ≤ orthDerived (Qn N.E Φ.r) := by
      show Subgroup.map _ ⁅TauCeti.QuadraticMap.orthogonalGroup Φ.Q,
          TauCeti.QuadraticMap.orthogonalGroup Φ.Q⁆ ≤
        ⁅TauCeti.QuadraticMap.orthogonalGroup (Qn N.E Φ.r),
          TauCeti.QuadraticMap.orthogonalGroup (Qn N.E Φ.r)⁆
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmap hmap
    exact h1 ⟨z, hz, rfl⟩
  obtain ⟨h, hh, hhz⟩ := key hz'
  have hhz' : h = z := N.cχ.injective hhz
  exact hhz' ▸ hh

theorem OrthFrameCore.le_iSup_img_rank2 (Φ : OrthFrameCore p Bs X)
    (hF : Nat.card Φ.F = 2) :
    X ≤ ⨆ (x : OmPlusIdx Φ.r) (y : OmPlusIdx Φ.r)
      (_ : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x),
        Φ.img (Φ.rank2 x y) := by
  classical
  set T : Subgroup G := ⨆ (x : OmPlusIdx Φ.r) (y : OmPlusIdx Φ.r)
    (_ : omPlusRefl p x * omPlusRefl p y ≠ omPlusRefl p y * omPlusRefl p x),
      Φ.img (Φ.rank2 x y) with hT
  have h1 : Φ.rank2Join ≤ (T.comap Φ.ψ).map (orthDerived Φ.Q).subtype := by
    unfold OrthFrameCore.rank2Join
    refine iSup₂_le fun x y => iSup_le fun hxy => ?_
    intro g hg
    have hgΩ : g ∈ orthDerived Φ.Q := Φ.rank2_le_orthDerived' x y hg
    refine ⟨⟨g, hgΩ⟩, ?_, rfl⟩
    show Φ.ψ ⟨g, hgΩ⟩ ∈ T
    have hmem : Φ.ψ ⟨g, hgΩ⟩ ∈ Φ.img (Φ.rank2 x y) :=
      ⟨⟨g, hgΩ⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
    have hle : Φ.img (Φ.rank2 x y) ≤ T := le_iSup₂_of_le x y (le_iSup_of_le hxy le_rfl)
    exact hle hmem
  rw [← Φ.hrange]
  rintro _ ⟨z, rfl⟩
  have hz : (z : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.rank2Join := Φ.orthDerived_le_rank2Join hF z.2
  obtain ⟨z', hz', hzz'⟩ := h1 hz
  have hz'z : z' = z := Subtype.ext hzz'
  exact hz'z ▸ hz'

end CFSG.StandardType.OrthTorus

end
