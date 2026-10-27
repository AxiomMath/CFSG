module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SectionRank.OddCover (diagHom)

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

private theorem ggQTUbx_B0_mem_suPairs {N : ℕ} {K : Type} [Field K] [Finite K]
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K)
    (hxBs : x ∈ Bs) (z0 : ↥(unitarySU 2 1 K N))
    (hz0_eq : F.φ z0 = x) :
    ((1 : G), (z0 : GL (Fin N) K)⁻¹ * diagHom N (F.δ x)) ∈ SUTorus.suPairs F.φ := by
  let B0 : GL (Fin N) K := (z0 : GL (Fin N) K)⁻¹ * diagHom N (F.δ x)
  have hB0_norm : B0 ∈ Subgroup.normalizer ((unitarySU 2 1 K N : Set (GL (Fin N) K))) := by
    have hz0_norm : (z0 : GL (Fin N) K)⁻¹ ∈
        Subgroup.normalizer ((unitarySU 2 1 K N : Set (GL (Fin N) K))) :=
      Subgroup.le_normalizer (Subgroup.inv_mem _ z0.2)
    have hdiag_norm : diagHom N (F.δ x) ∈
        Subgroup.normalizer ((unitarySU 2 1 K N : Set (GL (Fin N) K))) :=
      (F.pair x hxBs).1
    exact Subgroup.mul_mem _ hz0_norm hdiag_norm
  refine ⟨hB0_norm, ?_⟩
  intro u v hv
  let w : ↥(unitarySU 2 1 K N) :=
    ⟨(z0 : GL (Fin N) K) * (v : GL (Fin N) K) * (z0 : GL (Fin N) K)⁻¹, by
      have hv_SU : (v : GL (Fin N) K) ∈ unitarySU 2 1 K N := v.2
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ z0.2 hv_SU) (Subgroup.inv_mem _ z0.2)⟩
  have hw_eq : (w : GL (Fin N) K) =
      diagHom N (F.δ x) * u * (diagHom N (F.δ x))⁻¹ := by
    change (z0 : GL (Fin N) K) * (v : GL (Fin N) K) * (z0 : GL (Fin N) K)⁻¹ =
      diagHom N (F.δ x) * u * (diagHom N (F.δ x))⁻¹
    rw [hv]
    group
  have hpair := (F.pair x hxBs).2 u w hw_eq
  have hw_eq_phi : F.φ w = x * F.φ v * x⁻¹ := by
    calc F.φ w = F.φ (z0 * v * z0⁻¹) := rfl
      _ = F.φ (z0 * v) * F.φ (z0⁻¹) := by rw [map_mul]
      _ = F.φ z0 * F.φ v * F.φ (z0⁻¹) := by rw [map_mul]
      _ = F.φ z0 * F.φ v * (F.φ z0)⁻¹ := by rw [map_inv]
      _ = x * F.φ v * x⁻¹ := by simp only [hz0_eq]
  rw [hw_eq_phi] at hpair
  have hcancel : F.φ u = F.φ v := by
    calc F.φ u = x⁻¹ * (x * F.φ u * x⁻¹) * x := by group
      _ = x⁻¹ * (x * F.φ v * x⁻¹) * x := by rw [hpair]
      _ = F.φ v := by group
  simpa using hcancel

private theorem ggQTUbx_B0_scalar {N : ℕ} {K : Type} [Field K] [Finite K]
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K)
    (hxBs : x ∈ Bs) (hN : 7 ≤ N)
    (z0 : ↥(unitarySU 2 1 K N))
    (hz0_eq : F.φ z0 = x) :
    ∃ c : Kˣ, (z0 : GL (Fin N) K)⁻¹ * diagHom N (F.δ x) =
      Matrix.GeneralLinearGroup.scalar (Fin N) c := by
  have hmem := ggQTUbx_B0_mem_suPairs F hxBs z0 hz0_eq
  exact SUTorus.exists_scalar_of_mem_suPairs_one F.field (by omega)
    (by
      intro h
      have hN3 : N = 3 := congrArg Prod.fst h
      omega) Nat.prime_three (by norm_num) F.ker_le hmem

private theorem ggQTUbx_z0_diag {N : ℕ} {K : Type} [Field K] [Finite K]
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K)
    (I : Finset (Fin N)) (z0 : ↥(unitarySU 2 1 K N))
    (hz0_in : z0 ∈ TableBUE.blockSU I)
    (c : Kˣ)
    (hc : (z0 : GL (Fin N) K)⁻¹ * diagHom N (F.δ x) =
      Matrix.GeneralLinearGroup.scalar (Fin N) c)
    (hI4 : 4 ≤ I.card)
    (hIconst : ∀ i ∈ I, ∀ j ∈ I, F.δ x i = F.δ x j) :
    ∃ lam : Kˣ, (z0 : GL (Fin N) K) = diagHom N (fun i => if i ∈ I then lam else 1) := by
  classical
  have hI_nonempty : I.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i0, hi0⟩ := hI_nonempty
  let lam : Kˣ := F.δ x i0 * c⁻¹
  refine ⟨lam, ?_⟩
  have hz0_eq_diag : (z0 : GL (Fin N) K) =
      diagHom N (F.δ x) * Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ := by
    have h2 : (z0 : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) c =
        diagHom N (F.δ x) := by
      calc (z0 : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) c
          = (z0 : GL (Fin N) K) * ((z0 : GL (Fin N) K)⁻¹ * diagHom N (F.δ x)) := by rw [← hc]
        _ = diagHom N (F.δ x) := by group
    calc (z0 : GL (Fin N) K)
        = (z0 : GL (Fin N) K) * Matrix.GeneralLinearGroup.scalar (Fin N) c *
          Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ := by
            rw [map_inv (Matrix.GeneralLinearGroup.scalar (Fin N)) c]
            group
      _ = diagHom N (F.δ x) * Matrix.GeneralLinearGroup.scalar (Fin N) c⁻¹ := by rw [h2]
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ I
    · rw [hz0_eq_diag]
      rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar]
        rw [Matrix.diagonal_apply, Matrix.scalar_apply]
        simp only [if_true]
        rw [hIconst i hi i0 hi0]
        rw [CFSG.SectionRank.OddCover.coe_diagHom]
        rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
        simp only [if_true]
        rw [if_pos hi]
        rfl
      · intro j _ hij
        rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar]
        rw [Matrix.diagonal_apply, Matrix.scalar_apply]
        rw [if_neg (Ne.symm hij)]
        rw [zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    · rw [CFSG.SectionRank.OddCover.coe_diagHom]
      rw [Matrix.diagonal_apply]
      simp only [if_true, hi, if_false]
      simpa using (TableBUE.mem_blockSU).mp hz0_in i i (Or.inl hi)
  · rw [hz0_eq_diag]
    rw [Units.val_mul, Matrix.mul_apply]
    rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar]
    rw [CFSG.SectionRank.OddCover.coe_diagHom]
    simp only [Matrix.diagonal_apply, Matrix.scalar_apply]
    rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro j_1 _
      by_cases hij1 : i = j_1
      · subst hij1
        simp [hij]
      · simp [hij1]

private theorem ggQTUbx_lam_ne_one {N : ℕ} {K : Type} [Field K] [Finite K]
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K)
    (I : Finset (Fin N)) (lam : Kˣ) (z0 : ↥(unitarySU 2 1 K N))
    (hz0_eq : F.φ z0 = x)
    (hz0_diag : (z0 : GL (Fin N) K) = diagHom N (fun i => if i ∈ I then lam else 1))
    (hx_ne_one : x ≠ 1) :
    lam ≠ 1 := by
  intro hlam
  have hz0_one : (z0 : GL (Fin N) K) = 1 := by
    rw [hz0_diag]
    have hfun : (fun i => if i ∈ I then lam else 1) = (fun _ => 1) := by
      funext i
      by_cases hi : i ∈ I <;> simp [hi, hlam]
    rw [hfun]
    change diagHom N (1 : Fin N → Kˣ) = 1
    rw [map_one]
  have hz0_sub_one : z0 = 1 := by
    apply Subtype.ext
    exact hz0_one
  have hx_one : x = 1 := by
    calc x = F.φ z0 := hz0_eq.symm
      _ = F.φ 1 := by rw [hz0_sub_one]
      _ = 1 := map_one F.φ
  exact hx_ne_one hx_one

private theorem ggQTUbx_I_compl_nonempty {N : ℕ} {K : Type} [Field K] [Finite K]
    (hcfg : GGConfig 3 B Bs x L D J)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K)
    (I : Finset (Fin N)) (lam : Kˣ) (z0 : ↥(unitarySU 2 1 K N))
    (hz0_eq : F.φ z0 = x)
    (hz0_diag : (z0 : GL (Fin N) K) = diagHom N (fun i => if i ∈ I then lam else 1))
    (hx_ne_one : x ≠ 1) :
    Iᶜ.Nonempty := by
  by_contra h
  have hI_univ : I = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro i
    by_contra hi
    have : i ∈ (Iᶜ : Finset (Fin N)) := Finset.mem_compl.mpr hi
    exact h ⟨i, this⟩
  have hz0_scalar : (z0 : GL (Fin N) K) = Matrix.GeneralLinearGroup.scalar (Fin N) lam := by
    rw [hz0_diag, hI_univ]
    have hfun : (fun i : Fin N => if i ∈ Finset.univ then lam else 1) = (fun _ => lam) := by
      funext i
      simp
    rw [hfun]
    apply Units.ext
    rw [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.GeneralLinearGroup.coe_scalar]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.scalar_apply]
    · simp [Matrix.scalar_apply, hij]
  have hz0_central : z0 ∈ Subgroup.center ↥(unitarySU 2 1 K N) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz0_scalar]
    exact (Matrix.GeneralLinearGroup.scalar_commute lam (g : GL (Fin N) K)).symm
  have hx_central : x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← F.range_eq] at hy
    obtain ⟨u, rfl⟩ := hy
    calc F.φ u * x = F.φ u * F.φ z0 := by rw [hz0_eq]
      _ = F.φ (u * z0) := by rw [map_mul]
      _ = F.φ (z0 * u) := by rw [← Subgroup.mem_center_iff.mp hz0_central u]
      _ = F.φ z0 * F.φ u := by rw [map_mul]
      _ = x * F.φ u := by rw [hz0_eq]
  have hx_bot : x ∈ (Bs ⊓ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) := by
    exact Subgroup.mem_inf.mpr ⟨hcfg.tableB_facts.2.2.1, hx_central⟩
  rw [bstar_inf_centralizer_ggG0_eq_bot hcfg] at hx_bot
  exact hx_ne_one (Subgroup.mem_bot.mp hx_bot)

theorem ggQTwoXInLU_blockX {N : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∈ L) (hN : 7 ≤ N)
    (F : GGQTwoXInLUFrame Bs (ggG0 3 B x L D J) N K) :
    ∃ (I : Finset (Fin N)) (lam : Kˣ) (z : ↥(unitarySU 2 1 K N)), lam ≠ 1 ∧ Iᶜ.Nonempty ∧
      L = (TableBUE.blockSU (K := K) (n := 1) I).map F.φ ∧
      (z : GL (Fin N) K) = diagHom N (fun i => if i ∈ I then lam else 1) ∧ F.φ z = x := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hx_ne_one : x ≠ 1 := hcfg.1.2.2.2.2.2.2.1.2.2.1
  have hLcomp : IsComponentOf L (ggG0 3 B x L D J ⊓ Subgroup.centralizer ({x} : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le
      hcfg.1.2.2.2.2.2.2.1.2.2.2.1
      (le_inf (le_sup_left : L ≤ ggG0 3 B x L D J) hcfg.1.2.2.2.2.2.2.1.2.2.2.1.1) inf_le_right
  obtain ⟨I, hI4, hIconst, hLI⟩ := SUTorus.exists_blockSU_of_isComponentOf_two
    F.field F.ker_le (F.pair x hxBs) (by rwa [← F.range_eq] at hLcomp)
  have hxL' : x ∈ (TableBUE.blockSU (K := K) (n := 1) I).map F.φ := by rwa [hLI] at hxL
  obtain ⟨z0, hz0_in, hz0_eq⟩ := (Subgroup.mem_map).mp hxL'
  obtain ⟨c, hc⟩ := ggQTUbx_B0_scalar F hxBs hN z0 hz0_eq
  obtain ⟨lam, hlam_diag⟩ := ggQTUbx_z0_diag F I z0 hz0_in c hc hI4 hIconst
  have hlam_ne_one : lam ≠ 1 := ggQTUbx_lam_ne_one F I lam z0 hz0_eq hlam_diag hx_ne_one
  have hI_compl_nonempty : Iᶜ.Nonempty :=
    ggQTUbx_I_compl_nonempty hcfg F I lam z0 hz0_eq hlam_diag hx_ne_one
  exact ⟨I, lam, z0, hlam_ne_one, hI_compl_nonempty, hLI, hlam_diag, hz0_eq⟩

end CFSG.StandardType

end
