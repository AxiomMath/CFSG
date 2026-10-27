module

public import CFSG.RankThree.SubgroupLists.IrreducibleGL3
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3F3L3Tools
import CFSG.Quasithin.EmptyFaithful.A38c15IrrBasic
import CFSG.Quasithin.EmptyFaithful.A38c15IrrCyc
import CFSG.Quasithin.EmptyFaithful.A38c15IrrMono
import CFSG.Quasithin.Vol2.Ch11SecU1L3IX
import CFSG.Open.PGLModelStated
import CFSG.Quasithin.Vol2.Ch11SecU1L3IV
import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG.PGLModel (projSL)

open Matrix Subgroup CFSG.RepresentationTheory CFSG.RankThree.SubgroupLists
open CFSG.Quasithin.A38c15 (glImage det_of_mem_glImage eq_top_of_stated_le_glImage
  isSolvable_of_cyclic_normal isSolvable_of_isTransitiveMonomial normalizes_gl32
  scalar_of_commute_of_nonabelian alt5_nonabelian card_alt_five_fin omega_commutant_scalar
  commute_inv_mul_forms)
open CFSG.QuasithinUnique.Ch1 (soForm)
open scoped MatrixGroups

private theorem not_dvd_sixty {p : ℕ} (hp3 : 3 < p) (hp10 : p % 10 = 1 ∨ p % 10 = 9) :
    ¬ p ∣ 60 := by
  intro h
  have : p ≤ 60 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> omega

private theorem not_dvd_168 {p : ℕ} (hpp : p.Prime) (hp3 : 3 < p) (hp : p % 3 = 2)
    (hp7 : p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 4) : ¬ p ∣ 168 := by
  intro h
  have : p ≤ 168 := Nat.le_of_dvd (by norm_num) h
  interval_cases p <;> first | omega | exact absurd hpp (by norm_num)

private theorem p_dvd_card_omegaGL {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0) :
    p ∣ Nat.card (omegaGL M) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.KF1322.nonempty_omegaGL_equiv_psl2 hp5 hMt hdet
  obtain ⟨u, -, hu, hu1, -⟩ := exists_psl2_generators (F := ZMod p) (Nat.card_zmod p)
  have h := orderOf_dvd_natCard u
  rwa [orderOf_eq_prime hu hu1, ← Nat.card_congr e.toEquiv] at h

private theorem isometry_of_normalizes_omegaGL {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hp : p % 3 = 2) {M₀ : Matrix (Fin 3) (Fin 3) (ZMod p)} (hM₀t : M₀ᵀ = M₀)
    (hM₀d : M₀.det ≠ 0) (hirr : IsIrreducibleMatrixRep (omegaGL M₀).subtype)
    {g : GL (Fin 3) (ZMod p)} (hg : ∀ x ∈ omegaGL M₀, g * x * g⁻¹ ∈ omegaGL M₀)
    (hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ * (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = M₀ := by
  have hΩ₀ : ∀ h ∈ omegaGL M₀, (h : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ *
      (h : Matrix (Fin 3) (Fin 3) (ZMod p)) = M₀ := fun h hh =>
    (mem_soGL.mp (CFSG.RankThree.PartOne.LIT.omegaGL_le_soGL M₀ hh)).1
  have hu : IsUnit M₀.det := isUnit_iff_ne_zero.mpr hM₀d
  set M' := (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ *
    (g : Matrix (Fin 3) (Fin 3) (ZMod p)) with hM'
  have hinv : ∀ h ∈ omegaGL M₀, (h : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M' *
      (h : Matrix (Fin 3) (Fin 3) (ZMod p)) = M' := by
    intro h hh
    have hh' := hΩ₀ _ (hg h hh)
    have e1 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) * (h : Matrix (Fin 3) (Fin 3) (ZMod p)) =
        ((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (g : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      rw [← Units.val_mul, ← Units.val_mul]
      exact congrArg Units.val (by group)
    calc (h : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M' * (h : Matrix (Fin 3) (Fin 3) (ZMod p))
        = ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) * (h : Matrix (Fin 3) (Fin 3) (ZMod p)))ᵀ *
            M₀ * ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
              (h : Matrix (Fin 3) (Fin 3) (ZMod p))) := by
          simp only [hM', Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod p)))ᵀ * M₀ *
            (((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
              (g : Matrix (Fin 3) (Fin 3) (ZMod p))) := by rw [e1]
      _ = (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ *
            (((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ *
              ((g * h * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) *
            (g : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = M' := by rw [hh']
  obtain ⟨l, hl⟩ := omega_commutant_scalar hp2 hM₀t hM₀d hirr
    (S := M₀⁻¹ * M') (fun h hh => commute_inv_mul_forms hM₀d (hΩ₀ h hh) (hinv h hh))
  have hM'eq : M' = l • M₀ := by
    calc M' = (M₀ * M₀⁻¹) * M' := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
      _ = M₀ * (M₀⁻¹ * M') := by rw [Matrix.mul_assoc]
      _ = M₀ * Matrix.scalar (Fin 3) l := by rw [hl]
      _ = l • M₀ := by
          ext i j
          simp [Matrix.scalar_apply, Matrix.mul_diagonal, mul_comm]
  have hl3 : l ^ 3 = 1 := by
    have h1 := congrArg Matrix.det hM'eq
    rw [hM', Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet, one_mul, mul_one,
      Matrix.det_smul, Fintype.card_fin] at h1
    have h2 : (l ^ 3 - 1) * M₀.det = 0 := by linear_combination -h1
    have := (mul_eq_zero.mp h2).resolve_right hM₀d
    linear_combination this
  rw [hM'eq, F3L3.eq_one_of_pow_three_eq_one hp hl3, one_smul]

section Matrix


private theorem eq_top_of_omegaGL_normalizer {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hp : p % 3 = 2) {R : Matrix (Fin 3) (Fin 3) (ZMod p)} (hRt : Rᵀ = R) (hRd : R.det ≠ 0)
    {Y : SL(3, ZMod p)} (hY3 : Y ^ 3 = 1) (hY1 : Y ≠ 1) {M : Subgroup SL(3, ZMod p)}
    (hΩ : ⁅soForm R, soForm R⁆ ≤ M)
    (hN : ∀ g : SL(3, ZMod p),
      g ∈ Subgroup.normalizer (Subgroup.zpowers Y : Set SL(3, ZMod p)) → g ∈ M) :
    M = ⊤ := by
  have hpp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
    · exact absurd (h ▸ hpp) (by norm_num)
    · exact h
  have hp2 : p ≠ 2 := by omega
  have hΩS : omegaGL R ≤ glImage M := by
    rw [← CFSG.Quasithin.Vol2.Ch11.SecU1.L3I.map_toGL_commutator_soForm R]
    exact Subgroup.map_mono hΩ
  have hirr : IsIrreducibleMatrixRep (glImage M).subtype := fun W hW =>
    F3L3.omegaGL_irreducible hp5 hRt hRd W fun g w hw =>
      hW ⟨(g : GL (Fin 3) (ZMod p)), hΩS g.2⟩ w hw
  have hperf : Group.IsPerfect (omegaGL R) :=
    CFSG.RankThree.PartOne.KFBloom.omegaGL_isPerfect hp5 R hRt hRd
  have hpdvd : p ∣ Nat.card (omegaGL R) := p_dvd_card_omegaGL hp5 hRt hRd
  have hdetS : ∀ g ∈ glImage M, (g : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := fun g hg =>
    det_of_mem_glImage hg
  have hpdvdS : p ∣ Nat.card (glImage M) := hpdvd.trans (Subgroup.card_dvd_of_le hΩS)
  have hsolv : Group.IsSolvable ↥(glImage M) → False := by
    intro hs
    have : Group.IsSolvable ↥(omegaGL R) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hΩS)
        (Subgroup.inclusion_injective hΩS)
    have : Nontrivial ↥(omegaGL R) := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      exact lt_of_lt_of_le hpp.one_lt (Nat.le_of_dvd Nat.card_pos hpdvd)
    have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥(omegaGL R))
    rw [hperf.commutator_eq_top] at h1
    exact lt_irrefl _ h1
  obtain ⟨H, hHS, hnorm, hHirr, hcases⟩ :=
    CFSG.RankThree.SubgroupLists.bloom_mitchell_irreducible_gl_three hp2 hirr
  rcases hcases with h1 | ⟨M₀, hM₀t, hM₀d, hH⟩ | ⟨⟨e⟩, hp10, hdec, hint⟩ | ⟨⟨e⟩, hp7⟩ |
    ⟨hperfH, hZ, hA6, hp30⟩ | ⟨hcyc, -, -⟩ | ⟨hcard, hext, hp31⟩ | ⟨hHS', hmono⟩
  ·
    exact eq_top_of_stated_le_glImage (h1 ▸ hHS)
  ·
    exfalso
    subst hH
    have hiso : ∀ g ∈ glImage M, (g : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M₀ *
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = M₀ := fun g hg =>
      isometry_of_normalizes_omegaGL hp2 hp hM₀t hM₀d hHirr (hnorm g hg) (hdetS g hg)
    have hY3m : (Y : Matrix (Fin 3) (Fin 3) (ZMod p)) * Y * Y = 1 := by
      have := congrArg (fun z : SL(3, ZMod p) => (z : Matrix (Fin 3) (Fin 3) (ZMod p))) hY3
      simpa [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc] using this
    have hY1m : (Y : Matrix (Fin 3) (Fin 3) (ZMod p)) ≠ 1 := fun h =>
      hY1 (Subtype.ext (by simpa using h))
    obtain ⟨g, hgdet, hYg, hgM⟩ := F3L3.exists_commuting_scaling hp3 hp hY3m hY1m Y.2
    let G₂ : SL(3, ZMod p) := ⟨g, hgdet⟩
    have hcomm : G₂ * Y = Y * G₂ :=
      Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        exact hYg.symm)
    have hG₂N : G₂ ∈ Subgroup.normalizer (Subgroup.zpowers Y : Set SL(3, ZMod p)) := by
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_right hcomm k).eq.symm
    have hgS : Matrix.SpecialLinearGroup.toGL G₂ ∈ glImage M := ⟨G₂, hN G₂ hG₂N, rfl⟩
    exact hM₀d (hgM M₀ hM₀t (hiso _ hgS))
  ·
    exfalso
    have hnab : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := alt5_nonabelian
      refine ⟨(e.symm a : GL (Fin 3) (ZMod p)), (e.symm a).2,
        (e.symm b : GL (Fin 3) (ZMod p)), (e.symm b).2, fun h => hab ?_⟩
      have h' : e.symm a * e.symm b = e.symm b * e.symm a := Subtype.ext h
      have := congrArg e h'
      simpa using this
    have hle : glImage M ≤ H := by
      intro g hg
      obtain ⟨h, hh, z, hz, hzc, rfl⟩ := hdec g hg
      have hcomm : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (z : Matrix (Fin 3) (Fin 3) (ZMod p)) =
          (z : Matrix (Fin 3) (Fin 3) (ZMod p)) * (x : Matrix (Fin 3) (Fin 3) (ZMod p)) :=
        fun x hx => by
        rw [← Units.val_mul, ← Units.val_mul, ← hzc x (hHS hx)]
      obtain ⟨c, hc⟩ := scalar_of_commute_of_nonabelian hHirr hnab hcomm
      have hzd : (z : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
        have := hdetS _ hg
        rw [Units.val_mul, Matrix.det_mul, hdetS h (hHS hh), one_mul] at this
        exact this
      rw [F3L3.eq_one_of_scalar_det hp hc hzd, mul_one]
      exact hh
    have hcard : Nat.card (glImage M) = 60 := by
      rw [le_antisymm hle hHS, Nat.card_congr e.toEquiv, card_alt_five_fin]
    rw [hcard] at hpdvdS
    exact not_dvd_sixty hp3 hp10 hpdvdS
  ·
    exfalso
    have hp7' : p ≠ 7 := by omega
    have hdetH : ∀ y ∈ H, (y : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := fun y hy =>
      hdetS y (hHS hy)
    have hle : glImage M ≤ H := by
      intro g hg
      obtain ⟨h, hh, z, hz, rfl⟩ := normalizes_gl32 hp2 hp7' hdetH hHirr e (hnorm g hg)
        (fun x hx => by simpa using hnorm g⁻¹ ((glImage M).inv_mem hg) x hx)
      obtain ⟨c, hc⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hz
      have hzd : (z : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
        have := hdetS _ hg
        rw [Units.val_mul, Matrix.det_mul, hdetH h hh, one_mul] at this
        exact this
      rw [F3L3.eq_one_of_scalar_det hp hc.symm hzd, mul_one]
      exact hh
    have hGL32 : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
      CFSG.LieType.SteinbergBR.AutGL32.card_GL32
    have hcard : Nat.card (glImage M) = 168 := by
      rw [le_antisymm hle hHS, Nat.card_congr e.toEquiv, hGL32]
    rw [hcard] at hpdvdS
    exact not_dvd_168 hpp hp3 hp hp7 hpdvdS
  ·
    exfalso
    omega
  ·
    exact (hsolv (isSolvable_of_cyclic_normal hHS hnorm hHirr hcyc)).elim
  ·
    exfalso
    omega
  ·
    subst hHS'
    exact (hsolv (isSolvable_of_isTransitiveMonomial hmono)).elim

end Matrix

section Transport

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Ch1 CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

private theorem nonempty_equiv_psl3 {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (e : X ≃* projSL 3 (GaloisField p 1)) :
    Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod p)) := by
  have : Fintype (GaloisField p 1) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField p 1) = Fintype.card (ZMod p) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      GaloisField.card p 1 one_ne_zero, pow_one, Nat.card_zmod]
  exact ⟨e.trans ((CFSG.PGLModel.projSLEquivStatedProj 3 _).trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 _).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
        (FiniteField.ringEquivOfCardEq hc) (Fin 3))))⟩

private theorem exists_embedding_L3 {G : Type} [Group G] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hp : p % 3 = 2) {L : Subgroup G} [L.Normal] (hC : Subgroup.centralizer (L : Set G) = ⊥)
    (e : ↥L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod p)) {b : G} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) :
    ∃ (F : SL(3, ZMod p) →* G) (R : Matrix (Fin 3) (Fin 3) (ZMod p)), Function.Injective F ∧
      F.range = L ∧ Rᵀ = R ∧ R.det ≠ 0 ∧
      (soForm R).map F = L ⊓ Subgroup.centralizer ({b} : Set G) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨A, hA, hβ⟩ := exists_graph_of_outer hp2 hC e hbL hb2
  set ψ := e.trans (psl3EquivP p) with hψ
  set f : projectiveSL 3 (ZMod p) →* G := L.subtype.comp ψ.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp ψ.symm.injective
  have hfψ : ∀ (x : G) (hx : x ∈ L), f (ψ ⟨x, hx⟩) = x := fun x hx => by simp [hf]
  set R := ((A⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) with hR
  have hRt : Rᵀ = R := transpose_inv_of_transpose_eq' A hA
  have hRd : R.det ≠ 0 := GeneralLinearGroup.det_ne_zero _
  have hfix : ∀ x, b * f x * b⁻¹ = f x ↔
      (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x = x := by
    intro x
    have hβx : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x =
        ψ (MulAut.conjNormal b (ψ.symm x)) := by
      rw [← hβ]
      rfl
    rw [hβx]
    constructor
    · intro h
      apply ψ.symm.injective
      rw [MulEquiv.symm_apply_apply]
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      exact h
    · intro h
      have h1 := congrArg (fun y => ((ψ.symm y : ↥L) : G)) h
      simp only [MulEquiv.symm_apply_apply, MulAut.conjNormal_apply] at h1
      exact h1
  set F := f.comp (proj 3 (ZMod p)) with hF
  have hproj : Function.Injective (proj 3 (ZMod p)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨c, hc3, hcm⟩ := proj_eq_one_iff.1 hg
    have hc3' : (c : ZMod p) ^ 3 = 1 := by
      have := congrArg Units.val hc3
      simpa using this
    have hc1 := F3L3.eq_one_of_pow_three_eq_one hp hc3'
    refine Subtype.ext ?_
    rw [hcm, hc1]
    simp
  have hFinj : Function.Injective F := hfinj.comp hproj
  refine ⟨F, R, hFinj, ?_, hRt, hRd, ?_⟩
  ·
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (ψ.symm (proj 3 (ZMod p) s)).2
    · intro hx
      obtain ⟨s, hs⟩ := proj_surjective 3 (ZMod p) (ψ ⟨x, hx⟩)
      exact ⟨s, by rw [hF, MonoidHom.comp_apply, hs, hfψ x hx]⟩
  ·
    ext g
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨(ψ.symm (proj 3 (ZMod p) s)).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hx : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p))
          (proj 3 (ZMod p) s) = proj 3 (ZMod p) s :=
        (fixed_iff_mem_range_soProj hA _).mpr ⟨⟨s, hs⟩, rfl⟩
      have h1 := (hfix _).mpr hx
      have h2 : F s = f (proj 3 (ZMod p) s) := rfl
      rw [h2]
      calc f (proj 3 (ZMod p) s) * b = (b * f (proj 3 (ZMod p) s) * b⁻¹) * b := by rw [h1]
        _ = b * f (proj 3 (ZMod p) s) := by group
    · rintro ⟨hgL, hgC⟩
      have hgb := Subgroup.mem_centralizer_singleton_iff.mp hgC
      obtain ⟨x, hx⟩ : ∃ x, f x = g := ⟨ψ ⟨g, hgL⟩, hfψ g hgL⟩
      have hxf : (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x = x := by
        refine (hfix x).mp ?_
        rw [hx]
        calc b * g * b⁻¹ = g * b * b⁻¹ := by rw [hgb]
          _ = g := by group
      obtain ⟨s, hs⟩ := (fixed_iff_mem_range_soProj hA x).mp hxf
      refine ⟨s, s.2, ?_⟩
      have h1 : F s = f (soProj R s) := rfl
      rw [h1, hs, hx]

end Transport

theorem gen_normalizer_omega1412_L3
    {G : Type} [Group G] [Finite G] {L : Subgroup G} [L.Normal]
    (hC : Subgroup.centralizer (L : Set G) = ⊥) {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hp : p % 3 = 2) (e : ↥L ≃* projSL 3 (GaloisField p 1)) {b : G} (hbL : b ∉ L)
    (hb2 : orderOf b = 2) {y : G} (hyL : y ∈ L) (hy3 : orderOf y = 3) :
    L ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊔
      ⁅L ⊓ Subgroup.centralizer {b}, L ⊓ Subgroup.centralizer {b}⁆ := by
  have hpp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by
    rcases (show p = 4 ∨ 5 ≤ p by omega) with h | h
    · exact absurd (h ▸ hpp) (by norm_num)
    · exact h
  obtain ⟨e'⟩ := nonempty_equiv_psl3 e
  obtain ⟨F, R, hFinj, hFrange, hRt, hRd, hFH⟩ := exists_embedding_L3 hp5 hp hC e' hbL hb2
  obtain ⟨Y, hY⟩ : y ∈ F.range := hFrange ▸ hyL
  have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hY3 : Y ^ 3 = 1 := hFinj (by rw [map_pow, hY, hy3', map_one])
  have hY1 : Y ≠ 1 := fun h => by
    rw [h, map_one] at hY
    rw [← hY, orderOf_one] at hy3
    exact absurd hy3 (by norm_num)
  set S : Subgroup G := Subgroup.normalizer (Subgroup.zpowers y : Set G) ⊔
    ⁅L ⊓ Subgroup.centralizer ({b} : Set G), L ⊓ Subgroup.centralizer ({b} : Set G)⁆ with hS
  have hΩ : ⁅CFSG.QuasithinUnique.Ch1.soForm R, CFSG.QuasithinUnique.Ch1.soForm R⁆ ≤
      S.comap F := by
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator, hFH]
    exact le_sup_right
  have hN : ∀ g : SL(3, ZMod p),
      g ∈ Subgroup.normalizer (Subgroup.zpowers Y : Set SL(3, ZMod p)) → g ∈ S.comap F := by
    intro g hg
    have h1 : F g ∈ (Subgroup.normalizer (Subgroup.zpowers Y : Set SL(3, ZMod p))).map F :=
      ⟨g, hg, rfl⟩
    have h2 := Subgroup.le_normalizer_map F h1
    rw [MonoidHom.map_zpowers, hY] at h2
    exact Subgroup.mem_sup_left h2
  have htop := eq_top_of_omegaGL_normalizer hp3 hp hRt hRd hY3 hY1 hΩ hN
  intro l hl
  rw [← hFrange] at hl
  obtain ⟨s, rfl⟩ := hl
  have : s ∈ S.comap F := htop ▸ Subgroup.mem_top s
  exact this

end CFSG.RankThree.PartTwo.Sec20
