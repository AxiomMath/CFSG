module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1U3Odd
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Psl

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSL projSU)

namespace L3Even

section SL3

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanEps
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_form_of_involution' {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : GL (Fin 3) F}
    {c : F} (hBm3 : (B : Matrix (Fin 3) (Fin 3) F) ^ 3 = c • (1 : Matrix (Fin 3) (Fin 3) F))
    (hBs : ∀ x : F, (B : Matrix (Fin 3) (Fin 3) F) ≠ x • (1 : Matrix (Fin 3) (Fin 3) F))
    {T : GL (Fin 3) F} (hT2 : T * T = 1) (hT1 : T ≠ 1) (hTB : T * B = B * T) :
    ∃ (μ : F) (g : Matrix (Fin 3) (Fin 3) F) (j : Fin 3), μ ^ 3 = c ∧ μ ≠ 0 ∧ IsUnit g ∧
      (((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)) * g = g * diagonal ![τ, τ ^ 2, 1] ∨
        ((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)) * g = g * diagonal ![τ, 1, 1] ∨
        ((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)) * g =
          g * diagonal ![τ ^ 2, 1, 1]) ∧
      ((T : Matrix (Fin 3) (Fin 3) F) - 1 ≠ 0 ∧
        ((T : Matrix (Fin 3) (Fin 3) F) - 1) * ((T : Matrix (Fin 3) (Fin 3) F) - 1) = 0 ∧
        ∀ r : F, ((T : Matrix (Fin 3) (Fin 3) F) - 1) * (r • (B : Matrix (Fin 3) (Fin 3) F)) =
          (r • (B : Matrix (Fin 3) (Fin 3) F)) * ((T : Matrix (Fin 3) (Fin 3) F) - 1)) := by
  have hcommM : (T : Matrix (Fin 3) (Fin 3) F) * (B : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) := by
    rw [← Units.val_mul, hTB, Units.val_mul]
  have hTM2 : (T : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, hT2, Units.val_one]
  have hTM1 : (T : Matrix (Fin 3) (Fin 3) F) ≠ 1 := fun h1 =>
    hT1 (Units.ext (by rw [h1, Units.val_one]))
  obtain ⟨μ, hμ⟩ := u3OddEps_exists_cube_root_of_comm_involution hBm3 hTM2 hTM1 hcommM
  have hc0 : c ≠ 0 := by
    intro h0
    have hdet := congrArg Matrix.det hBm3
    rw [h0, zero_smul, Matrix.det_zero, Matrix.det_pow] at hdet
    have hu : IsUnit (B : Matrix (Fin 3) (Fin 3) F).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp B.isUnit
    exact hu.ne_zero ((pow_eq_zero_iff (by norm_num)).mp hdet)
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hc0
    rw [← hμ, h0]
    norm_num
  set Y : Matrix (Fin 3) (Fin 3) F := μ⁻¹ • (B : Matrix (Fin 3) (Fin 3) F) with hY
  have hY3 : Y ^ 3 = 1 := by
    rw [hY, smul_pow, hBm3, smul_smul, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow, one_smul]
  have hYs : ∀ x : F, Y ≠ x • (1 : Matrix (Fin 3) (Fin 3) F) := by
    intro x hx
    apply hBs (μ * x)
    calc (B : Matrix (Fin 3) (Fin 3) F)
        = μ • (μ⁻¹ • (B : Matrix (Fin 3) (Fin 3) F)) := by
          rw [smul_smul, mul_inv_cancel₀ hμ0, one_smul]
      _ = (μ * x) • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [← hY, hx, smul_smul]
  obtain ⟨g, j, hgU, hform⟩ :=
    Sec4.exists_normal_form hτ3 hτ1 U3Odd.three_ne_zero_char_two hY3 hYs
  have h2 : ∀ M : Matrix (Fin 3) (Fin 3) F, M + M = 0 := fun M => by
    rw [← two_smul F M, CharTwo.two_eq_zero, zero_smul]
  refine ⟨μ, g, j, hμ, hμ0, hgU, ?_, sub_ne_zero.mpr hTM1, ?_, fun r => ?_⟩
  · simpa only [hY, smul_smul] using hform
  · calc ((T : Matrix (Fin 3) (Fin 3) F) - 1) * ((T : Matrix (Fin 3) (Fin 3) F) - 1)
        = (T : Matrix (Fin 3) (Fin 3) F) * (T : Matrix (Fin 3) (Fin 3) F) -
          ((T : Matrix (Fin 3) (Fin 3) F) + (T : Matrix (Fin 3) (Fin 3) F)) + 1 := by
          noncomm_ring
      _ = 0 := by rw [hTM2, h2 _, sub_zero, h2 1]
  · have hNB : ((T : Matrix (Fin 3) (Fin 3) F) - 1) * (B : Matrix (Fin 3) (Fin 3) F) =
        (B : Matrix (Fin 3) (Fin 3) F) * ((T : Matrix (Fin 3) (Fin 3) F) - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, hcommM]
    simp only [Matrix.mul_smul, Matrix.smul_mul, hNB]

theorem odd_card_slCentralizer {τ : F} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {B : GL (Fin 3) F}
    (hdet : (B : Matrix (Fin 3) (Fin 3) F).det = 1) (hB3 : B ^ 3 = 1)
    (hBs : ∀ x : F, (B : Matrix (Fin 3) (Fin 3) F) ≠ x • (1 : Matrix (Fin 3) (Fin 3) F)) :
    Odd (Nat.card ((Subgroup.centralizer ({B} : Set (GL (Fin 3) F))).subgroupOf
      (CFSG.Open.StatedSL 3 F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
  set T : GL (Fin 3) F := ((t : CFSG.Open.StatedSL 3 F) : GL (Fin 3) F) with hTdef
  have hTord : orderOf T = 2 := by
    rw [hTdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
  have hT2 : T * T = 1 := by
    rw [← sq, ← hTord]
    exact pow_orderOf_eq_one _
  have hT1 : T ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hTord
    norm_num at hTord
  have hTB : T * B = B * T := Subgroup.mem_centralizer_singleton_iff.mp t.2
  have hBm3 : (B : Matrix (Fin 3) (Fin 3) F) ^ 3 = (1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [one_smul, ← Units.val_pow_eq_pow_val, hB3, Units.val_one]
  obtain ⟨μ, g, j, hμ, hμ0, hgU, hform, hN0, hN2, hNX⟩ :=
    exists_form_of_involution' hτ3 hτ1 hBm3 hBs hT2 hT1 hTB
  have hgdet : g.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det g).mp hgU).ne_zero
  have hdetS : ((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)).det = 1 := by
    rw [Matrix.det_smul, hdet, mul_one, Fintype.card_fin, mul_pow, ← pow_mul, mul_comm (j : ℕ) 3,
      pow_mul, hτ3, one_pow, one_mul, inv_pow, hμ, inv_one]
  have key : ∀ D : Matrix (Fin 3) (Fin 3) F,
      ((τ ^ (j : ℕ) * μ⁻¹) • (B : Matrix (Fin 3) (Fin 3) F)) * g = g * D → D.det = 1 := by
    intro D hD
    have h1 := congrArg Matrix.det hD
    rw [Matrix.det_mul, Matrix.det_mul, hdetS, one_mul] at h1
    exact mul_left_cancel₀ hgdet (h1.symm.trans (mul_one _).symm)
  rcases hform with hA | hB' | hC
  · exact hN0 (u3OddEps_eq_zero_of_regular (u3OddEps_distinct_tau hτ3 hτ1) hgU hA (hNX _) hN2)
  · have := key _ hB'
    rw [Matrix.det_diagonal, Fin.prod_univ_three] at this
    change τ * 1 * 1 = 1 at this
    rw [mul_one, mul_one] at this
    exact hτ1 this
  · have := key _ hC
    rw [Matrix.det_diagonal, Fin.prod_univ_three] at this
    change τ ^ 2 * 1 * 1 = 1 at this
    rw [mul_one, mul_one] at this
    exact (u3OddEps_tau_facts hτ3 hτ1).2.1 this

end SL3

section Lin

open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4.RonanEps
open CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK (fixedField)
open scoped commutatorElement

attribute [local instance] RonanEps.finite_projectiveSL_three

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem simple_of_linear {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Even n) (hn2 : 2 ≤ n)
    {g : GL (Fin 3) F} (hα3 : conjAut 3 F g ^ 3 = 1) (hα1 : conjAut 3 F g ≠ 1)
    {K : Subgroup (projectiveSL 3 F)} (hKC : K ≤ Sec4.autFix (conjAut 3 F g))
    (hKq : IsQuasisimple K) (hKs : (K.subgroupOf (Sec4.autFix (conjAut 3 F g))).IsSubnormal) :
    IsSimpleGroup K ∧ Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect K := hKq.1
  have hn1 : 1 ≤ n := by omega
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hfix : ∀ k ∈ K, conjAut 3 F g k = k := fun k hk => Sec4.mem_autFix.mp (hKC hk)
  have h2K : 2 ∣ Nat.card K :=
    even_iff_two_dvd.mp (CFSG.RankThree.OddKernel.even_card_of_isQuasisimple hKq)
  have hevC0 : ¬ Odd (Nat.card ↥(C0 g)) := by
    intro hodd
    have hK : Nat.card ↥K ∣ Nat.card ↥⁅K.comap (LinearFlag.proj 3 F),
        K.comap (LinearFlag.proj 3 F)⁆ := by
      have := Subgroup.card_map_dvd ⁅K.comap (LinearFlag.proj 3 F),
        K.comap (LinearFlag.proj 3 F)⁆ (LinearFlag.proj 3 F)
      rwa [map_proj_commutator_comap K] at this
    have hK₁ := Subgroup.card_dvd_of_le (commutator_comap_le_C0 K hfix)
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2K.trans (hK.trans hK₁)))
  obtain ⟨c, hc3⟩ := exists_scalar_of_conjAut_pow_three rfl hα3
  have hgM := RonanEps.pow_three_matrix_eq_scalar hc3
  obtain ⟨μ, hμc⟩ : ∃ μ : F, μ ^ 3 = (c : F) := by
    by_contra hμ
    exact hevC0 (odd_card_C0_of_no_cube_root hgM hμ)
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply Units.ne_zero c
    rw [← hμc, h0]
    norm_num
  set u : Fˣ := Units.mk0 μ hμ0 with hu
  have hu3 : u ^ 3 = c := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hμc)
  have hscal : Commute (Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ : GL (Fin 3) F) g :=
    (Subgroup.mem_center_iff.mp (scalar_mem_center (F := F) u⁻¹) g).symm
  set gp : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ * g with hgp
  have hg_eq : g = Matrix.GeneralLinearGroup.scalar (Fin 3) u * gp := by
    rw [hgp, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hgp3 : gp ^ 3 = 1 := by
    rw [hgp, Commute.mul_pow hscal, ← map_pow, ← hc3, ← map_mul, inv_pow, hu3, inv_mul_cancel,
      map_one]
  obtain ⟨ω, hω⟩ := exists_omega_of_card hF hn
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω
    norm_num at hω
  obtain ⟨h, a, hdiag⟩ :=
    RonanK432.exists_conj_diagonal_of_pow_three hω (three_ne_zero_of_charTwo F) hgp3
  obtain ⟨E0, s1, t2, hD⟩ := exists_scalar_diagUnits_eq hω0 a h gp hdiag
  have hcen_u : h * Matrix.GeneralLinearGroup.scalar (Fin 3) u =
      Matrix.GeneralLinearGroup.scalar (Fin 3) u * h :=
    Subgroup.mem_center_iff.mp (scalar_mem_center (F := F) u) h
  have hy : (h⁻¹)⁻¹ * g * h⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 3) (u * E0) * diagUnits 1 s1 t2 := by
    rw [inv_inv, hg_eq]
    calc h * (Matrix.GeneralLinearGroup.scalar (Fin 3) u * gp) * h⁻¹
        = (h * Matrix.GeneralLinearGroup.scalar (Fin 3) u) * gp * h⁻¹ := by group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u * (h * gp * h⁻¹) := by
          rw [hcen_u]
          group
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) u *
            (Matrix.GeneralLinearGroup.scalar (Fin 3) E0 * diagUnits 1 s1 t2) := by rw [hD]
      _ = Matrix.GeneralLinearGroup.scalar (Fin 3) (u * E0) * diagUnits 1 s1 t2 := by
          rw [map_mul, mul_assoc]
  have hnc : ∃ M ∈ slPi true 3 (2 ^ n) F, M * g ≠ g * M := by
    by_contra hcon
    push Not at hcon
    apply hα1
    apply MulEquiv.ext
    intro p
    obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective 3 F p
    exact conjAut_proj_eq_self_of_comm g x
      (hcon (Matrix.SpecialLinearGroup.toGL x) ((mem_slPi_true (2 ^ n)).mpr x.2))
  have hPi : PiField true 2 n F := ⟨Nat.prime_two, hn1, by rw [hF]; rfl⟩
  have hev : Even (Nat.card ↥(slPi true 3 (2 ^ n) F ⊓
      Subgroup.centralizer ({g} : Set (GL (Fin 3) F)))) := by
    rw [← card_C0_eq g (2 ^ n)]
    exact Nat.not_odd_iff_even.mp hevC0
  obtain ⟨ψR⟩ := Sec21.SL3Lines.perfectResidual_centralizer_of_conj (y := g) (g := h⁻¹)
    (l := u * E0) (s := s1) (t := t2) hPi h4 hy hnc hev
  haveI := isPerfect_commutator_comap K
  set K₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    ⁅K.comap (LinearFlag.proj 3 F), K.comap (LinearFlag.proj 3 F)⁆ with hK₁
  have h1 : K₁.map (LinearFlag.proj 3 F) = K := map_proj_commutator_comap K
  have h2 : K₁ ≤ C0 g := commutator_comap_le_C0 K hfix
  set X : Subgroup (GL (Fin 3) F) :=
    slPi true 3 (2 ^ n) F ⊓ Subgroup.centralizer ({g} : Set (GL (Fin 3) F)) with hX
  set R : Subgroup (GL (Fin 3) F) := inSubgroup perfectResidual X with hR
  set R' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    R.comap Matrix.SpecialLinearGroup.toGL with hR'
  have hRX : R ≤ X := Subgroup.map_subtype_le _
  have hXrange : X ≤ Matrix.SpecialLinearGroup.toGL.range := by
    rw [← slPi_true_eq_range F (2 ^ n)]
    exact inf_le_left
  have hR'comm : ∀ x ∈ R', Matrix.SpecialLinearGroup.toGL x * g =
      g * Matrix.SpecialLinearGroup.toGL x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_inf.mp (hRX (Subgroup.mem_comap.mp hx))).2
  have hK₁R' : ∀ x ∈ K₁, x ∈ R' := by
    intro x hx
    have hP : Subgroup.map Matrix.SpecialLinearGroup.toGL K₁ ≤ R := by
      apply le_inSubgroup_perfectResidual (Group.IsPerfect.map Matrix.SpecialLinearGroup.toGL)
      intro y hy
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact (mem_slPi_true (2 ^ n) (A := Matrix.SpecialLinearGroup.toGL z)).mpr z.2
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (mem_C0.mp (h2 hz))
    exact Subgroup.mem_comap.mpr (hP (Subgroup.mem_map_of_mem _ hx))
  have hRrange : ∀ r ∈ R, ∃ x : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.SpecialLinearGroup.toGL x = r := fun r hr =>
    MonoidHom.mem_range.mp (hXrange (hRX hr))
  let Ein : ↥R' →* ↥R := MonoidHom.codRestrict
    (Matrix.SpecialLinearGroup.toGL.comp R'.subtype) R (fun x => Subgroup.mem_comap.mp x.2)
  have hEin : Function.Bijective Ein := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.toGL_injective
      exact congrArg Subtype.val hxy
    · intro r
      obtain ⟨x, hx⟩ := hRrange r.1 r.2
      exact ⟨⟨x, Subgroup.mem_comap.mpr (by rw [hx]; exact r.2)⟩, Subtype.ext hx⟩
  let e : ↥R' ≃* Matrix.SpecialLinearGroup (Fin 2) F := (MulEquiv.ofBijective Ein hEin).trans ψR
  have hZR' : Subgroup.center ↥R' = ⊥ :=
    RonanK429.center_eq_bot_of_mulEquiv e Sec19.Item19Res2Proof.center_sl2_eq_bot
  set fN : ↥R' →* LinearFlag.projectiveSL 3 F := (LinearFlag.proj 3 F).comp R'.subtype with hf
  have hinj : Function.Injective fN := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : LinearFlag.proj 3 F (x : Matrix.SpecialLinearGroup (Fin 3) F) = 1 := hx
    have hxs : (x : Matrix.SpecialLinearGroup (Fin 3) F) ∈ scalars 3 F :=
      LinearFlag.proj_eq_one_iff.mp hx'
    have hxc : x ∈ Subgroup.center ↥R' := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp (scalars_le_center 3 F hxs) y.1
    rw [hZR', Subgroup.mem_bot] at hxc
    exact hxc
  set N : Subgroup (LinearFlag.projectiveSL 3 F) := fN.range with hN
  let ιN : ↥N ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MonoidHom.ofInjective hinj).symm.trans e
  have hKN : K ≤ N := by
    intro y hy
    rw [← h1] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact MonoidHom.mem_range.mpr ⟨⟨x, hK₁R' x hx⟩, rfl⟩
  have hNC : N ≤ Sec4.autFix (conjAut 3 F g) := by
    intro y hy
    obtain ⟨z, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [Sec4.mem_autFix]
    exact conjAut_proj_eq_self_of_comm g z.1 (hR'comm z.1 z.2)
  obtain ⟨hNs, -, hNcard⟩ := sl2_char_two_data h4 ιN.symm
  have hKeq : K = N := eq_of_subnormal_of_le_simple hKN hNC hKs hNs (ne_bot_of_isQuasisimple hKq)
  subst hKeq
  exact ⟨hNs, by rw [hNcard, hF]⟩

theorem sl2_card_ne_sixty' {n : ℕ} (hn4 : 4 ≤ n) : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 60 :=
  U3Odd.sl2_card_ne_sixty (by omega)

theorem good427_linear {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Even n) (hn4 : 4 ≤ n)
    {g : GL (Fin 3) F} (hα3 : conjAut 3 F g ^ 3 = 1) (hα1 : conjAut 3 F g ≠ 1) :
    Good427 (Sec4.autFix (conjAut 3 F g)) := by
  intro K hKC hKq hKs hA5
  obtain ⟨hs, hcard⟩ := simple_of_linear hF hn (by omega) hα3 hα1 hKC hKq hKs
  haveI := hs
  exact not_isA5Type_of_simple (exists_ne_comm_of_isQuasisimple hKq)
    (by rw [hcard]; exact sl2_card_ne_sixty' hn4) hA5

theorem onFree_inner {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Even n) (hn4 : 4 ≤ n)
    (hZ : Subgroup.center (projectiveSL 3 F) = ⊥) {y : projectiveSL 3 F} (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) : OnFree (Subgroup.centralizer ({y} : Set (projectiveSL 3 F))) y := by
  obtain ⟨x, rfl⟩ := LinearFlag.proj_surjective 3 F y
  have hconj := KFacts.conj_proj_eq_conjAut 3 F x
  have hB3 : conjAut 3 F (Matrix.SpecialLinearGroup.toGL x) ^ 3 = 1 := by
    rw [← hconj, ← map_pow, hy3, map_one]
  have hB1 : conjAut 3 F (Matrix.SpecialLinearGroup.toGL x) ≠ 1 := by
    rw [← hconj]
    intro h1
    apply hy1
    exact RonanKChevTwo.conj_injective_of_center_eq_bot hZ (h1.trans (map_one _).symm)
  have hC : Subgroup.centralizer ({LinearFlag.proj 3 F x} : Set (projectiveSL 3 F)) =
      Sec4.autFix (conjAut 3 F (Matrix.SpecialLinearGroup.toGL x)) := by
    rw [← hconj, autFix_conj]
  refine (good427_onFree_of_simple_qs hy1
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.mp hc) fun K hKC hKq hKs => ?_).2
  rw [hC] at hKC hKs
  obtain ⟨hs, hcard⟩ := simple_of_linear hF hn (by omega) hB3 hB1 hKC hKq hKs
  exact ⟨hs, by rw [hcard]; exact sl2_card_ne_sixty' hn4⟩

theorem good427_field {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn2 : 2 ≤ n)
    {α : MulAut (projectiveSL 3 F)} (hα3 : α ^ 3 = 1) (hD : α ∉ linearAutGroup 3 F) :
    Good427 (Sec4.autFix α) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro K hKC hKq hKs hA5
  haveI : Group.IsPerfect K := hKq.1
  have hnt : K ≠ ⊥ := ne_bot_of_isQuasisimple hKq
  obtain ⟨φ, hφ, H, hαH⟩ := linear_order_three_field_descent le_rfl α hα3 hD
  have hr : MulAut.congr (MulEquiv.refl (projectiveSL 3 F)) α = α := MulEquiv.ext fun x => rfl
  have hστ : MulAut.congr ((MulEquiv.refl (projectiveSL 3 F)).trans (conjAut 3 F H)⁻¹) α =
      fieldAut 3 F φ := by
    rw [congr_trans_mulAut, hr, hαH]
    group
  obtain ⟨a, ha⟩ := exists_card_eq_sixty_mul hA5
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3dvd : 3 ∣ Nat.card K := by
    rw [ha]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := K) 3 h3dvd
  have hk3 : k ^ 3 = 1 := by
    have h := pow_orderOf_eq_one k
    rwa [hk] at h
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk
    norm_num at hk
  have h3 : ∃ k' ∈ K, k' ≠ 1 ∧ k' ^ 3 = 1 :=
    ⟨k, k.2, fun h => hk1 (Subtype.ext h), by
      have := congrArg Subtype.val hk3
      simpa using this⟩
  obtain ⟨⟨eK⟩, -⟩ := fieldCase_linear _ hστ (fun x => Sec4.mem_autFix) hKC hnt hKs h3
  obtain ⟨h3n, -⟩ := eq_frobenius_pow_of_orderOf_eq_three Nat.prime_two (by omega) hF hφ
  obtain ⟨m, rfl⟩ := h3n
  have hm : 1 ≤ m := by omega
  have hcube : Nat.card F = (2 ^ m) ^ 3 := by rw [hF, ← pow_mul, mul_comm]
  have hK₀ : Nat.card (fixedField φ) = 2 ^ m := card_fixedField_of_orderOf_eq_three hφ hcube
  haveI := isSimpleGroup_projectiveSL_three (fixedField φ)
  haveI : IsSimpleGroup K := eK.isSimpleGroup
  obtain ⟨φ₁⟩ := nonempty_projSL_mulEquiv 3 (fixedField φ)
  have h8 : 2 ^ (3 * m) ∣ Nat.card K := by
    rw [Nat.card_congr (eK.trans φ₁.symm).toEquiv]
    have hc := KFacts.KS14.card_projSL_three_mul_gcd (fixedField φ)
    rw [hK₀] at hc
    exact two_pow_dvd_of_mul_gcd hc
  refine not_isA5Type_of_simple (exists_ne_comm_of_isQuasisimple hKq) (fun h60 => ?_) hA5
  rw [h60] at h8
  have : 2 ^ 3 ∣ 60 := (pow_dvd_pow 2 (by omega)).trans h8
  norm_num at this

theorem noCfgS427_psl3 {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : Even n) (hn4 : 4 ≤ n) :
    NoCfgS427 (projectiveSL 3 F) := by
  intro α hα3 hα1
  by_cases hD : α ∈ linearAutGroup 3 F
  · rw [linearAutGroup_eq_range] at hD
    obtain ⟨g, rfl⟩ := hD
    exact good427_linear hF hn hn4 hα3 hα1
  · exact good427_field hF (by omega) hα3 hD

end Lin

section Cover

open CFSG.Open (StatedSL StatedScalars StatedProj)

theorem center_or_odd_sl3
    {n : ℕ} (hn : Even n) (hn2 : 2 ≤ n) {L : Type} [Group L]
    [Finite L] (hL : IsQuasisimple L) (hZ3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL 3 (GaloisField 2 n))) :
    Subgroup.center L = ⊥ ∨ ∀ x : L, x ^ 3 = 1 → x ∉ Subgroup.center L →
      Odd (Nat.card (Subgroup.centralizer ({x} : Set L))) := by
  set K := GaloisField 2 n with hKdef
  haveI : Group.IsPerfect L := hL.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hoddZ : Odd (Nat.card (Subgroup.center L)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
    rw [hk]
    exact Odd.pow (by decide)
  have hK : Nat.card K = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨φ, hφs, hker, hDmap⟩ :=
    CFSG.SectionRank.EvenCover.even_linear_perfect_odd_cover_map (by norm_num : 2 ≤ 3) hoddZ e
  by_cases hZ : Subgroup.center L = ⊥
  · exact Or.inl hZ
  right
  set D : Subgroup (StatedSL 3 K) := (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) with hD
  have hD3 : Nat.card D ∣ 3 :=
    (Sec19.Census194.RonanC194.card_scalars_statedSL_dvd (K := K) (by norm_num : 1 ≤ 3)).1
  have hkerbot : φ.ker = ⊥ := by
    have hd : Nat.card φ.ker ∣ Nat.card D := Subgroup.card_dvd_of_le hker
    rcases (Nat.dvd_prime Nat.prime_three).mp (hd.trans hD3) with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hDc : Nat.card D = 3 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hD3 with h | h
        · rw [h] at hd
          rw [h3] at hd
          norm_num at hd
        · exact h
      have hkD : φ.ker = D := Subgroup.eq_of_le_of_card_ge hker (by rw [hDc, h3])
      apply hZ
      rw [← hDmap, ← hkD]
      exact (Subgroup.map_eq_bot_iff _).mpr le_rfl
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  let eφ : StatedSL 3 K ≃* L := MulEquiv.ofBijective φ ⟨hinj, hφs⟩
  intro x hx3 hxZ
  set B := eφ.symm x with hBdef
  have hB3 : (B : GL (Fin 3) K) ^ 3 = 1 := by
    have : B ^ 3 = 1 := by rw [hBdef, ← map_pow, hx3, map_one]
    rw [← Subgroup.coe_pow, this, Subgroup.coe_one]
  have hBs : ∀ c : K, ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hc
    apply hxZ
    have hc0 : c ≠ 0 := by
      rintro rfl
      have hdet := congrArg Matrix.det hc
      rw [zero_smul, Matrix.det_zero] at hdet
      exact ((Matrix.isUnit_iff_isUnit_det _).mp (B : GL (Fin 3) K).isUnit).ne_zero hdet
    have hBD : B ∈ D := by
      rw [hD, Subgroup.mem_subgroupOf]
      refine ⟨Units.mk0 c hc0, ?_⟩
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
        ← Matrix.smul_one_eq_diagonal]
      exact hc.symm
    rw [← hDmap]
    exact ⟨B, hBD, by rw [hBdef]; exact eφ.apply_symm_apply x⟩
  obtain ⟨ω, hω⟩ := RonanEps.exists_omega_of_card hK hn
  have hω3 : ω ^ 3 = 1 := by linear_combination (ω - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    rw [h1] at hω
    have h3 : (3 : K) = 0 := by linear_combination hω
    exact RonanEps.three_ne_zero_of_charTwo K h3
  have hdet : ((B : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    CFSG.SectionRank.OddCover.det_of_mem_statedSL B.2
  have hodd2 := odd_card_slCentralizer hω3 hω1 hdet hB3 hBs
  have hcent : (Subgroup.centralizer ({B} : Set (StatedSL 3 K))).map eφ.toMonoidHom =
      Subgroup.centralizer ({x} : Set L) := by
    rw [centralizer_map_mulEquiv, hBdef, MulEquiv.apply_symm_apply]
  have heq : Subgroup.centralizer ({B} : Set (StatedSL 3 K)) =
      (Subgroup.centralizer ({(B : GL (Fin 3) K)} : Set (GL (Fin 3) K))).subgroupOf
        (StatedSL 3 K) := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [← hcent, Subgroup.card_map_of_injective (f := eφ.toMonoidHom) eφ.injective, heq]
  exact hodd2

end Cover

end L3Even

open L3Even

section Rows


open CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem rowOf427_sl3_even
    : ∀ n : ℕ, 4 ≤ n → Even n → RowOf427 (projSL 3 (GaloisField 2 n)) := by
  intro n hn4 hev S _ _ hs hna ⟨eSX⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  obtain ⟨φ₀⟩ := nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
  let τ : S ≃* projectiveSL 3 (GaloisField 2 n) := eSX.trans φ₀
  haveI : Finite (projectiveSL 3 (GaloisField 2 n)) := Finite.of_equiv _ τ.toEquiv
  have hZ : Subgroup.center (projectiveSL 3 (GaloisField 2 n)) = ⊥ := by
    have hZS : Subgroup.center S = ⊥ := RonanK429.center_eq_bot_of_isSimpleGroup hs hna
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : τ.symm z ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      apply τ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact hz (τ g)
    rw [hZS, Subgroup.mem_bot] at hz'
    rw [← τ.apply_symm_apply z, hz', map_one]
  refine row427_of_noCfg_on' ?_ ?_ ?_
  · intro L _ _ _ hL hZ3 ⟨e'⟩
    exact center_or_odd_sl3 hev (by omega) hL hZ3
      ((e'.trans eSX).trans (CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField 2 n)))
  · intro S' _ _ ⟨e'⟩
    exact NoCfgS427.of_mulEquiv (e'.trans τ) (noCfgS427_psl3 hF hev hn4)
  · intro S' _ _ ⟨e'⟩ y hy1 hy3
    have hx3 : (e'.trans τ) y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have hx1 : (e'.trans τ) y ≠ 1 := by
      rw [Ne, map_eq_one_iff _ (e'.trans τ).injective]
      exact hy1
    have h1 := (onFree_inner hF hev hn4 hZ hx1 hx3).map (e'.trans τ).symm
    rwa [MulEquiv.symm_apply_apply] at h1

end Rows

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
