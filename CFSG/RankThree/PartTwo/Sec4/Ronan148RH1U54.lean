module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148RH1A8
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowLieType
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
public import CFSG.GH74.GLS.Bg.TwoGroups.L23Models
public import CFSG.RankThree.PartOne.U5K.Model

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429 CFSG.RankThree.PartTwo.Sec4.RonanK429H
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Assembly.RankThreeEven (projSU)

section Quot

variable {Y : Type} [Group Y] [Finite Y]

theorem card_map_mk_of_inf_eq_bot (N : Subgroup Y) [N.Normal] {P : Subgroup Y} (h : P ⊓ N = ⊥) :
    Nat.card (P.map (QuotientGroup.mk' N)) = Nat.card P := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx' : (x : Y) ∈ P ⊓ N := ⟨x.2, hx⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  have hrange : ((QuotientGroup.mk' N).comp P.subtype).range = P.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]

theorem e9_map_mk (N : Subgroup Y) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {P : Subgroup Y}
    (hP : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    CFSG.Assembly.IsElemAbelian 3 (P.map (QuotientGroup.mk' N)) ∧
      Nat.card (P.map (QuotientGroup.mk' N)) = 9 := by
  refine ⟨isElemAbelian_map _ hP, ?_⟩
  rw [card_map_mk_of_inf_eq_bot N (Subgroup.inf_eq_bot_of_coprime ?_), hP9]
  rw [hP9, show (9 : ℕ) = 3 ^ 2 by norm_num]
  exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN)

theorem e9Move_quotient (N : Subgroup Y) [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (h : E9Move Y) :
    E9Move (Y ⧸ N) := by
  intro E' hE' hE'9 s' hs' hs'1
  obtain ⟨P, hPmap, hP9, hPN, hP⟩ := RonanK429Lie.exists_e9_lift N hN hE' hE'9
  rw [← hPmap] at hs'
  obtain ⟨s, hsP, rfl⟩ := hs'
  have hs1 : s ≠ 1 := by
    rintro rfl
    exact hs'1 (map_one _)
  obtain ⟨n, hn, hns⟩ := h P hP hP9 s hsP hs1
  refine ⟨QuotientGroup.mk' N n, ?_, fun hmn => hns ?_⟩
  · rw [← hPmap]
    exact Subgroup.le_normalizer_map _ ⟨n, hn, rfl⟩
  · refine mem_normalizer_of_map_le ?_
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    have h1 : QuotientGroup.mk' N (n * s * n⁻¹) ∈ Subgroup.zpowers (QuotientGroup.mk' N s) := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hmn _).mp (Subgroup.mem_zpowers _)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    rw [← map_zpow] at hk
    have h2 : (s ^ k)⁻¹ * (n * s * n⁻¹) ∈ N := by
      rw [← QuotientGroup.eq]
      exact hk
    have h3 : n * s * n⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hn s).mp hsP
    have h4 : (s ^ k)⁻¹ * (n * s * n⁻¹) ∈ P ⊓ N :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (zpow_mem hsP k)) h3, h2⟩
    rw [hPN, Subgroup.mem_bot, inv_mul_eq_one] at h4
    show n * s * n⁻¹ ∈ Subgroup.zpowers s
    rw [← h4]
    exact zpow_mem (Subgroup.mem_zpowers s) k

end Quot

namespace SU54

open CFSG.GH74.GLS.Bg.TwoGroups.L23 (F16c)
open Matrix

abbrev K16 : Type := GaloisField 2 (2 * 2)

abbrev U : Type := ↥(CFSG.Open.StatedSU 5 (2 ^ 2) K16)

noncomputable def eK' : K16 ≃+* F16c :=
  let _ : Fintype K16 := Fintype.ofFinite K16
  FiniteField.ringEquivOfCardEq (K := K16) (K' := F16c) (by
    have h1 : Fintype.card K16 = 16 := by
      rw [← Nat.card_eq_fintype_card]
      have := GaloisField.card 2 (2 * 2) (by norm_num)
      simpa using this
    rw [h1]
    decide)

noncomputable def eK : F16c ≃+* K16 := eK'.symm

@[expose] noncomputable def Φ : Matrix (Fin 5) (Fin 5) K16 ≃+* Matrix (Fin 5) (Fin 5) F16c :=
  eK.symm.mapMatrix

@[expose] noncomputable def toM : U →* Matrix (Fin 5) (Fin 5) F16c :=
  (Φ.toMonoidHom.comp (Units.coeHom (Matrix (Fin 5) (Fin 5) K16))).comp
    (CFSG.Open.StatedSU 5 (2 ^ 2) K16).subtype

theorem toM_apply (a : U) :
    toM a = Φ (((a : GL (Fin 5) K16)) : Matrix (Fin 5) (Fin 5) K16) := rfl

theorem toM_injective : Function.Injective toM := by
  intro a b e
  rw [toM_apply, toM_apply] at e
  exact Subtype.ext (Units.ext (Φ.injective e))

theorem toM_inv_of {a : U} {A Ai : Matrix (Fin 5) (Fin 5) F16c} (h : toM a = A) (hA : A * Ai = 1) :
    toM a⁻¹ = Ai := by
  calc toM a⁻¹ = toM a⁻¹ * (A * Ai) := by rw [hA, mul_one]
    _ = toM (a⁻¹ * a) * Ai := by rw [map_mul, h, mul_assoc]
    _ = Ai := by rw [inv_mul_cancel, map_one, one_mul]

@[expose] def w16 : F16c := ⟨0, 1, 1, 0⟩

@[expose] def w16sq : F16c := ⟨1, 1, 1, 0⟩

@[expose] def u4G1 : Matrix (Fin 5) (Fin 5) F16c :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨1, 0, 1, 0⟩]

@[expose] def u4G1i : Matrix (Fin 5) (Fin 5) F16c :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩]

@[expose] def u4G2 : Matrix (Fin 5) (Fin 5) F16c :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨1, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]

@[expose] def u4G2i : Matrix (Fin 5) (Fin 5) F16c :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 0, 1, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩]

@[expose] def u4M : Matrix (Fin 5) (Fin 5) F16c :=
  !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨1, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

@[expose] def u4Mi : Matrix (Fin 5) (Fin 5) F16c :=
  !![⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨0, 1, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 1, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

@[expose] def u4R : Matrix (Fin 5) (Fin 5) F16c :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 0⟩, ⟨1, 0, 1, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨1, 1, 1, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

@[expose] def u4Ri : Matrix (Fin 5) (Fin 5) F16c :=
  !![⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨1, 1, 1, 0⟩, ⟨1, 0, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩;
    ⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨1, 1, 1, 0⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]

theorem u4G1_mul : u4G1 * u4G1i = 1 := by decide +kernel
theorem u4G1_mul' : u4G1i * u4G1 = 1 := by decide +kernel
theorem u4G2_mul : u4G2 * u4G2i = 1 := by decide +kernel
theorem u4G2_mul' : u4G2i * u4G2 = 1 := by decide +kernel
theorem u4R_mul : u4R * u4Ri = 1 := by decide +kernel
theorem u4R_mul' : u4Ri * u4R = 1 := by decide +kernel
theorem u4M_mul' : u4Mi * u4M = 1 := by decide +kernel

theorem u4G1_unitary : (u4G1.map (· ^ (2 ^ 2)))ᵀ * u4G1 = 1 := by decide +kernel
theorem u4G2_unitary : (u4G2.map (· ^ (2 ^ 2)))ᵀ * u4G2 = 1 := by decide +kernel
theorem u4R_unitary : (u4R.map (· ^ (2 ^ 2)))ᵀ * u4R = 1 := by decide +kernel

theorem u4G1_pow : u4G1 ^ 3 = 1 := by decide +kernel
theorem u4G2_pow : u4G2 ^ 3 = 1 := by decide +kernel
theorem u4R_pow : u4R ^ 4 = 1 := by decide +kernel
theorem u4G12 : u4G1 * u4G2 = u4G2 * u4G1 := by decide +kernel
theorem u4G1_ne : u4G1 ≠ 1 := by decide +kernel
theorem u4G2_ne : u4G2 ≠ 1 := by decide +kernel
theorem u4G2_ne_G1 : u4G2 ≠ u4G1 := by decide +kernel
theorem u4G2_ne_G1i : u4G2 ≠ u4G1i := by decide +kernel

theorem u4R_G1 : u4R * u4G1 * u4Ri = u4G2 ^ 2 := by decide +kernel

theorem u4R_G2 : u4R * u4G2 * u4Ri = u4G1 := by decide +kernel

theorem u4G1_diag : u4G1 = u4M * Matrix.diagonal ![w16, w16sq, 1, 1, 1] * u4Mi := by decide +kernel

theorem u4G2_diag : u4G2 = u4M * Matrix.diagonal ![1, 1, w16, w16sq, 1] * u4Mi := by decide +kernel

theorem f16c_eq_one_of_pow_four : ∀ c : F16c, c ^ 4 = 1 → c = 1 := by decide +kernel

theorem det_u4M : u4Mi.det * u4M.det = 1 := by rw [← Matrix.det_mul, u4M_mul', Matrix.det_one]

theorem det_u4G1 : u4G1.det = 1 := by
  have hD : (Matrix.diagonal ![w16, w16sq, 1, 1, 1]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_five]
    decide +kernel
  rw [u4G1_diag, Matrix.det_mul, Matrix.det_mul, hD, mul_one, mul_comm, det_u4M]

theorem det_u4G2 : u4G2.det = 1 := by
  have hD : (Matrix.diagonal ![1, 1, w16, w16sq, 1]).det = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_five]
    decide +kernel
  rw [u4G2_diag, Matrix.det_mul, Matrix.det_mul, hD, mul_one, mul_comm, det_u4M]

theorem det_u4R : u4R.det = 1 :=
  f16c_eq_one_of_pow_four _ (by rw [← Matrix.det_pow, u4R_pow, Matrix.det_one])

noncomputable def mkU (M Mi : Matrix (Fin 5) (Fin 5) F16c) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hu : (M.map (· ^ (2 ^ 2)))ᵀ * M = 1) (hd : M.det = 1) : U :=
  ⟨CFSG.Adapters.RankTwoModelTransports.glCongr eK ⟨M, Mi, h1, h2⟩, by
    rw [← CFSG.Adapters.RankTwoModelTransports.glCongr_statedSU eK 5 (2 ^ 2)]
    refine ⟨⟨M, Mi, h1, h2⟩, ?_, rfl⟩
    unfold CFSG.Open.StatedSU
    exact Subgroup.subset_closure ⟨hd, hu⟩⟩

theorem toM_mkU (M Mi : Matrix (Fin 5) (Fin 5) F16c) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hu : (M.map (· ^ (2 ^ 2)))ᵀ * M = 1) (hd : M.det = 1) :
    toM (mkU M Mi h1 h2 hu hd) = M := by
  show (M.map eK).map eK.symm = M
  rw [Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id M]
  congr 1
  funext c
  exact eK.symm_apply_apply c

noncomputable def g1U : U := mkU u4G1 u4G1i u4G1_mul u4G1_mul' u4G1_unitary det_u4G1

noncomputable def g2U : U := mkU u4G2 u4G2i u4G2_mul u4G2_mul' u4G2_unitary det_u4G2

noncomputable def rU : U := mkU u4R u4Ri u4R_mul u4R_mul' u4R_unitary det_u4R

theorem toM_g1 : toM g1U = u4G1 := toM_mkU _ _ _ _ _ _
theorem toM_g2 : toM g2U = u4G2 := toM_mkU _ _ _ _ _ _
theorem toM_r : toM rU = u4R := toM_mkU _ _ _ _ _ _

theorem g1U_pow : g1U ^ 3 = 1 := toM_injective (by rw [map_pow, toM_g1, u4G1_pow, map_one])
theorem g2U_pow : g2U ^ 3 = 1 := toM_injective (by rw [map_pow, toM_g2, u4G2_pow, map_one])
theorem g12U : g1U * g2U = g2U * g1U :=
  toM_injective (by rw [map_mul, map_mul, toM_g1, toM_g2, u4G12])
theorem g1U_ne : g1U ≠ 1 := fun h => u4G1_ne (by rw [← toM_g1, h, map_one])
theorem g2U_ne : g2U ≠ 1 := fun h => u4G2_ne (by rw [← toM_g2, h, map_one])
theorem g2U_ne_g1U : g2U ≠ g1U := fun h => u4G2_ne_G1 (by rw [← toM_g1, ← toM_g2, h])
theorem g2U_ne_g1U_inv : g2U ≠ g1U⁻¹ := fun h =>
  u4G2_ne_G1i (by rw [← toM_inv_of toM_g1 u4G1_mul, ← toM_g2, h])

theorem rU_g1 : rU * g1U * rU⁻¹ = g2U ^ 2 :=
  toM_injective (by rw [map_mul, map_mul, toM_inv_of toM_r u4R_mul, toM_r, toM_g1, map_pow, toM_g2,
    u4R_G1])

theorem rU_g2 : rU * g2U * rU⁻¹ = g1U :=
  toM_injective (by rw [map_mul, map_mul, toM_inv_of toM_r u4R_mul, toM_r, toM_g1, toM_g2, u4R_G2])

@[expose] noncomputable def E0 : Subgroup U := Subgroup.zpowers g1U ⊔ Subgroup.zpowers g2U

theorem e9_E0 : CFSG.Assembly.IsElemAbelian 3 E0 ∧ Nat.card E0 = 9 :=
  e9_of_commute g1U_pow g1U_ne g2U_pow g12U
    (not_mem_zpowers_of_ne g1U_pow g2U_ne g2U_ne_g1U g2U_ne_g1U_inv)

theorem mem_E0 {x : U} (hx : x ∈ E0) :
    ∃ i j : ℕ, i < 3 ∧ j < 3 ∧ x = g1U ^ i * g2U ^ j := by
  have hc : ∀ u ∈ Subgroup.zpowers g1U, ∀ v ∈ Subgroup.zpowers g2U, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact ((show Commute g1U g2U from g12U).zpow_zpow i j).eq
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hc).2
  have hx' : x ∈ ((Subgroup.zpowers g1U ⊔ Subgroup.zpowers g2U : Subgroup _) : Set _) := hx
  rw [hset] at hx'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hx'
  have hpow : ∀ (c : U), c ^ 3 = 1 → ∀ w ∈ Subgroup.zpowers c,
      ∃ k : ℕ, k < 3 ∧ w = c ^ k := by
    intro c hc3 w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    refine ⟨(k % 3).toNat, by omega, ?_⟩
    have h1 : c ^ k = c ^ (k % 3) := zpow_eq_zpow_emod' k hc3
    rw [h1, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))]
  obtain ⟨i, hi, rfl⟩ := hpow g1U g1U_pow u hu
  obtain ⟨j, hj, rfl⟩ := hpow g2U g2U_pow v hv
  exact ⟨i, j, hi, hj, rfl⟩

theorem rU_mem_normalizer : rU ∈ Subgroup.normalizer (E0 : Set U) := by
  refine mem_normalizer_of_map_le ?_
  rw [E0, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  refine sup_le ?_ ?_ <;> rw [Subgroup.zpowers_le]
  · show rU * g1U * rU⁻¹ ∈ Subgroup.zpowers g1U ⊔ Subgroup.zpowers g2U
    rw [rU_g1]
    exact Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers g2U) 2)
  · show rU * g2U * rU⁻¹ ∈ Subgroup.zpowers g1U ⊔ Subgroup.zpowers g2U
    rw [rU_g2]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers g1U)

theorem rU_not_mem (i j : ℕ) (h1 : u4R * (u4G1 ^ i * u4G2 ^ j) * u4Ri ≠ 1)
    (h2 : u4R * (u4G1 ^ i * u4G2 ^ j) * u4Ri ≠ u4G1 ^ i * u4G2 ^ j)
    (h3 : u4R * (u4G1 ^ i * u4G2 ^ j) * u4Ri ≠ (u4G1 ^ i * u4G2 ^ j) ^ 2) :
    rU ∉ Subgroup.normalizer (Subgroup.zpowers (g1U ^ i * g2U ^ j) : Set U) := by
  have ht : toM (g1U ^ i * g2U ^ j) = u4G1 ^ i * u4G2 ^ j := by
    rw [map_mul, map_pow, map_pow, toM_g1, toM_g2]
  have hc : toM (rU * (g1U ^ i * g2U ^ j) * rU⁻¹) = u4R * (u4G1 ^ i * u4G2 ^ j) * u4Ri := by
    rw [map_mul, map_mul, ht, toM_r, toM_inv_of toM_r u4R_mul]
  have hmem : g1U ^ i * g2U ^ j ∈ E0 :=
    mul_mem (Subgroup.mem_sup_left (pow_mem (Subgroup.mem_zpowers g1U) i))
      (Subgroup.mem_sup_right (pow_mem (Subgroup.mem_zpowers g2U) j))
  have ht3 : (g1U ^ i * g2U ^ j) ^ 3 = 1 := e9_E0.1.2 _ hmem
  have hti : (g1U ^ i * g2U ^ j)⁻¹ = (g1U ^ i * g2U ^ j) ^ 2 :=
    inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact ht3)
  refine not_mem_normalizer_of_conj (not_mem_zpowers_of_ne ht3 ?_ ?_ ?_)
  · intro h
    exact h1 (by rw [← hc, h, map_one])
  · intro h
    exact h2 (by rw [← hc, h, ht])
  · intro h
    exact h3 (by rw [← hc, h, hti, map_pow, ht])

theorem su54_move (s : U) (hs : s ∈ E0) (hs1 : s ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (E0 : Set U),
      n ∉ Subgroup.normalizer (Subgroup.zpowers s : Set U) := by
  obtain ⟨i, j, hi, hj, rfl⟩ := mem_E0 hs
  interval_cases i <;> interval_cases j
  · exact absurd (by simp) hs1
  all_goals exact ⟨rU, rU_mem_normalizer,
    rU_not_mem _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

theorem card_U : Nat.card U = 267219763200000 := by
  have hc := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int
    (CFSG.RankThree.PartOne.U5K.u5FieldData 2 (by norm_num)) (n := 5) (by norm_num)
  have hp : ∏ i ∈ Finset.Icc 2 5, (((2 ^ 2 : ℕ) : ℤ) ^ i - (-1) ^ i) = 254840625 := by decide
  rw [hp] at hc
  norm_num at hc
  exact_mod_cast hc

theorem factorization_card_U : (Nat.card U).factorization 3 = 2 := by
  rw [card_U, show (267219763200000 : ℕ) = 3 ^ 2 * 29691084800000 by norm_num]
  exact Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)

theorem e9Move_U : E9Move U :=
  e9Move_of_sylow factorization_card_U e9_E0.2 su54_move

noncomputable abbrev ZU : Subgroup U :=
  (CFSG.Open.StatedScalars (Fin 5) K16).subgroupOf (CFSG.Open.StatedSU 5 (2 ^ 2) K16)

noncomputable def projEquiv : projSU 5 2 2 ≃* U ⧸ ZU :=
  CFSG.PGLModel.projSUEquivStatedProj 5 2 2

theorem card_projSU : Nat.card (projSU 5 2 2) = 53443952640000 :=
  Item434SmallTwoOther.U54.card_U54.trans (by norm_num)

theorem card_ZU : Nat.card ZU = 5 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ZU
  rw [card_U, ← Nat.card_congr projEquiv.toEquiv, card_projSU] at h
  omega

theorem e9Move_projSU54 : E9Move (projSU 5 2 2) :=
  (e9Move_quotient ZU (by rw [card_ZU]; norm_num) e9Move_U).of_mulEquiv projEquiv

theorem rankTwo_projSU54 : RankTwoData (projSU 5 2 2) := by
  haveI : Finite (projSU 5 2 2) := Nat.finite_of_card_ne_zero (by rw [card_projSU]; norm_num)
  refine ⟨cubeInner_of_not_three_dvd_card_outer outU54_holds, fun E hE => ?_, ?_⟩
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hp : IsPGroup 3 E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hE.2 _ g.2)⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hd : 3 ^ k ∣ Nat.card (projSU 5 2 2) := hk ▸ Subgroup.card_subgroup_dvd_card E
    rw [hk]
    have : k ≤ 2 := by
      by_contra h
      push Not at h
      have h27 : 3 ^ 3 ∣ Nat.card (projSU 5 2 2) := (Nat.pow_dvd_pow 3 h).trans hd
      rw [card_projSU] at h27
      norm_num at h27
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) this
      _ = 9 := by norm_num
  · obtain ⟨hE, hE9⟩ := e9_map_mk ZU (by rw [card_ZU]; norm_num) e9_E0.1 e9_E0.2
    refine ⟨(E0.map (QuotientGroup.mk' ZU)).map projEquiv.symm.toMonoidHom,
      isElemAbelian_map _ hE, ?_⟩
    rw [Subgroup.card_map_of_injective projEquiv.symm.injective, hE9]

theorem u54_orderChecks :
    (∀ q, 2 ≤ q → q ^ 3 ∣ 53443952640000 →
      53443952640000 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))) ∧
    (∀ q, 2 ≤ q → q ^ 3 ∣ 53443952640000 →
      53443952640000 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))) :=
  orderChecks_of_bound (B := 60) (by norm_num) (by decide +kernel)

end SU54

open SU54

section Row



theorem rowOf427_su54
    : RowOf427 (projSU 5 2 2) := by
  haveI : Finite (projSU 5 2 2) := Nat.finite_of_card_ne_zero (by rw [card_projSU]; norm_num)
  refine rowOf427_of_e9Move ?_ rankTwo_projSU54
    (fun S _ _ ⟨e⟩ => e9Move_projSU54.of_mulEquiv e) (by rw [card_projSU]; norm_num)
  intro L _ _ hSL hL hZ3 ⟨e'⟩
  exact center_eq_bot_of_card hSL hL hZ3 ((Nat.card_congr e'.toEquiv).trans card_projSU)
    u54_orderChecks.1 u54_orderChecks.2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Row

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
