module

public import CFSG.RankThree.PartTwo.Sec21.Item21LateProof2119
import CFSG.RankThree.PartTwo.Sec21.Item21Late2ProofFrame
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofJArith

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof

open Matrix CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projImage projSL)
open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits)

variable {G : Type} [Group G] [Finite G]

theorem exists_two_subgroup_invariant {A E U L : Subgroup G} {c : G}
    (hcfg : Config2119 G A E U c L) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ V : Subgroup (lBar L), V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ (a : G) (ha : a ∈ A), ∀ v ∈ V,
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, hAL ha⟩) v ∈ V := by
  obtain ⟨-, ⟨n, hn0, hev, ⟨eL⟩⟩, hC, -, -⟩ := hcfg
  obtain ⟨π, p, f, K, _, hPi, hmod, e, D, hD, hconj, -⟩ := hC
  have hcard := Sec13.card_projImage_slPi_mul_three hPi hmod
  rw [← Nat.card_congr e.toEquiv] at hcard
  obtain ⟨rfl, rfl, hfn⟩ := Sec19.Step1917EqProof.eq_two_of_card hPi.prime hPi.one_le
    (by omega) hmod hcard (Sec19.Step1917EqProof.card_kStar (by omega) (Or.inr ⟨eL⟩))
  subst hfn
  have h2 : (2 : K) = 0 := Item21Late2Proof.two_eq_zero_of_piField hPi
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  obtain ⟨g, -, hdiag, -⟩ := Sec4.isTypeC_conj_std hPi hmod hD
  set R : Subgroup (GL (Fin 3) K) := (Sec4.rootGL K).map (MulAut.conj g).toMonoidHom with hR
  have hRS : R ≤ Sec4.slPi true 3 (2 ^ f) K := by
    rintro _ ⟨M, hM, rfl⟩
    have hMS := Sec4.rootGL_le_slPi (2 ^ f) hM
    rw [Sec4.mem_slPi_true] at hMS ⊢
    change ((g * M * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hMS, mul_one, ← det_mul,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
  set V₀ : Subgroup (projImage (Sec4.slPi true 3 (2 ^ f) K)) :=
    (R.map ProjGenLinGroup.mk).subgroupOf (projImage (Sec4.slPi true 3 (2 ^ f) K)) with hV₀
  have hmemV₀ : ∀ v : projImage (Sec4.slPi true 3 (2 ^ f) K), v ∈ V₀ ↔ ∃ M ∈ Sec4.rootGL K,
      ProjGenLinGroup.mk (g * M * g⁻¹) = (v : ProjGenLinGroup (Fin 3) K) := by
    intro v
    rw [hV₀, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨_, ⟨M, hM, rfl⟩, hv⟩
      exact ⟨M, hM, hv⟩
    · rintro ⟨M, hM, hv⟩
      exact ⟨g * M * g⁻¹, ⟨M, hM, rfl⟩, hv⟩
  have hmemS : ∀ M ∈ Sec4.rootGL K,
      ProjGenLinGroup.mk (g * M * g⁻¹) ∈ projImage (Sec4.slPi true 3 (2 ^ f) K) :=
    fun M hM => ⟨g * M * g⁻¹, hRS ⟨M, hM, rfl⟩, rfl⟩
  refine ⟨V₀.map e.symm.toMonoidHom, ?_, ?_, ?_⟩
  ·
    obtain ⟨⟨M, hM⟩, hM1⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one).mp (Sec4.rootGL_ne_bot (K := K))
    have hM1' : M ≠ 1 := fun h => hM1 (Subtype.ext h)
    obtain ⟨a, ha⟩ := hM
    have ha0 : a ≠ 0 := by
      rintro rfl
      apply hM1'
      exact Units.ext (by rw [ha, transvection_zero, Units.val_one])
    intro hbot
    have hv : (⟨ProjGenLinGroup.mk (g * M * g⁻¹), hmemS M ⟨a, ha⟩⟩ :
        projImage (Sec4.slPi true 3 (2 ^ f) K)) ∈ V₀ :=
      (hmemV₀ _).mpr ⟨M, ⟨a, ha⟩, rfl⟩
    have hv' : e.symm ⟨ProjGenLinGroup.mk (g * M * g⁻¹), hmemS M ⟨a, ha⟩⟩ ∈
        V₀.map e.symm.toMonoidHom := ⟨_, hv, rfl⟩
    rw [hbot, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hv'
    have h1 : ProjGenLinGroup.mk (g * M * g⁻¹) = 1 := congrArg Subtype.val hv'
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h1
    obtain ⟨u, hu⟩ := h1
    have hMu : M = GeneralLinearGroup.scalar (Fin 3) u := by
      have : M = g⁻¹ * (g * M * g⁻¹) * g := by group
      rw [this, ← hu]
      have hc : GeneralLinearGroup.scalar (Fin 3) u ∈ Subgroup.center (GL (Fin 3) K) := by
        rw [GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨u, rfl⟩
      rw [mul_assoc, ← (Subgroup.mem_center_iff.mp hc g), ← mul_assoc, inv_mul_cancel, one_mul]
    have h01 := congrArg (fun N : GL (Fin 3) K => (N : Matrix (Fin 3) (Fin 3) K) 0 1) hMu
    simp only [ha, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
    simp [transvection] at h01
    exact ha0 h01
  ·
    intro v
    obtain ⟨_, ⟨w, hw, rfl⟩⟩ := v
    obtain ⟨M, hM, hMw⟩ := (hmemV₀ w).mp hw
    refine ⟨1, Subtype.ext ?_⟩
    have hM2 : M ^ 2 = 1 := Sec4.rootGL_sq hM
    have hw2 : w ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hMw, ← map_pow]
      have : (g * M * g⁻¹) ^ 2 = 1 := by
        rw [conj_pow, hM2, mul_one, mul_inv_cancel]
      rw [this, map_one, Subgroup.coe_one]
    change (e.symm.toMonoidHom w) ^ 2 ^ 1 = 1
    rw [pow_one, ← map_pow, hw2, map_one]
  ·
    intro x hx v hv
    obtain ⟨y, hyD, hy⟩ := hconj _ (Sec4.mem_autThetaQuot_iff.mpr ⟨x, hAL hx, hx, rfl⟩)
    obtain ⟨l, s, t, -, -, hl⟩ := hdiag y hyD
    obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨M, hM, hMw⟩ := (hmemV₀ w).mp hw
    set τ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hAL hx⟩) with hτ
    set Dg : GL (Fin 3) K := GeneralLinearGroup.scalar (Fin 3) l * diagUnits 1 s t with hDg
    have hDg0 : ∀ i j, i ≠ j → (Dg : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
      intro i j hij
      rw [hDg, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagUnits,
        diagonal_mul_diagonal, diagonal_apply_ne _ hij]
    have hM' : Dg * M * Dg⁻¹ ∈ Sec4.rootGL K := Sec4.conj_mem_rootGL_of_diag hDg0 hM
    refine ⟨e (τ (e.symm.toMonoidHom w)), (hmemV₀ _).mpr ⟨Dg * M * Dg⁻¹, hM', ?_⟩, ?_⟩
    · rw [hy, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, ← hMw, ← map_inv, ← map_mul,
        ← map_mul]
      congr 1
      have hy' : y = g * Dg * g⁻¹ := by rw [← hl]; group
      rw [hy']
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

end CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof
