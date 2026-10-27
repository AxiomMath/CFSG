module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOdd
public import CFSG.GroupTheory.ConjNormalFaithful
public import CFSG.LieType.SeitzGeneration.QuasiHigh2Linear
import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddLinear
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup Matrix CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace LinSeitz

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem coe_ne_smul_one_of_conjAut_ne_one (hn : 3 ≤ n) {A : GL (Fin n) F}
    (hA : conjAut n F A ≠ 1) (r : F) : (A : Matrix (Fin n) (Fin n) F) ≠ r • 1 := by
  intro h
  apply hA
  obtain ⟨u, hu⟩ := exists_scalarGL_of_gl_coe_eq_smul (by omega) h
  exact (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff hn A).2 ⟨u, hu⟩

theorem exists_liftStable_of_four (hF : ringChar F ≠ 2) (hn : 3 ≤ n)
    {E : Subgroup (MulAut (projectiveSL n F))} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hlin : E ≤ linearAutGroup n F) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ LiftStable E W := by
  classical
  have := Fintype.ofFinite F
  have h4' : Nat.card E = 2 ^ 2 := h4
  have hexp : ∀ x ∈ E, x ^ 2 = 1 := hE.2
  obtain ⟨x, hxE, hx1⟩ : ∃ x ∈ E, x ≠ 1 := by
    have hne : E ≠ ⊥ := by rintro h; rw [h, Subgroup.card_bot] at h4; norm_num at h4
    obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨x, hx, fun h => hx1 (Subtype.ext h)⟩
  obtain ⟨y, hyE, hyx⟩ := exists_notMem_zpowers_of_card_sq Nat.prime_two hexp h4' hxE hx1
  have hgen := zpowers_sup_zpowers_eq_of_card_sq Nat.prime_two hexp h4' hxE hx1 hyE hyx
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 (hlin hxE)
  obtain ⟨B, rfl⟩ := mem_linearAutGroup_iff.1 (hlin hyE)
  have hy1 : conjAut n F B ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
  have hxy1 : conjAut n F (A * B) ≠ 1 := by
    rw [map_mul]
    intro h
    apply hyx
    rw [eq_inv_of_mul_eq_one_right h]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
  obtain ⟨a, ha⟩ := exists_scalarGL_pow hn hE hxE
  obtain ⟨b, hb⟩ := exists_scalarGL_pow hn hE hyE
  obtain ⟨u, hu⟩ := exists_scalarGL_comm hn hE hxE hyE
  set X : Matrix (Fin n) (Fin n) F := (A : Matrix (Fin n) (Fin n) F) with hXdef
  set Y : Matrix (Fin n) (Fin n) F := (B : Matrix (Fin n) (Fin n) F) with hYdef
  have hXX : X * X = (a : F) • 1 := by
    rw [← scalarGL_coe_eq_smul, ← ha, pow_two, Units.val_mul]
  have hYY : Y * Y = (b : F) • 1 := by
    rw [← scalarGL_coe_eq_smul, ← hb, pow_two, Units.val_mul]
  have hYX : Y * X = (u : F) • (X * Y) := by
    have := congrArg Units.val hu
    rw [Units.val_mul, Units.val_mul, Units.val_mul, scalarGL_coe_eq_smul, smul_mul_assoc,
      one_mul] at this
    exact this
  have hY0 : Y ≠ 0 := by
    intro h
    have h1 : ((B⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * B = 1 := Units.inv_mul B
    rw [show (B : Matrix (Fin n) (Fin n) F) = Y from rfl, h, Matrix.mul_zero] at h1
    exact zero_ne_one (congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩)
  have huu : (u : F) * u = 1 := by
    have e1 : Y * (X * X) = (a : F) • Y := by rw [hXX, mul_smul_comm, mul_one]
    have e2 : Y * (X * X) = ((u : F) * u * a) • Y := by
      calc Y * (X * X) = (Y * X) * X := (Matrix.mul_assoc _ _ _).symm
        _ = (u : F) • (X * (Y * X)) := by rw [hYX, smul_mul_assoc, Matrix.mul_assoc, hYX]
        _ = ((u : F) * u) • ((X * X) * Y) := by
          rw [hYX, mul_smul_comm, smul_smul, ← Matrix.mul_assoc]
        _ = ((u : F) * u * a) • Y := by rw [hXX, smul_mul_assoc, one_mul, smul_smul]
    have h3 : ((u : F) * u * a - a) • Y = 0 := by rw [sub_smul, ← e2, ← e1, sub_self]
    have h4 : (u : F) * u * a - a = 0 := (smul_eq_zero.mp h3).resolve_right hY0
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    have : ((u : F) * u - 1) * a = 0 := by rw [sub_mul, one_mul]; exact h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right ha0)
  have hXY : X * Y = (u : F) • (Y * X) := by
    rw [hYX, smul_smul, huu, one_smul]
  have hc : (u : F) = 1 ∨ (u : F) = -1 := mul_self_eq_one_iff.mp huu
  have hXYm : X * Y = ((A * B : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
    (Units.val_mul _ _).symm
  obtain ⟨W, hW0, hWt, hWX, hWY⟩ := exists_invariant_of_pair hF hn hXX hYY hXY hc a.ne_zero
    b.ne_zero (coe_ne_smul_one_of_conjAut_ne_one hn hx1)
    (coe_ne_smul_one_of_conjAut_ne_one hn hy1)
    (fun r => hXYm ▸ coe_ne_smul_one_of_conjAut_ne_one hn hxy1 r)
  refine ⟨W, hW0, hWt, fun C hC w hw => ?_⟩
  let S : Subgroup (GL (Fin n) F) :=
    { carrier := {A | (∀ w ∈ W, (A : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) ∧
        ∀ w ∈ W, ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W}
      one_mem' := ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
      mul_mem' := by
        rintro A B ⟨hA1, hA2⟩ ⟨hB1, hB2⟩
        refine ⟨fun w hw => ?_, fun w hw => ?_⟩
        · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
          exact hA1 _ (hB1 w hw)
        · rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
          exact hB2 _ (hA2 w hw)
      inv_mem' := by
        rintro A ⟨hA1, hA2⟩
        exact ⟨hA2, by simpa using hA1⟩ }
  have hmemS : ∀ D : GL (Fin n) F, (∀ w ∈ W, (D : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) →
      (∀ w ∈ W, ((D⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W) → D ∈ S :=
    fun D h1 h2 => ⟨h1, h2⟩
  have hCK : C ∈ S := by
    refine mem_of_conjAut_mem_of_sup_eq hn hgen (fun c => hmemS _ (fun w hw => ?_) fun w hw => ?_)
      (hmemS _ hWX (inv_mulVec_mem_of_pow_scalar two_pos ha hWX))
      (hmemS _ hWY (inv_mulVec_mem_of_pow_scalar two_pos hb hWY)) rfl rfl hC
    · rw [scalarGL_coe_eq_smul, smul_mulVec, one_mulVec]
      exact W.smul_mem _ hw
    · rw [← map_inv, scalarGL_coe_eq_smul, smul_mulVec, one_mulVec]
      exact W.smul_mem _ hw
  exact hCK.1 w hw

theorem seitzHyperGamma_two_of_linear {K : Type*} [Group K] [Finite K]
    (hperf : commutator K = ⊤) (hF : ringChar F ≠ 2) (hn : 3 ≤ n)
    (θ : K ⧸ Subgroup.center K ≃* projectiveSL n F) {E : Subgroup (MulAut K)}
    (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hlin : E.map (QuasiHigh2.modelAut θ) ≤ linearAutGroup n F) : seitzHyperGamma 2 E = ⊤ := by
  have hinj := QuasiHigh2.modelAut_injective hperf θ
  have hE' : IsElemAbelian 2 (E.map (QuasiHigh2.modelAut θ)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 2 hE _
  have h4' : Nat.card (E.map (QuasiHigh2.modelAut θ)) = 4 := by
    rw [Subgroup.card_map_of_injective hinj, h4]
  have hE1 : E ≠ ⊥ := by rintro rfl; rw [Subgroup.card_bot] at h4; norm_num at h4
  have h2F : ((2 : ℕ) : F) ≠ 0 := by rw [Nat.cast_ofNat]; exact Ring.two_ne_zero hF
  obtain ⟨W, hW0, hWt, hWE⟩ := exists_liftStable_of_four hF hn hE' h4' hlin
  exact QuasiHigh.seitzHyperGamma_eq_top_of_diagReducible hperf Nat.prime_two hE hE1
    (QuasiHigh2.diagReducible_of_liftStable hn Nat.prime_two h2F θ hE' hlin hW0 hWt hWE)

end LinSeitz

theorem iSup_centralizer_eq_of_seitzHyperGamma {G : Type*} [Group G] {L E : Subgroup G}
    [L.Normal] (hC : centralizer (L : Set G) = ⊥) (h4 : Nat.card E = 4)
    (h : seitzHyperGamma 2 (E.map (MulAut.conjNormal : G →* MulAut ↥L)) = ⊤) :
    (⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G)) = L := by
  set c : G →* MulAut ↥L := MulAut.conjNormal with hc
  have h4' : Nat.card (E.map c) = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.conjNormal_injective_of_centralizer_eq_bot hC), h4]
  refine le_antisymm (iSup₂_le fun x _ => iSup_le fun _ => inf_le_left) ?_
  intro y hy
  have hy' : (⟨y, hy⟩ : ↥L) ∈ seitzHyperGamma 2 (E.map c) := h ▸ mem_top _
  have hle : seitzHyperGamma 2 (E.map c) ≤
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G)).comap L.subtype := by
    refine iSup₂_le fun F hF => ?_
    have hF0 : F ≠ ⊥ := by
      rintro rfl
      have := hF.2
      rw [Subgroup.relIndex_bot_left, h4'] at this
      norm_num at this
    obtain ⟨⟨φ, hφF⟩, hφ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF0
    obtain ⟨e, he, rfl⟩ := hF.1 hφF
    have he1 : e ≠ 1 := by
      rintro rfl
      exact hφ1 (Subtype.ext (map_one c))
    intro z hz
    rw [mem_comap]
    have hsub : L ⊓ centralizer ({e} : Set G) ≤
        ⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G) :=
      le_iSup₂_of_le e he (le_iSup_of_le he1 le_rfl)
    refine hsub ⟨z.2, ?_⟩
    show (z : G) ∈ centralizer ({e} : Set G)
    have h2 := congrArg Subtype.val ((mem_fixedPoints.mp hz) (c e) hφF)
    rw [hc, MulAut.conjNormal_apply] at h2
    change e * z * e⁻¹ = z at h2
    rw [mem_centralizer_singleton_iff]
    calc (z : G) * e = e * z * e⁻¹ * e := by rw [h2]
      _ = e * z := by group
  exact hle hy'

@[expose] def SeitzFourPSLNonlinear : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Subgroup.center K = ⊥ → commutator K = ⊤ →
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 3 ≤ n → ringChar F ≠ 2 →
    ∀ (θ : K ⧸ Subgroup.center K ≃* projectiveSL n F) (E : Subgroup (MulAut K)),
      IsElemAbelian 2 E → Nat.card E = 4 →
      ¬ E.map (QuasiHigh2.modelAut θ) ≤ linearAutGroup n F → seitzHyperGamma 2 E = ⊤

theorem seitzFour_psl_of_nonlinear (hNL : SeitzFourPSLNonlinear) :
    SeitzFour fun X _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSL n p f := by
  intro G _ _ L E hLn hLs hnab ⟨n, p, f, hn, hp2, hm⟩ hC hE h4 _
  classical
  have hm' : CFSG.Models.LieModel ↥L .PSL n p f := hm
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ :=
    CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) hm'
  let ψ : ↥L ≃* projectiveSL n K :=
    (eS.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  have hKchar : ringChar K ≠ 2 := by
    have := Fintype.ofFinite K
    intro h2
    have hev := FiniteField.even_card_of_char_two h2
    rw [← Nat.card_eq_fintype_card, hK] at hev
    obtain ⟨k, hk⟩ : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    omega
  have hncomm : ¬ IsMulCommutative ↥L := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (h.is_comm.comm a b)
  have hZ : Subgroup.center ↥L = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hncomm
  have hperf : commutator ↥L = ⊤ :=
    (TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hncomm).commutator_eq_top
  let θ : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL n K :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans ψ
  have := hLn
  apply iSup_centralizer_eq_of_seitzHyperGamma hC h4
  have hE' : IsElemAbelian 2 (E.map (MulAut.conjNormal : G →* MulAut ↥L)) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 2 hE _
  have h4' : Nat.card (E.map (MulAut.conjNormal : G →* MulAut ↥L)) = 4 := by
    rw [Subgroup.card_map_of_injective (Subgroup.conjNormal_injective_of_centralizer_eq_bot hC), h4]
  by_cases hlin : (E.map (MulAut.conjNormal : G →* MulAut ↥L)).map (QuasiHigh2.modelAut θ) ≤
      linearAutGroup n K
  · exact LinSeitz.seitzHyperGamma_two_of_linear hperf hKchar hn θ hE' h4' hlin
  · exact hNL ↥L hZ hperf K n hn hKchar θ _ hE' h4' hlin

end CFSG.LocalAnalysis.WeakClosure81
