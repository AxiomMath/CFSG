module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem20

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open CFSG.Quasithin.SL2Model
open scoped IsMulCommutative commutatorElement Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem V_eq_conjClosure_ZS (h : Hyp611Nat G T M L V n) : V = conjClosure (ch6ZS T L V) L := by
  have hW : conjClosure (ch6ZS T L V) L ≤ V :=
    CFSG.Quasithin.conjClosure_le fun l hl z hz =>
      (Subgroup.mem_normalizer_iff.mp (h.toHyp611.L_le_normalizer hl) z).mp hz.1
  rcases h.natural.irreducible _ hW (le_normalizer_conjClosure _ L) with h0 | h0
  · exfalso
    apply h.ZS_ne_bot
    rw [eq_bot_iff, ← h0]
    exact le_conjClosure _ _
  · exact h0.symm

theorem isNaturalSL2Module (h : Hyp611Nat G T M L V n) :
    IsNaturalSL2Module n L (pCoreOf 2 (L ⊔ T)) V (ch6ZS T L V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : 2 ≤ n := h.two_le
  set D := h.data with hD
  have := Fintype.ofFinite D.K
  have hcardF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have := Fintype.ofFinite (GaloisField 2 n)
  let e : D.K ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, D.card, hcardF])
  let θ : ↥L →* SL(2, GaloisField 2 n) :=
    (Matrix.SpecialLinearGroup.map e.toRingHom).comp D.rho
  let φ : Multiplicative (Fin 2 → D.K) ≃* Wm (GaloisField 2 n) :=
    AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  have hφ : ∀ x : Multiplicative (Fin 2 → D.K),
      Multiplicative.toAdd (φ x) = e ∘ Multiplicative.toAdd x := fun x => rfl
  let ψ : ↥V ≃* Wm (GaloisField 2 n) := D.E.trans φ
  have hmapinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom) := by
    intro A B hAB
    apply Subtype.ext
    ext i j
    have := congrArg (fun C : SL(2, GaloisField 2 n) =>
      (C : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) i j) hAB
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at this
    exact e.injective this
  have hmapsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom) := by
    intro B
    refine ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom B, ?_⟩
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  refine ⟨D.le_normalizer, θ, ψ, ?_, ?_, ?_, ?_⟩
  ·
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : θ a = 1 ↔ D.rho a = 1 := by
      constructor
      · intro ha
        apply hmapinj
        rw [map_one]
        exact ha
      · intro ha
        show Matrix.SpecialLinearGroup.map e.toRingHom (D.rho a) = 1
        rw [ha, map_one]
    rw [h1, ← MonoidHom.mem_ker, D.mem_ker_rho_iff]
    have hCV := h.toHyp5_0_1.sup_inf_centralizer_eq h.module
    constructor
    · intro hc
      rw [← hCV]
      exact ⟨Subgroup.mem_sup_left a.2, hc⟩
    · intro hc
      rw [← hCV] at hc
      exact hc.2
  ·
    have hsurj : Function.Surjective θ := hmapsurj.comp D.rho_surjective
    rw [MonoidHom.range_eq_top.mpr hsurj]
    rcases card_two_or_exists_sq_ne_one (F := GaloisField 2 n) with h2 | ⟨c, hc0, hc1⟩
    · exfalso
      rw [hcardF] at h2
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    · exact (Matrix.SL2.commutator_eq_top hc0 hc1).symm
  ·
    intro a v
    rw [natAct_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    show Multiplicative.toAdd (φ (D.E (conjAct V ⟨a, D.le_normalizer a.2⟩ v))) =
      θ a • Multiplicative.toAdd (φ (D.E v))
    rw [hφ, hφ, ← D.conj_apply, D.conj_eq_rho a]
    funext i
    simp only [Function.comp_apply]
    rw [show e (((D.rho a : SL(2, D.K)) : Matrix (Fin 2) (Fin 2) D.K).mulVec
        (Multiplicative.toAdd (D.E v)) i) = e.toRingHom
        ((((D.rho a : SL(2, D.K)) : Matrix (Fin 2) (Fin 2) D.K)).mulVec
          (Multiplicative.toAdd (D.E v)) i) from rfl, RingHom.map_mulVec e.toRingHom]
    rfl
  ·
    obtain ⟨w, hw, hle⟩ := h.exists_line
    refine ⟨e ∘ w, fun h0 => hw ?_, fun v => ?_⟩
    · funext i
      have := congrFun h0 i
      simp only [Function.comp_apply, Pi.zero_apply] at this
      rw [Pi.zero_apply]
      exact (map_eq_zero_iff e e.injective).mp this
    · rw [h.mem_ZS_iff_line hw hle v]
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨e c, ?_⟩
        show Multiplicative.toAdd (φ (D.E v)) = e c • (e ∘ w)
        rw [hφ, hc]
        funext i
        simp
      · rintro ⟨c, hc⟩
        refine ⟨e.symm c, ?_⟩
        have hc' : Multiplicative.toAdd (φ (D.E v)) = c • (e ∘ w) := hc
        rw [hφ] at hc'
        funext i
        have := congrFun hc' i
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [Pi.smul_apply, smul_eq_mul]
        apply e.injective
        rw [this, map_mul, RingEquiv.apply_symm_apply]

end Hyp611Nat

namespace Hyp6116

theorem conjClosure_normalizer_eq (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) :
    conjClosure V (Subgroup.normalizer (ch6ZS T L V : Set G)) =
      conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  refine le_antisymm ?_ (conjClosure_mono le_rfl (Subgroup.centralizer_le_normalizer _))
  have hN := (h.toHyp611Nat.normalizer_ZS_eq h432).2
  refine CFSG.Quasithin.conjClosure_le fun x hx v hv => ?_
  have hKN : ch6MV M V ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer
      ((Subgroup.centralizer (ch6ZS T L V : Set G) : Subgroup G) : Set G) :=
    inf_le_right.trans (F7.normalizer_le_normalizer_centralizer _)
  rw [hN, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hKN] at hx
  obtain ⟨i, hi, m, hm, rfl⟩ := hx
  have hmv : m * v * m⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hm.1.2 v).mp hv
  have e : i * m * v * (i * m)⁻¹ = i * (m * v * m⁻¹) * i⁻¹ := by group
  rw [e]
  exact mem_conjClosure hi hmv

theorem conjClosure_not_le_pCoreOf (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) :
    ¬ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ pCoreOf 2 (L ⊔ T) := by
  intro hle
  apply h.lemma_6_1_20_two h432 h6111 h6119
  have hUC : conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
      Subgroup.centralizer (V : Set G) := by
    rw [← h.toHyp611.centralizer_eq] at hle
    exact hle.trans inf_le_right
  have hle' : conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
      Subgroup.centralizer ((conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) :
        Subgroup G) : Set G) := by
    intro u hu
    have hsub : conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
        Subgroup.centralizer ({u} : Set G) := by
      refine CFSG.Quasithin.conjClosure_le fun i hi v hv => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hu' : i⁻¹ * u * i ∈ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
        have := (Subgroup.mem_normalizer_iff.mp
          (le_normalizer_conjClosure V _ (Subgroup.inv_mem _ hi)) u).mp hu
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp (hUC hu') v hv
      calc i * v * i⁻¹ * u = i * (v * (i⁻¹ * u * i)) * i⁻¹ := by group
        _ = i * ((i⁻¹ * u * i) * v) * i⁻¹ := by rw [hc]
        _ = u * (i * v * i⁻¹) := by group
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (hsub hw)
  exact ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle' y.2) x x.2)⟩⟩

theorem almostSpecialL2Hyp (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) :
    AlmostSpecialL2Hyp n V (ch6ZS T L V) L T (Subgroup.normalizer (ch6ZS T L V : Set G)) where
  base := h.toHyp611Nat.almostSpecialHyp
  n_pos := by have := h.two_le; omega
  V_eq := h.toHyp611Nat.V_eq_conjClosure_ZS
  natural := h.toHyp611Nat.isNaturalSL2Module
  U_ne := by
    rw [h.conjClosure_normalizer_eq h432]
    exact h.conjClosure_not_le_pCoreOf h432 h6111 h6119

end Hyp6116

end CFSG.Quasithin.H13
