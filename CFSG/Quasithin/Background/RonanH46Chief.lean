module

public import CFSG.Quasithin.Background.RonanH46ZLev
public import CFSG.Quasithin.Background.RonanH46ZQ
public import CFSG.Quasithin.Background.RonanH46Irr

public section

namespace CFSG.Quasithin.RonanH46

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix
  CFSG.Quasithin.RonanH44
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem chief_bot_V1z (hK : Nat.card K = (2 ^ 1) ^ 2) :
    IsChiefFactorUnderR (actsOnModuleR (LZ hK)) ⊥ (V1z 1 K) := by
  have hcard : Nat.card ↥(V1z 1 K) = 2 := card_V1z hK
  unfold IsChiefFactorUnderR
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine lt_of_le_of_ne bot_le ?_
    intro h
    have h1 : Nat.card ↥(V1z 1 K) = 1 := by
      rw [← h, Subgroup.card_bot]
    omega
  · rintro f ⟨y, _, rfl⟩ u hu
    rw [Subgroup.mem_bot] at hu ⊢
    subst hu
    exact map_one y
  · rintro f ⟨y, hy, rfl⟩ u hu
    show y u ∈ V1z 1 K
    rw [LZ_eq_of_V1z hK hy hu]
    exact hu
  · intro W _ hWV _
    have hdvd : Nat.card ↥W ∣ Nat.card ↥(V1z 1 K) := Subgroup.card_dvd_of_le hWV
    rw [hcard] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact Or.inl (Subgroup.eq_bot_of_card_eq W h1)
    · have hfin : Finite ↥(V1z 1 K) :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      exact Or.inr (Subgroup.eq_of_le_of_card_ge hWV (by omega))

theorem chief_V1z_V2z (hK : Nat.card K = (2 ^ 1) ^ 2) :
    IsChiefFactorUnderR (actsOnModuleR (LZ hK)) (V1z 1 K) (V2z 1 K) := by
  have h4 : 4 ≤ Nat.card K := by simp [hK]
  have hinvV1 : IsActsInvR (actsOnModuleR (LZ hK)) (V1z 1 K) := by
    rintro f ⟨y, hy, rfl⟩ u hu
    show y u ∈ V1z 1 K
    rw [LZ_eq_of_V1z hK hy hu]
    exact hu
  have hinvV2 : IsActsInvR (actsOnModuleR (LZ hK)) (V2z 1 K) := by
    rintro f ⟨y, hy, rfl⟩ u hu
    exact LZ_mem_V2z hK hy hu
  unfold IsChiefFactorUnderR
  refine ⟨?_, hinvV1, hinvV2, ?_⟩
  · refine lt_of_le_of_ne V1z_le_V2z ?_
    intro h
    obtain ⟨X, hX⟩ := rowV2_surjective hK (Multiplicative.ofAdd ![1, 0])
    have hXV1 : (X : HMod 1 K) ∈ V1z 1 K := by
      rw [h]
      exact X.2
    have h1 : rowV2 1 K X = 1 := rowV2_eq_one_iff.mpr hXV1
    rw [hX] at h1
    have h2 := congrFun (ofAdd_eq_one.mp h1) 0
    simp at h2
  · intro W hVW hWV2 hWinv
    obtain ⟨S, hSmem⟩ : ∃ S : AddSubgroup (Fin 2 → K), ∀ r : Fin 2 → K, r ∈ S ↔
        ∃ X : HMod 1 K, X ∈ W ∧ ∃ hX : X ∈ V2z 1 K,
          rowV2 1 K ⟨X, hX⟩ = Multiplicative.ofAdd r := by
      refine ⟨{ carrier := {r | ∃ X : HMod 1 K, X ∈ W ∧ ∃ hX : X ∈ V2z 1 K,
                  rowV2 1 K ⟨X, hX⟩ = Multiplicative.ofAdd r},
                zero_mem' := ?zero, add_mem' := ?add, neg_mem' := ?neg }, fun r => Iff.rfl⟩
      case zero =>
        refine ⟨1, W.one_mem, (V2z 1 K).one_mem, ?_⟩
        rw [ofAdd_zero]
        exact map_one (rowV2 1 K)
      case add =>
        rintro a b ⟨X, hXW, hXV, hXa⟩ ⟨Y, hYW, hYV, hYb⟩
        refine ⟨X * Y, W.mul_mem hXW hYW, (V2z 1 K).mul_mem hXV hYV, ?_⟩
        rw [ofAdd_add, ← hXa, ← hYb]
        exact map_mul (rowV2 1 K) ⟨X, hXV⟩ ⟨Y, hYV⟩
      case neg =>
        rintro a ⟨X, hXW, hXV, hXa⟩
        refine ⟨X⁻¹, W.inv_mem hXW, (V2z 1 K).inv_mem hXV, ?_⟩
        rw [ofAdd_neg, ← hXa]
        exact map_inv (rowV2 1 K) ⟨X, hXV⟩
    have hSinv : ∀ (A : SL(2, K)) (v : Fin 2 → K), v ∈ S →
        (A : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈ S := by
      intro A v hv
      obtain ⟨X, hXW, hXV, hXv⟩ := (hSmem v).mp hv
      obtain ⟨y, hy, hrow⟩ := exists_LZ_rowV2 hK h4 A
      have hyX : y X ∈ W := hWinv (fun v => y v) ⟨y, hy, rfl⟩ X hXW
      refine (hSmem _).mpr ⟨y X, hyX, LZ_mem_V2z hK hy hXV, ?_⟩
      have h := hrow ⟨X, hXV⟩
      rw [hXv, toAdd_ofAdd] at h
      exact h
    rcases irr_natural hSinv with hSbot | hStop
    · refine Or.inl (le_antisymm ?_ hVW)
      intro X hXW
      have hXV : X ∈ V2z 1 K := hWV2 hXW
      have h1 : Multiplicative.toAdd (rowV2 1 K ⟨X, hXV⟩) ∈ S :=
        (hSmem _).mpr ⟨X, hXW, hXV, by rw [ofAdd_toAdd]⟩
      rw [hSbot, AddSubgroup.mem_bot] at h1
      have h2 : rowV2 1 K ⟨X, hXV⟩ = 1 := by
        have h3 := congrArg Multiplicative.ofAdd h1
        rwa [ofAdd_toAdd, ofAdd_zero] at h3
      exact rowV2_eq_one_iff.mp h2
    · refine Or.inr (le_antisymm hWV2 ?_)
      intro Y hYV2
      have hr : Multiplicative.toAdd (rowV2 1 K ⟨Y, hYV2⟩) ∈ S := by
        rw [hStop]
        exact AddSubgroup.mem_top _
      obtain ⟨X, hXW, hXV, hXr⟩ := (hSmem _).mp hr
      have hXr' : rowV2 1 K ⟨X, hXV⟩ = rowV2 1 K ⟨Y, hYV2⟩ := by
        rw [hXr, ofAdd_toAdd]
      have hZ : rowV2 1 K (⟨Y, hYV2⟩ * (⟨X, hXV⟩ : ↥(V2z 1 K))⁻¹) = 1 := by
        rw [map_mul, map_inv, hXr', mul_inv_cancel]
      have hZV1 : Y * X⁻¹ ∈ V1z 1 K := rowV2_eq_one_iff.mp hZ
      have hYW : Y * X⁻¹ * X ∈ W := W.mul_mem (hVW hZV1) hXW
      rwa [inv_mul_cancel_right] at hYW

private theorem natHomR_two_apply (A : SL(2, K)) (C : GL (Fin 2) K)
    (hAC : (A : Matrix (Fin 2) (Fin 2) K) = (C : Matrix (Fin 2) (Fin 2) K))
    (v : Multiplicative (Fin 2 → K)) :
    natHomR 2 K C v =
      Multiplicative.ofAdd ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ Multiplicative.toAdd v) := by
  apply Multiplicative.toAdd.injective
  rw [natHomR_apply, toAdd_ofAdd, hAC]

theorem inducesOn_V2z (hK : Nat.card K = (2 ^ 1) ^ 2) :
    InducesOnR (LZ hK) (V2z 1 K) (V1z 1 K) (Multiplicative (Fin 2 → K))
      (natSubR 2 K (StatedSLR 2 K)) := by
  have h4 : 4 ≤ Nat.card K := by simp [hK]
  unfold InducesOnR natSubR
  refine ⟨V1z_le_V2z, fun g hg u hu => LZ_mem_V2z hK hg hu, fun g hg z hz => ?_,
    rowV2 1 K, rowV2_surjective hK, fun u => rowV2_eq_one_iff, ?_, ?_⟩
  · rw [LZ_eq_of_V1z hK hg hz]
    exact hz
  · intro g hg
    obtain ⟨A, hA⟩ := LZ_rowV2 hK hg
    refine ⟨natHomR 2 K (Matrix.SpecialLinearGroup.toGL A), ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨Matrix.SpecialLinearGroup.toGL A, ?_, rfl⟩
      refine mem_StatedSLR.mpr ?_
      rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
      exact A.2
    · intro u u' huu'
      have hu' : u' = ⟨g u, LZ_mem_V2z hK hg u.2⟩ := Subtype.ext huu'
      subst hu'
      rw [hA u]
      exact (natHomR_two_apply A (Matrix.SpecialLinearGroup.toGL A)
        (Matrix.SpecialLinearGroup.coe_GL_coe_matrix A).symm (rowV2 1 K u)).symm
  · intro γ hγ
    obtain ⟨B, hB, rfl⟩ := Subgroup.mem_map.mp hγ
    obtain ⟨A, hA⟩ : ∃ A : SL(2, K),
        (A : Matrix (Fin 2) (Fin 2) K) = (B : Matrix (Fin 2) (Fin 2) K) :=
      ⟨⟨(B : Matrix (Fin 2) (Fin 2) K), mem_StatedSLR.mp hB⟩, rfl⟩
    obtain ⟨y, hy, hrow⟩ := exists_LZ_rowV2 hK h4 A
    refine ⟨y, hy, ?_⟩
    intro u u' huu'
    have hu' : u' = ⟨y u, LZ_mem_V2z hK hy u.2⟩ := Subtype.ext huu'
    subst hu'
    rw [hrow u]
    exact (natHomR_two_apply A B hA (rowV2 1 K u)).symm

end CFSG.Quasithin.RonanH46
