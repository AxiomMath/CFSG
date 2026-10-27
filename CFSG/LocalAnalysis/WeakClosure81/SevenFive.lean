module

public import CFSG.LocalAnalysis.WeakClosure81.SevenTwoUncond

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def kOrbSub (V H E U : Subgroup G) : Subgroup G :=
  ⨆ k : kSub V H E, conjSubgroup U (k : G)

theorem kSub_le_of_forall_le {V H E : Subgroup G}
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) : kSub V H E ≤ H :=
  iSup_le fun W => iSup_le fun hW => hOmH W hW

theorem commutator_eq_bot_or_exists_conj {V H E U U' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E) :
    ⁅U, U'⁆ = ⊥ ∨ ∃ x ∈ U ⊔ U', U' = conjSubgroup U x := by
  obtain ⟨a, b, hUa, hUb, hN⟩ := nVSub_conj_ne_bot_of_mem_omegaSet hTI hE hU hU'
  rw [← hUa, ← hUb] at hN
  rcases two_conj_eq_or_comm hV hTI (W := U) (W' := U') ⟨a, hUa⟩ ⟨b, hUb⟩ hN with
    hcomm | ⟨x, hx, hx'⟩
  · left
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hcomm u hu v hv).symm
  · exact Or.inr ⟨x, hx, hx'⟩

theorem kOrbSub_conj_eq_self {V H E U : Subgroup G} {k : G} (hk : k ∈ kSub V H E) :
    conjSubgroup (kOrbSub V H E U) k = kOrbSub V H E U := by
  have hmap : conjSubgroup (kOrbSub V H E U) k =
      ⨆ m : kSub V H E, conjSubgroup U ((m : G) * k) := by
    rw [kOrbSub]
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
    exact iSup_congr fun m => CFSG.Quasithin.conjSubgroup_conjSubgroup U (m : G) k
  rw [hmap, kOrbSub]
  exact Equiv.iSup_congr (Equiv.mulRight (⟨k, hk⟩ : kSub V H E)) (fun _ => rfl)

theorem kOrbSub_conjSubgroup {V H E U : Subgroup G} {k : G} (hk : k ∈ kSub V H E) :
    kOrbSub V H E (conjSubgroup U k) = kOrbSub V H E U := by
  have hstep : ∀ m : kSub V H E,
      conjSubgroup (conjSubgroup U k) (m : G) =
        conjSubgroup U (((⟨k, hk⟩ : kSub V H E) * m : kSub V H E) : G) :=
    fun m => CFSG.Quasithin.conjSubgroup_conjSubgroup U k (m : G)
  rw [kOrbSub, kOrbSub]
  trans ⨆ m : kSub V H E, conjSubgroup U (((⟨k, hk⟩ : kSub V H E) * m : kSub V H E) : G)
  · exact iSup_congr hstep
  · exact Equiv.iSup_congr (Equiv.mulLeft (⟨k, hk⟩ : kSub V H E)) (fun _ => rfl)

theorem commutator_conj_eq_bot_of_not_mem_kOrbit {V H E U U' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    (h : ∀ k ∈ kSub V H E, U' ≠ conjSubgroup U k)
    (a b : kSub V H E) :
    ⁅conjSubgroup U (a : G), conjSubgroup U' (b : G)⁆ = ⊥ := by
  have hKle : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hUa : conjSubgroup U (a : G) ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet hEH hEnorm hU (hKle a.2)
  have hU'b : conjSubgroup U' (b : G) ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet hEH hEnorm hU' (hKle b.2)
  rcases commutator_eq_bot_or_exists_conj hV hTI hE hUa hU'b with hbot | ⟨y, hy, hy'⟩
  · exact hbot
  · exfalso
    have hyK : y ∈ kSub V H E := sup_le (le_kSub hUa) (le_kSub hU'b) hy
    have hmem : a * y * (b : G)⁻¹ ∈ kSub V H E :=
      (kSub V H E).mul_mem ((kSub V H E).mul_mem a.2 hyK) ((kSub V H E).inv_mem b.2)
    refine h (a * y * (b : G)⁻¹) hmem ?_
    have h1 : conjSubgroup U ((a : G) * y) = conjSubgroup U' (b : G) := by
      rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup U (a : G) y, hy']
    calc U' = conjSubgroup (conjSubgroup U' (b : G)) (b : G)⁻¹ := by
          rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
            CFSG.Quasithin.conjSubgroup_one]
      _ = conjSubgroup (conjSubgroup U ((a : G) * y)) (b : G)⁻¹ := by rw [← h1]
      _ = conjSubgroup U ((a : G) * y * (b : G)⁻¹) :=
          CFSG.Quasithin.conjSubgroup_conjSubgroup U ((a : G) * y) (b : G)⁻¹

theorem kOrbSub_le_kSub {V H E U : Subgroup G}
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hU : U ∈ omegaSet V H E) :
    kOrbSub V H E U ≤ kSub V H E :=
  iSup_le fun k => le_kSub (conjSubgroup_mem_omegaSet hEH hEnorm hU
    (kSub_le_of_forall_le hOmH k.2))

theorem kOrbSub_subgroupOf_normal {V H E U : Subgroup G}
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) (hU : U ∈ omegaSet V H E) :
    ((kOrbSub V H E U).subgroupOf (kSub V H E)).Normal := by
  have hle := kOrbSub_le_kSub hEH hEnorm hOmH hU
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
  intro k hk
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  exact kOrbSub_conj_eq_self hk

theorem commutator_kOrbSub_eq_bot {V H E U U' : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hU : U ∈ omegaSet V H E) (hU' : U' ∈ omegaSet V H E)
    (h : ∀ k ∈ kSub V H E, U' ≠ conjSubgroup U k) :
    ⁅kOrbSub V H E U, kOrbSub V H E U'⁆ = ⊥ := by
  have hgen : ∀ a b : kSub V H E,
      ⁅conjSubgroup U (a : G), conjSubgroup U' (b : G)⁆ = ⊥ :=
    fun a b => commutator_conj_eq_bot_of_not_mem_kOrbit hV hTI hE hEH hEnorm hOmH hU hU' h a b
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff]
  refine iSup_le fun b => ?_
  rw [Subgroup.le_centralizer_iff]
  refine iSup_le fun a => ?_
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hgen a b)

end CFSG.LocalAnalysis.WeakClosure81
