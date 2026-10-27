module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110Module

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]
variable {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]

theorem bar_preimage_of_le {U : Subgroup G} (hQU : Q ≤ U) (hUM : U ≤ M) :
    ((bar M Q U).comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype = U := by
  ext x
  constructor
  · rintro ⟨m, hm, hmx⟩
    change (QuotientGroup.mk' (Q.subgroupOf M)) m ∈ bar M Q U at hm
    unfold bar at hm
    rw [Subgroup.mem_map] at hm
    obtain ⟨u, hu, hmu⟩ := hm
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hq : ((u : G)⁻¹ * (m : G)) ∈ Q :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hmu)
    have hmU : (m : G) ∈ U := by
      have h : (u : G) * ((u : G)⁻¹ * (m : G)) = (m : G) := by group
      rw [← h]
      exact U.mul_mem huU (hQU hq)
    rw [← hmx]
    exact hmU
  · intro hx
    refine ⟨⟨x, hUM hx⟩, ?_, rfl⟩
    change (QuotientGroup.mk' (Q.subgroupOf M)) ⟨x, hUM hx⟩ ∈ bar M Q U
    unfold bar
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hUM hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩

theorem eq_of_bar_eq {S T : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M)
    (hQT : Q ≤ T) (hTM : T ≤ M) (h : bar M Q S = bar M Q T) : S = T := by
  calc S = ((bar M Q S).comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype :=
        (bar_preimage_of_le hQS hSM).symm
    _ = ((bar M Q T).comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype := by rw [h]
    _ = T := bar_preimage_of_le hQT hTM

theorem Q_le_Lgen (M Q B : Subgroup G) : Q ≤ Lgen M (LB M Q B) := by
  calc Q ≤ LB M Q B := le_sup_left
    _ = conjSubgroup 1 (LB M Q B) := (conjSubgroup_one _).symm
    _ ≤ Lgen M (LB M Q B) :=
        le_iSup₂ (f := fun m (_ : m ∈ M) => conjSubgroup m (LB M Q B)) 1 M.one_mem

variable [Finite G]

theorem Lgen_le_M (hc : Ctx M Q Z B) : Lgen M (LB M Q B) ≤ M := by
  refine iSup₂_le fun m hm => ?_
  calc conjSubgroup m (LB M Q B) ≤ conjSubgroup m M := Subgroup.map_mono hc.LB_le_M
    _ = M := hc.conj_M_eq hm

theorem Lgen_eq_XbarPre_of_le (hc : Ctx M Q Z B)
    (h : Lgen M (LB M Q B) ≤ XbarPre M Q Z B) :
    Lgen M (LB M Q B) = XbarPre M Q Z B := by
  have hbar : bar M Q (Lgen M (LB M Q B)) = bar M Q (XbarPre M Q Z B) := by
    rw [bar_Lgen_eq_Xbar hc h, bar_XbarPre hc]
  refine le_antisymm h ?_
  exact (eq_of_bar_eq (Q_le_Lgen M Q B) (Lgen_le_M hc) (Q_le_XbarPre hc)
    (XbarPre_le_M hc) hbar).ge

theorem caseVICore_of_data {S : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]
    {φ : S →* GL (Fin n) K} (hK : Nat.card K = Nat.card Z)
    (hrange : φ.range = StatedSL n K) (hker : φ.ker = Q.subgroupOf S)
    {V₁ V₂ : Subgroup G} (hZV₁ : Z ≤ V₁) (hV₁Q : V₁ ≤ Q)
    (hZV₂ : Z ≤ V₂) (hV₂Q : V₂ ≤ Q) (hinf : V₁ ⊓ V₂ = Z) (hsup : V₁ ⊔ V₂ = Q)
    (hact₁ : SectionAct (ι := Fin n) K S V₁ Z φ
      (fun g => (g : Matrix (Fin n) (Fin n) K)))
    (hact₂ : SectionAct (ι := Fin n) K S V₂ Z φ
      (fun g => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ))
    (hswap : ∃ x ∈ M, conjSubgroup x V₁ = V₂) :
    CaseVICore M Q Z S n :=
  ⟨K, inferInstance, inferInstance, hK, φ, hrange, hker, V₁, V₂, hZV₁, hV₁Q, hZV₂, hV₂Q,
    hinf, hsup, hact₁, hact₂, hswap⟩

end CFSG.RankThree.GF2n.Stroth80
