module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.lemma_6_3_a_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_4

namespace CFSG
end CFSG
open CFSG

open scoped MatrixGroups Pointwise TensorProduct

/-! # lemma_6_3_a_2 from BG Section 6 -/

public theorem CFSG.lemma_6_3_a_2
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G]
    {H : Subgroup G} [H.Normal] (hHall : ∃ π : Set Nat.Primes, IsHallSubgroup π H)
    {K : Subgroup G} (hCompl : IsCompl H K) (hld : H ≤ derivedSubgroup G) :
    subgroupCentralizerIn H K ≤ ⁅H, H⁆ := by
  classical
  rcases hHall with ⟨π, hHallπ⟩
  have hHK' : H.IsComplement' K := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hCompl.disjoint ?_
    ext g
    constructor
    · rintro ⟨h, hh, k, hk, rfl⟩
      simp
    · intro _
      have hg_top : g ∈ (⊤ : Subgroup G) := by simp
      rw [← hCompl.sup_eq_top] at hg_top
      rcases (Subgroup.mem_sup_of_normal_left (s := H) (t := K) (x := g)).mp hg_top with
        ⟨h, hh, k, hk, rfl⟩
      exact ⟨h, hh, k, hk, rfl⟩
  have hcopHK : Nat.Coprime (Nat.card H) (Nat.card K) := by
    simpa [hHK'.symm.index_eq_card] using hHallπ.card_coprime_index
  let hKnormH : K ≤ Subgroup.normalizer H := Subgroup.le_normalizer_of_normal (H := H)
  let : MulDistribMulAction (↥K) (↥H) :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer (G := G) K H hKnormH
  let X : Subgroup G := ⁅H, H⁆
  have hX_le_H : X ≤ H := Subgroup.commutator_le_left (H₁ := H) (H₂ := H)
  let Xsub : Subgroup H := X.subgroupOf H
  have : Xsub.Normal := by
    dsimp [Xsub, X]
    infer_instance
  have hXsub_eq_comm : Xsub = _root_.commutator H := by
    apply (Subgroup.map_injective H.subtype_injective)
    calc
      Xsub.map H.subtype = X := by
        simpa [Xsub] using
          (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := X) (K := H) hX_le_H)
      _ = (_root_.commutator H).map H.subtype := by
        simpa [X] using (Subgroup.map_subtype_commutator (H := H)).symm
  have hXsub_inv : IsInvariant (↥K) (↥H) Xsub := by
    refine ⟨?_⟩
    intro a x
    constructor
    · intro hx
      have hxX : (x : G) ∈ X := by
        simpa [Xsub, Subgroup.mem_subgroupOf] using hx
      have hsmulX : (((a • x : H) : G)) ∈ X := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hKnormH] using
          (inferInstance : X.Normal).conj_mem (x : G) hxX (a : G)
      simpa [Xsub, Subgroup.mem_subgroupOf] using hsmulX
    · intro hx
      have hxX : (((a • x : H) : G)) ∈ X := by
        simpa [Xsub, Subgroup.mem_subgroupOf] using hx
      have hx' :
          ((((a : K) : G)⁻¹ * (((a : K) • x : H) : G) * (((a : K) : G)⁻¹)⁻¹) ∈ X) := by
        simpa using
          (inferInstance : X.Normal).conj_mem
            ((((a : K) • x : H) : G)) hxX (((a : K) : G)⁻¹)
      simpa [Xsub, Subgroup.mem_subgroupOf,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hKnormH, mul_assoc] using hx'
  let : IsInvariant (↥K) (↥H) Xsub := hXsub_inv
  let : MulAction.QuotientAction (↥K) Xsub :=
    quotientAction_of_isInvariant (A := ↥K) (G := ↥H) Xsub hXsub_inv
  let : MulDistribMulAction (↥K) (↥H ⧸ Xsub) :=
    quotientMulDistribMulAction (A := ↥K) (G := ↥H) Xsub hXsub_inv
  have hfixedH :
      fixedPointSubgroup (↥K) (↥H) = (subgroupCentralizerIn H K).subgroupOf H := by
    simpa using fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn H K hKnormH
  have hfixed_quot :
      fixedPointSubgroup (↥K) (↥H ⧸ Xsub) =
        ((subgroupCentralizerIn H K).subgroupOf H).map (QuotientGroup.mk' Xsub) := by
    calc
      fixedPointSubgroup (↥K) (↥H ⧸ Xsub) =
          (fixedPointSubgroup (↥K) (↥H)).map (QuotientGroup.mk' Xsub) := by
            simpa [Xsub] using
              proposition_1_5_d (G := ↥H) (A := ↥K) (by infer_instance) hcopHK.symm
                (π := ∅) Xsub hXsub_inv
      _ = ((subgroupCentralizerIn H K).subgroupOf H).map (QuotientGroup.mk' Xsub) := by
            rw [hfixedH]
  have hcomm_map :
      (commutatorAction (A := ↥K) (G := ↥H)).map H.subtype = ⁅H, K⁆ := by
    simpa using commutatorAction_subgroup_conj_map_eq_commutator H K hKnormH
  have htop_map : (⊤ : Subgroup H).map H.subtype = H := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp, rfl⟩
  have hcomm_top : commutatorAction (A := ↥K) (G := ↥H) = ⊤ := by
    apply (Subgroup.map_injective H.subtype_injective)
    calc
      (commutatorAction (A := ↥K) (G := ↥H)).map H.subtype = ⁅H, K⁆ := hcomm_map
      _ = H := (lemma_6_3_a_1 (H := H) ⟨π, hHallπ⟩ hCompl hld).symm
      _ = (⊤ : Subgroup H).map H.subtype := htop_map.symm
  have hcommQ_le :
      (commutatorAction (A := ↥K) (G := ↥H)).map (QuotientGroup.mk' Xsub) ≤
        commutatorAction (A := ↥K) (G := ↥H ⧸ Xsub) := by
    classical
    let S : Set H := {x : H | ∃ a : K, ∃ g : H, x = g⁻¹ * (a • g)}
    let T : Set (↥H ⧸ Xsub) := {x : ↥H ⧸ Xsub | ∃ a : K, ∃ g : ↥H ⧸ Xsub, x = g⁻¹ * (a • g)}
    have hS : commutatorAction (A := ↥K) (G := ↥H) = Subgroup.closure S := by
      simpa [S] using (commutatorAction_eq_closure (G := ↥H) (A := ↥K))
    have hT : commutatorAction (A := ↥K) (G := ↥H ⧸ Xsub) = Subgroup.closure T := by
      simpa [T] using (commutatorAction_eq_closure (G := ↥H ⧸ Xsub) (A := ↥K))
    rw [hS, hT]
    have hmap :
        (Subgroup.closure S).map (QuotientGroup.mk' Xsub) =
          Subgroup.closure ((QuotientGroup.mk' Xsub) '' S) := by
      simpa using (MonoidHom.map_closure (f := QuotientGroup.mk' Xsub) S)
    rw [hmap]
    refine (Subgroup.closure_le (K := Subgroup.closure T)).2 ?_
    intro x hx
    rcases hx with ⟨y, hyS, rfl⟩
    rcases hyS with ⟨a, g, rfl⟩
    refine Subgroup.subset_closure ?_
    refine ⟨a, QuotientGroup.mk' Xsub g, ?_⟩
    calc
      QuotientGroup.mk' Xsub (g⁻¹ * (a • g)) =
          (QuotientGroup.mk' Xsub g)⁻¹ * QuotientGroup.mk' Xsub (a • g) := by
            simp
      _ = (QuotientGroup.mk' Xsub g)⁻¹ * (a • (QuotientGroup.mk' Xsub g)) := by
            simp
  have hcommQ_top : commutatorAction (A := ↥K) (G := ↥H ⧸ Xsub) = ⊤ := by
    apply top_unique
    have hmap_top :
        (commutatorAction (A := ↥K) (G := ↥H)).map (QuotientGroup.mk' Xsub) = ⊤ := by
      rw [hcomm_top]
      exact Subgroup.map_top_of_surjective (f := QuotientGroup.mk' Xsub)
        (QuotientGroup.mk'_surjective Xsub)
    simpa [hmap_top] using hcommQ_le
  have hcopQ : Nat.Coprime (Nat.card K) (Nat.card (↥H ⧸ Xsub)) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_quotient_dvd_card (s := Xsub)) hcopHK.symm
  have hQcomm : IsMulCommutative (↥H ⧸ Xsub) := by
    let eQ : (↥H ⧸ Xsub) ≃* (↥H ⧸ _root_.commutator H) :=
      QuotientGroup.quotientMulEquivOfEq hXsub_eq_comm
    refine ⟨⟨?_⟩⟩
    intro a b
    apply eQ.injective
    calc
      eQ (a * b) = eQ a * eQ b := by simp [eQ]
      _ = eQ b * eQ a := by
            exact
              ((Subgroup.Normal.quotient_commutative_iff_commutator_le
                (N := (_root_.commutator H))).mpr le_rfl).is_comm.comm (eQ a) (eQ b)
      _ = eQ (b * a) := by simp [eQ]
  have hcomplQ :
      IsCompl (fixedPointSubgroup (↥K) (↥H ⧸ Xsub))
        (commutatorAction (A := ↥K) (G := ↥H ⧸ Xsub)) := by
    exact proposition_1_6_d (G := ↥H ⧸ Xsub) (A := ↥K) (by infer_instance) hcopQ hQcomm
  have hfixQ_bot : fixedPointSubgroup (↥K) (↥H ⧸ Xsub) = ⊥ := by
    simpa [hcommQ_top] using hcomplQ.inf_eq_bot
  have hmap_bot :
      ((subgroupCentralizerIn H K).subgroupOf H).map (QuotientGroup.mk' Xsub) = ⊥ := by
    simpa [hfixed_quot] using hfixQ_bot
  have hle_sub : ((subgroupCentralizerIn H K).subgroupOf H) ≤ Xsub := by
    simpa [QuotientGroup.ker_mk'] using
      (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' Xsub)
        (H := (subgroupCentralizerIn H K).subgroupOf H)).1 hmap_bot
  intro x hx
  have hx_sub : (⟨x, hx.1⟩ : H) ∈ (subgroupCentralizerIn H K).subgroupOf H := by
    simpa [Subgroup.mem_subgroupOf] using hx
  have hxXsub : (⟨x, hx.1⟩ : H) ∈ Xsub := hle_sub hx_sub
  simpa [X, Xsub, Subgroup.mem_subgroupOf] using hxXsub
