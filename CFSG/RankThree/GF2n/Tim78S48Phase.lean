module

public import CFSG.RankThree.GF2n.Tim78S48PairModel
public import CFSG.RankThree.GF2n.Tim78S48PhaseKern
public import CFSG.RankThree.GF2n.Tim78S48PhaseLines
public import CFSG.RankThree.GF2n.Tim78S48PhaseSz
import CFSG.RankThree.GF2n.Tim78NaturalModule
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G]

theorem map_ne_of_card_lt {Y : Type} [Group Y] [Finite Y] {N S S' : Subgroup Y} [N.Normal]
    (hSS' : Codisjoint S S')
    (hlt : Nat.card (S.map (QuotientGroup.mk' N)) < Nat.card (Y ⧸ N)) :
    S.map (QuotientGroup.mk' N) ≠ S'.map (QuotientGroup.mk' N) := by
  intro h
  have h1 : (S ⊔ S').map (QuotientGroup.mk' N) = S.map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_sup, ← h, sup_idem]
  rw [codisjoint_iff.mp hSS', Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
    at h1
  rw [← h1, Subgroup.card_top] at hlt
  exact lt_irrefl _ hlt

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T) {g : G}
include H

section Cert43

theorem phase1_l2 (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) (C : Core48 Q B T g)
    {f : ℕ} (hf : 2 ≤ f) (hrel : (T ⊓ kernel48 B T g).relIndex T = 2 ^ f)
    [((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)).Normal]
    (e : ↥(T ⊔ conjSubgroup g T) ⧸ (kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T) ≃*
      PSL(2, GaloisField 2 f)) : Phase1 B T g := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf0 : f ≠ 0 := by omega
  have hTK := C.exists_T_not_kernel
  have hTgK := C.exists_Tg_not_kernel
  have hKe := C.phase.1
  have hKp : IsPGroup 2 (kernel48 B T g) := hKe.isPGroup
  have hT₀e : Assembly.IsElemAbelian 2 (T ⊓ kernel48 B T g) := hKe.mono inf_le_right
  have hXK := H.X_le_normalizer_kernel h48
  obtain ⟨x, hxX, hxT, hxB⟩ := C.conj
  have hT2 : IsPGroup 2 T := H.isPGroup_Q.to_le H.T_le_Q
  have hTg2 : IsPGroup 2 (conjSubgroup g T) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hT2
    exact IsPGroup.of_card (n := n) (by rw [card_conjSubgroup, hn])
  have hc : Nat.card ((T.subgroupOf (T ⊔ conjSubgroup g T)).map
      (QuotientGroup.mk' ((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)))) = 2 ^ f :=
    (relIndex_eq_card_map_mk (G := G) (X := T ⊔ conjSubgroup g T) (N := kernel48 B T g)
      (S := T) le_sup_left).symm.trans hrel
  have hc' : Nat.card (((conjSubgroup g T).subgroupOf (T ⊔ conjSubgroup g T)).map
      (QuotientGroup.mk' ((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)))) = 2 ^ f := by
    have h := relIndex_eq_card_map_mk (G := G) (X := T ⊔ conjSubgroup g T)
      (N := kernel48 B T g) (S := conjSubgroup g T) le_sup_right
    rw [← h]
    have e1 : conjSubgroup g T ⊓ kernel48 B T g = conjSubgroup x (T ⊓ kernel48 B T g) := by
      rw [conjSubgroup_inf_eq_inf, ← hxT, conjSubgroup_eq_self_iff.mpr (hXK hxX)]
    calc (conjSubgroup g T ⊓ kernel48 B T g).relIndex (conjSubgroup g T)
        = (conjSubgroup x (T ⊓ kernel48 B T g)).relIndex (conjSubgroup x T) := by
          rw [← e1, ← hxT]
      _ = (T ⊓ kernel48 B T g).relIndex T := relIndex_conjSubgroup x _ _
      _ = 2 ^ f := hrel
  have hne := map_ne_of_card_lt (N := (kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T))
    (Subgroup.codisjoint_subgroupOf_sup T (conjSubgroup g T)) (by
      rw [hc, Nat.card_congr e.toEquiv, Nat.card_congr pslMulEquivSL.toEquiv,
        card_SL_two_galoisField hf0]
      have h4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      have h6 : 16 ≤ (2 ^ f) ^ 2 := by nlinarith
      have h5 : 1 < (2 ^ f) ^ 2 - 1 := by omega
      exact lt_mul_of_one_lt_right (by omega) h5)
  obtain ⟨ε, hεs, hεk, hεu, hεl⟩ := exists_sl2_coords
    ((kernel48 B T g).subgroupOf (T ⊔ conjSubgroup g T)) hf0 e
    (S := T.subgroupOf (T ⊔ conjSubgroup g T))
    (S' := (conjSubgroup g T).subgroupOf (T ⊔ conjSubgroup g T))
    (hT2.comap_subtype) (hTg2.comap_subtype) hc hc' hne
  let D : L2Coords B T g (GaloisField 2 f) := ⟨ε, hεs, hεk, hεu, hεl⟩
  obtain ⟨K₁, hK₁⟩ := exists_torusLift hf0 D hKp
  obtain ⟨hq, hlt, hnat⟩ := H.l2_numerics h48 hP hTK hTgK ⟨x, hxX, hxB⟩ hf D hK₁ hT₀e hrel
  obtain ⟨Θ, N⟩ := (hasNatCoords_iff D).mp hnat
  obtain ⟨hKA, hWA, hA, hcomm, hK₁A⟩ := H.kernel_structure h48 hP C hf D N hK₁ hT₀e hrel hlt
  have h4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK₁card : Nat.card K₁ = Nat.card B - 1 := by
    rw [hK₁.card, GaloisField.card 2 f hf0, hq]
  have hK₁ne : K₁ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot, hq] at hK₁card
    omega
  have hTC : T ⊓ kernel48 B T g =
      T ⊓ Subgroup.centralizer ((B ⊔ conjSubgroup g B : Subgroup G) : Set G) := by
    show T ⊓ ((T ⊔ conjSubgroup g T) ⊓ _) = _
    rw [← inf_assoc, inf_of_le_left (le_sup_left : T ≤ T ⊔ conjSubgroup g T)]
  refine ⟨f, hq, H.induces_natural N, H.partition_W h48 hP hTK N, H.trans_W h48 hP hTK N, hKe,
    hKA, hWA, hA, hcomm, by rw [← hTC, hrel, hq], K₁, hK₁.le_X, ?_, ?_, hK₁.cyclic, hK₁card, hK₁A,
    H.K₁_regular h48 hP hTK N hK₁, H.eq_of_normalized h48 hP hTK hTgK N hK₁ hK₁ne⟩
  · intro k hk
    exact (H.torus_normalizes h48 hP hTK hTgK D (x := ⟨k, hK₁.le_X hk⟩)
      (hK₁.eps_mem ⟨k, hK₁.le_X hk⟩ hk)).1
  · intro k hk
    exact (H.torus_normalizes h48 hP hTK hTgK D (x := ⟨k, hK₁.le_X hk⟩)
      (hK₁.eps_mem ⟨k, hK₁.le_X hk⟩ hk)).2

end Cert43

section Certified

theorem core48 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) : Core48 Q B T g :=
  ⟨H.T_not_cent hCen hU hP, H.Tg_not_cent hCen hU hP, H.exists_conj_Tg hCen hU h48 hP,
    H.T_inf_W hCen hU h48 hP, H.Tg_inf_W hCen hU h48 hP, H.phase1a hCen hU h48 hP⟩

theorem phase1 (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    (h48 : Hyp48 M B T g) (hP : ¬ conjSubgroup g B ≤ P) : Phase1 B T g := by
  have C := H.core48 hCen hU h48 hP
  obtain ⟨hKe, -, -, -, hmod⟩ := C.phase
  rcases hmod with ⟨f, hf, hrel, hN, ⟨e⟩⟩ | ⟨a, ha, hrel, hN, ⟨e⟩⟩ | ⟨m, hm, hm3, hrel, hN, ⟨e⟩⟩
  · haveI := hN
    exact H.phase1_l2 h48 hP C hf hrel e
  · haveI := hN
    exact (H.false_of_sz h48 hP C ha hrel e).elim
  · exact (H.false_of_index_two (le_inf H.B_le_T
      ((le_sup_left : B ≤ B ⊔ conjSubgroup g B).trans (H.W_le_kernel h48))) inf_le_left
      (hKe.mono inf_le_right) hrel).elim

end Certified

end Hyp4

end CFSG.RankThree.GF2n.Tim78
