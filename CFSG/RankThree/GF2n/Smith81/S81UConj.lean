module

public import CFSG.RankThree.GF2n.Smith81.S81BLane
public import CFSG.RankThree.GF2n.Smith81.Sec220Conj

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem s81u_card_map {G' : Type} [Group G'] (e : G ≃* G') (S : Subgroup G) :
    Nat.card ↥(S.map e.toMonoidHom) = Nat.card ↥S :=
  Subgroup.card_map_of_injective e.injective

private def s81u_eqv {G' : Type} [Group G'] (e : G ≃* G') (S : Subgroup G) :
    ↥S ≃* ↥(S.map e.toMonoidHom) :=
  MulEquiv.subgroupMap e S

private theorem s81u_subgroupOf_map {G' : Type} [Group G'] (e : G ≃* G') (S N : Subgroup G) :
    (N.subgroupOf S).map (s81u_eqv e S).toMonoidHom =
      (N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom) := by
  ext ⟨x', hx'⟩
  obtain ⟨x, hx, rfl⟩ := hx'
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, hy, congrArg Subtype.val hyx⟩
  · rintro ⟨y, hy, hyx⟩
    obtain rfl : y = x := e.injective hyx
    exact ⟨⟨y, hx⟩, hy, rfl⟩

private theorem s81u_normal_map {G' : Type} [Group G'] (e : G ≃* G') {S N : Subgroup G}
    (hN : (N.subgroupOf S).Normal) :
    ((N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)).Normal := by
  rw [← s81u_subgroupOf_map e S N]
  exact hN.map _ (s81u_eqv e S).surjective

private def s81u_quotEqv {G' : Type} [Group G'] (e : G ≃* G') (S N : Subgroup G)
    [(N.subgroupOf S).Normal]
    [((N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom)).Normal] :
    ↥S ⧸ N.subgroupOf S ≃*
      ↥(S.map e.toMonoidHom) ⧸ (N.map e.toMonoidHom).subgroupOf (S.map e.toMonoidHom) :=
  QuotientGroup.congr _ _ (s81u_eqv e S) (s81u_subgroupOf_map e S N)

private theorem s81u_bar_map {G' : Type} [Group G'] (e : G ≃* G') (H N S : Subgroup G)
    [(N.subgroupOf H).Normal]
    [((N.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom)).Normal] :
    bar (H.map e.toMonoidHom) (N.map e.toMonoidHom) (S.map e.toMonoidHom) =
      (bar H N S).map (s81u_quotEqv e H N).toMonoidHom := by
  unfold bar
  rw [← s81u_subgroupOf_map e H S, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem s81u_layer_quot_map {G' : Type} [Group G'] (e : G ≃* G') {M Q S : Subgroup G}
    (h : ∃ hN : (Q.subgroupOf M).Normal, haveI := hN
      layer (↥M ⧸ Q.subgroupOf M) = (S.subgroupOf M).map (QuotientGroup.mk' (Q.subgroupOf M))) :
    ∃ hN : ((Q.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom)).Normal, haveI := hN
      layer (↥(M.map e.toMonoidHom) ⧸ (Q.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom)) =
        ((S.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom)).map
          (QuotientGroup.mk' ((Q.map e.toMonoidHom).subgroupOf (M.map e.toMonoidHom))) := by
  obtain ⟨hN, hL⟩ := h
  haveI := hN
  haveI hN' := s81u_normal_map e hN
  refine ⟨hN', ?_⟩
  have h1 := s81u_bar_map e M Q S
  unfold bar at h1
  rw [h1, ← hL, WholeGroup.layer_map_mulEquiv]

theorem CaseE3U.map {G' : Type} [Group G'] (e : G ≃* G') {M Q Z B : Subgroup G}
    (h : CaseE3U M Q Z B) :
    CaseE3U (M.map e.toMonoidHom) (Q.map e.toMonoidHom) (Z.map e.toMonoidHom)
      (B.map e.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold CaseE3U
  rw [LB_map, Lgen_map, s81u_card_map, s81u_card_map]
  refine ⟨h1, s81u_layer_quot_map e h2, ?_⟩
  exact h3.map e isPSUModel_of_mulEquiv

theorem CaseE3U.conj {M Q Z B : Subgroup G} (h : CaseE3U M Q Z B) (y : G) :
    CaseE3U (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) :=
  h.map (MulAut.conj y)

theorem InCaseE3U.conj {M Q Z B : Subgroup G} (h : InCaseE3U M Q Z B) (y : G) :
    InCaseE3U (conjSubgroup y M) (conjSubgroup y Q) (conjSubgroup y Z) (conjSubgroup y B) := by
  unfold InCaseE3U at h ⊢
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨y * t * y⁻¹, ht.conj y, hc.conj y⟩

end CFSG.RankThree.GF2n.Smith81
