module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2LocB
public import CFSG.Quasithin.EmptyFaithful.S143SC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem tw_conj_mem (h : Ctx T M g A t d x) {s : G} (hs : s ∈ T) :
    ∃ v ∈ VZ T M, s * wOfX d x * s⁻¹ = wOfX d x * v := by
  have hwX := wOfX_mem_Xgen h.c h.hD h.hx
  have hw2 := wOfX_sq h.c h.hD h.hd4 h.hx h.hx3
  have hN := LT_le_normalizer_Xgen h.c h.hD h.hd4 (Subgroup.mem_sup_right hs)
  have hsX : s * wOfX d x * s⁻¹ ∈ Xgen T M := (Subgroup.mem_normalizer_iff.mp hN _).mp hwX
  have hsq : (s * wOfX d x * s⁻¹) * (s * wOfX d x * s⁻¹) = 1 := by
    calc (s * wOfX d x * s⁻¹) * (s * wOfX d x * s⁻¹) = s * (wOfX d x * wOfX d x) * s⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  rcases Xgen_invol h.c h.hD h.hd4 h.hx h.hx3 hsX hsq with hV | ⟨v, hv, hwv⟩
  · exfalso
    by_cases h1 : s * wOfX d x * s⁻¹ = 1
    · obtain ⟨y, hy⟩ := h.hN2
      have hw1 : wOfX d x = 1 := by
        calc wOfX d x = s⁻¹ * (s * wOfX d x * s⁻¹) * s := by group
          _ = 1 := by rw [h1]; group
      rw [hw1] at hy
      have : d * d = 1 := by
        have h2 : y * 1 * y⁻¹ = 1 * (d * d) := hy
        simpa using h2.symm
      exact (dd_facts h.hd4).2 this
    · obtain ⟨u, hu⟩ := exists_conj_of_mem_V_ne_one h.c h.hD h.hd4 h.hx h.hx3 hV h1
      refine h.hN1 (s⁻¹ * u) ?_
      calc (s⁻¹ * u) * (d * d) * (s⁻¹ * u)⁻¹ = s⁻¹ * (u * (d * d) * u⁻¹) * s := by group
        _ = s⁻¹ * (s * wOfX d x * s⁻¹) * s := by rw [hu]
        _ = wOfX d x := by group
  · exact ⟨v, hv, hwv⟩

theorem relIndex_Gw_le (h : Ctx T M g A t d x) : (Gw d x).relIndex T ≤ 4 := by
  classical
  obtain ⟨a, ha, haV, haZ, hza, haa, hxa, hall⟩ := three_cycle_x h.c h.hD h.hd4 h.hx h.hx3
  let v : Fin 4 → G := ![1, d * d, a, (d * d) * a]
  have hvall : ∀ u ∈ VZ T M, ∃ i, v i = u := by
    intro u hu
    rcases hall u hu with h1 | h1 | h1 | h1
    · exact ⟨0, h1.symm⟩
    · exact ⟨1, h1.symm⟩
    · exact ⟨2, h1.symm⟩
    · exact ⟨3, h1.symm⟩
  let S : Subgroup ↥T := (Gw d x).subgroupOf T
  let Φ : ↥T ⧸ S → G :=
    Quotient.lift (fun s : ↥T => (wOfX d x)⁻¹ * ((s : G) * wOfX d x * (s : G)⁻¹))
    (by
      intro s s' hss'
      have h1 : ((s : G)⁻¹ * (s' : G)) ∈ Gw d x := by
        have := QuotientGroup.leftRel_apply.mp hss'
        exact Subgroup.mem_subgroupOf.mp this
      have h2 : wOfX d x * ((s : G)⁻¹ * (s' : G)) = ((s : G)⁻¹ * (s' : G)) * wOfX d x :=
        Subgroup.mem_centralizer_iff.mp h1 (wOfX d x) (Set.mem_singleton _)
      show (wOfX d x)⁻¹ * ((s : G) * wOfX d x * (s : G)⁻¹) =
        (wOfX d x)⁻¹ * ((s' : G) * wOfX d x * (s' : G)⁻¹)
      congr 1
      calc (s : G) * wOfX d x * (s : G)⁻¹
          = (s : G) * (wOfX d x * ((s : G)⁻¹ * (s' : G))) * (s' : G)⁻¹ := by group
        _ = (s : G) * (((s : G)⁻¹ * (s' : G)) * wOfX d x) * (s' : G)⁻¹ := by rw [h2]
        _ = (s' : G) * wOfX d x * (s' : G)⁻¹ := by group)
  have key : ∀ q : ↥T ⧸ S, ∃ i : Fin 4, Φ q = v i := by
    intro q
    induction q using Quotient.inductionOn with
    | h s =>
      obtain ⟨u, hu, hsu⟩ := tw_conj_mem h s.2
      obtain ⟨i, hi⟩ := hvall u hu
      refine ⟨i, ?_⟩
      show (wOfX d x)⁻¹ * ((s : G) * wOfX d x * (s : G)⁻¹) = v i
      rw [hsu, hi]; group
  choose I hI using key
  have hinj : Function.Injective I := by
    intro q q' hqq
    have hΦ : Φ q = Φ q' := by rw [hI q, hI q', hqq]
    induction q using Quotient.inductionOn with
    | h s =>
    induction q' using Quotient.inductionOn with
    | h s' =>
      apply Quotient.sound
      show QuotientGroup.leftRel S s s'
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy; subst hy
      have h3 : (wOfX d x)⁻¹ * ((s : G) * wOfX d x * (s : G)⁻¹) =
          (wOfX d x)⁻¹ * ((s' : G) * wOfX d x * (s' : G)⁻¹) := hΦ
      have h4 := mul_left_cancel h3
      calc wOfX d x * ((s : G)⁻¹ * (s' : G))
          = (s : G)⁻¹ * ((s : G) * wOfX d x * (s : G)⁻¹) * (s' : G) := by group
        _ = (s : G)⁻¹ * ((s' : G) * wOfX d x * (s' : G)⁻¹) * (s' : G) := by rw [h4]
        _ = ((s : G)⁻¹ * (s' : G)) * wOfX d x := by group
  have h4 : Nat.card (↥T ⧸ S) ≤ 4 := by
    have := Nat.card_le_card_of_injective I hinj
    simpa using this
  exact h4

theorem four_le_relIndex_Gw (h : Ctx T M g A t d x) : 4 ≤ (Gw d x).relIndex T := by
  obtain ⟨φ⟩ := h.hR
  have h16 : Nat.card ↥(rOf T M ⊓ Gw d x) = 16 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
    have : Nat.card (Multiplicative (ZMod 4)) = 4 := by
      rw [Nat.card_eq_fintype_card]; decide
    rw [this]
  have hRT : rOf T M ≤ T := rOf_le_T_of_hyp h.c.h1281
  have hmul := Subgroup.relIndex_mul_card (Gw d x) (rOf T M)
  rw [inf_comm, h16, card_rOf h.c] at hmul
  have h4 : (Gw d x).relIndex (rOf T M) = 4 := by omega
  rw [← h4]
  exact Subgroup.relIndex_le_of_le_right hRT Subgroup.index_ne_zero_of_finite

theorem card_Tw_eq (h : Ctx T M g A t d x) : Nat.card ↥(Tw T d x) = 2 ^ 7 := by
  have hrel : (Gw d x).relIndex T = 4 := le_antisymm (relIndex_Gw_le h) (four_le_relIndex_Gw h)
  have hmul := Subgroup.relIndex_mul_card (Gw d x) T
  rw [hrel, inf_comm, card_T h] at hmul
  show Nat.card ↥(T ⊓ Gw d x) = 2 ^ 7
  omega

end InspW2

end S143

end CFSG.Quasithin
