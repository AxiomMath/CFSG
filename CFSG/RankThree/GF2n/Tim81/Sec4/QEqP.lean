module

public import CFSG.RankThree.GF2n.Tim81.Setting
public import CFSG.RankThree.GF2n.Tim81.ConjugatesInM
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

@[expose] def MinimalInvariant (M V : Subgroup G) : Prop :=
  ∀ U : Subgroup G, U ≤ V → M ≤ Subgroup.normalizer (U : Set G) → U = ⊥ ∨ U = V

namespace RootHyp

private theorem inf_centralizer_inSubgroup_generalizedFitting_le (M : Subgroup G) :
    M ⊓ Subgroup.centralizer (inSubgroup generalizedFitting M : Set G) ≤
      inSubgroup generalizedFitting M := by
  intro x hx
  obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
  have hx' : (⟨x, hxM⟩ : ↥M) ∈
      Subgroup.centralizer (generalizedFitting ↥M : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxC (y : G)
      (Subgroup.mem_map_of_mem M.subtype hy)
  have hxgen : (⟨x, hxM⟩ : ↥M) ∈ generalizedFitting ↥M :=
    centralizer_generalizedFitting_le (G := ↥M) hx'
  exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, hxgen, rfl⟩

private theorem inf_centralizer_pCore_le (h : Hyp M V) :
    M ⊓ Subgroup.centralizer (inSubgroup (pCore 2) M : Set G) ≤
      inSubgroup (pCore 2) M := by
  have hfit : inSubgroup (pCore 2) M = inSubgroup generalizedFitting M := by
    simp only [inSubgroup, h.fitting]
  rw [hfit]
  exact inf_centralizer_inSubgroup_generalizedFitting_le M

private theorem inf_centralizer_pCore_ne_bot (h : Hyp M V) :
    V ⊓ Subgroup.centralizer (inSubgroup (pCore 2) M : Set G) ≠ ⊥ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := inSubgroup (pCore 2) M with hQ
  have hVQ : V ≤ Q := by rw [hQ]; exact h.le_Q
  have hQ2 : IsPGroup 2 Q := by rw [hQ]; exact (inSubgroup_pCore_two M).1
  have hVnorm : Q ≤ Subgroup.normalizer (V : Set G) := by
    rw [hQ]
    exact (inSubgroup_pCore_two M).2.1.trans h.le_normalizer
  haveI : (V.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVQ).mpr hVnorm
  have hVsub_ne : V.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply h.ne_bot
    rw [← Subgroup.map_subgroupOf_eq_of_le hVQ, hbot, Subgroup.map_bot]
  haveI : Group.IsNilpotent ↥Q := hQ2.isNilpotent
  obtain ⟨w, hw1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hVsub_ne)
  intro hbot
  have hwV : (w : G) ∈ V := Subgroup.mem_subgroupOf.mp w.2.1
  have hwC : (w : G) ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2.2 ⟨q, hq⟩)
  have hw_bot : (w : G) ∈ (⊥ : Subgroup G) := by
    rw [← hbot]
    exact Subgroup.mem_inf.mpr ⟨hwV, hwC⟩
  have hwG1 : (w : G) = 1 := Subgroup.mem_bot.mp hw_bot
  have hwQ1 : (w : ↥Q) = 1 := Subtype.ext (by simpa using hwG1)
  exact hw1 (Subtype.ext hwQ1)

private theorem pCore_eq_Pc_of_minimal (h : RootHyp M V)
    (hmin : MinimalInvariant M V) :
    inSubgroup (pCore 2) M = Pc M V := by
  set Q : Subgroup G := inSubgroup (pCore 2) M with hQ
  have hCV_ne : V ⊓ Subgroup.centralizer (Q : Set G) ≠ ⊥ := by
    rw [hQ]
    exact inf_centralizer_pCore_ne_bot h.toHyp
  have hQnorm : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]
    exact (inSubgroup_pCore_two M).2.2
  have hCV_normal : M ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
    intro m hm
    exact mem_normalizer_inf (h.toHyp.le_normalizer hm)
      (mem_normalizer_centralizer (hQ.symm ▸ (inSubgroup_pCore_two M).2.2 hm))
  have hCV_eq : V ⊓ Subgroup.centralizer (Q : Set G) = V :=
    (hmin _ inf_le_left hCV_normal).resolve_left hCV_ne
  have hQ_le_centV : Q ≤ Subgroup.centralizer (V : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvQ : v ∈ Subgroup.centralizer (Q : Set G) := by
      have hv' : v ∈ V ⊓ Subgroup.centralizer (Q : Set G) := by
        rw [hCV_eq]
        exact hv
      exact hv'.2
    exact (Subgroup.mem_centralizer_iff.mp hvQ q hq).symm
  refine le_antisymm ?_ inf_le_left
  intro q hq
  exact Subgroup.mem_inf.mpr ⟨hQ ▸ hq, hQ_le_centV hq⟩

private theorem center_pCore_eq_of_eq_Pc (h : RootHyp M V)
    (hQP : inSubgroup (pCore 2) M = Pc M V) :
    inSubgroup Subgroup.center (inSubgroup (pCore 2) M) = V := by
  rw [hQP]
  exact (center_map_subtype_eq_inf_centralizer (Pc M V)).trans h.toHyp.center_Pc

private theorem pCore_eq_V_of_commutator_eq_bot (h : RootHyp M V)
    (hZQ : inSubgroup Subgroup.center (inSubgroup (pCore 2) M) = V)
    (hCbot : inSubgroup commutator (inSubgroup (pCore 2) M) = ⊥) :
    inSubgroup (pCore 2) M = V := by
  set Q : Subgroup G := inSubgroup (pCore 2) M with hQ
  have hCbot' : inSubgroup commutator Q = ⊥ := hQ.symm ▸ hCbot
  have hcomm_bot : _root_.commutator ↥Q = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (H := _root_.commutator ↥Q) (f := Q.subtype)
      Q.subtype_injective).mp hCbot'
  have hcenter_top : Subgroup.center ↥Q = ⊤ :=
    (commutator_eq_bot_iff_center_eq_top (G := ↥Q)).mp hcomm_bot
  have hQ_le_Z : Q ≤ inSubgroup Subgroup.center Q := by
    intro q hq
    refine Subgroup.mem_map.mpr ⟨⟨q, hq⟩, ?_, rfl⟩
    rw [hcenter_top]
    exact Subgroup.mem_top _
  have hZQ' : inSubgroup Subgroup.center Q = V := hQ.symm ▸ hZQ
  refine le_antisymm ?_ ?_
  · exact hZQ' ▸ hQ_le_Z
  · exact hQ.symm ▸ h.toHyp.le_Q

private theorem weaklyClosed_of_pCore_eq_V (h : RootHyp M V)
    (hQV : inSubgroup (pCore 2) M = V) : WeaklyClosedIn V M := by
  refine ⟨h.toHyp.le_M, ?_⟩
  intro g hg
  set U : Subgroup G := conjSubgroup g V with hU
  have hUne : U ≠ ⊥ := by
    intro hbot
    apply h.toHyp.ne_bot
    have hconj := congrArg (conjSubgroup g⁻¹) hbot
    rw [hU, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one] at hconj
    simpa [conjSubgroup] using hconj
  have hUinf : conjSubgroup g V ⊓ M ≠ ⊥ := by
    rw [← hU, inf_eq_left.mpr hg]
    exact hUne
  have hcomm := h.toHyp.commute_of_conj_inf_ne_bot h.rootType hUinf
  have hUM : U ≤ M := by rw [hU]; exact hg
  have hUcentV : U ≤ Subgroup.centralizer (V : Set G) := by
    intro b hb
    rw [hU] at hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcomm a ha b hb
  have hUcentQ : U ≤ Subgroup.centralizer (inSubgroup (pCore 2) M : Set G) := by
    rw [hQV]
    exact hUcentV
  have hCMQ : M ⊓ Subgroup.centralizer (inSubgroup (pCore 2) M : Set G) ≤
      inSubgroup (pCore 2) M := inf_centralizer_pCore_le h.toHyp
  have hU_le_Q : U ≤ inSubgroup (pCore 2) M := (le_inf hUM hUcentQ).trans hCMQ
  have hU_le_V : U ≤ V := by rw [hQV] at hU_le_Q; exact hU_le_Q
  exact Subgroup.eq_of_le_of_card_ge hU_le_V
    (by rw [hU]; exact le_of_eq (card_conjSubgroup g V).symm)

private theorem frattini_eq_and_commutator_eq_of_minimal (h : RootHyp M V)
    (hmin : MinimalInvariant M V) :
    inSubgroup frattini (inSubgroup (pCore 2) M) = V ∧
      inSubgroup commutator (inSubgroup (pCore 2) M) = V := by
  have hQP := pCore_eq_Pc_of_minimal h hmin
  have hZQ := center_pCore_eq_of_eq_Pc h hQP
  set Q : Subgroup G := inSubgroup (pCore 2) M with hQ
  have hQnorm : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ]
    exact (inSubgroup_pCore_two M).2.2
  have hPhi_le_V : inSubgroup frattini Q ≤ V := by
    rw [hQP]
    exact h.toHyp.frattini_Pc_le
  have hComm_le_Phi : inSubgroup commutator Q ≤ inSubgroup frattini Q := by
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : Fact (IsPGroup 2 ↥Q) := ⟨by rw [hQ]; exact (inSubgroup_pCore_two M).1⟩
    exact Subgroup.map_mono (commutator_le_frattini_of_isPGroup (R := ↥Q) (p := 2))
  have hComm_le_V : inSubgroup commutator Q ≤ V := hComm_le_Phi.trans hPhi_le_V
  have hComm_normal : M ≤ Subgroup.normalizer (inSubgroup commutator Q : Set G) :=
    hQnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Q) (commutator ↥Q))
  have hPhi_normal : M ≤ Subgroup.normalizer (inSubgroup frattini Q : Set G) :=
    hQnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (H := Q) (frattini ↥Q))
  rcases hmin (inSubgroup commutator Q) hComm_le_V hComm_normal with hCbot | hCtop
  · exfalso
    have hQV : Q = V := pCore_eq_V_of_commutator_eq_bot h hZQ (hQ ▸ hCbot)
    exact h.not_weaklyClosed (weaklyClosed_of_pCore_eq_V h (hQ ▸ hQV))
  · exact ⟨le_antisymm hPhi_le_V (hCtop ▸ hComm_le_Phi), hCtop⟩

theorem pCore_eq_Pc (h : RootHyp M V)
    (hmin : MinimalInvariant M V) :
    inSubgroup (pCore 2) M = Pc M V :=
  pCore_eq_Pc_of_minimal h hmin

theorem center_pCore_eq (h : RootHyp M V)
    (hmin : MinimalInvariant M V) :
    inSubgroup Subgroup.center (inSubgroup (pCore 2) M) = V :=
  center_pCore_eq_of_eq_Pc h (pCore_eq_Pc_of_minimal h hmin)

theorem frattini_pCore_eq (h : RootHyp M V)
    (hmin : MinimalInvariant M V) :
    inSubgroup frattini (inSubgroup (pCore 2) M) = V :=
  (frattini_eq_and_commutator_eq_of_minimal h hmin).1

theorem commutator_pCore_eq (h : RootHyp M V)
    (hmin : MinimalInvariant M V) :
    inSubgroup commutator (inSubgroup (pCore 2) M) = V :=
  (frattini_eq_and_commutator_eq_of_minimal h hmin).2

theorem pCore_eq_Pc_and (h : RootHyp M V)
    (hmin : MinimalInvariant M V) :
    inSubgroup (pCore 2) M = Pc M V ∧
      inSubgroup Subgroup.center (inSubgroup (pCore 2) M) = V ∧
      inSubgroup frattini (inSubgroup (pCore 2) M) = V ∧
      inSubgroup commutator (inSubgroup (pCore 2) M) = V :=
  ⟨pCore_eq_Pc h hmin, center_pCore_eq h hmin, frattini_pCore_eq h hmin,
    commutator_pCore_eq h hmin⟩

end RootHyp

end CFSG.RankThree.GF2n.Tim81
