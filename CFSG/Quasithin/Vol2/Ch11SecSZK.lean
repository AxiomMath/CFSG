module

public import CFSG.Quasithin.Background.C1GNC128
public import CFSG.Quasithin.Vol2.Ch10SecDClB
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import CFSG.Quasithin.Vol2.Ch1Nine

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

theorem isFaithfulLocal_of_omegaOneCenter (hQ : QuasithinUnique.quasithinIsQTKECat G)
    {T K : Subgroup G} (hT : quasithinIsSylowTwo T) (hK : quasithinIsLocal T K)
    (hZK : ⁅quasithinOmegaOneCenter T, K⁆ ≠ ⊥) : quasithinIsFaithfulLocal T K := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo hT
  have hchar : QuasithinUnique.CharTwo (K ⊔ T) := by
    have hH : InH (S : Subgroup G) (K ⊔ T) := ⟨hS ▸ le_sup_right, hK.2.2.2⟩
    exact charTwo_of_inH hQ.2.1 S hH
  have hV := C1GN.isTwoReducedIn_VZ hchar (isSylowTwoOf_of_quasithinIsSylowTwo hT le_sup_right)
  refine Ch10.SecD.quasithinIsFaithfulLocal_of_isTwoReducedIn hK hK.2.1 hchar hV ?_
  intro hb
  apply hZK
  refine eq_bot_iff.mpr ?_
  rw [← hb]
  exact Subgroup.commutator_mono (le_conjClosure _ _) le_rfl

theorem exists_maximalFaithful_ge (hQ : QuasithinUnique.quasithinIsQTKECat G)
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK)
    (h128 : Lemma128One) {T K : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hK : quasithinIsFaithfulLocal T K) :
    ∃ Kp : Subgroup G, K ≤ Kp ∧ quasithinIsMaximalLocal T Kp ∧ quasithinIsFaithfulLocal T Kp := by
  obtain ⟨Kp, ⟨hKp, hKKp⟩, hmax⟩ := Set.exists_max_image
    {J : Subgroup G | quasithinIsFaithfulLocal T J ∧ K ≤ J} (fun J => Nat.card ↥J)
    (Set.toFinite _) ⟨K, hK, le_rfl⟩
  have hmax' : ∀ J : Subgroup G, quasithinIsFaithfulLocal T J → Kp ≤ J → J = Kp := fun J hJ hle =>
    (Subgroup.eq_of_le_of_card_ge hle (hmax J ⟨hJ, hKKp.trans hle⟩)).symm
  obtain ⟨hm, hf⟩ := lemma_1_2_9_two hQ hs hnab h37 h128 hT hKp hmax'
  exact ⟨Kp, hKKp, hm, hf⟩

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem isLocal_K (h : StarHyp G T L I V₁ V₂ X K) : quasithinIsLocal T K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKT : K ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) :=
    sup_le h.K_le_normalizer_V₁ h.T_le_normalizer_V₁
  refine Ch10.SecD.quasithinIsLocal_of_mem_cComp h.comp rfl hKT
    (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right) fun hbot => ?_
  have hle : V₁ ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.V₁_le_T.trans le_sup_right) hKT
      h.isPGroup_V₁
  exact h.V₁_ne_bot (eq_bot_iff.mpr (hbot ▸ hle))

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
