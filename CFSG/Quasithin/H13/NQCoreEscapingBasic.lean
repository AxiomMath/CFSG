module

public import CFSG.Quasithin.H13.NQCoreEOneConfine
public import CFSG.Quasithin.H13.A7HyperplaneConfine

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem iSup_conjugate_eq_sSup (V T : Subgroup G) :
    (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) =
      sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate V g = X) ∧ X ≤ T} := by
  apply le_antisymm
  · exact iSup₂_le fun g hg => le_sSup ⟨⟨g, rfl⟩, hg⟩
  · refine sSup_le ?_
    rintro _ ⟨⟨g, rfl⟩, hg⟩
    exact le_iSup₂_of_le g hg le_rfl

omit [Finite G] in
theorem isSylowIn_of_quasithin {T H : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) :
    IsSylowIn 2 T H :=
  ⟨hTH, hT.1, fun hd => hT.2 (hd.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩

theorem qtnqU_le_sylow {T L M : Subgroup G} (h : QTNQ T L M) : qtnqU L M ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨-, hUM, hUn, hUe⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hUp : IsPGroup 2 ↥(qtnqU L M) := by
    have := hUe
    exact CFSG.IsElementaryAbelian.isPGroup 2 ↥(qtnqU L M)
  exact (isSylowIn_of_quasithin h.sylow h.t_le).le_of_normal hUM hUn hUp

theorem le_of_isSolvable_of_TI {T L M : Subgroup G}
    (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {H : Subgroup G} (hTH : T ≤ H) (hH : Group.IsSolvable H) : H ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨hU1, -, -, hUe⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hhyp := (nq_original_TI_hyperplane_conjugates_centralize_internal_module h hTI).2.2
  refine A7.A7_hyperplane_conjugates_confine_solvable_Sylow_overgroups
    (h.sylow.1.toSylow h.sylow.2) hU1 (qtnqU_le_sylow h) hUe ?_
    (centralizer_qtnqU_le h) ?_ H hTH hH
  · rw [iSup_conjugate_eq_sSup]
    exact hW
  · intro g B hB hidx
    exact hhyp g B hB hidx

omit [Finite G] in
theorem normalizer_sylow_le_of_TI {T L M : Subgroup G}
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M) :
    normalizer (T : Set G) ≤ M := fun n hn => by
  apply hW
  rw [← iSup_conjugate_eq_sSup]
  exact A7.mem_normalizer_conjugateJoin_of le_rfl (fun _ hg => hg) hn

theorem minimal_escaping_basic {T L M : Subgroup G}
    (h : QTNQ T L M)
    (hTI : ∀ g : G, qtnqU L M ⊓ CFSG.conjugate (qtnqU L M) g = ⊥ ∨
      CFSG.conjugate (qtnqU L M) g = qtnqU L M)
    (hW : normalizer ((sSup {X : Subgroup G | (∃ g : G, CFSG.conjugate (qtnqU L M) g = X) ∧
      X ≤ T} : Subgroup G) : Set G) ≤ M)
    {H₀ H : Subgroup G} (hH₀ : quasithinIsMaxTwoLocal H₀) (hTH₀ : T ≤ H₀)
    (hTH : T ≤ H) (hHH₀ : H ≤ H₀) (hHM : ¬ H ≤ M)
    (hmin : ∀ K : Subgroup G, T ≤ K → K ≤ H₀ → ¬ K ≤ M → Nat.card H ≤ Nat.card K) :
    ¬ Group.IsSolvable H ∧ pCoreOf 2 H ≠ ⊥ ∧ CFSG.SectionRank.IsSQTKCat H ∧
      ¬ (T.subgroupOf H).Normal ∧ T ≤ H ⊓ M ∧ H ⊓ M < H ∧
      ∀ K : Subgroup G, T ≤ K → K < H → K ≤ H ⊓ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  have hns : ¬ Group.IsSolvable H := fun hs => hHM (le_of_isSolvable_of_TI h hTI hW hTH hs)
  have hR₀ : pCoreOf 2 H₀ ≠ ⊥ := by
    obtain ⟨P, hP1, hP2, hPM⟩ := hH₀.1
    intro hb
    apply hP1
    rw [eq_bot_iff, ← hb, hPM]
    exact LieType.BorelTits.le_pCoreOf_normalizer 2 P hP2
  have hR₀T : pCoreOf 2 H₀ ≤ T :=
    QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowIn_of_quasithin h.sylow hTH₀)
  have hR₀R : pCoreOf 2 H₀ ≤ pCoreOf 2 H := by
    refine LieType.BorelTits.le_pCoreOf 2 (hR₀T.trans hTH) ?_
      (LieType.BorelTits.pCoreOf_isPGroup 2 H₀)
    exact (normal_subgroupOf_iff_le_normalizer (hR₀T.trans hTH)).2
      (hHH₀.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 H₀))
  have hR : pCoreOf 2 H ≠ ⊥ := fun hb => hR₀ (le_bot_iff.1 (hb ▸ hR₀R))
  have hsqtk : CFSG.SectionRank.IsSQTKCat H := (qtkeCore_of_cat h.nonabelian h.qtke).1 H hR
  have hTn : ¬ (T.subgroupOf H).Normal := fun hn =>
    hHM (((normal_subgroupOf_iff_le_normalizer hTH).1 hn).trans (normalizer_sylow_le_of_TI hW))
  refine ⟨hns, hR, hsqtk, hTn, le_inf hTH h.t_le, inf_lt_left.2 hHM, fun K hTK hKH => ?_⟩
  refine le_inf hKH.le ?_
  by_contra hKM
  have h1 := hmin K hTK (hKH.le.trans hHH₀) hKM
  have h2 : Nat.card K < Nat.card H := Subgroup.card_lt_of_lt hKH
  omega

end CFSG.Quasithin.H13.NQCore
