module

public import CFSG.Quasithin.EmptyFaithful.S151WJ0
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33

public section

namespace CFSG.Quasithin

open Equiv CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over
  CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.L246C127

set_option maxRecDepth 100000

namespace U33Lat

abbrev MU : Subgroup (Perm (Fin 28)) := Subgroup.closure {g | g ∈ CertU33.cert.mGens}

abbrev TU : Subgroup (Perm (Fin 28)) := Subgroup.closure {g | g ∈ CertU33.cert.tGens}

abbrev QU1 : Subgroup (Perm (Fin 28)) := Subgroup.closure {g | g ∈ CertU33.L1}

abbrev QU2 : Subgroup (Perm (Fin 28)) := Subgroup.closure {g | g ∈ CertU33.L2}

abbrev y1 : Perm (Fin 28) := CertU33.L1.getD 2 1

abbrev y2 : Perm (Fin 28) := CertU33.L2.getD 2 1

abbrev t1 : Perm (Fin 28) := CertU33.tGens.getD 0 1

abbrev t2 : Perm (Fin 28) := CertU33.tGens.getD 1 1

theorem L1_eq : CertU33.L1 = CertU33.tGens ++ [y1] := rfl

theorem L2_eq : CertU33.L2 = CertU33.tGens ++ [y2] := rfl

theorem tGens_eq : CertU33.cert.tGens = [t1, t2] := rfl

theorem tGens_eq' : CertU33.tGens = [t1, t2] := rfl

@[expose] def w1 : List ℕ := [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0]

@[expose] def w2 : List ℕ := [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]

theorem hw1 : evalW CertU33.cert.mGens w1 = y1 := by decide +kernel

theorem hw2 : evalW CertU33.cert.mGens w2 = y2 := by decide +kernel

theorem y1_mem : y1 ∈ MU := by
  have h := evalW_mem_closure CertU33.cert.mGens w1
  rwa [hw1] at h

theorem y2_mem : y2 ∈ MU := by
  have h := evalW_mem_closure CertU33.cert.mGens w2
  rwa [hw2] at h

@[expose] def stabSub (A : Finset (Fin 28)) : Subgroup (Perm (Fin 28)) where
  carrier := {g | ∀ a, a ∈ A ↔ g a ∈ A}
  one_mem' := fun a => Iff.rfl
  mul_mem' := fun {g h} hg hh a => (hh a).trans (hg (h a))
  inv_mem' := fun {g} hg a => by
    have h1 : g (g⁻¹ a) = a := by
      rw [← Equiv.Perm.mul_apply, mul_inv_cancel]
      rfl
    have := hg (g⁻¹ a)
    rw [h1] at this
    exact this.symm

theorem mem_stabSub {A : Finset (Fin 28)} {g : Perm (Fin 28)} :
    g ∈ stabSub A ↔ ∀ a, a ∈ A ↔ g a ∈ A := Iff.rfl

@[expose] def Aorb : Finset (Fin 28) := {4, 7, 10, 13, 16, 19, 22, 25}

@[expose] def A0 : Finset (Fin 28) := {0, 1, 2, 3}

theorem t1_Aorb : t1 ∈ stabSub Aorb := by
  rw [mem_stabSub]
  decide +kernel

theorem t2_Aorb : t2 ∈ stabSub Aorb := by
  rw [mem_stabSub]
  decide +kernel

theorem t1_A0 : t1 ∈ stabSub A0 := by
  rw [mem_stabSub]
  decide +kernel

theorem t2_A0 : t2 ∈ stabSub A0 := by
  rw [mem_stabSub]
  decide +kernel

theorem y1_A0 : y1 ∈ stabSub A0 := by
  rw [mem_stabSub]
  decide +kernel

theorem y2_not_A0 : y2 ∉ stabSub A0 := by
  rw [mem_stabSub]
  decide +kernel

theorem y1_conj_not : y1 * t2 * y1⁻¹ ∉ stabSub Aorb := by
  rw [mem_stabSub]
  decide +kernel

theorem y2_conj_not : y2 * t1 * y2⁻¹ ∉ stabSub A0 := by
  rw [mem_stabSub]
  decide +kernel

theorem TU_le_Aorb : TU ≤ stabSub Aorb := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [tGens_eq] at hg
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact t1_Aorb
  · exact t2_Aorb

theorem y1_not_norm : y1 ∉ Subgroup.normalizer (TU : Set (Perm (Fin 28))) := by
  intro h
  have ht2 : t2 ∈ TU := Subgroup.subset_closure (by rw [Set.mem_ofPred_eq, tGens_eq]; simp)
  exact y1_conj_not (TU_le_Aorb ((Subgroup.mem_normalizer_iff.1 h t2).1 ht2))

theorem TU_le_A0 : TU ≤ stabSub A0 := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [tGens_eq] at hg
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact t1_A0
  · exact t2_A0

theorem y2_not_norm : y2 ∉ Subgroup.normalizer (TU : Set (Perm (Fin 28))) := by
  intro h
  have ht1 : t1 ∈ TU := Subgroup.subset_closure (by rw [Set.mem_ofPred_eq, tGens_eq]; simp)
  exact y2_conj_not (TU_le_A0 ((Subgroup.mem_normalizer_iff.1 h t1).1 ht1))

theorem QU1_le_A0 : QU1 ≤ stabSub A0 := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [L1_eq, tGens_eq'] at hg
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl) | rfl
  · exact t1_A0
  · exact t2_A0
  · exact y1_A0

theorem QU1_ne_QU2 : QU1 ≠ QU2 := by
  intro h
  have hy2 : y2 ∈ QU2 := Subgroup.subset_closure (by rw [Set.mem_ofPred_eq, L2_eq]; simp)
  rw [← h] at hy2
  exact y2_not_A0 (QU1_le_A0 hy2)

theorem TU_le_QU1 : TU ≤ QU1 := Subgroup.closure_mono (by
  intro g hg
  rw [Set.mem_ofPred_eq] at hg ⊢
  rw [L1_eq]
  exact List.mem_append_left _ hg)

theorem TU_le_QU2 : TU ≤ QU2 := Subgroup.closure_mono (by
  intro g hg
  rw [Set.mem_ofPred_eq] at hg ⊢
  rw [L2_eq]
  exact List.mem_append_left _ hg)

theorem hcl : CertU33.cert.closedOK RN.enc = true :=
  CertU33.cert.closedOK_of_check CertU33.cert_check

theorem hsz : CertU33.cert.sizesOK RN.enc = true :=
  CertU33.cert.sizesOK_of_check CertU33.cert_check

theorem TU_le_MU : TU ≤ MU :=
  CertU33.cert.t_le_m (rawIsEnc 28) hcl (by
    have := CertU33.tle_ok
    exact this)

theorem QU1_le_MU : QU1 ≤ MU := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [L1_eq] at hg
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl
  · exact TU_le_MU (Subgroup.subset_closure hg)
  · exact y1_mem

theorem QU2_le_MU : QU2 ≤ MU := by
  rw [Subgroup.closure_le]
  intro g hg
  rw [L2_eq] at hg
  simp only [Set.mem_ofPred_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl
  · exact TU_le_MU (Subgroup.subset_closure hg)
  · exact y2_mem

theorem card_MU : Nat.card MU = 6048 := CertU33.cert.card_m (rawIsEnc 28) hcl hsz

theorem card_TU : Nat.card TU = 32 := CertU33.cert.card_t (rawIsEnc 28) hcl hsz

theorem card_QU1 : Nat.card QU1 = 96 :=
  CertU33.cert.card_member_idx (rawIsEnc 28) hcl hsz 1 (by decide)

theorem card_QU2 : Nat.card QU2 = 96 :=
  CertU33.cert.card_member_idx (rawIsEnc 28) hcl hsz 2 (by decide)

abbrev DU : Subgroup ↥MU := TU.subgroupOf MU

abbrev Q1 : Subgroup ↥MU := QU1.subgroupOf MU

abbrev Q2 : Subgroup ↥MU := QU2.subgroupOf MU

theorem sylow_DU : IsSylowTwoOf DU ⊤ :=
  CertU33.cert.isSylowTwoOf_top (rawIsEnc 28) CertU33.cert_check (k := 5) (m := 189) (by decide)
    (by decide) (by decide)

theorem DU_card : Nat.card ↥DU = 32 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe TU_le_MU).toEquiv, card_TU]

theorem Q1_card : Nat.card ↥Q1 = 96 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QU1_le_MU).toEquiv, card_QU1]

theorem Q2_card : Nat.card ↥Q2 = 96 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe QU2_le_MU).toEquiv, card_QU2]

theorem DU_le_Q1 : DU ≤ Q1 := fun _ hx => TU_le_QU1 hx

theorem DU_le_Q2 : DU ≤ Q2 := fun _ hx => TU_le_QU2 hx

theorem Q1_ne_top : Q1 ≠ ⊤ := fun h => by
  have := Q1_card
  rw [h, Subgroup.card_top, Nat.card_congr (Equiv.refl _), card_MU] at this
  omega

theorem Q2_ne_top : Q2 ≠ ⊤ := fun h => by
  have := Q2_card
  rw [h, Subgroup.card_top, card_MU] at this
  omega

theorem Q1_ne_Q2 : Q1 ≠ Q2 := fun h => QU1_ne_QU2 (by
  have := congrArg (Subgroup.map MU.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le QU1_le_MU,
    Subgroup.map_subgroupOf_eq_of_le QU2_le_MU] at this)

theorem DU_lt_Q1 : DU < Q1 := lt_of_le_of_ne DU_le_Q1 fun h => by
  have := DU_card
  rw [h, Q1_card] at this
  omega

theorem lat4 (Y : Subgroup ↥MU) (hY : DU ≤ Y) : Y = DU ∨ Y = Q1 ∨ Y = Q2 ∨ Y = ⊤ := by
  obtain ⟨j, hj, hLM, hYj, hcard⟩ :=
    CertU33.cert.overgroup_cases_idx (rawIsEnc 28) CertU33.cert_check Y hY
  have hlen : (CertU33.cert.tGens :: CertU33.cert.lat).length = 4 := rfl
  have hj4 : j < 4 := by omega
  interval_cases j
  · exact Or.inl hYj
  · exact Or.inr (Or.inl hYj)
  · exact Or.inr (Or.inr (Or.inl hYj))
  · right
    right
    right
    have heq := Subgroup.eq_of_le_of_card_ge hLM (by rw [hcard, card_MU]; decide)
    rw [hYj, heq, Subgroup.subgroupOf_self]

theorem not_mem_normalizer_DU {g : Perm (Fin 28)} (hg : g ∈ MU)
    (hn : g ∉ Subgroup.normalizer (TU : Set (Perm (Fin 28)))) :
    (⟨g, hg⟩ : ↥MU) ∉ Subgroup.normalizer (DU : Set ↥MU) := by
  intro h
  rw [← Subgroup.subgroupOf_normalizer_eq TU_le_MU] at h
  exact hn (Subgroup.mem_subgroupOf.1 h)

theorem normalizer_DU : Subgroup.normalizer (DU : Set ↥MU) ≤ DU := by
  intro x hx
  have hDN : DU ≤ Subgroup.normalizer (DU : Set ↥MU) := Subgroup.le_normalizer
  rcases lat4 _ hDN with h | h | h | h
  · rw [h] at hx
    exact hx
  · exfalso
    have hy : (⟨y1, y1_mem⟩ : ↥MU) ∈ Subgroup.normalizer (DU : Set ↥MU) := by
      rw [h]
      exact Subgroup.subset_closure (by
        rw [Set.mem_ofPred_eq, L1_eq]
        simp)
    exact not_mem_normalizer_DU y1_mem y1_not_norm hy
  · exfalso
    have hy : (⟨y2, y2_mem⟩ : ↥MU) ∈ Subgroup.normalizer (DU : Set ↥MU) := by
      rw [h]
      exact Subgroup.subset_closure (by
        rw [Set.mem_ofPred_eq, L2_eq]
        simp)
    exact not_mem_normalizer_DU y2_mem y2_not_norm hy
  · exfalso
    have hy : (⟨y1, y1_mem⟩ : ↥MU) ∈ Subgroup.normalizer (DU : Set ↥MU) := by
      rw [h]
      exact Subgroup.mem_top _
    exact not_mem_normalizer_DU y1_mem y1_not_norm hy

theorem isMax_Q1 : IsMaxSubgroupIn ⊤ Q1 := by
  refine ⟨lt_top_iff_ne_top.2 Q1_ne_top, fun K hK _ => ?_⟩
  rcases lat4 K (DU_le_Q1.trans hK.le) with h | h | h | h
  · exact absurd (h ▸ DU_le_Q1) (not_le_of_gt hK)
  · exact absurd h.symm hK.ne
  · exact absurd (Subgroup.eq_of_le_of_card_ge (h ▸ hK.le) (by rw [Q1_card, Q2_card])) Q1_ne_Q2
  · exact h

theorem isMax_Q2 : IsMaxSubgroupIn ⊤ Q2 := by
  refine ⟨lt_top_iff_ne_top.2 Q2_ne_top, fun K hK _ => ?_⟩
  rcases lat4 K (DU_le_Q2.trans hK.le) with h | h | h | h
  · exact absurd (h ▸ DU_le_Q2) (not_le_of_gt hK)
  · exact absurd (Subgroup.eq_of_le_of_card_ge (h ▸ hK.le) (by rw [Q1_card, Q2_card])).symm Q1_ne_Q2
  · exact absurd h.symm hK.ne
  · exact h

theorem charTwo_Q1 : CharTwo Q1 :=
  (overgroups_charTwo CertU33.cert CertU33.cts rfl TU_le_MU CertU33.cert_check CertU33.members_ok
    Q1 DU_le_Q1).resolve_left Q1_ne_top

theorem charTwo_Q2 : CharTwo Q2 :=
  (overgroups_charTwo CertU33.cert CertU33.cts rfl TU_le_MU CertU33.cert_check CertU33.members_ok
    Q2 DU_le_Q2).resolve_left Q2_ne_top

theorem rank2Data_U33 : Rank2Data DU := by
  refine ⟨normalizer_DU, Q1, Q2, Q1_ne_Q2, isMax_Q1, isMax_Q2, DU_le_Q1, DU_le_Q2, ?_, ?_,
    charTwo_Q1, charTwo_Q2, ?_⟩
  · rw [Q1_card, DU_card]
  · rw [Q2_card, DU_card]
  · intro K hK hDK
    rcases lat4 K hDK with h | h | h | h
    · exfalso
      exact (lt_top_iff_ne_top.1 isMax_Q1.1) (hK.2 Q1 (h ▸ DU_lt_Q1) le_top)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hK.1.ne

end U33Lat

end CFSG.Quasithin
