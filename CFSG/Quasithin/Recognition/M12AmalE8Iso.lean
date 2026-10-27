module

public import CFSG.Quasithin.Recognition.M12AmalAutLIso

public section

namespace CFSG.Quasithin.AmalTransport

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

@[expose] def E8Concl {G : Type} [Group G] (H L2 : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ pCoreOf 2 H ∧ IsElemAbelian 2 E ∧ Nat.card E = 8 ∧
    L2 ≤ Subgroup.normalizer (E : Set G) ∧
    ∀ V : Subgroup G, V ≤ pCoreOf 2 H → Nat.card V = 4 →
      L2 ≤ Subgroup.normalizer (V : Set G) → V ≤ E

theorem E8Concl.of_iso {G E : Type} [Group G] [Group E] {P₁ P₂ : Subgroup G} {K₁ K₂ : Subgroup E}
    (iso : (RankTwoAmalgam.ofSubgroups P₁ P₂).Iso (RankTwoAmalgam.ofSubgroups K₁ K₂))
    (hcore : pCoreOf 2 K₁ ≤ K₁ ⊓ K₂) (h : E8Concl K₁ K₂) : E8Concl P₁ P₂ := by
  obtain ⟨E', hE'P, hE'el, hE'8, hE'N, hE'V⟩ := h
  let F : Frame P₁ P₂ K₁ K₂ := Frame.ofIso iso
  have hPW : pCoreOf 2 P₁ ≤ P₁ ⊓ P₂ := F.pCoreOf_le_inf hcore
  have hP : F.tr (pCoreOf 2 P₁) = pCoreOf 2 K₁ := F.tr_pCoreOf hcore
  have hE'K : E' ≤ K₁ ⊓ K₂ := hE'P.trans hcore
  have hEtr : F.tr (F.pb E') = E' := F.tr_pb hE'K
  have hEW : F.pb E' ≤ P₁ ⊓ P₂ := F.pb_le E'
  refine ⟨F.pb E', ?_, ?_, ?_, ?_, ?_⟩
  · rw [← F.tr_le_tr_iff hEW, hEtr, hP]
    exact hE'P
  · exact (F.isElemAbelian_tr hEW).1 (by rw [hEtr]; exact hE'el)
  · rw [← F.card_tr hEW, hEtr]
    exact hE'8
  · exact (F.normalizer_tr2 hEW).2 (by rw [hEtr]; exact hE'N)
  · intro V hVP hV4 hN
    have hVW : V ≤ P₁ ⊓ P₂ := hVP.trans hPW
    have hVup : F.tr V ≤ pCoreOf 2 K₁ := by
      rw [← hP]
      exact F.tr_mono hVP
    have h1 := hE'V (F.tr V) hVup (by rw [F.card_tr hVW]; exact hV4)
      ((F.normalizer_tr2 hVW).1 hN)
    rw [← hEtr] at h1
    exact (F.tr_le_tr_iff hVW).1 h1

end CFSG.Quasithin.AmalTransport
