module

public import CFSG.Quasithin.Background.FFCSplitTransport

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

@[expose] def GoodFactor {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) : Prop :=
  B56FactorList ↥H ∧ B56Piece H ⊤ (fixV H)

theorem B56FactorList.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : B56FactorList Y) : B56FactorList X := by
  rcases h with h | h | h
  · obtain ⟨n, K, hK, hf, hn, hc, ⟨f⟩⟩ := h
    exact Or.inl ⟨n, K, hK, hf, hn, hc, ⟨e.trans f⟩⟩
  · obtain ⟨f⟩ := h
    exact Or.inr (Or.inl ⟨e.trans f⟩)
  · obtain ⟨m, K, hK, hf, hm, hodd, hc, ⟨f⟩⟩ := h
    exact Or.inr (Or.inr ⟨m, K, hK, hf, hm, hodd, hc, ⟨e.trans f⟩⟩)

section Transport

variable {V : Type} [CommGroup V]

namespace B58Split

variable {G A G₁ G₂ F : Subgroup (MulAut V)} (h : B58Split G A G₁ G₂ F)

include h in
theorem res_compat (g : ↥G₂) (w : ↥(fixV G₁)) :
    (fixV G₁).subtype (((resEquiv h.stab h.faithful g : ↥(autSub G₂ (fixV G₁))) :
      MulAut ↥(fixV G₁)) w) = (g : MulAut V) ((fixV G₁).subtype w) := rfl

theorem map_top_eq : (⊤ : Subgroup ↥(fixV G₁)).map (fixV G₁).subtype = fixV G₁ :=
  SplitTransport.map_top_eq

include h in
theorem fixV_eq : fixV G = fixV G₁ ⊓ fixV G₂ := by
  rw [← h.sup, fixV_sup]

include h in
theorem map_fixV_eq :
    (fixV (autSub G₂ (fixV G₁))).map (fixV G₁).subtype = fixV G :=
  SplitTransport.map_fixV_eq h.stab h.fixV_eq

include h in
theorem map_commV_eq :
    (commV (autSub G₂ (fixV G₁))).map (fixV G₁).subtype = commV G₂ := by
  rw [commV_eq_commSub, map_commSub_autSub h.stab, map_top_eq,
    commSub_eq_commV h.dec_sup h.triv₁]

include h in
theorem map_modComm_eq :
    (modComm (autSub G₂ (fixV G₁)) ⊤).map (fixV G₁).subtype = modComm G₂ (fixV G₁) :=
  SplitTransport.map_modComm_eq h.stab

include h in
theorem realizes_transport {D : FFModel} {U Z : Subgroup ↥(fixV G₁)}
    (hr : D.Realizes (autSub G₂ (fixV G₁)) U Z) :
    D.Realizes G₂ (U.map (fixV G₁).subtype) (Z.map (fixV G₁).subtype) :=
  SplitTransport.realizes_transport h.stab h.faithful hr


include h in
theorem binaryNaturalSL_transport {d a : ℕ}
    (hb : BinaryNaturalSL (autSub G₂ (fixV G₁)) ⊤ (fixV (autSub G₂ (fixV G₁))) d a) :
    BinaryNaturalSL G₂ (fixV G₁) (fixV G) d a :=
  SplitTransport.binaryNaturalSL_transport h.stab h.faithful h.fixV_eq hb

include h in
theorem symmetricNatural_transport {n : ℕ}
    (hb : SymmetricNatural (autSub G₂ (fixV G₁)) ⊤ (fixV (autSub G₂ (fixV G₁))) n) :
    SymmetricNatural G₂ (fixV G₁) (fixV G) n :=
  SplitTransport.symmetricNatural_transport h.stab h.faithful h.fixV_eq hb

include h in
theorem directSum_transport {D : FFModel} {k : ℕ}
    (hd : DirectSumOfCopies (autSub G₂ (fixV G₁)) ⊤ (fixV (autSub G₂ (fixV G₁))) D k) :
    DirectSumOfCopies G₂ (fixV G₁) (fixV G) D k :=
  SplitTransport.directSum_transport h.stab h.faithful h.fixV_eq hd


include h in
theorem pieceC_transport
    (hc : Nonempty (↥(autSub G₂ (fixV G₁)) ≃* ↥(StatedSL 3 (ZMod 2))) ∧
      commV (autSub G₂ (fixV G₁)) ≤ ⊤ ∧
      Nat.card ↥(⊤ : Subgroup ↥(fixV G₁)) = 2 ^ 4 * Nat.card ↥(fixV (autSub G₂ (fixV G₁))) ∧
      (¬ ∃ A B : Subgroup ↥(fixV G₁), fixV (autSub G₂ (fixV G₁)) < A ∧
        fixV (autSub G₂ (fixV G₁)) < B ∧ XMod.IsInv ↥(autSub G₂ (fixV G₁)) A ∧
        XMod.IsInv ↥(autSub G₂ (fixV G₁)) B ∧ A ⊔ B = ⊤ ∧ A ⊓ B = fixV (autSub G₂ (fixV G₁))) ∧
      BinaryNaturalSL (autSub G₂ (fixV G₁))
        (modComm (autSub G₂ (fixV G₁)) ⊤ ⊔ fixV (autSub G₂ (fixV G₁)))
        (fixV (autSub G₂ (fixV G₁))) 3 1) :
    Nonempty (↥G₂ ≃* ↥(StatedSL 3 (ZMod 2))) ∧ commV G₂ ≤ fixV G₁ ∧
      Nat.card ↥(fixV G₁) = 2 ^ 4 * Nat.card ↥(fixV G) ∧
      (¬ ∃ A B : Subgroup V, fixV G < A ∧ fixV G < B ∧ XMod.IsInv ↥G₂ A ∧ XMod.IsInv ↥G₂ B ∧
        A ⊔ B = fixV G₁ ∧ A ⊓ B = fixV G) ∧
      BinaryNaturalSL G₂ (modComm G₂ (fixV G₁) ⊔ fixV G) (fixV G) 3 1 :=
  SplitTransport.pieceC_transport h.stab h.faithful h.fixV_eq
    (by
      rw [← commSub_eq_commV h.dec_sup h.triv₁]
      exact commSub_le_of_invariant fun x hx w hw => (h.stab hx w).2 hw) hc


include h in
theorem GoodFactor.transport (hg : GoodFactor (autSub G₂ (fixV G₁))) :
    B56FactorList ↥G₂ ∧ B56Piece G₂ (fixV G₁) (fixV G) := by
  obtain ⟨hF, hP⟩ := hg
  refine ⟨B56FactorList.of_mulEquiv (resEquiv h.stab h.faithful) hF, ?_⟩
  have hT : ∀ (hT : (⊤ : Subgroup ↥(fixV G₁)) =
      commV (autSub G₂ (fixV G₁)) ⊔ fixV (autSub G₂ (fixV G₁))),
      fixV G₁ = commV G₂ ⊔ fixV G := fun hT => by
    have := congrArg (Subgroup.map (fixV G₁).subtype) hT
    rwa [map_top_eq, Subgroup.map_sup, map_commV_eq h, map_fixV_eq h] at this
  rcases hP with ⟨hT₀, hmod⟩ | ⟨hT₀, m, K, hK, hf, hc, hd⟩ | hC
  · refine Or.inl ⟨hT hT₀, ?_⟩
    rcases hmod with ⟨n, hn⟩ | hn | ⟨m, hm⟩
    · exact Or.inl ⟨n, h.binaryNaturalSL_transport hn⟩
    · exact Or.inr (Or.inl (h.symmetricNatural_transport hn))
    · exact Or.inr (Or.inr ⟨m, h.binaryNaturalSL_transport hm⟩)
  · exact Or.inr (Or.inl ⟨hT hT₀, m, K, hK, hf, hc, h.directSum_transport hd⟩)
  · exact Or.inr (Or.inr (h.pieceC_transport hC))

end B58Split

end Transport

end FFC

end CFSG.Quasithin
