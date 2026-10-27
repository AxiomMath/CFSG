module

public import CFSG.Quasithin.Background.FFCGoodFactorTransport
public import CFSG.Quasithin.Background.FFCProdSplit

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique

section Res5

variable {V : Type} [CommGroup V]

structure B511Split (G G₁ G₂ : Subgroup (MulAut V)) : Prop where
  G₁_le : G₁ ≤ G
  G₂_le : G₂ ≤ G
  sup : G₁ ⊔ G₂ = G
  inf : G₁ ⊓ G₂ = ⊥
  comm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a
  triv₁ : ∀ b ∈ G₂, ∀ v ∈ commV G₁, b v = v
  dec_sup : commV G₁ ⊔ fixV G₁ = ⊤

namespace B511Split

variable {G G₁ G₂ : Subgroup (MulAut V)} (h : B511Split G G₁ G₂)

include h in
theorem stab : G₂ ≤ stabSub (fixV G₁) :=
  ProdSplit.stab h.comm

include h in
theorem faithful : ∀ g ∈ G₂, (∀ v ∈ fixV G₁, g v = v) → g = 1 := by
  intro g hg hv
  ext v
  have hv' : v ∈ commV G₁ ⊔ fixV G₁ := by rw [h.dec_sup]; trivial
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hv'
  rw [map_mul, h.triv₁ g hg y hy, hv z hz]
  rfl

include h in
theorem normal : (G₂.subgroupOf G).Normal := normal_of_commute h.sup h.comm

include h in
theorem normal₁ : (G₁.subgroupOf G).Normal :=
  normal_of_commute (G₁ := G₂) (G₂ := G₁) (by rw [sup_comm]; exact h.sup)
    (fun a ha b hb => (h.comm b hb a ha).symm)

include h in
theorem conj_mem_G₁ : ∀ g ∈ G, ∀ x ∈ G₁, g * x * g⁻¹ ∈ G₁ := by
  intro g hg x hx
  have := h.normal₁.conj_mem ⟨x, h.G₁_le hx⟩ (by rwa [Subgroup.mem_subgroupOf]) ⟨g, hg⟩
  simpa [Subgroup.mem_subgroupOf] using this

include h in
theorem res_mem : ∀ g ∈ G, ∃ b ∈ G₂, ∀ v ∈ fixV G₁, g v = b v :=
  ProdSplit.res_mem h.sup h.comm

include h in
theorem stab_G : G ≤ stabSub (fixV G₁) :=
  ProdSplit.stab_G h.sup h.comm

include h in
theorem autSub_sup_eq : autSub G (fixV G₁) = autSub G₂ (fixV G₁) :=
  ProdSplit.autSub_sup_eq h.sup h.comm

include h in
theorem ffJ_autSub [Finite V] (hJ : G = ffJ G) :
    autSub G₂ (fixV G₁) ≤ ffJ (autSub G₂ (fixV G₁)) :=
  ProdSplit.ffJ_autSub h.sup h.comm hJ

include h in
theorem b53 [Finite V] (hO2 : pCoreOf 2 G = ⊥) (hJ : G = ffJ G) (hq : IsQuotientOfSQTKTauCeti ↥G) :
    B53Hyp (autSub G₂ (fixV G₁)) :=
  ProdSplit.b53 h.sup h.comm h.faithful hO2 hJ hq

include h in
theorem card_lt [Finite V] (hG₁ : G₁ ≠ ⊥) : Nat.card ↥(autSub G₂ (fixV G₁)) < Nat.card ↥G :=
  ProdSplit.card_lt h.sup h.inf h.comm h.faithful hG₁

include h in
theorem autSub_ne_bot (hne : G₂ ≠ ⊥) : autSub G₂ (fixV G₁) ≠ ⊥ :=
  ProdSplit.autSub_ne_bot h.comm h.faithful hne





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
    B56FactorList ↥G₂ ∧ B56Piece G₂ (fixV G₁) (fixV G) :=
  SplitTransport.goodFactor_transport h.stab h.faithful h.fixV_eq
    (by
      rw [← commSub_eq_commV h.dec_sup h.triv₁]
      exact commSub_le_of_invariant fun x hx w hw => (h.stab hx w).2 hw) hg

end B511Split

end Res5

end FFC

end CFSG.Quasithin
