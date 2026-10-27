module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Bar2TransferSL3
import CFSG.Quasithin.Background.FFC4Res
import CFSG.Quasithin.Background.HSecTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {W : Type} [CommGroup W]

theorem realizes_of_autSub {L : Subgroup (MulAut W)} {I : Subgroup W} (hLI : L ≤ stabSub I)
    (hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1) {D : CFSG.Quasithin.FFModel}
    (h : D.Realizes (autSub L I) ⊤ ⊥) : D.Realizes L I ⊥ :=
  H.FFModel.realizes_of_equiv (fun _ hl u hu => (hLI hl u).2 hu) (MulEquiv.refl ↥I)
    (FFC.resEquiv hLI hinj) (fun _ _ => rfl) h

theorem binaryNaturalSL_of_autSub {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hLI : L ≤ stabSub I) (hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1) {d a : ℕ}
    (h : CFSG.Quasithin.BinaryNaturalSL (autSub L I) ⊤ ⊥ d a) :
    CFSG.Quasithin.BinaryNaturalSL L I ⊥ d a := by
  obtain ⟨K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨K, hK, hKf, hcard, realizes_of_autSub hLI hinj hreal⟩

theorem natOmegaMinus_of_autSub {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hLI : L ≤ stabSub I) (hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1) {m a : ℕ}
    (h : NatOmegaMinus (autSub L I) ⊤ ⊥ m a) : NatOmegaMinus L I ⊥ m a := by
  obtain ⟨hm, K, hK, hKf, b, c, hcard, hirr, hreal⟩ := h
  exact ⟨hm, K, hK, hKf, b, c, hcard, hirr, realizes_of_autSub hLI hinj hreal⟩

private theorem natOmegaPlus_of_autSub {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hLI : L ≤ stabSub I) (hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1) {m a : ℕ}
    (h : NatOmegaPlus (autSub L I) ⊤ ⊥ m a) : NatOmegaPlus L I ⊥ m a := by
  obtain ⟨hm, K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨hm, K, hK, hKf, hcard, realizes_of_autSub hLI hinj hreal⟩

private theorem natSpn_of_autSub {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hLI : L ≤ stabSub I) (hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1) {m a : ℕ}
    (h : NatSpn (autSub L I) ⊤ ⊥ m a) : NatSpn L I ⊥ m a := by
  obtain ⟨hm, K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨hm, K, hK, hKf, hcard, realizes_of_autSub hLI hinj hreal⟩

private theorem natSUn_of_autSub {L : Subgroup (MulAut W)} {I : Subgroup W}
    (hLI : L ≤ stabSub I) (hinj : ∀ l ∈ L, (∀ u ∈ I, l u = u) → l = 1) {m a : ℕ}
    (h : NatSUn (autSub L I) ⊤ ⊥ m a) : NatSUn L I ⊥ m a := by
  obtain ⟨K, hK, hKf, hcard, hreal⟩ := h
  exact ⟨K, hK, hKf, hcard, realizes_of_autSub hLI hinj hreal⟩

private theorem isSpn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSpn X n a) : IsSpn Y n a := by
  obtain ⟨hn, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hn, K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

private theorem isSUn_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {n a : ℕ}
    (h : IsSUn X n a) : IsSUn Y n a := by
  obtain ⟨K, hK, hKf, hcard, ⟨e'⟩⟩ := h
  exact ⟨K, hK, hKf, hcard, ⟨e.symm.trans e'⟩⟩

theorem isNaturalClassicalModule_of_autSub_top {L : Subgroup (MulAut W)} {k : ℕ}
    (h : IsNaturalClassicalModule (autSub L (⊤ : Subgroup W)) k) :
    IsNaturalClassicalModule L k := by
  have hLI : L ≤ stabSub (⊤ : Subgroup W) :=
    fun _ _ _ => ⟨fun _ => Subgroup.mem_top _, fun _ => Subgroup.mem_top _⟩
  have hinj : ∀ l ∈ L, (∀ u ∈ (⊤ : Subgroup W), l u = u) → l = 1 :=
    fun _ _ hl => MulEquiv.ext fun u => hl u (Subgroup.mem_top u)
  let e := (FFC.resEquiv hLI hinj).symm
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨a, ha, h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨CFSG.Blueprint.LieModel.of_mulEquiv e h1, binaryNaturalSL_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inl ⟨IsOmegaMinus.of_mulEquiv e h1, natOmegaMinus_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨IsOmegaPlus.of_mulEquiv e h1, natOmegaPlus_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨CFSG.Blueprint.LieModel.of_mulEquiv e h1, natSpn_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨IsSLn.of_mulEquiv e h1, binaryNaturalSL_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨a, ha, isSUn_of_mulEquiv e h1, natSUn_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨IsOmegaMinus.of_mulEquiv e h1, natOmegaMinus_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      ⟨IsSLn.of_mulEquiv e h1, binaryNaturalSL_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inl ⟨IsOmegaPlus.of_mulEquiv e h1, natOmegaPlus_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inl ⟨isSpn_of_mulEquiv e h1, natSpn_of_autSub hLI hinj h2⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr
        ⟨CFSG.Blueprint.LieModel.of_mulEquiv e h1, natOmegaMinus_of_autSub hLI hinj h2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
