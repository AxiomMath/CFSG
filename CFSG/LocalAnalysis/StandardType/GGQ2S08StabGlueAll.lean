module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabDatumAll
public import CFSG.LocalAnalysis.StandardType.GGQ2S08StabEmbedAll
public import CFSG.LocalAnalysis.StandardType.GGQ2S08HLCardAll
public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDiag
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggQ2s08_stab_card_le_all
    (hTBW : GGTBWNormInputOn (fun p lab => p = 3 ∧ GGQ2S08BigLabel lab))
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S) (hx : x ∈ Bs) (M : GGQ2LDatum 3 Bs L x) (hSh : M.Shape)
    {lab : LargeEvenLabel} (hlab : GGQ2S08BigLabel lab)
    (hmark : LargeEvenMarking L (fun lab' _ _ _ _ _ => lab' = lab))
    (hInn : GGInnerDiagOnLab (fun p lab' => p = 3 ∧ GGQ2S08BigLabel lab') 3 Bs L)
    (hCen : GGQ2S08BigCenterInput) (hOut : GGQ2S08BigInnerPartInput)
    (hMW : GGQ2LabelWeyl lab M.coxeter) :
    Nat.card ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤
      2 * Nat.card {π : M.Λ ≃ M.Λ // GGQ2S08DiagPerm 3 M.cartan π} *
        Nat.card ↥(ggAutomizer L Bs) := by
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.1.1
  obtain ⟨ι, φ, h, α, hcompat, hpair, hsimple, hAut, hdisj, hcard⟩ :=
    ggQ2s08_stab_datum_all hS hInn hCen hOut hBsN M hSh hmark hlab hMW
  have h1 := ggQ2s08_stab_embed_all hTBW hS hnc hx hBsN M hInn ι φ h α hcompat hpair hsimple hAut
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  haveI : Finite (M.V ⧸ Submodule.span (ZMod 3) {M.xV}) :=
    Finite.of_surjective (Submodule.Quotient.mk (p := Submodule.span (ZMod 3) {M.xV}))
      (Submodule.Quotient.mk_surjective _)
  have h2 := ggQ2s08_hL_card_le_all ι φ h α hdisj hsimple
  have hset : Nat.card {π : M.Λ ≃ M.Λ // ∀ i j, α (π i) (h (π j)) = α i (h j)} =
      Nat.card {π : M.Λ ≃ M.Λ // GGQ2S08DiagPerm 3 M.cartan π} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun π => by simp only [GGQ2S08DiagPerm, hpair])
  rw [hset] at h2
  calc _ ≤ Nat.card ↥(ggHL ι φ h α) := h1
    _ ≤ _ := h2
    _ ≤ _ := Nat.mul_le_mul_left _ hcard

end CFSG.StandardType

end
