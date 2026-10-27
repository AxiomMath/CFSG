module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagDefs
import CFSG.LieType.Steinberg.Minuscule.Datum
import CFSG.LieType.Steinberg.Exceptional.Fields
import CFSG.LieType.Steinberg.TwistedE6.Datum
import CFSG.LieType.Steinberg.TwistedE6.Generation

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Exceptional CFSG.Assembly.LowTwoRank
  CFSG.Blueprint.Chevalley

section Helpers

private theorem nm_sq_eq_one {k : Type*} [Field k] [CharP k 2] {τ : Tag} {D : MinData τ}
    (hV : D.Valid) (i : Fin τ.rank) : hV.nm k i * hV.nm k i = 1 := by
  have hneg : (-1 : kˣ) = 1 := by
    apply Units.ext
    rw [Units.coe_neg_one, Units.val_one, CharTwo.neg_eq]
  rw [← pow_two, hV.nm_sq k i, hneg, hV.hm_one k i]

end Helpers

section Tag

variable {G : Type} [Group G] [Finite G]

theorem ggTagFacts_E6 {n f : ℕ} (hadm : StatedLieAdmissible .E6 n 2 f)
    (hrank : 3 ≤ bnRank .E6 n) : GGTagFacts .E6 n f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ggUniversalFacts_of_steinberg
    (n := e6Data_valid.nm (GaloisField 2 f))
    (H := e6Data_valid.torus (GaloisField 2 f)) ?_ ?_ ?_ ?_⟩
  · show 2 ≤ 6
    norm_num
  · exact Tag.rank_pos .E6
  · exact e6Datum_isCTGroupDatum (GaloisField 2 f)
  · exact e6Datum_steinbergExtras (GaloisField 2 f)
  · intro i
    exact nm_sq_eq_one e6Data_valid i

theorem ggSecFivePres_of_psi_E6 {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .E6 n 2 f) (hrank : 3 ≤ bnRank .E6 n)
    (ψ : (ggU .E6 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E6 n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .E6 n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_E6 hadm hrank) ψ hker hrange

theorem ggTagFacts_E7 {n f : ℕ} (hadm : StatedLieAdmissible .E7 n 2 f)
    (hrank : 3 ≤ bnRank .E7 n) : GGTagFacts .E7 n f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, ggUniversalFacts_of_steinberg
    (n := e7Data_valid.nm (GaloisField 2 f))
    (H := e7Data_valid.torus (GaloisField 2 f)) ?_ ?_ ?_ ?_⟩
  · show 2 ≤ 7
    norm_num
  · exact Tag.rank_pos .E7
  · exact e7Datum_isCTGroupDatum (GaloisField 2 f)
  · exact e7Datum_steinbergExtras (GaloisField 2 f)
  · intro i
    exact nm_sq_eq_one e7Data_valid i

theorem ggSecFivePres_of_psi_E7 {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .E7 n 2 f) (hrank : 3 ≤ bnRank .E7 n)
    (ψ : (ggU .E7 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .E7 n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .E7 n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_E7 hadm hrank) ψ hker hrange

theorem ggTagFacts_twistedE6 {n f : ℕ} (hadm : StatedLieAdmissible .twistedE6 n 2 f)
    (hrank : 3 ≤ bnRank .twistedE6 n) : GGTagFacts .twistedE6 n f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf : 1 ≤ f := hadm.2.1
  have hθ : ∀ c, frobQ 2 f (frobQ 2 f c) = c := frobQ_frobQ 2 f hf
  refine ⟨?_, ggUniversalFacts_of_steinberg
    (n := TwistedE6.nHat (frobQ 2 f))
    (H := TwistedE6.hHat (GaloisField 2 (2 * f)) (frobQ 2 f)) ?_ ?_ ?_ ?_⟩
  · show 2 ≤ 4
    norm_num
  · exact Tag.rank_pos .F4
  · exact TwistedE6.twistedDatum_isCTGroupDatum (frobQ 2 f) hθ
      (TwistedE6.iSup_twistedDatum_rootGroup (frobQ 2 f) hθ)
  · exact TwistedE6.twistedDatum_steinbergExtras (frobQ 2 f) hθ
  · intro i
    apply Subtype.ext
    change TwistedE6.nHatE (GaloisField 2 (2 * f)) i *
      TwistedE6.nHatE (GaloisField 2 (2 * f)) i = 1
    fin_cases i
    · change e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 1) *
        e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 1) = 1
      exact nm_sq_eq_one e6Data_valid (TwistedE6.nd 1)
    · change e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 3) *
        e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 3) = 1
      exact nm_sq_eq_one e6Data_valid (TwistedE6.nd 3)
    · change e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2) *
        e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4) *
        (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2) *
          e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4)) = 1
      have ha : e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2) *
          e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2) = 1 :=
        nm_sq_eq_one e6Data_valid (TwistedE6.nd 2)
      have hb : e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4) *
          e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4) = 1 :=
        nm_sq_eq_one e6Data_valid (TwistedE6.nd 4)
      have hcomm : Commute (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2))
          (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4)) :=
        e6Data_valid.nm_comm _ (by decide) (by decide)
      calc e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2) *
            e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4) *
            (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2) *
              e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4))
          = (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2) *
              e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4)) ^ 2 :=
            (pow_two _).symm
        _ = e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 2) ^ 2 *
              e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 4) ^ 2 :=
            hcomm.mul_pow 2
        _ = 1 := by rw [pow_two, pow_two, ha, hb, mul_one]
    · change e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0) *
        e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5) *
        (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0) *
          e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5)) = 1
      have ha : e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0) *
          e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0) = 1 :=
        nm_sq_eq_one e6Data_valid (TwistedE6.nd 0)
      have hb : e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5) *
          e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5) = 1 :=
        nm_sq_eq_one e6Data_valid (TwistedE6.nd 5)
      have hcomm : Commute (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0))
          (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5)) :=
        e6Data_valid.nm_comm _ (by decide) (by decide)
      calc e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0) *
            e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5) *
            (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0) *
              e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5))
          = (e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0) *
              e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5)) ^ 2 :=
            (pow_two _).symm
        _ = e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 0) ^ 2 *
              e6Data_valid.nm (GaloisField 2 (2 * f)) (TwistedE6.nd 5) ^ 2 :=
            hcomm.mul_pow 2
        _ = 1 := by rw [pow_two, pow_two, ha, hb, mul_one]

theorem ggSecFivePres_of_psi_twistedE6 {p : ℕ} {B : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} (hadm : StatedLieAdmissible .twistedE6 n 2 f) (hrank : 3 ≤ bnRank .twistedE6 n)
    (ψ : (ggU .twistedE6 n f).K →* G) (hker : ψ.ker ≤ Subgroup.center (ggU .twistedE6 n f).K)
    (hrange : ψ.range = ggG0 p B x L D J) : GGSecFivePres p B x L D J .twistedE6 n f :=
  ggSecFivePres_of_psi_of_tagFacts hadm hrank (ggTagFacts_twistedE6 hadm hrank) ψ hker hrange

end Tag

end CFSG.StandardType

end
