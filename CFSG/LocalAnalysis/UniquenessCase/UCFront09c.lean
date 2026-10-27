module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeSolv
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.AGLEmbedding (KFactCatalogSchreier)

variable {G : Type} [Group G] [Finite G]

theorem pRank_le_inf_of_strong3 {M H : Subgroup G} (hM : IsStronglyPEmbedded 3 M)
    (h3 : 3 ∣ Nat.card ↥(H ⊓ M)) : CFSG.Open.pRank 3 H ≤ CFSG.Open.pRank 3 (H ⊓ M) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(H ⊓ M)) 3 h3
  set Q : Subgroup G := zpowers (x : G)
  have hQHM : Q ≤ H ⊓ M := zpowers_le.mpr x.2
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx]
  have hQ : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hQ1 : Q ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot.1 h, orderOf_one] at hxo
    norm_num at hxo
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := H)).exists_le_sylow
  set P : Subgroup G := (S : Subgroup ↥H).map H.subtype
  have hQP : Q ≤ P := fun y hy => ⟨⟨y, (hQHM hy).1⟩, hS (Subgroup.mem_subgroupOf.2 hy), rfl⟩
  have hPM : P ≤ M := by
    refine hM.le_of_isPGroup_inf (S.isPGroup'.map H.subtype) fun h => hQ1 (eq_bot_iff.2 ?_)
    rw [← h]
    exact le_inf hQP (hQHM.trans inf_le_right)
  calc CFSG.Open.pRank 3 H = CFSG.Open.pRank 3 (⊤ : Subgroup ↥H) :=
        CFSG.SectionRank.pRank_eq_pRank_top_subgroup H
    _ = CFSG.Open.pRank 3 (S : Subgroup ↥H) := (CFSG.SectionRank.pRank_sylow S).1.symm
    _ ≤ CFSG.Open.pRank 3 P :=
        CFSG.SectionRank.pRank_le_map (by norm_num) H.subtype H.subtype_injective _
    _ ≤ CFSG.Open.pRank 3 (H ⊓ M) :=
        CFSG.SectionRank.pRank_mono (by norm_num) (le_inf (map_subtype_le _) hPM)

theorem isSolvable_img9_of_strong3 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSch : KFactCatalogSchreier) (hK : CFSG.Open.IsKProper G) {M H : Subgroup G}
    (hM : IsStronglyPEmbedded 3 M) (hH : H ≠ ⊤) (hHM : ¬ H ≤ M)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (H ⊓ M)) :
    Group.IsSolvable ↥(img9 H (H ⊓ M)) :=
  CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.isSolvable_of_isStronglyPEmbedded_three hG3
    hSch
    (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient'
      (CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hK hH) (CFSG.pPrimeCore 3 ↥H))
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three)
    (CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.two_le_pRank_quotient_pPrimeCore Nat.prime_three
      h2)
    (CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.isStronglyPEmbedded_map_quotient_pPrimeCore
      Nat.prime_three hM hHM h2)

theorem isSolvable_of_img9 {H X : Subgroup G} (hXH : X ≤ H)
    (himg : Group.IsSolvable ↥(img9 H X)) (hXI : Group.IsSolvable ↥(X ⊓ I9 H)) :
    Group.IsSolvable ↥X := by
  let φ : ↥X →* ↥(img9 H X) :=
    { toFun := fun x => ⟨QuotientGroup.mk ⟨(x : G), hXH x.2⟩,
        ⟨⟨(x : G), hXH x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (inf_le_left : X ⊓ I9 H ≤ X)) φ ?_
  intro x hx
  have h1 : (⟨(x : G), hXH x.2⟩ : ↥H) ∈ CFSG.pPrimeCore 3 ↥H :=
    (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val hx)
  exact ⟨⟨(x : G), x.2, ⟨_, h1, rfl⟩⟩, rfl⟩

theorem pRank_le_one_of_strong3 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSch : KFactCatalogSchreier) (hK : CFSG.Open.IsKProper G) {M H X : Subgroup G}
    (hM : IsStronglyPEmbedded 3 M) (hH : H ≠ ⊤) (hHM : ¬ H ≤ M) (h3 : 3 ∣ Nat.card ↥(H ⊓ M))
    (hXHM : X ≤ H ⊓ M) (hX : ¬ Group.IsSolvable ↥X) (hXI : Group.IsSolvable ↥(X ⊓ I9 H)) :
    CFSG.Open.pRank 3 H ≤ 1 := by
  by_contra hlt
  have h2 : 2 ≤ CFSG.Open.pRank 3 (H ⊓ M) :=
    (Nat.lt_of_not_le hlt).trans_le (pRank_le_inf_of_strong3 hM h3)
  have hsol := isSolvable_img9_of_strong3 hG3 hSch hK hM hH hHM h2
  have himg : img9 H X ≤ img9 H (H ⊓ M) :=
    Subgroup.map_mono (Subgroup.comap_mono hXHM)
  have : Group.IsSolvable ↥(img9 H X) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion himg)
      (Subgroup.inclusion_injective himg)
  exact hX (isSolvable_of_img9 (hXHM.trans inf_le_left) this hXI)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
