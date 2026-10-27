module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.Open.StatedDefs
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal
import CFSG.LieType.Steinberg.CentralExt.SpinPlusCentrallyClosed
import CFSG.LieType.Steinberg.CentralExt.SpinMinusCentrallyClosed
import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
import CFSG.LocalAnalysis.StandardType.GGTBTorRelDCoverTwo
import CFSG.LocalAnalysis.SectionRank.SporadicCover
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.Assembly
open CFSG.SectionRank.EvenCover CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal

theorem center_eq_bot_of_statedOmegaPlus
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {n : ℕ} (hn : 3 ≤ n)
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ Subgroup.center L ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n K))) :
    Subgroup.center L = ⊥ := by
  obtain ⟨hsurj, hcen, -⟩ := pullbackFst_centralQuotientMap e
  set Φ : spinGroup (quadPlus n K) ≃*
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n K) :=
    spinMatrixEquiv (ker_spinMatrix_quadPlus_eq_bot (n := n) (K := K) CharTwo.two_eq_zero)
      (range_spinMatrix_quadPlus hn)
  have hker : (Φ.symm.toMonoidHom.comp
      (pullbackFst (centralQuotientMap e) (QuotientGroup.mk' _))).ker ≤
      Subgroup.center (pullback (centralQuotientMap e) (QuotientGroup.mk' _)) := by
    rw [ker_symm_comp]
    exact hcen
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed.spinPlus_exists_section_of_central
      (n := n) (K := K) hn hK (Φ.symm.surjective.comp hsurj) hker
  let σ : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadPlus n K) →*
      pullback (centralQuotientMap e) (QuotientGroup.mk' _) := s.comp Φ.symm.toMonoidHom
  have hσ : ∀ x, pullbackFst _ _ (σ x) = x := fun x => by
    apply Φ.symm.injective
    simpa [σ] using hs (Φ.symm x)
  obtain ⟨φ, -, -, hD⟩ := perfect_cover_map_of_section e σ hσ
  rw [← hD, statedScalars_subgroupOf_statedOmega_eq_bot (coe_quadPlus n K)
    (exists_map_ne_zero_of_hypPair _ (plusPair K (⟨0, by omega⟩ : Fin n))), Subgroup.map_bot]

theorem center_eq_bot_of_statedOmegaMinus
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (e : L ⧸ Subgroup.center L ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus n K b c))) :
    Subgroup.center L = ⊥ := by
  obtain ⟨hsurj, hcen, -⟩ := pullbackFst_centralQuotientMap e
  set Φ : spinGroup (quadMinus n K b c) ≃*
      CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus n K b c) :=
    spinMatrixEquiv (ker_spinMatrix_quadMinus_eq_bot (n := n) hirr CharTwo.two_eq_zero)
      (range_spinMatrix_quadMinus hn hirr)
  have hker : (Φ.symm.toMonoidHom.comp
      (pullbackFst (centralQuotientMap e) (QuotientGroup.mk' _))).ker ≤
      Subgroup.center (pullback (centralQuotientMap e) (QuotientGroup.mk' _)) := by
    rw [ker_symm_comp]
    exact hcen
  obtain ⟨s, hs⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.spinMinus_exists_section_of_central
      (n := n) (K := K) (b := b) (c := c) hirr hn hK
      (Φ.symm.surjective.comp hsurj) hker
  let σ : CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus n K b c) →*
      pullback (centralQuotientMap e) (QuotientGroup.mk' _) := s.comp Φ.symm.toMonoidHom
  have hσ : ∀ x, pullbackFst _ _ (σ x) = x := fun x => by
    apply Φ.symm.injective
    simpa [σ] using hs (Φ.symm x)
  obtain ⟨φ, -, -, hD⟩ := perfect_cover_map_of_section e σ hσ
  rw [← hD, statedScalars_subgroupOf_statedOmega_eq_bot (coe_quadMinus n K b c)
    (exists_map_ne_zero_of_hypPair _ (minusPair K b c (⟨0, by omega⟩ : Fin (n - 1)))),
    Subgroup.map_bot]

theorem center_eq_bot_of_hasLabel_orth
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {lab : LargeEvenLabel}
    (htag : lab.tag = .D ∨ lab.tag = .twD) (hrank : 4 ≤ lab.rank) (hn : 2 ≤ lab.n)
    (hL : GGHasLabel lab (L ⧸ Subgroup.center L)) : Subgroup.center L = ⊥ := by
  rcases lab with ⟨tag, rank, n⟩
  change 4 ≤ rank at hrank
  change 2 ≤ n at hn
  rcases htag with rfl | rfl
  · obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
      statedClassicalModel_of_hasLabel_typeD (n := rank) (f := n) hrank hL
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := by gcongr
    exact center_eq_bot_of_statedOmegaPlus (n := rank) h4 (by omega) e
  · obtain ⟨⟨-, -, -⟩, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ :=
      statedClassicalModel_of_hasLabel_typeTwD (n := rank) (f := n) hrank hL
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP K 2 := CFSG.SectionRank.ClassicalOdd.charP_of_card hK
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := by gcongr
    exact center_eq_bot_of_statedOmegaMinus (n := rank) (b := b) (c := c) h4 (by omega) hirr e

theorem center_eq_bot_of_hasLabel_orth_two
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L] {lab : LargeEvenLabel}
    (hrow : (lab.tag = .D ∧ 5 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank)) (hn : lab.n = 1)
    (hL : GGHasLabel lab (L ⧸ Subgroup.center L)) : Subgroup.center L = ⊥ := by
  have hperf : commutator L = ⊤ := Group.isPerfect_def.mp inferInstance
  rcases lab with ⟨tag, rank, n⟩
  change n = 1 at hn
  subst hn
  have hker : ∀ {R : Type} [Group R] (e : L ⧸ Subgroup.center L ≃* R),
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = Subgroup.center L := by
    intro R _ e
    ext z
    rw [MonoidHom.mem_ker]
    change e ((QuotientGroup.mk' (Subgroup.center L)) z) = 1 ↔ z ∈ Subgroup.center L
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  have hsurj : ∀ {R : Type} [Group R] (e : L ⧸ Subgroup.center L ≃* R),
      Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))) :=
    fun e => e.surjective.comp (QuotientGroup.mk'_surjective _)
  rcases hrow with ⟨htag, hr⟩ | ⟨htag, hr⟩
  · change tag = .D at htag
    change 5 ≤ rank at hr
    subst htag
    have hr3 : rank ≠ 3 := by omega
    have hraw := hL
    simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, if_neg hr3] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hraw
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by rw [hKcard]; norm_num
    have hinj := rPlus_injective_of_cover_two hK2 hr L _ (hsurj e) (hker e).le hperf
    rw [← hker e]
    exact (MonoidHom.ker_eq_bot_iff _).mpr hinj
  · change tag = .twD at htag
    change 4 ≤ rank at hr
    subst htag
    have hr2 : rank ≠ 2 := by omega
    have hr3 : rank ≠ 3 := by omega
    have hraw := hL
    simp only [GGHasLabel, CFSG.StandardType.LargeEvenRawDatum, if_neg hr2, if_neg hr3] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, b, c, hirr, ⟨e⟩⟩ := hraw
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by rw [hKcard]; norm_num
    have hinj := rMinus_injective_of_cover_two hK2 (by omega : 3 ≤ rank - 1) hirr L _
      (hsurj e) (hker e).le hperf
    rw [← hker e]
    exact (MonoidHom.ker_eq_bot_iff _).mpr hinj

end OrthTorus

end CFSG.StandardType

end
