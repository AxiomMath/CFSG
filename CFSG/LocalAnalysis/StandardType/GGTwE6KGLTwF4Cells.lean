module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTwF4
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.Foundations.QuasisimpleMulEquiv

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree

private theorem center_eq_bot_twF4Cell {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  haveI := hs
  obtain ⟨a, b, hab⟩ := hna
  exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R)).resolve_right fun h =>
    hab (Subgroup.mem_center_iff.mp (by rw [h]; exact Subgroup.mem_top b) a)

private theorem not_ggOutsideInndiag_of_conj_twF4Cell {R : Type} [Group R] {J : Subgroup R}
    {t : MulAut R} {P : LargeEvenMarkProp ↥J} (hM : LargeEvenMarking ↥J P) {z : R} (hz : z ∈ J)
    (hzt : ∀ j ∈ J, t j = z * j * z⁻¹) : ¬ GGOutsideInndiag J t := by
  rintro ⟨-, hout⟩
  obtain ⟨hJ, lab, hlab, hraw⟩ := hM
  have hM' : LargeEvenMarking ↥J fun _ R' _ I' _ θ =>
      ∃ φ ∈ Subgroup.closure I', LargeEvenInduces θ (fun l l' : ↥J => (l' : R) = t l) φ := by
    refine ⟨hJ, lab, hlab, largeEvenRawDatum_mono ?_ (largeEvenRawDatum_inn_all hraw)⟩
    rintro R' _ I' F' ⟨⟨hs, hna, θ, -⟩, hinn⟩
    refine ⟨hs, hna, θ, MulAut.conj (θ (QuotientGroup.mk ⟨z, hz⟩)),
      Subgroup.subset_closure (hinn ⟨_, rfl⟩), fun l l' hll' => ?_⟩
    have hl' : l' = ⟨z, hz⟩ * l * (⟨z, hz⟩ : ↥J)⁻¹ :=
      Subtype.ext (by rw [hll', hzt l l.2]; rfl)
    subst hl'
    simp only [MulAut.conj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_inv]
  obtain ⟨-, lab', -, hraw'⟩ := hout _ hM'
  obtain ⟨_, _, _, _, -, -, _, hPQ⟩ := largeEvenRawDatum_exists hraw'
  exact hPQ.2 hPQ.1

private theorem ggFix_conj_eq_centralizer_twF4Cell {G : Type*} [Group G] (x : G) :
    ggFix (MulAut.conj x) = Subgroup.centralizer {x} := by
  ext h
  rw [mem_ggFix, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff,
    mul_inv_eq_iff_eq_mul, eq_comm]

private theorem map_centralizer_twF4Cell {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (x : G) : (Subgroup.centralizer {x}).map e.toMonoidHom = Subgroup.centralizer {e x} := by
  ext g
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    simpa using congrArg e h
  · intro h
    apply e.injective
    simpa using h

private theorem isQuasisimple_ggFix_of_mulEquiv_twF4Cell {G G' : Type*} [Group G] [Group G']
    (e : G ≃* G') {x : G} (h : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({e x} : Set G'))) :
    CFSG.IsQuasisimple ↥(ggFix (MulAut.conj x)) :=
  CFSG.IsQuasisimple.of_mulEquiv (((MulEquiv.subgroupCongr
    (ggFix_conj_eq_centralizer_twF4Cell x)).trans (e.subgroupMap _)).trans
      (MulEquiv.subgroupCongr (map_centralizer_twF4Cell e x))) h

private theorem isQuasisimple_centralizer_reeGamma_twF4Cell {a : ℕ} (ha : 1 ≤ a) {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = 3) :
    CFSG.IsQuasisimple ↥(Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) := by
  obtain ⟨e⟩ :=
    CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hy
  have hFcard : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  exact CFSG.IsQuasisimple.of_mulEquiv e
    (CFSG.RankThree.PartTwo.Sec8.Item87Proof.isQuasisimple_statedSU_three
      (F := GaloisField 2 (2 * (2 * a + 1))) (f := 2 * a + 1) hFcard (by omega)).1

private theorem largeEvenLabelAll_isQuasisimple_ggFix_twF4Cell {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4) :
    LargeEvenLabelAll lab fun R _ _ _ => ∀ x : R, orderOf x = 3 →
      CFSG.IsQuasisimple ↥(ggFix (MulAut.conj x)) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  dsimp only at ht
  subst ht
  obtain ⟨-, -, h3⟩ := hl
  intro Q hQ
  refine recipeTwF4_and (P := fun R _ _ _ => ∀ x : R, orderOf x = 3 →
    CFSG.IsQuasisimple ↥(ggFix (MulAut.conj x))) (fun K _ _ hK x hx => ?_) hQ
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨e⟩ := TableBExcSmallRest.nonempty_twF4_equiv (by omega) K hK
  exact isQuasisimple_ggFix_of_mulEquiv_twF4Cell e
    (isQuasisimple_centralizer_reeGamma_twF4Cell (by omega) hK (e x)
      (by rw [MulEquiv.orderOf_eq]; exact hx))

theorem ggInndiagOnCompAt_twF4 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twF4) (P : ℕ → LargeEvenLabel → Prop) : GGInndiagOnCompAt lab P := by
  unfold GGInndiagOnCompAt
  refine (largeEvenLabelAll_and (largeEvenLabelAll_subset_inn_twF4 hlab htag)
    (largeEvenLabelAll_isQuasisimple_ggFix_twF4Cell hlab htag)).mono
    fun R _ I _ ⟨hinn, hq⟩ hR hna _ _ _ _ hs3 hs1 _ hst hsI htI _ J₁ hJ₁ hmark => ?_
  have hI : I ⊆ LargeEvenInnSet R := hinn hR hna
  have hinj := CFSG.mulAutConj_injective_of_center_eq_bot (center_eq_bot_twF4Cell hR hna)
  obtain ⟨x, rfl⟩ := hI hsI
  obtain ⟨w, rfl⟩ := hI htI
  have hx3 : x ^ 3 = 1 := hinj (by rw [map_pow, hs3, map_one])
  have hx1 : x ≠ 1 := fun h => hs1 (by rw [h, map_one])
  have hxw : x * w = w * x := hinj (by rw [map_mul, map_mul, hst])
  have hJ : J₁ = ggFix (MulAut.conj x) := GGHalf.eq_of_isComponentOf_isQuasisimple
    ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (hq x (orderOf_eq_prime hx3 hx1))) hJ₁
  have hw : w ∈ J₁ := by rw [hJ, mem_ggFix, MulAut.conj_apply, hxw, mul_inv_cancel_right]
  exact not_ggOutsideInndiag_of_conj_twF4Cell hmark hw fun j _ => MulAut.conj_apply w j

end CFSG.StandardType.SCFourCover

end
