module

public import CFSG.Quasithin.EmptyFaithful.Der6DAux
public import CFSG.Quasithin.Background.A3StructureBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise
open CFSG.Quasithin.C1Pack12
open CFSG.Quasithin.EmptyFaithfulMultiple

@[expose] def Insp15212 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M H L : Subgroup G), Setting152 T Mc M → IsHStar T M H →
    Nonempty (OTwoQuot H ≃* S152N.W3) → L ∈ cComp Mc → Mc ≤ Subgroup.normalizer (L : Set G) →
    conjClosure (oTwoUpper H) Mc = L →
    (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 3 1 ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3))) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 5 2 1) →
    ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsAutLnTwo n (OTwoQuot (L ⊔ T))

namespace Der6D

variable {G : Type} [Group G] [Finite G]

noncomputable def oTwoQuotEquiv (L : Subgroup G) : OTwoQuot L ≃* (↥L ⧸ CFSG.pCore 2 ↥L) :=
  QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥L).symm

omit [Finite G] in
theorem conjClosure_eq_sup_of_orbit {Mc L : Subgroup G} {t : G} (htMc : t ∈ Mc)
    (horb : conjSubgroupsBy Mc L = {L, conjByElt t L}) :
    conjClosure L Mc = L ⊔ conjByElt t L := by
  refine le_antisymm (conjClosure_le fun g hg z hz => ?_) (sup_le (le_conjClosure L Mc) ?_)
  · have hmem : conjByElt g L ∈ conjSubgroupsBy Mc L := ⟨g, hg, rfl⟩
    rw [horb] at hmem
    have hgz : g * z * g⁻¹ ∈ conjByElt g L := ⟨z, hz, rfl⟩
    rcases hmem with h | h
    · rw [h] at hgz
      exact Subgroup.mem_sup_left hgz
    · rw [Set.mem_singleton_iff] at h
      rw [h] at hgz
      exact Subgroup.mem_sup_right hgz
  · rintro _ ⟨z, hz, rfl⟩
    exact mem_conjClosure htMc hz

theorem conjClosure_eq_of_invariant {Mc K L P : Subgroup G} (hLc : L ∈ cComp Mc)
    (hLn : Mc ≤ Subgroup.normalizer (L : Set G)) (hKL : K ≤ L)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) (hPK : P ≤ K) (hP3 : IsPGroup 3 P)
    (hPne : P ≠ ⊥) : conjClosure K Mc = L := by
  have hLMc : L ≤ Mc := le_of_mem_cComp hLc
  have hle : conjClosure K Mc ≤ L := conjClosure_le fun g hg k hk =>
    (Subgroup.mem_normalizer_iff.mp (hLn hg) k).mp (hKL hk)
  refine eq_of_normal_of_not_le_pCoreOf (perfect_of_mem_cComp hLc) hq hZ hle
    (fun l hl n hn => (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K Mc (hLMc hl)) n).mp
      hn) ?_
  intro hQ
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hyL : (y : G) ∈ pCoreOf 2 L := hQ (le_conjClosure K Mc (hPK y.2))
  have hdis := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 L) hP3 (pCoreOf_isPGroup 2 L)
  have hy : (y : G) ∈ P ⊓ pCoreOf 2 L := ⟨y.2, hyL⟩
  rw [hdis.eq_bot, Subgroup.mem_bot] at hy
  exact hy1 (Subtype.ext hy)

theorem conjClosure_eq_sup_of_pair {Mc T K L P : Subgroup G} {t' : G} (hLc : L ∈ cComp Mc)
    (hTMc : T ≤ Mc) (ht'T : t' ∈ T) (hY : conjClosure L Mc = L ⊔ conjByElt t' L)
    (hKY : K ≤ conjClosure L T)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) (hPK : P ≤ K) (hP3 : IsPGroup 3 P)
    (hPL : P ⊓ L ≠ ⊥) : conjClosure K Mc = L ⊔ conjByElt t' L := by
  have hLMc : L ≤ Mc := le_of_mem_cComp hLc
  have hKY' : K ≤ conjClosure L Mc := hKY.trans (conjClosure_mono le_rfl hTMc)
  have hLK : L ≤ conjClosure K Mc := by
    have h := eq_of_normal_of_not_le_pCoreOf (perfect_of_mem_cComp hLc) hq hZ
      (inf_le_left : L ⊓ conjClosure K Mc ≤ L)
      (fun l hl n hn => ⟨L.mul_mem (L.mul_mem hl hn.1) (L.inv_mem hl),
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K Mc (hLMc hl)) n).mp hn.2⟩)
      (by
        intro hQ
        obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPL
        have hyL : (y : G) ∈ pCoreOf 2 L := hQ ⟨y.2.2, le_conjClosure K Mc (hPK y.2.1)⟩
        have hdis := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 L) hP3
          (pCoreOf_isPGroup 2 L)
        have hy : (y : G) ∈ P ⊓ pCoreOf 2 L := ⟨y.2.1, hyL⟩
        rw [hdis.eq_bot, Subgroup.mem_bot] at hy
        exact hy1 (Subtype.ext hy))
    exact inf_eq_left.mp h
  refine le_antisymm (conjClosure_le fun g hg k hk => ?_) (sup_le hLK ?_)
  · rw [← hY]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure L Mc hg) k).mp (hKY' hk)
  · rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure K Mc (hTMc ht'T)) z).mp
      (hLK hz)

end Der6D

end CFSG.Quasithin
