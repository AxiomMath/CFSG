module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwoAux1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwoAux2
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJRowSpTwoAux3
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCommonJNativeDefs
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlock
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockZ
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusBlockZ2
import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryBlock
import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticFrameDimensions
import CFSG.LocalAnalysis.StandardType.GGQTwoSymplecticComponent
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourTwo
import CFSG.LocalAnalysis.StandardType.GGTBJOmAutomizerAux
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OSpThreeFixed2
import CFSG.LocalAnalysis.StandardType.GGTBJFrameCorank

public section

namespace CFSG.StandardType.CommonJSpTwo

open CFSG.Assembly
open CFSG.Open (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.StandardType.SpJoin
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
open Multiplicative Polynomial Module

theorem ggCommonJSpTwo_hcomp {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {r : ℕ}
    (hr : 3 ≤ r) {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    {f : Fin r → Multiplicative (ZMod 3)} {J : Subgroup (StatedSp r K)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({spPlaneTorus r ζ f} : Set (StatedSp r K))))
    (hcard : Nat.card ↥((spPlaneTorus r ζ).range ⊓
      Subgroup.centralizer (J : Set (StatedSp r K))) = 3) :
    (GGCoordDense f ∧ 4 ≤ r ∧ LargeEvenInLambda2 ⟨.twA, r - 1, 1⟩ ∧
        GGHasLabel ⟨.twA, r - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J) ∧
        ((⟨.twA, r - 1, 1⟩ : LargeEvenLabel) = ⟨.twA, 3, 1⟩ → Subgroup.center ↥J = ⊥)) ∨
      (GGCoordSparse f ∧
        ((4 ≤ r ∧ LargeEvenInLambda2 ⟨.C, r - 1, 1⟩ ∧
            GGHasLabel ⟨.C, r - 1, 1⟩ (↥J ⧸ Subgroup.center ↥J)) ∨
          (r = 3 ∧ LargeEvenInLambda2 ⟨.B2der, 0, 1⟩ ∧
            GGHasLabel ⟨.B2der, 0, 1⟩ (↥J ⧸ Subgroup.center ↥J)))) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  have hp : Nat.Prime 3 := by norm_num
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) (by simpa using hK)
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hq : 4 ≤ Nat.card K ∨ Nat.card K = 2 := Or.inr hK
  have hm3 : Nat.card K = 2 → 3 ≤ r := fun _ => hr
  have hinj : Function.Injective (spPlaneTorus r ζ) := TorC.spPlaneTorus_injective hζ r
  have hx3 : (spPlaneTorus r ζ f) ^ 3 = 1 := SympMinus.sympMinusZ_spPlaneTorus_pow ζ f
  have hcommJ : ∀ j ∈ J, j * spPlaneTorus r ζ f = spPlaneTorus r ζ f * j :=
    fun j hj => (Subgroup.mem_centralizer_iff.mp (hJ.1 hj) _ (Set.mem_singleton _)).symm
  rcases SympMinus.sympMinus_component_localize hp hp2 hpq hζ hζW f hJ with
    hsupp | ⟨c, hc, hsupp⟩
  ·
    rcases SympMinus.sympMinus_block_zero hq hm3 hp hp2 hpq hζ hζW f hJ hsupp with
      ⟨hS1, hAut, hfix, -⟩ | ⟨-, e, hblocks, hdim4, hJeq⟩
    ·
      set S : Finset (Fin r) := Finset.univ.filter fun i => f i = 1 with hS
      have hSmem : ∀ i, i ∈ S ↔ f i = 1 := fun i => by simp [hS]
      have hcount := ggCommonJSpTwo_count_signed (K := K) (r := r) (ζ := ζ) (J := J)
        (S := S) hζ hS1 (by simpa [hS] using hAut) hfix
      rw [hcard] at hcount
      have hdiff : r - S.card = 1 := by
        have hpow : 3 ^ (r - S.card) = 3 ^ 1 := by
          rw [pow_one]
          exact hcount.symm
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
      have hScard : S.card = r - 1 := by omega
      have hsparse : GGCoordSparse f := by
        have hSr : S.card ≤ r := by simpa using Finset.card_le_univ S
        have hcompl : Sᶜ.card = 1 := by
          rw [Finset.card_compl, Fintype.card_fin, hScard]
          omega
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
        refine ⟨i, fun j hj => ?_⟩
        have hjS : j ∈ S := by
          by_contra h
          have hmem : j ∈ Sᶜ := Finset.mem_compl.mpr h
          rw [hi] at hmem
          simp at hmem
          exact hj hmem
        exact (hSmem j).mp hjS
      exact Or.inr ⟨hsparse,
        ggCommonJSpTwo_label_sparse hK hr hζ hζW hJ hsparse hScard
          (by simpa [hS] using hAut)⟩
    ·
      set S : Finset (Fin r) := Finset.univ.filter fun i => f i = 1 with hS
      have hSmem : ∀ i, i ∈ S ↔ f i = 1 := fun i => by simp [hS]
      have hdim : 2 * S.card = 4 := by
        have h := (spFixedDim_spPlaneTorus hζ f).trans (by rw [Fintype.card_subtype])
        rw [← hS] at h
        omega
      have hScard : S.card = 2 := by omega
      have hSr : S.card ≤ r := by simpa using Finset.card_le_univ S
      have hlower : 3 ^ (r - S.card) ≤ Nat.card ↥((spPlaneTorus r ζ).range ⊓
          Subgroup.centralizer (J : Set (StatedSp r K))) := by
        have hinj' : Function.Injective
            (fun g : {g : Fin r → Multiplicative (ZMod 3) // ∀ i ∈ S, g i = 1} =>
              (⟨spPlaneTorus r ζ g.1,
                Subgroup.mem_inf.mpr
                  ⟨MonoidHom.mem_range.mpr ⟨g.1, rfl⟩,
                    Subgroup.mem_centralizer_iff.mpr fun j hj =>
                      (SympMinus.sympMinusZ_commute_of_fix ζ f hsupp g.1
                        (fun i hi => g.2 i ((hSmem i).mpr hi)) hj).symm⟩⟩ :
                ↥((spPlaneTorus r ζ).range ⊓
                  Subgroup.centralizer (J : Set (StatedSp r K))))) := by
          intro g g' hgg
          apply Subtype.ext
          exact hinj (congrArg (fun x : ↥((spPlaneTorus r ζ).range ⊓
            Subgroup.centralizer (J : Set (StatedSp r K))) => x.1) hgg)
        have hle := Nat.card_le_card_of_injective _ hinj'
        rwa [FrameBs.card_frame_trivial_on S] at hle
      rw [hcard] at hlower
      have hdiff : r - S.card ≤ 1 :=
        (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by simpa using hlower)
      have hr3 : r = 3 := by omega
      have hsparse : GGCoordSparse f := by
        have hcompl : Sᶜ.card = 1 := by
          rw [Finset.card_compl, Fintype.card_fin, hScard, hr3]
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcompl
        refine ⟨i, fun j hj => ?_⟩
        have hjS : j ∈ S := by
          by_contra h
          have hmem : j ∈ Sᶜ := Finset.mem_compl.mpr h
          rw [hi] at hmem
          simp at hmem
          exact hj hmem
        exact (hSmem j).mp hjS
      have hA6 : ∃ e : ℕ, SpPrimaryBlocks 2 e 3 (spPlaneTorus r ζ f)
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K
            (spPlaneTorus r ζ f)) ∧
          spFixedDim (spPlaneTorus r ζ f) = 4 ∧
          J = ⁅spFixedFactor (spPlaneTorus r ζ f),
            spFixedFactor (spPlaneTorus r ζ f)⁆ :=
        ⟨e, hblocks, hdim4, hJeq⟩
      exact Or.inr ⟨hsparse, Or.inr
        ⟨hr3, ggCommonJSpTwo_label_a6 hK hr3 hJ hsparse hA6⟩⟩
  ·
    have hs : ∀ i, (if f i = c then (1 : ZMod 3) else -1) *
        (if f i = c then (1 : ZMod 3) else -1) = 1 := by
      intro i
      split_ifs <;> simp
    obtain ⟨hS2, hunitary⟩ :=
      SympMinus.sympMinus_block_unitary hq hp hp2 hpq hζ hζW f hc hJ hsupp
    obtain ⟨hAut, hfix⟩ := hunitary hs
    set S : Finset (Fin r) := Finset.univ.filter fun i => f i = c ∨ f i = c⁻¹ with hS
    have hSmem : ∀ i, i ∈ S ↔ f i = c ∨ f i = c⁻¹ := fun i => by simp [hS]
    have hcount := ggCommonJSpTwo_count_twisted (K := K) (r := r) (ζ := ζ) (J := J)
      (S := S) (s := fun i => if f i = c then (1 : ZMod 3) else -1) hζ hs hS2
      (by simpa [hS] using hAut) hfix
    rw [hcard] at hcount
    have hdiff : r + 1 - S.card = 1 := by
      have hpow : 3 ^ (r + 1 - S.card) = 3 ^ 1 := by
        rw [pow_one]
        exact hcount.symm
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
    have hScard : S.card = r := by omega
    have hSuniv : S = Finset.univ := Finset.eq_univ_of_card _ (by simpa using hScard)
    have hdense : GGCoordDense f := by
      intro i
      have hi : i ∈ S := by rw [hSuniv]; exact Finset.mem_univ i
      refine ⟨?_, fun j => ?_⟩
      · rcases (hSmem i).mp hi with h | h
        · rw [h]; exact hc
        · rw [h]; exact inv_ne_one.mpr hc
      · have hj : j ∈ S := by rw [hSuniv]; exact Finset.mem_univ j
        rcases (hSmem i).mp hi with hi' | hi' <;>
          rcases (hSmem j).mp hj with hj' | hj'
        · exact Or.inl (by rw [hi', hj'])
        · exact Or.inr (by rw [hi', hj'])
        · exact Or.inr (by rw [hi', hj', inv_inv])
        · exact Or.inl (by rw [hi', hj'])
    rcases Nat.lt_or_ge r 4 with hlt | hge
    ·
      have hr3 : r = 3 := by omega
      have hfne : f ≠ 1 := by
        intro hf1
        have i0 : Fin r := ⟨0, by omega⟩
        exact (hdense i0).1 (congrFun hf1 i0)
      have hxne : spPlaneTorus r ζ f ≠ 1 :=
        SympMinus.sympMinusZ_spPlaneTorus_ne_one ζ hζ f hfne
      have hblocks : SpPrimaryBlocks 2 1 3 (spPlaneTorus r ζ f)
          (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj r K
            (spPlaneTorus r ζ f)) :=
        CFSG.LocalAnalysis.GLTheoremA.T173O.spPrimaryBlocks_of_order_three
          hK (by omega) hx3 hxne
      have hmem : SpFin.h3 K ∈ primaryFactors (spEnd (spPlaneTorus r ζ f)) :=
        SpFin.h3_mem_primaryFactors hK hx3 hxne
      have hS0 : (Finset.univ.filter fun i => f i = 1) = ∅ := by
        ext i
        simp [(hdense i).1]
      have hfixdim : spFixedDim (spPlaneTorus r ζ f) = 0 := by
        have h := (spFixedDim_spPlaneTorus hζ f).trans (by rw [Fintype.card_subtype])
        rw [h, hS0]
        simp
      have hkerdim : finrank K (LinearMap.ker (spEnd (spPlaneTorus r ζ f) - 1)) = 0 := by
        rw [← hblocks.fixed_eq]
        simpa [spFixedDim] using hfixdim
      have hrange : finrank K (LinearMap.range (spEnd (spPlaneTorus r ζ f) - 1)) = 2 * r := by
        have h := LinearMap.finrank_range_add_finrank_ker
          (spEnd (spPlaneTorus r ζ f) - 1)
        rw [hkerdim, Module.finrank_pi, Fintype.card_sum, Fintype.card_fin] at h
        omega
      have hmult : primaryMultiplicity (spEnd (spPlaneTorus r ζ f)) (SpFin.h3 K) = 3 := by
        haveI : Fact (Irreducible (SpFin.h3 K)) := ⟨SpFin.h3_irreducible hK⟩
        have h1 : finrank K (primaryComponent (spEnd (spPlaneTorus r ζ f)) (SpFin.h3 K)) =
            2 * r := by
          rw [SpFin.primaryComponent_h3 hK hx3, hrange]
        have h2 := finrank_primaryComponent (spEnd (spPlaneTorus r ζ f)) (SpFin.h3 K)
        rw [h1, SpFin.h3_natDegree] at h2
        change 2 * r = 2 * primaryMultiplicity (spEnd (spPlaneTorus r ζ f))
          (SpFin.h3 K) at h2
        omega
      haveI hUsolv : Group.IsSolvable
          ↥(spSupported (spPlaneTorus r ζ f) ({SpFin.h3 K} : Set K[X])) :=
        SpFour.selfDual_solvable_of_le hK hblocks hmem (by omega) (by omega)
      have hquadmem : SympMinus.smuQuad
          (((ζ c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace)
          ∈ primaryFactors (spEnd (spPlaneTorus r ζ f)) :=
        SympMinus.smuQuad_mem_primaryFactors hp hp2 hpq hζ f hc hSmem
          (Finset.card_pos.mp (by omega))
      have hquadeq : SympMinus.smuQuad
          (((ζ c : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).trace) =
          SpFin.h3 K := by
        have h := CFSG.LocalAnalysis.GLTheoremA.T173O.eq_quad_of_mem_primaryFactors
          hK hx3 hquadmem (SympMinus.smuQuad_ne_X_sub_one _)
        rw [SpFin.h3]
        exact h
      have hJU : J ≤ spSupported (spPlaneTorus r ζ f) ({SpFin.h3 K} : Set K[X]) := by
        intro j hj
        have hmemJ := SympMinus.smu_mem_spSupported_of_fix hp hp2 hpq hζ f hc hSmem
          (Finset.card_pos.mp (by omega)) (hcommJ j hj) (by
            intro v hv
            rw [hSuniv] at hv
            have hv0 : v = 0 := funext fun x => hv x (Finset.mem_univ (WitSpNs.plane x))
            simp [hv0])
        rwa [hquadeq] at hmemJ
      haveI : Group.IsSolvable ↥J :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJU)
          (Subgroup.inclusion_injective hJU)
      haveI : Nontrivial (↥J ⧸ Subgroup.center ↥J) := hJ.2.2.2.toNontrivial
      haveI : Nontrivial ↥J :=
        (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
      exact absurd hJ.2.2.1
        (ne_of_lt (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J))
    · rcases ggCommonJSpTwo_label_dense hK hge hζ hζW hJ hdense hs hScard
        (by simpa [hS] using hAut) with ⟨hLam, hLab, hZ⟩
      exact Or.inl ⟨hdense, hge, hLam, hLab, hZ⟩

end CFSG.StandardType.CommonJSpTwo

end
