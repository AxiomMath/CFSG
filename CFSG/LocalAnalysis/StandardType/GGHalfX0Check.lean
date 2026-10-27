module

public import CFSG.LocalAnalysis.StandardType.GGHalfE6GlueCheck
public import CFSG.LocalAnalysis.StandardType.GGHalfX0Group
public import CFSG.LocalAnalysis.StandardType.GGHalfX0Bridge
public import CFSG.LocalAnalysis.StandardType.GGHalfX0Data
public import CFSG.LocalAnalysis.StandardType.GGHalfX0Kernel
public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.LocalAnalysis.StandardType.GGHalfX0KernelSound
public import CFSG.LocalAnalysis.StandardType.GGHalfGraphTheta
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi
public import CFSG.CGT.T75P.Chain4
public import CFSG.CGT.T75P.Aut
public import CFSG.CGT.Timmesfeld75.OddCenter
public import CFSG.CGT.Timmesfeld75.Sec5FiveEng
public import CFSG.CGT.Timmesfeld75.Sec5Nine
public import CFSG.CGT.Timmesfeld75.Step57Reduction
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open scoped Pointwise

private noncomputable def ggX0Endo
    (g : GGE6Two) :
    Module.End (GaloisField 2 1) (Fin 27 →₀ GaloisField 2 1) :=
  e6Data_valid.endo (GaloisField 2 1) g

private theorem ggX0Endo_one :
    ggX0Endo (1 : GGE6Two) = 1 :=
  e6Data_valid.endo_one (GaloisField 2 1)

private theorem ggX0Endo_mul
    (g h : GGE6Two) :
    ggX0Endo (g * h) = ggX0Endo g * ggX0Endo h :=
  e6Data_valid.endo_mul (GaloisField 2 1) g h

private instance : Finite (Fin e6Data.d → GaloisField 2 1) := inferInstance

private instance : Finite (Fin e6Data.d →₀ GaloisField 2 1) :=
  Finite.of_injective (fun v : Fin e6Data.d →₀ GaloisField 2 1 => (v : Fin e6Data.d → GaloisField 2 1))
    (fun v w h => Finsupp.ext (congrFun h))

private instance : Finite (Fin 27 → GaloisField 2 1) := inferInstance

private instance : Finite (Fin 27 →₀ GaloisField 2 1) :=
  Finite.of_injective (fun v : Fin 27 →₀ GaloisField 2 1 => (v : Fin 27 → GaloisField 2 1))
    (fun v w h => Finsupp.ext (congrFun h))

private instance : Finite (Module.End (GaloisField 2 1) (Fin e6Data.d →₀ GaloisField 2 1)) :=
  Finite.of_injective
    (fun f : Module.End (GaloisField 2 1) (Fin e6Data.d →₀ GaloisField 2 1) =>
      (f : (Fin e6Data.d →₀ GaloisField 2 1) → (Fin e6Data.d →₀ GaloisField 2 1)))
    (fun f g h => LinearMap.ext (congrFun h))

private instance : Finite ((Module.End (GaloisField 2 1) (Fin e6Data.d →₀ GaloisField 2 1))ˣ) :=
  Finite.of_injective
    (fun u : (Module.End (GaloisField 2 1) (Fin e6Data.d →₀ GaloisField 2 1))ˣ =>
      (u : Module.End (GaloisField 2 1) (Fin e6Data.d →₀ GaloisField 2 1)))
    Units.val_injective

private instance :
    Finite GGE6Two :=
  Finite.of_injective Subtype.val Subtype.val_injective

private noncomputable instance ggX0MulAction :
    MulAction GGE6Two (Fin 27 →₀ GaloisField 2 1) where
  smul g v := ggX0Endo g v
  one_smul v := by
    show ggX0Endo (1 : GGE6Two) v = v
    rw [ggX0Endo_one]; rfl
  mul_smul g h v := by
    show ggX0Endo (g * h) v = ggX0Endo g (ggX0Endo h v)
    rw [ggX0Endo_mul, Module.End.mul_apply]

private lemma ggX0_gf2_eq_zero_or_one (x : GaloisField 2 1) : x = 0 ∨ x = 1 := by
  classical
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by norm_num)
  haveI : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have h2 : Fintype.card (GaloisField 2 1) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact hF
  have hc : ({(0 : GaloisField 2 1), 1} : Finset (GaloisField 2 1)).card = 2 :=
    Finset.card_pair zero_ne_one
  have hun : ({(0 : GaloisField 2 1), 1} : Finset (GaloisField 2 1)) = Finset.univ := by
    apply Finset.eq_univ_of_card; rw [hc, h2]
  have : x ∈ ({(0 : GaloisField 2 1), 1} : Finset (GaloisField 2 1)) := by
    rw [hun]; exact Finset.mem_univ x
  simpa using this

private theorem card_J0_ge :
    20160 ≤ Nat.card (ggHalfM0.J0) := by
  classical
  obtain ⟨θ, hθinj, hθframe⟩ :=
    GGHalfE6Model.exists_theta ggHalfM0 .L ggHalfM0_good.1
  have hmap : (GGHalf.slOn 6 {i : Fin 6 | 2 ≤ i.val}).map θ ≤ ggHalfM0.J0 := by
    rw [GGHalf.slOn, MonoidHom.map_closure]
    refine (Subgroup.closure_le (ggHalfM0.J0)).2 ?_
    rintro t ⟨g, hg, rfl⟩
    rcases hg with ⟨a, b, hab, c, ha, hb, rfl⟩
    rcases ggX0_gf2_eq_zero_or_one c with rfl | rfl
    · rw [SpecialLinearGroup.transvection_coeff_zero, map_one]
      exact Subgroup.one_mem (ggHalfM0.J0)
    · have hslE : slE a b = SpecialLinearGroup.transvection hab 1 := by
        rw [slE, dif_neg hab]
      rw [← hslE, hθframe a b hab]
      refine Subgroup.subset_closure ⟨GGHalfBlk.lab .L a, GGHalfBlk.lab .L b, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · simpa [GGHalfBlk.lab, GGHalfBlk.off] using ha
      · simp only [GGHalfBlk.lab, GGHalfBlk.off]; omega
      · simpa [GGHalfBlk.lab, GGHalfBlk.off] using hb
      · simp only [GGHalfBlk.lab, GGHalfBlk.off]; omega
      · intro h
        apply hab
        apply Fin.ext
        simpa [GGHalfBlk.lab, GGHalfBlk.off] using congrArg Fin.val h
  have hslOn : 20160 ≤ Nat.card (GGHalf.slOn 6 {i : Fin 6 | 2 ≤ i.val}) := by
    rw [← GGHalf.range_slLower2Hom 3]
    calc 20160 = Nat.card (SpecialLinearGroup (Fin 4) (GaloisField 2 1)) :=
          CFSG.CGT.T75P.card_SL_four_two.symm
      _ ≤ Nat.card (GGHalf.slLower2Hom 3).range :=
          Nat.card_le_card_of_injective
            (fun x : SpecialLinearGroup (Fin 4) (GaloisField 2 1) =>
              (⟨GGHalf.slLower2Hom 3 x, ⟨x, rfl⟩⟩ : (GGHalf.slLower2Hom 3).range))
            (fun x y hxy => GGHalf.slLower2Hom_injective 3 (Subtype.ext_iff.mp hxy))
  have hcardmap : Nat.card ((GGHalf.slOn 6 {i : Fin 6 | 2 ≤ i.val}).map θ) =
      Nat.card (GGHalf.slOn 6 {i : Fin 6 | 2 ≤ i.val}) :=
    Subgroup.card_map_of_injective hθinj
  calc 20160 ≤ Nat.card ((GGHalf.slOn 6 {i : Fin 6 | 2 ≤ i.val}).map θ) := by
        rw [hcardmap]; exact hslOn
    _ ≤ Nat.card (ggHalfM0.J0) :=
        Nat.card_le_card_of_injective
          (fun x : ↥((GGHalf.slOn 6 {i : Fin 6 | 2 ≤ i.val}).map θ) =>
            (⟨x.1, hmap x.2⟩ : ↥ggHalfM0.J0))
          (fun x y hxy => Subtype.ext (congrArg (fun z : ↥ggHalfM0.J0 => (z : GGE6Two)) hxy))

private noncomputable def ggX0GensG
    (D : GGHalfX0Data) (i : ℕ) :
    GGE6Two :=
  let r := ggHalfWord D.rWord
  if i < 12 then ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD i 0))
  else r * ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD (i - 12) 0)) * r

private noncomputable def ggX0GensList
    (D : GGHalfX0Data) : List GGE6Two :=
  (List.range 24).map (ggX0GensG D)

private noncomputable def ggX0WordG
    (D : GGHalfX0Data) (w : List ℕ) : GGE6Two :=
  w.foldl (fun A i => A * (ggX0GensList D).getD i 1) 1

private theorem ggX0J0Idx_getD_lt {i : ℕ} (hi : i < 24) : ggHalfX0J0Idx.getD i 0 < 72 := by
  interval_cases i <;> decide

private theorem ggX0GensList_length
    (D : GGHalfX0Data) : (ggX0GensList D).length = 24 := by
  rw [ggX0GensList, List.length_map, List.length_range]

private theorem ggX0GensBits_length (D : GGHalfX0Data) : (ggHalfX0GensBits D).length = 24 := by
  simp [ggHalfX0GensBits, ggHalfX0J0GensBits, ggHalfX0J0Idx]

private theorem ggX0GensList_getD_lt
    (D : GGHalfX0Data) {i : ℕ} (hi : i < 24) :
    (ggX0GensList D).getD i 1 = ggX0GensG D i := by
  interval_cases i <;> rfl

private theorem ggX0GensBits_getD_lt (D : GGHalfX0Data) {i : ℕ} (hi : i < 12) :
    (ggHalfX0GensBits D).getD i ggHalfIdBits =
      ggHalfRootBits (ggHalfX0J0Idx.getD i 0) := by
  interval_cases i <;> rfl

private theorem ggX0GensBits_getD_ge (D : GGHalfX0Data) {i : ℕ} (h12 : 12 ≤ i) (hi : i < 24) :
    (ggHalfX0GensBits D).getD i ggHalfIdBits =
      ggHalfMulBits (ggHalfMulBits (ggHalfWordBits D.rWord)
        (ggHalfRootBits (ggHalfX0J0Idx.getD (i - 12) 0))) (ggHalfWordBits D.rWord) := by
  interval_cases i <;> rfl

private theorem ggX0GensG_bits
    (D : GGHalfX0Data)
    (hr : ∀ k ∈ D.rWord, k < 72) {i : ℕ} (hi : i < 24) :
    ggE6Bits (ggX0GensG D i) = (ggHalfX0GensBits D).getD i ggHalfIdBits := by
  by_cases h12 : i < 12
  · rw [ggX0GensG, if_pos h12, ggE6Bits_x (ggX0J0Idx_getD_lt hi),
      ggX0GensBits_getD_lt D h12]
  · rw [ggX0GensG, if_neg h12]
    rw [ggE6Bits_mul, ggE6Bits_mul, ggE6Bits_x (ggX0J0Idx_getD_lt (i := i - 12) (by omega)),
      ggE6Bits_word hr, ggX0GensBits_getD_ge D (by omega) hi]

private theorem ggX0GensList_bits
    (D : GGHalfX0Data)
    (hr : ∀ k ∈ D.rWord, k < 72) (i : ℕ) :
    ggE6Bits ((ggX0GensList D).getD i 1) = (ggHalfX0GensBits D).getD i ggHalfIdBits := by
  by_cases hi : i < 24
  · rw [ggX0GensList_getD_lt D hi, ggX0GensG_bits D hr hi]
  · have hge : 24 ≤ i := by omega
    rw [List.getD_eq_default (l := ggX0GensList D) (d := 1) (n := i)
        (by rw [ggX0GensList_length]; exact hge),
      List.getD_eq_default (l := ggHalfX0GensBits D) (d := ggHalfIdBits) (n := i)
        (by rw [ggX0GensBits_length]; exact hge)]
    exact ggE6Bits_one

private theorem ggE6Bits_foldl_list
    (gen : List GGE6Two)
    (gens : List (List ℕ)) (hgen : ∀ i, ggE6Bits (gen.getD i 1) = gens.getD i ggHalfIdBits)
    (X : GGE6Two) (w : List ℕ) :
    ggE6Bits (w.foldl (fun A i => A * gen.getD i 1) X) =
      w.foldl (fun A i => ggHalfMulBits A (gens.getD i ggHalfIdBits)) (ggE6Bits X) := by
  induction w generalizing X with
  | nil => rfl
  | cons i w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (X * gen.getD i 1), ggE6Bits_mul, hgen i]

private theorem ggX0WordG_bits
    (D : GGHalfX0Data)
    (hr : ∀ k ∈ D.rWord, k < 72) (w : List ℕ) :
    ggE6Bits (ggX0WordG D w) = ggHalfX0MatOfGens (ggHalfX0GensBits D) w := by
  rw [ggX0WordG]
  rw [ggE6Bits_foldl_list (ggX0GensList D) (ggHalfX0GensBits D) (ggX0GensList_bits D hr) 1 w,
      ggE6Bits_one]
  rfl

private def ggX0CBits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens (ggHalfX0GensBits D) D.cGen

private def ggX0DBits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens (ggHalfX0GensBits D) D.dGen

private def ggX0ZBits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens (ggHalfX0GensBits D) D.zGen

private def ggX0ABits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens ggHalfX0J0GensBits D.aJ

private def ggX0BBits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens ggHalfX0J0GensBits D.bJ

private def ggX0ARBits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens ggHalfX0J0GensBits D.aJr

private def ggX0BRBits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens ggHalfX0J0GensBits D.bJr

private def ggX0SymBits (D : GGHalfX0Data) : List (List ℕ) :=
  [ggX0ABits D, ggX0BBits D, ggHalfX0MatPow (ggX0ABits D) 59,
    ggHalfX0MatPow (ggX0BBits D) 59]

private def ggX0PBits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens (ggX0SymBits D) D.pa

private def ggX0QBits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens (ggX0SymBits D) D.qa

private def ggX0P'Bits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens (ggX0SymBits D) D.pb

private def ggX0Q'Bits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens (ggX0SymBits D) D.qb

private def ggX0E3Bits (D : GGHalfX0Data) : List ℕ :=
  ggHalfX0MatOfGens (ggX0SymBits D) D.e3

private def ggX0CheapFacts (D : GGHalfX0Data) : Prop :=
  ggHalfWordBits (D.rWord ++ D.rWord) = ggHalfIdBits ∧
  ggHalfWordBits (D.rWord ++ D.uWord) = ggHalfWordBits (D.uWord ++ D.rWord) ∧
  ggHalfX0MatPow (ggX0CBits D) 3 = ggHalfIdBits ∧
  ggX0CBits D ≠ ggHalfIdBits ∧
  (List.range 12).all (fun i => decide (ggHalfMulBits (ggX0CBits D)
      (ggHalfX0J0GensBits.getD i ggHalfIdBits) =
      ggHalfMulBits (ggHalfX0J0GensBits.getD i ggHalfIdBits) (ggX0CBits D))) = true ∧
  ggHalfApplyBits (ggX0CBits D) (ggHalfX0W0.getD D.cWit 0) ≠
    ggHalfX0W0.getD D.cWit 0 ∧
  ggHalfMulBits (ggX0DBits D) (ggX0CBits D) =
    ggHalfMulBits (ggHalfMulBits (ggX0CBits D) (ggX0CBits D)) (ggX0DBits D) ∧
  (List.range 12).all (fun i => ggHalfX0W0.all (fun b =>
      decide (ggHalfApplyBits (ggHalfX0J0GensBits.getD i ggHalfIdBits) b ∈
        ggHalfX0SpanMasks ggHalfX0W0))) = true ∧
  ggHalfX0W0.all (fun b => decide (ggHalfApplyBits (ggX0CBits D) b ∈
      ggHalfX0SpanMasks ggHalfX0W0)) = true ∧
  ggHalfX0W0.all (fun b => decide (ggHalfApplyBits (ggX0DBits D) b ∈
      ggHalfX0SpanMasks ggHalfX0W0)) = true ∧
  ggHalfX0MatPow (ggX0ZBits D) 17 = ggHalfIdBits ∧
  ggX0ZBits D ≠ ggHalfIdBits ∧
  ggHalfMulBits (ggX0ZBits D) (ggHalfX0J0GensBits.getD D.zj ggHalfIdBits) ≠
    ggHalfMulBits (ggHalfX0J0GensBits.getD D.zj ggHalfIdBits) (ggX0ZBits D) ∧
  ggHalfX0MatPow (ggX0ABits D) 60 = ggHalfIdBits ∧
  ggHalfX0MatPow (ggX0BBits D) 60 = ggHalfIdBits ∧
  ggHalfMulBits (ggHalfWordBits D.rWord) (ggHalfMulBits (ggX0ARBits D)
      (ggHalfWordBits D.rWord)) = ggX0ABits D ∧
  ggHalfMulBits (ggHalfWordBits D.rWord) (ggHalfMulBits (ggX0BRBits D)
      (ggHalfWordBits D.rWord)) = ggX0BBits D ∧
  ggHalfMulBits (ggX0PBits D) (ggX0QBits D) =
    ggHalfMulBits (ggHalfMulBits (ggX0ABits D) (ggX0QBits D)) (ggX0PBits D) ∧
  ggHalfMulBits (ggX0P'Bits D) (ggX0Q'Bits D) =
    ggHalfMulBits (ggHalfMulBits (ggX0BBits D) (ggX0Q'Bits D)) (ggX0P'Bits D) ∧
  ggHalfX0MatPow (ggX0E3Bits D) 3 = ggHalfIdBits ∧
  ggX0E3Bits D ≠ ggHalfIdBits

private def ggX0TreeOK : List ℕ → ℕ → Bool
  | [], _ => true
  | t :: ts, j => if (t / 24 < j + 1) then ggX0TreeOK ts (j + 1) else false

private def ggX0TreeFacts (D : GGHalfX0Data) : Prop :=
  ggX0TreeOK D.tree.tail 0 = true

private def ggX0SubFacts (D : GGHalfX0Data) : Prop :=
  ggHalfX0CheckDistinctLength (ggHalfX0SubKeys D) 1632 = true ∧
  (ggHalfX0SubBases D).all (fun b => ggHalfX0CheckNodup (ggHalfX0SpanMasks b)) = true ∧
  ggX0TreeFacts D

private theorem ggX0CheapFacts_P : ggX0CheapFacts ggHalfX0DataP := by
  unfold ggX0CheapFacts
  decide +kernel

private theorem ggX0CheapFacts_N : ggX0CheapFacts ggHalfX0DataN := by
  unfold ggX0CheapFacts
  decide +kernel

private theorem ggX0SubFacts_P : ggX0SubFacts ggHalfX0DataP := by
  have h := ggHalfX0CheckSubOrbit_P
  have h' : (ggHalfX0CheckDistinctLength (ggHalfX0SubKeys ggHalfX0DataP) 1632 = true) ∧
      (ggHalfX0SubBases ggHalfX0DataP).all
        (fun b => ggHalfX0CheckNodup (ggHalfX0SpanMasks b)) = true := by
    simpa only [ggHalfX0CheckSubOrbit, Bool.and_eq_true] using h
  exact ⟨h'.1, h'.2, by unfold ggX0TreeFacts; decide +kernel⟩

private theorem ggX0SubFacts_N : ggX0SubFacts ggHalfX0DataN := by
  have h := ggHalfX0CheckSubOrbit_N
  have h' : (ggHalfX0CheckDistinctLength (ggHalfX0SubKeys ggHalfX0DataN) 1632 = true) ∧
      (ggHalfX0SubBases ggHalfX0DataN).all
        (fun b => ggHalfX0CheckNodup (ggHalfX0SpanMasks b)) = true := by
    simpa only [ggHalfX0CheckSubOrbit, Bool.and_eq_true] using h
  exact ⟨h'.1, h'.2, by unfold ggX0TreeFacts; decide +kernel⟩

private def ggX0Bounds (D : GGHalfX0Data) : Prop :=
  (D.rWord.all (fun k => k < 72)) = true ∧ (D.uWord.all (fun k => k < 72)) = true ∧
  (D.cGen.all (fun k => k < 24)) = true ∧ (D.dGen.all (fun k => k < 24)) = true ∧
  (D.zGen.all (fun k => k < 24)) = true ∧
  (D.aJ.all (fun k => k < 12)) = true ∧ (D.bJ.all (fun k => k < 12)) = true ∧
  (D.aJr.all (fun k => k < 12)) = true ∧ (D.bJr.all (fun k => k < 12)) = true ∧
  (D.pa.all (fun k => k < 4)) = true ∧ (D.qa.all (fun k => k < 4)) = true ∧
  (D.pb.all (fun k => k < 4)) = true ∧ (D.qb.all (fun k => k < 4)) = true ∧
  (D.e3.all (fun k => k < 4)) = true ∧ D.cWit < 5 ∧ D.zj < 12

private theorem ggX0Bounds_P : ggX0Bounds ggHalfX0DataP := by unfold ggX0Bounds; decide

private theorem ggX0Bounds_N : ggX0Bounds ggHalfX0DataN := by unfold ggX0Bounds; decide

private theorem ggX0Bounds_rWord {D : GGHalfX0Data} (h : ggX0Bounds D) :
    ∀ k ∈ D.rWord, k < 72 :=
  fun k hk => of_decide_eq_true (List.all_eq_true.mp h.1 k hk)

private theorem ggX0Bounds_uWord {D : GGHalfX0Data} (h : ggX0Bounds D) :
    ∀ k ∈ D.uWord, k < 72 :=
  fun k hk => of_decide_eq_true (List.all_eq_true.mp h.2.1 k hk)

private theorem ggX0Bounds_aJ {D : GGHalfX0Data} (h : ggX0Bounds D) :
    ∀ k ∈ D.aJ, k < 12 := by
  obtain ⟨-, -, -, -, -, ha, -, -, -, -, -, -, -, -, -, -⟩ := h
  exact fun k hk => of_decide_eq_true (List.all_eq_true.mp ha k hk)

private theorem ggX0Bounds_bJ {D : GGHalfX0Data} (h : ggX0Bounds D) :
    ∀ k ∈ D.bJ, k < 12 := by
  obtain ⟨-, -, -, -, -, -, hb, -, -, -, -, -, -, -, -, -⟩ := h
  exact fun k hk => of_decide_eq_true (List.all_eq_true.mp hb k hk)

private theorem ggX0Bounds_aJr {D : GGHalfX0Data} (h : ggX0Bounds D) :
    ∀ k ∈ D.aJr, k < 12 := by
  obtain ⟨-, -, -, -, -, -, -, ha, -, -, -, -, -, -, -, -⟩ := h
  exact fun k hk => of_decide_eq_true (List.all_eq_true.mp ha k hk)

private theorem ggX0Bounds_bJr {D : GGHalfX0Data} (h : ggX0Bounds D) :
    ∀ k ∈ D.bJr, k < 12 := by
  obtain ⟨-, -, -, -, -, -, -, -, hb, -, -, -, -, -, -, -⟩ := h
  exact fun k hk => of_decide_eq_true (List.all_eq_true.mp hb k hk)

private theorem ggX0_charTwo (x : GaloisField 2 1) : x + x = 0 := by
  have h2 : (2 : GaloisField 2 1) = 0 := CharTwo.two_eq_zero
  calc x + x = (2 : ℕ) • x := (two_nsmul x).symm
    _ = (2 : GaloisField 2 1) • x := nsmul_eq_mul 2 x
    _ = 0 := by rw [h2, zero_smul]

private theorem ggE6x_mul_self'
    (δ : GGE6Root) :
    ggE6x δ * ggE6x δ = 1 := by
  change e6Data_valid.xm (GaloisField 2 1) δ 1 * e6Data_valid.xm (GaloisField 2 1) δ 1 = 1
  rw [← e6Data_valid.xm_add]
  have h : (1 : GaloisField 2 1) + 1 = 0 := ggX0_charTwo 1
  rw [h, e6Data_valid.xm_zero]

private theorem ggHalfWord_singleton_70 :
    ggHalfWord [70] = ggE6x (e6Certificate.root 70) := by
  apply ggE6Bits_injective
  rw [ggE6Bits_word (w := [70]) (by decide), ggE6Bits_x (by decide)]
  decide

private theorem ggHalfWord_singleton_71 :
    ggHalfWord [71] = ggE6x (e6Certificate.root 71) := by
  apply ggE6Bits_injective
  rw [ggE6Bits_word (w := [71]) (by decide), ggE6Bits_x (by decide)]
  decide

private theorem ggHalfWord_singleton_6 :
    ggHalfWord [6] = ggE6x (e6Certificate.root 6) := by
  apply ggE6Bits_injective
  rw [ggE6Bits_word (w := [6]) (by decide), ggE6Bits_x (by decide)]
  decide

private theorem ggHalfWord_singleton_0 :
    ggHalfWord [0] = ggE6x (e6Certificate.root 0) := by
  apply ggE6Bits_injective
  rw [ggE6Bits_word (w := [0]) (by decide), ggE6Bits_x (by decide)]
  decide

private theorem hu_P :
    ggHalfWord ggHalfX0DataP.uWord =
      ggE6u (ggHalfM0.frame .L 0 1) * ggE6u (ggHalfM0.frame .K 6 7) ^ (1 : ℤ) := by
  have h01 : ggHalfM0.frame .L 0 1 = e6Certificate.root 70 := by decide
  have h10 : ggHalfM0.frame .L 1 0 = e6Certificate.root 71 := by decide
  have h67 : ggHalfM0.frame .K 6 7 = e6Certificate.root 6 := by decide
  have h76 : ggHalfM0.frame .K 7 6 = e6Certificate.root 0 := by decide
  have hnegL : ggHalfM0.frame .L 1 0 = - ggHalfM0.frame .L 0 1 := by decide
  have hnegK : ggHalfM0.frame .K 7 6 = - ggHalfM0.frame .K 6 7 := by decide
  have h71 : e6Certificate.root 71 = - ggHalfM0.frame .L 0 1 := by rw [← h10]; exact hnegL
  have h0 : e6Certificate.root 0 = - ggHalfM0.frame .K 6 7 := by rw [← h76]; exact hnegK
  have hsplit : ggHalfWord ggHalfX0DataP.uWord =
      ggHalfWord [70] * (ggHalfWord [71] * (ggHalfWord [6] * ggHalfWord [0])) := by
    rw [show ggHalfX0DataP.uWord = [70, 71, 6, 0] from rfl]
    rw [show ([70, 71, 6, 0] : List ℕ) = [70] ++ [71] ++ [6] ++ [0] from rfl]
    rw [ggHalfWord_append, ggHalfWord_append, ggHalfWord_append]
    group
  rw [hsplit, ggHalfWord_singleton_70, ggHalfWord_singleton_71, ggHalfWord_singleton_6,
    ggHalfWord_singleton_0, h71, h0, h01, h67]
  simp only [ggE6u, zpow_one]
  group

private theorem hu_N :
    ggHalfWord ggHalfX0DataN.uWord =
      ggE6u (ggHalfM0.frame .L 0 1) * ggE6u (ggHalfM0.frame .K 6 7) ^ (-1 : ℤ) := by
  have h01 : ggHalfM0.frame .L 0 1 = e6Certificate.root 70 := by decide
  have h10 : ggHalfM0.frame .L 1 0 = e6Certificate.root 71 := by decide
  have h67 : ggHalfM0.frame .K 6 7 = e6Certificate.root 6 := by decide
  have h76 : ggHalfM0.frame .K 7 6 = e6Certificate.root 0 := by decide
  have hnegL : ggHalfM0.frame .L 1 0 = - ggHalfM0.frame .L 0 1 := by decide
  have hnegK : ggHalfM0.frame .K 7 6 = - ggHalfM0.frame .K 6 7 := by decide
  have h71 : e6Certificate.root 71 = - ggHalfM0.frame .L 0 1 := by rw [← h10]; exact hnegL
  have h0 : e6Certificate.root 0 = - ggHalfM0.frame .K 6 7 := by rw [← h76]; exact hnegK
  have hsplit : ggHalfWord ggHalfX0DataN.uWord =
      ggHalfWord [70] * (ggHalfWord [71] * (ggHalfWord [0] * ggHalfWord [6])) := by
    rw [show ggHalfX0DataN.uWord = [70, 71, 0, 6] from rfl]
    rw [show ([70, 71, 0, 6] : List ℕ) = [70] ++ [71] ++ [0] ++ [6] from rfl]
    rw [ggHalfWord_append, ggHalfWord_append, ggHalfWord_append]
    group
  rw [hsplit, ggHalfWord_singleton_70, ggHalfWord_singleton_71, ggHalfWord_singleton_0,
    ggHalfWord_singleton_6, h71, h0, h01, h67]
  simp only [ggE6u, _root_.zpow_neg, zpow_one, _root_.mul_inv_rev,
    inv_eq_of_mul_eq_one_right (ggE6x_mul_self' (e6Certificate.root 6)),
    inv_eq_of_mul_eq_one_right (ggE6x_mul_self' (- e6Certificate.root 6))]
  group

private theorem ggX0_foldl_congr {α : Type} {f f' : ℕ → α → α} (w : List ℕ) :
    (∀ i ∈ w, ∀ A, f i A = f' i A) → ∀ A,
      w.foldl (fun A i => f i A) A = w.foldl (fun A i => f' i A) A := by
  induction w with
  | nil => intro _ A; rfl
  | cons i t ih =>
    intro h A
    rw [List.foldl_cons, List.foldl_cons, h i (List.mem_cons_self ..) A]
    exact ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) _

private theorem ggHalfX0MatOfGens_congr (gens gens' : List (List ℕ)) (w : List ℕ)
    (h : ∀ i ∈ w, gens.getD i ggHalfIdBits = gens'.getD i ggHalfIdBits) :
    ggHalfX0MatOfGens gens w = ggHalfX0MatOfGens gens' w :=
  ggX0_foldl_congr w (fun i hi A => by rw [h i hi]) ggHalfIdBits

private theorem ggX0J0GensBits_getD {i : ℕ} (hi : i < 12) :
    ggHalfX0J0GensBits.getD i ggHalfIdBits = ggHalfRootBits (ggHalfX0J0Idx.getD i 0) := by
  interval_cases i <;> rfl

private theorem ggX0MatOfGens_J0_eq (D : GGHalfX0Data) (w : List ℕ)
    (hw : ∀ i ∈ w, i < 12) :
    ggHalfX0MatOfGens (ggHalfX0GensBits D) w = ggHalfX0MatOfGens ggHalfX0J0GensBits w :=
  ggHalfX0MatOfGens_congr _ _ _ fun i hi =>
    (ggX0GensBits_getD_lt D (hw i hi)).trans (ggX0J0GensBits_getD (hw i hi)).symm

private theorem ggX0_rWord_append_lt {D : GGHalfX0Data} (h : ggX0Bounds D) :
    ∀ k ∈ D.rWord ++ D.rWord, k < 72 := by
  intro k hk
  rw [List.mem_append] at hk
  exact hk.elim (ggX0Bounds_rWord h k) (ggX0Bounds_rWord h k)

private theorem ggX0_rWord_sq
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (hc : ggHalfWordBits (D.rWord ++ D.rWord) = ggHalfIdBits) :
    ggHalfWord D.rWord * ggHalfWord D.rWord = 1 := by
  have h1 := ggE6Bits_word (w := D.rWord ++ D.rWord) (ggX0_rWord_append_lt h)
  rw [ggHalfWord_append, hc] at h1
  exact ggE6Bits_injective (by rw [h1, ggE6Bits_one])

private theorem ggX0_rWord_inv
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (hc : ggHalfWordBits (D.rWord ++ D.rWord) = ggHalfIdBits) :
    (ggHalfWord D.rWord)⁻¹ = ggHalfWord D.rWord :=
  inv_eq_of_mul_eq_one_right (ggX0_rWord_sq D h hc)

private theorem ggX0J0Idx_mem
    (i : ℕ) (hi : i < 12) :
    ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD i 0)) ∈ ggHalfM0.J0 := by
  interval_cases i
  · refine Subgroup.subset_closure ⟨2, 3, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 2 3 = e6Certificate.root (ggHalfX0J0Idx.getD 0 0) from by decide]
  · refine Subgroup.subset_closure ⟨2, 4, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 2 4 = e6Certificate.root (ggHalfX0J0Idx.getD 1 0) from by decide]
  · refine Subgroup.subset_closure ⟨2, 5, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 2 5 = e6Certificate.root (ggHalfX0J0Idx.getD 2 0) from by decide]
  · refine Subgroup.subset_closure ⟨3, 2, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 3 2 = e6Certificate.root (ggHalfX0J0Idx.getD 3 0) from by decide]
  · refine Subgroup.subset_closure ⟨3, 4, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 3 4 = e6Certificate.root (ggHalfX0J0Idx.getD 4 0) from by decide]
  · refine Subgroup.subset_closure ⟨3, 5, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 3 5 = e6Certificate.root (ggHalfX0J0Idx.getD 5 0) from by decide]
  · refine Subgroup.subset_closure ⟨4, 2, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 4 2 = e6Certificate.root (ggHalfX0J0Idx.getD 6 0) from by decide]
  · refine Subgroup.subset_closure ⟨4, 3, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 4 3 = e6Certificate.root (ggHalfX0J0Idx.getD 7 0) from by decide]
  · refine Subgroup.subset_closure ⟨4, 5, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 4 5 = e6Certificate.root (ggHalfX0J0Idx.getD 8 0) from by decide]
  · refine Subgroup.subset_closure ⟨5, 2, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 5 2 = e6Certificate.root (ggHalfX0J0Idx.getD 9 0) from by decide]
  · refine Subgroup.subset_closure ⟨5, 3, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 5 3 = e6Certificate.root (ggHalfX0J0Idx.getD 10 0) from by decide]
  · refine Subgroup.subset_closure ⟨5, 4, by decide, by decide, by decide, by decide, by decide, ?_⟩
    rw [show ggHalfM0.frame .L 5 4 = e6Certificate.root (ggHalfX0J0Idx.getD 11 0) from by decide]

private theorem ggX0GensG_J0_mem
    (D : GGHalfX0Data)
    {i : ℕ} (hi : i < 12) : ggX0GensG D i ∈ ggHalfM0.J0 := by
  rw [ggX0GensG, if_pos hi]
  exact ggX0J0Idx_mem i hi

private theorem ggX0GensG_J0r_mem
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (hc : ggHalfWordBits (D.rWord ++ D.rWord) = ggHalfIdBits)
    {i : ℕ} (h12 : 12 ≤ i) (hi : i < 24) : ggX0GensG D i ∈
      ggHalfM0.J0.map (MulAut.conj (ggHalfWord D.rWord)).toMonoidHom := by
  rw [ggX0GensG, if_neg (by omega)]
  have hx : ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD (i - 12) 0)) ∈ ggHalfM0.J0 :=
    ggX0J0Idx_mem (i - 12) (by omega)
  have hrinv := ggX0_rWord_inv D h hc
  have hmem : ggHalfWord D.rWord * ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD (i - 12) 0)) *
      (ggHalfWord D.rWord)⁻¹ ∈ ggHalfM0.J0.map (MulAut.conj (ggHalfWord D.rWord)).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rwa [hrinv] at hmem

private theorem ggX0GensList_mem_J0
    (D : GGHalfX0Data)
    (w : List ℕ) (hw : ∀ i ∈ w, i < 12) : ggX0WordG D w ∈ ggHalfM0.J0 := by
  suffices ∀ A ∈ ggHalfM0.J0,
      w.foldl (fun A i => A * (ggX0GensList D).getD i 1) A ∈ ggHalfM0.J0 from
    this 1 (Subgroup.one_mem _)
  induction w with
  | nil => intro A hA; simpa using hA
  | cons i t ih =>
    intro A hA
    have hi12 : i < 12 := hw i (List.mem_cons_self ..)
    rw [List.foldl_cons]
    refine ih (fun j hj => hw j (List.mem_cons_of_mem _ hj))
      (A * (ggX0GensList D).getD i 1) (Subgroup.mul_mem _ hA ?_)
    rw [ggX0GensList_getD_lt D (by omega)]
    exact ggX0GensG_J0_mem D hi12

private theorem ggX0_comm
    (D : GGHalfX0Data)
    (h : ggX0Bounds D)
    (hc : ggHalfWordBits (D.rWord ++ D.uWord) = ggHalfWordBits (D.uWord ++ D.rWord)) :
    ggHalfWord D.rWord * ggHalfWord D.uWord = ggHalfWord D.uWord * ggHalfWord D.rWord := by
  have hru : ∀ k ∈ D.rWord ++ D.uWord, k < 72 := by
    intro k hk; rw [List.mem_append] at hk
    exact hk.elim (ggX0Bounds_rWord h k) (ggX0Bounds_uWord h k)
  have hur : ∀ k ∈ D.uWord ++ D.rWord, k < 72 := by
    intro k hk; rw [List.mem_append] at hk
    exact hk.elim (ggX0Bounds_uWord h k) (ggX0Bounds_rWord h k)
  apply ggE6Bits_injective
  calc ggE6Bits (ggHalfWord D.rWord * ggHalfWord D.uWord)
      = ggE6Bits (ggHalfWord (D.rWord ++ D.uWord)) := by rw [ggHalfWord_append]
    _ = ggHalfWordBits (D.rWord ++ D.uWord) := ggE6Bits_word hru
    _ = ggHalfWordBits (D.uWord ++ D.rWord) := hc
    _ = ggE6Bits (ggHalfWord (D.uWord ++ D.rWord)) := (ggE6Bits_word hur).symm
    _ = ggE6Bits (ggHalfWord D.uWord * ggHalfWord D.rWord) := by rw [ggHalfWord_append]

private noncomputable def ggX0SymG
    (D : GGHalfX0Data) :
    List GGE6Two :=
  let a := ggX0WordG D D.aJ
  let b := ggX0WordG D D.bJ
  [a, b, a ^ 59, b ^ 59]

private noncomputable def ggX0AlphaG
    (D : GGHalfX0Data)
    (w : List ℕ) : GGE6Two :=
  w.foldl (fun A i => A * (ggX0SymG D).getD i 1) 1

private theorem ggE6Bits_pow
    (g : GGE6Two) (n : ℕ) :
    ggE6Bits (g ^ n) = ggHalfX0MatPow (ggE6Bits g) n := by
  induction n with
  | zero => rw [pow_zero, ggE6Bits_one]; rfl
  | succ n ih => rw [pow_succ, ggE6Bits_mul, ih]; rfl

private theorem ggX0WordG_bits_J0
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (w : List ℕ) (hw : ∀ i ∈ w, i < 12) :
    ggE6Bits (ggX0WordG D w) = ggHalfX0MatOfGens ggHalfX0J0GensBits w := by
  rw [ggX0WordG_bits D (ggX0Bounds_rWord h) w, ggX0MatOfGens_J0_eq D w hw]

private theorem ggX0SymG_getD_bits
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (i : ℕ) :
    ggE6Bits ((ggX0SymG D).getD i 1) = (ggX0SymBits D).getD i ggHalfIdBits := by
  by_cases hi : i < 4
  · interval_cases i <;>
      simp only [ggX0SymG, ggX0SymBits, ggE6Bits_pow, List.getD_cons_zero, List.getD_cons_succ,
        ggX0WordG_bits_J0 D h D.aJ (ggX0Bounds_aJ h),
        ggX0WordG_bits_J0 D h D.bJ (ggX0Bounds_bJ h), ggX0ABits, ggX0BBits]
  · have hlen : (ggX0SymG D).length = 4 := by simp [ggX0SymG]
    have hlen' : (ggX0SymBits D).length = 4 := by simp [ggX0SymBits]
    rw [List.getD_eq_default _ _ (by rw [hlen]; omega),
      List.getD_eq_default _ _ (by rw [hlen']; omega), ggE6Bits_one]

private theorem ggX0AlphaG_bits
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (w : List ℕ) :
    ggE6Bits (ggX0AlphaG D w) = ggHalfX0MatOfGens (ggX0SymBits D) w := by
  rw [ggX0AlphaG]
  rw [ggE6Bits_foldl_list (ggX0SymG D) (ggX0SymBits D) (ggX0SymG_getD_bits D h) 1 w,
    ggE6Bits_one]
  rfl

private theorem ggX0SymG_getD_mem
    (D : GGHalfX0Data)
    (P : Subgroup GGE6Two) (ha : ggX0WordG D D.aJ ∈ P) (hb : ggX0WordG D D.bJ ∈ P) (i : ℕ) :
    (ggX0SymG D).getD i 1 ∈ P := by
  by_cases hi : i < 4
  · interval_cases i <;> simp only [ggX0SymG, List.getD_cons_zero, List.getD_cons_succ]
    · exact ha
    · exact hb
    · exact Subgroup.pow_mem P ha 59
    · exact Subgroup.pow_mem P hb 59
  · have hlen : (ggX0SymG D).length = 4 := by simp [ggX0SymG]
    rw [List.getD_eq_default _ _ (by rw [hlen]; omega)]
    exact Subgroup.one_mem P

private theorem ggX0AlphaG_mem
    (D : GGHalfX0Data)
    (P : Subgroup GGE6Two) (ha : ggX0WordG D D.aJ ∈ P) (hb : ggX0WordG D D.bJ ∈ P) (w : List ℕ) :
    ggX0AlphaG D w ∈ P := by
  rw [ggX0AlphaG]
  suffices ∀ A ∈ P, w.foldl (fun A i => A * (ggX0SymG D).getD i 1) A ∈ P from
    this 1 (Subgroup.one_mem _)
  induction w with
  | nil => intro A hA; simpa using hA
  | cons i t ih =>
    intro A hA
    rw [List.foldl_cons]
    exact ih _ (Subgroup.mul_mem _ hA (ggX0SymG_getD_mem D P ha hb i))

private noncomputable def ggX0H
    (D : GGHalfX0Data) :
    Subgroup GGE6Two :=
  ggHalfM0.J0 ⊔ ggHalfM0.J0.map (MulAut.conj (ggHalfWord D.rWord)).toMonoidHom

private theorem ggE6Bits_apply_bits
    (g : GGE6Two) {v : ℕ}
    (hv : v < 2 ^ 27) :
    ggHalfApplyBits (ggE6Bits g) v = ggHalfVecBits (ggX0Endo g (ggHalfVecOfBits v)) := by
  calc ggHalfApplyBits (ggE6Bits g) v
      = ggHalfApplyBits (ggE6Bits g) (ggHalfVecBits (ggHalfVecOfBits v)) := by
        rw [ggHalfVecBits_ofBits hv]
    _ = ggHalfVecBits (ggX0Endo g (ggHalfVecOfBits v)) := by
        rw [← ggE6Bits_apply g (ggHalfVecOfBits v)]; rfl

private theorem ggHalfApplyBits_mul_bits
    (g h : GGE6Two) {v : ℕ}
    (hv : v < 2 ^ 27) :
    ggHalfApplyBits (ggE6Bits g) (ggHalfApplyBits (ggE6Bits h) v) =
      ggHalfApplyBits (ggHalfMulBits (ggE6Bits g) (ggE6Bits h)) v := by
  have happly := fun k => ggE6Bits_apply_bits k hv
  calc ggHalfApplyBits (ggE6Bits g) (ggHalfApplyBits (ggE6Bits h) v)
      = ggHalfApplyBits (ggE6Bits g) (ggHalfVecBits (ggX0Endo h (ggHalfVecOfBits v))) := by
        rw [happly h]
    _ = ggHalfVecBits (ggX0Endo g (ggX0Endo h (ggHalfVecOfBits v))) :=
        (ggE6Bits_apply g (ggX0Endo h (ggHalfVecOfBits v))).symm
    _ = ggHalfVecBits ((ggX0Endo g * ggX0Endo h) (ggHalfVecOfBits v)) := by
        rw [Module.End.mul_apply]
    _ = ggHalfVecBits (ggX0Endo (g * h) (ggHalfVecOfBits v)) := by rw [ggX0Endo_mul]
    _ = ggHalfApplyBits (ggE6Bits (g * h)) v := (happly (g * h)).symm
    _ = ggHalfApplyBits (ggHalfMulBits (ggE6Bits g) (ggE6Bits h)) v := by rw [ggE6Bits_mul]

private theorem ggX0W0Span_lt :
    (ggHalfX0SpanMasks ggHalfX0W0).all (fun m => decide (m < 2 ^ 27)) = true := by decide

private theorem ggX0W0_lt {m : ℕ} (hm : m ∈ ggHalfX0SpanMasks ggHalfX0W0) : m < 2 ^ 27 :=
  of_decide_eq_true ((List.all_eq_true.mp ggX0W0Span_lt) m hm)

private theorem ggX0W0Mem_lt : (ggHalfX0W0.all (fun m => decide (m < 2 ^ 27))) = true := by
  decide

private theorem ggX0W0_mem_lt {m : ℕ} (hm : m ∈ ggHalfX0W0) : m < 2 ^ 27 :=
  of_decide_eq_true ((List.all_eq_true.mp ggX0W0Mem_lt) m hm)

private theorem ggX0ApplyBits_lt
    (g : GGE6Two) {m : ℕ}
    (hm : m < 2 ^ 27) : ggHalfApplyBits (ggE6Bits g) m < 2 ^ 27 := by
  rw [ggE6Bits_apply_bits g hm]; exact ggHalfVecBits_lt _

private theorem ggX0MapSpan_lt
    (g : GGE6Two) {m : ℕ}
    (hm : m ∈ ggHalfX0SpanMasks (ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits g) b))) :
    m < 2 ^ 27 := by
  rw [ggHalfX0SpanMasks_map_apply, List.mem_map] at hm
  obtain ⟨m', hm', hmm⟩ := hm
  rw [← hmm]; exact ggX0ApplyBits_lt g (ggX0W0_lt hm')

private noncomputable def ggX0W0set : Set (Fin 27 →₀ GaloisField 2 1) :=
  {v | ggHalfVecBits v ∈ ggHalfX0SpanMasks ggHalfX0W0}

private theorem ggX0_smul_W0set
    (g : GGE6Two) :
    g • ggX0W0set = {v | ggHalfVecBits v ∈
      ggHalfX0SpanMasks (ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits g) b))} := by
  ext v; constructor
  · rintro ⟨u, hu, rfl⟩
    change ggHalfVecBits (e6Data_valid.endo (GaloisField 2 1) g u) ∈
      ggHalfX0SpanMasks (ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits g) b))
    rw [ggE6Bits_apply, ggHalfX0SpanMasks_map_apply, List.mem_map]
    exact ⟨ggHalfVecBits u, hu, rfl⟩
  · intro hv
    simp only [Set.mem_setOf_eq] at hv
    rw [ggHalfX0SpanMasks_map_apply, List.mem_map] at hv
    obtain ⟨m, hm, hmm⟩ := hv
    refine ⟨ggHalfVecOfBits m, ?_, ?_⟩
    · change ggHalfVecBits (ggHalfVecOfBits m) ∈ ggHalfX0SpanMasks ggHalfX0W0
      rw [ggHalfVecBits_ofBits (ggX0W0_lt hm)]; exact hm
    · apply ggHalfVecBits_injective
      change ggHalfVecBits (e6Data_valid.endo (GaloisField 2 1) g (ggHalfVecOfBits m)) =
        ggHalfVecBits v
      rw [ggE6Bits_apply, ggHalfVecBits_ofBits (ggX0W0_lt hm)]
      exact hmm

private noncomputable def ggX0SubNodesAux
    (gens : List GGE6Two) (gensB : List (List ℕ)) :
    List (GGE6Two × List ℕ) → ℕ → List ℕ → List (GGE6Two × List ℕ)
  | acc, i, [] => acc.reverse
  | acc, i, t :: ts =>
    let par := t / 24
    let gen := t % 24
    let p := acc.getD (i - 1 - par) (1, [])
    let g' := (gens.getD gen 1) * p.1
    let b' := p.2.map (fun b => ggHalfApplyBits (gensB.getD gen ggHalfIdBits) b)
    ggX0SubNodesAux gens gensB ((g', b') :: acc) (i + 1) ts

private noncomputable def ggX0SubNodes
    (D : GGHalfX0Data) :
    List (GGE6Two × List ℕ) :=
  ggX0SubNodesAux (ggX0GensList D) (ggHalfX0GensBits D) [(1, ggHalfX0W0)] 1 D.tree.tail

private theorem ggX0SubNodesAux_map_snd
    (gens : List GGE6Two)
    (gensB : List (List ℕ)) (acc : List (GGE6Two × List ℕ)) (accB : List (List ℕ))
    (i : ℕ) (tree : List ℕ) (h : acc.map (·.2) = accB) :
    (ggX0SubNodesAux gens gensB acc i tree).map (·.2) =
      ggHalfX0SubBasesAux gensB accB i tree := by
  induction tree generalizing acc accB i with
  | nil => simp only [ggX0SubNodesAux, ggHalfX0SubBasesAux, List.map_reverse, h]
  | cons t ts ih =>
    simp only [ggX0SubNodesAux, ggHalfX0SubBasesAux]
    have hp : (acc.getD (i - 1 - t / 24) (1, [])).2 = accB.getD (i - 1 - t / 24) [] := by
      have h2 := congrArg (fun l : List (List ℕ) => l.getD (i - 1 - t / 24) []) h
      have h3 : (acc.map (fun x : GGE6Two × List ℕ => x.2)).getD (i - 1 - t / 24)
          ((fun x : GGE6Two × List ℕ => x.2) (1, [])) = accB.getD (i - 1 - t / 24) [] := h2
      rw [List.getD_map] at h3
      simpa using h3
    have hmap := ih
      (((gens.getD (t % 24) 1) * (acc.getD (i - 1 - t / 24) (1, [])).1,
        (acc.getD (i - 1 - t / 24) (1, [])).2.map
          (fun b => ggHalfApplyBits (gensB.getD (t % 24) ggHalfIdBits) b)) :: acc)
      ((accB.getD (i - 1 - t / 24) []).map
        (fun b => ggHalfApplyBits (gensB.getD (t % 24) ggHalfIdBits) b) :: accB)
      (i + 1)
      (by simp only [List.map_cons, List.map_map, Function.comp_apply, hp, h])
    simpa only [List.map_cons] using hmap

private theorem ggX0SubNodes_bases
    (D : GGHalfX0Data) :
    (ggX0SubNodes D).map (·.2) = ggHalfX0SubBases D := by
  unfold ggX0SubNodes ggHalfX0SubBases
  exact ggX0SubNodesAux_map_snd _ _ _ _ _ _ rfl

private theorem ggX0W0_length : ggHalfX0W0.length = 5 := by decide

private theorem ggX0Bounds_cWit {D : GGHalfX0Data} (h : ggX0Bounds D) : D.cWit < 5 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hcw, -⟩ := h
  exact hcw

private theorem ggX0ApplyBits_idBits
    {b : ℕ} (hb : b < 2 ^ 27) :
    ggHalfApplyBits ggHalfIdBits b = b := by
  rw [← ggE6Bits_one]
  rw [ggE6Bits_apply_bits (1 : GGE6Two) hb, ggX0Endo_one, Module.End.one_apply,
    ggHalfVecBits_ofBits hb]

private theorem ggX0SpanMasks_zero (l : List ℕ) : (0 : ℕ) ∈ ggHalfX0SpanMasks l := by
  induction l with
  | nil => simp [ggHalfX0SpanMasks]
  | cons v vs ih => exact List.mem_append_right _ ih

private theorem ggX0W0Span_xor :
    (ggHalfX0SpanMasks ggHalfX0W0).all (fun a =>
      (ggHalfX0SpanMasks ggHalfX0W0).all (fun b =>
        decide (a ^^^ b ∈ ggHalfX0SpanMasks ggHalfX0W0))) = true := by decide

private theorem ggX0SpanMasks_apply_subset {l A S : List ℕ}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ^^^ b ∈ S) (h0 : (0 : ℕ) ∈ S)
    (h : ∀ b ∈ l, ggHalfApplyBits A b ∈ S) :
    ∀ m ∈ ggHalfX0SpanMasks l, ggHalfApplyBits A m ∈ S := by
  induction l with
  | nil =>
    intro m hm
    rw [ggHalfX0SpanMasks, List.mem_singleton] at hm
    subst hm
    rw [ggHalfApplyBits_of_zero]
    exact h0
  | cons v vs ih =>
    intro m hm
    rw [ggHalfX0SpanMasks, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨m', hm', rfl⟩ | hm
    · rw [ggHalfApplyBits_xor]
      exact hS _ (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) m' hm') _
        (h v (List.mem_cons_self ..))
    · exact ih (fun b hb => h b (List.mem_cons_of_mem _ hb)) m hm

private theorem ggX0TreeOK_getD_lt : ∀ (l : List ℕ) (j0 : ℕ), ggX0TreeOK l j0 = true →
    ∀ j, j < l.length → (l.getD j 0) / 24 < j0 + j + 1 := by
  intro l
  induction l with
  | nil => intro j0 _ j hj; simp at hj
  | cons t ts ih =>
    intro j0 h j hj
    rw [ggX0TreeOK] at h
    split at h
    · rename_i ht
      cases j with
      | zero => simpa using ht
      | succ j' =>
        simp only [List.getD_cons_succ, List.length_cons] at hj ⊢
        have := ih (j0 + 1) h j' (by omega)
        omega
    · simp at h

private theorem ggX0SubNodes_length
    (D : GGHalfX0Data)
    (hs : ggX0SubFacts D) : (ggX0SubNodes D).length = 1632 := by
  have hnodup_len := (ggHalfX0CheckDistinctLength_spec hs.1).2
  have hkeys : (ggHalfX0SubKeys D).length = (ggHalfX0SubBases D).length := by
    simp [ggHalfX0SubKeys]
  have hB : (ggHalfX0SubBases D).length = 1632 := by
    rw [← hkeys]; exact hnodup_len
  have hlen : (ggX0SubNodes D).length = (ggHalfX0SubBases D).length := by
    have := congrArg List.length (ggX0SubNodes_bases D)
    simpa [List.length_map] using this
  rw [hlen]; exact hB

private theorem ggX0GensList_getD_mem_H
    (D : GGHalfX0Data) (h : ggX0Bounds D)
    (hr2 : ggHalfWordBits (D.rWord ++ D.rWord) = ggHalfIdBits) (i : ℕ) :
    (ggX0GensList D).getD i 1 ∈ ggX0H D := by
  by_cases hi : i < 24
  · rw [ggX0GensList_getD_lt D hi]
    by_cases h12 : i < 12
    · exact Subgroup.mem_sup_left (ggX0GensG_J0_mem D h12)
    · exact Subgroup.mem_sup_right (ggX0GensG_J0r_mem D h hr2 (by omega) hi)
  · rw [List.getD_eq_default _ _ (by rw [ggX0GensList_length]; omega)]
    exact Subgroup.one_mem _

private theorem ggX0SubNodesAux_spec
    (D : GGHalfX0Data)
    (gens : List GGE6Two) (gensB : List (List ℕ)) (acc : List (GGE6Two × List ℕ)) (i : ℕ)
    (tree : List ℕ)
    (hbits : ∀ gen, ggE6Bits (gens.getD gen 1) = gensB.getD gen ggHalfIdBits)
    (hgensH : ∀ gen, gens.getD gen 1 ∈ ggX0H D)
    (hacc : ∀ p ∈ acc, p.1 ∈ ggX0H D ∧
      p.2 = ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits p.1) b))
    (hlen : acc.length = i)
    (hbound : ∀ j, j < tree.length → (tree.getD j 0) / 24 < i + j) :
    ∀ p ∈ ggX0SubNodesAux gens gensB acc i tree,
      p.1 ∈ ggX0H D ∧ p.2 = ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits p.1) b) := by
  induction tree generalizing acc i with
  | nil =>
    intro p hp
    rw [ggX0SubNodesAux] at hp
    exact hacc p (List.mem_reverse.mp hp)
  | cons t ts ih =>
    rw [ggX0SubNodesAux]
    have htbound : t / 24 < i := by
      have := hbound 0 (by simp)
      simpa using this
    have hpar : i - 1 - t / 24 < acc.length := by rw [hlen]; omega
    have hpacc : acc.getD (i - 1 - t / 24) (1, []) ∈ acc := by
      rw [List.getD_eq_getElem (l := acc) (d := (1, [])) hpar]
      exact List.getElem_mem _
    have hpmem := hacc _ hpacc
    have hpval := hpmem.2
    have hb' : (acc.getD (i - 1 - t / 24) (1, [])).2.map
          (fun b => ggHalfApplyBits (gensB.getD (t % 24) ggHalfIdBits) b) =
        ggHalfX0W0.map (fun b => ggHalfApplyBits
          (ggE6Bits (gens.getD (t % 24) 1 * (acc.getD (i - 1 - t / 24) (1, [])).1)) b) := by
      rw [hpval, List.map_map]
      apply List.map_congr_left
      intro b hb
      simp only [Function.comp_apply]
      rw [← hbits (t % 24), ggE6Bits_mul]
      exact ggHalfApplyBits_mul_bits (gens.getD (t % 24) 1)
        (acc.getD (i - 1 - t / 24) (1, [])).1 (ggX0W0_mem_lt hb)
    refine ih _ (i + 1) ?_ (by simp [hlen]) ?_
    · intro p hp
      rw [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨Subgroup.mul_mem _ (hgensH (t % 24)) hpmem.1, hb'⟩
      · exact hacc p hp
    · intro j hj
      have hlt : j + 1 < (t :: ts).length := by simpa using hj
      have hb2 := hbound (j + 1) hlt
      have hget : (t :: ts).getD (j + 1) 0 = ts.getD j 0 := by simp
      rw [hget] at hb2
      omega

private theorem ggX0SubNodes_spec
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (hc : ggX0CheapFacts D) (hs : ggX0SubFacts D) :
    ∀ p ∈ ggX0SubNodes D, p.1 ∈ ggX0H D ∧
      p.2 = ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits p.1) b) := by
  unfold ggX0SubNodes
  refine ggX0SubNodesAux_spec D (ggX0GensList D) (ggHalfX0GensBits D) [(1, ggHalfX0W0)] 1
    D.tree.tail (fun gen => ggX0GensList_bits D (ggX0Bounds_rWord h) gen)
    (fun gen => ggX0GensList_getD_mem_H D h hc.1 gen) ?_ rfl ?_
  · intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    refine ⟨Subgroup.one_mem _, ?_⟩
    have hmap : ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits (1 : GGE6Two)) b) =
        ggHalfX0W0 := by
      calc ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits (1 : GGE6Two)) b)
          = ggHalfX0W0.map id := by
            apply List.map_congr_left
            intro b hb
            simp only [Function.comp_apply, id_eq]
            rw [ggE6Bits_one]
            exact ggX0ApplyBits_idBits (ggX0W0_mem_lt hb)
        _ = ggHalfX0W0 := List.map_id _
    exact hmap.symm
  · intro j hj
    have := ggX0TreeOK_getD_lt D.tree.tail 0 hs.2.2 j hj
    omega

private theorem ggX0J0FixW0 (D : GGHalfX0Data) (hcw : D.cWit < 5) :
    (List.range 12).all (fun i => decide (ggHalfApplyBits (ggHalfX0J0GensBits.getD i ggHalfIdBits)
      (ggHalfX0W0.getD D.cWit 0) = ggHalfX0W0.getD D.cWit 0)) = true := by
  obtain ⟨k, hk⟩ : ∃ k : Fin 5, D.cWit = (k : ℕ) := ⟨⟨D.cWit, hcw⟩, rfl⟩
  rw [hk]
  fin_cases k <;> decide +kernel

private theorem ggX0J0FixW0_eq :
    (List.range 12).all (fun i => decide (ggHalfX0SpanMasks
      (ggHalfX0W0.map (ggHalfApplyBits (ggHalfX0J0GensBits.getD i ggHalfIdBits))) =
      ggHalfX0SpanMasks ggHalfX0W0)) = true := by decide +kernel

private theorem ggHalfM0_frame_J0Idx (a b : Fin 8) (ha : 2 ≤ a.val) (ha' : a.val < 6)
    (hb : 2 ≤ b.val) (hb' : b.val < 6) (hab : a ≠ b) :
    ∃ i, i < 12 ∧ ggHalfM0.frame .L a b = e6Certificate.root (ggHalfX0J0Idx.getD i 0) := by
  have hany : (List.range 12).any (fun i => decide (ggHalfM0.frame .L a b =
      e6Certificate.root (ggHalfX0J0Idx.getD i 0))) = true := by
    revert a b
    decide +kernel
  obtain ⟨i, hi, hdec⟩ := List.any_eq_true.mp hany
  exact ⟨i, List.mem_range.mp hi, by simpa using hdec⟩

private theorem ggX0J0FixW0_vec
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) :
    ∀ j ∈ ggHalfM0.J0, ggX0Endo j (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0)) =
      ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0) := by
  have hcw := ggX0Bounds_cWit h
  have hmemW : ggHalfX0W0.getD D.cWit 0 ∈ ggHalfX0W0 := by
    rw [List.getD_eq_getElem (l := ggHalfX0W0) (d := 0) (by rw [ggX0W0_length]; exact hcw)]
    exact List.getElem_mem _
  have hltW := ggX0W0_mem_lt hmemW
  have hgen_fix : ∀ i < 12,
      ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD i 0)) ∈
        MulAction.stabilizer GGE6Two (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0)) := by
    intro i hi
    change ggX0Endo (ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD i 0)))
      (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0)) = ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0)
    apply ggHalfVecBits_injective
    change ggHalfVecBits (e6Data_valid.endo (GaloisField 2 1)
        (ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD i 0)))
        (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0))) =
      ggHalfVecBits (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0))
    rw [ggE6Bits_apply, ggHalfVecBits_ofBits hltW,
      ggE6Bits_x (ggX0J0Idx_getD_lt (i := i) (by omega)), ← ggX0J0GensBits_getD hi]
    exact of_decide_eq_true (List.all_eq_true.mp (ggX0J0FixW0 D hcw) i (List.mem_range.mpr hi))
  have hJ0le : ggHalfM0.J0 ≤ MulAction.stabilizer GGE6Two
      (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0)) := by
    rw [show ggHalfM0.J0 = Subgroup.closure {g | ∃ a b : Fin 8, 2 ≤ a.val ∧ a.val < 6 ∧
        2 ≤ b.val ∧ b.val < 6 ∧ a ≠ b ∧ g = ggE6x (ggHalfM0.frame .L a b)} from rfl]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨a, b, ha, ha', hb, hb', hab, rfl⟩
    obtain ⟨i, hi, hframe⟩ := ggHalfM0_frame_J0Idx a b ha ha' hb hb' hab
    rw [hframe]
    exact hgen_fix i hi
  intro j hj
  exact hJ0le hj

private noncomputable def ggX0SubGen
    (D : GGHalfX0Data)
    (i : Fin 1632) : GGE6Two :=
  ((ggX0SubNodes D).getD i.1 (1, [])).1

private noncomputable def ggX0SubBas
    (D : GGHalfX0Data)
    (i : Fin 1632) : List ℕ :=
  ((ggX0SubNodes D).getD i.1 (1, [])).2

private noncomputable def ggX0SubKey
    (D : GGHalfX0Data)
    (i : Fin 1632) : ℕ :=
  ggHalfX0SubKeyOfBasis (ggX0SubBas D i)

private theorem ggX0SubBas_spec
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (hc : ggX0CheapFacts D) (hs : ggX0SubFacts D) (i : Fin 1632) :
    ggX0SubBas D i = ggHalfX0W0.map (fun b => ggHalfApplyBits (ggE6Bits (ggX0SubGen D i)) b) := by
  have hnode : (ggX0SubNodes D).getD i.1 (1, []) ∈ ggX0SubNodes D := by
    rw [List.getD_eq_getElem (l := ggX0SubNodes D) (d := (1, []))
      (by rw [ggX0SubNodes_length D hs]; exact i.2)]
    exact List.getElem_mem _
  exact (ggX0SubNodes_spec D h hc hs _ hnode).2

private theorem ggX0SubBas_mem
    (D : GGHalfX0Data)
    (hs : ggX0SubFacts D) (i : Fin 1632) : ggX0SubBas D i ∈ ggHalfX0SubBases D := by
  have hnode : (ggX0SubNodes D).getD i.1 (1, []) ∈ ggX0SubNodes D := by
    rw [List.getD_eq_getElem (l := ggX0SubNodes D) (d := (1, []))
      (by rw [ggX0SubNodes_length D hs]; exact i.2)]
    exact List.getElem_mem _
  have hmem : ggX0SubBas D i ∈ (ggX0SubNodes D).map (·.2) := List.mem_map.mpr ⟨_, hnode, rfl⟩
  rwa [ggX0SubNodes_bases D] at hmem

private theorem ggX0SubBas_nodup
    (D : GGHalfX0Data)
    (hs : ggX0SubFacts D) (i : Fin 1632) :
    (ggHalfX0SpanMasks (ggX0SubBas D i)).Nodup :=
  ggHalfX0CheckNodup_spec (List.all_eq_true.mp hs.2.1 _ (ggX0SubBas_mem D hs i))

private theorem ggX0SubKey_getD
    (D : GGHalfX0Data)
    (hs : ggX0SubFacts D) (i : Fin 1632) :
    (ggHalfX0SubKeys D).getD i.1 (ggHalfX0SubKeyOfBasis ([] : List ℕ)) = ggX0SubKey D i := by
  have hkfst : (ggX0SubNodes D).map
        (fun p : GGE6Two × List ℕ => ggHalfX0SubKeyOfBasis p.2) = ggHalfX0SubKeys D := by
    rw [ggHalfX0SubKeys, ← ggX0SubNodes_bases D, List.map_map]
    rfl
  rw [← hkfst]
  exact List.getD_map (fun p : GGE6Two × List ℕ => ggHalfX0SubKeyOfBasis p.2)
    (l := ggX0SubNodes D) (n := i.1) (d := (1, []))

private theorem ggX0SubKey_get
    (D : GGHalfX0Data)
    (hs : ggX0SubFacts D) (i : Fin 1632) :
    (ggHalfX0SubKeys D).get (⟨i.1, by
        rw [(ggHalfX0CheckDistinctLength_spec hs.1).2]; exact i.2⟩ :
      Fin (ggHalfX0SubKeys D).length) = ggX0SubKey D i :=
  ((List.getD_eq_get (l := ggHalfX0SubKeys D) (d := ggHalfX0SubKeyOfBasis ([] : List ℕ))
    (⟨i.1, by rw [(ggHalfX0CheckDistinctLength_spec hs.1).2]; exact i.2⟩ :
      Fin (ggHalfX0SubKeys D).length)).symm).trans (ggX0SubKey_getD D hs i)

private theorem ggX0SubKey_inj
    (D : GGHalfX0Data)
    (hs : ggX0SubFacts D) : Function.Injective (ggX0SubKey D) := by
  intro i j hij
  have hnd := (ggHalfX0CheckDistinctLength_spec hs.1).1
  have heq : (ggHalfX0SubKeys D).get (⟨i.1, by
        rw [(ggHalfX0CheckDistinctLength_spec hs.1).2]; exact i.2⟩ :
      Fin (ggHalfX0SubKeys D).length) =
      (ggHalfX0SubKeys D).get (⟨j.1, by
        rw [(ggHalfX0CheckDistinctLength_spec hs.1).2]; exact j.2⟩ :
      Fin (ggHalfX0SubKeys D).length) := by
    rw [ggX0SubKey_get D hs i, ggX0SubKey_get D hs j, hij]
  have hfin := (List.Nodup.get_inj_iff hnd).mp heq
  have hv : i.val = j.val := by simpa using congrArg Fin.val hfin
  exact Fin.ext hv

private theorem ggX0SubKey_eq_of_smul_eq
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (hc : ggX0CheapFacts D) (hs : ggX0SubFacts D) {i j : Fin 1632}
    (hij : ggX0SubGen D i • ggX0W0set = ggX0SubGen D j • ggX0W0set) :
    ggX0SubKey D i = ggX0SubKey D j := by
  have hspec_i := ggX0SubBas_spec D h hc hs i
  have hspec_j := ggX0SubBas_spec D h hc hs j
  have hset : {v | ggHalfVecBits v ∈ ggHalfX0SpanMasks (ggX0SubBas D i)} =
      {v | ggHalfVecBits v ∈ ggHalfX0SpanMasks (ggX0SubBas D j)} := by
    have h1 : ggX0SubGen D i • ggX0W0set =
        {v | ggHalfVecBits v ∈ ggHalfX0SpanMasks (ggX0SubBas D i)} := by
      rw [ggX0_smul_W0set (ggX0SubGen D i), ← hspec_i]
    have h2 : ggX0SubGen D j • ggX0W0set =
        {v | ggHalfVecBits v ∈ ggHalfX0SpanMasks (ggX0SubBas D j)} := by
      rw [ggX0_smul_W0set (ggX0SubGen D j), ← hspec_j]
    rw [← h1, ← h2]; exact hij
  have hmem : ∀ m, m ∈ ggHalfX0SpanMasks (ggX0SubBas D i) ↔
      m ∈ ggHalfX0SpanMasks (ggX0SubBas D j) := by
    intro m
    constructor
    · intro hm
      have hmi := hm
      rw [hspec_i] at hmi
      have hltm := ggX0MapSpan_lt (ggX0SubGen D i) hmi
      have h := Set.ext_iff.mp hset (ggHalfVecOfBits m)
      simp only [Set.mem_setOf_eq] at h
      rw [ggHalfVecBits_ofBits hltm] at h
      exact h.mp hm
    · intro hm
      have hmj := hm
      rw [hspec_j] at hmj
      have hltm := ggX0MapSpan_lt (ggX0SubGen D j) hmj
      have h := Set.ext_iff.mp hset (ggHalfVecOfBits m)
      simp only [Set.mem_setOf_eq] at h
      rw [ggHalfVecBits_ofBits hltm] at h
      exact h.mpr hm
  exact ggHalfX0SubKeyOfBasis_eq_of_mem_iff (ggX0SubBas_nodup D hs i)
    (ggX0SubBas_nodup D hs j) hmem

private theorem ggX0SubGen_smul_inj
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (hc : ggX0CheapFacts D) (hs : ggX0SubFacts D) :
    Function.Injective (fun i : Fin 1632 => ggX0SubGen D i • ggX0W0set) := by
  intro i j hij
  exact ggX0SubKey_inj D hs (ggX0SubKey_eq_of_smul_eq D h hc hs hij)

private theorem ggX0_holds_general
    (D : GGHalfX0Data)
    (h : ggX0Bounds D) (hc : ggX0CheapFacts D) (hs : ggX0SubFacts D)
    (hu : ggHalfWord D.uWord =
      ggE6u (ggHalfM0.frame .L 0 1) * ggE6u (ggHalfM0.frame .K 6 7) ^ D.eps) :
    GGHalfX0 ggHalfM0 D.eps := by
  classical
  have hcAll : ggX0CheapFacts D := hc
  obtain ⟨hr2, hcomm, hc3, hcne, hcommJ0, hcmove, hdcd, hj0fix, hcfix, hdfix,
    hz17, hzne, hznc, ha60, hb60, har, hbr, hpq, hpq', he3pow, he3ne⟩ := hc
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have haJ0 : ggX0WordG D D.aJ ∈ ggHalfM0.J0 := ggX0GensList_mem_J0 D D.aJ (ggX0Bounds_aJ h)
  have hbJ0 : ggX0WordG D D.bJ ∈ ggHalfM0.J0 := ggX0GensList_mem_J0 D D.bJ (ggX0Bounds_bJ h)
  have harG : ggHalfWord D.rWord * (ggX0WordG D D.aJr * ggHalfWord D.rWord) =
      ggX0WordG D D.aJ := by
    apply ggE6Bits_injective
    simp only [ggE6Bits_mul, ggE6Bits_word (ggX0Bounds_rWord h),
      ggX0WordG_bits_J0 D h D.aJr (ggX0Bounds_aJr h),
      ggX0WordG_bits_J0 D h D.aJ (ggX0Bounds_aJ h)]
    simpa only [ggX0ARBits, ggX0ABits] using har
  have hbrG : ggHalfWord D.rWord * (ggX0WordG D D.bJr * ggHalfWord D.rWord) =
      ggX0WordG D D.bJ := by
    apply ggE6Bits_injective
    simp only [ggE6Bits_mul, ggE6Bits_word (ggX0Bounds_rWord h),
      ggX0WordG_bits_J0 D h D.bJr (ggX0Bounds_bJr h),
      ggX0WordG_bits_J0 D h D.bJ (ggX0Bounds_bJ h)]
    simpa only [ggX0BRBits, ggX0BBits] using hbr
  have haJ0r : ggX0WordG D D.aJ ∈
      ggHalfM0.J0.map (MulAut.conj (ggHalfWord D.rWord)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨ggX0WordG D D.aJr,
      ggX0GensList_mem_J0 D D.aJr (ggX0Bounds_aJr h), ?_⟩
    change (MulAut.conj (ggHalfWord D.rWord)) (ggX0WordG D D.aJr) = ggX0WordG D D.aJ
    rw [MulAut.conj_apply, ggX0_rWord_inv D h hr2, mul_assoc]
    exact harG
  have hbJ0r : ggX0WordG D D.bJ ∈
      ggHalfM0.J0.map (MulAut.conj (ggHalfWord D.rWord)).toMonoidHom := by
    refine Subgroup.mem_map.mpr ⟨ggX0WordG D D.bJr,
      ggX0GensList_mem_J0 D D.bJr (ggX0Bounds_bJr h), ?_⟩
    change (MulAut.conj (ggHalfWord D.rWord)) (ggX0WordG D D.bJr) = ggX0WordG D D.bJ
    rw [MulAut.conj_apply, ggX0_rWord_inv D h hr2, mul_assoc]
    exact hbrG
  let P : Subgroup GGE6Two :=
    Subgroup.closure ({ggX0WordG D D.aJ, ggX0WordG D D.bJ} : Set GGE6Two)
  have haP : ggX0WordG D D.aJ ∈ P := Subgroup.subset_closure (by simp)
  have hbP : ggX0WordG D D.bJ ∈ P := Subgroup.subset_closure (by simp)
  have hPle : P ≤ ggHalfM0.J0 ⊓ ggHalfM0.J0.map (MulAut.conj (ggHalfWord D.rWord)).toMonoidHom :=
    (Subgroup.closure_le _).2 (by
      intro x hx
      rcases hx with rfl | rfl
      · exact ⟨haJ0, haJ0r⟩
      · exact ⟨hbJ0, hbJ0r⟩)
  have hpqG : ggX0AlphaG D D.pa * ggX0AlphaG D D.qa =
      ggX0WordG D D.aJ * ggX0AlphaG D D.qa * ggX0AlphaG D D.pa := by
    apply ggE6Bits_injective
    simp only [ggE6Bits_mul, ggX0AlphaG_bits D h D.pa, ggX0AlphaG_bits D h D.qa,
      ggX0WordG_bits_J0 D h D.aJ (ggX0Bounds_aJ h)]
    simpa only [ggX0PBits, ggX0QBits, ggX0ABits] using hpq
  have hp'q'G : ggX0AlphaG D D.pb * ggX0AlphaG D D.qb =
      ggX0WordG D D.bJ * ggX0AlphaG D D.qb * ggX0AlphaG D D.pb := by
    apply ggE6Bits_injective
    simp only [ggE6Bits_mul, ggX0AlphaG_bits D h D.pb, ggX0AlphaG_bits D h D.qb,
      ggX0WordG_bits_J0 D h D.bJ (ggX0Bounds_bJ h)]
    simpa only [ggX0P'Bits, ggX0Q'Bits, ggX0BBits] using hpq'
  have ha_comm : ggX0WordG D D.aJ =
      (commutatorElement (G := GGE6Two)).bracket (ggX0AlphaG D D.pa) (ggX0AlphaG D D.qa) := by
    rw [commutatorElement_def, hpqG]
    group
  have hb_comm : ggX0WordG D D.bJ =
      (commutatorElement (G := GGE6Two)).bracket (ggX0AlphaG D D.pb) (ggX0AlphaG D D.qb) := by
    rw [commutatorElement_def, hp'q'G]
    group
  have hpP : ggX0AlphaG D D.pa ∈ P := ggX0AlphaG_mem D P haP hbP D.pa
  have hqP : ggX0AlphaG D D.qa ∈ P := ggX0AlphaG_mem D P haP hbP D.qa
  have hp'P : ggX0AlphaG D D.pb ∈ P := ggX0AlphaG_mem D P haP hbP D.pb
  have hq'P : ggX0AlphaG D D.qb ∈ P := ggX0AlphaG_mem D P haP hbP D.qb
  have haPP : ggX0WordG D D.aJ ∈ ⁅P, P⁆ := by
    have hm := Subgroup.commutator_mem_commutator (H₁ := P) (H₂ := P) hpP hqP
    rwa [← ha_comm] at hm
  have hbPP : ggX0WordG D D.bJ ∈ ⁅P, P⁆ := by
    have hm := Subgroup.commutator_mem_commutator (H₁ := P) (H₂ := P) hp'P hq'P
    rwa [← hb_comm] at hm
  have hPP : ⁅P, P⁆ = P := by
    have h := ggHalf_perfect_of_commutators (ggX0WordG D D.aJ) (ggX0WordG D D.bJ) ⟨haPP, hbPP⟩
    simpa only [P] using h
  have he3powG : (ggX0AlphaG D D.e3) ^ 3 = 1 := by
    apply ggE6Bits_injective
    simp only [ggE6Bits_pow, ggX0AlphaG_bits D h D.e3, ggE6Bits_one]
    simpa only [ggX0E3Bits] using he3pow
  have he3neG : ggX0AlphaG D D.e3 ≠ 1 := by
    intro h1
    apply he3ne
    rw [show ggX0E3Bits D = ggE6Bits (ggX0AlphaG D D.e3) from
      (ggX0AlphaG_bits D h D.e3).symm, h1, ggE6Bits_one]
  have he3P : ggX0AlphaG D D.e3 ∈ P := ggX0AlphaG_mem D P haP hbP D.e3
  have he3ord : orderOf (ggX0AlphaG D D.e3) = 3 := orderOf_eq_prime he3powG he3neG
  have hz17G : (ggX0WordG D D.zGen) ^ 17 = 1 := by
    apply ggE6Bits_injective
    simp only [ggE6Bits_pow, ggX0WordG_bits D (ggX0Bounds_rWord h) D.zGen, ggE6Bits_one]
    simpa only [ggX0ZBits] using hz17
  have hzneG : ggX0WordG D D.zGen ≠ 1 := by
    intro h1
    apply hzne
    rw [show ggX0ZBits D = ggE6Bits (ggX0WordG D D.zGen) from
      (ggX0WordG_bits D (ggX0Bounds_rWord h) D.zGen).symm, h1, ggE6Bits_one]
  have hzord : orderOf (ggX0WordG D D.zGen) = 17 := orderOf_eq_prime hz17G hzneG
  have hzj12 : D.zj < 12 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hzj⟩ := h
    exact hzj
  have hjJ0 : ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD D.zj 0)) ∈ ggHalfM0.J0 :=
    ggX0J0Idx_mem D.zj hzj12
  have hzncG : ggX0WordG D D.zGen * ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD D.zj 0)) ≠
      ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD D.zj 0)) * ggX0WordG D D.zGen := by
    intro h1
    apply hznc
    have hbits := congrArg ggE6Bits h1
    rw [ggE6Bits_mul, ggE6Bits_mul, ggX0WordG_bits D (ggX0Bounds_rWord h) D.zGen,
      ggE6Bits_x (ggX0J0Idx_getD_lt (i := D.zj) (by omega)),
      ← ggX0J0GensBits_getD hzj12] at hbits
    exact hbits
  have hgensG_mem_H : ∀ i, (ggX0GensList D).getD i 1 ∈ ggX0H D := by
    intro i
    by_cases hi : i < 24
    · rw [ggX0GensList_getD_lt D hi]
      by_cases h12 : i < 12
      · exact Subgroup.mem_sup_left (ggX0GensG_J0_mem D h12)
      · exact Subgroup.mem_sup_right (ggX0GensG_J0r_mem D h hr2 (by omega) hi)
    · rw [List.getD_eq_default _ _ (by rw [ggX0GensList_length]; omega)]
      exact Subgroup.one_mem (ggX0H D)
  have hword_mem_H : ∀ w, ggX0WordG D w ∈ ggX0H D := by
    intro w
    rw [ggX0WordG]
    suffices ∀ A ∈ ggX0H D, w.foldl (fun A i => A * (ggX0GensList D).getD i 1) A ∈ ggX0H D from
      this 1 (Subgroup.one_mem _)
    induction w with
    | nil => intro A hA; simpa using hA
    | cons i t ih =>
      intro A hA
      rw [List.foldl_cons]
      exact ih _ (Subgroup.mul_mem _ hA (hgensG_mem_H i))
  refine ⟨ggHalfWord D.rWord, ?_, ?_, ?_, ?_⟩
  · rw [← hu]
    exact ggX0_comm D h hcomm
  · exact ⟨P, hPle, hPP, by
      have hdvd : orderOf (ggX0AlphaG D D.e3) ∣ Nat.card P :=
        Subgroup.orderOf_dvd_natCard P he3P
      rwa [he3ord] at hdvd⟩
  · exact ⟨ggX0WordG D D.zGen,
      show ggX0WordG D D.zGen ∈ ggHalfM0.J0 ⊔
        ggHalfM0.J0.map (MulAut.conj (ggHalfWord D.rWord)).toMonoidHom from hword_mem_H D.zGen,
      hzord, ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD D.zj 0)), hjJ0, hzncG⟩
  ·
    let c : GGE6Two := ggX0WordG D D.cGen
    let d : GGE6Two := ggX0WordG D D.dGen
    have hcbits : ggE6Bits c = ggX0CBits D :=
      ggX0WordG_bits D (ggX0Bounds_rWord h) D.cGen
    have hdbits : ggE6Bits d = ggX0DBits D :=
      ggX0WordG_bits D (ggX0Bounds_rWord h) D.dGen
    have hc3pow : c ^ 3 = 1 := by
      apply ggE6Bits_injective
      rw [ggE6Bits_pow, hcbits, hc3, ggE6Bits_one]
    have hcne' : c ≠ 1 := by
      intro h1
      apply hcne
      rw [← hcbits, h1, ggE6Bits_one]
    have hc3ord : orderOf c = 3 := orderOf_eq_prime hc3pow hcne'
    have hcJ : ∀ j ∈ ggHalfM0.J0, c * j = j * c := by
      have hJ0cent : ggHalfM0.J0 ≤ Subgroup.centralizer ({c} : Set GGE6Two) := by
        rw [show ggHalfM0.J0 = Subgroup.closure {g | ∃ a b : Fin 8, 2 ≤ a.val ∧ a.val < 6 ∧
            2 ≤ b.val ∧ b.val < 6 ∧ a ≠ b ∧ g = ggE6x (ggHalfM0.frame .L a b)} from rfl]
        refine (Subgroup.closure_le _).2 ?_
        rintro g ⟨a, b, ha, ha', hb, hb', hab, rfl⟩
        obtain ⟨i, hi, hframe⟩ := ggHalfM0_frame_J0Idx a b ha ha' hb hb' hab
        rw [hframe]
        change ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD i 0)) ∈
          Subgroup.centralizer ({c} : Set GGE6Two)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        apply ggE6Bits_injective
        rw [ggE6Bits_mul, ggE6Bits_mul, hcbits,
          ggE6Bits_x (ggX0J0Idx_getD_lt (i := i) (by omega)), ← ggX0J0GensBits_getD hi]
        exact of_decide_eq_true (List.all_eq_true.mp hcommJ0 i (List.mem_range.mpr hi))
      intro j hj
      exact (Subgroup.mem_centralizer_iff.mp (hJ0cent hj)) c (Set.mem_singleton c)
    have hmemW : ggHalfX0W0.getD D.cWit 0 ∈ ggHalfX0W0 := by
      rw [List.getD_eq_getElem (l := ggHalfX0W0) (d := 0)
        (by rw [ggX0W0_length]; exact ggX0Bounds_cWit h)]
      exact List.getElem_mem _
    have hltW := ggX0W0_mem_lt hmemW
    have hcmove_vec : ggX0Endo c (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0)) ≠
        ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0) := by
      intro h1
      apply hcmove
      have h2 := congrArg ggHalfVecBits h1
      change ggHalfVecBits (e6Data_valid.endo (GaloisField 2 1) c
          (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0))) =
        ggHalfVecBits (ggHalfVecOfBits (ggHalfX0W0.getD D.cWit 0)) at h2
      rw [ggE6Bits_apply, ggHalfVecBits_ofBits hltW, hcbits] at h2
      exact h2
    have hcnot : c ∉ ggHalfM0.J0 := by
      intro hcin
      exact hcmove_vec (ggX0J0FixW0_vec D h c hcin)
    have hdc : d * c = c * c * d := by
      apply ggE6Bits_injective
      simp only [ggE6Bits_mul, hdbits, hcbits, hdcd]
    have hc2inv : c * c = c⁻¹ := by
      have h3 : c * c * c = 1 := by
        simpa [pow_succ, pow_two, mul_assoc] using hc3pow
      exact mul_eq_one_iff_eq_inv.mp h3
    have hd' : d * c * d⁻¹ = c⁻¹ := by
      rw [hdc]
      calc c * c * d * d⁻¹ = c * c * (d * d⁻¹) := by group
        _ = c * c := by rw [mul_inv_cancel, mul_one]
        _ = c⁻¹ := hc2inv
    have hmem_span_c : ∀ m ∈ ggHalfX0SpanMasks ggHalfX0W0,
        ggHalfApplyBits (ggX0CBits D) m ∈ ggHalfX0SpanMasks ggHalfX0W0 :=
      ggX0SpanMasks_apply_subset
        (fun a ha b hb => of_decide_eq_true
          (List.all_eq_true.mp (List.all_eq_true.mp ggX0W0Span_xor a ha) b hb))
        (ggX0SpanMasks_zero ggHalfX0W0)
        (fun b hb => of_decide_eq_true (List.all_eq_true.mp hcfix b hb))
    have hsub_c : c • ggX0W0set ⊆ ggX0W0set := by
      intro v hv
      rw [ggX0_smul_W0set c, hcbits] at hv
      simp only [Set.mem_setOf_eq] at hv
      rw [ggHalfX0SpanMasks_map_apply, List.mem_map] at hv
      obtain ⟨m, hm, hmm⟩ := hv
      change ggHalfVecBits v ∈ ggHalfX0SpanMasks ggHalfX0W0
      rw [← hmm]
      exact hmem_span_c m hm
    have hcset : c • ggX0W0set = ggX0W0set := by
      apply le_antisymm hsub_c
      have h2 : c • (c • ggX0W0set) ⊆ c • ggX0W0set := Set.smul_set_mono hsub_c
      have h3 : ggX0W0set ⊆ c • ggX0W0set := by
        calc ggX0W0set = (1 : GGE6Two) • ggX0W0set := (one_smul _ _).symm
          _ = (c ^ 3) • ggX0W0set := by rw [hc3pow]
          _ = c • (c • (c • ggX0W0set)) := by
                rw [show c ^ 3 = c * (c * c) by rw [pow_succ, pow_succ, pow_one, mul_assoc],
                  mul_smul, mul_smul]
          _ ⊆ c • ggX0W0set := (Set.smul_set_mono h2).trans h2
      exact h3
    have hmem_span_d : ∀ m ∈ ggHalfX0SpanMasks ggHalfX0W0,
        ggHalfApplyBits (ggX0DBits D) m ∈ ggHalfX0SpanMasks ggHalfX0W0 :=
      ggX0SpanMasks_apply_subset
        (fun a ha b hb => of_decide_eq_true
          (List.all_eq_true.mp (List.all_eq_true.mp ggX0W0Span_xor a ha) b hb))
        (ggX0SpanMasks_zero ggHalfX0W0)
        (fun b hb => of_decide_eq_true (List.all_eq_true.mp hdfix b hb))
    have hsub_d : d • ggX0W0set ⊆ ggX0W0set := by
      intro v hv
      rw [ggX0_smul_W0set d, hdbits] at hv
      simp only [Set.mem_setOf_eq] at hv
      rw [ggHalfX0SpanMasks_map_apply, List.mem_map] at hv
      obtain ⟨m, hm, hmm⟩ := hv
      change ggHalfVecBits v ∈ ggHalfX0SpanMasks ggHalfX0W0
      rw [← hmm]
      exact hmem_span_d m hm
    have hdset : d • ggX0W0set = ggX0W0set := by
      let f : (Fin 27 →₀ GaloisField 2 1) ↪ (Fin 27 →₀ GaloisField 2 1) :=
        ⟨fun x => d • x, fun x y hxy => by
          simpa using congrArg (fun z => d⁻¹ • z) hxy⟩
      have hsub : f '' ggX0W0set ⊆ ggX0W0set := by
        change Set.image (fun x => d • x) ggX0W0set ⊆ ggX0W0set
        exact hsub_d
      have h := Set.map_eq_of_subset (f := f) hsub
        (hs := Set.finite_univ.subset (Set.subset_univ _))
      change d • ggX0W0set = ggX0W0set
      exact h
    let T : Subgroup GGE6Two := Subgroup.closure ((ggHalfM0.J0 : Set GGE6Two) ∪ {c, d})
    have hTle : T ≤ ggX0H D := by
      change Subgroup.closure ((ggHalfM0.J0 : Set GGE6Two) ∪ {c, d}) ≤ ggX0H D
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      rcases hx with hxJ | hxcd
      · exact Subgroup.mem_sup_left hxJ
      · rcases hxcd with rfl | rfl
        · exact hword_mem_H D.cGen
        · exact hword_mem_H D.dGen
    have hT_semi : 6 * Nat.card (ggHalfM0.J0) ≤ Nat.card T :=
      ggHalf_card_ge_semidirect (ggHalfM0.J0) c d hc3ord hcJ hcnot hd'
    have hfixT : ∀ t ∈ T, t • ggX0W0set = ggX0W0set := by
      have hstab : T ≤ MulAction.stabilizer GGE6Two ggX0W0set := by
        change Subgroup.closure ((ggHalfM0.J0 : Set GGE6Two) ∪ {c, d}) ≤
          MulAction.stabilizer GGE6Two ggX0W0set
        refine (Subgroup.closure_le _).2 ?_
        intro x hx
        rcases hx with hxJ | hxcd
        · have hJ0stab : ggHalfM0.J0 ≤ MulAction.stabilizer GGE6Two ggX0W0set := by
            rw [show ggHalfM0.J0 = Subgroup.closure {g | ∃ a b : Fin 8, 2 ≤ a.val ∧ a.val < 6 ∧
                2 ≤ b.val ∧ b.val < 6 ∧ a ≠ b ∧ g = ggE6x (ggHalfM0.frame .L a b)} from rfl]
            refine (Subgroup.closure_le _).2 ?_
            rintro g ⟨a, b, ha, ha', hb, hb', hab, rfl⟩
            obtain ⟨i, hi, hframe⟩ := ggHalfM0_frame_J0Idx a b ha ha' hb hb' hab
            rw [hframe]
            change ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD i 0)) • ggX0W0set = ggX0W0set
            rw [ggX0_smul_W0set (ggE6x (e6Certificate.root (ggHalfX0J0Idx.getD i 0))),
              ggE6Bits_x (ggX0J0Idx_getD_lt (i := i) (by omega)), ← ggX0J0GensBits_getD hi,
              of_decide_eq_true (List.all_eq_true.mp ggX0J0FixW0_eq i (List.mem_range.mpr hi))]
            rfl
          exact hJ0stab hxJ
        · rcases hxcd with rfl | rfl
          · exact hcset
          · exact hdset
      intro t ht
      exact hstab ht
    have hH : ∀ i : Fin 1632, ggX0SubGen D i ∈ ggX0H D := by
      intro i
      have hnode : (ggX0SubNodes D).getD i.1 (1, []) ∈ ggX0SubNodes D := by
        rw [List.getD_eq_getElem (l := ggX0SubNodes D) (d := (1, []))
          (by rw [ggX0SubNodes_length D hs]; exact i.2)]
        exact List.getElem_mem _
      exact (ggX0SubNodes_spec D h hcAll hs _ hnode).1
    have horbit := ggHalf_card_ge_of_orbit (ggX0H D) T ggX0W0set 1632
      (fun i : Fin 1632 => ggX0SubGen D i) hH (ggX0SubGen_smul_inj D h hcAll hs) hTle hfixT
      (6 * Nat.card (ggHalfM0.J0)) hT_semi
    calc 197406720 = 1632 * (6 * 20160) := by norm_num
      _ ≤ 1632 * (6 * Nat.card (ggHalfM0.J0)) :=
          Nat.mul_le_mul_left 1632 (Nat.mul_le_mul_left 6 card_J0_ge)
      _ ≤ Nat.card (ggX0H D) := horbit

theorem ggHalfX0_holds_P :
    GGHalfX0 ggHalfM0 1 :=
  ggX0_holds_general ggHalfX0DataP ggX0Bounds_P ggX0CheapFacts_P ggX0SubFacts_P hu_P

theorem ggHalfX0_holds_N :
    GGHalfX0 ggHalfM0 (-1) :=
  ggX0_holds_general ggHalfX0DataN ggX0Bounds_N ggX0CheapFacts_N ggX0SubFacts_N hu_N

theorem ggHalfE6Cert_holds :
    GGHalfE6Cert :=
  ⟨ggHalfM0, ggHalfM0_good, ggHalfX0_holds_P, ggHalfX0_holds_N⟩

end CFSG.StandardType

end
