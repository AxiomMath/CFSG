module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceTypes
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112SliceDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

abbrev F112Conc : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Subgroup G → Subgroup G → Subgroup G → Prop

@[expose] def F112ConclPred : F112Conc :=
  fun _ _ _ L1 L2 S => F112Concl L1 L2 S

@[expose] def F112ConclPredLegacyBare : F112Conc :=
  fun _ _ _ L1 L2 S => F112ConclLegacyBare L1 L2 S

@[expose] def F112SliceSS (C : F112Conc) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairSS L1 L2 → C G L1 L2 S

@[expose] def F112SliceTits (C : F112Conc) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairTits L1 L2 → C G L1 L2 S

@[expose] def F112SliceS3Big (C : F112Conc) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairS3Big L1 L2 → C G L1 L2 S

@[expose] def F112SliceFDBig : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairFDBig L1 L2 → False

@[expose] def F112SliceBig (C : F112Conc) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairBig L1 L2 → C G L1 L2 S

@[expose] def F112SliceExotic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → PairExotic L1 L2 → False

theorem f112_of_slices {C : F112Conc} (hss : F112SliceSS C) (htits : F112SliceTits C)
    (hs3 : F112SliceS3Big C) (hfd : F112SliceFDBig) (hbig : F112SliceBig C)
    (hex : F112SliceExotic) :
    ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G), F112Hyp L1 L2 S → C G L1 L2 S := by
  intro G _ _ L1 L2 S h
  rcases f112_pair_cases L1 L2 with p | p | p | p | p | p
  · exact hss G L1 L2 S h p
  · exact htits G L1 L2 S h p
  · exact hs3 G L1 L2 S h p
  · exact (hfd G L1 L2 S h p).elim
  · exact hbig G L1 L2 S h p
  · exact (hex G L1 L2 S h p).elim

theorem f112Statement_of_slices (hss : F112SliceSS F112ConclPred)
    (htits : F112SliceTits F112ConclPred) (hs3 : F112SliceS3Big F112ConclPred)
    (hfd : F112SliceFDBig) (hbig : F112SliceBig F112ConclPred) (hex : F112SliceExotic) :
    F112Statement :=
  f112Statement_iff.2 fun G _ _ L1 L2 S h =>
    f112_of_slices hss htits hs3 hfd hbig hex G L1 L2 S h

theorem f112LegacyPrintedError_of_slices (hss : F112SliceSS F112ConclPredLegacyBare)
    (htits : F112SliceTits F112ConclPredLegacyBare) (hs3 : F112SliceS3Big F112ConclPredLegacyBare)
    (hfd : F112SliceFDBig) (hbig : F112SliceBig F112ConclPredLegacyBare) (hex : F112SliceExotic) :
    F112LegacyPrintedError :=
  f112LegacyPrintedError_iff.2 fun G _ _ L1 L2 S h =>
    f112_of_slices hss htits hs3 hfd hbig hex G L1 L2 S h

section Ordered

variable {C : F112Conc} (hC : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
  C G L2 L1 S → C G L1 L2 S)

include hC in
theorem F112SliceTits.of_ordered
    (h : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VFD L1 → VS3 L2 → C G L1 L2 S) : F112SliceTits C := by
  intro G _ _ L1 L2 S hh hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h G L1 L2 S hh h1 h2
  · exact hC G L1 L2 S (h G L2 L1 S hh.symm h2 h1)

include hC in
theorem F112SliceS3Big.of_ordered
    (h : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VS3 L1 → VBig L2 → C G L1 L2 S) : F112SliceS3Big C := by
  intro G _ _ L1 L2 S hh hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h G L1 L2 S hh h1 h2
  · exact hC G L1 L2 S (h G L2 L1 S hh.symm h2 h1)

end Ordered

theorem F112SliceFDBig.of_ordered
    (h : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VFD L1 → VBig L2 → False) : F112SliceFDBig := by
  intro G _ _ L1 L2 S hh hp
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h G L1 L2 S hh h1 h2
  · exact h G L2 L1 S hh.symm h2 h1

theorem F112SliceExotic.of_parts
    (hu : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VU3two L1 → False)
    (hd : ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
      F112Hyp L1 L2 S → VFD L1 → VFD L2 → False) : F112SliceExotic := by
  intro G _ _ L1 L2 S hh hp
  rcases hp with h | h | ⟨h1, h2⟩
  · exact hu G L1 L2 S hh h
  · exact hu G L2 L1 S hh.symm h
  · exact hd G L1 L2 S hh h1 h2

end CFSG.Quasithin
