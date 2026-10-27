module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps136ClassicalOrders

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps136

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise Matrix

private lemma w1369_nat_realizes_card {V : Type} [CommGroup V] [Finite V]
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (GL ι K)} (H : Subgroup (MulAut V))
    (h : (FFModel.nat Γ).Realizes H ⊤ ⊥) :
    Nat.card V = Nat.card K ^ Fintype.card ι := by
  classical
  rw [FFModel.Realizes] at h
  obtain ⟨π, hπ⟩ := h
  rw [FFModel.RealizesVia] at hπ
  obtain ⟨-, -, -, -, -, -, -, β, hβsurj, hβker, -⟩ := hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 : (u : V) ∈ (⊥ : Subgroup V) := (hβker u).mp hu
    exact Subtype.ext (by simpa using (Subgroup.mem_bot.mp h1))
  have hcard : Nat.card ↥(⊤ : Subgroup V) =
      Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
        (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤) :=
    Nat.card_congr (Equiv.ofBijective β ⟨hβinj, hβsurj⟩)
  calc
    Nat.card V = Nat.card ↥(⊤ : Subgroup V) :=
      Nat.card_congr (Subgroup.topEquiv (G := V)).toEquiv.symm
    _ = Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K))) ⧸
          (⊥ : Subgroup (Multiplicative (ι → K))).subgroupOf ⊤) := hcard
    _ = Nat.card (↥(⊤ : Subgroup (Multiplicative (ι → K)))) := by
      rw [Subgroup.bot_subgroupOf]
      exact Nat.card_congr
        (QuotientGroup.quotientBot (G := ↥(⊤ : Subgroup (Multiplicative (ι → K))))).toEquiv
    _ = Nat.card (Multiplicative (ι → K)) :=
      Nat.card_congr (Subgroup.topEquiv (G := Multiplicative (ι → K))).toEquiv
    _ = Nat.card K ^ Fintype.card ι := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_eq_fintype_card (α := ι)]

theorem w1369_mcl_nat_card {M : Type} [CommGroup M] [Finite M]
    (H : Subgroup (MulAut M)) (hMcL : McLShape H) (hcard : Nat.card ↥H = 168) :
    Nat.card M = 8 := by
  unfold McLShape at hMcL
  rcases hMcL with ⟨m, hSL, hNat⟩ | ⟨m, hSp, hNatSp⟩ | ⟨m, hOP, hNatOP⟩ |
    ⟨m, hOM, hNatOM⟩ | ⟨n, hAlt, hNatAlt⟩
  · unfold BinaryNaturalSL at hNat
    obtain ⟨K, hKfield, hKfinite, hKcard, hReal⟩ := hNat
    letI : Field K := hKfield
    letI : Finite K := hKfinite
    have hm : m = 3 := w1369_card_sl_eq_168 hSL hcard
    subst hm
    have hV : Nat.card M = Nat.card K ^ Fintype.card (Fin 3) :=
      w1369_nat_realizes_card (K := K) (Γ := StatedSL 3 K) H hReal
    rw [hV, hKcard]
    norm_num
  · exact absurd hcard (w1369_card_sp_ne_168 hSp)
  · exact absurd hcard (w1369_card_omegaPlus_ne_168 hOP)
  · exact absurd hcard (w1369_card_omegaMinus_ne_168 hOM)
  · exact absurd hcard (w1369_card_alt_ne_168 hAlt)

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps136
