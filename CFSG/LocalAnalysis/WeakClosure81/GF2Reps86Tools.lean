module

public import CFSG.Quasithin.Background.E3Defs
import CFSG.Quasithin.Background.CommVBasics
import CFSG.Quasithin.Background.D2Coprime
import CFSG.Quasithin.Background.InvolutionQuadratic
import CFSG.Quasithin.MS93.ML3Gen
import CFSG.GH74.QTGen4.Leaves.L14742Aut
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaLagArith

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

theorem index_le_eight_of_mQuot_le_three [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V}
    (h : CFSG.Quasithin.E3.mQuot ⊤ U ≤ 3) : U.index ≤ 8 := by
  have hp : IsPGroup 2 (⊤ : Subgroup V) := fun g => ⟨1, Subtype.ext (by simpa using hV g)⟩
  have h1 := E3.relIndex_eq_two_pow hp U
  rw [Subgroup.relIndex_top_right] at h1
  rw [h1]
  calc 2 ^ E3.mQuot ⊤ U ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h
    _ = 8 := by norm_num

theorem apply_eq_of_mem_commV_zpowers (hV : ∀ v : V, v ^ 2 = 1) {c : MulAut V} (hc : c ^ 2 = 1)
    {v : V} (hv : v ∈ commV (Subgroup.zpowers c)) : c v = v :=
  mem_fixV_zpowers_iff_apply.1 (commV_zpowers_le_fixV_of_involution hV hc hv)

theorem card_commV_zpowers [Finite V] (_hV : ∀ v : V, v ^ 2 = 1) {c : MulAut V}
    (_hc : c ^ 2 = 1) :
    Nat.card (commV (Subgroup.zpowers c)) = (fixV (Subgroup.zpowers c)).index := by
  rw [commV_zpowers_eq_map, ← MonoidHom.range_eq_map, ← ker_commHom, Subgroup.index_ker]

theorem commV_closure_le (S : Set (MulAut V)) :
    commV (Subgroup.closure S) ≤ ⨆ s ∈ S, commV (Subgroup.zpowers s) :=
  (MS93.commV_closure_eq_iSup S).le

theorem card_commV_closure_le [Finite V] (S : Finset (MulAut V)) :
    Nat.card (commV (Subgroup.closure (S : Set (MulAut V)))) ≤
      ∏ s ∈ S, Nat.card (commV (Subgroup.zpowers s)) := by
  classical
  have key : ∀ T : Finset (MulAut V), Nat.card ↥(⨆ s ∈ T, commV (Subgroup.zpowers s)) ≤
      ∏ s ∈ T, Nat.card (commV (Subgroup.zpowers s)) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert a T ha ih =>
      rw [Finset.iSup_insert, Finset.prod_insert ha]
      exact (MS93.card_sup_le_mul _ _).trans (Nat.mul_le_mul_left _ ih)
  have h1 : Nat.card (commV (Subgroup.closure (S : Set (MulAut V)))) ≤
      Nat.card ↥(⨆ s ∈ S, commV (Subgroup.zpowers s)) :=
    Subgroup.card_le_of_le (by simpa using commV_closure_le (S : Set (MulAut V)))
  exact h1.trans (key S)

theorem centralizes_commV_of_simple [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {E : Type*} [Group E]
    [Finite E] [IsSimpleGroup E] (hE : ¬ Nat.card E ∣ 168) (f : E →* MulAut V) {c : MulAut V}
    (hc : c ^ 2 = 1) (hcomm : ∀ e, f e * c = c * f e)
    (hidx : (fixV (Subgroup.zpowers c)).index ≤ 8) (e : E) {v : V}
    (hv : v ∈ commV (Subgroup.zpowers c)) : f e v = v := by
  have hpres : ∀ (e : E) (u : V), u ∈ commV (Subgroup.zpowers c) →
      f e u ∈ commV (Subgroup.zpowers c) := by
    intro e u hu
    refine commV_apply_mem_of_commute (A := Subgroup.zpowers c) (B := f.range) ?_
      (MonoidHom.mem_range.2 ⟨e, rfl⟩) hu
    rintro a ha b ⟨e', rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact ((Commute.zpow_right (hcomm e') k).symm).eq
  have hmem : ∀ e : E, f e ∈ stabSub (commV (Subgroup.zpowers c)) := fun e u =>
    ⟨fun h => by simpa using hpres e⁻¹ _ h, hpres e u⟩
  have hAut : Nat.card (MulAut (commV (Subgroup.zpowers c))) ∣ 168 :=
    CFSG.GH74.QTGen4.Leaves.L14742.card_mulAut_dvd_168 (fun a b => mul_comm a b)
      (fun a => Subtype.ext (by simpa using hV a)) ((card_commV_zpowers hV hc).le.trans hidx)
  have h1 := CFSG.SeitzReduction.SymplecticPilot.eq_one_of_isSimpleGroup_of_not_dvd
    ((resHom (commV (Subgroup.zpowers c))).comp (f.codRestrict _ hmem))
    (fun h => hE (h.trans hAut)) e
  exact congrArg (fun φ : MulAut (commV (Subgroup.zpowers c)) => (φ ⟨v, hv⟩ : V)) h1

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
