module

public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Misc
public import CFSG.Quasithin.Background.D2Seventeen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section JFacts

variable {V : Type*} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)}

theorem Jhat_conj_mem {g : MulAut V} (hg : g ∈ X) {j : MulAut V} (hj : j ∈ Jhat X) :
    g * j * g⁻¹ ∈ Jhat X := by
  have hle : Jhat X ≤ (Jhat X).comap (MulAut.conj g).toMonoidHom := by
    refine iSup₂_le fun A hA a ha => ?_
    have hmem : g * a * g⁻¹ ∈ conjBy g A := mem_conjBy_of_mem ha
    exact le_Jhat (conjBy_mem_QhatStar hA hg) hmem
  exact hle hj

theorem le_normalizer_Jhat : X ≤ Subgroup.normalizer (Jhat X : Set (MulAut V)) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨Jhat_conj_mem hg, fun hx => ?_⟩
  have := Jhat_conj_mem (X.inv_mem hg) hx
  simpa [mul_assoc] using this

theorem isSolvable_Jhat (hX : Group.IsSolvable ↥X) : Group.IsSolvable ↥(Jhat X) :=
  Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (Jhat_le X))

theorem pCoreOf_Jhat_eq_bot (hO2 : pCoreOf 2 X = ⊥) : pCoreOf 2 (Jhat X) = ⊥ := by
  have hle : pCoreOf 2 (Jhat X) ≤ pCoreOf 2 X := by
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans (Jhat_le X)) ?_
      (pCoreOf_isPGroup 2 _)
    exact le_normalizer_Jhat.trans (normalizer_le_normalizer_pCoreOf 2 _)
  rw [hO2, le_bot_iff] at hle
  exact hle

theorem odd_card_fittingOf_Jhat (hO2 : pCoreOf 2 X = ⊥) :
    Odd (Nat.card (fittingOf (Jhat X))) :=
  odd_card_fittingOf (pCoreOf_Jhat_eq_bot hO2)

theorem v0_invariant {j : MulAut V} (hj : j ∈ Jhat X) {w : V}
    (hw : w ∈ commV (fittingOf (Jhat X))) : j w ∈ commV (fittingOf (Jhat X)) := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨f, hf, v, rfl⟩ := hx
    have hjf : j * f * j⁻¹ ∈ fittingOf (Jhat X) := conj_mem_fittingOf hj hf
    refine Subgroup.subset_closure ⟨j * f * j⁻¹, hjf, j v, ?_⟩
    show (j * f * j⁻¹) (j v) * (j v)⁻¹ = j (f v * v⁻¹)
    simp [map_mul]
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [map_mul]
    exact Subgroup.mul_mem _ ihx ihy
  | inv x _ ih =>
    rw [map_inv]
    exact Subgroup.inv_mem _ ih

theorem commV_fitting_sup_fixV (hV : ∀ v : V, v ^ 2 = 1) (hO2 : pCoreOf 2 X = ⊥) :
    commV (fittingOf (Jhat X)) ⊔ fixV (fittingOf (Jhat X)) = ⊤ ∧
      commV (fittingOf (Jhat X)) ⊓ fixV (fittingOf (Jhat X)) = ⊥ := by
  have := coprime_decomp (odd_card_fittingOf_Jhat hO2) hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  simpa [commV_eq_commSub] using this

end JFacts

end CFSG.Quasithin
