module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7Y
import all CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23O7Y
public import CFSG.GroupActions.EquivariantGenerators

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23O7

open CFSG.YGroups CFSG.LieType.Multipliers.O73
open CFSG.Monster.B.Co2.Native CFSG.YGroups.ModelNative
open CFSG.Certificates.CosetEnumeration
open CFSG.Monster.B.Co2
open Matrix

attribute [local irreducible] betaArr y322Arrays


theorem exists_y322_matrix_refl :
    ∃ ρ : YGroup 3 2 2 →* GL Idx (ZMod 3), Function.Injective ρ ∧
      (∀ i : Fin 8, (ρ (yGen 3 2 2 i.val) : Matrix Idx Idx (ZMod 3)) = rMat (vecs i)) ∧
        ρ y322F1 = -1 := by
  have hgen : ∀ i : Fin 8, ρ (yGen 3 2 2 i.val) = rG i.val := fun i =>
    CFSG.YGroups.yModelHom_yGen i.2
  have hcode : ∀ c < 8, ∀ x : Fin 728,
      ψ (ρ (yGen 3 2 2 c)) (βf x) = βf (y322Model (yGen 3 2 2 c) x) := by
    intro c hc x
    rw [hgen ⟨c, hc⟩]
    apply Fin.ext
    have htab : Rep 2187 rTabs[c]! (ψ (rG c)) := by
      rw [rTabs, getElem!_ofFn' _ hc]
      exact rep_tabOf (by simp [rG, hc])
    have h1 := htab (βf x)
    change (rTabs[c]!)[betaArr[x.val]!]! = (ψ (rG c) (βf x)).val at h1
    rw [← h1]
    change (rTabs[c]!)[betaArr[x.val]!]! = betaArr[(y322Model (yGen 3 2 2 c) x).val]!
    rw [beta_check.2.2.2 ⟨c, hc⟩ x, ← y322Model_rep hc x]
  have hinj : Function.Injective ρ :=
    CFSG.GroupActions.injective_of_equivariant_on_generators _ (closure_yGen 3 2 2)
      ρ y322Model y322Model_injective ψ βf
      (fun x y h => beta_check.2.2.1 x y (congrArg Fin.val h)) (by
        rintro _ ⟨c, hc, rfl⟩ x
        exact hcode c (by simpa [ngen] using hc) x)
  have hρword : ∀ w : List ℕ, (∀ c ∈ w, c < 8) →
      ρ (evalWord (yGen 3 2 2) w) =
        mOne ^ w.length * τ (evalWord (yGen 3 2 2) w) := by
    intro w hw
    induction w with
    | nil => simp
    | cons c w ih =>
      have hc : c < 8 := hw c (by simp)
      have htail : ∀ d ∈ w, d < 8 := fun d hd => hw d (by simp [hd])
      have hτgen : τ (yGen 3 2 2 c) = tG c := yModelHom_yGen hc
      rw [evalWord_cons, map_mul, map_mul, hgen ⟨c, hc⟩, ih htail, hτgen]
      have hrc : rG c = mOne * tG c := by
        ext a b
        simp only [rG, tG, hc, dite_true, mOne, Units.val_neg, tMat, neg_one_mul]
        exact (neg_neg _).symm
      rw [hrc]
      have hcomm : tG c * mOne ^ w.length = mOne ^ w.length * tG c := by
        exact (Commute.pow_right (by simp [mOne] : Commute (tG c) mOne) _).eq
      rw [List.length_cons, pow_succ', mul_assoc, ← mul_assoc (tG c), hcomm]
      group
  have hf : ρ y322F1 = -1 := by
    have h := hρword y322WordF1 (by decide)
    change ρ y322F1 = mOne ^ y322WordF1.length * τ y322F1 at h
    have hτ : τ y322F1 = 1 := by
      have hfmem : y322WordF1 ∈ eWords := by
        unfold eWords
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..))
      have hmap : ∀ w : List ℕ, τ (evalWord (yGen 3 2 2) w) = evalWord (fun c => τ (yGen 3 2 2 c)) w := by
        intro w
        induction w with
        | nil => simp
        | cons c w ih => rw [evalWord_cons, map_mul, ih, evalWord_cons]
      have htgen : ∀ c ∈ y322WordF1, τ (yGen 3 2 2 c) = tG c := by
        intro c hc
        exact yModelHom_yGen (show c < ngen 3 2 2 from
          (by decide : ∀ d ∈ y322WordF1, d < 8) c hc)
      rw [y322F1, hmap, evalWord_congr (g' := tG) htgen]
      exact evalWord_tG_eq_one (List.mem_append_right _ hfmem)
    rw [hτ, mul_one, show y322WordF1.length = 63 by decide] at h
    have hm2 : mOne * mOne = 1 := by simp [mOne]
    have hm : mOne ^ 63 = (-1 : GL Idx (ZMod 3)) := by
      rw [show 63 = 2 * 31 + 1 by decide, pow_succ, pow_mul, pow_two,
        hm2, one_pow, one_mul]
      rfl
    exact h.trans hm
  refine ⟨ρ, hinj, fun i => ?_, hf⟩
  rw [hgen]
  simp [rG, i.2]

end CFSG.HardMathSupport.Dickson.I271.TabFi23O7
