module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoShapeL2
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoShapeL3
public import CFSG.LocalAnalysis.WeakClosure81.W183K1
public import CFSG.LocalAnalysis.WeakClosure81.W183CF

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3 IsSp4 IsAlt OInf)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem shape186OddTriv_of_shapes {X : Type} [Group X]
    (hX : (IsL2 X 2 ∨ IsU3 X 2) ∨ IsSp4 X 2 ∨ CFSG.Quasithin.F6.IsL2 5 2 X ∨
      LieModel X .PSp 2 5 1) : Shape186OddTriv X := by
  rcases hX with (h | h) | h | h | h
  · exact Or.inl (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem shape54_to_seven (hO : LieOrderFormulasInput) (hCF : Tail1812TwoNoSectionCF)
    {Q : Type} [Group Q] [Finite Q] {H T L : Subgroup Q} (hShape : Shape54 H T L)
    (hfac : ∀ (X : Type) [Group X], (∃ φ : ↥L →* X, Function.Surjective φ ∧
        ∀ k : ↥L, φ k = 1 ↔ (k : Q) ∈ OInf H) → IsSimpleGroup X →
        (∃ u v : X, u * v ≠ v * u) → OddTranspFactor X) :
    HasQuotShape L (OInf H : Set Q) (fun X _ => IsL2 X 2 ∨ IsU3 X 2) ∨
    HasQuotShape L (OInf H : Set Q) (fun X _ => IsAlt X 6) ∨
    (HasQuotShape L (OInf H : Set Q) (fun X _ => IsSp4 X 2) ∧
      ∃ t ∈ T, ActsOnDynkinMod (OInf H) L t) ∨
    HasQuotShape L (OInf H : Set Q) (fun X _ => CFSG.Quasithin.F6.IsL2 5 2 X) ∨
    HasQuotShape L (OInf H : Set Q) (fun X _ => LieModel X .PSp 2 5 1) ∨
    HasQuotShape L (OInf H : Set Q) (fun X _ => LieModel X .PSp 2 3 1) := by
  rcases hShape with h1 | h2 | h3 | h4 | h5 | h6
  ·
    rcases h1 with ⟨X, hXg, φ, hφs, hφk, hX⟩
    letI : Group X := hXg
    exact Or.inl ⟨X, hXg, φ, hφs, hφk, hX⟩
  ·
    rcases h2 with ⟨X, hXg, φ, hφs, hφk, hX⟩
    letI : Group X := hXg
    rcases hX with hAlt | hL31
    · exact Or.inr (Or.inl ⟨X, hXg, φ, hφs, hφk, hAlt⟩)
    · obtain ⟨hf, hs, hnc⟩ :=
        isSimple_nonab_of_shape hO (Or.inr (Or.inr (Or.inr (Or.inl hL31))))
      haveI : Finite X := hf
      have hF := hfac X ⟨φ, hφs, hφk⟩ hs hnc
      have hS : Socle186Shape X := Or.inr (Or.inr (Or.inl hL31))
      exact (false_of_isL3_one_card_mem hO hL31
        (card_mem_of_tail1812Shape hO (hCF X hS hF))).elim
  ·
    rcases h3 with ⟨⟨X, hXg, φ, hφs, hφk, hX⟩, t, htT, hDyn⟩
    letI : Group X := hXg
    rcases hX with hL32 | hSp4
    · obtain ⟨hf, hs, hnc⟩ :=
        isSimple_nonab_of_shape hO (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL32)))))
      haveI : Finite X := hf
      have hF := hfac X ⟨φ, hφs, hφk⟩ hs hnc
      have hS : Socle186Shape X := Or.inr (Or.inr (Or.inr (Or.inl hL32)))
      exact (false_of_isL3_two_card_mem hO hL32
        (card_mem_of_tail1812Shape hO (hCF X hS hF))).elim
    · exact Or.inr (Or.inr (Or.inl ⟨⟨X, hXg, φ, hφs, hφk, hSp4⟩, t, htT, hDyn⟩))
  ·
    obtain ⟨p, e, hp, hp2, hq, X, hXg, φ, hφs, hφk, hX⟩ := h4
    letI : Group X := hXg
    obtain ⟨hf, hs, hnc⟩ := isSimple_nonab_of_shape hO
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨p, e, hp, hp2, hq, hX⟩)))))))
    haveI : Finite X := hf
    have hF := hfac X ⟨φ, hφs, hφk⟩ hs hnc
    have hS : Socle186Shape X :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨p, e, hp, hp2, hq, hX⟩))))))
    have hpe : p ^ e = 25 :=
      eq_of_isL2_card_mem hO hp hp2 hq hX (card_mem_of_tail1812Shape hO (hCF X hS hF))
    have hp5 : p = 5 := by
      rcases hp.eq_two_or_odd with h2 | hodd
      · exact absurd h2 hp2
      · have he0 : e ≠ 0 := by rintro rfl; simp at hq
        have hdvd : p ∣ 25 := hpe ▸ dvd_pow_self p he0
        have hdvd5 : p ∣ 5 := by
          rw [show (25 : ℕ) = 5 ^ 2 by norm_num] at hdvd
          exact hp.dvd_of_dvd_pow hdvd
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 hdvd5
    subst p
    have he2 : e = 2 := by
      have h55 : 5 ^ e = 5 ^ 2 := hpe.trans (by norm_num)
      exact Nat.pow_right_injective (by norm_num) h55
    subst e
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨X, hXg, φ, hφs, hφk, hX⟩)))
  ·
    obtain ⟨p, hp, hp2, hrest⟩ := h5
    rcases hrest with ⟨hmod, hQuot⟩ | ⟨hmod, hQuot⟩
    · rcases hQuot with ⟨X, hXg, φ, hφs, hφk, hX⟩
      letI : Group X := hXg
      obtain ⟨hf, hs, hnc⟩ := isSimple_nonab_of_shape hO
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨p, hp, hp2, Or.inl hX⟩)))))))
      haveI : Finite X := hf
      have hF := hfac X ⟨φ, hφs, hφk⟩ hs hnc
      have hS : Socle186Shape X :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨p, hp, hp2, Or.inl ⟨hmod, hX⟩⟩)))))))
      exact (false_of_psl_three_card_mem hO hp hp2 hX
        (card_mem_of_tail1812Shape hO (hCF X hS hF))).elim
    · rcases hQuot with ⟨X, hXg, φ, hφs, hφk, hX⟩
      letI : Group X := hXg
      obtain ⟨hf, hs, hnc⟩ := isSimple_nonab_of_shape hO
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨p, hp, hp2, Or.inr (Or.inl hX)⟩)))))))
      haveI : Finite X := hf
      have hF := hfac X ⟨φ, hφs, hφk⟩ hs hnc
      have hS : Socle186Shape X :=
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨p, hp, hp2, Or.inr ⟨hmod, hX⟩⟩)))))))
      exact (false_of_psu_three_card_mem hO hp hp2 hX
        (card_mem_of_tail1812Shape hO (hCF X hS hF))).elim
  ·
    obtain ⟨p, hp, hp2, X, hXg, φ, hφs, hφk, hX⟩ := h6
    letI : Group X := hXg
    obtain ⟨hf, hs, hnc⟩ := isSimple_nonab_of_shape hO
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p, hp, hp2, Or.inr (Or.inr hX)⟩)))))))
    haveI : Finite X := hf
    have hF := hfac X ⟨φ, hφs, hφk⟩ hs hnc
    have hS : Socle186Shape X :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨p, hp, hp2, hX⟩)))))))
    rcases eq_of_psp_card_mem hO hp hp2 hX
      (card_mem_of_tail1812Shape hO (hCF X hS hF)) with hp3 | hp5
    · subst p
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨X, hXg, φ, hφs, hφk, hX⟩))))
    · subst p
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨X, hXg, φ, hφs, hφk, hX⟩))))

end CFSG.LocalAnalysis.WeakClosure81

end
