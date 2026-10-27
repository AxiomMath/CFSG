module

public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmHyp
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenA3OmBlock

public section

namespace CFSG.StandardType

namespace CoordOm

open Polynomial Module Multiplicative CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)

section Single

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime]
  {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ} {F : SevOm.Frame Q p A r} {E J : Subgroup (V ≃ₗ[K] V)}

theorem exists_fin_ne_of_four_le {r : ℕ} (hr : 4 ≤ r) (a : Fin r) : ∃ m : Fin r, m ≠ a := by
  refine ⟨⟨if a.val = 0 then 1 else 0, by split_ifs <;> omega⟩, fun h => ?_⟩
  have hv : (if a.val = 0 then 1 else 0) = a.val := congrArg Fin.val h
  by_cases h0 : a.val = 0
  · rw [if_pos h0] at hv; omega
  · rw [if_neg h0] at hv; omega

theorem GGOmA3Hyp.exists_full_support_of_single (H : GGOmA3Hyp F E J) {a : Fin r}
    (hY : ∀ m : Fin r, F.ι (ofAdd (Pi.single m 1)) ∈ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) →
      m = a) :
    ∃ (t : Fin r → ZMod p) (h : K[X]), F.ι (ofAdd t) ∈ E ∧ t a = 0 ∧ (∀ m, m ≠ a → t m ≠ 0) ∧
      h ∈ primaryFactors (F.ι (ofAdd t)).toLinearMap ∧ h ≠ X - 1 ∧
      J ≤ supportedBlock Q (F.ι (ofAdd t)) h ∧
      F.U a ≤ othersSpace (F.ι (ofAdd t)).toLinearMap h := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨t, htE, ht0, hta⟩ := exists_ne_zero_apply_eq_zero F H.le_A H.card_E a
  obtain ⟨h, hh, hJB, hpiece⟩ :=
    exists_factor_of_mem H.nondeg H.tsub H.ne_two F H.le_orthDerived H.max H.le_A
      H.isComponent htE
  have hnot : ∀ m : Fin r, m ≠ a →
      F.ι (ofAdd (Pi.single m 1)) ∉
        Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) := fun m hm hmem => hm (hY m hmem)
  have hfull : ∀ m, m ≠ a → t m ≠ 0 := by
    intro m hm htm
    have hU : F.U m ≤ orbitSpace (F.ι (ofAdd t)).toLinearMap h := hpiece m (hnot m hm)
    have hX : h = X - 1 :=
      eq_X_sub_one_of_apply_eq_zero H.nondeg H.ne_two F H.le_orthDerived hh htm hU
    exact ht0 (funext fun k => by
      by_cases hk : k = a
      · rw [hk]; exact hta
      · have hU' : F.U k ≤ orbitSpace (F.ι (ofAdd t)).toLinearMap (X - 1) := by
          rw [← hX]; exact hpiece k (hnot k hk)
        exact apply_eq_zero_of_le_orbitSpace_X_sub_one F hU')
  have hne_X : h ≠ X - 1 := by
    intro hX
    obtain ⟨m, hm⟩ := exists_fin_ne_of_four_le H.four_le a
    have hU : F.U m ≤ orbitSpace (F.ι (ofAdd t)).toLinearMap (X - 1) := by
      rw [← hX]; exact hpiece m (hnot m hm)
    exact hfull m hm (apply_eq_zero_of_le_orbitSpace_X_sub_one F hU)
  have hUa : F.U a ≤ othersSpace (F.ι (ofAdd t)).toLinearMap h := by
    rcases frame_piece_dichotomy H.nondeg H.tsub hp H.ne_two F H.le_orthDerived H.max
      (ofAdd t) hh a with h1 | h1
    · exact absurd
        (eq_X_sub_one_of_apply_eq_zero H.nondeg H.ne_two F H.le_orthDerived hh hta h1) hne_X
    · exact h1
  exact ⟨t, h, htE, hta, hfull, hh, hne_X, hJB, hUa⟩

theorem GGOmA3Hyp.exists_decomp_of_single (H : GGOmA3Hyp F E J) {a : Fin r}
    (ha : F.ι (ofAdd (Pi.single a 1)) ∈ E) {t : Fin r → ZMod p} (ht : F.ι (ofAdd t) ∈ E)
    (hta : t a = 0) (hfull : ∀ m, m ≠ a → t m ≠ 0) {s : Fin r → ZMod p}
    (hs : F.ι (ofAdd s) ∈ E) :
    ∃ c₁ c₂ : ZMod p, s = c₁ • (Pi.single a 1 : Fin r → ZMod p) + c₂ • t := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  haveI : Finite E := inferInstance
  obtain ⟨m₀, hm₀⟩ := exists_fin_ne_of_four_le H.four_le a
  set c₂ : ZMod p := s m₀ / t m₀ with hc₂
  have hs'E : F.ι (ofAdd (s - c₂ • t)) ∈ E := by
    rw [ofAdd_sub, _root_.map_div]
    exact E.div_mem hs (StepTwoToral.ofAdd_smul_mem ht c₂)
  have hs'0 : (s - c₂ • t) m₀ = 0 := by
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc₂, div_mul_cancel₀ _ (hfull m₀ hm₀),
      sub_self]
  have hs'van : ∀ m₁, m₁ ≠ a → (s - c₂ • t) m₁ = 0 := by
    intro m₁ hm₁
    by_contra hne
    have hle := card_ge_of_three (F := F) (H := E)
      (h₁ := ha) (h₂ := hs'E) (h₃ := ht)
      (k₁ := a) (k₂ := m₁) (k₃ := m₀)
      (hv₁ := by rw [Pi.single_eq_same]; exact one_ne_zero)
      (hv₂ := hne) (hv₃ := hfull m₀ hm₀)
      (h12 := by rw [Pi.single_eq_of_ne hm₁])
      (h13 := by rw [Pi.single_eq_of_ne hm₀])
      (h23 := hs'0)
    rw [H.card_E] at hle
    exact absurd hle (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
  refine ⟨(s - c₂ • t) a, c₂, ?_⟩
  funext m
  by_cases hm : m = a
  · subst hm
    simp [hta, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  · have h0 : s m = c₂ * t m := sub_eq_zero.mp (hs'van m hm)
    rw [h0]
    simp [Pi.single_eq_of_ne hm, smul_eq_mul]

theorem GGOmA3Hyp.isComponentOf_single (H : GGOmA3Hyp F E J) {a : Fin r}
    (ha : F.ι (ofAdd (Pi.single a 1)) ∈ E) {t : Fin r → ZMod p} {h : K[X]}
    (ht : F.ι (ofAdd t) ∈ E) (hta : t a = 0) (hfull : ∀ m, m ≠ a → t m ≠ 0)
    (hh : h ∈ primaryFactors (F.ι (ofAdd t)).toLinearMap)
    (hJB : J ≤ supportedBlock Q (F.ι (ofAdd t)) h)
    (hUa : F.U a ≤ othersSpace (F.ι (ofAdd t)).toLinearMap h) :
    IsComponentOf J (orthDerived Q ⊓
      Subgroup.centralizer ({F.ι (ofAdd t)} : Set (V ≃ₗ[K] V))) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hx : OddOrderIsometry Q p (F.ι (ofAdd t)) :=
    F.oddOrderIsometry H.nondeg H.ne_two hp H.le_orthDerived (ofAdd t)
  refine isComponentOf_centralizer_of_le_block (b := F.ι (ofAdd t)) hx hh ht H.isComponent hJB ?_
  intro e he
  obtain ⟨s, hs⟩ := F.exists_eq (H.le_A he)
  have hsE : F.ι (ofAdd (toAdd s)) ∈ E := by
    rw [ofAdd_toAdd]
    exact hs.symm ▸ he
  obtain ⟨c₁, c₂, hsc⟩ := H.exists_decomp_of_single ha ht hta hfull hsE
  have hb_eq : F.ι (ofAdd (c₂ • t)) = (F.ι (ofAdd t)) ^ c₂.val := by
    have h1 : c₂ • t = c₂.val • t := by
      funext i
      rw [Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val, smul_eq_mul]
    rw [h1, ofAdd_nsmul, map_pow]
  refine ⟨c₂.val, F.ι (ofAdd (c₁ • (Pi.single a 1 : Fin r → ZMod p))), ?_, ?_, ?_⟩
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (frame_comm F (F.mem _) (F.mem _))
  · rw [← hs]
    change F.ι (ofAdd (toAdd s)) =
      (F.ι (ofAdd t)) ^ c₂.val * F.ι (ofAdd (c₁ • (Pi.single a 1 : Fin r → ZMod p)))
    rw [hsc, ofAdd_add, map_mul, frame_comm F (F.mem _) (F.mem _), hb_eq]
  · refine frame_triv_orbit F hx hh ?_
    intro j hj
    have hj' : (c₁ • (Pi.single a 1 : Fin r → ZMod p)) j ≠ 0 := by
      simpa only [toAdd_ofAdd] using hj
    have hja : j = a := by
      by_contra hne
      exact hj' (by simp [Pi.smul_apply, Pi.single_eq_of_ne hne, smul_eq_mul])
    rw [hja]
    exact hUa

end Single

end CoordOm

end CFSG.StandardType
