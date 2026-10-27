module

public import CFSG.LocalAnalysis.StandardType.GGK0LCData
public import CFSG.LocalAnalysis.StandardType.GGK0LCDataE8
public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
public import CFSG.LocalAnalysis.StandardType.GGKacTableShapes

public section

namespace CFSG.StandardType.GGK0LC

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.GGK0MarkedKacIface1587
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

private def lk0xlckp_d : GGKacType → ℕ
  | .E6 => 3
  | .E7 => 2
  | .E8 => 1
  | .F4 => 1

private theorem lk0xlckp_length_eq (T : GGKacType) :
    (k0DiagOf T).marks.length = (absTag T).rank + 1 := by
  cases T <;> rfl

private theorem lk0xlckp_box (T : GGKacType) :
    KacBox (absTag T) := by
  cases T
  · exact kacBox_E6
  · exact kacBox_E7
  · exact kacBox_E8
  · exact kacBox_F4

private theorem lk0xlckp_centred (T : GGKacType) :
    KacCentred (absTag T) (lk0xlckp_d T) := by
  cases T
  · exact kacCentred_E6
  · exact kacCentred_E7
  · exact kacCentred_E8
  · exact kacCentred_F4

private theorem lk0xlckp_weight (T : GGKacType) (τ : Tag) (hτ : absTag T = τ)
    (p : ℕ) (s : List ℕ) (hs : s ∈ k0VecsAux (k0DiagOf T).marks p) :
    s.getD 0 0 + ∑ i : Fin τ.rank, hr τ i * s.getD (i.val + 1) 0 = p := by
  subst hτ
  cases T
  ·
    change s.getD 0 0 + ∑ i : Fin 6, hr .E6 i * s.getD (i.val + 1) 0 = p
    have h := ggKacShVecs_sum (k0DiagOf .E6).marks p s hs
    rw [show (k0DiagOf .E6).marks.length = 7 from rfl] at h
    rw [show (k0DiagOf .E6).marks = [1, 1, 2, 2, 3, 2, 1] from rfl] at h
    rw [Fin.sum_univ_succ] at h
    change [1, 1, 2, 2, 3, 2, 1].getD 0 0 * s.getD 0 0
      + ∑ i : Fin 6, [1, 1, 2, 2, 3, 2, 1].getD (Fin.succ i).val 0 *
          s.getD (Fin.succ i).val 0 = p at h
    have h0 : [1, 1, 2, 2, 3, 2, 1].getD 0 0 = 1 := by decide
    rw [h0, one_mul] at h
    have hkey : ∀ i : Fin 6, [1, 1, 2, 2, 3, 2, 1].getD (Fin.succ i).val 0 = hr .E6 i := by
      intro i
      fin_cases i <;> decide
    have hsum : (∑ i : Fin 6,
          [1, 1, 2, 2, 3, 2, 1].getD (Fin.succ i).val 0 * s.getD (Fin.succ i).val 0) =
        ∑ i : Fin 6, hr .E6 i * s.getD (i.val + 1) 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hkey i]
      rfl
    rw [hsum] at h
    exact h
  ·
    change s.getD 0 0 + ∑ i : Fin 7, hr .E7 i * s.getD (i.val + 1) 0 = p
    have h := ggKacShVecs_sum (k0DiagOf .E7).marks p s hs
    rw [show (k0DiagOf .E7).marks.length = 8 from rfl] at h
    rw [show (k0DiagOf .E7).marks = [1, 2, 2, 3, 4, 3, 2, 1] from rfl] at h
    rw [Fin.sum_univ_succ] at h
    change [1, 2, 2, 3, 4, 3, 2, 1].getD 0 0 * s.getD 0 0
      + ∑ i : Fin 7, [1, 2, 2, 3, 4, 3, 2, 1].getD (Fin.succ i).val 0 *
          s.getD (Fin.succ i).val 0 = p at h
    have h0 : [1, 2, 2, 3, 4, 3, 2, 1].getD 0 0 = 1 := by decide
    rw [h0, one_mul] at h
    have hkey : ∀ i : Fin 7, [1, 2, 2, 3, 4, 3, 2, 1].getD (Fin.succ i).val 0 = hr .E7 i := by
      intro i
      fin_cases i <;> decide
    have hsum : (∑ i : Fin 7,
          [1, 2, 2, 3, 4, 3, 2, 1].getD (Fin.succ i).val 0 * s.getD (Fin.succ i).val 0) =
        ∑ i : Fin 7, hr .E7 i * s.getD (i.val + 1) 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hkey i]
      rfl
    rw [hsum] at h
    exact h
  ·
    change s.getD 0 0 + ∑ i : Fin 8, hr .E8 i * s.getD (i.val + 1) 0 = p
    have h := ggKacShVecs_sum (k0DiagOf .E8).marks p s hs
    rw [show (k0DiagOf .E8).marks.length = 9 from rfl] at h
    rw [show (k0DiagOf .E8).marks = [1, 2, 3, 4, 6, 5, 4, 3, 2] from rfl] at h
    rw [Fin.sum_univ_succ] at h
    change [1, 2, 3, 4, 6, 5, 4, 3, 2].getD 0 0 * s.getD 0 0
      + ∑ i : Fin 8, [1, 2, 3, 4, 6, 5, 4, 3, 2].getD (Fin.succ i).val 0 *
          s.getD (Fin.succ i).val 0 = p at h
    have h0 : [1, 2, 3, 4, 6, 5, 4, 3, 2].getD 0 0 = 1 := by decide
    rw [h0, one_mul] at h
    have hkey : ∀ i : Fin 8,
        [1, 2, 3, 4, 6, 5, 4, 3, 2].getD (Fin.succ i).val 0 = hr .E8 i := by
      intro i
      fin_cases i <;> decide
    have hsum : (∑ i : Fin 8,
          [1, 2, 3, 4, 6, 5, 4, 3, 2].getD (Fin.succ i).val 0 * s.getD (Fin.succ i).val 0) =
        ∑ i : Fin 8, hr .E8 i * s.getD (i.val + 1) 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hkey i]
      rfl
    rw [hsum] at h
    exact h
  ·
    change s.getD 0 0 + ∑ i : Fin 4, hr .F4 i * s.getD (i.val + 1) 0 = p
    have h := ggKacShVecs_sum (k0DiagOf .F4).marks p s hs
    rw [show (k0DiagOf .F4).marks.length = 5 from rfl] at h
    rw [show (k0DiagOf .F4).marks = [1, 2, 3, 4, 2] from rfl] at h
    rw [Fin.sum_univ_succ] at h
    change [1, 2, 3, 4, 2].getD 0 0 * s.getD 0 0
      + ∑ i : Fin 4, [1, 2, 3, 4, 2].getD (Fin.succ i).val 0 *
          s.getD (Fin.succ i).val 0 = p at h
    have h0 : [1, 2, 3, 4, 2].getD 0 0 = 1 := by decide
    rw [h0, one_mul] at h
    have hkey : ∀ i : Fin 4, [1, 2, 3, 4, 2].getD (Fin.succ i).val 0 = hr .F4 i := by
      intro i
      fin_cases i <;> decide
    have hsum : (∑ i : Fin 4,
          [1, 2, 3, 4, 2].getD (Fin.succ i).val 0 * s.getD (Fin.succ i).val 0) =
        ∑ i : Fin 4, hr .F4 i * s.getD (i.val + 1) 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hkey i]
      rfl
    rw [hsum] at h
    exact h

private theorem lk0xlckp_a_eq {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ}
    {R : Type} [Group R] {I : Set (MulAut R)} {phi : MulAut R}
    (A : K0LangMark Omega lab p R I phi) (i : Fin A.tau.rank) :
    A.a i = A.zeta ^ (A.row.s.getD (i.val + 1) 0) := by
  have hlen : A.row.diagram.marks.length = A.tau.rank + 1 := by
    show (k0DiagOf A.row.T).marks.length = A.tau.rank + 1
    rw [lk0xlckp_length_eq A.row.T, A.tau_eq]
  have hlt : i.val + 1 < A.row.diagram.marks.length := by
    rw [hlen]
    exact Nat.succ_lt_succ i.isLt
  have h1 := A.node_eval ⟨i.val + 1, hlt⟩
  have hstd := A.node_std ⟨i.val + 1, hlt⟩ i (by rfl)
  rw [hstd] at h1
  have h2 : CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar A.a
      (Pi.single i 1) = A.a i := by
    simpa using
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_nsmul_single A.a i 1
  rw [h2] at h1
  simpa using h1

private theorem lk0xlckp_not_dvd {lab : LargeEvenLabel} {p : ℕ} (hpair : GGKacExcPair lab p)
    (hc : GGKacCentred lab p) (T : GGKacType) (tw : Bool)
    (htype : ggKacTypeOfLabel lab = some (T, tw)) : ¬ p ∣ lk0xlckp_d T := by
  have hpprime : p.Prime := hpair.1
  cases T
  ·
    have htag : lab.tag = .E6 ∨ lab.tag = .twE6 := by
      cases htag : lab.tag <;> simp [ggKacTypeOfLabel, htag] at htype ⊢
    intro hdvd
    have hp_le : p ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hp_ge : 2 ≤ p := hpprime.two_le
    have hp_ne2 : p ≠ 2 := hpair.2.1
    have hp3 : p = 3 := by omega
    exact hc ⟨htag, hp3⟩
  ·
    intro hdvd
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hp_ge : 2 ≤ p := hpprime.two_le
    have hp2 : p = 2 := by omega
    exact hpair.2.1 hp2
  ·
    intro hdvd
    have hp_le : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
    have hp_ge : 2 ≤ p := hpprime.two_le
    omega
  ·
    intro hdvd
    have hp_le : p ≤ 1 := Nat.le_of_dvd (by norm_num) hdvd
    have hp_ge : 2 ≤ p := hpprime.two_le
    omega

theorem k0_kacPt {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]
    {lab : LargeEvenLabel} {p : ℕ}
    {R : Type} [Group R] {I : Set (MulAut R)}
    {phi : MulAut R} (hpair : GGKacExcPair lab p) (hc : GGKacCentred lab p)
    (A : K0LangMark Omega lab p R I phi) :
    ∃ (K : KacPt A.tau) (d : ℕ), KacBox A.tau ∧ KacCentred A.tau d ∧ K.p = p ∧ p.Prime ∧
      ¬ p ∣ d ∧ ∀ i, A.a i = A.zeta ^ K.s i := by
  refine ⟨{ p := p
            p_pos := hpair.1.pos
            s := fun i => A.row.s.getD (i.val + 1) 0
            s0 := A.row.s.getD 0 0
            weight := lk0xlckp_weight A.row.T A.tau A.tau_eq p A.row.s A.row.s_mem },
    lk0xlckp_d A.row.T, ?_, ?_, rfl, hpair.1, ?_, ?_⟩
  · rw [← A.tau_eq]
    exact lk0xlckp_box A.row.T
  · rw [← A.tau_eq]
    exact lk0xlckp_centred A.row.T
  · exact lk0xlckp_not_dvd hpair hc A.row.T A.row.tw A.row.type_eq
  · intro i
    exact lk0xlckp_a_eq A i

end CFSG.StandardType.GGK0LC

end
