module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Defs
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Sym
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Wr
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Sp
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Unit
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Orth
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Orth63
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenSmallCls

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem nine3_one_le_of_card_eq_two_pow {F : Type} [Field F] [Finite F] {n : ℕ}
    (h : Nat.card F = 2 ^ n) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := Nat.lt_one_iff.mp (not_le.mp hn)
  rw [hn0, pow_zero] at h
  have hlt : 1 < Nat.card F := Finite.one_lt_card
  omega

private theorem nine3_one_le_of_card_eq_two_pow_sq {F : Type} [Field F] [Finite F] {n : ℕ}
    (h : Nat.card F = (2 ^ n) ^ 2) : 1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := Nat.lt_one_iff.mp (not_le.mp hn)
  rw [hn0, pow_zero] at h
  norm_num at h
  have hlt : 1 < Nat.card F := Finite.one_lt_card
  omega

private theorem nine3_prop710_transport {X M : Type} [Group X] [Group M] {O : Subgroup X}
    [O.Normal] (ψ : X ⧸ O ≃* M) {s : X} {a e v : X ⧸ O}
    (hmodel : ∃ d : M, IsConj (ψ (QuotientGroup.mk s)) d ∧ d ≠ ψ v ∧
      d * ψ a = ψ a * d ∧ d * ψ e = ψ e * d) :
    ∃ d : X ⧸ O, IsConj (QuotientGroup.mk s) d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  obtain ⟨d, hdconj, hdne, hda, hde⟩ := hmodel
  refine ⟨ψ.symm d, ?_, ?_, ?_, ?_⟩
  · simpa using MonoidHom.map_isConj ψ.symm.toMonoidHom hdconj
  · intro hv
    exact hdne (by simpa using congrArg ψ hv)
  · simpa using congrArg (⇑ψ.symm) hda
  · simpa using congrArg (⇑ψ.symm) hde

theorem nine3_prop710 {X : Type} [Group X] [Finite X] {s : X} {O : Subgroup X} [O.Normal]
    (hcl : Nine3Classical X s O) {a e a' v : X ⧸ O}
    (h : Nine3Config (QuotientGroup.mk s) a e a' v) :
    ∃ d : X ⧸ O, IsConj (QuotientGroup.mk s) d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  unfold Nine3Classical at hcl
  rcases hcl with ⟨m, n, hsp, hO⟩ | ⟨m, n, huni, hO⟩ | ⟨m, n, horth, hO⟩ |
    ⟨n, m, hwr, hO⟩ | ⟨n, hsym, hO⟩ | h63
  · subst O
    obtain ⟨k, _hmk, F, hFld, hFin, hcard, ψ, hψ⟩ := hsp
    letI : Field F := hFld
    letI : Finite F := hFin
    have hn1 : 1 ≤ n := nine3_one_le_of_card_eq_two_pow hcard
    exact nine3_prop710_transport ψ
      (nine3_prop710_sp ⟨n, hn1, hcard⟩ hψ (Nine3Config.map ψ h))
  · subst O
    obtain ⟨F, hFld, hFin, hcard, ψ, hψ⟩ := huni
    letI : Field F := hFld
    letI : Finite F := hFin
    have hn1 : 1 ≤ n := nine3_one_le_of_card_eq_two_pow_sq hcard
    exact nine3_prop710_transport ψ
      (nine3_prop710_unitary hn1 hcard hψ (Nine3Config.map ψ h))
  · subst O
    rcases horth with ⟨k, hk, _hm, F, hFld, hFin, hcard, ψ, hc⟩ |
      ⟨k, hk, _hm, F, hFld, hFin, hcard, b, c', hbc, ψ, hc⟩
    · letI : Field F := hFld
      letI : Finite F := hFin
      have hn1 : 1 ≤ n := nine3_one_le_of_card_eq_two_pow hcard
      exact nine3_prop710_transport ψ
        (nine3_prop710_orthPlus hk ⟨n, hn1, hcard⟩ hc (Nine3Config.map ψ h))
    · letI : Field F := hFld
      letI : Finite F := hFin
      have hn1 : 1 ≤ n := nine3_one_le_of_card_eq_two_pow hcard
      exact nine3_prop710_transport ψ
        (nine3_prop710_orthMinus hk ⟨n, hn1, hcard⟩ hbc hc (Nine3Config.map ψ h))
  · subst O
    obtain ⟨hn1, F, hFld, hFin, hcard, ψ, i, j, hij, hψ⟩ := hwr
    letI : Field F := hFld
    letI : Finite F := hFin
    exact nine3_prop710_transport ψ
      (nine3_prop710_wreath hn1 hcard hij hψ (Nine3Config.map ψ h))
  · subst O
    obtain ⟨ψ, hψ⟩ := hsym
    exact nine3_prop710_transport ψ
      (nine3_prop710_sym hψ (Nine3Config.map ψ h))
  · obtain ⟨F, hFld, hFin, hcardF, b, c', hbc, N, hN1, hN2, φ, hφsurj, hker, _hcardO,
      _hcen, r, hr, hr1, hrs⟩ := h63
    letI : Field F := hFld
    letI : Finite F := hFin
    let ψ : X ⧸ O ≃* ↥N :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
    have hψs : ψ (QuotientGroup.mk s) = φ s := by
      change (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
          (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
          (QuotientGroup.mk s) = φ s
      rw [MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
      exact QuotientGroup.kerLift_mk (φ := φ) s
    have hcr : ((ψ (QuotientGroup.mk s) : ↥N) :
        Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
        Matrix.ProjGenLinGroup.mk r := by
      rw [hψs]
      exact hrs
    exact nine3_prop710_transport ψ
      (nine3_prop710_orth63 hcardF hbc N hN1 hN2 hr hr1 hcr (Nine3Config.map ψ h))

theorem nine3_classical_of_smallAlt {X : Type} [Group X] {S : Subgroup X}
    (h : SevenElevenSmallAltCls X S) :
    ∃ s ∈ S, s ≠ 1 ∧ ∃ O : Subgroup X, O.Normal ∧ Nine3Classical X s O := by
  unfold SevenElevenSmallAltCls at h
  obtain ⟨hS, hcl⟩ := h
  have hSne : S ≠ ⊥ := by
    intro hbot
    rw [hbot] at hS
    simp at hS
  obtain ⟨s, hsne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSne
  have hsne' : (s : X) ≠ 1 := fun hh => hsne (Subtype.ext hh)
  refine ⟨(s : X), s.2, hsne', ?_⟩
  rcases hcl with ⟨m, n, h4⟩ | ⟨n, hsym⟩ | h63
  · rcases h4 with ⟨_hSp, hsp⟩ | ⟨_hPSU, huni⟩ | horth | hwr
    · exact ⟨Subgroup.center X, inferInstance, Or.inl ⟨m, n, hsp s s.2 hsne', rfl⟩⟩
    · exact ⟨Subgroup.center X, inferInstance,
        Or.inr (Or.inl ⟨m, n, huni s s.2 hsne', rfl⟩)⟩
    · exact ⟨Subgroup.center X, inferInstance,
        Or.inr (Or.inr (Or.inl ⟨m, n, horth s s.2 hsne', rfl⟩))⟩
    · exact ⟨Subgroup.center X, inferInstance,
        Or.inr (Or.inr (Or.inr (Or.inl ⟨n, m, hwr s s.2 hsne', rfl⟩)))⟩
  · exact ⟨fusionOddCore X, inferInstance,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hsym s s.2 hsne', rfl⟩))))⟩
  · obtain ⟨F, hFld, hFin, hcardF, b, c', hbc, N, hN1, hN2, φ, hφsurj, hcardO, hcen,
      r, hr, hr1, hrs⟩ := h63 s s.2 hsne'
    exact ⟨φ.ker, φ.normal_ker,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨F, hFld, hFin, hcardF, b, c', hbc, N, hN1, hN2, φ, hφsurj, rfl, hcardO, hcen,
          r, hr, hr1, hrs⟩))))⟩

end CFSG.LocalAnalysis.WeakClosure81
