module

public import CFSG.LocalAnalysis.StandardType.GGDepELLowLine
public import CFSG.LocalAnalysis.StandardType.GGDepELLowHK
public import CFSG.LocalAnalysis.StandardType.GGDepELLowPZB
public import CFSG.LocalAnalysis.StandardType.GGDepELLowEnc

public section

namespace CFSG.StandardType

open Certificates.DepED4Low Certificates.TwoDepSmall Certificates.DepASmall
  Certificates.TwoDepSmallLow

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nK1_check_one (d : DepELData) (h : ggDepELCheck d = true)
    (c0 : ℕ) (hc0 : c0 ∈ ggDepELNLeaves) :
    ∃ wits, d.one.lookup c0 = some wits ∧
      (∀ w ∈ wits, ggDepELTvValid 7 w = true) ∧
      ggDepELCases1 c0 wits ((d.excOne.lookup c0).getD []) = true := by
  have hh := h
  rw [ggDepELCheck] at hh
  have h1 := Bool.and_eq_true_iff.mp hh
  have h2 := Bool.and_eq_true_iff.mp h1.1
  have h3 := Bool.and_eq_true_iff.mp h2.1
  have hone : d.one.all (fun e => e.2.all (ggDepELTvValid 7)) = true := h3.1
  have hcases := List.all_eq_true.mp h2.2 c0 hc0
  cases hlook : d.one.lookup c0 with
  | none => rw [hlook] at hcases; simp at hcases
  | some wits =>
      rw [hlook] at hcases
      obtain ⟨l₁, l₂, hdata, -⟩ := List.lookup_eq_some_iff.mp hlook
      have hentry : (c0, wits) ∈ d.one := by
        rw [hdata]; simp
      have hwv : ∀ w ∈ wits, ggDepELTvValid 7 w = true := by
        intro w hw
        exact List.all_eq_true.mp
          (List.all_eq_true.mp hone (c0, wits) hentry) w hw
      exact ⟨wits, rfl, hwv, hcases⟩

private theorem l05nK1_cases1_extract (c0 : ℕ) (wits : List GGDepANWit)
    (exc : List ((List ℕ × List ℕ) × GGDepELReason))
    (h : ggDepELCases1 c0 wits exc = true) {lh la : List ℕ}
    (hlh : lh ∈ ggDepELSolH (fun c => if c = c0 then 2 else 0))
    (hla : la ∈ ggDepELSolA (fun c => if c = c0 then 2 else 0))
    (hd : ggDepANDot 3 la lh = 2) (hz : ggDepANDot 3 la ggDepELNX ≠ 0) :
    (∃ w ∈ wits, ggDepELTvTest [(lh, la)] w = true) ∨
      (∃ e ∈ exc, ggTWLVecEq 3 e.1.1 lh = true ∧ ggTWLVecEq 3 e.1.2 la = true ∧
        ggDepELReasonTest [(lh, la)] e.2 = true) := by
  simp only [ggDepELCases1] at h
  have h1 := List.all_eq_true.mp h lh hlh
  have h2 := List.all_eq_true.mp h1 la hla
  have hc : (ggDepANDot 3 la lh == 2 && ggDepANDot 3 la ggDepELNX != 0) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hd, bne_iff_ne.mpr hz⟩
  rw [if_pos hc] at h2
  cases hfind : exc.find?
      (fun e => ggTWLVecEq 3 e.1.1 lh && ggTWLVecEq 3 e.1.2 la) with
  | none =>
      rw [hfind] at h2
      exact Or.inl (List.any_eq_true.mp h2)
  | some e =>
      rw [hfind] at h2
      have hmem : e ∈ exc := List.mem_of_find?_eq_some hfind
      have hpred : (ggTWLVecEq 3 e.1.1 lh && ggTWLVecEq 3 e.1.2 la) = true :=
        List.find?_some (p := fun e => ggTWLVecEq 3 e.1.1 lh && ggTWLVecEq 3 e.1.2 la)
          (a := e) hfind
      rw [Bool.and_eq_true] at hpred
      exact Or.inr ⟨e, hmem, hpred.1, hpred.2, h2⟩

theorem ggDepELNotSurv1 (d : DepELData) (h : ggDepELCheck d = true) :
    ¬ GGDepED4LowSurv1 := by
  rintro ⟨c0, ha, αa, lam, mu, hleaf, hpair, hdot, hx, hlm, hfix, hkf, hko, hpz⟩
  have hc0 : c0.val ∈ ggDepELNLeaves := (ggDepELNLeaves_iff c0).mpr hleaf
  obtain ⟨wits, _hlook, hwv, hcases⟩ := l05nK1_check_one d h c0.val hc0
  obtain ⟨lh, la, hlh, hla, hd, hz, hvalid_pair, hnews_eq⟩ :=
    ggDepELEnc1 c0 hleaf ha αa hpair hdot hx
  have hvalid : ∀ q ∈ [(lh, la)], GGDepELNValid q := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact hvalid_pair
  have hla_eq : ggDepELToZ la = αa := by
    have hmem : (ggDepELToZ lh, ggDepELToZ la) ∈ ggDepELNNews [(lh, la)] :=
      ⟨(lh, la), by simp, rfl⟩
    rw [hnews_eq] at hmem
    rw [Set.mem_singleton_iff] at hmem
    exact congrArg Prod.snd hmem
  have hfix' : ∀ q ∈ [(lh, la)],
      ggDepAdot (ggDepELToZ q.2) (lam • ggDepELx + mu • ggDepELz) = 0 := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    rw [hla_eq]
    exact hfix
  have hx' : ∃ q ∈ [(lh, la)], ggDepAdot (ggDepELToZ q.2) ggDepELx ≠ 0 :=
    ⟨(lh, la), by simp, by rw [hla_eq]; exact hx⟩
  obtain hwit | hexc := l05nK1_cases1_extract c0 wits
    ((d.excOne.lookup c0.val).getD []) hcases hlh hla hd hz
  · obtain ⟨w, hwmem, hwtest⟩ := hwit
    have hv : ggDepELTvValid (6 + [(lh, la)].length) w = true := by
      have hlen : 6 + [(lh, la)].length = 7 := by
        simp only [List.length_cons, List.length_nil]
      rw [hlen]; exact hwv w hwmem
    have hkill := ggDepELTv_sound hvalid w hv hwtest
    rw [hnews_eq] at hkill
    exact hkf (Or.inl hkill)
  · obtain ⟨e, _hemem, _hp1, _hp2, hrt⟩ := hexc
    obtain ⟨e1, r⟩ := e
    cases r with
    | hk w =>
        obtain ⟨hY0len, t, ht, heq⟩ := ggDepELY0_line hvalid lam mu hlm hfix' hx'
        have htest : ggDepELHKTest [(lh, la)] (ggDepELY0 [(lh, la)]) w = true := hrt
        have hkill0 := ggDepELHKTest_sound hvalid
          (ggDepELY0 [(lh, la)]) hY0len w htest
        rw [hnews_eq] at hkill0
        have hs := (ggDepELKill_other_smul {(ha, αa)}
          (ggDepELToZ (ggDepELY0 [(lh, la)])) t ht).mpr hkill0
        rw [← heq] at hs
        exact hko hs
    | pz w =>
        obtain ⟨hY0len, t, ht, heq⟩ := ggDepELY0_line hvalid lam mu hlm hfix' hx'
        have htest : ggDepELPZTest [(lh, la)] (ggDepELY0 [(lh, la)]) w = true := hrt
        obtain ⟨hc0z, hpz0⟩ := ggDepELPZTest_sound hvalid
          (ggDepELY0 [(lh, la)]) hY0len w htest
        rw [hnews_eq] at hpz0
        have hcne : (w.c0 : ZMod 3) * t⁻¹ ≠ 0 := mul_ne_zero hc0z (inv_ne_zero ht)
        have harg : ggDepELx + (w.c0 : ZMod 3) •
              ggDepELToZ (ggDepELY0 [(lh, la)]) =
            ggDepELx + ((w.c0 : ZMod 3) * t⁻¹) •
              (lam • ggDepELx + mu • ggDepELz) := by
          have htoz : ggDepELToZ (ggDepELY0 [(lh, la)]) =
              t⁻¹ • (lam • ggDepELx + mu • ggDepELz) := by
            rw [heq, smul_smul, inv_mul_cancel₀ ht, one_smul]
          rw [htoz, smul_smul]
        rw [harg] at hpz0
        exact hpz ((w.c0 : ZMod 3) * t⁻¹) hcne hpz0

end CFSG.StandardType

end
