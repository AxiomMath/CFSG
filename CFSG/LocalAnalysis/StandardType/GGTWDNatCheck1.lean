module

public import CFSG.LocalAnalysis.StandardType.GGTWDNatSolve
public import CFSG.LocalAnalysis.StandardType.GGTWDNatWord

public section

namespace CFSG.StandardType

open Certificates.TwoDepSmallN Certificates.DepASmall Certificates.TwoDepSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l05nD3_X_length (N : ℕ) : (ggDepANX N).length = N := by
  simp [ggDepANX]

private lemma l05nD3_toZ_X {p N : ℕ} :
    ggDepANToZ p N (ggDepANX N) = ggDepAx p N := by
  funext j
  have hj : j.val < (ggDepANX N).length := by simp [ggDepANX, j.isLt]
  rw [ggDepANToZ, List.getD_eq_getElem (l := ggDepANX N) (d := 0) (n := j.val) hj]
  simp only [ggDepANX, ggDepAx, List.getElem_map, List.getElem_range]
  split <;> simp

private lemma l05nD3_cases1_extract {p N : ℕ} (posn c0 mi ni : ℕ) (wits : List GGDepANWit)
    (h : ggTWDCases1 p N posn c0 mi ni wits = true)
    {lh la : List ℕ}
    (hlh : lh ∈ ggTWDSolH p N posn (fun c => if c = c0 then (p - ni % p) % p else 0))
    (hla : la ∈ ggTWDSolA p N posn (fun c => if c = c0 then (p - mi % p) % p else 0))
    (hd : ggDepANDot p la lh = 2 % p)
    (hz : ggDepANDot p la (ggDepANX N) ≠ 0) :
    ∃ w ∈ wits, ggTWDWitTest p N [(lh, la)] w = true := by
  simp only [ggTWDCases1] at h
  have h1 := List.all_eq_true.mp h lh hlh
  have h2 := List.all_eq_true.mp h1 la hla
  have hc : (ggDepANDot p la lh == 2 % p && ggDepANDot p la (ggDepANX N) != 0) = true := by
    rw [Bool.and_eq_true]
    exact ⟨beq_iff_eq.mpr hd, bne_iff_ne.mpr hz⟩
  rw [if_pos hc] at h2
  exact List.any_eq_true.mp h2

theorem ggTWDCases1_sound {p N : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hN : 5 ≤ N) (pos : GGTWPos)
    (c0 : Fin (N - 1)) (mi ni : ℕ) (hmi : mi = 1 ∨ mi = 2) (hni : ni = 1 ∨ ni = 2)
    (wits : List GGDepANWit) (hwv : ∀ w ∈ wits, ggTWDWitValid N w = true)
    (hc : ggTWDCases1 p N (ggTWPosNat pos) c0.val mi ni wits = true) (ha αa : GGDepAE p N)
    (hpair : GGTWDPairs1 p N pos c0 (-(mi : ℤ)) (-(ni : ℤ)) ha αa)
    (hdot : ggDepAdot αa ha = 2) (hx : ggDepAdot αa (ggDepAx p N) ≠ 0) :
    ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
        ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g := by
  have hp3 : 3 ≤ p := by
    have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  have hni_lt : ni < p := by rcases hni with rfl | rfl <;> omega
  have hmi_lt : mi < p := by rcases hmi with rfl | rfl <;> omega
  have hvH : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot (ggDepAα p N c) ha =
        (((fun x => if x = c0.val then (p - ni % p) % p else 0) c.val : ℕ) : ZMod p) := by
    intro c hcJ
    have h2 := (hpair c hcJ).2
    by_cases hcc : c = c0
    · rw [hcc] at h2 ⊢
      rw [if_pos rfl] at h2
      change ggDepAdot (ggDepAα p N c0) ha =
        (((if c0.val = c0.val then (p - ni % p) % p else 0 : ℕ)) : ZMod p)
      rw [if_pos rfl, h2, Nat.mod_eq_of_lt hni_lt, l05nND_cast_neg p ni (le_of_lt hni_lt)]
      simp
    · rw [if_neg hcc] at h2
      have hne : c.val ≠ c0.val := fun hh => hcc (Fin.ext hh)
      change ggDepAdot (ggDepAα p N c) ha =
        (((if c.val = c0.val then (p - ni % p) % p else 0 : ℕ)) : ZMod p)
      rw [if_neg hne, h2]
      simp
  have hvA : ∀ c : Fin (N - 1), ggTWInJ N pos c.val →
      ggDepAdot αa (ggDepAh p N c) =
        (((fun x => if x = c0.val then (p - mi % p) % p else 0) c.val : ℕ) : ZMod p) := by
    intro c hcJ
    have h1 := (hpair c hcJ).1
    by_cases hcc : c = c0
    · rw [hcc] at h1 ⊢
      rw [if_pos rfl] at h1
      change ggDepAdot αa (ggDepAh p N c0) =
        (((if c0.val = c0.val then (p - mi % p) % p else 0 : ℕ)) : ZMod p)
      rw [if_pos rfl, h1, Nat.mod_eq_of_lt hmi_lt, l05nND_cast_neg p mi (le_of_lt hmi_lt)]
      simp
    · rw [if_neg hcc] at h1
      have hne : c.val ≠ c0.val := fun hh => hcc (Fin.ext hh)
      change ggDepAdot αa (ggDepAh p N c) =
        (((if c.val = c0.val then (p - mi % p) % p else 0 : ℕ)) : ZMod p)
      rw [if_neg hne, h1]
      simp
  obtain ⟨lh, hlh_mem, hlh_eq, hlh_len⟩ :=
    ggTWDSolH_complete (p := p) (N := N) pos
      (fun x => if x = c0.val then (p - ni % p) % p else 0) ha hvH
  obtain ⟨la, hla_mem, hla_eq, hla_len⟩ :=
    ggTWDSolA_complete (p := p) (N := N) pos
      (fun x => if x = c0.val then (p - mi % p) % p else 0) αa hvA
  have hd : ggDepANDot p la lh = 2 % p := by
    have h := ggDepANDot_cast (p := p) (N := N) la lh hla_len hlh_len
    rw [hla_eq, hlh_eq, hdot] at h
    have h2 : ((ggDepANDot p la lh : ℕ) : ZMod p) = ((2 % p : ℕ) : ZMod p) := by
      rw [ZMod.natCast_mod]; exact h
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    simpa [ggDepANDot, Nat.mod_mod] using h2
  have hz : ggDepANDot p la (ggDepANX N) ≠ 0 := by
    intro h0
    apply hx
    have h := ggDepANDot_cast (p := p) (N := N) la (ggDepANX N) hla_len (l05nD3_X_length N)
    rw [h0, Nat.cast_zero, hla_eq, l05nD3_toZ_X] at h
    exact h.symm
  obtain ⟨w, hwmem, hwtest⟩ :=
    l05nD3_cases1_extract (p := p) (N := N) (ggTWPosNat pos) c0.val mi ni wits hc
      hlh_mem hla_mem hd hz
  have hnews : ∀ q ∈ [(lh, la)], GGTWDValid p N q := by
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ⟨hlh_len, hla_len, hd⟩
  have hv' : ggTWDWitValid (N - 1 + [(lh, la)].length) w = true := by
    have hlen : N - 1 + [(lh, la)].length = N := by
      simp only [List.length_cons, List.length_nil]
      omega
    rw [hlen]
    exact hwv w hwmem
  obtain ⟨g, hmem, htv⟩ :=
    ggTWDTv_sound (p := p) (N := N) hp2 hN (news := [(lh, la)]) hnews w hv' hwtest
  have hset : {s : Module.End (ZMod p) (GGDepAE p N) |
      ∃ q ∈ [(lh, la)], s = ggTWDRflOf p N q} = {ggDepARefl ha αa} := by
    ext s
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [List.mem_singleton] at hq
      subst hq
      rw [Set.mem_singleton_iff]
      simp only [ggTWDRflOf, hlh_eq, hla_eq]
    · intro hs
      rw [Set.mem_singleton_iff] at hs
      exact ⟨(lh, la), by simp, by simp only [ggTWDRflOf, hlh_eq, hla_eq, hs]⟩
  have hgens : ggTWDGens p N [(lh, la)] =
      Set.range (fun i : Fin (N - 1) => ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
        {ggDepARefl ha αa} := by
    simp only [ggTWDGens, hset]
  exact ⟨g, by rw [← hgens]; exact hmem, htv⟩

end CFSG.StandardType

end
