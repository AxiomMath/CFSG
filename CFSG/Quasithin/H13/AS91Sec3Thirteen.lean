module

public import Certificates.Certificate89016
public import CFSG.Quasithin.H13.AS91Sec3Transport

public section

open scoped Pointwise

namespace CFSG.Quasithin.H13.AS91.M24G

open CFSG.ASVolI.ChH

section Cert


theorem zc_ne_zero_of_oneIn {p p' : ℕ} (hp : p < 3795) (hk : Native.oneIn p 0 = true)
    (hm : p' ∈ Native.sextTrios (Native.trioSexts ()) 0) :
    Native.zc (Native.trioList ())[p']! (Native.trioList ())[p]! ≠ 0 := by
  have h : Native.stmt313Check () = true := Certificates.certificate89016
  simp only [Native.stmt313Check, Bool.and_eq_true] at h
  have h2 := List.all_eq_true.1 h.1 p (List.mem_range.2 hp)
  simp only [hk, Bool.not_true, Bool.false_or] at h2
  exact bne_iff_ne.1 (List.all_eq_true.1 h2 p' hm)

theorem d2_iff {l k : ℕ} (hl : l < 3795) (hk : k < 3795) :
    (!(Native.meets (Native.trioList ())[l]! (Native.trioList ())[k]!) &&
      Native.coplanar (Native.trioSexts ()) l k) = true ↔ Delta (trioFin l) (trioFin k) 2 :=
  deltaB_iff hl hk 2

theorem exists_delta_two_base {p : ℕ} (hp : p < 3795)
    (hz : ((trioFin p).filter (InZeta (trioFin 0))).card = 0) :
    ∃ k, k < 3795 ∧ Delta (trioFin 0) (trioFin k) 2 ∧ Delta (trioFin p) (trioFin k) 2 := by
  have h0 : (0 : ℕ) < 3795 := by norm_num
  have h : Native.stmt313Check () = true := Certificates.certificate89016
  simp only [Native.stmt313Check, Bool.and_eq_true] at h
  have h3 := List.all_eq_true.1 h.2 p (List.mem_range.2 hp)
  have hz0 : Native.zc (Native.trioList ())[0]! (Native.trioList ())[p]! = 0 := by
    rw [zc_eq h0 hp]
    exact hz
  simp only [hz0, bne_self_eq_false, Bool.false_or, List.any_eq_true, List.mem_range] at h3
  obtain ⟨k, hk, hkk⟩ := h3
  rw [Bool.and_eq_true] at hkk
  exact ⟨k, hk, (d2_iff h0 hk).1 hkk.1, (d2_iff hp hk).1 hkk.2⟩

theorem delta_two_base {m : Finset (Finset (Fin 24))} (hm : IsTrio m)
    (hΔ : Delta (trioFin 0) m 4) : ∃ k, IsTrio k ∧ Delta (trioFin 0) k 2 ∧ Delta m k 2 := by
  obtain ⟨p, hp, rfl⟩ := (isTrio_iff m).1 hm
  have hz : ((trioFin p).filter (InZeta (trioFin 0))).card = 0 := hΔ
  obtain ⟨k, hk, h02, hpk⟩ := exists_delta_two_base hp hz
  exact ⟨trioFin k, isTrio_trioFin hk, h02, hpk⟩

theorem not_delta_four_base {l m : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hlU : Kappa (sextFin 0) l 1) (hm : IsTrio m) (hmU : TrioIn m (sextFin 0)) :
    ¬ Delta m l 4 := by
  obtain ⟨p, hp, rfl⟩ := (isTrio_iff l).1 hl
  obtain ⟨p', hp', rfl⟩ := (isTrio_iff m).1 hm
  have h0 : (0 : ℕ) < 1771 := by norm_num
  have hk : Native.oneIn p 0 = true := (oneIn_iff hp h0).2 hlU
  have hmem : p' ∈ Native.sextTrios (Native.trioSexts ()) 0 :=
    (sextTrios_iff h0).2 ⟨hp', hmU⟩
  have hne := zc_ne_zero_of_oneIn hp hk hmem
  rw [zc_eq hp' hp] at hne
  exact fun hΔ => hne hΔ

theorem not_delta_four_of_kappa_one {U l m : Finset (Finset (Fin 24))} (hU : IsSextet U)
    (hl : IsTrio l) (hlU : Kappa U l 1) (hm : IsTrio m) (hmU : TrioIn m U) : ¬ Delta m l 4 := by
  have hinv : ∀ g ∈ M24g, ∀ V : Finset (Finset (Fin 24)),
      (∀ a, IsTrio a → Kappa V a 1 → ∀ b, IsTrio b → TrioIn b V → ¬ Delta b a 4) →
      ∀ a, IsTrio a → Kappa (g • V) a 1 → ∀ b, IsTrio b → TrioIn b (g • V) → ¬ Delta b a 4 := by
    intro g hg V hPV a ha hκ b hb hTI hΔ
    have ha' : IsTrio (g⁻¹ • a) := (isTrio_smul_iff (M24g.inv_mem hg)).2 ha
    have hb' : IsTrio (g⁻¹ • b) := (isTrio_smul_iff (M24g.inv_mem hg)).2 hb
    have hκ' : Kappa V (g⁻¹ • a) 1 :=
      (kappa_smul_iff hg 1).1 (by rw [smul_inv_smul]; exact hκ)
    have hTI' : TrioIn (g⁻¹ • b) V := (trioIn_smul_iff g).1 (by rw [smul_inv_smul]; exact hTI)
    have hΔ' : Delta (g⁻¹ • b) (g⁻¹ • a) 4 :=
      (delta_smul_iff hg 4).1 (by rw [smul_inv_smul, smul_inv_smul]; exact hΔ)
    exact hPV (g⁻¹ • a) ha' hκ' (g⁻¹ • b) hb' hTI' hΔ'
  have key : ∀ a, IsTrio a → Kappa U a 1 → ∀ b, IsTrio b → TrioIn b U → ¬ Delta b a 4 :=
    forall_sextet_of_base
      (P := fun V => ∀ a, IsTrio a → Kappa V a 1 → ∀ b, IsTrio b → TrioIn b V → ¬ Delta b a 4)
      (fun g hg V hPV => hinv g hg V hPV)
      (fun a ha hκ b hb hTI => not_delta_four_base ha hκ hb hTI) hU
  exact key l hl hlU m hm hmU

theorem exists_delta_two_delta_two {l m : Finset (Finset (Fin 24))} (hl : IsTrio l)
    (hm : IsTrio m) (h : Delta l m 4) : ∃ k, IsTrio k ∧ Delta l k 2 ∧ Delta m k 2 := by
  have hinv : ∀ g ∈ M24g, ∀ a : Finset (Finset (Fin 24)),
      (∀ b, IsTrio b → Delta a b 4 → ∃ k, IsTrio k ∧ Delta a k 2 ∧ Delta b k 2) →
      ∀ b, IsTrio b → Delta (g • a) b 4 → ∃ k, IsTrio k ∧ Delta (g • a) k 2 ∧ Delta b k 2 := by
    intro g hg a hPa b hb hΔ
    have hb' : IsTrio (g⁻¹ • b) := (isTrio_smul_iff (M24g.inv_mem hg)).2 hb
    have hΔ' : Delta a (g⁻¹ • b) 4 := (delta_smul_iff hg 4).1 (by rw [smul_inv_smul]; exact hΔ)
    obtain ⟨k, hk, hak, hbk⟩ := hPa (g⁻¹ • b) hb' hΔ'
    refine ⟨g • k, (isTrio_smul_iff hg).2 hk, (delta_smul_iff hg 2).2 hak, ?_⟩
    have h2 := (delta_smul_iff hg 2).2 hbk
    rwa [smul_inv_smul] at h2
  have key : ∀ b, IsTrio b → Delta l b 4 → ∃ k, IsTrio k ∧ Delta l k 2 ∧ Delta b k 2 :=
    forall_trio_of_base
      (P := fun a => ∀ b, IsTrio b → Delta a b 4 → ∃ k, IsTrio k ∧ Delta a k 2 ∧ Delta b k 2)
      (fun g hg a hPa => hinv g hg a hPa) (fun b hb hΔ => delta_two_base hb hΔ) hl
  exact key m hm h

end Cert

end CFSG.Quasithin.H13.AS91.M24G
