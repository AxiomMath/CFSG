module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrCasesA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrCasesB
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrCasesD
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrSetup
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrIso
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13ThrNU

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W] {A : Subgroup (MulAut W)} {t : MulAut W}

theorem s13_2_four (hW : ∀ w : W, w * w = 1) {t : MulAut W} (ht : orderOf t = 2)
    (hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3) {P : Subgroup (MulAut W)}
    (hP3 : IsPGroup 3 ↥P) (hne : P ≠ ⊥) (hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P)
    (hc : ⁅P, Subgroup.zpowers t⁆ = P) (h4 : IsZ3TimesPOnePlusTwo ↥P ∨ IsZ3WrZ3 ↥P) :
    ∃! Q : Subgroup (MulAut W), Q ≤ P ∧ IsPOnePlusTwo 3 ↥Q ∧ rk ↥(commSub ⊤ Q) = 6 := by
  have htt : t * t = 1 := by
    rw [← pow_two, ← ht]
    exact pow_orderOf_eq_one t
  obtain ⟨V₀, hstab, hle, Q, ⟨hQP, hQext, hQrk⟩, hQuniq⟩ :=
    w16g_four_via_min hW ht hrk hP3 hne hn hc h4
  have hVP : StableUnder P V₀ := fun x hx v hv => hstab x (Subgroup.mem_sup_left hx) v hv
  have hVt : ∀ v ∈ V₀, t v ∈ V₀ := fun v hv =>
    hstab t (Subgroup.mem_sup_right (Subgroup.mem_zpowers t)) v hv
  have hM := w16g_commSub_eq_of_commSub_le hW htt hP3 hc hVP hVt hle
  refine ⟨Q, ⟨hQP, hQext, by rw [hM Q hQP]; exact hQrk⟩, ?_⟩
  rintro Q' ⟨hQ'P, hQ'ext, hQ'rk⟩
  exact hQuniq Q' ⟨hQ'P, hQ'ext, by rw [← hM Q' hQ'P]; exact hQ'rk⟩

theorem s13_case_four_N (h : Cfg133 A t 3)
    (h4 : IsZ3TimesPOnePlusTwo ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆) ∨
      IsZ3WrZ3 ↥(⁅pCoreOf 3 A, Subgroup.zpowers t⁆)) :
    ∃ L : Subgroup (MulAut W), L ≤ pCoreOf 3 A ∧ Conc4_133 A t L ∧ IsPOnePlusTwo 3 ↥L ∧
      rk ↥(commSub ⊤ L) = 6 ∧ ∀ n ∈ pCoreOf 3 A, L.map (MulAut.conj n).toMonoidHom = L := by
  classical
  let O : Subgroup (MulAut W) := pCoreOf 3 A
  let P : Subgroup (MulAut W) := ⁅O, Subgroup.zpowers t⁆
  obtain ⟨hPO, hPgrp, hPne, hnP, hcP, hOn⟩ := s13_P_facts h
  have ht2 : orderOf t = 2 := orderOf_eq_prime h.ht2 h.ht1
  obtain ⟨K, hKspec, hKuniq⟩ := s13_2_four h.hW ht2 h.hrk hPgrp hPne hnP hcP h4
  obtain ⟨hKP, hKext, hKrk⟩ := hKspec
  obtain ⟨z, hzK, hz3, hzc, hZK⟩ := w16g_ext_center_of_extraspecial hKext
  obtain ⟨hKeq, hKirr⟩ :=
    w16g_commSub_extraspecial_eq_and_irreducible h.hW hKext hzK hz3 hzc hZK hKrk
  have hKO : K ≤ O := hKP.trans hPO
  have htt : t * t = 1 := by rw [← pow_two]; exact h.ht2
  have ht_norm : t ∈ Subgroup.normalizer (P : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hnP y hy, fun hy => ?_⟩
    have hmem : t * (t * y * t⁻¹) * t⁻¹ ∈ P := hnP (t * y * t⁻¹) hy
    have hyy : t * (t * y * t⁻¹) * t⁻¹ = y := by
      rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_left htt]
      calc t * (t * y * t) * t = (t * t) * y * (t * t) := by group
        _ = y := by rw [htt]; simp
    rwa [hyy] at hmem
  have hOnT : ∀ y ∈ Subgroup.zpowers t, ∀ x ∈ P, y * x * y⁻¹ ∈ P := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr ht_norm hy) x).mp hx
  have hPmap : P.map (MulAut.conj t).toMonoidHom = P :=
    s13_map_conj_eq_of_normalizes hOnT (Subgroup.mem_zpowers t)
  have hKt_le : K.map (MulAut.conj t).toMonoidHom ≤ P := by
    have h := Subgroup.map_mono hKP (f := (MulAut.conj t).toMonoidHom)
    rwa [hPmap] at h
  have hKt_ext : IsPOnePlusTwo 3 ↥(K.map (MulAut.conj t).toMonoidHom) :=
    w16g_isPOnePlusTwo_of_mulEquiv
      (Subgroup.equivMapOfInjective K (MulAut.conj t).toMonoidHom (MulAut.conj t).injective) hKext
  have hKt_rk : rk ↥(commSub ⊤ (K.map (MulAut.conj t).toMonoidHom)) = 6 := by
    have hmap := CFSG.Quasithin.Asc81c.commSub_map_conj K t
    have hcard : Nat.card ↥((commSub ⊤ K).map t.toMonoidHom) = Nat.card ↥(commSub ⊤ K) :=
      Subgroup.card_map_of_injective (K := commSub ⊤ K) (f := t.toMonoidHom) t.injective
    have hsame : rk ↥((commSub ⊤ K).map t.toMonoidHom) = rk ↥(commSub ⊤ K) := by
      unfold rk
      rw [hcard]
    rw [hmap, hsame, hKrk]
  have hKt_eq : K.map (MulAut.conj t).toMonoidHom = K :=
    hKuniq _ ⟨hKt_le, hKt_ext, hKt_rk⟩
  have hKnorm : ∀ x ∈ K, t * x * t⁻¹ ∈ K := by
    intro x hx
    have hmem : (MulAut.conj t) x ∈ K.map (MulAut.conj t).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [MulAut.conj_apply] at hmem
    rwa [hKt_eq] at hmem
  have hOK : ∀ n ∈ O, K.map (MulAut.conj n).toMonoidHom = K := by
    intro n hn
    have hPn : P.map (MulAut.conj n).toMonoidHom = P :=
      s13_map_conj_eq_of_normalizes hOn hn
    have hKn_le : K.map (MulAut.conj n).toMonoidHom ≤ P := by
      have h := Subgroup.map_mono hKP (f := (MulAut.conj n).toMonoidHom)
      rwa [hPn] at h
    have hKn_ext : IsPOnePlusTwo 3 ↥(K.map (MulAut.conj n).toMonoidHom) :=
      w16g_isPOnePlusTwo_of_mulEquiv
        (Subgroup.equivMapOfInjective K (MulAut.conj n).toMonoidHom (MulAut.conj n).injective) hKext
    have hKn_rk : rk ↥(commSub ⊤ (K.map (MulAut.conj n).toMonoidHom)) = 6 := by
      have hmap := CFSG.Quasithin.Asc81c.commSub_map_conj K n
      have hcard : Nat.card ↥((commSub ⊤ K).map n.toMonoidHom) = Nat.card ↥(commSub ⊤ K) :=
        Subgroup.card_map_of_injective (K := commSub ⊤ K) (f := n.toMonoidHom) n.injective
      have hsame : rk ↥((commSub ⊤ K).map n.toMonoidHom) = rk ↥(commSub ⊤ K) := by
        unfold rk
        rw [hcard]
      rw [hmap, hsame, hKrk]
    exact hKuniq _ ⟨hKn_le, hKn_ext, hKn_rk⟩
  have hKodd : Odd (Nat.card K) := by rw [hKext.2.1]; norm_num
  have hOstab : StableUnder O (commSub ⊤ K) := s13_commSub_invariant_of_normalizes hOK
  have hirrO : IsIrrOn O (commSub ⊤ K) ⊥ := by
    refine ⟨hKirr.1, hOstab, ?_, ?_⟩
    · intro x hx u hu
      rw [Subgroup.mem_bot.mp hu, map_one]
      exact Subgroup.mem_bot.mpr rfl
    · intro J hJstab hJbot hJle
      exact hKirr.2.2.2 J (fun x hx => hJstab x (hKO hx)) hJbot hJle
  have hiso : IsEntireIsotypic K (commSub ⊤ K) := s13_isotypic_commSub h.hW hKodd
  have hss : sSupIndep (conjSubs A (commSub ⊤ K)) :=
    sSupIndep_conjSubs_of_isotypic h.hW A O K (s13_pCore_facts A 3).2.1
      (s13_pCore_facts A 3).1 hKO (commSub ⊤ K) hirrO hiso
  have hcardP : Nat.card P = 81 := by
    rcases h4 with hZ | hWr
    · obtain ⟨H, hinstH, hPext, ⟨e⟩⟩ := hZ
      letI := hinstH
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, hPext.2.1]
      norm_num
    · exact hWr.1
  have hKcommne : ⁅K, Subgroup.zpowers t⁆ ≠ ⊥ :=
    w16g_commSub_zpowers_t_ne_bot hPgrp hcardP ht2 hnP hcP hKP hKext
  refine ⟨K, hKO, ?_, hKext, hKrk, hOK⟩
  exact ⟨3, h.hp, hKO, hKcommne, hss, Or.inr (Or.inr (Or.inl ⟨hKext, hKrk⟩))⟩

end CFSG.LocalAnalysis.WeakClosure81
