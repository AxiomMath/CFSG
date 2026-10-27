module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K38Fam
import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRed
import CFSG.Holt.H78.Prelim
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K38B

open Subgroup CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Bar

variable {X : Type} [Group X] [Finite X] {q : ℕ} [hq : Fact q.Prime]

theorem false_of_borelConfig (hq2 : q ≠ 2) (hq3 : q ≠ 3) {Hb K : Subgroup X} {T : Sylow q K}
    (hB : BorelConfig q Hb K T) {W A : Subgroup X} (hW : IsPGroup 2 W) (hWH : W ≤ Hb)
    (hA : IsElemAbelian q A) (hAcard : q < Nat.card A) (hAH : A ≤ Hb)
    (hAW : A ≤ normalizer (W : Set X)) (hCW : centralizer (W : Set X) ≤ Hb) : False := by
  haveI := hB.normal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup X := (T : Subgroup K).map K.subtype with hQ
  have hQp : IsPGroup q Q := T.isPGroup'.map K.subtype
  obtain ⟨⟨a, haA, haK⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (inf_ne_bot_of_outPChain (hB.outPChain hq2 hq3) hB.centralizer_eq_bot hA hAcard)
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  set a' : K := ⟨a, haK⟩ with ha'
  have ha'1 : a' ≠ 1 := fun h => ha1' (congrArg Subtype.val h)
  have ha'N : a' ∈ normalizer ((T : Subgroup K) : Set K) :=
    (mem_normalizer_map_iff _ a').1 (hB.le_normalizer (hAH haA))
  have ha'p : IsPGroup q (zpowers a') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (Subtype.ext (by simpa using hA.2 a haA)) ha'1
  have ha'T : a' ∈ (T : Subgroup K) := by
    have hmem : a' ∈ zpowers a' ⊓ normalizer ((T : Subgroup K) : Set K) :=
      ⟨mem_zpowers a', ha'N⟩
    have h : zpowers a' ⊓ normalizer ((T : Subgroup K) : Set K) = zpowers a' ⊓ T :=
      ha'p.inf_normalizer_sylow T
    rw [h] at hmem
    exact hmem.2
  have haQ : a ∈ Q := ⟨a', ha'T, rfl⟩
  have haW : ∀ w ∈ W, w * a * w⁻¹ = a := by
    intro w hw
    have hc1 : a * w * a⁻¹ * w⁻¹ ∈ W :=
      W.mul_mem ((mem_normalizer_iff.1 (hAW haA) w).1 hw) (W.inv_mem hw)
    have hc2 : a * w * a⁻¹ * w⁻¹ ∈ Q := by
      have h1 : w * a⁻¹ * w⁻¹ ∈ Q :=
        (mem_normalizer_iff.1 (hB.le_normalizer (hWH hw)) a⁻¹).1 (Q.inv_mem haQ)
      have e : a * w * a⁻¹ * w⁻¹ = a * (w * a⁻¹ * w⁻¹) := by group
      rw [e]
      exact Q.mul_mem haQ h1
    have hc : a * w * a⁻¹ * w⁻¹ = 1 :=
      (IsPGroup.disjoint_of_ne 2 q (Ne.symm hq2) W Q hW hQp).le_bot ⟨hc1, hc2⟩
    have e : a * w = w * a := by
      calc a * w = (a * w * a⁻¹ * w⁻¹) * (w * a) := by group
        _ = w * a := by rw [hc, one_mul]
    rw [← e, mul_inv_cancel_right]
  set φ : X →* MulAut K := MulAut.conjNormal with hφ
  obtain ⟨k, hkV, hkN⟩ := exists_fixed_not_mem_normalizer hq2 T hB.ti (hB.card_sylow hq3)
    (W.map φ) (hW.map φ) ⟨a', ha'T, ha'1, by
      rintro _ ⟨w, hw, rfl⟩
      apply Subtype.ext
      rw [hφ, MulAut.conjNormal_apply]
      exact haW w hw⟩
  have hkC : (k : X) ∈ centralizer (W : Set X) := by
    rw [mem_centralizer_iff]
    intro w hw
    have h := congrArg Subtype.val (hkV (φ w) ⟨w, hw, rfl⟩)
    rw [hφ, MulAut.conjNormal_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  exact hkN ((mem_normalizer_map_iff _ k).1 (hB.le_normalizer (hCW hkC)))

end Bar

section Global

variable {G : Type} [Group G] [Finite G] {q : ℕ} [hq : Fact q.Prime]

theorem twoLocalPrimeRank_le_pRank (q : ℕ) [hq : Fact q.Prime] :
    twoLocalPrimeRank q G ≤ CFSG.Open.pRank q (⊤ : Subgroup G) := by
  apply csSup_le'
  rintro _ ⟨L, -, rfl⟩
  exact CFSG.SectionRank.pRank_mono hq.out.one_lt le_top

theorem exists_isMaxTwoLocal_ge {L : Subgroup G} (hL : IsTwoLocal L) :
    ∃ N : Subgroup G, IsMaxTwoLocalSubgroup N ∧ L ≤ N := by
  obtain ⟨N, hLN, hN⟩ := Finite.exists_le_maximal (p := IsTwoLocal) hL
  exact ⟨N, ⟨hN.1, fun K hK hNK => le_antisymm (hN.2 hK hNK) hNK⟩, hLN⟩

theorem not_normalizer_le (hq2 : q ≠ 2) (hq3 : q ≠ 3) {H : Subgroup G}
    (hodd : Odd (Nat.card (CFSG.pPrimeCore q G)))
    (hA : ∃ (K : Subgroup (G ⧸ CFSG.pPrimeCore q G)) (T : Sylow q K),
      BorelConfig q (H.map (QuotientGroup.mk' (CFSG.pPrimeCore q G))) K T)
    {W : Subgroup G} (hW : IsPGroup 2 W)
    (hrk : 1 < CFSG.Open.pRank q (normalizer (W : Set G))) :
    ¬ normalizer (W : Set G) ≤ H := by
  intro hNH
  obtain ⟨K, T, hB⟩ := hA
  haveI : (CFSG.pPrimeCore q G).Normal := CFSG.pPrimeCore_normal
  set O := CFSG.pPrimeCore q G with hO
  set π : G →* G ⧸ O := QuotientGroup.mk' O with hπ
  obtain ⟨A, hAN, hA, hAc⟩ :=
    CFSG.SectionRank.exists_pRank hq.out.one_lt (normalizer (W : Set G))
  have hdisj : Disjoint A O := Subgroup.disjoint_of_coprime_natCard (by
    rw [hAc]
    exact Nat.Coprime.pow_left _ CFSG.pPrimeCore_coprime_card)
  have hinj : Function.Injective (π.comp A.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haO : (a : G) ∈ O := by
      rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hπ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at ha
      exact ha
    exact Subtype.ext (hdisj.le_bot ⟨a.2, haO⟩)
  have hcard : Nat.card (A.map π) = Nat.card A := by
    have h := Subgroup.card_map_of_injective (K := (⊤ : Subgroup A)) hinj
    rwa [← MonoidHom.range_eq_map, MonoidHom.range_comp, Subgroup.range_subtype,
      Subgroup.card_top] at h
  refine false_of_borelConfig hq2 hq3 hB (W := W.map π) (A := A.map π) (hW.map π)
    (map_mono (le_normalizer.trans hNH)) (CFSG.SectionRank.isElemAbelian_map hA π) ?_
    (map_mono (hAN.trans hNH)) ((map_mono hAN).trans (le_normalizer_map π)) ?_
  · rw [hcard, hAc]
    calc q = q ^ 1 := (pow_one q).symm
      _ < q ^ CFSG.Open.pRank q (normalizer (W : Set G)) :=
        Nat.pow_lt_pow_right hq.out.one_lt hrk
  · rw [← CFSG.Holt.H78.map_centralizer_eq_of_odd O hodd hW]
    exact map_mono ((centralizer_le_normalizer _).trans hNH)

theorem exists_maxTwoLocal_not_le (hq2 : q ≠ 2) (hq3 : q ≠ 3) {H : Subgroup G}
    (hH : IsStronglyPEmbedded q H) (h1 : 1 < twoLocalPrimeRank q G)
    (hA : ∃ (K : Subgroup (G ⧸ CFSG.pPrimeCore q G)) (T : Sylow q K),
      BorelConfig q (H.map (QuotientGroup.mk' (CFSG.pPrimeCore q G))) K T) :
    ∃ N : Subgroup G, IsMaxTwoLocalSubgroup N ∧ 1 < CFSG.Open.pRank q N ∧
      ∀ g : G, ¬ N ≤ H.map (MulAut.conj g).toMonoidHom := by
  haveI : (CFSG.pPrimeCore q G).Normal := CFSG.pPrimeCore_normal
  set O := CFSG.pPrimeCore q G with hO
  have hp1 := hq.out.one_lt
  obtain ⟨L₀, hL₀, hL₀r⟩ : ∃ L₀ : Subgroup G, IsTwoLocal L₀ ∧ 1 < CFSG.Open.pRank q L₀ := by
    have hne : {k | ∃ L : Subgroup G, IsTwoLocal L ∧ CFSG.Open.pRank q L = k}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [twoLocalPrimeRank, h] at h1
      simp at h1
    obtain ⟨k, ⟨L₀, hL₀, rfl⟩, hk⟩ := exists_lt_of_lt_csSup hne h1
    exact ⟨L₀, hL₀, hk⟩
  have h2 : 2 ≤ CFSG.Open.pRank q (⊤ : Subgroup G) :=
    hL₀r.trans_le (CFSG.SectionRank.pRank_mono hp1 le_top)
  have hOH : O ≤ H := pPrimeCore_le_of_stronglyPEmbedded hH h2
  have hOHg : ∀ g : G, O ≤ H.map (MulAut.conj g).toMonoidHom := by
    intro g o ho
    refine ⟨g⁻¹ * o * g, hOH ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa using (inferInstance : O.Normal).conj_mem o ho g⁻¹
  have hHg : ∀ g : G, H.map (MulAut.conj g).toMonoidHom ≠ ⊤ := by
    intro g htop
    apply hH.1
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, hy, hyx⟩ := htop ▸ mem_top (MulAut.conj g x)
    rwa [(MulAut.conj g).injective hyx] at hy
  by_cases hodd : Odd (Nat.card O)
  ·
    obtain ⟨N, hN, hLN⟩ := exists_isMaxTwoLocal_ge hL₀
    refine ⟨N, hN, hL₀r.trans_le (CFSG.SectionRank.pRank_mono hp1 hLN), fun g hg => ?_⟩
    obtain ⟨V, -, hV, hNV⟩ := hN.1
    set W : Subgroup G := V.map (MulAut.conj g⁻¹).toMonoidHom with hW
    have hWV : W.map (MulAut.conj g).toMonoidHom = V := by
      rw [hW, Subgroup.map_map]
      convert Subgroup.map_id V
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hWN : normalizer (W : Set G) ≤ H := by
      intro x hx
      have h1 := le_normalizer_map (MulAut.conj g).toMonoidHom (mem_map_of_mem _ hx)
      rw [hWV, ← hNV] at h1
      obtain ⟨y, hy, hyx⟩ := hg h1
      rwa [(MulAut.conj g).injective hyx] at hy
    have hrk : 1 < CFSG.Open.pRank q (normalizer (W : Set G)) := by
      refine hL₀r.trans_le ((CFSG.SectionRank.pRank_mono hp1 hLN).trans
        ((CFSG.SectionRank.pRank_le_map hp1 (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective N).trans (CFSG.SectionRank.pRank_mono hp1 ?_)))
      rw [hNV]
      exact le_normalizer_map _
    exact not_normalizer_le hq2 hq3 hodd hA (hV.map _) hrk hWN
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2O : 2 ∣ Nat.card O := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q G))
    have hqO : ¬ q ∣ Nat.card O :=
      (Nat.Prime.coprime_iff_not_dvd hq.out).1 CFSG.pPrimeCore_coprime_card
    have hPO : (P : Subgroup G) ≤ normalizer (O : Set G) := by
      rw [normalizer_eq_top_iff.2 inferInstance]
      exact le_top
    have hPbot : (P : Subgroup G) ≤ normalizer ((⊥ : Subgroup G) : Set G) := by
      rw [normalizer_eq_top_iff.2 inferInstance]
      exact le_top
    obtain ⟨S, hS, -, hPS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing hq.out
      Nat.prime_two (A := (P : Subgroup G)) (M := O) (Q := ⊥) P.isPGroup' hqO hPO bot_le
      IsPGroup.of_bot hPbot
    obtain ⟨T₂, hT₂⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS
    have hfr : normalizer (S : Set G) ⊔ O = ⊤ := by
      have := Sylow.normalizer_sup_eq_top T₂
      rwa [hT₂] at this
    have hS1 : S ≠ ⊥ := by
      intro hS1
      have hTd : 2 ∣ Nat.card (T₂ : Subgroup O) := T₂.dvd_card_of_dvd_card h2O
      have hc : Nat.card S = Nat.card (T₂ : Subgroup O) := by
        rw [← hT₂]
        exact Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
      rw [hS1, Subgroup.card_bot] at hc
      rw [← hc] at hTd
      exact absurd (Nat.le_of_dvd one_pos hTd) (by norm_num)
    obtain ⟨N, hN, hSN⟩ := exists_isMaxTwoLocal_ge (L := normalizer (S : Set G))
      ⟨S, hS1, hS.2.1, rfl⟩
    haveI : (P : Subgroup G).FiniteIndex := Subgroup.finiteIndex_of_finite
    have hrkP : CFSG.Open.pRank q (⊤ : Subgroup G) ≤ CFSG.Open.pRank q (P : Subgroup G) :=
      CFSG.SectionRank.pRank_top_le_of_not_dvd_index hq.out (P : Subgroup G) P.not_dvd_index
    refine ⟨N, hN, ?_, fun g hg => hHg g ?_⟩
    · exact lt_of_lt_of_le (by omega)
        (h2.trans (hrkP.trans (CFSG.SectionRank.pRank_mono hp1 (hPS.trans hSN))))
    · rw [eq_top_iff, ← hfr]
      exact sup_le (hSN.trans hg) (hOHg g)

end Global

end CFSG.LocalAnalysis.UniquenessCase.UCK.K38B
