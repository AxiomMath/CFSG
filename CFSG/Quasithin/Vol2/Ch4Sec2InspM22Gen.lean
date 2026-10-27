module

public import CFSG.Quasithin.Vol2.Ch4Sec2InspM22LT
public import CFSG.Quasithin.EmptyFaithful.S152VPsl
public import CFSG.Sporadic.Schreier.M12

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Quasithin.KGC31 CFSG.SectionRank.QTK CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.GorensteinWalter

theorem no_m22_surj_of_not_dvd {S : Type} [Group S]
    (h : ¬ 443520 ∣ Nat.card S) (A : Subgroup S) (φ : A →* NativeSporadic.Carrier .M22) :
    ¬ Function.Surjective φ := by
  intro hφ
  apply h
  have hM : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Schreier.m22_card
  rw [← hM]
  exact (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card A)

theorem no_m22_surj_of_psl2 {S : Type} [Group S] {q : ℕ}
    (hq : (∃ n : ℕ, q = 2 ^ n) ∨ IsOddPrimePower q) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = q) (e : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K)
    (A : Subgroup S) (φ : A →* NativeSporadic.Carrier .M22) : ¬ Function.Surjective φ := by
  intro hφ
  let B : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) := A.map e.toMonoidHom
  let ψ : B →* NativeSporadic.Carrier .M22 :=
    φ.comp (MulEquiv.subgroupMap e A).symm.toMonoidHom
  have hψ : Function.Surjective ψ := hφ.comp (MulEquiv.subgroupMap e A).symm.surjective
  rcases hq with h | h
  · exact CFSG.Quasithin.S152V.no_m22_section_psl2 (F := K) (Or.inl (by rw [hK]; exact h)) B ψ hψ
  · exact CFSG.Quasithin.S152V.no_m22_section_psl2 (F := K) (Or.inr (by rw [hK]; exact h)) B ψ hψ

theorem prop3_generic
    (hLT : LTQTK) (hOrd : QTKOrdNoM22) {S : Type} [Group S] [Finite S] (hS : QTKSimpleList S)
    (hnot : ∀ s : TauCeti.SporadicName,
      (s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .HS ∨ s = .McL ∨ s = .J4) →
        ¬ Nonempty (S ≃* NativeSporadic.Carrier s))
    (A : Subgroup S) (φ : A →* NativeSporadic.Carrier .M22) : ¬ Function.Surjective φ := by
  obtain ⟨hLT1, hLT2, hLT3, hLT4, hLT5, hLT6⟩ := hLT
  obtain ⟨hO1, hO2, hO3, hO4, hO5, hO6, hO7, hO8, hO9, hO10, hO11⟩ := hOrd
  unfold QTKSimpleList at hS
  rcases hS with h1 | h2 | (h3 | h4 | h5) | (h6 | h7) | h8
  ·
    obtain ⟨n, h5', h9, ⟨e⟩⟩ := h1
    have hcard : Nat.card S = n.factorial / 2 := by
      haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 (by omega)
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
    exact no_m22_surj_of_not_dvd (by rw [hcard]; interval_cases n <;> norm_num) A φ
  ·
    obtain ⟨p, hp, hp2, hp'⟩ := h2
    have hodd : Odd p := hp.odd_of_ne_two hp2
    rcases hp' with ⟨f, hf1, hPSL2⟩ | ⟨f, hf, hPSL3⟩ | hPSp | hG2 | ⟨⟨a, ha⟩, hPSL4⟩ |
      ⟨⟨b, hb⟩, hPSU4⟩
    ·
      obtain ⟨_, K, _, _, hK, ⟨eS⟩⟩ := hPSL2
      exact no_m22_surj_of_psl2 (q := p ^ f) (Or.inr ⟨p, f, hp, hodd, hf1, rfl⟩) K hK
        (eS.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm) A φ
    ·
      by_cases h11 : p = 11
      · exact no_m22_surj_of_sylowAutBound ((hLT1 S p f hp2 hf hPSL3).2 h11)
          (Or.inr ⟨rfl, by norm_num⟩) A φ
      · exact no_m22_surj_of_sylowAutBound ((hLT1 S p f hp2 hf hPSL3).1 h11)
          (Or.inl ⟨rfl, by norm_num⟩) A φ
    ·
      by_cases h11 : p = 11
      · subst h11
        exact no_m22_surj_of_not_dvd (hO1 S hPSp) A φ
      · exact no_m22_surj_of_sylowAutBound (hLT2 S p hp2 h11 (Or.inl hPSp))
          (Or.inl ⟨rfl, by norm_num⟩) A φ
    ·
      by_cases h11 : p = 11
      · subst h11
        exact no_m22_surj_of_not_dvd (hO2 S hG2) A φ
      · exact no_m22_surj_of_sylowAutBound (hLT2 S p hp2 h11 (Or.inr hG2))
          (Or.inl ⟨rfl, by norm_num⟩) A φ
    ·
      exact no_m22_surj_of_sylowAutBound (hLT3 S p hp2 ⟨a, ha⟩ hPSL4)
        (Or.inl ⟨rfl, by norm_num⟩) A φ
    ·
      exact no_m22_surj_of_sylowAutBound (hLT4 S p hp2 ⟨b, hb⟩ hPSU4)
        (Or.inl ⟨rfl, by norm_num⟩) A φ
  ·
    obtain ⟨f, hf⟩ := h3
    rcases hf with ⟨hf2, hPSL2⟩ | ⟨hf1, hPSL3⟩ | ⟨hf2b, hPSU3⟩ | ⟨hf2c, hPSp2⟩ |
      ⟨hf1b, hPSU4⟩ | ⟨hf2d, hG2⟩ | ⟨hf1c, hD4⟩ | ⟨hodd, hf3, hF4⟩ | ⟨hodd2, hf3b, hSz⟩
    ·
      obtain ⟨_, K, _, _, hK, ⟨eS⟩⟩ := hPSL2
      exact no_m22_surj_of_psl2 (q := 2 ^ f) (Or.inl ⟨f, rfl⟩) K hK
        (eS.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm) A φ
    · exact no_m22_surj_of_sylowAutBound (hLT5 S f (Or.inl hPSL3))
        (Or.inl ⟨rfl, by norm_num⟩) A φ
    · exact no_m22_surj_of_sylowAutBound (hLT5 S f (Or.inr (Or.inl hPSU3)))
        (Or.inl ⟨rfl, by norm_num⟩) A φ
    · exact no_m22_surj_of_sylowAutBound (hLT5 S f (Or.inr (Or.inr (Or.inl hPSp2))))
        (Or.inl ⟨rfl, by norm_num⟩) A φ
    · exact no_m22_surj_of_sylowAutBound (hLT5 S f (Or.inr (Or.inr (Or.inr hPSU4))))
        (Or.inl ⟨rfl, by norm_num⟩) A φ
    · exact no_m22_surj_of_sylowAutBound (hLT6 S f (Or.inl hG2))
        (Or.inl ⟨rfl, by norm_num⟩) A φ
    · exact no_m22_surj_of_sylowAutBound (hLT6 S f (Or.inr (Or.inl hD4)))
        (Or.inl ⟨rfl, by norm_num⟩) A φ
    · exact no_m22_surj_of_sylowAutBound (hLT6 S f (Or.inr (Or.inr hF4)))
        (Or.inl ⟨rfl, by norm_num⟩) A φ
    · exact no_m22_surj_of_not_dvd (hO6 S f hSz) A φ
  ·
    exact no_m22_surj_of_not_dvd (hO4 S h4) A φ
  ·
    exact no_m22_surj_of_not_dvd (hO5 S h5) A φ
  ·
    obtain ⟨n, hn, hPSL⟩ := h6
    obtain ⟨_, K, _, _, hK, ⟨eS⟩⟩ := hPSL
    have hK2 : Nat.card K = 2 := by rw [hK]; norm_num
    rcases hn with rfl | rfl
    · have hd : Nat.card S ∣ 20160 := by
        rw [Nat.card_congr eS.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK2]
        exact Subgroup.card_quotient_dvd_card _
      exact no_m22_surj_of_not_dvd (fun h => by
        have := h.trans hd
        norm_num at this) A φ
    · have hd : Nat.card S ∣ 9999360 := by
        rw [Nat.card_congr eS.toEquiv, ← CFSG.Open.StatedAPI.card_statedSL_five_of_card_eq_two hK2]
        exact Subgroup.card_quotient_dvd_card _
      exact no_m22_surj_of_not_dvd (fun h => by
        have := h.trans hd
        norm_num at this) A φ
  ·
    exact no_m22_surj_of_not_dvd (hO3 S h7) A φ
  ·
    obtain ⟨s, hs, ⟨e⟩⟩ := h8
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have hcard : Nat.card S = 7920 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.Sporadic.Schreier.m11_card
      exact no_m22_surj_of_not_dvd (by rw [hcard]; norm_num) A φ
    ·
      have hcard : Nat.card S = 95040 := by
        rw [Nat.card_congr e.toEquiv]
        exact CFSG.Sporadic.Schreier.m12_card
      exact no_m22_surj_of_not_dvd (by rw [hcard]; norm_num) A φ
    · exact (hnot _ (by simp) ⟨e⟩).elim
    · exact (hnot _ (by simp) ⟨e⟩).elim
    · exact (hnot _ (by simp) ⟨e⟩).elim
    · exact no_m22_surj_of_not_dvd (hO7 S ⟨e⟩) A φ
    · exact no_m22_surj_of_not_dvd (hO8 S ⟨e⟩) A φ
    · exact no_m22_surj_of_not_dvd (hO9 S ⟨e⟩) A φ
    · exact (hnot _ (by simp) ⟨e⟩).elim
    · exact (hnot _ (by simp) ⟨e⟩).elim
    · exact no_m22_surj_of_not_dvd (hO10 S ⟨e⟩) A φ
    · exact no_m22_surj_of_not_dvd (hO11 S ⟨e⟩) A φ
    · exact (hnot _ (by simp) ⟨e⟩).elim

end CFSG.Quasithin.H13.Ch4

end
