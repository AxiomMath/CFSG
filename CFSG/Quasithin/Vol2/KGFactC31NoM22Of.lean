module

public import CFSG.Quasithin.Vol2.KGFactC31NoM22Lie
public import CFSG.Quasithin.Vol2.KGFactC31NoM22Exc
public import CFSG.Quasithin.Vol2.KGFactC31NoM22Odd
public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersRee

public section

namespace CFSG.Quasithin.KGC31.NoM22

open Function CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.Quasithin.KGC31.KG443
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree

theorem statedSL_le_ker (n : ℕ) (K : Type) [Field K] :
    StatedSL n K ≤ (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K)).ker := by
  rw [StatedSL, Subgroup.closure_le]
  intro A hA
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact hA

theorem statedSU_le_ker (n q : ℕ) (K : Type) [Field K] :
    StatedSU n q K ≤ (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K)).ker := by
  rw [StatedSU, Subgroup.closure_le]
  intro A hA
  rw [SetLike.mem_coe, MonoidHom.mem_ker]
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
  exact hA.1

theorem det_eq_one_of_mem_ker {n : ℕ} {K : Type} [Field K] {h : GL (Fin n) K}
    (hh : h ∈ (Matrix.GeneralLinearGroup.det (n := Fin n) (R := K)).ker) :
    (h : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [MonoidHom.mem_ker] at hh
  have := congrArg Units.val hh
  rwa [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one] at this

theorem not_secOnto_tits
    {S : Type} [Group S] [Finite S] (h : IsTits S) :
    ¬ SecOnto S (NativeSporadic.Carrier .M22) := fun hs => by
  obtain ⟨-, a, hf, hmodel⟩ := h
  obtain rfl : a = 0 := by omega
  obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ :=
    CFSG.EvenSmallLie.CatalogOrders.exists_mulEquiv_of_reeTitsRelationModel_F4 hmodel
  rw [pow_one] at hK
  have h1 : Nat.card (NativeSporadic.Carrier .M22) ∣ Nat.card S := hs.card_dvd
  have h2 : Nat.card S ∣ 35942400 := by
    rw [Nat.card_congr e.toEquiv]
    exact (Subgroup.card_quotient_dvd_card _).trans
      (CFSG.SectionRank.TitsOrder.Tits_commutator_card_dvd hK)
  have h3 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  rw [h3] at h1
  exact absurd (h1.trans h2) (by norm_num)

theorem noM22SectionLie_of
    (hExc : NoM22SectionLieExc) : NoM22SectionLie := by
  intro S _ _ hS Y φ hφ
  have hs : SecOnto S (NativeSporadic.Carrier .M22) := ⟨Y, φ, hφ⟩
  have hSL : ∀ {n : ℕ} {K : Type} [Field K], ∀ h ∈ StatedSL n K,
      (h : Matrix (Fin n) (Fin n) K).det = 1 := fun h hh =>
    det_eq_one_of_mem_ker (statedSL_le_ker _ _ hh)
  have hSU : ∀ {n q : ℕ} {K : Type} [Field K], ∀ h ∈ StatedSU n q K,
      (h : Matrix (Fin n) (Fin n) K).det = 1 := fun h hh =>
    det_eq_one_of_mem_ker (statedSU_le_ker _ _ _ hh)
  rcases hS with (⟨p, hp, hp2, hc⟩ | ⟨f, hc⟩ | hT) | ⟨s, p, k, hp, hk, hpk, hm⟩
  ·
    have hodd : ∀ j : ℕ, Odd (p ^ j) := fun j => (hp.odd_of_ne_two hp2).pow
    rcases hc with ⟨f, -, -, K, _, _, hK, ⟨e⟩⟩ | ⟨-, K, _, _, hK, ⟨e⟩⟩ | ⟨-, K, _, _, hK, ⟨e⟩⟩
    · exact not_secOnto_of_det_quot (by rw [hK]; exact hodd f) (Or.inl rfl) _ hSL _
        (hs.of_equiv e)
    · exact not_secOnto_of_det_quot (by rw [hK]; exact hodd 1) (Or.inr rfl) _ hSL _
        (hs.of_equiv e)
    · exact not_secOnto_of_det_quot (by rw [hK, ← pow_mul]; exact hodd _) (Or.inr rfl) _ hSU _
        (hs.of_equiv e)
  ·
    rcases hc with ⟨hf, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hf, -, K, _, _, hK, ⟨e⟩⟩ |
      ⟨hf, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hf, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hf, hf3, hm⟩ | ⟨-, hf3, -, a, -, K, _, _, -, hK, ⟨e⟩⟩
    · have := charP_two_of_card (by omega) hK
      exact not_secOnto_quot (by simp) _ _ (hs.of_equiv e)
    · have := charP_two_of_card hf hK
      exact not_secOnto_quot (by simp) _ _ (hs.of_equiv e)
    · have := charP_two_of_card (f := f * 2) (by omega) (by rw [hK, ← pow_mul])
      exact not_secOnto_quot (by simp) _ _ (hs.of_equiv e)
    · have := charP_two_of_card (by omega) hK
      exact not_secOnto_quot (by simp) _ _ (hs.of_equiv e)
    · exact hExc S ⟨f, Or.inl ⟨hf, hm⟩⟩ Y φ hφ
    · exact hExc S ⟨f, Or.inr (Or.inl ⟨hf, hm⟩)⟩ Y φ hφ
    · exact hExc S ⟨f, Or.inr (Or.inr ⟨hf, hf3, hm⟩)⟩ Y φ hφ
    · have := charP_two_of_card (by omega) hK
      exact not_secOnto_glSub (by simp) _ (hs.of_equiv e)
  ·
    exact not_secOnto_tits hT hs
  ·
    cases s
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
      rcases hpk with ⟨rfl, -⟩ | ⟨hp2, rfl⟩
      · have := charP_two_of_card (f := k * 2) (by omega) (by rw [hK, ← pow_mul])
        exact not_secOnto_glSub (by simp) _ (hs.of_equiv e)
      · exact not_secOnto_of_det (by rw [hK, ← pow_mul]; exact (hp.odd_of_ne_two hp2).pow)
          (Or.inr rfl) _ hSU (hs.of_equiv e)
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
      rcases hpk with ⟨rfl, -⟩ | ⟨hp2, rfl⟩
      · have := charP_two_of_card hk hK
        exact not_secOnto_glSub (by simp) _ (hs.of_equiv e)
      · exact not_secOnto_of_det (by rw [hK]; exact (hp.odd_of_ne_two hp2).pow) (Or.inr rfl) _
          hSL (hs.of_equiv e)

end CFSG.Quasithin.KGC31.NoM22

end
