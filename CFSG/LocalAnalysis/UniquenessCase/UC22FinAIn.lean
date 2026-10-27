module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22P2014b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.FinA

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem sp_of_mem_calC {D : Data G} (hSg : UC6S846.SigmaStd D) {p : ℕ} (hp : p ∈ D.sig)
    {M' Y : Subgroup G} (hM' : M' ≤ D.M) (hY : Y ∈ calC M') : IsStronglyPEmbedded p D.M := by
  refine UC6S846.sp_of_mem_sig hSg (fun hs => ?_) hp
  exact UC6S846.not_solvable_of_mem_calC hY
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hM')
      (Subgroup.inclusion_injective hM'))

omit [Finite G] in
theorem exists_orderOf_eq_prime {p : ℕ} (hp : p.Prime) {X : Subgroup G} (h : Opp p X ≠ ⊥) :
    ∃ x ∈ X, orderOf x = p := by
  by_contra hcon
  have hcon' : ∀ x ∈ X, orderOf x ≠ p := fun x hx hxo => hcon ⟨x, hx, hxo⟩
  apply h
  rw [eq_bot_iff]
  refine (Subgroup.closure_le ⊥).2 ?_
  rintro x ⟨hxX, k, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [pow_zero, orderOf_eq_one_iff] at hk
    simp [hk]
  · exfalso
    have hdvd : p ∣ orderOf x := by
      rw [hk]
      exact dvd_pow_self p hk0.ne'
    have hne : orderOf x ≠ 0 := by
      rw [hk]
      exact pow_ne_zero _ hp.ne_zero
    exact hcon' _ (X.pow_mem hxX _) (orderOf_pow_orderOf_div hne hdvd)

omit [Finite G] in
theorem ne_bot_of_mem_calC {M' Y : Subgroup G} (hY : Y ∈ calC M') : Y ≠ ⊥ := by
  intro hbot
  have : Nontrivial (Bar2 Y ⧸ center (Bar2 Y)) := hY.2.2.2.toNontrivial
  have : Nontrivial (Bar2 Y) := (QuotientGroup.mk'_surjective (center (Bar2 Y))).nontrivial
  have : Nontrivial ↥Y :=
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot Y).1 inferInstance hbot

theorem L0_le_opp (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D) (h205 : S20_5 D)
    {Ch : Choice2011 G} (c : Ctx22b D Ch) {p : ℕ} (hp : p.Prime)
    (hsp : IsStronglyPEmbedded p D.M) {H : Subgroup G} (hH : H ∈ hSet D.T D.M)
    (hZH : centralizer (D.Z : Set G) ≤ H) {x : G} (hxH : x ∈ H) (hxM : x ∈ D.M)
    (hx : orderOf x = p) : c.L0 ≤ Opp p H := by
  have hLZ : c.L ≤ centralizer (D.Z : Set G) := c.hL.2.le
  obtain ⟨K, hK, hLK⟩ := h205 h1930 c.L0 c.hL0.1 H hH ((c.hLge.trans hLZ).trans hZH)
  exact hLK.trans (uc22p2014b_calLOf_le_opp D hB h1930 hp hsp hH hK hxH hxM hx)

theorem exists_inverting {D : Data G} {Ch : Choice2011 G} (c : Ctx22b D Ch) :
    ∃ t ∈ c.L0, t ∉ D.M ∧ ∀ x ∈ c.B0, t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨t, htL, htM, -, ht⟩, -⟩ := c.hB0
  exact ⟨t, htL, htM, ht⟩

omit [Finite G] in
theorem not_dvd_card_of_inverted {q : ℕ} {M B : Subgroup G} (hsp : IsStronglyPEmbedded q M)
    (hBM : B ≤ M) {t : G} (htM : t ∉ M) (ht : ∀ x ∈ B, t * x * t⁻¹ = x⁻¹) :
    ¬ q ∣ Nat.card B := by
  intro hq
  refine hsp.2.2 t htM (hq.trans (Subgroup.card_dvd_of_le (le_inf hBM fun x hx => ?_)))
  refine ⟨x⁻¹, hBM (B.inv_mem hx), ?_⟩
  simpa [MulAut.conj_apply] using ht x⁻¹ (B.inv_mem hx)

end CFSG.LocalAnalysis.UniquenessCase.UC22.FinA
