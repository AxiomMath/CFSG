module

public import CFSG.LocalAnalysis.UniquenessCase.UCKQSCrossTools
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcF4
public import CFSG.LocalAnalysis.UniquenessCase.UCKQSDispatch

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
  CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem qsExc_seven_le_of_dvd_orderOf {p q d : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hpq : ¬ p ∣ q)
    (hd : 3 ∣ d) (he : orderOf (q : ZMod p) = d) : 7 ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := fun h => hpq ((ZMod.natCast_eq_zero_iff q p).1 h)
  have h1 : d ∣ p - 1 := he ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have h2 : 3 ∣ p - 1 := hd.trans h1
  omega

theorem qsExc_degCount_le_two_of {τ : Tag}
    (hτ : τ = Tag.F4 ∨ τ = Tag.E6 ∨ τ = Tag.E7 ∨ τ = Tag.E8) {S : List ℕ}
    (hS : ∀ e ≤ 30, e ∈ S ∨ degCount τ e ≤ 2) {e : ℕ} (he : e ∉ S) : degCount τ e ≤ 2 := by
  by_cases h30 : e ≤ 30
  · exact (hS e h30).resolve_left he
  · have : ¬ 0 < degCount τ e := fun h => h30 (le_thirty_of_degCount_pos hτ h)
    omega

theorem qsExc_degCount_E6_eq_two {e : ℕ} (h : degCount Tag.E6 e = 2) : e = 4 ∨ e = 6 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E6) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E6 e = 2 → e = 4 ∨ e = 6 := by decide
  exact key e h30 h

theorem qsExc_degCount_E7_eq_two {e : ℕ} (h : degCount Tag.E7 e = 2) : e = 4 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E7) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E7 e = 2 → e = 4 := by decide
  exact key e h30 h

theorem qsExc_degCount_E8_eq_two {e : ℕ} (h : degCount Tag.E8 e = 2) :
    e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by
  have h30 := le_thirty_of_degCount_pos (τ := Tag.E8) (e := e) (by simp) (by omega)
  have key : ∀ e ≤ 30, degCount Tag.E8 e = 2 → e = 5 ∨ e = 8 ∨ e = 10 ∨ e = 12 := by decide
  exact key e h30 h

theorem qsExc_degCount_F4_le_one {e : ℕ} (he : e ∉ [1, 2, 3, 4, 6]) : degCount Tag.F4 e ≤ 1 := by
  by_cases h30 : e ≤ 30
  · have key : ∀ e ≤ 30, e ∈ [1, 2, 3, 4, 6] ∨ degCount Tag.F4 e ≤ 1 := by decide
    exact (key e h30).resolve_left he
  · have : ¬ 0 < degCount Tag.F4 e := fun h => h30 (le_thirty_of_degCount_pos (Or.inl rfl) h)
    omega

section Certified

theorem qsExc_pca_of_adjoint {τ : Tag} {K : Type} [Group K] [Finite K] {ℓ f p : ℕ} [Fact p.Prime]
    (hp : p.Prime) (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ) (hm : UntwistedChevalleyModel K τ (ℓ ^ f))
    (H : ∀ (F : Type) [Field F] [Finite F], ¬ p ∣ Nat.card F →
      PCentralAbelianAt ↥(adjointGroup τ F) p) : PCentralAbelianAt K p := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).1 (hp.dvd_of_dvd_pow h))
  exact PCentralAbelianAt.of_mulEquiv
    (e.trans ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)) (H F hpF)

theorem qsExc_pca_of_degCount_le_two {τ : Tag} (hτ : τ = Tag.E6 ∨ τ = Tag.E7 ∨ τ = Tag.E8) (K : Type) [Field K]
    [Finite K] {p : ℕ} [Fact p.Prime] (hp : p.Prime) (h5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K)
    (hcnt : degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 2) :
    PCentralAbelianAt ↥(adjointGroup τ K) p := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card K : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  rcases Nat.lt_or_ge (degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p))) 2 with hlt | hge
  · have h1 : degCount τ (orderOf ((Nat.card K : ℕ) : ZMod p)) ≤ 1 := by omega
    rcases hτ with rfl | rfl | rfl
    · exact PCentralAbelianAt.of_rankLE1 hp2 (rankLE1_E6 K hp hpK h1)
    · exact PCentralAbelianAt.of_rankLE1 hp2 (rankLE1_E7 K hp hpK h1)
    · exact PCentralAbelianAt.of_rankLE1 hp2 (rankLE1_E8 K hp hpK h1)
  · have h2 : degCount τ e = 2 := by rw [← he]; omega
    rcases hτ with rfl | rfl | rfl
    · rcases qsExc_degCount_E6_eq_two h2 with rfl | rfl
      · exact PCentralAbelianAt.of_sylowTorus (sylowTorus_E6_four K hp he)
      · exact PCentralAbelianAt.of_sylowTorus (sylowTorus_E6_six K hp he)
    · obtain rfl := qsExc_degCount_E7_eq_two h2
      exact PCentralAbelianAt.of_sylowTorus (sylowTorus_E7_four K hp he)
    · rcases qsExc_degCount_E8_eq_two h2 with rfl | rfl | rfl | rfl
      · exact PCentralAbelianAt.of_sylowTorus (sylowTorus_E8_five K hp he)
      · exact PCentralAbelianAt.of_sylowTorus (sylowTorus_E8_eight K hp he)
      · exact PCentralAbelianAt.of_sylowTorus (sylowTorus_E8_ten K hp he)
      · exact PCentralAbelianAt.of_sylowTorus (sylowTorus_E8_twelve K hp he)

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw in
theorem qsExc_pca_F4 (F : Type) [Field F] [Finite F] {p : ℕ} [Fact p.Prime] (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) : PCentralAbelianAt ↥(adjointGroup Tag.F4 F) p := by
  have hp3 : 3 < p := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h1 : e = 1
  · subst h1
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_F4_one F hp hp3 he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc le_rfl
  by_cases h2 : e = 2
  · subst h2
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_F4_two F hp hp3 he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc le_rfl
  by_cases h3 : e = 3
  · subst h3
    exact PCentralAbelianAt.of_sylowFrameM (F4.sylowFrameM_three hp hp3 (dvd_phi3_of_orderOf' hp he))
  by_cases h4 : e = 4
  · subst h4
    exact PCentralAbelianAt.of_sylowFrameM (F4.sylowFrameM_four hp hp3 (dvd_phi4_of_orderOf' hp he))
  by_cases h6 : e = 6
  · subst h6
    exact PCentralAbelianAt.of_sylowFrameM (F4.sylowFrameM_six hp hp3 (dvd_phi6_of_orderOf' hp he))
  refine PCentralAbelianAt.of_rankLE1 (by omega) (rankLE1_F4 F hp hpF ?_)
  rw [he]
  exact qsExc_degCount_F4_le_one (by simp [h1, h2, h3, h4, h6])

theorem qsExc_pca_E6 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) [Fact p.Prime] : PCentralAbelianAt ↥(adjointGroup Tag.E6 F) p := by
  have hp3 : 3 < p := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h1 : e = 1
  · subst h1
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_one F hp hp3 he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h2 : e = 2
  · subst h2
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E6_two F hp hp3 he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc le_rfl
  by_cases h3 : e = 3
  · subst h3
    have h7 := qsExc_seven_le_of_dvd_orderOf hp h5 hpF (dvd_refl 3) he
    obtain ⟨m, hm⟩ := exists_sylowTorus_E6 F hp h7 hpF (by rw [he]; decide)
    exact PCentralAbelianAt.of_sylowTorus hm
  exact qsExc_pca_of_degCount_le_two (Or.inl rfl) F hp h5 hpF (by
    rw [he]
    exact qsExc_degCount_le_two_of (Or.inr (Or.inl rfl)) (S := [1, 2, 3]) (by decide)
      (by simp [h1, h2, h3]))

theorem qsExc_pca_E7 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) [Fact p.Prime] : PCentralAbelianAt ↥(adjointGroup Tag.E7 F) p := by
  have hp3 : 3 < p := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h1 : e = 1
  · subst h1
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_one F hp hp3 he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h2 : e = 2
  · subst h2
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E7_two F hp hp3 he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h3 : e = 3
  · subst h3
    have h7 := qsExc_seven_le_of_dvd_orderOf hp h5 hpF (dvd_refl 3) he
    obtain ⟨m, hm⟩ := exists_sylowTorus_E7 F hp h7 hpF (by rw [he]; decide)
      (Or.inr (by rw [he]))
    exact PCentralAbelianAt.of_sylowTorus hm
  by_cases h6 : e = 6
  · subst h6
    have h7 := qsExc_seven_le_of_dvd_orderOf hp h5 hpF (by norm_num) he
    obtain ⟨m, hm⟩ := exists_sylowTorus_E7 F hp h7 hpF (by rw [he]; decide)
      (Or.inr (by rw [he]; norm_num))
    exact PCentralAbelianAt.of_sylowTorus hm
  exact qsExc_pca_of_degCount_le_two (Or.inr (Or.inl rfl)) F hp h5 hpF (by
    rw [he]
    exact qsExc_degCount_le_two_of (Or.inr (Or.inr (Or.inl rfl))) (S := [1, 2, 3, 6]) (by decide)
      (by simp [h1, h2, h3, h6]))

theorem qsExc_pca_E8 (F : Type) [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpF : ¬ p ∣ Nat.card F) [Fact p.Prime] : PCentralAbelianAt ↥(adjointGroup Tag.E8 F) p := by
  have hp3 : 3 < p := by omega
  obtain ⟨e, he⟩ : ∃ e, orderOf ((Nat.card F : ℕ) : ZMod p) = e := ⟨_, rfl⟩
  by_cases h1 : e = 1
  · subst h1
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_one F hp hp3 he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h2 : e = 2
  · subst h2
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_two F hp hp3 he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc (by norm_num)
  by_cases h3 : e = 3
  · subst h3
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_three F hp he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc le_rfl
  by_cases h4 : e = 4
  · subst h4
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_four F hp he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc le_rfl
  by_cases h6 : e = 6
  · subst h6
    obtain ⟨E, hE, hc⟩ := exists_elemAbelian_E8_six F hp he
    exact PCentralAbelianAt.of_elemAbelian hp hE hc le_rfl
  exact qsExc_pca_of_degCount_le_two (Or.inr (Or.inr rfl)) F hp h5 hpF (by
    rw [he]
    exact qsExc_degCount_le_two_of (Or.inr (Or.inr (Or.inr rfl))) (S := [1, 2, 3, 4, 6]) (by decide)
      (by simp [h1, h2, h3, h4, h6]))

theorem pcaLieCross_F4 : PCALieCrossAt .F4 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hℓ, _, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact qsExc_pca_of_adjoint (τ := Tag.F4) hp hℓ hpℓ hm fun F _ _ hpF => qsExc_pca_F4 F hp h5 hpF

theorem pcaLieCross_E6 : PCALieCrossAt .E6 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hℓ, _, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact qsExc_pca_of_adjoint (τ := Tag.E6) hp hℓ hpℓ hm fun F _ _ hpF => qsExc_pca_E6 F hp h5 hpF

theorem pcaLieCross_E7 : PCALieCrossAt .E7 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hℓ, _, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact qsExc_pca_of_adjoint (τ := Tag.E7) hp hℓ hpℓ hm fun F _ _ hpF => qsExc_pca_E7 F hp h5 hpF

theorem pcaLieCross_E8 : PCALieCrossAt .E8 := by
  intro K _ _ _ _ n ℓ f _ hmodel p hp h5 hpℓ _
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hℓ, _, _⟩, hm⟩ := hmodel.chevalleyExceptionalModel (by simp [chevalleyExceptionalTags])
  exact qsExc_pca_of_adjoint (τ := Tag.E8) hp hℓ hpℓ hm fun F _ _ hpF => qsExc_pca_E8 F hp h5 hpF

end Certified

end CFSG.LocalAnalysis.UniquenessCase.UCK
