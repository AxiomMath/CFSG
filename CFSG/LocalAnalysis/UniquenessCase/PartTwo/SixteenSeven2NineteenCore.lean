module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_nineteen_core (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hHyp : Hyp16 D ⊥ V)
    (h14 : ((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hA : A ∈ E3.gammaSet V D.k D.T)
    (hAg : A ≤ conjSubgroup V g) (hC : Concl1617 D ⊥ V hV L A g Δ)
    (hI : Insp18 D ⊥ V hV L g Δ) (hVM : ¬ conjSubgroup V g ≤ D.M)
    (hn2 : ¬ Case168_2 D ⊥ V hV L) (huniq : Unique19 D V g Δ) (hsec : Second19 V A)
    {B U : Subgroup G} (hBU : Hyperplane1618 V A B U) : False := by
  obtain ⟨B', U', hBU', hne⟩ := hsec B U hBU
  obtain ⟨h1, u, huU, huVM, hE, hfix⟩ :=
    s16c167_eighteen_u D hV hHyp h14 hA hAg hC hI hBU
  obtain ⟨h1', z, hzU, hzVM, hE', hfix'⟩ :=
    s16c167_eighteen_u D hV hHyp h14 hA hAg hC hI hBU'
  have h18 := s16c167_eighteen_core D hV hHyp h14 hA hAg hC hI hBU
  have h18' := s16c167_eighteen_core D hV hHyp h14 hA hAg hC hI hBU'
  obtain ⟨I, ⟨hIΓ, hIB⟩, -⟩ := h18.2.2.1 hn2
  obtain ⟨I', ⟨hI'Γ, hI'B'⟩, -⟩ := h18'.2.2.1 hn2
  have hAM : A ≤ D.M := hA.1.trans D.sylowM.le
  have hBA : B ≤ A := hBU.1
  have hB'A : B' ≤ A := hBU'.1
  obtain ⟨hn, -, -, hsum, -⟩ := hC
  obtain ⟨a, b, hab, hΔ⟩ := Set.ncard_eq_two.1 hn
  have hsup_ab : a ⊔ b = V := by
    rw [← sSup_pair, ← hΔ]
    exact hsum
  have hdelta : deltaConj Δ g = {conjSubgroup a g, conjSubgroup b g} := by
    rw [hΔ]
    unfold deltaConj
    rw [Set.image_pair]
  have hsupJ : conjSubgroup a g ⊔ conjSubgroup b g = conjSubgroup V g := by
    unfold conjSubgroup
    rw [← Subgroup.map_sup, hsup_ab]
  have mem_pair : ∀ J ∈ deltaConj Δ g, J = conjSubgroup a g ∨ J = conjSubgroup b g := by
    intro J hJ
    rw [hdelta] at hJ
    rcases Set.mem_insert_iff.1 hJ with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.1 h)
  have hII' : I' = I := by
    by_contra hne'
    have hsupII : I ⊔ I' = conjSubgroup V g := by
      rcases mem_pair I hIΓ with h | h <;> rcases mem_pair I' hI'Γ with h' | h'
      · exact absurd (h'.trans h.symm) hne'
      · rw [h, h', hsupJ]
      · rw [h, h', sup_comm, hsupJ]
      · exact absurd (h'.trans h.symm) hne'
    exact hVM ((hsupII ▸ sup_le (hIB.trans hBA) (hI'B'.trans hB'A)).trans hAM)
  have hmB : E3.mQuot (conjSubgroup V g) B = D.k + 1 := h1.1.trans h1.2
  have hmB' : E3.mQuot (conjSubgroup V g) B' = D.k + 1 := h1'.1.trans h1'.2
  have hnontriv : ∀ {w : G} {C : Subgroup G},
      conjSubgroup V g ⊓ centralizer ({w} : Set G) = C →
      E3.mQuot (conjSubgroup V g) C = D.k + 1 →
      ¬ conjSubgroup V g ≤ centralizer ({w} : Set G) := by
    intro w C hC' hm hle
    rw [inf_eq_left.2 hle] at hC'
    rw [← hC'] at hm
    rw [E3.mQuot_self] at hm
    omega
  have hIu : I ≤ centralizer ({u} : Set G) := by
    refine hIB.trans ?_
    rw [← hE]
    exact inf_le_right
  have hIz : I ≤ centralizer ({z} : Set G) := by
    refine (hII' ▸ hI'B').trans ?_
    rw [← hE']
    exact inf_le_right
  have hsame := huniq u huVM z hzVM (hnontriv hE hmB) (hnontriv hE' hmB') I hIΓ hIu hIz
  exact hne (hE'.symm.trans (hsame.symm.trans hE))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
