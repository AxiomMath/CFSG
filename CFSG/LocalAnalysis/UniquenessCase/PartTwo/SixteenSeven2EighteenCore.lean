module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCoreA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem s16c167_eighteen_pair {W J₁ J₂ B C : Subgroup G} {u : G}
    (hW : IsElemAbelian 2 W) (hJ₁ : J₁ ≤ W) (hJ₂ : J₂ ≤ W)
    (hdisj : J₁ ⊓ J₂ = ⊥) (hsup : J₁ ⊔ J₂ = W)
    (hu₁ : conjSubgroup J₁ u = J₁) (hu₂ : conjSubgroup J₂ u = J₂)
    (hBW : B = W ⊓ centralizer ({u} : Set G))
    (hBC : B ≤ C) (hCu : C ≤ centralizer ({u} : Set G)) :
    B = W ⊓ C ∧
      B = (J₁ ⊓ C) ⊔ (J₂ ⊓ C) ∧
      B = (B ⊓ J₁) ⊔ (B ⊓ J₂) ∧
      (J₁ ⊓ C = J₁ ⊓ B) ∧ (J₂ ⊓ C = J₂ ⊓ B) ∧
      (J₁ ⊓ centralizer ({u} : Set G) = J₁ ⊓ B) ∧
      (J₂ ⊓ centralizer ({u} : Set G) = J₂ ⊓ B) ∧
      (E3.mQuot W B = E3.mQuot J₁ (J₁ ⊓ B) + E3.mQuot J₂ (J₂ ⊓ B)) ∧
      (E3.mQuot J₁ (J₁ ⊓ B) = 0 ↔ J₁ ≤ B) ∧
      (E3.mQuot J₂ (J₂ ⊓ B) = 0 ↔ J₂ ≤ B) := by
  have hJ₁p : IsPGroup 2 ↥J₁ :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hJ₁ hW)
  have hJ₂p : IsPGroup 2 ↥J₂ :=
    B2F.isPGroup_of_isElemAbelian (B2F.isElemAbelian_mono hJ₂ hW)
  have hBleW : B ≤ W := by rw [hBW]; exact inf_le_left
  have hBW' : B = W ⊓ C := by
    apply le_antisymm
    · exact le_inf hBleW hBC
    · rw [hBW]
      exact inf_le_inf_left W hCu
  have hJ₁u : J₁ ⊓ centralizer ({u} : Set G) = J₁ ⊓ B := by
    rw [hBW, ← inf_assoc, inf_eq_left.2 hJ₁]
  have hJ₂u : J₂ ⊓ centralizer ({u} : Set G) = J₂ ⊓ B := by
    rw [hBW, ← inf_assoc, inf_eq_left.2 hJ₂]
  have hJ₁C : J₁ ⊓ C = J₁ ⊓ B := by
    apply le_antisymm
    · calc J₁ ⊓ C ≤ J₁ ⊓ centralizer ({u} : Set G) := inf_le_inf_left J₁ hCu
        _ = J₁ ⊓ B := hJ₁u
    · exact inf_le_inf_left J₁ hBC
  have hJ₂C : J₂ ⊓ C = J₂ ⊓ B := by
    apply le_antisymm
    · calc J₂ ⊓ C ≤ J₂ ⊓ centralizer ({u} : Set G) := inf_le_inf_left J₂ hCu
        _ = J₂ ⊓ B := hJ₂u
    · exact inf_le_inf_left J₂ hBC
  have hBsup : B = (J₁ ⊓ centralizer ({u} : Set G)) ⊔
      (J₂ ⊓ centralizer ({u} : Set G)) := by
    rw [hBW]
    exact s16c167_centralizer_split hW hJ₁ hJ₂ hdisj hsup hu₁ hu₂
  have hBsupC : B = (J₁ ⊓ C) ⊔ (J₂ ⊓ C) := by
    rw [hBsup, hJ₁u, hJ₂u, hJ₁C, hJ₂C]
  have hBsupB : B = (B ⊓ J₁) ⊔ (B ⊓ J₂) := by
    calc B = (J₁ ⊓ C) ⊔ (J₂ ⊓ C) := hBsupC
      _ = (J₁ ⊓ B) ⊔ (J₂ ⊓ B) := by rw [hJ₁C, hJ₂C]
      _ = (B ⊓ J₁) ⊔ (B ⊓ J₂) := by rw [inf_comm J₁ B, inf_comm J₂ B]
  have hEs : B = (J₁ ⊓ B) ⊔ (J₂ ⊓ B) := by
    calc B = (B ⊓ J₁) ⊔ (B ⊓ J₂) := hBsupB
      _ = (J₁ ⊓ B) ⊔ (J₂ ⊓ B) := by rw [inf_comm B J₁, inf_comm B J₂]
  have hsumM := s16c167_mQuot_split hW hJ₁ hJ₂ hdisj hsup hBleW hEs
  have h₁z : E3.mQuot J₁ (J₁ ⊓ B) = 0 ↔ J₁ ≤ B := by
    rw [E3.mQuot_eq_zero_iff hJ₁p inf_le_left, inf_eq_left]
  have h₂z : E3.mQuot J₂ (J₂ ⊓ B) = 0 ↔ J₂ ≤ B := by
    rw [E3.mQuot_eq_zero_iff hJ₂p inf_le_left, inf_eq_left]
  exact ⟨hBW', hBsupC, hBsupB, hJ₁C, hJ₂C, hJ₁u, hJ₂u, hsumM, h₁z, h₂z⟩

theorem s16c167_eighteen_core (D : Data G) {V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hHyp : Hyp16 D ⊥ V)
    (h14 : ((D.k + 2 : ℕ) : ℕ∞) < rMV D.M V)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hA : A ∈ E3.gammaSet V D.k D.T)
    (hAg : A ≤ conjSubgroup V g) (hC : Concl1617 D ⊥ V hV L A g Δ)
    (hI : Insp18 D ⊥ V hV L g Δ) {B U : Subgroup G} (hBU : Hyperplane1618 V A B U) :
    (E3.mQuot (conjSubgroup V g) B = mBar D.M ⊥ V hV ∧ mBar D.M ⊥ V hV = D.k + 1) ∧
      (B = conjSubgroup V g ⊓ centralizer (U : Set G) ∧
        B = ⨆ I ∈ deltaConj Δ g, I ⊓ centralizer (U : Set G) ∧
        B = ⨆ I ∈ deltaConj Δ g, B ⊓ I) ∧
      (¬ Case168_2 D ⊥ V hV L → ∃! J : Subgroup G, J ∈ deltaConj Δ g ∧ J ≤ B) ∧
      (Case168_2 D ⊥ V hV L → ∀ J ∈ deltaConj Δ g, E3.mQuot J (B ⊓ J) = 1) := by
  obtain ⟨h1, u, huU, huVM, hE, hfix⟩ :=
    s16c167_eighteen_u D hV hHyp h14 hA hAg hC hI hBU
  obtain ⟨hn, hΔV, hind, hsum, -⟩ := hC
  obtain ⟨a, b, hab, hΔ⟩ := Set.ncard_eq_two.1 hn
  have hW : IsElemAbelian 2 (conjSubgroup V g) := E3.isElemAbelian_conjSubgroup hV g
  set J₁ : Subgroup G := conjSubgroup a g with hJ₁def
  set J₂ : Subgroup G := conjSubgroup b g with hJ₂def
  have hdelta : deltaConj Δ g = {J₁, J₂} := by
    rw [hΔ]
    unfold deltaConj
    rw [Set.image_pair]
  have haV : a ≤ V := hΔV a (by rw [hΔ]; exact Set.mem_insert_iff.2 (Or.inl rfl))
  have hbV : b ≤ V :=
    hΔV b (by rw [hΔ]; exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 rfl)))
  have hind' : sSupIndep ({a, b} : Set (Subgroup G)) := by rw [← hΔ]; exact hind
  have hsum' : sSup ({a, b} : Set (Subgroup G)) = V := by rw [← hΔ]; exact hsum
  have hdisj_ab : a ⊓ b = ⊥ := disjoint_iff.1 ((sSupIndep_pair hab).1 hind')
  have hsup_ab : a ⊔ b = V := by rw [← sSup_pair]; exact hsum'
  have hJ₁W : J₁ ≤ conjSubgroup V g := by
    rw [hJ₁def]
    exact E3.conjSubgroup_mono_left g haV
  have hJ₂W : J₂ ≤ conjSubgroup V g := by
    rw [hJ₂def]
    exact E3.conjSubgroup_mono_left g hbV
  have hdisjJ : J₁ ⊓ J₂ = ⊥ := by
    rw [hJ₁def, hJ₂def, ← E3.conjSubgroup_inf a b g, hdisj_ab, E3.conjSubgroup_bot]
  have hsupJ : J₁ ⊔ J₂ = conjSubgroup V g := by
    rw [hJ₁def, hJ₂def]
    unfold conjSubgroup
    rw [← Subgroup.map_sup, hsup_ab]
  have hmem₁ : J₁ ∈ deltaConj Δ g := by
    rw [hdelta]
    exact Set.mem_insert_iff.2 (Or.inl rfl)
  have hmem₂ : J₂ ∈ deltaConj Δ g := by
    rw [hdelta]
    exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 rfl))
  have hfix₁ : conjSubgroup J₁ u = J₁ := hfix J₁ hmem₁
  have hfix₂ : conjSubgroup J₂ u = J₂ := hfix J₂ hmem₂
  have mem_pair : ∀ J ∈ deltaConj Δ g, J = J₁ ∨ J = J₂ := by
    intro J hJ
    rw [hdelta] at hJ
    rcases Set.mem_insert_iff.1 hJ with h | h
    · exact Or.inl h
    · exact Or.inr (Set.mem_singleton_iff.1 h)
  have hBU' : U = V ⊓ centralizer (B : Set G) := hBU.2.2.1
  have hBC : B ≤ centralizer (U : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y ∈ centralizer (B : Set G) := by
      rw [hBU'] at hy
      exact hy.2
    exact (Subgroup.mem_centralizer_iff.1 hy' x hx).symm
  have hCu : centralizer (U : Set G) ≤ centralizer ({u} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 hx u huU).symm
  have hBW : B = conjSubgroup V g ⊓ centralizer ({u} : Set G) := hE.symm
  have hmB : E3.mQuot (conjSubgroup V g) B = D.k + 1 := h1.1.trans h1.2
  have hmE : E3.mQuot (conjSubgroup V g)
      (conjSubgroup V g ⊓ centralizer ({u} : Set G)) = D.k + 1 := by
    rw [hE]
    exact hmB
  have h₁B : J₁ ≤ B ↔ J₁ ≤ centralizer ({u} : Set G) := by
    rw [← hE, le_inf_iff]
    exact ⟨fun h => h.2, fun h => ⟨hJ₁W, h⟩⟩
  have h₂B : J₂ ≤ B ↔ J₂ ≤ centralizer ({u} : Set G) := by
    rw [← hE, le_inf_iff]
    exact ⟨fun h => h.2, fun h => ⟨hJ₂W, h⟩⟩
  obtain ⟨hBeq, hBsupC, hBsupB, hJ₁C, hJ₂C, hJ₁u, hJ₂u, hsumM, h₁z, h₂z⟩ :=
    s16c167_eighteen_pair hW hJ₁W hJ₂W hdisjJ hsupJ hfix₁ hfix₂ hBW hBC hCu
  have hsum1 : B = ⨆ I ∈ deltaConj Δ g, I ⊓ centralizer (U : Set G) := by
    rw [hdelta, iSup_pair]
    exact hBsupC
  have hsum2 : B = ⨆ I ∈ deltaConj Δ g, B ⊓ I := by
    rw [hdelta, iSup_pair]
    exact hBsupB
  have hsumM' : E3.mQuot J₁ (J₁ ⊓ B) + E3.mQuot J₂ (J₂ ⊓ B) = D.k + 1 := by
    rw [← hsumM]
    exact hmB
  have hpart3 : ¬ Case168_2 D ⊥ V hV L → ∃! J : Subgroup G, J ∈ deltaConj Δ g ∧ J ≤ B := by
    intro hnc
    have hd₁ := hI.dist hnc u huVM hfix hmE J₁ hmem₁
    have hd₂ := hI.dist hnc u huVM hfix hmE J₂ hmem₂
    have hd₁' : E3.mQuot J₁ (J₁ ⊓ B) = 0 ∨ D.k + 1 ≤ E3.mQuot J₁ (J₁ ⊓ B) := by
      rcases hd₁ with h | h
      · exact Or.inl (h₁z.mpr (h₁B.mpr h))
      · exact Or.inr (by rwa [hJ₁u] at h)
    have hd₂' : E3.mQuot J₂ (J₂ ⊓ B) = 0 ∨ D.k + 1 ≤ E3.mQuot J₂ (J₂ ⊓ B) := by
      rcases hd₂ with h | h
      · exact Or.inl (h₂z.mpr (h₂B.mpr h))
      · exact Or.inr (by rwa [hJ₂u] at h)
    rcases hd₁' with hz₁ | hge₁
    · have hz₂ : E3.mQuot J₂ (J₂ ⊓ B) ≠ 0 := by
        intro h0
        omega
      refine ⟨J₁, ⟨hmem₁, h₁z.mp hz₁⟩, ?_⟩
      intro J hJ
      rcases mem_pair J hJ.1 with h | h
      · exact h
      · exfalso
        apply hz₂
        rw [h] at hJ
        exact h₂z.mpr hJ.2
    · have hz₂ : E3.mQuot J₂ (J₂ ⊓ B) = 0 := by omega
      refine ⟨J₂, ⟨hmem₂, h₂z.mp hz₂⟩, ?_⟩
      intro J hJ
      rcases mem_pair J hJ.1 with h | h
      · exfalso
        have hm₁0 : E3.mQuot J₁ (J₁ ⊓ B) = 0 := by
          rw [h] at hJ
          exact h₁z.mpr hJ.2
        omega
      · exact h
  have hpart4 : Case168_2 D ⊥ V hV L → ∀ J ∈ deltaConj Δ g, E3.mQuot J (B ⊓ J) = 1 := by
    intro hc J hJ
    have hk1 : D.k = 1 := hI.k_eq_one hc
    have hd₁ := hI.dist₂ hc u huVM hfix hmE J₁ hmem₁
    have hd₂ := hI.dist₂ hc u huVM hfix hmE J₂ hmem₂
    have hm₁ne : E3.mQuot J₁ (J₁ ⊓ B) ≠ 0 := fun h0 => hd₁ (h₁B.mp (h₁z.mp h0))
    have hm₂ne : E3.mQuot J₂ (J₂ ⊓ B) ≠ 0 := fun h0 => hd₂ (h₂B.mp (h₂z.mp h0))
    have hm₁pos : 1 ≤ E3.mQuot J₁ (J₁ ⊓ B) := Nat.one_le_iff_ne_zero.2 hm₁ne
    have hm₂pos : 1 ≤ E3.mQuot J₂ (J₂ ⊓ B) := Nat.one_le_iff_ne_zero.2 hm₂ne
    have hm₁ : E3.mQuot J₁ (J₁ ⊓ B) = 1 := by omega
    have hm₂ : E3.mQuot J₂ (J₂ ⊓ B) = 1 := by omega
    rcases mem_pair J hJ with h | h
    · rw [h, inf_comm]
      exact hm₁
    · rw [h, inf_comm]
      exact hm₂
  exact ⟨h1, ⟨hBeq, hsum1, hsum2⟩, hpart3, hpart4⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
