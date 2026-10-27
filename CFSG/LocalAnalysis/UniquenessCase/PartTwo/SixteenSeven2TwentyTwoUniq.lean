module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResults2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCase2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCoreA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyUniq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyTwoX

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_twenty_two_unique (D : Data G) (hk : D.k = 1)
    (h13 : R16_13_1 D) (h14 : R16_14 D) (h18 : R16_18 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} (hC : Counterex16 D ⊥ V L hV)
    {A : Subgroup G} {g : G} {Δ : Set (Subgroup G)} (hA : Choice1613 D ⊥ V hV L A)
    (hAg : A ≤ conjSubgroup V g) (hΔ : Concl1617 D ⊥ V hV L A g Δ)
    (h2 : Case168_2 D ⊥ V hV L) (hS : Case168_2Small D ⊥ V hV L) {B₁ B₂ U₁ U₂ : Subgroup G}
    (h₁ : Hyperplane1618 V A B₁ U₁) (h₂ : Hyperplane1618 V A B₂ U₂) : B₁ = B₂ := by
  have hI : Insp18 D ⊥ V hV L g Δ :=
    s16c167_insp18_case2 D hk hC.setting hC.conc hΔ h2
  have hn : Δ.ncard = 2 := hΔ.1
  have hΔV : ∀ I ∈ Δ, I ≤ V := hΔ.2.1
  have hsum : sSup Δ = V := hΔ.2.2.2.1
  obtain ⟨a, b, hab, hΔab⟩ := Set.ncard_eq_two.1 hn
  have haV : a ≤ V := hΔV a (by rw [hΔab]; exact Set.mem_insert_iff.2 (Or.inl rfl))
  have hbV : b ≤ V :=
    hΔV b (by rw [hΔab]; exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 rfl)))
  have hsup_ab : a ⊔ b = V := by
    rw [← sSup_pair]
    exact (by rw [← hΔab]; exact hsum)
  set J₁ : Subgroup G := conjSubgroup a g with hJ₁def
  set J₂ : Subgroup G := conjSubgroup b g with hJ₂def
  have hdelta : deltaConj Δ g = {J₁, J₂} := by
    rw [hΔab]
    unfold deltaConj
    rw [Set.image_pair]
  have hJ₁W : J₁ ≤ conjSubgroup V g := by
    rw [hJ₁def]
    exact E3.conjSubgroup_mono_left g haV
  have hJ₂W : J₂ ≤ conjSubgroup V g := by
    rw [hJ₂def]
    exact E3.conjSubgroup_mono_left g hbV
  have hsupJ : J₁ ⊔ J₂ = conjSubgroup V g := by
    rw [hJ₁def, hJ₂def]
    unfold conjSubgroup
    rw [← Subgroup.map_sup, hsup_ab]
  have hneJ : J₁ ≠ J₂ := by
    intro h
    rw [hJ₁def, hJ₂def] at h
    have h2 := congrArg (fun S : Subgroup G => conjSubgroup S g⁻¹) h
    rw [E3.conjSubgroup_conj_inv, E3.conjSubgroup_conj_inv] at h2
    exact hab h2
  have hJ₁el : IsElemAbelian 2 J₁ :=
    B2F.isElemAbelian_mono hJ₁W (E3.isElemAbelian_conjSubgroup hV g)
  have hJ₂el : IsElemAbelian 2 J₂ :=
    B2F.isElemAbelian_mono hJ₂W (E3.isElemAbelian_conjSubgroup hV g)
  have hmem₁ : J₁ ∈ deltaConj Δ g := by
    rw [hdelta]
    exact Set.mem_insert_iff.2 (Or.inl rfl)
  have hmem₂ : J₂ ∈ deltaConj Δ g := by
    rw [hdelta]
    exact Set.mem_insert_iff.2 (Or.inr (Set.mem_singleton_iff.2 rfl))
  obtain ⟨-, u₁, -, hu₁M, hu₁B, hu₁fix⟩ :=
    s16c167_eighteen_u D hV hC.setting.hyp16 (h14 ⊥ V L hV hC) hA.1 hAg hΔ hI h₁
  obtain ⟨-, u₂, -, hu₂M, hu₂B, hu₂fix⟩ :=
    s16c167_eighteen_u D hV hC.setting.hyp16 (h14 ⊥ V L hV hC) hA.1 hAg hΔ hI h₂
  obtain ⟨-, hdec₁, -, hcase2₁⟩ :=
    h18 ⊥ V L hV hC A g Δ hA hAg hΔ B₁ U₁ h₁
  obtain ⟨-, hdec₂, -, hcase2₂⟩ :=
    h18 ⊥ V L hV hC A g Δ hA hAg hΔ B₂ U₂ h₂
  have hBs₁ : B₁ = (B₁ ⊓ J₁) ⊔ (B₁ ⊓ J₂) := by
    have hstep : (⨆ I ∈ deltaConj Δ g, B₁ ⊓ I) = (B₁ ⊓ J₁) ⊔ (B₁ ⊓ J₂) := by
      rw [hdelta, iSup_pair]
    exact hdec₁.2.2.trans hstep
  have hBs₂ : B₂ = (B₂ ⊓ J₁) ⊔ (B₂ ⊓ J₂) := by
    have hstep : (⨆ I ∈ deltaConj Δ g, B₂ ⊓ I) = (B₂ ⊓ J₁) ⊔ (B₂ ⊓ J₂) := by
      rw [hdelta, iSup_pair]
    exact hdec₂.2.2.trans hstep
  have hm : E3.mQuot J₁ (B₁ ⊓ J₁) = 1 ∧ E3.mQuot J₂ (B₁ ⊓ J₂) = 1 :=
    ⟨hcase2₁ h2 J₁ hmem₁, hcase2₁ h2 J₂ hmem₂⟩
  have hm' : E3.mQuot J₁ (B₂ ⊓ J₁) = 1 ∧ E3.mQuot J₂ (B₂ ⊓ J₂) = 1 :=
    ⟨hcase2₂ h2 J₁ hmem₁, hcase2₂ h2 J₂ hmem₂⟩
  have hX : ∀ K ∈ ({J₁, J₂} : Set (Subgroup G)), ∃ x : G,
      conjSubgroup K x ∈ ({J₁, J₂} : Set (Subgroup G)) ∧ conjSubgroup K x ≠ K ∧
        conjSubgroup (K ⊓ centralizer ({u₁} : Set G)) x =
          conjSubgroup K x ⊓ centralizer ({u₁} : Set G) ∧
        conjSubgroup (K ⊓ centralizer ({u₂} : Set G)) x =
          conjSubgroup K x ⊓ centralizer ({u₂} : Set G) := by
    intro K hK
    have hKd : K ∈ deltaConj Δ g := by rw [hdelta]; exact hK
    obtain ⟨x, hKx, hKxne, hxall⟩ := s16c167_twenty_two_x D hC hΔ hS K hKd
    refine ⟨x, ?_, hKxne, hxall u₁ hu₁M hu₁fix, hxall u₂ hu₂M hu₂fix⟩
    rw [hdelta] at hKx
    exact hKx
  rcases s16c167_twenty_uniq (A := A) (Vg := conjSubgroup V g) (J := J₁) (J' := J₂)
    (B := B₁) (B' := B₂) (u := u₁) (u' := u₂)
    hJ₁W hJ₂W hneJ hsupJ hJ₁el hJ₂el h₁.1 h₂.1 hu₁B hu₂B hBs₁ hBs₂ hm hm' hX with h | h
  · exact h
  · exact absurd (h.trans (hA.1.1.trans D.sylowM.le))
      ((h13 ⊥ V L hV hC).2 A hA g hAg).1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
