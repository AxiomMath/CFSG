module

public import CFSG.OddTranspositions.Blocks
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.Timmesfeld.Bridge.Asc72Minimal

import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.Timmesfeld.Bridge.Asc72ConjOrbit
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem commute_of_mem_conjOrbit_of_notMem (hD : IsOddTransp D) (hN : IsNormalSet D)
    {z x a b : G} (hx : x ∈ centSet D z) (ha : a ∈ conjOrbit (localGroup D z) x)
    (hb : b ∈ centSet D z) (hbx : b ∉ conjOrbit (localGroup D z) x) : Commute a b := by
  have hT : IsOddTransp (centSet D z) := hD.mono fun y hy => hy.1
  have hP : conjOrbit (localGroup D z) x ⊆ centSet D z := conjOrbit_subset_centSet hN hx
  have hQ : conjOrbit (localGroup D z) b ⊆ centSet D z := conjOrbit_subset_centSet hN hb
  have hPinv : ∀ g ∈ Subgroup.closure (centSet D z),
      ∀ y ∈ conjOrbit (localGroup D z) x, g * y * g⁻¹ ∈ conjOrbit (localGroup D z) x := by
    intro g hg y hy
    exact conj_mem_conjOrbit (M := localGroup D z) (by simpa [localGroup] using hg) hy
  have hQinv : ∀ g ∈ Subgroup.closure (centSet D z),
      ∀ y ∈ conjOrbit (localGroup D z) b, g * y * g⁻¹ ∈ conjOrbit (localGroup D z) b := by
    intro g hg y hy
    exact conj_mem_conjOrbit (M := localGroup D z) (by simpa [localGroup] using hg) hy
  exact commute_of_isOddTransp_invariant_partition hT hP hQ hPinv hQinv
    (disjoint_conjOrbit_of_not_mem hbx) a ha b (self_mem_conjOrbit _ b)

omit [Finite G] in
theorem conj_mem_iff_of_mem_of_commute_partition (hD : IsOddTransp D) (hN : IsNormalSet D)
    {z x : G} (hx : x ∈ centSet D z) {A B : Set G}
    (hAB : A ∪ B = conjOrbit (localGroup D z) x) (hdisj : Disjoint A B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {c : G} (hc : c ∈ centSet D z) (a : G) :
    c * a * c⁻¹ ∈ A ↔ a ∈ A := by
  have hc2 : c * c = 1 := hD.mul_self_eq_one hc.1
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hmem : ∀ y, y ∈ A ∪ B ↔ y ∈ conjOrbit (localGroup D z) x := fun y => by rw [hAB]
  have hgen : ∀ y ∈ A, c * y * c⁻¹ ∈ A := by
    intro y hy
    have hyO : y ∈ conjOrbit (localGroup D z) x := (hmem y).mp (Or.inl hy)
    have hcyO : c * y * c⁻¹ ∈ conjOrbit (localGroup D z) x :=
      conj_mem_conjOrbit (mem_localGroup_of_mem hc) hyO
    rcases (hmem _).mpr hcyO with h | h
    · exact h
    · exfalso
      have hcy : c * y * c⁻¹ = y := by
        by_cases hcA : c ∈ A
        · have hceq : c * (c * y * c⁻¹) = (c * y * c⁻¹) * c :=
            (hcomm c hcA _ h).eq
          have hyc : y * c = c * y := by
            calc y * c = c * (c * y * c⁻¹) := by rw [hcinv, ← mul_assoc, ← mul_assoc,
              hc2, one_mul]
              _ = (c * y * c⁻¹) * c := hceq
              _ = c * y := by rw [hcinv, mul_assoc, hc2, mul_one]
          rw [hcinv, ← hyc, mul_assoc, hc2, mul_one]
        · by_cases hcB : c ∈ B
          · have hyc : y * c = c * y := (hcomm y hy c hcB).eq
            rw [hcinv, ← hyc, mul_assoc, hc2, mul_one]
          · have hcO : c ∉ conjOrbit (localGroup D z) x := by
              intro hco
              exact (hmem c).mpr hco |>.elim hcA hcB
            have hyc : Commute y c :=
              commute_of_mem_conjOrbit_of_notMem hD hN hx hyO hc hcO
            rw [hcinv, ← hyc.eq, mul_assoc, hc2, mul_one]
      exact (Set.disjoint_left.mp hdisj) hy (hcy ▸ h)
  constructor
  · intro h
    have h' : c * (c * a * c⁻¹) * c⁻¹ ∈ A := hgen _ h
    rwa [show c * (c * a * c⁻¹) * c⁻¹ = a by
      rw [hcinv, show c * (c * a * c) * c = (c * c) * a * (c * c) by group, hc2];
      group] at h'
  · exact hgen a

omit [Finite G] in
theorem conj_mem_iff_of_mem_of_localGroup_partition (hD : IsOddTransp D) (hN : IsNormalSet D)
    {z x : G} (hx : x ∈ centSet D z) {A B : Set G}
    (hAB : A ∪ B = conjOrbit (localGroup D z) x) (hdisj : Disjoint A B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) {k : G} (hk : k ∈ localGroup D z) :
    ∀ a, k * a * k⁻¹ ∈ A ↔ a ∈ A := by
  induction hk using Subgroup.closure_induction with
  | mem c hc =>
      intro a
      exact conj_mem_iff_of_mem_of_commute_partition hD hN hx hAB hdisj hcomm hc a
  | one => intro a; simp
  | mul p q _ _ hp hq =>
      intro a
      rw [show (p * q) * a * (p * q)⁻¹ = p * (q * a * q⁻¹) * p⁻¹ by group, hp, hq]
  | inv p _ hp =>
      intro a
      have h := hp (p⁻¹ * a * p)
      rw [show p * (p⁻¹ * a * p) * p⁻¹ = a by group] at h
      simpa using h.symm

omit [Finite G] in
theorem eq_empty_or_eq_empty_of_commute (hD : IsOddTransp D) (hN : IsNormalSet D) {z x : G}
    (hx : x ∈ centSet D z) {A B : Set G} (hAB : A ∪ B = conjOrbit (localGroup D z) x)
    (hdisj : Disjoint A B) (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) : A = ∅ ∨ B = ∅ := by
  classical
  by_cases hA : A = ∅
  · exact Or.inl hA
  right
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr hA
  have haO : a ∈ conjOrbit (localGroup D z) x := by rw [← hAB]; exact Or.inl ha
  have horb : conjOrbit (localGroup D z) a = conjOrbit (localGroup D z) x := by
    obtain ⟨m, hm, rfl⟩ := haO
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k * m, (localGroup D z).mul_mem hk hm, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k * m⁻¹, (localGroup D z).mul_mem hk ((localGroup D z).inv_mem hm), by group⟩
  have hsub : conjOrbit (localGroup D z) x ⊆ A := by
    rw [← horb]
    rintro y ⟨k, hk, rfl⟩
    exact (conj_mem_iff_of_mem_of_localGroup_partition hD hN hx hAB hdisj hcomm hk a).mpr ha
  ext b
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hb
  have hbO : b ∈ conjOrbit (localGroup D z) x := by rw [← hAB]; exact Or.inr hb
  exact (Set.disjoint_left.mp hdisj) (hsub hbO) hb

theorem conjOrbit_subset_or_subset_DalphaStar (hC : HypothesisC D) {z x d : G}
    (hx : x ∈ centSet D z) (hd : d ∈ centSet D z) (hdx : d ∉ conjOrbit (localGroup D z) x)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) (hdρ : d ∈ ρ) :
    conjOrbit (localGroup D z) x ⊆ ρ ∨ conjOrbit (localGroup D z) x ⊆ DalphaStar D ρ := by
  classical
  have hD : IsOddTransp D := hC.setup.oddT
  have hN : IsNormalSet D := hC.setup.normal
  have hOsub : conjOrbit (localGroup D z) x ⊆ centSet D z := conjOrbit_subset_centSet hN hx
  have hsplit : ∀ a ∈ conjOrbit (localGroup D z) x, a ∈ ρ ∨ a ∈ DalphaStar D ρ := by
    intro a ha
    have hcomm : Commute d a :=
      (commute_of_mem_conjOrbit_of_notMem hD hN hx ha hd hdx).symm
    exact CFSG.OddTranspositions.PartThree.Nine.mem_block_or_DalphaStar_of_commute hC hρ hdρ
      (hOsub ha).1 hcomm
  set A : Set G := conjOrbit (localGroup D z) x ∩ ρ with hAdef
  set B : Set G := conjOrbit (localGroup D z) x ∩ DalphaStar D ρ with hBdef
  have hAB : A ∪ B = conjOrbit (localGroup D z) x := by
    ext a
    constructor
    · rintro (⟨ha, -⟩ | ⟨ha, -⟩) <;> exact ha
    · intro ha
      rcases hsplit a ha with h | h
      · exact Or.inl ⟨ha, h⟩
      · exact Or.inr ⟨ha, h⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro a ⟨-, haρ⟩ ⟨-, ⟨δ, hδ, haδ⟩⟩
    have hρblock : IsBlock D ρ :=
      isBlock_of_mem_blockClass hN hC.isBlock_alpha hρ
    have hδρ : δ = ρ :=
      eq_of_mem_of_mem_blockClass hρblock hδ.1 (mem_blockClass_self ρ) ⟨a, haδ, haρ⟩
    exact (mem_Dalpha_iff.mp hδ).2.2.1 hδρ
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    rintro a ⟨-, haρ⟩ b ⟨-, ⟨δ, hδ, hbδ⟩⟩
    exact (mem_Dalpha_iff.mp hδ).2.2.2 a haρ b hbδ
  have hcase := eq_empty_or_eq_empty_of_commute hD hN hx hAB hdisj hcomm
  rcases hcase with hA | hB
  · right
    intro a ha
    have hab : a ∈ A ∪ B := by rw [hAB]; exact ha
    rcases hab with h | h
    · rw [hA] at h
      exact False.elim ((Set.mem_empty_iff_false a).mp h)
    · exact h.2
  · left
    intro a ha
    have hab : a ∈ A ∪ B := by rw [hAB]; exact ha
    rcases hab with h | h
    · exact h.2
    · rw [hB] at h
      exact False.elim ((Set.mem_empty_iff_false a).mp h)

end CFSG.OddTranspositions.PartThree.EightEight

end
