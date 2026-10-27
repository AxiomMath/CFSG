module

public import CFSG.RankThree.Asc83Table.MatGroup
public import CFSG.RankThree.PartTwo.Sec21.Hering214KFour
public import CFSG.GroupTheory.BaerSuzuki
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Hering214KConj
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists
public import CFSG.RankThree.PartTwo.Sec4.LThreePiSLOn
public import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import Certificates.Certificate3084
public import Certificates.Certificate3169

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.Asc83Table
  CFSG.RankThree.Asc83Table.Native
open scoped commutatorElement

theorem hasOrd_pair_four {C : MCert} {r s : ℕ} (hr : ∃ e, MFact.ord r e ∈ C.facts)
    (hs : ∃ e, MFact.ord s e ∈ C.facts) (a b : ℕ) : HasOrd C [(r, a), (s, b)] := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  exacts [hr, hs]

theorem hasOrd_single_four {C : MCert} {r : ℕ} (hr : ∃ e, MFact.ord r e ∈ C.facts) (a : ℕ) :
    HasOrd C [(r, a)] := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl
  exact hr

structure FourFacts (C : MCert) (rz rw r₁ r₂ : ℕ) : Prop where
  o₁ : MFact.ord r₁ 2 ∈ C.facts
  o₂ : MFact.ord r₂ 2 ∈ C.facts
  comm : MFact.eq [(r₁, 1), (r₂, 1)] [(r₂, 1), (r₁, 1)] ∈ C.facts
  ne₁ : ∃ t, MFact.ne [(r₁, 1)] [] t ∈ C.facts
  ne₂ : ∃ t, MFact.ne [(r₂, 1)] [] t ∈ C.facts
  ne₁₂ : ∃ t, MFact.ne [(r₁, 1)] [(r₂, 1)] t ∈ C.facts
  zu₁ : ∃ a b, a < 2 ∧ b < 2 ∧ MFact.conj rz [(r₁, 1)] [(r₁, a), (r₂, b)] ∈ C.facts
  zu₂ : ∃ a b, a < 2 ∧ b < 2 ∧ MFact.conj rz [(r₂, 1)] [(r₁, a), (r₂, b)] ∈ C.facts
  wu₁ : ∃ a b, a < 2 ∧ b < 2 ∧ MFact.conj rw [(r₁, 1)] [(r₁, a), (r₂, b)] ∈ C.facts
  wu₂ : ∃ a b, a < 2 ∧ b < 2 ∧ MFact.conj rw [(r₂, 1)] [(r₁, a), (r₂, b)] ∈ C.facts
  moved : (∃ t, MFact.ne [(rz, 1), (r₁, 1)] [(r₁, 1), (rz, 1)] t ∈ C.facts) ∨
    (∃ t, MFact.ne [(rw, 1), (r₁, 1)] [(r₁, 1), (rw, 1)] t ∈ C.facts)

section Sound

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d) [Inhabited M]
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true)

theorem FourFacts.datum {rz rw r₁ r₂ : ℕ} (hz : MFact.ord rz 3 ∈ C.facts)
    (hw : MFact.ord rw 3 ∈ C.facts) (hF : FourFacts C rz rw r₁ r₂) :
    FourDatum (regUnit Sp hC rz) (regUnit Sp hC rw) := by
  have ho₁ : ∃ e, MFact.ord r₁ e ∈ C.facts := ⟨2, hF.o₁⟩
  have ho₂ : ∃ e, MFact.ord r₂ e ∈ C.facts := ⟨2, hF.o₂⟩
  have hoz : ∃ e, MFact.ord rz e ∈ C.facts := ⟨3, hz⟩
  have how : ∃ e, MFact.ord rw e ∈ C.facts := ⟨3, hw⟩
  have h₁ : regUnit Sp hC r₁ ^ 2 = 1 := regUnit_pow Sp hC hF.o₁
  have h₂ : regUnit Sp hC r₂ ^ 2 = 1 := regUnit_pow Sp hC hF.o₂
  have hcomm : Commute (regUnit Sp hC r₁) (regUnit Sp hC r₂) :=
    regUnit_comm' Sp hC hF.comm (hasOrd_pair_four ho₁ ho₂ 1 1) (hasOrd_pair_four ho₂ ho₁ 1 1)
  obtain ⟨t₁, ht₁⟩ := hF.ne₁
  obtain ⟨t₂, ht₂⟩ := hF.ne₂
  obtain ⟨t₃, ht₃⟩ := hF.ne₁₂
  have hne₁ : regUnit Sp hC r₁ ≠ 1 := regUnit_ne_one' Sp hC ht₁ (hasOrd_single_four ho₁ 1)
  have hne₂ : regUnit Sp hC r₂ ≠ 1 := regUnit_ne_one' Sp hC ht₂ (hasOrd_single_four ho₂ 1)
  have hne₁₂ : regUnit Sp hC r₁ ≠ regUnit Sp hC r₂ := by
    have := regUnit_ne_pow' Sp hC ht₃ (hasOrd_single_four ho₁ 1) (hasOrd_single_four ho₂ 1)
    rwa [pow_one] at this
  have key : ∀ {h : ℕ}, MFact.ord h 3 ∈ C.facts → ∀ {u : ℕ}, (∃ e, MFact.ord u e ∈ C.facts) →
      ∀ {a b : ℕ}, a < 2 → b < 2 → MFact.conj h [(u, 1)] [(r₁, a), (r₂, b)] ∈ C.facts →
      Four4 (regUnit Sp hC r₁) (regUnit Sp hC r₂)
        (regUnit Sp hC h * regUnit Sp hC u * (regUnit Sp hC h)⁻¹) := by
    intro h hh u hu a b ha hb hf
    have := regUnit_conj' Sp hC hf hh (hasOrd_single_four hu 1) (hasOrd_pair_four ho₁ ho₂ a b)
    rw [this]
    interval_cases a <;> interval_cases b <;> simp [Four4]
  have mv : ∀ {h : ℕ}, (∃ e, MFact.ord h e ∈ C.facts) → ∀ {t : ℕ},
      MFact.ne [(h, 1), (r₁, 1)] [(r₁, 1), (h, 1)] t ∈ C.facts →
      regUnit Sp hC h * regUnit Sp hC r₁ * (regUnit Sp hC h)⁻¹ ≠ regUnit Sp hC r₁ := by
    intro h hh t ht heq
    have hne := regUnit_ne Sp hC ht (hasOrd_pair_four hh ho₁ 1 1) (hasOrd_pair_four ho₁ hh 1 1)
    simp only [wordUnit_pair Sp hC, pow_one] at hne
    apply hne
    calc regUnit Sp hC h * regUnit Sp hC r₁
        = regUnit Sp hC h * regUnit Sp hC r₁ * (regUnit Sp hC h)⁻¹ * regUnit Sp hC h := by group
      _ = regUnit Sp hC r₁ * regUnit Sp hC h := by rw [heq]
  obtain ⟨a₁, b₁, ha₁, hb₁, hf₁⟩ := hF.zu₁
  obtain ⟨a₂, b₂, ha₂, hb₂, hf₂⟩ := hF.zu₂
  obtain ⟨a₃, b₃, ha₃, hb₃, hf₃⟩ := hF.wu₁
  obtain ⟨a₄, b₄, ha₄, hb₄, hf₄⟩ := hF.wu₂
  refine ⟨regUnit Sp hC r₁, regUnit Sp hC r₂, ?_, ?_, hcomm.eq, hne₁, hne₂, hne₁₂,
    key hz ho₁ ha₁ hb₁ hf₁, key hz ho₂ ha₂ hb₂ hf₂, key hw ho₁ ha₃ hb₃ hf₃,
    key hw ho₂ ha₄ hb₄ hf₄, ?_⟩
  · rwa [← pow_two]
  · rwa [← pow_two]
  · rcases hF.moved with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl (mv hoz ht)
    · exact Or.inr (mv how ht)

end Sound

structure Four27Facts (C : MCert) (rx ry rz r₃ r₄ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℕ) : Prop where
  ex27 : ∃ t, Ex27Facts C rx ry t
  oz : MFact.ord rz 3 ∈ C.facts
  ez : MFact.eq [(rz, 1)] (commWord rx ry) ∈ C.facts
  o₃ : MFact.ord r₃ 3 ∈ C.facts
  e₃ : MFact.eq [(r₃, 1)] [(rx, 1), (ry, 1)] ∈ C.facts
  o₄ : MFact.ord r₄ 3 ∈ C.facts
  e₄ : MFact.eq [(r₄, 1)] [(rx, 1), (ry, 2)] ∈ C.facts
  f₁ : FourFacts C rz rx a₁ b₁
  f₂ : FourFacts C rz ry a₂ b₂
  f₃ : FourFacts C rz r₃ a₃ b₃
  f₄ : FourFacts C rz r₄ a₄ b₄

section Config

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d) [Inhabited M]
  {sA sB : String} {C : MCert} (hC : mcertCheck O sA sB C = true)
  {rx ry rz r₃ r₄ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄ : ℕ}
  (hF : Four27Facts C rx ry rz r₃ r₄ a₁ b₁ a₂ b₂ a₃ b₃ a₄ b₄)

include Sp hC hF in
theorem Four27Facts.fourData27 : FourData27 (certMonoid p d sA sB)ˣ := by
  obtain ⟨t, hE⟩ := hF.ex27
  have hox : ∃ e, MFact.ord rx e ∈ C.facts := ⟨3, hE.hx⟩
  have hoy : ∃ e, MFact.ord ry e ∈ C.facts := ⟨3, hE.hy⟩
  have hoz : ∃ e, MFact.ord rz e ∈ C.facts := ⟨3, hF.oz⟩
  have ho₃ : ∃ e, MFact.ord r₃ e ∈ C.facts := ⟨3, hF.o₃⟩
  have ho₄ : ∃ e, MFact.ord r₄ e ∈ C.facts := ⟨3, hF.o₄⟩
  have hz : regUnit Sp hC rz = ⁅regUnit Sp hC rx, regUnit Sp hC ry⁆ := by
    rw [regUnit_eq' Sp hC hF.ez (hasOrd_single_four hoz 1) (hE.hasOrd_comm),
      hE.wordUnit_comm Sp hC]
  have h3 : regUnit Sp hC r₃ = regUnit Sp hC rx * regUnit Sp hC ry := by
    rw [regUnit_eq' Sp hC hF.e₃ (hasOrd_single_four ho₃ 1) (hasOrd_pair_four hox hoy 1 1),
      wordUnit_pair Sp hC, pow_one, pow_one]
  have h4 : regUnit Sp hC r₄ = regUnit Sp hC rx * regUnit Sp hC ry ^ 2 := by
    rw [regUnit_eq' Sp hC hF.e₄ (hasOrd_single_four ho₄ 1) (hasOrd_pair_four hox hoy 1 2),
      wordUnit_pair Sp hC, pow_one]
  refine ⟨regUnit Sp hC rx, regUnit Sp hC ry, hE.x_cube Sp hC, hE.y_cube Sp hC, hE.z_x Sp hC,
    hE.z_y Sp hC, hE.z_ne Sp hC, ?_, ?_, ?_, ?_⟩
  · rw [← hz]
    exact hF.f₁.datum Sp hC hF.oz hE.hx
  · rw [← hz]
    exact hF.f₂.datum Sp hC hF.oz hE.hy
  · rw [← hz, ← h3]
    exact hF.f₃.datum Sp hC hF.oz hF.o₃
  · rw [← hz, ← h4]
    exact hF.f₄.datum Sp hC hF.oz hF.o₄

end Config

end CFSG.RankThree.PartTwo.Sec21.Hering214
