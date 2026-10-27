module

public import CFSG.CGT.PushingUpLit.SolK.QStruct
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo

structure Setting (G : Type) [Group G] [Finite G] (M X : Subgroup G) (n : ℕ) : Prop where
  simple : IsSimpleGroup G
  nonab : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G
  charTwo : CFSG.Assembly.IsCharTwoType G
  evenRank : CFSG.Assembly.evenRank G = 3
  maxLocal : CFSG.IsMaximalTwoLocal M
  block : IsBlock M X
  elemU : CFSG.Open.IsElemAbelian 2 (blockU X)
  normalizer_eq : Subgroup.normalizer (X : Set G) = M
  uniq : CFSG.maximalTwoLocalsContaining (X : Set G) = {M}
  type : IsAltNaturalType X n
  n_mem : n = 6 ∨ n = 8 ∨ n = 10
  cent : ∀ x ∈ CFSG.Open.pCoreOf 2 M, x ≠ 1 →
    CFSG.generalizedFitting ↥(Subgroup.centralizer ({x} : Set G)) =
      CFSG.pCore 2 ↥(Subgroup.centralizer ({x} : Set G))

@[expose] def EvenN (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M X : Subgroup G), Setting G M X n →
    CFSG.Assembly.InCatalog G

namespace Setting

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {n : ℕ} (S : Setting G M X n)
include S

theorem le : X ≤ M := S.block.2.1

theorem normal {m : G} (hm : m ∈ M) {x : G} (hx : x ∈ X) : m * x * m⁻¹ ∈ X := by
  rw [← S.normalizer_eq] at hm
  exact (Subgroup.mem_normalizer_iff.mp hm x).mp hx

theorem xnorm : CFSG.CGT.PushingUpLit.SolK.XNorm M X where
  le := S.le
  normal := fun _ hm _ hx => S.normal hm hx

theorem centralizer_le : Subgroup.centralizer (X : Set G) ≤ M := by
  rw [← S.normalizer_eq]
  exact Subgroup.centralizer_le_normalizer (X : Set G)

theorem Y_le_Q : CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 M :=
  CFSG.CGT.PushingUpLit.SolK.XNorm.Y_le_Q S.xnorm

theorem W_le_Y : blockU X ≤ CFSG.Open.pCoreOf 2 X := by
  rw [blockU, blockQ, Subgroup.commutator_le]
  intro y hy x hx
  rw [commutatorElement_def]
  have h1 : x * y⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X :=
    CFSG.CGT.PushingUpLit.SolK.pCoreOf_normalized X hx ((CFSG.Open.pCoreOf 2 X).inv_mem hy)
  have h2 : y * x * y⁻¹ * x⁻¹ = y * (x * y⁻¹ * x⁻¹) := by group
  rw [h2]
  exact (CFSG.Open.pCoreOf 2 X).mul_mem hy h1

theorem W_le_Q : blockU X ≤ CFSG.Open.pCoreOf 2 M := S.W_le_Y.trans S.Y_le_Q

omit S in
theorem map_conj_eq_of_normalized {H : Subgroup G} {m : G}
    (h1 : ∀ x ∈ H, m * x * m⁻¹ ∈ H) (h2 : ∀ x ∈ H, m⁻¹ * x * m⁻¹⁻¹ ∈ H) :
    H.map (MulAut.conj m).toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact h1 x hx
  · intro x hx
    refine ⟨m⁻¹ * x * m⁻¹⁻¹, h2 x hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem W_normalized {m : G} (hm : m ∈ M) {w : G} (hw : w ∈ blockU X) :
    m * w * m⁻¹ ∈ blockU X := by
  have hY := map_conj_eq_of_normalized (H := CFSG.Open.pCoreOf 2 X) (m := m)
    (fun y hy => CFSG.CGT.PushingUpLit.SolK.XNorm.Y_normalized S.xnorm hm hy)
    (fun y hy => CFSG.CGT.PushingUpLit.SolK.XNorm.Y_normalized S.xnorm (M.inv_mem hm) hy)
  have hX := map_conj_eq_of_normalized (H := X) (m := m)
    (fun x hx => S.normal hm hx) (fun x hx => S.normal (M.inv_mem hm) hx)
  have hU : (blockU X).map (MulAut.conj m).toMonoidHom = blockU X := by
    rw [blockU, Subgroup.map_commutator, blockQ, hY, hX]
  rw [← hU]
  exact ⟨w, hw, rfl⟩

end Setting

end CFSG.RankThree.PartTwo.Sec19.SolEven
