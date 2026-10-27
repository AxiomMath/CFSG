module

public import CFSG.Quasithin.Vol2.Ch5StatementsB
public import CFSG.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.Vol2.Ch1Local

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

structure Emb512 (G : Type) [Group G] [Finite G] (T M L H B D K₁ X Kh₁ : Subgroup G)
    (n k : ℕ) : Prop where
  hyp : Hyp5_1_8 G T M L H n
  nota : IsNotation5_1_9 T M L H B D
  field : IsFieldParam510 T H k
  comp : quasithinIsCComponent K₁ H
  closure : oTwoUpper H = conjClosure K₁ T
  inH : InH H X
  hat : IsHatComp X K₁ Kh₁
  lt : oTwoUpper H < conjClosure Kh₁ T

namespace Emb512

variable {T M L H B D K₁ X Kh₁ : Subgroup G} {n k : ℕ}
  (e : Emb512 G T M L H B D K₁ X Kh₁ n k)
include e

theorem T_le_H : T ≤ H := e.hyp.hStar.1.1

theorem K₁_le_H : K₁ ≤ H := A3.subnormal_le e.comp.2.2.1

theorem K₁_le_X : K₁ ≤ X := e.K₁_le_H.trans e.inH.1

theorem T_le_X : T ≤ X := e.T_le_H.trans e.inH.1

theorem sylowH : IsSylowTwoOf T H := e.hyp.toHyp5_0_1.isSylowTwoOf e.T_le_H

theorem sylowX : IsSylowTwoOf T X := e.hyp.toHyp5_0_1.isSylowTwoOf e.T_le_X

theorem pCoreH : pCoreOf 2 H ≠ ⊥ := e.hyp.hStar.1.2

theorem pCoreX : pCoreOf 2 X ≠ ⊥ := e.inH.2

theorem K₁_cComp : K₁ ∈ cComp H := e.comp

theorem hat_cComp : Kh₁ ∈ cComp X := e.hat.1

theorem K₁_le_hat : K₁ ≤ Kh₁ := e.hat.2.1

theorem K₁_lFamily : K₁ ∈ lFamily T :=
  cComp_mem_of_le e.K₁_cComp le_sup_left (sup_le e.K₁_le_H e.T_le_H)

theorem isLocal₁ : quasithinIsLocal T K₁ :=
  isLocal_of_mem_cComp_of_sylow e.sylowH e.pCoreH e.K₁_cComp

theorem isLocalHat : quasithinIsLocal T Kh₁ :=
  isLocal_of_mem_cComp_of_sylow e.sylowX e.pCoreX e.hat_cComp

theorem K₁_le_K : K₁ ≤ oTwoUpper H := by
  rw [e.closure]
  exact le_conjClosure K₁ T

theorem T_le_normalizer_K : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
  rw [e.closure]
  exact le_normalizer_conjClosure K₁ T

theorem lt_or_eq : K₁ < oTwoUpper H ∨ K₁ = oTwoUpper H := lt_or_eq_of_le e.K₁_le_K

theorem T_le_normalizer₁ (heq : K₁ = oTwoUpper H) : T ≤ Subgroup.normalizer (K₁ : Set G) := by
  rw [heq]
  exact e.T_le_normalizer_K

omit [Finite G] e in
theorem conjClosure_hat_eq (hT : T ≤ Subgroup.normalizer (Kh₁ : Set G)) :
    conjClosure Kh₁ T = Kh₁ :=
  le_antisymm (conjClosure_le fun _ hg _ hl => (Subgroup.mem_normalizer_iff.mp (hT hg) _).mp hl)
    (le_conjClosure _ _)

theorem shape (heq : K₁ = oTwoUpper H) :
    IsBenderCh5 k (O2Q (oTwoUpper H)) ∨
      ((IsSL3Ch5 k (O2Q (oTwoUpper H)) ∨ LieModel (O2Q (oTwoUpper H)) .PSp 2 2 k) ∧
        E2.IsDiagramNontrivial T (oTwoUpper H) (T ⊓ oTwoUpper H)) := by
  obtain ⟨-, K₁', hK₁', -, hc⟩ := e.field
  rcases hc with ⟨hlt, -⟩ | ⟨-, hB⟩ | ⟨-, hS, hD⟩
  · exfalso
    rw [← heq] at hlt
    exact e.comp.2.2.2 K₁' hlt hK₁'.1 hK₁'.2.1 hK₁'.2.2.1
  · exact Or.inl hB
  · exact Or.inr ⟨hS, hD⟩

end Emb512

structure EmbLoc (G : Type) [Group G] [Finite G] (S X K Kh : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : quasithinIsQTKECat G
  pCoreX : pCoreOf 2 X ≠ ⊥
  sylowX : IsSylowTwoOf S X
  le_X : K ≤ X
  mem_lFamily : K ∈ lFamily S
  normalizes : S ≤ Subgroup.normalizer (K : Set G)
  hat : IsHatComp X K Kh
  lt : K < Kh

namespace EmbLoc

variable {S X K Kh : Subgroup G} (l : EmbLoc G S X K Kh)
include l

theorem hat_cComp : Kh ∈ cComp X := l.hat.1

theorem le_hat : K ≤ Kh := l.hat.2.1

theorem hat_le_X : Kh ≤ X := le_of_mem_cComp l.hat_cComp

theorem S_le_X : S ≤ X := l.sylowX.1

theorem perfect : ⁅K, K⁆ = K := perfect_of_mem_cComp l.mem_lFamily

theorem sylow_sup : IsSylowTwoOf S (K ⊔ S) := by
  refine ⟨le_sup_right, l.sylowX.2.1, fun hdvd => l.sylowX.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex S (K ⊔ S) X le_sup_right (sup_le l.le_X l.S_le_X)
  show 2 ∣ S.relIndex X
  rw [← h1]
  exact Dvd.dvd.mul_right hdvd _

theorem sylowK : IsSylowTwoOf (S ⊓ K) K :=
  A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp l.mem_lFamily) l.sylow_sup

end EmbLoc

end CFSG.Quasithin.H13
