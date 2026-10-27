module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssemblyR
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeKFixLineDefs
public import CFSG.LocalAnalysis.StandardType.GGTWCoreDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGResTwoNodeLE3SmallInput : Prop :=
  GGResLeaf fun _ _ _ p _ _ Bs x L _ J y K =>
    (GGResRowAt ggRowTwoNodeSmall p J L ∧ x ∉ L ∧ GGResLeviSideDatumLE3 p Bs K J) ∨
      (GGResRowAt ggRowTwoNodeSmall p J K ∧ y ∉ K ∧ GGResLeviSideDatumLE3 p Bs L J)

@[expose] def ggRowTwoNodeSmallJA (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNodeSmall p J X ∧ (J.tag = .A ∨ J.tag = .twA)

@[expose] def ggRowTwoNodeSmallJD (p : ℕ) (J X : LargeEvenLabel) : Prop :=
  ggRowTwoNodeSmall p J X ∧ J.tag = .D

@[expose] def GGTBJTwoNodeSmallInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K → ∀ [Fact p.Prime],
    (GGResXDatum p Bs L → GGResRowAt ggRowTwoNodeSmallJA p J L → GGResTwoNodeSideDatum p Bs L J) ∧
      (GGResXDatum p Bs K → GGResRowAt ggRowTwoNodeSmallJA p J K → GGResTwoNodeSideDatum p Bs K J)

theorem ggTWSmall_yK_of_Z (hZ : GGTWZKInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {labJ labK : LargeEvenLabel}
    (hJΛ : LargeEvenInLambda2 labJ) (hKΛ : LargeEvenInLambda2 labK)
    (hJl : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hKl : GGHasLabel labK (↥K ⧸ Subgroup.center ↥K)) (hJtag : labJ.tag = .A ∨ labJ.tag = .twA)
    (hpN : p ∣ labJ.rank + 3)
    (hA : ((labK.tag = .A ∧ ¬ p ∣ labK.rank + 1) ∨
        (labK.tag = .twA ∧ ¬ p ∣ labK.rank + 1 ∧ p ∣ 2 ^ labK.n + 1) ∨
        (p = 3 ∧ labK.tag = .D ∧ labK.rank = 4)) → ¬ p ∣ Nat.card ↥(Subgroup.center ↥K))
    (hK : GGResSideDatum p Bs K J) : y ∉ K := by
  classical
  intro hyK
  have hnd : ¬ p ∣ Nat.card ↥(Subgroup.center ↥K) := by
    by_cases hcov : (labK.tag = .A ∧ ¬ p ∣ labK.rank + 1) ∨
        (labK.tag = .twA ∧ ¬ p ∣ labK.rank + 1 ∧ p ∣ 2 ^ labK.n + 1) ∨
        (p = 3 ∧ labK.tag = .D ∧ labK.rank = 4)
    · exact hA hcov
    · exact hZ G p B Bs x L D J y K hH labJ labK hJΛ hKΛ hJl hKl hJtag hpN hcov hK
  have hDcl : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hDea : IsElemAbelian p D := hH.1.2.2.1.2.1
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hxD : x ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hyD : y ∈ D := hDcl ▸ Subgroup.subset_closure (by simp)
  have hy_ne1 : y ≠ 1 := by
    intro hy1
    have hcl : Subgroup.closure ({x, y} : Set G) = Subgroup.zpowers x := by
      apply le_antisymm
      · rw [Subgroup.closure_le]; rintro z hz; rcases hz with hz | hz
        · rw [hz]; exact Subgroup.mem_zpowers x
        · simp only [Set.mem_singleton_iff] at hz; rw [hz, hy1]; exact Subgroup.one_mem _
      · exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have h1 : Nat.card D ≤ p := by
      rw [hDcl, hcl, Nat.card_zpowers]
      exact Nat.le_of_dvd (Fact.out : p.Prime).pos
        (orderOf_dvd_iff_pow_eq_one.mpr (hDea.2 x hxD))
    have : p ^ 2 ≤ p := by simpa [hDcard] using h1
    nlinarith [(Fact.out : p.Prime).two_le]
  have hyord : orderOf y = p := orderOf_eq_prime (hDea.2 y hyD) hy_ne1
  have hKy : K ≤ Subgroup.centralizer ({y} : Set G) := hH.2.2.2.2.1.1.2.2.2.1
  have hzc : (⟨y, hyK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro k
    have hk : y * (k : G) = (k : G) * y :=
      Subgroup.mem_centralizer_iff.mp (hKy k.2) y (Set.mem_singleton y)
    exact Subtype.ext hk.symm
  have hdvd : orderOf (⟨(⟨y, hyK⟩ : K), hzc⟩ : Subgroup.center K) ∣
      Nat.card ↥(Subgroup.center ↥K) := orderOf_dvd_natCard _
  have hord : orderOf (⟨(⟨y, hyK⟩ : K), hzc⟩ : Subgroup.center K) = p := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hyord]
  exact hnd (hord ▸ hdvd)

end CFSG.StandardType

end
