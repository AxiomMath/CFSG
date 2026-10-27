module

public import CFSG.LocalAnalysis.StandardType.GGTBJE8LangWitness
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylNoLine
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggE8LangWitness_K_of_resHyp
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hreg : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    GGE8LangWitness n p J := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hH.1.1.2.2.2.2.2.2.1 hH.1.2.2 hnb hJK
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hxp : x ^ p = 1 := hH.1.2.1.2.1.2 x hxBs
  have hgX : ∃ l ∈ K, x * l * x⁻¹ ≠ l := by
    by_contra h
    refine not_mem_centralizer_of_nbr hnb (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
    by_contra hne
    exact h ⟨l, hl, fun h' => hne (mul_inv_eq_iff_eq_mul.mp h').symm⟩
  exact ggE8LangWitness_of_inner hRig hp hp2 hΛ (hH.2.2.1.2 y K hnb) hK hreg hxBs hxp hgX hcomp

theorem ggE8LangWitness_L_of_resHyp
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E8, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E8, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hreg : p ∣ 2 ^ n - 1 ∨ p ∣ 2 ^ n + 1) :
    GGE8LangWitness n p J := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hyp : y ^ p = 1 := hBs.2 y hyBs
  have hD : D = Subgroup.closure {x, y} := hnb.2.1
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  have hgX : ∃ l ∈ L, y * l * y⁻¹ ≠ l := by
    by_contra h
    have hyC : y ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun l hl => ?_
      by_contra hne
      exact h ⟨l, hl, fun h' => hne (mul_inv_eq_iff_eq_mul.mp h').symm⟩
    have hyx : y ∈ Subgroup.zpowers x := by
      rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
      exact ⟨hyB, hyC⟩
    have hle : D ≤ Subgroup.zpowers x := by
      rw [hD, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | rfl
      · exact Subgroup.mem_zpowers _
      · exact hyx
    have h1 : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hx1] at h1
    have : 1 < p := hp.one_lt
    nlinarith
  have hcomp0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hH.1.2.2.1.2.2.2.2.2.1
  have hyD : y ∈ D := by
    rw [hD]
    exact Subgroup.subset_closure (by simp)
  have hLC : L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyD))
    · intro l hl
      refine ⟨hl.1, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
      have hxl : x * l = l * x := Subgroup.mem_centralizer_iff.mp (hLx hl.1) x rfl
      have hyl : y * l = l * y := Subgroup.mem_centralizer_iff.mp hl.2 y rfl
      rw [hD] at hd
      refine Subgroup.closure_induction (p := fun d _ => d * l = l * d) ?_ ?_ ?_ ?_ hd
      · rintro d (rfl | rfl)
        · exact hxl
        · exact hyl
      · simp
      · intro a b _ _ ha hb
        rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
      · intro a _ ha
        exact (Commute.inv_left ha : Commute a⁻¹ l)
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := hLC ▸ hcomp0
  exact ggE8LangWitness_of_inner hRig hp hp2 hΛ hH.2.2.1.1 hL hreg hyBs hyp hgX hcomp

end CFSG.StandardType

end
