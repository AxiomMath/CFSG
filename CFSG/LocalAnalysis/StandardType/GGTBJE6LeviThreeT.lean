module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import CFSG.LocalAnalysis.StandardType.GGTBJE6ThreeGlue
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviCell

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTBJE6LeviL_threeT
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : GGResXDatum p Bs L) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (hL : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥L ⧸ Subgroup.center ↥L))
    (hp3 : p = 3) (h3 : 3 ∣ 2 ^ n - 1) {labJ : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hdvd : n ∣ labJ.n) (hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4)) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs :=
    hH.1.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hH.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
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
  have hLC : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
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
  have hJX : J ≤ L := hcomp.1.trans inf_le_left
  have hJg : J ≤ Subgroup.centralizer ({y} : Set G) := hcomp.1.trans inf_le_right
  have hbXc : (x : G) ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hLx hl) x rfl).symm
  have hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hx1' : (⟨x, hxBs⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  subst hp3
  obtain ⟨-, -, -, hperf⟩ := GGConfig.data_L hH.1
  exact ggTBJE6Levi_threeT_of_label hRig hBs hSC hJX hyBs hJg hgX hcomp ⟨x, hxBs⟩ hx1' hbXc
    hcardJ hH.2.2.1.1 (ggTorusTBAt_L hH.1 hperf) hΛ hL h3 hΛJ hJlab hD4


theorem ggTBJE6LeviK_threeT
    (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJK : J ≤ K) (hX : GGResXDatum p Bs K) {n : ℕ}
    (hΛ : LargeEvenInLambda2 (⟨.E6, 0, n⟩ : LargeEvenLabel))
    (hK : GGHasLabel (⟨.E6, 0, n⟩ : LargeEvenLabel) (↥K ⧸ Subgroup.center ↥K))
    (hp3 : p = 3) (h3 : 3 ∣ 2 ^ n - 1) {labJ : LargeEvenLabel}
    (hΛJ : LargeEvenInLambda2 labJ) (hJlab : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J))
    (hdvd : n ∣ labJ.n) (hD4 : ¬ (labJ.tag = .D ∧ labJ.rank = 4)) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ a ∈ Subgroup.centralizer (Bs : Set G), a ^ p = 1 → a ∈ Bs :=
    hH.1.2.1.2.2.2
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hyB
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hH.1.1.2.2.2.2.2.2.1 hH.1.2.2 hnb hJK
  have hJg : J ≤ Subgroup.centralizer ({x} : Set G) := hcomp.1.trans inf_le_right
  have hgX : ∃ l ∈ K, x * l * x⁻¹ ≠ l := by
    by_contra h
    refine not_mem_centralizer_of_nbr hnb (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
    by_contra hne
    exact h ⟨l, hl, fun h' => hne (mul_inv_eq_iff_eq_mul.mp h').symm⟩
  have hbXc : (y : G) ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hl) y rfl).symm
  have hcardJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) ≤ p ^ 3 :=
    GGConfig.card_bstar_inf_centralizer_J_le hH.1
  have hy1' : (⟨y, hyBs⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hnb.1.2.2.1 (congrArg Subtype.val h)
  subst hp3
  obtain ⟨-, -, -, hperf⟩ := hH.data_K
  exact ggTBJE6Levi_threeT_of_label hRig hBs hSC hJK hxBs hJg hgX hcomp ⟨y, hyBs⟩ hy1' hbXc
    hcardJ (hH.2.2.1.2 _ _ hH.2.2.2.2.1) (ggTorusTBAt_nbr hH.1 hH.2.2.2.2.1 hperf) hΛ hK h3
    hΛJ hJlab hD4


theorem ggTBJE6LeviL_T
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviL .E6 fun p n labJ =>
      ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1) := by
  intro G _ _ p B Bs x L D J y K hH _ _ hX n hΛ hL _ labJ hΛJ hJlab hdvd hnc
  have hP : p = 3 ∧ 3 ∣ 2 ^ n - 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, h3⟩ := hP
  exact ggTBJE6LeviL_threeT hRig hH hX hΛ hL hp3 h3 hΛJ hJlab hdvd
    fun h => hnc (Or.inl ⟨h.1, h.2, hp3, h3⟩)

theorem ggTBJE6LeviK_T
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviK .E6 fun p n labJ =>
      ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1) := by
  intro G _ _ p B Bs x L D J y K hH hJK _ _ hX n hΛ hK _ labJ hΛJ hJlab hdvd hnc
  have hP : p = 3 ∧ 3 ∣ 2 ^ n - 1 := by
    by_contra h
    exact hnc (Or.inr h)
  obtain ⟨hp3, h3⟩ := hP
  exact ggTBJE6LeviK_threeT hRig hH hJK hX hΛ hK hp3 h3 hΛJ hJlab hdvd
    fun h => hnc (Or.inl ⟨h.1, h.2, hp3, h3⟩)

end CFSG.StandardType

end
