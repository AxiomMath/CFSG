module

public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGFieldNbr
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusSmall
public import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusCover
import CFSG.LocalAnalysis.StandardType.GGTBJUnitaryMinusSide
import CFSG.LocalAnalysis.StandardType.GGTBJSpPlus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggTBJLeft_uniMinus_of_label
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 5 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (↥L ⧸ Subgroup.center ↥L))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    GGResSideDatum p Bs L J ∨ GGResLeviSideDatumLE3 p Bs L J := by
  classical
  have hp : p.Prime := Fact.out
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨F, hField, hFinite, m, ε, hUFD, ζ, τ, φ, hdim, hε, hζ, hζb, hsplit, hφX, hker, hkp,
    hBsN, hinj, hfr, hmeet, hact⟩ :=
    exists_hypFrame_of_uniMinus hRig hBs hSC hH.2.2.1.1 (by omega) hpq hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  have hm : 2 ≤ m := by omega
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (Subgroup.mem_centralizer_iff.mp (hLx hl) x rfl).symm
  have hDgen : D = Subgroup.closure {x, y} := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by
    rw [hDgen]
    exact Subgroup.subset_closure (by simp)
  have hDB : D ≤ B := hcfg.2.2.1.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 (hDB hyD)
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hyX : y ∉ Subgroup.centralizer (L : Set G) := by
    intro hyC
    have hyx : y ∈ Subgroup.zpowers x := by
      rw [← inf_centralizer_eq_zpowers_of_sstar hp hS]
      exact ⟨hDB hyD, hyC⟩
    have hDle : D ≤ Subgroup.zpowers x := by
      rw [hDgen, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact Subgroup.mem_zpowers g
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact hyx
    have hle := Subgroup.card_le_of_le hDle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 x hxBs) hx1] at hle
    have : 1 < p := hp.one_lt
    nlinarith
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hLD : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hDgen, Subgroup.centralizer_closure]
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hl, h⟩
      exact ⟨hl, fun g hg => h g (Or.inr hg)⟩
    · rintro ⟨hl, h⟩
      refine ⟨hl, fun g hg => ?_⟩
      rcases hg with rfl | rfl
      · exact Subgroup.mem_centralizer_iff.mp (hLx hl) g rfl
      · exact h g rfl
  have hJ' : IsComponentOf J (L ⊓ Subgroup.centralizer ({y} : Set G)) := hLD ▸ hJcomp
  exact ggTBJ_uniMinus_sideDatum_of_frame hUFD hp2 hpq hε hm hζ hζb hsplit hBs hφX hker hkp hinj
    hfr hmeet hact hyBs hyX hJ' hxBs hxC hx1 hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJNbr_uniMinus_of_label
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    {r f : ℕ} (hr : 5 ≤ r) (hpq : p ∣ 2 ^ f - 1)
    (hLab : GGHasLabel ⟨.twA, r, f⟩ (↥K ⧸ Subgroup.center ↥K))
    (hΛ : LargeEvenInLambda2 ⟨.twA, r, f⟩) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hp : p.Prime := Fact.out
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨F, hField, hFinite, m, ε, hUFD, ζ, τ, φ, hdim, hε, hζ, hζb, hsplit, hφX, hker, hkp,
    hBsN, hinj, hfr, hmeet, hact⟩ :=
    exists_hypFrame_of_uniMinus hRig hBs hSC (hH.2.2.1.2 y K hnb) (by omega) hpq hLab hΛ
  let : Field F := hField
  let : Finite F := hFinite
  have hm : 2 ≤ m := by omega
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hyB : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hyB
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hyC : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hnb.1.2.2.2.1 hk) y rfl).symm
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hxX : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hxC
    have hxy : x ∈ Subgroup.zpowers y := by
      rw [← inf_centralizer_eq_zpowers_of_sHat hnb.1]
      exact ⟨hxB, hxC⟩
    have hDle : D ≤ Subgroup.zpowers y := by
      have hDgen : D = Subgroup.closure {x, y} := hH.2.2.2.2.1.2.1
      rw [hDgen, Subgroup.closure_le]
      intro g hg
      rcases hg with rfl | hg
      · exact hxy
      · rw [Set.mem_singleton_iff] at hg
        rw [hg]
        exact Subgroup.mem_zpowers y
    have hle := Subgroup.card_le_of_le hDle
    rw [hDcard, Nat.card_zpowers, orderOf_eq_prime (hBs.2 y hyBs) hy1] at hle
    have : 1 < p := hp.one_lt
    nlinarith
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hJ' : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  exact ggTBJ_uniMinus_sideDatum_of_frame hUFD hp2 hpq hε hm hζ hζb hsplit hBs hφX hker hkp hinj
    hfr hmeet hact hxBs hxX hJ' hyBs hyC hy1 hcfg.card_bstar_inf_centralizer_J_le

theorem ggTBJLeftOn_uniMinusLarge
    (hRig : GGLabelRigidInput) :
    GGTBJLeftOn ggTBJUniMinusLargeLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL _
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨htag, hr5, hpq⟩ := hP.1
  have hlab : lab = ⟨.twA, lab.rank, lab.n⟩ := by
    rcases lab with ⟨t, r, n⟩
    simp only at htag
    subst htag
    rfl
  have hΛ' : LargeEvenInLambda2 (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) := by
    rw [← hlab]
    exact hΛ
  have hhas' : GGHasLabel (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L) := by
    rw [← hlab]
    exact hhas
  rcases ggTBJLeft_uniMinus_of_label hRig hH hr5 hpq hhas' hΛ' with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJNbrOn_uniMinusLarge
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn ggTBJUniMinusLargeLabel := by
  intro G _ _ p B Bs x L D J y K hH hp hL _
  obtain ⟨lab, hΛ, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨htag, hr5, hpq⟩ := hP.1
  have hlab : lab = ⟨.twA, lab.rank, lab.n⟩ := by
    rcases lab with ⟨t, r, n⟩
    simp only at htag
    subst htag
    rfl
  have hΛ' : LargeEvenInLambda2 (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel) := by
    rw [← hlab]
    exact hΛ
  have hhas' : GGHasLabel (⟨.twA, lab.rank, lab.n⟩ : LargeEvenLabel)
      (↥K ⧸ Subgroup.center ↥K) := by
    rw [← hlab]
    exact hhas
  rcases ggTBJNbr_uniMinus_of_label hRig hI3 hH hr5 hpq hhas' hΛ' with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem ggTBJLeftOn_uniMinus
    (hRig : GGLabelRigidInput) :
    GGTBJLeftOn ggTBJUniMinusLabel :=
  (ggTBJLeftOn_uniMinusSmall.or (ggTBJLeftOn_uniMinusLarge hRig)).mono
    fun _ _ h => ggTBJUniMinusLabel_cases h

theorem ggTBJNbrOn_uniMinus
    (hRig : GGLabelRigidInput) (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn ggTBJUniMinusLabel :=
  (ggTBJNbrOn_uniMinusSmall.or (ggTBJNbrOn_uniMinusLarge hRig hI3)).mono
    fun _ _ h => ggTBJUniMinusLabel_cases h

end CFSG.StandardType

end
