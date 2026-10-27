module

public import CFSG.LocalAnalysis.WeakClosure81.W16Gt2OrbitHyp
public import CFSG.LocalAnalysis.WeakClosure81.SevenThreeTI
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenTwo
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.LocalAnalysis.WeakClosure81.EightThreeE
public import CFSG.LocalAnalysis.WeakClosure81.SevenFour
public import CFSG.LocalAnalysis.WeakClosure81.ThirteenFour
public import CFSG.Open.SplitBNPair
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11
open CFSG.LocalAnalysis.WeakClosure81.SevenK
open Subgroup
open scoped Pointwise

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem w16l_inr_mem_kSub_of_mem_kHatOf (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) {n : ↥G} (hn : (n : LGL 2 V) ∈ kHatOf Γ) :
    (SemidirectProduct.inr n : VG G) ∈
      kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) := by
  let S : Set ↥G := ⋃ A ∈ Γ, (A.subgroupOf G : Set ↥G)
  have hgen : (⋃ A ∈ Γ, (A : Set (LGL 2 V))) ⊆
      ((Subgroup.closure S).map G.subtype : Set (LGL 2 V)) := by
    intro y hy
    rw [Set.mem_iUnion₂] at hy
    obtain ⟨A, hA, hyA⟩ := hy
    refine ⟨⟨y, h.le_G A hA hyA⟩, ?_, rfl⟩
    refine Subgroup.subset_closure ?_
    change (⟨y, h.le_G A hA hyA⟩ : ↥G) ∈ ⋃ A ∈ Γ, (A.subgroupOf G : Set ↥G)
    rw [Set.mem_iUnion₂]
    exact ⟨A, hA, hyA⟩
  have hnS : n ∈ Subgroup.closure S := by
    have h1 : (n : LGL 2 V) ∈ (Subgroup.closure S).map G.subtype :=
      ((Subgroup.closure_le (K := (Subgroup.closure S).map G.subtype)).mpr hgen) hn
    obtain ⟨m, hm, hmn⟩ := h1
    have hmn' : m = n := Subtype.ext hmn
    simpa [hmn'] using hm
  have hSle : Subgroup.closure S ≤
      (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)).comap
        (SemidirectProduct.inr : ↥G →* VG G) := by
    rw [Subgroup.closure_le]
    intro x hx
    change x ∈ ⋃ A ∈ Γ, (A.subgroupOf G : Set ↥G) at hx
    rw [Set.mem_iUnion₂] at hx
    obtain ⟨A, hA, hxA⟩ := hx
    change (x : LGL 2 V) ∈ A at hxA
    refine Subgroup.mem_comap.mpr ?_
    refine le_kSub (U := UAOf G VA A) ?_ ?_
    · rw [(thirteen_two_three h hrank htrans hA₀).1]
      exact ⟨A, hA, rfl⟩
    · exact Subgroup.mem_sup_right (S := wHat G (VA A)) (mem_aHat.mpr ⟨x, hxA, rfl⟩)
  exact hSle hnS

theorem w16l_inr_mem_pCoreOf_kSub (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ) {q : LGL 2 V}
    (hq : q ∈ pCoreOf 2 (kHatOf Γ)) (hqG : q ∈ G) :
    (SemidirectProduct.inr (⟨q, hqG⟩ : ↥G) : VG G) ∈
      pCoreOf 2 (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hqk : q ∈ kHatOf Γ := CFSG.LieType.BorelTits.pCoreOf_le 2 (kHatOf Γ) hq
  have hxK : (SemidirectProduct.inr (⟨q, hqG⟩ : ↥G) : VG G) ∈
      kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) :=
    w16l_inr_mem_kSub_of_mem_kHatOf h hrank htrans hA₀ (n := ⟨q, hqG⟩) (by simpa using hqk)
  exact (mem_pCoreOf_kSub_UAOf_orbit_iff h hrank htrans hA₀ hxK).2 (by
    rw [projG_inr]
    exact hq)

theorem w16l_UAOf_conj_of_congr (h : Assumption131 G Γ VA i)
    (hrank : ∀ A ∈ Γ, mRank A ≤ i) (hVAle : ∀ A ∈ Γ, VA A ≤ fixSub A)
    (htrans : ∀ A ∈ Γ, ∀ B ∈ Γ, ∃ g ∈ G, B = cj g A)
    {A₀ : Subgroup (LGL 2 V)} (hA₀ : A₀ ∈ Γ)
    (h711 : Hyp711 (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G))
    (hcore_le : pCoreOf 2 (kHatOf Γ) ≤ pCoreOf 2 G)
    {B B' : Subgroup (LGL 2 V)} (hB : B ∈ Γ) (hB' : B' ∈ Γ)
    {β β' : LGL 2 V} (hβ : β ∈ B) (hβ1 : β ≠ 1) (hβ' : β' ∈ B')
    (hq : β⁻¹ * β' ∈ pCoreOf 2 (kHatOf Γ)) :
    ∃ x ∈ pCoreOf 2 (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)),
      UAOf G VA B' = CFSG.Quasithin.conjSubgroup (UAOf G VA B) x := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsubi : iSub (UAOf G VA B) (⊤ : Subgroup (VG G)) (vHat G) =
      iSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) :=
    ((thirteen_two_three h hrank htrans hB).2).trans
      ((thirteen_two_three h hrank htrans hA₀).2).symm
  have hHypB : Hyp73 (UAOf G VA B) (⊤ : Subgroup (VG G)) (vHat G)
      (pCoreOf 2 (kSub (UAOf G VA B) (⊤ : Subgroup (VG G)) (vHat G))) :=
    hyp73_UAOf_orbit h hrank hVAle htrans hB
  have hBle : B ≤ kHatOf Γ := fun x hx =>
    Subgroup.subset_closure (Set.mem_iUnion.2 ⟨B, Set.mem_iUnion.2 ⟨hB, hx⟩⟩)
  have hB'le : B' ≤ kHatOf Γ := fun x hx =>
    Subgroup.subset_closure (Set.mem_iUnion.2 ⟨B', Set.mem_iUnion.2 ⟨hB', hx⟩⟩)
  obtain ⟨g, hgG, hBg⟩ := htrans A₀ hA₀ B hB
  obtain ⟨g', hg'G, hB'g'⟩ := htrans A₀ hA₀ B' hB'
  let gG : ↥G := ⟨g, hgG⟩
  let g'G : ↥G := ⟨g', hg'G⟩
  have hUB : UAOf G VA B = CFSG.Quasithin.conjSubgroup (UAOf G VA A₀)
      (SemidirectProduct.inr gG⁻¹ : VG G) := by
    rw [conjSubgroup_UAOf_inr_inv h hA₀ gG]
    exact congrArg (UAOf G VA) hBg
  have hUB' : UAOf G VA B' = CFSG.Quasithin.conjSubgroup (UAOf G VA A₀)
      (SemidirectProduct.inr g'G⁻¹ : VG G) := by
    rw [conjSubgroup_UAOf_inr_inv h hA₀ g'G]
    exact congrArg (UAOf G VA) hB'g'
  let hcon : VG G := (SemidirectProduct.inr gG⁻¹ : VG G)⁻¹ * SemidirectProduct.inr g'G⁻¹
  have hmul : (SemidirectProduct.inr gG⁻¹ : VG G) * hcon = SemidirectProduct.inr g'G⁻¹ := by
    simp only [hcon]
    group
  have hconj_h : CFSG.Quasithin.conjSubgroup (UAOf G VA B) hcon = UAOf G VA B' := by
    rw [hUB, hUB', CFSG.Quasithin.conjSubgroup_conjSubgroup, hmul]
  let xG : ↥G := ⟨β, h.le_G B hB hβ⟩
  let yG : ↥G := ⟨β', h.le_G B' hB' hβ'⟩
  let a : VG G := SemidirectProduct.inr xG
  let a' : VG G := SemidirectProduct.inr yG
  have ha : a ∈ UAOf G VA B :=
    Subgroup.mem_sup_right (S := wHat G (VA B)) (mem_aHat.mpr ⟨xG, hβ, rfl⟩)
  have ha' : a' ∈ CFSG.Quasithin.conjSubgroup (UAOf G VA B) hcon := by
    rw [hconj_h]
    exact Subgroup.mem_sup_right (S := wHat G (VA B')) (mem_aHat.mpr ⟨yG, hβ', rfl⟩)
  have haJ : a ∉ pCoreOf 2 (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)) := by
    intro haJ
    have haK : a ∈ kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G) :=
      CFSG.LieType.BorelTits.pCoreOf_le 2 _ haJ
    have hproj := (mem_pCoreOf_kSub_UAOf_orbit_iff h hrank htrans hA₀ haK).1 haJ
    have hβc : β ∈ pCoreOf 2 (kHatOf Γ) := by simpa [a, xG] using hproj
    have hbot : β ∈ (⊥ : Subgroup (LGL 2 V)) := by
      have hmem : β ∈ B ⊓ pCoreOf 2 G := ⟨hβ, hcore_le hβc⟩
      rwa [h.inf_pCore B hB] at hmem
    exact hβ1 (Subgroup.mem_bot.1 hbot)
  have haJ' : a⁻¹ * a' ∈ pCoreOf 2
      (kSub (UAOf G VA A₀) (⊤ : Subgroup (VG G)) (vHat G)) := by
    have hq' : ((xG⁻¹ * yG : ↥G) : LGL 2 V) ∈ pCoreOf 2 (kHatOf Γ) := by
      change β⁻¹ * β' ∈ pCoreOf 2 (kHatOf Γ)
      exact hq
    have hh := w16l_inr_mem_pCoreOf_kSub h hrank htrans hA₀ hq' (xG⁻¹ * yG).2
    have heq : a⁻¹ * a' = (SemidirectProduct.inr (xG⁻¹ * yG) : VG G) := by
      simp only [a, a', map_mul, map_inv]
    rw [heq]
    exact hh
  obtain ⟨x, hxJ, hxeq⟩ := seven_three_four_ti hHypB.elemAbelian hHypB.ti hHypB.abelian
    le_top hHypB.normal hHypB.mem (fun _ _ => le_top)
    h711.pcore_le h711.jnormal (by rw [hsubi]; exact h711.iSub_le)
    (Subgroup.mem_top hcon) ha haJ ha' haJ'
  exact ⟨x, hxJ, by rw [← hconj_h, hxeq]⟩

end CFSG.LocalAnalysis.WeakClosure81

end
