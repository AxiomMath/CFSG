module

public import CFSG.Quasithin.Background.B15P4Layer2Final
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.Background.B2Factorization

public section

namespace CFSG.Quasithin.LJ

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem isComponentOf_autI {X L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hLc : L ∈ cComp X)
    (hquasi : CFSG.Open.IsQuasisimple ↥(autI hV L)) :
    IsComponentOf (autI hV L) (autI hV X) := by
  have hLX : L ≤ X := le_of_mem_cComp hLc
  refine ⟨autI_mono hV hLX, ?_, hquasi⟩
  have h2 : IsSubnormal (L.subgroupOf X) ⊤ := by
    have := A3.subnormal_comap X.subtype (subnormal_of_mem_cComp hLc)
    have e : X.comap X.subtype = ⊤ := by ext x; simp
    rwa [e] at this
  have h3 := A3.subnormal_map (convHom hV X hXN) h2
  rw [← autI_eq_map_convHom hV hXN hLX, Subgroup.map_top, range_convHom hV X hXN] at h3
  exact h3

variable [Finite G]

theorem autI_thompsonJ_le_normalizer {X L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVX : V ≤ X) (hXN : X ≤ Subgroup.normalizer (V : Set G))
    (hcomp : IsComponentOf (autI hV L) (autI hV X)) :
    autI hV (thompsonJ X) ≤ Subgroup.normalizer ((autI hV L : Subgroup (MulAut (IntMod V hV))) :
      Set (MulAut (IntMod V hV))) := by
  rw [autI_thompsonJ hV hXN]
  refine iSup_le fun B => iSup_le fun hB => iSup_le fun _ => ?_
  exact B15P4.asB15Part4 (IntMod V hV) (fun v => IntMod.sq_eq_one v) (autI hV X) B
    (offenderImages_isFFStarOffender hV hVX hXN hB) (autI hV L) hcomp

theorem thompsonJ_le_normalizer_of_offenders {X S L V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hVX : V ≤ X) (hXN : X ≤ Subgroup.normalizer (V : Set G)) (hS : IsSylowTwoOf S X)
    (hLc : L ∈ cComp X) (hLV : ¬ L ≤ Subgroup.centralizer (V : Set G))
    (hquasi : CFSG.Open.IsQuasisimple ↥(autI hV L))
    (hcomm : ∀ L' ∈ cComp X, L' ≠ L → ⁅L, L'⁆ ≤ Subgroup.centralizer (V : Set G)) :
    thompsonJ S ≤ Subgroup.normalizer (L : Set G) := by
  have hLX : L ≤ X := le_of_mem_cComp hLc
  have hJX := autI_thompsonJ_le_normalizer hV hVX hXN (isComponentOf_autI hV hXN hLc hquasi)
  intro a ha
  have hJa : a ∈ thompsonJ X := thompsonJ_le_thompsonJ_of_isSylowTwoOf hS ha
  have haX : a ∈ X := B6.thompsonJ_le X hJa
  have hastar : convI hV ⟨a, hXN haX⟩ ∈ Subgroup.normalizer ((autI hV L : Subgroup (MulAut
      (IntMod V hV))) : Set (MulAut (IntMod V hV))) := hJX (convI_mem_autI hV hJa (hXN haX))
  by_contra hnot
  have hL'c : L.map (MulAut.conj a).toMonoidHom ∈ cComp X := map_conj_mem_cComp hLc haX
  have hne : L.map (MulAut.conj a).toMonoidHom ≠ L := fun h => hnot (A38.map_conj_eq_iff.mp h)
  have hcm := hcomm _ hL'c hne
  set φ := convHom hV X hXN with hφ
  set ā := convI hV ⟨a, hXN haX⟩ with hā
  have hLsmem : ∀ x ∈ autI hV L, ∃ l : ↥X, (l : G) ∈ L ∧ φ l = x := by
    intro x hx
    obtain ⟨g, hg, rfl⟩ := (mem_autI hV).1 hx
    exact ⟨⟨g, hLX hg⟩, hg, rfl⟩
  have hab : ∀ x ∈ autI hV L, ∀ y ∈ autI hV L, x * y = y * x := by
    intro x hx y hy
    obtain ⟨l₁, hl₁, rfl⟩ := hLsmem x hx
    have hy' : ā⁻¹ * y * ā ∈ autI hV L := by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer _).inv_mem hastar) y).mp hy
      simpa [hā] using this
    obtain ⟨l₂, hl₂, he⟩ := hLsmem _ hy'
    set l₃ : ↥X := ⟨a, haX⟩ * l₂ * ⟨a, haX⟩⁻¹ with hl₃
    have hφa : φ ⟨a, haX⟩ = ā := rfl
    have hy3 : y = φ l₃ := by
      rw [hl₃, map_mul, map_mul, map_inv, hφa, he]
      group
    have hl₃L' : (l₃ : G) ∈ L.map (MulAut.conj a).toMonoidHom := ⟨(l₂ : G), hl₂, by
      simp [hl₃]⟩
    have hcc : ⁅l₁, l₃⁆ ∈ φ.ker := by
      rw [hφ, ker_convHom hV X hXN, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨(⁅l₁, l₃⁆ : ↥X).2, ?_⟩
      have e : ((⁅l₁, l₃⁆ : ↥X) : G) = ⁅(l₁ : G), (l₃ : G)⁆ := by
        simp [commutatorElement_def]
      rw [e]
      exact hcm (Subgroup.commutator_mem_commutator hl₁ hl₃L')
    have h1 : ⁅φ l₁, φ l₃⁆ = 1 := by
      rw [← map_commutatorElement]
      exact hcc
    rw [hy3]
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1)
  have hperf : ⁅autI hV L, autI hV L⁆ = autI hV L := Subgroup.isPerfect_iff.1
    (Group.isPerfect_def.mpr hquasi.1)
  have hbot : autI hV L = ⊥ := by
    rw [← hperf, eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_def]
    have := hab x hx y hy
    rw [this]
    group
  exact hLV ((autI_eq_bot_iff hV (hLX.trans hXN)).1 hbot)

end CFSG.Quasithin.LJ
