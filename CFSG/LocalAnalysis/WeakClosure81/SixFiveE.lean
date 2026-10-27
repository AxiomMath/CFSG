module

public import CFSG.LocalAnalysis.WeakClosure81.SixFiveD
public import CFSG.RankThree.GF2n.Tim78P210Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def pairConjOf (V : Subgroup G) (g : G) : Set (Subgroup G) :=
  {A | ∃ x ∈ LOf V g, A = conjSubgroup V x ∨ A = conjSubgroup (conjSubgroup V g) x}

theorem V_mem_pairConjOf (V : Subgroup G) (g : G) : V ∈ pairConjOf V g :=
  ⟨1, Subgroup.one_mem _, Or.inl (conjSubgroup_one V).symm⟩

theorem conjV_mem_pairConjOf (V : Subgroup G) (g : G) : conjSubgroup V g ∈ pairConjOf V g :=
  ⟨1, Subgroup.one_mem _, Or.inr (conjSubgroup_one (conjSubgroup V g)).symm⟩

theorem le_LOf_of_mem_pairConjOf {V : Subgroup G} {g : G} {A : Subgroup G}
    (hA : A ∈ pairConjOf V g) : A ≤ LOf V g := by
  obtain ⟨x, hxL, hxA | hxA⟩ := hA
  · rw [hxA]
    exact (conjSubgroup_mono (le_sup_left : V ≤ LOf V g) x).trans
      (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hxL)))
  · rw [hxA]
    exact (conjSubgroup_mono (le_sup_right : conjSubgroup V g ≤ LOf V g) x).trans
      (le_of_eq (conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hxL)))

namespace Hyp65

variable {n : ℕ} {M V₀ V : Subgroup G} {g : G}

theorem isElemAbelian_of_mem_pairConjOf (h : Hyp65 n M V₀ V g) {A : Subgroup G}
    (hA : A ∈ pairConjOf V g) : IsElemAbelian 2 A := by
  obtain ⟨x, -, hxA | hxA⟩ := hA
  · rw [hxA]
    exact isElemAbelian_conjSubgroup' h.elemAbelian x
  · rw [hxA, conjSubgroup_conjSubgroup]
    exact isElemAbelian_conjSubgroup' h.elemAbelian (g * x)

theorem conjV₀_eq_of_inf_ne_bot (h : Hyp65 n M V₀ V g) {y y' : G}
    (hne : conjSubgroup V₀ y ⊓ conjSubgroup V₀ y' ≠ ⊥) :
    conjSubgroup V₀ y = conjSubgroup V₀ y' :=
  (inf_conjSubgroup_eq_bot_or_eq h.isTI y y').resolve_left hne

theorem conjV_eq_of_conjV₀_eq (h : Hyp65 n M V₀ V g) {y y' : G}
    (he : conjSubgroup V₀ y = conjSubgroup V₀ y') : conjSubgroup V y = conjSubgroup V y' :=
  conjSubgroup_V₀_eq_of_conjSubgroup_eq (A := V) (V := V₀) (x := y) (y := y')
    h.normalizer₀ h.normalizer_eq.ge he

private theorem s65_SixFiveE_conj_inf_C_le_K (h : Hyp65 n M V₀ V g) {A₀ : Subgroup G}
    (hAK : A₀ ⊓ COf M V₀ V g ≤ KOf M V g) {x : G} (hx : x ∈ LOf V g) :
    conjSubgroup A₀ x ⊓ COf M V₀ V g ≤ KOf M V g := by
  intro a ha
  obtain ⟨haA, haC⟩ := Subgroup.mem_inf.mp ha
  have hxaxA : x * a * x⁻¹ ∈ A₀ := mem_conjSubgroup_iff.mp haA
  have hxaxC : x * a * x⁻¹ ∈ COf M V₀ V g := by
    have hnorm := h.L_le_normalizer_C hx
    rw [Subgroup.mem_normalizer_iff] at hnorm
    exact (hnorm a).mp haC
  have hxaxK : x * a * x⁻¹ ∈ KOf M V g := hAK (Subgroup.mem_inf.mpr ⟨hxaxA, hxaxC⟩)
  have hnormK := h.L_le_normalizer_K (Subgroup.inv_mem (LOf V g) hx)
  rw [Subgroup.mem_normalizer_iff] at hnormK
  have h := (hnormK (x * a * x⁻¹)).mp hxaxK
  have haeq : x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ = a := by group
  rwa [haeq] at h

theorem inf_C_le_K (h : Hyp65 n M V₀ V g) {A : Subgroup G} (hA : A ∈ pairConjOf V g) :
    A ⊓ COf M V₀ V g ≤ KOf M V g := by
  obtain ⟨x, hxL, hxA | hxA⟩ := hA
  · rw [hxA]
    refine h.s65_SixFiveE_conj_inf_C_le_K ?_ hxL
    rw [inf_comm, h.C_inf_V]
    exact le_sup_left
  · rw [hxA]
    refine h.s65_SixFiveE_conj_inf_C_le_K ?_ hxL
    rw [inf_comm, h.C_inf_conjV]
    exact le_sup_right

private theorem s65_SixFiveE_L0_inf_centralizer_conj (h : Hyp65 n M V₀ V g) {x a : G}
    (hx : x ∈ LOf V g) :
    L0Of M V₀ g ⊓ centralizer ({a} : Set G) =
      conjSubgroup (L0Of M V₀ g ⊓ centralizer ({x * a * x⁻¹} : Set G)) x := by
  ext l
  rw [mem_conjSubgroup_iff]
  have hL0 : l ∈ L0Of M V₀ g ↔ x * l * x⁻¹ ∈ L0Of M V₀ g := by
    have hnorm := h.L_le_normalizer_L0 hx
    rw [Subgroup.mem_normalizer_iff] at hnorm
    exact hnorm l
  have hcen : l ∈ centralizer ({a} : Set G) ↔
      x * l * x⁻¹ ∈ centralizer ({x * a * x⁻¹} : Set G) := by
    constructor
    · intro hl
      rw [Subgroup.mem_centralizer_iff] at hl ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hc := hl a (Set.mem_singleton a)
      calc (x * a * x⁻¹) * (x * l * x⁻¹) = x * (a * l) * x⁻¹ := by group
        _ = x * (l * a) * x⁻¹ := by rw [hc]
        _ = (x * l * x⁻¹) * (x * a * x⁻¹) := by group
    · intro hl
      rw [Subgroup.mem_centralizer_iff] at hl ⊢
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hc := hl (x * a * x⁻¹) (Set.mem_singleton (x * a * x⁻¹))
      have h2 : x * (a * l) * x⁻¹ = x * (l * a) * x⁻¹ := by
        calc x * (a * l) * x⁻¹ = (x * a * x⁻¹) * (x * l * x⁻¹) := by group
          _ = (x * l * x⁻¹) * (x * a * x⁻¹) := hc
          _ = x * (l * a) * x⁻¹ := by group
      have h3 : x⁻¹ * (x * (a * l) * x⁻¹) * x = a * l := by group
      have h4 : x⁻¹ * (x * (l * a) * x⁻¹) * x = l * a := by group
      have h5 := congrArg (fun z => x⁻¹ * z * x) h2
      rwa [h3, h4] at h5
  simp only [Subgroup.mem_inf]
  rw [hL0, hcen]

theorem exists_centralizer_L0 (h : Hyp65 n M V₀ V g) {A : Subgroup G}
    (hA : A ∈ pairConjOf V g) {a : G} (ha : a ∈ A) (haC : a ∉ COf M V₀ V g) :
    ∃ y : G, A = conjSubgroup V y ∧
      L0Of M V₀ g ⊓ centralizer ({a} : Set G) ≠ ⊥ ∧
      L0Of M V₀ g ⊓ centralizer ({a} : Set G) ≤ conjSubgroup V₀ y := by
  obtain ⟨x, hxL, hxA | hxA⟩ := hA
  · have haV : a ∈ conjSubgroup V x := hxA ▸ ha
    set a' := x * a * x⁻¹ with ha'def
    have ha'V : a' ∈ V := mem_conjSubgroup_iff.mp haV
    have ha'U : a' ∉ UOf M V g := by
      intro hU
      exact haC (by
        have hnorm := h.L_le_normalizer_C hxL
        rw [Subgroup.mem_normalizer_iff] at hnorm
        exact (hnorm a).mpr (ha'def ▸ h.U_le_C hU))
    have hconj := s65_SixFiveE_L0_inf_centralizer_conj (a := a) h hxL
    have hL0 := h.L0_inf_centralizer_of_notMem_U ha'V ha'U
    refine ⟨x, hxA, ?_, ?_⟩
    · rw [hconj, ← ha'def, hL0]
      intro hbot
      exact h.Z0_ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
    · rw [hconj, ← ha'def, hL0]
      exact conjSubgroup_mono inf_le_left x
  · have haVg : a ∈ conjSubgroup (conjSubgroup V g) x := hxA ▸ ha
    set a' := x * a * x⁻¹ with ha'def
    have ha'Vg : a' ∈ conjSubgroup V g := mem_conjSubgroup_iff.mp haVg
    have ha'B : a' ∉ BOf M V g := by
      intro hB
      exact haC (by
        have hnorm := h.L_le_normalizer_C hxL
        rw [Subgroup.mem_normalizer_iff] at hnorm
        exact (hnorm a).mpr (ha'def ▸ h.B_le_C hB))
    have hconj := s65_SixFiveE_L0_inf_centralizer_conj (a := a) h hxL
    have hL0 := h.L0_inf_centralizer_of_notMem_B ha'Vg ha'B
    refine ⟨g * x, ?_, ?_, ?_⟩
    · rw [hxA, conjSubgroup_conjSubgroup]
    · rw [hconj, ← ha'def, hL0]
      intro hbot
      exact h.Y_ne_bot (conjSubgroup_eq_bot_iff.mp hbot)
    · rw [hconj, ← ha'def, hL0, ← conjSubgroup_conjSubgroup]
      exact conjSubgroup_mono inf_le_left x

theorem eq_of_comm_mod_C (h : Hyp65 n M V₀ V g) {A A' : Subgroup G}
    (hA : A ∈ pairConjOf V g) (hA' : A' ∈ pairConjOf V g) {a a' : G} (ha : a ∈ A)
    (haC : a ∉ COf M V₀ V g) (ha' : a' ∈ A') (ha'C : a' ∉ COf M V₀ V g)
    (hcomm : ⁅a, a'⁆ ∈ COf M V₀ V g) : A = A' := by
  obtain ⟨y', hA'eq, hWne, hWle⟩ := h.exists_centralizer_L0 hA' ha' ha'C
  obtain ⟨y, hAeq, -, hW'le⟩ := h.exists_centralizer_L0 hA ha haC
  have haL : a ∈ LOf V g := le_LOf_of_mem_pairConjOf hA ha
  have ha2 : a * a = 1 := (h.isElemAbelian_of_mem_pairConjOf hA).mul_self_eq_one ha
  rw [COf] at hcomm
  have hcCen : ⁅a, a'⁆ ∈ centralizer (L0Of M V₀ g : Set G) :=
    (Subgroup.mem_inf.mp hcomm).2
  have hnormL0 := h.L_le_normalizer_L0 haL
  rw [Subgroup.mem_normalizer_iff] at hnormL0
  have hforward : ∀ w ∈ L0Of M V₀ g ⊓ centralizer ({a'} : Set G),
      a * w * a⁻¹ ∈ L0Of M V₀ g ⊓ centralizer ({a'} : Set G) := by
    intro w hw
    obtain ⟨hwL0, hwC⟩ := Subgroup.mem_inf.mp hw
    have hv : a * w * a⁻¹ ∈ L0Of M V₀ g := (hnormL0 w).mp hwL0
    have hw' : a' * w = w * a' :=
      (Subgroup.mem_centralizer_iff.mp hwC) a' (Set.mem_singleton a')
    have hcw : (a * w * a⁻¹) * ⁅a, a'⁆ = ⁅a, a'⁆ * (a * w * a⁻¹) :=
      (Subgroup.mem_centralizer_iff.mp hcCen) (a * w * a⁻¹) hv
    refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h1 : a' * a * a'⁻¹ = ⁅a, a'⁆⁻¹ * a := by
      rw [commutatorElement_def]; group
    have h2 : a' * w * a'⁻¹ = w := by rw [hw']; group
    have hconj : a' * (a * w * a⁻¹) * a'⁻¹ = a * w * a⁻¹ := by
      calc a' * (a * w * a⁻¹) * a'⁻¹
          = (a' * a * a'⁻¹) * (a' * w * a'⁻¹) * (a' * a * a'⁻¹)⁻¹ := by group
        _ = (⁅a, a'⁆⁻¹ * a) * w * (⁅a, a'⁆⁻¹ * a)⁻¹ := by rw [h1, h2]
        _ = a * w * a⁻¹ := by
              calc (⁅a, a'⁆⁻¹ * a) * w * (⁅a, a'⁆⁻¹ * a)⁻¹
                  = ⁅a, a'⁆⁻¹ * ((a * w * a⁻¹) * ⁅a, a'⁆) := by group
                _ = ⁅a, a'⁆⁻¹ * (⁅a, a'⁆ * (a * w * a⁻¹)) := by rw [hcw]
                _ = a * w * a⁻¹ := by group
    have hX : a' * (a * w * a⁻¹) = (a * w * a⁻¹) * a' := by
      have hc := congrArg (fun z => z * a') hconj
      simpa [mul_assoc] using hc
    exact hX
  have haN : a ∈ Subgroup.normalizer
      (((L0Of M V₀ g ⊓ centralizer ({a'} : Set G)) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    exact ⟨hforward w, fun hw => by
      have h2 := hforward (a * w * a⁻¹) hw
      have hww : a * (a * w * a⁻¹) * a⁻¹ = w := by
        have hh : a * (a * w * a⁻¹) * a⁻¹ = (a * a) * w * (a * a)⁻¹ := by group
        rw [hh, ha2]; group
      rwa [hww] at h2⟩
  have hW2 : IsPGroup 2 ↥(L0Of M V₀ g ⊓ centralizer ({a'} : Set G)) :=
    IsElemAbelian.isPGroup ((h.L0_isElemAbelian).mono inf_le_left)
  have hw2 : ∃ k : ℕ, a ^ 2 ^ k = 1 := ⟨1, by rw [pow_one, pow_two]; exact ha2⟩
  obtain ⟨u, huW, hu1, hucomm⟩ :=
    CFSG.RankThree.GF2n.Tim78.exists_ne_one_commute' hW2 hWne hw2 haN
  have huL0 : u ∈ L0Of M V₀ g := (Subgroup.mem_inf.mp huW).1
  have huCa : u ∈ centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact hucomm
  have huW' : u ∈ L0Of M V₀ g ⊓ centralizer ({a} : Set G) :=
    Subgroup.mem_inf.mpr ⟨huL0, huCa⟩
  have huVy : u ∈ conjSubgroup V₀ y := hW'le huW'
  have huVy' : u ∈ conjSubgroup V₀ y' := hWle huW
  have hne : conjSubgroup V₀ y ⊓ conjSubgroup V₀ y' ≠ ⊥ := by
    intro hbot
    have hmem : u ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact ⟨huVy, huVy'⟩
    exact hu1 (Subgroup.mem_bot.mp hmem)
  have he : conjSubgroup V₀ y = conjSubgroup V₀ y' := h.conjV₀_eq_of_inf_ne_bot hne
  have heV : conjSubgroup V y = conjSubgroup V y' := h.conjV_eq_of_conjV₀_eq he
  rw [hAeq, hA'eq, heV]

end Hyp65

end CFSG.LocalAnalysis.WeakClosure81
