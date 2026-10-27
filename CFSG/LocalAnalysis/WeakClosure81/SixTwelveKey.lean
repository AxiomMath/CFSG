module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveKeyA
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveInv

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace KLPair

variable {n : ℕ} {M V A C : Subgroup G} {g : G}

private lemma k612_ah_mul_self {a h' : G} (hA : IsElemAbelian 2 A) (ha : a ∈ A) :
    (h'⁻¹ * a * h') * (h'⁻¹ * a * h') = 1 := by
  have haa : a * a = 1 := by
    have h2 := hA.2 a ha
    rwa [pow_two] at h2
  calc (h'⁻¹ * a * h') * (h'⁻¹ * a * h') = h'⁻¹ * (a * a) * h' := by group
    _ = 1 := by rw [haa]; group

private lemma k612_ah_mem_conj {a h' : G} (ha : a ∈ A) :
    h'⁻¹ * a * h' ∈ conjSubgroup A h' :=
  CFSG.Quasithin.mem_conjSubgroup_iff.2 (by
    rw [show h' * (h'⁻¹ * a * h') * h'⁻¹ = a by group]
    exact ha)

private lemma k612_ah_notMem_conj {a h' : G} (haC : a ∉ C) :
    h'⁻¹ * a * h' ∉ conjSubgroup C h' := by
  intro hc
  apply haC
  have h1 := CFSG.Quasithin.mem_conjSubgroup_iff.1 hc
  rwa [show h' * (h'⁻¹ * a * h') * h'⁻¹ = a by group] at h1

private lemma k612_mem_normalizer_NOf_of_mem_L (h : Hyp612Sym n M V g) {l : G}
    (hl : l ∈ LOf V g) : l ∈ normalizer ((NOf M V g : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  constructor
  · intro hm
    have hc : m * l = l * m := h.mul_comm_of_mem_NOf hm hl
    have hlm : l * m * l⁻¹ = m := by rw [← hc]; group
    rwa [hlm]
  · intro hm
    have hc : (l * m * l⁻¹) * l = l * (l * m * l⁻¹) := h.mul_comm_of_mem_NOf hm hl
    have hm' : m = l * m * l⁻¹ := by
      calc m = l⁻¹ * (l * m * l⁻¹) * l := by group
        _ = l⁻¹ * ((l * m * l⁻¹) * l) := by group
        _ = l⁻¹ * (l * (l * m * l⁻¹)) := by rw [hc]
        _ = l * m * l⁻¹ := by group
    rw [hm']
    exact hm

private lemma k612_conjSubgroup_le_KOf (h : Hyp612Sym n M V g) {D : Subgroup G} {h' : G}
    (hDK : D ≤ KOf M V g) (hh' : h' ∈ LOf V g) : conjSubgroup D h' ≤ KOf M V g := by
  have hK : conjSubgroup (KOf M V g) h' = KOf M V g :=
    conjSubgroup_eq_iff_mem_normalizer.2 (h.LOf_le_normalizer_KOf hh')
  rw [← hK]
  exact conjSubgroup_mono hDK h'

theorem exists_mem_sdiff_UOf (h : Hyp612Sym n M V g) (P : KLPair M V g A C) {a h' : G}
    (ha : a ∈ A) (hh' : h' ∈ LOf V g) (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) :
    ∃ u ∈ UOf M V g, u ∉ NOf M V g ∧ ⁅u, h'⁻¹ * a * h'⁆ ∈ NOf M V g := by
  have hUV : UOf M V g ≤ V := inf_le_left
  have hNU : NOf M V g ≤ UOf M V g := inf_le_left
  have hahL : h'⁻¹ * a * h' ∈ LOf V g :=
    (LOf V g).mul_mem ((LOf V g).mul_mem ((LOf V g).inv_mem hh') (P.le_L ha)) hh'
  exact exists_mem_sdiff_commutator_mem (h.elemAbelian.mono hUV) hNU (Ne.symm h.UOf_ne_NOf) hn
    (k612_mem_normalizer_NOf_of_mem_L h hahL) (k612_ah_mul_self P.elemAbelian ha)

theorem lt_inf_conj (h : Hyp612Sym n M V g) (P : KLPair M V g A C) {a h' : G} (ha : a ∈ A)
    (haC : a ∉ C) (hh' : h' ∈ LOf V g) (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) :
    V ⊓ conjSubgroup V g < V ⊓ conjSubgroup A h' := by
  have hUV : UOf M V g ≤ V := inf_le_left
  have hNU : NOf M V g ≤ UOf M V g := inf_le_left
  obtain ⟨u, huU, huN, hcuN⟩ := exists_mem_sdiff_UOf h P ha hh' hn
  have huV : u ∈ V := hUV huU
  have huK : u ∈ KOf M V g := by rw [KOf]; exact Subgroup.mem_sup_left huU
  have hChK : conjSubgroup C h' ≤ KOf M V g := k612_conjSubgroup_le_KOf h P.le_K hh'
  have hChA : conjSubgroup C h' ≤ conjSubgroup A h' := conjSubgroup_mono P.le h'
  have huCh : u ∈ conjSubgroup C h' := (P.mem_conjSubgroup_iff h ha haC hh' huK).1 hcuN
  have huAh : u ∈ conjSubgroup A h' := hChA huCh
  have hNle : V ⊓ conjSubgroup V g ≤ V ⊓ conjSubgroup A h' := by
    rw [← h.NOf_eq_inf]
    intro x hx
    refine Subgroup.mem_inf.2 ⟨hUV (hNU hx), ?_⟩
    have hxN : x ∈ conjSubgroup (NOf M V g) h' := by
      rw [conjSubgroup_eq_iff_mem_normalizer.2 (k612_mem_normalizer_NOf_of_mem_L h hh')]
      exact hx
    exact hChA (conjSubgroup_mono P.NOf_le h' hxN)
  refine lt_of_le_of_ne hNle ?_
  intro heq
  apply huN
  rw [h.NOf_eq_inf]
  exact heq.symm ▸ Subgroup.mem_inf.2 ⟨huV, huAh⟩

theorem mQuot_inf_M_lt (h : Hyp612Sym n M V g) (P : KLPair M V g A C) {a h' : G} (ha : a ∈ A)
    (haC : a ∉ C) (hh' : h' ∈ LOf V g) (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) :
    E3.mQuot (conjSubgroup A h') M < n := by
  have hAh : IsElemAbelian 2 (conjSubgroup A h') := E3.isElemAbelian_conjSubgroup P.elemAbelian h'
  have hCA : conjSubgroup C h' ≤ conjSubgroup A h' := conjSubgroup_mono P.le h'
  have hCM : conjSubgroup C h' ≤ M := (k612_conjSubgroup_le_KOf h P.le_K hh').trans h.KOf_le_M
  have haM : h'⁻¹ * a * h' ∈ M := h.normalizer_U_le hn
  have hstep := mQuot_add_one_le_of_mem (A := conjSubgroup A h') (C := conjSubgroup C h')
    hAh hCA hCM (k612_ah_mem_conj ha) haM (k612_ah_notMem_conj haC)
  have hchain : E3.mQuot (conjSubgroup A h') (conjSubgroup C h') =
      E3.mQuot V (UOf M V g) := by
    rw [E3.mQuot_conjSubgroup, P.mQuot_eq]
  rw [hchain] at hstep
  have hle := h.mQuot_U_le
  omega

theorem exists_subgroup_le_normalizer (h : Hyp612Sym n M V g) (P : KLPair M V g A C) {a h' : G}
    (ha : a ∈ A) (haC : a ∉ C) (hh' : h' ∈ LOf V g)
    (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) :
    ∃ P₀ : Subgroup G, UOf M V g ≤ P₀ ∧ P₀ ≤ V ∧
      P₀ ≤ normalizer ((conjSubgroup A h' : Subgroup G) : Set G) ∧
      2 * E3.mQuot V P₀ ≤ E3.mQuot V (UOf M V g) := by
  have hUV : UOf M V g ≤ V := inf_le_left
  have hahM : h'⁻¹ * a * h' ∈ M := h.normalizer_U_le hn
  have hnormV : h'⁻¹ * a * h' ∈ normalizer (V : Set G) := by
    rw [h.normalizer_eq]
    exact hahM
  obtain ⟨P₀, hP₀, hmP₀⟩ := exists_subgroup_two_mul_mQuot_le (V := V) (W := UOf M V g)
    h.elemAbelian hUV hnormV hn (k612_ah_mul_self P.elemAbelian ha)
  have hUP₀ : UOf M V g ≤ P₀ := by
    intro u hu
    rw [hP₀]
    refine ⟨hUV hu, ?_⟩
    have hcU : h'⁻¹ * a * h' * u⁻¹ * (h'⁻¹ * a * h')⁻¹ ∈ UOf M V g :=
      (Subgroup.mem_normalizer_iff.1 hn u⁻¹).1 ((UOf M V g).inv_mem hu)
    rw [commutatorElement_def,
      show u * (h'⁻¹ * a * h') * u⁻¹ * (h'⁻¹ * a * h')⁻¹ =
        u * (h'⁻¹ * a * h' * u⁻¹ * (h'⁻¹ * a * h')⁻¹) by group]
    exact (UOf M V g).mul_mem hu hcU
  have hP₀V : P₀ ≤ V := fun v hv => ((hP₀ v).1 hv).1
  have hChK : conjSubgroup C h' ≤ KOf M V g := k612_conjSubgroup_le_KOf h P.le_K hh'
  have hChA : conjSubgroup C h' ≤ conjSubgroup A h' := conjSubgroup_mono P.le h'
  have hforward : ∀ v ∈ P₀, ∀ c ∈ conjSubgroup C h', v * c * v⁻¹ ∈ conjSubgroup C h' := by
    intro v hv c hc
    have hvV : v ∈ V := ((hP₀ v).1 hv).1
    have hvcU : ⁅v, h'⁻¹ * a * h'⁆ ∈ UOf M V g := ((hP₀ v).1 hv).2
    have hvL : v ∈ LOf V g := by rw [LOf]; exact Subgroup.mem_sup_left hvV
    have hvcD : ⁅v, h'⁻¹ * a * h'⁆ ∈ CKOf M V g :=
      h.KOf_le_CKOf (by rw [KOf]; exact Subgroup.mem_sup_left hvcU)
    have hcK : c ∈ KOf M V g := hChK hc
    have hcN : ⁅c, h'⁻¹ * a * h'⁆ ∈ NOf M V g :=
      (P.mem_conjSubgroup_iff h ha haC hh' hcK).2 hc
    have hcommN : ⁅v * c * v⁻¹, h'⁻¹ * a * h'⁆ ∈ NOf M V g :=
      h.commutator_conj_mem_NOf hvL hvcD hcK hcN
    have hvcK : v * c * v⁻¹ ∈ KOf M V g :=
      (Subgroup.mem_normalizer_iff.1 (h.LOf_le_normalizer_KOf hvL) c).1 hcK
    exact (P.mem_conjSubgroup_iff h ha haC hh' hvcK).1 hcommN
  have hP₀NormCh : P₀ ≤ normalizer ((conjSubgroup C h' : Subgroup G) : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · intro hc
      exact hforward v hv c hc
    · intro hc
      have h1 := hforward v⁻¹ (P₀.inv_mem hv) (v * c * v⁻¹) hc
      rwa [show v⁻¹ * (v * c * v⁻¹) * (v⁻¹)⁻¹ = c by group] at h1
  obtain ⟨x, hx⟩ := P.exists_conj
  have hAh_eq : conjSubgroup A h' = conjSubgroup V (x * h') := by
    rw [hx, conjSubgroup_conjSubgroup]
  have hYX : conjSubgroup C h' ≤ conjSubgroup V (x * h') := by
    rw [← hAh_eq]
    exact hChA
  have hm : E3.mQuot (conjSubgroup V (x * h')) (conjSubgroup C h') ≤ n := by
    rw [← hAh_eq, E3.mQuot_conjSubgroup, P.mQuot_eq]
    exact h.mQuot_U_le
  have hnorm_le : normalizer ((conjSubgroup C h' : Subgroup G) : Set G) ≤
      normalizer ((conjSubgroup A h' : Subgroup G) : Set G) := by
    rw [hAh_eq]
    exact h.normalizer_le_of_mQuot_le hYX hm
  exact ⟨P₀, hUP₀, hP₀V, hP₀NormCh.trans hnorm_le, hmP₀⟩

theorem mQuot_normalizer_lt (h : Hyp612Sym n M V g) (P : KLPair M V g A C) {a h' : G}
    (ha : a ∈ A) (haC : a ∉ C) (hh' : h' ∈ LOf V g)
    (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) :
    E3.mQuot V (normalizer ((conjSubgroup A h' : Subgroup G) : Set G)) < n := by
  obtain ⟨P₀, -, -, hP₀Norm, hmP₀⟩ := exists_subgroup_le_normalizer h P ha haC hh' hn
  have hmono : E3.mQuot V (normalizer ((conjSubgroup A h' : Subgroup G) : Set G)) ≤
      E3.mQuot V P₀ := E3.mQuot_mono hP₀Norm
  have hle := h.mQuot_U_le
  have h1 := h.one_le
  omega

theorem commutator_mem_NOf_of_h3 (h : Hyp612H3 n M V g) (P : KLPair M V g A C) {a h' : G}
    (ha : a ∈ A) (haC : a ∉ C) (hh' : h' ∈ LOf V g)
    (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) {u : G} (hu : u ∈ UOf M V g) :
    ⁅u, h'⁻¹ * a * h'⁆ ∈ NOf M V g := by
  let hS := h.toHyp612Sym
  obtain ⟨P₀, hUP₀, -, hP₀Norm, -⟩ := exists_subgroup_le_normalizer hS P ha haC hh' hn
  obtain ⟨x, hx⟩ := P.exists_conj
  have hAh_eq : conjSubgroup A h' = conjSubgroup V (x * h') := by
    rw [hx, conjSubgroup_conjSubgroup]
  have hlt := lt_inf_conj hS P ha haC hh' hn
  have hmM := mQuot_inf_M_lt hS P ha haC hh' hn
  have hmN := mQuot_normalizer_lt hS P ha haC hh' hn
  have hle := h.h3 (conjSubgroup A h') ⟨x * h', hAh_eq⟩ hlt (max_lt hmM hmN)
  have haAh : h'⁻¹ * a * h' ∈ conjSubgroup A h' := k612_ah_mem_conj ha
  have hahM : h'⁻¹ * a * h' ∈ M := hS.normalizer_U_le hn
  have huV : u ∈ V := (inf_le_left : UOf M V g ≤ V) hu
  have huNorm : u ∈ normalizer ((conjSubgroup A h' : Subgroup G) : Set G) := hP₀Norm (hUP₀ hu)
  have hc := Subgroup.commutator_mem_commutator (Subgroup.mem_inf.2 ⟨haAh, hahM⟩)
    (Subgroup.mem_inf.2 ⟨huV, huNorm⟩)
  have hcN : ⁅h'⁻¹ * a * h', u⁆ ∈ NOf M V g := by
    have h1 := hle hc
    rwa [← hS.NOf_eq_inf] at h1
  rw [(commutatorElement_inv (h'⁻¹ * a * h') u).symm]
  exact (NOf M V g).inv_mem hcN

theorem conjSubgroup_eq_UOf (h : Hyp612H3 n M V g) (P : KLPair M V g A C) {a h' : G}
    (ha : a ∈ A) (haC : a ∉ C) (hh' : h' ∈ LOf V g)
    (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) :
    conjSubgroup C h' = UOf M V g := by
  let hS := h.toHyp612Sym
  have hUCh : UOf M V g ≤ conjSubgroup C h' := by
    intro u hu
    have huK : u ∈ KOf M V g := by rw [KOf]; exact Subgroup.mem_sup_left hu
    exact (P.mem_conjSubgroup_iff hS ha haC hh' huK).1
      (commutator_mem_NOf_of_h3 h P ha haC hh' hn hu)
  have hcard : Nat.card (conjSubgroup C h') ≤ Nat.card (UOf M V g) := by
    rw [E3.card_conjSubgroup, P.card_eq]
  exact (Subgroup.eq_of_le_of_card_ge hUCh hcard).symm

end KLPair

namespace Hyp612H3

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem conjSubgroup_UOf_eq (h : Hyp612H3 n M V g) {a h' : G} (ha : a ∈ V)
    (haU : a ∉ UOf M V g) (hh' : h' ∈ LOf V g)
    (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) :
    conjSubgroup (UOf M V g) h' = UOf M V g :=
  (KLPair.ofV h.toHyp612Sym).conjSubgroup_eq_UOf h ha haU hh' hn

theorem conjSubgroup_BOf_eq_UOf (h : Hyp612H3 n M V g) {a h' : G} (ha : a ∈ conjSubgroup V g)
    (haB : a ∉ BOf M V g) (hh' : h' ∈ LOf V g)
    (hn : h'⁻¹ * a * h' ∈ normalizer (UOf M V g : Set G)) :
    conjSubgroup (BOf M V g) h' = UOf M V g :=
  (KLPair.ofConjV h.toHyp612Sym).conjSubgroup_eq_UOf h ha haB hh' hn

end Hyp612H3

end CFSG.LocalAnalysis.WeakClosure81
