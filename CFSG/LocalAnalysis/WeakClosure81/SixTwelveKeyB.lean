module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveKey

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem conjSubgroup_le_LOf_of_mem {A V : Subgroup G} {g l : G}
    (hA : A ≤ LOf V g) (hl : l ∈ LOf V g) : conjSubgroup A l ≤ LOf V g := by
  intro y hy
  have h1 : l * y * l⁻¹ ∈ A := mem_conjSubgroup_iff.1 hy
  have h2 : y = l⁻¹ * (l * y * l⁻¹) * l := by group
  rw [h2]
  exact (LOf V g).mul_mem ((LOf V g).mul_mem ((LOf V g).inv_mem hl) (hA h1)) hl

namespace Hyp612Sym

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem conjSubgroup_V_eq_of_conjSubgroup_UOf_eq (h : Hyp612Sym n M V g) {h' : G}
    (hU : conjSubgroup (UOf M V g) h' = UOf M V g) : conjSubgroup V h' = V := by
  have h1 : h' ∈ normalizer ((UOf M V g : Subgroup G) : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.1 hU
  have h2 : h' ∈ normalizer (V : Set G) := by
    rw [h.normalizer_eq]
    exact h.normalizer_U_le h1
  exact conjSubgroup_eq_iff_mem_normalizer.2 h2

theorem conjSubgroup_conjV_eq_of_le_sup (h : Hyp612Sym n M V g) {l : G} (hl : l ∈ LOf V g)
    (hB : BOf M V g = conjSubgroup (UOf M V g) l)
    (hle : conjSubgroup V g ≤ conjSubgroup V l ⊔ KOf M V g) :
    conjSubgroup V g = conjSubgroup V l := by
  have hVL : V ≤ LOf V g := le_sup_left
  have hVlL := conjSubgroup_le_LOf_of_mem hVL hl
  have hUV : UOf M V g ≤ V := inf_le_left
  have hBVl : BOf M V g ≤ conjSubgroup V l := by
    rw [hB]; exact conjSubgroup_mono hUV l
  have hBVg : BOf M V g ≤ conjSubgroup V g := inf_le_left
  have hVlK : conjSubgroup V l ≤ normalizer ((KOf M V g : Subgroup G) : Set G) :=
    hVlL.trans h.LOf_le_normalizer_KOf
  have hVlab : IsElemAbelian 2 (conjSubgroup V l) := E3.isElemAbelian_conjSubgroup h.elemAbelian l
  have hVgab : IsElemAbelian 2 (conjSubgroup V g) := h.elemAbelian_conj
  have hsub : conjSubgroup V g ≤ conjSubgroup V l := by
    intro w hw
    have hw' : w ∈ conjSubgroup V l ⊔ KOf M V g := hle hw
    have hprod := Subgroup.coe_mul_of_left_le_normalizer_right (conjSubgroup V l) (KOf M V g)
      hVlK
    have hw'' : w ∈ ((conjSubgroup V l : Subgroup G) : Set G) * (KOf M V g : Set G) := by
      rw [← hprod]; exact hw'
    obtain ⟨v', hv', κ, hκ, rfl⟩ := hw''
    suffices hκB : κ ∈ conjSubgroup V l from (conjSubgroup V l).mul_mem hv' hκB
    have hκc : ∀ b ∈ BOf M V g, κ * b = b * κ := by
      intro b hb
      have h1 : v' * b = b * v' := hVlab.comm hv' (hBVl hb)
      have h2 : v' * κ * b = b * (v' * κ) := hVgab.comm hw (hBVg hb)
      calc κ * b = v'⁻¹ * (v' * κ * b) := by group
        _ = v'⁻¹ * (b * (v' * κ)) := by rw [h2]
        _ = v'⁻¹ * (b * v') * κ := by group
        _ = v'⁻¹ * (v' * b) * κ := by rw [h1]
        _ = b * κ := by group
    have hκK : κ ∈ ((BOf M V g : Subgroup G) : Set G) * (UOf M V g : Set G) := by
      rw [← h.coe_KOf_eq_BOf_mul_UOf]; exact hκ
    obtain ⟨b₀, hb₀, u, hu, rfl⟩ := hκK
    have huc : u ∈ centralizer ((BOf M V g : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hb₀b : b₀ * b = b * b₀ := hVgab.comm (hBVg hb₀) (hBVg hb)
      have h3 : b₀ * u * b = b * (b₀ * u) := hκc b hb
      calc b * u = b₀⁻¹ * (b₀ * b) * u := by group
        _ = b₀⁻¹ * (b * b₀) * u := by rw [hb₀b]
        _ = b₀⁻¹ * (b * (b₀ * u)) := by group
        _ = b₀⁻¹ * (b₀ * u * b) := by rw [h3]
        _ = u * b := by group
    have huVg : u ∈ conjSubgroup V g := h.centralizer_le (Subgroup.mem_inf.2 ⟨hUV hu, huc⟩)
    have huN : u ∈ NOf M V g := by
      rw [h.NOf_eq_inf]
      exact Subgroup.mem_inf.2 ⟨hUV hu, huVg⟩
    have hNB : NOf M V g ≤ BOf M V g := inf_le_right
    exact (conjSubgroup V l).mul_mem (hBVl hb₀) (hBVl (hNB huN))
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [E3.card_conjSubgroup, E3.card_conjSubgroup])

end Hyp612Sym

namespace Hyp612H3

variable {n : ℕ} {M V : Subgroup G} {g : G}

theorem conjSubgroup_eq_of_commutator_mem (h : Hyp612H3 n M V g) {l l' a a' : G}
    (hl : l ∈ LOf V g) (hl' : l' ∈ LOf V g) (ha : a ∈ conjSubgroup V l)
    (haK : a ∉ KOf M V g) (ha' : a' ∈ conjSubgroup V l') (ha'K : a' ∉ KOf M V g)
    (hc : ⁅a, a'⁆ ∈ CKOf M V g) : conjSubgroup V l = conjSubgroup V l' := by
  have hs := h.toHyp612Sym
  have hKL : ∀ x ∈ LOf V g, ∀ y, y ∈ KOf M V g ↔ x * y * x⁻¹ ∈ KOf M V g := fun x hx =>
    Subgroup.mem_normalizer_iff.1 (hs.LOf_le_normalizer_KOf hx)
  have hDL : ∀ x ∈ LOf V g, ∀ y, y ∈ CKOf M V g ↔ x * y * x⁻¹ ∈ CKOf M V g := fun x hx =>
    Subgroup.mem_normalizer_iff.1 (hs.LOf_le_normalizer_CKOf hx)
  have hUK : UOf M V g ≤ KOf M V g := le_sup_left
  have hVL : V ≤ LOf V g := le_sup_left
  have hVl'L := conjSubgroup_le_LOf_of_mem hVL hl'
  have ha₀V : l * a * l⁻¹ ∈ V := mem_conjSubgroup_iff.1 ha
  have ha₀U : l * a * l⁻¹ ∉ UOf M V g := fun hU => haK ((hKL l hl a).2 (hUK hU))
  have ha₁V : l' * a' * l'⁻¹ ∈ V := mem_conjSubgroup_iff.1 ha'
  have ha₁U : l' * a' * l'⁻¹ ∉ UOf M V g := fun hU => ha'K ((hKL l' hl' a').2 (hUK hU))
  have ha'L : a' ∈ LOf V g := hVl'L ha'
  have hxL : l * a' * l⁻¹ ∈ LOf V g :=
    (LOf V g).mul_mem ((LOf V g).mul_mem hl ha'L) ((LOf V g).inv_mem hl)
  have hc₀ : ⁅l * a * l⁻¹, l * a' * l⁻¹⁆ ∈ CKOf M V g := by
    have e : ⁅l * a * l⁻¹, l * a' * l⁻¹⁆ = l * ⁅a, a'⁆ * l⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (hDL l hl _).1 hc
  have hxU := hs.normalizer_UOf_of_commutator_mem_CKOf ha₀V ha₀U hxL hc₀
  have hh₀ : l' * l⁻¹ ∈ LOf V g := (LOf V g).mul_mem hl' ((LOf V g).inv_mem hl)
  have hxe : (l' * l⁻¹)⁻¹ * (l' * a' * l'⁻¹) * (l' * l⁻¹) = l * a' * l⁻¹ := by group
  have hU := h.conjSubgroup_UOf_eq ha₁V ha₁U hh₀ (by rw [hxe]; exact hxU)
  have hV := hs.conjSubgroup_V_eq_of_conjSubgroup_UOf_eq hU
  calc conjSubgroup V l = conjSubgroup (conjSubgroup V (l' * l⁻¹)) l := by rw [hV]
    _ = conjSubgroup V (l' * l⁻¹ * l) := conjSubgroup_conjSubgroup _ _ _
    _ = conjSubgroup V l' := by rw [inv_mul_cancel_right]

theorem conjSubgroup_conjV_eq_of_commutator_mem (h : Hyp612H3 n M V g)
    (hd : H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹) {l l' a a' : G}
    (hl : l ∈ LOf V g) (hl' : l' ∈ LOf V g) (ha : a ∈ conjSubgroup (conjSubgroup V g) l)
    (haK : a ∉ KOf M V g) (ha' : a' ∈ conjSubgroup (conjSubgroup V g) l')
    (ha'K : a' ∉ KOf M V g) (hc : ⁅a, a'⁆ ∈ CKOf M V g) :
    conjSubgroup (conjSubgroup V g) l = conjSubgroup (conjSubgroup V g) l' :=
  (h.swapH3 hd).conjSubgroup_eq_of_commutator_mem (l := l) (l' := l') (a := a) (a' := a')
    (by rwa [LOf_swap]) (by rwa [LOf_swap]) ha (by rwa [KOf_swap]) ha' (by rwa [KOf_swap])
    (by rwa [CKOf_swap])

theorem false_of_mem_normalizer_sup (h : Hyp612H3 n M V g) {b : G}
    (hb : b ∈ conjSubgroup V g) (hbK : b ∉ KOf M V g)
    (hbV : ∀ v ∈ V, b * v * b⁻¹ ∈ V ⊔ KOf M V g) : False := by
  have hbL : b ∈ LOf V g := Subgroup.mem_sup_right hb
  have hbU : b ∈ normalizer ((UOf M V g : Subgroup G) : Set G) :=
    h.toHyp612Sym.normalizer_UOf_of_conj_mem_sup hbL hbV
  have hbB : b ∉ BOf M V g := fun hB => hbK (Subgroup.mem_sup_right hB)
  have hKL := h.conjSubgroup_BOf_eq_UOf hb hbB (one_mem _) (by simpa using hbU)
  rw [conjSubgroup_one] at hKL
  exact h.toHyp612Sym.UOf_ne_BOf hKL.symm

theorem BOf_eq_conjSubgroup_UOf (h : Hyp612H3 n M V g) {b l : G} (hb : b ∈ conjSubgroup V g)
    (hbK : b ∉ KOf M V g) (hl : l ∈ LOf V g)
    (hbl : ∀ w ∈ conjSubgroup V l, b * w * b⁻¹ ∈ conjSubgroup V l ⊔ KOf M V g) :
    BOf M V g = conjSubgroup (UOf M V g) l := by
  have hbL : b ∈ LOf V g := Subgroup.mem_sup_right hb
  have hb'L : l * b * l⁻¹ ∈ LOf V g := (LOf V g).mul_mem ((LOf V g).mul_mem hl hbL)
    ((LOf V g).inv_mem hl)
  have hKl : conjSubgroup (KOf M V g) l = KOf M V g :=
    conjSubgroup_eq_iff_mem_normalizer.2 (h.toHyp612Sym.LOf_le_normalizer_KOf hl)
  have hsup : conjSubgroup V l ⊔ KOf M V g ≤ conjSubgroup (V ⊔ KOf M V g) l := by
    refine sup_le (conjSubgroup_mono le_sup_left l) ?_
    have hK1 : KOf M V g ≤ V ⊔ KOf M V g := le_sup_right
    have h5 := conjSubgroup_mono hK1 l
    rwa [hKl] at h5
  have hb'V : ∀ v ∈ V, (l * b * l⁻¹) * v * (l * b * l⁻¹)⁻¹ ∈ V ⊔ KOf M V g := by
    intro v hv
    have hw : l⁻¹ * v * l ∈ conjSubgroup V l := by
      rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hv
    have h1 := mem_conjSubgroup_iff.1 (hsup (hbl _ hw))
    have h2 : l * (b * (l⁻¹ * v * l) * b⁻¹) * l⁻¹ = (l * b * l⁻¹) * v * (l * b * l⁻¹)⁻¹ := by
      group
    rwa [h2] at h1
  have hbU : l * b * l⁻¹ ∈ normalizer ((UOf M V g : Subgroup G) : Set G) :=
    h.toHyp612Sym.normalizer_UOf_of_conj_mem_sup hb'L hb'V
  have hbB : b ∉ BOf M V g := fun hB => hbK (Subgroup.mem_sup_right hB)
  have hres := h.conjSubgroup_BOf_eq_UOf hb hbB ((LOf V g).inv_mem hl)
    (by simpa using hbU)
  have h3 := congrArg (fun A => conjSubgroup A l) hres
  simpa [conjSubgroup_conjSubgroup, conjSubgroup_one] using h3

theorem conjSubgroup_le_EOf_of_mem_normalizer_sup (h : Hyp612H3 n M V g) {b l : G}
    (hb : b ∈ conjSubgroup V g) (hbK : b ∉ KOf M V g) (hl : l ∈ LOf V g)
    (hbl : ∀ w ∈ conjSubgroup V l, b * w * b⁻¹ ∈ conjSubgroup V l ⊔ KOf M V g) :
    conjSubgroup V l ≤ EOf M V g :=
  h.toHyp612Sym.conjV_le_EOf_of_conj_UOf_eq hl (h.BOf_eq_conjSubgroup_UOf hb hbK hl hbl)

end Hyp612H3

end CFSG.LocalAnalysis.WeakClosure81
