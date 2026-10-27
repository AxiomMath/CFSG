module

public import CFSG.LocalAnalysis.StandardType.GGHalfWeylBasic
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylAutomizer
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylSingleBlock
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylOrbitFacts
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylRank
public import CFSG.LocalAnalysis.StandardType.GGSpJoinOrbitBound

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfTorusFrame

theorem support_of_orbit {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} {n : ℕ}
    {ψ : SpecialLinearGroup (Fin (n + 1)) F2 →* G} (hψ : GGHalfTorusFrame Bs X (halfTorus n) ψ)
    (hn : 5 ≤ n) {W : Subgroup (MulAut ↥Bs)} (hXW : ggAutomizer X Bs ≤ W) {b z : G} (hb : b ∈ Bs)
    (hz : z ∈ Bs) (hzX : z ∈ Subgroup.centralizer (X : Set G)) (hbz : b ≠ z)
    (hW : Set.ncard (GGHalfOrbit W b hb) ≤ 2 * ((n + 1) / 2) + 2) (hzW : z ∈ GGHalfOrbit W b hb) :
    ∃ P : Fin n, P.val % 2 = 0 ∧ GGHalfSupportedAt X ψ b P := by
  obtain ⟨t, ht, hbt⟩ := hψ.act b hb
  rcases hψ.single_block_of_orbit hn hb ht hbt with ⟨P, hP, hPt⟩ | hbig
  · exact ⟨P, hP, t, hPt, hbt⟩
  · exfalso
    have hsub : GGHalfOrbit (ggAutomizer X Bs) b hb ⊆ GGHalfOrbit W b hb :=
      fun w ⟨φ, hφ, hw⟩ => ⟨φ, hXW hφ, hw⟩
    have heq : GGHalfOrbit (ggAutomizer X Bs) b hb = GGHalfOrbit W b hb :=
      Set.eq_of_subset_of_ncard_le hsub (le_trans hW hbig) (Set.toFinite _)
    rw [← heq] at hzW
    obtain ⟨φ, hφ, hφb⟩ := hzW
    have hfix := SpJoin.ggAutomizer_fixes_of_mem_centralizer hz hzX φ hφ
    apply hbz
    have h2 : φ ⟨b, hb⟩ = φ ⟨z, hz⟩ := Subtype.ext (hφb.trans hfix.symm)
    exact congrArg Subtype.val (φ.injective h2)

end GGHalfTorusFrame

namespace GGHalfWeylCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  (h : GGHalfWeylCtx p B Bs x L D J m y K)

include h

theorem exists_support {ψL ψK : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}
    (hL : GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψL)
    (hK : GGHalfTorusFrame Bs K (halfTorus (m + 1 + 1)) ψK) :
    (∃ P : Fin (m + 1 + 1), P.val % 2 = 0 ∧ GGHalfSupportedAt L ψL y P) ∧
    (∃ P : Fin (m + 1 + 1), P.val % 2 = 0 ∧ GGHalfSupportedAt K ψK x P) := by
  obtain ⟨-, -, hxBs, hyBs, hx1, hy1, hLx, hKy, hxK, -⟩ := h.basic
  have hn5 : 5 ≤ m + 1 + 1 := h.five_le
  obtain rfl : p = 3 := h.p_eq
  have hBsEA : IsElemAbelian 3 Bs := h.cfg.2.1.2.1
  obtain ⟨-, -, -, -, -, -, r, hr⟩ := h.nbr
  have hrk : r = (m + 1 + 1 + 1) / 2 + 1 := h.weylRank_eq hL hK hr
  subst hrk
  have hxL : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl => (hLx l hl).symm
  have hyK : y ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => (hKy k hk).symm
  have hxy : x ≠ y := by
    intro hxy
    apply hxK
    intro k hk
    rw [hxy]
    exact hKy k hk
  obtain ⟨hWy, hWx, hxWy, hyWx⟩ := weyl_orbit_facts hBsEA (by omega) (h.card_bs hL) hxBs hyBs hx1
    hy1 hxL hyK (hL.card_automizer_ge (by omega)) (hK.card_automizer_ge (by omega)) hr
  exact ⟨hL.support_of_orbit hn5 le_sup_left hyBs hxBs hxL hxy.symm hWy hxWy,
    hK.support_of_orbit hn5 le_sup_right hxBs hyBs hyK hxy hWx hyWx⟩

end GGHalfWeylCtx

end CFSG.StandardType

end
