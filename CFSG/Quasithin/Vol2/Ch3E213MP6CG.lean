module

public import CFSG.Quasithin.Vol2.Ch3E213MP6CF
public import CFSG.Quasithin.Vol2.Ch3E213MP6CD

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat uElt antiUnipotentCenter)

variable {k : Type} [Field k]

theorem isUpper_one : IsUpper (1 : antiSp k) := fun i j hij => by
  change (1 : Matrix (Fin 4) (Fin 4) k) i j = 0
  exact Matrix.one_apply_ne (ne_of_gt hij)

theorem map_conj_one (X : Subgroup (antiSp k)) :
    X.map (MulAut.conj (1 : antiSp k)).toMonoidHom = X := by
  rw [map_one]
  exact Subgroup.map_id X

variable [Finite k] [CharP k 2]

theorem exists_subfieldSp_member (hIrr : IrrStatement) (hG41 : FactSp4TransvW) {n : ℕ}
    (hk : Nat.card k = 2 ^ n) {W : Subgroup (antiSp k)} (hWZ : W ≤ antiUnipotentCenter k)
    (hsp : SpansCenter W) {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) (hl : uElt 0 0 a 0 ∈ W)
    (hs : uElt 0 b 0 0 ∈ W) :
    ∃ (F₀ : Subfield k) (c g : antiSp k), IsUpper c ∧
      g ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ∧
      W ⊔ W.map (MulAut.conj g).toMonoidHom = (subfieldSp F₀).map (MulAut.conj c).toMonoidHom := by
  suffices key : ∀ N : ℕ, ∀ (F₀ : Subfield k) (c : antiSp k), IsUpper c →
      W ≤ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom →
      Nat.card ((subfieldSp F₀).map (MulAut.conj c).toMonoidHom) ≤ N →
      ∃ (F₀ : Subfield k) (c g : antiSp k), IsUpper c ∧
        g ∈ (subfieldSp F₀).map (MulAut.conj c).toMonoidHom ∧
        W ⊔ W.map (MulAut.conj g).toMonoidHom =
          (subfieldSp F₀).map (MulAut.conj c).toMonoidHom by
    refine key _ ⊤ 1 isUpper_one ?_ le_rfl
    rw [map_conj_one, subfieldSp_top]
    exact le_top
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro F₀ c hc hW hcard
    set Y := (subfieldSp F₀).map (MulAut.conj c).toMonoidHom with hY
    set g := c * wLong * c⁻¹ with hg
    have hgY : g ∈ Y := ⟨wLong, wLong_mem_subfieldSp F₀, rfl⟩
    set Y' := W ⊔ W.map (MulAut.conj g).toMonoidHom with hY'
    have hY'Y : Y' ≤ Y := by
      refine sup_le hW ?_
      rintro _ ⟨w, hw, rfl⟩
      exact Y.mul_mem (Y.mul_mem hgY (hW hw)) (Y.inv_mem hgY)
    have hirr := hIrr k W g hWZ hsp (isOppStd_conj_of_isUpper hc)
    have hlY' : uElt 0 0 a 0 ∈ Y' := le_sup_left (a := W) hl
    have hsY' : uElt 0 b 0 0 ∈ Y' := le_sup_left (a := W) hs
    have htr : (transvSet Y').Nonempty := ⟨_, hlY', isTransvection_zl ha⟩
    rcases hG41 k n hk Y' hirr htr with h1 | h2 | h3
    · obtain ⟨F₀', c', hY'eq⟩ := h1
      obtain ⟨c'', hc'', hc''eq⟩ := exists_isUpper_conj ha hb (hY'eq ▸ hlY') (hY'eq ▸ hsY')
      by_cases hEq : Y' = Y
      · exact ⟨F₀, c, g, hc, hgY, hEq⟩
      · have hlt : Nat.card Y' < Nat.card Y :=
          Subgroup.card_lt_of_lt (lt_of_le_of_ne hY'Y hEq)
        refine ih (Nat.card Y') (lt_of_lt_of_le hlt hcard) F₀' c'' hc'' ?_ ?_
        · rw [hc''eq, ← hY'eq]
          exact le_sup_left
        · rw [hc''eq, ← hY'eq]
    · exact absurd h2 (not_g41Orth ha hb hlY' hsY')
    · exact absurd h3 (not_g41Dec ha hb hlY' hsY')

end CFSG.Quasithin.Ch3E213M
