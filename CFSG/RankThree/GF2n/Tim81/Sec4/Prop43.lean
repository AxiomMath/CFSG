module

public import CFSG.RankThree.GF2n.Tim81.Sec4.W0Orth
public import CFSG.RankThree.GF2n.Tim81.Sec4.VLeW0
public import CFSG.RankThree.GF2n.Tim81.Sec4.OrthW

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

namespace RootHyp

theorem conj_le_of_le_of_normalizer (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) {W₀ : Subgroup G}
    (hN : H ≤ Subgroup.normalizer (W₀ : Set G)) (hVW₀ : V ≤ W₀) :
    conjSubgroup h₀ V ≤ W₀ := by
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH hH
  rw [hVy]
  calc conjSubgroup y V ≤ conjSubgroup y W₀ := conjSubgroup_mono hVW₀
    _ = W₀ := conjSubgroup_eq_self_iff.mpr (hN hyH)

theorem exists_orth_xOf_of_kOf_abelian
    {hW : Assembly.IsElemAbelian 2 (Tim79a.xOf V H)}
    [Module (ZMod 2) (Additive (IntMod (Tim79a.xOf V H) hW))]
    (h : RootHyp M V) (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) (hnM : ¬ H ≤ M)
    (hK : KFactorization M V H h₀)
    (hab : ∀ x ∈ kOf V H, ∀ y ∈ kOf V H, x * y = y * x) (hL : IsL2OrSz V H) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2) (l : ℕ),
      1 ≤ l ∧ ∃ hl : Fintype.card F = 2 ^ (2 * l), ∃ ψ : HBar V H ≃* SL(2, F),
        Sec2.IsOrthModule hl (repW (hW := hW) ψ) ∧ kOf V H = Tim79a.xOf V H ∧
        Nat.card V = 2 ^ l ∧ Nat.card (Tim79a.xOf V H) = 2 ^ (4 * l) := by
  classical
  have hWne : Tim79a.xOf V H ≠ ⊥ := fun hbot =>
    h.toHyp.ne_bot (le_bot_iff.mp (hbot ▸ le_xOf_self V H))
  obtain ⟨W₀, hW₀W, hW₀ne, hN, hmin⟩ :=
    exists_minimal_normalized_le (H := H) hWne (Tim79a.H_le_normalizer_xOf V H)
  obtain ⟨F, hField, hFintype, hCharP, l, hl1, hl, ψ, horth, hcardW0, hcardVW0,
    hPW0, hPK, hKsup⟩ :=
    exists_orth_of_kOf_abelian (hW := hW) h hPH hVH hH hnM hK hab hL
      hW₀W hN hW₀ne hmin
  letI := hField
  letI := hFintype
  letI := hCharP
  have hstar : Pc M V ⊓ Tim79a.xOf V H ≤ V ⊔ (Pc M V ⊓ W₀) := by
    calc Pc M V ⊓ Tim79a.xOf V H ≤ Pc M V ⊓ kOf V H :=
          inf_le_inf_left (Pc M V) (xOf_le_kOf h hPH hVH)
      _ = (Pc M V ⊓ W₀) ⊔ V := hPK
      _ = V ⊔ (Pc M V ⊓ W₀) := sup_comm _ _
  have hPW : Pc M V ⊓ W₀ ≤ ⁅W₀, Pc M V⁆ := le_of_eq hPW0
  have hVW0 : V ≤ W₀ :=
    le_of_isOrthModule (hW := hW) h hPH hVH hH hnM ψ hl hW₀W hN horth hPW hstar
  have hVhW0 : conjSubgroup h₀ V ≤ W₀ :=
    conj_le_of_le_of_normalizer h hPH hH hN hVW0
  have hK_eq_W0 : kOf V H = W₀ := by
    rw [hKsup]
    exact le_antisymm (sup_le (sup_le le_rfl hVW0) hVhW0)
      (le_sup_left.trans le_sup_left)
  have hW_eq_W0 : Tim79a.xOf V H = W₀ :=
    (le_antisymm (xOf_le_kOf h hPH hVH) (hK_eq_W0.symm ▸ hW₀W)).trans hK_eq_W0
  have hcardV : Nat.card V = 2 ^ l := by
    calc Nat.card V = Nat.card ↥(V ⊓ W₀) := by rw [inf_eq_left.mpr hVW0]
      _ = 2 ^ l := hcardVW0
  have hcardW : Nat.card (Tim79a.xOf V H) = 2 ^ (4 * l) := by
    rw [hW_eq_W0]
    exact hcardW0
  refine ⟨F, hField, hFintype, hCharP, l, hl1, hl, ψ, ?_,
    hK_eq_W0.trans hW_eq_W0.symm, hcardV, hcardW⟩
  cases hW_eq_W0
  have hW₀eq : hW₀W = (le_rfl : Tim79a.xOf V H ≤ Tim79a.xOf V H) := Subsingleton.elim _ _
  have hNeq : hN = Tim79a.H_le_normalizer_xOf V H := Subsingleton.elim _ _
  rw [hW₀eq, hNeq] at horth
  exact IsOrthModule.repW_of_subRepW (hW := hW) ψ hl horth

end RootHyp

end CFSG.RankThree.GF2n.Tim81

end
