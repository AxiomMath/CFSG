module

public import CFSG.RankThree.PartOne.CTP.Su4Blk
public import CFSG.RankThree.PartOne.CTP.Su4Long
public import CFSG.RankThree.PartOne.CTP.Su4Pos
public import CFSG.RankThree.PartOne.CTP.Su4Short

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

variable {K : Type} [Field K] {σ : K ≃+* K} {p : ℕ} [NeZero p] {ζ : K}

theorem su4_pair [Finite K] [CharP K 2] (hσ : IsUnitaryInvolution σ) (hζ : IsPrimitiveRoot ζ p)
    (hfix : ∀ l : K, l ^ p = 1 → σ l = l) (hlt : Nat.card (SU σ 2) < Nat.card SL(2, K))
    {gA gB : SUid σ 4} (hgA : gA ^ p = 1) (hgB : gB ^ p = 1) (hgA1 : gA ≠ 1) (hgB1 : gB ≠ 1)
    (hcom : gA * gB = gB * gA) {A B : Subgroup (SUid σ 4)} [Group.IsPerfect A]
    [Group.IsPerfect B] (hA1 : A ≠ ⊥) (hB1 : B ≠ ⊥) (hcardA : Nat.card A = Nat.card (SU σ 2))
    (hcardB : Nat.card B = Nat.card SL(2, K)) (hcA : ∀ a ∈ A, a * gA = gA * a)
    (hcB : ∀ b ∈ B, b * gB = gB * b) (hmovB : ∃ b ∈ B, gA * b ≠ b * gA) {z : SUid σ 4}
    (hzA : z ∈ A) (hzp : z ^ p = 1) (hzg : z * gB = gB * z)
    (hzB : ¬ ∀ b ∈ B, z * b = b * z) :
    ∃ (Q : GL (Fin 4) K) (hQ : conjTr σ (Q : Matrix (Fin 4) (Fin 4) K) *
        (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4),
      A = (lbEmb σ).range.map (conjEquiv Q hQ).toMonoidHom ∧
      B = (sbEmb σ hσ.invol).range.map (conjEquiv Q hQ).toMonoidHom := by
  rcases su4_node hσ.invol hζ hfix hgB hgB1 B hB1 hcB with ⟨hBd, hBfix⟩ |
    ⟨lB, hlB, hlBp, hLB2, hLB2', hcomplB, hzeroB⟩
  ·
    have h := card_le_of_long hσ hζ hgB hBd hBfix
    rw [hcardB] at h
    exact absurd hlt (not_lt.mpr h)
  rcases su4_node hσ.invol hζ hfix hgA hgA1 A hA1 hcA with ⟨hAd, hAfix⟩ |
    ⟨lA, hlA, hlAp, hLA2, hLA2', hcomplA, hzeroA⟩
  swap
  · exact (su4_not_short_short hσ hζ hfix hgA hgB hcom hcA hcB hmovB hzA hzp hzg hzB hlA hlAp
      hLA2 hLA2' hcomplA hzeroA hlB hlBp hLB2 hLB2' hcomplB hzeroB).elim
  obtain ⟨b, hb, hspanL, hspanL', hspanW⟩ := su4_pos_LS hσ hζ hfix hgB hAd
    (W := eigU gA 1) (fun w hw h => eigU_one_nondeg hσ.invol hζ hgA hw h)
    (fun v hv => smul_mem_eigU hcom.symm hv) hlB hlBp hLB2 hLB2' hcomplB hzeroB
  obtain ⟨Q, hQ, hQb⟩ := exists_wittConj b hb
  have hmov : movU gA = hermOrth σ (eigU gA 1) := movU_eq_hermOrth_eigU_one hσ.invol hζ hgA
  have hperp : ∀ k : Fin 4, (k = 0 ∨ k = 3) → b k ∈ movU gA := by
    intro k hk
    rw [hmov, mem_hermOrth, ← hspanW]
    intro s hs
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hs
    rw [herm_add_left, herm_smul_left, herm_smul_left]
    rcases hk with rfl | rfl
    · have e1 := hb 1 0
      have e2 := hb 2 0
      simp [Fin.rev] at e1 e2
      rw [e1, e2]
      ring
    · have e1 := hb 1 3
      have e2 := hb 2 3
      simp [Fin.rev] at e1 e2
      rw [e1, e2]
      ring
  refine ⟨Q, hQ, eq_map_lbEmb_of_fix hQ hcardA (fun a ha => ?_) (fun a ha => ?_),
    eq_map_sbEmb_of_stab hQ hσ.invol hcardB (fun b' hb' v hv => ?_) (fun b' hb' v hv => ?_)⟩
  · rw [hQb]
    exact hAfix a ha _ (hperp 0 (Or.inl rfl))
  · rw [hQb]
    exact hAfix a ha _ (hperp 3 (Or.inr rfl))
  · rw [hQb 0, hQb 1, hspanL] at hv ⊢
    exact smul_mem_eigU (hcB b' hb') hv
  · rw [hQb 2, hQb 3, hspanL'] at hv ⊢
    exact smul_mem_eigU (hcB b' hb') hv

end CFSG.RankThree.PartOne.CTP
