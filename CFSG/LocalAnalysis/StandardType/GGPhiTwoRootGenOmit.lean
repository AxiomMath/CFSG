module

public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenRoot
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.WeylRoots

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem eq_or_eq_neg_of_excRefl_eq_excRefl
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {α β : Fin τ.rank → ℤ} (hα : IsRoot τ α) (hβ : IsRoot τ β)
    (h : ExcSplitRootGen.excRefl (p := p) α = ExcSplitRootGen.excRefl β) : β = α ∨ β = -α := by
  refine ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero hτ hp2 hα hβ ?_
  intro t ht
  rw [← ExcSplitRootGen.excRefl_eq_self_iff hp2 hβ t, ← congrFun h t,
    ExcSplitRootGen.excRefl_eq_self_iff hp2 hα t]
  exact ht

private theorem map_conj_le_of_le_of_mem {G : Type} [Group G] {M S : Subgroup G} {n : G}
    (hn : n ∈ M) (hS : S ≤ M) : S.map (MulAut.conj n).toMonoidHom ≤ M := by
  rintro y ⟨x, hx, rfl⟩
  show MulAut.conj n x ∈ M
  rw [MulAut.conj_apply]
  exact M.mul_mem (M.mul_mem hn (hS hx)) (M.inv_mem hn)

theorem iSup_excRefl_ne_eq_top
    {τ : Tag} {p : ℕ} {G : Type} [Group G] (J : (Fin τ.rank → ℤ) → Subgroup G)
    (hweyl : ∀ ε, IsRoot τ ε → ∃ n ∈ J ε, ∀ γ, IsRoot τ γ →
      (J γ).map (MulAut.conj n).toMonoidHom = J (rootReflection ε • γ))
    (hsep : ∀ α β, IsRoot τ α → IsRoot τ β →
      ExcSplitRootGen.excRefl (p := p) α = ExcSplitRootGen.excRefl β → β = α ∨ β = -α)
    (hne : ∀ δ, IsRoot τ δ → ∃ ε, IsRoot τ ε ∧ ε ≠ δ ∧ ε ≠ -δ ∧
      rootReflection ε • δ ≠ δ ∧ rootReflection ε • δ ≠ -δ)
    (htop : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, J γ.1) = ⊤)
    (δ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}) :
    (⨆ (i : {γ : Fin τ.rank → ℤ // IsRoot τ γ})
        (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl δ.1), J i.1) = ⊤ := by
  let M' : Subgroup G := ⨆ (i : {γ : Fin τ.rank → ℤ // IsRoot τ γ})
      (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl δ.1), J i.1
  have hM' : ∀ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, J γ.1 ≤ M' := by
    intro γ
    by_cases hγδ : ExcSplitRootGen.excRefl (p := p) γ.1 = ExcSplitRootGen.excRefl δ.1
    · obtain ⟨ε, hεroot, hεne, hεneneg, hεγ, hεγneg⟩ := hne γ.1 γ.2
      have hεδ : ExcSplitRootGen.excRefl (p := p) ε ≠ ExcSplitRootGen.excRefl δ.1 := by
        intro hEq
        rcases hsep ε γ.1 hεroot γ.2 (hEq.trans hγδ.symm) with h | h
        · exact hεne h.symm
        · exact hεneneg (by rw [h]; simp)
      have hγ'root : IsRoot τ (rootReflection ε • γ.1) := IsRoot.smul γ.2 _
      have hγ'δ : ExcSplitRootGen.excRefl (p := p) (rootReflection ε • γ.1) ≠
          ExcSplitRootGen.excRefl δ.1 := by
        intro hEq
        rcases hsep (rootReflection ε • γ.1) γ.1 hγ'root γ.2 (hEq.trans hγδ.symm) with h | h
        · exact hεγ h.symm
        · exact hεγneg (by simpa using (congrArg Neg.neg h).symm)
      have hJε : J ε ≤ M' := by
        change J ε ≤ ⨆ (i : {γ : Fin τ.rank → ℤ // IsRoot τ γ})
          (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl δ.1), J i.1
        exact le_iSup₂_of_le (a := J ε) ⟨ε, hεroot⟩ hεδ le_rfl
      have hJγ' : J (rootReflection ε • γ.1) ≤ M' := by
        change J (rootReflection ε • γ.1) ≤ ⨆ (i : {γ : Fin τ.rank → ℤ // IsRoot τ γ})
          (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl δ.1), J i.1
        exact le_iSup₂_of_le (a := J (rootReflection ε • γ.1))
          ⟨rootReflection ε • γ.1, hγ'root⟩ hγ'δ le_rfl
      obtain ⟨n, hn, hconj⟩ := hweyl ε hεroot
      have hfix : rootReflection ε • (rootReflection ε • γ.1) = γ.1 := by
        rw [← mul_smul, rootReflection_mul_self hεroot, one_smul]
      have hmap : (J (rootReflection ε • γ.1)).map (MulAut.conj n).toMonoidHom = J γ.1 := by
        rw [hconj (rootReflection ε • γ.1) hγ'root, hfix]
      calc J γ.1 = (J (rootReflection ε • γ.1)).map (MulAut.conj n).toMonoidHom := hmap.symm
        _ ≤ M' := map_conj_le_of_le_of_mem (hJε hn) hJγ'
    · change J γ.1 ≤ ⨆ (i : {γ : Fin τ.rank → ℤ // IsRoot τ γ})
        (_ : ExcSplitRootGen.excRefl (p := p) i.1 ≠ ExcSplitRootGen.excRefl δ.1), J i.1
      exact le_iSup₂_of_le (a := J γ.1) ⟨γ.1, γ.2⟩ hγδ le_rfl
  have htop' : (⨆ γ : {γ : Fin τ.rank → ℤ // IsRoot τ γ}, J γ.1) ≤ M' := iSup_le hM'
  rw [htop] at htop'
  exact eq_top_iff.2 htop'

end CFSG.StandardType.PhiTwoRootGen

end
