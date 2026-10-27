module

public import CFSG.RankThree.PartOne.U5K.Pkg.At
public import CFSG.RankThree.PartOne.U5K.Pkg.Torus
public import CFSG.RankThree.PartOne.U5K.Pkg.Zero

public section

namespace CFSG.RankThree.PartOne.U5K.Pkg

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.RankThreeEven (projSU)

theorem _root_.CFSG.RankThree.PartOne.U5K.u5FiveInndiag_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) : U5FiveInndiag := by
  intro G _ _ p A c L E h15 hF hout hp5 f e x hx hxE
  subst hp5
  have h := h15.h12
  have hp := h.prime
  obtain ⟨f₀, hf₀1, hpf₀, ⟨e₀⟩, -⟩ := id hout
  have hf₀2 : 2 ≤ f₀ := by
    by_contra hlt
    have hf₁ : f₀ = 1 := by omega
    subst hf₁
    norm_num at hpf₀
  have hf1 : 1 ≤ f := by
    by_contra hlt
    have hf0 : f = 0 := by omega
    subst hf0
    exact (not_mulEquiv_projSU_zero hf₀2).false (e.symm.trans e₀)
  have hff : f = f₀ := eq_of_mulEquiv_projSU_five hf1 hf₀1 (e.symm.trans e₀)
  have hpf : 5 ∣ 2 ^ f + 1 := hff ▸ hpf₀
  have hAt := kfU5At_holds hGA G 5 A c L E f h15 hF hout hf1 hpf ⟨e⟩
  obtain ⟨ψ, k, hk, hstab⟩ := exists_psi_k h15 hF hout
  let M := mkModel h15 hF hout ψ k hk hstab
  set I := lieGenerated 5 E with hI
  have hEN : ∀ y : G, y ∈ E → y ∈ Subgroup.normalizer (I : Set G) := fun y hy =>
    torusNormalizer_le_lieNormalizer hp E (Subgroup.le_normalizer hy)
  let ι : ↥E →* ↥(Subgroup.normalizer (I : Set G)) :=
    { toFun := fun y => ⟨(y : G), hEN y y.2⟩
      map_one' := rfl
      map_mul' := fun a b => rfl }
  let φ : ↥E →* MulAut (projSU 5 2 f) := (U5Act I e).comp ι
  let S : Subgroup ↥E := (U5Inndiag f).comap φ
  have hv : ∀ i, M.v i ∈ S := by
    intro i
    obtain ⟨j, k', hjk, hji, hki⟩ : ∃ j k' : Fin 5, j ≠ k' ∧ j ≠ i ∧ k' ≠ i := by
      have : ∀ i : Fin 5, ∃ j k' : Fin 5, j ≠ k' ∧ j ≠ i ∧ k' ≠ i := by decide
      exact this i
    obtain ⟨t, ht, hψ⟩ := M.surj_swap (σ := Equiv.swap j k') ⟨j, k', hjk, rfl⟩
    have hfix : t (M.v i) = M.v i := by
      have := M.equivariant ⟨t, Subgroup.subset_closure ht⟩ i
      rw [hψ, Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) (Ne.symm hki)] at this
      exact this
    obtain ⟨-, hmod, hcent, -⟩ := hAt t ht
    have hmemfix : ((M.v i : E) : G) ∈ autFixedInG E t := ⟨M.v i, hfix, rfl⟩
    rw [← hcent] at hmemfix
    have hK : ∀ z ∈ kZero 5 E t, z * ((M.v i : E) : G) = ((M.v i : E) : G) * z :=
      fun z hz => Subgroup.mem_centralizer_iff.1 hmemfix.2 z hz
    have hKI : kZero 5 E t ≤ lieGenerated 5 E :=
      PhanAssembly.kZero_le_lieGenerated (fun t ht => hAt t ht) ht
    have hx5 : ((M.v i : E) : G) ^ 5 = 1 := Sec12Three.pow_eq_one_of_mem_E h (M.v i).2
    have := U5Act_mem_inndiag_of_centralizes hf1 hpf e hKI hmod (hEN _ (M.v i).2)
      (fun z hz => (hK z hz).symm) hx5
    exact this
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← M.span_eq_top]
    exact (Subgroup.closure_le S).2 (by rintro _ ⟨i, rfl⟩; exact hv i)
  have hmem : (⟨x, hxE⟩ : ↥E) ∈ S := by
    rw [hS]
    trivial
  exact hmem

end CFSG.RankThree.PartOne.U5K.Pkg
