module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeAd

public section

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TableBExc.E6Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def corootVec (γ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ZMod 3 :=
  fun k => ((∑ l, Tag.E6.cartan k l * γ l : ℤ) : ZMod 3)

set_option maxRecDepth 100000 in
theorem coroot_hit : ∀ lam : Fin 6 → ZMod 3, lam ≠ 0 →
    ∃ r ∈ Tag.E6.artifactRoots,
      ∑ i : Fin 6, lam i * (((∑ l : Fin 6, Tag.E6.cartan i l * r.getD l 0 : ℤ)) : ZMod 3) = 0 := by
  decide +kernel

section Subspace


theorem exists_root_corootVec_mem (S : Submodule (ZMod 3) (Fin Tag.E6.rank → ZMod 3))
    (h : 3 ^ 5 ≤ Nat.card S) :
    ∃ γ : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 γ ∧ corootVec γ ∈ S := by
  by_cases hS : S = ⊤
  · exact ⟨Pi.single 0 1, isRoot_single Tag.E6 0, by rw [hS]; trivial⟩
  obtain ⟨f, hf0, hSf⟩ := Submodule.exists_le_ker_of_lt_top S (lt_top_iff_ne_top.2 hS)
  have hker : Module.finrank (ZMod 3) (LinearMap.ker f) = 5 := by
    have h1 := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
    rw [Module.finrank_fin_fun] at h1
    change _ + 1 = 6 at h1
    omega
  have hS5 : 5 ≤ Module.finrank (ZMod 3) S := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3) (V := S), Nat.card_zmod] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 h
  have hSeq : S = LinearMap.ker f :=
    Submodule.eq_of_le_of_finrank_le hSf (by rw [hker]; exact hS5)
  set lam : Fin Tag.E6.rank → ZMod 3 := fun i => f (Pi.single i 1) with hlam
  have hfx : ∀ x : Fin Tag.E6.rank → ZMod 3, f x = ∑ i, lam i * x i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ f x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, mul_comm]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hf0
    refine LinearMap.ext fun x => ?_
    rw [hfx x, h0]
    simp
  obtain ⟨r, hr, hr0⟩ := coroot_hit lam hlam0
  have hlen : r.length = 6 := length_of_mem_artifactRoots (τ := Tag.E6) hr
  refine ⟨fun i => r.getD i 0, isRoot_iff_mem_artifactRoots.2 ?_, ?_⟩
  · convert hr using 1
    refine List.ext_getElem (by rw [List.length_ofFn, hlen]; rfl) fun n h1 h2 => ?_
    simp [List.getD_eq_getElem?_getD, h2]
  · rw [hSeq, LinearMap.mem_ker, hfx]
    rw [← hr0]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1

end Subspace

section Tuple


theorem corootTuple_eq_zetaVec {L : Type} [Field L] (ζ : Lˣ) (hζ : ζ ^ 3 = 1)
    (γ : Fin Tag.E6.rank → ℤ) :
    TwE6RootAs.corootTuple γ ζ = zetaVec ζ hζ (corootVec γ) := by
  refine funext fun k => Eq.trans ?_ (zetaVec_apply ζ hζ (corootVec γ) k).symm
  have hv : ((corootVec γ k).val : ℤ) = (∑ l, Tag.E6.cartan k l * γ l) % 3 :=
    ZMod.val_intCast (∑ l, Tag.E6.cartan k l * γ l)
  change ζ ^ (∑ l, Tag.E6.cartan k l * γ l) = ζ ^ (corootVec γ k).val
  rw [zpow_eq_zpow_emod' _ hζ, ← zpow_natCast, hv]
  rfl

end Tuple

end CFSG.StandardType.TwE6EndNode3

end
