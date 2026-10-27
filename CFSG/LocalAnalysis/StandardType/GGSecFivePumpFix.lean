module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
import CFSG.LocalAnalysis.StandardType.GGSpJoinReflPairing
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.Spin

private def parD (k : ℕ) (hk : 4 ≤ k) (i : Fin k) : Fin k :=
  ⟨if i.val = k - 1 then k - 3 else i.val - 1, by have := i.isLt; split_ifs <;> omega⟩

private def depthD (k : ℕ) (i : Fin k) : ℕ := if i.val = k - 1 then k - 2 else i.val

private theorem hslD (k : ℕ) (i j : Fin k) (hij : i ≠ j) :
    CartanMatrix.D k i j = 0 ∨ CartanMatrix.D k i j = -1 := by
  rw [← cartanD_eq]
  simp only [cartanD, Matrix.of_apply, if_neg hij]
  split_ifs <;> simp

private theorem hparD (k : ℕ) (hk : 4 ≤ k) (i j : Fin k) (hij : i ≠ j) :
    CartanMatrix.D k i j = -1 ↔ ((i ≠ ⟨0, by omega⟩ ∧ parD k hk i = j) ∨
      (j ≠ ⟨0, by omega⟩ ∧ parD k hk j = i)) := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  have hij' : i ≠ j := fun h => hij (Fin.ext h)
  rw [← cartanD_eq]
  simp only [cartanD, Matrix.of_apply, parD, ne_eq, Fin.mk.injEq, if_neg hij']
  by_cases hc : i + 1 = j ∧ j + 1 < k ∨ j + 1 = i ∧ i + 1 < k ∨ i + 3 = k ∧ j + 1 = k ∨
      j + 3 = k ∧ i + 1 = k
  · rw [if_pos hc]
    refine iff_of_true rfl ?_
    split_ifs <;> omega
  · rw [if_neg hc]
    refine iff_of_false (by decide) ?_
    split_ifs <;> omega

private theorem hdepthD (k : ℕ) (hk : 4 ≤ k) (i : Fin k) (hi : i ≠ ⟨0, by omega⟩) :
    depthD k (parD k hk i) < depthD k i := by
  have := i.isLt
  have hi' : i.val ≠ 0 := fun h => hi (Fin.ext h)
  simp only [depthD, parD]
  split_ifs <;> omega

private theorem quot_pairing {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {r : ℕ}
    (h : Fin r → V) (α : Fin r → Module.Dual (ZMod p) V) (S : Submodule (ZMod p) V)
    (hS : ∀ i, S ≤ LinearMap.ker (α i)) :
    ∃ (h' : Fin r → V ⧸ S) (α' : Fin r → Module.Dual (ZMod p) (V ⧸ S)),
      ∀ i j, α' i (h' j) = α i (h j) :=
  ⟨fun i => S.mkQ (h i), fun i => S.liftQ (α i) (hS i), fun i j => by
    simp only [Submodule.mkQ_apply, Submodule.liftQ_apply]⟩

theorem ggWeylD_eq_one_of_fixed {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {k : ℕ} (hk : 4 ≤ k) {A : Subgroup (MulAut ↥Bs)}
    (hW : GGWeylOfType p (ggCoxeterMatrixD k) A) (hind : ∀ ψ ∈ A, ψ ∈ ggInduced ⊤ Bs)
    (hcard : Nat.card Bs = p ^ k) {b : ↥Bs} (hb : ∀ ψ ∈ A, ψ b = b) : b = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, _, _, ⟨ιV⟩⟩ := exists_ggLinData (p := p) hBs
  haveI : Finite V := Finite.of_equiv _ (Additive.ofMul.trans ιV.toEquiv)
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  obtain ⟨e, h, α, hα, hrefl, hP⟩ := SpJoinRefl.exists_cartan_pairing_of_weylOfType hp2 hNT
    (ggIntCartan_D k) (hslD k) (parD k hk) ⟨0, by omega⟩ (depthD k) (hparD k hk) (hdepthD k hk)
    hW hind ιV
  have hdim : Module.finrank (ZMod p) V = k := by
    have h1 : Nat.card Bs = p ^ Module.finrank (ZMod p) V := by
      rw [card_eq_of_ggLin ιV, Module.natCard_eq_pow_finrank (K := ZMod p) (V := V),
        Nat.card_zmod]
    rw [hcard] at h1
    exact (Nat.pow_right_injective hp.two_le h1).symm
  have hαv : ∀ i, α i (ιV (Additive.ofMul b)) = 0 := by
    intro i
    have h1 := (ggLin_fix_iff (p := p) ιV _ b).mp (hb _ (e ((ggCoxeterMatrixD k).simple i)).2)
    rw [hrefl i, Module.reflection_apply, sub_eq_self] at h1
    refine (smul_eq_zero.mp h1).resolve_right fun h0 => ?_
    have h2 := hα i
    rw [h0, map_zero] at h2
    exact zmod_two_ne_zero hp2 h2.symm
  by_contra hb1
  have hv0 : ιV (Additive.ofMul b) ≠ 0 := fun h0 =>
    hb1 (ofMul_eq_zero.mp (ιV.injective (h0.trans (map_zero ιV).symm)))
  let S : Submodule (ZMod p) V := ZMod p ∙ ιV (Additive.ofMul b)
  have hS : ∀ i, S ≤ LinearMap.ker (α i) := fun i => by
    rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact hαv i
  obtain ⟨h', α', hP'⟩ := quot_pairing h α S hS
  have hle := SpJoinRefl.le_finrank_of_cartanD hp2 (by omega : 2 ≤ k) h' α' fun i j =>
    (hP' i j).trans (hP i j)
  have hq := Submodule.finrank_quotient_add_finrank S
  rw [finrank_span_singleton hv0, hdim] at hq
  omega

end CFSG.StandardType

end
