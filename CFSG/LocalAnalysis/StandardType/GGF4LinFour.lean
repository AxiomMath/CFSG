module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofLin
import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverCoord
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.Abel

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggF4Orig_fix_four {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) (hcard : Nat.card ↥Bs ≤ p ^ 4)
    (t : Fin 4 → MulAut ↥Bs) (ht : ∀ k, GGIsReflection p (t k))
    (hcomm : ∀ j k, t j * t k = t k * t j) (hinj : Function.Injective t)
    (b : ↥Bs) (hb : ∀ k, t k b = b) : b = 1 := by
  classical
  obtain ⟨V, iAV, iMV, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  haveI hB : Finite ↥Bs := Finite.of_injective (Subtype.val : ↥Bs → G) Subtype.val_injective
  haveI : Finite (Additive ↥Bs) := hB
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [Nat.card_zmod] at h
    exact h
  have hfr : Module.finrank (ZMod p) V ≤ 4 := by
    have h1 : p ^ Module.finrank (ZMod p) V ≤ p ^ 4 := by
      rw [← hVcard, ← card_eq_of_ggLin ι]
      exact hcard
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp h1
  let T : Fin 4 → (V ≃ₗ[ZMod p] V) := fun k => ggLin (p := p) ι (t k)
  have hT : ∀ k, IsLinRefl (T k) := fun k => isLinRefl_ggLin ι (ht k)
  have hTc : ∀ j k, T j * T k = T k * T j := by
    intro j k
    show ggLin (p := p) ι (t j) * ggLin (p := p) ι (t k) =
      ggLin (p := p) ι (t k) * ggLin (p := p) ι (t j)
    rw [← map_mul, ← map_mul, hcomm j k]
  have hTne : ∀ j k, j ≠ k → T j ≠ T k := fun j k hjk h => hjk (hinj (ggLin_injective ι h))
  have hx : ∀ k, ∃ x : V, x ≠ 0 ∧ T k x = -x := by
    intro k
    obtain ⟨x, f, hfx, hTv⟩ := hT k
    refine ⟨x, ?_, ?_⟩
    · intro h0
      rw [h0, map_zero] at hfx
      exact zmod_two_ne_zero hp2 hfx.symm
    · rw [hTv x, hfx, two_smul]
      abel
  choose x hxne hxneg using hx
  have hfix : ∀ j k, j ≠ k → T j (x k) = x k := fun j k hjk =>
    IsLinRefl.comm_fix hp2 (hT k) (hT j) (hTc k j) (hTne k j hjk.symm) (hxneg k)
  let K : Fin 4 → Submodule (ZMod p) V :=
    fun k => LinearMap.ker ((T k).toLinearMap - LinearMap.id)
  have hK : ∀ k v, v ∈ K k ↔ T k v = v := by
    intro k v
    simp [K, sub_eq_zero]
  have hnegne : ∀ k, x k ∉ K k := by
    intro k hk
    rw [hK, hxneg k] at hk
    have h2 : x k + x k = 0 := by
      calc x k + x k = -x k + x k := by rw [hk]
        _ = 0 := neg_add_cancel _
    have h3 : (2 : ZMod p) • x k = 0 := by rw [two_smul]; exact h2
    exact hxne k ((smul_eq_zero.mp h3).resolve_left (zmod_two_ne_zero hp2))
  have h1 : K 0 < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => hnegne 0 ?_
    rw [h]
    exact Submodule.mem_top
  have h2 : K 0 ⊓ K 1 < K 0 := by
    refine lt_of_le_of_ne inf_le_left fun h => hnegne 1 ?_
    have hmem : x 1 ∈ K 0 := (hK 0 _).2 (hfix 0 1 (by decide))
    have hmem' : x 1 ∈ K 0 ⊓ K 1 := by rw [h]; exact hmem
    exact (Submodule.mem_inf.1 hmem').2
  have h3 : (K 0 ⊓ K 1) ⊓ K 2 < K 0 ⊓ K 1 := by
    refine lt_of_le_of_ne inf_le_left fun h => hnegne 2 ?_
    have hmem : x 2 ∈ K 0 ⊓ K 1 :=
      Submodule.mem_inf.2 ⟨(hK 0 _).2 (hfix 0 2 (by decide)), (hK 1 _).2 (hfix 1 2 (by decide))⟩
    have hmem' : x 2 ∈ (K 0 ⊓ K 1) ⊓ K 2 := by rw [h]; exact hmem
    exact (Submodule.mem_inf.1 hmem').2
  have h4 : ((K 0 ⊓ K 1) ⊓ K 2) ⊓ K 3 < (K 0 ⊓ K 1) ⊓ K 2 := by
    refine lt_of_le_of_ne inf_le_left fun h => hnegne 3 ?_
    have hmem : x 3 ∈ (K 0 ⊓ K 1) ⊓ K 2 :=
      Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨(hK 0 _).2 (hfix 0 3 (by decide)),
        (hK 1 _).2 (hfix 1 3 (by decide))⟩, (hK 2 _).2 (hfix 2 3 (by decide))⟩
    have hmem' : x 3 ∈ ((K 0 ⊓ K 1) ⊓ K 2) ⊓ K 3 := by rw [h]; exact hmem
    exact (Submodule.mem_inf.1 hmem').2
  have hl1 := Submodule.finrank_lt_finrank_of_lt h1
  have hl2 := Submodule.finrank_lt_finrank_of_lt h2
  have hl3 := Submodule.finrank_lt_finrank_of_lt h3
  have hl4 := Submodule.finrank_lt_finrank_of_lt h4
  have hftop : Module.finrank (ZMod p) (⊤ : Submodule (ZMod p) V) = Module.finrank (ZMod p) V := by
    simp
  have hV4 : Module.finrank (ZMod p) ↥(((K 0 ⊓ K 1) ⊓ K 2) ⊓ K 3) = 0 := by omega
  have hbot : ((K 0 ⊓ K 1) ⊓ K 2) ⊓ K 3 = ⊥ := Submodule.finrank_eq_zero.1 hV4
  have hk : ∀ k, ι (Additive.ofMul b) ∈ K k := fun k =>
    (hK k _).2 ((ggLin_fix_iff ι (t k) b).1 (hb k))
  have hv : ι (Additive.ofMul b) ∈ ((K 0 ⊓ K 1) ⊓ K 2) ⊓ K 3 :=
    Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hk 0, hk 1⟩, hk 2⟩, hk 3⟩
  rw [hbot] at hv
  have h0 : ι (Additive.ofMul b) = 0 := (Submodule.mem_bot _).1 hv
  have h00 : Additive.ofMul b = 0 := ι.injective (by rw [h0, map_zero])
  exact Additive.ofMul.injective (h00.trans ofMul_one.symm)

end CFSG.StandardType

end
