module

public import CFSG.Quasithin.Background.HSp4Model

public section

namespace CFSG.Quasithin

namespace H

namespace Sp4

open CFSG.Assembly.LowTwoRank Matrix PairG
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour (sym2 sym2_transpose)
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauSp_bijective)
open scoped Matrix

local notation "ι₀" => (Sum.inl 0 : Fin 2 ⊕ Fin 2)
local notation "ι₁" => (Sum.inl 1 : Fin 2 ⊕ Fin 2)
local notation "ι₂" => (Sum.inr 0 : Fin 2 ⊕ Fin 2)
local notation "ι₃" => (Sum.inr 1 : Fin 2 ⊕ Fin 2)

variable {K : Type} [Field K] [CharP K 2]

abbrev pairSp (K : Type) [Field K] [CharP K 2] : Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) :=
  pairImg (StatedSp 2 K) tauSp

abbrev pairNormSp (K : Type) [Field K] [CharP K 2] :
    Subgroup (MulAut (PairMod (Fin 2 ⊕ Fin 2) K)) :=
  pairNorm (StatedSp 2 K) tauSp

theorem pairHom_apply_inl (γ : StatedSp 2 K) (u : Fin 2 ⊕ Fin 2 → K) :
    pairHom (StatedSp 2 K) tauSp γ ((Multiplicative.ofAdd u, 1) : PairMod (Fin 2 ⊕ Fin 2) K) =
      (Multiplicative.ofAdd (((γ : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ u), 1) := by
  rw [pairHom_apply, pairAut_apply, map_one]
  rfl

theorem pairHom_apply_inr (γ : StatedSp 2 K) (w : Fin 2 ⊕ Fin 2 → K) :
    pairHom (StatedSp 2 K) tauSp γ ((1, Multiplicative.ofAdd w) : PairMod (Fin 2 ⊕ Fin 2) K) =
      (1, Multiplicative.ofAdd ((((tauSp γ : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w)) := by
  rw [pairHom_apply, pairAut_apply, map_one]
  rfl

theorem not_isoMod [Finite K] :
    ¬ Pair.IsoMod (pairSp K) (V₁ (Fin 2 ⊕ Fin 2) K) (V₂ (Fin 2 ⊕ Fin 2) K) := by
  rintro ⟨e, he⟩
  set l := pairHom (StatedSp 2 K) tauSp (upSp (sym2_transpose (1 : K) 0 0)) with hl
  have hlm : l ∈ pairSp K := pairHom_mem_pairImg _ _ _
  have a₁ : ∀ u : Fin 2 ⊕ Fin 2 → K, l ((Multiplicative.ofAdd u, 1) :
      PairMod (Fin 2 ⊕ Fin 2) K) = (Multiplicative.ofAdd (u + Pi.single ι₀ (u ι₂)), 1) := by
    intro u
    rw [hl, pairHom_apply_inl, coe_upSp, up_mulVec]
    simp
  have b₁ : ∀ w : Fin 2 ⊕ Fin 2 → K, l ((1, Multiplicative.ofAdd w) :
      PairMod (Fin 2 ⊕ Fin 2) K) =
        (1, Multiplicative.ofAdd (w + Pi.single ι₀ (w ι₃) + Pi.single ι₁ (w ι₂))) := by
    intro w
    rw [hl, pairHom_apply_inr, tauSp_upSp_diag_mulVec]
    simp
  let F₁ := {v : V₁ (Fin 2 ⊕ Fin 2) K // l v = v}
  let F₂ := {w : V₂ (Fin 2 ⊕ Fin 2) K // l w = w}
  have hfix : ∀ v : V₁ (Fin 2 ⊕ Fin 2) K, l v = v → l (e v) = e v := by
    intro v h1
    have e1 := he l hlm v (by rw [h1]; exact v.2)
    have v1 : (⟨l v, by rw [h1]; exact v.2⟩ : V₁ (Fin 2 ⊕ Fin 2) K) = v := Subtype.ext h1
    rw [v1] at e1
    exact e1.symm
  have hinj : Nat.card F₁ ≤ Nat.card F₂ := by
    refine Nat.card_le_card_of_injective (fun v => ⟨e v.1, hfix v.1 v.2⟩) ?_
    intro v w h
    have := congrArg (fun z : F₂ => z.1) h
    exact Subtype.ext (e.injective this)
  have h1 : Nat.card (K × K × K) ≤ Nat.card F₁ := by
    refine Nat.card_le_card_of_injective (fun p => ⟨⟨(Multiplicative.ofAdd
      (Sum.elim ![p.1, p.2.1] ![0, p.2.2]), 1), mem_V₁.mpr rfl⟩, ?_⟩) ?_
    · change l ((Multiplicative.ofAdd (Sum.elim ![p.1, p.2.1] ![0, p.2.2]), 1) :
        PairMod (Fin 2 ⊕ Fin 2) K) = _
      rw [a₁]
      simp
    · intro p q hpq
      have := congrArg (fun z : F₁ => Multiplicative.toAdd (z.1 : PairMod (Fin 2 ⊕ Fin 2) K).1) hpq
      simp only [toAdd_ofAdd] at this
      have e0 := congrFun this ι₀
      have e1 := congrFun this ι₁
      have e3 := congrFun this ι₃
      simp at e0 e1 e3
      exact Prod.ext e0 (Prod.ext e1 e3)
  have h2 : Nat.card F₂ ≤ Nat.card (K × K) := by
    refine Nat.card_le_card_of_injective
      (fun w => (Multiplicative.toAdd (w.1 : PairMod (Fin 2 ⊕ Fin 2) K).2 ι₀,
        Multiplicative.toAdd (w.1 : PairMod (Fin 2 ⊕ Fin 2) K).2 ι₁)) ?_
    intro w w' hww'
    have eq0 : ∀ z : F₂, Multiplicative.toAdd (z.1 : PairMod (Fin 2 ⊕ Fin 2) K).2 ι₂ = 0 ∧
        Multiplicative.toAdd (z.1 : PairMod (Fin 2 ⊕ Fin 2) K).2 ι₃ = 0 := by
      intro z
      have hz1 : (z.1 : PairMod (Fin 2 ⊕ Fin 2) K).1 = 1 := mem_V₂.mp z.1.2
      have hzeq : (z.1 : PairMod (Fin 2 ⊕ Fin 2) K) = (1, Multiplicative.ofAdd
          (Multiplicative.toAdd (z.1 : PairMod (Fin 2 ⊕ Fin 2) K).2)) := Prod.ext hz1 rfl
      have k1 := z.2
      rw [hzeq, b₁] at k1
      have k0 := congrFun (congrArg (fun x : PairMod (Fin 2 ⊕ Fin 2) K =>
        Multiplicative.toAdd x.2) k1) ι₀
      have k1' := congrFun (congrArg (fun x : PairMod (Fin 2 ⊕ Fin 2) K =>
        Multiplicative.toAdd x.2) k1) ι₁
      simp at k0 k1'
      exact ⟨k1', k0⟩
    have hw1 : (w.1 : PairMod (Fin 2 ⊕ Fin 2) K).1 = 1 := mem_V₂.mp w.1.2
    have hw1' : (w'.1 : PairMod (Fin 2 ⊕ Fin 2) K).1 = 1 := mem_V₂.mp w'.1.2
    have hww0 := congrArg Prod.fst hww'
    have hww1 := congrArg Prod.snd hww'
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext (hw1.trans hw1'.symm)
    apply funext
    intro i
    rcases i with i | i <;> fin_cases i
    · exact hww0
    · exact hww1
    · exact (eq0 w).1.trans (eq0 w').1.symm
    · exact (eq0 w).2.trans (eq0 w').2.symm
  have hK : 1 < Nat.card K := Finite.one_lt_card
  have := (h1.trans hinj).trans h2
  simp only [Nat.card_prod] at this
  nlinarith

theorem tauSp_surjective [Finite K] :
    Function.Surjective (tauSp : StatedSp 2 K →* StatedSp 2 K) :=
  tauSp_bijective.2

theorem map_V₁_eq_or [Finite K] {x : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)}
    (hx : x ∈ pairNormSp K) :
    (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K ∨
      (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₂ (Fin 2 ⊕ Fin 2) K :=
  PairG.map_V₁_eq_or isNatIrr_statedSp tauSp_surjective not_isoMod hx

theorem exists_pairAut [Finite K] {x : MulAut (PairMod (Fin 2 ⊕ Fin 2) K)}
    (hx : x ∈ pairNormSp K)
    (h1 : (V₁ (Fin 2 ⊕ Fin 2) K).map x.toMonoidHom = V₁ (Fin 2 ⊕ Fin 2) K) :
    ∃ a b : MulAut (StdMod (Fin 2 ⊕ Fin 2) K), x = pairAut a b :=
  PairG.exists_pairAut isNatIrr_statedSp tauSp_surjective not_isoMod hx h1

end Sp4

end H

end CFSG.Quasithin
