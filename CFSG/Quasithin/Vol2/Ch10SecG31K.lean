module

public import CFSG.Quasithin.Vol2.Ch10SecG31G
public import CFSG.Quasithin.Vol2.Ch10SecG31I

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.G31

open Module CFSG.Open CFSG.Quasithin.ASInputs
open CFSG.Quasithin.Vol2.Ch10.SecD (map_zpowers_mulAut)

variable {V : Type} [CommGroup V]

structure MulHyp (Gm : Subgroup (MulAut V)) (Δ₀ : Set (Subgroup V)) {s : ℕ}
    (Δ : Fin s → Set (Subgroup V)) : Prop where
  exp : ∀ v : V, v ^ 2 = 1
  O2 : pCoreOf 2 Gm = ⊥
  card : ∀ X ∈ Δ₀, Nat.card X = 2
  inv : ∀ X ∈ Δ₀, ∀ g ∈ Gm, X.map (g : MulAut V).toMonoidHom ∈ Δ₀
  trans : ∀ X ∈ Δ₀, ∀ Y ∈ Δ₀, ∃ g ∈ Gm, X.map (g : MulAut V).toMonoidHom = Y
  rel : ∀ X ∈ Δ₀, 4 ≤ (transvGroup Gm X ⊓ pCoreOf 2 Gm).relIndex (transvGroup Gm X)
  disj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)
  union : (⋃ i, Δ i) = Δ₀
  ne : ∀ i, (Δ i).Nonempty
  ginv : ∀ i, ∀ X ∈ Δ i, ∀ g ∈ g31G Gm Δ₀, X.map (g : MulAut V).toMonoidHom ∈ Δ i
  gtrans : ∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ g31G Gm Δ₀, X.map (g : MulAut V).toMonoidHom = Y

namespace MulHyp

variable {Gm : Subgroup (MulAut V)} {Δ₀ : Set (Subgroup V)} {s : ℕ} {Δ : Fin s → Set (Subgroup V)}

theorem mem_of_mem (hM : MulHyp Gm Δ₀ Δ) {i : Fin s} {X : Subgroup V} (hX : X ∈ Δ i) :
    X ∈ Δ₀ :=
  hM.union ▸ Set.mem_iUnion_of_mem i hX

theorem card_i (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) : ∀ X ∈ Δ i, Nat.card X = 2 :=
  fun _ hX => hM.card _ (hM.mem_of_mem hX)

variable [Finite V] [Module (ZMod 2) (Additive V)]

theorem map_g31G_i (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) :
    (g31G Gm (Δ i)).map linAutHom = Subgroup.closure (gens (vecs (Δ i)) (forms Gm)) :=
  map_g31G hM.exp (hM.card_i i)

theorem mem_g31V_iff_i (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) {v : V} :
    v ∈ g31V (Δ i) ↔ Additive.ofMul v ∈ Submodule.span (ZMod 2) (vecs (Δ i)) :=
  mem_g31V_iff hM.exp (hM.card_i i)

omit [Finite V] in
theorem map_mem_vecs (hM : MulHyp Gm Δ₀ Δ) (i : Fin s) {g : MulAut V}
    (hg : g ∈ g31G Gm Δ₀) {w : Additive V} (hw : w ∈ vecs (Δ i)) :
    linAutHom g w ∈ vecs (Δ i) := by
  refine ⟨?_, ?_⟩
  · rw [linAutHom_apply]
    simpa using hw.1
  · rw [linAutHom_apply, toMul_ofMul, ← map_zpowers_mulAut]
    exact hM.ginv i _ hw.2 g hg

theorem orbHyp (hM : MulHyp Gm Δ₀ Δ) :
    OrbHyp (Gm.map linAutHom) (vecs Δ₀) (forms Gm) (fun i => vecs (Δ i)) := by
  have hG₀ := map_g31G hM.exp (Gm := Gm) hM.card
  refine ⟨hyp_vecs hM.exp hM.inv hM.trans, O2_of_pCoreOf hM.O2, fun w hw => ?_, ?_, ?_, ?_, ?_⟩
  · have h := hM.rel _ hw.2
    rw [hM.O2, inf_bot_eq, Subgroup.relIndex_bot_left, card_transvGroup hM.exp hw.1] at h
    by_contra hlt
    have : 2 ^ finrank (ZMod 2) (forms Gm (Additive.ofMul (Additive.toMul w))) ≤ 2 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) (by change finrank (ZMod 2) (forms Gm w) ≤ 1; omega)
    omega
  · intro i j hij
    refine Set.disjoint_left.2 fun w hwi hwj => ?_
    exact Set.disjoint_left.1 (hM.disj i j hij) hwi.2 hwj.2
  · ext w
    simp only [Set.mem_iUnion, vecs, Set.mem_ofPred_eq, ← hM.union]
    constructor
    · rintro ⟨i, h1, h2⟩
      exact ⟨h1, i, h2⟩
    · rintro ⟨h1, i, h2⟩
      exact ⟨i, h1, h2⟩
  · intro i w hw g' hg'
    rw [← hG₀] at hg'
    obtain ⟨g, hg, rfl⟩ := hg'
    exact hM.map_mem_vecs i hg hw
  · intro i w hw w' hw'
    obtain ⟨g, hg, hgX⟩ := hM.gtrans i _ hw.2 _ hw'.2
    refine ⟨linAutHom g, hG₀ ▸ ⟨g, hg, rfl⟩, ?_⟩
    rw [map_zpowers_mulAut] at hgX
    have := eq_of_zpowers_eq hM.exp (fun h => hw.1 ((MulEquiv.map_eq_one_iff g).1 h)) hgX
    rw [linAutHom_apply, this, ofMul_toMul]

end MulHyp

end CFSG.Quasithin.G31
