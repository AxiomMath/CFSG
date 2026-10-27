module

public import CFSG.Quasithin.EmptyFaithful.S151S9E
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsU33Abs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.Setup.X6

namespace GoldC3

open CFSG.QuasithinUnique.Vol2Native.L239 (HasChi0Block)
open CFSG.QuasithinUnique.Vol2Native.L239.Lie (ParabolicFacts)
open CFSG.QuasithinUnique.Vol2Native.L239.U33 (Witness)

@[expose] def BlockFree {X : Type} [Group X] (P : Subgroup X) : Prop :=
  (∃ Q : Subgroup X, ParabolicFacts P Q) ∨ Witness P

theorem BlockFree.map {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X'] {P : Subgroup X}
    (h : BlockFree P) (f : X →* X') (hf : Function.Injective f) : BlockFree (P.map f) := by
  rcases h with ⟨Q, hQ⟩ | hW
  · exact Or.inl ⟨Q.map f, hQ.map f hf⟩
  · exact Or.inr (hW.map f hf)

theorem BlockFree.charTwo {X : Type} [Group X] [Finite X] {P : Subgroup X} (h : BlockFree P) :
    CharTwo P := by
  rcases h with ⟨Q, hQ⟩ | hW
  · exact hQ.charTwo
  · exact hW.charTwo

theorem BlockFree.not_hasChi0Block {X : Type} [Group X] [Finite X] {P : Subgroup X}
    (h : BlockFree P) : ¬ HasChi0Block P := by
  rcases h with ⟨Q, hQ⟩ | hW
  · exact hQ.not_hasChi0Block
  · exact hW.not_hasChi0Block

theorem le_centralizer_centerOf {X : Type} [Group X] (U : Subgroup X) :
    U ≤ Subgroup.centralizer (centerOf U : Set X) := fun t ht =>
  Subgroup.mem_centralizer_iff.2 fun _ hz => (Subgroup.mem_centralizer_iff.1 hz.2 t ht).symm

structure C3Facts (X : Type) [Group X] (U P : Subgroup X) : Prop where
  le : U ≤ P
  card : Nat.card P = 3 * Nat.card U
  not_normal : ¬ P ≤ Subgroup.normalizer (U : Set X)
  not_centralizes : ¬ P ≤ Subgroup.centralizer (centerOf U : Set X)
  maximal : IsMaxSubgroupIn ⊤ (P ⊔ Subgroup.normalizer (U : Set X))
  blockFree : BlockFree P
  inv : ∀ α : MulAut X, U.map α.toMonoidHom = U → P.map α.toMonoidHom = P
  cent : Subgroup.normalizer (U : Set X) ≤ Subgroup.centralizer (centerOf U : Set X)
  norm : Subgroup.normalizer (U : Set X) ≤ U ∨
    ((∀ α : MulAut X, (∃ a : ℕ, α ^ 2 ^ a = 1) → ∃ g : X, ∀ x, α x = g * x * g⁻¹) ∧
      ∀ g : X, (∀ x : X, x * g = g * x) → g = 1)

theorem C3Facts.map {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X'] {U P : Subgroup X}
    (h : C3Facts X U P) (e : X ≃* X') :
    C3Facts X' (U.map e.toMonoidHom) (P.map e.toMonoidHom) where
  le := Subgroup.map_mono h.le
  card := by
    rw [Subgroup.card_map_of_injective e.injective, Subgroup.card_map_of_injective e.injective]
    exact h.card
  not_normal := by
    rw [← Subgroup.map_equiv_normalizer_eq U e]
    intro hle
    exact h.not_normal ((Subgroup.map_le_map_iff_of_injective e.injective).1 hle)
  not_centralizes := by
    rw [centerOf_map_equiv e U, centralizer_map_equiv e (centerOf U)]
    intro hle
    exact h.not_centralizes ((Subgroup.map_le_map_iff_of_injective e.injective).1 hle)
  maximal := by
    have h1 := isMaxSubgroupIn_map e h.maximal
    rwa [Subgroup.map_sup, Subgroup.map_equiv_normalizer_eq] at h1
  blockFree := h.blockFree.map e.toMonoidHom e.injective
  inv := by
    intro α' hα'
    set α : MulAut X := e.trans (α'.trans e.symm) with hα
    have hαU : U.map α.toMonoidHom = U := by
      have h1 := hα'
      rw [map_comm_equiv] at h1
      exact Subgroup.map_injective (f := e.toMonoidHom) e.injective h1
    have h2 := h.inv α hαU
    rw [map_comm_equiv, ← hα, h2]
  cent := by
    rw [← Subgroup.map_equiv_normalizer_eq, centerOf_map_equiv e U,
      centralizer_map_equiv e (centerOf U)]
    exact Subgroup.map_mono h.cent
  norm := by
    rcases h.norm with hN | ⟨hout, hZ⟩
    · left
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hN
    · right
      refine ⟨fun α' ⟨a, ha⟩ => ?_, fun g' hg' => ?_⟩
      · obtain ⟨g, hg⟩ := hout ((MulAut.congr e).symm α')
          ⟨a, by rw [← map_pow, ha, map_one]⟩
        refine ⟨e g, fun x' => ?_⟩
        have h1 := hg (e.symm x')
        rw [MulAut.congr_symm_apply] at h1
        have h2 := congrArg e h1
        simpa only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, map_mul, map_inv] using h2
      · have hg : e.symm g' = 1 := hZ (e.symm g') fun x => by
          have h1 := hg' (e x)
          apply e.injective
          simpa using h1
        simpa using congrArg e hg

@[expose] def HasC3Data (X : Type) [Group X] (U : Subgroup X) : Prop :=
  ∃ P : Subgroup X, C3Facts X U P

theorem HasC3Data.map {X X' : Type} [Group X] [Group X'] [Finite X] [Finite X'] {U : Subgroup X}
    (h : HasC3Data X U) (e : X ≃* X') : HasC3Data X' (U.map e.toMonoidHom) := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P.map e.toMonoidHom, hP.map e⟩

theorem HasC3Data.of_isSylow {X : Type} [Group X] [Finite X] {U₀ U : Subgroup X}
    (h₀ : HasC3Data X U₀) (hU₀ : IsSylowTwoOf U₀ ⊤) (hU : IsSylowTwoOf U ⊤) :
    HasC3Data X U := by
  obtain ⟨k, -, hk⟩ := (isSylowTwoOf_iff_isSylowOf.1 hU₀).exists_mem_conj
    (isSylowTwoOf_iff_isSylowOf.1 hU)
  have hconj : U₀.map (MulAut.conj k).toMonoidHom = U := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have := h₀.map (MulAut.conj k)
  rwa [hconj] at this

end GoldC3

end CFSG.Quasithin
