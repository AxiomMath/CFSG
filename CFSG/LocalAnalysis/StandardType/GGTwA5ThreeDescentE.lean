module

public import CFSG.LocalAnalysis.StandardType.GGTBTorAIndUFourTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem twd_automizer_transport {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    {N : ℕ}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hind : ∀ a ∈ A, ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (a l))
    {A₁ : Subgroup (MulAut R)} (hA₁ : A₁ = TypeA.inducedSub ψ A) {M : CoxeterMatrix (Fin N)}
    (n : Fin N → L') (m : Fin N → R) (hnm : ∀ k, ψ (n k) = m k)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hm : ∀ k, MulAut.conj (m k) ∈ Subgroup.normalizer (A₁ : Set (MulAut R)))
    (h : ggAutomizer (MulAut.conj : R →* MulAut R).range A₁ =
        Subgroup.closure (Set.range fun k => ggConjAut A₁ (hm k)) ∧
      ∃ e : M.Group ≃* ↥(ggAutomizer (MulAut.conj : R →* MulAut R).range A₁),
        ∀ k, (e (M.simple k) : MulAut ↥A₁) = ggConjAut A₁ (hm k)) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
        Subgroup.closure (Set.range fun k => ggConjAut A (hn k)) ∧
      ∃ e : M.Group ≃* ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
        ∀ k, (e (M.simple k) : MulAut ↥A) = ggConjAut A (hn k) := by
  subst hA₁
  obtain rfl : m = fun k => ψ (n k) := funext fun k => (hnm k).symm
  have hmap := map_ggAutomizer_inducedSub hψ hker hperf hind
  have hgg : ∀ k, MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hind).symm
      (ggConjAut (TypeA.inducedSub ψ A) (hm k)) = ggConjAut A (hn k) := fun k =>
    mulAutCongr_ggConjAut hψ hker hperf hind (hn k) (hm k)
  obtain ⟨h1, e, he⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← hmap, h1, MonoidHom.map_closure]
    congr 1
    ext φ
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨k, (hgg k).symm⟩
    · rintro ⟨k, rfl⟩
      exact ⟨_, ⟨k, rfl⟩, hgg k⟩
  · let E : ↥(ggAutomizer (MulAut.conj : R →* MulAut R).range (TypeA.inducedSub ψ A)) ≃*
        ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A) :=
      ((ggAutomizer (MulAut.conj : R →* MulAut R).range (TypeA.inducedSub ψ A)).equivMapOfInjective
        (MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hind).symm).toMonoidHom
        (fun x y hxy => (MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hind).symm).injective
          hxy)).trans (MulEquiv.subgroupCongr hmap)
    have hE : ∀ φ : ↥(ggAutomizer (MulAut.conj : R →* MulAut R).range
        (TypeA.inducedSub ψ A)), (E φ : MulAut ↥A) =
        MulAut.congr (TypeA.inducedSubEquiv hψ hker hperf hind).symm
          (φ : MulAut ↥(TypeA.inducedSub ψ A)) := by
      intro φ
      rfl
    refine ⟨e.trans E, fun k => ?_⟩
    rw [MulEquiv.trans_apply, hE, he k]
    exact hgg k

theorem twd_clause16 {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (w₁ : GGTorusTorWit 3 N (L' ⧸ U63TB.twoSub ψ.ker hker) (U63TB.redSub hker hAle).range)
    (hw₁ : w₁.Holds C M)
    (n : Fin N → L') (hnmk : ∀ k, (n k : L' ⧸ U63TB.twoSub ψ.ker hker) = w₁.n k)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
        Subgroup.closure (Set.range fun k => ggConjAut A (hn k)) ∧
      ∃ e : M.Group ≃*
          ↥(ggAutomizer (MulAut.conj : L' →* MulAut L').range A),
        ∀ k, (e (M.simple k) : MulAut ↥A) = ggConjAut A (hn k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h16, h17⟩ := hw₁
  have hZc : (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)).ker ≤ Subgroup.center L' := by
    rw [QuotientGroup.ker_mk']
    exact U63TB.twoSub_le_center hker
  have hind : ∀ a ∈ A, ∃ φ : MulAut (L' ⧸ U63TB.twoSub ψ.ker hker),
      ∀ l, φ (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker) l) =
        QuotientGroup.mk' (U63TB.twoSub ψ.ker hker) (a l) := fun a ha =>
    ⟨U63TB.redAut (U63TB.twoSub ψ.ker hker) ⟨a, hAle ha⟩, fun l =>
      U63TB.redAut_mk (U63TB.twoSub ψ.ker hker) ⟨a, hAle ha⟩ l⟩
  have hA₁ : (U63TB.redSub hker hAle).range =
      TypeA.inducedSub (QuotientGroup.mk' (U63TB.twoSub ψ.ker hker)) A := by
    ext φ
    constructor
    · rintro ⟨⟨a, ha⟩, rfl⟩
      exact ⟨a, ha, fun l => U63TB.redSub_mk hker hAle ⟨a, ha⟩ l⟩
    · rintro ⟨a, ha, hφ⟩
      refine ⟨⟨a, ha⟩, ?_⟩
      ext x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
      rw [U63TB.redSub_mk]
      exact (hφ l).symm
  exact twd_automizer_transport (QuotientGroup.mk'_surjective _) hZc hperf hind hA₁ n w₁.n hnmk
    hn w₁.hn ⟨h16, h17⟩

end CFSG.StandardType

end
