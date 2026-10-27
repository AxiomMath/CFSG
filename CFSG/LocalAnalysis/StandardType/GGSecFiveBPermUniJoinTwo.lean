module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocks

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.UnitaryFlag

variable {G : Type} [Group G] {p n f : ℕ} {K : Type} [Field K] {Bs X : Subgroup G}
  {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
  {σ : ↥(unitarySU 2 f K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}

private theorem card_map_eq_and_not_mem {S : Finset (Fin n)} {i0 j0 : Fin n}
    (hS : S.card = 3 ∧ ¬ (π.symm i0 ∈ S ∧ π.symm j0 ∈ S)) :
    (S.map π.toEmbedding).card = 3 ∧
      (i0 ∉ S.map π.toEmbedding ∨ j0 ∉ S.map π.toEmbedding) := by
  refine ⟨by rw [Finset.card_map, hS.1], ?_⟩
  simp only [Finset.mem_map_equiv]
  exact not_and_or.mp hS.2

theorem GGSecFiveBPermUniLFrame.le_sup_map_conj_of_triples_of_covariance
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) {i0 j0 : Fin n}
    (hgen : (⨆ (S : Finset (Fin n)) (_ : S.card = 3 ∧ ¬ (π.symm i0 ∈ S ∧ π.symm j0 ∈ S)),
      TableBUE.blockSU (K := K) (n := f) S) = ⊤)
    (hblk : ∀ S : Finset (Fin n), S.card = 3 →
      (TableBUE.blockSU (K := K) (n := f) S).map σ ≤ ggBlockComm Bs eta (π '' (S : Set (Fin n))))
    {g : G}
    (hcov : ∀ S : Set (Fin n), (ggBlockComm Bs eta S).map (MulAut.conj g).toMonoidHom =
      ggBlockComm Bs eta ((Equiv.swap i0 j0) '' S))
    {M : Subgroup G}
    (hM : ∀ S : Finset (Fin n), S.card = 3 → i0 ∉ S →
      ggBlockComm Bs eta (S : Set (Fin n)) ≤ M) :
    X ≤ M ⊔ M.map (MulAut.conj g).toMonoidHom := by
  have hX : X = (⊤ : Subgroup ↥(unitarySU 2 f K n)).map σ := by
    rw [← hF.1, MonoidHom.range_eq_map]
  rw [hX, ← hgen, Subgroup.map_iSup]
  refine iSup_le fun S => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hS => (hblk S hS.1).trans ?_
  obtain ⟨hcard, hT⟩ := card_map_eq_and_not_mem (π := π) hS
  have hset : π '' (S : Set (Fin n)) = ((S.map π.toEmbedding : Finset (Fin n)) : Set (Fin n)) := by
    simp
  rw [hset]
  by_cases hi : i0 ∈ S.map π.toEmbedding
  · have hj : j0 ∉ S.map π.toEmbedding := hT.resolve_left (not_not.mpr hi)
    set T := (S.map π.toEmbedding).map (Equiv.swap i0 j0).toEmbedding
    have hTcard : T.card = 3 := by rw [Finset.card_map, hcard]
    have hiT : i0 ∉ T := by
      rw [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_left]
      exact hj
    have himg : (Equiv.swap i0 j0 : Equiv.Perm (Fin n)) '' (T : Set (Fin n)) =
        ((S.map π.toEmbedding : Finset (Fin n)) : Set (Fin n)) := by
      ext x
      simp [T, Equiv.swap_apply_self]
    rw [← himg, ← hcov]
    exact le_sup_of_le_right (Subgroup.map_mono (hM T hTcard hiT))
  · exact le_sup_of_le_left (hM _ hcard hi)

theorem GGSecFiveBPermUniLFrame.le_sup_map_conj_of_triples
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) {i0 j0 : Fin n}
    (hgen : (⨆ (S : Finset (Fin n)) (_ : S.card = 3 ∧ ¬ (π.symm i0 ∈ S ∧ π.symm j0 ∈ S)),
      TableBUE.blockSU (K := K) (n := f) S) = ⊤)
    (hblk : ∀ S : Finset (Fin n), S.card = 3 →
      (TableBUE.blockSU (K := K) (n := f) S).map σ ≤ ggBlockComm Bs eta (π '' (S : Set (Fin n))))
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 j0))
    {M : Subgroup G}
    (hM : ∀ S : Finset (Fin n), S.card = 3 → i0 ∉ S →
      ggBlockComm Bs eta (S : Set (Fin n)) ≤ M) :
    X ≤ M ⊔ M.map (MulAut.conj g).toMonoidHom :=
  hF.le_sup_map_conj_of_triples_of_covariance hgen hblk
    (fun S => ggBlockComm_map_conj (S := S) hg hτ) hM

theorem GGSecFiveBPermUniLFrame.sup_map_conj_eq_of_triples
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) {i0 j0 : Fin n}
    (hgen : (⨆ (S : Finset (Fin n)) (_ : S.card = 3 ∧ ¬ (π.symm i0 ∈ S ∧ π.symm j0 ∈ S)),
      TableBUE.blockSU (K := K) (n := f) S) = ⊤)
    (hblk : ∀ S : Finset (Fin n), S.card = 3 →
      (TableBUE.blockSU (K := K) (n := f) S).map σ ≤ ggBlockComm Bs eta (π '' (S : Set (Fin n))))
    {g : G} (hgX : g ∈ X) (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (hτ : MulAut.congr eta (ggConjAut Bs hg) = SpCoord.permAut (Equiv.swap i0 j0))
    {M : Subgroup G}
    (hM : ∀ S : Finset (Fin n), S.card = 3 → i0 ∉ S →
      ggBlockComm Bs eta (S : Set (Fin n)) ≤ M) :
    M ⊔ M.map (MulAut.conj g).toMonoidHom = X ⊔ M := by
  apply le_antisymm
  · refine sup_le le_sup_right ?_
    calc M.map (MulAut.conj g).toMonoidHom ≤ (X ⊔ M).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono le_sup_right
      _ = X ⊔ M := Subgroup.mem_normalizer_iff_map_conj_eq.mp
          (Subgroup.le_normalizer (Subgroup.mem_sup_left hgX))
  · exact sup_le (hF.le_sup_map_conj_of_triples hgen hblk hg hτ hM) le_sup_left

end CFSG.StandardType

end
