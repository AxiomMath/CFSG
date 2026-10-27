module

public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem map_conj_mul (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      H.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

variable [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem stmt11_1_3_conj (h1113 : Stmt11_1_3) (h : Hyp11 G T L I n) {U₂ : Subgroup G}
    (hU₂ : IsVi T L I n 2 U₂) {x : G} (hx : x ∈ L) :
    quasithinIsCComponent (LOf L (U₂.map (MulAut.conj x).toMonoidHom))
        (Subgroup.normalizer ((U₂.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)) ∧
      ¬ LOf L (U₂.map (MulAut.conj x).toMonoidHom) ≤
        Subgroup.centralizer ((U₂.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ∧
      ∀ K : Subgroup G, quasithinIsCComponent K
          (Subgroup.normalizer ((U₂.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G)) →
        ¬ K ≤ Subgroup.centralizer ((U₂.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) →
        K = LOf L (U₂.map (MulAut.conj x).toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h1113 G T L I n U₂ h hU₂
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hx
  rw [← map_conj_lOf U₂ hxN, ← map_conj_normalizer, ← map_conj_centralizer]
  refine ⟨isCComponent_map_equiv _ h1, fun hle => h2 ?_, fun K hK hKC => ?_⟩
  · exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj x).injective).mp hle
  · have hKK := map_map_symm (MulAut.conj x).symm K
    rw [MulEquiv.symm_symm] at hKK
    have hK' := isCComponent_map_equiv (MulAut.conj x).symm hK
    rw [map_map_symm] at hK'
    have hKC' : ¬ K.map (MulAut.conj x).symm.toMonoidHom ≤
        Subgroup.centralizer (U₂ : Set G) := by
      intro hle
      apply hKC
      have := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hle
      rwa [hKK] at this
    rw [← h3 _ hK' hKC', hKK]

end CFSG.Quasithin.Vol2.Ch11.SecA
