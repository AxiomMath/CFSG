module

public import CFSG.RankThree.GF2n.Tim81.TIQuotient

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

theorem conjSubgroup_le_xOf_of_mem {V H : Subgroup G} {y : G} (hy : y ∈ H) :
    conjSubgroup y V ≤ Tim79a.xOf V H :=
  Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf (V := V) (H := H) (h := y) hy)

namespace RootHyp

theorem conjSubgroup_le_kOf_of_mem (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {y : G} (hy : y ∈ H) :
    conjSubgroup y V ≤ kOf V H :=
  (conjSubgroup_le_xOf_of_mem (V := V) (H := H) hy).trans (xOf_le_kOf h hPH hVH)

theorem kOf_le_centralizer_conjSubgroup_of_mem {V H : Subgroup G} {y : G} (hy : y ∈ H) :
    kOf V H ≤ Subgroup.centralizer (conjSubgroup y V : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact Subgroup.mem_centralizer_iff.mp (mem_kOf_iff.mp hk).2 v
    (conjSubgroup_le_xOf_of_mem (V := V) (H := H) hy hv)

theorem kOf_le_conjSubgroup_of_mem (h : RootHyp M V) {y : G} (hy : y ∈ H) :
    kOf V H ≤ conjSubgroup y M := by
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.toHyp.ne_bot
  have hv1' : v ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  have hvV' : MulAut.conj y v ∈ conjSubgroup y V :=
    Subgroup.mem_map.mpr ⟨v, hvV, rfl⟩
  have hv1'' : MulAut.conj y v ≠ 1 := fun h1 =>
    hv1' ((MulAut.conj y).injective (by simpa using h1))
  intro k hk
  have hcomm : k * (MulAut.conj y v) = (MulAut.conj y v) * k :=
    (Subgroup.mem_centralizer_iff.mp
      (kOf_le_centralizer_conjSubgroup_of_mem (V := V) (H := H) hy hk)
      (MulAut.conj y v) hvV').symm
  have hk_N : k ∈ Subgroup.normalizer (conjSubgroup y V) :=
    Tim77.mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup h.toHyp.ti y)
      hvV' hv1'' hcomm
  rw [normalizer_conjSubgroup, h.toHyp.normalizer_eq] at hk_N
  exact hk_N

theorem kOf_le_normalizer_conjSubgroup_Pc_of_mem (h : RootHyp M V) {y : G} (hy : y ∈ H) :
    kOf V H ≤ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) := by
  have hMN : conjSubgroup y M ≤ Subgroup.normalizer (conjSubgroup y (Pc M V) : Set G) := by
    rw [normalizer_conjSubgroup]
    exact Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) h.toHyp.le_normalizer_Pc
  exact (kOf_le_conjSubgroup_of_mem h hy).trans hMN

theorem exists_mem_conj_eq_of_eq_sup (h : RootHyp M V) (hPH : Pc M V ≤ H) {h₀ : G}
    (hH : H = Pc M V ⊔ conjSubgroup h₀ (Pc M V)) :
    ∃ y ∈ H, conjSubgroup h₀ (Pc M V) = conjSubgroup y (Pc M V) ∧
      conjSubgroup h₀ V = conjSubgroup y V ∧
      H = Pc M V ⊔ conjSubgroup y (Pc M V) := by
  have hgH : conjSubgroup h₀ (Pc M V) ≤ H := by rw [hH]; exact le_sup_right
  obtain ⟨y, hyH, hPy, hVy⟩ := h.toHyp.exists_mem_conj_eq_of_conj_Pc_le hPH hgH
  exact ⟨y, hyH, hPy, hVy, by rw [hH, hPy]⟩

end RootHyp

end CFSG.RankThree.GF2n.Tim81
