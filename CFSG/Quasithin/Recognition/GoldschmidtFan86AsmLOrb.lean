module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62Lbl
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace AsmL

variable (F : FanTree Γ G) (L : ZLab Γ G)

include F

theorem exists_conj {α v : V} (hα : valence Γ α = 5) (hv : valence Γ v = 5) :
    ∃ g : G, g • α = v ∧ L.z v = g * L.z α * g⁻¹ := by
  obtain ⟨g, hg⟩ := P62.exists_smul_of_valence_eq F (u := α) (w := v) (by rw [hv, hα])
  exact ⟨g, hg, by rw [← hg]; exact L.equivariant g α hα⟩

omit F in
theorem cinv_lab {α : V} (hα : valence Γ α = 5) : L.z α ∈ Cinv G α :=
  P62.cinv_iff.2 (L.isCentral α hα)

theorem zSet_eq {α : V} (hα : valence Γ α = 5) (k : ℕ) :
    L.zSet k α = zBall Γ α (L.z α) k := by
  ext w
  constructor
  · rintro ⟨δ, hd, hδ, rfl⟩
    obtain ⟨g, hg, hz⟩ := exists_conj F L hα hδ
    exact ⟨g, by rw [hg]; exact hd, hz⟩
  · rintro ⟨g, hd, rfl⟩
    refine ⟨g • α, hd, ?_, (L.equivariant g α hα).symm⟩
    rw [F.valence_smul_eq g α]
    exact hα

omit L in
theorem valence_of_dist_two {α l : V} (hα : valence Γ α = 5) (h : Γ.dist α l = 2) :
    valence Γ l = 5 := by
  obtain ⟨ν, hν⟩ := P62.exists_br F h
  exact (P62.Br.valence F hα hν).2

end AsmL

end CFSG.Quasithin.Fan86
