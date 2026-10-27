module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AmalgamKernel
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.AmalgamShapes

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.Monster.GMS CFSG.AGLEmbedding

theorem relIndex_ne_zero_of_finite {G : Type} [Group G] [Finite G] (K H : Subgroup G) :
    K.relIndex H ≠ 0 :=
  Subgroup.index_ne_zero_of_finite (H := K.subgroupOf H)

theorem coprime_of_lt {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hnp : n < p) : Nat.Coprime n p :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => by
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h
    omega)

theorem kernelTrivialAt_of_asegAmalgam {V : Type*} {Γ : SimpleGraph V} {G : Type} [Group G]
    [Finite G] [MulAction G V] {a y z : G} (D : TitsData Γ G Bool) {p : ℕ} [hpp : Fact p.Prime]
    (hp2 : p ≠ 2) (ha : a * a = 1) (a1 : a ≠ 1) (y1 : y ≠ 1) (hne : a ≠ y)
    (hXv : D.Xv = Subgroup.centralizer ({a} : Set G))
    (hXe : ∀ g, g ∈ D.Xe ↔ (g * a * g⁻¹ = a ∧ g * y * g⁻¹ = y) ∨
      (g * a * g⁻¹ = y ∧ g * y * g⁻¹ = a))
    (hXt0 : D.Xt false = Subgroup.normalizer ({a, y, a * y} : Set G))
    (hXt1 : D.Xt true = Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.normalizer ({a, y, a * y * z} : Set G))
    (hdec : ∀ g ∈ Subgroup.normalizer ({a, y, a * y} : Set G), ∃ k ∈ cent₂ a y,
      ∃ w ∈ Subgroup.normalizer ({a, y, a * y} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        g = k * w)
    (hCa : PerfectCoreCell p (Subgroup.centralizer ({a} : Set G)))
    (hCz : PerfectCoreCell p (Subgroup.centralizer ({z} : Set G)))
    (hK : PerfectCoreOf p (cent₂ a y))
    (hJ : PerfectCoreOf p (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({z} : Set G))) :
    KernelTrivialAt G p := by
  have hp3 : 3 ≤ p := by have := hpp.out.two_le; omega
  have hK_eq : D.Xv ⊓ D.Xe = cent₂ a y := by rw [hXv]; exact cent_inf_edge hne hXe
  have hZ : D.Xt true ≤ Subgroup.centralizer ({z} : Set G) := by rw [hXt1]; exact inf_le_left
  have hKle : cent₂ a y ≤ Subgroup.centralizer ({a} : Set G) := inf_le_left
  refine kernelTrivialAt_of_amalgamCells D hp2 (Subgroup.centralizer ({z} : Set G)) hZ
    (hXv ▸ hCa) hCz (hK_eq ▸ hK) (by rw [hXv]; exact hJ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hK_eq]; exact edge_normal hXe
  · rw [hK_eq]
    exact coprime_of_lt hpp.out (relIndex_ne_zero_of_finite _ _) (by
      have := edge_relIndex_le hne hXe
      omega)
  · rw [hK_eq, hXt0]; exact cent₂_le_normalizer_triple
  · rw [hK_eq, hXt0]; exact triple_normal
  · rw [hK_eq, hXt0]; exact Or.inr hdec
  · rw [hK_eq, hXt0, hXv]
    intro g hg
    obtain ⟨hga, hgt⟩ := hg
    have : g * a * g⁻¹ = a := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hga
      calc g * a * g⁻¹ = a * g * g⁻¹ := by rw [this]
        _ = a := by group
    exact triple_sq_mem ha hne rfl this hgt
  · rw [hK_eq]
    intro g hg
    exact edge_sq_mem hXe hg.1
  · rw [hK_eq, hXt1]; exact cent₂_inf_cent_le_xt1
  · rw [hK_eq, hXt1]
    intro g hg
    exact ⟨edge_sq_mem hXe hg.1, Subgroup.pow_mem _ hg.2.1 2⟩

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
