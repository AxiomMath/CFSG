module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoChartHubBlk

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}
variable {F0 : Type} [Field F0] [Finite F0] [CharP F0 2]

private theorem qTwoChartHub_extendDomain_swap (ε0 : Fin m ↪ Fin (n + 1)) (i j : Fin m) :
    (Equiv.swap i j).extendDomain (Equiv.ofInjective ε0 ε0.injective) =
      Equiv.swap (ε0 i) (ε0 j) := by
  classical
  apply Equiv.ext
  intro y
  by_cases hy : y ∈ Set.range ε0
  · obtain ⟨k, hk⟩ := hy
    rw [← hk]
    change (Equiv.swap i j).extendDomain (Equiv.ofInjective ε0 ε0.injective)
        (Equiv.ofInjective ε0 ε0.injective k) = Equiv.swap (ε0 i) (ε0 j) (ε0 k)
    rw [Equiv.Perm.extendDomain_apply_image]
    change ε0 (Equiv.swap i j k) = Equiv.swap (ε0 i) (ε0 j) (ε0 k)
    rcases eq_or_ne k i with h | h
    · subst h
      rw [Equiv.swap_apply_left, Equiv.swap_apply_left]
    rcases eq_or_ne k j with h' | h'
    · subst h'
      rw [Equiv.swap_apply_right, Equiv.swap_apply_right]
    · rw [Equiv.swap_apply_of_ne_of_ne h h', Equiv.swap_apply_of_ne_of_ne]
      · intro hx
        exact h (ε0.injective hx)
      · intro hx
        exact h' (ε0.injective hx)
  · rw [Equiv.Perm.extendDomain_apply_not_subtype _ _ hy]
    exact (Equiv.swap_apply_of_ne_of_ne (fun h => hy ⟨i, h.symm⟩)
      (fun h => hy ⟨j, h.symm⟩)).symm

theorem qTwoChartHub_swap (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    {ψ : Su F0 2 1 m →* G} (hψ : QTwoOrdModel Bs L ψ) {ε0 : Fin m ↪ Fin (n + 1)}
    (hε0 : QTwoFrameMatch S ψ ε0)
    (hlifts : ∀ π : Equiv.Perm (Fin (n + 1)), ∃ g : G, QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g π)
    {blk : Finset (Fin (n + 1)) → Subgroup G} (hblk : qTwoChartHub_spec S ψ ε0 blk) :
    ∀ i j : Fin (n + 1), (j : ℕ) = (i : ℕ) + 1 → ∃ s ∈ blk {i, j},
      ∀ I : Finset (Fin (n + 1)), 2 ≤ I.card → I.card ≤ 4 →
        (blk I).map (MulAut.conj s).toMonoidHom = blk (I.map (Equiv.swap i j).toEmbedding) := by
  intro i j hij
  have hm : 5 ≤ m := S.hm
  let p : Fin m := ⟨0, by omega⟩
  let q : Fin m := ⟨1, by omega⟩
  have hpq : p ≠ q := by
    intro h
    have hval : (p : ℕ) = (q : ℕ) := congrArg Fin.val h
    have hp0 : (p : ℕ) = 0 := rfl
    have hq1 : (q : ℕ) = 1 := rfl
    omega
  have hab : ε0 p ≠ ε0 q := fun h => hpq (ε0.injective h)
  have hij' : i ≠ j := by
    rintro rfl
    omega
  obtain ⟨π, hπa, hπb⟩ := qTwoChartHub_exists_perm_pair hab hij'
  obtain ⟨g, hg⟩ := hlifts π
  let σ : Equiv.Perm (Fin m) := Equiv.swap p q
  obtain ⟨u, hu1, hu2⟩ := hε0 σ
  have hσeq : σ.extendDomain (Equiv.ofInjective ε0 ε0.injective) =
      Equiv.swap (ε0 p) (ε0 q) := by
    simpa [σ] using qTwoChartHub_extendDomain_swap ε0 p q
  rw [hσeq] at hu2
  have hgu : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA (g * ψ u)
      (π * Equiv.swap (ε0 p) (ε0 q)) :=
    qTwoChartHub_lifts_mul S hg hu2
  have hginv : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA g⁻¹ π⁻¹ :=
    qTwoChartHub_lifts_inv S hg
  have hs_lift' : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA (g * ψ u * g⁻¹)
      ((π * Equiv.swap (ε0 p) (ε0 q)) * π⁻¹) :=
    qTwoChartHub_lifts_mul S hgu hginv
  have hconjperm : (π * Equiv.swap (ε0 p) (ε0 q)) * π⁻¹ = Equiv.swap i j := by
    have h := Equiv.swap_apply_apply π (ε0 p) (ε0 q)
    rw [hπa, hπb] at h
    exact h.symm
  have hs_lift : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA (g * ψ u * g⁻¹) (Equiv.swap i j) := by
    rw [hconjperm] at hs_lift'
    exact hs_lift'
  have hTmap : ({p, q} : Finset (Fin m)).map ε0 =
      ({ε0 p, ε0 q} : Finset (Fin (n + 1))) := by
    simp
  have hTmap2 : ({ε0 p, ε0 q} : Finset (Fin (n + 1))).map π.toEmbedding = {i, j} := by
    simp only [Finset.map_insert, Finset.map_singleton]
    change insert (π (ε0 p)) {π (ε0 q)} = {i, j}
    rw [hπa, hπb]
  have hframe : qTwoFrameSet ε0 π ({p, q} : Finset (Fin m)) = {i, j} := by
    unfold qTwoFrameSet
    rw [hTmap, hTmap2]
  have hcard0 : ({p, q} : Finset (Fin m)).card = 2 := Finset.card_pair hpq
  have h2_0 : 2 ≤ ({p, q} : Finset (Fin m)).card := by simp [hcard0]
  have h4_0 : ({p, q} : Finset (Fin m)).card ≤ 4 := by simp [hcard0]
  have hblk0 : blk {i, j} = qTwoBlockOf ψ g ({p, q} : Finset (Fin m)) := by
    rw [← hframe]
    exact hblk (g := g) (π := π) (T := ({p, q} : Finset (Fin m))) hg h2_0 h4_0
  have hu_mem : u ∈ coordBlockSU F0 2 1 ({p, q} : Finset (Fin m)) := by
    rw [mem_coordBlockSU_iff]
    intro r c hrc
    have hentry : (((u : GL (Fin m) F0) : Matrix (Fin m) (Fin m) F0)) r c =
        if r = σ c then 1 else 0 := by
      have h := congrFun (hu1 c) r
      simpa [Matrix.mulVec_single_one, Pi.single_apply] using h
    rw [hentry]
    by_cases hc : c ∈ ({p, q} : Finset (Fin m))
    · have hr : r ∉ ({p, q} : Finset (Fin m)) := by
        rcases hrc with h | h
        · exact h
        · exact absurd hc h
      have hσc : σ c ∈ ({p, q} : Finset (Fin m)) := by
        have hcpq : c = p ∨ c = q := by simpa using hc
        rcases hcpq with rfl | rfl
        · have hp : σ p = q := by
            change (Equiv.swap p q) p = q
            rw [Equiv.swap_apply_left]
          rw [hp]; simp
        · have hq : σ q = p := by
            change (Equiv.swap p q) q = p
            rw [Equiv.swap_apply_right]
          rw [hq]; simp
      have hrne : r ≠ σ c := fun h => hr (h ▸ hσc)
      rw [if_neg hrne]
      have hrc' : r ≠ c := fun h => hr (h ▸ hc)
      rw [if_neg hrc']
    · have hσc : σ c = c := by
        have hcp : c ≠ p := fun h => hc (by rw [h]; simp)
        have hcq : c ≠ q := fun h => hc (by rw [h]; simp)
        change (Equiv.swap p q) c = c
        rw [Equiv.swap_apply_of_ne_of_ne hcp hcq]
      rw [hσc]
  have hs_mem : g * ψ u * g⁻¹ ∈ blk {i, j} := by
    rw [hblk0]
    change g * ψ u * g⁻¹ ∈ (coordBlockSU F0 2 1 ({p, q} : Finset (Fin m))).map
      ((MulAut.conj g).toMonoidHom.comp ψ)
    refine Subgroup.mem_map.mpr ⟨u, hu_mem, ?_⟩
    change (MulAut.conj g) (ψ u) = g * ψ u * g⁻¹
    rw [MulAut.conj_apply]
  refine ⟨g * ψ u * g⁻¹, hs_mem, ?_⟩
  intro I h2 h4
  have hIm : I.card ≤ m := by omega
  obtain ⟨π', T, hI, hTcard⟩ := qTwoChartHub_exists_frameSet ε0 hIm
  obtain ⟨g', hg'⟩ := hlifts π'
  have hT2 : 2 ≤ T.card := by rw [hTcard]; exact h2
  have hT4 : T.card ≤ 4 := by rw [hTcard]; exact h4
  have hblkI : blk I = qTwoBlockOf ψ g' T := by
    rw [← hI]
    exact hblk (g := g') (π := π') (T := T) hg' hT2 hT4
  have hs_lift_mul : QTwoLiftsPerm Bs (QTwoH L 𝒦) S.ρA ((g * ψ u * g⁻¹) * g')
      (Equiv.swap i j * π') :=
    qTwoChartHub_lifts_mul S hs_lift hg'
  calc
    (blk I).map (MulAut.conj (g * ψ u * g⁻¹)).toMonoidHom
        = (qTwoBlockOf ψ g' T).map (MulAut.conj (g * ψ u * g⁻¹)).toMonoidHom := by
          rw [hblkI]
    _ = qTwoBlockOf ψ ((g * ψ u * g⁻¹) * g') T :=
          qTwoChartHub_blockOf_conj ψ (g * ψ u * g⁻¹) g' T
    _ = blk (qTwoFrameSet ε0 (Equiv.swap i j * π') T) :=
          (hblk (g := (g * ψ u * g⁻¹) * g') (π := Equiv.swap i j * π') (T := T)
            hs_lift_mul hT2 hT4).symm
    _ = blk (I.map (Equiv.swap i j).toEmbedding) := by
          rw [qTwoChartHub_frameSet_mul ε0 (Equiv.swap i j) π' T, hI]

end CFSG.StandardType.QTwo

end
