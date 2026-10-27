module

public import CFSG.Quasithin.Background.E1SolvAux
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem weakClosure_weakClosure (X : Subgroup G) (Ω : Set (Subgroup G)) :
    E1.weakClosure (E1.weakClosure X Ω) Ω = E1.weakClosure X Ω := by
  refine le_antisymm E1.weakClosure_le ?_
  refine iSup₂_le fun A hA => iSup_le fun hAX => ?_
  exact E1.le_weakClosure hA (E1.le_weakClosure hA hAX)

theorem weakClosure_mono {X Y : Subgroup G} (Ω : Set (Subgroup G)) (h : X ≤ Y) :
    E1.weakClosure X Ω ≤ E1.weakClosure Y Ω := by
  refine iSup₂_le fun A hA => iSup_le fun hAX => ?_
  exact E1.le_weakClosure hA (hAX.trans h)

theorem mem_normalizer_weakClosure_of_isInvColl {H T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) {x : G} (hxH : x ∈ H)
    (hx : ∀ w ∈ E1.weakClosure T Ω, x * w * x⁻¹ ∈ T) :
    x ∈ normalizer (E1.weakClosure T Ω : Set G) := by
  apply E1.mem_normalizer_of_conj_mem
  have hle : E1.weakClosure T Ω ≤ (E1.weakClosure T Ω).comap (MulAut.conj x).toMonoidHom := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    intro a ha
    rw [Subgroup.mem_comap]
    have h1 : A1b.conjSub x A ∈ Ω := hΩ.conj A hA x hxH
    have h2 : A1b.conjSub x A ≤ T := by
      intro y hy
      rw [A1b.mem_conjSub_iff] at hy
      have h3 : x * (x⁻¹ * y * x) * x⁻¹ ∈ T := hx _ (E1.le_weakClosure hA hAT hy)
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rwa [e] at h3
    exact E1.le_weakClosure h1 h2 (A1b.mem_conjSub_of_mem ha)
  intro w hw
  exact hle hw

theorem le_normalizer_weakClosure_of_isInvColl {H T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hTH : T ≤ H) :
    T ≤ normalizer (E1.weakClosure T Ω : Set G) := by
  intro t ht
  apply mem_normalizer_weakClosure_of_isInvColl hΩ (hTH ht)
  intro w hw
  exact T.mul_mem (T.mul_mem ht (E1.weakClosure_le hw)) (T.inv_mem ht)

theorem conjSub_weakClosure_le {H : Subgroup G} {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl H Ω)
    {g : G} (hg : g ∈ H) (X : Subgroup G) :
    A1b.conjSub g (E1.weakClosure X Ω) ≤ E1.weakClosure (A1b.conjSub g X) Ω := by
  unfold A1b.conjSub
  rw [Subgroup.map_le_iff_le_comap]
  refine iSup₂_le fun A hA => iSup_le fun hAX => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact E1.le_weakClosure (hΩ.conj A hA g hg) (A1b.conjSub_mono g hAX)

theorem conjSub_weakClosure {H : Subgroup G} {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl H Ω)
    {g : G} (hg : g ∈ H) (X : Subgroup G) :
    A1b.conjSub g (E1.weakClosure X Ω) = E1.weakClosure (A1b.conjSub g X) Ω := by
  refine le_antisymm (conjSub_weakClosure_le hΩ hg X) ?_
  have h1 := conjSub_weakClosure_le hΩ (H.inv_mem hg) (A1b.conjSub g X)
  rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one] at h1
  have h2 := A1b.conjSub_mono g h1
  rwa [← A1b.conjSub_mul, mul_inv_cancel, A1b.conjSub_one] at h2

theorem isInvColl_restrict {H N : Subgroup G} {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl H Ω)
    (hNH : N ≤ H) : E1.IsInvColl N {B | B ∈ Ω ∧ B ≤ N} where
  le B hB := hB.2
  isElemAbelian B hB := hΩ.isElemAbelian B hB.1
  conj B hB n hn := by
    refine ⟨hΩ.conj B hB.1 n (hNH hn), fun y hy => ?_⟩
    rw [A1b.mem_conjSub_iff] at hy
    have h1 : n⁻¹ * y * n ∈ N := hB.2 hy
    have h2 : n * (n⁻¹ * y * n) * n⁻¹ ∈ N := N.mul_mem (N.mul_mem hn h1) (N.inv_mem hn)
    simpa [mul_assoc] using h2

theorem weakClosure_restrict {X N : Subgroup G} {Ω : Set (Subgroup G)} (hXN : X ≤ N) :
    E1.weakClosure X {B | B ∈ Ω ∧ B ≤ N} = E1.weakClosure X Ω := by
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun A hA => iSup_le fun hAX => ?_
    exact E1.le_weakClosure hA.1 hAX
  · refine iSup₂_le fun A hA => iSup_le fun hAX => ?_
    exact E1.le_weakClosure ⟨hA, hAX.trans hXN⟩ hAX

end CFSG.LocalAnalysis.WeakClosure81
