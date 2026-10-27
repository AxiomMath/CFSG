module

public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.RankThree.PartOne.S12.Sec13Zero
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne CFSG.RankThree

variable {G : Type} [Group G]

theorem conjBy_eq_of_commute {w : G} {K : Subgroup G} (h : ∀ k ∈ K, w * k = k * w) :
    conjBy w K = K := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : w * k * w⁻¹ = k := by rw [h k hk]; group
    simpa [MulAut.conj_apply, this] using hk
  · intro hx
    refine ⟨x, hx, ?_⟩
    have : w * x * w⁻¹ = x := by rw [h x hx]; group
    simpa [MulAut.conj_apply] using this

theorem theta_conj_eq [Finite G] {p : ℕ} (hp : p.Prime) {b w : G} {I K : Subgroup G}
    (hI : I ∈ thetaComponentsAt p b) (hKI : K ≤ I) (hK : Group.IsPerfect K) (hK0 : K ≠ ⊥)
    (hw : Subgroup.zpowers (w * b * w⁻¹) = Subgroup.zpowers b) (hwK : conjBy w K = K) :
    conjBy w I = I := by
  have h1 : conjBy w I ∈ thetaComponentsAt p b := by
    rw [← thetaComponentsAt_eq_of_zpowers_eq p hw]
    exact conjBy_mem_thetaComponentsAt hp w b hI
  have hle : K ≤ conjBy w I := by
    rw [← hwK]
    exact Subgroup.map_mono hKI
  exact EmbeddingFixedResidual.eq_of_perfect_le_of_mem_thetaComponentsAt hp h1 hI hK0 hK hle hKI

theorem commute_of_inverted_odd {x t : G} {I : Subgroup G}
    (hx : x ∈ Subgroup.normalizer (I : Set G)) (ht : ∀ u ∈ I, t * u = u * t)
    (hinv : t * x * t⁻¹ = x⁻¹) (hodd : Odd (orderOf x)) : ∀ u ∈ I, x * u = u * x := by
  intro u hu
  have hxu : x * u * x⁻¹ ∈ I := (Subgroup.mem_normalizer_iff.mp hx u).mp hu
  have hxu' : x⁻¹ * u * x ∈ I := by
    have hx' : x⁻¹ ∈ Subgroup.normalizer (I : Set G) := Subgroup.inv_mem _ hx
    simpa using (Subgroup.mem_normalizer_iff.mp hx' u).mp hu
  have h1 : t * (x * u * x⁻¹) * t⁻¹ = x⁻¹ * u * x := by
    have e : t * (x * u * x⁻¹) * t⁻¹ = (t * x * t⁻¹) * (t * u * t⁻¹) * (t * x * t⁻¹)⁻¹ := by
      group
    rw [e, hinv, inv_inv, show t * u * t⁻¹ = u by rw [ht u hu]; group]
  have h2 : t * (x * u * x⁻¹) * t⁻¹ = x * u * x⁻¹ := by
    rw [ht _ hxu]
    group
  have h3 : x⁻¹ * u * x = x * u * x⁻¹ := h1.symm.trans h2
  have h4 : Commute (x ^ 2) u := by
    show x ^ 2 * u = u * x ^ 2
    have : x ^ 2 * u * (x ^ 2)⁻¹ = u := by
      calc x ^ 2 * u * (x ^ 2)⁻¹ = x * (x * u * x⁻¹) * x⁻¹ := by rw [pow_two]; group
        _ = x * (x⁻¹ * u * x) * x⁻¹ := by rw [h3]
        _ = u := by group
    calc x ^ 2 * u = x ^ 2 * u * (x ^ 2)⁻¹ * x ^ 2 := by group
      _ = u * x ^ 2 := by rw [this]
  obtain ⟨k, hk⟩ := hodd
  have hxk : (x ^ 2) ^ (k + 1) = x := by
    have : x ^ (orderOf x) = 1 := pow_orderOf_eq_one x
    calc (x ^ 2) ^ (k + 1) = x ^ (2 * k + 2) := by rw [← pow_mul]; ring_nf
      _ = x ^ (orderOf x + 1) := by rw [hk]
      _ = x := by rw [pow_succ, this, one_mul]
  have h5 : Commute x u := by
    have := h4.pow_left (k + 1)
    rwa [hxk] at this
  exact h5.eq

end CFSG.RankThree.PartOne.CTP
