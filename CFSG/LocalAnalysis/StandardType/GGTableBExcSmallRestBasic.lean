module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmall
public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOther

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBExcSmallRest

variable {G : Type*} [Group G]

theorem card_lt_of_nonabelian_isPGroup [Finite G] {p k : ℕ} (hp : p.Prime)
    (hG : ¬ p ^ (k + 1) ∣ Nat.card G) {P : Subgroup G} (hP : IsPGroup p P) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) (hxy : x * y ≠ y * x) {E : Subgroup G}
    (hE : IsElemAbelian p E) : Nat.card E < p ^ k := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp (TableB.isPGroup_of_isElemAbelian hE)
  have hdvd : p ^ n ∣ Nat.card G := hn ▸ Subgroup.card_subgroup_dvd_card E
  have hnk : n ≤ k := by
    by_contra h
    exact hG (dvd_trans (pow_dvd_pow p (by omega)) hdvd)
  rcases hnk.lt_or_eq with h | rfl
  · rw [hn]
    exact Nat.pow_lt_pow_right hp.one_lt h
  · exfalso
    have hG0 : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hfac : (Nat.card G).factorization p = n := by
      apply le_antisymm
      · by_contra h
        exact hG ((hp.pow_dvd_iff_le_factorization hG0).mpr (by omega))
      · exact (hp.pow_dvd_iff_le_factorization hG0).mp hdvd
    let S : Sylow p G := Sylow.ofCard E (by rw [hn, hfac])
    obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q S
    have hmem : ∀ z ∈ P, g * z * g⁻¹ ∈ E := by
      intro z hz
      have h1 : g * z * g⁻¹ ∈ ((g • Q : Sylow p G) : Subgroup G) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul z (MulAut.conj g) (Q : Subgroup G) (hPQ hz)
      rw [hg] at h1
      exact h1
    apply hxy
    have hc := TableB.IsElemAbelian.comm hE (hmem x hx) (hmem y hy)
    have : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
      calc g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        _ = (g * y * g⁻¹) * (g * x * g⁻¹) := hc
        _ = g * (y * x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel this)

theorem card_lt_of_mulEquiv {R : Type*} [Group R] {p k : ℕ}
    (e : R ≃* G) (h : ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E < p ^ k)
    {A : Subgroup R} (hA : IsElemAbelian p A) : Nat.card A < p ^ k := by
  have h1 := h (A.map e.toMonoidHom) (TableB.isElemAbelian_map hA _)
  rwa [Subgroup.card_map_of_injective e.injective] at h1

theorem center_eq_bot_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : Subgroup.center B = ⊥) : Subgroup.center A = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center B := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hz g']
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hz', map_one])

theorem card_lt_of_subset_inn {R : Type*} [Group R] [Finite R] (hR : Subgroup.center R = ⊥)
    {p k : ℕ} (h : ∀ A : Subgroup R, IsElemAbelian p A → Nat.card A < p ^ k)
    {X : Subgroup (MulAut R)}
    (hXI : (X : Set (MulAut R)) ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hX : IsElemAbelian p X) : Nat.card X < p ^ k := by
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn hR hXI hX
  rw [← hAc]
  exact h A hA

end TableBExcSmallRest

end CFSG.StandardType
