module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.DetDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Sporadic.SchreierLemmas.OrderThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)

private theorem k328dax_hom_trivial {G H : Type*} [Group G] [Group H] [Group.IsSolvable H]
    (hG : commutator G = ⊤) (f : G →* H) : f = 1 := by
  obtain ⟨m, hm⟩ := Group.IsSolvable.solvable (G := H)
  have hder : ∀ j, derivedSeries G j = ⊤ := fun j => by
    induction j with
    | zero => exact derivedSeries_zero G
    | succ j ih => rw [derivedSeries_succ, ih]; exact hG
  have h1 := map_derivedSeries_le_derivedSeries f m
  rw [hder m, hm] at h1
  ext g
  simpa using h1 ⟨g, Subgroup.mem_top g, rfl⟩

private theorem k328dax_card_cycleFactors {n : ℕ} (hn : n ≤ 11) {σ : Equiv.Perm (Fin n)}
    (hσ : orderOf σ = 3) : Nat.card σ.cycleFactorsFinset ≤ 4 := by
  obtain ⟨k, -, h3k, -, hk, -, -⟩ :=
    CFSG.Sporadic.SchreierLemmas.order_three_permutation_shape hσ
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, hk]
  rw [Fintype.card_fin] at h3k
  omega

private theorem k328dax_commute_cycles {n : ℕ} (hn : n ≤ 11) {σ : Equiv.Perm (Fin n)}
    (hσ : orderOf σ = 3) {Q : Subgroup (Equiv.Perm (Fin n))}
    (hQC : Q ≤ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) (hQ : ⁅Q, Q⁆ = Q)
    {q : Equiv.Perm (Fin n)} (hq : q ∈ Q) {c : Equiv.Perm (Fin n)}
    (hc : c ∈ σ.cycleFactorsFinset) : Commute q c := by
  have : Group.IsSolvable (Equiv.Perm σ.cycleFactorsFinset) :=
    Equiv.Perm.isSolvable (k328dax_card_cycleFactors hn hσ)
  have hperf : commutator ↥Q = ⊤ := Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hQ)
  have h1 := k328dax_hom_trivial hperf
    ((Equiv.Perm.OnCycleFactors.toPermHom σ).comp (Subgroup.inclusion hQC))
  have h2 : (⟨q, hQC hq⟩ : ↥(Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n))))) ∈
      (Equiv.Perm.OnCycleFactors.toPermHom σ).ker := by
    rw [MonoidHom.mem_ker]
    exact DFunLike.congr_fun h1 ⟨q, hq⟩
  exact (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff σ ⟨q, hQC hq⟩).1 h2 c hc

private theorem k328dax_exists_zpow {n : ℕ} {σ q : Equiv.Perm (Fin n)} {t : Fin n}
    (ht : t ∈ σ.support) (hq : Commute q (σ.cycleOf t)) : ∃ i : ℤ, q t = (σ ^ i) t := by
  have hct : σ.cycleOf t t ≠ t := by
    rw [Equiv.Perm.cycleOf_apply_self]
    exact Equiv.Perm.mem_support.1 ht
  have hcq : σ.cycleOf t (q t) ≠ q t := by
    have h := Equiv.Perm.congr_fun hq.eq t
    simp only [Equiv.Perm.mul_apply] at h
    rw [← h]
    exact fun h' => hct (q.injective h')
  obtain ⟨i, hi⟩ := (Equiv.Perm.isCycle_cycleOf σ (Equiv.Perm.mem_support.1 ht)).sameCycle hct hcq
  exact ⟨i, by rw [← hi, Equiv.Perm.cycleOf_zpow_apply_self]⟩

private theorem k328dax_commutator_fix {n : ℕ} {σ q₁ q₂ : Equiv.Perm (Fin n)}
    (h₁ : Commute q₁ σ) (h₂ : Commute q₂ σ)
    (z₁ : ∀ t ∈ σ.support, ∃ i : ℤ, q₁ t = (σ ^ i) t)
    (z₂ : ∀ t ∈ σ.support, ∃ i : ℤ, q₂ t = (σ ^ i) t) :
    ∀ t ∈ σ.support, (q₁ * q₂ * q₁⁻¹ * q₂⁻¹) t = t := by
  have hzpow : ∀ q : Equiv.Perm (Fin n), Commute q σ → ∀ (i : ℤ) (t : Fin n),
      q ((σ ^ i) t) = (σ ^ i) (q t) := fun q hq i t =>
    Equiv.Perm.congr_fun (hq.zpow_right i).eq t
  have hsupp : ∀ q : Equiv.Perm (Fin n), Commute q σ → ∀ t ∈ σ.support, q t ∈ σ.support := by
    intro q hq t ht
    rw [Equiv.Perm.mem_support] at ht ⊢
    have h := Equiv.Perm.congr_fun hq.eq t
    simp only [Equiv.Perm.mul_apply] at h
    rw [← h]
    exact fun h' => ht (q.injective h')
  have hcomm : ∀ t ∈ σ.support, q₁ (q₂ t) = q₂ (q₁ t) := by
    intro t ht
    obtain ⟨a, ha⟩ := z₁ t ht
    obtain ⟨b, hb⟩ := z₂ t ht
    calc q₁ (q₂ t) = q₁ ((σ ^ b) t) := by rw [hb]
      _ = (σ ^ b) ((σ ^ a) t) := by rw [hzpow q₁ h₁ b t, ha]
      _ = (σ ^ a) ((σ ^ b) t) := by
        rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← zpow_add, ← zpow_add, add_comm]
      _ = (σ ^ a) (q₂ t) := by rw [hb]
      _ = q₂ ((σ ^ a) t) := (hzpow q₂ h₂ a t).symm
      _ = q₂ (q₁ t) := by rw [ha]
  intro t ht
  have hu : q₁⁻¹ (q₂⁻¹ t) ∈ σ.support := hsupp _ h₁.inv_left _ (hsupp _ h₂.inv_left _ ht)
  have h := hcomm _ hu
  simp only [Equiv.Perm.mul_apply]
  rw [h]
  simp

private theorem k328dax_fix {n : ℕ} (hn : n ≤ 11) {σ : Equiv.Perm (Fin n)} (hσ : orderOf σ = 3)
    {Q : Subgroup (Equiv.Perm (Fin n))}
    (hQC : Q ≤ Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin n)))) (hQ : ⁅Q, Q⁆ = Q) :
    ∀ q ∈ Q, ∀ t ∈ σ.support, q t = t := by
  have hcomm : ∀ q ∈ Q, Commute q σ := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.1 (hQC hq)
  have hz : ∀ q ∈ Q, ∀ t ∈ σ.support, ∃ i : ℤ, q t = (σ ^ i) t := fun q hq t ht =>
    k328dax_exists_zpow ht (k328dax_commute_cycles hn hσ hQC hQ hq
      (Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.2 ht))
  have hle : ⁅Q, Q⁆ ≤ fixingSubgroup (Equiv.Perm (Fin n)) (σ.support : Set (Fin n)) := by
    rw [Subgroup.commutator_le]
    intro q₁ h₁ q₂ h₂
    rw [mem_fixingSubgroup_iff]
    intro t ht
    exact k328dax_commutator_fix (hcomm _ h₁) (hcomm _ h₂) (hz _ h₁) (hz _ h₂) t ht
  intro q hq t ht
  have hq' : q ∈ ⁅Q, Q⁆ := by rw [hQ]; exact hq
  exact (mem_fixingSubgroup_iff _).1 (hle hq') t ht

private theorem k328dax_false {G : Type*} [Group G] {n : ℕ} (hn : n ≤ 11)
    (ι : G →* Equiv.Perm (Fin n)) (hι : Function.Injective ι) {z : G} (hz : orderOf z = 3)
    {X : Subgroup G} (hzX : z ∈ X) (hXz : X ≤ Subgroup.centralizer ({z} : Set G))
    (hX : ⁅X, X⁆ = X) : False := by
  have hσ : orderOf (ι z) = 3 := by rw [orderOf_injective ι hι z]; exact hz
  have hQC : X.map ι ≤ Subgroup.centralizer ({ι z} : Set (Equiv.Perm (Fin n))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.1 (hXz hx)]
  have hQ : ⁅X.map ι, X.map ι⁆ = X.map ι := by rw [← Subgroup.map_commutator, hX]
  have h1 := k328dax_fix hn hσ hQC hQ (ι z) (Subgroup.mem_map_of_mem ι hzX)
  have hne : (ι z).support ≠ ∅ := by
    rw [Ne, Equiv.Perm.support_eq_empty_iff]
    intro h
    have : z = 1 := hι (h.trans (map_one ι).symm)
    rw [this, orderOf_one] at hz
    omega
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hne
  exact Equiv.Perm.mem_support.1 ht (h1 t ht)

theorem k328det_altExcluded :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → ∀ n : ℕ, n ≤ 11 → IsAlt S n →
      ¬ K328DetPosIn S := by
  rintro S _ _ _ n hn ⟨e⟩ ⟨Z, X, hp, -⟩
  obtain ⟨hZ, hZX, hXC, -, hq, -, -⟩ := hp
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 3 (by rw [hZ])
  have hXz : X ≤ Subgroup.centralizer ({(z : S)} : Set S) :=
    hXC.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 z.2))
  have hX : ⁅X, X⁆ = X := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hq.1)
  exact k328dax_false hn ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
    ((alternatingGroup (Fin n)).subtype_injective.comp e.injective)
    (by rw [Subgroup.orderOf_coe]; exact hz) (hZX z.2) hXz hX

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
