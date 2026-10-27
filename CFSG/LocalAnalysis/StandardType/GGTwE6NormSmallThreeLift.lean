module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeRefl

public section

namespace CFSG.StandardType.TwE6D3

open CFSG.Open

theorem exists_fixed_of_refl {R L' : Type} [Group R] [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Nat.card (Subgroup.center L') ∣ 3) (hZR : Subgroup.center R = ⊥)
    {Y : Subgroup (MulAut R)} (hY : IsElemAbelian 3 Y) {ι : Type} (r s : ι → R)
    (hs : ∀ i, MulAut.conj (s i) ∈ Y)
    (hrs : ∀ i, ∀ y ∈ Y, ∃ k : ℕ,
      MulAut.conj (r i) * y * (MulAut.conj (r i))⁻¹ = MulAut.conj (s i) ^ k * y)
    (hrsi : ∀ i, r i * s i * (r i)⁻¹ = (s i)⁻¹) :
    ∃ E : Subgroup L', IsElemAbelian 3 E ∧ Subgroup.center L' ≤ E ∧
      Subgroup.closure (Set.range s) ≤ E.map ψ ∧
      ∀ a : MulAut L', a ^ 3 = 1 → (∃ φ ∈ Y, ∀ l, φ (ψ l) = ψ (a l)) → ∀ e ∈ E, a e = e := by
  classical
  have hcinj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxZ : x ∈ Subgroup.center R := Subgroup.mem_center_iff.mpr fun g => by
      have h1 := congrArg (fun f : MulAut R => f g) hx
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * x = x * g * x⁻¹ * x := by rw [h1]
        _ = x * g := by group
    rwa [hZR] at hxZ
  have hconj : ∀ (φ : MulAut R) (x : R), φ * MulAut.conj x * φ⁻¹ = MulAut.conj (φ x) := by
    intro φ x
    ext y
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]
  have hYc : ∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x := fun x hx y hy => hY.comm hx hy
  choose η hη using fun i => hψ (s i)
  choose m hm using fun i => hψ (r i)
  have hrs' : ∀ i j, ∃ k : ℕ, r i * s j * (r i)⁻¹ = s i ^ k * s j := fun i j => by
    obtain ⟨k, hk⟩ := hrs i _ (hs j)
    exact ⟨k, hcinj (by simpa only [map_mul, map_inv, map_pow] using hk)⟩
  have hφs : ∀ φ ∈ Y, ∀ i, φ (s i) = s i := fun φ hφ i =>
    hcinj (by rw [← hconj, hYc _ hφ _ (hs i), mul_inv_cancel_right])
  have hφr : ∀ φ ∈ Y, ∀ i, ∃ k : ℕ, φ (r i) = (s i ^ k)⁻¹ * r i := by
    intro φ hφ i
    obtain ⟨k, hk⟩ := hrs i φ hφ
    refine ⟨k, hcinj ?_⟩
    rw [← hconj]
    simp only [map_mul, map_inv, map_pow]
    rw [show MulAut.conj (s i) ^ k = MulAut.conj (r i) * φ * (MulAut.conj (r i))⁻¹ * φ⁻¹ by
      rw [hk, mul_inv_cancel_right]]
    group
  have hZ3' : ∀ z ∈ Subgroup.center L', z ^ 3 = 1 := fun z hz => by
    obtain ⟨c, hc⟩ := hZ
    have h1 : (⟨z, hz⟩ : Subgroup.center L') ^ 3 = 1 := by
      rw [hc, pow_mul, pow_card_eq_one', one_pow]
    simpa using congrArg Subtype.val h1
  have hmη : ∀ i, ψ (m i * η i * (m i)⁻¹) = ψ (η i)⁻¹ := fun i => by
    simpa only [map_mul, map_inv, hη, hm] using hrsi i
  have hcomm : ∀ i j, η i * η j = η j * η i := by
    intro i j
    obtain ⟨k, hk⟩ := hrs' i j
    refine (commute_of_refl hker hZ3' (w := m i) (k := k) ?_ ?_ (hmη i)).symm
    · have hss : s j * s i = s i * s j :=
        hcinj (by simpa only [map_mul] using hYc _ (hs j) _ (hs i))
      refine hker (MonoidHom.mem_ker.2 ?_)
      simp only [map_mul, map_inv, hη]
      rw [hss]
      group
    · simpa only [map_mul, map_inv, map_pow, hη, hm] using hk
  have hη3 : ∀ i, η i ^ 3 = 1 := fun i => pow_three_of_refl hker hZ3'
    (hker (MonoidHom.mem_ker.2 (hcinj (by
      rw [map_pow, hη, map_pow, hY.2 _ (hs i), map_one])))) (hmη i)
  set E : Subgroup L' := Subgroup.closure ((Subgroup.center L' : Set L') ∪ Set.range η)
  have hEel : IsElemAbelian 3 E := by
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · rintro x (hx | ⟨i, rfl⟩) y (hy | ⟨j, rfl⟩)
      · exact Subgroup.mem_center_iff.mp hy x
      · exact (Subgroup.mem_center_iff.mp hx (η j)).symm
      · exact Subgroup.mem_center_iff.mp hy (η i)
      · exact hcomm i j
    · rintro x (hx | ⟨i, rfl⟩)
      · exact hZ3' x hx
      · exact hη3 i
  refine ⟨E, hEel, fun z hz => Subgroup.subset_closure (Or.inl hz), ?_,
    fun a ha3 ⟨φ, hφ, hφa⟩ => ?_⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_map.2 ⟨η i, Subgroup.subset_closure (Or.inr ⟨i, rfl⟩), hη i⟩
  have haZ : ∀ z ∈ Subgroup.center L', a z = z := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hZ with h1 | h3
    · intro z hz
      rw [Subgroup.card_eq_one.1 h1, Subgroup.mem_bot] at hz
      rw [hz, map_one]
    · exact CFSG.RankThree.PartTwo.Sec14.Res148.fix_center_of_pow_three a ha3 h3
  have hfix : Set.EqOn a.toMonoidHom (MonoidHom.id L')
      ((Subgroup.center L' : Set L') ∪ Set.range η) := by
    rintro x (hx | ⟨i, rfl⟩)
    · exact haZ x hx
    · obtain ⟨k, hk⟩ := hφr φ hφ i
      refine fix_of_refl hker hZ3' haZ (w := m i) (k := k) ?_ ?_ (hmη i)
      · rw [← hφa, hη, hφs φ hφ i]
      · rw [← hφa, hm, hk, map_mul, map_inv, map_pow, hη, hm]
  exact fun e he => MonoidHom.eqOn_closure hfix he

end CFSG.StandardType.TwE6D3
