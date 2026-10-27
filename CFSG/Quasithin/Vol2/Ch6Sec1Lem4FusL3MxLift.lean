module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Lift

variable {S : Type*} [Group S] {G : Type*} [Group G] {ψ : S →* G}

theorem lift_involution_L3 (h3 : ∀ z ∈ ψ.ker, z ^ 3 = 1) {u : G} (hu : u ∈ ψ.range)
    (hu2 : u * u = 1) : ∃ s : S, s * s = 1 ∧ ψ s = u := by
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hu
  have hz : b * b ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul]
    exact hu2
  have hz3 := h3 _ hz
  refine ⟨b * (b * b), ?_, ?_⟩
  · have h1 : b * (b * b) * (b * (b * b)) = (b * b) ^ 3 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [h1, hz3]
  · rw [map_mul, MonoidHom.mem_ker.mp hz, mul_one]

theorem lift_five_L3 (h3 : ∀ z ∈ ψ.ker, z ^ 3 = 1) {y : G} (hy : y ∈ ψ.range)
    (hy5 : y ^ 5 = 1) : ∃ s : S, s ^ 5 = 1 ∧ ψ s = y := by
  obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hy
  have hz : b ^ 5 ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hy5
  have hz3 := h3 _ hz
  refine ⟨b ^ 6, ?_, ?_⟩
  · have e : (b ^ 6) ^ 5 = ((b ^ 5) ^ 3) ^ 2 := by group
    rw [e, hz3, one_pow]
  · rw [map_pow, show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hy5, one_mul]

theorem lift_five_unique_L3 (hcen : ψ.ker ≤ Subgroup.center S) (h3 : ∀ z ∈ ψ.ker, z ^ 3 = 1)
    {s s' : S} (hss' : ψ s = ψ s') (hs : s ^ 5 = 1) (hs' : s' ^ 5 = 1) : s = s' := by
  obtain ⟨z, hzdef⟩ : ∃ z : S, z = s' * s⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ ψ.ker := by
    rw [hzdef, MonoidHom.mem_ker, map_mul, map_inv, ← hss']
    simp
  have hzc : ∀ g : S, g * z = z * g := Subgroup.mem_center_iff.mp (hcen hz)
  have hz3 : z ^ 3 = 1 := h3 z hz
  have hsplit : s' = z * s := by
    rw [hzdef, inv_mul_cancel_right]
  have hcomm : Commute z s := (hzc s).symm
  have hz5 : z ^ 5 = 1 := by
    have h := hcomm.mul_pow 5
    rw [← hsplit, hs', hs, mul_one] at h
    exact h.symm
  have hz1 : z = 1 := by
    have e : z = z ^ 3 * z ^ 3 * (z ^ 5)⁻¹ := by group
    rw [hz3, hz5, inv_one, mul_one, mul_one] at e
    exact e
  exact (mul_inv_eq_one.mp (hzdef.symm.trans hz1)).symm

theorem commute_of_map_commute_L3 (hcen : ψ.ker ≤ Subgroup.center S)
    (h3 : ∀ z ∈ ψ.ker, z ^ 3 = 1) {s : S} (hs : s * s = 1) {t : S}
    (h : Commute (ψ t) (ψ s)) : Commute t s :=
  CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.commute_of_map_commute ψ hcen h3 hs h

theorem leviOfL3_range_eq (hcen : ψ.ker ≤ Subgroup.center S) (h3 : ∀ z ∈ ψ.ker, z ^ 3 = 1)
    {s : S} (hs : s * s = 1) :
    leviOfL3 ψ.range (ψ s) =
      (⁅Subgroup.centralizer ({s} : Set S), Subgroup.centralizer ({s} : Set S)⁆).map ψ := by
  have hC : ψ.range ⊓ Subgroup.centralizer ({ψ s} : Set G) =
      (Subgroup.centralizer ({s} : Set S)).map ψ := by
    ext g
    constructor
    · intro hg
      obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hg1
      refine Subgroup.mem_map.mpr ⟨t, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_map_commute_L3 hcen h3 hs (Subgroup.mem_centralizer_singleton_iff.mp hg2))
    · intro hg
      obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_inf.mpr ⟨MonoidHom.mem_range.mpr ⟨t, rfl⟩, ?_⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have ht' := Subgroup.mem_centralizer_singleton_iff.mp ht
      rw [← map_mul, ← map_mul, ht']
  rw [leviOfL3, hC, Subgroup.map_commutator]

end Lift

end CFSG.Quasithin.H13
