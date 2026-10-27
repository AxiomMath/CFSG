module

public import CFSG.Sporadic.J4.Struct.DoubleCoset

public section

namespace CFSG.Sporadic.J4.Struct

open MulAction

variable {G X : Type*} [Group G] [MulAction G X]

theorem smul_mem_orbit_iff (K : Subgroup G) (x₀ : X) (hK : stabilizer G x₀ = K) (g g' : G) :
    g' • x₀ ∈ orbit K (g • x₀) ↔ g' ∈ dcSet K g := by
  constructor
  · rintro ⟨⟨k, hk⟩, he⟩
    have he' : (k * g) • x₀ = g' • x₀ := by rw [mul_smul]; exact he
    have hs : (k * g)⁻¹ * g' ∈ K := by
      rw [← hK, mem_stabilizer_iff, mul_smul, ← he', ← mul_smul, inv_mul_cancel, one_smul]
    refine ⟨k, hk, (k * g)⁻¹ * g', hs, ?_⟩
    group
  · rintro ⟨k, hk, k', hk', rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    have hk'' : k' • x₀ = x₀ := by
      have : k' ∈ stabilizer G x₀ := hK ▸ hk'
      exact this
    change k • g • x₀ = (k * g * k') • x₀
    rw [mul_smul, mul_smul, hk'']

theorem ncard_dcSet_eq [Finite G] (K : Subgroup G) (x₀ : X) (hK : stabilizer G x₀ = K) (g : G) :
    (dcSet K g).ncard = Nat.card K * (orbit K (g • x₀)).ncard := by
  classical
  have : Fintype G := Fintype.ofFinite G
  set s : Set G := dcSet K g
  set t : Set X := orbit K (g • x₀)
  have hst : ∀ x ∈ s, x • x₀ ∈ t := fun x hx => (smul_mem_orbit_iff K x₀ hK g x).2 hx
  have hfib : ∀ x ∈ s, {y | y ∈ s ∧ y • x₀ = x • x₀} = (fun k : K => x * (k : G)) '' Set.univ := by
    intro x hx
    ext y
    simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
    constructor
    · rintro ⟨-, he⟩
      have hs : x⁻¹ * y ∈ K := by
        rw [← hK, mem_stabilizer_iff, mul_smul, he, ← mul_smul, inv_mul_cancel, one_smul]
      exact ⟨⟨x⁻¹ * y, hs⟩, by simp⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      refine ⟨⟨a, ha, b * k, K.mul_mem hb hk, by group⟩, ?_⟩
      have : k • x₀ = x₀ := by
        have : k ∈ stabilizer G x₀ := hK ▸ hk
        exact this
      change (a * g * b * k) • x₀ = (a * g * b) • x₀
      rw [mul_smul, this]
  have hcardfib : ∀ x ∈ s, ({y | y ∈ s ∧ y • x₀ = x • x₀} : Set G).ncard = Nat.card K := by
    intro x hx
    rw [hfib x hx, Set.ncard_image_of_injective _ (fun a b h => Subtype.ext (mul_left_cancel h)),
      Set.ncard_univ]
  have hsf : s.Finite := Set.toFinite s
  have htf : t.Finite := Set.Finite.subset (Set.finite_range fun x : G => x • x₀) (by
    rintro _ ⟨⟨k, -⟩, rfl⟩
    refine ⟨k * g, ?_⟩
    change (k * g) • x₀ = k • g • x₀
    rw [mul_smul])
  rw [Set.ncard_eq_toFinset_card s hsf, Set.ncard_eq_toFinset_card t htf,
    Finset.card_eq_sum_card_fiberwise (f := fun x => x • x₀) (t := htf.toFinset)
      (fun x hx => by simpa using hst x (by simpa using hx))]
  rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Set.Finite.mem_toFinset] at hp
  obtain ⟨⟨k, hk⟩, rfl⟩ := hp
  have hx : k * g ∈ s := ⟨k, hk, 1, K.one_mem, by group⟩
  have e := hcardfib (k * g) hx
  rw [← e, ← Set.ncard_coe_finset]
  congr 1
  ext y
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [mul_smul]
  rfl

end CFSG.Sporadic.J4.Struct

end
