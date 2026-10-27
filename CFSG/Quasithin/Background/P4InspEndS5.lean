module

public import CFSG.Quasithin.Background.P4InspEndAbs

public section

namespace CFSG.Quasithin.G11.P4InspEnd

open Equiv

theorem p4inspend_s5_cent_a5 : ∀ s : Perm (Fin 5),
    (∀ t : Perm (Fin 5), Perm.sign t = 1 → t * s = s * t) → s = 1 := by
  decide +kernel

theorem p4inspend_outer_s5 {G : Type*} [Group G] (M K : Subgroup G) (hKM : K ≤ M)
    (hnorm : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (θ : ↥M ≃* Equiv.Perm (Fin 5))
    (e : ↥K ≃* ↥(alternatingGroup (Fin 5))) (α : ↥K ≃* ↥K) :
    ∃ m ∈ M, ∀ k : ↥K, ((α k : ↥K) : G) = m * (k : G) * m⁻¹ := by
  classical
  have hKcard : Nat.card ↥K = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    simp [Nat.factorial]
  have hPerm : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hMcard : Nat.card ↥M = 120 := by
    rw [Nat.card_congr θ.toEquiv, hPerm]
  let K' : Subgroup ↥M := K.subgroupOf M
  have hK'card : Nat.card ↥K' = 60 := by
    rw [← hKcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  let H : Subgroup (Perm (Fin 5)) := K'.map θ.toMonoidHom
  have hHcard : Nat.card ↥H = 60 := by
    rw [Subgroup.card_map_of_injective θ.injective, hK'card]
  have hHindex : H.index = 2 := by
    have := Subgroup.index_mul_card H
    rw [hHcard, hPerm] at this
    omega
  have hHA : H = alternatingGroup (Fin 5) := Equiv.Perm.eq_alternatingGroup_of_index_eq_two hHindex
  have hcent : ∀ z : ↥M, (∀ k ∈ K, (z : G) * k = k * z) → z = 1 := by
    intro z hz
    have h1 : θ z = 1 := by
      apply p4inspend_s5_cent_a5
      intro t ht
      have htH : t ∈ H := by
        rw [hHA]
        exact Equiv.Perm.mem_alternatingGroup.2 ht
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 htH
      have hyK : (y : G) ∈ K := hy
      have hyz : y * z = z * y := Subtype.ext (hz y hyK).symm
      show θ y * θ z = θ z * θ y
      rw [← map_mul, ← map_mul, hyz]
    exact θ.injective (by rw [h1, map_one])
  have hM' : ∀ m : ↥M, ∀ k ∈ K, (m : G)⁻¹ * k * (m : G)⁻¹⁻¹ ∈ K :=
    fun m k hk => hnorm _ (M.inv_mem m.2) k hk
  let Φ : ↥M → MulAut ↥K := fun m => p4inspendConj K (m : G) (hnorm m m.2)
    (fun k hk => by simpa using hM' m k hk)
  have hΦ : ∀ (m : ↥M) (k : ↥K), ((Φ m k : ↥K) : G) = (m : G) * k * (m : G)⁻¹ := fun m k => rfl
  have hΦinj : Function.Injective Φ := by
    intro m n hmn
    have h1 : (⟨(n : G)⁻¹ * m, M.mul_mem (M.inv_mem n.2) m.2⟩ : ↥M) = 1 := by
      apply hcent
      intro k hk
      have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : G)) hmn
      simp only [hΦ] at h2
      show (n : G)⁻¹ * m * k = k * ((n : G)⁻¹ * m)
      calc (n : G)⁻¹ * (m : G) * k
          = (n : G)⁻¹ * ((m : G) * k * (m : G)⁻¹) * (m : G) := by group
        _ = (n : G)⁻¹ * ((n : G) * k * (n : G)⁻¹) * (m : G) := by rw [h2]
        _ = k * ((n : G)⁻¹ * (m : G)) := by group
    have h3 : (n : G)⁻¹ * m = 1 := congrArg Subtype.val h1
    exact Subtype.ext (inv_mul_eq_one.1 h3).symm
  have hAut : Nat.card (MulAut ↥K) = 120 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 le_rfl
      (by norm_num)
    rw [← Nat.card_eq_of_bijective _ hb, hPerm]
  have hfin : Finite (MulAut ↥K) := Nat.finite_of_card_ne_zero (by rw [hAut]; norm_num)
  have hbij : Function.Bijective Φ :=
    hΦinj.bijective_of_nat_card_le (by rw [hAut, hMcard])
  obtain ⟨m, hm⟩ := hbij.2 α
  refine ⟨(m : G), m.2, fun k => ?_⟩
  rw [← hm, hΦ]

end CFSG.Quasithin.G11.P4InspEnd
