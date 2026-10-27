module

public import CFSG.Quasithin.Vol2.Ch12Sec6L1a

public section

namespace CFSG.Quasithin.H13.NPLConj

open Equiv
open scoped Pointwise

theorem card_alt8 : Nat.card ↥(alternatingGroup (Fin 8)) = 20160 :=
  CFSG.Quasithin.H13.S126L1a.card_A8

theorem exists_conj_A8 (H K : Subgroup ↥(alternatingGroup (Fin 8)))
    (hH : Nat.card H = 64) (hK : Nat.card K = 64) :
    ∃ m : ↥(alternatingGroup (Fin 8)), ∀ y : ↥(alternatingGroup (Fin 8)),
      y ∈ K ↔ m⁻¹ * y * m ∈ H := by
  have hpH : IsPGroup 2 H := IsPGroup.of_card (n := 6) (by rw [hH]; norm_num)
  have hpK : IsPGroup 2 K := IsPGroup.of_card (n := 6) (by rw [hK]; norm_num)
  have hidxH : ¬ 2 ∣ H.index := by
    have h := H.card_mul_index
    rw [hH, card_alt8] at h
    omega
  have hidxK : ¬ 2 ∣ K.index := by
    have h := K.card_mul_index
    rw [hK, card_alt8] at h
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq (↥(alternatingGroup (Fin 8)))
    (hpH.toSylow hidxH) (hpK.toSylow hidxK)
  refine ⟨m, fun y => ?_⟩
  have hK2 : y ∈ K ↔ y ∈ hpK.toSylow hidxK := (IsPGroup.mem_toSylow hpK hidxK).symm
  have key : y ∈ hpK.toSylow hidxK ↔
      y ∈ MulAut.conj m • (((hpH.toSylow hidxH) : Set ↥(alternatingGroup (Fin 8)))) := by
    rw [← hm, ← SetLike.mem_coe, Sylow.coe_smul]
  rw [hK2, key, Set.mem_smul_set]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hz' : z ∈ H := (IsPGroup.mem_toSylow hpH hidxH).1 hz
    have hy : y = m * z * m⁻¹ := by
      rw [← hzy]
      simp [MulAut.conj_apply]
    have e : m⁻¹ * y * m = z := by
      rw [hy]
      group
    rw [e]
    exact hz'
  · intro hy
    refine ⟨m⁻¹ * y * m, (IsPGroup.mem_toSylow hpH hidxH).2 hy, ?_⟩
    simp [MulAut.conj_apply]
    group

theorem card_closure_conj (g a : Equiv.Perm (Fin 8)) (s : Set (Equiv.Perm (Fin 8))) :
    Nat.card ↥(Subgroup.closure (insert a s)) =
      Nat.card ↥(Subgroup.closure (insert (g * a * g⁻¹) ((fun x => g * x * g⁻¹) '' s))) := by
  let φ : Equiv.Perm (Fin 8) →* Equiv.Perm (Fin 8) := (MulAut.conj g).toMonoidHom
  have hφ : ∀ x, φ x = g * x * g⁻¹ := fun x => rfl
  have hinj : Function.Injective φ := (MulAut.conj g).injective
  have hmap : (Subgroup.closure (insert a s)).map φ =
      Subgroup.closure (insert (g * a * g⁻¹) ((fun x => g * x * g⁻¹) '' s)) := by
    rw [MonoidHom.map_closure, Set.image_insert_eq]
    rfl
  rw [← hmap, Subgroup.card_map_of_injective hinj]

theorem exists_conj_perm (S0 S : Subgroup (Equiv.Perm (Fin 8)))
    (h0 : S0 ≤ alternatingGroup (Fin 8)) (hS : S ≤ alternatingGroup (Fin 8))
    (c0 : Nat.card ↥S0 = 64) (c : Nat.card ↥S = 64) :
    ∃ g : Equiv.Perm (Fin 8), ∀ x : Equiv.Perm (Fin 8), x ∈ S ↔ g * x * g⁻¹ ∈ S0 := by
  let H : Subgroup ↥(alternatingGroup (Fin 8)) := S0.subgroupOf (alternatingGroup (Fin 8))
  let K : Subgroup ↥(alternatingGroup (Fin 8)) := S.subgroupOf (alternatingGroup (Fin 8))
  have hH : Nat.card H = 64 := by
    rw [← c0]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h0).toEquiv
  have hK : Nat.card K = 64 := by
    rw [← c]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  obtain ⟨m, hm⟩ := exists_conj_A8 H K hH hK
  refine ⟨((m⁻¹ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)), fun x => ?_⟩
  by_cases hx : x ∈ alternatingGroup (Fin 8)
  · have key := hm ⟨x, hx⟩
    simp only [H, K, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at key
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using key
  · have hxS : x ∉ S := fun h => hx (hS h)
    have hgx : ((m⁻¹ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8)) * x *
        ((m⁻¹ : ↥(alternatingGroup (Fin 8))) : Equiv.Perm (Fin 8))⁻¹ ∉ alternatingGroup (Fin 8) := by
      intro h
      apply hx
      have h' := Subgroup.Normal.conj_mem inferInstance _ h (m : Equiv.Perm (Fin 8))
      simpa [Subgroup.coe_inv, mul_assoc] using h'
    constructor
    · intro h
      exact absurd h hxS
    · intro h
      exact absurd (h0 h) hgx

end CFSG.Quasithin.H13.NPLConj

end
