module

public import CFSG.ClassicalInvolution.ModelFacts.OddCover.SL3Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA.AKN

open Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open scoped Pointwise

variable {K : Type} [Field K]

theorem card_Zsl [Finite K] : Nat.card (Zsl K) = Nat.card K := by
  let f : K → Zsl K := fun b => ⟨uSL 0 b 0, uSL_mem_Zsl b⟩
  have hf : Function.Bijective f :=
    ⟨fun x y h => (uSL_injective (congrArg Subtype.val h)).2.1, fun g => by
      obtain ⟨g, b, rfl⟩ := g
      exact ⟨b, rfl⟩⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem comm_of_mem_Zsl {z g : SpecialLinearGroup (Fin 3) K} (hz : z ∈ Zsl K)
    (hg : g ∈ Usl K) : z * g = g * z := by
  obtain ⟨b, rfl⟩ := hz
  obtain ⟨a', b', c', rfl⟩ := hg
  rw [uSL_mul, uSL_mul]
  congr 1 <;> ring

theorem exists_mem_not_mem_comm {X : Type*} [Group X] [Finite X] {P D Z₀ : Subgroup X} {q : ℕ}
    (hPq : q < Nat.card P) (hDP : D ≤ P) (hD : Nat.card D ≤ q) (hZ₀P : Z₀ ≤ P)
    (hZ₀ : Nat.card Z₀ = q) (hZ₀c : ∀ z ∈ Z₀, ∀ p ∈ P, z * p = p * z) :
    ∃ s ∈ P, s ∉ D ∧ ∀ d ∈ D, s * d = d * s := by
  by_cases h : Z₀ ≤ D
  · have hZD : Z₀ = D := Subgroup.eq_of_le_of_card_ge h (by rw [hZ₀]; exact hD)
    obtain ⟨s, hs, hsD⟩ : ∃ s ∈ P, s ∉ D := by
      by_contra hall
      push Not at hall
      have hPD : P ≤ D := fun s hs => hall s hs
      have := Subgroup.card_le_of_le hPD
      omega
    exact ⟨s, hs, hsD, fun d hd => (hZ₀c d (hZD ▸ hd) s hs).symm⟩
  · obtain ⟨s, hs, hsD⟩ := Set.not_subset.mp h
    exact ⟨s, hZ₀P hs, hsD, fun d hd => hZ₀c s hs d (hDP hd)⟩

theorem exists_center_of_isSylowTwoOf [Finite K] {X : Type*} [Group X] [Finite X]
    (θ : SpecialLinearGroup (Fin 3) K →* X) (hθ : Function.Surjective θ)
    (hodd : Odd (Nat.card θ.ker)) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 1 ≤ n)
    {P : Subgroup X} (hP : QuasithinUnique.IsSylowTwoOf P ⊤) :
    Nat.card P = Nat.card K ^ 3 ∧ ∃ Z₀ : Subgroup X, Z₀ ≤ P ∧ Nat.card Z₀ = Nat.card K ∧
      ∀ z ∈ Z₀, ∀ p ∈ P, z * p = p * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 (Usl K) := isPGroup_Usl hK
  have hinj : Set.InjOn θ (Usl K : Set (SpecialLinearGroup (Fin 3) K)) := by
    intro u hu v hv huv
    have hk : u⁻¹ * v ∈ θ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, huv, inv_mul_cancel]
    have hU : u⁻¹ * v ∈ Usl K := (Usl K).mul_mem ((Usl K).inv_mem hu) hv
    obtain ⟨k, hk2⟩ := hU2 ⟨_, hU⟩
    have h1 : orderOf (u⁻¹ * v) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hk2)
    have h2 : orderOf (u⁻¹ * v) ∣ Nat.card θ.ker := by
      have := orderOf_dvd_natCard (⟨_, hk⟩ : θ.ker)
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (orderOf (u⁻¹ * v)) (Nat.card θ.ker) :=
      Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd))
    have h3 := orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd h2)
    calc u = u * (u⁻¹ * v) := by rw [h3, mul_one]
      _ = v := by group
  have hcardU : Nat.card ((Usl K).map θ) = Nat.card K ^ 3 := by
    rw [← card_Usl, ← SetLike.coe_sort_coe, Subgroup.coe_map, Nat.card_image_of_injOn hinj]
    rfl
  have hU'2 : IsPGroup 2 ((Usl K).map θ) := hU2.map θ
  have hindex : ¬ 2 ∣ ((Usl K).map θ).index := by
    intro h2
    apply not_dvd_index_Usl hK hn
    have e1 := (Usl K).card_mul_index
    have e2 := ((Usl K).map θ).card_mul_index
    have e3 : Nat.card (SpecialLinearGroup (Fin 3) K) = Nat.card X * Nat.card θ.ker := by
      rw [θ.ker.card_eq_card_quotient_mul_card_subgroup,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ hθ).toEquiv]
    rw [hcardU, ← card_Usl] at e2
    rw [e3, ← e2, mul_assoc] at e1
    have e4 := Nat.eq_of_mul_eq_mul_left Nat.card_pos e1
    rw [e4]
    exact h2.mul_right _
  set SP := hP.2.1.toSylow (by
    have := hP.2.2
    rwa [show (P.subgroupOf ⊤).index = P.relIndex ⊤ from rfl, Subgroup.relIndex_top_right]
      at this) with hSP
  set SU := hU'2.toSylow hindex with hSU
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X SU SP
  have hPeq : P = ((Usl K).map θ).map (MulAut.conj x).toMonoidHom := by
    have h1 := congrArg (fun S : Sylow 2 X => (S : Subgroup X)) hx
    simp only [Sylow.coe_subgroup_smul, hSP, hSU, IsPGroup.toSylow_coe] at h1
    rw [← h1]
    rfl
  refine ⟨?_, ((Zsl K).map θ).map (MulAut.conj x).toMonoidHom, ?_, ?_, ?_⟩
  · rw [hPeq, Subgroup.card_map_of_injective (MulAut.conj x).injective, hcardU]
  · rw [hPeq]
    exact Subgroup.map_mono (Subgroup.map_mono Zsl_le_Usl)
  · rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, ← card_Zsl,
      ← SetLike.coe_sort_coe, Subgroup.coe_map,
      Nat.card_image_of_injOn (hinj.mono (fun z hz => Zsl_le_Usl hz))]
    rfl
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ p hp
    rw [hPeq] at hp
    obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hp
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show x * θ z * x⁻¹ * (x * θ u * x⁻¹) = x * θ (z * u) * x⁻¹ by rw [map_mul]; group,
      comm_of_mem_Zsl hz hu, map_mul]
    group

end CFSG.Quasithin.Vol2.Ch11.SecA.AKN
