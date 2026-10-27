module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructStab

public section

namespace CFSG.Quasithin.H13.F431.D4q.Struct

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


section Tsub

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem mulAut_mul_conj (φ : MulAut (Cm σ)) (u : Cm σ) :
    φ * MulAut.conj u = MulAut.conj (φ u) * φ := by
  ext x
  simp [MulAut.conj_apply]

theorem fieldActor_mem_Ust (δ : K ≃+* K) {u : Cm σ} (hu : u ∈ Ust σ) :
    fieldActor σ δ u ∈ Ust σ := by
  rw [← fieldActor_map_Ust σ δ]
  exact Subgroup.mem_map_of_mem _ hu

@[expose] noncomputable def Tsub (S : Subgroup (K ≃+* K)) : Subgroup (MulAut (Cm σ)) where
  carrier := {α | ∃ u ∈ Ust σ, ∃ δ ∈ S, α = MulAut.conj u * fieldActor σ δ}
  mul_mem' := by
    rintro _ _ ⟨u, hu, δ, hδ, rfl⟩ ⟨u', hu', δ', hδ', rfl⟩
    refine ⟨u * fieldActor σ δ u', (Ust σ).mul_mem hu (fieldActor_mem_Ust σ δ hu'), δ * δ',
      S.mul_mem hδ hδ', ?_⟩
    have h := mulAut_mul_conj σ (fieldActor σ δ) u'
    rw [map_mul, fieldActor_mul σ δ δ']
    calc MulAut.conj u * fieldActor σ δ * (MulAut.conj u' * fieldActor σ δ') =
        MulAut.conj u * (fieldActor σ δ * MulAut.conj u') * fieldActor σ δ' := by
          simp only [mul_assoc]
      _ = _ := by rw [h]; simp only [mul_assoc]
  one_mem' := ⟨1, (Ust σ).one_mem, 1, S.one_mem, by rw [map_one, fieldActor_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨u, hu, δ, hδ, rfl⟩
    refine ⟨fieldActor σ δ⁻¹ u⁻¹, fieldActor_mem_Ust σ δ⁻¹ ((Ust σ).inv_mem hu), δ⁻¹,
      S.inv_mem hδ, ?_⟩
    have h := mulAut_mul_conj σ (fieldActor σ δ⁻¹) u⁻¹
    have hinv : (fieldActor σ δ)⁻¹ = fieldActor σ δ⁻¹ :=
      (map_inv (fieldActorHom (t := TwistTag.D4) σ) δ).symm
    rw [mul_inv_rev, ← map_inv, hinv]
    exact h

theorem mem_Tsub_iff (S : Subgroup (K ≃+* K)) (α : MulAut (Cm σ)) :
    α ∈ Tsub σ S ↔ ∃ u ∈ Ust σ, ∃ δ ∈ S, α = MulAut.conj u * fieldActor σ δ := Iff.rfl

end Tsub

section Order

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ} (hf : 1 ≤ f)
  (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ.toRingHom c = c ^ (2 ^ f))

include hf hK hσ

theorem Tsub_le {Kb : Subgroup (MulAut (Cm σ))}
    (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb) {S : Subgroup (K ≃+* K)}
    (hS : S ≤ Kb.map (theta σ hf hK hσ)) : Tsub σ S ≤ Kb := by
  rintro _ ⟨u, -, δ, hδ, rfl⟩
  exact (conj_mul_fieldActor_mem_iff σ hf hK hσ hinn u δ).2 (hS hδ)

theorem card_Tsub (S : Subgroup (K ≃+* K)) :
    Nat.card (Tsub σ S) = Nat.card (Ust σ) * Nat.card S := by
  let e : ↥(Ust σ) × ↥S ≃ ↥(Tsub σ S) := Equiv.ofBijective
    (fun p => ⟨MulAut.conj (p.1 : Cm σ) * fieldActor σ (p.2 : K ≃+* K),
      ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩) ⟨?_, ?_⟩
  · rw [← Nat.card_prod]
    exact (Nat.card_congr e).symm
  · rintro ⟨u, δ⟩ ⟨u', δ'⟩ h
    have h1 : MulAut.conj (u : Cm σ) * fieldActor σ (δ : K ≃+* K) =
        MulAut.conj (u' : Cm σ) * fieldActor σ (δ' : K ≃+* K) := congrArg Subtype.val h
    have hδ : (δ : K ≃+* K) = δ' := by
      have := congrArg (theta σ hf hK hσ) h1
      rwa [theta_conj_fieldActor, theta_conj_fieldActor] at this
    have hu : (u : Cm σ) = u' := by
      apply conj_injective σ
      rw [hδ] at h1
      exact mul_right_cancel h1
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hδ)
  · rintro ⟨_, u, hu, δ, hδ, rfl⟩
    exact ⟨(⟨u, hu⟩, ⟨δ, hδ⟩), rfl⟩

theorem isSylowTwoOf_Tsub {Kb : Subgroup (MulAut (Cm σ))}
    (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb) {S : Subgroup (K ≃+* K)}
    (hS : IsSylowTwoOf S (Kb.map (theta σ hf hK hσ))) (hU : IsSylowTwoOf (Ust σ) ⊤) :
    IsSylowTwoOf (Tsub σ S) Kb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (K ≃+* K) := Finite.of_injective (fun δ : K ≃+* K => (δ : K → K))
    fun _ _ h => RingEquiv.ext (congrFun h)
  obtain ⟨hSle, hS2, hSodd⟩ := hS
  obtain ⟨-, hU2, hUodd⟩ := hU
  have hle : Tsub σ S ≤ Kb := Tsub_le σ hf hK hσ hinn hSle
  refine ⟨hle, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hU2
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 hS2
    exact IsPGroup.iff_card.2 ⟨a + b, by rw [card_Tsub σ hf hK hσ, ha, hb, pow_add]⟩
  · have e1 := Subgroup.relIndex_mul_card (Tsub σ S) Kb
    rw [inf_eq_left.2 hle, card_Tsub σ hf hK hσ, card_eq_of_inn_le σ hf hK hσ hinn] at e1
    have e2 := Subgroup.card_mul_index (Ust σ)
    have e3 := Subgroup.relIndex_mul_card S (Kb.map (theta σ hf hK hσ))
    rw [inf_eq_left.2 hSle] at e3
    have hUpos : 0 < Nat.card (Ust σ) := Nat.card_pos
    have hSpos : 0 < Nat.card S := Nat.card_pos
    have hr : (Tsub σ S).relIndex Kb = (Ust σ).index * S.relIndex (Kb.map (theta σ hf hK hσ)) := by
      apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hUpos hSpos)
      rw [e1, ← e2, ← e3]
      ring
    have hUodd' : ¬ 2 ∣ (Ust σ).index := by
      rwa [show ((Ust σ).subgroupOf ⊤).index = (Ust σ).index from
        Subgroup.relIndex_top_right _] at hUodd
    change ¬ 2 ∣ (Tsub σ S).relIndex Kb
    rw [hr]
    intro hd
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
    · exact hUodd' h
    · exact hSodd h

theorem Tsub_bot : Tsub σ ⊥ = (Ust σ).map (MulAut.conj : Cm σ →* MulAut (Cm σ)) := by
  ext α
  constructor
  · rintro ⟨u, hu, δ, hδ, rfl⟩
    rw [Subgroup.mem_bot.1 hδ, fieldActor_one, mul_one]
    exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, 1, Subgroup.one_mem _, by rw [fieldActor_one, mul_one]⟩

include hf hK hσ in
theorem isSylowTwoOf_conj_Ust {Kb : Subgroup (MulAut (Cm σ))}
    (hinn : (MulAut.conj : Cm σ →* MulAut (Cm σ)).range ≤ Kb)
    (hodd : Odd (Nat.card Kb / Nat.card (Cm σ))) (hU : IsSylowTwoOf (Ust σ) ⊤) :
    IsSylowTwoOf ((Ust σ).map (MulAut.conj : Cm σ →* MulAut (Cm σ))) Kb := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have : Finite (K ≃+* K) := Finite.of_injective (fun δ : K ≃+* K => (δ : K → K))
    fun _ _ h => RingEquiv.ext (congrFun h)
  have hc := card_eq_of_inn_le σ hf hK hσ hinn
  have hpos : 0 < Nat.card (Cm σ) := Nat.card_pos
  have hdiv : Nat.card Kb / Nat.card (Cm σ) = Nat.card (Kb.map (theta σ hf hK hσ)) := by
    rw [hc, Nat.mul_div_cancel_left _ hpos]
  rw [hdiv] at hodd
  have hS := isSylowTwoOf_bot_of_odd (Kb.map (theta σ hf hK hσ)) hodd
  have := isSylowTwoOf_Tsub σ hf hK hσ hinn hS hU
  rwa [Tsub_bot] at this

end Order

end CFSG.Quasithin.H13.F431.D4q.Struct
