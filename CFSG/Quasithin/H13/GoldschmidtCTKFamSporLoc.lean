module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Data
public import CFSG.Quasithin.H13.GoldschmidtCTKFam

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.QuasithinUnique.A5.Kc3J
  CFSG.QuasithinUnique.A5.Kc3NSC

section Delta

variable {K : Type*} [Group K] {V : Subgroup K}

theorem IsDelta5Ext.normal (h : IsDelta5Ext K V) : V.Normal := by
  obtain ⟨α, -, hαk, -⟩ := h
  exact hαk ▸ α.normal_ker

theorem IsDelta5Ext.card_eq (h : IsDelta5Ext K V) (hV : Nat.card V = 16) : Nat.card K = 960 := by
  obtain ⟨α, hα, hαk, -⟩ := h
  have hcardA : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hker : Nat.card ↥α.ker = 16 := by
    rw [hαk]
    exact hV
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker, hker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv, hcardA]

end Delta

section Config

variable {S : Type} [Group S]

theorem IsDelta5Ext.exists_equivariant {K V : Subgroup S} (hVK : V ≤ K)
    (h : IsDelta5Ext ↥K (V.subgroupOf K)) :
    ∃ (α : ↥K →* ↥(alternatingGroup (Fin 5))) (β : ↥V ≃* Multiplicative ↥(evenWeight 5)),
      Function.Surjective α ∧ ∀ (l : ↥K) (v w : ↥V), (w : S) = (l : S) * v * (l : S)⁻¹ →
        Multiplicative.toAdd (β w) =
          Delta5.vact ((α l : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5))
            (Multiplicative.toAdd (β v)) := by
  obtain ⟨α, hα, -, β, hβ, hact⟩ := h
  let φ : ↥(V.subgroupOf K) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVK
  refine ⟨α, φ.symm.trans (MulEquiv.ofBijective β hβ), hα, fun l v w hw => ?_⟩
  have hu : ((φ.symm w : ↥(V.subgroupOf K)) : ↥K) =
      l * ((φ.symm v : ↥(V.subgroupOf K)) : ↥K) * l⁻¹ := by
    apply Subtype.ext
    have h1 : (((φ.symm w : ↥(V.subgroupOf K)) : ↥K) : S) = (w : S) := by
      conv_rhs => rw [← φ.apply_symm_apply w]
      rfl
    have h2 : (((φ.symm v : ↥(V.subgroupOf K)) : ↥K) : S) = (v : S) := by
      conv_rhs => rw [← φ.apply_symm_apply v]
      rfl
    rw [h1, hw]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, h2]
  exact Subtype.ext (funext fun i => hact l (φ.symm v) (φ.symm w) hu i)

end Config

section Main

variable {S : Type} [Group S] [Finite S]

theorem A5Config.not_kc3LocalData (h : A5Config S) : ¬ Kc3LocalData S := by
  intro hloc
  obtain ⟨K, V, T₁, -, hVK, -, -, hΔ, hT1N, hN, -, -, -, -⟩ := h
  have hKN : K ≤ Subgroup.normalizer (V : Set S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).1 hΔ.normal
  have hnorm : Subgroup.normalizer (V : Set S) ≤ Subgroup.normalizer (K : Set S) := by
    rw [hN]
    exact sup_le Subgroup.le_normalizer hT1N
  obtain ⟨α, β, hα, hβ⟩ := hΔ.exists_equivariant hVK
  have hsub : IsSubnormal K (Subgroup.normalizer (V : Set S)) :=
    IsSubnormal.step hKN ((Subgroup.normal_subgroupOf_iff_le_normalizer hKN).2 hnorm)
      (IsSubnormal.refl _)
  have hperm := nsc_perm hKN le_rfl α hα β hβ hsub
  have hD : Delta5Norm V β := by
    intro σ hσ
    obtain ⟨l, hl⟩ := hα ⟨σ, Equiv.Perm.mem_alternatingGroup.2 hσ⟩
    refine ⟨l, hKN l.2, fun v w hw => ?_⟩
    have := hβ l v w hw
    rw [hl] at this
    exact this
  have hS5 : Subgroup.normalizer (V : Set S) ≤ S5Stab V β := fun y hy => ⟨hy, hperm y hy⟩
  have h2 := (hloc V β hD).2
  rw [Subgroup.relIndex_eq_one.2 hS5] at h2
  omega

end Main

end CFSG.Quasithin.H13.CTK
