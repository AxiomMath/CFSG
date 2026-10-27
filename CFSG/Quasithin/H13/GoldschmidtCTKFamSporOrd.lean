module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamSporLoc
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3J2
public import CFSG.Quasithin.H13.GoldschmidtCTKFamCore

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint.NativeSporadic

variable {S : Type} [Group S]

theorem A5Config.exists_card_eq (h : A5Config S) : ∃ K : Subgroup S, Nat.card K = 960 := by
  obtain ⟨K, V, -, -, hVK, hV16, -, hΔ, -⟩ := h
  refine ⟨K, hΔ.card_eq ?_⟩
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV16]

theorem not_a5Config_of_not_dvd [Finite S] {n : ℕ} (hn : Nat.card S = n) (hd : ¬ 960 ∣ n) :
    ¬ A5Config S := by
  intro h
  obtain ⟨K, hK⟩ := h.exists_card_eq
  have h1 : Nat.card K ∣ Nat.card S := Subgroup.card_subgroup_dvd_card K
  rw [hK, hn] at h1
  exact hd h1

theorem not_a5Config_m11 [Finite S] (e : S ≃* Carrier .M11) :
    ¬ A5Config S :=
  not_a5Config_of_not_dvd (n := 7920)
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Mathieu.card_M11) (by norm_num)

theorem not_a5Config_j1 [Finite S] (e : S ≃* Carrier .J1) :
    ¬ A5Config S :=
  not_a5Config_of_not_dvd (n := 175560)
    ((Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J1.card_J1) (by norm_num)

theorem not_a5Config_m12 [Finite S] (e : S ≃* Carrier .M12) :
    ¬ A5Config S := by
  intro h
  obtain ⟨K, hK⟩ := h.exists_card_eq
  exact CFSG.QuasithinUnique.A5.G3.false_of_m12 e (n := 4) le_rfl (by rw [hK]; norm_num)

theorem A5Config.exists_five (h : A5Config S) :
    ∃ (V : Subgroup S) (x : S), IsElemAbelian 2 V ∧ Nat.card V = 16 ∧ orderOf x = 5 ∧
      (∀ v ∈ V, x * v * x⁻¹ ∈ V) ∧ ∀ v ∈ V, x * v * x⁻¹ = v → v = 1 := by
  obtain ⟨K, V, -, -, hVK, hV16, hel, hΔ, -⟩ := h
  have hKN : K ≤ Subgroup.normalizer (V : Set S) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVK).1 hΔ.normal
  have hcardV : Nat.card ↥(V.subgroupOf K) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv, hV16]
  obtain ⟨x, hxK, hx5⟩ := exists_orderOf_five_of_card_eq_960 (hΔ.card_eq hcardV)
  refine ⟨V, x, hel, hV16, hx5, fun v hv => (Subgroup.mem_normalizer_iff.1 (hKN hxK) v).1 hv,
    fun v hv hfix => ?_⟩
  obtain ⟨α, hα, hαk, β, hβ, hact⟩ := hΔ
  have hℓ5 : orderOf (⟨x, hxK⟩ : ↥K) = 5 := (Subgroup.orderOf_coe (⟨x, hxK⟩ : ↥K)).symm.trans hx5
  have hℓp : (⟨x, hxK⟩ : ↥K) ^ 5 = 1 := hℓ5 ▸ pow_orderOf_eq_one _
  have hσ5 : ((α ⟨x, hxK⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow, hℓp, map_one]
    rfl
  have hσ1 : ((α ⟨x, hxK⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro h1
    have hker : (⟨x, hxK⟩ : ↥K) ∈ α.ker := by
      rw [MonoidHom.mem_ker]
      exact Subtype.ext h1
    rw [hαk] at hker
    have hpg : IsPGroup 2 ↥(V.subgroupOf K) := IsPGroup.of_card (n := 4) (by rw [hcardV]; norm_num)
    exact CFSG.QuasithinUnique.A5.G3.false_of_isPGroup_of_orderOf_five hpg
      (z := ⟨⟨x, hxK⟩, hker⟩) (by rw [← Subgroup.orderOf_coe]; exact hℓ5)
  set u : ↥(V.subgroupOf K) := ⟨⟨v, hVK hv⟩, hv⟩ with hu
  have hcomm : ((u : ↥K)) = ⟨x, hxK⟩ * (u : ↥K) * ⟨x, hxK⟩⁻¹ :=
    Subtype.ext (by simpa using hfix.symm)
  have hzero := CFSG.QuasithinUnique.A5.G3.vector_eq_zero_of_fixed hσ5 hσ1
    (Multiplicative.toAdd (β u)) (fun i => (hact ⟨x, hxK⟩ u u hcomm i).symm)
  have hu1 : u = 1 := by
    apply hβ.1
    rw [map_one]
    apply Multiplicative.toAdd.injective
    simpa using hzero
  exact congrArg (fun z : ↥(V.subgroupOf K) => (((z : ↥K)) : S)) hu1

theorem not_a5Config_j2
    (e : S ≃* Carrier .J2) : ¬ A5Config S := by
  intro h
  obtain ⟨V, x, hel, hV16, hx5, hnorm, hfpf⟩ := h.exists_five
  have hcent := CFSG.QuasithinUnique.A5.G3.centralizes_of_noPair
    (CFSG.QuasithinUnique.A5.G3.noPairTwoFive_of_isSporadic (Nonempty.intro e)) hel hx5 hnorm
  have hbot : V = ⊥ := (Subgroup.eq_bot_iff_forall V).2 fun v hv => hfpf v hv (hcent v hv)
  rw [hbot, Subgroup.card_bot] at hV16
  omega

end CFSG.Quasithin.H13.CTK
