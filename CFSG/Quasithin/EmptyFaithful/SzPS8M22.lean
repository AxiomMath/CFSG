module

public import CFSG.Quasithin.EmptyFaithful.SzPS8Ovg
public import CFSG.Quasithin.EmptyFaithful.SzPS8Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11

namespace SzPS8

section Three

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {Γ T0 : Subgroup (V ≃ₗ[ZMod 2] V)} {v : V}

theorem OvgSetting.false_of_normal_card_three (S : OvgSetting Γ T0 v) (Z : Subgroup ↥Γ)
    (hZ : Z.Normal) (hZ3 : Nat.card ↥Z = 3)
    (hZN : ∀ N : Subgroup ↥Γ, N.Normal → N ≠ ⊥ → Z ≤ N) : False := by
  classical
  have : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun e => (e : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)
  obtain ⟨N, hNn, hN1, hF⟩ := S.exists_normal_subtype
  have hT0Γ : T0 ≤ Γ := S.sylow.1
  have hT2 : IsPGroup 2 ↥(T0.subgroupOf Γ) :=
    S.sylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT0Γ).symm
  have hinf : Nat.card ↥(T0.subgroupOf Γ ⊓ Z) = 1 := by
    obtain ⟨n, hn⟩ := (hT2.to_inf_left (K := Z)).exists_card_eq
    have hdvd : Nat.card ↥(T0.subgroupOf Γ ⊓ Z) ∣ Nat.card ↥Z :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hn, hZ3] at hdvd
    rcases n with _ | n
    · simpa using hn
    · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero n)) hdvd) (by norm_num)
  have hidx : (T0.subgroupOf Γ).relIndex Z = 3 ∨ (T0.subgroupOf Γ).relIndex Z = 5 := by
    left
    have := Subgroup.relIndex_mul_card (H := T0.subgroupOf Γ) (K := Z)
    rwa [hinf, mul_one, hZ3] at this
  have hfix : ∀ α ∈ Z, (α : V ≃ₗ[ZMod 2] V) v = v :=
    hF.fix_of_subgroup hT0Γ Z (Subgroup.map_mono (hZN N hNn hN1))
      (fun t _ j hj => hZ.conj_mem j hj t) hidx
  have hZ1 : Z.map Γ.subtype ≠ ⊥ := by
    intro hbot
    have hZbot : Z = ⊥ := (Subgroup.map_eq_bot_iff_of_injective Z Γ.subtype_injective).mp hbot
    rw [hZbot, Subgroup.card_bot] at hZ3
    exact absurd hZ3 (by norm_num)
  refine S.false_of_fixes (N := Z.map Γ.subtype) ?_ hZ1 ?_
  · rintro γ hγ _ ⟨z, hz, rfl⟩
    exact ⟨⟨γ, hγ⟩ * z * ⟨γ, hγ⟩⁻¹, hZ.conj_mem z hz ⟨γ, hγ⟩, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hfix z hz

end Three

theorem excl13S_of_ovg (h11 : StageLemma14111) (h113 : StageLemma14113) (h35 : Lemma1435) :
    Lemma14315Excl13S := by
  intro G _ _ T M hyp hnot hU D hc
  obtain ⟨v, S⟩ := exists_ovgSetting h11 h113 h35 hyp hnot hU D
  obtain ⟨-, ⟨Z, hZn, hZ3, hZN⟩, -⟩ := hc
  exact (S.false_of_normal_card_three Z hZn hZ3 hZN).elim

end SzPS8

end CFSG.Quasithin
