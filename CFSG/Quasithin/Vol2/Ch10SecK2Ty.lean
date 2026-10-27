module

public import CFSG.Quasithin.Vol2.Ch10SecK2Tx
public import CFSG.Quasithin.Vol2.Ch10SecK2Tv

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Ch11.SecA
open scoped IsMulCommutative

variable {Γ : Type} [Group Γ]

theorem exists_equivJ {J V : Subgroup Γ} [IsMulCommutative ↥V]
    (hJV : J ≤ Subgroup.normalizer (V : Set Γ)) {D : FFModel} {π : D.Gam →* ↥(autOn J V)}
    {I₀ I₁ : Subgroup ↥V} (h₀ : D.RealizesVia (autOn J V) I₀ ⊥ π)
    (h₁ : D.RealizesVia (autOn J V) I₁ ⊥ π)
    (hJ₀ : J ≤ Subgroup.normalizer ((I₀.map V.subtype : Subgroup Γ) : Set Γ)) :
    ∃ ι : ↥(I₀.map V.subtype) ≃* ↥(I₁.map V.subtype), ∀ (g : Γ) (hg : g ∈ J)
      (w : ↥(I₀.map V.subtype)),
      ((ι ⟨g * w * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJ₀ hg) w).mp w.2⟩ :
        ↥(I₁.map V.subtype)) : Γ) = g * ι w * g⁻¹ := by
  obtain ⟨e, he⟩ := InternalSec.equiv_of_secIsoL (Ch11.SecC.B51.secIsoL_of_realizesVia h₀ h₁)
  set f₀ := Subgroup.equivMapOfInjective I₀ V.subtype V.subtype_injective with hf₀
  set f₁ := Subgroup.equivMapOfInjective I₁ V.subtype V.subtype_injective with hf₁
  refine ⟨f₀.symm.trans (e.trans f₁), fun g hg w => ?_⟩
  obtain ⟨w', rfl⟩ := f₀.surjective w
  set k : ↥(autOn J V) := ⟨conjAct V ⟨g, hJV hg⟩, InternalSec.conjAct_mem_autOn hJV hg⟩ with hk
  have hkw : (k : MulAut ↥V) (w' : ↥V) ∈ I₀ := h₀.2.2.2.1 k w' w'.2
  have hkw' : (k : MulAut ↥V) (e w' : ↥V) ∈ I₁ := h₁.2.2.2.1 k _ (e w').2
  have h1 := he k w' hkw hkw'
  have h2 : (⟨g * (f₀ w' : Γ) * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJ₀ hg) _).mp (f₀ w').2⟩ :
      ↥(I₀.map V.subtype)) = f₀ ⟨(k : MulAut ↥V) (w' : ↥V), hkw⟩ := by
    apply Subtype.ext
    show g * (f₀ w' : Γ) * g⁻¹ = (f₀ ⟨(k : MulAut ↥V) (w' : ↥V), hkw⟩ : Γ)
    rw [Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_equivMapOfInjective_apply]
    exact (Setup.coe_conjAct_apply (G := Γ) (V := V) ⟨g, hJV hg⟩ w').symm
  rw [h2, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply, h1,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulEquiv.trans_apply,
    Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_equivMapOfInjective_apply]
  exact Setup.coe_conjAct_apply (G := Γ) (V := V) ⟨g, hJV hg⟩ (e w')

section Case1ii

variable [Finite Γ]

theorem torus_case1ii {R J L V₁ V : Subgroup Γ} {n m : ℕ} (hV : IsElemAbelian 2 V)
    [IsMulCommutative ↥V] (hC : K2Ctx R J L V₁ V n) (hV₁U : V₁ ≤ ⁅V, J⁆)
    (hX : KindJ ↥(autOn J V) m) {G : Subgroup (MulAut ↥V)} (hii : B51Case1ii G (autOn J V)) :
    ∃ y ∈ J ⊓ Subgroup.normalizer (V₁ : Set Γ), y ∉ Subgroup.centralizer (V₁ : Set Γ) ∧
      (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ)) ∧
      y ^ (2 ^ n - 1) ∈ Subgroup.centralizer (V₁ : Set Γ) := by
  obtain ⟨-, n', K, _, _, hK, I, π, hind, hsup, hreal, -, -⟩ := hii
  obtain ⟨hm, F, _, _, hF, he⟩ := hX
  have hn' := one_le_of_card_field hK
  have hπs : Function.Surjective π := (hreal 0).1
  have hπ' : Function.Surjective
      (π.comp (Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).toMonoidHom) :=
    hπs.comp (MulEquiv.surjective _)
  obtain ⟨e⟩ : Nonempty (↥(autOn J V) ≃* Matrix.SpecialLinearGroup (Fin 3) F) := by
    rcases he with h | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact h
    · exact (Ch11.SecC.B51.not_surjective_SL3_Sp4 hK hm hF (e.toMonoidHom.comp _)
        (e.surjective.comp hπ')).elim
    · exact (Ch11.SecC.B51.not_surjective_SL3_G2 KGNat.factG2DerivedOrder_holds hK hm hF
        (e.toMonoidHom.comp _) (e.surjective.comp hπ')).elim
  have hn2 : 2 ≤ n' := by
    by_contra h
    obtain rfl : n' = 1 := by omega
    have h1 := Nat.card_le_card_of_surjective _ (e.surjective.comp hπs)
    rw [card_statedSL_three1527d, hK, Ch11.SecC.B51.card_SL3_eq_pow hF] at h1
    have ha : 64 ≤ 2 ^ (3 * m) := by
      calc 64 = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (3 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb : 16 ≤ 2 ^ (2 * m) := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 64 * (63 * 15) ≤ 2 ^ (3 * m) * ((2 ^ (3 * m) - 1) * (2 ^ (2 * m) - 1)) :=
      Nat.mul_le_mul ha (Nat.mul_le_mul (by omega) (by omega))
    norm_num at h1
    omega
  have hJV := hC.hJV
  have h₁ : (I 0).map V.subtype ≤ V := Subgroup.map_subtype_le _
  have h₂ : (I 1).map V.subtype ≤ V := Subgroup.map_subtype_le _
  have hI₁ : ((I 0).map V.subtype).subgroupOf V = I 0 :=
    Subgroup.comap_map_eq_self_of_injective V.subtype_injective _
  have hI₂ : ((I 1).map V.subtype).subgroupOf V = I 1 :=
    Subgroup.comap_map_eq_self_of_injective V.subtype_injective _
  have hinv : ∀ i, ∀ σ ∈ autOn J V, ∀ u ∈ I i, σ u ∈ I i :=
    fun i σ hσ u hu => (hreal i).2.2.2.1 ⟨σ, hσ⟩ u hu
  have hJ₁ := Ch11.SecC.B51.le_normalizer_map_of_inv hJV (hinv 0)
  have hJ₂ := Ch11.SecC.B51.le_normalizer_map_of_inv hJV (hinv 1)
  have h12 : (I 0).map V.subtype ⊓ (I 1).map V.subtype = ⊥ := by
    rw [← Subgroup.map_inf_eq _ _ _ V.subtype_injective,
      disjoint_iff.mp (hind.pairwiseDisjoint (by decide)), Subgroup.map_bot]
  have h01 : I 0 ⊔ I 1 = commV (autOn J V) := by
    rw [← hsup]
    refine le_antisymm (sup_le (le_iSup I 0) (le_iSup I 1)) (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hU : (I 0).map V.subtype ⊔ (I 1).map V.subtype = ⁅V, J⁆ := by
    rw [← Subgroup.map_sup, h01, Ch11.SecC.B51.map_commV_autOn hJV]
  have : IsMulCommutative ↥((I 0).map V.subtype) := Ch11.SecC.B51.isMulCommutative_of_le h₁
  have : IsMulCommutative ↥((I 1).map V.subtype) := Ch11.SecC.B51.isMulCommutative_of_le h₂
  have hW2 : ∀ i, ∀ w : ↥((I i).map V.subtype), w ^ 2 = 1 := fun i w =>
    Subtype.ext (by simpa using hV.2 w (Subgroup.map_subtype_le _ w.2))
  have hHZ : ∀ {W : Subgroup Γ} [IsMulCommutative ↥W], ∀ h ∈ autOn J W,
      ∀ z ∈ (⊥ : Subgroup ↥W), h z = z := fun h _ z hz => by
    rw [Subgroup.mem_bot.mp hz, map_one]
  have hR₁ := Ch11.SecC.B51.realizesVia_resAutOn hJV hJ₁ h₁
    (D := FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)) (Z := ⊥) (π := π)
    (by rw [hI₁, Subgroup.bot_subgroupOf]; exact hreal 0)
  have hR₂ := Ch11.SecC.B51.realizesVia_resAutOn hJV hJ₂ h₂
    (D := FFModel.nat (Assembly.LowTwoRank.StatedSL 3 K)) (Z := ⊥) (π := π)
    (by rw [hI₂, Subgroup.bot_subgroupOf]; exact hreal 1)
  rw [Subgroup.bot_subgroupOf] at hR₁ hR₂
  have hD₁ := torusData_SL3 hn2 hK (hW2 0) hR₁ hHZ
  have hD₂ := torusData_SL3 hn2 hK (hW2 1) hR₂ hHZ
  obtain ⟨ι, hι⟩ := exists_equivJ hJV (hreal 0) (hreal 1) hJ₁
  exact torus_two_copies hV hC h₁ h₂ h12 hJ₁ hJ₂ (hU ▸ hV₁U) hD₁ hD₂ ι hι

end Case1ii

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
