module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Model
public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelExtract
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Background.A4Aut
public import CFSG.Quasithin.Vol2.Ch10SecABasicV
public import CFSG.Quasithin.Vol2.Ch3T326S
public import CFSG.Quasithin.Vol2.Ch7Bridge326

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch10
open CFSG.Quasithin.Vol2.Ch10.SecA
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem exists_uModel [IsMulCommutative ↥(fsuVM T L I)] (hfsu : FSU G T L I)
    (hiv : Case3_2_6_iv T L I) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 4 ≤ Nat.card K ∧
      Nonempty (UModel (fsuVM T L I) (fsuUL T L I)
        (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) L K) := by
  obtain ⟨n, K, hF, hfin, hcard, hlie, hds⟩ := hiv
  have hn : 2 ≤ n := two_le_of_lieModel_psl_two hlie
  have hK4 : 4 ≤ Nat.card K := by
    rw [hcard]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hcard])
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hUA : fsuUL T L I ≤ fsuVM T L I := by
    refine Subgroup.commutator_le.mpr fun a ha l hl => ?_
    have hlv : l * a⁻¹ * l⁻¹ ∈ fsuVM T L I :=
      (Subgroup.mem_normalizer_iff.mp (hLN hl) a⁻¹).mp (inv_mem ha)
    rw [commutatorElement_def, show a * l * a⁻¹ * l⁻¹ = a * (l * a⁻¹ * l⁻¹) by group]
    exact mul_mem ha hlv
  let e₁ : ↥((fsuUL T L I).subgroupOf (fsuVM T L I)) ≃* ↥(fsuUL T L I) :=
    Subgroup.subgroupOfEquivOfLe hUA
  have hsymm : ∀ y : ↥(fsuUL T L I),
      (((e₁.symm y : ↥((fsuUL T L I).subgroupOf (fsuVM T L I))) : ↥(fsuVM T L I)) : G) =
        (y : G) := fun y =>
    (Subgroup.subgroupOfEquivOfLe_apply_coe hUA (e₁.symm y)).symm.trans
      (congrArg Subtype.val (e₁.apply_symm_apply y))
  obtain ⟨π, ψ', hψ'surj, hψ'ker, hψ'equiv⟩ :=
    exists_model_of_directSumOfCopies (autOn L (fsuVM T L I)) _ _ hds
  let ψ : ↥(fsuUL T L I) →* Multiplicative ((Fin 2 → K) × (Fin 2 → K)) :=
    ψ'.comp e₁.symm.toMonoidHom
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hψ'surj y
    refine ⟨e₁ x, ?_⟩
    show ψ' (e₁.symm (e₁ x)) = y
    rw [MulEquiv.symm_apply_apply]
    exact hx
  have hψker : ∀ u : ↥(fsuUL T L I),
      ψ u = 1 ↔ (u : G) ∈ fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) := by
    intro u
    have hk := hψ'ker (e₁.symm u)
    rw [Subgroup.mem_subgroupOf, hsymm] at hk
    exact hk
  let ψ₀ : ↥L →* ↥(autOn L (fsuVM T L I)) :=
    ((conjAct (fsuVM T L I)).comp (Subgroup.inclusion hLN)).codRestrict _
      fun l => ⟨Subgroup.inclusion hLN l, l.2, rfl⟩
  have hψ₀surj : Function.Surjective ψ₀ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  let γ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) K := π.symm.toMonoidHom.comp ψ₀
  have hγsurj : Function.Surjective γ := π.symm.surjective.comp hψ₀surj
  have hγker : ∀ l : ↥L, γ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (fsuVM T L I : Set G) := by
    intro l
    have h1 : γ l = 1 ↔ ψ₀ l = 1 := π.symm.map_eq_one_iff
    have h2 : ψ₀ l = 1 ↔ conjAct (fsuVM T L I) ⟨(l : G), hLN l.2⟩ = 1 :=
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [h1, h2, A4.conjAct_eq_one_iff]
  have hact : ∀ (l : ↥L) (x : ↥(fsuVM T L I)),
      (((π (γ l) : ↥(autOn L (fsuVM T L I))) : MulAut ↥(fsuVM T L I)) x : G) =
        (l : G) * (x : G) * (l : G)⁻¹ := by
    intro l x
    rw [show π (γ l) = ψ₀ l from π.apply_symm_apply (ψ₀ l)]
    exact coe_conjAct_apply' (Subgroup.inclusion hLN l) x
  have hequiv : ∀ (l : ↥L) (u : ↥(fsuUL T L I))
      (hu : (l : G) * (u : G) * (l : G)⁻¹ ∈ fsuUL T L I),
      ψ ⟨(l : G) * (u : G) * (l : G)⁻¹, hu⟩ =
        Multiplicative.ofAdd (rhoSL K (γ l) (Multiplicative.toAdd (ψ u))) := by
    intro l u hu
    have hmem : ((π (γ l) : MulAut ↥(fsuVM T L I))
        ((e₁.symm u : ↥((fsuUL T L I).subgroupOf (fsuVM T L I))) : ↥(fsuVM T L I))) ∈
          (fsuUL T L I).subgroupOf (fsuVM T L I) := by
      rw [Subgroup.mem_subgroupOf, hact, hsymm]
      exact hu
    have key := hψ'equiv (γ l) (e₁.symm u) hmem
    have heq : e₁.symm ⟨(l : G) * (u : G) * (l : G)⁻¹, hu⟩ =
        ⟨(π (γ l) : MulAut ↥(fsuVM T L I))
          ((e₁.symm u : ↥((fsuUL T L I).subgroupOf (fsuVM T L I))) : ↥(fsuVM T L I)), hmem⟩ := by
      apply Subtype.ext
      apply Subtype.ext
      show (((e₁.symm ⟨(l : G) * (u : G) * (l : G)⁻¹, hu⟩ :
          ↥((fsuUL T L I).subgroupOf (fsuVM T L I))) : ↥(fsuVM T L I)) : G) =
        ((π (γ l) : MulAut ↥(fsuVM T L I))
          ((e₁.symm u : ↥((fsuUL T L I).subgroupOf (fsuVM T L I))) : ↥(fsuVM T L I)) : G)
      rw [hsymm, hact, hsymm]
    show ψ' (e₁.symm ⟨(l : G) * (u : G) * (l : G)⁻¹, hu⟩) =
      Multiplicative.ofAdd (rhoSL K (γ l) (Multiplicative.toAdd (ψ' (e₁.symm u))))
    rw [heq]
    exact key
  exact ⟨K, hF, hfin, hchar, hK4, ⟨UModel.mk ψ hψsurj hψker γ hγsurj hγker hequiv⟩⟩

end CFSG.Quasithin.Vol2.Ch10Reselect
