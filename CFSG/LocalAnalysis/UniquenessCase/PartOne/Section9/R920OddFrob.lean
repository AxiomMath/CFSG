module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.GH74.Uniqueness.Bender.Core
import CFSG.LocalAnalysis.SteinbergCEFrobeniusComplementFixedVector
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddRed
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddRep

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.PSL2Table (unip diag unipSL diag_conj_unip diag_inv diag_one unip_mem_unipSL unip_zero)
open scoped MatrixGroups

theorem diag_zpow {F : Type} [Field F] (a : Fˣ) (j : ℤ) : diag (a ^ j) = diag a ^ j :=
  map_zpow (MonoidHom.mk' diag CFSG.PSL2Table.diag_mul) a j

theorem orderOf_diag {F : Type} [Field F] (a : Fˣ) : orderOf (diag a) = orderOf a :=
  orderOf_injective (MonoidHom.mk' diag CFSG.PSL2Table.diag_mul) (fun a b h => Units.ext (by
    have h1 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0)
      (show diag a = diag b from h)
    simpa using h1)) a

theorem exists_fixed_diag {k V : Type*} {F : Type} [Field k] [AddCommGroup V] [Module k V]
    [Field F] [Fintype F] (σ : Representation k SL(2, F) V) (hσ : Function.Injective σ)
    (hF : (Fintype.card F : k) ≠ 0) {μ : Fˣ} (hμ : Odd (orderOf μ)) :
    ∃ v : V, v ≠ 0 ∧ σ (diag μ) v = v := by
  classical
  have hKu : ∀ A ∈ unipSL F, A = unip ((A : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    intro A hA
    obtain ⟨h10, h00, h11⟩ := (CFSG.PSL2Table.mem_unipSL_iff A).mp hA
    exact CFSG.PSL2Table.SL_ext (by simp [h00]) (by simp) (by simp [h10]) (by simp [h11])
  have hconj : ∀ a : Fˣ, ∀ A ∈ unipSL F, diag a * A * (diag a)⁻¹ ∈ unipSL F := by
    intro a A hA
    rw [hKu A hA, diag_conj_unip]
    exact unip_mem_unipSL _
  have hRN : zpowers (diag μ) ≤ normalizer (unipSL F : Set SL(2, F)) :=
    (Subgroup.zpowers_le).mpr (Subgroup.mem_normalizer_iff.mpr fun A => ⟨hconj μ A, fun h => by
      have h' := hconj μ⁻¹ _ h
      rwa [← diag_inv, inv_inv,
        show (diag μ)⁻¹ * (diag μ * A * (diag μ)⁻¹) * diag μ = A by group] at h'⟩)
  have hKq : Nat.card (unipSL F) = Fintype.card F := CFSG.PSL2Table.card_unipSL
  have hRo : Nat.card (zpowers (diag μ)) = orderOf μ := by
    rw [Nat.card_zpowers, orderOf_diag]
  have hcop : Nat.Coprime (Nat.card (unipSL F)) (Nat.card (zpowers (diag μ))) := by
    have h1 : 1 ≤ Fintype.card F := Fintype.card_pos
    have h2 := Nat.coprime_self_add_right.mpr (Nat.coprime_one_right (Fintype.card F - 1))
    rw [Nat.sub_add_cancel h1] at h2
    rw [hKq, hRo]
    refine h2.symm.coprime_dvd_right ?_
    rw [← Nat.card_eq_fintype_card, ← Nat.card_units]
    exact orderOf_dvd_natCard μ
  have hfixSL : ∀ r ∈ zpowers (diag μ), r ≠ 1 → ∀ A ∈ unipSL F, A * r = r * A → A = 1 := by
    intro r hr hr1 A hA hAr
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
    rw [← diag_zpow] at hr1 hAr
    have ha1 : μ ^ j ≠ 1 := fun h => hr1 (by rw [h, diag_one])
    have hc : diag (μ ^ j) * A * (diag (μ ^ j))⁻¹ = A := by rw [← hAr, mul_inv_cancel_right]
    rw [hKu A hA, diag_conj_unip] at hc
    have ht : ((μ ^ j : Fˣ) : F) ^ 2 * (A : Matrix (Fin 2) (Fin 2) F) 0 1 =
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      have h1 := congrArg (fun C : SL(2, F) => (C : Matrix (Fin 2) (Fin 2) F) 0 1) hc
      simpa using h1
    rw [hKu A hA]
    by_cases ht0 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0
    · rw [ht0, unip_zero]
    · exfalso
      have h2 : (μ ^ j) ^ 2 = 1 := Units.ext (by
        rw [Units.val_pow_eq_pow_val, Units.val_one]
        exact (mul_eq_right₀ ht0).mp ht)
      have h3 := Nat.Coprime.eq_one_of_dvd ((Nat.coprime_two_right.mpr hμ).coprime_dvd_left
        (orderOf_dvd_of_mem_zpowers (Subgroup.mem_zpowers_iff.mpr ⟨j, rfl⟩)))
        (orderOf_dvd_of_pow_eq_one h2)
      exact ha1 (orderOf_eq_one_iff.mp h3)
  haveI : ((unipSL F).subgroupOf (unipSL F ⊔ zpowers (diag μ))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hRN)
  have hcK : Nat.card ((unipSL F).subgroupOf (unipSL F ⊔ zpowers (diag μ))) =
      Nat.card (unipSL F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have hcR : Nat.card ((zpowers (diag μ)).subgroupOf (unipSL F ⊔ zpowers (diag μ))) =
      Nat.card (zpowers (diag μ)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hKR : ((unipSL F).subgroupOf (unipSL F ⊔ zpowers (diag μ))).IsComplement'
      ((zpowers (diag μ)).subgroupOf (unipSL F ⊔ zpowers (diag μ))) := by
    refine Subgroup.isComplement'_of_coprime ?_ (by rw [hcK, hcR]; exact hcop)
    rw [hcK, hcR, CFSG.GH74.Uniqueness.Bender.card_sup_eq_mul_of_le_normalizer hRN
      (Subgroup.inf_eq_bot_of_coprime hcop)]
  obtain ⟨v, hv0, hv⟩ := CFSG.LocalAnalysis.frobenius_complement_fixed_vector hKR
    (fun r hr hr1 x hx hxr => Subtype.ext (hfixSL r (Subgroup.mem_subgroupOf.mp hr)
      (fun h => hr1 (Subtype.ext h)) x (Subgroup.mem_subgroupOf.mp hx)
      (congrArg Subtype.val hxr)))
    (by rw [hcK, hKq]; exact hF) (σ.asGroupHom.comp (unipSL F ⊔ zpowers (diag μ)).subtype)
    ⟨⟨unip 1, Subgroup.mem_sup_left (unip_mem_unipSL 1)⟩,
      Subgroup.mem_subgroupOf.mpr (unip_mem_unipSL 1), fun h => unip_one_ne_one (hσ (by
        have h1 := congrArg Units.val h
        rw [MonoidHom.comp_apply, Representation.asGroupHom_apply, Units.val_one] at h1
        rw [map_one]
        exact h1))⟩
  have h := hv ⟨diag μ, Subgroup.mem_sup_right (mem_zpowers _)⟩
    (Subgroup.mem_subgroupOf.mpr (mem_zpowers _))
  rw [MonoidHom.comp_apply, Representation.asGroupHom_apply] at h
  exact ⟨v, hv0, h⟩

variable {G : Type} [Group G] [Finite G]

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem I9_le_M_of_odd_dvd (S : Slice D L D₃ Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M)
    {E : Subgroup G} (hyp : F09.Hyp91 D Y H E) (hr : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ q - 1)
    (hK461 : UCK.K461) (hK462 : UCK.K462) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) :
    F09.I9 H ≤ D.M := by
  by_contra hIM
  obtain ⟨p, hp, F, hF, hFt, V, hV, hVm, hVf, σ, hcard, -, hpq, hσ, -, hfpf⟩ :=
    S.exists_sl2_rep_of_not_le hN hyp hK461 hK462 hSch hIM
  obtain ⟨r, hrp, hr2, hrq⟩ := hr
  haveI : Fact r.Prime := ⟨hrp⟩
  obtain ⟨μ, hμ⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by
    rw [Nat.card_units, Nat.card_eq_fintype_card, hcard]
    exact hrq)
  have hqp : (Fintype.card F : ZMod p) ≠ 0 := by
    rw [hcard, Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp.out S.prime).mp h)
  obtain ⟨v, hv0, hv⟩ := exists_fixed_diag σ hσ hqp (μ := μ)
    (by rw [hμ]; exact hrp.odd_of_ne_two hr2)
  have hdo : orderOf (diag μ) = r := by rw [orderOf_diag, hμ]
  exact hv0 (hfpf _ (by rw [hdo]; exact hrp) (by rw [hdo]; exact hr2) v hv)

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
