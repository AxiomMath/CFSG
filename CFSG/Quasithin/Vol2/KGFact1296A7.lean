module

public import CFSG.Quasithin.Vol2.KGFact1296Red
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.H13.KG1296

open Equiv Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem mem_zpowers_of_commute {c σ : Perm (Fin 7)} (hc : orderOf c = 7) (hσ : Commute σ c) :
    σ ∈ Subgroup.zpowers c := by
  classical
  have hcyc : c.IsCycle := Perm.isCycle_of_prime_order' (by rw [hc]; norm_num)
    (by rw [hc, Fintype.card_fin]; norm_num)
  have hsupp : c.support = Finset.univ := by
    have h := hcyc.orderOf
    rw [hc] at h
    exact Finset.eq_univ_of_card _ (by rw [← h, Fintype.card_fin])
  obtain ⟨hc', hmem⟩ := hcyc.commute_iff.1 hσ
  have h1 : Perm.ofSubtype (σ.subtypePerm hc') = σ :=
    Perm.ofSubtype_subtypePerm hc' fun x _ => by rw [hsupp]; exact Finset.mem_univ x
  rwa [h1] at hmem

theorem eq_one_of_forall_fix {B : Subgroup (alternatingGroup (Fin 7))} (hB : Nat.card B = 168)
    {α : MulAut (alternatingGroup (Fin 7))} (hα : ∀ x ∈ B, α x = x) : α = 1 := by
  obtain ⟨σ, rfl⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)).2 α
  have hcomm : ∀ x ∈ B, Commute σ ((x : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    intro x hx
    have h := congrArg Subtype.val (hα x hx)
    rw [MulAut.conjNormal_apply] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 7 (by rw [hB]; norm_num)
  have hc' : orderOf ((c : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 7 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc]
  have hσc := mem_zpowers_of_commute hc' (hcomm c c.2)
  by_contra hne
  have hσ1 : σ ≠ 1 := fun h => hne (by rw [h, map_one])
  have hσ7 : orderOf σ = 7 := by
    have h := orderOf_dvd_of_mem_zpowers hσc
    rw [hc'] at h
    rcases (Nat.dvd_prime (by norm_num)).1 h with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hσ1
    · exact h1
  have hBle : ∀ x ∈ B, ((x : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ Subgroup.zpowers σ :=
    fun x hx => mem_zpowers_of_commute hσ7 (hcomm x hx).symm
  have hinj : Function.Injective (fun x : ↥B =>
      (⟨((x : alternatingGroup (Fin 7)) : Perm (Fin 7)), hBle x x.2⟩ :
        ↥(Subgroup.zpowers σ))) :=
    fun x y h => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  have h := Nat.card_le_card_of_injective _ hinj
  rw [hB, Nat.card_zpowers, hσ7] at h
  omega

theorem pCoreOf_eq_bot_of_A7 {B : Subgroup (alternatingGroup (Fin 7))}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 3) (ZMod 2))) :
    pCoreOf 2 B = ⊥ ∧ Nat.card B = 168 := by
  obtain ⟨e⟩ := hB
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h168 : Nat.card (ModO2 B) = 168 := by
    rw [Nat.card_congr e.toEquiv, card_SL_eq (by norm_num), Nat.card_zmod]
    decide
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥B))
  have hdvd : Nat.card B ∣ 168 * 15 := by
    rw [show 168 * 15 = 2520 from rfl, ← card_alternatingGroup_seven]
    exact Subgroup.card_subgroup_dvd_card B
  rw [hcard, h168, hr] at hdvd
  have h15 : 2 ^ r ∣ 15 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have hr0 : r = 0 := by
    by_contra h
    have h2 : 2 ∣ 15 := (dvd_pow_self 2 h).trans h15
    omega
  rw [hr0, pow_zero] at hr
  have hbot : CFSG.pCore 2 ↥B = ⊥ := Subgroup.eq_bot_of_card_eq _ hr
  refine ⟨?_, by rw [hcard, h168, hr, mul_one]⟩
  rw [pCoreOf, hbot, Subgroup.map_bot]

theorem innClosed_A7 {B : Subgroup (alternatingGroup (Fin 7))}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 3) (ZMod 2))) : InnClosed B := by
  obtain ⟨hO2, hcard⟩ := pCoreOf_eq_bot_of_A7 hB
  intro α _ h2
  refine ⟨1, B.one_mem, ?_⟩
  rw [map_one]
  refine eq_one_of_forall_fix hcard fun x hx => ?_
  have h := h2 x hx
  rw [hO2, Subgroup.mem_bot, mul_inv_eq_one] at h
  exact h

theorem parConclusion_A7 {B : Subgroup (alternatingGroup (Fin 7))}
    (hB : Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 3) (ZMod 2))) (m : ℕ) :
    ParConclusion B m := by
  obtain ⟨hO2, -⟩ := pCoreOf_eq_bot_of_A7 hB
  intro Q hQ _ hQbot
  rw [hO2] at hQ
  exact absurd (eq_bot_iff.2 hQ) hQbot

theorem not_modO2_SL4_of_A7 {B : Subgroup (alternatingGroup (Fin 7))} :
    ¬ Nonempty (ModO2 B ≃* SpecialLinearGroup (Fin 4) (ZMod 2)) := by
  rintro ⟨e⟩
  have hcard : Nat.card B = Nat.card (ModO2 B) * Nat.card (CFSG.pCore 2 ↥B) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h1 : Nat.card (ModO2 B) = 20160 := by
    rw [Nat.card_congr e.toEquiv, card_SL_eq (by norm_num), Nat.card_zmod]
    decide
  have h2 : Nat.card B ≤ 2520 := card_alternatingGroup_seven ▸ Subgroup.card_le_card_group B
  have h3 : 0 < Nat.card (CFSG.pCore 2 ↥B) := Nat.card_pos
  rw [hcard, h1] at h2
  omega

end CFSG.Quasithin.H13.KG1296
