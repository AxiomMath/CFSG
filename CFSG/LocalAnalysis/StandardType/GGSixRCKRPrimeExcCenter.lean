module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Open (IsElemAbelian)

private theorem rckExc_exists_ne_one_centralizer {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {U D : Subgroup X} (hUp : IsPGroup p U) (hUne : U ≠ ⊥) (hDp : IsPGroup p D)
    (hDU : D ≤ Subgroup.normalizer (U : Set X)) :
    ∃ y ∈ U, y ≠ 1 ∧ y ∈ Subgroup.centralizer (D : Set X) := by
  have hB : IsPGroup p (↥(U ⊔ D)) := hUp.to_sup_of_normal_left' hDp hDU
  have hBN : U ⊔ D ≤ Subgroup.normalizer (U : Set X) := sup_le Subgroup.le_normalizer hDU
  haveI : (U.subgroupOf (U ⊔ D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 hBN
  haveI : Group.IsNilpotent ↥(U ⊔ D) := hB.isNilpotent
  have hne : U.subgroupOf (U ⊔ D) ≠ ⊥ := by
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    intro hbot
    apply hu1
    have hmem : (⟨u, Subgroup.mem_sup_left u.2⟩ : ↥(U ⊔ D)) ∈ U.subgroupOf (U ⊔ D) := u.2
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 : ((⟨u, Subgroup.mem_sup_left u.2⟩ : ↥(U ⊔ D)) : X) = ((1 : ↥(U ⊔ D)) : X) :=
      congrArg Subtype.val hmem
    exact Subtype.ext h2
  have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hW
  refine ⟨(((a : ↥(U.subgroupOf (U ⊔ D) ⊓ Subgroup.center ↥(U ⊔ D))) : ↥(U ⊔ D)) : X), a.2.1,
    ?_, ?_⟩
  · intro h1
    apply ha1
    exact Subtype.ext (Subtype.ext h1)
  · refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 a.2.2 ⟨w, Subgroup.mem_sup_right hw⟩)

theorem rck_p_not_dvd_center {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {G₀ A : Subgroup X} (hAel : IsElemAbelian p A)
    (hAN : A ≤ Subgroup.normalizer (G₀ : Set X))
    (hSC : ∀ y ∈ (A ⊔ G₀) ⊓ Subgroup.centralizer (A : Set X), orderOf y = p → y ∈ A)
    (hAC : A ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) :
    ¬ p ∣ Nat.card (Subgroup.center ↥G₀) := by
  intro hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  let E : Subgroup X :=
    { carrier := {y | y ∈ G₀ ∧ (∀ g ∈ G₀, y * g = g * y) ∧ y ^ p = 1}
      mul_mem' := by
        rintro a b ⟨haG, hac, hap⟩ ⟨hbG, hbc, hbp⟩
        refine ⟨G₀.mul_mem haG hbG, fun g hg => ?_, ?_⟩
        · rw [mul_assoc, hbc g hg, ← mul_assoc, hac g hg, mul_assoc]
        · rw [(show Commute a b from hac b hbG).mul_pow, hap, hbp, mul_one]
      one_mem' := ⟨G₀.one_mem, fun g _ => by simp, one_pow p⟩
      inv_mem' := by
        rintro a ⟨haG, hac, hap⟩
        refine ⟨G₀.inv_mem haG, fun g hg => ?_, ?_⟩
        · exact ((show Commute a g from hac g hg).inv_left : Commute a⁻¹ g)
        · rw [inv_pow, hap, inv_one] }
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥G₀)) p hdvd
  have hyord : orderOf (((z : ↥G₀)) : X) = p := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hyE : (((z : ↥G₀)) : X) ∈ E := by
    refine ⟨(z : ↥G₀).2, fun g hg => ?_, ?_⟩
    · have := Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩
      exact congrArg Subtype.val this.symm
    · rw [← hyord]; exact pow_orderOf_eq_one _
  have hEne : E ≠ ⊥ := by
    intro h
    have h1 : (((z : ↥G₀)) : X) = 1 := by
      have := hyE; rw [h] at this; exact Subgroup.mem_bot.mp this
    rw [h1, orderOf_one] at hyord
    exact hp.one_lt.ne hyord
  have hEp : IsPGroup p E := fun g => ⟨1, by apply Subtype.ext; simpa using g.2.2.2⟩
  have hAp : IsPGroup p A := fun a => ⟨1, by apply Subtype.ext; simpa using hAel.2 a a.2⟩
  have hconj : ∀ a ∈ A, ∀ x ∈ E, a * x * a⁻¹ ∈ E := by
    intro a ha x hx
    obtain ⟨hxG, hxc, hxp⟩ := hx
    have haG := Subgroup.mem_normalizer_iff.mp (hAN ha)
    refine ⟨(haG x).mp hxG, fun g hg => ?_, ?_⟩
    · have hg' : a⁻¹ * g * a ∈ G₀ := by
        have := (Subgroup.mem_normalizer_iff.mp (hAN (A.inv_mem ha)) g).mp hg
        simpa using this
      have hxg := hxc _ hg'
      calc a * x * a⁻¹ * g = a * (x * (a⁻¹ * g * a)) * a⁻¹ := by group
        _ = a * ((a⁻¹ * g * a) * x) * a⁻¹ := by rw [hxg]
        _ = g * (a * x * a⁻¹) := by group
    · calc (a * x * a⁻¹) ^ p = a * x ^ p * a⁻¹ := by rw [conj_pow]
        _ = 1 := by rw [hxp]; group
  have hAE : A ≤ Subgroup.normalizer (E : Set X) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hconj a ha x, fun hx => ?_⟩
    have h1 := hconj a⁻¹ (A.inv_mem ha) _ hx
    have h2 : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
    rw [h2] at h1
    exact h1
  obtain ⟨w, hwE, hw1, hwC⟩ :=
    rckExc_exists_ne_one_centralizer
      hEp hEne hAp hAE
  have hword : orderOf w = p := orderOf_eq_prime hwE.2.2 hw1
  have hwA : w ∈ A :=
    hSC w ⟨Subgroup.mem_sup_right hwE.1, hwC⟩ hword
  have hwC' : w ∈ Subgroup.centralizer (G₀ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (hwE.2.1 g hg).symm
  have : w ∈ A ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨hwA, hwC'⟩
  rw [hAC] at this
  exact hw1 (Subgroup.mem_bot.mp this)

end CFSG.StandardType.RCKRP
