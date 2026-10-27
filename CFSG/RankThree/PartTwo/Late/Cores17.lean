module

import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG

section Decomposition

variable {G : Type*} [Group G] [Finite G]

theorem iSup_inf_centralizer_eq_and_iSupIndep {r : ℕ} (hr : r.Prime) {B X : Subgroup G}
    (hB : CFSG.Assembly.IsElemAbelian r B) (hB2 : Nat.card B = r ^ 2)
    (hBX : B ≤ Subgroup.normalizer (X : Set G)) (hX : IsMulCommutative X)
    (hcop : Nat.Coprime r (Nat.card X)) (hfix : X ⊓ Subgroup.centralizer (B : Set G) = ⊥) :
    (⨆ D : {D : Subgroup G // D ≤ B ∧ Nat.card D = r},
        X ⊓ Subgroup.centralizer ((D : Subgroup G) : Set G)) = X ∧
      iSupIndep fun D : {D : Subgroup G // D ≤ B ∧ Nat.card D = r} =>
        X ⊓ Subgroup.centralizer ((D : Subgroup G) : Set G) := by
  refine ⟨le_antisymm (iSup_le fun D => inf_le_left) ?_, ?_⟩
  ·
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation r 1 hr
      B X hB (le_of_eq (by rw [hB2])) hBX hcop
    conv_lhs => rw [← hgen]
    exact iSup₂_le fun D hD => le_iSup_of_le ⟨D, hD.1, by rw [hD.2, pow_one]⟩ le_rfl
  let : CommGroup X := IsMulCommutative.instCommGroup
  rw [iSupIndep_def]
  intro D₀
  rw [Subgroup.disjoint_def]
  intro x hx₀ hx
  let := Fintype.ofFinite (D₀ : Subgroup G)
  let ψ : Subgroup.normalizer (X : Set G) → (X →* X) := fun g =>
    (X.normalizerMonoidHom g).toMonoidHom
  have hψ : ∀ g y, ((ψ g y : X) : G) = g * y * (g : G)⁻¹ := fun g y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X g y
  have hcent : ∀ (g : Subgroup.normalizer (X : Set G)) (z : X), ψ g z = z →
      (g : G) ∈ Subgroup.centralizer {(z : G)} := by
    intro g z h
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h' := congrArg Subtype.val h
    rw [hψ, mul_inv_eq_iff_eq_mul] at h'
    exact h'
  let φ : ↥(D₀ : Subgroup G) → (X →* X) := fun d => ψ ⟨d, hBX (D₀.2.1 d.2)⟩
  have hφ : ∀ (d : (D₀ : Subgroup G)) (y : X), ((φ d y : X) : G) = d * y * (d : G)⁻¹ :=
    fun d y => hψ _ y
  let N : X →* X := ∏ d : (D₀ : Subgroup G), φ d
  have hN : ∀ y : X, N y = ∏ d : (D₀ : Subgroup G), φ d y := fun y =>
    MonoidHom.finsetProd_apply _ _ _
  have hpow : ∀ y : X, (y : G) ∈ Subgroup.centralizer ((D₀ : Subgroup G) : Set G) →
      N y = y ^ r := by
    intro y hy
    have hfixd : ∀ d : (D₀ : Subgroup G), φ d y = y := fun d => by
      apply Subtype.ext
      rw [hφ, mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_iff.mp hy d d.2
    rw [hN, Finset.prod_congr rfl fun d _ => hfixd d, Finset.prod_const, Finset.card_univ,
      Fintype.card_eq_nat_card, D₀.2.2]
  have hsup : ∀ D : {D : Subgroup G // D ≤ B ∧ Nat.card D = r}, D ≠ D₀ →
      (D₀ : Subgroup G) ⊔ D = B := by
    intro D hD
    have hle : (D₀ : Subgroup G) ⊔ D ≤ B := sup_le D₀.2.1 D.2.1
    have hlt : (D₀ : Subgroup G) < (D₀ : Subgroup G) ⊔ D := by
      refine lt_of_le_of_ne le_sup_left fun heq => hD (Subtype.ext ?_)
      exact Subgroup.eq_of_le_of_card_ge (heq ▸ le_sup_right) (by rw [D.2.2, D₀.2.2])
    have hdvd : Nat.card ((D₀ : Subgroup G) ⊔ D : Subgroup G) ∣ r ^ 2 :=
      hB2 ▸ Subgroup.card_dvd_of_le hle
    obtain ⟨k, hk, hkeq⟩ := (Nat.dvd_prime_pow hr).mp hdvd
    have hcardlt := Subgroup.card_lt_of_lt hlt
    rw [D₀.2.2, hkeq] at hcardlt
    have hk2 : k = 2 := by
      interval_cases k
      · have := hr.one_lt
        simp at hcardlt
        omega
      · simp at hcardlt
      · rfl
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hB2, hkeq, hk2])
  have hkill : ∀ D : {D : Subgroup G // D ≤ B ∧ Nat.card D = r}, D ≠ D₀ → ∀ y : X,
      (y : G) ∈ Subgroup.centralizer ((D : Subgroup G) : Set G) → N y = 1 := by
    intro D hD y hy
    have hD₀ : (D₀ : Subgroup G) ≤ Subgroup.centralizer {((N y : X) : G)} := by
      intro d₀ hd₀
      apply hcent ⟨d₀, hBX (D₀.2.1 hd₀)⟩
      rw [hN, map_prod]
      refine Fintype.prod_equiv (Equiv.mulLeft ⟨d₀, hd₀⟩) _ _ fun d => Subtype.ext ?_
      rw [hψ, hφ, hφ]
      simp only [Equiv.coe_mulLeft, Subgroup.coe_mul]
      group
    have hDc : (D : Subgroup G) ≤ Subgroup.centralizer {((N y : X) : G)} := by
      intro e he
      apply hcent ⟨e, hBX (D.2.1 he)⟩
      have hcomm : ∀ d : (D₀ : Subgroup G), (e : G) * d = d * e := fun d =>
        congrArg Subtype.val (hB.1.is_comm.comm ⟨e, D.2.1 he⟩ ⟨d, D₀.2.1 d.2⟩)
      have hey : e * (y : G) * e⁻¹ = y := by
        rw [mul_inv_eq_iff_eq_mul]
        exact Subgroup.mem_centralizer_iff.mp hy e he
      rw [hN, map_prod]
      refine Finset.prod_congr rfl fun d _ => Subtype.ext ?_
      rw [hψ, hφ]
      calc e * (d * y * (d : G)⁻¹) * e⁻¹ = (e * d) * y * (e * d)⁻¹ := by group
        _ = (d * e) * y * (d * e)⁻¹ := by rw [hcomm d]
        _ = d * (e * y * e⁻¹) * (d : G)⁻¹ := by group
        _ = d * y * (d : G)⁻¹ := by rw [hey]
    have hB' : B ≤ Subgroup.centralizer {((N y : X) : G)} := hsup D hD ▸ sup_le hD₀ hDc
    have hmem : ((N y : X) : G) ∈ X ⊓ Subgroup.centralizer (B : Set G) := by
      refine ⟨(N y).2, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mp (hB' hb)
    rw [hfix, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hK : (⨆ (D : {D : Subgroup G // D ≤ B ∧ Nat.card D = r}) (_ : D ≠ D₀),
      X ⊓ Subgroup.centralizer ((D : Subgroup G) : Set G)) ≤ N.ker.map X.subtype := by
    refine iSup₂_le fun D hD z hz => ⟨⟨z, hz.1⟩, ?_, rfl⟩
    exact hkill D hD ⟨z, hz.1⟩ hz.2
  obtain ⟨y, hy, rfl⟩ := hK hx
  have hyr : y ^ r = 1 := by
    rw [← hpow y (Subgroup.mem_inf.mp hx₀).2]
    exact hy
  have hord : orderOf y = 1 := Nat.dvd_one.mp (hcop.gcd_eq_one ▸
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hyr) (orderOf_dvd_natCard y))
  rw [orderOf_eq_one_iff] at hord
  rw [hord, map_one]

end Decomposition

end CFSG.RankThree.PartTwo.Late
