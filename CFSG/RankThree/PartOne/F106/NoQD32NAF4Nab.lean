module

public import CFSG.RankThree.PartOne.F106.NoQD32NAF4Tab
public import Certificates.Certificate271035

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity.TitsBits TauCeti CFSG.RankThree.PartOne.SEITZX Subgroup
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory
open scoped commutatorElement

section Main


theorem f4_nonabelian_false
    {X : Type} [Group X] [Finite X] (hT : UntwistedChevalleyModel X .F4 2) {Y R : Subgroup X}
    (hexp : ∀ y ∈ Y, y ^ 3 = 1) (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (hRN : R ≤ Subgroup.normalizer (Y : Set X)) (ψ : ↥R →* QD32) (hψs : Function.Surjective ψ)
    (hψc : ∀ r : ↥R, ψ r = 1 ↔ (r : X) ∈ Subgroup.centralizer (Y : Set X))
    (hB : ∀ r ∈ R, (∀ y ∈ Y, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.centralizer (Y : Set X)) →
      r ∈ Subgroup.centralizer (Y : Set X)) : False := by
  classical
  obtain ⟨K, _, _, hX, ⟨e₀⟩⟩ := nonempty_mulEquiv_adjointGroup .F4 hT
  obtain ⟨e⟩ : Nonempty (X ≃* adjointGroup ReeTag.F4.tag K) := ⟨e₀⟩
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (k := 1)
    (le_refl 1) (by simpa using hX)
  have hf : f4ThreeCert.Facts :=
    F4SylowCert.facts_of_check _ (Certificates.certificate271060 : F4ThreeRankCheck)
  have hna : f4ThreeCert.NAFacts fun i => f4ThreeCert.tabArr.getD i 0 :=
    F4SylowCert.NAFacts.of_naCheck (Certificates.certificate271035 : F4NACheck)
  have hg : ∀ i < 729, (fun i => f4ThreeCert.tabArr.getD i 0) i = f4ThreeCert.tab.getD i 0 :=
    fun i _ => F4SylowCert.tabArr_getD
  have hG : Nat.card (adjointGroup ReeTag.F4.tag K) = 3311126603366400 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4 (K := K)
    rw [hX] at h
    exact h.trans (by norm_num [CFSG.Open.ordF4])
  have : Finite (adjointGroup ReeTag.F4.tag K) :=
    Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  let T0 := f4GTab (K := K) hf
  have hB' : ∀ r : ↥R, (∀ y ∈ Y, (r : X) * y * (r : X)⁻¹ * y⁻¹ ∈
      Subgroup.centralizer (Y : Set X)) → (r : X) ∈ Subgroup.centralizer (Y : Set X) :=
    fun r hr => hB r r.2 hr
  have hV : 3 ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y) :=
    card_quotient_pow_four Nat.prime_three (by norm_num) hexp hcl hRN ψ hψs hψc hB'
  have hYp : IsPGroup 3 ↥Y := fun y => ⟨1, Subtype.ext (by simpa using hexp y y.2)⟩
  have hYZ : Nat.card ↥Y = Nat.card (↥Y ⧸ Subgroup.center ↥Y) * Nat.card (Subgroup.center ↥Y) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hZpos : 0 < Nat.card (Subgroup.center ↥Y) := Nat.card_pos
  have hYnt : Nontrivial ↥Y := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    rw [hYZ]
    calc 1 < 3 ^ 4 * 1 := by norm_num
      _ ≤ _ := Nat.mul_le_mul hV hZpos
  have hZ2 : 2 ≤ Nat.card (Subgroup.center ↥Y) := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (hYp.center_nontrivial)
    omega
  have hY3 : IsPGroup 3 (Y.map e.toMonoidHom) := fun y => by
    obtain ⟨a, ha, hay⟩ := y.2
    have h3 : (y : adjointGroup ReeTag.F4.tag K) ^ 3 = 1 := by
      rw [← hay, ← map_pow, hexp a ha, map_one]
    exact ⟨1, Subtype.ext h3⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hgS⟩ := exists_conj_le_of_sylow (p := 3) (k := 6) T0.S T0.card
    (by rw [hG]; norm_num) _ hY3
  have hYcard : Nat.card ↥((Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom) =
      Nat.card ↥Y := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective e.injective]
  have hdvd : Nat.card ↥Y ∣ 3 ^ 6 := by
    rw [← hYcard, ← T0.card]
    exact Subgroup.card_dvd_of_le hgS
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have h243 : 243 ≤ Nat.card ↥Y := by
    have h162 : 2 * 81 ≤ Nat.card ↥Y := by
      rw [hYZ]
      calc 2 * 81 = 3 ^ 4 * 2 := by norm_num
        _ ≤ _ := Nat.mul_le_mul hV hZ2
    rw [hjeq] at h162 ⊢
    interval_cases j <;> omega
  have hexp1 : ∀ y ∈ (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom, y ^ 3 = 1 :=
    map_pow_of_pow _ _ 3 (map_pow_of_pow e.toMonoidHom Y 3 hexp)
  have hcov : ∀ y ∈ (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom,
      y ∈ f4Y (K := K) hf f4WA hna.homA ∨ y ∈ f4Y (K := K) hf f4WB hna.homB ∨
        y ∈ f4Y (K := K) hf f4WC hna.homC := fun y hy =>
    cube_cover hg hf hna (hgS hy) (hexp1 y hy)
  set Y1 := (Y.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom with hY1
  have hcovle := le_of_cover_three (j := j) (by rw [hYcard, hjeq]) hcov
  have hA243 := card_f4Y (K := K) hf f4WA hna.homA hna.cardA
  have hB243 := card_f4Y (K := K) hf f4WB hna.homB hna.cardB
  have hC243 := card_f4Y (K := K) hf f4WC hna.homC hna.cardC
  have hmain : ∀ Ys : Subgroup (adjointGroup ReeTag.F4.tag K), Y1 ≤ Ys → Nat.card Ys = 243 →
      ∃ φ : ↥Y ≃* ↥Ys, ∀ x : ↥Y,
        ((φ x : ↥Ys) : adjointGroup ReeTag.F4.tag K) = g * e (x : X) * g⁻¹ := by
    intro Ys hle hc
    have hEq : Y1 = Ys := Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hYcard]; exact h243)
    exact exists_mulEquiv_conj e g Y Ys hEq
  have hZbig : ∀ Ys : Subgroup (adjointGroup ReeTag.F4.tag K), ↥Y ≃* ↥Ys →
      9 ≤ Nat.card (Subgroup.center ↥Ys) → Nat.card ↥Y = 243 → False := by
    intro Ys φ h9 hY243
    have hZ : Nat.card (Subgroup.center ↥Ys) = Nat.card (Subgroup.center ↥Y) :=
      (card_center_congr φ).symm
    have h := Nat.mul_le_mul hV (hZ ▸ h9 : 9 ≤ Nat.card (Subgroup.center ↥Y))
    rw [← hYZ, hY243] at h
    norm_num at h
  rcases hcovle with hle | hle | hle
  · obtain ⟨φ, -⟩ := hmain _ hle hA243
    exact hZbig _ φ (nine_le_card_center_Ya hg hf hna) ((Nat.card_congr φ.toEquiv).trans hA243)
  · obtain ⟨φ, hφ⟩ := hmain _ hle hB243
    have hY243 : Nat.card ↥Y = 243 := (Nat.card_congr φ.toEquiv).trans hB243
    have hZ3 : Nat.card (Subgroup.center ↥Y) = 3 ∧
        Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 3 ^ 4 := by
      rw [hY243] at hYZ
      generalize Nat.card (↥Y ⧸ Subgroup.center ↥Y) = a at hV hYZ ⊢
      generalize Nat.card (Subgroup.center ↥Y) = b at hZ2 hYZ ⊢
      have hb : b ≤ 3 := by nlinarith
      interval_cases b <;> omega
    have hZ0 : Nat.card (Subgroup.center ↥(f4Y (K := K) hf f4WB hna.homB)) = 3 :=
      (card_center_congr φ).symm.trans hZ3.1
    let pr : X → Prop := fun x => ¬ trI (e x) = 0
    have hconj : ∀ r ∈ R, ∀ x, pr (r * x * r⁻¹) ↔ pr x := by
      intro r _ x
      simp only [pr, map_mul, map_inv, trI_conj]
    have hQcard : Nat.card (Qset Y pr) = 24 := by
      have h := card_Qset_congr (Y := Y) (Y' := f4Y (K := K) hf f4WB hna.homB) (pr := pr)
        (pr' := fun g : adjointGroup ReeTag.F4.tag K => ¬ trI g = 0) φ
        (fun y => by simp only [pr, hφ y, trI_conj])
      rw [h]
      exact card_Qset_Yb hg hf hna hZ0
    have hAcard : Nat.card (Aset Y pr) = 8 := by
      have := card_Qset (Y := Y) (pr := pr)
      rw [hQcard, hZ3.1] at this
      omega
    have hZlt : f4NaZ < 729 := by decide
    have hzmem : f4ThreeCert.sel (X := K) f4NaZ ∈ f4Y (K := K) hf f4WB hna.homB :=
      (mem_f4Y hf _ _ hZlt).2 hna.zbWt
    let z1 : ↥(f4Y (K := K) hf f4WB hna.homB) := ⟨f4ThreeCert.sel (X := K) f4NaZ, hzmem⟩
    have hz1c : z1 ∈ Subgroup.center ↥(f4Y (K := K) hf f4WB hna.homB) :=
      sel_central_f4Y hg hf f4WB hna.homB hZlt hzmem hna.zbComm
    have h1 : (1 : ↥Y ⧸ Subgroup.center ↥Y) ∉ Aset Y pr := by
      apply one_not_mem_Aset_of_central
      refine ⟨φ.symm z1, (mulEquiv_mem_center_iff φ).mp (by
        rw [MulEquiv.apply_symm_apply]
        exact hz1c), ?_⟩
      intro h0
      have h2 := hφ (φ.symm z1)
      rw [MulEquiv.apply_symm_apply] at h2
      have h3 : trI (f4ThreeCert.sel (X := K) f4NaZ) = 0 := by
        have h2' : f4ThreeCert.sel (X := K) f4NaZ = g * e ((φ.symm z1 : ↥Y) : X) * g⁻¹ := h2
        rw [h2', trI_conj]
        exact h0
      have h4 := (trI_eq_zero_iff (hasBits_sel' (K := K) hg hf hZlt)).1 h3
      rw [hna.zbTr] at h4
      exact Bool.noConfusion h4
    exact false_of_Aset hexp hcl hRN ψ hψs hψc hB' hZ3.2 pr hconj h1 (by norm_num) hAcard
  · obtain ⟨φ, -⟩ := hmain _ hle hC243
    exact hZbig _ φ (nine_le_card_center_Yc hg hf hna) ((Nat.card_congr φ.toEquiv).trans hC243)

end Main

end CFSG.RankThree.PartOne.F106
