module

public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofG2
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Model
public import CFSG.Walter.Ree.Model.Fusion
import CFSG.RankThree.PartTwo.Sec4.T444.Item434Kit
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.CGT.PushingUpLit.CGT6.EmbG23 (G23 phi fixedGroup exists_conj_phi exists_equiv_g23)


@[expose] def KS611G2AutCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Blueprint.ChevalleyExceptionalModel Y .G2 3 1 →
    ∀ F V : Subgroup (MulAut Y), F ≤ (MulAut.conj : Y →* MulAut Y).range →
      CFSG.Assembly.IsElemAbelian 3 F → 9 ≤ Nat.card F → CFSG.Assembly.IsElemAbelian 2 V →
      (∀ f ∈ F, ∀ v ∈ V, f * v = v * f) → Nat.card V ≤ 2

namespace Res611Fix

theorem isElemAbelian_closure_of {X : Type*} [Group X] {p : ℕ} {S : Set X}
    (hS : S.Pairwise Commute) (hp : ∀ x ∈ S, x ^ p = 1) :
    CFSG.Assembly.IsElemAbelian p (Subgroup.closure S) := by
  have hc : IsMulCommutative (Subgroup.closure S) := Subgroup.isMulCommutative_closure hS
  refine ⟨hc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hp x hx
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem conj_injective {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : x ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 := congrArg (fun σ : MulAut X => σ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h2
    calc y * x = (x * y * x⁻¹) * x := by rw [h2]
      _ = x * y := by group
  rw [hZ, Subgroup.mem_bot] at h1
  exact h1

theorem commute_of_conj_commute {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) {x y : X}
    (h : MulAut.conj x * MulAut.conj y = MulAut.conj y * MulAut.conj x) : x * y = y * x := by
  apply conj_injective hZ
  rw [map_mul, map_mul, h]

theorem fix_of_commute_conj {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) {σ : MulAut X}
    {x : X} (h : σ * MulAut.conj x = MulAut.conj x * σ) : σ x = x := by
  apply conj_injective hZ
  have h1 : MulAut.conj (σ x) = σ * MulAut.conj x * σ⁻¹ := by
    ext y
    simp [MulAut.conj_apply, MulAut.mul_apply]
  rw [h1, h, mul_inv_cancel_right]

end Res611Fix

section Certs


@[expose] def KS611ReeThreeInvolCent : Prop :=
  ∀ t : G23, phi t = t → t ≠ 1 → t ^ 2 = 1 →
    ∀ F : Subgroup G23, F ≤ fixedGroup phi → CFSG.Assembly.IsElemAbelian 3 F → 9 ≤ Nat.card F →
      (∀ f ∈ F, f * t = t * f) → False


open Res611Fix

theorem ks611G2AutCent_of (hR : KS611ReeThreeInvolCent) : KS611G2AutCent := by
  intro Y _ _ hY F V hFi hFe hF9 hVe hcomm
  by_contra hV
  push Not at hV
  obtain ⟨Ψ⟩ := exists_equiv_g23 hY
  have hZ : Subgroup.center Y = ⊥ :=
    Sec4.center_eq_bot_of_mulEquiv Ψ CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  have : CharP (ZMod 3) CFSG.LieType.Ree.ReeTag.G2.prime := ZMod.charP 3
  obtain ⟨-, -, ⟨Θ, -, -, hΘker⟩, -⟩ :=
    CFSG.LieType.Chevalley.G2_three_exact_automorphism_normal_form (f := 1) le_rfl (ZMod 3)
      (by simp)
  set κ : MulAut Y ≃* MulAut G23 := MulAut.congr Ψ with hκ
  have hκconj : ∀ y : Y, κ (MulAut.conj y) = MulAut.conj (Ψ y) := by
    intro y
    ext z
    simp [hκ, MulAut.congr_apply]
  have hinn : ∀ σ : MulAut Y, Θ (κ σ) = 1 ↔ ∃ y : Y, MulAut.conj y = σ := by
    intro σ
    rw [← MonoidHom.mem_ker, hΘker]
    constructor
    · rintro ⟨g, hg⟩
      refine ⟨Ψ.symm g, κ.injective ?_⟩
      rw [hκconj, MulEquiv.apply_symm_apply, hg]
    · rintro ⟨y, rfl⟩
      exact ⟨Ψ y, (hκconj y).symm⟩
  have hΘ2 : ∀ a b : Multiplicative (ZMod (2 * 1)), a ≠ 1 → b ≠ 1 → a * b = 1 := by decide
  have hV1 : ∃ v₁ ∈ V, ∃ v₂ ∈ V, v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ ≠ v₂ := by
    have hfin : Finite V := Nat.finite_of_card_ne_zero (by omega)
    have := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card] at hV
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hV
    by_cases ha : (a : MulAut Y) = 1
    · refine ⟨b, b.2, c, c.2, fun h => hab (Subtype.ext (ha.trans h.symm)),
        fun h => hac (Subtype.ext (ha.trans h.symm)), fun h => hbc (Subtype.ext h)⟩
    · by_cases hb : (b : MulAut Y) = 1
      · exact ⟨a, a.2, c, c.2, ha, fun h => hbc (Subtype.ext (hb.trans h.symm)),
          fun h => hac (Subtype.ext h)⟩
      · exact ⟨a, a.2, b, b.2, ha, hb, fun h => hab (Subtype.ext h)⟩
  obtain ⟨v₁, hv₁, v₂, hv₂, hv₁1, hv₂1, hv₁₂⟩ := hV1
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hVe.2 v hv
  obtain ⟨f, hfF, hf1⟩ : ∃ f ∈ F, f ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).mpr hall
    rw [hbot, Subgroup.card_bot] at hF9
    omega
  have hinvol : ∀ v ∈ V, v ≠ 1 → ∀ y : Y, MulAut.conj y = v → y ≠ 1 ∧ y ^ 2 = 1 := by
    intro v hv hv1 y hy
    refine ⟨fun h => hv1 (by rw [← hy, h, map_one]), ?_⟩
    apply conj_injective hZ
    rw [map_pow, hy, map_one, pow_two]
    exact hVsq v hv
  by_cases hboth : Θ (κ v₁) = 1 ∧ Θ (κ v₂) = 1
  ·
    obtain ⟨y₁, hy₁⟩ := (hinn v₁).mp hboth.1
    obtain ⟨y₂, hy₂⟩ := (hinn v₂).mp hboth.2
    obtain ⟨hy₁1, hy₁2⟩ := hinvol v₁ hv₁ hv₁1 y₁ hy₁
    obtain ⟨hy₂1, hy₂2⟩ := hinvol v₂ hv₂ hv₂1 y₂ hy₂
    have hy₁₂ : y₁ ≠ y₂ := fun h => hv₁₂ (by rw [← hy₁, ← hy₂, h])
    have hc₁₂ : y₁ * y₂ = y₂ * y₁ :=
      commute_of_conj_commute hZ (by rw [hy₁, hy₂]; exact hVcomm v₁ hv₁ v₂ hv₂)
    obtain ⟨x, hx⟩ := hFi hfF
    have hx1 : x ≠ 1 := fun h => hf1 (by rw [← hx, h, map_one])
    have hx3 : x ^ 3 = 1 := by
      apply conj_injective hZ
      rw [map_pow, hx, map_one]
      exact hFe.2 f hfF
    have hxy : ∀ y : Y, MulAut.conj y ∈ V → x * y = y * x := fun y hyV =>
      commute_of_conj_commute hZ (by rw [hx]; exact hcomm f hfF _ hyV)
    set W := Subgroup.closure ({y₁, y₂} : Set Y) with hW
    have hWe : CFSG.Assembly.IsElemAbelian 2 W := by
      refine isElemAbelian_closure_of ?_ ?_
      · intro a ha b hb _
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
        rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
        all_goals first | exact Commute.refl _ | exact hc₁₂ | exact hc₁₂.symm
      · intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · exact hy₁2
        · exact hy₂2
    have hxW : ∀ w ∈ W, x * w = w * x := by
      intro w hw
      have hle : W ≤ Subgroup.centralizer ({x} : Set Y) := by
        rw [hW, Subgroup.closure_le]
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        rcases ha with rfl | rfl
        · exact (hxy a (hy₁ ▸ hv₁)).symm
        · exact (hxy a (hy₂ ▸ hv₂)).symm
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hw)).symm
    have hW2 := kS611G2Cent_holds Y hY x hx1 hx3 W hWe hxW
    have h3 : 3 ≤ Nat.card W := by
      have hsub : ({1, y₁, y₂} : Set Y) ⊆ (W : Set Y) := by
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · exact W.one_mem
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_eq_three.mpr ⟨1, y₁, y₂, hy₁1.symm, hy₂1.symm, hy₁₂, rfl⟩] at h1
      show 3 ≤ Nat.card (W : Set Y)
      rw [Nat.card_coe_set_eq]
      exact h1
    omega
  ·
    obtain ⟨σ, hσV, hσout, τ, hτV, hτ1, hτinn⟩ : ∃ σ ∈ V, Θ (κ σ) ≠ 1 ∧ ∃ τ ∈ V, τ ≠ 1 ∧
        Θ (κ τ) = 1 := by
      rcases not_and_or.mp hboth with h1 | h2
      · by_cases h2 : Θ (κ v₂) = 1
        · exact ⟨v₁, hv₁, h1, v₂, hv₂, hv₂1, h2⟩
        · refine ⟨v₁, hv₁, h1, v₁ * v₂, V.mul_mem hv₁ hv₂, fun h => hv₁₂ ?_, ?_⟩
          · calc v₁ = v₁ * (v₂ * v₂) := by rw [hVsq v₂ hv₂, mul_one]
              _ = (v₁ * v₂) * v₂ := by group
              _ = v₂ := by rw [h, one_mul]
          · rw [map_mul, map_mul]
            exact hΘ2 _ _ h1 h2
      · by_cases h1 : Θ (κ v₁) = 1
        · exact ⟨v₂, hv₂, h2, v₁, hv₁, hv₁1, h1⟩
        · refine ⟨v₂, hv₂, h2, v₁ * v₂, V.mul_mem hv₁ hv₂, fun h => hv₁₂ ?_, ?_⟩
          · calc v₁ = v₁ * (v₂ * v₂) := by rw [hVsq v₂ hv₂, mul_one]
              _ = (v₁ * v₂) * v₂ := by group
              _ = v₂ := by rw [h, one_mul]
          · rw [map_mul, map_mul]
            exact hΘ2 _ _ h1 h2
    obtain ⟨t, ht⟩ := (hinn τ).mp hτinn
    obtain ⟨ht1, ht2⟩ := hinvol τ hτV hτ1 t ht
    have hσt : σ t = t := fix_of_commute_conj hZ (by rw [ht]; exact hVcomm σ hσV τ hτV)
    have hσF : ∀ x : Y, MulAut.conj x ∈ F → σ x = x := fun x hxF =>
      fix_of_commute_conj hZ (hcomm _ hxF σ hσV).symm
    have hσ2 : κ σ * κ σ = 1 := by rw [← map_mul, hVsq σ hσV, map_one]
    have hσ'out : κ σ ∉ (MulAut.conj : G23 →* MulAut G23).range := by
      intro h
      apply hσout
      rw [← MonoidHom.mem_ker, hΘker]
      exact h
    obtain ⟨⟨ψ, hψ⟩, -⟩ := exists_conj_phi (κ σ) hσ2 hσ'out
    set e : Y ≃* G23 := Ψ.trans ψ with he
    have hphi : ∀ y : Y, phi (e y) = e (σ y) := by
      intro y
      rw [← hψ]
      simp [he, hκ, MulAut.congr_apply, MulAut.mul_apply]
    set F₀ := F.comap (MulAut.conj : Y →* MulAut Y) with hF₀
    have hF₀card : Nat.card F₀ = Nat.card F := by
      have hmap : F₀.map (MulAut.conj : Y →* MulAut Y) = F :=
        Subgroup.map_comap_eq_self (hFi)
      rw [← hmap, Subgroup.card_map_of_injective (conj_injective hZ)]
    have hF₀e : CFSG.Assembly.IsElemAbelian 3 F₀ := by
      refine Sec4.Item434Kit.isElemAbelian_of_map_injective (conj_injective hZ) ?_
      rw [Subgroup.map_comap_eq_self hFi]
      exact hFe
    refine hR (e t) (by rw [hphi, hσt]) (fun h => ht1 (e.injective (h.trans (map_one e).symm)))
      (by rw [← map_pow, ht2, map_one]) (F₀.map e.toMonoidHom) ?_
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 e.toMonoidHom F₀ hF₀e) ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      change phi (e x) = e x
      rw [hphi, hσF x hx]
    · rw [Subgroup.card_map_of_injective e.injective, hF₀card]
      exact hF9
    · rintro _ ⟨x, hx, rfl⟩
      have hxt : x * t = t * x :=
        commute_of_conj_commute hZ (by rw [ht]; exact hcomm _ hx τ hτV)
      change e x * e t = e t * e x
      rw [← map_mul, ← map_mul, hxt]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.Walter.Ree.Model in
theorem ks611ReeThreeInvolCent_holds : KS611ReeThreeInvolCent := by
  intro t htφ ht1 ht2 F hFφ hFe hF9 hFt
  have : CharP (ZMod 3) ReeTag.G2.prime := ZMod.charP 3
  have hK : Nat.card (ZMod 3) = 3 ^ (2 * 0 + 1) := by simp
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element ReeTag.G2.tag
  set ι := (adjointGroup ReeTag.G2.tag (ZMod 3)).subtype with hι
  set Γ := ReeTag.G2.reeGamma (ZMod 3) 0 with hΓ
  have hmemΓ : ∀ x : G23, phi x = x → ι x ∈ Γ := fun x hx => ⟨x, hx, rfl⟩
  have hto : orderOf (ι t) = 2 := by
    rw [orderOf_injective ι (adjointGroup ReeTag.G2.tag (ZMod 3)).subtype_injective]
    exact orderOf_eq_prime ht2 ht1
  obtain ⟨-, -, -, -, -, hfus⟩ := small_Ree_prime_field_involution_fusion 0 (ZMod 3) hK w₀ hw₀
  obtain ⟨g, hgΓ, hgt⟩ := hfus (ι t) (hmemΓ t htφ) hto
  set F' := (F.map ι).map (MulAut.conj g).toMonoidHom with hF'
  have hF'le : F' ≤ smallReeInvCentralizer 0 (ZMod 3) := by
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · change g * ι f * g⁻¹ ∈ Γ
      exact Γ.mul_mem (Γ.mul_mem hgΓ (hmemΓ f (hFφ hf))) (Γ.inv_mem hgΓ)
    · show g * ι f * g⁻¹ ∈ Subgroup.centralizer {smallReeH 0 (ZMod 3) (-1)}
      rw [Subgroup.mem_centralizer_singleton_iff, ← hgt]
      have hft : ι f * ι t = ι t * ι f := by rw [← map_mul, ← map_mul, hFt f hf]
      calc g * ι f * g⁻¹ * (g * ι t * g⁻¹) = g * (ι f * ι t) * g⁻¹ := by group
        _ = g * (ι t * ι f) * g⁻¹ := by rw [hft]
        _ = g * ι t * g⁻¹ * (g * ι f * g⁻¹) := by group
  have hF'card : Nat.card F' = Nat.card F := by
    rw [hF', Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Subgroup.card_map_of_injective (adjointGroup ReeTag.G2.tag (ZMod 3)).subtype_injective]
  have hC : Nat.card (smallReeInvCentralizer 0 (ZMod 3)) = 24 := by
    rw [card_smallReeInvCentralizer hw₀ hK]
    norm_num
  have hdvd : Nat.card F ∣ 24 := hF'card ▸ hC ▸ Subgroup.card_dvd_of_le hF'le
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF3 : IsPGroup 3 F := Sec5.isPGroup_of_isElemAbelian hFe
  obtain ⟨k, hk⟩ := hF3.exists_card_eq
  rw [hk] at hdvd hF9
  have hk2 : k < 2 := by
    by_contra hk2
    push Not at hk2
    have h9 : 9 ∣ 3 ^ k := by
      rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.pow_dvd_pow 3 hk2
    have := h9.trans hdvd
    omega
  interval_cases k <;> omega

theorem ks611G2AutCent_holds : KS611G2AutCent :=
  ks611G2AutCent_of ks611ReeThreeInvolCent_holds

end Certs

end CFSG.RankThree.PartTwo.Sec6
