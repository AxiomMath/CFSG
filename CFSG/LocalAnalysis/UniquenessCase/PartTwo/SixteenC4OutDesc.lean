module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Out1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem s16_C4OutDesc_card_addSub (S : Subgroup (Vtil V₀ V hV)) :
    Nat.card (F.addSub S) = Nat.card S := by
  refine (Nat.card_congr ?_).symm
  refine
    { toFun := fun w => ⟨F.vec (w : Vtil V₀ V hV), (F.vec_mem_addSub S (w : Vtil V₀ V hV)).2 w.2⟩
      invFun := fun x => ⟨F.ofVec (x : Fin 4 → F.K), (F.mem_addSub S (x : Fin 4 → F.K)).1 x.2⟩
      left_inv := fun w => Subtype.ext (F.ofVec_vec (w : Vtil V₀ V hV))
      right_inv := fun x => Subtype.ext (F.vec_ofVec (x : Fin 4 → F.K)) }

theorem mem_addSub_fixV (E : Subgroup (MulAut (Vtil V₀ V hV))) (x : Fin 4 → F.K) :
    x ∈ F.addSub (fixV E) ↔ ∀ φ ∈ E, F.rho φ x = x := by
  rw [F.mem_addSub, mem_fixV]
  constructor
  · intro h φ hφ
    rw [← F.vec_ofVec x, F.rho_vec, h φ hφ, F.vec_ofVec]
  · intro h φ hφ
    apply F.vec_injective
    rw [← F.rho_vec, F.vec_ofVec]
    exact h φ hφ

theorem descent_decomp {τ : MulAut (Vtil V₀ V hV)} (hτ : F.IsSemi τ) (hτ2 : τ * τ = 1)
    {ω : F.K} (hω : ω ^ 2 + ω + 1 = 0) (x : Fin 4 → F.K) :
    ∃ r₁ r₂ : Fin 4 → F.K, F.rho τ r₁ = r₁ ∧ F.rho τ r₂ = r₂ ∧ x = ω ^ 2 • r₁ + r₂ := by
  have hfix : F.rho τ (F.rho τ x) = x := by
    rw [← F.rho_mul τ τ x, hτ2]
    simp [UFrame.rho]
  have hω3 : ω ^ 3 = 1 := by
    have h : ω ^ 3 - 1 = 0 := by linear_combination (ω - 1) * hω
    exact sub_eq_zero.mp h
  have hω4 : (ω ^ 2) ^ 2 = ω := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, show (4 : ℕ) = 3 + 1 by norm_num, pow_add,
      hω3, one_mul, pow_one]
  have hω2ω : ω ^ 2 + ω = 1 := by
    have h : ω ^ 2 + ω = -1 := by linear_combination hω
    have hneg1 : (-1 : F.K) = 1 := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, mul_one, F.two_eq_zero]
    rw [h, hneg1]
  refine ⟨x + F.rho τ x, ω • x + ω ^ 2 • F.rho τ x, ?_, ?_, ?_⟩
  · rw [map_add, hfix, add_comm]
  · rw [map_add, hτ ω x, hτ (ω ^ 2) (F.rho τ x), hfix, hω4, add_comm]
  · have hω2ω2 : ω ^ 2 + ω ^ 2 = 0 := by
      rw [← two_mul, F.two_eq_zero, zero_mul]
    have hsum : ω ^ 2 • (x + F.rho τ x) + (ω • x + ω ^ 2 • F.rho τ x) = x := by
      rw [smul_add]
      calc (ω ^ 2 • x + ω ^ 2 • F.rho τ x) + (ω • x + ω ^ 2 • F.rho τ x)
          = (ω ^ 2 • x + ω • x) + (ω ^ 2 • F.rho τ x + ω ^ 2 • F.rho τ x) := by abel
        _ = (ω ^ 2 + ω) • x + (ω ^ 2 + ω ^ 2) • F.rho τ x := by rw [← add_smul, ← add_smul]
        _ = x := by rw [hω2ω, hω2ω2, one_smul, zero_smul, add_zero]
    exact hsum.symm

theorem descent_inter {τ : MulAut (Vtil V₀ V hV)} (hτ : F.IsSemi τ) {ω : F.K}
    (hω : ω ^ 2 + ω + 1 = 0) {r : Fin 4 → F.K} (hr : F.rho τ r = r)
    (hωr : F.rho τ (ω • r) = ω • r) : r = 0 := by
  have hneg : -ω = ω := by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, F.two_eq_zero, zero_mul]
  have hω2ω : ω ^ 2 + ω = 1 := by
    have h : ω ^ 2 + ω = -1 := by linear_combination hω
    have hneg1 : (-1 : F.K) = 1 := by
      rw [neg_eq_iff_add_eq_zero, ← two_mul, mul_one, F.two_eq_zero]
    rw [h, hneg1]
  have heq : ω ^ 2 • r = ω • r := by
    have h1 : F.rho τ (ω • r) = ω ^ 2 • r := by rw [hτ ω r, hr]
    rw [← h1, hωr]
  have hsub : (ω ^ 2 - ω) • r = 0 := by
    rw [sub_smul, heq, sub_self]
  have hcoef : ω ^ 2 - ω = 1 := by
    rw [sub_eq_add_neg, hneg, hω2ω]
  calc r = (1 : F.K) • r := (one_smul _ _).symm
    _ = (ω ^ 2 - ω) • r := by rw [hcoef]
    _ = 0 := hsub

theorem card_fixV_zpowers_of_isSemi {τ : MulAut (Vtil V₀ V hV)} (hτ : F.IsSemi τ)
    (hτ2 : τ * τ = 1) : Nat.card (fixV (Subgroup.zpowers τ)) = 2 ^ 4 := by
  obtain ⟨ω, hω, -⟩ := F.exists_omega
  have hω3 : ω ^ 3 = 1 := by
    have h : ω ^ 3 - 1 = 0 := by linear_combination (ω - 1) * hω
    exact sub_eq_zero.mp h
  let R : AddSubgroup (Fin 4 → F.K) := F.addSub (fixV (Subgroup.zpowers τ))
  have hR : ∀ x : Fin 4 → F.K, x ∈ R ↔ F.rho τ x = x := by
    intro x
    change x ∈ F.addSub (fixV (Subgroup.zpowers τ)) ↔ F.rho τ x = x
    rw [F.mem_addSub, mem_fixV_zpowers_iff_apply]
    constructor
    · intro h
      rw [← F.vec_ofVec x, F.rho_vec, h, F.vec_ofVec]
    · intro h
      apply F.vec_injective
      rw [← F.rho_vec, F.vec_ofVec]
      exact h
  have hcardR : Nat.card R = Nat.card (fixV (Subgroup.zpowers τ)) :=
    s16_C4OutDesc_card_addSub F _
  let Φ : R × R → (Fin 4 → F.K) := fun p => ω ^ 2 • (p.1 : Fin 4 → F.K) + p.2
  have hsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨r₁, r₂, hr₁, hr₂, hx⟩ := descent_decomp F hτ hτ2 hω x
    exact ⟨(⟨r₁, (hR r₁).2 hr₁⟩, ⟨r₂, (hR r₂).2 hr₂⟩), hx.symm⟩
  have hinj : Function.Injective Φ := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq
    change ω ^ 2 • (p₁ : Fin 4 → F.K) + (p₂ : Fin 4 → F.K) =
      ω ^ 2 • (q₁ : Fin 4 → F.K) + (q₂ : Fin 4 → F.K) at hpq
    let s : Fin 4 → F.K := (q₂ : Fin 4 → F.K) - p₂
    have hs_eq : ω ^ 2 • ((p₁ : Fin 4 → F.K) - q₁) = s := by
      have h2 : ω ^ 2 • (p₁ : Fin 4 → F.K) + (p₂ : Fin 4 → F.K) - (p₂ : Fin 4 → F.K) =
          (ω ^ 2 • (q₁ : Fin 4 → F.K) + (q₂ : Fin 4 → F.K)) - (p₂ : Fin 4 → F.K) := by
        rw [hpq]
      rw [smul_sub, sub_eq_iff_eq_add']
      rwa [add_sub_cancel_right, add_sub_assoc] at h2
    have hsR : s ∈ R := sub_mem q₂.2 p₂.2
    have hsfix : F.rho τ s = s := (hR s).1 hsR
    have hws_eq : ω • s = (p₁ : Fin 4 → F.K) - q₁ := by
      rw [← hs_eq, smul_smul, show ω * ω ^ 2 = ω ^ 3 by ring, hω3, one_smul]
    have hwsR : ω • s ∈ R := by
      rw [hws_eq]
      exact sub_mem p₁.2 q₁.2
    have hwsfix : F.rho τ (ω • s) = ω • s := (hR (ω • s)).1 hwsR
    have hs0 : s = 0 := descent_inter F hτ hω hsfix hwsfix
    have hq2p2 : (q₂ : Fin 4 → F.K) = p₂ := sub_eq_zero.mp hs0
    have hp1q1 : (p₁ : Fin 4 → F.K) = q₁ := by
      have h : (p₁ : Fin 4 → F.K) - q₁ = 0 := by rw [← hws_eq, hs0, smul_zero]
      exact sub_eq_zero.mp h
    exact Prod.ext (Subtype.ext hp1q1) (Subtype.ext hq2p2.symm)
  have hbij : Function.Bijective Φ := ⟨hinj, hsurj⟩
  have hcard : Nat.card (Fin 4 → F.K) = Nat.card R * Nat.card R := by
    rw [← Nat.card_prod]
    exact (Nat.card_eq_of_bijective Φ hbij).symm
  have h256 : Nat.card (Fin 4 → F.K) = 2 ^ 8 := by
    rw [Nat.card_fun, F.card_K, Nat.card_fin]
    norm_num
  have hsquare : Nat.card R * Nat.card R = 2 ^ 4 * 2 ^ 4 := by
    rw [← hcard, h256]
    norm_num
  have hRcard : Nat.card R = 2 ^ 4 := Nat.mul_self_inj.1 hsquare
  rw [← hcardR]
  exact hRcard

theorem card_preimage_of_isSemi {τ : MulAut (Vtil V₀ V hV)} (hτ : F.IsSemi τ)
    (hτ2 : τ * τ = 1) {C : Subgroup (Vtil V₀ V hV)} (hC : C ≤ fixV (Subgroup.zpowers τ))
    {Ut : Subgroup (Vtil V₀ V hV)} (hUt : ∀ w : Vtil V₀ V hV, w ∈ Ut ↔ τ w * w⁻¹ ∈ C) :
    Nat.card Ut = 2 ^ 4 * Nat.card C := by
  obtain ⟨ω, hω, -⟩ := F.exists_omega
  let δ : Vtil V₀ V hV →* Vtil V₀ V hV := τ.toMonoidHom * invMonoidHom
  have hδ : ∀ w : Vtil V₀ V hV, δ w = τ w * w⁻¹ := fun w => by simp [δ]
  have hker : δ.ker = fixV (Subgroup.zpowers τ) := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixV_zpowers_iff_apply]
    constructor
    · intro h
      rwa [hδ w, mul_inv_eq_one] at h
    · intro h
      rw [hδ w, h, mul_inv_cancel]
  have hUt_eq : Ut = C.comap δ := by
    ext w
    rw [hUt w, Subgroup.mem_comap, hδ w]
  have hle : δ.ker ≤ C.comap δ := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact C.one_mem
  have hpre : ∀ c : C, ∃ w : Vtil V₀ V hV, w ∈ C.comap δ ∧ δ w = c := by
    intro c
    have hcfix : F.rho τ (F.vec (c : Vtil V₀ V hV)) = F.vec (c : Vtil V₀ V hV) := by
      rw [F.rho_vec, (mem_fixV_zpowers_iff_apply).1 (hC c.2)]
    have hcoef : ω ^ 2 - ω = 1 := by
      have hneg : -ω = ω := by
        rw [neg_eq_iff_add_eq_zero, ← two_mul, F.two_eq_zero, zero_mul]
      have h : ω ^ 2 + ω = -1 := by linear_combination hω
      have hneg1 : (-1 : F.K) = 1 := by
        rw [neg_eq_iff_add_eq_zero, ← two_mul, mul_one, F.two_eq_zero]
      rw [sub_eq_add_neg, hneg, h, hneg1]
    have hδw : δ (F.ofVec (ω • F.vec (c : Vtil V₀ V hV))) = (c : Vtil V₀ V hV) := by
      apply F.vec_injective
      rw [hδ, F.vec_mul, F.vec_inv,
        ← F.rho_vec τ (F.ofVec (ω • F.vec (c : Vtil V₀ V hV))), F.vec_ofVec,
        hτ ω (F.vec (c : Vtil V₀ V hV)), hcfix, ← sub_eq_add_neg, ← sub_smul, hcoef,
        one_smul]
    refine ⟨F.ofVec (ω • F.vec (c : Vtil V₀ V hV)), ?_, hδw⟩
    rw [Subgroup.mem_comap, hδw]
    exact c.2
  let δ' : (C.comap δ) →* C :=
    { toFun := fun u => ⟨δ (u : Vtil V₀ V hV), u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hsurj' : Function.Surjective δ' := by
    intro c
    obtain ⟨w, hw, hδw⟩ := hpre c
    exact ⟨⟨w, hw⟩, Subtype.ext hδw⟩
  have hker' : δ'.ker = (δ.ker).subgroupOf (C.comap δ) := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcardker : Nat.card δ'.ker = Nat.card (fixV (Subgroup.zpowers τ)) := by
    rw [hker']
    calc Nat.card ((δ.ker).subgroupOf (C.comap δ))
        = Nat.card δ.ker := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
      _ = Nat.card (fixV (Subgroup.zpowers τ)) := by rw [hker]
  have hiso : Nat.card δ'.ker * Nat.card C = Nat.card (C.comap δ) :=
    Subgroup.card_ker_mul_card_of_surjective (f := δ') hsurj'
  rw [hcardker, card_fixV_zpowers_of_isSemi F hτ hτ2] at hiso
  rw [← hUt_eq] at hiso
  exact hiso.symm

end UFrame

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
