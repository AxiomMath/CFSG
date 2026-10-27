module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.A10C626
public import CFSG.LocalAnalysis.UniquenessCase.UC6TitsC626

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Sporadic.Schreier.Tits (titsD card_titsD titsD_center card_outer_titsD)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial (injective_conj_of_center_eq_bot)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

section C626Tits

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

theorem c626gen_of_tits (m : Mz614 Dat) (hL : m.L620) (hOL : CFSG.pPrimeCore m.r ↥m.L = ⊥) (hr : m.r = 5)
    (hT : LieModel m.Lbar .Tits 0 2 1) : m.C626gen := by
  classical
  intro p hp P hP hPne
  have hpp : p.Prime := (Dat.sig_prime _ hp).1
  have hp2 : p ≠ 2 := (Dat.sig_prime _ hp).2
  have hp5 : p ≠ 5 := fun h => m.hrσ (hr ▸ h ▸ hp)
  have h620 := hL.1
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨e₀⟩ := TitsAut.lieModel_equiv hT
  let eL : ↥m.L ≃* ↥titsD := (m.equivLbar hOL).trans e₀
  have hLcard : Nat.card ↥m.L = 17971200 := by rw [Nat.card_congr eL.toEquiv, card_titsD]
  have h5 : (17971200 : ℕ).factorization 5 = 2 := by
    rw [show (17971200 : ℕ) = 5 ^ 2 * 718848 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_five, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcardB : Nat.card ((m.A ⊓ m.L).subgroupOf m.L) = 5 ^ (Nat.card ↥m.L).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, m.card_A_inf_L h620, hr, hLcard,
      h5]
  have hcardR : Nat.card (TitsCore.Rt.subgroupOf titsD) = 5 ^ (Nat.card ↥titsD).factorization 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe TitsCore.R_le_D).toEquiv, TitsCore.card_R, card_titsD, h5]
    norm_num
  obtain ⟨ψ, hψ⟩ :=
    exists_mulEquiv_sylow_eq_uc6 eL (TitsCore.Rt.subgroupOf titsD) hcardR (Sylow.ofCard _ hcardB)
  let ι : ↥titsD →* G := m.L.subtype.comp ψ.symm.toMonoidHom
  have hι_inj : Function.Injective ι := m.L.subtype_injective.comp ψ.symm.injective
  set Γ := gammaL m.L p P ⊔ gammaL m.L m.r m.E with hΓ
  let T' : Subgroup (Equiv.Perm (Fin 1755)) := (Γ.comap ι).map titsD.subtype
  have hT'D : T' ≤ titsD := by
    rintro _ ⟨d, -, rfl⟩
    exact d.2
  have hmemT' : ∀ x (hx : x ∈ titsD), ι ⟨x, hx⟩ ∈ Γ → x ∈ T' := fun x hx h => ⟨⟨x, hx⟩, h, rfl⟩
  have hE : ∀ e ∈ TitsCore.Rt, e ≠ 1 → ∀ x ∈ titsD, x * e = e * x → x ∈ T' := by
    intro e he he1 x hx hxe
    have heD : e ∈ titsD := TitsCore.R_le_D he
    have heB : ι ⟨e, heD⟩ ∈ m.A ⊓ m.L :=
      (hψ (ψ.symm ⟨e, heD⟩)).2 (by rw [MulEquiv.apply_symm_apply]; exact he)
    have he1' : ι ⟨e, heD⟩ ≠ 1 := fun h => he1 (congrArg Subtype.val (hι_inj (h.trans (map_one ι).symm)))
    have hc : ι ⟨x, hx⟩ * ι ⟨e, heD⟩ = ι ⟨e, heD⟩ * ι ⟨x, hx⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hxe
    exact hmemT' x hx (Subgroup.mem_sup_right (mem_gammaL_E h620 heB he1' (ψ.symm _).2 hc))
  have hPN : P ≤ normalizer (m.L : Set G) := fun q hq => m.normalizer_Z_le_normalizer_L (hP.le hq).2
  have hPp : IsPGroup p P := hP.isPGroup
  let act : ↥P →* MulAut ↥m.L := m.L.normalizerMonoidHom.comp (Subgroup.inclusion hPN)
  have act_apply : ∀ (q : ↥P) (y : ↥m.L), ((act q y : ↥m.L) : G) = (q : G) * y * (q : G)⁻¹ := by
    intro q y
    simp [act]
  by_cases hall : ∀ q : ↥P, act q = 1
  ·
    obtain ⟨⟨q, hq⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hPne
    refine le_sup_of_le_left fun y hy =>
      mem_gammaL_of_commute hpp hPp hq (fun h => hq1 (Subtype.ext h)) hy ?_
    have h1 := act_apply ⟨q, hq⟩ ⟨y, hy⟩
    rw [hall ⟨q, hq⟩] at h1
    simp only [MulAut.one_apply] at h1
    calc y * q = (q * y * q⁻¹) * q := by rw [← h1]
      _ = q * y := by group
  · push Not at hall
    obtain ⟨q, hq1⟩ := hall
    obtain ⟨q', hq'⟩ := A10Gen.exists_orderOf_map_eq_prime hpp hPp act hq1
    have hout : Nat.card (Outer ↥m.L) = 2 := by
      rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence eL).toEquiv,
        card_outer_titsD]
    have hodd : Odd (orderOf (act q')) := by
      rw [hq']
      exact hpp.odd_of_ne_two hp2
    obtain ⟨ℓ, hℓ⟩ := mem_inner_of_odd_uc6 hout (act q') hodd
    have hcen : center ↥m.L = ⊥ := ABGLocalTools.center_eq_bot_of_mulEquiv eL titsD_center
    have hℓp : orderOf ℓ = p := by
      rw [← orderOf_injective _ (injective_conj_of_center_eq_bot hcen) ℓ, hℓ, hq']
    set σ : ↥titsD := ψ ℓ with hσ
    have hσp : orderOf σ = p := by rw [hσ, MulEquiv.orderOf_eq, hℓp]
    have hp313 : p = 3 ∨ p = 13 := by
      have h1 := orderOf_dvd_natCard σ
      rw [hσp, card_titsD] at h1
      exact eq_three_or_thirteen_uc6 hpp hp2 hp5 h1
    have hq'1 : (q' : G) ≠ 1 := fun h => by
      have h1 : q' = 1 := Subtype.ext h
      rw [h1, map_one, orderOf_one] at hq'
      exact hpp.ne_one hq'.symm
    have hsT : ∀ x ∈ titsD, x * (σ : Equiv.Perm (Fin 1755)) = (σ : Equiv.Perm (Fin 1755)) * x → x ∈ T' := by
      intro x hx hxs
      set xl : ↥m.L := ψ.symm ⟨x, hx⟩ with hxl
      have hxlℓ : xl * ℓ = ℓ * xl := by
        apply ψ.injective
        rw [map_mul, map_mul, hxl, MulEquiv.apply_symm_apply, ← hσ]
        exact Subtype.ext hxs
      have hfix : act q' xl = xl := by
        rw [← hℓ, MulAut.conj_apply, ← hxlℓ, mul_inv_cancel_right]
      have hc : (xl : G) * q' = q' * (xl : G) := by
        have h1 := act_apply q' xl
        rw [hfix] at h1
        calc (xl : G) * q' = ((q' : G) * xl * (q' : G)⁻¹) * q' := by rw [← h1]
          _ = q' * xl := by group
      exact hmemT' x hx (Subgroup.mem_sup_left (mem_gammaL_of_commute hpp hPp q'.2 hq'1 xl.2 hc))
    have hσp' : orderOf (σ : Equiv.Perm (Fin 1755)) = 3 ∨ orderOf (σ : Equiv.Perm (Fin 1755)) = 13 := by
      rw [Subgroup.orderOf_coe, hσp]
      exact hp313
    have hTeq := TitsCore.eq_titsD_of_centralizers hT'D hE σ.2 hσp' hsT
    intro l hl
    have h1 : ((ψ ⟨l, hl⟩ : ↥titsD) : Equiv.Perm (Fin 1755)) ∈ T' := by
      rw [hTeq]
      exact (ψ ⟨l, hl⟩).2
    obtain ⟨d, hd, hdl⟩ := h1
    have hd' : d = ψ ⟨l, hl⟩ := Subtype.ext hdl
    have hιd : ι d = l := by
      rw [hd']
      simp [ι]
    rw [← hιd]
    exact hd

end C626Tits

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
