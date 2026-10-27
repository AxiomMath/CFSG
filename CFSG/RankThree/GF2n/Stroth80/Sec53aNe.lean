module

public import CFSG.RankThree.GF2n.Stroth80.Sec53aLe
public import CFSG.RankThree.GF2n.Stroth80.Sec53aCard

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.hBC_iff_vone_ne (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hm : 2 ≤ m) (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} (hD : GlobalModelData M Q Z γ M₀)
    (T : Submodule K M₀.E)
    (hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t)) :
    (Module.finrank K ↥(imgQInfQB M₀ B ⊓ imgQInfQB M₀ (conjSubgroup r B)) + 1 = 2 * m)
      ↔ Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t := by
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Vone Q B (conjSubgroup r B) V with hV1def
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hV1Q : V1 ≤ Q := vone_le_Q hVQ
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hZV1 : Z ≤ V1 := Z_le_vone
  have hVleV1 : V ≤ V1 := le_inf le_sup_right le_sup_right
  have hrM : r ∈ M := hc.Rt_le_M t hr
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hnoC : NoA2 Q Z (LB M Q (conjSubgroup r B)) := hc.noA2_conj hs.noA2 hrM
  have hq1 : 1 < Nat.card Z := by have := hc.hyp.q4; omega
  have hq2 : 2 ≤ Nat.card Z := by omega
  have hK2 : 2 ≤ Nat.card K := by rw [hD.card]; exact hq2
  have hspan : T ≤ imgQInfQB M₀ B ⊔ imgQInfQB M₀ (conjSubgroup r B) :=
    Ctx.le_sup_imgQInfQB_sp_of_hplane h34 hRoot hc hs hm hV hr hplane hD T hTmem
  constructor
  · intro hBC
    have hcard := Ctx.card_vone_sp_of_hBC h34 hRoot hc hs hm hV hr hD T hTmem hBC hspan
    have hcardV : Nat.card ↥V1 = Nat.card ↥V * Nat.card Z := by
      rw [← hVdef, ← hV1def] at hcard
      exact hcard
    intro hEq
    have hlt : Nat.card ↥V < Nat.card ↥V1 := by
      rw [hcardV]
      exact lt_mul_of_one_lt_right (Nat.card_pos (α := ↥V)) hq1
    have hcEq : Nat.card ↥V1 = Nat.card ↥V := by rw [hEq]
    omega
  · intro hne
    haveI : FiniteDimensional K M₀.E := M₀.fin
    haveI hTfin : FiniteDimensional K ↥T := FiniteDimensional.finiteDimensional_submodule T
    let W : Submodule K M₀.E :=
      imgSub M₀ V1 (hc.img_vone_smul (C := conjSubgroup r B) hs hcC hnoC hD)
    let d : ℕ := Module.finrank K ↥W
    haveI hWfin : FiniteDimensional K ↥W := FiniteDimensional.finiteDimensional_submodule W
    have hWmem : ∀ e : M₀.E, e ∈ W ↔ e ∈ M₀.img V1 := fun e => mem_imgSub
    have hWcard : Nat.card ↥(M₀.img V1) = Nat.card K ^ d := by
      rw [← Nat.card_congr (Equiv.subtypeEquivRight hWmem)]
      exact Module.natCard_eq_pow_finrank
    have hV1card : Nat.card ↥V1 = Nat.card Z * Nat.card K ^ d := by
      rw [M₀.card_eq hV1Q hZV1, hWcard]
    have hVcardK : Nat.card ↥V = Nat.card Z * Nat.card K ^ (2 * m) := by
      rw [SpMNat.card_V hV, hD.card, pow_succ']
    have hTcard : Nat.card ↥T = Nat.card Z ^ (2 * m) := by
      have hTimg : Nat.card ↥T = Nat.card ↥(M₀.img V) :=
        Nat.card_congr (Equiv.subtypeEquivRight hTmem)
      have hVT : Nat.card ↥V = Nat.card Z * Nat.card ↥(M₀.img V) :=
        M₀.card_eq hVQ hZV
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥Z)) ?_
      calc Nat.card Z * Nat.card ↥T
          = Nat.card Z * Nat.card ↥(M₀.img V) := by rw [hTimg]
        _ = Nat.card ↥V := hVT.symm
        _ = Nat.card Z ^ (2 * m + 1) := SpMNat.card_V hV
        _ = Nat.card Z * Nat.card Z ^ (2 * m) := by rw [pow_succ']
    have hTdim : Module.finrank K ↥T = 2 * m := by
      have h := Module.natCard_eq_pow_finrank (K := K) (V := ↥T)
      have h2 : Nat.card K ^ Module.finrank K ↥T = Nat.card K ^ (2 * m) := by
        rw [← h, hTcard, hD.card]
      exact Nat.pow_right_injective hK2 h2
    have hTW : T ≤ W := by
      intro e he
      rw [hWmem e]
      exact M₀.img_mono hVleV1 ((hTmem e).mp he)
    have hge : 2 * m ≤ d := by
      rw [← hTdim]
      exact Submodule.finrank_mono hTW
    have hdne : d ≠ 2 * m := by
      intro hd
      apply hne
      have hcardV1V : Nat.card ↥V1 = Nat.card ↥V := by
        rw [hV1card, hd, hVcardK]
      exact (Subgroup.eq_of_le_of_card_ge hVleV1 (le_of_eq hcardV1V)).symm
    have hgt : 2 * m < d := by omega
    have hle : d ≤ 2 * m + 1 := by
      have hbound := Ctx.card_vone_le h34 hRoot h51 hc hs hm hV hr hplane
      have h1 : Nat.card Z * Nat.card K ^ d ≤ Nat.card Z * Nat.card K ^ (2 * m + 1) := by
        calc Nat.card Z * Nat.card K ^ d = Nat.card ↥V1 := hV1card.symm
          _ ≤ Nat.card ↥V * Nat.card Z := hbound
          _ = (Nat.card Z * Nat.card K ^ (2 * m)) * Nat.card Z := by rw [hVcardK]
          _ = Nat.card Z * Nat.card K ^ (2 * m + 1) := by
              rw [hD.card, pow_succ']
              ring
      by_contra hcon
      push Not at hcon
      have h2 : Nat.card K ^ d ≤ Nat.card K ^ (2 * m + 1) :=
        Nat.le_of_mul_le_mul_left h1 (Nat.card_pos (α := ↥Z))
      have h3 := Nat.pow_lt_pow_right (by omega : 1 < Nat.card K) hcon
      omega
    have hd : d = 2 * m + 1 := by omega
    have hcardV : Nat.card ↥V1 = Nat.card ↥V * Nat.card Z := by
      rw [hV1card, hd, hVcardK, hD.card, pow_succ]
      ring
    have hcard : Nat.card ↥(Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))
        = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z := by
      rw [← hVdef, ← hV1def]
      exact hcardV
    exact Ctx.finrank_inf_imgQInfQB_of_card_vone h34 hc hs hV hcC hnoC hD T hTmem
      (Ctx.finrank_imgQInfQB_inf_Vt_sp h34 hRoot hc hs hm hV hD T hTmem)
      (Ctx.finrank_imgQInfQB_conj_inf_Vt_sp h34 hRoot hc hs hm hV hD T hTmem hr)
      hspan hcard

theorem stroth53a_of_vone_ne (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement)
    (hne : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t →
      Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t)
    (hOdd : ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B)
      (n : ℕ) (t : G), Sec5Hyp hc n t → SpNat hc t →
      ∀ r ∈ Rt M (LB M Q B) t, HypPlane Q Z B (conjSubgroup r B) t → Odd n) :
    Stroth53aStatement := by
  refine stroth53a_of_card_vone h34 hRoot ?_ hOdd
  intro G _ _ M Q Z B hc n t hs hsp r hr hplane m hV K _ _ _ γ M₀ hD
  let T : Submodule K M₀.E :=
    imgSub M₀ (Vt M (LB M Q B) B Z t) (hc.smul_mem_img_Vt hD t)
  have hTmem : ∀ e : M₀.E, e ∈ T ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun e => mem_imgSub
  have hm : 2 ≤ m := by
    obtain ⟨K₀, iF₀, iFin₀, hK₀, m₀, hm₀, hrep₀⟩ := hsp
    have hEq : m = m₀ := SpMNat.m_unique hV ⟨K₀, iF₀, iFin₀, hK₀, hrep₀⟩
    omega
  have hneV : Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t)
      ≠ Vt M (LB M Q B) B Z t :=
    hne G M Q Z B hc n t hs hsp r hr hplane
  have hBC : Module.finrank K ↥(imgQInfQB M₀ B ⊓ imgQInfQB M₀ (conjSubgroup r B)) + 1
      = 2 * m :=
    (Ctx.hBC_iff_vone_ne h34 hRoot h51 hc hs hm hV hr hplane hD T hTmem).mpr hneV
  have hspan : T ≤ imgQInfQB M₀ B ⊔ imgQInfQB M₀ (conjSubgroup r B) :=
    Ctx.le_sup_imgQInfQB_sp_of_hplane h34 hRoot hc hs hm hV hr hplane hD T hTmem
  exact ⟨T, hTmem, Ctx.card_vone_sp_of_hBC h34 hRoot hc hs hm hV hr hD T hTmem hBC hspan⟩

end CFSG.RankThree.GF2n.Stroth80
