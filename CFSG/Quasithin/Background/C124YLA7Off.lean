module

public import CFSG.Quasithin.Background.C124YLA7Woff
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A7FourMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Bridge

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

public section

namespace CFSG.Quasithin.C124.YL.A7

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246.C123

theorem exists_sylow_ge {K : Subgroup A7} (hK : IsPGroup 2 K) :
    ∃ T : Subgroup A7, K ≤ T ∧ Nat.card T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := hK.exists_le_sylow
  refine ⟨P, hP, ?_⟩
  rw [P.card_eq_multiplicity, fac_card_A7]
  norm_num

theorem genFitting_eq_self_of_simple {G : Type*} [Group G] (L : Subgroup G) [IsSimpleGroup ↥L]
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) : quasithinGenFitting L = L := by
  apply le_antisymm (quasithinGenFitting_le L)
  have hcomm : commutator ↥L = ⊤ := by
    rcases (inferInstance : (commutator ↥L).Normal).eq_bot_or_eq_top with h | h
    · exfalso
      have hc : IsMulCommutative ↥L := (_root_.commutator_eq_bot_iff ↥L).1 h
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc.is_comm.comm a b)
    · exact h
  have hcen : Subgroup.center ↥L = ⊥ := by
    rcases (inferInstance : (Subgroup.center ↥L).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have : a ∈ Subgroup.center ↥L := by rw [h]; trivial
      exact (Subgroup.mem_center_iff.1 this b).symm
  have hq : CFSG.Open.IsQuasisimple ↥L := by
    refine ⟨hcomm, ?_⟩
    have e : ↥L ≃* (↥L ⧸ Subgroup.center ↥L) :=
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm
    exact e.symm.isSimpleGroup
  have hcomp : CFSG.Open.IsComponentOf L L := ⟨le_rfl, IsSubnormal.refl L, hq⟩
  exact le_trans (le_sSup hcomp) le_sup_right

theorem exists_sylow_card_eight : ∃ T : Subgroup A7, Nat.card T = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 A7) := inferInstance
  refine ⟨P, ?_⟩
  rw [P.card_eq_multiplicity, fac_card_A7]
  norm_num

theorem exists_noncomm_of_equiv {R : Type*} [Group R] (e : R ≃* A7) :
    ∃ a b : R, a * b ≠ b * a := by
  have hc := alternatingGroup.center_eq_bot (α := Fin 7)
    (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  have : Nontrivial A7 := Finite.one_lt_card_iff_nontrivial.1 (by rw [card_A7]; norm_num)
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (1 : A7)
  have hxc : x ∈ Subgroup.center A7 :=
    Subgroup.mem_center_iff.2 fun g => by
      have := h (e.symm g) (e.symm x)
      exact e.symm.injective (by rw [map_mul, map_mul]; exact this)
  rw [hc] at hxc
  exact hx (Subgroup.mem_bot.1 hxc)

section Generic

variable {U : Type} [CommGroup U] (ρ : A7 →* MulAut U)

theorem isIrr_range (hcard : Nat.card U = 16) (hinj : Function.Injective ρ) :
    XMod.IsIrrSec ↥ρ.range (⊥ : Subgroup U) ⊤ := by
  obtain ⟨T, hT⟩ := exists_sylow_card_eight
  obtain ⟨u₀, hu₀T, hu₀1⟩ := exists_fixed_ne_one ρ hcard hT
  refine ⟨?_, fun J hJ _ _ => ?_⟩
  · rw [bot_lt_iff_ne_bot]
    intro h
    have h1 : Nat.card (⊤ : Subgroup U) = 1 := by rw [h, Subgroup.card_bot]
    rw [Subgroup.card_top, hcard] at h1
    omega
  · by_cases hbot : J = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
      rw [eq_top_iff]
      intro v _
      by_cases hv : v = 1
      · rw [hv]
        exact J.one_mem
      · have hu1' : (u : U) ≠ 1 := fun h => hu1 (Subtype.ext h)
        obtain ⟨g1, hg1⟩ := exists_apply_eq ρ hcard hinj hT hu₀1 hu₀T hu1'
        obtain ⟨g2, hg2⟩ := exists_apply_eq ρ hcard hinj hT hu₀1 hu₀T hv
        have h4 : ρ g1⁻¹ (u : U) = u₀ := by
          rw [← hg1, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
        have h3 : ρ (g2 * g1⁻¹) (u : U) = v := by
          rw [map_mul, MulAut.mul_apply, h4, hg2]
        have h5 : ρ (g2 * g1⁻¹) (u : U) ∈ J := hJ ⟨ρ (g2 * g1⁻¹), g2 * g1⁻¹, rfl⟩ u u.2
        rwa [h3] at h5

theorem ctx_range [Finite U] (hinj : Function.Injective ρ) :
    Bridge.Alt57.Ctx ρ.range ρ.range 7 := by
  let e : A7 ≃* ↥ρ.range := MonoidHom.ofInjective hinj
  have := isSimple_A7
  have : IsSimpleGroup ↥ρ.range := e.symm.isSimpleGroup
  refine ⟨Or.inr rfl, ⟨e.symm⟩, ?_, fun y hy => ρ.range.pow_mem hy 2⟩
  exact (genFitting_eq_self_of_simple ρ.range (exists_noncomm_of_equiv e.symm)).symm

theorem klein_of_woff (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) (hU2 : ∀ u : U, u ^ 2 = 1) {B : Subgroup A7} (hne : B ≠ ⊥)
    (hc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hs : ∀ a ∈ B, a * a = 1)
    (h16 : 16 ≤ Nat.card B * Nat.card (fixU ρ B)) : IsKleinConj B := by
  have : Finite U := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hBR : B.map ρ ≤ ρ.range := Subgroup.map_le_range ρ B
  have hA2 : IsA2 ρ.range (B.map ρ) :=
    ⟨hBR, by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective B hinj],
      (isElemAbelian2_map_iff' hinj).2 ⟨hc, hs⟩⟩
  have hfix : fixV (B.map ρ) = fixU ρ B := by
    ext u
    rw [mem_fixV, mem_fixU]
    constructor
    · intro h g hg
      exact h (ρ g) (Subgroup.mem_map_of_mem ρ hg)
    · intro h x hx
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
      exact h g hg
  have hr : Nat.card U + 0 ≤ Nat.card (B.map ρ) * Nat.card (fixV (B.map ρ)) := by
    rw [hfix, Subgroup.card_map_of_injective hinj, hcard]
    omega
  obtain ⟨A₂, hA₂B, hA₂, -⟩ := B1.exists_offender_below hA2 0 hr
  let π : ↥(alternatingGroup (Fin 7)) ≃* ↥ρ.range := MonoidHom.ofInjective hinj
  have hP := B42A57.asB42A7Four_holds U hU2 ρ.range ρ.range A₂ (ctx_range ρ hinj)
    (isIrr_range ρ hcard hinj) hA₂ (by rw [hcard]; norm_num) π
  have hK := isKleinConj_of_altConjTo hP
  set P : Subgroup A7 := (A₂.subgroupOf ρ.range).comap π.toMonoidHom with hPdef
  have hPB : P ≤ B := by
    intro x hx
    have h1 : ρ x ∈ A₂ := Subgroup.mem_subgroupOf.1 (Subgroup.mem_comap.1 hx)
    obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.1 (hA₂B h1)
    have : b = x := hinj hbx
    rwa [← this]
  have hB4 : Nat.card B ≤ 4 := card_le_four hc fun a ha => by rw [pow_two]; exact hs a ha
  have heq : P = B := Subgroup.eq_of_le_of_card_ge hPB (by rw [hK.card]; exact hB4)
  rw [← heq]
  exact hK

theorem card_fixU_eq_four (hcard : Nat.card U = 16)
    (hinj : Function.Injective ρ) (hU2 : ∀ u : U, u ^ 2 = 1) {B : Subgroup A7}
    (hK : IsKleinConj B) (h16 : 16 ≤ Nat.card B * Nat.card (fixU ρ B)) :
    Nat.card (fixU ρ B) = 4 := by
  have hB4 := hK.card
  obtain ⟨T, hBT, hT⟩ := exists_sylow_ge (IsPGroup.of_card (n := 2) (by rw [hB4]; norm_num))
  have hle := card_fixU_le_four ρ hcard hinj hU2 hT hB4 hBT
  rw [hB4] at h16
  omega

end Generic

end CFSG.Quasithin.C124.YL.A7
