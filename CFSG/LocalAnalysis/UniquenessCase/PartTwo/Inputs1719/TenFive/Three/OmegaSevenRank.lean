module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmegaSevenModA
import CFSG.ClassicalInvolution.Orders.Orthogonal
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.Catalog
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Open.Defs
public import CFSG.Quasithin.Background.D2Coprime

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

private theorem omSevenR_not_dvd_prod (n : ℕ) (hn : n ≤ 15) :
    ¬ 3 ^ 10 ∣ ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  interval_cases n <;> decide

private theorem omSevenR_commute_coe {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {z : ↥L} (hz : z ∈ Subgroup.center ↥L) (g : ↥L) :
    Commute (g : MulAut W) (z : MulAut W) := by
  have h : g * z = z * g := Subgroup.mem_center_iff.mp hz g
  have h' : (g : MulAut W) * (z : MulAut W) = (z : MulAut W) * (g : MulAut W) := by
    have h1 := congrArg (Subgroup.subtype L) h
    simpa [map_mul] using h1
  exact h'

theorem sixteen_le_rk_of_injective {L U : Type} [Group L] [Finite L] [CommGroup U] [Finite U]
    (hU : ∀ u : U, u ^ 2 = 1) (ρ : L →* MulAut U) (hρ : Function.Injective ρ)
    (hd : 3 ^ 10 ∣ Nat.card L) : 16 ≤ rk U := by
  by_contra hle
  have hlt : rk U < 16 := not_le.mp hle
  have hdvd : 3 ^ 10 ∣ Nat.card (MulAut U) := by
    have h1 : Nat.card L = Nat.card ρ.range :=
      Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv
    have h2 : Nat.card ρ.range ∣ Nat.card (MulAut U) := Subgroup.card_subgroup_dvd_card ρ.range
    exact dvd_trans hd (h1 ▸ h2)
  rw [card_mulAut_eq hU] at hdvd
  exact omSevenR_not_dvd_prod (rk U) (by omega) hdvd

theorem sixteen_le_rk_commSub_center {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} (hLq : CFSG.IsQuasisimple ↥L)
    (hZ : Nat.card (center ↥L) = 3) {z : ↥L} (hz : z ∈ center ↥L) (hz3 : orderOf z = 3)
    (hord : 3 ^ 10 ∣ Nat.card ↥L) :
    16 ≤ rk ↥(commSub ⊤ (zpowers (z : MulAut W))) := by
  let zA : MulAut W := (z : MulAut W)
  let U : Subgroup W := commSub ⊤ (zpowers zA)
  have hzA3 : orderOf zA = 3 := (Subgroup.orderOf_coe z).trans hz3
  have hzA3pow : zA ^ 3 = 1 := by
    rw [← hzA3]
    exact pow_orderOf_eq_one zA
  have hstab : L ≤ stabSub U := by
    intro g hg
    rw [mem_stabSub]
    intro u
    constructor
    · intro hu
      have hgi : Commute (((⟨g, hg⟩ : ↥L)⁻¹ : MulAut W)) zA := by
        have h1 := (omSevenR_commute_coe hz ⟨g, hg⟩).inv_left
        simpa using h1
      have h2 := apply_mem_commSub_of_commute hgi hu
      simpa using h2
    · intro hu
      exact apply_mem_commSub_of_commute (omSevenR_commute_coe hz ⟨g, hg⟩) hu
  let f : ↥L →* stabSub U :=
    (Subgroup.subtype L).codRestrict (stabSub U) fun x => hstab x.2
  let ρ : ↥L →* MulAut ↥U := (resHom U).comp f
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hzA1 : zA ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hzA3
      norm_num at hzA3
    have hev : ∃ w : W, zA w ≠ w := by
      by_contra h
      exact hzA1 (MulEquiv.ext fun w => by
        by_contra hw
        exact h ⟨w, hw⟩)
    obtain ⟨w, hw⟩ := hev
    have hmem : zA w * w⁻¹ ∈ U := by
      show zA w * w⁻¹ ∈ commSub ⊤ (zpowers zA)
      exact Subgroup.subset_closure ⟨zA, Subgroup.mem_zpowers zA, w, Subgroup.mem_top w, rfl⟩
    have hne : zA w * w⁻¹ ≠ 1 := fun h => hw (mul_inv_eq_one.mp h)
    rw [hbot] at hmem
    exact hne (Subgroup.mem_bot.mp hmem)
  have hznotker : z ∉ ρ.ker := by
    intro hzker
    have hzU : ∀ u : U, zA (u : W) = u := by
      intro u
      have h1 : ρ z u = u := by rw [MonoidHom.mem_ker.mp hzker]; rfl
      have h2 : ((ρ z u : U) : W) = zA (u : W) := by
        show (((resHom U) (f z)) u : W) = zA (u : W)
        rw [resHom_apply]
        rfl
      rw [← h2, h1]
    have hle : U ≤ fixV (zpowers zA) := fun u hu => mem_fixV_zpowers_iff.mpr (hzU ⟨u, hu⟩)
    have hle' : U ≤ fixV (zpowers zA) ⊓ commSub ⊤ (zpowers zA) := le_inf hle le_rfl
    rw [fixV_inf_commSub_zpowers_eq_bot hW hzA3pow] at hle'
    exact hUne (bot_unique hle')
  have hker : ρ.ker = ⊥ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq (MonoidHom.normal_ker ρ) with
      htop | hle
    · exact absurd (htop ▸ Subgroup.mem_top z) hznotker
    · have hdvd3 : Nat.card ρ.ker ∣ 3 := by
        rw [← hZ]
        exact Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd3 with h1 | h3
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        have hcenter : ρ.ker = center ↥L :=
          Subgroup.eq_of_le_of_card_ge hle (by omega)
        have hz' : z ∈ ρ.ker := by
          rw [← hcenter] at hz
          exact hz
        exact hznotker hz'
  have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hker
  have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hW (u : W))
  exact sixteen_le_rk_of_injective hU2 ρ hinj hord

theorem three_pow_ten_dvd_card_of_model {L : Type} [Group L] [Finite L]
    (hm : LieModel (L ⧸ center L) .POmegaOdd 3 3 1) (hZ : Nat.card (center L) = 3) :
    3 ^ 10 ∣ Nat.card L := by
  have hcl : (.POmegaOdd : StatedLieTag) ∈ CFSG.Blueprint.classicalTags := by
    decide
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨e⟩⟩ := hm.statedClassicalModel hcl
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hord : Nat.card (L ⧸ center L) = ordBC 3 3 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.ClassicalInvolution.card_statedProj_statedOmega_quadOdd_eq_ordBC
      (K := K) (p := 3) (f := 1) (n := 3) (by norm_num) (by norm_num)
      (by simpa using hKcard) (by norm_num)
  have hbc : ordBC 3 3 = 3 ^ 9 * 232960 := by decide
  have hcard : Nat.card L = Nat.card (L ⧸ center L) * Nat.card (center L) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (center L)
  rw [hcard, hZ, hord, hbc]
  exact ⟨232960, by ring⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
