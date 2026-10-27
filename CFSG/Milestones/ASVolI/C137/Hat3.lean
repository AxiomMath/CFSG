module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.H13.GoldschmidtC137H6Str
public import CFSG.Quasithin.MS93.S38OffHatMod

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
  CFSG.LieType.BorelTits
open CFSG.Quasithin.C124 CFSG.Quasithin.H13.U3.GC137
open scoped commutatorElement

variable {G : Type} [Group G]

theorem burnsideC137_fixV_bot {W : Type} [CommGroup W] : fixV (⊥ : Subgroup (MulAut W)) = ⊤ :=
  eq_top_iff.2 fun w _ x hx => by rw [Subgroup.mem_bot.1 hx]; rfl

theorem burnsideC137_hat_J [Finite G] {X T R U L : Subgroup G} (hU : IsElemAbelian 2 U)
    (hHM : MS93.S38H.HatMod (autI hU L)) (hUR : U ≤ R) (hRT : R ≤ T) (hTX : T ≤ X)
    (hXN : X ≤ normalizer (U : Set G)) (hXL : X ≤ normalizer (L : Set G))
    (hT2 : IsPGroup 2 ↥(autI hU T)) (hJ : ¬ thompsonJ R ≤ centralizer (U : Set G)) :
    autI hU (thompsonJ R) ≤ autI hU L ∧ Nat.card ↥(fixV (autI hU (thompsonJ R))) = 16 := by
  have hRN : R ≤ normalizer (U : Set G) := hRT.trans (hTX.trans hXN)
  rw [autI_thompsonJ hU hRN]
  obtain ⟨B₀, hB₀⟩ := (offenderImages_nonempty_iff_not_le hU).2 hJ
  have hfacts : ∀ B ∈ offenderImages hU R, B ≤ autI hU L ∧ Nat.card ↥B = 4 ∧
      Nat.card ↥(fixV B) = 16 ∧ IsElemAbelian2 B ∧ B ≤ autI hU T := by
    intro B hB
    have hoff := offenderImages_isFFStarOffender hU hUR hRN hB
    have hBN : B ≤ normalizer ((autI hU L : Subgroup (MulAut (IntMod U hU))) :
        Set (MulAut (IntMod U hU))) :=
      hoff.1.trans ((autI_mono hU (hRT.trans hTX)).trans (autI_le_normalizer_autI_gc hU hXL))
    have hcard : Nat.card (IntMod U hU) ≤ Nat.card ↥B * Nat.card ↥(fixV B) := by
      have := hoff.2.2.2 ⊥ bot_le
      rwa [Subgroup.card_bot, one_mul, burnsideC137_fixV_bot, Subgroup.card_top] at this
    obtain ⟨h1, h2, h3, -⟩ := hHM.offender hBN hoff.2.2.1 hoff.2.1 hcard
    exact ⟨h1, h2, h3, hoff.2.2.1, hoff.1.trans (autI_mono hU hRT)⟩
  have heq : ∀ B ∈ offenderImages hU R, B = B₀ := fun B hB =>
    hHM.offender_unique hT2 (hfacts B hB).2.2.2.2 (hfacts B₀ hB₀).2.2.2.2 (hfacts B hB).1
      (hfacts B₀ hB₀).1 (hfacts B hB).2.2.2.1 (hfacts B₀ hB₀).2.2.2.1 (hfacts B hB).2.1
      (hfacts B₀ hB₀).2.1 (hfacts B hB).2.2.1 (hfacts B₀ hB₀).2.2.1
  have hJeq : ffJP (offenderImages hU R) (autI hU R) = B₀ := by
    apply le_antisymm
    · exact iSup₂_le fun B hB => iSup_le fun _ => (heq B hB).le
    · exact le_iSup₂_of_le B₀ hB₀
        (le_iSup_of_le (offenderImages_isFFStarOffender hU hUR hRN hB₀).1 le_rfl)
  rw [hJeq]
  exact ⟨(hfacts B₀ hB₀).1, (hfacts B₀ hB₀).2.2.1⟩

theorem burnsideC137_baum_le_centralizer [Finite G] {R U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hUR : U ≤ R) :
    baum R ≤ centralizer ((U ⊓ centralizer (thompsonJ R : Set G) : Subgroup G) : Set G) := by
  have hE : U ⊓ centralizer (thompsonJ R : Set G) ≤ omegaOneCenterOf (thompsonJ R) := by
    rw [← (omegaOne_centralizer_thompsonJ R).1]
    intro u hu
    exact Subgroup.subset_closure ⟨⟨hUR hu.1, hu.2⟩, hU.2 u hu.1⟩
  exact inf_le_right.trans (Subgroup.centralizer_le hE)

theorem burnsideC137_hat_baum [Finite G] {X R U L : Subgroup G} (hU : IsElemAbelian 2 U)
    (hHM : MS93.S38H.HatMod (autI hU L)) (hUR : U ≤ R) (hRX : R ≤ X)
    (hXN : X ≤ normalizer (U : Set G)) (hXL : X ≤ normalizer (L : Set G))
    (hJL : autI hU (thompsonJ R) ≤ autI hU L)
    (hF16 : Nat.card ↥(fixV (autI hU (thompsonJ R))) = 16) :
    autI hU (baum R) ≤ autI hU L := by
  have := hHM.finite
  obtain ⟨zH, hcen, h3, hfp⟩ := hHM.exists_z
  have hz1 : (zH : MulAut (IntMod U hU)) ≠ 1 := by
    intro h1
    have hall : ∀ w : IntMod U hU, w = 1 := fun w => hfp w (by rw [h1]; rfl)
    have hc := hHM.card
    have : Nat.card (IntMod U hU) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, ⟨1⟩⟩
    omega
  have hJN : thompsonJ R ≤ normalizer (U : Set G) := (thompsonJ_le_self R).trans (hRX.trans hXN)
  set F := fixV (autI hU (thompsonJ R)) with hF
  have hzc : ∀ h ∈ autI hU L, h * (zH : MulAut (IntMod U hU)) = (zH : MulAut (IntMod U hU)) * h := by
    intro h hh
    have hzc' : zH ∈ Subgroup.center ↥(autI hU L) := hcen ▸ Subgroup.mem_zpowers zH
    have := Subgroup.mem_center_iff.1 hzc' ⟨h, hh⟩
    exact congrArg Subtype.val this
  have hzF : ∀ w ∈ F, (zH : MulAut (IntMod U hU)) w ∈ F := by
    intro w hw j hj
    have h1 := congrArg (fun φ : MulAut (IntMod U hU) => φ w) (hzc j (hJL hj))
    simp only [MulAut.mul_apply] at h1
    rw [h1, hw j hj]
  intro σ hσ
  obtain ⟨s, hsS, rfl⟩ := (mem_autI hU).1 hσ
  have hsX : (s : G) ∈ X := hRX (B2F.baum_le R hsS)
  have hσN : convI hU s ∈ normalizer ((autI hU L : Subgroup (MulAut (IntMod U hU))) :
      Set (MulAut (IntMod U hU))) :=
    autI_le_normalizer_autI_gc hU hXL (convI_mem_autI hU hsX s.2)
  have hsF : ∀ w ∈ F, convI hU s w = w := by
    intro w hw
    apply IntMod.val_injective
    rw [convI_apply_val]
    have hwE : w.val ∈ U ⊓ centralizer (thompsonJ R : Set G) :=
      ⟨w.val_mem, (mem_fixV_autI hU hJN w).1 hw⟩
    have h1 := Subgroup.mem_centralizer_iff.1 (burnsideC137_baum_le_centralizer hU hUR hsS)
      w.val hwE
    rw [← h1]
    group
  rcases HatA6.conj_z_cases hcen h3 hz1 hσN with hc | hc
  · refine hHM.mem_of_comm hσN fun k hk => ?_
    rw [hcen] at hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    simp only [Subgroup.coe_zpow]
    exact (Commute.zpow_right hc n).eq
  · exfalso
    have hbot : F = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      have h1 : convI hU s ((zH : MulAut (IntMod U hU)) w) = (zH : MulAut (IntMod U hU)) w :=
        hsF _ (hzF w hw)
      have h2 : convI hU s ((zH : MulAut (IntMod U hU)) w) =
          (zH : MulAut (IntMod U hU)) ((zH : MulAut (IntMod U hU)) w) := by
        have := congrArg (fun φ : MulAut (IntMod U hU) => φ w) hc
        simp only [MulAut.mul_apply] at this
        rw [this, hsF w hw]
      have h3' : (zH : MulAut (IntMod U hU)) w = w :=
        ((zH : MulAut (IntMod U hU)).injective (h1.symm.trans h2)).symm
      exact (Subgroup.mem_bot).2 (hfp w h3')
    rw [hbot, Subgroup.card_bot] at hF16
    omega

theorem burnsideC137_le_normalizer_toG_fixV [Finite G] {U K : Subgroup G} (hU : IsElemAbelian 2 U)
    (hK : K ≤ normalizer (U : Set G)) {J : Subgroup (MulAut (IntMod U hU))}
    (hKJ : autI hU K ≤ normalizer (J : Set (MulAut (IntMod U hU)))) :
    K ≤ normalizer ((toG hU (fixV J) : Subgroup G) : Set G) := by
  have hinv : XMod.IsInv ↥(autI hU K) (fixV J) := by
    intro a f hf j hj
    have ha := hKJ a.2
    have hj' : (a : MulAut (IntMod U hU))⁻¹ * j * (a : MulAut (IntMod U hU)) ∈ J := by
      have := (Subgroup.mem_normalizer_iff.1 ((normalizer _).inv_mem ha) j).1 hj
      simpa [mul_assoc] using this
    have h1 : (a : MulAut (IntMod U hU))⁻¹ (j ((a : MulAut (IntMod U hU)) f)) = f := hf _ hj'
    have h2 := congrArg (a : MulAut (IntMod U hU)) h1
    rw [MulAut.apply_inv_self] at h2
    exact h2
  have hconj := (isInv_iff hU hK).1 hinv
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro w
  constructor
  · exact hconj g hg w
  · intro hw
    have := hconj g⁻¹ (K.inv_mem hg) _ hw
    simpa [mul_assoc] using this

theorem burnsideC137_autI_o2Z_le_centralizer [Finite G] {U L : Subgroup G} (hU : IsElemAbelian 2 U)
    (hLN : L ≤ normalizer (U : Set G)) (hOL : pCoreOf 2 L ≤ centralizer (U : Set G)) :
    autI hU (H13.A6.o2Z L) ≤
      centralizer ((autI hU L : Subgroup (MulAut (IntMod U hU))) : Set (MulAut (IntMod U hU))) := by
  intro φ hφ
  obtain ⟨d, hdD, rfl⟩ := (mem_autI hU).1 hφ
  rw [Subgroup.mem_centralizer_iff]
  intro ψ hψ
  obtain ⟨y, hyL, rfl⟩ := (mem_autI hU).1 hψ
  have hk : (d : G) * y * (d : G)⁻¹ * (y : G)⁻¹ ∈ centralizer (U : Set G) :=
    hOL (comm_o2Z_gc hdD hyL)
  set c : ↥(normalizer (U : Set G)) := d * y * d⁻¹ * y⁻¹ with hc
  have hc1 : convI hU c = 1 := (convI_eq_one_iff hU c).2 hk
  rw [hc, map_mul, map_mul, map_mul, map_inv, map_inv] at hc1
  exact (commutatorElement_eq_one_iff_mul_comm.1 hc1).symm

end CFSG.ASVolI
