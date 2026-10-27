module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Fix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSecA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SecBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenSmallMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.Quasithin.EmptyFaithful.F918C13
public import CFSG.Quasithin.Vol2.Ch10SecC8H1A
public import CFSG.Quasithin.Background.HPair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Pair CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W]

private theorem s16h_e3_l3_data_faithful_quot {V : Type*} [CommGroup V]
    {L : Subgroup (MulAut V)} {U Z : Subgroup V} (D : L3Data L U Z)
    {l : MulAut V} (hl : l ∈ L) (h : ∀ u ∈ U, l u * u⁻¹ ∈ Z) : l = 1 := by
  obtain ⟨γ, rfl⟩ := D.exists_rho hl
  have hγ : γ = 1 := by
    apply L3.act_injective
    intro v
    obtain ⟨u, hu⟩ := D.β_surj (Multiplicative.ofAdd v)
    have hmem : D.rho γ (u : V) ∈ U := D.inv_U _ (D.rho_mem γ) _ u.2
    have h2 := D.β_rho γ (u : V) u.2 hmem
    have hmem' : D.rho γ (u : V) * (u : V)⁻¹ ∈ U := U.mul_mem hmem (U.inv_mem u.2)
    have h4 : D.β ⟨D.rho γ (u : V) * (u : V)⁻¹, hmem'⟩ = 1 :=
      (D.ker_β _).mpr (h (u : V) u.2)
    have h5 : D.β ⟨D.rho γ (u : V) * (u : V)⁻¹, hmem'⟩ =
        D.β ⟨D.rho γ (u : V), hmem⟩ * (D.β u)⁻¹ := by
      rw [show (⟨D.rho γ (u : V) * (u : V)⁻¹, hmem'⟩ : ↥U) =
          ⟨D.rho γ (u : V), hmem⟩ * (⟨(u : V), u.2⟩ : ↥U)⁻¹ from Subtype.ext (by simp),
        map_mul, map_inv]
    have h3 : D.β ⟨D.rho γ (u : V), hmem⟩ = D.β u := by
      rw [h4] at h5
      exact mul_inv_eq_one.mp h5.symm
    rw [h3, hu] at h2
    exact (Multiplicative.ofAdd.injective h2).symm
  rw [hγ, map_one]

private theorem s16h_e3_l3_realizes_summand {U Z I : Subgroup W} {L : Subgroup (MulAut W)}
    (hZI : Z ≤ I) (hIU : I ≤ U) (hLU : L ≤ stabSub U) (hLI : L ≤ stabSub I) (hLZ : L ≤ stabSub Z)
    (hfaithI : L ⊓ centSec I Z = ⊥) (hfaith : L ⊓ centSec U Z = ⊥) {D : FFModel}
    (h : D.Realizes L I Z) :
    D.Realizes (autSec L U Z) ((I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))) ⊥ := by
  obtain ⟨π, hπ⟩ := s16h_realizes_autSec_of_realizes hZI hLI hLZ hfaithI h
  let Ī : Subgroup (Sec U Z) := (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))
  let eI : Sec I Z ≃* ↥Ī :=
    (MonoidHom.ofInjective (s16h_secIncl_injective Z I U hIU)).trans
      (MulEquiv.subgroupCongr (s16h_secIncl_range Z I U hIU))
  let e : ↥(⊤ : Subgroup (Sec I Z)) ≃* ↥Ī :=
    (Subgroup.topEquiv (G := Sec I Z)).trans eI
  let ψ : ↥(autSec L I Z) ≃* ↥(autSec L U Z) :=
    (B5.secEquiv L hLI hLZ hfaithI).symm.trans (B5.secEquiv L hLU hLZ hfaith)
  have he_apply : ∀ u : ↥(⊤ : Subgroup (Sec I Z)),
      ((e u : ↥Ī) : Sec U Z) = s16h_secIncl Z I U hIU (u : Sec I Z) := fun _ => rfl
  have heZ : ∀ u : ↥(⊤ : Subgroup (Sec I Z)),
      ((e u : ↥Ī) : Sec U Z) ∈ (⊥ : Subgroup (Sec U Z)) ↔
        (u : Sec I Z) ∈ (⊥ : Subgroup (Sec I Z)) := by
    intro u
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      have h1 : e u = 1 := by
        apply Subtype.ext
        simpa using h
      have h2 : u = 1 := e.injective (by rw [h1, map_one])
      exact congrArg Subtype.val h2
    · intro h
      have h1 : u = 1 := by
        apply Subtype.ext
        simpa using h
      have h2 : e u = e 1 := congrArg (⇑e) h1
      rw [map_one] at h2
      exact congrArg Subtype.val h2
  have hU : ∀ h' : ↥(autSec L U Z),
      ∀ u ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)),
        (h' : MulAut (Sec U Z)) u ∈ (I.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) :=
    fun h' => s16h_secIncl_image_stable Z I U hIU hLI hLZ hLU h' h'.2
  have hZ : ∀ h' : ↥(autSec L U Z), ∀ z ∈ (⊥ : Subgroup (Sec U Z)),
      (h' : MulAut (Sec U Z)) z ∈ (⊥ : Subgroup (Sec U Z)) := by
    intro h' z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  have hc : ∀ (g : ↥(autSec L I Z)) (u : ↥(⊤ : Subgroup (Sec I Z)))
      (hu : (g : MulAut (Sec I Z)) (u : Sec I Z) ∈ (⊤ : Subgroup (Sec I Z))),
      ((ψ g : ↥(autSec L U Z)) : MulAut (Sec U Z)) ((e u : ↥Ī) : Sec U Z) =
        ((e ⟨_, hu⟩ : ↥Ī) : Sec U Z) := by
    intro g u hu
    let a : ↥L := (B5.secEquiv L hLI hLZ hfaithI).symm g
    have hg_eq : (g : MulAut (Sec I Z)) = B5.secHom L hLI hLZ a := by
      have h1 := B5.secEquiv_apply L hLI hLZ hfaithI a
      have h2 : B5.secEquiv L hLI hLZ hfaithI a = g := by
        dsimp only [a]
        exact MulEquiv.apply_symm_apply _ _
      rw [h2] at h1
      exact h1
    have hψ_eq : ((ψ g : ↥(autSec L U Z)) : MulAut (Sec U Z)) = B5.secHom L hLU hLZ a := by
      have h1 := B5.secEquiv_apply L hLU hLZ hfaith a
      simpa only [ψ, a, MulEquiv.trans_apply] using h1
    rw [hψ_eq, he_apply u, he_apply ⟨_, hu⟩, hg_eq]
    exact (s16h_secIncl_secHom Z I U hIU hLI hLZ hLU a (u : Sec I Z)).symm
  exact ⟨ψ.toMonoidHom.comp π,
    CFSG.Quasithin.Vol2.Ch10.SecC.realizesVia_transport hπ ψ e heZ bot_le hU hZ hc⟩

theorem s16h_e3_l3_quotient_natSum3 (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hL3 : s16h_H5L3Sum L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    L ⊓ centSec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) = ⊥ ∧
    SumOfNat (fun H A B => BinaryNaturalSL H A B 3 1)
      (autSec L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
      (⊤ : Subgroup (Sec (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))) ⊥ 3 := by
  obtain ⟨hsl, I, hZI, hind, hsup, hnat⟩ := hL3
  set U : Subgroup W := commSub ⊤ L with hU
  set Z : Subgroup W := commSub ⊤ L ⊓ fixV L with hZ
  have hIU : ∀ i, I i ≤ U := by
    intro i
    rw [← hsup]
    exact le_sup_of_le_right (le_iSup I i)
  have hLU : L ≤ stabSub U := by
    rw [hU]
    exact le_stabSub_of_inv (s16jp_commSub_stable (Y := ⊤) (fun _ _ _ _ => Subgroup.mem_top _))
  have hLZ : L ≤ stabSub Z := by
    rw [hZ]
    refine le_stabSub_of_inv fun l hl z hz => ?_
    rw [Subgroup.mem_inf] at hz ⊢
    refine ⟨(mem_stabSub.mp (hLU hl) z).mpr hz.1, ?_⟩
    rw [mem_fixV] at hz ⊢
    intro a ha
    rw [show a (l z) = l ((l⁻¹ * a * l) z) from by simp [MulAut.mul_apply],
      hz.2 (l⁻¹ * a * l) (L.mul_mem (L.mul_mem (L.inv_mem hl) ha) hl)]
  have hLI : ∀ i, L ≤ stabSub (I i) := by
    intro i
    obtain ⟨K, hK, hKfin, hcard, hR⟩ := hnat i
    exact le_stabSub_of_inv (s16c1614_invariant_of_realizes hR)
  have hfaith_I : ∀ i, L ⊓ centSec (I i) Z = ⊥ := by
    intro i
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_inf] at hl
    rw [Subgroup.mem_bot]
    exact s16h_e3_l3_data_faithful_quot (Classical.choice (hnat i).toL3Coord) hl.1
      (fun u hu => (mem_centSec.mp hl.2).2 u hu)
  let i0 : Fin 3 := ⟨0, by norm_num⟩
  have hfaith : L ⊓ centSec U Z = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    rw [Subgroup.mem_inf] at hl
    rw [Subgroup.mem_bot]
    have hl' : l ∈ L ⊓ centSec (I i0) Z :=
      Subgroup.mem_inf.mpr ⟨hl.1, mem_centSec.mpr
        ⟨hLI i0 hl.1, fun u hu => (mem_centSec.mp hl.2).2 u (hIU i0 hu)⟩⟩
    rw [hfaith_I i0] at hl'
    exact hl'
  refine ⟨hfaith, ?_⟩
  let Ī : Fin 3 → Subgroup (Sec U Z) :=
    fun i => ((I i).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))
  have hĪ : ∀ i, Ī i = ((I i).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := fun _ => rfl
  refine ⟨Ī, ?_, ?_, ?_, ?_⟩
  · intro i
    exact bot_le
  · intro i
    rw [bot_sup_eq]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxi, hxj⟩ := hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hxi
    have haI : (a : W) ∈ I i := Subgroup.mem_subgroupOf.mp ha
    have hJmap : (⨆ (j : Fin 3) (_ : j ≠ i), Ī j) =
        ((⨆ (j : Fin 3) (_ : j ≠ i), I j).subgroupOf U).map
          (QuotientGroup.mk' (Z.subgroupOf U)) := by
      simp only [hĪ, s16h_subgroupOf_iSup_ne (fun j => hIU j) i, Subgroup.map_iSup]
    rw [hJmap] at hxj
    obtain ⟨b, hb, hb_eq⟩ := Subgroup.mem_map.mp hxj
    have hbJ : (b : W) ∈ ⨆ (j : Fin 3) (_ : j ≠ i), I j := Subgroup.mem_subgroupOf.mp hb
    have hab : (a : W) * (b : W)⁻¹ ∈ Z := by
      have h1 : a * b⁻¹ ∈ (QuotientGroup.mk' (Z.subgroupOf U)).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hb_eq, mul_inv_cancel]
      rw [QuotientGroup.ker_mk'] at h1
      exact Subgroup.mem_subgroupOf.mp h1
    have ha_mem : (a : W) ∈ I i ⊓ (Z ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) := by
      refine ⟨haI, ?_⟩
      rw [show (a : W) = ((a : W) * (b : W)⁻¹) * (b : W) from by group]
      exact mul_mem (Subgroup.mem_sup_left hab) (Subgroup.mem_sup_right hbJ)
    have haZ : (a : W) ∈ Z := hind i ha_mem
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff a).mpr (Subgroup.mem_subgroupOf.mpr haZ)
  · rw [bot_sup_eq]
    have hUeq : (⨆ i, I i) = U := by
      rw [← hsup]
      exact (sup_eq_right.mpr (le_trans (hZI i0) (le_iSup I i0))).symm
    have h1 : (⨆ i, Ī i) =
        (⨆ i, (I i).subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U)) := by
      simp only [hĪ, Subgroup.map_iSup]
    rw [h1, ← s16h_subgroupOf_iSup hIU, hUeq, Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective (N := Z.subgroupOf U))
  · intro i
    obtain ⟨K, hK, hKfin, hcard, hR⟩ := hnat i
    exact ⟨K, hK, hKfin, hcard,
      s16h_e3_l3_realizes_summand (hZI i) (hIU i) hLU (hLI i) hLZ (hfaith_I i) hfaith hR⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
