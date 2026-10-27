module

public import CFSG.Quasithin.Background.F9Sixteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

section FF

variable {G : Type*} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}

theorem isFFModule_tilde_of_offender (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H)
    (hBel : IsElemAbelian 2 B) (hnt : ¬ B ≤ pCoreOf 2 H)
    (hr : (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
      (B ⊓ pCoreOf 2 H).relIndex B) :
    @IsFFModule ↥(tildeOf V₁ (conjClosure Vp H)) (commGroupOfElemAbelian h.isElemAbelian_tilde)
      (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) := by
  have hŨ := h.isElemAbelian_tilde
  let _ : CommGroup ↥(tildeOf V₁ (conjClosure Vp H)) := commGroupOfElemAbelian hŨ
  have hBt : IsElemAbelian 2 (tildeOf V₁ B) := isElemAbelian_secImg hBel
  have hn := HypF91.tilde_le_normalizer (V₁ := V₁) (Vp := Vp) hBH
  have hN : ∀ b ∈ B, b ∈ Subgroup.normalizer (V₁ : Set G) := fun b hb =>
    h.H_normalizes_V₁ (hBH hb)
  have hA2 : IsA2 (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H)))
      (autOn (tildeOf V₁ B) (tildeOf V₁ (conjClosure Vp H))) := by
    refine ⟨autOn_le_autOn _ (secImg_mono hBH), ?_, isElemAbelian2_autOn hŨ hBt hn⟩
    refine autOn_ne_bot_of_not_le_centralizer hn ?_
    intro hle
    apply hnt
    intro b hb
    have hy : secMk (Subgroup.normalizer (V₁ : Set G)) V₁ (⟨b, hN b hb⟩ : Subgroup.normalizer
        (V₁ : Set G)) ∈ tildeOf V₁ B ⊓ Subgroup.centralizer (tildeOf V₁ (conjClosure Vp H) :
          Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) :=
      ⟨secMk_mem_secImg (x := ⟨b, hN b hb⟩) hb, hle (secMk_mem_secImg (x := ⟨b, hN b hb⟩) hb)⟩
    rw [h.tilde_inf_centralizer_pCoreOf hBH] at hy
    obtain ⟨b', ⟨hb'B, hb'Q⟩, hbb'⟩ := mem_secImg.mp hy
    have h1 := secMk_eq_secMk_iff.mp hbb'
    have hc : ((b' : G))⁻¹ * b ∈ pCoreOf 2 H := h.V₁_le_pCoreOf h1
    have e : b = (b' : G) * ((b' : G)⁻¹ * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ hb'Q hc
  refine ⟨_, hA2.1, hA2.2.1, hA2.2.2, ?_⟩
  have c1 := HypF91.card_autOn_tilde h hBH
  have c2 := card_fixV_autOn_eq hŨ hn
  have c3 := h.relIndex_tilde_fixV hBH
  have hmul := Subgroup.relIndex_mul_card (tildeOf V₁ (conjClosure Vp H) ⊓
    Subgroup.centralizer (tildeOf V₁ B : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)))
    (tildeOf V₁ (conjClosure Vp H))
  rw [inf_eq_left.mpr (inf_le_left : tildeOf V₁ (conjClosure Vp H) ⊓
    Subgroup.centralizer (tildeOf V₁ B : Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁)) ≤
      tildeOf V₁ (conjClosure Vp H))] at hmul
  rw [c1, c2]
  calc Nat.card ↥(tildeOf V₁ (conjClosure Vp H))
      = (tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer (tildeOf V₁ B :
        Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))).relIndex
          (tildeOf V₁ (conjClosure Vp H)) *
        Nat.card ↥(tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer (tildeOf V₁ B :
          Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))) := hmul.symm
    _ ≤ (B ⊓ pCoreOf 2 H).relIndex B *
        Nat.card ↥(tildeOf V₁ (conjClosure Vp H) ⊓ Subgroup.centralizer (tildeOf V₁ B :
          Set (SecQuot (Subgroup.normalizer (V₁ : Set G)) V₁))) := by
      rw [c3]; exact Nat.mul_le_mul_right _ hr

end FF

namespace HypF98

variable {G : Type*} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G} {γ γ' : F8.Geom T L H}
  {g : ↥((L ⊔ T) ⊔ H)}

theorem exists_ffOffender_of_transvection (h : HypF98 T V L V₁ Vp H) (s : F8Setup T V L H γ γ' g)
    {W : Subgroup G} (hW : IsElemAbelian 2 W) (hV₁W : V₁ ≤ W) (hWV : W ≤ conjClosure V H)
    (hcomm : ⁅W, F8.Uγ Vp H (g : G)⁆ = V₁) :
    ∃ B : Subgroup G, B ≤ H ∧ IsElemAbelian 2 B ∧ ¬ B ≤ pCoreOf 2 H ∧
      (centralizerMod V₁ (conjClosure Vp H) B).relIndex (conjClosure Vp H) ≤
        (B ⊓ pCoreOf 2 H).relIndex B := by
  have hBL := h.conjSub_inv_V_le_pCoreOf_L₁T s hWV
  have hUH : conjClosure Vp H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hBH : conjSub (g : G)⁻¹ W ≤ H :=
    hBL.trans ((pCoreOf_le 2 _).trans h.L₁T_le_H)
  have hUab := h.F911_3
  have hBel := isElemAbelian_conjSub (g := (g : G)⁻¹) hW
  have hcardV₁' : Nat.card (conjSub (g : G)⁻¹ V₁) = 2 := (card_conjSub _ _).trans h.card_V₁
  have hUconj : conjSub (g : G)⁻¹ (F8.Uγ Vp H (g : G)) = conjClosure Vp H := by
    rw [F8.Uγ, conjSub_conjSub_inv]
  have hBU : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ = conjSub (g : G)⁻¹ V₁ := by
    rw [← hUconj, conjSub_commutator, hcomm]
  have hV₁'inf : conjSub (g : G)⁻¹ V₁ ⊓ V₁ = ⊥ := by
    have h5b := h.F913_5b s
    have := congrArg (conjSub (g : G)⁻¹) h5b
    rw [conjSub_inf, conjSub_bot] at this
    have e : conjSub (g : G)⁻¹ (F8.A₁ V₁ (g : G)) = V₁ := by
      rw [F8.A₁, conjSub_conjSub_inv]
    rwa [e] at this
  have hV₁'B : conjSub (g : G)⁻¹ V₁ ≤ conjSub (g : G)⁻¹ W := conjSub_mono _ hV₁W
  have hBUU : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ ≤ conjClosure Vp H := by
    refine Subgroup.commutator_le.mpr fun b hb u hu => ?_
    have hbH := hBH hb
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Vp H hbH) u).mp hu
    show b * u * b⁻¹ * u⁻¹ ∈ conjClosure Vp H
    exact (conjClosure Vp H).mul_mem (by simpa using this) ((conjClosure Vp H).inv_mem hu)
  refine ⟨conjSub (g : G)⁻¹ W, hBH, hBel, ?_, ?_⟩
  ·
    intro hle
    have h1 : ⁅conjSub (g : G)⁻¹ W, conjClosure Vp H⁆ ≤ V₁ := by
      refine Subgroup.commutator_le.mpr fun b hb u hu => ?_
      have := V₁.inv_mem (h.commutator_conjClosure_le u hu b (hle hb))
      have e : (u * b * u⁻¹ * b⁻¹)⁻¹ = b * u * b⁻¹ * u⁻¹ := by group
      rwa [e] at this
    rw [hBU] at h1
    have : conjSub (g : G)⁻¹ V₁ = ⊥ := le_bot_iff.mp (hV₁'inf ▸ le_inf le_rfl h1)
    have h2 : Nat.card (conjSub (g : G)⁻¹ V₁) = 1 := by rw [this]; simp
    omega
  ·
    have hCU : conjSub (g : G)⁻¹ V₁ ≤ conjClosure Vp H := by
      rw [← hBU]; exact hBUU
    have hpair := relIndex_eq_of_commutator_le (X := conjSub (g : G)⁻¹ W)
      (Y := conjClosure Vp H) hUab hcardV₁' hBU.le
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
        (isElemAbelian_comm hBel (hV₁'B ha) hb).symm)
      (fun a ha => Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (isElemAbelian_comm hUab (hCU ha) hu).symm)
    have hcM : centralizerMod V₁ (conjClosure Vp H) (conjSub (g : G)⁻¹ W) =
        conjClosure Vp H ⊓ Subgroup.centralizer (conjSub (g : G)⁻¹ W : Set G) := by
      ext x
      constructor
      · rintro ⟨hxU, hxN, hxc⟩
        refine ⟨hxU, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
        have h1 := hxc b hb
        have h2 : x * b * x⁻¹ * b⁻¹ ∈ conjSub (g : G)⁻¹ V₁ := by
          have := Subgroup.commutator_mem_commutator hxU hb
          rwa [Subgroup.commutator_comm, hBU] at this
        have h3 : x * b * x⁻¹ * b⁻¹ ∈ conjSub (g : G)⁻¹ V₁ ⊓ V₁ := ⟨h2, h1⟩
        rw [hV₁'inf, Subgroup.mem_bot] at h3
        calc b * x = (x * b * x⁻¹ * b⁻¹)⁻¹ * (x * b) := by group
          _ = x * b := by rw [h3]; group
      · rintro ⟨hxU, hxc⟩
        refine ⟨hxU, h.H_normalizes_V₁ (hUH hxU), fun b hb => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp hxc b hb
        have e : x * b * x⁻¹ * b⁻¹ = 1 := by rw [← this]; group
        rw [e]; exact V₁.one_mem
    have hQC : conjSub (g : G)⁻¹ W ⊓ pCoreOf 2 H =
        conjSub (g : G)⁻¹ W ⊓ Subgroup.centralizer (conjClosure Vp H : Set G) := by
      ext b
      constructor
      · rintro ⟨hb, hbQ⟩
        refine ⟨hb, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
        have hbQ' := (h.toHypF91.pCoreOf_eq_centralizerMod ▸ hbQ : b ∈ centralizerMod V₁ H
          (conjClosure Vp H))
        have h1 := hbQ'.2.2 u hu
        have h2 : b * u * b⁻¹ * u⁻¹ ∈ conjSub (g : G)⁻¹ V₁ := by
          have := Subgroup.commutator_mem_commutator hb hu
          rwa [hBU] at this
        have h3 : b * u * b⁻¹ * u⁻¹ ∈ conjSub (g : G)⁻¹ V₁ ⊓ V₁ := ⟨h2, h1⟩
        rw [hV₁'inf, Subgroup.mem_bot] at h3
        calc u * b = (b * u * b⁻¹ * u⁻¹)⁻¹ * (b * u) := by group
          _ = b * u := by rw [h3]; group
      · rintro ⟨hb, hbc⟩
        refine ⟨hb, ?_⟩
        rw [h.toHypF91.pCoreOf_eq_centralizerMod]
        refine ⟨hBH hb, h.H_normalizes_V₁ (hBH hb), fun u hu => ?_⟩
        have := Subgroup.mem_centralizer_iff.mp hbc u hu
        have e : b * u * b⁻¹ * u⁻¹ = 1 := by rw [← this]; group
        rw [e]; exact V₁.one_mem
    rw [hcM, hQC]
    exact hpair.ge

end HypF98

end CFSG.Quasithin
