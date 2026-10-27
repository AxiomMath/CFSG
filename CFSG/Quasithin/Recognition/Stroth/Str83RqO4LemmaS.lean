module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Defs
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Dictionary
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4Class
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4NaturalModule
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4L2Cover
import CFSG.Quasithin.Recognition.Stroth.Str83RqO4SzPair
import CFSG.Quasithin.Vol2.Ch4Sec1Defs
import CFSG.Goldschmidt.Steps.Sec82Tools

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.Stroth.G5 CFSG.QuasithinUnique.Setup.Campbell

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

private theorem lms_Qv_zero_le_normalizer {R : Subgroup G} (hR : R ≤ t.Zv 0) :
    t.Qv 0 ≤ normalizer (R : Set G) := by
  intro q hq
  refine CFSG.Goldschmidt.Sec82.mem_normalizer_of_conj_mem (fun r hr => ?_)
  have hqr : q * r = r * q := mem_centralizer_iff.mp (t.Zv_le_centralizer 0 (hR hr)) q hq
  have : q * r * q⁻¹ = r := by rw [hqr, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]
  exact hr

private theorem lms_map_normalizer {R : Subgroup G} {x : G} (hx : x ∈ normalizer (R : Set G)) :
    (normalizer (R : Set G)).map (MulAut.conj x).toMonoidHom = normalizer (R : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)

theorem eq_bot_of_cosetTrans_normalizer
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {R : Subgroup G}
    (hR : R ≤ t.Zv 0) (hK : t.K ≤ normalizer (R : Set G)) (hx : t.x₁ ∈ normalizer (R : Set G))
    (htr : CosetTrans (normalizer (R : Set G)) (t.Gv 1) (t.Gv 0)) : R = ⊥ := by
  by_contra hne
  have hpairAll : ∀ R' : Subgroup G, t.K ≤ normalizer (R' : Set G) →
      (∃ s ∈ normIn R' (t.Gv 0), t.x₁⁻¹ * s ∈ t.Gv 1 ⊓ t.Gv (-1)) →
      (∀ g ∈ normIn R' (t.Gv 0), g ∈ t.Gv 1 ⊓ t.Gv (-1) ∨
        t.x₁⁻¹ * g ∈ t.Gv 1 ⊓ t.Gv (-1)) ∨ L1 ≤ normIn R' (t.Gv 0) ⊔ t.Qv 0 := by
    rintro R' hK' ⟨s, hs, hsx⟩
    exact t.pair_or_le_sup_Qv_zero hfr inf_le_right (le_inf hK' (t.K_le_Gv 0)) hs hsx
  have hx0 : t.x₁ ∈ normIn R (t.Gv 0) := ⟨hx, t.x₁_mem_Gv_zero⟩
  have hxx : t.x₁⁻¹ * t.x₁ ∈ t.Gv 1 ⊓ t.Gv (-1) := by
    rw [inv_mul_cancel]
    exact (t.Gv 1 ⊓ t.Gv (-1)).one_mem
  have hRQ : R ≤ t.Qv 0 := hR.trans (t.Zv_le_Qv 0)
  have hQ01 : t.Qv 0 ≤ t.Gv (-1) ∧ t.Qv 0 ≤ t.Gv 1 := by
    simpa using t.Qv_le_Gv hfr 0
  have hRle0 : R ≤ t.Gv 0 := hRQ.trans (t.Qv_le_Gv_self 0)
  have hRle1 : R ≤ t.Gv 1 := hRQ.trans hQ01.2
  have hRlem : R ≤ t.Gv (-1) := hRQ.trans hQ01.1
  rcases hpairAll R hK ⟨t.x₁, hx0, hxx⟩ with hpair | hcov0
  swap
  · apply hne
    have h0 : CosetTrans (normalizer (R : Set G)) (t.Gv 0) (t.Gv 1) :=
      (t.cosetTrans_zero_of_le_sup hfr inf_le_right hcov0).mono inf_le_left
    exact t.eq_bot_of_cosetTrans hfr (le_inf hRle0 hRle1) h0 htr
  have htr₂ : CosetTrans (normalizer (R : Set G)) (t.Gv (-1)) (t.Gv 0) := by
    have h := htr.map_conj t.x₁
    rw [lms_map_normalizer hx, t.map_Gv_x₁ 1, t.map_Gv_x₁ 0, neg_zero] at h
    exact h
  have hRarc : t.ArcL R :=
    { ne_bot := hne
      le := le_inf (le_inf hRle1 hRle0) hRlem
      K_le := hK
      trans₀ := htr
      trans₂ := htr₂
      pair := hpair
      swap := ⟨t.x₁, hx0, hxx⟩ }
  obtain ⟨Y, hY, hMY⟩ := t.exists_arcLMax hRarc ((t.isPGroup_Zv 0).to_le hR)
  have hYarc : t.ArcL Y := hY.isArcClass
  have hQR : t.Qv 0 ≤ t.MX R 1 := le_inf (t.lms_Qv_zero_le_normalizer hR) hQ01.2
  have hPY : t.PX Y = t.Qv 0 := le_antisymm inf_le_left (le_inf le_rfl (hQR.trans hMY))
  have hPMX : IsSylowTwoOf (t.PX Y) (t.MX Y 1) := ArcL.isSylowTwoOf_pX_one t hfr hYarc
  have hP : IsSylowTwoOf (t.PX Y) (t.LX Y 1) :=
    F7.isSylowTwoOf_mono_right hPMX (le_oTwoPrime_of_isPGroup hPMX.2.1 hPMX.1)
      (oTwoPrime_le _)
  have hncM : NoCharNormal (t.PX Y) (t.MX Y 1) := ArcLMax.noCharNormal t hfr hY hpairAll
  have hnc : NoCharNormal (t.PX Y) (t.LX Y 1) := by
    intro C hCP hCne hCchar hLXnorm
    apply hncM C hCP hCne hCchar
    have hfratt := CFSG.Quasithin.H13.Ch4.sup_inf_normalizer_eq
      (M := t.MX Y 1) (N := t.LX Y 1) (P := t.PX Y)
      (oTwoPrime_le (t.MX Y 1)) (le_normalizer_oTwoPrime (t.MX Y 1)) hP
    have hcharN : normalizer ((t.PX Y : Subgroup G) : Set G) ≤ normalizer (C : Set G) := by
      haveI : (C.subgroupOf (t.PX Y)).Characteristic := hCchar
      have h := normalizer_le_normalizer_map_of_characteristic (H := t.PX Y)
        (K := C.subgroupOf (t.PX Y))
      rwa [Subgroup.map_subgroupOf_eq_of_le hCP] at h
    rw [← hfratt]
    exact sup_le hLXnorm (inf_le_right.trans hcharN)
  exact ArcLMax.pX_ne_Qv_zero t hfr hY (ArcL.isL2Quot_LX_one t hfr hYarc)
    (ArcL.charTwo_LX_one t hfr hYarc hY.isPGroup) hP hnc (ArcL.pCoreOf_LX_one t hfr hYarc)
    (ArcL.L2_le_LX_sup_Qv_one t hfr hYarc) hPY

end Track

end CFSG.Quasithin.Stroth.Rq
