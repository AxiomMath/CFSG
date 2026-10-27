module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTKer
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTOrderThree
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameCoord
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameDelta
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameDiag
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameE
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameKer
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFramePerm
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTFrameS
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTInner

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (autT)
open CFSG.RankThree.PartOne.KFU (torusSU diagU diagU_val exists_diagU_of_isDiag)

private theorem rhoTFrame_normalizes_symm {M : GL (Fin 6) F4}
    (hM : ∀ d ∈ torusSU 3 6 F4, M * d * M⁻¹ ∈ torusSU 3 6 F4) :
    ∀ d ∈ torusSU 3 6 F4, M⁻¹ * d * M ∈ torusSU 3 6 F4 := by
  have hle : (torusSU 3 6 F4).map (MulAut.conj M).toMonoidHom ≤ torusSU 3 6 F4 := by
    rintro _ ⟨d, hd, rfl⟩
    exact hM d hd
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj M).injective).ge
  intro d hd
  rw [← heq] at hd
  obtain ⟨d', hd', rfl⟩ := hd
  have e : M⁻¹ * ((MulAut.conj M).toMonoidHom d') * M = d' := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [e]
  exact hd'

theorem exists_rhoT_eq_conj_deltaGU
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m n : Fin 7} (h : CoordCtx B Bs x L A κ m) (hn : n ≠ m) {g : G}
    (hg : g ∈ normalizer (Bs : Set G)) (hl : IsCoordLift Bs κ g (Equiv.swap m n))
    {e : (L ⧸ center L) ≃* T46} {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)}
    (hρ : RhoTSpec e ρ) (hz : g * x * g⁻¹ ∈ normalizer (L : Set G)) :
    ∃ (y : GU0) (k : ℤ), (k = 1 ∨ k = -1) ∧ ρ ⟨_, hz⟩ = piGU (y * deltaGU ^ k * y⁻¹) := by
  obtain ⟨-, hBab, -, -⟩ := h.setting.bstar
  have hx := h.coords.x_mem
  have hzBs : g * x * g⁻¹ ∈ Bs := (mem_normalizer_iff.1 hg x).1 hx
  have hzc := rhoTFrame_z_coord h hg hl
  obtain ⟨E, hEle, hEcomm, hE3, hEcard, hE⟩ := rhoTFrame_exists_E h hρ
  obtain ⟨y, hyGU, hD⟩ := rhoTFrame_conj_eq_torusSU hEle hEcomm hE3 hEcard
  have h3 : (ρ ⟨_, hz⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨g * x * g⁻¹, hz⟩ : normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hBab.2 _ hzBs)
    rw [this, map_one]
  obtain ⟨zh, hzh⟩ := mem_range_piGU_of_pow_three_eq_one (hρ.mem_autT _) h3
  have hcommz : ∀ a : SU0, (a : GL (Fin 6) F4) ∈ E → piGU zh * piSU a = piSU a * piGU zh := by
    intro a ha
    obtain ⟨b, hb, -, hpi⟩ := (hE a).1 ha
    have hcb : g * x * g⁻¹ * b = b * (g * x * g⁻¹) :=
      congrArg Subtype.val (hBab.1.is_comm.comm ⟨g * x * g⁻¹, hzBs⟩ ⟨b, hb⟩)
    rw [hzh, hpi, ← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext hcb)
  have hdiag : ((y⁻¹ * (zh : GL (Fin 6) F4) * y : GL (Fin 6) F4) :
      Matrix (Fin 6) (Fin 6) F4).IsDiag := by
    refine rhoTFrame_isDiag hD (fun a ha => ?_)
    obtain ⟨c, -, hc⟩ := rhoTFrame_commute_scalar (hcommz ⟨a, hEle ha⟩ ha)
    exact ⟨c, hc⟩
  obtain ⟨wd, hdw⟩ := exists_diagU_of_isDiag hdiag
  obtain ⟨s, hs, hsinj⟩ := rhoTFrame_exists_s h hn hρ hE hzBs hzc
  let T : Finset (Equiv.Perm (Fin 7)) := Finset.univ.filter fun σ => σ m = m ∧ σ n = n
  let M : Equiv.Perm (Fin 7) → GL (Fin 6) F4 := fun σ => y⁻¹ * ((s σ : SU0) : GL (Fin 6) F4) * y
  have hTmem : ∀ σ ∈ T, σ m = m ∧ σ n = n := fun σ hσ => (Finset.mem_filter.1 hσ).2
  have hM : ∀ σ ∈ T, ∀ d ∈ torusSU 3 6 F4, M σ * d * (M σ)⁻¹ ∈ torusSU 3 6 F4 := by
    intro σ hσ d hd
    obtain ⟨hσm, hσn⟩ := hTmem σ hσ
    have hyd : y * d * y⁻¹ ∈ E := (rhoTFrame_mem_torus_iff hD).1 hd
    have key := ((hs σ hσm hσn).1 ⟨y * d * y⁻¹, hEle hyd⟩ hyd)
    rw [rhoTFrame_mem_torus_iff hD]
    have e1 : y * (M σ * d * (M σ)⁻¹) * y⁻¹ =
        (((s σ : SU0) * ⟨y * d * y⁻¹, hEle hyd⟩ * (s σ)⁻¹ : SU0) : GL (Fin 6) F4) := by
      simp only [M, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e1]
    exact key
  have hw : ∀ σ ∈ T, ∃ c : F4, c ≠ 0 ∧
      ((diagU wd : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *
        (M σ : Matrix (Fin 6) (Fin 6) F4) = c • ((M σ : Matrix (Fin 6) (Fin 6) F4) *
          ((diagU wd : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) := by
    intro σ hσ
    obtain ⟨hσm, hσn⟩ := hTmem σ hσ
    have hcz : piGU zh * piSU (s σ) = piSU (s σ) * piGU zh := by
      rw [hzh]
      exact ((hs σ hσm hσn).2).symm
    obtain ⟨c, hc0, hc⟩ := rhoTFrame_commute_scalar hcz
    refine ⟨c, hc0, ?_⟩
    have e1 : (diagU wd : GL (Fin 6) F4) * M σ =
        y⁻¹ * ((zh : GL (Fin 6) F4) * (s σ : GL (Fin 6) F4)) * y := by
      rw [hdw]
      simp only [M]
      group
    have e2 : M σ * (diagU wd : GL (Fin 6) F4) =
        y⁻¹ * ((s σ : GL (Fin 6) F4) * (zh : GL (Fin 6) F4)) * y := by
      rw [hdw]
      simp only [M]
      group
    rw [← Units.val_mul, ← Units.val_mul, e1, e2]
    simp only [Units.val_mul]
    rw [hc, Matrix.mul_smul, Matrix.smul_mul]
  have hinj : ∀ σ ∈ T, ∀ σ' ∈ T,
      (∀ d ∈ torusSU 3 6 F4, M σ * d * (M σ)⁻¹ = M σ' * d * (M σ')⁻¹) → σ = σ' := by
    intro σ hσ σ' hσ' hMM
    obtain ⟨hσm, hσn⟩ := hTmem σ hσ
    obtain ⟨hσ'm, hσ'n⟩ := hTmem σ' hσ'
    refine hsinj σ σ' hσm hσn hσ'm hσ'n (fun a ha => ?_)
    have hd : y⁻¹ * (a : GL (Fin 6) F4) * y ∈ torusSU 3 6 F4 := by
      rw [rhoTFrame_mem_torus_iff hD]
      have e1 : y * (y⁻¹ * (a : GL (Fin 6) F4) * y) * y⁻¹ = a := by group
      rw [e1]
      exact ha
    have h1 := hMM _ hd
    have e1 : ∀ τ : Equiv.Perm (Fin 7), M τ * (y⁻¹ * (a : GL (Fin 6) F4) * y) * (M τ)⁻¹ =
        y⁻¹ * ((s τ : GL (Fin 6) F4) * a * (s τ : GL (Fin 6) F4)⁻¹) * y := fun τ => by
      simp only [M]
      group
    rw [e1, e1] at h1
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using mul_left_cancel (mul_right_cancel h1)
  rcases rhoTFrame_pattern_core T (rhoTFrame_card_stab hn) M hM
      (fun σ hσ => rhoTFrame_normalizes_symm (hM σ hσ)) wd hw hinj with
    ⟨c, hc⟩ | ⟨k₀, c, u, hu1, hu⟩
  · exfalso
    have hdc : diagU wd = scalarGL c := by
      apply Units.ext
      rw [diagU_val, scalarGL_val, Matrix.smul_one_eq_diagonal]
      congr 1
      funext i
      rw [hc i]
    have hz1 : (zh : GL (Fin 6) F4) = scalarGL c := by
      have e1 : y⁻¹ * (zh : GL (Fin 6) F4) * y = scalarGL c := hdw.symm.trans hdc
      calc (zh : GL (Fin 6) F4) = y * (y⁻¹ * (zh : GL (Fin 6) F4) * y) * y⁻¹ := by group
        _ = y * scalarGL c * y⁻¹ := by rw [e1]
        _ = scalarGL c := by rw [← scalarGL_central]; group
    have hpi : piGU zh = 1 := by
      have : zh = ⟨scalarGL c, SU0_le_GU0 (scalarGL_mem c)⟩ := Subtype.ext hz1
      rw [this]
      exact rhoTFrame_piSU_scalarGL c
    have hone : ρ ⟨g * x * g⁻¹, hz⟩ = 1 := by rw [← hzh, hpi]
    obtain ⟨t, ht⟩ := Subgroup.mem_zpowers_iff.1
      ((rhoT_eq_one_iff_mem_zpowers h hρ hzBs).1 hone)
    have e2 : κ m ⟨g * x * g⁻¹, hzBs⟩ = 1 := by
      have : (⟨g * x * g⁻¹, hzBs⟩ : Bs) = (⟨x, hx⟩ : Bs) ^ t :=
        Subtype.ext (by simpa using ht.symm)
      rw [this, map_zpow, h.coords.x_coord, if_pos rfl, one_zpow]
    rw [hzc m, if_neg hn.symm] at e2
    exact one_ne_ω3 e2.symm
  · obtain ⟨y', k, hk, hpi⟩ :=
      rhoTFrame_exists_conj_delta (y := ⟨y, hyGU⟩) (z := zh) hu1 hdw.symm hu
    exact ⟨y', k, hk, hzh.symm.trans hpi⟩

end CFSG.GGQ2Prime
