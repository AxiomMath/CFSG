module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTKer
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeDeltaCentAut
public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeRhoTOrderThree
public import Certificates.Certificate3600

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType CFSG.Fischer
open CFSG.EvenSmallLie.UnitarySix.YamadaHAut (autT)

theorem inf_centralizer_eq_closure
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {A : Subgroup (MulAut Bs)} {κ : Fin 7 → (Bs →* Multiplicative (ZMod 3))}
    {m : Fin 7} (h : CoordCtx B Bs x L A κ m) {g : G} (hg : g ∈ normalizer (Bs : Set G))
    {e : (L ⧸ center L) ≃* T46} {ρ : normalizer (L : Set G) →* Equiv.Perm (Fin 693)}
    (hρ : RhoTSpec e ρ) (hz : g * x * g⁻¹ ∈ normalizer (L : Set G)) {y : GU0} {k : ℤ}
    (hk : k = 1 ∨ k = -1) (hzρ : ρ ⟨_, hz⟩ = piGU (y * deltaGU ^ k * y⁻¹)) {X : Subgroup G}
    (hXL : X ≤ L) (hXz : X ≤ centralizer ({g * x * g⁻¹} : Set G))
    (hXs : ∀ c ∈ T46 ⊓ centralizer ({ρ ⟨_, hz⟩} : Set (Equiv.Perm (Fin 693))),
      ∃ l : L, (l : G) ∈ X ∧ (e (QuotientGroup.mk l) : Equiv.Perm (Fin 693)) = c) :
    Bs ⊓ centralizer (X : Set G) = closure {x, x * (g * x * g⁻¹)⁻¹} := by
  obtain ⟨-, -, -, hLc', -⟩ := ggThmIHyp_unpack h.setting.hyp
  have hLc : L ≤ centralizer ({x} : Set G) := hLc'.1
  have hxBs : x ∈ Bs := h.coords.x_mem
  set Z : G := g * x * g⁻¹
  have hZBs : Z ∈ Bs := (mem_normalizer_iff.1 hg x).1 hxBs
  have hxC : x ∈ centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.1 (hLc (hXL hl))
  have hZC : Z ∈ centralizer (X : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.1 (hXz hl)
  have hx_cl : x ∈ closure ({x, x * Z⁻¹} : Set G) := Subgroup.subset_closure (by simp)
  have hxZ_cl : x * Z⁻¹ ∈ closure ({x, x * Z⁻¹} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hZcl : Z ∈ closure ({x, x * Z⁻¹} : Set G) := by
    have h3 := mul_mem (inv_mem hxZ_cl) hx_cl
    rwa [show (x * Z⁻¹)⁻¹ * x = Z by group] at h3
  apply le_antisymm
  · intro b hb
    obtain ⟨hbBs, hbC⟩ := Subgroup.mem_inf.1 hb
    have hbX : ∀ l ∈ X, l * b = b * l := fun l hl => Subgroup.mem_centralizer_iff.1 hbC l hl
    have hbn : b ∈ normalizer (L : Set G) := h.setting.Bs_norm hbBs
    have hcomm : ∀ c ∈ T46 ⊓ centralizer ({ρ ⟨Z, hz⟩} : Set (Equiv.Perm (Fin 693))),
        ρ ⟨b, hbn⟩ * c = c * ρ ⟨b, hbn⟩ := by
      intro c hc
      obtain ⟨l, hlX, hlc⟩ := hXs c hc
      have hbl : b * (l : G) * b⁻¹ = (l : G) := by
        rw [← hbX (l : G) hlX]
        group
      have hl : ((⟨b, hbn⟩ : normalizer (L : Set G)) : G) * (l : G) *
          ((⟨b, hbn⟩ : normalizer (L : Set G)) : G)⁻¹ ∈ L := by
        show b * (l : G) * b⁻¹ ∈ L
        rw [hbl]
        exact l.2
      have key := hρ.conj ⟨b, hbn⟩ l hl
      have e2 : (⟨((⟨b, hbn⟩ : normalizer (L : Set G)) : G) * (l : G) *
          ((⟨b, hbn⟩ : normalizer (L : Set G)) : G)⁻¹, hl⟩ : L) = l :=
        Subtype.ext hbl
      rw [e2, hlc] at key
      calc ρ ⟨b, hbn⟩ * c = (ρ ⟨b, hbn⟩ * c * (ρ ⟨b, hbn⟩)⁻¹) * ρ ⟨b, hbn⟩ := by group
        _ = c * ρ ⟨b, hbn⟩ := by rw [key]
    have hP : piGU y ∈ autT := piGU_mem_autT y
    have hρZ : ρ ⟨Z, hz⟩ = piGU y * piGU deltaGU ^ k * (piGU y)⁻¹ := by
      rw [hzρ, map_mul, map_mul, map_zpow, map_inv]
    have hconj : ∀ c' ∈ T46 ⊓ centralizer ({piGU deltaGU} : Set (Equiv.Perm (Fin 693))),
        (piGU y)⁻¹ * ρ ⟨b, hbn⟩ * piGU y * c' = c' * ((piGU y)⁻¹ * ρ ⟨b, hbn⟩ * piGU y) := by
      intro c' hc'
      obtain ⟨hc'T, hc'C⟩ := Subgroup.mem_inf.1 hc'
      have hcD : Commute c' (piGU deltaGU) := Subgroup.mem_centralizer_singleton_iff.1 hc'C
      have hcP : Commute (piGU y * c' * (piGU y)⁻¹)
          (piGU y * piGU deltaGU ^ k * (piGU y)⁻¹) := by
        have h1 := (hcD.zpow_right k).map (MulAut.conj (piGU y))
        simpa only [MulAut.conj_apply] using h1
      have hcT : piGU y * c' * (piGU y)⁻¹ ∈ T46 := (mem_normalizer_iff.1 hP c').1 hc'T
      have hcC : piGU y * c' * (piGU y)⁻¹ ∈
          centralizer ({ρ ⟨Z, hz⟩} : Set (Equiv.Perm (Fin 693))) := by
        rw [Subgroup.mem_centralizer_singleton_iff, hρZ]
        exact hcP
      have hm := hcomm _ (Subgroup.mem_inf.2 ⟨hcT, hcC⟩)
      calc (piGU y)⁻¹ * ρ ⟨b, hbn⟩ * piGU y * c'
          = (piGU y)⁻¹ * (ρ ⟨b, hbn⟩ * (piGU y * c' * (piGU y)⁻¹)) * piGU y := by group
        _ = (piGU y)⁻¹ * ((piGU y * c' * (piGU y)⁻¹) * ρ ⟨b, hbn⟩) * piGU y := by rw [hm]
        _ = c' * ((piGU y)⁻¹ * ρ ⟨b, hbn⟩ * piGU y) := by group
    have hu_aut : (piGU y)⁻¹ * ρ ⟨b, hbn⟩ * piGU y ∈ autT :=
      mul_mem (mul_mem (inv_mem hP) (hρ.mem_autT _)) hP
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
      (mem_zpowers_of_commute_inf_centralizer hu_aut hconj)
    have hkk : k * (k * j) = j := by rcases hk with rfl | rfl <;> ring
    have hpow : ρ ⟨Z, hz⟩ ^ (k * j) = ρ ⟨b, hbn⟩ := by
      rw [hρZ, conj_zpow, ← zpow_mul, hkk, hj]
      group
    have hbZ : b * Z ^ (-(k * j)) ∈ Bs := mul_mem hbBs (zpow_mem hZBs _)
    have hone : ρ ⟨b * Z ^ (-(k * j)), h.setting.Bs_norm hbZ⟩ = 1 := by
      have e3 : (⟨b * Z ^ (-(k * j)), h.setting.Bs_norm hbZ⟩ : normalizer (L : Set G)) =
          ⟨b, hbn⟩ * ⟨Z, hz⟩ ^ (-(k * j)) := rfl
      rw [e3, map_mul, map_zpow, ← hpow, zpow_neg, mul_inv_cancel]
    have hw := (rhoT_eq_one_iff_mem_zpowers h hρ hbZ).1 hone
    have hzp : zpowers x ≤ closure ({x, x * Z⁻¹} : Set G) := Subgroup.zpowers_le.2 hx_cl
    have hmem : b * Z ^ (-(k * j)) * Z ^ (k * j) ∈ closure ({x, x * Z⁻¹} : Set G) :=
      mul_mem (hzp hw) (zpow_mem hZcl _)
    rwa [show b * Z ^ (-(k * j)) * Z ^ (k * j) = b by group] at hmem
  · rw [Subgroup.closure_le]
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with hc | hc
    · rw [hc]
      exact Subgroup.mem_inf.2 ⟨hxBs, hxC⟩
    · rw [hc]
      exact Subgroup.mem_inf.2 ⟨mul_mem hxBs (inv_mem hZBs), mul_mem hxC (inv_mem hZC)⟩

end CFSG.GGQ2Prime
