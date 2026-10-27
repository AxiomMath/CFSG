module

public import CFSG.Quasithin.H13.GoldschmidtC137H6InvNC

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem swap_mem_pCore {L : Subgroup G} {l₁ l₂ d₁ d₂ : G} (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L)
    (hd₁ : d₁ ∈ A6.o2Z L) (hd₂ : d₂ ∈ A6.o2Z L) :
    ((l₂ * d₁) * (l₁ * d₂) * (l₂ * d₁)⁻¹ * (l₁ * d₂)⁻¹) * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) ∈
      pCoreOf 2 L := by
  obtain ⟨hd₁L, hz₁⟩ := mem_o2Z_gc.1 hd₁
  obtain ⟨hd₂L, hz₂⟩ := mem_o2Z_gc.1 hd₂
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hφ
  set a₁ : ↥L := ⟨l₁, hl₁⟩ with ha₁
  set a₂ : ↥L := ⟨l₂, hl₂⟩ with ha₂
  set e₁ : ↥L := ⟨d₁, hd₁L⟩ with he₁
  set e₂ : ↥L := ⟨d₂, hd₂L⟩ with he₂
  have h1 : φ (⁅a₂ * e₁, a₁ * e₂⁆ * ⁅a₁, a₂⁆) = 1 := by
    have hc : ⁅φ a₂ * φ e₁, φ a₁ * φ e₂⁆ = ⁅φ a₂, φ a₁⁆ :=
      commutator_mul_central_gc (z₁ := φ e₁) (z₂ := φ e₂) hz₁ hz₂ _ _
    rw [map_mul, map_commutatorElement, map_commutatorElement, map_mul, map_mul, hc,
      ← commutatorElement_inv (φ a₁) (φ a₂), inv_mul_cancel]
  have h2 := coe_mem_pCoreOf_iff.2 ((QuotientGroup.eq_one_iff _).1 h1)
  exact h2

theorem conj_comm_eq_gc {g l₁ l₂ d₁ d₂ : G} (e1 : g * l₁ * g⁻¹ = l₂ * d₁)
    (e2 : g * l₂ * g⁻¹ = l₁ * d₂) :
    g * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * g⁻¹ = (l₂ * d₁) * (l₁ * d₂) * (l₂ * d₁)⁻¹ * (l₁ * d₂)⁻¹ := by
  calc g * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * g⁻¹
      = (g * l₁ * g⁻¹) * (g * l₂ * g⁻¹) * (g * l₁ * g⁻¹)⁻¹ * (g * l₂ * g⁻¹)⁻¹ := by group
    _ = (l₂ * d₁) * (l₁ * d₂) * (l₂ * d₁)⁻¹ * (l₁ * d₂)⁻¹ := by rw [e1, e2]

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem o2Z_of_star_eq {x y : G} (hx : x ∈ L) (hy : y ∈ L)
    (hNx : x ∈ normalizer (V : Set G)) (hNy : y ∈ normalizer (V : Set G))
    (hxy : convI h.hVe ⟨x, hNx⟩ = convI h.hVe ⟨y, hNy⟩) : x⁻¹ * y ∈ A6.o2Z L := by
  have h1 : convI h.hVe (⟨x, hNx⟩⁻¹ * ⟨y, hNy⟩) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 : x⁻¹ * y ∈ centralizer (V : Set G) := (convI_eq_one_iff h.hVe _).1 h1
  rw [← h.D_eq_o2Z]
  exact ⟨L.mul_mem (L.inv_mem hx) hy, h2⟩

end H6Ctx

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

theorem lift_L {σ : Gp 6} (hσ : σ ∈ alternatingGroup (Fin 6)) :
    ∃ l ∈ L, ∃ hN : l ∈ normalizer (V : Set G), convI h.hVe ⟨l, hN⟩ = F.ρ σ := by
  have hmem : F.ρ σ ∈ autI h.hVe L := by
    rw [← F.hA]
    exact ⟨σ, hσ, rfl⟩
  obtain ⟨g, hgL, hg⟩ := (mem_autI h.hVe).1 hmem
  exact ⟨g, hgL, g.2, hg⟩

theorem lift_X (σ : Gp 6) :
    ∃ g ∈ X, ∃ hN : g ∈ normalizer (V : Set G), convI h.hVe ⟨g, hN⟩ = F.ρ σ := by
  have hmem : F.ρ σ ∈ autI h.hVe X := by
    rw [← F.hX]
    exact ⟨σ, trivial, rfl⟩
  obtain ⟨g, hgX, hg⟩ := (mem_autI h.hVe).1 hmem
  exact ⟨g, hgX, g.2, hg⟩

theorem star_conj_eq {g l : G} {σ τ : Gp 6} (hg : g ∈ normalizer (V : Set G))
    (hl : l ∈ normalizer (V : Set G)) (hgl : g * l * g⁻¹ ∈ normalizer (V : Set G))
    (hσ : convI h.hVe ⟨g, hg⟩ = F.ρ σ) (hτ : convI h.hVe ⟨l, hl⟩ = F.ρ τ) :
    convI h.hVe ⟨g * l * g⁻¹, hgl⟩ = F.ρ (σ * τ * σ⁻¹) := by
  have e : (⟨g * l * g⁻¹, hgl⟩ : ↥(normalizer (V : Set G))) =
      ⟨g, hg⟩ * ⟨l, hl⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hσ, hτ, map_mul, map_mul, map_inv]

theorem star_comm_eq {a b : G} {σ τ : Gp 6} (ha : a ∈ normalizer (V : Set G))
    (hb : b ∈ normalizer (V : Set G)) (hab : a * b * a⁻¹ * b⁻¹ ∈ normalizer (V : Set G))
    (hσ : convI h.hVe ⟨a, ha⟩ = F.ρ σ) (hτ : convI h.hVe ⟨b, hb⟩ = F.ρ τ) :
    convI h.hVe ⟨a * b * a⁻¹ * b⁻¹, hab⟩ = F.ρ (σ * τ * σ⁻¹ * τ⁻¹) := by
  have e : (⟨a * b * a⁻¹ * b⁻¹, hab⟩ : ↥(normalizer (V : Set G))) =
      ⟨a, ha⟩ * ⟨b, hb⟩ * ⟨a, ha⟩⁻¹ * ⟨b, hb⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hσ, hτ, map_mul, map_mul, map_mul, map_inv,
    map_inv]

theorem comm_lifts_mem_o2Z {l₁ l₂ : G} (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L)
    (hN₁ : l₁ ∈ normalizer (V : Set G)) (hN₂ : l₂ ∈ normalizer (V : Set G))
    (h₁ : convI h.hVe ⟨l₁, hN₁⟩ = F.ρ cT1) (h₂ : convI h.hVe ⟨l₂, hN₂⟩ = F.ρ cT2) :
    l₁ * l₂ * l₁⁻¹ * l₂⁻¹ ∈ A6.o2Z L := by
  have hNw : l₁ * l₂ * l₁⁻¹ * l₂⁻¹ ∈ normalizer (V : Set G) :=
    (normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem
      ((normalizer (V : Set G)).mul_mem hN₁ hN₂) ((normalizer (V : Set G)).inv_mem hN₁))
      ((normalizer (V : Set G)).inv_mem hN₂)
  have h1 : convI h.hVe ⟨l₁ * l₂ * l₁⁻¹ * l₂⁻¹, hNw⟩ = 1 := by
    rw [F.star_comm_eq hN₁ hN₂ hNw h₁ h₂, cT_comm, map_one]
  have h2 : l₁ * l₂ * l₁⁻¹ * l₂⁻¹ ∈ centralizer (V : Set G) :=
    (convI_eq_one_iff h.hVe _).1 h1
  rw [← h.D_eq_o2Z]
  exact ⟨L.mul_mem (L.mul_mem (L.mul_mem hl₁ hl₂) (L.inv_mem hl₁)) (L.inv_mem hl₂), h2⟩

theorem exists_inv_witness :
    ∃ (g₀ : G) (_ : g₀ ∈ X) (hN₀ : g₀ ∈ normalizer (V : Set G)),
      convI h.hVe ⟨g₀, hN₀⟩ = F.ρ sw0 ∧
      ∃ w : G, w ∈ A6.o2Z L ∧ w ∉ pCoreOf 2 L ∧ g₀ * w * g₀⁻¹ * w ∈ pCoreOf 2 L := by
  obtain ⟨g₀, hg₀X, hN₀, hg₀⟩ := F.lift_X sw0
  obtain ⟨l₁, hl₁, hN₁, h₁⟩ := F.lift_L cT1_even
  obtain ⟨l₂, hl₂, hN₂, h₂⟩ := F.lift_L cT2_even
  have hn := Subgroup.mem_normalizer_iff.1 (h.hn hg₀X)
  have hc₁ : g₀ * l₁ * g₀⁻¹ ∈ L := (hn l₁).1 hl₁
  have hc₂ : g₀ * l₂ * g₀⁻¹ ∈ L := (hn l₂).1 hl₂
  have hNc₁ : g₀ * l₁ * g₀⁻¹ ∈ normalizer (V : Set G) := h.hXN (h.hLX hc₁)
  have hNc₂ : g₀ * l₂ * g₀⁻¹ ∈ normalizer (V : Set G) := h.hXN (h.hLX hc₂)
  have hs₁ : convI h.hVe ⟨l₂, hN₂⟩ = convI h.hVe ⟨g₀ * l₁ * g₀⁻¹, hNc₁⟩ := by
    rw [F.star_conj_eq hN₀ hN₁ hNc₁ hg₀ h₁, sw0_conj1, h₂]
  have hs₂ : convI h.hVe ⟨l₁, hN₁⟩ = convI h.hVe ⟨g₀ * l₂ * g₀⁻¹, hNc₂⟩ := by
    rw [F.star_conj_eq hN₀ hN₂ hNc₂ hg₀ h₂, sw0_conj2, h₁]
  have hd₁ := h.o2Z_of_star_eq hl₂ hc₁ hN₂ hNc₁ hs₁
  have hd₂ := h.o2Z_of_star_eq hl₁ hc₂ hN₁ hNc₂ hs₂
  have hw := F.comm_lifts_mem_o2Z hl₁ hl₂ hN₁ hN₂ h₁ h₂
  refine ⟨g₀, hg₀X, hN₀, hg₀, l₁ * l₂ * l₁⁻¹ * l₂⁻¹, hw, F.not_comm_lifts hl₁ hl₂ h₁ h₂, ?_⟩
  obtain ⟨d₁, hd₁def⟩ : ∃ d₁, d₁ = l₂⁻¹ * (g₀ * l₁ * g₀⁻¹) := ⟨_, rfl⟩
  obtain ⟨d₂, hd₂def⟩ : ∃ d₂, d₂ = l₁⁻¹ * (g₀ * l₂ * g₀⁻¹) := ⟨_, rfl⟩
  rw [← hd₁def] at hd₁
  rw [← hd₂def] at hd₂
  have e1 : g₀ * l₁ * g₀⁻¹ = l₂ * d₁ := by rw [hd₁def]; group
  have e2 : g₀ * l₂ * g₀⁻¹ = l₁ * d₂ := by rw [hd₂def]; group
  rw [conj_comm_eq_gc e1 e2]
  exact swap_mem_pCore hl₁ hl₂ hd₁ hd₂

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
