module

public import CFSG.Quasithin.H13.GoldschmidtC137H6InvSw
public import CFSG.Quasithin.H13.GoldschmidtC137H6Str2

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

namespace H6Ctx

variable [Finite G] {X T V L P : Subgroup G} (h : H6Ctx X T V L P)
include h

theorem Q_inf_L_le : pCoreOf 2 X ⊓ L ≤ pCoreOf 2 L := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le inf_le_left)
  intro u hu
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have hQn := Subgroup.mem_normalizer_iff.1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (h.hLX hu))
  constructor
  · rintro ⟨hnQ, hnL⟩
    exact ⟨(hQn n).1 hnQ, L.mul_mem (L.mul_mem hu hnL) (L.inv_mem hu)⟩
  · rintro ⟨hnQ, hnL⟩
    refine ⟨(hQn n).2 hnQ, ?_⟩
    have := L.mul_mem (L.mul_mem (L.inv_mem hu) hnL) hu
    simpa [mul_assoc] using this

theorem comm_Q_L {t u : G} (ht : t ∈ pCoreOf 2 X) (hu : u ∈ L) :
    t * u * t⁻¹ * u⁻¹ ∈ pCoreOf 2 L := by
  refine h.Q_inf_L_le ⟨?_, ?_⟩
  · have hQn := Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (h.hLX hu))
    have h1 := (hQn t⁻¹).1 ((pCoreOf 2 X).inv_mem ht)
    have : t * u * t⁻¹ * u⁻¹ = t * (u * t⁻¹ * u⁻¹) := by group
    rw [this]
    exact (pCoreOf 2 X).mul_mem ht h1
  · have htX : t ∈ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X ht
    have hn := Subgroup.mem_normalizer_iff.1 (h.hn htX)
    exact L.mul_mem ((hn u).1 hu) (L.inv_mem hu)

theorem conj_pCore_mem {x k : G} (hx : x ∈ X) (hk : k ∈ pCoreOf 2 L) :
    x * k * x⁻¹ ∈ pCoreOf 2 L :=
  (Subgroup.mem_normalizer_iff.1
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (h.hn hx)) k).1 hk

end H6Ctx

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

theorem sign_eq_neg_one {τ : Gp 6} (hτ : τ ∉ alternatingGroup (Fin 6)) :
    Equiv.Perm.sign τ = -1 := by
  rw [Equiv.Perm.mem_alternatingGroup] at hτ
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h1 | h1
  · exact absurd h1 hτ
  · exact h1

theorem inv_action {g₀ w r : G} (hg₀X : g₀ ∈ X) (hN₀ : g₀ ∈ normalizer (V : Set G))
    (hg₀ : convI h.hVe ⟨g₀, hN₀⟩ = F.ρ sw0) (hw : w ∈ A6.o2Z L)
    (hsw : g₀ * w * g₀⁻¹ * w ∈ pCoreOf 2 L) (hr : r ∈ X)
    (hrn : r ∉ L ⊔ (X ⊓ centralizer (V : Set G))) : r * w * r⁻¹ * w ∈ pCoreOf 2 L := by
  have hrN : r ∈ normalizer (V : Set G) := h.hXN hr
  have hrmem : convI h.hVe ⟨r, hrN⟩ ∈ autI h.hVe X := convI_mem_autI h.hVe hr hrN
  rw [← F.hX] at hrmem
  obtain ⟨σ, -, hσ⟩ := hrmem
  have hσodd : σ ∉ alternatingGroup (Fin 6) := by
    intro hσA
    obtain ⟨l, hlL, hlN, hl⟩ := F.lift_L hσA
    apply hrn
    have hc : convI h.hVe (⟨l, hlN⟩⁻¹ * ⟨r, hrN⟩) = 1 := by
      rw [map_mul, map_inv, hl, hσ, inv_mul_cancel]
    have hcC : l⁻¹ * r ∈ centralizer (V : Set G) := (convI_eq_one_iff h.hVe _).1 hc
    have : r = l * (l⁻¹ * r) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlL)
      (Subgroup.mem_sup_right ⟨X.mul_mem (X.inv_mem (h.hLX hlL)) hr, hcC⟩)
  have hσ' : sw0⁻¹ * σ ∈ alternatingGroup (Fin 6) := by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, sign_eq_neg_one sw0_odd,
      sign_eq_neg_one hσodd]
    decide
  obtain ⟨l, hlL, hlN, hl⟩ := F.lift_L hσ'
  have hg₀N : g₀ ∈ normalizer (V : Set G) := hN₀
  have hcX : l⁻¹ * (g₀⁻¹ * r) ∈ X :=
    X.mul_mem (X.inv_mem (h.hLX hlL)) (X.mul_mem (X.inv_mem hg₀X) hr)
  have hcC : l⁻¹ * (g₀⁻¹ * r) ∈ centralizer (V : Set G) := by
    have hc : convI h.hVe (⟨l, hlN⟩⁻¹ * (⟨g₀, hN₀⟩⁻¹ * ⟨r, hrN⟩)) = 1 := by
      rw [map_mul, map_mul, map_inv, map_inv, hl, hg₀, ← hσ, ← map_inv, ← map_inv, ← map_mul,
        ← map_mul, ← map_one F.ρ]
      congr 1
      group
    exact (convI_eq_one_iff h.hVe _).1 hc
  obtain ⟨d, hd, t, ht, hdt⟩ := h.C_le_D_mul_T ⟨hcX, hcC⟩
  have htQ : t ∈ pCoreOf 2 X := by
    rw [← h.hTC]
    refine ⟨ht, ?_⟩
    have : t = d⁻¹ * (l⁻¹ * (g₀⁻¹ * r)) := by rw [hdt]; group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hd.2) hcC
  have hreq : r = g₀ * (l * d) * t := by
    have : r = g₀ * (l * (l⁻¹ * (g₀⁻¹ * r))) := by group
    rw [this, hdt]
    group
  have hy : l * d ∈ L := L.mul_mem hlL hd.1
  have hdz : d ∈ A6.o2Z L := h.D_eq_o2Z ▸ hd
  have hk₁ : t * w * t⁻¹ * w⁻¹ ∈ pCoreOf 2 L :=
    h.comm_Q_L htQ (o2Z_le_gc L hw)
  have hk₃ : (l * d) * w * (l * d)⁻¹ * w⁻¹ ∈ pCoreOf 2 L := by
    have h1 := (pCoreOf 2 L).inv_mem (comm_o2Z_gc hw hy)
    have : (l * d) * w * (l * d)⁻¹ * w⁻¹ = (w * (l * d) * w⁻¹ * (l * d)⁻¹)⁻¹ := by group
    rw [this]
    exact h1
  have hk₂ := h.conj_pCore_mem (h.hLX hy) hk₁
  have hk₄ := h.conj_pCore_mem hg₀X ((pCoreOf 2 L).mul_mem hk₂ hk₃)
  have e : r * w * r⁻¹ * w =
      (g₀ * ((l * d) * (t * w * t⁻¹ * w⁻¹) * (l * d)⁻¹ * ((l * d) * w * (l * d)⁻¹ * w⁻¹)) *
        g₀⁻¹) * (g₀ * w * g₀⁻¹ * w) := by
    rw [hreq]
    group
  rw [e]
  exact (pCoreOf 2 L).mul_mem hk₄ hsw

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
