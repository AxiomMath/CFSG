module

public import CFSG.Quasithin.H13.GoldschmidtC137S6ToBase
public import CFSG.Quasithin.H13.GoldschmidtC137CPst
public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin2
public import CFSG.Quasithin.H13.GoldschmidtC137Data

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type}  [Group G]

theorem card_Gp6 : Nat.card (Gp 6) = 720 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem T6_ne_H1 : T6 ≠ H1 := fun h => by
  have := card_T6
  rw [h, card_H1] at this
  omega

theorem H1_ne_top : H1 ≠ ⊤ := fun h => by
  have := card_H1
  rw [h, Subgroup.card_top, card_Gp6] at this
  omega

namespace S6Frame

variable [Finite G] {X T V L P M : Subgroup G} {h : S6Ctx X T V L P M} (F : S6Frame h)

@[expose] noncomputable def KP : Subgroup (Gp 6) := (autI h.hVe P).comap F.ρ

theorem map_KP : F.KP.map F.ρ = autI h.hVe P :=
  F.toC137B.map_KP

theorem T6_le_KP : T6 ≤ F.KP :=
  F.toC137B.T6_le_KP

theorem KP_max {H : Subgroup (Gp 6)} (hKH : F.KP ≤ H) : H = F.KP ∨ H = ⊤ := by
  have hY : H.map F.ρ ≤ autI h.hVe X := by
    rw [← F.hX]
    exact Subgroup.map_mono le_top
  have hPpre : P ≤ starPreIn h.hVe X (H.map F.ρ) := by
    intro p hp
    have hpN := h.hXN (h.hPX.le hp)
    refine mem_starPreIn.2 ⟨h.hPX.le hp, hpN, ?_⟩
    have h1 : convI h.hVe ⟨p, hpN⟩ ∈ autI h.hVe P := convI_mem_autI h.hVe hp hpN
    rw [← F.map_KP] at h1
    exact Subgroup.map_mono hKH h1
  have hpre := autI_starPreIn h.hVe h.hXN hY
  rcases h.hmax _ (h.hPeq.symm.le.trans hPpre) (starPreIn_le h.hVe) with h1 | h1
  · left
    have hPP : starPreIn h.hVe X (H.map F.ρ) = P := h1.trans h.hPeq.symm
    have h2 : autI h.hVe P = H.map F.ρ := by
      rw [hPP] at hpre
      exact hpre
    show H = (autI h.hVe P).comap F.ρ
    rw [h2, Subgroup.comap_map_eq_self_of_injective F.inj]
  · right
    rw [h1, ← F.hX] at hpre
    exact (Subgroup.map_injective F.inj hpre).symm

theorem KP_ne_top : F.KP ≠ ⊤ := by
  intro hK
  have h1 : autI h.hVe P = autI h.hVe X := by
    rw [← F.map_KP, hK, F.hX]
  have hXP : X ≤ P := by
    intro x hx
    have hxN := h.hXN hx
    have hx1 : convI h.hVe ⟨x, hxN⟩ ∈ autI h.hVe P := h1 ▸ convI_mem_autI h.hVe hx hxN
    obtain ⟨g, hgP, hg⟩ := (mem_autI h.hVe).1 hx1
    have hc : convI h.hVe (g⁻¹ * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, map_inv, hg, inv_mul_cancel]
    have hcen := (convI_eq_one_iff h.hVe _).1 hc
    have hQ : (g : G)⁻¹ * x ∈ pCoreOf 2 P := by
      refine h.hQR ?_
      rw [← h.CXV]
      exact ⟨X.mul_mem (X.inv_mem (h.hPX.le hgP)) hx, hcen⟩
    have : x = (g : G) * ((g : G)⁻¹ * x) := by group
    rw [this]
    exact P.mul_mem hgP (CFSG.LieType.BorelTits.pCoreOf_le 2 P hQ)
  exact h.hPX.not_ge hXP

theorem KP_cases : F.KP = H1 ∨ F.KP = H2 := by
  rcases overgroups F.T6_le_KP with h0 | h1 | h2 | htop
  · exfalso
    rcases F.KP_max (H := H1) (h0 ▸ T6_le_H1) with h3 | h3
    · exact T6_ne_H1 (h0.symm.trans h3.symm)
    · exact H1_ne_top h3
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd htop F.KP_ne_top

theorem autI_P_cases : autI h.hVe P = H1.map F.ρ ∨ autI h.hVe P = H2.map F.ρ := by
  rw [← F.map_KP]
  rcases F.KP_cases with h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1])

end S6Frame

end CFSG.Quasithin.H13.U3.GC137
