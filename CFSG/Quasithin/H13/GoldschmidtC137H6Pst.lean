module

public import CFSG.Quasithin.H13.GoldschmidtC137H6Frm2
public import CFSG.Quasithin.H13.GoldschmidtC137S6Pst

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

@[expose] noncomputable def KP : Subgroup (Gp 6) := (autI h.hVe P).comap F.ρ

theorem map_KP : F.KP.map F.ρ = autI h.hVe P :=
  F.map_comap_eq (autI_mono h.hVe h.hPX.le)

theorem T6_le_KP : T6 ≤ F.KP := fun σ hσ => by
  show F.ρ σ ∈ autI h.hVe P
  have hmem : F.ρ σ ∈ T6.map F.ρ := ⟨σ, hσ, rfl⟩
  rw [F.hT] at hmem
  exact autI_mono h.hVe h.hTP hmem

theorem KP_max
    (hPmax : ∀ K : Subgroup (MulAut (IntMod V h.hVe)), autI h.hVe P ≤ K → K ≤ autI h.hVe X →
      K = autI h.hVe P ∨ K = autI h.hVe X)
    {H : Subgroup (Gp 6)} (hKH : F.KP ≤ H) : H = F.KP ∨ H = ⊤ := by
  have hY : H.map F.ρ ≤ autI h.hVe X := by
    rw [← F.hX]
    exact Subgroup.map_mono le_top
  have hle : autI h.hVe P ≤ H.map F.ρ := by
    rw [← F.map_KP]
    exact Subgroup.map_mono hKH
  rcases hPmax _ hle hY with h1 | h1
  · left
    show H = (autI h.hVe P).comap F.ρ
    rw [← h1, Subgroup.comap_map_eq_self_of_injective F.inj]
  · right
    exact Subgroup.map_injective F.inj (h1.trans F.hX.symm)

theorem KP_ne_top (hPne : autI h.hVe P ≠ autI h.hVe X) : F.KP ≠ ⊤ := by
  intro hK
  apply hPne
  rw [← F.map_KP, hK, F.hX]

theorem KP_cases
    (hPmax : ∀ K : Subgroup (MulAut (IntMod V h.hVe)), autI h.hVe P ≤ K → K ≤ autI h.hVe X →
      K = autI h.hVe P ∨ K = autI h.hVe X)
    (hPne : autI h.hVe P ≠ autI h.hVe X) : F.KP = H1 ∨ F.KP = H2 := by
  rcases overgroups F.T6_le_KP with h0 | h1 | h2 | htop
  · exfalso
    rcases F.KP_max hPmax (H := H1) (h0 ▸ T6_le_H1) with h3 | h3
    · exact T6_ne_H1 (h0.symm.trans h3.symm)
    · exact H1_ne_top h3
  · exact Or.inl h1
  · exact Or.inr h2
  · exact absurd htop (F.KP_ne_top hPne)

theorem autI_P_cases
    (hPmax : ∀ K : Subgroup (MulAut (IntMod V h.hVe)), autI h.hVe P ≤ K → K ≤ autI h.hVe X →
      K = autI h.hVe P ∨ K = autI h.hVe X)
    (hPne : autI h.hVe P ≠ autI h.hVe X) :
    autI h.hVe P = H1.map F.ρ ∨ autI h.hVe P = H2.map F.ρ := by
  rw [← F.map_KP]
  rcases F.KP_cases hPmax hPne with h1 | h1
  · exact Or.inl (by rw [h1])
  · exact Or.inr (by rw [h1])

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
