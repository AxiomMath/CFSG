module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab2Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL2DMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab2

namespace F6

namespace GoldAmLab4

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem exists_swap (h : GoldHyp A B) (h32 : 32 ≤ Nat.card ↥(A ⊓ B))
    (hn : IsNaturalAt A (A ⊓ B) z V) (hmove : ∃ y ∈ B, y * z * y⁻¹ ≠ z) :
    ∃ (x c : D) (V₂ : Subgroup D), x ∈ B ∧ x * x * x = 1 ∧ x * z * x⁻¹ ≠ z ∧
      c = (x * z * x⁻¹) * (x * x * z * (x * x)⁻¹) ∧ OneSide B A c V₂ := by
  obtain ⟨x, c, V₂, hxB, hx3, hxz, hc, hn₂, -⟩ :=
    exists_natural_data h.vertex_right hn.z_mem hn.z_sq hmove
  have h32' : 32 ≤ Nat.card ↥(B ⊓ A) := by rwa [inf_comm]
  have hn₂' : IsNaturalAt B (B ⊓ A) c V₂ := by rw [inf_comm]; exact hn₂
  have hV₂A : V₂ ≤ pCoreOf 2 A := hn₂'.le_pCoreOf_of_large h.symm h32'
  rcases critDist_dichotomy h.symm hn₂' hV₂A with hb₂ | ⟨-, hU₂⟩
  · exfalso
    have hz' : z ∈ centerOf (B ⊓ A) := by rw [inf_comm]; exact hn.z_mem
    obtain ⟨g, hgA, hg⟩ := exists_move_of_natural hn
    exact hg (((GoldAmL2D.B2Setup.of_critDist_two h.symm hn₂' hb₂).centralizes_omega hz'
      hn.z_sq) g hgA)
  · exact ⟨x, c, V₂, hxB, hx3, hxz, hc, ⟨h.symm, hn₂', hV₂A, hU₂⟩⟩

theorem not_mem_centralizer_of_mem {c : D} {V₂ : Subgroup D} (h2 : OneSide B A c V₂) {p : D}
    (hp : p ∈ V₂) (hp1 : p ≠ 1) (hpc : p ≠ c) :
    p ∉ Subgroup.centralizer (pCoreOf 2 A : Set D) := by
  intro hpC
  have hne : pCoreOf 2 B ≠ pCoreOf 2 A := h2.nat.pCoreOf_ne h2.gold
  have hnot : ¬ pCoreOf 2 A ≤ pCoreOf 2 B := h2.gold.not_pCoreOf_right_le_left hne
  obtain ⟨q, hqA, hqB⟩ : ∃ q ∈ pCoreOf 2 A, q ∉ pCoreOf 2 B := by
    by_contra hcon
    push Not at hcon
    exact hnot fun q hq => hcon q hq
  have hqT : q ∈ B ⊓ A := h2.gold.pCoreOf_right_le hqA
  have h1 : q * p * q⁻¹ = p * c := h2.nat.conj_eq_mul inf_le_left hqT hqB hp hp1 hpc
  have h3 : q * p = p * q := Subgroup.mem_centralizer_iff.mp hpC q hqA
  have h4 : p * c = p * 1 := by
    calc p * c = q * p * q⁻¹ := h1.symm
      _ = p * 1 := by rw [h3]; group
  exact h2.nat.z_ne (mul_left_cancel h4)

end GoldAmLab4

end F6

end CFSG.Quasithin
