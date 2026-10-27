module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2Base
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Stmt2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1S82Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan_8_3b {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h512 : Fan512 F L) : Fan83b F L := by
  intro α D δ' hY i j
  have h : Fan71c F L := h7.2.2.1
  have hkey : ∀ {v : V}, Γ.dist α v ≤ 4 →
      (D.y δ' i • v = v ↔ (Γ.dist (D.alpha i) v ≤ 2 ∨ Γ.dist (D.beta i) v ≤ 2)) :=
    fun {v} hv => D.y_fixed_iff F h h81 hY i hv
  by_cases hij : i = j
  · simp only [hij, ↓reduceIte]
    rw [← hij]
    have hfix : D.y δ' i • D.alpha i = D.alpha i :=
      (hkey (by rw [D.dist_start_alpha F i]; norm_num)).2
        (Or.inl (by rw [SimpleGraph.dist_self]; norm_num))
    have hc := (h.comm_z_iff (D.valence_alpha F i) (D.y δ' i)).2 hfix
    unfold fcomm
    rw [L.z_inv (D.valence_alpha F i)]
    calc (D.y δ' i)⁻¹ * L.z (D.alpha i) * D.y δ' i * L.z (D.alpha i)
        = (D.y δ' i)⁻¹ * (L.z (D.alpha i) * D.y δ' i) * L.z (D.alpha i) := by group
      _ = (D.y δ' i)⁻¹ * (D.y δ' i * L.z (D.alpha i)) * L.z (D.alpha i) := by rw [← hc]
      _ = L.z (D.alpha i) * L.z (D.alpha i) := by group
      _ = 1 := L.z_mul_self (D.valence_alpha F i)
  · simp only [hij, ↓reduceIte]
    refine D.fcomm_z_alpha_eq F h h512 j ?_ ?_ ?_
    · exact (hkey (by rw [SimpleGraph.dist_self]; norm_num)).2
        (Or.inl (by rw [D.dist_alpha_start F i]))
    · refine (hkey (by rw [D.dist_start_beta F j]; norm_num)).2 (Or.inr ?_)
      have := D.dist_vert_ne F h hij (m := 1) (m' := 1) (by norm_num) (by norm_num)
      have h2 : Γ.dist (D.beta i) (D.beta j) = 1 + 1 := this
      omega
    · intro hfix
      have h1 := (hkey (by rw [D.dist_start_alpha F j]; norm_num)).1 hfix
      have h2 : Γ.dist (D.alpha i) (D.alpha j) = 4 := D.dist_alpha_alpha F h hij
      have h3 : Γ.dist (D.beta i) (D.alpha j) = 3 := D.dist_beta_alpha_ne F h (Ne.symm hij)
      omega

end CFSG.Quasithin.Fan86
