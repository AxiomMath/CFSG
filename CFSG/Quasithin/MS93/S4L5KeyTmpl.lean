module

public import CFSG.Quasithin.MS93.S4LCoreC
public import CFSG.Quasithin.MS93.M15Lift

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem le_center_of_le_sup_lift (h : PUHyp M T L) (hmin : PUMin M T L)
    (hlift : ∀ l ∈ L, ∀ u ∈ Uq M T L,
      l * u * l⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) → l * u * l⁻¹ = u)
    {W : Subgroup G} (hWT : W ≤ T) (hWc : (W.subgroupOf T).Characteristic)
    (hW : W ≤ Uq M T L ⊔ Dq M L) : T ≤ Subgroup.centralizer (W : Set G) := by
  set T₁ := T ⊓ Subgroup.centralizer (W : Set G) with hT₁
  have hT₁T : T₁ ≤ T := inf_le_left
  have hDU : Dq M L ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (inf_le_left.trans (pCoreOf_le' M)).trans (le_normalizer_Uq h.le_normalizer)
  have hUQ : Uq M T L ≤ Xq M := h.Uq_le_Xq
  have hgood : (L ⊔ T₁) ⊓ pCoreOf 2 M ≤ T₁ := by
    rintro x ⟨hxLT, hxQ⟩
    refine ⟨h.pCore_le hxQ, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    obtain ⟨ℓ, hℓ, t, ht, rfl⟩ :=
      S34D.exists_mul_of_mem_sup (hT₁T.trans (h.le.trans h.le_normalizer)) hxLT
    obtain ⟨u, hu, d, hd, rfl⟩ := S34D.exists_mul_of_mem_sup hDU (hW hw)
    have htw : u * d * t = t * (u * d) :=
      Subgroup.mem_centralizer_iff.mp ht.2 (u * d) hw
    have hdℓ : d * ℓ = ℓ * d := Subgroup.mem_centralizer_iff.mp hd.2 ℓ hℓ |>.symm
    have huZ : u ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
      A4.centerOf_le_centralizer _ (A4.omegaOneCenterOf_le_centerOf _ (hUQ hu))
    have hux : u * (ℓ * t) = ℓ * t * u := (Subgroup.mem_centralizer_iff.mp huZ _ hxQ).symm
    have hud : u * d = d * u := (Subgroup.mem_centralizer_iff.mp huZ _ hd.1).symm
    have e1 : ⁅u * d, ℓ * t⁆ = ⁅u, ℓ⁆ := by
      have htw' : t * (u * d)⁻¹ * t⁻¹ = (u * d)⁻¹ := by
        calc t * (u * d)⁻¹ * t⁻¹ = (u * d)⁻¹ * (u * d * t) * (u * d)⁻¹ * t⁻¹ := by group
          _ = (u * d)⁻¹ * (t * (u * d)) * (u * d)⁻¹ * t⁻¹ := by rw [htw]
          _ = (u * d)⁻¹ := by group
      have hdℓ' : d * ℓ * d⁻¹ = ℓ := by rw [hdℓ, mul_inv_cancel_right]
      calc ⁅u * d, ℓ * t⁆ = u * d * ℓ * (t * (u * d)⁻¹ * t⁻¹) * ℓ⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = u * (d * ℓ * d⁻¹) * u⁻¹ * ℓ⁻¹ := by rw [htw']; group
        _ = ⁅u, ℓ⁆ := by rw [hdℓ', commutatorElement_def]
    have e2 : ⁅u * d, ℓ * t⁆ = ⁅d, ℓ * t⁆ := by
      have hc : u * (d * (ℓ * t) * d⁻¹) = d * (ℓ * t) * d⁻¹ * u := by
        have h1 : Commute u d := hud
        have h2 : Commute u (ℓ * t) := hux
        exact ((h1.mul_right h2).mul_right h1.inv_right).eq
      calc ⁅u * d, ℓ * t⁆ = u * (d * (ℓ * t) * d⁻¹) * u⁻¹ * (ℓ * t)⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = ⁅d, ℓ * t⁆ := by rw [hc, commutatorElement_def]; group
    have hxM : ℓ * t ∈ M := pCoreOf_le' M hxQ
    have hcD : ⁅u * d, ℓ * t⁆ ∈ Dq M L := by
      rw [e2, commutatorElement_def]
      have : d * (ℓ * t) * d⁻¹ * (ℓ * t)⁻¹ = d * ((ℓ * t) * d⁻¹ * (ℓ * t)⁻¹) := by group
      rw [this]
      exact (Dq M L).mul_mem hd ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_Dq h.le_normalizer hxM) d⁻¹).mp ((Dq M L).inv_mem hd))
    have hu' : u⁻¹ ∈ Uq M T L := inv_mem hu
    have hw' : ℓ * u⁻¹ * ℓ⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_Uq h.le_normalizer (h.L_le hℓ)) u⁻¹).mp hu'
    have hcomm' : ⁅u, ℓ⁆ = ℓ * u⁻¹ * ℓ⁻¹ * u⁻¹⁻¹ := by
      rw [commutatorElement_def, inv_inv]
      calc u * ℓ * u⁻¹ * ℓ⁻¹ = u * (ℓ * u⁻¹ * ℓ⁻¹) := by group
        _ = ℓ * u⁻¹ * ℓ⁻¹ * u := Sp4L.uq_comm h hu hw'
    have hmem : ℓ * u⁻¹ * ℓ⁻¹ * u⁻¹⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      rw [← hcomm', ← e1]
      exact hcD.2
    have hfix := hlift ℓ hℓ u⁻¹ hu' hmem
    have h1 : ⁅u * d, ℓ * t⁆ = 1 := by
      rw [e1, hcomm', hfix, mul_inv_cancel]
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hT₁eq := hmin T₁ hT₁T (S34E.inf_centralizer_characteristic hWT hWc) hgood
  intro t ht
  rw [← hT₁eq] at ht
  exact ht.2

theorem qv_le_centralizer_of_le_uloc_sup_dloc_lift (h : PUHyp M T L) (hmin : PUMin M T L)
    (hlift : ∀ l ∈ L, ∀ u ∈ Uq M T L,
      l * u * l⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G) → l * u * l⁻¹ = u)
    {W : Subgroup (puAmalgam h.le).Universal} (hWT : W ≤ Qv (puAmalgam h.le) (baseB _))
    (hWn : stab (puAmalgam h.le) (baseB _) ≤ Subgroup.normalizer (W : Set _))
    (hW : W ≤ Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _)) :
    Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.centralizer (W : Set _) := by
  have hWM : W ≤ imM h.le M :=
    hWT.trans (by rw [puAmalgam.qv_baseB]; exact imM_mono h.le h.le)
  have himW : imM h.le (S33.pre h.le W) = W := S33.imM_pre h.le hWM
  have hW₀T := Core.pre_le_of_le_qv_baseB h hWT
  have hW₀c := Core.characteristic_pre h hWn
  have hUD : Uloc h.le L (baseA _) ⊔ Dloc h.le L (baseA _) ≤ imM h.le (Uq M T L ⊔ Dq M L) := by
    rw [Uloc, Dloc, puTrans_baseA h.le (S4A.Uq_normal h), puTrans_baseA h.le (S4A.Dq_normal h)]
    exact sup_le (imM_mono h.le le_sup_left) (imM_mono h.le le_sup_right)
  have hW₀UD : S33.pre h.le W ≤ Uq M T L ⊔ Dq M L := by
    intro x hx
    obtain ⟨m, hmW, rfl⟩ := (S33.mem_pre_iff' h.le).mp hx
    exact (S33.ofA_mem_imM_iff h.le m).mp (hUD (hW hmW))
  have hcen := le_center_of_le_sup_lift h hmin hlift hW₀T hW₀c hW₀UD
  rw [puAmalgam.qv_baseB, ← himW]
  exact S34E.imM_le_centralizer h hcen

end CFSG.Quasithin.MS93.S4L
