module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.M591A
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632d

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.UC6.Mz614 (centralizer_singleton_le_normalizer_zpowers)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem gl (h63 : R6_3 Dat) (h619 : m.C619) (h620 : m.C620)
    (h632 : m.C632) {u : G} (hu : u ∈ normalizer (m.L : Set G)) (h2 : ∃ k : ℕ, orderOf u = 2 ^ k)
    (h1 : u ≠ 1) : ¬ ⁅zpowers u, m.L⁆ ≤ m.OL := by
  intro hcomm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨n, hn⟩ := h2
  have hup : IsPGroup 2 (zpowers u) := IsPGroup.of_card (by rw [Nat.card_zpowers, hn])
  have hodd := m.odd_card_OL h63 h619 h620 h632
  have hsup : m.L = m.OL ⊔ (m.L ⊓ centralizer ((zpowers u : Subgroup G) : Set G)) :=
    eq_sup_centralizer_of_coprime m.OL_le_L m.L_le_normalizer_OL hup (Subgroup.zpowers_le.2 hu)
      hcomm hodd
  set C : Subgroup G := m.L ⊓ centralizer ((zpowers u : Subgroup G) : Set G) with hC
  have hCL : C ≤ m.L := inf_le_left
  obtain ⟨P₁, hP₁C⟩ := exists_isSylowOf m.r C
  have hP₁L : IsSylowOf m.r P₁ m.L := by
    rw [isSylowOf_iff] at hP₁C ⊢
    obtain ⟨hle, hp, hdvd⟩ := hP₁C
    refine ⟨hle.trans hCL, hp, fun hdvd' => ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex P₁ C m.L hle hCL] at hdvd'
    rcases (Nat.Prime.dvd_mul m.hr).1 hdvd' with h | h
    · exact hdvd h
    · have hrel := relIndex_dvd_card_of_sup_eq m.OL_le_L hCL m.L_le_normalizer_OL hsup
      exact ((Nat.Prime.coprime_iff_not_dvd m.hr).1 m.coprime_card_OL) (h.trans hrel)
  obtain ⟨k, hkL, hk⟩ := exists_conj_le_of_isSylowOf hP₁L
    (show m.EL ≤ m.L from inf_le_right) (m.isPGroup_of_le_A_inf_L le_rfl)
  have hkC : ∀ e ∈ m.EL, k⁻¹ * e * k ∈ centralizer ((zpowers u : Subgroup G) : Set G) :=
    fun e he => (hP₁C.le (hk e he)).2
  set v : G := k * u * k⁻¹ with hv
  have hvord : orderOf v = 2 ^ n := by
    have h := MulEquiv.orderOf_eq (MulAut.conj k) u
    rw [MulAut.conj_apply] at h
    rw [hv, h, hn]
  have hQp : IsPGroup 2 (zpowers v) := IsPGroup.of_card (by rw [Nat.card_zpowers, hvord])
  have hQne : zpowers v ≠ ⊥ := by
    intro hb
    have hv1 : v = 1 := Subgroup.zpowers_eq_bot.1 hb
    apply h1
    calc u = k⁻¹ * v * k := by rw [hv]; group
      _ = 1 := by rw [hv1]; group
  have hEQ : m.EL ≤ normalizer ((zpowers v : Subgroup G) : Set G) := by
    intro e he
    apply centralizer_singleton_le_normalizer_zpowers v
    rw [mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hcomm' := mem_centralizer_iff.1 (hkC e he) u (mem_zpowers u)
    calc v * e = k * (u * (k⁻¹ * e * k)) * k⁻¹ := by rw [hv]; group
      _ = k * ((k⁻¹ * e * k) * u) * k⁻¹ := by rw [hcomm']
      _ = e * v := by rw [hv]; group
  have hNM := m.normalizer_le_M_of_E_le h63 h620 h632 hQp hQne hEQ
  have hLMk : m.L ≤ m.M.comap (MulAut.conj k).toMonoidHom := by
    refine (le_of_eq hsup).trans (sup_le (fun o ho => ?_) (fun c hc => ?_))
    · have := (mem_normalizer_iff.1 (m.L_le_normalizer_OL hkL) o).1 ho
      exact m.OL_le_M h620 h632 this
    · apply hNM
      apply centralizer_singleton_le_normalizer_zpowers v
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have hcomm' := mem_centralizer_iff.1 hc.2 u (mem_zpowers u)
      calc v * (k * c * k⁻¹) = k * (u * c) * k⁻¹ := by rw [hv]; group
        _ = k * (c * u) * k⁻¹ := by rw [hcomm']
        _ = (k * c * k⁻¹) * v := by rw [hv]; group
  refine m.not_L_le_M h619 fun y hy => ?_
  have h := hLMk (m.L.mul_mem (m.L.mul_mem (m.L.inv_mem hkL) hy) hkL)
  have e : (MulAut.conj k).toMonoidHom (k⁻¹ * y * k) = y := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  rw [Subgroup.mem_comap, e] at h
  exact h

theorem comm_EL_le {Y : Subgroup G} (hEY : m.EL ≤ normalizer (Y : Set G))
    (hcent : ∀ y ∈ Y, ∀ e ∈ m.EL, y * e * y⁻¹ * e⁻¹ ∈ m.OL) : ⁅m.EL, Y⁆ ≤ Y ⊓ m.OL := by
  rw [Subgroup.commutator_le]
  intro e he y hy
  refine ⟨?_, ?_⟩
  · have h1 : e * y * e⁻¹ ∈ Y := (mem_normalizer_iff.1 (hEY he) y).1 hy
    rw [commutatorElement_def]
    exact Y.mul_mem h1 (Y.inv_mem hy)
  · have h1 := hcent y hy e⁻¹ (m.EL.inv_mem he)
    have h2 : e * (y * e⁻¹ * y⁻¹ * e⁻¹⁻¹) * e⁻¹ ∈ m.OL :=
      (mem_normalizer_iff.1 (m.L_le_normalizer_OL he.2) _).1 h1
    have h3 : e * (y * e⁻¹ * y⁻¹ * e⁻¹⁻¹) * e⁻¹ = e * y * e⁻¹ * y⁻¹ := by group
    rw [h3] at h2
    rw [commutatorElement_def]
    exact h2

theorem eq_sup_centralizer_EL {Y : Subgroup G} (hYL : Y ≤ normalizer (m.L : Set G))
    (hEY : m.EL ≤ normalizer (Y : Set G))
    (hcent : ∀ y ∈ Y, ∀ e ∈ m.EL, y * e * y⁻¹ * e⁻¹ ∈ m.OL) :
    Y = (Y ⊓ m.OL) ⊔ (Y ⊓ centralizer (m.EL : Set G)) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  refine eq_sup_centralizer_of_coprime inf_le_left ?_ (m.isPGroup_of_le_A_inf_L le_rfl) hEY
    (m.comm_EL_le hEY hcent) ?_
  · intro y hy
    refine mem_normalizer_of_forward_uc6 fun w hw => ⟨Y.mul_mem (Y.mul_mem hy hw.1) (Y.inv_mem hy), ?_⟩
    have hn := m.mem_normalizer_OL (hYL hy)
    exact (mem_normalizer_iff.1 hn w).1 hw.2
  · intro hdvd
    have hd : Nat.card ↥(Y ⊓ m.OL) ∣ Nat.card m.OL := Subgroup.card_dvd_of_le inf_le_right
    exact ((Nat.Prime.coprime_iff_not_dvd m.hr).1 m.coprime_card_OL) (hdvd.trans hd)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
