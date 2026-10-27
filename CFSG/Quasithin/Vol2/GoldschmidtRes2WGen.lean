module

public import CFSG.Quasithin.Vol2.GoldschmidtRes2WGenAct
public import CFSG.Quasithin.Vol2.GoldschmidtRes2WGenCent

public section

namespace CFSG.Quasithin.Res2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B6 E2 WGen

variable {G : Type} [Group G] [Finite G] {X T M V : Subgroup G} {g : G}

theorem conjSub_B_of_general (h : E2.Pair X T M V g) (hchar : CharTwo X)
    (hcard : (kerIn M X).relIndex X = 60) (hidx : M.relIndex X = 5)
    (hJ : IsPGroup 2 ↥(kerIn M X)) (hVB : (kerIn M X ⊓ V).relIndex V = 4)
    (hBZ : (V ⊓ conjSub g V).relIndex (kerIn M X ⊓ V) = 4)
    (hBru : ∀ x ∈ X, x ∈ M ∨ ∃ m₁ ∈ M, ∃ m₂ ∈ M, x = m₁ * g * m₂) :
    ∀ m ∈ M, conjSub m (kerIn M X ⊓ V) = kerIn M X ⊓ V := by
  have hVM : V ≤ M := h.le_pCoreOf.trans (pCoreOf_le 2 M)
  have hgM : g ∉ M := by
    intro hg
    have hXM : X ≤ M := by
      intro x hx
      rcases hBru x hx with hx | ⟨m₁, hm₁, m₂, hm₂, rfl⟩
      · exact hx
      · exact M.mul_mem (M.mul_mem hm₁ hg) hm₂
    have := Subgroup.relIndex_eq_one.2 hXM
    omega
  have hJM : (kerIn M X).relIndex M = 12 := by
    have := Subgroup.relIndex_mul_relIndex (kerIn M X) M X kerIn_le h.le_X
    rw [hcard, hidx] at this
    omega
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := h.elem.2
  have hG2 := commutator_kerIn_mem_Z h hchar hJ hcard hBZ
  have key : ∀ m ∈ M, conjSub m (kerIn M X ⊓ V) ≤ kerIn M X ⊓ V := by
    intro m hm x hx
    rw [mem_conjSub] at hx
    set b := m⁻¹ * x * m with hbdef
    have hxb : x = m * b * m⁻¹ := by rw [hbdef]; group
    have hmX : m ∈ X := h.le_X hm
    have hbP : b ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) := Subgroup.mem_sup_left hx
    have hxP : x ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) := by
      have := (Subgroup.mem_normalizer_iff.mp (h.le_normalizer_P hmX) b).mp hbP
      rwa [← hxb] at this
    refine h.mem_B_of_commutator_mem_Z hxP (fun v hv => ?_)
    obtain ⟨w, hwV, hwJ⟩ := exists_mem_of_conj h.mem h.le_X hVM hgM hBru hidx hJM hV2 hVB
      (M.inv_mem hm) hv
    set j₀ := w⁻¹ * (m⁻¹ * v * m⁻¹⁻¹) with hj₀
    have hz₁ := hG2 b hbP j₀ hwJ
    set z₁ := b⁻¹ * j₀ * b * j₀⁻¹ with hz₁def
    have hwX : w ∈ X := h.V_le hwV
    have hbV : b ∈ V := hx.2
    have hbX : b ∈ X := h.V_le hbV
    have hz₁w : z₁ * w⁻¹ = w⁻¹ * z₁ := h.mem_center hz₁ (X.inv_mem hwX)
    have hz₁b : z₁ * b⁻¹ = b⁻¹ * z₁ := h.mem_center hz₁ (X.inv_mem hbX)
    have hwb : w * b * w⁻¹ = b := by
      have := h.comm hwV hbV
      calc w * b * w⁻¹ = b * w * w⁻¹ := by rw [this]
        _ = b := by group
    have hin : w * b * z₁ * w⁻¹ * b⁻¹ = z₁ := by
      calc w * b * z₁ * w⁻¹ * b⁻¹ = w * b * (z₁ * w⁻¹) * b⁻¹ := by group
        _ = w * b * (w⁻¹ * z₁) * b⁻¹ := by rw [hz₁w]
        _ = (w * b * w⁻¹) * (z₁ * b⁻¹) := by group
        _ = b * (b⁻¹ * z₁) := by rw [hwb, hz₁b]
        _ = z₁ := by group
    have e : v * x * v⁻¹ * x⁻¹ = m * (w * b * z₁ * w⁻¹ * b⁻¹) * m⁻¹ := by
      rw [hxb, hz₁def, hj₀]; group
    rw [e, hin, conj_eq_of_mem_Z h hz₁ hmX]
    exact hz₁
  intro m hm
  exact conjSub_eq_self (mem_normalizer_of_conjSub_le (key m hm) (by
    simpa using key m⁻¹ (M.inv_mem hm)))

end CFSG.Quasithin.Res2
