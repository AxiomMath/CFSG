module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3S6Cen
public import CFSG.Quasithin.Background.GoldschmidtAmalgamVBBall

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem pair_conj_eq {β s₁ s₃ x : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (h1 : (graph (A ⊔ B) A B).Adj β s₁) (h3 : (graph (A ⊔ B) A B).Adj β s₃)
    (hx : (graph (A ⊔ B) A B).Adj β x) (n13 : s₁ ≠ s₃) (n1x : s₁ ≠ x) (n3x : s₃ ≠ x)
    (e3 : ballStab 1 s₃ ⊓ ballStab 1 β = ballStab 1 s₁ ⊓ ballStab 1 β)
    (ex : ballStab 1 x ⊓ ballStab 1 β = ballStab 1 s₁ ⊓ ballStab 1 β) {m : D}
    (hm : IsPair z V β x m) {g : D} (hgx : g ∈ stab x) (hgβ : g ∈ stab β) :
    g * m * g⁻¹ = m := by
  obtain ⟨a, a', ha, ha1, ha', ha'1, rfl⟩ :=
    h.isPair_decomp hβ hx h1 h3 n1x.symm n3x.symm n13 hm
  have hs1 := vtype_eq_false_of_adj h1 hβ
  have hs3 := vtype_eq_false_of_adj h3 hβ
  have hab := h.elemAbelian_Vv_B hβ
  have haV : a ∈ Vv V β := Vv_le_Vv_of_adj h1.symm hs1 ha
  have ha'V : a' ∈ Vv V β := Vv_le_Vv_of_adj h3.symm hs3 ha'
  have hZV : Zv z β ≤ Vv V β := (h.Zv_le_Vv h1.symm hs1).trans (Vv_le_Vv_of_adj h1.symm hs1)
  have hcomm : ∀ {p q : D}, p ∈ Vv V β → q ∈ Vv V β → p * q = q * p := fun hp hq =>
    isElemAbelian_comm hab hp hq
  let k : ↥(A ⊔ B) := ⟨g, stab_le x hgx⟩
  have hkx : k • x = x := smul_eq_of_mem_stab hgx
  have hkβ : k • β = β := smul_eq_of_mem_stab hgβ
  have hadj : ∀ w, (graph (A ⊔ B) A B).Adj β w → (graph (A ⊔ B) A B).Adj β (k • w) := fun w hw => by
    have := (smul_adj k).mpr hw
    rwa [hkβ] at this
  have hne_x : ∀ w, w ≠ x → k • w ≠ x := fun w hw e => hw (smul_left_cancel k (e.trans hkx.symm))
  rcases h.eq_or_eq_of_adj h1 h3 hx (hadj s₁ h1) n13 n1x n3x with e | e | e
  ·
    have hg1 : g ∈ stab s₁ := mem_stab_of_smul_eq e
    have hgQ : g ∈ ballStab 1 β := h.mem_ballStab_one_of_fix_two' h1 hx n1x hgβ hg1 hgx
    have hg3 : g ∈ stab s₃ := ballStab_le_stab_of_dist_le (n := 1)
      (dist_eq_one_iff_adj.mpr h3).le hgQ
    have hiff : g ∈ ballStab 1 s₁ ↔ g ∈ ballStab 1 s₃ := by
      constructor
      · intro hq
        have : g ∈ ballStab 1 s₁ ⊓ ballStab 1 β := ⟨hq, hgQ⟩
        rw [← e3] at this
        exact this.1
      · intro hq
        have : g ∈ ballStab 1 s₃ ⊓ ballStab 1 β := ⟨hq, hgQ⟩
        rw [e3] at this
        exact this.1
    obtain ⟨ζ₁, hζ₁, hg₁, hζ₁1⟩ := h.conj_factor hs1 h1.symm hg1 hgβ ha ha1
    obtain ⟨ζ₃, hζ₃, hg₃, hζ₃1⟩ := h.conj_factor hs3 h3.symm hg3 hgβ ha' ha'1
    have e0 : g * (a * a') * g⁻¹ = (ζ₁ * a) * (ζ₃ * a') := by
      rw [← hg₁, ← hg₃]
      group
    rw [e0]
    by_cases hζ : ζ₁ = 1
    · have : ζ₃ = 1 := hζ₃1.mpr (hiff.mp (hζ₁1.mp hζ))
      rw [hζ, this]
      group
    · have hζ3 : ζ₃ ≠ 1 := fun e' => hζ (hζ₁1.mpr (hiff.mpr (hζ₃1.mp e')))
      have hzz : ζ₁ = ζ₃ := h.eq_of_mem_Zv hβ hζ₁ hζ₃ hζ hζ3
      have hsq : ζ₁ * ζ₁ = 1 := h.mul_self_eq_one_of_mem_Zv hβ hζ₁
      have hc : a * ζ₃ = ζ₃ * a := hcomm haV (hZV hζ₃)
      rw [← hzz] at hc ⊢
      calc ζ₁ * a * (ζ₁ * a') = ζ₁ * (a * ζ₁) * a' := by group
        _ = ζ₁ * (ζ₁ * a) * a' := by rw [hc]
        _ = (ζ₁ * ζ₁) * (a * a') := by group
        _ = a * a' := by rw [hsq]; group
  ·
    have hg3' : k • s₃ = s₁ := by
      rcases h.eq_or_eq_of_adj h1 h3 hx (hadj s₃ h3) n13 n1x n3x with e' | e' | e'
      · exact e'
      · exact absurd (smul_left_cancel k (e'.trans e.symm)).symm n13
      · exact absurd e' (hne_x s₃ n3x)
    have hga : g * a * g⁻¹ ∈ Vv V s₃ := by
      have : g * a * g⁻¹ ∈ Vv V (k • s₁) := by
        rw [h.Vv_smul' k s₁]
        exact mul_mem_conjSub ha
      rwa [e] at this
    have hga' : g * a' * g⁻¹ ∈ Vv V s₁ := by
      have : g * a' * g⁻¹ ∈ Vv V (k • s₃) := by
        rw [h.Vv_smul' k s₃]
        exact mul_mem_conjSub ha'
      rwa [hg3'] at this
    have hga1 : g * a * g⁻¹ ∉ Zv z β := fun hmem => ha1 ((h.conj_mem_Zv_iff hkβ).mp hmem)
    have hga'1 : g * a' * g⁻¹ ∉ Zv z β := fun hmem => ha'1 ((h.conj_mem_Zv_iff hkβ).mp hmem)
    have hζ₁ : (g * a * g⁻¹) * a'⁻¹ ∈ Zv z β := h.mul_inv_mem_Zv_of_Vv hs3 h3.symm ha' ha'1 hga hga1
    have hζ₂ : (g * a' * g⁻¹) * a⁻¹ ∈ Zv z β := h.mul_inv_mem_Zv_of_Vv hs1 h1.symm ha ha1 hga' hga'1
    set ζ₁ := (g * a * g⁻¹) * a'⁻¹ with hζ₁def
    set ζ₂ := (g * a' * g⁻¹) * a⁻¹ with hζ₂def
    have eg1 : g * a * g⁻¹ = ζ₁ * a' := by rw [hζ₁def]; group
    have eg2 : g * a' * g⁻¹ = ζ₂ * a := by rw [hζ₂def]; group
    have hsqQ : g * g ∈ ballStab 1 s₁ := by
      have h1' : g * g ∈ ballStab 1 β := h.sq_mem_ballStab_one_of_adj hx hgβ hgx
      have h2' : g * g ∈ ballStab 1 x := h.sq_mem_ballStab_one_of_adj hx.symm hgx hgβ
      have : g * g ∈ ballStab 1 x ⊓ ballStab 1 β := ⟨h2', h1'⟩
      rw [ex] at this
      exact this.1
    have hc2 := h.ballStab_one_le_centralizer hs1 hsqQ ha
    have hg1fix : g * ζ₁ * g⁻¹ = ζ₁ := h.conj_eq_of_mem_stab_Zv hβ hgβ hζ₁
    have hprod : ζ₁ * ζ₂ = 1 := by
      have e4 : (g * g) * a * (g * g)⁻¹ = ζ₁ * (ζ₂ * a) := by
        calc (g * g) * a * (g * g)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by group
          _ = g * (ζ₁ * a') * g⁻¹ := by rw [eg1]
          _ = (g * ζ₁ * g⁻¹) * (g * a' * g⁻¹) := by group
          _ = ζ₁ * (ζ₂ * a) := by rw [hg1fix, eg2]
      rw [hc2] at e4
      have : (ζ₁ * ζ₂) * a = 1 * a := by
        calc (ζ₁ * ζ₂) * a = ζ₁ * (ζ₂ * a) := by group
          _ = a := e4.symm
          _ = 1 * a := by group
      exact mul_right_cancel this
    have hc3 : a' * ζ₂ = ζ₂ * a' := hcomm ha'V (hZV hζ₂)
    have hc4 : a' * a = a * a' := hcomm ha'V haV
    have e0 : g * (a * a') * g⁻¹ = (ζ₁ * a') * (ζ₂ * a) := by
      rw [← eg1, ← eg2]
      group
    rw [e0]
    calc ζ₁ * a' * (ζ₂ * a) = ζ₁ * (a' * ζ₂) * a := by group
      _ = ζ₁ * (ζ₂ * a') * a := by rw [hc3]
      _ = (ζ₁ * ζ₂) * (a' * a) := by group
      _ = a * a' := by rw [hprod, hc4]; group
  · exact absurd e (hne_x s₁ n1x)

theorem not_inf_le_of_noACentral (hA : NoACentral A B) {s₁ β s₃ : CosetGeom (A ⊔ B) A B}
    (hβ : vtype β = true) (h1 : (graph (A ⊔ B) A B).Adj s₁ β)
    (h3 : (graph (A ⊔ B) A B).Adj β s₃) (n13 : s₁ ≠ s₃) :
    ¬ ballStab 1 s₁ ⊓ ballStab 1 β ≤ ballStab 1 s₃ := by
  intro hle
  obtain ⟨x, hx, hxs₁, hxs₃⟩ := h.exists_third (w := β) n13
  obtain ⟨e3, ex⟩ := h.inf_kernels_eq hβ h1.symm h3 hx n13 (Ne.symm hxs₁) (Ne.symm hxs₃) hle
  have hs1 := vtype_eq_false_of_adj h1.symm hβ
  have hs3 := vtype_eq_false_of_adj h3 hβ
  have hx0 := vtype_eq_false_of_adj hx hβ
  obtain ⟨m, hm⟩ := h.exists_isPair hβ hx
  have hmV : m ∈ Vv V β := isPair_mem_Vv hβ hm
  obtain ⟨n, hn⟩ : ∃ n, critDist (A ⊔ B) A B V = n + 1 :=
    ⟨critDist (A ⊔ B) A B V - 1, by have := h.three_le_critDist; omega⟩
  have hn2 : 2 ≤ n := by have := h.three_le_critDist; omega
  have hmx : m ∈ stab x := h.Vv_le_stab_B hn hβ (by
    rw [dist_eq_one_iff_adj.mpr hx]; omega) hmV
  have hmβ : m ∈ stab β := h.Vv_le_stab_B hn hβ (by rw [CosetGeom.dist_self]; omega) hmV
  have hfix := fun {g : D} (hgx : g ∈ stab x) (hgβ : g ∈ stab β) =>
    h.pair_conj_eq hβ h1.symm h3 hx n13 (Ne.symm hxs₁) (Ne.symm hxs₃) e3 ex hm hgx hgβ
  have hmc : ∀ t ∈ stab x ⊓ stab β, t * m = m * t := fun t ht =>
    mul_inv_eq_iff_eq_mul.mp (hfix ht.1 ht.2)
  have hm2 : m ^ 2 = 1 := isElemAbelian_pow_eq_one (h.elemAbelian_Vv_B hβ) hmV
  have hcen := h.centralizes_of_noACentral hA hx.symm hx0 ⟨hmx, hmβ⟩ hmc hm2
  obtain ⟨k, hkβ, hks₃, hkx⟩ := h.exists_swap_B h3 hs3 hx h1.symm (Ne.symm hxs₃) n13.symm hxs₁
  have hkβ' : k • β = β := smul_eq_of_mem_stab hkβ
  have hpair : IsPair z V β s₁ m := by
    have := h.isPair_conj k hm
    rw [hkβ', hkx, hcen (k : D) hkβ] at this
    exact this
  exact h.isPair_not_both hβ h1.symm h3 hx n13 (Ne.symm hxs₁) (Ne.symm hxs₃) hm hpair

theorem hF_of_noACentral (hA : NoACentral A B) :
    ∀ s₁ s₂ s₃ : CosetGeom (A ⊔ B) A B, vtype s₂ = true → (graph (A ⊔ B) A B).Adj s₁ s₂ →
      (graph (A ⊔ B) A B).Adj s₂ s₃ → s₁ ≠ s₃ →
        ¬ ballStab 1 s₁ ⊓ ballStab 1 s₂ ≤ ballStab 1 s₃ :=
  fun _ _ _ hs h12 h23 n13 => h.not_inf_le_of_noACentral hA hs h12 h23 n13

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
