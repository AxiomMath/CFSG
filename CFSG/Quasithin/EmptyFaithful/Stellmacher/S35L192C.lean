module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L192Chart
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L192Fin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.L192

open S35.Std S35.II S35.Fin S35.Ch2
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem exists_transv (hS : Sit H M S) (hRk : RkZvEq H M) {β α' l : Geo H M}
    (hL : Lam β α') (hT : HasTransp α' β) (hl : l ∈ nbrs β) {A B : Subgroup G}
    (hA : A ≤ Qv β) (hBV : B ≤ Vn α') (hAB : A ⊔ B = Vn α')
    (hnl : ¬ Vn α' ≤ Subgroup.normalizer (Zv l : Set G)) :
    ∃ x ∈ B, x ∉ Subgroup.normalizer (Zv l : Set G) ∧
      secIdx (Subgroup.zpowers x) (Zv β) (Vn β) = 2 := by
  have hβ : vtype β = false := hL.1.vδ
  obtain ⟨c⟩ := exists_chart2 hS hβ
  have hVs : Vn α' ≤ stab β := (Std.PD_Vn_le_stab hS hL.1).2
  have hQN : Qv β ≤ Subgroup.normalizer (Zv l : Set G) := fun q hq =>
    stab_le_normalizer_Zv hS.glob.amalg l (Std.Qv_le_stab hS hl hq)
  obtain ⟨b0, hb0B, hb0N⟩ : ∃ b0 ∈ B, b0 ∉ Subgroup.normalizer (Zv l : Set G) := by
    by_contra h
    push Not at h
    apply hnl
    rw [← hAB]
    exact sup_le (hA.trans hQN) h
  obtain ⟨v, hvV, hvS, hvr⟩ := hT
  have hs : (c.θ ⟨v, hvS⟩).IsSwap := (secIdx_eq_two_iff c hRk hβ hvS).mp hvr
  have hAV : A ≤ Vn α' := hAB ▸ le_sup_left
  have hbar : c.bar (Vn α') = c.bar B := by
    rw [← hAB, bar_sup' c (hAV.trans hVs) (hBV.trans hVs), bar_eq_bot_of_le_Qv c hS hβ hA,
      bot_sup_eq]
  have hsB : c.θ ⟨v, hvS⟩ ∈ c.bar B := hbar ▸ c.mem_bar_of_mem hvV hvS
  obtain ⟨b1, hb1B, hb1θ⟩ := (c.mem_bar_iff).mp hsB
  have hb0s : b0 ∈ stab β := hVs (hBV hb0B)
  have hg0 : c.θ ⟨b0, hb0s⟩ ∈ c.bar (Vn α') := c.mem_bar_of_mem (hBV hb0B) hb0s
  have hg01 : c.θ ⟨b0, hb0s⟩ ≠ 1 := fun h =>
    hb0N (hQN (((c.ker_iff hS hβ ⟨b0, hb0s⟩).mp h)))
  have hsA : c.θ ⟨v, hvS⟩ ∈ c.bar (Vn α') := c.mem_bar_of_mem hvV hvS
  rcases swap_or_mul_swap (isElemAb_bar' c hS α') (isQuad_bar' c hS hL.1) hsA hs hg0
    hg01 with h | h
  · exact ⟨b0, hb0B, hb0N, (secIdx_eq_two_iff c hRk hβ hb0s).mpr h⟩
  · by_cases hb1N : (b1 : G) ∈ Subgroup.normalizer (Zv l : Set G)
    · refine ⟨b0 * b1, B.mul_mem hb0B hb1B, fun hx => hb0N ?_, ?_⟩
      · have := (Subgroup.normalizer (Zv l : Set G)).mul_mem hx
          ((Subgroup.normalizer (Zv l : Set G)).inv_mem hb1N)
        simpa using this
      · refine (secIdx_eq_two_iff c hRk hβ ((stab β).mul_mem hb0s b1.2)).mpr ?_
        have e : (⟨b0 * (b1 : G), (stab β).mul_mem hb0s b1.2⟩ : ↥(stab β)) = ⟨b0, hb0s⟩ * b1 :=
          rfl
        rw [e, map_mul, hb1θ]
        exact h
    · exact ⟨b1, hb1B, hb1N, (secIdx_eq_two_iff c hRk hβ b1.2).mpr (by rw [hb1θ]; exact hs)⟩

omit [Finite G] in
theorem comm_mem_Vn {β : Geo H M} {v a : G} (hv : v ∈ Vn β) (ha : a ∈ stab β) :
    v * a * v⁻¹ * a⁻¹ ∈ Vn β := by
  have h1 := S35.Ch.conj_mem_Vn ha ((Vn β).inv_mem hv)
  have e : v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by group
  rw [e]
  exact (Vn β).mul_mem hv h1

theorem claim8aC_II (hS : Sit H M S) (hRk : RkZvEq H M) (h8a : Claim8a H M)
    (h192 : Lem192 H M) (h16 : Claim16a H M) (hSym : Claim10Sym H M) : Claim8aC H M := by
  intro β α' m γ' hL hB l hl
  have hβ : vtype β = false := hL.1.vδ
  have hL' : Lam α' β := hSym β α' hL
  obtain ⟨A, B, hAV, hBV, hAB, hVA, hYB, -⟩ := h8a β α' hL.1 (h16 β α' hL)
  have hVs : Vn α' ≤ stab β := (Std.PD_Vn_le_stab hS hL.1).2
  have hZV : Zv α' ⊓ Vn β = ⊥ := Fn.inf_eq_bot_of_card_two (hS.cardZ5 α' hL.1.vδ') hL'.2
  have hAQ : A ≤ Qv β := by
    intro a ha
    refine Std.Vn_centralizer_le_Qv hS hβ a (hVs (hAV ha)) fun v hv => ?_
    have h1 : v * a * v⁻¹ * a⁻¹ ∈ Zv α' := hVA (Subgroup.commutator_mem_commutator hv ha)
    have h2 : v * a * v⁻¹ * a⁻¹ ∈ Vn β := comm_mem_Vn hv (hVs (hAV ha))
    have h3 : v * a * v⁻¹ * a⁻¹ = 1 := Subgroup.mem_bot.mp (hZV ▸ ⟨h1, h2⟩)
    have h4 : a * v * a⁻¹ * v⁻¹ = (v * a * v⁻¹ * a⁻¹)⁻¹ := by group
    rw [h4, h3, inv_one]
    exact (Zv β).one_mem
  obtain ⟨x, hxB, hxN, hxr⟩ := exists_transv hS hRk hL (h16 α' β hL') hl.1 hAQ hBV hAB hl.2
  refine ⟨x, hBV hxB, hxN, hxr, fun w hw => ?_⟩
  obtain ⟨-, -, h3⟩ := h192 β α' m γ' hL hB
  have hWW : Wl l ≤ Wb β := by
    rw [Std.Wb_eq_iSup_Wl hS hβ]
    exact le_iSup₂_of_le (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l hl.1 le_rfl
  have h1 : ⁅w, x⁆ ∈ ⁅Wb β ⊓ stab α', B⁆ :=
    Subgroup.commutator_mem_commutator ⟨hWW hw, h3 l hl hw⟩ hxB
  have h2 : ⁅Vn β, B⁆ ≤ Vn β := by
    rw [Subgroup.commutator_le]
    intro v hv b hb
    exact comm_mem_Vn hv (hVs (hBV hb))
  exact (sup_le_sup_left h2 (Zv α')) (hYB h1)

end S35.L192

end F53.Stellmacher

end CFSG.Quasithin
