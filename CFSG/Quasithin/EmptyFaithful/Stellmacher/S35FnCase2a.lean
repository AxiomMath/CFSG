module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnChart
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnCfg

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.Fn

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

open S35.Std

omit [Finite G] in
theorem le_normalizer_of_conj {K N : Subgroup G} (h : ∀ x ∈ K, ∀ y ∈ N, x * y * x⁻¹ ∈ N) :
    K ≤ Subgroup.normalizer (N : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h x hx y hy, fun hy => ?_⟩
  have := h x⁻¹ (inv_mem hx) _ hy
  convert this using 1
  group

omit [Finite G] in
theorem comm_mem_of_mem_normalizer {N : Subgroup G} {b v : G} (hv : v ∈ N)
    (hb : b ∈ Subgroup.normalizer (N : Set G)) : ⁅v, b⁆ ∈ N := by
  rw [commutatorElement_def]
  have : b * v⁻¹ * b⁻¹ ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp hb v⁻¹).mp (inv_mem hv)
    simpa [mul_assoc] using this
  simpa [mul_assoc] using mul_mem hv this

theorem Qv_le_normalizer_Zl (hS : Sit H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) : Qv β ≤ Subgroup.normalizer (Zv l : Set G) := by
  refine le_normalizer_of_conj fun q hq z hz => ?_
  have hzV : z ∈ Vn β := Zv_le_Vn hl hz
  have h1 : ⁅z, q⁆ ∈ Zv β := by
    rw [← comm_Vn_Qv hS hβ]
    exact Subgroup.commutator_mem_commutator hzV hq
  have h2 : ⁅z, q⁆ ∈ Zv l := Zv_le_Zv_of_nbr hS hβ hl h1
  have : q * z * q⁻¹ = ⁅z, q⁆⁻¹ * z := by
    simp [commutatorElement_def, mul_assoc]
  rw [this]
  exact mul_mem (inv_mem h2) hz

theorem case2a (hS : Sit H M S) (hF : ChartFacts H M) (h8a : Claim8a H M) (h10 : Claim10 H M)
    (h14 : Claim14 H M) (h16a : Claim16a H M) {β α' : Geo H M} (hL : Lam β α') {l : Geo H M}
    (hl : l ∈ nbrs β) (hn : ¬ Vn α' ≤ Subgroup.normalizer (Zv l : Set G))
    (hW : Wl l ≤ stab α') : False := by
  have hβ : vtype β = false := hL.1.vδ
  have hβ' : vtype α' = false := hL.1.vδ'
  have hαβ : Vn α' ≤ stab β := (PD_Vn_le_stab hS hL.1).2
  obtain ⟨A, B, hA, hB, hAB, hcA, hcB, -⟩ := h8a β α' hL.1 (h16a β α' hL)
  have hZ2 := hS.cardZ5 α' hβ'
  have hZV : Zv α' ⊓ Vn β = ⊥ := inf_eq_bot_of_card_two hZ2 (h10.2 β α' hL).2
  have hZW : Zv α' ⊓ Wb β = ⊥ := inf_eq_bot_of_card_two hZ2 (h14 β α' hL)
  have hAQ : A ≤ Qv β := by
    intro a ha
    have haβ : a ∈ stab β := hαβ (hA ha)
    refine Vn_centralizer_le_Qv hS hβ a haβ fun v hv => ?_
    have h1 : ⁅v, a⁆ ∈ Zv α' := hcA (Subgroup.commutator_mem_commutator hv ha)
    have h2 : ⁅v, a⁆ ∈ Vn β := comm_mem_of_mem_normalizer hv (Vn_normal β haβ)
    have h3 : ⁅v, a⁆ ∈ Zv α' ⊓ Vn β := ⟨h1, h2⟩
    rw [hZV, Subgroup.mem_bot] at h3
    have : a * v * a⁻¹ * v⁻¹ = ⁅v, a⁆⁻¹ := by
      rw [commutatorElement_def]; group
    rw [this, h3, inv_one]
    exact one_mem _
  have hAN : A ≤ Subgroup.normalizer (Zv l : Set G) := hAQ.trans (Qv_le_normalizer_Zl hS hβ hl)
  have hBN : ¬ B ≤ Subgroup.normalizer (Zv l : Set G) := fun h =>
    hn (hAB ▸ sup_le hAN h)
  obtain ⟨x, hxB, hxN⟩ := Set.not_subset.mp hBN
  have hxβ : x ∈ stab β := hαβ (hB hxB)
  have hWl_le : Wl l ≤ Wb β := by
    rw [Wb_eq_iSup_Wl hS hβ]
    exact le_iSup₂ (f := fun (l : Geo H M) (_ : l ∈ nbrs β) => Wl l) l hl
  have hZnorm : Zv α' ≤ Subgroup.normalizer (Vn β : Set G) :=
    (Zα'_le_stab_of_dist hS hL (by rw [CosetGeom.dist_self]; exact Nat.zero_le _)).trans
      (Vn_normal β)
  have hBW : B ≤ Subgroup.normalizer (Wl l : Set G) := by
    refine le_normalizer_of_conj fun x hx w hw => ?_
    have hxβ : x ∈ stab β := hαβ (hB hx)
    have hwW : w ∈ Wb β ⊓ stab α' := ⟨hWl_le hw, hW hw⟩
    have h1 : ⁅w, x⁆ ∈ Zv α' ⊔ ⁅Vn β, B⁆ := hcB (Subgroup.commutator_mem_commutator hwW hx)
    have h2 : ⁅Vn β, B⁆ ≤ Vn β := by
      rw [Subgroup.commutator_le]
      intro v hv b hb
      exact comm_mem_of_mem_normalizer hv (Vn_normal β (hαβ (hB hb)))
    have h3 : ⁅w, x⁆ ∈ Vn β ⊔ Zv α' := by
      rw [sup_comm]
      exact sup_le_sup_left h2 (Zv α') h1
    have h4 : ⁅w, x⁆ ∈ Wb β := by
      have : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [this]
      refine mul_mem (hWl_le hw) ?_
      have := (Subgroup.mem_normalizer_iff.mp (Wb_normal β hxβ) w⁻¹).mp (inv_mem (hWl_le hw))
      simpa [mul_assoc] using this
    have h3' : ⁅w, x⁆ ∈ (↑(Vn β ⊔ Zv α') : Set G) := h3
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZnorm] at h3'
    obtain ⟨v, hv, z, hz, hvz⟩ := h3'
    have hzW : z ∈ Wb β := by
      have : z = v⁻¹ * ⁅w, x⁆ := by rw [← hvz]; simp
      rw [this]
      exact mul_mem (inv_mem (Vn_le_Wb_self hS hβ hv)) h4
    have hz1 : z = 1 := by
      have : z ∈ Zv α' ⊓ Wb β := ⟨hz, hzW⟩
      rw [hZW] at this
      exact Subgroup.mem_bot.mp this
    have h5 : ⁅w, x⁆ ∈ Vn β := by
      rw [← hvz, hz1]
      simpa using hv
    have h6 : ⁅w, x⁆ ∈ Wl l := Vn_le_Wl (mem_nbrs_symm.mp hl) h5
    have : x * w * x⁻¹ = ⁅w, x⁆⁻¹ * w := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact mul_mem (inv_mem h6) hw
  set P : Subgroup G := (stab β ⊓ stab l) ⊔ Subgroup.zpowers x with hP
  have hPβ : P ≤ stab β :=
    sup_le inf_le_left ((Subgroup.zpowers_le).mpr hxβ)
  have hPeq : P = stab β := by
    rcases hF.block β l P hβ hl le_sup_left hPβ with h | h
    · exact absurd (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))) hxN
    · exact h
  have hβW : stab β ≤ Subgroup.normalizer (Wl l : Set G) := by
    rw [← hPeq]
    exact sup_le (inf_le_right.trans (Wl_normal l))
      ((Subgroup.zpowers_le).mpr (hBW hxB))
  have hWQ : Wl l ≤ stab β ⊓ stab l := by
    refine le_inf ?_ ?_
    · exact (hWl_le.trans (Wb_le_Qv hS β)).trans (pCoreOf_le 2 _)
    · exact (hWl_le.trans (Wb_le_Ql hS hl)).trans (pCoreOf_le 2 _)
  have hbot : Wl l = ⊥ :=
    eq_bot_of_normalizes_both hS.glob.amalg
      (show (graph (H ⊔ M) H M).Adj β l from hl) hWQ hβW (Wl_normal l)
  have hVbot : Zv β = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hbot]
    exact (Zv_le_Vn_S5 hS hβ).trans (Vn_le_Wl (mem_nbrs_symm.mp hl))
  exact Zv_ne_bot hS.glob.amalg β hVbot

end S35.Fn

end F53.Stellmacher

end CFSG.Quasithin
