module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem sec8_le_normalizer_of_conj {S H : Subgroup G}
    (h : ∀ s ∈ S, ∀ x ∈ H, s * x * s⁻¹ ∈ H) : S ≤ Subgroup.normalizer (H : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h s hs x, fun hx => ?_⟩
  have h' := h s⁻¹ (S.inv_mem hs) _ hx
  rwa [show s⁻¹ * (s * x * s⁻¹) * s⁻¹⁻¹ = x by group] at h'

theorem sec8_conjSubgroup_eq_of_mem_normalizer {H : Subgroup G} {ρ : G}
    (hρ : ρ ∈ Subgroup.normalizer (H : Set G)) : conjSubgroup ρ H = H := by
  ext x
  rw [mem_conjSubgroup]
  have h := (Subgroup.mem_normalizer_iff.mp hρ (ρ⁻¹ * x * ρ))
  rw [show ρ * (ρ⁻¹ * x * ρ) * ρ⁻¹ = x by group] at h
  exact h

theorem sec8_Wt_mem_normalizer {Q V : Subgroup G} {ρ : G}
    (hQ : ρ ∈ Subgroup.normalizer (Q : Set G)) (hV : ρ ∈ Subgroup.normalizer (V : Set G)) :
    ρ ∈ Subgroup.normalizer (Wt Q V : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (Q : Set G) →
      g ∈ Subgroup.normalizer (V : Set G) → ∀ x ∈ Wt Q V, g * x * g⁻¹ ∈ Wt Q V := by
    intro g hgQ hgV x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgQ x).mp hx.1,
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hv' : g⁻¹ * v * g ∈ V := by
      have h := (Subgroup.mem_normalizer_iff.mp hgV (g⁻¹ * v * g))
      rw [show g * (g⁻¹ * v * g) * g⁻¹ = v by group] at h
      exact h.mpr hv
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
    calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * v := by group
  exact sec8_le_normalizer_of_conj (S := Subgroup.zpowers ρ ⊓ (Subgroup.normalizer
    (Q : Set G) ⊓ Subgroup.normalizer (V : Set G))) (fun s hs => key s hs.2.1 hs.2.2)
    ⟨Subgroup.mem_zpowers ρ, hQ, hV⟩

variable [Finite G] {M Q Z B : Subgroup G}

theorem sec8_conj_mem_of_QB {X V W : Subgroup G} (hX : Ctx M Q Z X) (hXV : X ≤ V)
    (hVQ : V ≤ Q) (hZV : Z ≤ V) (hVW : V ≤ W) {g : G} (hg : g ∈ QB X)
    (hgV : g ∈ Subgroup.normalizer (V : Set G)) {y : G} (hy : y ∈ (Q ⊓ QB X) ⊔ V)
    (hyW : y ∈ W) : g * y * g⁻¹ ∈ W := by
  have hnorm : Q ⊓ QB X ≤ Subgroup.normalizer (V : Set G) := by
    refine sec8_le_normalizer_of_conj fun a ha v hv => ?_
    have hc : ⁅a, v⁆ ∈ Z := hX.hyp.toHyp79.comm_mem_V ha.1 (hVQ hv)
    rw [show a * v * a⁻¹ = ⁅a, v⁆ * v by rw [commutatorElement_def]; group]
    exact V.mul_mem (hZV hc) hv
  obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hy
  have h1 : ⁅g, a⁆ ∈ X := hX.comm_QB_le_B hg ha.2
  have h2 : g * v * g⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hgV v).mp hv
  rw [show g * (a * v) * g⁻¹ = ⁅g, a⁆ * (a * v) * (v⁻¹ * (g * v * g⁻¹)) by
    rw [commutatorElement_def]; group]
  exact W.mul_mem (W.mul_mem (hVW (hXV h1)) hyW) (hVW (V.mul_mem (V.inv_mem hv) h2))

theorem sec8InvStatement_holds : Sec8InvStatement := by
  intro G _ _ M Q Z B hc n t h r hA ρ hρ
  have ht : t ∈ LB M Q B := h.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hA.mem
  have hC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hRV : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    hc.Rt_normalizes_Vt ht
  have hBV : B ≤ Vt M (LB M Q B) B Z t := by
    have h1 := sec39_conjB_le_Vt (M := M) (L := LB M Q B) (B := B) (Z := Z) (t := t) M.one_mem
      (by rw [conjSubgroup_one]; exact ht)
    rwa [conjSubgroup_one] at h1
  have hCV : conjSubgroup r B ≤ Vt M (LB M Q B) B Z t := by
    intro x hx
    rw [mem_conjSubgroup] at hx
    have h1 := (Subgroup.mem_normalizer_iff.mp (hRV hA.mem) (r⁻¹ * x * r)).mp (hBV hx)
    rwa [show r * (r⁻¹ * x * r) * r⁻¹ = x by group] at h1
  have hV1V : Vt M (LB M Q B) B Z t ≤ Sec8V1 M Q Z B t r := le_inf le_sup_right le_sup_right
  have hV1Q : Sec8V1 M Q Z B t r ≤ Q := inf_le_left.trans (sup_le inf_le_left hVQ)
  have hQN : Q ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hc' : ⁅x, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx (hV1Q hy)
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact (Sec8V1 M Q Z B t r).mul_mem (hV1V (hZV hc')) hy
  have hBN : QB B ⊓ M ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    refine sec8_le_normalizer_of_conj fun g hg y hy => ?_
    have hgR : g ∈ Rt M (LB M Q B) t := le_Rt (LB M Q B) ht (le_sup_right (a := Q) hg)
    exact sec8_conj_mem_of_QB hc hBV hVQ hZV hV1V hg.1 (hRV hgR) hy.1 hy
  have hCN : QB (conjSubgroup r B) ⊓ M ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    refine sec8_le_normalizer_of_conj fun g hg y hy => ?_
    have hgR : g ∈ Rt M (LB M Q B) t := by
      rw [hA.gen]
      exact Subgroup.mem_sup_right (le_sup_right (a := Q) hg)
    exact sec8_conj_mem_of_QB hC hCV hVQ hZV hV1V hg.1 (hRV hgR) hy.2 hy
  have hRN : Rt M (LB M Q B) t ≤ Subgroup.normalizer (Sec8V1 M Q Z B t r : Set G) := by
    rw [hA.gen]
    exact sup_le (sup_le hQN hBN) (sup_le hQN hCN)
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  refine ⟨sec8_conjSubgroup_eq_of_mem_normalizer (hRN hρ), ?_⟩
  exact sec8_conjSubgroup_eq_of_mem_normalizer
    (sec8_Wt_mem_normalizer (hc.hyp.Q_normal.2 hρM) (hRN hρ))

theorem stroth83_of_inputs_inv (h34 : Stroth34Statement) (h51 : Stroth51Statement)
    (h53 : Stroth53Statement) (h54 : Stroth54Statement) (hPts : Sec5NatPointsSpStatement)
    (hA : Sec8AExistsStatement) (h82 : Stroth82Statement) (hC : Sec83UpperStatement)
    (hG : Sec83SevenStatement) : Stroth83Statement :=
  stroth83_of_inputs h34 h51 h53 h54 hPts hA sec8InvStatement_holds h82 hC hG

end CFSG.RankThree.GF2n.Stroth80