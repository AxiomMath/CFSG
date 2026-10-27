module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem2
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem conj_mem_ZS_of_fix {x z : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hz : z ∈ ch6ZS T L V) (hz1 : z ≠ 1)
    (hxz : x * z = z * x) {y : G} (hy : y ∈ ch6ZS T L V) : x * y * x⁻¹ ∈ ch6ZS T L V := by
  obtain ⟨v, hv, hle⟩ := h.toHyp611Nat.exists_line
  set D := h.data with hD
  obtain ⟨σ, hσ⟩ := D.exists_semilinear ⟨x, hxV⟩ hxL
  obtain ⟨c₀, hc₀⟩ := (h.toHyp611Nat.mem_ZS_iff_line hv hle ⟨z, hz.1⟩).mp hz
  obtain ⟨c, hc⟩ := (h.toHyp611Nat.mem_ZS_iff_line hv hle ⟨y, hy.1⟩).mp hy
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc₀
    apply hz1
    have := D.E.injective (show D.E ⟨z, hz.1⟩ = D.E 1 by
      rw [map_one]
      exact Multiplicative.toAdd.injective (by rw [hc₀]; rfl))
    exact congrArg Subtype.val this
  have hxz' : D.conj ⟨x, hxV⟩ (Multiplicative.toAdd (D.E ⟨z, hz.1⟩)) =
      Multiplicative.toAdd (D.E ⟨z, hz.1⟩) := by
    rw [D.conj_apply]
    congr 2
    apply Subtype.ext
    rw [conjAct_apply_coe]
    show x * z * x⁻¹ = z
    rw [hxz, mul_inv_cancel_right]
  have hyx : x * y * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV y).mp hy.1
  refine (h.toHyp611Nat.mem_ZS_iff_line hv hle ⟨_, hyx⟩).mpr ⟨σ (c / c₀) * c₀, ?_⟩
  have e1 : Multiplicative.toAdd (D.E ⟨y, hy.1⟩) =
      (c / c₀) • Multiplicative.toAdd (D.E ⟨z, hz.1⟩) := by
    rw [hc, hc₀, smul_smul, div_mul_cancel₀ c hc₀0]
  have e2 : (⟨x * y * x⁻¹, hyx⟩ : ↥V) = conjAct V ⟨x, hxV⟩ ⟨y, hy.1⟩ :=
    Subtype.ext (by rw [conjAct_apply_coe])
  rw [e2, ← D.conj_apply, e1, hσ, hxz', hc₀, smul_smul]

theorem mem_normalizer_ZS_of_fix {x z : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hz : z ∈ ch6ZS T L V) (hz1 : z ≠ 1)
    (hxz : x * z = z * x) : x ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h.conj_mem_ZS_of_fix hxV hxL hz hz1 hxz, fun hy => ?_⟩
  have hxz' : x⁻¹ * z = z * x⁻¹ := by
    calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * z) * x⁻¹ := by rw [hxz]
      _ = z * x⁻¹ := by group
  have := h.conj_mem_ZS_of_fix (Subgroup.inv_mem _ hxV) (Subgroup.inv_mem _ hxL) hz hz1 hxz' hy
  simpa [mul_assoc] using this

end Hyp6Sec2

theorem stmt6_2_9 (h331 : Stmt3_3_1) (h432 : Stmt4_3_2) (h512 : Stmt5_1_2) (h614 : Stmt6_1_4)
    (h615 : Stmt6_1_5) : Stmt6_2_9 := by
  intro G _ _ T M L V h H K
  set Z := quasithinOmegaOneCenter T with hZ
  have hZV : Z ≤ V := h.omega_le_V h331 h432 h512 h614 h615
  have hZ2 : Nat.card Z = 2 := h.card_omega h331 h432 h512 h614 h615
  have hZ1 : Z ≠ ⊥ := by
    intro h0
    have : Nat.card Z = 1 := by rw [h0, Subgroup.card_bot]
    omega
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ1
  have hZC : Z ≤ Subgroup.centralizer (T : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨⟨-, hy⟩, -⟩
    exact hy
  have hzZS : (z : G) ∈ ch6ZS T L V := ⟨hZV z.2, Subgroup.centralizer_le inf_le_left (hZC z.2)⟩
  have hz1' : (z : G) ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hNV := h.normalizer_V_le h432
  have hHN : H ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  have hVH : V ≤ H := fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    B2F.isElemAbelian_comm h.toHyp611.isElemAbelian (hZV hw) hv
  have hKH : K ≤ H :=
    conjClosure_le fun a ha v hv => H.mul_mem (H.mul_mem ha (hVH hv)) (H.inv_mem ha)
  have key : ∀ x ∈ H, x ∈ Subgroup.normalizer (V : Set G) →
      x ∈ Subgroup.normalizer (ch6ZS T L V : Set G) := by
    intro x hxH hxV
    refine h.mem_normalizer_ZS_of_fix hxV (h.normal (hNV hxV)) hzZS hz1' ?_
    exact (Subgroup.mem_centralizer_iff.mp hxH z z.2).symm
  have hZSV := h.normalizer_ZS_le h432
  refine ⟨h.toHyp611Nat.inf_eq_inf_normalizer hNV hZ1 hZV hHN, ?_,
    h.toHyp611Nat.inf_eq_inf_normalizer hNV hZ1 hZV (hKH.trans hHN), ?_⟩
  · exact le_antisymm (le_inf inf_le_left fun x hx => key x hx.1 hx.2)
      (inf_le_inf_left _ hZSV)
  · exact le_antisymm (le_inf inf_le_left fun x hx => key x (hKH hx.1) hx.2)
      (inf_le_inf_left _ hZSV)

end CFSG.Quasithin.H13
