module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7ModTransfer
import CFSG.LocalAnalysis.StandardType.FS81.S7NormalizerW

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Pointwise commutatorElement

private theorem conj_eq_of_central_zpowers {G : Type*} [Group G] {t₀ h : G}
    (hcomm : h * t₀ = t₀ * h) {t : G} (ht : t ∈ Subgroup.zpowers t₀) :
    h * t * h⁻¹ = t := by
  have hle : Subgroup.zpowers t₀ ≤ Subgroup.centralizer ({h} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hcomm
  have hht : h * t = t * h := Subgroup.mem_centralizer_iff.mp (hle ht) h (by simp)
  rw [hht]
  group

private theorem commutator_mem_of_normalizes {G : Type*} [Group G] {U H : Subgroup G}
    (hUn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U) {u : G} (hu : u ∈ U) {s : G} (hs : s ∈ H) :
    u * s * u⁻¹ * s⁻¹ ∈ U := by
  have h : s * u⁻¹ * s⁻¹ ∈ U := hUn s hs u⁻¹ (U.inv_mem hu)
  have heq : u * s * u⁻¹ * s⁻¹ = u * (s * u⁻¹ * s⁻¹) := by group
  rw [heq]
  exact U.mul_mem hu h

theorem mem_sup_of_trivial_on_W {G : Type} [Group G] [Finite G] {H U L P J D : Subgroup G}
    [(U.subgroupOf H).Normal] {t₀ σ b : G} (hUH : U ≤ H) (hU : IsPGroup 2 U) (hLH : L ≤ H)
    (hLU : ∀ x ∈ L, x ∈ U → x = 1) (ht₀H : ∀ h ∈ H, h * t₀ = t₀ * h)
    (hlev : E7LeviData L σ b P J D) (hmod : E7ModuleData U t₀ σ L P)
    (hmem : ∀ g ∈ H, g * b * g⁻¹ ∈ L ⊔ U → g ∈ L ⊔ U)
    {x : G} (hxH : x ∈ H) (hxσ : x * σ * x⁻¹ * σ⁻¹ ∈ U)
    (hxW : ∀ w ∈ modW U t₀ σ, x * w * x⁻¹ * w⁻¹ ∈ Subgroup.zpowers t₀) : x ∈ P ⊔ U := by
  have _ : IsPGroup 2 U := hU
  have hσH : σ ∈ H := hLH (hlev.P_le hlev.σ_mem)
  have hUn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh u hu
    have hmem : (⟨u, hUH hu⟩ : ↥H) ∈ U.subgroupOf H := by
      simpa [Subgroup.mem_subgroupOf] using hu
    have hconj := (inferInstance : (U.subgroupOf H).Normal).conj_mem
      ⟨u, hUH hu⟩ hmem ⟨h, hh⟩
    simpa [Subgroup.mem_subgroupOf] using hconj
  have hcommU : ⁅U, Subgroup.zpowers σ⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro u hu s hs
    have hsH : s ∈ H := Subgroup.zpowers_le.mpr hσH hs
    rw [commutatorElement_def]
    exact commutator_mem_of_normalizes hUn hu hsH
  have hWU : modW U t₀ σ ≤ U := by
    rw [modW]
    exact sup_le hcommU (Subgroup.zpowers_le.mpr hmod.t₀_mem)
  let S : Subgroup G :=
    { carrier := {y | y ∈ H ∧ y * σ * y⁻¹ * σ⁻¹ ∈ U ∧
          ∀ w ∈ modW U t₀ σ, y * w * y⁻¹ * w⁻¹ ∈ Subgroup.zpowers t₀}
      mul_mem' := by
        rintro y z ⟨hyH, hyσ, hyW⟩ ⟨hzH, hzσ, hzW⟩
        refine ⟨H.mul_mem hyH hzH, ?_, ?_⟩
        · change ⁅y * z, σ⁆ ∈ U
          rw [commutatorElement_mul_left_eq_conj_mul]
          exact U.mul_mem (hUn y hyH _ hzσ) hyσ
        · intro w hw
          change ⁅y * z, w⁆ ∈ Subgroup.zpowers t₀
          have hzw : ⁅z, w⁆ ∈ Subgroup.zpowers t₀ := hzW w hw
          rw [commutatorElement_mul_left_eq_conj_mul,
            conj_eq_of_central_zpowers (ht₀H y hyH) hzw]
          exact (Subgroup.zpowers t₀).mul_mem hzw (hyW w hw)
      one_mem' := by
        refine ⟨H.one_mem, ?_, ?_⟩
        · change ⁅(1 : G), σ⁆ ∈ U
          rw [commutatorElement_one_left]
          exact U.one_mem
        · intro w hw
          change ⁅(1 : G), w⁆ ∈ Subgroup.zpowers t₀
          rw [commutatorElement_one_left]
          exact (Subgroup.zpowers t₀).one_mem
      inv_mem' := by
        rintro y ⟨hyH, hyσ, hyW⟩
        refine ⟨H.inv_mem hyH, ?_, ?_⟩
        · change ⁅y⁻¹, σ⁆ ∈ U
          have hcomm : ⁅y⁻¹, σ⁆ = y⁻¹ * ⁅y, σ⁆⁻¹ * y := by
            rw [commutatorElement_inv_left, commutatorElement_inv]
          rw [hcomm]
          change y⁻¹ * (y * σ * y⁻¹ * σ⁻¹)⁻¹ * y ∈ U
          simpa only [inv_inv] using hUn y⁻¹ (H.inv_mem hyH) _ (U.inv_mem hyσ)
        · intro w hw
          change ⁅y⁻¹, w⁆ ∈ Subgroup.zpowers t₀
          have hyw : ⁅y, w⁆ ∈ Subgroup.zpowers t₀ := hyW w hw
          have hcomm : ⁅y⁻¹, w⁆ = y⁻¹ * ⁅y, w⁆⁻¹ * y := by
            rw [commutatorElement_inv_left, commutatorElement_inv]
          rw [hcomm]
          have hconj : y⁻¹ * ⁅y, w⁆⁻¹ * y = ⁅y, w⁆⁻¹ := by
            calc y⁻¹ * ⁅y, w⁆⁻¹ * y
                = y⁻¹ * ⁅y, w⁆⁻¹ * (y⁻¹)⁻¹ := by group
              _ = ⁅y, w⁆⁻¹ := conj_eq_of_central_zpowers (ht₀H y⁻¹ (H.inv_mem hyH))
                  (Subgroup.inv_mem _ hyw)
          rw [hconj]
          exact Subgroup.inv_mem _ hyw }
  have hxS : x ∈ S := ⟨hxH, hxσ, hxW⟩
  have hUS : U ≤ S := by
    intro u hu
    refine ⟨hUH hu, ?_, ?_⟩
    · change ⁅u, σ⁆ ∈ U
      rw [commutatorElement_def]
      exact commutator_mem_of_normalizes hUn hu hσH
    · intro w hw
      change ⁅u, w⁆ ∈ Subgroup.zpowers t₀
      rw [commutatorElement_def]
      exact hmod.U_comm u hu w (hWU hw)
  have hSH : S ≤ H := fun _ hy => hy.1
  have hPS : P ≤ S := by
    intro p hp
    refine ⟨hLH (hlev.P_le hp), ?_, ?_⟩
    · change ⁅p, σ⁆ ∈ U
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hlev.P_cent p hp)]
      exact U.one_mem
    · intro w hw
      change ⁅p, w⁆ ∈ Subgroup.zpowers t₀
      rw [commutatorElement_def]
      exact hmod.P_W p hp w hw
  have hDH : D ≤ H := fun d hd => hLH (hlev.J_le (hlev.D_le hd))
  have hDU : ∀ d ∈ D, d ∈ U → d = 1 :=
    fun d hd hdU => hLU d (hlev.J_le (hlev.D_le hd)) hdU
  have hDS : D ≤ Subgroup.normalizer (S : Set G) := by
    have hconj : ∀ e ∈ D, ∀ s ∈ S, e * s * e⁻¹ ∈ S := by
      intro e he s hs
      have heH : e ∈ H := hDH he
      have heσ : e * σ = σ * e := hlev.J_cent e (hlev.D_le he)
      have heW : e ∈ Subgroup.normalizer (modW U t₀ σ : Set G) :=
        mem_normalizer_commutator_sup hUn hmod.t₀_mem ht₀H hmod.U_comm hσH heH (by
          have he1 : e * σ * e⁻¹ * σ⁻¹ = 1 := by rw [heσ]; group
          rw [he1]
          exact U.one_mem)
      refine ⟨H.mul_mem (H.mul_mem heH hs.1) (H.inv_mem heH), ?_, ?_⟩
      · change ⁅e * s * e⁻¹, σ⁆ ∈ U
        have heσ' : e * σ * e⁻¹ = σ := by rw [heσ]; group
        have heq : e * ⁅s, σ⁆ * e⁻¹ = ⁅e * s * e⁻¹, σ⁆ := by
          rw [conjugate_commutatorElement, heσ']
        rw [← heq]
        exact hUn e heH _ hs.2.1
      · intro w hw
        change ⁅e * s * e⁻¹, w⁆ ∈ Subgroup.zpowers t₀
        have hw₁ : e⁻¹ * w * e ∈ modW U t₀ σ :=
          (Subgroup.mem_normalizer_iff''.mp heW w).mp hw
        have hst : ⁅s, e⁻¹ * w * e⁆ ∈ Subgroup.zpowers t₀ := hs.2.2 (e⁻¹ * w * e) hw₁
        have hw₂ : e * (e⁻¹ * w * e) * e⁻¹ = w := by group
        have heq : e * ⁅s, e⁻¹ * w * e⁆ * e⁻¹ = ⁅e * s * e⁻¹, w⁆ := by
          rw [conjugate_commutatorElement, hw₂]
        rw [← heq, conj_eq_of_central_zpowers (ht₀H e heH) hst]
        exact hst
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs; exact hconj d hd s hs
    · intro hs
      have h := hconj d⁻¹ (D.inv_mem hd) (d * s * d⁻¹) hs
      convert h using 1
      group
  have hbL : b ∈ L := hlev.J_le (hlev.D_le hlev.b_mem)
  have hC : ∀ y ∈ S, y * b * y⁻¹ * b⁻¹ ∈ U → y ∈ P ⊔ U := by
    intro y hy hyb
    have hyH : y ∈ H := hy.1
    have hybLU : y * b * y⁻¹ ∈ L ⊔ U := by
      have heq : y * b * y⁻¹ = (y * b * y⁻¹ * b⁻¹) * b := by group
      rw [heq, sup_comm]
      exact Subgroup.mul_mem_sup hyb hbL
    have hyLU : y ∈ L ⊔ U := hmem y hyH hybLU
    have hHnormU : H ≤ Subgroup.normalizer (U : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mp inferInstance
    have hLnormU : L ≤ Subgroup.normalizer (U : Set G) := hLH.trans hHnormU
    have hy_mul : y ∈ (L : Set G) * (U : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L U hLnormU]
      exact hyLU
    obtain ⟨l, hlL, u, huU, hlu⟩ := hy_mul
    have hl_eq : l = y * u⁻¹ := by rw [← hlu]; group
    have hlσ : l * σ * l⁻¹ * σ⁻¹ ∈ U := by
      have hc₂ : u⁻¹ * σ * u * σ⁻¹ ∈ U := by
        simpa using commutator_mem_of_normalizes hUn (U.inv_mem huU) hσH
      have heq : l * σ * l⁻¹ * σ⁻¹
          = y * (u⁻¹ * σ * u * σ⁻¹) * y⁻¹ * (y * σ * y⁻¹ * σ⁻¹) := by
        rw [hl_eq]; group
      rw [heq]
      exact U.mul_mem (hUn y hyH _ hc₂) hy.2.1
    have hlW : ∀ w ∈ modW U t₀ σ, l * w * l⁻¹ * w⁻¹ ∈ Subgroup.zpowers t₀ := by
      intro w hw
      have hc₁ : u⁻¹ * w * u * w⁻¹ ∈ Subgroup.zpowers t₀ := by
        simpa using hmod.U_comm u⁻¹ (U.inv_mem huU) w (hWU hw)
      have heq : l * w * l⁻¹ * w⁻¹
          = y * (u⁻¹ * w * u * w⁻¹) * y⁻¹ * (y * w * y⁻¹ * w⁻¹) := by
        rw [hl_eq]; group
      rw [heq, conj_eq_of_central_zpowers (ht₀H y hyH) hc₁]
      exact (Subgroup.zpowers t₀).mul_mem hc₁ (hy.2.2 w hw)
    have hlP : l ∈ P := hmod.L_W l hlL hlσ hlW
    rw [← hlu]
    exact Subgroup.mul_mem_sup hlP huU
  have hle : S ≤ P ⊔ U :=
    le_sup_of_selfNormalizing_l3Two_mod (S := S) hUS hSH hPS hlev.P_two hlev.σ_mem
      (fun s hs => hs.2.1) hlev.P_comm hDH hDU hDS hlev.D_norm hlev.D_SL hlev.b_mem
      hlev.b_ord hC
  exact hle hxS

end CFSG.StandardType.FrameRoute.FS81

end
