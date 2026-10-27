module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.SevenCover
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Claim1Core

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher Equiv
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Claim6Spec (H M S : Subgroup G) : Prop :=
  ∀ {α β α' : Geo H M}, Ctx H M S α β α' → ∀ {μ : Geo H M}, μ ∈ nbrs α' → Vn β ≤ Qv μ →
    stab α' ⊓ stab μ ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ ⊔ Zv α' : Subgroup G) : Set G)

omit [Finite G] in
theorem mem_normalizer_sup' {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ x : G, x ∈ Subgroup.normalizer (A : Set G) → x ∈ Subgroup.normalizer (B : Set G) →
      ∀ h ∈ A ⊔ B, x * h * x⁻¹ ∈ A ⊔ B := by
    intro x hxA hxB h hh
    have hle : (A ⊔ B).map (MulAut.conj x).toMonoidHom ≤ A ⊔ B := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hxA a).mp ha
      · rintro _ ⟨a, ha, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hxB a).mp ha
    exact hle ⟨h, hh, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hA hB h, fun hh => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hA) (Subgroup.inv_mem _ hB) _ hh
  simpa [mul_assoc] using this

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem R_le : ⁅Vn β, Vn α'⁆ ≤ Vn β ⊓ Vn α' := by
  have h := hss114_d C.hA C.hb3 C.dist_beta
  exact commutator_le_inf_of_normalizes (h.1.trans (stab_le_normalizer_Vn α'))
    (h.2.1.trans (stab_le_normalizer_Vn β))

theorem R_le_Vn_beta : ⁅Vn β, Vn α'⁆ ≤ Vn β := C.R_le.trans inf_le_left

theorem R_le_Vn_alpha' : ⁅Vn β, Vn α'⁆ ≤ Vn α' := C.R_le.trans inf_le_right

theorem Vn_alpha'_le_centralizer_δ (P : CritPath α β α') :
    Vn α' ≤ Subgroup.centralizer (Vn P.δ : Set G) := by
  have hb := C.hb5
  have hd : dist α' P.δ = 2 := by
    have := P.dist_of_le (i := bMin H M - 2) (j := bMin H M) (by omega) le_rfl
    rw [P.p_b, CosetGeom.dist_comm] at this
    show dist α' (P.p (bMin H M - 2)) = 2
    omega
  exact C.Vn_le_centralizer_Vn (C.vtype_P_δ P) (by omega)

theorem isElemAbelian_RV (P : CritPath α β α') :
    IsElemAbelian 2 (⁅Vn β, Vn α'⁆ ⊔ Vn P.δ) := by
  have hR : IsElemAbelian 2 ⁅Vn β, Vn α'⁆ :=
    isElemAbelian_mono (isElemAbelian_Vn C.hA C.hb3 β) C.R_le_Vn_beta
  have hV := isElemAbelian_Vn C.hA C.hb3 P.δ
  have e : ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ = ⨆ i : Bool, cond i ⁅Vn β, Vn α'⁆ (Vn P.δ) := by
    rw [iSup_bool_eq]; rfl
  rw [e]
  refine isElemAbelian_iSup _ (fun i => by cases i <;> assumption) ?_
  have hc : ∀ x ∈ ⁅Vn β, Vn α'⁆, ∀ y ∈ Vn P.δ, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.mp (C.Vn_alpha'_le_centralizer_δ P (C.R_le_Vn_alpha' hx)))
      y hy).symm
  intro i j x hx y hy
  cases i <;> cases j
  · exact isElemAbelian_comm hV hx hy
  · exact (hc y hy x hx).symm
  · exact hc x hx y hy
  · exact isElemAbelian_comm hR hx hy

theorem Vn_beta_le_Qv_P_γ (P : CritPath α β α') : Vn β ≤ Qv P.γ :=
  C.Vn_le_Qv_of_dist C.vtype_beta (C.dist_beta_P_γ P).le

theorem Zv_alpha'_le_Vn_P_δ (P : CritPath α β α') : Zv α' ≤ Vn P.δ := by
  have hb := C.hb5
  have hγ : α' ∈ nbrs P.γ := P.γ_adj (by omega)
  have hδ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  exact (C.Zv_le_Zv_of_mem_nbrs (C.vtype_P_γ P) hγ).trans (Zv_le_Vn_of_mem_nbrs hδ)

theorem stab_le_normalizer_RV (h4 : Claim4Spec H M S) (hH8 : FactH8) (h6 : Claim6Spec H M S)
    (P : CritPath α β α') (hW : ¬ Wnn β ≤ stab P.γ) :
    stab P.δ ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ ⊔ Vn P.δ : Subgroup G) : Set G) := by
  have hb := C.hb5
  rw [← C.cover_eq h4 hH8 P hW]
  have hWδ : Wnn β ≤ stab P.δ := C.Wnn_le_stab_of_dist C.vtype_beta (C.dist_beta_P_δ P).le
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hQγ : Qv P.γ ≤ stab P.δ := Qv_le_stab_of_mem_nbrs C.hA (mem_nbrs_comm hγ)
  refine sup_le (fun w hw => mem_normalizer_sup' ?_ (stab_le_normalizer_Vn _ (hWδ hw)))
    (fun q hq => ?_)
  · refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact (Subgroup.mem_centralizer_iff.mp (C.Wnn_le_centralizer_Vn C.vtype_beta hw))
      r (C.R_le_Vn_beta hr)
  ·
    have hα' : α' ∈ nbrs P.γ := P.γ_adj (by omega)
    have hqα : q ∈ stab α' ⊓ stab P.γ :=
      ⟨Qv_le_stab_of_mem_nbrs C.hA hα' hq, pCoreOf_le 2 _ hq⟩
    have h1 := h6 C (mem_nbrs_comm hα') (C.Vn_beta_le_Qv_P_γ P) hqα
    have h2 := stab_le_normalizer_Vn _ (hQγ hq)
    have h3 := mem_normalizer_sup' h1 h2
    have e : ⁅Vn β, Vn α'⁆ ⊔ Zv α' ⊔ Vn P.δ = ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ := by
      rw [sup_assoc, sup_eq_right.mpr (C.Zv_alpha'_le_Vn_P_δ P)]
    rwa [e] at h3

theorem isSec_RV (h4 : Claim4Spec H M S) (hH8 : FactH8) (h6 : Claim6Spec H M S)
    (P : CritPath α β α') (hW : ¬ Wnn β ≤ stab P.γ) :
    IsSec (stab P.δ) (Vn P.δ) (⁅Vn β, Vn α'⁆ ⊔ Vn P.δ) where
  le := le_sup_right
  normN := C.stab_le_normalizer_RV h4 hH8 h6 P hW
  normL := stab_le_normalizer_Vn _
  comm := fun x hx y hy => by
    rw [isElemAbelian_comm (C.isElemAbelian_RV P) hx hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  sq := fun x hx => by
    rw [isElemAbelian_pow_eq_one (C.isElemAbelian_RV P) hx]
    exact one_mem _

theorem RV_le_stab (P : CritPath α β α') : ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ ≤ stab P.δ := by
  have hb := C.hb5
  refine sup_le (C.R_le_Vn_beta.trans (C.Vn_le_stab_of_dist C.vtype_beta ?_))
    ((C.Vn_le_Qv_self (C.vtype_P_δ P)).trans (pCoreOf_le 2 _))
  have := C.dist_beta_P_δ P
  omega

theorem comm_oTwoRes_R (h4 : Claim4Spec H M S) (hH8 : FactH8) (h6 : Claim6Spec H M S)
    (P : CritPath α β α') (hW : ¬ Wnn β ≤ stab P.γ) :
    ∀ l ∈ oTwoRes (stab P.δ), ∀ r ∈ ⁅Vn β, Vn α'⁆, l * r * l⁻¹ * r⁻¹ ∈ Vn P.δ := by
  have hb := C.hb5
  have hvδ := C.vtype_P_δ P
  have hsec := C.isSec_RV h4 hH8 h6 P hW
  have hγ : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hWδ : Wnn β ≤ stab P.δ := C.Wnn_le_stab_of_dist C.vtype_beta (C.dist_beta_P_δ P).le
  have hWQ : ¬ Wnn β ≤ Qv P.δ := fun h => hW (h.trans (Qv_le_stab_of_mem_nbrs C.hA hγ))
  have hXV : stab P.δ ≤ Subgroup.normalizer (Vn P.δ : Set G) := stab_le_normalizer_Vn _
  have hUV : ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ ≤ Subgroup.normalizer (Vn P.δ : Set G) :=
    (C.RV_le_stab P).trans hXV
  have hfix : ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ ≤ fixSecIn (Wnn β) (Vn P.δ) (⁅Vn β, Vn α'⁆ ⊔ Vn P.δ) := by
    refine sup_le (fun r hr => ?_) (fun v hv => ?_)
    · rw [mem_fixSecIn_iff hUV]
      refine ⟨Subgroup.mem_sup_left hr, fun w hw => ?_⟩
      have hc := (Subgroup.mem_centralizer_iff.mp (C.Wnn_le_centralizer_Vn C.vtype_beta hw))
        r (C.R_le_Vn_beta hr)
      rw [← hc]; simp
    · rw [mem_fixSecIn_iff hUV]
      refine ⟨Subgroup.mem_sup_right hv, fun w hw => ?_⟩
      exact (Vn P.δ).mul_mem ((Subgroup.mem_normalizer_iff.mp (hXV (hWδ hw)) v).mp hv)
        ((Vn P.δ).inv_mem hv)
  have hW' : ∀ w ∈ Wnn β, ∀ u ∈ ⁅Vn β, Vn α'⁆ ⊔ Vn P.δ, w * u * w⁻¹ * u⁻¹ ∈ Vn P.δ :=
    fun w hw u hu => ((mem_fixSecIn_iff hUV).mp (hfix hu)).2 w hw
  have hL := C.oTwoRes_le_cSecIn_of_normal hvδ hsec hWδ hWQ hW'
  intro l hl r hr
  exact ((mem_cSecIn_iff hXV).mp (hL hl)).2 r (Subgroup.mem_sup_left hr)

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
