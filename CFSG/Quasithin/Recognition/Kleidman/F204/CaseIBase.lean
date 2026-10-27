module

public import CFSG.Quasithin.Recognition.Kleidman.F204.NatAThree
public import CFSG.Quasithin.MS93.S46I469Grp
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X
open CFSG.Quasithin.F7 CFSG.Quasithin.FA5
open CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G]

section Generic

omit [Finite G] in
private theorem elem_comm {V : Subgroup G} (hV : IsElemAbelian 2 V) {a b : G} (ha : a ∈ V)
    (hb : b ∈ V) : a * b = b * a := CFSG.Open.IsElemAbelian.comm hV ha hb

omit [Finite G] in
private theorem mul_six_comm {V : Subgroup G} (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {a b c d e f : G} (hb : b ∈ V) (hc : c ∈ V) (hd : d ∈ V) (he : e ∈ V) :
    a * b * (c * d) * (e * f) = a * c * e * (b * d * f) := by
  calc a * b * (c * d) * (e * f) = a * (b * c) * d * (e * f) := by group
    _ = a * (c * b) * d * (e * f) := by rw [hV b hb c hc]
    _ = a * c * (b * d * e) * f := by group
    _ = a * c * (e * (b * d)) * f := by rw [hV (b * d) (Subgroup.mul_mem _ hb hd) e he]
    _ = a * c * e * (b * d * f) := by group

theorem le_of_relIndex_le_two_of_norm {V K : Subgroup G} (hV : IsElemAbelian 2 V) {ρ : G}
    (hρV : ρ ∈ Subgroup.normalizer (V : Set G))
    (hρK : ρ ∈ Subgroup.normalizer (K : Set G))
    (hN : ∀ v ∈ V, v * (ρ * v * ρ⁻¹) * (ρ ^ 2 * v * (ρ ^ 2)⁻¹) = 1)
    (hidx : K.relIndex V ≤ 2) : V ≤ K := by
  have hρV' : ∀ v ∈ V, ρ * v * ρ⁻¹ ∈ V := fun v hv => (Subgroup.mem_normalizer_iff.mp hρV v).mp hv
  have hρK' : ∀ v ∈ K, ρ * v * ρ⁻¹ ∈ K := fun v hv => (Subgroup.mem_normalizer_iff.mp hρK v).mp hv
  have hρK'' : ∀ v, ρ * v * ρ⁻¹ ∈ K → v ∈ K := fun v hv => (Subgroup.mem_normalizer_iff.mp hρK v).mpr hv
  have hstep : ∀ v ∈ V, v⁻¹ * (ρ * v * ρ⁻¹) ∈ K := by
    intro v hv
    by_cases hvK : v ∈ K
    · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hvK) (hρK' v hvK)
    · have hne1 : K.relIndex V ≠ 1 := fun h1 => hvK (Subgroup.relIndex_eq_one.mp h1 hv)
      have hne0 : K.relIndex V ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 : (K.subgroupOf V).index = 2 := by
        change K.relIndex V = 2
        omega
      have hw : ρ * v * ρ⁻¹ ∉ K := fun h => hvK (hρK'' v h)
      have key := Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨v, hv⟩ : V)⁻¹)
        (b := ⟨ρ * v * ρ⁻¹, hρV' v hv⟩)
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, inv_mem_iff] at key
      exact key.mpr (iff_of_false hvK hw)
  intro v hv
  have hv1 : ρ * v * ρ⁻¹ ∈ V := hρV' v hv
  have e2 : ρ ^ 2 * v * (ρ ^ 2)⁻¹ = ρ * (ρ * v * ρ⁻¹) * ρ⁻¹ := by rw [pow_two]; group
  have hk1 := hstep v hv
  have hk2 := hstep _ hv1
  rw [← e2] at hk2
  have hk : v⁻¹ * (ρ ^ 2 * v * (ρ ^ 2)⁻¹) ∈ K := by
    have := Subgroup.mul_mem _ hk1 hk2
    rwa [show v⁻¹ * (ρ * v * ρ⁻¹) * ((ρ * v * ρ⁻¹)⁻¹ * (ρ ^ 2 * v * (ρ ^ 2)⁻¹)) =
      v⁻¹ * (ρ ^ 2 * v * (ρ ^ 2)⁻¹) by group] at this
  have hvv : v * v = 1 := by rw [← pow_two]; exact hV.2 v hv
  have hcomm : v * (ρ * v * ρ⁻¹) = (ρ * v * ρ⁻¹) * v := elem_comm hV hv hv1
  have e3 : v⁻¹ * (ρ ^ 2 * v * (ρ ^ 2)⁻¹) = ρ * v * ρ⁻¹ := by
    have h := hN v hv
    have e4 : ρ ^ 2 * v * (ρ ^ 2)⁻¹ = (v * (ρ * v * ρ⁻¹))⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [e4, hcomm]
    calc v⁻¹ * ((ρ * v * ρ⁻¹) * v)⁻¹ = v⁻¹ * v⁻¹ * (ρ * v * ρ⁻¹)⁻¹ := by group
      _ = (v * v)⁻¹ * (ρ * v * ρ⁻¹)⁻¹ := by group
      _ = (ρ * v * ρ⁻¹)⁻¹ := by rw [hvv, inv_one, one_mul]
      _ = ρ * v * ρ⁻¹ := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hV.2 _ hv1
  rw [e3] at hk
  exact hρK'' v hk

end Generic

variable {L1 L2 S D X : Subgroup G}

theorem sq_mem_Qv_of_mem_nbrs (F : Frame L1 L2 S D X) {μ l : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hμ : vtype μ = true) (hl : l ∈ nbrs μ) {q : G} (hq : q ∈ Qv l) : q * q ∈ Qv μ := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have hQ0 : Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q1 L1 L2 S := by
    unfold Qv; rw [stab_γ₀ h₁]
  have hQ1 : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  have hbase : ∀ q₀ ∈ Q1 L1 L2 S, q₀ * q₀ ∈ Q2 L1 L2 S := by
    obtain ⟨φ, hφk, T, hT4, hTin, -, -⟩ := exists_phi_Q1 F
    intro q₀ hq₀
    have hP : q₀ ∈ P2 L1 L2 S := Q1_mem_P2 F hq₀
    have h1 : φ ⟨q₀, hP⟩ * φ ⟨q₀, hP⟩ = 1 := alt5_klein_sq hT4 (hTin _ hq₀)
    rw [← map_mul] at h1
    exact (hφk _).mp h1
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge (show (graph _ _ _).Adj μ l from hl)
  · exfalso
    have := vtype_smul g (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))
    rw [hg0, hμ, vtype_γ₀] at this
    exact Bool.noConfusion this
  · rw [← hg0, Qv_smul, hQ0, mem_conjSub] at hq
    rw [← hg1, Qv_smul, hQ1, mem_conjSub]
    have e : (g : G)⁻¹ * (q * q) * g = ((g : G)⁻¹ * q * g) * ((g : G)⁻¹ * q * g) := by group
    rw [e]
    exact hbase _ hq

theorem relIndex_Qv_sup_Qv (F : Frame L1 L2 S D X) {μ l : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hμ : vtype μ = true) (hl : l ∈ nbrs μ) : (Qv μ).relIndex (Qv l ⊔ Qv μ) = 4 := by
  have h₁ : P1 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_left
  have h₂ : P2 L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S := le_sup_right
  have hQ0 : Qv (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q1 L1 L2 S := by
    unfold Qv; rw [stab_γ₀ h₁]
  have hQ1 : Qv (γ₁ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S)) = Q2 L1 L2 S := by
    unfold Qv; rw [stab_γ₁ h₂]
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge (show (graph _ _ _).Adj μ l from hl)
  · exfalso
    have := vtype_smul g (γ₀ (P1 L1 L2 S ⊔ P2 L1 L2 S) (P1 L1 L2 S) (P2 L1 L2 S))
    rw [hg0, hμ, vtype_γ₀] at this
    exact Bool.noConfusion this
  · rw [← hg0, ← hg1, Qv_smul, Qv_smul, hQ0, hQ1, ← conjSub_sup, Q1_sup_Q2 F, relIndex_conjSub]
    exact relIndex_Q2_S F

section T1

variable (F : Frame L1 L2 S D X) (hT1 : ConfigT1 L1 L2 S)
include F hT1

theorem not_stab_le_centralizer_Zv {x : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true) :
    ¬ stab x ≤ Subgroup.centralizer (Zv x : Set G) := by
  intro hle
  have hA := Amal.of_frame F
  apply hA.Zv_ne_bot x
  rw [← H1 F hT1 hx]
  refine le_antisymm (le_inf le_rfl fun z hz => ?_) inf_le_left
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact (Subgroup.mem_centralizer_iff.mp (hle hg) z hz).symm

theorem conj_mul_mem_Zv {μ l : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hμ : vtype μ = true)
    (hN : NatA μ) (hl : l ∈ nbrs μ) {u : G} (hu : u ∈ Zv μ) {q : G} (hq : q ∈ Qv l) :
    u⁻¹ * (q * u * q⁻¹) ∈ Zv l := by
  have hA := Amal.of_frame F
  have hlμ : μ ∈ nbrs l := (show (graph _ _ _).Adj μ l from hl).symm
  have hqμ : q ∈ stab μ := hA.Qv_le_stab_of_mem_nbrs hlμ hq
  have ha : q * u * q⁻¹ ∈ Zv μ :=
    (Subgroup.mem_normalizer_iff.mp (hA.stab_le_normalizer_Zv μ hqμ) u).mp hu
  by_cases hqQ : q ∈ Qv μ
  · have hc : u * q = q * u :=
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ hu).2 q hqQ).symm
    rw [show q * u * q⁻¹ = u by rw [← hc, mul_inv_cancel_right], inv_mul_cancel]
    exact one_mem _
  · obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (stab l)) ⟨q, hq⟩
    have hk' : q ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have heq := inf_centralizer_two_eq F hT1 hμ hN hl (not_stab_le_centralizer_Zv F hT1 hμ) hqμ
      (pCoreOf_le 2 _ hq) hk' hqQ
    rw [← heq]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) ha, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqq : q * q ∈ Qv μ := sq_mem_Qv_of_mem_nbrs F hμ hl hq
    have hc2 : u * (q * q) = (q * q) * u :=
      (Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv μ hu).2 _ hqq).symm
    have e2 : q * (q * u * q⁻¹) * q⁻¹ = u := by
      calc q * (q * u * q⁻¹) * q⁻¹ = (q * q) * u * (q * q)⁻¹ := by group
        _ = u := by rw [← hc2, mul_inv_cancel_right]
    have huu : u * u = 1 := by rw [← pow_two]; exact (hA.isElemAbelian_Zv μ).2 u hu
    have haa : (q * u * q⁻¹) * (q * u * q⁻¹) = 1 := by
      rw [← pow_two]; exact (hA.isElemAbelian_Zv μ).2 _ ha
    have hua : u * (q * u * q⁻¹) = (q * u * q⁻¹) * u := elem_comm (hA.isElemAbelian_Zv μ) hu ha
    have hconj : q * (u⁻¹ * (q * u * q⁻¹)) * q⁻¹ = u⁻¹ * (q * u * q⁻¹) := by
      have e1 : q * (u⁻¹ * (q * u * q⁻¹)) * q⁻¹ =
          (q * u * q⁻¹)⁻¹ * (q * (q * u * q⁻¹) * q⁻¹) := by group
      rw [e1, e2, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right huu, hua]
    calc u⁻¹ * (q * u * q⁻¹) * q = q * (q⁻¹ * (u⁻¹ * (q * u * q⁻¹)) * q) := by group
      _ = q * (u⁻¹ * (q * u * q⁻¹)) := by
        congr 1
        calc q⁻¹ * (u⁻¹ * (q * u * q⁻¹)) * q
            = q⁻¹ * (q * (u⁻¹ * (q * u * q⁻¹)) * q⁻¹) * q := by rw [hconj]
          _ = u⁻¹ * (q * u * q⁻¹) := by group

theorem conj_mul_mem_Zv_of_mem_Vn (hN : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → NatA x)
    (hb : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S)) {l : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hl : vtype l = false) {q : G} (hq : q ∈ Qv l) {u : G} (hu : u ∈ Vn l) :
    u⁻¹ * (q * u * q⁻¹) ∈ Zv l := by
  have hA := Amal.of_frame F
  have hV2 := hA.isElemAbelian_Vn hb l
  have hZV : Zv l ≤ Vn l := by
    obtain ⟨μ, hμ⟩ := exists_adj l
    have hμt : vtype μ = true := by
      have := vtype_ne_of_adj hμ
      rw [hl] at this
      cases h : vtype μ <;> simp_all
    have hlμ : l ∈ nbrs μ := hμ.symm
    rw [Zv_eq_inf_centralizer F hT1 hμt hlμ]
    exact inf_le_left.trans (hA.Zv_le_Vn hμ)
  have e : Vn l = ⨆ μ : {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S) // μ ∈ nbrs l}, Zv μ.1 := by
    unfold Vn; exact iSup_subtype'
  rw [e] at hu
  refine Subgroup.iSup_induction' (C := fun u _ => u⁻¹ * (q * u * q⁻¹) ∈ Zv l) _ ?_ ?_ ?_ hu
  · intro μ v hv
    have hμt : vtype μ.1 = true := by
      have := vtype_ne_of_adj (show (graph _ _ _).Adj l μ.1 from μ.2)
      rw [hl] at this
      cases h : vtype μ.1 <;> simp_all
    exact conj_mul_mem_Zv F hT1 hμt (hN _ hμt) (show l ∈ nbrs μ.1 from
      (show (graph _ _ _).Adj l μ.1 from μ.2).symm) hv hq
  · simp
  · intro x y hx hy hCx hCy
    rw [← e] at hx hy
    have hyC : y * (x⁻¹ * (q * x * q⁻¹)) = (x⁻¹ * (q * x * q⁻¹)) * y :=
      elem_comm hV2 hy (hZV hCx)
    have e1 : (x * y)⁻¹ * (q * (x * y) * q⁻¹) =
        (x⁻¹ * (q * x * q⁻¹)) * (y⁻¹ * (q * y * q⁻¹)) := by
      calc (x * y)⁻¹ * (q * (x * y) * q⁻¹)
          = y⁻¹ * ((x⁻¹ * (q * x * q⁻¹)) * y) * (y⁻¹ * (q * y * q⁻¹)) := by group
        _ = y⁻¹ * (y * (x⁻¹ * (q * x * q⁻¹))) * (y⁻¹ * (q * y * q⁻¹)) := by rw [hyC]
        _ = (x⁻¹ * (q * x * q⁻¹)) * (y⁻¹ * (q * y * q⁻¹)) := by group
    rw [e1]
    exact Subgroup.mul_mem _ hCx hCy

theorem Zv_eq_Zv_of_not_le {x y x1 y1 : Geo (P1 L1 L2 S) (P2 L1 L2 S)} (hx : vtype x = true)
    (hy : vtype y = true) (hNx : NatA x) (hNy : NatA y) (hx1 : x1 ∈ nbrs x) (hy1 : y1 ∈ nbrs y)
    (hxy : Zv x ≤ Qv y1) (hyx : Zv y ≤ Qv x1) (hnot : ¬ Zv x ≤ Qv y) : Zv x1 = Zv y1 := by
  have hA := Amal.of_frame F
  have hy1y : y ∈ nbrs y1 := (show (graph _ _ _).Adj y y1 from hy1).symm
  have hx1x : x ∈ nbrs x1 := (show (graph _ _ _).Adj x x1 from hx1).symm
  have hZxy : Zv x ≤ stab y := hxy.trans (hA.Qv_le_stab_of_mem_nbrs hy1y)
  have hZxy1 : Zv x ≤ stab y1 := hxy.trans (pCoreOf_le 2 _)
  have hZyx : Zv y ≤ stab x := hyx.trans (hA.Qv_le_stab_of_mem_nbrs hx1x)
  have hZyx1 : Zv y ≤ stab x1 := hyx.trans (pCoreOf_le 2 _)
  have hy1le : Zv y1 ≤ Zv y := by
    rw [Zv_eq_inf_centralizer F hT1 hy hy1]; exact inf_le_left
  have hcy : ∀ a ∈ Zv y, ∀ b ∈ Zv y, a * b = b * a := fun a ha b hb =>
    elem_comm (hA.isElemAbelian_Zv y) ha hb
  obtain ⟨z, hz, hzQ⟩ : ∃ z ∈ Zv x, z ∉ Qv y := by
    by_contra h; push Not at h; exact hnot fun z hz => h z hz
  have hzz : z * z = 1 := by rw [← pow_two]; exact (hA.isElemAbelian_Zv x).2 z hz
  have hz2 : z ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hzz
  have hCy := inf_centralizer_two_eq F hT1 hy hNy hy1 (not_stab_le_centralizer_Zv F hT1 hy)
    (hZxy hz) (hZxy1 hz) hz2 hzQ
  have hyQ : ¬ Zv y ≤ Qv x := by
    intro hle
    have h : Zv y ⊓ Subgroup.centralizer {z} = Zv y := by
      apply inf_eq_left.mpr
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hA.Zv_le_centerOf_Qv x hz).2 w (hle hw)
    rw [h] at hCy
    have h16 := hNy.1
    rw [hCy, card_Zv_nbr F hT1 hy hNy hy1] at h16
    omega
  obtain ⟨w, hw, hwQ⟩ : ∃ w ∈ Zv y, w ∉ Qv x := by
    by_contra h; push Not at h; exact hyQ fun w hw => h w hw
  have hw2 : w ^ 2 ^ 1 = 1 := by rw [pow_one]; exact (hA.isElemAbelian_Zv y).2 w hw
  have hCx := inf_centralizer_two_eq F hT1 hx hNx hx1 (not_stab_le_centralizer_Zv F hT1 hx)
    (hZyx hw) (hZyx1 hw) hw2 hwQ
  have hzn : z ∈ Subgroup.normalizer (Zv y : Set G) := hA.stab_le_normalizer_Zv y (hZxy hz)
  have hcz : ∀ u ∈ Zv y, ⁅z, u⁆ ∈ Zv y := fun u hu => by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hzn u).mp hu) (Subgroup.inv_mem _ hu)
  have hc : ∀ w₁ ∈ Zv y, ∀ w₂ ∈ Zv y, w₁ * ⁅z, w₂⁆ = ⁅z, w₂⁆ * w₁ := fun w₁ h₁ w₂ h₂ =>
    hcy _ h₁ _ (hcz w₂ h₂)
  set f := CFSG.Quasithin.MS93.S46.commHomOf (Zv y) z hc with hf
  have hker : f.ker = (Subgroup.centralizer {z}).subgroupOf (Zv y) := by
    ext u
    rw [MonoidHom.mem_ker, hf, CFSG.Quasithin.MS93.S46.commHomOf_apply,
      commutatorElement_eq_one_iff_mul_comm, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    exact eq_comm
  have hidx : (Zv y ⊓ Subgroup.centralizer {z}).relIndex (Zv y) = 4 := by
    have hc' := card_eq_relIndex_mul (V := Zv y) (Z := Subgroup.centralizer {z})
    have hcard : Nat.card (Zv y ⊓ Subgroup.centralizer {z} : Subgroup G) = 4 := by
      rw [hCy]; exact card_Zv_nbr F hT1 hy hNy hy1
    rw [hNy.1, hcard] at hc'
    omega
  have hrange : Nat.card f.range = 4 := by
    rw [← Subgroup.index_ker, hker, ← hidx, Subgroup.inf_relIndex_left]
    rfl
  have hrle : f.range ≤ Zv y1 := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    rw [hf, CFSG.Quasithin.MS93.S46.commHomOf_apply, ← hCy]
    refine Subgroup.mem_inf.mpr ⟨hcz u hu, ?_⟩
    show ⁅z, u⁆ ∈ Subgroup.centralizer {z}
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
    have hkk : ⁅z, u⁆ * ⁅z, u⁆ = 1 := by rw [← pow_two]; exact (hA.isElemAbelian_Zv y).2 _ (hcz u hu)
    have hki : ⁅z, u⁆⁻¹ = ⁅z, u⁆ := inv_eq_of_mul_eq_one_right hkk
    have e1 : z * ⁅z, u⁆ * z = ⁅z, u⁆⁻¹ := by
      rw [commutatorElement_def]
      calc z * (z * u * z⁻¹ * u⁻¹) * z = (z * z) * u * z⁻¹ * u⁻¹ * z := by group
        _ = u * z * u⁻¹ * z := by rw [hzz, one_mul, hzi]
        _ = u * z * u⁻¹ * z⁻¹ := by rw [hzi]
        _ = (z * u * z⁻¹ * u⁻¹)⁻¹ := by group
    rw [hki] at e1
    calc ⁅z, u⁆ * z = z * (z * ⁅z, u⁆ * z) := by
          rw [← mul_assoc, ← mul_assoc, hzz, one_mul]
      _ = z * ⁅z, u⁆ := by rw [e1]
  have hreq : f.range = Zv y1 :=
    Subgroup.eq_of_le_of_card_ge hrle (by rw [hrange, card_Zv_nbr F hT1 hy hNy hy1])
  have hrx : f.range ≤ Zv x := by
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    rw [hf, CFSG.Quasithin.MS93.S46.commHomOf_apply, commutatorElement_def]
    have hun : u ∈ Subgroup.normalizer (Zv x : Set G) := hA.stab_le_normalizer_Zv x (hZyx hu)
    have h1 : u * z⁻¹ * u⁻¹ ∈ Zv x :=
      (Subgroup.mem_normalizer_iff.mp hun z⁻¹).mp (Subgroup.inv_mem _ hz)
    rw [show z * u * z⁻¹ * u⁻¹ = z * (u * z⁻¹ * u⁻¹) by group]
    exact Subgroup.mul_mem _ hz h1
  have hle : Zv y1 ≤ Zv x1 := by
    rw [← hCx]
    intro v hv
    refine Subgroup.mem_inf.mpr ⟨hrx (hreq ▸ hv), ?_⟩
    show v ∈ Subgroup.centralizer {w}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcy v (hy1le hv) w hw
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_Zv_nbr F hT1 hx hNx hx1, card_Zv_nbr F hT1 hy hNy hy1])).symm

theorem norm_three_Vn (hN : ∀ x : Geo (P1 L1 L2 S) (P2 L1 L2 S), vtype x = true → NatA x)
    (hb : 3 ≤ bMin (P1 L1 L2 S) (P2 L1 L2 S)) {l : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (hl : vtype l = false) {ρ : G} (hρ : ρ ∈ stab l) (hρ3 : ρ ^ 3 = 1) (hρ1 : ρ ≠ 1) {v : G}
    (hv : v ∈ Vn l) : v * (ρ * v * ρ⁻¹) * (ρ ^ 2 * v * (ρ ^ 2)⁻¹) = 1 := by
  have hA := Amal.of_frame F
  have hV2 := hA.isElemAbelian_Vn hb l
  have hρV : ∀ u ∈ Vn l, ∀ n : ℕ, ρ ^ n * u * (ρ ^ n)⁻¹ ∈ Vn l := fun u hu n =>
    (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (stab_le_normalizer_Vn l hρ) n) u).mp hu
  have e : Vn l = ⨆ μ : {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S) // μ ∈ nbrs l}, Zv μ.1 := by
    unfold Vn; exact iSup_subtype'
  have hv' := hv
  rw [e] at hv'
  refine Subgroup.iSup_induction'
    (C := fun v _ => v * (ρ * v * ρ⁻¹) * (ρ ^ 2 * v * (ρ ^ 2)⁻¹) = 1) _ ?_ ?_ ?_ hv'
  · intro μ u hu
    have hμt : vtype μ.1 = true := by
      have := vtype_ne_of_adj (show (graph _ _ _).Adj l μ.1 from μ.2)
      rw [hl] at this
      cases h : vtype μ.1 <;> simp_all
    have hρμ : ρ ∈ stab μ.1 := three_mem_stab_nbr F hl μ.2 hρ hρ3
    have hρn : ∀ n : ℕ, ρ ^ n * u * (ρ ^ n)⁻¹ ∈ Zv μ.1 := fun n =>
      (Subgroup.mem_normalizer_iff.mp
        (Subgroup.pow_mem _ (hA.stab_le_normalizer_Zv μ.1 hρμ) n) u).mp hu
    have h1 : ρ * u * ρ⁻¹ ∈ Zv μ.1 := by simpa using hρn 1
    have h2 := hρn 2
    have hnZ : u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹) ∈ Zv μ.1 :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hu h1) h2
    have hnC : u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹) ∈ Subgroup.centralizer {ρ} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : ρ * (u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹)) * ρ⁻¹ =
          (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹) * (ρ ^ 3 * u * (ρ ^ 3)⁻¹) := by group
      rw [hρ3, one_mul, inv_one, mul_one] at e1
      have hcomm : u * ((ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹)) =
          ((ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹)) * u :=
        elem_comm (hA.isElemAbelian_Zv μ.1) hu (Subgroup.mul_mem _ h1 h2)
      have e2 : ρ * (u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹)) * ρ⁻¹ =
          u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹) := by
        rw [e1, mul_assoc u, hcomm]
      calc u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹) * ρ
          = ρ * (u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹)) * ρ⁻¹ * ρ := by rw [e2]
        _ = ρ * (u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹)) := by group
    have hbot := inf_centralizer_three_eq_bot F hT1 hμt (hN _ hμt) hρμ hρ3 hρ1
    have hmem : u * (ρ * u * ρ⁻¹) * (ρ ^ 2 * u * (ρ ^ 2)⁻¹) ∈
        Zv μ.1 ⊓ Subgroup.centralizer {ρ} := ⟨hnZ, hnC⟩
    rw [hbot] at hmem
    exact hmem
  · simp
  · intro x y hx hy hCx hCy
    rw [← e] at hx hy
    have hx1 : ρ * x * ρ⁻¹ ∈ Vn l := by simpa using hρV x hx 1
    have hy1 : ρ * y * ρ⁻¹ ∈ Vn l := by simpa using hρV y hy 1
    have hx2 := hρV x hx 2
    have hy2 := hρV y hy 2
    calc x * y * (ρ * (x * y) * ρ⁻¹) * (ρ ^ 2 * (x * y) * (ρ ^ 2)⁻¹)
        = x * y * ((ρ * x * ρ⁻¹) * (ρ * y * ρ⁻¹)) *
            ((ρ ^ 2 * x * (ρ ^ 2)⁻¹) * (ρ ^ 2 * y * (ρ ^ 2)⁻¹)) := by group
      _ = x * (ρ * x * ρ⁻¹) * (ρ ^ 2 * x * (ρ ^ 2)⁻¹) *
            (y * (ρ * y * ρ⁻¹) * (ρ ^ 2 * y * (ρ ^ 2)⁻¹)) :=
          mul_six_comm (fun a ha b hb => elem_comm hV2 ha hb) hy hx1 hy1 hx2
      _ = 1 := by rw [hCx, hCy, one_mul]

end T1

end CFSG.Quasithin.Kleidman.F204
