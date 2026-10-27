module

public import CFSG.Quasithin.H13.L32A756b
public import CFSG.Quasithin.H13.L32A755i
public import CFSG.Quasithin.H13.L32A770a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit
open scoped commutatorElement

namespace Ctx753

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

@[expose] noncomputable def ΦX (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (X : Subgroup G) : Subgroup ↥(quasithinG2 (ZMod 2)) :=
  (X.subgroupOf (hz T V)).map (C.Φ E)

theorem mem_ΦX (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    {X : Subgroup G} (hXH : X ≤ hz T V) {a : ↥(quasithinG2 (ZMod 2))} :
    a ∈ C.ΦX E X ↔ ∃ u ∈ X, C.ΦG E u = a := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Subgroup.mem_subgroupOf.mp hu, C.ΦG_eq E u.2⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hXH hu⟩, Subgroup.mem_subgroupOf.mpr hu, (C.ΦG_eq E (hXH hu)).symm⟩

theorem ΦG_mem_sSubG (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e) {t : G}
    (ht : t ∈ T) : C.ΦG E t ∈ sSubG := by
  rw [C.ΦG_eq E (C.T_le ht)]
  exact C.Φ_mem_sSubG E (t := ⟨t, C.T_le ht⟩) ht

theorem ΦX_le_sSubG (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    {X : Subgroup G} (hXT : X ≤ T) : C.ΦX E X ≤ sSubG := by
  intro a ha
  obtain ⟨u, hu, rfl⟩ := (C.mem_ΦX E (hXT.trans C.T_le)).1 ha
  exact C.ΦG_mem_sSubG E (hXT hu)

theorem ΦX_elem (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    {X : Subgroup G} (hXH : X ≤ hz T V) (hX : IsElemAbelian 2 X) :
    (∀ a ∈ C.ΦX E X, a ^ 2 = 1) ∧ ∀ a ∈ C.ΦX E X, ∀ b ∈ C.ΦX E X, a * b = b * a := by
  refine ⟨fun a ha => ?_, fun a ha b hb => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := (C.mem_ΦX E hXH).1 ha
    have hu2 : u * u = 1 := by
      have := F7.isElemAbelian_pow_eq_one hX hu
      rwa [pow_two] at this
    rw [pow_two, ← C.ΦG_mul E (hXH hu) (hXH hu), hu2, C.ΦG_eq E (one_mem _)]
    exact (C.Φ E).map_one
  · obtain ⟨u, hu, rfl⟩ := (C.mem_ΦX E hXH).1 ha
    obtain ⟨v, hv, rfl⟩ := (C.mem_ΦX E hXH).1 hb
    rw [← C.ΦG_mul E (hXH hu) (hXH hv), ← C.ΦG_mul E (hXH hv) (hXH hu),
      F7.isElemAbelian_comm hX hu hv]

theorem card_ΦX (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    {X : Subgroup G} (hXH : X ≤ hz T V) :
    Nat.card (C.ΦX E X) = (X ⊓ pCoreOf 2 (hz T V)).relIndex X := by
  set f : ↥X →* ↥(quasithinG2 (ZMod 2)) := (C.Φ E).comp (Subgroup.inclusion hXH) with hf
  have hrange : f.range = C.ΦX E X := by
    ext a
    rw [C.mem_ΦX E hXH]
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, (C.ΦG_eq E (hXH u.2))⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, (C.ΦG_eq E (hXH hu)).symm⟩
  have hker : f.ker = (pCoreOf 2 (hz T V)).subgroupOf X := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact C.Φ_eq_one_iff E _
  rw [← hrange, ← Subgroup.index_ker, hker, ← Subgroup.relIndex, Subgroup.inf_relIndex_left]

theorem ΦG_fix_V (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e) {r v : G}
    (hr : r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hv : v ∈ V) :
    g2QAct (ZMod 2) (C.ΦG E r) (C.θG e v) = C.θG e v := by
  have hrT := pCoreOf_le_of_le C.hyp le_sup_right hr
  have hrH := C.T_le hrT
  have hVU := le_conjClosure V (hz T V)
  have hc := comm_mem_of_R1 C.hF98 hr hv
  rw [← C.θG_conj E hrH (hVU hv)]
  have e1 : r * v * r⁻¹ = (r * v * r⁻¹ * v⁻¹) * v := by group
  have hcU : r * v * r⁻¹ * v⁻¹ ∈ conjClosure V (hz T V) := hVU ((inf_le_left : fsuV1 T V ≤ V) hc)
  rw [e1, C.θG_mul e hcU (hVU hv), C.θG_eq e hcU]
  rw [(C.θ_eq_one_iff e _).2, one_mul]
  have hc' : modMk C.U_le_normalizer _ hcU = 1 := (C.modMk_eq_one_iff' hcU).2 hc
  rw [hc']
  exact Subgroup.one_mem _

theorem exists_K_θG (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e) {p q : ModQ}
    (hp : p ≠ 1) (hq : q ≠ 1) : ∃ k ∈ K, g2QAct (ZMod 2) (C.ΦG E k) p = q := by
  obtain ⟨g₁, hg₁, hg₁p⟩ := M755.exists_g2Derived_of_ne hp
  obtain ⟨g₂, hg₂, hg₂q⟩ := M755.exists_g2Derived_of_ne hq
  have hg : g₂ * g₁⁻¹ ∈ (K.subgroupOf (hz T V)).map (C.Φ E) := by
    rw [C.map_Φ_K E]
    exact mul_mem hg₂ (inv_mem hg₁)
  obtain ⟨k, hk, hke⟩ := hg
  refine ⟨k, Subgroup.mem_subgroupOf.mp hk, ?_⟩
  rw [C.ΦG_eq E k.2, hke, map_mul, MulAut.mul_apply, map_inv, ← hg₁p, MulAut.inv_apply_self,
    hg₂q]

theorem θG_eq_one_of_comm (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h13322 : Stmt13_3_2_two) (hMod : StmtL32NModule) (h13314 : A6.Stmt13_3_14)
    (h1222 : Stmt12_2_2) {u : G} (hu : u ∈ conjClosure V (hz T V))
    (hc : ∀ q ∈ pCoreOf 2 (hz T V), q * u = u * q) : C.θG e u = 1 := by
  by_contra hne
  have hF := C.hF98
  have hUeq : conjClosure V (hz T V) = fsuU T V := C.conjClosure_eq
  set Cq := conjClosure V (hz T V) ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) with hCq
  have hHC : hz T V ≤ Subgroup.normalizer (Cq : Set G) := by
    intro k hk
    rw [← conjSub_eq_self_iff, hCq, conjSub_inf, ← conjSub_centralizer,
      conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ hk),
      conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hk)]
  have huC : u ∈ Cq := ⟨hu, Subgroup.mem_centralizer_iff.mpr fun q hq => hc q hq⟩
  have hV1C : fsuV1 T V ≤ Cq := le_inf ((inf_le_left : fsuV1 T V ≤ V).trans
    (le_conjClosure V _)) fun z hz => Subgroup.mem_centralizer_iff.mpr fun q hq =>
      (Subgroup.mem_centralizer_iff.mp (pCoreOf_le 2 _ hq) z hz).symm
  have hdec : ∀ v ∈ conjClosure V (hz T V), ∃ c ∈ Cq, C.θG e (c⁻¹ * v) = 1 := by
    intro v hv
    by_cases hv1 : C.θG e v = 1
    · exact ⟨1, one_mem _, by rw [inv_one, one_mul]; exact hv1⟩
    · obtain ⟨k, hk, hkθ⟩ := C.exists_K_θG E hne hv1
      have hkH := C.le_hz hk
      refine ⟨k * u * k⁻¹, (Subgroup.mem_normalizer_iff.mp (hHC hkH) u).mp huC, ?_⟩
      have hcU : k * u * k⁻¹ ∈ conjClosure V (hz T V) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V _ hkH) u).mp hu
      rw [C.θG_mul e (inv_mem hcU) hv, C.θG_inv e hcU, C.θG_conj E hkH hu, hkθ, inv_mul_cancel]
  have hUK : ⁅conjClosure V (hz T V), K⁆ ≤ Cq := by
    rw [Subgroup.commutator_le]
    intro v hv k hk
    have hkH := C.le_hz hk
    obtain ⟨c, hcC, hcv⟩ := hdec v hv
    have hcU : c ∈ conjClosure V (hz T V) := hcC.1
    set u₀ := c⁻¹ * v with hu₀
    have hu₀U : u₀ ∈ conjClosure V (hz T V) := mul_mem (inv_mem hcU) hv
    have hvu : v = c * u₀ := by rw [hu₀]; group
    have hu₀k : u₀ * k * u₀⁻¹ * k⁻¹ ∈ fsuV1 T V := by
      have h1 : C.θG e (k * u₀ * k⁻¹) = C.θG e u₀ := by
        rw [C.θG_conj E hkH hu₀U, hcv, map_one]
      have h2 := C.mem_V1_of_θG E hkH hu₀U h1
      have hcomm : ∀ a ∈ conjClosure V (hz T V), ∀ b ∈ conjClosure V (hz T V), a * b = b * a :=
        fun a ha b hb => F7.isElemAbelian_comm hF.F911_3 ha hb
      have hku : k * u₀⁻¹ * k⁻¹ ∈ conjClosure V (hz T V) :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V _ hkH) _).mp (inv_mem hu₀U)
      have e1 : u₀ * k * u₀⁻¹ * k⁻¹ = (u₀⁻¹ * (k * u₀ * k⁻¹))⁻¹ := by
        rw [show u₀ * k * u₀⁻¹ * k⁻¹ = u₀ * (k * u₀⁻¹ * k⁻¹) by group,
          hcomm _ hu₀U _ hku]
        group
      rw [e1]
      exact inv_mem h2
    have hckC : c * k * c⁻¹ * k⁻¹ ∈ Cq := by
      have : k * c⁻¹ * k⁻¹ ∈ Cq := (Subgroup.mem_normalizer_iff.mp (hHC hkH) _).mp (inv_mem hcC)
      rw [show c * k * c⁻¹ * k⁻¹ = c * (k * c⁻¹ * k⁻¹) by group]
      exact mul_mem hcC this
    rw [commutatorElement_def, hvu, ← comm_mul_comm C.hyp hMod hkH (hUeq ▸ hcU) (hUeq ▸ hu₀U)]
    exact mul_mem hckC (hV1C hu₀k)
  have hUC : conjClosure V (hz T V) ≤ Cq := by
    have := C.comm_eq
    rw [← hUeq] at this
    rw [this]
    exact hUK
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 h13322 hMod h1222
  have h41 := lemma14_7_4_one C.hyp h13322 hMod h13314 hV2
  rw [show A6.g1 T V = hz T V from normalizer_eq_centralizer_of_card_eq_two hF.card_V₁] at h41
  have hb : ⁅V₂, pCoreOf 2 (hz T V)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw q hq
    have hwC : w ∈ Cq := hUC (le_conjClosure V _ (hV2.2.1 hw))
    rw [Subgroup.mem_bot, commutatorElement_def,
      ← Subgroup.mem_centralizer_iff.mp hwC.2 q hq, mul_inv_cancel_right, mul_inv_cancel]
  rw [h41] at hb
  have := hF.card_V₁
  rw [hb, Subgroup.card_bot] at this
  omega

end Ctx753

end CFSG.Quasithin.H13.L32A
