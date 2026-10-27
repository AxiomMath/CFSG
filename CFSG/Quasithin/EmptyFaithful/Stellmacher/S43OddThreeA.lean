module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Three

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

omit [Finite G] in
theorem Yv_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Yv (g • δ) = conjSub (g : G) (Yv δ) := by
  apply le_antisymm
  · rw [le_conjSub_iff]
    refine le_iInf₂ fun l hl => ?_
    have hl' : g • l ∈ nbrs (g • δ) := (smul_adj g).mpr hl
    have h1 := conjSub_mono ((g : G)⁻¹) (Yv_le_Zv hl')
    rwa [Zv_smul, conjSub_conjSub_inv] at h1
  · refine le_iInf₂ fun l hl => ?_
    have hl' : g⁻¹ • l ∈ nbrs δ := by
      have : g⁻¹ • l ∈ nbrs (g⁻¹ • g • δ) := (smul_adj g⁻¹).mpr hl
      rwa [inv_smul_smul] at this
    have h1 := conjSub_mono (g : G) (Yv_le_Zv hl')
    rwa [← Zv_smul, smul_inv_smul] at h1

omit [Finite G] in
theorem Qst_smul (g : ↥(H ⊔ M)) (δ : Geo H M) : Qst (g • δ) = conjSub (g : G) (Qst δ) := by
  unfold Qst
  rw [conjSub_inf, Qv_smul, Yv_smul, conjSub_centralizer]

omit [Finite G] in
theorem conjSub_eq_self {g : G} {U : Subgroup G} (h : ∀ u ∈ U, g * u = u * g) :
    conjSub g U = U := by
  ext x
  rw [mem_conjSub]
  constructor
  · intro hx
    have h1 := h _ hx
    have e : x = g⁻¹ * x * g := by
      calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
        _ = (g⁻¹ * x * g) * g * g⁻¹ := by rw [h1]
        _ = g⁻¹ * x * g := by group
    rw [e]
    exact hx
  · intro hx
    have h1 := h x hx
    have e : g⁻¹ * x * g = x := by
      calc g⁻¹ * x * g = g⁻¹ * (x * g) := by group
        _ = g⁻¹ * (g * x) := by rw [h1]
        _ = x := by group
    rw [e]
    exact hx

omit [Finite G] in
theorem le_normalizer_of_conjSub_le {L N : Subgroup G} (h : ∀ l ∈ L, conjSub l N ≤ N) :
    L ≤ Subgroup.normalizer (N : Set G) :=
  fun l hl => Subgroup.mem_normalizer_iff.mpr fun n =>
    ⟨fun hn => h l hl (mul_mem_conjSub hn), fun hn => by
      have := h l⁻¹ (L.inv_mem hl) (mul_mem_conjSub (g := l⁻¹) hn)
      simpa [mul_assoc] using this⟩

omit [Finite G] in
theorem commutatorElement_mul_mul {a b u w : G} (hua : u * a = a * u) (hub : u * b = b * u)
    (huw : u * w = w * u) (hwa : w * a = a * w) (hwb : w * b = b * w) :
    ⁅u * a, w * b⁆ = ⁅a, b⁆ := by
  have h1 : u * (b * w) = (b * w) * u := by
    rw [← mul_assoc, hub, mul_assoc, huw, ← mul_assoc]
  have h2 : w * a⁻¹ = a⁻¹ * w := by
    calc w * a⁻¹ = a⁻¹ * (a * w) * a⁻¹ := by group
      _ = a⁻¹ * (w * a) * a⁻¹ := by rw [hwa]
      _ = a⁻¹ * w := by group
  rw [hua, hwb]
  simp only [commutatorElement_def]
  calc a * u * (b * w) * (a * u)⁻¹ * (b * w)⁻¹
      = a * (u * (b * w)) * u⁻¹ * a⁻¹ * (b * w)⁻¹ := by group
    _ = a * ((b * w) * u) * u⁻¹ * a⁻¹ * (b * w)⁻¹ := by rw [h1]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [h2]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem mem_normalizer_of_conjSub_eq {g : G} {K : Subgroup G} (h : conjSub g K = K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    rw [← h]
    exact mul_mem_conjSub hn
  · intro hn
    rw [← h, mem_conjSub] at hn
    simpa [mul_assoc] using hn

omit [Finite G] in
theorem conjSub_zpowers (g x : G) :
    conjSub g (Subgroup.zpowers x) = Subgroup.zpowers (g * x * g⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

theorem mem_Qv_of_mem_centralizer (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ : Geo H M} (hδ : vtype δ = true) {g : G} (hg : g ∈ stab δ)
    (hgc : g ∈ Subgroup.centralizer (Vn δ : Set G)) : g ∈ Qv δ := by
  by_contra hgQ
  have hmov : ∃ l ∈ nbrs δ, (⟨g, stab_le δ hg⟩ : ↥(H ⊔ M)) • l ≠ l := by
    by_contra hcon
    push Not at hcon
    apply hgQ
    rw [Qv_eq_iInf hA δ]
    exact Subgroup.mem_iInf.mpr fun w => Subgroup.mem_iInf.mpr fun hw =>
      ⟨hg, mem_stab_of_smul_eq (hcon w hw)⟩
  obtain ⟨l, hl, hl'⟩ := hmov
  have hU : conjSub g (Zv l) = Zv l := conjSub_eq_self fun u hu =>
    (Subgroup.mem_centralizer_iff.mp hgc u (Sit43.Zv_le_Vn_nbrs hl hu)).symm
  have hle := hs.le_Yv_of_normalizes hA h26 hδ hl le_rfl hg hl' hU
  have h1 := Subgroup.card_le_of_le hle
  rw [hs.card_Zv_false (Sit43.vtype_false_of_adj hδ hl), hs.card_Yv hA h26 hδ] at h1
  omega

theorem mem_normalizer_comm_sup (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ : Geo H M} (hδ : vtype δ = true) {x : G} (hx : x ∈ stab δ) :
    x ∈ Subgroup.normalizer ((⁅Vn δ, Subgroup.zpowers x⁆ ⊔ Yv δ : Subgroup G) : Set G) := by
  refine mem_normalizer_of_conjSub_eq ?_
  have hz : conjSub x (Subgroup.zpowers x) = Subgroup.zpowers x := conjSub_eq_self fun u hu => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact ((Commute.refl x).zpow_right k).eq
  rw [conjSub_sup, ← conjSub_commutator,
    F1.conjSub_eq_of_mem_normalizer (stab_le_normalizer_Vn δ hx),
    F1.conjSub_eq_of_mem_normalizer (hs.stab_le_normalizer_Yv hA h26 hδ hx), hz]

theorem Qv_le_normalizer_comm_sup (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {δ l : Geo H M} (hδ : vtype δ = true) (hl : l ∈ nbrs δ) {x : G} (hx : x ∈ stab δ)
    (hxC : x ∈ Subgroup.centralizer (Yv δ : Set G)) :
    Qv δ ≤ Subgroup.normalizer ((⁅Vn δ, Subgroup.zpowers x⁆ ⊔ Yv δ : Subgroup G) : Set G) := by
  set R : Subgroup G := ⁅Vn δ, Subgroup.zpowers x⁆ ⊔ Yv δ with hR
  have hYR : Yv δ ≤ R := le_sup_right
  have hKR : ⁅Vn δ, Subgroup.zpowers x⁆ ≤ R := le_sup_left
  have hRV : R ≤ Vn δ := sup_le (commutator_zpowers_le_self (stab_le_normalizer_Vn δ hx))
    ((Yv_le_Zv hl).trans (Sit43.Zv_le_Vn_nbrs hl))
  have hYn : stab δ ≤ Subgroup.normalizer (Yv δ : Set G) := hs.stab_le_normalizer_Yv hA h26 hδ
  have hst : Qst δ ≤ Subgroup.normalizer (R : Set G) := by
    refine Sit43.le_normalizer_of_conj_mem fun c hc r hr => ?_
    have h1 : ⁅r, c⁆ ∈ Yv δ := hs.comm_Vn_Qst hA h26 hδ hl ▸
      Subgroup.commutator_mem_commutator (hRV hr) hc
    have e : c * r * c⁻¹ = ⁅r, c⁆⁻¹ * r := by simp only [commutatorElement_def]; group
    rw [e]
    exact R.mul_mem (hYR (Subgroup.inv_mem _ h1)) hr
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := mem_normalizer_comm_sup hA h26 hs hδ hx
  refine le_normalizer_of_conjSub_le fun q hq => ?_
  have hqδ : q ∈ stab δ := pCoreOf_le 2 _ hq
  have hcst : q * x * q⁻¹ * x⁻¹ ∈ Qst δ := by
    have h1 := Subgroup.commutator_mem_commutator hq
      (show x ∈ stab δ ⊓ Subgroup.centralizer (Yv δ : Set G) from ⟨hx, hxC⟩)
    exact hs.commutator_Qv_centralizer_le hA h26 hδ h1
  set c := q * x * q⁻¹ * x⁻¹ with hc
  have hqx : q * x * q⁻¹ = c * x := by rw [hc]; group
  have hcR := hst hcst
  rw [hR, conjSub_sup, ← conjSub_commutator,
    F1.conjSub_eq_of_mem_normalizer (stab_le_normalizer_Vn δ hqδ),
    F1.conjSub_eq_of_mem_normalizer (hYn hqδ), conjSub_zpowers, hqx]
  refine sup_le (commutator_zpowers_le (Subgroup.mul_mem _ hcR hxR) fun v hv => ?_) le_sup_right
  have e : ⁅v, c * x⁆ = ⁅v, c⁆ * (c * ⁅v, x⁆ * c⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e]
  have h1 : ⁅v, c⁆ ∈ Yv δ := hs.comm_Vn_Qst hA h26 hδ hl ▸
    Subgroup.commutator_mem_commutator hv hcst
  exact R.mul_mem (hYR h1) ((Subgroup.mem_normalizer_iff.mp hcR _).mp
    (hKR (Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers x))))

theorem edge_le_normalizer_comm_sup (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {ρ δ : Geo H M} (hρ : vtype ρ = false) (hδ : δ ∈ nbrs ρ) {x : G} (hx : x ∈ stab ρ ⊓ stab δ)
    (hxC : x ∈ Subgroup.centralizer (Yv δ : Set G)) (hxQ : x ∉ Qv δ) :
    stab ρ ⊓ stab δ ≤
      Subgroup.normalizer ((⁅Vn δ, Subgroup.zpowers x⁆ ⊔ Yv δ : Subgroup G) : Set G) := by
  have hδv := Sit43.vtype_true_of_adj hρ hδ
  have hQ := Qv_le_normalizer_comm_sup hA h26 hs hδv (nbrs_symm hδ) hx.2 hxC
  have hxN := mem_normalizer_comm_sup hA h26 hs hδv hx.2
  intro g hg
  by_cases hgQ : g ∈ Qv δ
  · exact hQ hgQ
  · have h1 := inv_mul_mem_of_relIndex_two (Sit43.relIndex_Qv_edge hA hρ hδ) hx hg hxQ hgQ
    have e : g = x * (x⁻¹ * g) := by group
    rw [e]
    exact Subgroup.mul_mem _ hxN (hQ h1)

end Three

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
