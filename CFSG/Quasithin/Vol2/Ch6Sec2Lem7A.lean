module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem commutator_mem_ZS_ch62 {s w : G} (hs : s ∈ ch6S T L V) (hw : w ∈ V) :
    s * w * s⁻¹ * w⁻¹ ∈ ch6ZS T L V := by
  have h1 : ⁅s, w⁆ ∈ ⁅ch6S T L V, V⁆ := Subgroup.commutator_mem_commutator hs hw
  rw [Subgroup.commutator_comm] at h1
  have h2 := h.toHyp611Nat.commutator_V_S_le h1
  rwa [commutatorElement_def] at h2

theorem exists_commutator_eq_ch62 {X : Subgroup G} (hXS : X ≤ ch6S T L V)
    (hX4 : (Subgroup.centralizer (V : Set G)).relIndex X = 4) {w : G} (hwV : w ∈ V)
    (hwZ : w ∉ ch6ZS T L V) {z : G} (hz : z ∈ ch6ZS T L V) :
    ∃ x ∈ X, x * w * x⁻¹ * w⁻¹ = z := by
  have hV := h.toHyp611.isElemAbelian
  let f : ↥X →* ↥(ch6ZS T L V) :=
    { toFun := fun x => ⟨(x : G) * w * (x : G)⁻¹ * w⁻¹, h.commutator_mem_ZS_ch62 (hXS x.2) hwV⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (x : G) * y * w * ((x : G) * y)⁻¹ * w⁻¹ =
          ((x : G) * w * (x : G)⁻¹ * w⁻¹) * ((y : G) * w * (y : G)⁻¹ * w⁻¹)
        have hcy := h.commutator_mem_ZS_ch62 (hXS y.2) hwV
        have hcx := h.commutator_mem_ZS_ch62 (hXS x.2) hwV
        have h1 : ((y : G) * w * (y : G)⁻¹ * w⁻¹) * (x : G) =
            (x : G) * ((y : G) * w * (y : G)⁻¹ * w⁻¹) :=
          Subgroup.mem_centralizer_iff.mp (hXS x.2).2 _ hcy
        have h2 := B2F.isElemAbelian_comm hV hcx.1 hcy.1
        calc (x : G) * y * w * ((x : G) * y)⁻¹ * w⁻¹ =
              (x : G) * ((y : G) * w * (y : G)⁻¹ * w⁻¹) * w * (x : G)⁻¹ * w⁻¹ := by group
          _ = ((y : G) * w * (y : G)⁻¹ * w⁻¹) * (x : G) * w * (x : G)⁻¹ * w⁻¹ := by rw [h1]
          _ = ((y : G) * w * (y : G)⁻¹ * w⁻¹) * ((x : G) * w * (x : G)⁻¹ * w⁻¹) := by group
          _ = _ := h2.symm }
  have hker : f.ker = (Subgroup.centralizer (V : Set G)).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (x : G) * w * (x : G)⁻¹ * w⁻¹ = 1 := congrArg Subtype.val hx
      have hxw : (x : G) * w = w * x := by
        have := congrArg (· * (w * x)) hx'
        simpa [mul_assoc] using this
      exact h.toHyp611Nat.mem_centralizer_V_of_mem_S_ch62 (hXS x.2) hwV hwZ hxw
    · intro hx
      apply Subtype.ext
      show (x : G) * w * (x : G)⁻¹ * w⁻¹ = 1
      rw [(Subgroup.mem_centralizer_iff.mp hx w hwV).symm]
      group
  have hcard : Nat.card f.range = Nat.card (ch6ZS T L V) := by
    rw [← Subgroup.index_ker, hker, h.card_ZS_four]
    exact hX4
  have htop : f.range = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
  obtain ⟨x, hx⟩ : (⟨z, hz⟩ : ↥(ch6ZS T L V)) ∈ f.range := htop ▸ Subgroup.mem_top _
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem exists_mem_V_not_mem_ZS_ch62 : ∃ w ∈ V, w ∉ ch6ZS T L V := by
  by_contra hcon
  push Not at hcon
  have h1 : Nat.card V ≤ Nat.card (ch6ZS T L V) := Subgroup.card_le_of_le hcon
  rw [h.natural.card_eq, h.card_ZS_four] at h1
  norm_num at h1

theorem frame627_O (h331 : Stmt3_3_1) (h6110 : Stmt6_1_10) {x₀ : G}
    (hXT : conjSubgroup V x₀ ≤ T)
    (hXC : ¬ conjSubgroup V x₀ ≤ Subgroup.centralizer (V : Set G)) :
    conjSubgroup V x₀ ≤ ch6S T L V ∧
    mQuot (conjSubgroup V x₀) (conjSubgroup V x₀ ⊓ Subgroup.centralizer (V : Set G)) = 2 ∧
    (∀ x ∈ conjSubgroup V x₀, x ∉ Subgroup.centralizer (V : Set G) → ∀ w ∈ V,
      x * w = w * x → w ∈ ch6ZS T L V) ∧
    (∀ w ∈ V, w ∉ ch6ZS T L V → ∀ z ∈ ch6ZS T L V,
      ∃ x ∈ conjSubgroup V x₀, x * w * x⁻¹ * w⁻¹ = z) ∧
    (∀ s ∈ ch6S T L V, ∃ x ∈ conjSubgroup V x₀, ∃ q ∈ ch6Q T V, s = x * q) ∧
    V ⊓ Subgroup.centralizer (conjSubgroup V x₀ : Set G) = ch6ZS T L V ∧
    ⁅conjSubgroup V x₀, V⁆ = ch6ZS T L V := by
  set X := conjSubgroup V x₀ with hXdef
  have hV := h.toHyp611.isElemAbelian
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hXS : X ≤ ch6S T L V := by
    have hXW : X ≤ wClos V 0 T :=
      le_wClos (mem_gammaSet_iff.mpr ⟨hXT, x₀, le_rfl, mQuot_self _⟩)
    exact hXW.trans (stmt6_1_12 h331 h6110 G T M L V 2 h.toHyp611Nat).2.2
  have hm : mQuot X (X ⊓ Subgroup.centralizer (V : Set G)) = 2 :=
    (h6110 G T M L V 2 h.toHyp611Nat).2.2 x₀ (hXT.trans h.toHyp611.T_le_normalizer) hXC
  have hX4 : (Subgroup.centralizer (V : Set G)).relIndex X = 4 := by
    have h1 := relIndex_eq_two_pow (isPGroup_conjSubgroup hV2 x₀)
      (X ⊓ Subgroup.centralizer (V : Set G))
    rw [hm, Subgroup.inf_relIndex_left] at h1
    rw [h1]; norm_num
  have h3 : ∀ x ∈ X, x ∉ Subgroup.centralizer (V : Set G) → ∀ w ∈ V,
      x * w = w * x → w ∈ ch6ZS T L V := by
    intro x hx hxC w hw hxw
    by_contra hwZ
    exact hxC (h.toHyp611Nat.mem_centralizer_V_of_mem_S_ch62 (hXS hx) hw hwZ hxw)
  have h5 : ∀ w ∈ V, w ∉ ch6ZS T L V → ∀ z ∈ ch6ZS T L V, ∃ x ∈ X, x * w * x⁻¹ * w⁻¹ = z :=
    fun w hw hwZ z hz => h.exists_commutator_eq_ch62 hXS hX4 hw hwZ hz
  obtain ⟨w₀, hw₀V, hw₀Z⟩ := h.exists_mem_V_not_mem_ZS_ch62
  refine ⟨hXS, hm, h3, h5, ?_, ?_, ?_⟩
  ·
    intro s hs
    obtain ⟨x, hxX, hx⟩ := h5 w₀ hw₀V hw₀Z _ (h.commutator_mem_ZS_ch62 hs hw₀V)
    refine ⟨x, hxX, x⁻¹ * s, ⟨T.mul_mem (T.inv_mem (hXT hxX)) hs.1, ?_⟩, by group⟩
    have e1 : s * w₀ * s⁻¹ = x * w₀ * x⁻¹ := by
      have := congrArg (· * w₀) hx
      simpa using this.symm
    have hqw : x⁻¹ * s * w₀ = w₀ * (x⁻¹ * s) := by
      calc x⁻¹ * s * w₀ = x⁻¹ * (s * w₀ * s⁻¹) * s := by group
        _ = x⁻¹ * (x * w₀ * x⁻¹) * s := by rw [e1]
        _ = w₀ * (x⁻¹ * s) := by group
    have hqS : x⁻¹ * s ∈ ch6S T L V := (ch6S T L V).mul_mem ((ch6S T L V).inv_mem (hXS hxX)) hs
    exact h.toHyp611Nat.mem_centralizer_V_of_mem_S_ch62 hqS hw₀V hw₀Z hqw
  ·
    obtain ⟨x, hxX, hxC⟩ := Set.not_subset.mp hXC
    apply le_antisymm
    · rintro w ⟨hwV, hwC⟩
      exact h3 x hxX hxC w hwV (Subgroup.mem_centralizer_iff.mp hwC x hxX)
    · intro z hz
      refine ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      exact (Subgroup.mem_centralizer_iff.mp (hXS hx).2 z hz).symm
  ·
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx w hw
      rw [commutatorElement_def]
      exact h.commutator_mem_ZS_ch62 (hXS hx) hw
    · intro z hz
      obtain ⟨x, hxX, hx⟩ := h5 w₀ hw₀V hw₀Z z hz
      have := Subgroup.commutator_mem_commutator hxX hw₀V
      rwa [commutatorElement_def, hx] at this

theorem frame627 (h331 : Stmt3_3_1) (h6110 : Stmt6_1_10) {g : G} (hVT : V ≤ conjSubgroup T g)
    (hnc : ⁅V, conjSubgroup V g⁆ ≠ ⊥) :
    V ≤ conjSubgroup (ch6S T L V) g ∧
    mQuot V (V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)) = 2 ∧
    (∀ v ∈ V, v ∉ Subgroup.centralizer (conjSubgroup V g : Set G) → ∀ a ∈ conjSubgroup V g,
      v * a = a * v → a ∈ conjSubgroup (ch6ZS T L V) g) ∧
    (∀ a ∈ conjSubgroup V g, a ∉ conjSubgroup (ch6ZS T L V) g →
      ∀ z ∈ conjSubgroup (ch6ZS T L V) g, ∃ v ∈ V, v * a * v⁻¹ * a⁻¹ = z) ∧
    (∀ s ∈ conjSubgroup (ch6S T L V) g, ∃ v ∈ V, ∃ q ∈ conjSubgroup (ch6Q T V) g, s = v * q) ∧
    conjSubgroup V g ⊓ Subgroup.centralizer (V : Set G) = conjSubgroup (ch6ZS T L V) g ∧
    ⁅V, conjSubgroup V g⁆ = conjSubgroup (ch6ZS T L V) g := by
  set A := conjSubgroup V g with hAdef
  set X := conjSubgroup V g⁻¹ with hXdef
  have hXg : conjSubgroup X g = V := conjSubgroup_inv_conj V g
  have hXT : X ≤ T := by
    have := conjSubgroup_mono_left g⁻¹ hVT
    rwa [conjSubgroup_conj_inv] at this
  have hXC : ¬ X ≤ Subgroup.centralizer (V : Set G) := by
    intro hle
    apply hnc
    have h0 : ⁅X, V⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have h1 := conjSubgroup_commutator X V g
    rw [h0, conjSubgroup_bot, hXg] at h1
    rw [← hAdef] at h1
    exact h1.symm
  obtain ⟨hXS, hm, h3, h5, h6, h7, h8⟩ := h.frame627_O h331 h6110 hXT hXC
  have memX : ∀ v : G, g * v * g⁻¹ ∈ X ↔ v ∈ V := fun v => by
    rw [hXdef, mem_conjSubgroup_iff]
    simp [mul_assoc]
  have memXV : ∀ x : G, x ∈ X ↔ g⁻¹ * x * g ∈ V := fun x => by
    rw [hXdef, mem_conjSubgroup_iff]
    simp
  have hCA : conjSubgroup (Subgroup.centralizer (V : Set G)) g =
      Subgroup.centralizer (A : Set G) := conjSubgroup_centralizer V g
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := conjSubgroup_mono_left g hXS
    rwa [hXg] at this
  · have := mQuot_conjSubgroup X (X ⊓ Subgroup.centralizer (V : Set G)) g
    rw [conjSubgroup_inf, hXg, hCA, hm] at this
    exact this
  · intro v hv hvC a ha hva
    have hx : g * v * g⁻¹ ∈ X := (memX v).mpr hv
    have hxC : g * v * g⁻¹ ∉ Subgroup.centralizer (V : Set G) := by
      intro hxC'
      apply hvC
      rw [← hCA, mem_conjSubgroup_iff]
      exact hxC'
    have hw : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp ha
    have hxw : g * v * g⁻¹ * (g * a * g⁻¹) = g * a * g⁻¹ * (g * v * g⁻¹) := by
      calc g * v * g⁻¹ * (g * a * g⁻¹) = g * (v * a) * g⁻¹ := by group
        _ = g * (a * v) * g⁻¹ := by rw [hva]
        _ = g * a * g⁻¹ * (g * v * g⁻¹) := by group
    exact mem_conjSubgroup_iff.mpr (h3 _ hx hxC _ hw hxw)
  · intro a ha haZ z hz
    have hw : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.mp ha
    have hwZ : g * a * g⁻¹ ∉ ch6ZS T L V := fun h' => haZ (mem_conjSubgroup_iff.mpr h')
    obtain ⟨x, hxX, hx⟩ := h5 _ hw hwZ _ (mem_conjSubgroup_iff.mp hz)
    refine ⟨g⁻¹ * x * g, (memXV x).mp hxX, ?_⟩
    have := congrArg (fun y => g⁻¹ * y * g) hx
    calc g⁻¹ * x * g * a * (g⁻¹ * x * g)⁻¹ * a⁻¹ =
          g⁻¹ * (x * (g * a * g⁻¹) * x⁻¹ * (g * a * g⁻¹)⁻¹) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹) * g := this
      _ = z := by group
  · intro s hs
    obtain ⟨x, hxX, q, hq, hsq⟩ := h6 _ (mem_conjSubgroup_iff.mp hs)
    refine ⟨g⁻¹ * x * g, (memXV x).mp hxX, g⁻¹ * q * g, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      simpa [mul_assoc] using hq
    · calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
        _ = g⁻¹ * (x * q) * g := by rw [hsq]
        _ = g⁻¹ * x * g * (g⁻¹ * q * g) := by group
  · have := congrArg (fun Y => conjSubgroup Y g) h7
    rw [conjSubgroup_inf, conjSubgroup_centralizer, hXg] at this
    exact this
  · have := conjSubgroup_commutator X V g
    rw [h8, hXg] at this
    exact this.symm

end Hyp6Sec2

end CFSG.Quasithin.H13
