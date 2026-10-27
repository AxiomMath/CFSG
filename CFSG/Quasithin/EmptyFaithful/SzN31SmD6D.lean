module

public import CFSG.Quasithin.EmptyFaithful.SzN31SmD6B

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN31

open CFSG.Quasithin.G11
open scoped Pointwise

namespace SmD6

open CntLin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {Γ A : Subgroup (GLV V)}

section Plane

variable {P : Subgroup (GLV V)}

theorem card_eq_three_mul_card_centralizerOn (hP3 : IsPGroup 3 P) (hfix : fixedSpace P = ⊥)
    {U : Submodule (ZMod 2) V} (hU : Invariant P U) (hU2 : Module.finrank (ZMod 2) U = 2) :
    Nat.card P = 3 * Nat.card (centralizerOn P U) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hU2
    omega
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hstab : MulAction.stabilizer ↥P u = (centralizerOn P U).subgroupOf P := by
    ext ⟨k, hk⟩
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_centralizerOn]
    constructor
    · intro hku
      refine ⟨hk, ?_⟩
      rcases trichotomy hP3 hU hU2 hk with h | h
      · exact h
      · exact absurd (h u huU hku) hu0
    · intro h
      exact h.2 u huU
  have hidx := MulAction.index_stabilizer ↥P u
  have horb : (MulAction.orbit ↥P u) ⊆ ((U : Set V) \ {0}) := by
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    refine ⟨hU k hk u huU, ?_⟩
    intro h0
    have : (k : GLV V) u = 0 := h0
    exact hu0 (by simpa using (map_eq_zero_iff (k : GLV V) (LinearEquiv.injective k)).1 this)
  have hUcard : (U : Set V).ncard = 4 := by
    have : Module.Finite (ZMod 2) U := Module.Finite.of_finite
    rw [← Nat.card_coe_set_eq]
    show Nat.card U = 4
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hU2]
    norm_num
  have hcard3 : ((U : Set V) \ {0}).ncard = 3 := by
    rw [Set.ncard_sdiff_singleton_of_mem (by exact U.zero_mem), hUcard]
  have hle3 : (MulAction.stabilizer ↥P u).index ≤ 3 := by
    rw [hidx, ← hcard3]
    exact Set.ncard_le_ncard horb (Set.toFinite _)
  obtain ⟨k, hk⟩ := hP3.exists_card_eq
  have hdvd : (MulAction.stabilizer ↥P u).index ∣ 3 ^ k := hk ▸ Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
  have hne1 : (MulAction.stabilizer ↥P u).index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    have hu' : u ∈ fixedSpace P := fun q hq => by
      have hmem : (⟨q, hq⟩ : ↥P) ∈ MulAction.stabilizer ↥P u := by rw [h1]; exact Subgroup.mem_top _
      exact MulAction.mem_stabilizer_iff.1 hmem
    rw [hfix] at hu'
    exact hu0 ((Submodule.mem_bot (ZMod 2)).1 hu')
  have h3 : (MulAction.stabilizer ↥P u).index = 3 := by
    have hj1 : j ≤ 1 := by
      by_contra hcon
      have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases j
    · exact absurd (by simpa using hj) hne1
    · simpa using hj
  have hle : centralizerOn P U ≤ P := fun q hq => (mem_centralizerOn.1 hq).1
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer ↥P u)
  rw [h3, hstab, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hmul
  omega

end Plane

section Planes

variable {P : Subgroup (GLV V)} {W : Fin 3 → Submodule (ZMod 2) V}

omit [Finite V] in
theorem ThreePlanes.disjoint (hW : ThreePlanes Γ P W) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (W i) (W j) := by
  have h02 : Disjoint (W 0) (W 2) := hW.disj012.mono_left le_sup_left
  have h12 : Disjoint (W 1) (W 2) := hW.disj012.mono_left le_sup_right
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hW.disj01
  · exact h02
  · exact hW.disj01.symm
  · exact absurd rfl hij
  · exact h12
  · exact h02.symm
  · exact h12.symm
  · exact absurd rfl hij

omit [Finite V] in
theorem ThreePlanes.conj_ij (hW : ThreePlanes Γ P W) (i j : Fin 3) :
    ∃ g ∈ Γ, W j = G11.conjSub g (W i) := by
  obtain ⟨gi, hgi, hi⟩ := hW.conj i
  obtain ⟨gj, hgj, hj⟩ := hW.conj j
  refine ⟨gj * gi⁻¹, Γ.mul_mem hgj (Γ.inv_mem hgi), ?_⟩
  rw [hj, hi, ← G11.conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]

omit [Finite V] in
theorem ThreePlanes.exists_decomp (hW : ThreePlanes Γ P W) (v : V) :
    ∃ w : Fin 3 → V, (∀ i, w i ∈ W i) ∧ v = w 0 + w 1 + w 2 := by
  have hv : v ∈ W 0 ⊔ W 1 ⊔ W 2 := by rw [hW.sup]; exact Submodule.mem_top
  obtain ⟨a, ha, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  refine ⟨![x, y, z], fun i => ?_, rfl⟩
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

omit [Finite V] in
theorem ThreePlanes.eq_zero_of_sum (hW : ThreePlanes Γ P W) {w : Fin 3 → V} (hw : ∀ i, w i ∈ W i)
    (h : w 0 + w 1 + w 2 = 0) : ∀ i, w i = 0 := by
  have h2 : w 2 = 0 := by
    have hmem : w 2 ∈ W 0 ⊔ W 1 := by
      have : w 2 = -(w 0 + w 1) := eq_neg_of_add_eq_zero_right h
      rw [this]
      exact Submodule.neg_mem _ (Submodule.add_mem_sup (hw 0) (hw 1))
    exact Submodule.disjoint_def.1 hW.disj012 _ hmem (hw 2)
  rw [h2, add_zero] at h
  have h1 : w 1 = 0 := by
    have hmem : w 1 ∈ W 0 := by
      have : w 1 = -(w 0) := eq_neg_of_add_eq_zero_right h
      rw [this]
      exact Submodule.neg_mem _ (hw 0)
    exact Submodule.disjoint_def.1 hW.disj01 _ hmem (hw 1)
  rw [h1, add_zero] at h
  intro i
  fin_cases i
  · exact h
  · exact h1
  · exact h2

omit [Finite V] in
theorem ThreePlanes.fixed_split (hW : ThreePlanes Γ P W) {S : Set (GLV V)}
    (hS : ∀ k ∈ S, ∀ i, ∀ u ∈ W i, k u ∈ W i) {w : Fin 3 → V} (hw : ∀ i, w i ∈ W i)
    (hfix : ∀ k ∈ S, k (w 0 + w 1 + w 2) = w 0 + w 1 + w 2) : ∀ k ∈ S, ∀ i, k (w i) = w i := by
  intro k hk
  have hsum : (k (w 0) - w 0) + (k (w 1) - w 1) + (k (w 2) - w 2) = 0 := by
    have := hfix k hk
    rw [map_add, map_add] at this
    have h2 : k (w 0) + k (w 1) + k (w 2) - (w 0 + w 1 + w 2) = 0 := sub_eq_zero.2 this
    rw [← h2]
    abel
  have hz := hW.eq_zero_of_sum (w := fun i => k (w i) - w i)
    (fun i => Submodule.sub_mem _ (hS k hk i _ (hw i)) (hw i)) hsum
  intro i
  exact sub_eq_zero.1 (hz i)

end Planes

section Kernels

variable {P : Subgroup (GLV V)} {W : Fin 3 → Submodule (ZMod 2) V}

theorem le_centralizerOn_of_fixed (hP3 : IsPGroup 3 P) {U : Submodule (ZMod 2) V}
    (hU : Invariant P U) (hU2 : Module.finrank (ZMod 2) U = 2) {S : Subgroup (GLV V)} (hS : S ≤ P)
    {w : V} (hwU : w ∈ U) (hw : w ≠ 0) (hfix : ∀ k ∈ S, k w = w) : S ≤ centralizerOn P U := by
  intro k hk
  refine ⟨hS hk, ?_⟩
  rcases trichotomy hP3 hU hU2 (hS hk) with h | h
  · exact h
  · exact absurd (h w hwU (hfix k hk)) hw

theorem centralizerOn_eq_of_le (hP3 : IsPGroup 3 P) (hfix : fixedSpace P = ⊥)
    {U U' : Submodule (ZMod 2) V} (hU : Invariant P U) (hU2 : Module.finrank (ZMod 2) U = 2)
    (hU' : Invariant P U') (hU2' : Module.finrank (ZMod 2) U' = 2)
    (h : centralizerOn P U ≤ centralizerOn P U') : centralizerOn P U = centralizerOn P U' := by
  have h1 := card_eq_three_mul_card_centralizerOn hP3 hfix hU hU2
  have h2 := card_eq_three_mul_card_centralizerOn hP3 hfix hU' hU2'
  exact Subgroup.eq_of_le_of_card_ge h (by omega)

variable (hP3 : IsPGroup 3 P) (hfix : fixedSpace P = ⊥) (hW : ThreePlanes Γ P W)
include hP3 hW

theorem ThreePlanes.component_zero (i : Fin 3) {S : Subgroup (GLV V)} (hS : S ≤ P)
    (hne : ¬ S ≤ centralizerOn P (W i)) {w : Fin 3 → V} (hw : ∀ j, w j ∈ W j)
    (hfixS : ∀ k ∈ S, k (w 0 + w 1 + w 2) = w 0 + w 1 + w 2) : w i = 0 := by
  have hsplit := hW.fixed_split (S := (S : Set (GLV V)))
    (fun k hk j u hu => hW.inv j k (hS hk) u hu) hw hfixS
  by_contra hi
  exact hne (le_centralizerOn_of_fixed hP3 (hW.inv i) (hW.rank i) hS (hw i) hi
    (fun k hk => hsplit k hk i))

theorem ThreePlanes.fixedSpace_le (c : Fin 3)
    (h : ∀ i, i ≠ c → ¬ centralizerOn P (W c) ≤ centralizerOn P (W i)) :
    fixedSpace (centralizerOn P (W c)) ≤ W c := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := hW.exists_decomp v
  have hz : ∀ i, i ≠ c → w i = 0 := fun i hi =>
    hW.component_zero hP3 i (fun k hk => (mem_centralizerOn.1 hk).1) (h i hi) hw (fun k hk => hv k hk)
  fin_cases c
  · have h1 := hz 1 (by decide)
    have h2 := hz 2 (by decide)
    simp only [h1, h2, add_zero]
    exact hw 0
  · have h0 := hz 0 (by decide)
    have h2 := hz 2 (by decide)
    simp only [h0, h2, zero_add, add_zero]
    exact hw 1
  · have h0 := hz 0 (by decide)
    have h1 := hz 1 (by decide)
    simp only [h0, h1, zero_add]
    exact hw 2

omit [Finite V] hP3 hW in
theorem le_fixedSpace_centralizerOn (U : Submodule (ZMod 2) V) :
    U ≤ fixedSpace (centralizerOn P U) := fun u hu _ hk => (mem_centralizerOn.1 hk).2 u hu

end Kernels

section Conj

variable {P : Subgroup (GLV V)}

omit [Finite V] in
theorem conj_apply_eq (g k : GLV V) (x : V) : (g * k * g⁻¹) x = g (k (g.symm x)) := rfl

omit [Finite V] in
theorem fixedSpace_centralizerOn_conj (hPn : ∀ γ ∈ Γ, ∀ n ∈ P, γ * n * γ⁻¹ ∈ P)
    {g : GLV V} (hg : g ∈ Γ) (U : Submodule (ZMod 2) V) :
    fixedSpace (centralizerOn P (G11.conjSub g U)) =
      G11.conjSub g (fixedSpace (centralizerOn P U)) := by
  have hginv : g⁻¹ ∈ Γ := Γ.inv_mem hg
  ext v
  rw [G11.mem_conjSub]
  constructor
  · intro hv k' hk'
    obtain ⟨hk'P, hk'U⟩ := mem_centralizerOn.1 hk'
    have hkP : g * k' * g⁻¹ ∈ P := hPn g hg k' hk'P
    have hk : g * k' * g⁻¹ ∈ centralizerOn P (G11.conjSub g U) := by
      refine mem_centralizerOn.2 ⟨hkP, ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      have : (g * k' * g⁻¹) (g u) = g u := by
        rw [conj_apply_eq]
        simp only [LinearEquiv.symm_apply_apply]
        rw [hk'U u hu]
      exact this
    have h1 := hv _ hk
    rw [conj_apply_eq] at h1
    have h2 := congrArg g.symm h1
    simpa only [LinearEquiv.symm_apply_apply] using h2
  · intro hv k hk
    obtain ⟨hkP, hkU⟩ := mem_centralizerOn.1 hk
    have hk'P : g⁻¹ * k * g⁻¹⁻¹ ∈ P := hPn g⁻¹ hginv k hkP
    rw [inv_inv] at hk'P
    have hk' : g⁻¹ * k * g ∈ centralizerOn P U := by
      refine mem_centralizerOn.2 ⟨hk'P, fun u hu => ?_⟩
      have h1 : k (g u) = g u := hkU _ ⟨u, hu, rfl⟩
      show g.symm (k (g u)) = u
      rw [h1]
      exact g.symm_apply_apply u
    have h1 := hv _ hk'
    have h2 : g.symm (k v) = g.symm v := by
      have : (g⁻¹ * k * g) (g.symm v) = g.symm (k v) := by
        simp [LinearEquiv.mul_apply]
      rw [← this]
      exact h1
    exact g.symm.injective h2

end Conj

section Dichotomy

variable {P : Subgroup (GLV V)} {W : Fin 3 → Submodule (ZMod 2) V}
variable (hP3 : IsPGroup 3 P) (hfix : fixedSpace P = ⊥)
  (hPn : ∀ γ ∈ Γ, ∀ n ∈ P, γ * n * γ⁻¹ ∈ P) (hW : ThreePlanes Γ P W)

omit [Finite V] in
include hPn hW in
theorem ThreePlanes.finrank_fixedSpace_eq (i j : Fin 3) :
    Module.finrank (ZMod 2) (fixedSpace (centralizerOn P (W j))) =
      Module.finrank (ZMod 2) (fixedSpace (centralizerOn P (W i))) := by
  obtain ⟨g, hg, hj⟩ := hW.conj_ij i j
  rw [hj, fixedSpace_centralizerOn_conj hPn hg, G11.finrank_conjSub]

include hP3 hfix hPn hW in
theorem ThreePlanes.mixed_false {a b c : Fin 3} (hab : a ≠ b)
    (hcover : ∀ i, i = a ∨ i = b ∨ i = c) (hac : a ≠ c) (hbc : b ≠ c)
    (hK : centralizerOn P (W a) = centralizerOn P (W b))
    (hc : centralizerOn P (W c) ≠ centralizerOn P (W a)) : False := by
  have hle : fixedSpace (centralizerOn P (W c)) ≤ W c := by
    refine hW.fixedSpace_le hP3 c fun i hi hle' => ?_
    have hne : centralizerOn P (W c) = centralizerOn P (W i) :=
      centralizerOn_eq_of_le hP3 hfix (hW.inv c) (hW.rank c) (hW.inv i) (hW.rank i) hle'
    rcases hcover i with rfl | rfl | rfl
    · exact hc hne
    · exact hc (hne.trans hK.symm)
    · exact hi rfl
  have hge : W a ⊔ W b ≤ fixedSpace (centralizerOn P (W a)) := by
    refine sup_le (le_fixedSpace_centralizerOn _) ?_
    rw [hK]
    exact le_fixedSpace_centralizerOn _
  have h4 : Module.finrank (ZMod 2) ↥(W a ⊔ W b) = 4 := by
    have h1 : Module.Finite (ZMod 2) (W a) := Module.Finite.of_finite
    have h2 : Module.Finite (ZMod 2) (W b) := Module.Finite.of_finite
    have := Submodule.finrank_sup_add_finrank_inf_eq (W a) (W b)
    rw [disjoint_iff.1 (hW.disjoint hab), finrank_bot, hW.rank a, hW.rank b] at this
    omega
  have hd := hW.finrank_fixedSpace_eq hPn a c
  have h1 := Submodule.finrank_mono hge
  have h2 := Submodule.finrank_mono hle
  rw [h4] at h1
  rw [hW.rank c] at h2
  omega

end Dichotomy

section Cases

variable {P : Subgroup (GLV V)} {W : Fin 3 → Submodule (ZMod 2) V}
variable (hP3 : IsPGroup 3 P) (hfix : fixedSpace P = ⊥)
  (hPn : ∀ γ ∈ Γ, ∀ n ∈ P, γ * n * γ⁻¹ ∈ P) (hW : ThreePlanes Γ P W)

include hP3 hfix hPn hW in
theorem ThreePlanes.kernels_eq_or_ne :
    (centralizerOn P (W 0) = centralizerOn P (W 1) ∧ centralizerOn P (W 1) = centralizerOn P (W 2)) ∨
      (centralizerOn P (W 0) ≠ centralizerOn P (W 1) ∧ centralizerOn P (W 0) ≠ centralizerOn P (W 2) ∧
        centralizerOn P (W 1) ≠ centralizerOn P (W 2)) := by
  by_cases h01 : centralizerOn P (W 0) = centralizerOn P (W 1)
  · by_cases h12 : centralizerOn P (W 1) = centralizerOn P (W 2)
    · exact Or.inl ⟨h01, h12⟩
    · exact (hW.mixed_false hP3 hfix hPn (a := 0) (b := 1) (c := 2) (by decide)
        (by decide) (by decide) (by decide) h01 (fun h => h12 (h01.symm.trans h.symm))).elim
  · by_cases h02 : centralizerOn P (W 0) = centralizerOn P (W 2)
    · exact (hW.mixed_false hP3 hfix hPn (a := 0) (b := 2) (c := 1) (by decide)
        (by decide) (by decide) (by decide) h02 (fun h => h01 h.symm)).elim
    · by_cases h12 : centralizerOn P (W 1) = centralizerOn P (W 2)
      · exact (hW.mixed_false hP3 hfix hPn (a := 1) (b := 2) (c := 0) (by decide)
          (by decide) (by decide) (by decide) h12 (fun h => h01 h)).elim
      · exact Or.inr ⟨h01, h02, h12⟩

include hP3 hfix hW in
theorem ThreePlanes.card_le_three_of_eq
    (h01 : centralizerOn P (W 0) = centralizerOn P (W 1))
    (h12 : centralizerOn P (W 1) = centralizerOn P (W 2)) : Nat.card P ≤ 3 := by
  have hK : centralizerOn P (W 0) = ⊥ := by
    rw [eq_bot_iff]
    intro k hk
    rw [Subgroup.mem_bot]
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨w, hw, rfl⟩ := hW.exists_decomp v
    have h1 : k ∈ centralizerOn P (W 1) := h01 ▸ hk
    have h2 : k ∈ centralizerOn P (W 2) := h12 ▸ h1
    show k (w 0 + w 1 + w 2) = w 0 + w 1 + w 2
    rw [map_add, map_add, (mem_centralizerOn.1 hk).2 _ (hw 0), (mem_centralizerOn.1 h1).2 _ (hw 1),
      (mem_centralizerOn.1 h2).2 _ (hw 2)]
  have := card_eq_three_mul_card_centralizerOn hP3 hfix (hW.inv 0) (hW.rank 0)
  rw [hK, Subgroup.card_bot] at this
  omega

end Cases

section Distinct

variable {P : Subgroup (GLV V)} {W : Fin 3 → Submodule (ZMod 2) V}
variable (hP3 : IsPGroup 3 P) (hfix : fixedSpace P = ⊥)
  (hPn : ∀ γ ∈ Γ, ∀ n ∈ P, γ * n * γ⁻¹ ∈ P) (hW : ThreePlanes Γ P W)
  (hdist : ∀ i j : Fin 3, i ≠ j → centralizerOn P (W i) ≠ centralizerOn P (W j))

include hP3 hfix hW hdist in
theorem ThreePlanes.fixedSpace_eq_of_distinct (c : Fin 3) :
    fixedSpace (centralizerOn P (W c)) = W c := by
  refine le_antisymm (hW.fixedSpace_le hP3 c fun i hi hle => hdist c i (Ne.symm hi) ?_)
    (le_fixedSpace_centralizerOn _)
  exact centralizerOn_eq_of_le hP3 hfix (hW.inv c) (hW.rank c) (hW.inv i) (hW.rank i) hle

include hP3 hfix hPn hW hdist in
theorem ThreePlanes.conj_mem_of_distinct {g : GLV V} (hg : g ∈ Γ) (i : Fin 3) :
    ∃ j, G11.conjSub g (W i) = W j := by
  set U := G11.conjSub g (W i) with hU
  have hUinv : Invariant P U := (hW.inv i).conj_of_normal hPn hg
  have hU2 : Module.finrank (ZMod 2) U = 2 := by rw [hU, G11.finrank_conjSub, hW.rank i]
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hU2
    omega
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hSP : centralizerOn P U ≤ P := fun k hk => (mem_centralizerOn.1 hk).1
  have hj : ∃ j, centralizerOn P U ≤ centralizerOn P (W j) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w, hw, rfl⟩ := hW.exists_decomp u
    have hz : ∀ j, w j = 0 := fun j =>
      hW.component_zero hP3 j hSP (hcon j) hw (fun k hk => (mem_centralizerOn.1 hk).2 _ huU)
    apply hu0
    rw [hz 0, hz 1, hz 2]
    simp
  obtain ⟨j, hle⟩ := hj
  have heq := centralizerOn_eq_of_le hP3 hfix hUinv hU2 (hW.inv j) (hW.rank j) hle
  refine ⟨j, ?_⟩
  have hsub : U ≤ W j := by
    have := le_fixedSpace_centralizerOn (P := P) U
    rw [heq, hW.fixedSpace_eq_of_distinct hP3 hfix hdist j] at this
    exact this
  exact Submodule.eq_of_le_of_finrank_eq hsub (by rw [hU2, hW.rank j])

include hP3 hfix hPn hW hdist in
theorem ThreePlanes.three_dvd_index_of_distinct : 3 ∣ (P.subgroupOf Γ).index := by
  have hne : ∀ i j : Fin 3, i ≠ j → W i ≠ W j := by
    intro i j hij h
    have hd := hW.disjoint hij
    rw [← h, disjoint_self] at hd
    have := hW.rank i
    rw [hd, finrank_bot] at this
    omega
  have horb : (MulAction.orbit ↥Γ (W 0) : Set (Submodule (ZMod 2) V)) = {W 0, W 1, W 2} := by
    ext U
    constructor
    · rintro ⟨⟨g, hg⟩, rfl⟩
      obtain ⟨j, hj⟩ := hW.conj_mem_of_distinct hP3 hfix hPn hdist hg 0
      have hgj : (⟨g, hg⟩ : ↥Γ) • W 0 = W j := hj
      change (⟨g, hg⟩ : ↥Γ) • W 0 ∈ ({W 0, W 1, W 2} : Set (Submodule (ZMod 2) V))
      rw [hgj]
      fin_cases j <;> simp
    · intro hU
      have hU' : ∃ j, U = W j := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hU
        rcases hU with rfl | rfl | rfl
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩
      obtain ⟨j, rfl⟩ := hU'
      obtain ⟨g, hg, hgj⟩ := hW.conj_ij 0 j
      exact ⟨⟨g, hg⟩, hgj.symm⟩
  have hcard : (MulAction.orbit ↥Γ (W 0)).ncard = 3 := by
    rw [horb]
    exact Set.ncard_eq_three.2 ⟨W 0, W 1, W 2, hne 0 1 (by decide), hne 0 2 (by decide),
      hne 1 2 (by decide), rfl⟩
  have hidx := MulAction.index_stabilizer ↥Γ (W 0)
  rw [hcard] at hidx
  have hle : P.subgroupOf Γ ≤ MulAction.stabilizer ↥Γ (W 0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    exact (hW.inv 0).conjSub_eq (Subgroup.mem_subgroupOf.1 hg)
  have hmul := Subgroup.relIndex_mul_index hle
  rw [hidx] at hmul
  exact Dvd.intro_left _ hmul

end Distinct

end SmD6

end CFSG.Quasithin.SzN31
