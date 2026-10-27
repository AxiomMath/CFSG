module

public import CFSG.Quasithin.Vol2.Ch11SecA15Z1d

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem conjV_pow_apply_coe (V : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (k : ℕ) (v : ↥V) : ((conjV V x hx ^ k) v : G) = x ^ k * v * (x ^ k)⁻¹ := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, MulAut.mul_apply, ih, conjV_apply_coe]
    group

theorem conjV_pow (V : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (k : ℕ) :
    conjV V (x ^ k) (Subgroup.pow_mem _ hx k) = conjV V x hx ^ k := by
  ext v
  rw [conjV_apply_coe, conjV_pow_apply_coe]

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}

theorem centralizes_V1_of_mem (hF11 : Facts11) (h1102 : Stmt11_0_2) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) {g : G} (hgL : g ∈ L)
    (hgV : g ∈ Subgroup.normalizer (fsuV T I : Set G))
    (hg : conjV (fsuV T I) g hgV ∈
      perfectCore (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I)))) :
    ∀ u ∈ V₁, g * u = u * g := by
  rw [← autOn_lOf_eq h hU, mem_autOn_iff] at hg
  obtain ⟨l₁, hl₁, hl₁V, he⟩ := hg
  have hk : l₁⁻¹ * g ∈ L ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
    refine ⟨L.mul_mem (L.inv_mem (lOf_le_L hl₁)) hgL, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro v hv
    have h1 := congrArg (fun φ : MulAut ↥(fsuV T I) => ((φ ⟨v, hv⟩ : ↥(fsuV T I)) : G)) he
    simp only [conjV_apply_coe] at h1
    calc v * (l₁⁻¹ * g) = l₁⁻¹ * (l₁ * v * l₁⁻¹) * g := by group
      _ = l₁⁻¹ * (g * v * g⁻¹) * g := by rw [h1]
      _ = l₁⁻¹ * g * v := by group
  intro u hu
  have hl₁u := Subgroup.mem_centralizer_iff.mp (lOf_one_le_centralizer hF11 h1102 h hU hl₁) u hu
  have hku := Subgroup.mem_centralizer_iff.mp hk.2 u (IsVi.le_fsuV hU hu)
  have e : g = l₁ * (l₁⁻¹ * g) := by group
  rw [e]
  calc l₁ * (l₁⁻¹ * g) * u = l₁ * (u * (l₁⁻¹ * g)) := by rw [mul_assoc, ← hku]
    _ = (l₁ * u) * (l₁⁻¹ * g) := by group
    _ = u * l₁ * (l₁⁻¹ * g) := by rw [← hl₁u]
    _ = u * (l₁ * (l₁⁻¹ * g)) := by group

theorem mem_centralizer_Z1 (hF : Facts15) (hFc : Facts15c) (hF11 : Facts11)
    (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h : Hyp11 G T L I n)
    (hU : IsVi T L I n 1 V₁) (hB : IsSL3Block L ∨ IsSp4Block L) {g : G} (hgL : g ∈ L)
    (hV1 : ∀ u ∈ V₁, g * u = u * g) :
    g ∈ Subgroup.centralizer (omegaOneCenterOf (ROf T L V₁) : Set G) := by
  have hle := Z1_le_sup hF hFc hF11 hG2 h1102 h1103 h hU hB
  have hC : g ∈ Subgroup.centralizer
      ((V₁ ⊔ (omegaOneCenterOf (ROf T L V₁) ⊓ Subgroup.centralizer (L : Set G)) :
        Subgroup G) : Set G) := by
    rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
    rintro x (hx | hx)
    · exact (hV1 x hx).symm
    · exact (Subgroup.mem_centralizer_iff.mp hx.2 g hgL).symm
  exact Subgroup.centralizer_le (fun x hx => hle hx) hC

theorem torus_data (hFc : Facts15c) (hG2 : FactG2DerivedOrder) (h1102 : Stmt11_0_2)
    (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁)
    (hk : KindSL3 L (fsuV T I) n ∨ KindSp4 L (fsuV T I) n) :
    ∃ d₀ ∈ L, ∃ hd₀V : d₀ ∈ Subgroup.normalizer (fsuV T I : Set G),
      d₀ ∈ Subgroup.normalizer (V₁ : Set G) ∧
      (∀ g ∈ L, ∀ hgV : g ∈ Subgroup.normalizer (fsuV T I : Set G),
        g ∈ Subgroup.normalizer (V₁ : Set G) → ∃ k : ℕ, conjV (fsuV T I) g hgV *
          (conjV (fsuV T I) d₀ hd₀V ^ k)⁻¹ ∈
            perfectCore (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I)))) ∧
      (∃ m : ℕ, Odd m ∧ conjV (fsuV T I) d₀ hd₀V ^ m ∈
        perfectCore (autOn L (fsuV T I) ⊓ stabW (V₁.subgroupOf (fsuV T I)))) ∧
      (∀ v ∈ V₁, ∀ w ∈ V₁, v ∉ Subgroup.centralizer (L : Set G) →
        w ∉ Subgroup.centralizer (L : Set G) → ∃ k : ℕ,
          d₀ ^ k * v * (d₀ ^ k)⁻¹ * w⁻¹ ∈ Subgroup.centralizer (L : Set G)) := by
  have hsq : ∀ w : ↥(fsuV T I), w ^ 2 = 1 := fun w =>
    Subtype.ext (by simpa using (isElemAbelian_fsuV h).2 w w.2)
  have hPT : PointTorus (autOn L (fsuV T I))
      ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) (V₁.subgroupOf (fsuV T I)) := by
    rcases hk with hk | hk
    · obtain ⟨_, K, _, _, π, hK, hπ⟩ := sl3_realization hG2 h1102 h hk
      exact hFc.torusSL3 K n h.one_lt hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _
        (isFlagW_of_isVi h hU)
    · obtain ⟨_, K, _, _, π, hK, hπ⟩ := sp4_realization hG2 h1102 h hk
      exact hFc.torusSp4 K n h.one_lt hK _ hsq _ _ π hπ _ (isSylowTwoOf_P h) _
        (isFlagW_of_isVi h hU)
  obtain ⟨d, ⟨hdH, hdU⟩, hgen, ⟨m, hm, hdm⟩, htr⟩ := hPT
  obtain ⟨d₀, hd₀L, hd₀V, rfl⟩ := mem_autOn_iff.mp hdH
  have hUV := IsVi.le_fsuV hU
  refine ⟨d₀, hd₀L, hd₀V, (conjV_mem_stabW_iff hUV hd₀V).mp hdU, fun g hgL hgV hgV₁ => ?_,
    ⟨m, hm, hdm⟩, fun v hv w hw hvC hwC => ?_⟩
  · exact hgen _ ⟨conjV_mem_autOn hgL hgV, (conjV_mem_stabW_iff hUV hgV).mpr hgV₁⟩
  · obtain ⟨k, hk⟩ := htr ⟨v, hUV hv⟩ (Subgroup.mem_subgroupOf.mpr hv) ⟨w, hUV hw⟩
      (Subgroup.mem_subgroupOf.mpr hw) (fun h' => hvC (Subgroup.mem_subgroupOf.mp h'))
      (fun h' => hwC (Subgroup.mem_subgroupOf.mp h'))
    refine ⟨k, ?_⟩
    have := Subgroup.mem_subgroupOf.mp hk
    rwa [Subgroup.coe_mul, Subgroup.coe_inv, conjV_pow_apply_coe] at this

theorem three_points (h : Hyp11 G T L I n) (hU : IsVi T L I n 1 V₁) :
    ∃ v ∈ V₁, ∃ w ∈ V₁, v ∉ Subgroup.centralizer (L : Set G) ∧
      w ∉ Subgroup.centralizer (L : Set G) ∧ v * w⁻¹ ∉ Subgroup.centralizer (L : Set G) := by
  classical
  have hn : 2 ≤ n := h.one_lt
  set K := (fsuV T I ⊓ Subgroup.centralizer (L : Set G)).subgroupOf V₁ with hK
  have hidx : K.index = 2 ^ n := by
    have := IsVi.relIndex_eq hU
    rwa [mul_one] at this
  have : Fintype (↥V₁ ⧸ K) := Fintype.ofFinite _
  have hcard : 4 ≤ Fintype.card (↥V₁ ⧸ K) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index, hidx]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set s := (Finset.univ : Finset (↥V₁ ⧸ K)).erase (QuotientGroup.mk 1) with hs
  have hscard : 1 < s.card := by
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hscard
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective b
  have hcomm : ∀ x ∈ fsuV T I, ∀ y ∈ fsuV T I, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((isElemAbelian_fsuV h).1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hvV := IsVi.le_fsuV hU v.2
  have hwV := IsVi.le_fsuV hU w.2
  have hnot : ∀ x : ↥V₁, (QuotientGroup.mk x : ↥V₁ ⧸ K) ≠ QuotientGroup.mk 1 →
      (x : G) ∉ Subgroup.centralizer (L : Set G) := by
    intro x hx hxC
    apply hx
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [mul_one, Subgroup.coe_inv]
    exact ⟨Subgroup.inv_mem _ (IsVi.le_fsuV hU x.2), Subgroup.inv_mem _ hxC⟩
  refine ⟨v, v.2, w, w.2, hnot v (Finset.ne_of_mem_erase ha), hnot w (Finset.ne_of_mem_erase hb),
    fun hvw => hab ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have e : (v : G)⁻¹ * w = ((v : G) * (w : G)⁻¹)⁻¹ := by
    rw [mul_inv_rev, inv_inv, hcomm _ (Subgroup.inv_mem _ hvV) _ hwV]
  rw [e]
  exact ⟨Subgroup.inv_mem _ (Subgroup.mul_mem _ hvV (Subgroup.inv_mem _ hwV)),
    Subgroup.inv_mem _ hvw⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
