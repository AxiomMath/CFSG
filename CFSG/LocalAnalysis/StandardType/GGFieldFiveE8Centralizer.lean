module

public import CFSG.LocalAnalysis.StandardType.GGFieldFiveE8Classes
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsSp
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.BlockNormalizerControl

public section

namespace CFSG.StandardType

namespace FieldFiveE8

open CFSG.Assembly LayerFacts

open scoped commutatorElement

private theorem commutatorElement_mul_eq_of_commute {G : Type*} [Group G] {z z' k k' : G}
    (hzk : Commute z k) (hzk' : Commute z k') (hz'k : Commute z' k)
    (hz'k' : Commute z' k') (hzz' : Commute z z') : ⁅z * k, z' * k'⁆ = ⁅k, k'⁆ := by
  have hzc : Commute z ⁅k, k'⁆ := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using
      (hzk.mul_right hzk').mul_right (hzk.inv_right.mul_right hzk'.inv_right)
  have hz'c : Commute z' ⁅k, k'⁆ := by
    rw [commutatorElement_def]
    simpa only [mul_assoc] using
      (hz'k.mul_right hz'k').mul_right (hz'k.inv_right.mul_right hz'k'.inv_right)
  rw [commutatorElement_mul_left_eq_conj_mul, (hzz'.mul_right hzk').commutator_eq, mul_one,
    commutatorElement_mul_right_eq_mul_conj, hz'k.symm.commutator_eq, one_mul]
  calc z * (z' * ⁅k, k'⁆ * z'⁻¹) * z⁻¹
      = (z * z') * ⁅k, k'⁆ * (z'⁻¹ * z⁻¹) := by group
    _ = (z * z') * ⁅k, k'⁆ * (z * z')⁻¹ := by rw [mul_inv_rev]
    _ = ⁅k, k'⁆ := by rw [(hzc.mul_left hz'c).eq, mul_assoc, mul_inv_cancel, mul_one]

section Shape

variable {H : Type} [Group H]

theorem IsFiveB.of_zpowers_eq {y y' : H} {K₀ : Subgroup H} (h : IsFiveB y K₀)
    (hyy' : Subgroup.zpowers y = Subgroup.zpowers y') : IsFiveB y' K₀ := by
  have hcy : Subgroup.centralizer ({y} : Set H) = Subgroup.centralizer ({y'} : Set H) := by
    rw [← Subgroup.centralizer_closure ({y} : Set H),
      ← Subgroup.centralizer_closure ({y'} : Set H),
      ← Subgroup.zpowers_eq_closure y, ← Subgroup.zpowers_eq_closure y', hyy']
  refine ⟨?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · rw [← hcy]; exact h.1
  · intro c hc
    have hc' : c ∈ Subgroup.centralizer ({y} : Set H) := by rwa [← hcy] at hc
    obtain ⟨m, hm⟩ := h.2.1 c hc'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← hyy']; exact Subgroup.mem_zpowers y)
    exact ⟨k * m, by rw [zpow_mul y' k m, hk]; exact hm⟩

theorem le_of_isFiveB_of_isQuasisimple {y : H} {K₀ : Subgroup H} (h : IsFiveB y K₀)
    {J : Subgroup H} (hJy : J ≤ Subgroup.centralizer {y}) (hJ : IsQuasisimple ↥J) : J ≤ K₀ := by
  rw [← ggCommutator_eq_of_isQuasisimple hJ]
  refine Subgroup.commutator_le.mpr ?_
  intro g hg g' hg'
  obtain ⟨m, hm⟩ := h.2.1 g (hJy hg)
  obtain ⟨n, hn⟩ := h.2.1 g' (hJy hg')
  have hyk : Commute y (y ^ m * g) :=
    Subgroup.mem_centralizer_iff.mp (h.1.1 hm) y (Set.mem_singleton y)
  have hyk' : Commute y (y ^ n * g') :=
    Subgroup.mem_centralizer_iff.mp (h.1.1 hn) y (Set.mem_singleton y)
  have hzz' : Commute (y ^ (-m)) (y ^ (-n)) :=
    ((Commute.refl y).zpow_left (-m)).zpow_right (-n)
  have hcomm := commutatorElement_mul_eq_of_commute (hyk.zpow_left (-m)) (hyk'.zpow_left (-m))
    (hyk.zpow_left (-n)) (hyk'.zpow_left (-n)) hzz'
  have hg_eq : g = y ^ (-m) * (y ^ m * g) := by group
  have hg'_eq : g' = y ^ (-n) * (y ^ n * g') := by group
  rw [hg_eq, hg'_eq, hcomm, commutatorElement_def]
  exact K₀.mul_mem (K₀.mul_mem (K₀.mul_mem hm hn) (K₀.inv_mem hm)) (K₀.inv_mem hn)

theorem eq_of_isComponentOf_of_isFiveB [Finite H] {y : H} {K₀ : Subgroup H} (h : IsFiveB y K₀)
    {X : Subgroup H} (hX : IsComponentOf X (Subgroup.centralizer {y})) : X = K₀ := by
  have hXq : IsQuasisimple ↥X :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native X).mp hX.2.2
  exact CFSG.LocalAnalysis.ComponentInitial.eq_of_isComponentOf_le hX h.1
    (le_of_isFiveB_of_isQuasisimple h hX.1 hXq)

theorem mem_zpowers_of_mem_centralizer_of_isFiveB {y : H} {K₀ : Subgroup H} (h : IsFiveB y K₀)
    {b : H} (hb : b ∈ Subgroup.centralizer {y}) (hbK : b ∈ Subgroup.centralizer (K₀ : Set H)) :
    b ∈ Subgroup.zpowers y := by
  obtain ⟨n, hn⟩ := h.2.1 b hb
  have hKcent : (⟨y ^ n * b, hn⟩ : ↥K₀) ∈ Subgroup.center ↥K₀ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hgy : Commute (g : H) y :=
      (Subgroup.mem_centralizer_iff.mp (h.1.1 g.2) y (Set.mem_singleton y)).symm
    have hgb : Commute (g : H) b :=
      Subgroup.mem_centralizer_iff.mp hbK (g : H) g.2
    exact ((hgy.zpow_right n).mul_right hgb).eq
  have h1 : y ^ n * b = 1 := by
    have := hKcent
    rw [h.2.2.1, Subgroup.mem_bot] at this
    exact Subtype.ext_iff.mp this
  exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by rw [zpow_neg, ← eq_inv_of_mul_eq_one_right h1]⟩

theorem exists_inner_of_isFiveB {y : H} {K₀ : Subgroup H} (h : IsFiveB y K₀) {b : H}
    (hb : b ∈ Subgroup.centralizer {y}) : ∃ k ∈ K₀, ∀ l ∈ K₀, b⁻¹ * l * b = k⁻¹ * l * k := by
  obtain ⟨n, hn⟩ := h.2.1 b hb
  refine ⟨y ^ n * b, hn, ?_⟩
  intro l hl
  have hyl : Commute y l :=
    Subgroup.mem_centralizer_iff.mp (h.1.1 hl) y (Set.mem_singleton y)
  have hconj : (y ^ n)⁻¹ * l * y ^ n = l := by
    rw [← zpow_neg, (hyl.zpow_left (-n)).eq, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero,
      mul_one]
  calc b⁻¹ * l * b
      = b⁻¹ * ((y ^ n)⁻¹ * l * y ^ n) * b := by rw [hconj]
    _ = (y ^ n * b)⁻¹ * l * (y ^ n * b) := by rw [mul_inv_rev]; group

end Shape

section Transport

variable {H G : Type} [Group H] [Group G]

theorem exists_inner_map {ψ : H →* G} {x : G} {s : H} (hs : (x, s) ∈ ggConjPairs ψ)
    {K₀ : Subgroup H} {k₀ : H} (hk₀ : k₀ ∈ K₀) (hin : ∀ l ∈ K₀, s⁻¹ * l * s = k₀⁻¹ * l * k₀) :
    ∃ k ∈ K₀.map ψ, ∀ l ∈ K₀.map ψ, x⁻¹ * l * x = k⁻¹ * l * k := by
  refine ⟨ψ k₀, Subgroup.mem_map_of_mem ψ hk₀, ?_⟩
  intro l hl
  obtain ⟨u, hu, hul⟩ := Subgroup.mem_map.mp hl
  rw [← hul]
  have hs' : ψ (s * (s⁻¹ * u * s) * s⁻¹) = x * ψ (s⁻¹ * u * s) * x⁻¹ :=
    mem_ggConjPairs.mp hs (s⁻¹ * u * s)
  have hsu : s * (s⁻¹ * u * s) * s⁻¹ = u := by group
  rw [hsu] at hs'
  have hx : x⁻¹ * ψ u * x = ψ (s⁻¹ * u * s) := by rw [hs']; group
  rw [hin u hu, map_mul, map_mul, map_inv] at hx
  exact hx

end Transport

end FieldFiveE8

end CFSG.StandardType
