module

public import CFSG.Quasithin.H13.AS91Sec8Equiv
import Mathlib.Tactic.Group
public import Mathlib.GroupTheory.GroupAction.Basic

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94 MulAction
open scoped Pointwise

universe u v u' v'

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]
  {Gb : Type v'} [Group Gb] {Xb : Type u'} [MulAction Gb Xb]
  {x y : X} {xb yb : Xb} {I : Subgroup G} {Ib : Subgroup Gb}
  {β : stabilizer G x ≃* stabilizer Gb xb} {ζ : I ≃* Ib}

theorem conj_mem_stab_inf {g : G} (hg : g ∈ stabilizer G ({x, y} : Set X)) {m : G}
    (hm : m ∈ stabilizer G x ⊓ stabilizer G y) : g * m * g⁻¹ ∈ stabilizer G x ⊓ stabilizer G y := by
  have hmem : ∀ {g : G}, g ∈ stabilizer G ({x, y} : Set X) → ∀ a ∈ ({x, y} : Set X),
      g • a ∈ ({x, y} : Set X) := by
    intro g hg a ha
    have := Set.smul_mem_smul_set (a := g) ha
    rwa [mem_stabilizer_iff.mp hg] at this
  have hx : g⁻¹ • x ∈ ({x, y} : Set X) := hmem (inv_mem hg) x (by simp)
  have hy : g⁻¹ • y ∈ ({x, y} : Set X) := hmem (inv_mem hg) y (by simp)
  have hfix : ∀ a ∈ ({x, y} : Set X), m • a = a := by
    intro a ha
    rcases ha with rfl | ha
    · exact mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hm).1
    · rw [Set.mem_singleton_iff] at ha
      subst ha
      exact mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hm).2
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_stabilizer_iff, mul_smul, mul_smul, hfix _ hx, smul_inv_smul]
  · rw [mem_stabilizer_iff, mul_smul, mul_smul, hfix _ hy, smul_inv_smul]

theorem mem_stab_iff_of_map (hs : IsSimilarity I x y Ib xb yb β ζ) (k : ↥(stabilizer G x)) :
    (k : G) ∈ stabilizer G y ↔ ((β k : ↥(stabilizer Gb xb)) : Gb) ∈ stabilizer Gb yb := by
  have h := hs.map_stab_two
  have h1 : k ∈ (stabilizer G y).subgroupOf (stabilizer G x) ↔
      β k ∈ ((stabilizer G y).subgroupOf (stabilizer G x)).map β.toMonoidHom := by
    rw [Subgroup.mem_map_equiv]
    simp
  rw [h] at h1
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h1
  exact h1

theorem totFun_mem_inf (hs : IsSimilarity I x y Ib xb yb β ζ) {m : G}
    (hm : m ∈ stabilizer G x ⊓ stabilizer G y) :
    totFun β m ∈ stabilizer Gb xb ⊓ stabilizer Gb yb := by
  have hm' := Subgroup.mem_inf.mp hm
  rw [totFun_of_mem β hm'.1]
  exact Subgroup.mem_inf.mpr ⟨(β ⟨m, hm'.1⟩).2, (mem_stab_iff_of_map hs ⟨m, hm'.1⟩).mp hm'.2⟩

theorem totFun_symm_mem_inf (hs : IsSimilarity I x y Ib xb yb β ζ) {b : Gb}
    (hb : b ∈ stabilizer Gb xb ⊓ stabilizer Gb yb) :
    totFun β.symm b ∈ stabilizer G x ⊓ stabilizer G y := by
  have hb' := Subgroup.mem_inf.mp hb
  rw [totFun_of_mem β.symm hb'.1]
  refine Subgroup.mem_inf.mpr ⟨(β.symm ⟨b, hb'.1⟩).2, ?_⟩
  rw [mem_stab_iff_of_map hs, MulEquiv.apply_symm_apply]
  exact hb'.2

theorem conj_mem_stabImage_of_char (hs : IsSimilarity I x y Ib xb yb β ζ) (K : Subgroup G)
    (hKxy : K ≤ stabilizer G x ⊓ stabilizer G y)
    (hchar : ∀ φ : ↥(stabilizer G x ⊓ stabilizer G y) ≃* ↥(stabilizer G x ⊓ stabilizer G y),
      ∀ k : ↥(stabilizer G x ⊓ stabilizer G y), (k : G) ∈ K →
        ((φ k : ↥(stabilizer G x ⊓ stabilizer G y)) : G) ∈ K)
    {n : Gb} (hn : n ∈ stabilizer Gb ({xb, yb} : Set Xb)) {b : Gb} (hb : b ∈ stabImage β K) :
    n * b * n⁻¹ ∈ stabImage β K := by
  have hnM : ∀ m : Gb, m ∈ stabilizer Gb xb ⊓ stabilizer Gb yb →
      n * m * n⁻¹ ∈ stabilizer Gb xb ⊓ stabilizer Gb yb := fun m hm => conj_mem_stab_inf hn hm
  have hninvM : ∀ m : Gb, m ∈ stabilizer Gb xb ⊓ stabilizer Gb yb →
      n⁻¹ * m * n ∈ stabilizer Gb xb ⊓ stabilizer Gb yb := by
    intro m hm
    simpa using conj_mem_stab_inf (inv_mem hn) hm
  have hMx : ∀ m : Gb, m ∈ stabilizer Gb xb ⊓ stabilizer Gb yb → m ∈ stabilizer Gb xb :=
    fun m hm => (Subgroup.mem_inf.mp hm).1
  have hMx' : ∀ m : G, m ∈ stabilizer G x ⊓ stabilizer G y → m ∈ stabilizer G x :=
    fun m hm => (Subgroup.mem_inf.mp hm).1
  let f : ↥(stabilizer G x ⊓ stabilizer G y) → ↥(stabilizer G x ⊓ stabilizer G y) := fun m =>
    ⟨totFun β.symm (n * totFun β m * n⁻¹),
      totFun_symm_mem_inf hs (hnM _ (totFun_mem_inf hs m.2))⟩
  let g : ↥(stabilizer G x ⊓ stabilizer G y) → ↥(stabilizer G x ⊓ stabilizer G y) := fun m =>
    ⟨totFun β.symm (n⁻¹ * totFun β m * n),
      totFun_symm_mem_inf hs (hninvM _ (totFun_mem_inf hs m.2))⟩
  have hfg : ∀ m, g (f m) = m := by
    intro m
    apply Subtype.ext
    change totFun β.symm (n⁻¹ * totFun β (totFun β.symm (n * totFun β m * n⁻¹)) * n) = m
    rw [totFun_totFun_symm β (hMx _ (hnM _ (totFun_mem_inf hs m.2)))]
    rw [show n⁻¹ * (n * totFun β m * n⁻¹) * n = totFun β m by group]
    exact totFun_symm_totFun β (hMx' _ m.2)
  have hgf : ∀ m, f (g m) = m := by
    intro m
    apply Subtype.ext
    change totFun β.symm (n * totFun β (totFun β.symm (n⁻¹ * totFun β m * n)) * n⁻¹) = m
    rw [totFun_totFun_symm β (hMx _ (hninvM _ (totFun_mem_inf hs m.2)))]
    rw [show n * (n⁻¹ * totFun β m * n) * n⁻¹ = totFun β m by group]
    exact totFun_symm_totFun β (hMx' _ m.2)
  have hfmul : ∀ a b : ↥(stabilizer G x ⊓ stabilizer G y), f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    change totFun β.symm (n * totFun β ((a : G) * b) * n⁻¹) =
      totFun β.symm (n * totFun β a * n⁻¹) * totFun β.symm (n * totFun β b * n⁻¹)
    rw [totFun_mul β (hMx' _ a.2) (hMx' _ b.2)]
    rw [show n * (totFun β a * totFun β b) * n⁻¹ =
      (n * totFun β a * n⁻¹) * (n * totFun β b * n⁻¹) by group]
    exact totFun_mul β.symm (hMx _ (hnM _ (totFun_mem_inf hs a.2)))
      (hMx _ (hnM _ (totFun_mem_inf hs b.2)))
  let φ : ↥(stabilizer G x ⊓ stabilizer G y) ≃* ↥(stabilizer G x ⊓ stabilizer G y) :=
    { toFun := f
      invFun := g
      left_inv := hfg
      right_inv := hgf
      map_mul' := hfmul }
  obtain ⟨k, hkK, rfl⟩ := mem_stabImage.mp hb
  have hkM : (k : G) ∈ stabilizer G x ⊓ stabilizer G y := hKxy hkK
  have hφ := hchar φ ⟨k, hkM⟩ hkK
  change totFun β.symm (n * totFun β k * n⁻¹) ∈ K at hφ
  have hmem := totFun_mem_stabImage (β := β) (fun a ha => (Subgroup.mem_inf.mp (hKxy ha)).1) hφ
  rw [totFun_totFun_symm β (hMx _ (hnM _ (totFun_mem_inf hs hkM)))] at hmem
  rwa [totFun_coe] at hmem

theorem mem_normalizer_stabImage_of_mem (K : Subgroup G) {g : G} (hg : g ∈ stabilizer G x)
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) :
    ((β ⟨g, hg⟩ : ↥(stabilizer Gb xb)) : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb) := by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  constructor
  · intro hb
    obtain ⟨k, hkK, rfl⟩ := mem_stabImage.mp hb
    have hk' : g * k * g⁻¹ ∈ K := conj_mem_of_normalizer' hgK hkK
    refine mem_stabImage.mpr ⟨⟨g * k * g⁻¹, ?_⟩, hk', ?_⟩
    · exact mul_mem (mul_mem hg k.2) (inv_mem hg)
    · have : (⟨g * k * g⁻¹, mul_mem (mul_mem hg k.2) (inv_mem hg)⟩ : ↥(stabilizer G x)) =
        ⟨g, hg⟩ * k * ⟨g, hg⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      rfl
  · intro hb
    obtain ⟨k, hkK, hk⟩ := mem_stabImage.mp hb
    have hk' : g⁻¹ * k * g ∈ K := conj_mem_of_normalizer hgK hkK
    refine mem_stabImage.mpr ⟨⟨g⁻¹ * k * g, ?_⟩, hk', ?_⟩
    · exact mul_mem (mul_mem (inv_mem hg) k.2) hg
    · have h1 : (⟨g⁻¹ * k * g, mul_mem (mul_mem (inv_mem hg) k.2) hg⟩ : ↥(stabilizer G x)) =
        ⟨g, hg⟩⁻¹ * k * ⟨g, hg⟩ := rfl
      rw [h1, map_mul, map_mul, map_inv]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hk]
      group

theorem mem_stabilizer_pair_of_swap {t : G} (htx : t • x = y) (hty : t • y = x) :
    t ∈ stabilizer G ({x, y} : Set X) := by
  rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, htx, hty, Set.pair_comm]

theorem equivalence_of_charK (hs : IsSimilarity I x y Ib xb yb β ζ) (K : Subgroup G)
    (hKxy : K ≤ stabilizer G x ⊓ stabilizer G y)
    (h1 : ∀ α : K ≃* K, (∀ k : K, (k : G) ∈ I → α k = k) →
      ∃ w : G, w ∈ I ∧ w ∈ Subgroup.normalizer (K : Set G) ∧ (∀ i ∈ I, w * i = i * w) ∧
        ∀ k : K, (α k : G) = w * k * w⁻¹)
    (hchar : ∀ φ : ↥(stabilizer G x ⊓ stabilizer G y) ≃* ↥(stabilizer G x ⊓ stabilizer G y),
      ∀ k : ↥(stabilizer G x ⊓ stabilizer G y), (k : G) ∈ K →
        ((φ k : ↥(stabilizer G x ⊓ stabilizer G y)) : G) ∈ K)
    (t h₁ : I) (u : X) (htx : (t : G) • x = y) (hty : (t : G) • y = x) (htu : (t : G) • u = u)
    (hh₁x : (h₁ : G) • x = x) (hh₁y : (h₁ : G) • y = u)
    (htK : (t : G) ∈ Subgroup.normalizer (K : Set G))
    (hh₁K : (h₁ : G) ∈ Subgroup.normalizer (K : Set G))
    (h3 : stabilizer G x ⊓ stabilizer G y = K ⊔ I ⊓ stabilizer G x ⊓ stabilizer G y) :
    IsEquivalence I x y Ib xb yb β ζ := by
  have hK : K ≤ stabilizer G x := fun k hk => (Subgroup.mem_inf.mp (hKxy hk)).1
  have hKy : K ≤ stabilizer G y := fun k hk => (Subgroup.mem_inf.mp (hKxy hk)).2
  have hh₁x' : (h₁ : G) ∈ stabilizer G x := mem_stabilizer_iff.mpr hh₁x
  have hhx : ((h₁ * t : I) : G) • x = u := by
    rw [Subgroup.coe_mul, mul_smul, htx, hh₁y]
  have htpair : (t : G) ∈ stabilizer G ({x, y} : Set X) := mem_stabilizer_pair_of_swap htx hty
  have hζt : (ζ t : Gb) ∈ stabilizer Gb ({xb, yb} : Set Xb) := by
    have : ζ t ∈ ((stabilizer G ({x, y} : Set X)).subgroupOf I).map ζ.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htpair)
    rw [hs.map_edge] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hζtβ : (ζ t : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb) := by
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · exact conj_mem_stabImage_of_char hs K hKxy hchar hζt
    · intro hb
      have htpair' : ((t⁻¹ : I) : G) ∈ stabilizer G ({x, y} : Set X) := by
        rw [Subgroup.coe_inv]; exact inv_mem htpair
      have hζt' : (ζ t⁻¹ : Gb) ∈ stabilizer Gb ({xb, yb} : Set Xb) := by
        have : ζ t⁻¹ ∈ ((stabilizer G ({x, y} : Set X)).subgroupOf I).map ζ.toMonoidHom :=
          Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htpair')
        rw [hs.map_edge] at this
        exact Subgroup.mem_subgroupOf.mp this
      have := conj_mem_stabImage_of_char hs K hKxy hchar hζt' hb
      rw [map_inv, Subgroup.coe_inv] at this
      simpa [mul_assoc] using this
  have hh₁β : (ζ h₁ : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb) := by
    rw [← hs.eq_on h₁ hh₁x']
    exact mem_normalizer_stabImage_of_mem K hh₁x' hh₁K
  have hhβ : (ζ (h₁ * t) : Gb) ∈ Subgroup.normalizer (stabImage β K : Set Gb) := by
    rw [map_mul, Subgroup.coe_mul]
    exact mul_mem hh₁β hζtβ
  refine (equivalence_criterion_Z hs K t (h₁ * t) hK h1 htx hty ?_ htK ?_ hhβ ?_).2
  · rw [mem_stabilizer_iff, mul_smul, mul_smul, hhx, htu]
    exact inv_smul_eq_iff.mpr hhx.symm
  · rw [Subgroup.coe_mul]; exact mul_mem hh₁K htK
  · rw [h3, inf_eq_left.mpr hKy]

end CFSG.Quasithin.H13.AS91
