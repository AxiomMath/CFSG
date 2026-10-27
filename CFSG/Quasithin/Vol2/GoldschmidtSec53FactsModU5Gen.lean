module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.Sec53F.Unit

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

theorem exists_commutator_mul {G : Type*} [Group G] {U Z : Subgroup G} [Finite U]
    (hZc : ∀ z ∈ Z, ∀ u ∈ U, u * z = z * u) {t : G}
    (hUt : ∀ u ∈ U, t * u * t⁻¹ ∈ U) (hZt : ∀ z ∈ Z, t * z * t⁻¹ ∈ Z)
    (hfix : ∀ v ∈ U, ∀ z ∈ Z, t * v * t⁻¹ = v * z → v ∈ Z) :
    ∀ g ∈ U, ∃ u ∈ U, ∃ z ∈ Z, g = u * t * u⁻¹ * t⁻¹ * z := by
  classical
  have hcm : ∀ u : U, ((u : G) * (t * (u : G)⁻¹ * t⁻¹)) ∈ U := fun u =>
    mul_mem u.2 (by simpa [mul_assoc] using hUt _ (inv_mem u.2))
  let c : U → U := fun u => ⟨(u : G) * (t * (u : G)⁻¹ * t⁻¹), hcm u⟩
  have hkey : ∀ a b : U, (((c a)⁻¹ * c b : U) : G) =
      (t * (a : G) * t⁻¹) * ((a : G)⁻¹ * b) * (t * (b : G)⁻¹ * t⁻¹) := by
    intro a b
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, c]
    group
  have hrel : ∀ a b : U, QuotientGroup.leftRel (Z.subgroupOf U) a b ↔
      ((a⁻¹ * b : U) : G) ∈ Z := by
    intro a b
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  have hc : ∀ a b : U, QuotientGroup.leftRel (Z.subgroupOf U) a b →
      QuotientGroup.leftRel (Z.subgroupOf U) (c a) (c b) := by
    intro a b hab
    rw [hrel] at hab ⊢
    rw [hkey]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hab
    set z := (a : G)⁻¹ * b with hz
    have hbz : (b : G) = a * z := by rw [hz]; group
    have hz1 : t * z⁻¹ * t⁻¹ ∈ Z := hZt _ (inv_mem hab)
    have hb' : t * (b : G)⁻¹ * t⁻¹ = (t * z⁻¹ * t⁻¹) * (t * (a : G)⁻¹ * t⁻¹) := by
      rw [hbz]; group
    have hcomm := hZc _ (mul_mem hab hz1) _ (hUt _ a.2)
    have : t * (a : G) * t⁻¹ * z * (t * (b : G)⁻¹ * t⁻¹) = z * (t * z⁻¹ * t⁻¹) := by
      rw [hb']
      calc t * (a : G) * t⁻¹ * z * (t * z⁻¹ * t⁻¹ * (t * (a : G)⁻¹ * t⁻¹))
          = t * (a : G) * t⁻¹ * (z * (t * z⁻¹ * t⁻¹)) * (t * (a : G)⁻¹ * t⁻¹) := by group
        _ = (z * (t * z⁻¹ * t⁻¹)) * (t * (a : G) * t⁻¹) * (t * (a : G)⁻¹ * t⁻¹) := by
          rw [hcomm]
        _ = z * (t * z⁻¹ * t⁻¹) := by group
    rw [this]
    exact mul_mem hab hz1
  let φ : U ⧸ Z.subgroupOf U → U ⧸ Z.subgroupOf U := Quotient.map' c hc
  have hinj : Function.Injective φ := by
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have h0 : (QuotientGroup.mk (c a) : U ⧸ Z.subgroupOf U) = QuotientGroup.mk (c b) := hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, hkey] at h0
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    set v : G := (a : G)⁻¹ * b with hv
    have hvU : v ∈ U := mul_mem (inv_mem a.2) b.2
    have hbv : (b : G) = (a : G) * v := by rw [hv]; group
    have hs : t * (a : G) * t⁻¹ ∈ U := hUt _ a.2
    set z' : G := t * (a : G) * t⁻¹ * v * (t * (b : G)⁻¹ * t⁻¹) with hz'
    have hz'c := hZc _ h0 _ hs
    have e1 : z' = (t * (a : G) * t⁻¹) * (v * (t * v⁻¹ * t⁻¹)) * (t * (a : G) * t⁻¹)⁻¹ := by
      rw [hz', hbv]; group
    have hw : v * (t * v⁻¹ * t⁻¹) = z' := by
      calc v * (t * v⁻¹ * t⁻¹)
          = (t * (a : G) * t⁻¹)⁻¹ * ((t * (a : G) * t⁻¹) * (v * (t * v⁻¹ * t⁻¹)) *
            (t * (a : G) * t⁻¹)⁻¹) * (t * (a : G) * t⁻¹) := by group
        _ = (t * (a : G) * t⁻¹)⁻¹ * z' * (t * (a : G) * t⁻¹) := by rw [← e1]
        _ = z' := by rw [mul_assoc, ← hz'c, inv_mul_cancel_left]
    have hvc : Commute v z' := hZc _ h0 _ hvU
    have ht : t * v * t⁻¹ = v * z'⁻¹ := by
      have h1 : t * v⁻¹ * t⁻¹ = v⁻¹ * z' := by
        rw [← hw]; group
      have h2 : t * v * t⁻¹ = (v⁻¹ * z')⁻¹ := by
        rw [← h1]; group
      rw [h2, mul_inv_rev, inv_inv, hvc.inv_right.eq]
    exact hfix v hvU _ (inv_mem h0) ht
  have hsurj : Function.Surjective φ := Finite.injective_iff_surjective.mp hinj
  intro g hg
  obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk ⟨g, hg⟩)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  have h0 : (QuotientGroup.mk (c u) : U ⧸ Z.subgroupOf U) = QuotientGroup.mk ⟨g, hg⟩ := hq
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h0
  refine ⟨u, u.2, _, h0, ?_⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, c]
  group

theorem commutator_mul_mul_of_commute {G : Type*} [Group G] {a b z w : G}
    (h1 : z * (b * w) = (b * w) * z) (h2 : w * a = a * w) :
    a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have h3 : w * a⁻¹ = a⁻¹ * w := (show Commute w a from h2).inv_right.eq
  calc a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹
      = a * (z * (b * w)) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹) := by group
    _ = a * ((b * w) * z) * (z⁻¹ * a⁻¹) * (w⁻¹ * b⁻¹) := by rw [h1]
    _ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * w) * w⁻¹ * b⁻¹ := by rw [h3]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem range_le_perfectCore {G₁ G : Type*} [Group G₁] [Group G] (h₁ : Group.IsPerfect G₁)
    (φ : G₁ →* G) {H : Subgroup G} (hφ : φ.range ≤ H) : φ.range ≤ perfectCore H := by
  refine le_perfectCore_of_perfect hφ ?_
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def,
    h₁.commutator_eq_top]

theorem isTwoLocal_of_le_normalizer {C : Type*} [Group C] {M R : Subgroup C} (hM : IsCoatom M)
    (hno : ∀ N : Subgroup C, N.Normal → IsPGroup 2 N → N = ⊥) (hR0 : R ≠ ⊥)
    (hR : IsPGroup 2 R) (hMR : M ≤ Subgroup.normalizer (R : Set C)) : IsTwoLocal M := by
  refine ⟨R, hR0, hR, ?_⟩
  rcases hM.le_iff.mp hMR with h | h
  · exact absurd (hno R (Subgroup.normalizer_eq_top_iff.mp h) hR) hR0
  · exact h.symm

end CFSG.Quasithin.H13.Sec53F.Unit
