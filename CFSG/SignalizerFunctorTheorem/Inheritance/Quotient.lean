module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Basic
public import CFSG.SignalizerFunctorTheorem.Inheritance.Pullback
public import CFSG.SignalizerFunctorTheorem.Inheritance.CosetFixed

public section

namespace CFSG.SignalizerFunctorTheorem

theorem noFaithfulSection_map {H : Type*} [Group H] [Finite H] {p : ℕ} {A W N : Subgroup H}
    [N.Normal] (hNW : N ≤ W) (hA : ∀ a ∈ A, a ^ p = 1) (hcop : Nat.Coprime p (Nat.card W))
    (h : NoFaithfulSection A W) :
    NoFaithfulSection (A.map (QuotientGroup.mk' N)) (W.map (QuotientGroup.mk' N)) := by
  intro KQ LQ hKQ hLQ hnorm hAK hAL hsimple hnonab
  set π := QuotientGroup.mk' N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hAN : ∀ a ∈ A, π a = 1 → a = 1 := by
    intro a ha hπa
    have haN : a ∈ N := by rwa [← hker, MonoidHom.mem_ker]
    have h1 : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one (hA a ha)
    have h2 : orderOf a ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W (hNW haN)
    have h3 : orderOf a ∣ Nat.gcd p (Nat.card W) := Nat.dvd_gcd h1 h2
    rw [hcop] at h3
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)
  have hKW : KQ.comap π ≤ W := by
    have := Subgroup.comap_mono (f := π) hKQ
    rwa [Subgroup.comap_map_eq, hker, sup_eq_left.mpr hNW] at this
  have hLK : LQ.comap π ≤ KQ.comap π := Subgroup.comap_mono hLQ
  have hnormK := normal_comap_subgroupOf π hLQ
  have hnormalizer : ∀ {K : Subgroup (H ⧸ N)}, A.map π ≤ Subgroup.normalizer (K : Set (H ⧸ N)) →
      A ≤ Subgroup.normalizer ((K.comap π : Subgroup H) : Set H) := by
    intro K hK a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have := Subgroup.mem_normalizer_iff.mp (hK (Subgroup.mem_map_of_mem π ha)) (π x)
    simpa [Subgroup.mem_comap] using this
  let e := comapSectionEquiv π hsurj (K := KQ) (L := LQ)
  obtain ⟨a, haA, ha1, hmem⟩ := h (KQ.comap π) (LQ.comap π) hKW hLK (hnormalizer hAK)
    (hnormalizer hAL) e.isSimpleGroup
    (by
      obtain ⟨x, y, hxy⟩ := hnonab
      exact ⟨e.symm x, e.symm y, fun hc => hxy (by simpa using congrArg e hc)⟩)
  refine ⟨π a, Subgroup.mem_map_of_mem π haA, fun h1 => ha1 (hAN a haA h1), ?_⟩
  intro y hy
  obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp (hKQ hy)
  have := hmem w (Subgroup.mem_comap.mpr hy)
  simpa [Subgroup.mem_comap] using this

theorem map_inf_centralizer_eq {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {W N : Subgroup H} [N.Normal] (hNW : N ≤ W) (hcop : Nat.Coprime p (Nat.card N)) {a : H}
    (ha : a ^ p = 1) :
    (W ⊓ Subgroup.centralizer {a}).map (QuotientGroup.mk' N) =
      W.map (QuotientGroup.mk' N) ⊓ Subgroup.centralizer {QuotientGroup.mk' N a} := by
  refine le_antisymm (le_inf (Subgroup.map_mono inf_le_left) ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hx.2 a rfl]
  · rintro _ ⟨⟨w, hwW, rfl⟩, hy⟩
    have hcomm : QuotientGroup.mk' N a * QuotientGroup.mk' N w =
        QuotientGroup.mk' N w * QuotientGroup.mk' N a :=
      Subgroup.mem_centralizer_iff.mp hy _ rfl
    have hw : a * w * a⁻¹ * w⁻¹ ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      rw [hcomm]
      group
    obtain ⟨x, hx1, hx2⟩ := exists_fixed_of_coprime hp ha N hcop hw
    have hxW : x ∈ W := by simpa using mul_mem (hNW hx1) hwW
    refine ⟨x, Subgroup.mem_inf.mpr ⟨hxW, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact mul_inv_eq_iff_eq_mul.mp hx2
    · exact QuotientGroup.eq_iff_div_mem.mpr (by simpa [div_eq_mul_inv] using hx1)

end CFSG.SignalizerFunctorTheorem
