module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

abbrev o2Map (X : Subgroup G) : ↥X →* O2Q X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)

namespace ParLift

variable {X K T : Subgroup G}

theorem mem_bar_iff {Y : Subgroup G} {x : ↥X} :
    o2Map X x ∈ modO2Image X Y ↔ ∃ y ∈ Y, ∃ hy : y ∈ X, o2Map X ⟨y, hy⟩ = o2Map X x := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, y.2, hyx⟩
  · rintro ⟨y, hy, hyX, hyx⟩
    exact ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr hy, hyx⟩

theorem inv_mul_mem_of_eq (hS : IsSylowTwoOf T X) {x y : ↥X} (h : o2Map X x = o2Map X y) :
    ((x⁻¹ * y : ↥X) : G) ∈ T := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
  exact pCore_two_le_subgroupOf hS h

theorem inf_bar_eq (hS : IsSylowTwoOf T X) :
    o2Img X T ⊓ modO2Image X K = modO2Image X (T ⊓ K) := by
  apply le_antisymm
  · rintro z ⟨⟨t, ht, rfl⟩, hz⟩
    obtain ⟨k, hk, hkX, hkt⟩ := mem_bar_iff.mp hz
    have h1 := inv_mul_mem_of_eq hS hkt
    have hkT : k = (t : G) * ((⟨k, hkX⟩⁻¹ * t : ↥X) : G)⁻¹ := by simp
    have hkT' : k ∈ T := by
      rw [hkT]
      exact T.mul_mem (Subgroup.mem_subgroupOf.mp ht) (T.inv_mem h1)
    exact mem_bar_iff.mpr ⟨k, Subgroup.mem_inf.mpr ⟨hkT', hk⟩, hkX, hkt⟩
  · exact le_inf (Subgroup.map_mono fun x hx => (Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp hx).1))
      (Subgroup.map_mono fun x hx => (Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_subgroupOf.mp hx).2))

theorem mem_normalizer_of_bar (hS : IsSylowTwoOf T X) (hKX : K ≤ X) {k : G} (hk : k ∈ K)
    (hkn : o2Map X ⟨k, hKX hk⟩ ∈ Subgroup.normalizer
      ((o2Img X T ⊓ modO2Image X K : Subgroup (O2Q X)) : Set (O2Q X))) :
    k ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
  rw [inf_bar_eq hS] at hkn
  have one_dir : ∀ {g : G} (hg : g ∈ K),
      o2Map X ⟨g, hKX hg⟩ ∈ Subgroup.normalizer
        ((modO2Image X (T ⊓ K) : Subgroup (O2Q X)) : Set (O2Q X)) →
      ∀ s ∈ T ⊓ K, g * s * g⁻¹ ∈ T ⊓ K := by
    intro g hg hgn s hs
    have hsX : s ∈ X := hKX hs.2
    have hgsK : g * s * g⁻¹ ∈ K := K.mul_mem (K.mul_mem hg hs.2) (K.inv_mem hg)
    have h1 : o2Map X ⟨g * s * g⁻¹, hKX hgsK⟩ ∈ modO2Image X (T ⊓ K) := by
      have h2 : o2Map X ⟨s, hsX⟩ ∈ modO2Image X (T ⊓ K) :=
        ⟨⟨s, hsX⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      have h3 := (Subgroup.mem_normalizer_iff.mp hgn _).mp h2
      have e : o2Map X ⟨g * s * g⁻¹, hKX hgsK⟩ =
          o2Map X ⟨g, hKX hg⟩ * o2Map X ⟨s, hsX⟩ * (o2Map X ⟨g, hKX hg⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h3
    obtain ⟨s', hs', hs'X, hs'e⟩ := mem_bar_iff.mp h1
    have h4 := inv_mul_mem_of_eq hS hs'e
    have e2 : g * s * g⁻¹ = s' * ((⟨s', hs'X⟩⁻¹ * ⟨g * s * g⁻¹, hKX hgsK⟩ : ↥X) : G) := by
      simp
    refine Subgroup.mem_inf.mpr ⟨?_, hgsK⟩
    rw [e2]
    exact T.mul_mem hs'.1 h4
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact one_dir hk hkn s
  · intro h
    have hki : k⁻¹ ∈ K := K.inv_mem hk
    have hkin : o2Map X ⟨k⁻¹, hKX hki⟩ ∈ Subgroup.normalizer
        ((modO2Image X (T ⊓ K) : Subgroup (O2Q X)) : Set (O2Q X)) := by
      have e : o2Map X ⟨k⁻¹, hKX hki⟩ = (o2Map X ⟨k, hKX hk⟩)⁻¹ := by
        rw [← map_inv]
        rfl
      rw [e]
      exact Subgroup.inv_mem _ hkn
    have := one_dir hki hkin _ h
    simpa [mul_assoc] using this

end ParLift

open ParLift in
theorem exists_maxParabolic_lift {X K T : Subgroup G} (hS : IsSylowTwoOf T X) (hKX : K ≤ X)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hSK : IsSylowTwoOf (T ⊓ K) K)
    (hSb : IsSylowTwoOf (o2Img X T ⊓ modO2Image X K) (modO2Image X K))
    {Pb : Subgroup (O2Q X)} (hPb : IsMaxParabolic2 (modO2Image X K) Pb)
    (hB : modO2Image X K ⊓
      Subgroup.normalizer ((o2Img X T ⊓ modO2Image X K : Subgroup (O2Q X)) : Set (O2Q X)) ≤ Pb)
    (hTP : o2Img X T ≤ Subgroup.normalizer (Pb : Set (O2Q X))) :
    ∃ P : Subgroup G, IsMaxParabolic2 K P ∧
      K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ P ∧
      T ≤ Subgroup.normalizer (P : Set G) := by
  classical
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  set P : Subgroup G := (Pb.comap π).map X.subtype ⊓ K with hPdef
  have mem_P : ∀ {g : G} (hg : g ∈ K), g ∈ P ↔ π ⟨g, hKX hg⟩ ∈ Pb := by
    intro g hg
    constructor
    · rintro ⟨⟨y, hy, hyg⟩, -⟩
      have : y = ⟨g, hKX hg⟩ := Subtype.ext hyg
      rw [← this]
      exact hy
    · intro h
      exact Subgroup.mem_inf.mpr ⟨⟨⟨g, hKX hg⟩, h, rfl⟩, hg⟩
  have hPK : P ≤ K := inf_le_right
  have hPbK : Pb ≤ modO2Image X K := hPb.1.1
  have hPbP : ∀ z ∈ Pb, ∃ g ∈ P, ∃ hg : g ∈ X, π ⟨g, hg⟩ = z := by
    intro z hz
    obtain ⟨⟨g, hgX⟩, hgK, rfl⟩ := hPbK hz
    have hgK' : g ∈ K := Subgroup.mem_subgroupOf.mp hgK
    exact ⟨g, (mem_P hgK').mpr hz, hgX, rfl⟩
  have hBP : K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ≤ P := by
    rintro k ⟨hk, hkn⟩
    rw [mem_P hk]
    apply hB
    refine Subgroup.mem_inf.mpr ⟨⟨⟨k, hKX hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩, ?_⟩
    rw [inf_bar_eq hS]
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨⟨s, hsX⟩, hs, rfl⟩
      have hs' : s ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hs
      have h1 := (Subgroup.mem_normalizer_iff.mp hkn s).mp hs'
      refine ⟨⟨k * s * k⁻¹, hKX h1.2⟩, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    · intro hz
      obtain ⟨⟨s, hsX⟩, hs, hse⟩ := hz
      have hs' : s ∈ T ⊓ K := Subgroup.mem_subgroupOf.mp hs
      have hki := Subgroup.inv_mem _ hkn
      have h1 := (Subgroup.mem_normalizer_iff.mp hki s).mp hs'
      refine ⟨⟨k⁻¹ * s * k⁻¹⁻¹, hKX h1.2⟩, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
      have e : z = (π ⟨k, hKX hk⟩)⁻¹ * π ⟨s, hsX⟩ * π ⟨k, hKX hk⟩ := by
        rw [hse]
        group
      rw [e, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp
  have hTP' : T ≤ Subgroup.normalizer (P : Set G) := by
    have one_dir : ∀ t ∈ T, ∀ x ∈ P, t * x * t⁻¹ ∈ P := by
      intro t ht x hx
      have hxK := hPK hx
      have htK := hTK ht
      have hxt : t * x * t⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp htK x).mp hxK
      rw [mem_P hxt]
      have htX : t ∈ X := hS.1 ht
      have h1 : π ⟨t, htX⟩ ∈ o2Img X T := ⟨⟨t, htX⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      have h2 := (Subgroup.mem_normalizer_iff.mp (hTP h1) _).mp ((mem_P hxK).mp hx)
      have e : π ⟨t * x * t⁻¹, hKX hxt⟩ = π ⟨t, htX⟩ * π ⟨x, hKX hxK⟩ * (π ⟨t, htX⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact h2
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨one_dir t ht x, fun h => ?_⟩
    have := one_dir t⁻¹ (T.inv_mem ht) _ h
    simpa [mul_assoc] using this
  have hPpar : IsParabolic2 K P := ⟨hPK, T ⊓ K, hSK, hBP⟩
  have hPne : P ≠ K := by
    intro hPK'
    apply hPb.2.1
    apply le_antisymm hPbK
    rintro _ ⟨⟨g, hgX⟩, hgK, rfl⟩
    have hgK' : g ∈ K := Subgroup.mem_subgroupOf.mp hgK
    have : g ∈ P := hPK'.symm ▸ hgK'
    exact (mem_P hgK').mp this
  refine ⟨P, ⟨hPpar, hPne, fun Q hQ hQK hPQ => ?_⟩, hBP, hTP'⟩
  have hQK' : Q ≤ K := hQ.1
  set Qb : Subgroup (O2Q X) := modO2Image X Q with hQb
  have hQbK : Qb ≤ modO2Image X K := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hQK' (Subgroup.mem_subgroupOf.mp hx))
  have hQbpar : IsParabolic2 (modO2Image X K) Qb := by
    refine ⟨hQbK, o2Img X T ⊓ modO2Image X K, hSb, ?_⟩
    rintro z ⟨hzK, hzn⟩
    obtain ⟨⟨y, hyX⟩, hyK, rfl⟩ := hzK
    have hyK' : y ∈ K := Subgroup.mem_subgroupOf.mp hyK
    have hyn := mem_normalizer_of_bar hS hKX hyK' hzn
    exact ⟨⟨y, hyX⟩, Subgroup.mem_subgroupOf.mpr (hPQ (hBP (Subgroup.mem_inf.mpr ⟨hyK', hyn⟩))),
      rfl⟩
  have hQbne : Qb ≠ modO2Image X K := by
    intro hQbeq
    apply hQK
    apply le_antisymm hQK'
    intro k hk
    have hkb : π ⟨k, hKX hk⟩ ∈ Qb := hQbeq ▸ ⟨⟨k, hKX hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    obtain ⟨q, hq, hqX, hqk⟩ := mem_bar_iff.mp hkb
    have h1 := inv_mul_mem_of_eq hS hqk
    have hqK := hQK' hq
    have hnK : ((⟨q, hqX⟩⁻¹ * ⟨k, hKX hk⟩ : ↥X) : G) ∈ K := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact K.mul_mem (K.inv_mem hqK) hk
    have hnN : ((⟨q, hqX⟩⁻¹ * ⟨k, hKX hk⟩ : ↥X) : G) ∈
        Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      have h2 : ((⟨q, hqX⟩⁻¹ * ⟨k, hKX hk⟩ : ↥X) : G) ∈ T ⊓ K := Subgroup.mem_inf.mpr ⟨h1, hnK⟩
      exact Subgroup.le_normalizer h2
    have h3 := hPQ (hBP (Subgroup.mem_inf.mpr ⟨hnK, hnN⟩))
    have e : k = q * ((⟨q, hqX⟩⁻¹ * ⟨k, hKX hk⟩ : ↥X) : G) := by simp
    rw [e]
    exact Q.mul_mem hq h3
  have hPbQb : Pb ≤ Qb := by
    intro z hz
    obtain ⟨g, hgP, hgX, rfl⟩ := hPbP z hz
    exact ⟨⟨g, hgX⟩, Subgroup.mem_subgroupOf.mpr (hPQ hgP), rfl⟩
  have hQbeq : Qb = Pb := hPb.2.2 Qb hQbpar hQbne hPbQb
  apply le_antisymm _ hPQ
  intro q hq
  have hqK := hQK' hq
  rw [mem_P hqK, ← hQbeq]
  exact ⟨⟨q, hKX hqK⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩

end CFSG.Quasithin.H13
