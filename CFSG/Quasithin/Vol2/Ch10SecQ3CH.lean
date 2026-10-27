module

public import CFSG.Quasithin.Vol2.Ch10SecQ3CG

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem card_hall_eq {X T B₀ B : Subgroup G} (hT : IsSylowTwoOf T X)
    (hB₀ : Lin2.IsHallTwoPrimeOf B₀ X) (hB : Lin2.IsHallTwoPrimeOf B X) :
    Nat.card B = Nat.card B₀ := by
  have h1 := card_eq_card_mul_card hT hB₀
  have h2 := card_eq_card_mul_card hT hB
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.symm.trans h1)

omit [Finite G] in
theorem mk_mem_normalizer_map {X N B : Subgroup G} [(N.subgroupOf X).Normal] {s : G}
    (hs : s ∈ X) (hsB : s ∈ Subgroup.normalizer (B : Set G)) :
    QuotientGroup.mk' (N.subgroupOf X) ⟨s, hs⟩ ∈
      Subgroup.normalizer (((B.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) :
        Subgroup (↥X ⧸ N.subgroupOf X)) : Set (↥X ⧸ N.subgroupOf X)) := by
  refine Subgroup.le_normalizer_map _ ⟨⟨s, hs⟩, ?_, rfl⟩
  refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_normalizer_iff.mp hsB (z : G)

omit [Finite G] in
theorem mk_eq_one_of_mem {X N : Subgroup G} [(N.subgroupOf X).Normal] {q : G} (hq : q ∈ N)
    (hqX : q ∈ X) : QuotientGroup.mk' (N.subgroupOf X) ⟨q, hqX⟩ = 1 :=
  (QuotientGroup.eq_one_iff _).mpr hq

theorem normal_map_of_hall {X T B₀ : Subgroup G} (hT : IsSylowTwoOf T X)
    (hB₀ : Lin2.IsHallTwoPrimeOf B₀ X)
    (hTQ : T ≤ pCoreOf 2 X ⊔ (T ⊓ Subgroup.normalizer (B₀ : Set G)))
    [((pCoreOf 2 X).subgroupOf X).Normal] :
    ((B₀.subgroupOf X).map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X))).Normal := by
  set φ := QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X)
  set B₀' := (B₀.subgroupOf X).map φ
  set N' := ((Subgroup.normalizer (B₀' : Set (↥X ⧸ (pCoreOf 2 X).subgroupOf X))).comap φ).map
    X.subtype
  have hmemN' : ∀ {x : G} (hx : x ∈ X), φ ⟨x, hx⟩ ∈ Subgroup.normalizer (B₀' : Set _) →
      x ∈ N' := fun hx h => ⟨⟨_, hx⟩, h, rfl⟩
  have hXN' : X ≤ N' := by
    refine (le_sup_of_hall hT hB₀).trans (sup_le ?_ ?_)
    · refine hTQ.trans (sup_le ?_ ?_)
      · intro q hq
        refine hmemN' (pCoreOf_le 2 X hq) ?_
        rw [mk_eq_one_of_mem hq]
        exact Subgroup.one_mem _
      · intro s hs
        exact hmemN' (hT.1 hs.1) (mk_mem_normalizer_map (hT.1 hs.1) hs.2)
    · intro b hb
      exact hmemN' (hB₀.1 hb) (Subgroup.le_normalizer ⟨⟨b, hB₀.1 hb⟩, hb, rfl⟩)
  refine ⟨fun β hβ γ => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ γ
  obtain ⟨x', hx', hxe⟩ := hXN' x.2
  have hx'' : φ x' ∈ Subgroup.normalizer (B₀' : Set _) := hx'
  have : x' = x := Subtype.ext hxe
  rw [this] at hx''
  exact (Subgroup.mem_normalizer_iff.mp hx'' β).mp hβ

theorem exists_orderOf_dvd_of_map {X Y : Type} [Group X] [Group Y] [Finite X] (φ : X →* Y)
    (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker) {B₀ B : Subgroup X}
    [(B₀.map φ).Normal] {i : ℕ} (hi : (B₀.map φ).index = 2 ^ i) (hB : Odd (Nat.card B))
    (hcard : Nat.card B = Nat.card B₀) {y : X} (hy : Odd (orderOf y)) :
    ∃ b ∈ B, orderOf y ∣ orderOf b := by
  have : Finite Y := Finite.of_surjective φ hφ
  have hodd_mem : ∀ z : X, Odd (orderOf z) → φ z ∈ B₀.map φ := fun z hz =>
    mem_of_odd_of_index hi (Odd.of_dvd_nat hz (orderOf_map_dvd φ z))
  have hle : B.map φ ≤ B₀.map φ := by
    rintro _ ⟨z, hz, rfl⟩
    exact hodd_mem z (Odd.of_dvd_nat hB (Subgroup.orderOf_dvd_natCard _ hz))
  have hinj : Function.Injective (φ.domRestrict B) := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have h1 : (z : X) ∈ φ.ker := hz
    have h2 := eq_one_of_mem_of_odd hker h1
      (Odd.of_dvd_nat hB (Subgroup.orderOf_dvd_natCard _ z.2))
    exact Subtype.ext h2
  have hcardB : Nat.card (B.map φ) = Nat.card B := by
    rw [← MonoidHom.domRestrict_range, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  have hcardB₀ : Nat.card (B₀.map φ) ≤ Nat.card B₀ :=
    Nat.card_le_card_of_surjective _ (φ.subgroupMap_surjective _)
  have heq : B.map φ = B₀.map φ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcardB, hcard]; exact hcardB₀)
  have hyB : φ y ∈ B.map φ := heq ▸ hodd_mem y hy
  obtain ⟨b, hb, hbe⟩ := hyB
  refine ⟨b, hb, ?_⟩
  have h1 : y ^ orderOf b ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, ← hbe, ← map_pow, pow_orderOf_eq_one, map_one]
  have h2 := eq_one_of_mem_of_odd hker h1 (Odd.of_dvd_nat hy (orderOf_pow_dvd _))
  exact orderOf_dvd_of_pow_eq_one h2

theorem exists_mem_orderOf_dvd {X T B₀ B : Subgroup G} (hT : IsSylowTwoOf T X)
    (hB₀ : Lin2.IsHallTwoPrimeOf B₀ X)
    (hTQ : T ≤ pCoreOf 2 X ⊔ (T ⊓ Subgroup.normalizer (B₀ : Set G)))
    (hB : Lin2.IsHallTwoPrimeOf B X) {y : G} (hyX : y ∈ X) (hyodd : Odd (orderOf y)) :
    ∃ b ∈ B, orderOf y ∣ orderOf b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 X) := pCoreOf_isPGroup 2 X
  have : ((pCoreOf 2 X).subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 X g.2) _).mp hn⟩
  have : ((B₀.subgroupOf X).map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X))).Normal :=
    normal_map_of_hall hT hB₀ hTQ
  have hker : IsPGroup 2 (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X)).ker := by
    rw [QuotientGroup.ker_mk']
    exact hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 X)).symm
  obtain ⟨k, hk⟩ := hB₀.2.2
  have hidx : ((B₀.subgroupOf X).map (QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X))).index ∣
      2 ^ k := by
    have h := Subgroup.index_map_dvd (f := QuotientGroup.mk' ((pCoreOf 2 X).subgroupOf X))
      (B₀.subgroupOf X) (QuotientGroup.mk'_surjective _)
    rwa [← Subgroup.relIndex, hk] at h
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hidx
  have hcardB : Nat.card (B.subgroupOf X) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB.1).toEquiv
  have hcardB₀ : Nat.card (B₀.subgroupOf X) = Nat.card B₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀.1).toEquiv
  obtain ⟨b, hb, hdvd⟩ := exists_orderOf_dvd_of_map _ (QuotientGroup.mk'_surjective _) hker hi
    (by rw [hcardB]; exact hB.2.1) (by rw [hcardB, hcardB₀]; exact card_hall_eq hT hB₀ hB)
    (y := ⟨y, hyX⟩) (by rwa [← Subgroup.orderOf_coe])
  refine ⟨b, hb, ?_⟩
  rw [← Subgroup.orderOf_coe (⟨y, hyX⟩ : ↥X), ← Subgroup.orderOf_coe b] at hdvd
  exact hdvd

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
