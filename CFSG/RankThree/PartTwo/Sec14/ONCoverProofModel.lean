module

public import CFSG.RankThree.Native.ONTripleRed

public section

namespace CFSG.RankThree.PartTwo.Sec15.ONCoverCent

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree.Native.ONTriple CFSG.RankThree.PartTwo Subgroup
open scoped commutatorElement

theorem sV_mul_sY_ne : ∀ i < 3, sV 0 0 i * sY 0 ≠ sY 0 * sV 0 0 i := by
  decide

theorem commutatorElement_mul_mul {G : Type*} [Group G] {c d k k' : G} (hck : Commute c k)
    (hck' : Commute c k') (hdk : Commute d k) (hdk' : Commute d k') (hcd : Commute c d) :
    ⁅c * k, d * k'⁆ = ⁅k, k'⁆ := by
  have h1 : Commute c (k * (d * k') * k⁻¹) :=
    ((hck.mul_right (hcd.mul_right hck')).mul_right hck.inv_right)
  have h2 : Commute d (k * k' * k⁻¹ * k'⁻¹) :=
    ((hdk.mul_right hdk').mul_right hdk.inv_right).mul_right hdk'.inv_right
  calc ⁅c * k, d * k'⁆ = c * (k * (d * k') * k⁻¹) * c⁻¹ * (d * k')⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev, mul_assoc]
    _ = k * (d * k') * k⁻¹ * (d * k')⁻¹ := by rw [h1.eq, mul_inv_cancel_right]
    _ = d * (k * k' * k⁻¹ * k'⁻¹) * d⁻¹ := by
        rw [show k * (d * k') = d * (k * k') by rw [← mul_assoc, hdk.eq.symm, mul_assoc]]
        group
    _ = ⁅k, k'⁆ := by rw [h2.eq, mul_inv_cancel_right, commutatorElement_def]

theorem le_K0_of_isPerfect
    {X : Subgroup GM}
    [hXp : Group.IsPerfect X] (hX : X ≤ centralizer {xG 0}) : X ≤ K0G := by
  rw [← Subgroup.commutator_eq_self (H := X)]
  refine (Subgroup.commutator_mono hX hX).trans ?_
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨p, k, hk, rfl⟩ := mem_centralizer_x0_iff.1 ha
  obtain ⟨q, k', hk', rfl⟩ := mem_centralizer_x0_iff.1 hb
  have hxk : Commute (xG 0) k := (K0_comm hk).symm
  have hxk' : Commute (xG 0) k' := (K0_comm hk').symm
  rw [commutatorElement_mul_mul (hxk.pow_left p) (hxk'.pow_left p) (hxk.pow_left q)
    (hxk'.pow_left q) ((Commute.refl (xG 0)).pow_pow p q), commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hk hk') (inv_mem hk)) (inv_mem hk')

theorem eq_bot_of_le_centralizer_K0
    {T : Subgroup GM} (hT : IsPGroup 2 T)
    (hTK : T ≤ centralizer (K0G : Set GM)) (hx : xG 0 ∈ normalizer (T : Set GM)) : T = ⊥ := by
  have h0 : (0 : ℕ) < 2 := by norm_num
  have h00 : (0 : ℕ) < 3 := by norm_num
  set V := VG 0 0 h0 h00 with hV
  have hVK : V ≤ K0G := VG_le_K0 h0 h00
  have hyK : yG 0 ∈ K0G := yG_mem_K0 h0
  have hcomm : ∀ t ∈ T, ∀ k ∈ K0G, t * k = k * t := fun t ht k hk =>
    ((mem_centralizer_iff.mp (hTK ht)) k hk).symm
  have hTV : T ≤ normalizer (V : Set GM) := fun t ht =>
    mem_normalizer_of_comm fun v hv => hcomm t ht v (hVK hv)
  have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV, card_VG]; norm_num)
  have hS2 : IsPGroup 2 (T ⊔ V : Subgroup GM) := hT.to_sup_of_normal_right' hV2 hTV
  have hSpi : IsPiSubgroup (piOf 2) (T ⊔ V) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    intro p hp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hS2
    rw [hk] at hp
    exact (Nat.prime_dvd_prime_iff_eq p.2 Nat.prime_two).1 (p.2.dvd_of_dvd_pow hp)
  have hAS : AG 0 ≤ normalizer ((T ⊔ V : Subgroup GM) : Set GM) := by
    intro a ha
    have hcl : Subgroup.closure {xG 0, yG 0, zG} ≤
        normalizer (T : Set GM) ⊓ normalizer (V : Set GM) := by
      rw [closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨hx, AG_le_normalizer_VG h0 h00 (xG0_mem_AG 0)⟩
      · exact ⟨mem_normalizer_of_comm fun t ht => (hcomm t ht _ hyK).symm,
          AG_le_normalizer_VG h0 h00 (yG_mem_AG h0)⟩
      · exact ⟨mem_normalizer_of_comm fun v _ => zG_central v,
          mem_normalizer_of_comm fun v _ => zG_central v⟩
    obtain ⟨haT, haV⟩ := mem_inf.mp (hcl (XG_mem_closure h0 ha))
    rw [mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp haT,
      mem_normalizer_iff_map_conj_eq.mp haV]
  have hV4 : Nat.card V = 4 := by rw [hV, card_VG]
  rcases inv_two_subgroups h0 (T ⊔ V) hSpi hAS with hbot | ⟨l, hl, m, hm, hX⟩
  · exfalso
    have hle : V ≤ ⊥ := hbot ▸ le_sup_right
    rw [le_bot_iff] at hle
    rw [hle, card_bot] at hV4
    exact absurd hV4 (by norm_num)
  · have hcS : Nat.card (T ⊔ V : Subgroup GM) = 4 := by rw [hX, card_XG]
    have hSV : V = T ⊔ V := eq_of_le_of_card_ge le_sup_right (by rw [hcS, hV4])
    have hTV' : T ≤ V := hSV ▸ le_sup_left
    rw [eq_bot_iff]
    intro t ht
    rw [mem_bot]
    rcases mem_VG.1 (hTV' ht) with h1 | ⟨i, hi, rfl⟩
    · exact h1
    · exfalso
      have hc : (⟨vG 0 0 i, vG_mem_K0 h0 h00 hi⟩ : K0G) * ⟨yG 0, yG_mem_K0 h0⟩ =
          ⟨yG 0, yG_mem_K0 h0⟩ * ⟨vG 0 0 i, vG_mem_K0 h0 h00 hi⟩ :=
        Subtype.ext (hcomm _ ht _ hyK)
      have := congrArg actK hc
      rw [map_mul, map_mul, actK_yG h0, actK_vG h0 h00 hi] at this
      exact sV_mul_sY_ne i hi this

theorem eq_bot_of_le_centralizer
    {X T : Subgroup GM} {g : GM} (hg3 : g ^ 3 = 1)
    (hgz : g ∉ zpowers zG) (hXp : Group.IsPerfect X) (hXc : Nat.card X = 1080)
    (hXg : X ≤ centralizer {g}) (hT : IsPGroup 2 T) (hTX : T ≤ centralizer (X : Set GM))
    (hgT : g ∈ normalizer (T : Set GM)) : T = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hg1 : g ≠ 1 := fun h => hgz (h ▸ one_mem _)
  have hp : IsPGroup 3 (zpowers g) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hg3 hg1)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hgP : (MulAut.conj a).toMonoidHom g ∈ P0G := by
    rw [← P0Syl_coe, ← ha, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hP (mem_zpowers g))
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 hgP (conj_not_mem_zpowers hgz a)
  set n := a⁻¹ * wordN w with hn
  have hgn : n⁻¹ * g * n = xG 0 * zG ^ c := by
    rw [← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  set φ := (MulAut.conj n⁻¹).toMonoidHom with hφ
  have hφg : φ g = xG 0 * zG ^ c := by
    rw [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hgn]
  have hX'C : X.map φ ≤ centralizer {xG 0} := by
    have h1 : (centralizer {g}).map φ = centralizer {xG 0} := by
      rw [hφ, map_conj_centralizer, inv_inv, hgn, centralizer_mul_zpow]
    rw [← h1]
    exact map_mono hXg
  have hX'p : Group.IsPerfect (X.map φ) := Group.IsPerfect.map φ
  have hX'K : X.map φ = K0G := by
    refine eq_of_le_of_card_ge (le_K0_of_isPerfect hX'C) ?_
    rw [centralizer_x0_eq.2, hφ, card_map_of_injective (MulAut.conj n⁻¹).injective, hXc]
  have hT'K : T.map φ ≤ centralizer (K0G : Set GM) := by
    rw [← hX'K]
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hTX ht)) x hx]
  have hgT' : xG 0 * zG ^ c ∈ normalizer ((T.map φ : Subgroup GM) : Set GM) := by
    have h1 := Subgroup.map_equiv_normalizer_eq T (MulAut.conj n⁻¹)
    rw [← hφg, hφ, ← h1]
    exact mem_map_of_mem _ hgT
  have hzN : ∀ k : ℕ, zG ^ k ∈ normalizer ((T.map φ : Subgroup GM) : Set GM) := fun k =>
    pow_mem (mem_normalizer_of_comm fun v _ => zG_central v) k
  have hxT' : xG 0 ∈ normalizer ((T.map φ : Subgroup GM) : Set GM) := by
    have e : xG 0 = xG 0 * zG ^ c * (zG ^ c)⁻¹ := by group
    rw [e]
    exact mul_mem hgT' (inv_mem (hzN c))
  have hT' := eq_bot_of_le_centralizer_K0 (hT.map φ) hT'K hxT'
  rwa [map_eq_bot_iff_of_injective _ (MulAut.conj n⁻¹).injective] at hT'

end CFSG.RankThree.PartTwo.Sec15.ONCoverCent
