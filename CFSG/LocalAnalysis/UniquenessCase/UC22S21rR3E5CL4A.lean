module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.Lie.Suzuki
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint CFSG.Blueprint.EvenSource CFSG.LieType.Ree Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut coe_szFieldAut szFieldAut_D
  szFieldAut_injective)

theorem uc22r3e5c_eq_or_sq_of_orderOf_eq_three {H : Type*} [Group H] [Finite H]
    (hH : IsCyclic H) {x y : H} (hx : orderOf x = 3) (hy : orderOf y = 3) :
    y = x ∨ y = x ^ 2 := by
  letI := hH
  have hX : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hY : Nat.card (Subgroup.zpowers y) = 3 := by rw [Nat.card_zpowers, hy]
  have hEq : Subgroup.zpowers x = Subgroup.zpowers y :=
    IsCyclic.subgroup_eq_iff_card_eq.2 (by rw [hX, hY])
  have hy_mem : y ∈ Subgroup.zpowers x := by
    rw [hEq]; exact Subgroup.mem_zpowers y
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.1 hy_mem
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hpow : y = x ^ (z % 3) := by
    rw [← hz, zpow_eq_zpow_emod' z hx3]
    norm_num
  have hlt := Int.emod_lt_of_pos z (by norm_num : (0:ℤ) < 3)
  have hnon := Int.emod_nonneg z (by norm_num : (3:ℤ) ≠ 0)
  interval_cases h : z % 3
  · exfalso
    simp at hpow
    rw [hpow, orderOf_one] at hy
    omega
  · left; rw [hpow]; norm_num
  · right; rw [hpow]; norm_num

theorem uc22r3e5c_szFieldAut_map_torus {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (σ : K ≃+* K) :
    (suzukiT a K).map (szFieldAut a K σ).toMonoidHom = suzukiT a K := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hg
    change szFieldAut a K σ (suzukiDElt a K l) ∈ suzukiT a K
    rw [szFieldAut_D]
    exact suzukiDElt_mem_suzukiT a K _
  · rw [Subgroup.card_map_of_injective (szFieldAut a K σ).injective]

theorem uc22r3e5c_iterateFrobeniusEquiv_pow {K : Type} [Field K] [Finite K] [ExpChar K 2]
    (k j : ℕ) :
    (iterateFrobeniusEquiv K 2 k) ^ j = iterateFrobeniusEquiv K 2 (k * j) := by
  induction j with
  | zero => simp [RingAut.one_eq_refl]
  | succ j ih =>
      rw [pow_succ, ih]
      rw [show k * (j + 1) = k * j + k by ring]
      rw [iterateFrobeniusEquiv_add]
      refine RingEquiv.ext fun x => ?_
      rw [RingAut.mul_apply, RingEquiv.trans_apply]

theorem uc22r3e5c_iterateFrobeniusEquiv_pow_three {K : Type} [Field K] [Finite K]
    [ExpChar K 2] {m k : ℕ} (h3k : 3 * k = m) (hK : Nat.card K = 2 ^ m) :
    (iterateFrobeniusEquiv K 2 k) ^ 3 = 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [uc22r3e5c_iterateFrobeniusEquiv_pow, show k * 3 = m by omega]
  refine RingEquiv.ext fun x => ?_
  rw [iterateFrobeniusEquiv_def, RingAut.one_apply, ← hK, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

theorem uc22r3e5c_iterateFrobeniusEquiv_ne_one {K : Type} [Field K] [Finite K] [ExpChar K 2]
    {m k : ℕ} (hK : Nat.card K = 2 ^ m) (hk0 : 0 < k) (hkm : k < m) :
    iterateFrobeniusEquiv K 2 k ≠ 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  intro h
  have hfix : ∀ x : K, x ^ (2 ^ k) = x := by
    intro x
    have hx := congrArg (fun f : K ≃+* K => f x) h
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at hx
    exact hx
  have hunit : ∀ x : Kˣ, x ^ (2 ^ k - 1) = 1 := by
    intro x
    have hx : (x : K) ^ (2 ^ k) = (x : K) := hfix (x : K)
    rw [← Nat.sub_add_cancel (Nat.one_le_two_pow : 1 ≤ 2 ^ k), pow_succ] at hx
    have hx' : (x : K) ^ (2 ^ k - 1) * (x : K) = 1 * (x : K) := by
      rw [one_mul]; exact hx
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact mul_right_cancel₀ x.ne_zero hx'
  have hdvd : Fintype.card K - 1 ∣ 2 ^ k - 1 :=
    (FiniteField.forall_pow_eq_one_iff K (2 ^ k - 1)).mp hunit
  rw [← Nat.card_eq_fintype_card, hK] at hdvd
  have hpos : 0 < 2 ^ k - 1 := by
    have := Nat.one_lt_two_pow (n := k) (by omega : k ≠ 0)
    omega
  have hle : 2 ^ m - 1 ≤ 2 ^ k - 1 := Nat.le_of_dvd hpos hdvd
  have hlt : 2 ^ k - 1 < 2 ^ m - 1 :=
    tsub_lt_tsub_right_of_le (Nat.one_le_two_pow)
      (Nat.pow_lt_pow_right (by norm_num : 1 < 2) hkm)
  exact absurd hle (Nat.not_le.mpr hlt)

theorem uc22r3e5c_szFieldAut_iterateFrobenius_not_inner {a : ℕ} {K : Type} [Field K]
    [Finite K] [ExpChar K 2] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : ℕ} (hk0 : 0 < k) (hkm : k < 2 * a + 1) :
    szFieldAut a K (iterateFrobeniusEquiv K 2 k) ∉ inner (suzukiGroup a K) := by
  intro h
  have hφ1 : iterateFrobeniusEquiv K 2 k = 1 :=
    CFSG.RankThree.Automorphisms.eq_one_of_szFieldAut_mem_inner ha hK h
  exact uc22r3e5c_iterateFrobeniusEquiv_ne_one (m := 2 * a + 1) hK hk0 hkm hφ1

theorem uc22r3e5c_szFieldAut_iterateFrobenius_torus_pow {a : ℕ} {K : Type} [Field K]
    [Finite K] [ExpChar K 2] (k : ℕ) {c : suzukiGroup a K}
    (hc : c ∈ suzukiT a K) :
    szFieldAut a K (iterateFrobeniusEquiv K 2 k) c = c ^ (2 ^ k) := by
  obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hc
  change szFieldAut a K (iterateFrobeniusEquiv K 2 k) (suzukiDElt a K l) = _
  rw [szFieldAut_D]
  have hpow : suzukiDElt a K (l ^ (2 ^ k)) = (suzukiDElt a K l) ^ (2 ^ k) :=
    map_pow (uc22pwr1_szD a K) l (2 ^ k)
  rw [← hpow]
  congr 1

theorem uc22r3e5c_szFieldAut_iterateFrobenius_torus_pow_pow {a : ℕ} {K : Type} [Field K]
    [Finite K] [ExpChar K 2] (k j : ℕ) {c : suzukiGroup a K}
    (hc : c ∈ suzukiT a K) :
    ((szFieldAut a K (iterateFrobeniusEquiv K 2 k)) ^ j) c = c ^ ((2 ^ k) ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_pow,
        uc22r3e5c_szFieldAut_iterateFrobenius_torus_pow k hc]
      rw [← pow_mul, ← pow_succ']

theorem uc22r3e5c_congr_mem_inner_iff {S M : Type*} [Group S] [Group M] (ε : S ≃* M)
    (α : MulAut S) : MulAut.congr ε α ∈ inner M ↔ α ∈ inner S := by
  have h := CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr ε
  constructor
  · intro hα
    have hmem : MulAut.congr ε α ∈ (inner S).map (MulAut.congr ε).toMonoidHom := by
      rw [h]; exact hα
    obtain ⟨β, hβ, hβeq⟩ := Subgroup.mem_map.1 hmem
    rwa [← (MulAut.congr ε).injective hβeq]
  · intro hα
    rw [← h]
    exact Subgroup.mem_map_of_mem (MulAut.congr ε).toMonoidHom hα

theorem uc22r3e5c_transport_le_normalizer {S M : Type*} [Group S] [Group M]
    (ε : S ≃* M) {U C : Subgroup S} {U' : Subgroup M} (hU' : U' = U.map ε.toMonoidHom)
    (hC : C ≤ Subgroup.normalizer (U : Set S)) :
    C.map ε.toMonoidHom ≤ Subgroup.normalizer (U' : Set M) := by
  have h1 : C.map ε.toMonoidHom ≤
      (Subgroup.normalizer (U : Set S)).map ε.toMonoidHom := Subgroup.map_mono hC
  rw [Subgroup.map_equiv_normalizer_eq, ← hU'] at h1
  exact h1

theorem uc22r3e5c_transport_stable {S M : Type*} [Group S] [Group M]
    (ε : S ≃* M) {α : MulAut S} {β : MulAut M} (hβ : ∀ x : S, β (ε x) = ε (α x))
    {H : Subgroup S} (hH : H.map α.toMonoidHom = H) :
    (H.map ε.toMonoidHom).map β.toMonoidHom = H.map ε.toMonoidHom := by
  refine Classical.choice ⟨?_⟩
  have hcomp : β.toMonoidHom.comp ε.toMonoidHom = ε.toMonoidHom.comp α.toMonoidHom := by
    refine MonoidHom.ext fun x => ?_
    exact hβ x
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hH]

theorem uc22r3e5c_transport_pow_conclusion {S M : Type*} [Group S] [Group M]
    (ε : S ≃* M) {α : MulAut S} {β : MulAut M} (hβ : ∀ x : S, β (ε x) = ε (α x))
    {C : Subgroup S} {N : ℕ}
    (h : ∀ y ∈ C.map ε.toMonoidHom, β y = y ^ N) :
    ∀ c ∈ C, α c = c ^ N := by
  refine Classical.choice ⟨?_⟩
  intro c hc
  have hy : ε c ∈ C.map ε.toMonoidHom := Subgroup.mem_map.2 ⟨c, hc, rfl⟩
  have h1 := h (ε c) hy
  rw [hβ c, ← map_pow] at h1
  exact ε.injective h1

theorem uc22r3e5c_map_pow_eq_of_map_eq {G : Type*} [Group G] (e : MulAut G)
    {H : Subgroup G} (h : H.map e.toMonoidHom = H) (j : ℕ) :
    H.map (e ^ j).toMonoidHom = H := by
  refine Classical.choice ⟨?_⟩
  induction j with
  | zero => exact Subgroup.map_id H
  | succ j ih =>
      change H.map ((e ^ j).toMonoidHom.comp e.toMonoidHom) = H
      rw [← Subgroup.map_map, h, ih]

theorem uc22r3e5c_map_mul_eq_of_map_eq {G : Type*} [Group G] (e f : MulAut G)
    {H : Subgroup G} (he : H.map e.toMonoidHom = H) (hf : H.map f.toMonoidHom = H) :
    H.map (e * f).toMonoidHom = H := by
  refine Classical.choice ⟨?_⟩
  change H.map (e.toMonoidHom.comp f.toMonoidHom) = H
  rw [← Subgroup.map_map, hf, he]

theorem uc22r3e5c_inv_comp_self {G : Type*} [Group G] (e : MulAut G) :
    (e⁻¹).toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
  refine Classical.choice ⟨?_⟩
  refine MonoidHom.ext fun y => ?_
  change e⁻¹ (e y) = y
  simp

theorem uc22r3e5c_conj_inv_mul_conj_map_of_map {G : Type*} [Group G] (γ α : MulAut G)
    {K L : Subgroup G} (hγ : K.map γ.toMonoidHom = L) (hα : L.map α.toMonoidHom = L) :
    K.map ((γ⁻¹ * α * γ).toMonoidHom) = K := by
  refine Classical.choice ⟨?_⟩
  have hγinv : L.map (γ⁻¹).toMonoidHom = K := by
    rw [← hγ, Subgroup.map_map, uc22r3e5c_inv_comp_self, Subgroup.map_id]
  change K.map ((γ⁻¹).toMonoidHom.comp (α.toMonoidHom.comp γ.toMonoidHom)) = K
  rw [← Subgroup.map_map, ← Subgroup.map_map, hγ, hα, hγinv]

theorem uc22r3e5c_conj_pow_three {G : Type*} [Group G] (γ α : MulAut G)
    (hα : α ^ 3 = 1) : (γ⁻¹ * α * γ) ^ 3 = 1 := by
  refine Classical.choice ⟨?_⟩
  calc (γ⁻¹ * α * γ) ^ 3
      = γ⁻¹ * α * γ * (γ⁻¹ * α * γ) * (γ⁻¹ * α * γ) := by
        rw [pow_succ, pow_succ, pow_one]
    _ = γ⁻¹ * α ^ 3 * γ := by
        rw [pow_succ, pow_succ, pow_one]
        group
    _ = 1 := by rw [hα]; group

theorem uc22r3e5c_conj_not_inner {G : Type*} [Group G] (γ α : MulAut G)
    (hα : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G) :
    γ⁻¹ * α * γ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
  intro h
  apply hα
  have hαeq : α = γ * (γ⁻¹ * α * γ) * γ⁻¹ := by group
  rw [hαeq]
  exact (inferInstance :
    (CFSG.ComponentClassification.OuterAutomorphisms.inner G).Normal).conj_mem
      (γ⁻¹ * α * γ) h γ

theorem uc22r3e5c_exists_conj_pow_of_not_inner {G : Type*} [Group G] [Finite G]
    {β Φ : MulAut G} (hβ3 : β ^ 3 = 1) (hΦ3 : Φ ^ 3 = 1)
    (hβni : β ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G)
    (hΦni : Φ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner G)
    (hcyc : IsCyclic (Outer G)) (h3dvd : 3 ∣ Nat.card (Outer G)) :
    ∃ j ∈ ({1, 2} : Finset ℕ), ∃ x : G, β = Φ ^ j * MulAut.conj x := by
  let q : MulAut G →* Outer G := QuotientGroup.mk' (inner G)
  have hqβ3 : (q β) ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hqΦ3 : (q Φ) ^ 3 = 1 := by rw [← map_pow, hΦ3, map_one]
  have hqβne : q β ≠ 1 := fun h => hβni ((QuotientGroup.eq_one_iff β).1 h)
  have hqΦne : q Φ ≠ 1 := fun h => hΦni ((QuotientGroup.eq_one_iff Φ).1 h)
  have hβord : orderOf (q β) = 3 := orderOf_eq_prime hqβ3 hqβne
  have hΦord : orderOf (q Φ) = 3 := orderOf_eq_prime hqΦ3 hqΦne
  have hcases : q β = q Φ ∨ q β = (q Φ) ^ 2 :=
    uc22r3e5c_eq_or_sq_of_orderOf_eq_three hcyc hΦord hβord
  have hj : ∃ j ∈ ({1, 2} : Finset ℕ), q β = q (Φ ^ j) := by
    rcases hcases with h | h
    · exact ⟨1, by simp, by simpa using h⟩
    · exact ⟨2, by simp, by simpa using h⟩
  obtain ⟨j, hjmem, hqj⟩ := hj
  have hq1 : q ((Φ ^ j)⁻¹ * β) = 1 := by
    rw [map_mul, map_inv, hqj, inv_mul_cancel]
  have hker : (Φ ^ j)⁻¹ * β ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
    refine (QuotientGroup.eq_one_iff ((Φ ^ j)⁻¹ * β)).1 ?_
    change q ((Φ ^ j)⁻¹ * β) = 1
    exact hq1
  obtain ⟨x, hx⟩ := hker
  refine ⟨j, hjmem, x, ?_⟩
  calc β = Φ ^ j * ((Φ ^ j)⁻¹ * β) := by group
    _ = Φ ^ j * MulAut.conj x := by rw [← hx]

theorem uc22r3e5c_inv_pow_map_eq_of_map_eq {G : Type*} [Group G] (e : MulAut G)
    {H : Subgroup G} (he : H.map e.toMonoidHom = H) (he3 : e ^ 3 = 1)
    {j : ℕ} (hj : j = 1 ∨ j = 2) :
    H.map ((e ^ j)⁻¹).toMonoidHom = H := by
  refine Classical.choice ⟨?_⟩
  have he1 : e ^ 2 = e⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, he3]
  have he2 : (e ^ 2)⁻¹ = e := by
    rw [← mul_eq_one_iff_inv_eq]
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, he3]
  rcases hj with rfl | rfl
  · rw [pow_one, ← he1]
    exact uc22r3e5c_map_pow_eq_of_map_eq e he 2
  · rw [he2]
    exact he

end CFSG.LocalAnalysis.UniquenessCase.UC22
