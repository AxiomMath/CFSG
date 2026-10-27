module

public import CFSG.Blueprint.Catalog
import CFSG.RankThree.PartTwo.KFacts.AutSzOrderThree
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG.SignalizerFunctorTheorem.NearModels.Suzuki (szFieldAut szFieldAut_D szFieldAut_injective)
open CFSG.LieType.Ree (suzukiDElt suzukiDElt_one suzukiDElt_mul suzukiDElt_inj)
open CFSG.RankThree.PartTwo.KFacts
  (IsInnerAut isField_sz_of_pow_three_eq_one not_three_dvd_card_suzukiGroup)

private theorem eq_one_of_pow_succ_eq {G : Type*} [Group G] {s j : ℕ} (hs : s = 3 * j + 1) {g : G}
    (hfix : g ^ (s + 1) = g) (hN : g ^ (s * (s + 3) + 3) = 1) : g = 1 := by
  have h1 : g ^ s = 1 := by
    have h : g ^ s * g = 1 * g := by rw [one_mul, ← pow_succ]; exact hfix
    exact mul_right_cancel h
  have h3 : g ^ 3 = 1 := by
    rw [pow_add, pow_mul, h1, one_pow, one_mul] at hN
    exact hN
  have hgs : g ^ s = g := by
    rw [hs, pow_succ, pow_mul, h3, one_pow, one_mul]
  exact hgs.symm.trans h1

private theorem two_pow_mod_three_of_odd {m : ℕ} (hm : m % 2 = 1) : 2 ^ m % 3 = 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = 2 * k + 1 := ⟨m / 2, by omega⟩
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

section Cert113


private theorem exists_fpf_cyclic_suzuki {a : ℕ} {K : Type} [Field K] (ha : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (α : MulAut (CFSG.Blueprint.suzukiGroup a K))
    (hα : orderOf α = 3) :
    ∃ F : Subgroup (CFSG.Blueprint.suzukiGroup a K), IsCyclic F ∧ (∀ x ∈ F, α x ∈ F) ∧
      (∀ x ∈ F, α x = x → x = 1) ∧
      ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ Nat.card F = 4 ^ m + 2 ^ m + 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα3 : α ^ 3 = 1 := hα ▸ pow_orderOf_eq_one α
  have hnot : ¬ IsInnerAut α := by
    rintro ⟨y, hy⟩
    have hmem : α ∈ (MulAut.conj : CFSG.Blueprint.suzukiGroup a K →*
        MulAut (CFSG.Blueprint.suzukiGroup a K)).range := ⟨y, hy⟩
    have h3 : 3 ∣ Nat.card (MulAut.conj : CFSG.Blueprint.suzukiGroup a K →*
        MulAut (CFSG.Blueprint.suzukiGroup a K)).range := by
      have h := orderOf_dvd_natCard (⟨α, hmem⟩ : (MulAut.conj :
        CFSG.Blueprint.suzukiGroup a K →* MulAut (CFSG.Blueprint.suzukiGroup a K)).range)
      rwa [Subgroup.orderOf_mk, hα] at h
    exact not_three_dvd_card_suzukiGroup hK (h3.trans (Subgroup.card_range_dvd _))
  obtain ⟨φ, hφ, hφ1, d, hd, hαd⟩ := isField_sz_of_pow_three_eq_one (by omega) hK hα3 hnot
  obtain ⟨σ, rfl⟩ : φ ∈ (szFieldAut a K).range := hφ
  obtain ⟨g, rfl⟩ : d ∈ (MulAut.conj : CFSG.Blueprint.suzukiGroup a K →*
      MulAut (CFSG.Blueprint.suzukiGroup a K)).range := hd
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    exact hφ1 (map_one _)
  have hφ3 : szFieldAut a K σ ^ 3 = 1 := by
    have h := hα3
    rw [hαd, conj_pow] at h
    calc szFieldAut a K σ ^ 3
        = (MulAut.conj g)⁻¹ * (MulAut.conj g * szFieldAut a K σ ^ 3 * (MulAut.conj g)⁻¹)
          * MulAut.conj g := by group
      _ = 1 := by rw [h]; group
  have hσ3 : σ ^ 3 = 1 := by
    apply szFieldAut_injective (a := a) (K := K)
    rw [map_pow, map_one]
    exact hφ3
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  obtain ⟨hdvd, hcardF⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf Nat.prime_two
      (by omega) hK σ hσo
  obtain ⟨m, hm⟩ := hdvd
  have hmdiv : (2 * a + 1) / 3 = m := by omega
  rw [hmdiv] at hcardF
  have hKcard : Nat.card K = (2 ^ m) ^ 3 := by rw [hK, hm, pow_mul']
  have hodd : m % 2 = 1 := by omega
  have hm3 : 3 ≤ m := by omega
  have hmod : 2 ^ m % 3 = 2 := two_pow_mod_three_of_odd hodd
  obtain ⟨s, hs⟩ : ∃ s, 2 ^ m = s + 1 :=
    ⟨2 ^ m - 1, by have := pow_pos (by norm_num : (0 : ℕ) < 2) m; omega⟩
  have hs3 : s = 3 * (s / 3) + 1 := by omega
  have h4 : (4 : ℕ) ^ m = (2 ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hN : 4 ^ m + 2 ^ m + 1 = s * (s + 3) + 3 := by
    rw [h4, hs]; ring
  have hunits : Nat.card Kˣ = s * (s * (s + 3) + 3) := by
    have h1 := Nat.card_eq_card_units_add_one K
    have h2 : Nat.card K = s * (s * (s + 3) + 3) + 1 := by rw [hKcard, hs]; ring
    exact Nat.add_right_cancel (h1.symm.trans h2)
  have hdvdN : 4 ^ m + 2 ^ m + 1 ∣ Nat.card Kˣ := ⟨s, by rw [hN, hunits]; ring⟩
  obtain ⟨μ, hμdef⟩ : ∃ μ : Subgroup Kˣ,
      μ = (powMonoidHom (4 ^ m + 2 ^ m + 1) : Kˣ →* Kˣ).ker := ⟨_, rfl⟩
  have hμmem : ∀ l : Kˣ, l ∈ μ ↔ l ^ (4 ^ m + 2 ^ m + 1) = 1 := fun l => by
    rw [hμdef]; exact MonoidHom.mem_ker
  have hμcard : Nat.card μ = 4 ^ m + 2 ^ m + 1 := by
    rw [hμdef, IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right hdvdN]
  obtain ⟨D, hD⟩ : ∃ D : Kˣ →* CFSG.Blueprint.suzukiGroup a K,
      ∀ l : Kˣ, D l = suzukiDElt a K l :=
    ⟨{ toFun := fun l => suzukiDElt a K l
       map_one' := suzukiDElt_one
       map_mul' := fun l l' => (suzukiDElt_mul l l').symm }, fun l => rfl⟩
  have hDinj : Function.Injective D := by
    intro l l' h
    rw [hD, hD] at h
    exact (suzukiDElt_inj hK).1 h
  obtain ⟨F₀, hF₀⟩ : ∃ F₀ : Subgroup (CFSG.Blueprint.suzukiGroup a K), F₀ = μ.map D :=
    ⟨_, rfl⟩
  have hF₀mem : ∀ y : CFSG.Blueprint.suzukiGroup a K, y ∈ F₀ ↔ ∃ l ∈ μ, D l = y := by
    intro y
    rw [hF₀]
    exact Subgroup.mem_map
  have hF₀card : Nat.card F₀ = 4 ^ m + 2 ^ m + 1 := by
    rw [hF₀, Subgroup.card_map_of_injective hDinj, hμcard]
  have hF₀cyc : IsCyclic F₀ := by
    rw [hF₀]
    exact isCyclic_of_surjective (Subgroup.equivMapOfInjective μ D hDinj)
      (Subgroup.equivMapOfInjective μ D hDinj).surjective
  have hszD : ∀ l : Kˣ, szFieldAut a K σ (D l) = D (Units.map (σ : K →* K) l) := by
    intro l
    rw [hD, hD]
    exact szFieldAut_D σ l
  have hΦF₀ : ∀ y ∈ F₀, szFieldAut a K σ y ∈ F₀ := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := (hF₀mem y).1 hy
    have hl' : l ^ (4 ^ m + 2 ^ m + 1) = 1 := (hμmem l).1 hl
    rw [hszD]
    refine (hF₀mem _).2 ⟨Units.map (σ : K →* K) l, (hμmem _).2 ?_, rfl⟩
    rw [← map_pow, hl', map_one]
  have hfixpow : ∀ x : K, σ x = x → x ^ (2 ^ m) = x := by
    intro x hx
    letI : Fintype (RingHom.eqLocusField (RingEquiv.toRingHom σ) (RingHom.id K)) :=
      Fintype.ofFinite _
    have hxF : x ∈ RingHom.eqLocusField (RingEquiv.toRingHom σ) (RingHom.id K) := hx
    have hp := FiniteField.pow_card
      (⟨x, hxF⟩ : RingHom.eqLocusField (RingEquiv.toRingHom σ) (RingHom.id K))
    rw [← Nat.card_eq_fintype_card, hcardF] at hp
    exact congrArg Subtype.val hp
  have hfpf₀ : ∀ y ∈ F₀, szFieldAut a K σ y = y → y = 1 := by
    intro y hy hfix
    obtain ⟨l, hl, rfl⟩ := (hF₀mem y).1 hy
    rw [hszD] at hfix
    have hl2 : Units.map (σ : K →* K) l = l := hDinj hfix
    have hval : σ (l : K) = (l : K) := congrArg Units.val hl2
    have hlpow : l ^ (2 ^ m) = l := Units.ext (by simpa using hfixpow _ hval)
    have hN' : l ^ (s * (s + 3) + 3) = 1 := by
      rw [← hN]
      exact (hμmem l).1 hl
    have hs1 : l ^ (s + 1) = l := by
      rw [← hs]
      exact hlpow
    rw [eq_one_of_pow_succ_eq hs3 hs1 hN', map_one]
  have hkey : ∀ y : CFSG.Blueprint.suzukiGroup a K,
      α (MulAut.conj g y) = MulAut.conj g (szFieldAut a K σ y) := by
    intro y
    rw [hαd, MulAut.mul_apply, MulAut.inv_apply_self, MulAut.mul_apply]
  refine ⟨F₀.map (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, m, Nat.odd_iff.mpr hodd, hm3, ?_⟩
  · exact isCyclic_of_surjective
      (Subgroup.equivMapOfInjective F₀ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
      (Subgroup.equivMapOfInjective F₀ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).surjective
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    show α (MulAut.conj g y) ∈ F₀.map (MulAut.conj g).toMonoidHom
    rw [hkey]
    exact Subgroup.mem_map.2 ⟨_, hΦF₀ y hy, rfl⟩
  · intro x hx hfix
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    have hfix' : α (MulAut.conj g y) = MulAut.conj g y := hfix
    rw [hkey] at hfix'
    have hφy : szFieldAut a K σ y = y := (MulAut.conj g).injective hfix'
    show MulAut.conj g y = 1
    rw [hfpf₀ y hy hφy, map_one]
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective, hF₀card]

theorem exists_fpf_cyclic_of_order_three {T : Type} [Group T] {n : ℕ}
    (hSz : CFSG.Blueprint.SuzukiModel T 2 n) (α : MulAut T) (hα : orderOf α = 3) :
    ∃ F : Subgroup T, IsCyclic F ∧ (∀ x ∈ F, α x ∈ F) ∧ (∀ x ∈ F, α x = x → x = 1) ∧
      (Nat.card F = 13 ∨ ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ Nat.card F = 4 ^ m + 2 ^ m + 1) := by
  have hSz0 := hSz
  obtain ⟨-, a, ha, K, _, _, hn, hK, ⟨e⟩⟩ := hSz0
  rcases Nat.lt_or_ge a 2 with ha2 | ha2
  · obtain rfl : a = 1 := by omega
    obtain rfl : n = 3 := by omega
    obtain ⟨X, hX, hinv, hfree⟩ :=
      CFSG.RankThree.PartTwo.KFacts.KP7.exists_thirteen_fixedPointFree_of_suzukiModel hSz α hα
    haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
    exact ⟨X, isCyclic_of_prime_card hX, hinv, hfree, Or.inl hX⟩
  · have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hn]
    obtain ⟨F₀, hcyc, hinv, hfpf, m, hodd, hm3, hcard⟩ :=
      exists_fpf_cyclic_suzuki ha2 hK' (MulAut.congr e α) (by rw [MulEquiv.orderOf_eq, hα])
    refine ⟨F₀.map e.symm.toMonoidHom, ?_, ?_, ?_, Or.inr ⟨m, hodd, hm3, ?_⟩⟩
    · exact isCyclic_of_surjective
        (Subgroup.equivMapOfInjective F₀ e.symm.toMonoidHom e.symm.injective)
        (Subgroup.equivMapOfInjective F₀ e.symm.toMonoidHom e.symm.injective).surjective
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      refine Subgroup.mem_map.2 ⟨MulAut.congr e α y, hinv y hy, ?_⟩
      simp [MulAut.congr_apply]
    · intro x hx hfix
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      have hfix' : α (e.symm y) = e.symm y := hfix
      have h1 : MulAut.congr e α y = y := by
        simp [MulAut.congr_apply, hfix']
      have h2 : y = 1 := hfpf y hy h1
      show e.symm y = 1
      rw [h2, map_one]
    · rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective, hcard]

end Cert113

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
