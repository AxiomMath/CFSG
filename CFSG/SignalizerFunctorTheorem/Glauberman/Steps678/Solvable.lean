module

public import CFSG.SignalizerFunctorTheorem.Glauberman.External
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.PrimeCore
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Hyperplane

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.Glauberman.Steps678

variable {G : Type*} [Group G] [Finite G]

theorem eq_bot_of_primeCoreIn_eq_bot {q : ℕ} (hq : q.Prime) {L : Subgroup G}
    (hL : Group.IsSolvable L) (h1 : primeCoreIn ({q}ᶜ : Set ℕ) L = ⊥)
    (h2 : primeCoreIn {q} L = ⊥) : L = ⊥ := by
  by_contra hne
  have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hne
  have hc1 : primeSetCore (GroupType := L) ({q}ᶜ : Set ℕ) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1
  have hc2 : primeSetCore (GroupType := L) {q} = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h2
  exact solvable_prime_core_nontrivial_of_complement_core_trivial q hq hc1 hc2

theorem centralizer_primeCoreIn_le {q : ℕ} (hq : q.Prime) {L : Subgroup G}
    (hL : Group.IsSolvable L) (hcore : primeCoreIn ({q}ᶜ : Set ℕ) L = ⊥) :
    L ⊓ Subgroup.centralizer (primeCoreIn {q} L : Set G) ≤ primeCoreIn {q} L := by
  have hc : primeSetCore (GroupType := L) ({q}ᶜ : Set ℕ) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp hcore
  have h := solvable_prime_core_self_centralizing (GroupType := L) q hq hc
  rintro x ⟨hxL, hxC⟩
  have hx' : (⟨x, hxL⟩ : L) ∈
      Subgroup.centralizer (primeSetCore (GroupType := L) {q} : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG : (y : G) ∈ primeCoreIn {q} L := Subgroup.mem_map_of_mem L.subtype hy
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) y hyG)
  exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, h hx', rfl⟩

theorem le_primeCoreIn_of_sylow_normalizes {q : ℕ} (hq : q.Prime) {L U P : Subgroup G}
    (hL : Group.IsSolvable L) (hUL : U ≤ L) (hU : Nat.Coprime q (Nat.card U))
    (hP : IsSylowOf q P L) (hPU : P ≤ Subgroup.normalizer (U : Set G)) :
    U ≤ primeCoreIn ({q}ᶜ : Set ℕ) L := by
  obtain ⟨sylow, rfl⟩ := hP
  have hcop : Nat.Coprime q (Nat.card (U.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUL).toEquiv]
    exact hU
  have hnorm : (sylow : Subgroup L) ≤
      Subgroup.normalizer ((U.subgroupOf L : Subgroup L) : Set L) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have hsP : (s : G) ∈ (sylow : Subgroup L).map L.subtype := Subgroup.mem_map_of_mem L.subtype hs
    exact Subgroup.mem_normalizer_iff.mp (hPU hsP) (u : G)
  have h := solvable_sylow_normalized_complement_le_core (GroupType := L) q hq sylow
    (U.subgroupOf L) hcop hnorm
  have h2 := Subgroup.map_mono (f := L.subtype) h
  rw [Subgroup.map_subgroupOf_eq_of_le hUL] at h2
  exact h2

theorem pPrimeCore_eq_primeSetCore {q : ℕ} (hq : q.Prime) (K : Type*) [Group K] [Finite K] :
    CFSG.pPrimeCore q K = primeSetCore (GroupType := K) ({q}ᶜ : Set ℕ) := by
  apply le_antisymm
  · refine sSup_le ?_
    rintro N ⟨hN, hc⟩
    exact prime_set_core_contains _ N hN
      ((prime_supported_complement_singleton_iff_coprime q hq _).mpr hc)
  · unfold primeSetCore
    refine iSup₂_le fun N hN => ?_
    exact le_sSup ⟨hN.1, (prime_supported_complement_singleton_iff_coprime q hq _).mp hN.2⟩

theorem primeCoreIn_inf_centralizer_le {q : ℕ} (hq : q.Prime) {L P : Subgroup G}
    (hL : Group.IsSolvable L) (hPL : P ≤ L) (hP : IsPGroup q P) :
    primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G)) ≤
      primeCoreIn ({q}ᶜ : Set ℕ) L := by
  have : Fact q.Prime := ⟨hq⟩
  have hR : IsPGroup q (P.subgroupOf L) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  have hBG : (CFSG.pPrimeCore q (Subgroup.centralizer ((P.subgroupOf L : Subgroup L) : Set L))).map
      (Subgroup.centralizer ((P.subgroupOf L : Subgroup L) : Set L)).subtype ≤
        CFSG.pPrimeCore q L :=
    CFSG.pPrimeCore_map_centralizer_le_pPrimeCore_of_solvable hL q (P.subgroupOf L) hR
  have hXD : primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G)) ≤
      L ⊓ Subgroup.centralizer (P : Set G) := primeCoreIn_le _ _
  have hXnorm : L ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer
      (primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G)) : Set G) :=
    le_normalizer_primeCoreIn _ Subgroup.le_normalizer
  have hXL : primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G)) ≤ L :=
    hXD.trans inf_le_left
  have hX'C : (primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G))).subgroupOf L ≤
      Subgroup.centralizer ((P.subgroupOf L : Subgroup L) : Set L) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hxX : (x : G) ∈ primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G)) := hx
    have hxC : (x : G) ∈ Subgroup.centralizer (P : Set G) := (hXD hxX).2
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxC) (r : G) (show (r : G) ∈ P from hr))
  have hYnormal : (((primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G))).subgroupOf
      L).subgroupOf (Subgroup.centralizer ((P.subgroupOf L : Subgroup L) : Set L))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgD : ((g : L) : G) ∈ L ⊓ Subgroup.centralizer (P : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨(g : L).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp g.2) ⟨y, hPL hy⟩ hy)
    have hn' : ((n : L) : G) ∈
        primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G)) := hn
    exact (Subgroup.mem_normalizer_iff.mp (hXnorm hgD) _).mp hn'
  have hYcop : Nat.Coprime q (Nat.card
      (((primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G))).subgroupOf
        L).subgroupOf (Subgroup.centralizer ((P.subgroupOf L : Subgroup L) : Set L)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX'C).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXL).toEquiv]
    exact coprime_primeCoreIn hq _
  have hYle : ((primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.centralizer (P : Set G))).subgroupOf
      L).subgroupOf (Subgroup.centralizer ((P.subgroupOf L : Subgroup L) : Set L)) ≤
        CFSG.pPrimeCore q (Subgroup.centralizer ((P.subgroupOf L : Subgroup L) : Set L)) :=
    le_sSup ⟨hYnormal, hYcop⟩
  have h2 := Subgroup.map_mono (f := (Subgroup.centralizer
    ((P.subgroupOf L : Subgroup L) : Set L)).subtype) hYle
  rw [Subgroup.map_subgroupOf_eq_of_le hX'C] at h2
  have h3 := h2.trans hBG
  rw [pPrimeCore_eq_primeSetCore hq L] at h3
  have h4 := Subgroup.map_mono (f := L.subtype) h3
  rw [Subgroup.map_subgroupOf_eq_of_le hXL] at h4
  exact h4

theorem primeCoreIn_inf_normalizer_le {q : ℕ} (hq : q.Prime) {L P : Subgroup G}
    (hL : Group.IsSolvable L) (hPL : P ≤ L) (hP : IsPGroup q P) :
    primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) ≤
      primeCoreIn ({q}ᶜ : Set ℕ) L := by
  have : Fact q.Prime := ⟨hq⟩
  have hXN : primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) ≤
      L ⊓ Subgroup.normalizer (P : Set G) := primeCoreIn_le _ _
  have hXnorm : L ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer
      (primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) : Set G) :=
    le_normalizer_primeCoreIn _ Subgroup.le_normalizer
  have hXcop : Nat.Coprime q (Nat.card
      (primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)))) :=
    coprime_primeCoreIn hq _
  have hXC : primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyN : y ∈ L ⊓ Subgroup.normalizer (P : Set G) := ⟨hPL hy, Subgroup.le_normalizer hy⟩
    have hxN : x ∈ Subgroup.normalizer (P : Set G) := (hXN hx).2
    have h1 : x * y * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hxN y).mp hy
    have h2 : y * x⁻¹ * y⁻¹ ∈
        primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) :=
      (Subgroup.mem_normalizer_iff.mp (hXnorm hyN) x⁻¹).mp (Subgroup.inv_mem _ hx)
    have h3 : x * y * x⁻¹ * y⁻¹ ∈
        primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) := by
      have := Subgroup.mul_mem _ hx h2
      simpa [mul_assoc] using this
    have h4 : x * y * x⁻¹ * y⁻¹ ∈ P := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hy)
    have hdisj : Disjoint
        (primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G))) P := by
      apply Subgroup.disjoint_of_coprime_natCard
      obtain ⟨n, hn⟩ := hP.exists_card_eq
      rw [hn]
      exact hXcop.symm.pow_right n
    have h5 : x * y * x⁻¹ * y⁻¹ = 1 := by
      have hmem : x * y * x⁻¹ * y⁻¹ ∈
          primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) ⊓ P := ⟨h3, h4⟩
      rw [hdisj.eq_bot] at hmem
      simpa using hmem
    calc y * x = x * y * x⁻¹ * y⁻¹ * (y * x) := by rw [h5, one_mul]
      _ = x * y := by group
  have hXD : primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) ≤
      L ⊓ Subgroup.centralizer (P : Set G) := le_inf (hXN.trans inf_le_left) hXC
  have hDN : L ⊓ Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer
      (primeCoreIn ({q}ᶜ : Set ℕ) (L ⊓ Subgroup.normalizer (P : Set G)) : Set G) :=
    (inf_le_inf_left L (Subgroup.centralizer_le_normalizer _)).trans hXnorm
  exact (le_primeCoreIn_compl hq hXD hDN hXcop).trans (primeCoreIn_inf_centralizer_le hq hL hPL hP)

theorem map_eq_one_of_mem_pGroup {q : ℕ} (hq : q.Prime) {K L : Type*} [Group K] [Group L]
    {O : Subgroup L} (hO : IsPGroup q O) (f : K →* L) {k : K} (hfk : f k ∈ O)
    (hk : Nat.Coprime q (orderOf k)) : f k = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_orderOf.mp hO ⟨f k, hfk⟩
  have h1 : orderOf (f k) = q ^ n := by
    rw [← hn]
    exact Subgroup.orderOf_coe ⟨f k, hfk⟩
  have h2 : q ^ n ∣ orderOf k := by
    rw [← h1]
    exact orderOf_map_dvd f k
  have h3 : q ^ n = 1 := (Nat.Coprime.pow_left n hk).eq_one_of_dvd h2
  rw [h3] at h1
  exact orderOf_eq_one_iff.mp h1

omit [Finite G] in
theorem orderOf_dvd_card_of_mem {W : Subgroup G} {g : G} (hg : g ∈ W) :
    orderOf g ∣ Nat.card W := by
  have h := orderOf_dvd_natCard (⟨g, hg⟩ : W)
  rwa [Subgroup.orderOf_mk] at h

theorem exists_lift_centralizer {q : ℕ} (hq : q.Prime) {K : Type*} [Group K] [Finite K]
    (N : Subgroup K) [N.Normal] (hN : Nat.Coprime q (Nat.card N)) {P : Subgroup K}
    (hP : IsPGroup q P) {cbar : K ⧸ N} (hcbar : ∀ y ∈ P, (y : K ⧸ N) * cbar = cbar * (y : K ⧸ N)) :
    ∃ c : K, (c : K ⧸ N) = cbar ∧ ∀ y ∈ P, y * c = c * y := by
  have : Fact q.Prime := ⟨hq⟩
  let α := ↥((QuotientGroup.mk' N) ⁻¹' ({cbar} : Set (K ⧸ N)))
  have hmem : ∀ (y : P) (c : α), (y : K) * c.1 * (y : K)⁻¹ ∈
      (QuotientGroup.mk' N) ⁻¹' ({cbar} : Set (K ⧸ N)) := by
    intro y c
    have h1 := hcbar (y : K) y.2
    have h2 : ((c.1 : K) : K ⧸ N) = cbar := c.2
    show (((y : K) * c.1 * (y : K)⁻¹ : K) : K ⧸ N) = cbar
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h2, h1]
    group
  let _ : MulAction P α :=
    { smul := fun y c => ⟨(y : K) * c.1 * (y : K)⁻¹, hmem y c⟩
      one_smul := fun c => by
        apply Subtype.ext
        change (1 : K) * c.1 * (1 : K)⁻¹ = c.1
        simp
      mul_smul := fun y₁ y₂ c => by
        apply Subtype.ext
        change ((y₁ * y₂ : P) : K) * c.1 * ((y₁ * y₂ : P) : K)⁻¹ =
          (y₁ : K) * ((y₂ : K) * c.1 * (y₂ : K)⁻¹) * (y₁ : K)⁻¹
        simp [mul_assoc] }
  have hcard : Nat.card α = Nat.card N := by
    have h := Nat.card_congr ((QuotientGroup.mk' N).fiberEquivKerOfSurjective
      (QuotientGroup.mk'_surjective N) cbar)
    rw [QuotientGroup.ker_mk'] at h
    exact h
  have hndvd : ¬ q ∣ Nat.card α := by
    rw [hcard]
    exact hq.coprime_iff_not_dvd.mp hN
  obtain ⟨c, hc⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card α hndvd
  refine ⟨c.1, c.2, fun y hy => ?_⟩
  have h := congrArg Subtype.val (hc (⟨y, hy⟩ : P))
  change y * c.1 * y⁻¹ = c.1 at h
  exact mul_inv_eq_iff_eq_mul.mp h

theorem le_primeCoreIn_of_commutators {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {A H U : Subgroup G} (hA : IsElemAbelian p A) (hA2 : p ^ 2 ≤ Nat.card A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) (hH : Group.IsSolvable H)
    (hcop : Nat.Coprime p (Nat.card H)) (hUH : U ≤ H) (hU : Nat.Coprime q (Nat.card U))
    (hcomm : ∀ B ∈ Coprime.hyperplanes p A,
      Nat.Coprime q (Nat.card (⁅U, H ⊓ Subgroup.centralizer (B : Set G)⁆ : Subgroup G))) :
    U ≤ primeCoreIn ({q}ᶜ : Set ℕ) H := by
  have : Fact q.Prime := ⟨hq⟩
  let N : Subgroup H := primeSetCore (GroupType := H) ({q}ᶜ : Set ℕ)
  have hNn : N.Normal := prime_set_core_normal _
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  let O : Subgroup (H ⧸ N) := primeSetCore (GroupType := H ⧸ N) {q}
  have hOn : O.Normal := prime_set_core_normal _
  have hOq : IsPGroup q O := prime_core_isPGroup q hq
  have hself : Subgroup.centralizer (O : Set (H ⧸ N)) ≤ O :=
    solvable_complement_core_quotient_characteristic_prime (GroupType := H) q hq
  obtain ⟨sylow, hAsyl⟩ := normalized_subgroup_invariant_sylow p q hp hq A H
    (elementary_abelian_isPGroup p A hA) hAH hcop
  have hOle : O ≤ (sylow : Subgroup H).map π := by
    have h1 : O ≤ ((sylow.mapSurjective (QuotientGroup.mk'_surjective N) : Sylow q (H ⧸ N)) :
        Subgroup (H ⧸ N)) := hOq.le_sylow_of_normal _
    rwa [Sylow.coe_mapSurjective] at h1
  let Rsub : Subgroup H := O.comap π
  have hRchar : Rsub.Characteristic := two_stage_core_characteristic (GroupType := H) q
  have hRn : Rsub.Normal := inferInstance
  have hAR : A ≤ Subgroup.normalizer ((Rsub.map H.subtype : Subgroup G) : Set G) :=
    characteristic_subgroup_map_normalized A H hAH Rsub
  let P₁ : Subgroup G := (sylow : Subgroup H).map H.subtype ⊓ Rsub.map H.subtype
  have hP₀q : IsPGroup q ((sylow : Subgroup H).map H.subtype) := sylow.isPGroup'.map _
  have hP₀H : (sylow : Subgroup H).map H.subtype ≤ H := Subgroup.map_subtype_le _
  have hP₁q : IsPGroup q P₁ := hP₀q.to_le inf_le_left
  have hAP₁ : A ≤ Subgroup.normalizer (P₁ : Set G) := normalizer_inf_of_le A _ _ hAsyl hAR
  have hgen := generation_hyperplanes hp hA hA2 hAP₁ (coprime_of_isPGroup hq hp hpq hP₁q)
  intro u hu
  have huH : u ∈ H := hUH hu
  let u' : H := ⟨u, huH⟩
  have hcomm_y : ∀ B ∈ Coprime.hyperplanes p A, ∀ y' : H, (y' : G) ∈ P₁ →
      (y' : G) ∈ Subgroup.centralizer (B : Set G) → π u' * π y' = π y' * π u' := by
    intro B hB y' hy'P hy'C
    have hy'R : y' ∈ Rsub := by
      obtain ⟨r, hr, hry⟩ := hy'P.2
      have hr' : r = y' := Subtype.ext hry
      rwa [hr'] at hr
    have hw : π ⁅u', y'⁆ ∈ O :=
      Rsub.mul_mem (hRn.conj_mem y' hy'R u') (Rsub.inv_mem hy'R)
    have hyHB : (y' : G) ∈ H ⊓ Subgroup.centralizer (B : Set G) := ⟨y'.2, hy'C⟩
    have hWmem : ((⁅u', y'⁆ : H) : G) ∈ ⁅U, H ⊓ Subgroup.centralizer (B : Set G)⁆ :=
      Subgroup.commutator_mem_commutator hu hyHB
    have hcop' : Nat.Coprime q (orderOf (⁅u', y'⁆ : H)) := by
      rw [← Subgroup.orderOf_coe]
      exact (hcomm B hB).coprime_dvd_right (orderOf_dvd_card_of_mem hWmem)
    have hπw : π ⁅u', y'⁆ = 1 := map_eq_one_of_mem_pGroup hq hOq π hw hcop'
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hπw
    exact hπw
  have hcommP₁ : ∀ y' : H, (y' : G) ∈ P₁ → π u' * π y' = π y' * π u' := by
    intro y' hy'
    let Vsub : Subgroup H := (Subgroup.centralizer ({π u'} : Set (H ⧸ N))).comap π
    have hle : P₁ ≤ Vsub.map H.subtype := by
      refine le_trans (le_of_eq hgen.symm) (iSup₂_le fun B hB => ?_)
      intro y hy
      have hyH : y ∈ H := hP₀H hy.1.1
      refine ⟨⟨y, hyH⟩, ?_, rfl⟩
      show π ⟨y, hyH⟩ ∈ Subgroup.centralizer ({π u'} : Set (H ⧸ N))
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      rw [hg]
      exact hcomm_y B hB ⟨y, hyH⟩ hy.1 hy.2
    obtain ⟨v, hv, hvy⟩ := hle hy'
    have hvy' : v = y' := Subtype.ext hvy
    rw [hvy'] at hv
    exact (Subgroup.mem_centralizer_iff.mp hv) (π u') (Set.mem_singleton _)
  have hOcent : O ≤ Subgroup.centralizer ({π u'} : Set (H ⧸ N)) := by
    intro z hz
    obtain ⟨s, hs, hsz⟩ := hOle hz
    have hsR : s ∈ Rsub := by
      show π s ∈ O
      rw [hsz]
      exact hz
    have hsP₁ : (s : G) ∈ P₁ :=
      ⟨Subgroup.mem_map_of_mem H.subtype hs, Subgroup.mem_map_of_mem H.subtype hsR⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg, ← hsz]
    exact hcommP₁ s hsP₁
  have hπu : π u' ∈ O := by
    apply hself
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hOcent hz) (π u') (Set.mem_singleton _)).symm
  have hcop_u : Nat.Coprime q (orderOf u') := by
    rw [← Subgroup.orderOf_coe]
    exact hU.coprime_dvd_right (orderOf_dvd_card_of_mem hu)
  have h1 : π u' = 1 := map_eq_one_of_mem_pGroup hq hOq π hπu hcop_u
  have hu'N : u' ∈ N := (QuotientGroup.eq_one_iff u').mp h1
  exact Subgroup.mem_map.mpr ⟨u', hu'N, rfl⟩

theorem le_primeCoreIn_of_thompson {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {L P T : Subgroup G}
    (hL : Group.IsSolvable L) (hPL : P ≤ L) (hP : IsPGroup q P) (hTL : T ≤ L)
    (hT : Nat.Coprime q (Nat.card T)) (hPT : P ≤ Subgroup.normalizer (T : Set G))
    (hz : ∀ V : Subgroup G, V ≤ L → IsPGroup q V → V ≤ Subgroup.centralizer (P : Set G) →
      V ≤ P) :
    T ≤ primeCoreIn ({q}ᶜ : Set ℕ) L := by
  have : Fact q.Prime := ⟨hq⟩
  let N : Subgroup L := primeSetCore (GroupType := L) ({q}ᶜ : Set ℕ)
  have hNn : N.Normal := prime_set_core_normal _
  let π : L →* L ⧸ N := QuotientGroup.mk' N
  let O : Subgroup (L ⧸ N) := primeSetCore (GroupType := L ⧸ N) {q}
  have hOn : O.Normal := prime_set_core_normal _
  have hOq : IsPGroup q O := prime_core_isPGroup q hq
  have hself : Subgroup.centralizer (O : Set (L ⧸ N)) ≤ O :=
    solvable_complement_core_quotient_characteristic_prime (GroupType := L) q hq
  have hNcop : Nat.Coprime q (Nat.card N) :=
    (prime_supported_complement_singleton_iff_coprime q hq _).mp (prime_set_core_supported _)
  let P' : Subgroup L := P.subgroupOf L
  let T' : Subgroup L := T.subgroupOf L
  have hP' : IsPGroup q P' := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPL).symm
  have hT'cop : Nat.Coprime q (Nat.card T') := by
    show Nat.Coprime q (Nat.card (T.subgroupOf L))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv]
    exact hT
  have hP'T' : ∀ y ∈ P', ∀ t ∈ T', y * t * y⁻¹ ∈ T' := by
    intro y hy t ht
    exact (Subgroup.mem_normalizer_iff.mp (hPT hy) (t : G)).mp ht
  have hPbTb : P'.map π ≤ Subgroup.normalizer ((T'.map π : Subgroup (L ⧸ N)) : Set (L ⧸ N)) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨y, hy, rfl⟩ _ ⟨t, ht, rfl⟩
    exact ⟨y * t * y⁻¹, hP'T' y hy t ht, by simp⟩
  have hTbcop : Nat.Coprime q (Nat.card (T'.map π)) :=
    hT'cop.of_dvd_right (Subgroup.card_map_dvd T' π)
  have hC : O ⊓ Subgroup.centralizer ((P'.map π : Subgroup (L ⧸ N)) : Set (L ⧸ N)) ≤
      Subgroup.centralizer ((T'.map π : Subgroup (L ⧸ N)) : Set (L ⧸ N)) := by
    rintro xb ⟨hxO, hxP⟩
    have hcbar : ∀ y ∈ P', (y : L ⧸ N) * xb = xb * (y : L ⧸ N) := fun y hy =>
      (Subgroup.mem_centralizer_iff.mp hxP) (π y) (Subgroup.mem_map_of_mem π hy)
    obtain ⟨c, hcπ, hcP⟩ := exists_lift_centralizer hq N hNcop hP' hcbar
    obtain ⟨d, hdπ, a, hda, hdP⟩ : ∃ d : L, π d = xb ∧ ∃ a : ℕ, orderOf d = q ^ a ∧
        ∀ y ∈ P', y * d = d * y := by
      obtain ⟨e, b, hbq, hord⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' q hq.ne_one
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hOq ⟨xb, hxO⟩
      have hk' : orderOf xb = q ^ k := by
        rw [← Subgroup.orderOf_coe ⟨xb, hxO⟩] at hk
        exact hk
      have hcb : Nat.Coprime b (orderOf xb) := by
        rw [hk']
        exact ((Nat.Prime.coprime_iff_not_dvd hq).mpr hbq).symm.pow_right k
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcb
      have hb0 : b ≠ 0 := fun h0 => hbq (by rw [h0]; exact dvd_zero q)
      have hbdvd : b ∣ orderOf c := Dvd.intro_left _ hord.symm
      have h1 : orderOf (c ^ b) = q ^ e := by
        rw [orderOf_pow_of_dvd hb0 hbdvd, hord]
        exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hb0)
      have h2 : orderOf (c ^ (b * m)) ∣ q ^ e := by
        rw [← h1, pow_mul]
        exact orderOf_pow_dvd m
      obtain ⟨i, -, hi'⟩ := (Nat.dvd_prime_pow hq).mp h2
      refine ⟨c ^ (b * m), ?_, i, hi', fun y hy => ?_⟩
      · have hπc : π c = xb := hcπ
        rw [map_pow, pow_mul, hπc, hm]
      · exact (show Commute y c from hcP y hy).pow_right (b * m)
    have hdq : IsPGroup q (Subgroup.zpowers (d : G)) := by
      apply IsPGroup.of_card (n := a)
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hda]
    have hdL : Subgroup.zpowers (d : G) ≤ L := Subgroup.zpowers_le.mpr d.2
    have hdC : Subgroup.zpowers (d : G) ≤ Subgroup.centralizer (P : Set G) := by
      refine Subgroup.zpowers_le.mpr ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (hdP ⟨y, hPL hy⟩ hy)
    have hdP' : d ∈ P' := hz _ hdL hdq hdC (Subgroup.mem_zpowers _)
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    have hdt : d * t * d⁻¹ * t⁻¹ ∈ T' :=
      T'.mul_mem (hP'T' d hdP' t ht) (T'.inv_mem ht)
    have hπO : π (d * t * d⁻¹ * t⁻¹) ∈ O := by
      have heq : π (d * t * d⁻¹ * t⁻¹) = xb * (π t * xb * (π t)⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hdπ]
        group
      rw [heq]
      exact O.mul_mem hxO (O.inv_mem (hOn.conj_mem xb hxO (π t)))
    have hcopc : Nat.Coprime q (orderOf (d * t * d⁻¹ * t⁻¹)) :=
      hT'cop.coprime_dvd_right (orderOf_dvd_card_of_mem hdt)
    have hπ1 := map_eq_one_of_mem_pGroup hq hOq π hπO hcopc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hdπ] at hπ1
    have hcomm : xb * π t = π t * xb := by
      calc xb * π t = (xb * π t * xb⁻¹ * (π t)⁻¹) * (π t * xb) := by group
        _ = π t * xb := by rw [hπ1, one_mul]
    exact hcomm.symm
  have hTh := thompson_semidirect_centralizer hq hq2 (P := P'.map π) (Q := T'.map π) (X := O)
    (hP'.map π) hTbcop hPbTb hOq Subgroup.le_normalizer_of_normal Subgroup.le_normalizer_of_normal
    hC
  have hTbO : T'.map π ≤ O := (Subgroup.le_centralizer_iff.mp hTh).trans hself
  intro u hu
  have huL : u ∈ L := hTL hu
  let u' : L := ⟨u, huL⟩
  have hu'T : u' ∈ T' := hu
  have hcop_u : Nat.Coprime q (orderOf u') := by
    rw [← Subgroup.orderOf_coe]
    exact hT.coprime_dvd_right (orderOf_dvd_card_of_mem hu)
  have h1 : π u' = 1 :=
    map_eq_one_of_mem_pGroup hq hOq π (hTbO (Subgroup.mem_map_of_mem π hu'T)) hcop_u
  have hu'N : u' ∈ N := (QuotientGroup.eq_one_iff u').mp h1
  exact Subgroup.mem_map.mpr ⟨u', hu'N, rfl⟩

end CFSG.SignalizerFunctorTheorem.Glauberman.Steps678
