module

public import CFSG.GroupTheory.PGroup.ElemAbelianSq
public import CFSG.Quasithin.Vol2.Ch11SecA12Cop

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped Pointwise

private theorem card_sup_mul_card_inf_of_normalizes' {G : Type*} [Group G] {X N : Subgroup G}
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) :
    Nat.card (X ⊔ N : Subgroup G) * Nat.card (X ⊓ N : Subgroup G) = Nat.card X * Nat.card N := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hXN
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hXN
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X N hXN
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (X ⊔ N))
  have h3 : Nat.card (N.subgroupOf X) = Nat.card (X ⊓ N : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (N.subgroupOf (X ⊔ N)) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

private theorem le_centralizer_of_isCyclic {G : Type*} [Group G] {p r : ℕ} (hp : p.Prime)
    (hr : r.Prime) (hpr : p ≠ r) (hpr1 : ¬ p ∣ r - 1) {Q S : Subgroup G} [Finite S]
    (hQ : IsPGroup p Q) (hSc : IsCyclic S) (hSr : IsPGroup r S)
    (hQS : Q ≤ Subgroup.normalizer (S : Set G)) :
    Q ≤ Subgroup.centralizer (S : Set G) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : IsCyclic S := hSc
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hqS : q ∈ Subgroup.normalizer (S : Set G) := hQS hq
  have hpow : (S.normalizerMonoidHom ⟨q, hqS⟩) ^ orderOf q = 1 := by
    rw [← map_pow]
    have h1 : (⟨q, hqS⟩ : Subgroup.normalizer (S : Set G)) ^ orderOf q = 1 :=
      Subtype.ext (pow_orderOf_eq_one q)
    rw [h1, map_one]
  have hdvd1 : orderOf (S.normalizerMonoidHom ⟨q, hqS⟩) ∣ orderOf q :=
    orderOf_dvd_of_pow_eq_one hpow
  have hdvd2 : orderOf (S.normalizerMonoidHom ⟨q, hqS⟩) ∣ Nat.card (MulAut S) :=
    orderOf_dvd_natCard _
  obtain ⟨n, hn⟩ := hQ.exists_orderOf_eq_pow ⟨q, hq⟩
  rw [Subgroup.orderOf_mk q hq] at hn
  obtain ⟨k, hk⟩ := hSr.exists_card_eq
  have hcop : Nat.Coprime (p ^ n) (Nat.card (MulAut S)) := by
    rw [IsCyclic.card_mulAut]
    cases k with
    | zero => simp [hk]
    | succ j =>
        rw [hk, Nat.totient_prime_pow_succ hr]
        exact Nat.Coprime.mul_right
          (Nat.Coprime.pow_left n (Nat.Coprime.pow_right j ((Nat.coprime_primes hp hr).2 hpr)))
          (Nat.Coprime.pow_left n (hp.coprime_iff_not_dvd.mpr hpr1))
  have h1 : orderOf (S.normalizerMonoidHom ⟨q, hqS⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (hn.symm ▸ hcop) hdvd1 hdvd2
  have h2 : S.normalizerMonoidHom ⟨q, hqS⟩ = 1 := orderOf_eq_one_iff.mp h1
  have h3 : q * s * q⁻¹ = s := by
    have h := congrArg (fun f : MulAut S => ((f ⟨s, hs⟩ : S) : G)) h2
    simpa using h
  calc s * q = (q * s * q⁻¹) * q := by rw [h3]
    _ = q * s := by group

theorem exists_isElemAbelian_le_centralizer_of_coprime_action {M : Type} {H : Type*} [Group M]
    [Finite M] [Group H] (π : M →* H) {p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpr : p ≠ r)
    (hpr1 : ¬ p ∣ r - 1) {Q : Subgroup M} (hQp : IsPGroup p Q) (hker : ¬ p ∣ Nat.card π.ker)
    (hcyc : ∀ S : Subgroup M, S ≤ π.ker → IsPGroup r S → IsCyclic S) {L : Subgroup H}
    (hQL : ∀ q ∈ Q, ∀ u ∈ L, π q * u = u * π q)
    {A : Subgroup M} (hAL : A ≤ L.comap π) (hA : IsElemAbelian r A) :
    ∃ A' : Subgroup M, A' ≤ L.comap π ∧ A' ≤ centralizer (Q : Set M) ∧ IsElemAbelian r A' ∧
      Nat.card A' = Nat.card A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  let C : Subgroup M := π.ker
  let X : Subgroup M := L.comap π
  let Y : Subgroup M := X ⊓ Subgroup.centralizer (Q : Set M)
  have hC : C = π.ker := rfl
  have hX : X = L.comap π := rfl
  have hY : Y = X ⊓ Subgroup.centralizer (Q : Set M) := rfl
  have hconjX : ∀ q ∈ Q, ∀ x ∈ X, q * x * q⁻¹ ∈ X := by
    intro q hq x hx
    have hxL : π x ∈ L := hx
    have hcomm : π q * π x = π x * π q := hQL q hq (π x) hxL
    change π (q * x * q⁻¹) ∈ L
    have h1 : π q * π x * (π q)⁻¹ = π x := by rw [hcomm]; group
    simpa only [map_mul, map_inv, h1] using hxL
  have hQX : Q ≤ Subgroup.normalizer (X : Set M) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hconjX q hq x
    · intro hx
      have hx' : q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ ∈ X :=
        hconjX q⁻¹ (Q.inv_mem hq) (q * x * q⁻¹) hx
      have heq : q⁻¹ * (q * x * q⁻¹) * (q⁻¹)⁻¹ = x := by group
      rwa [heq] at hx'
  have hcommC : ∀ q ∈ Q, ∀ x ∈ X, q * x * q⁻¹ * x⁻¹ ∈ C := by
    intro q hq x hx
    have hxL : π x ∈ L := hx
    have hcomm : π q * π x = π x * π q := hQL q hq (π x) hxL
    rw [hC, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have hker_le_X : C ≤ X := by
    intro c hc
    rw [hC, MonoidHom.mem_ker] at hc
    change π c ∈ L
    rw [hc]
    exact L.one_mem
  have hXker : X ≤ Subgroup.normalizer (C : Set M) := by
    rw [hC, Subgroup.normalizer_eq_top]
    exact le_top
  have hX_eq : X = Y ⊔ C := by
    apply le_antisymm
    · intro x hx
      obtain ⟨c, hcY, hcx⟩ :=
        CFSG.Quasithin.Vol2.Ch11.SecA.exists_mem_centralizer_of_coprime hp hQp hQX hker_le_X
          hXker ((hp.coprime_iff_not_dvd).2 hker) hcommC hx
      have hx' : x = c * (c⁻¹ * x) := by group
      rw [hx']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcY) (Subgroup.mem_sup_right hcx)
    · exact sup_le inf_le_left hker_le_X
  have hQ_C : Q ≤ Subgroup.normalizer (C : Set M) := by
    rw [hC, Subgroup.normalizer_eq_top]
    exact le_top
  obtain ⟨S₀, hS₀⟩ :=
    CFSG.GroupTheory.exists_sylow_le_normalizer_of_isPGroup hp hr hQp hQ_C hker
  let S : Subgroup M := (S₀ : Subgroup C).map C.subtype
  have hS_le_C : S ≤ C := Subgroup.map_subtype_le _
  have hS_pg : IsPGroup r S := S₀.isPGroup'.map C.subtype
  have hQ_S : Q ≤ Subgroup.normalizer (S : Set M) := hS₀
  have hS_card : Nat.card S = Nat.card (S₀ : Subgroup C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hS_cyc : IsCyclic S := hcyc S hS_le_C hS_pg
  have hS_sylow : Nat.card S = r ^ (Nat.card C).factorization r := by
    rw [hS_card]
    exact Sylow.card_eq_multiplicity S₀
  have hQ_cent_S : Q ≤ Subgroup.centralizer (S : Set M) :=
    le_centralizer_of_isCyclic hp hr hpr hpr1 hQp hS_cyc hS_pg hQ_S
  have hS_centQ : S ≤ Subgroup.centralizer (Q : Set M) :=
    Subgroup.le_centralizer_iff.mp hQ_cent_S
  have hS_X : S ≤ X := hS_le_C.trans hker_le_X
  have hS_Y : S ≤ Y := le_inf hS_X hS_centQ
  have hS_YC : S ≤ Y ⊓ C := le_inf hS_Y hS_le_C
  have hYC_dvd : Nat.card ↥(Y ⊓ C) ∣ Nat.card C := Subgroup.card_dvd_of_le inf_le_right
  have hS_dvd_YC : Nat.card S ∣ Nat.card ↥(Y ⊓ C) := Subgroup.card_dvd_of_le hS_YC
  haveI : Nonempty ↥(Y ⊓ C) := ⟨1⟩
  haveI : Nonempty ↥C := ⟨1⟩
  haveI : Nonempty ↥X := ⟨1⟩
  haveI : Nonempty ↥Y := ⟨1⟩
  have hYC_ne : Nat.card ↥(Y ⊓ C) ≠ 0 := (Nat.card_pos (α := ↥(Y ⊓ C))).ne'
  have hC_ne : Nat.card C ≠ 0 := (Nat.card_pos (α := ↥C)).ne'
  have hX_ne : Nat.card X ≠ 0 := (Nat.card_pos (α := ↥X)).ne'
  have hY_ne : Nat.card Y ≠ 0 := (Nat.card_pos (α := ↥Y)).ne'
  have hfac_dvd : (Nat.card ↥(Y ⊓ C)).factorization r ≤ (Nat.card C).factorization r :=
    (Nat.factorization_prime_le_iff_dvd hYC_ne hC_ne).2 hYC_dvd r hr
  have hfac_le : (Nat.card C).factorization r ≤ (Nat.card ↥(Y ⊓ C)).factorization r :=
    (hr.pow_dvd_iff_le_factorization hYC_ne).mp (hS_sylow ▸ hS_dvd_YC)
  have hfac_eq : (Nat.card ↥(Y ⊓ C)).factorization r = (Nat.card C).factorization r :=
    le_antisymm hfac_dvd hfac_le
  have hYC_comm : Y ⊔ C = X := hX_eq.symm
  have hprod : Nat.card X * Nat.card ↥(Y ⊓ C) = Nat.card Y * Nat.card C := by
    have h := card_sup_mul_card_inf_of_normalizes' (G := M) (X := Y) (N := C)
      (inf_le_left.trans hXker)
    rwa [hYC_comm] at h
  have hfac_X : (Nat.card X).factorization r = (Nat.card Y).factorization r := by
    have h0 : (Nat.card X * Nat.card ↥(Y ⊓ C)).factorization =
        (Nat.card Y * Nat.card C).factorization := by rw [hprod]
    have h1 := congrArg (fun f : ℕ →₀ ℕ => f r) h0
    simp only [Nat.factorization_mul hX_ne hYC_ne, Nat.factorization_mul hY_ne hC_ne,
      Finsupp.coe_add, Pi.add_apply] at h1
    omega
  obtain ⟨TY, hS_TY⟩ := (hS_pg.comap_subtype (K := Y)).exists_le_sylow
  let T : Subgroup M := (TY : Subgroup ↥Y).map Y.subtype
  have hTdef : T = (TY : Subgroup ↥Y).map Y.subtype := rfl
  have hT_Y : T ≤ Y := by rw [hTdef]; exact Subgroup.map_subtype_le _
  have hS_T : S ≤ T := by
    rw [hTdef]
    intro s hs
    exact Subgroup.mem_map.mpr
      ⟨⟨s, hS_Y hs⟩, hS_TY (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
  have hT_cardY : Nat.card T = r ^ (Nat.card Y).factorization r := by
    rw [hTdef, Subgroup.card_map_of_injective Y.subtype_injective]
    exact Sylow.card_eq_multiplicity TY
  have hT_X : T ≤ X := hT_Y.trans inf_le_left
  have hT_sub : Nat.card (T.subgroupOf X) = Nat.card T := by
    rw [← Subgroup.card_subtype X (T.subgroupOf X), Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hT_X]
  have hT_card : Nat.card T = r ^ (Nat.card X).factorization r := by
    rw [hT_cardY, hfac_X]
  let TX : Sylow r ↥X := Sylow.ofCard (T.subgroupOf X) (by rw [hT_sub]; exact hT_card)
  have hTX_coe : (TX : Subgroup ↥X) = T.subgroupOf X := Sylow.coe_ofCard _ _
  haveI : Finite (Sylow r ↥X) :=
    Finite.of_injective (fun P : Sylow r ↥X => (P : Set ↥X))
      (fun P Q h => SetLike.coe_injective h)
  obtain ⟨TA, hA_TA⟩ := (hA.isPGroup.comap_subtype (K := X)).exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥X TA TX
  have hA'T : A.map (MulAut.conj (x : M)).toMonoidHom ≤ T := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    have haX : a ∈ X := hAL ha
    have h1 : (⟨a, haX⟩ : ↥X) ∈ A.subgroupOf X := Subgroup.mem_subgroupOf.mpr ha
    have h2 : (⟨a, haX⟩ : ↥X) ∈ (TA : Subgroup ↥X) := hA_TA h1
    have h3 : (MulAut.conj x) (⟨a, haX⟩ : ↥X) ∈
        (MulAut.conj x) • (TA : Subgroup ↥X) :=
      Subgroup.smul_mem_pointwise_smul _ (MulAut.conj x) _ h2
    have hx' : (TX : Subgroup ↥X) = (MulAut.conj x) • (TA : Subgroup ↥X) := by
      rw [← congrArg (fun P : Sylow r ↥X => (P : Subgroup ↥X)) hx, Sylow.coe_subgroup_smul]
    have h4 : (MulAut.conj x) (⟨a, haX⟩ : ↥X) ∈ T.subgroupOf X := by
      rw [← hTX_coe, hx']
      exact h3
    have h5 : (((MulAut.conj x) (⟨a, haX⟩ : ↥X)) : M) ∈ T :=
      Subgroup.mem_subgroupOf.mp h4
    simpa using h5
  refine ⟨A.map (MulAut.conj (x : M)).toMonoidHom, ?_, ?_, hA.map _, ?_⟩
  · exact hA'T.trans (hT_Y.trans inf_le_left)
  · exact hA'T.trans (hT_Y.trans inf_le_right)
  · exact Subgroup.card_map_of_injective (MulAut.conj (x : M)).injective

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
