module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1R925Pure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise

private lemma r925_not_dvd_card_of_forall_orderOf {X : Type} [Group X] [Finite X] {N : Subgroup X}
    {p : ℕ} (hp : p.Prime) (hN : ∀ x ∈ N, ¬ p ∣ orderOf x) : ¬ p ∣ Nat.card N := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p h
  exact hN (x : X) x.2 (by rw [Subgroup.orderOf_coe, hx])

theorem r925_pCore_two_orderOf {X : Type} [Group X] [Finite X] {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) : ∀ x ∈ CFSG.pCore 2 X, ¬ q ∣ orderOf x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx hdvd
  have hP : IsPGroup 2 ↥(CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  rw [IsPGroup.iff_orderOf] at hP
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : orderOf x = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥(CFSG.pCore 2 X))).trans hk
  rw [hk'] at hdvd
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow hdvd))

theorem r925_pRank_quotient_le {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    {p : ℕ} (hp : p.Prime) (hN : ∀ x ∈ N, ¬ p ∣ orderOf x) :
    CFSG.Open.pRank p (⊤ : Subgroup (X ⧸ N)) ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  exact le_of_eq (CFSG.SectionRank.pRank_quotient_eq (p := p) N
    (r925_not_dvd_card_of_forall_orderOf hp hN))

theorem r925_pPrimeCore_orderOf {Γ : Type} [Group Γ] [Finite Γ] :
    ∀ x ∈ CFSG.pPrimeCore 3 Γ, ¬ 3 ∣ orderOf x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hx hdvd
  have hcop : Nat.Coprime 3 (Nat.card ↥(CFSG.pPrimeCore 3 Γ)) := CFSG.pPrimeCore_coprime_card
  have hdvd' : 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 Γ) := by
    have h := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(CFSG.pPrimeCore 3 Γ))
    rw [← Subgroup.orderOf_coe (⟨x, hx⟩ : ↥(CFSG.pPrimeCore 3 Γ))] at h
    exact dvd_trans hdvd h
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop) hdvd'

theorem r925_odd_relIndex_map {Γ Λ : Type} [Group Γ] [Group Λ] [Finite Γ] (π : Γ →* Λ)
    (hπ : Function.Surjective π) {K M : Subgroup Γ} (hK : K.Normal) (hM : Odd M.index) :
    Odd ((K.map π ⊓ M.map π).relIndex (K.map π)) := by
  haveI : Finite Λ := Finite.of_surjective π hπ
  haveI : (K.map π).Normal := hK.map π hπ
  have hodd : Odd (M.map π).index := Odd.of_dvd_nat hM (Subgroup.index_map_dvd M hπ)
  have h1 : (K.map π ⊓ M.map π).relIndex (K.map π) = (M.map π).relIndex (K.map π) :=
    Subgroup.inf_relIndex_left _ _
  have h2 : (M.map π).relIndex (K.map π) =
      (M.map π).relIndex ((K.map π) ⊔ (M.map π)) :=
    (CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (K.map π) (M.map π)).symm
  rw [h1, h2]
  exact Odd.of_dvd_nat hodd
    (Subgroup.relIndex_dvd_index_of_le (le_sup_right : (M.map π) ≤ (K.map π) ⊔ (M.map π)))

theorem r925_card_map_eq_three {Γ : Type} [Group Γ] [Finite Γ] {J D : Subgroup Γ} [J.Normal]
    (hJ : ∀ x ∈ J, ¬ 3 ∣ orderOf x) (hD : Nat.card D = 3) :
    Nat.card (D.map (QuotientGroup.mk' J)) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : D →* D.map (QuotientGroup.mk' J) := (QuotientGroup.mk' J).subgroupMap D
  have hinj : Function.Injective f := by
    intro x y hxy
    have h1 : (QuotientGroup.mk' J) (x : Γ) = (QuotientGroup.mk' J) (y : Γ) := by
      have := congrArg Subtype.val hxy
      simpa [f] using this
    have hmem : ((x : D) : Γ)⁻¹ * ((y : D) : Γ) ∈ D := D.mul_mem (D.inv_mem x.2) y.2
    have h2 : ((x : D) : Γ)⁻¹ * ((y : D) : Γ) ∈ J := by
      have h : (QuotientGroup.mk' J) (((x : D) : Γ)⁻¹ * ((y : D) : Γ)) = 1 := by
        rw [map_mul, map_inv, h1, inv_mul_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    have h3 : orderOf (((x : D) : Γ)⁻¹ * ((y : D) : Γ)) ∣ 3 := by
      have h := orderOf_dvd_natCard (⟨((x : D) : Γ)⁻¹ * ((y : D) : Γ), hmem⟩ : D)
      rw [← Subgroup.orderOf_coe (⟨_, hmem⟩ : D)] at h
      rwa [hD] at h
    have h4 : orderOf (((x : D) : Γ)⁻¹ * ((y : D) : Γ)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact h
      · exfalso
        exact hJ _ h2 (by rw [h])
    have h5 : ((x : D) : Γ)⁻¹ * ((y : D) : Γ) = 1 := orderOf_eq_one_iff.mp h4
    have h6 : ((x : D) : Γ) = ((y : D) : Γ) := by
      calc ((x : D) : Γ) = ((x : D) : Γ) * (((x : D) : Γ)⁻¹ * ((y : D) : Γ)) := by
            rw [h5, mul_one]
        _ = ((y : D) : Γ) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
    exact Subtype.ext h6
  have hsurj : Function.Surjective f := MonoidHom.subgroupMap_surjective _ _
  have hcard : Nat.card (D.map (QuotientGroup.mk' J)) = Nat.card D :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
  rw [hcard, hD]

theorem r925_exists_lift_card_three {X : Type} [Group X] [Finite X] {J : Subgroup X} [J.Normal]
    (hJ : ∀ x ∈ J, ¬ 3 ∣ orderOf x) {D' : Subgroup (X ⧸ J)} (hD' : Nat.card D' = 3) :
    ∃ D : Subgroup X, Nat.card D = 3 ∧ D.map (QuotientGroup.mk' J) = D' := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup X := D'.comap (QuotientGroup.mk' J)
  have hPcard : Nat.card P = Nat.card J * 3 := by
    have h := QuotientGroup.card_preimage_mk J (D' : Set (X ⧸ J))
    have hD'' : Nat.card ↥(D' : Set (X ⧸ J)) = 3 := hD'
    rw [hD''] at h
    exact h
  have h3dvd : 3 ∣ Nat.card P := by
    rw [hPcard]
    exact dvd_mul_left 3 (Nat.card J)
  obtain ⟨D₀, hD₀card⟩ := Sylow.exists_subgroup_card_pow_prime (G := P) 3 (n := 1)
    (by simpa using h3dvd)
  let D : Subgroup X := D₀.map P.subtype
  have hDcard : Nat.card D = 3 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hD₀card, pow_one]
  refine ⟨D, hDcard, ?_⟩
  have hle : D.map (QuotientGroup.mk' J) ≤ D' := by
    rw [Subgroup.map_le_iff_le_comap]
    exact Subgroup.map_subtype_le D₀
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  change Nat.card D' ≤ Nat.card (D.map (QuotientGroup.mk' J))
  rw [hD', r925_card_map_eq_three hJ hDcard]

private lemma r925_map_conj_subtype {G : Type} [Group G] (P : Subgroup G) (q : ↥P)
    (S : Subgroup ↥P) :
    (S.map (MulAut.conj q : ↥P →* ↥P)).map P.subtype =
      (S.map P.subtype).map (MulAut.conj ((q : ↥P) : G) : G →* G) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private lemma r925_map_conj_inv_mul {G : Type} [Group G] {D : Subgroup G} {q x : G}
    (h : D.map (MulAut.conj q : G →* G) = D.map (MulAut.conj x : G →* G)) :
    q⁻¹ * x ∈ Subgroup.normalizer (D : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 : (↑(MulAut.conj (q⁻¹ * x)) : G →* G) =
      (↑((MulAut.conj q)⁻¹ * MulAut.conj x) : G →* G) := by
    ext g
    simp [MulAut.conj_apply, mul_assoc]
  rw [h1]
  calc D.map (↑((MulAut.conj q)⁻¹ * MulAut.conj x) : G →* G)
      = (D.map (↑(MulAut.conj x) : G →* G)).map (↑((MulAut.conj q)⁻¹) : G →* G) := by
          rw [Subgroup.map_map]
          congr 1
    _ = (D.map (MulAut.conj q : G →* G)).map (↑((MulAut.conj q)⁻¹) : G →* G) := by
          rw [h]
    _ = D := by
          have hcomp : (↑((MulAut.conj q)⁻¹) : G →* G).comp (MulAut.conj q : G →* G) =
              MonoidHom.id G := by
            ext g
            simp [MonoidHom.comp_apply, MulAut.conj_apply, mul_assoc]
          rw [Subgroup.map_map, hcomp, Subgroup.map_id]

private lemma r925_normalizer_sup_le {Γ : Type} [Group Γ] [Finite Γ] {J D M : Subgroup Γ}
    [J.Normal] (hJ : ∀ x ∈ J, ¬ 3 ∣ orderOf x) (hD : Nat.card D = 3)
    (hM : normalizer (D : Set Γ) ≤ M) :
    normalizer ((D ⊔ J : Subgroup Γ) : Set Γ) ≤ J ⊔ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro x hxN
  have hDleP : D ≤ D ⊔ J := le_sup_left
  have hJ3 : ¬ 3 ∣ Nat.card J := r925_not_dvd_card_of_forall_orderOf Nat.prime_three hJ
  have hDM : D ≤ M := le_trans Subgroup.le_normalizer hM
  have hDJ : D ⊓ J = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyD, hyJ⟩ := Subgroup.mem_inf.mp hy
    have h3 : orderOf y ∣ 3 := by
      have h := orderOf_dvd_natCard (⟨y, hyD⟩ : D)
      rw [← Subgroup.orderOf_coe (⟨y, hyD⟩ : D), hD] at h
      exact h
    have h4 : orderOf y = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
      · exact h
      · exfalso
        exact hJ y hyJ (by rw [h])
    exact orderOf_eq_one_iff.mp h4
  have hsubDJ : D.subgroupOf J = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    exact Subtype.ext ((Subgroup.eq_bot_iff_forall (D ⊓ J)).mp hDJ (y : Γ) ⟨hy, y.2⟩)
  have hDrelJ : D.relIndex J = Nat.card J := by
    change (D.subgroupOf J).index = Nat.card J
    rw [hsubDJ, Subgroup.index_bot]
  have hDrelP : D.relIndex (D ⊔ J) = Nat.card J := by
    rw [sup_comm, CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal J D, hDrelJ]
  have hCleP : D.map (MulAut.conj x : Γ →* Γ) ≤ D ⊔ J := by
    rintro y ⟨d, hd, rfl⟩
    simpa using (Subgroup.mem_normalizer_iff.mp hxN d).mp (hDleP hd)
  have hCcard : Nat.card (D.map (MulAut.conj x : Γ →* Γ)) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hD]
  have hDcard : Nat.card (D.subgroupOf (D ⊔ J)) = 3 := by
    have h := Subgroup.card_map_of_injective (K := D.subgroupOf (D ⊔ J))
      (D ⊔ J).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDleP, hD] at h
    exact h.symm
  have hCcard' : Nat.card ((D.map (MulAut.conj x : Γ →* Γ)).subgroupOf (D ⊔ J)) = 3 := by
    have h := Subgroup.card_map_of_injective
      (K := (D.map (MulAut.conj x : Γ →* Γ)).subgroupOf (D ⊔ J)) (D ⊔ J).subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCleP, hCcard] at h
    exact h.symm
  have hPcard : Nat.card ↥(D ⊔ J) = Nat.card J * 3 := by
    have h := Subgroup.relIndex_mul_card D (D ⊔ J)
    rw [hDrelP, inf_eq_left.mpr hDleP, hD] at h
    exact h.symm
  have hCrelP : (D.map (MulAut.conj x : Γ →* Γ)).relIndex (D ⊔ J) = Nat.card J := by
    have h := Subgroup.relIndex_mul_card (D.map (MulAut.conj x : Γ →* Γ)) (D ⊔ J)
    rw [inf_eq_left.mpr hCleP, hCcard, hPcard] at h
    exact Nat.mul_right_cancel (by norm_num) h
  have hPgroup1 : IsPGroup 3 (D.subgroupOf (D ⊔ J)) :=
    IsPGroup.of_card (by rw [hDcard, pow_one])
  have hrelD : ¬ 3 ∣ (D.subgroupOf (D ⊔ J)).index := by
    change ¬ 3 ∣ D.relIndex (D ⊔ J)
    rw [hDrelP]; exact hJ3
  have hPgroup2 : IsPGroup 3 ((D.map (MulAut.conj x : Γ →* Γ)).subgroupOf (D ⊔ J)) :=
    IsPGroup.of_card (by rw [hCcard', pow_one])
  have hrelC : ¬ 3 ∣ ((D.map (MulAut.conj x : Γ →* Γ)).subgroupOf (D ⊔ J)).index := by
    change ¬ 3 ∣ (D.map (MulAut.conj x : Γ →* Γ)).relIndex (D ⊔ J)
    rw [hCrelP]; exact hJ3
  obtain ⟨q, hq⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥(D ⊔ J))
    (hPgroup1.toSylow hrelD) (hPgroup2.toSylow hrelC)
  have hq' : (D.subgroupOf (D ⊔ J)).map (MulAut.conj q : ↥(D ⊔ J) →* ↥(D ⊔ J)) =
      (D.map (MulAut.conj x : Γ →* Γ)).subgroupOf (D ⊔ J) := by
    have h := congrArg (fun S : Sylow 3 ↥(D ⊔ J) => (S : Subgroup ↥(D ⊔ J))) hq
    change MulAut.conj q • (hPgroup1.toSylow hrelD : Subgroup ↥(D ⊔ J)) =
      (hPgroup2.toSylow hrelC : Subgroup ↥(D ⊔ J)) at h
    rw [IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at h
    change (D.subgroupOf (D ⊔ J)).map (MulAut.conj q : ↥(D ⊔ J) →* ↥(D ⊔ J)) =
      (D.map (MulAut.conj x : Γ →* Γ)).subgroupOf (D ⊔ J) at h
    exact h
  have hqmap : D.map (MulAut.conj ((q : ↥(D ⊔ J)) : Γ) : Γ →* Γ) =
      D.map (MulAut.conj x : Γ →* Γ) := by
    have h := congrArg (Subgroup.map (D ⊔ J).subtype) hq'
    rw [r925_map_conj_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDleP,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCleP] at h
    exact h
  have hgN : ((q : ↥(D ⊔ J)) : Γ)⁻¹ * x ∈ normalizer (D : Set Γ) :=
    r925_map_conj_inv_mul hqmap
  have hgM : ((q : ↥(D ⊔ J)) : Γ)⁻¹ * x ∈ M := hM hgN
  have hqJM : ((q : ↥(D ⊔ J)) : Γ) ∈ J ⊔ M :=
    (sup_le (le_trans hDM le_sup_right) le_sup_left) q.2
  have hxJM : x ∈ J ⊔ M := by
    have h1 : ((q : ↥(D ⊔ J)) : Γ) * (((q : ↥(D ⊔ J)) : Γ)⁻¹ * x) ∈ J ⊔ M :=
      (J ⊔ M).mul_mem hqJM ((show M ≤ J ⊔ M from le_sup_right) hgM)
    rwa [mul_inv_cancel_left] at h1
  exact hxJM

theorem r925_normalizer_map_le {Γ : Type} [Group Γ] [Finite Γ] {J D M : Subgroup Γ} [J.Normal]
    (hJ : ∀ x ∈ J, ¬ 3 ∣ orderOf x) (hD : Nat.card D = 3)
    (hM : normalizer (D : Set Γ) ≤ M) :
    normalizer ((D.map (QuotientGroup.mk' J) : Subgroup (Γ ⧸ J)) : Set (Γ ⧸ J)) ≤
      M.map (QuotientGroup.mk' J) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set D' : Subgroup (Γ ⧸ J) := D.map (QuotientGroup.mk' J) with hD'def
  have hcomap : D'.comap (QuotientGroup.mk' J) = D ⊔ J := by
    rw [hD'def, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  intro xbar hxbar
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective J xbar
  have hxN : x ∈ normalizer ((D ⊔ J : Subgroup Γ) : Set Γ) := by
    have h1 : x ∈ (Subgroup.normalizer (D' : Set (Γ ⧸ J))).comap (QuotientGroup.mk' J) := hxbar
    rwa [Subgroup.comap_normalizer_eq_of_surjective D' (QuotientGroup.mk'_surjective J),
      hcomap] at h1
  have hxJM : x ∈ J ⊔ M := r925_normalizer_sup_le hJ hD hM hxN
  have hmem : (QuotientGroup.mk' J) x ∈ (J ⊔ M).map (QuotientGroup.mk' J) :=
    ⟨x, hxJM, rfl⟩
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq] at hmem
  exact hmem

theorem r925_perfA5Cover_map_mk {Γ : Type} [Group Γ] {Y J : Subgroup Γ} [J.Normal]
    (hJ : ∀ x ∈ J, ¬ 3 ∣ orderOf x) (hY : IsPerfA5Cover ↥Y) :
    IsPerfA5Cover ↥(Y.map (QuotientGroup.mk' J)) := by
  refine IsPerfA5Cover.map hY ((QuotientGroup.mk' J).subgroupMap Y)
    (MonoidHom.subgroupMap_surjective _ _) ?_
  intro y hy
  have hy' : ((y : ↥Y) : Γ) ∈ J := by
    have h1 : (QuotientGroup.mk' J) ((y : ↥Y) : Γ) = 1 :=
      congrArg (fun z : ↥(Y.map (QuotientGroup.mk' J)) => (z : Γ ⧸ J))
        (MonoidHom.mem_ker.mp hy)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [← Subgroup.orderOf_coe y]
  exact hJ _ hy'

theorem r925_kGroupNonab_map {Γ Λ : Type} [Group Γ] [Group Λ] (π : Γ →* Λ)
    {C : CFSG.KCore.Catalogue.{0}} (hC : CFSG.KCore.IsoInvariant C) {M : Subgroup Γ}
    (hM : CFSG.KCore.KGroupNonab C ↥M) {N : Subgroup Λ} (hN : N ≤ M.map π) :
    CFSG.KCore.KGroupNonab C ↥N := by
  have hM' : CFSG.KCore.KGroupNonab C ↥(M.map π) :=
    CFSG.KCore.KGroupNonab.of_surjective hC hM (π.subgroupMap M)
      (MonoidHom.subgroupMap_surjective π M)
  exact CFSG.KCore.KGroupNonab.of_injective hC hM' (Subgroup.inclusion hN)
    (Subgroup.inclusion_injective hN)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
