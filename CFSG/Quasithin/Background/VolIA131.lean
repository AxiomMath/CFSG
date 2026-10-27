module

public import CFSG.Quasithin.Background.VolIA131Core
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.Quasithin.Vol2.Ch3Sec3InputsA131

public section

namespace CFSG.Quasithin.VolI.A131

open scoped Pointwise

section Transport

variable {Q Q' : Type} [Group Q] [Group Q'] [Finite Q] [Finite Q']

omit [Finite Q] [Finite Q'] in
theorem centralizer_le_of_mulEquiv {p : ℕ} (e : Q ≃* Q')
    (hC : Subgroup.centralizer (CFSG.pCore p Q' : Set Q') ≤ CFSG.pCore p Q') :
    Subgroup.centralizer (CFSG.pCore p Q : Set Q) ≤ CFSG.pCore p Q := by
  have hmap := CFSG.pCore_map_iso p e
  intro x hx
  have hex : e x ∈ Subgroup.centralizer (CFSG.pCore p Q' : Set Q') := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hmap] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have := Subgroup.mem_centralizer_iff.mp hx z hz
    change e z * e x = e x * e z
    rw [← map_mul, ← map_mul, this]
  have h1 := hC hex
  rw [← hmap] at h1
  obtain ⟨z, hz, hzx⟩ := h1
  rwa [← e.injective hzx]

theorem a131Concl_of_mulEquiv {p : ℕ} (hp : p.Prime) (e : Q ≃* Q') (h : A131Concl p Q) :
    A131Concl p Q' := by
  have : Fact p.Prime := ⟨hp⟩
  have hmap := CFSG.pCore_map_iso p e
  have hrank : CFSG.pRank 2 Q' = CFSG.pRank 2 Q := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e).symm
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun S' hS' hS'1 => ?_, hrank ▸ h2, fun hel hcard hr => ?_⟩
  ·
    set S := S'.comap e.toMonoidHom with hSdef
    have hS : IsPGroup 2 S := hS'.comap_of_injective e.toMonoidHom e.injective
    have hS1 : S ≠ ⊥ := by
      intro hbot
      apply hS'1
      rw [eq_bot_iff]
      intro s' hs'
      have h : e.symm s' ∈ S := by
        show e.toMonoidHom (e.symm s') ∈ S'
        simpa using hs'
      rw [hbot, Subgroup.mem_bot] at h
      rw [Subgroup.mem_bot]
      simpa using congrArg e h
    have hcyc := h1 S hS hS1
    have hle : CFSG.pCore p Q' ⊓ Subgroup.centralizer (S' : Set Q') ≤
        (CFSG.pCore p Q ⊓ Subgroup.centralizer (S : Set Q)).map e.toMonoidHom := by
      rintro x' ⟨hx'P, hx'C⟩
      refine ⟨e.symm x', ⟨?_, ?_⟩, e.apply_symm_apply x'⟩
      · rw [← hmap] at hx'P
        obtain ⟨z, hz, rfl⟩ := hx'P
        simpa using hz
      · refine Subgroup.mem_centralizer_iff.mpr fun s hs => ?_
        have := Subgroup.mem_centralizer_iff.mp hx'C (e s) hs
        apply e.injective
        rw [map_mul, map_mul, e.apply_symm_apply]
        exact this
    have : IsCyclic ↥((CFSG.pCore p Q ⊓ Subgroup.centralizer (S : Set Q)).map e.toMonoidHom) :=
      isCyclic_of_surjective _ (e.toMonoidHom.subgroupMap_surjective _)
    exact Subgroup.isCyclic_of_le hle
  ·
    have hmap' : (CFSG.pCore p Q').map e.symm.toMonoidHom = CFSG.pCore p Q :=
      CFSG.pCore_map_iso p e.symm
    have hel0 : CFSG.IsElementaryAbelian p ↥(CFSG.pCore p Q) := by
      rw [← hmap']
      exact CFSG.IsElementaryAbelian.map e.symm.toMonoidHom
    have hcard0 : Nat.card ↥(CFSG.pCore p Q) = p ^ 3 := by
      rw [← hcard, ← hmap, Subgroup.card_map_of_injective e.injective]
    obtain ⟨K, hKn, hK1, hK2⟩ := h3 hel0 hcard0 (hrank ▸ hr)
    refine ⟨K.map e.toMonoidHom, hKn.map _ e.surjective, ?_, ?_⟩
    · rw [← Subgroup.map_bot e.toMonoidHom]
      exact (Subgroup.map_lt_map_iff_of_injective e.injective).mpr hK1
    · rw [← hmap]
      exact (Subgroup.map_lt_map_iff_of_injective e.injective).mpr hK2

end Transport

theorem exists_reduction {p : ℕ} (hp : p.Prime) :
    ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G = n → ∀ (H : Subgroup G) [H.Normal],
      ∃ (G₀ : Type) (_ : Group G₀) (_ : Finite G₀) (H₀ : Subgroup G₀) (_ : H₀.Normal),
        IsPGroup p H₀ ∧ CFSG.pRank p G₀ ≤ CFSG.pRank p G ∧ Nonempty (G₀ ⧸ H₀ ≃* G ⧸ H) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn H _
  have : Fact p.Prime := ⟨hp⟩
  by_cases hHp : IsPGroup p H
  · exact ⟨G, inferInstance, inferInstance, H, inferInstance, hHp, le_rfl, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨r, hr, hrH, hrp⟩ : ∃ r, r.Prime ∧ r ∣ Nat.card H ∧ r ≠ p := by
    by_contra hno
    push Not at hno
    apply hHp
    have hcard := Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdH => hno d hd hdH)
    exact IsPGroup.of_card hcard
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨R⟩ : Nonempty (Sylow r ↥H) := inferInstance
  set R' : Subgroup G := (R : Subgroup ↥H).map H.subtype with hR'def
  have hR'H : R' ≤ H := Subgroup.map_subtype_le _
  have hR'card : Nat.card R' = r ^ (Nat.card H).factorization r := by
    rw [hR'def, Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity]
  have hR'1 : R' ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card R' = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hR'card] at h1
    have h2 : (Nat.card H).factorization r ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd hr Nat.card_pos.ne' hrH).ne'
    exact h2 (by simpa [hr.one_lt.ne'] using (Nat.pow_eq_one.mp h1))
  by_cases hN : Subgroup.normalizer (R' : Set G) = ⊤
  ·
    have hR'n : R'.Normal := Subgroup.normalizer_eq_top_iff.mp hN
    have hlt : Nat.card (G ⧸ R') < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup R']
      have h1 : 1 < Nat.card R' := by
        rw [hR'card]
        exact Nat.one_lt_pow (Nat.Prime.factorization_pos_of_dvd hr Nat.card_pos.ne' hrH).ne'
          hr.one_lt
      have h2 : 0 < Nat.card (G ⧸ R') := Nat.card_pos
      nlinarith
    have hHn' : (H.map (QuotientGroup.mk' R')).Normal :=
      Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective R')
    obtain ⟨G₀, _, _, H₀, _, hH₀, hr₀, ⟨e⟩⟩ := ih _ hlt (G ⧸ R') rfl (H.map (QuotientGroup.mk' R'))
    have hpR : ¬ p ∣ Nat.card R' := by
      rw [hR'card]
      intro h
      exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)).symm
    refine ⟨G₀, inferInstance, inferInstance, H₀, inferInstance, hH₀, ?_,
      ⟨e.trans (QuotientGroup.quotientQuotientEquivQuotient R' H hR'H)⟩⟩
    rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd hp R' hpR]
    exact hr₀
  ·
    set N := Subgroup.normalizer (R' : Set G) with hNdef
    have hlt : Nat.card N < n := by
      rw [← hn, ← Subgroup.card_top (G := G)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hN)
    have hHN : (H.subgroupOf N).Normal := Subgroup.Normal.subgroupOf inferInstance N
    obtain ⟨G₀, _, _, H₀, _, hH₀, hr₀, ⟨e⟩⟩ := ih _ hlt ↥N rfl (H.subgroupOf N)
    have hfr : N ⊔ H = ⊤ := Sylow.normalizer_sup_eq_top R
    let φ : ↥N →* G ⧸ H := (QuotientGroup.mk' H).comp N.subtype
    have hφ : Function.Surjective φ := by
      intro gb
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
      have hg : g ∈ ((N : Set G) * (H : Set G)) := by
        rw [← Subgroup.mul_normal, hfr]
        exact Subgroup.mem_top g
      obtain ⟨x, hx, h, hh, rfl⟩ := Set.mem_mul.mp hg
      refine ⟨⟨x, hx⟩, ?_⟩
      show (x : G ⧸ H) = ((x * h : G) : G ⧸ H)
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h).mpr hh, mul_one]
    have hker : H.subgroupOf N = φ.ker := by
      ext x
      rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      show (x : G) ∈ H ↔ ((x : G) : G ⧸ H) = 1
      rw [QuotientGroup.eq_one_iff]
    refine ⟨G₀, inferInstance, inferInstance, H₀, inferInstance, hH₀, ?_,
      ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ))⟩⟩
    refine hr₀.trans ?_
    rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hp,
      CFSG.SectionRank.pRank_eq_open_pRank_top p G]
    exact CFSG.SectionRank.pRank_mono hp.one_lt le_top

end CFSG.Quasithin.VolI.A131

namespace CFSG.Quasithin.ASInputs

open CFSG.Quasithin.VolI.A131

theorem AS_A_1_31_holds : AS_A_1_31 := by
  intro G _ _ p hp hp2 hr H _ hF
  have : Fact p.Prime := ⟨hp⟩
  have hC : Subgroup.centralizer (CFSG.pCore p (G ⧸ H) : Set (G ⧸ H)) ≤
      CFSG.pCore p (G ⧸ H) :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore (G ⧸ H) p).mpr hF
  obtain ⟨G₀, _, _, H₀, _, hH₀, hr₀, ⟨e⟩⟩ := exists_reduction hp _ G rfl H
  exact a131Concl_of_mulEquiv hp e (a131Concl_of_isPGroup hp hp2 (hr₀.trans hr) H₀ hH₀
    (centralizer_le_of_mulEquiv e hC))

end CFSG.Quasithin.ASInputs
