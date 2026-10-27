module

public import CFSG.Quasithin.Vol2.KGFactU35Star
public import CFSG.Quasithin.Vol2.KGFactAutSylowU35Syl
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316KGU35
public import CFSG.CharacterTheory.Semidihedral.FieldFactorOneSylowNormalizer
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryDiagonalOuterOrder

public section

namespace CFSG.Quasithin.H13.KGU35

open CFSG.Quasithin CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial

theorem card_outer_of_model {Q : Type} [Group Q] (hQ : StatedClassicalModel Q .PSU 3 5 1) :
    Nat.card (Outer Q) = 6 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hQ
  have hU : UnitaryFieldData 5 1 K := ⟨by norm_num, le_rfl, by rw [hK]; norm_num⟩
  let e2 : Q ≃* CFSG.ClassicalGroups.UnitaryFlag.unitaryPSU hU 3 :=
    e.trans (CFSG.ClassicalGroups.UnitaryFlag.unitaryPSUEquiv hU (n := 3) (by norm_num)).symm
  rw [Nat.card_congr (equivalence e2).toEquiv,
    (UnitaryHigher.unitary_full_diagonal_outer_order hU (n := 3) (by norm_num)
      (by norm_num)).2.2.2.2.1]
  norm_num

theorem aut_isPGroup_of_card {Q : Type} [Group Q] [Finite Q]
    (hQ : StatedClassicalModel Q .PSU 3 5 1) (P : Subgroup Q) (hP : Nat.card P = 16) :
    IsPGroup 2 (MulAut ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card Q = 126000 := (CFSG.RankThree.Classical.unitary_three_five_model Q hQ).1
  have hf : (Nat.card Q).factorization 2 = 4 := by
    rw [hcard, show (126000 : ℕ) = 2 ^ 4 * 7875 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 7875)]
    simp
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hQ
  obtain ⟨T, ⟨eT⟩⟩ := KGAutSyl.u35SylowSemidihedral_holds K hK
  obtain ⟨T₀, hT₀⟩ := Sylow.exists_comap_eq_of_injective T (f := e.symm.toMonoidHom)
    e.symm.injective
  have hT₀map : (T₀ : Subgroup Q).map e.toMonoidHom = T := by
    rw [← hT₀]
    exact Subgroup.map_equiv_eq_comap_symm e _
  let e1 : ↥(T₀ : Subgroup Q) ≃* CFSG.Open.SemidihedralGroup 4 :=
    ((e.subgroupMap (T₀ : Subgroup Q)).trans (MulEquiv.subgroupCongr hT₀map)).trans eT
  let P' : Sylow 2 Q := Sylow.ofCard P (by rw [hP, hf]; norm_num)
  let eP : ↥P ≃* CFSG.Open.SemidihedralGroup 4 :=
    ((MulEquiv.subgroupCongr (Sylow.coe_ofCard P _).symm).trans (Sylow.equiv P' T₀)).trans e1
  exact (CFSG.Semidihedral.FieldFactorOne.semidihedral_automorphism_isPGroup
    (n := 4) le_rfl).of_equiv (MulAut.congr eP).symm

theorem commute_of_aut_isPGroup {G : Type*} [Group G] {P : Subgroup G}
    (hP : IsPGroup 2 (MulAut ↥P)) {x : G} (hx : x ^ 5 = 1)
    (hxP : x ∈ Subgroup.normalizer (P : Set G)) : ∀ t ∈ P, t * x = x * t := by
  have hmem : ∀ z ∈ P, x * z * x⁻¹ ∈ P := fun z hz => (Subgroup.mem_normalizer_iff.mp hxP z).mp hz
  have hmem' : ∀ z ∈ P, x⁻¹ * z * x ∈ P := fun z hz => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxP) z).mp hz
    simpa using this
  let α : MulAut ↥P :=
    { toFun := fun z => ⟨x * z * x⁻¹, hmem z z.2⟩
      invFun := fun z => ⟨x⁻¹ * z * x, hmem' z z.2⟩
      left_inv := fun z => Subtype.ext (by simp [mul_assoc])
      right_inv := fun z => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun z w => Subtype.ext (by simp [mul_assoc]) }
  have hαpow : ∀ k : ℕ, ∀ z : ↥P, (((α ^ k) z : ↥P) : G) = x ^ k * z * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [pow_succ', MulAut.mul_apply]
      change x * (((α ^ k) z : ↥P) : G) * x⁻¹ = _
      rw [ih z, pow_succ', mul_inv_rev]
      group
  have hα5 : α ^ 5 = 1 := by
    ext z
    rw [hαpow, hx, one_mul, inv_one, mul_one]
    rfl
  obtain ⟨k, hk⟩ := hP α
  have hα1 : α = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hk
    have h2 := orderOf_dvd_of_pow_eq_one hα5
    have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left k (by norm_num)
    exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)
  intro t ht
  have h := congrArg (fun β : MulAut ↥P => ((β ⟨t, ht⟩ : ↥P) : G)) hα1
  change x * t * x⁻¹ = t at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

theorem exists_ne_one_commute {G : Type*} [Group G] [Finite G] {T : Subgroup G} {x : G}
    (hx : orderOf x = 5) (hxT : x ∈ Subgroup.normalizer (T : Set G))
    (hT : ¬ Nat.card T ≡ 1 [MOD 5]) : ∃ z ∈ T, z ≠ 1 ∧ z * x = x * z := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.zpowers_le.mpr hxT
  let _ : MulAction (Subgroup.zpowers x) T :=
    { smul := fun p z => ⟨(p : G) * z * (p : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hle p.2) z).mp z.2⟩
      one_smul := fun z => Subtype.ext (by
        change (1 : G) * z * (1 : G)⁻¹ = z
        group)
      mul_smul := fun p q z => Subtype.ext (by
        change (p : G) * q * z * ((p : G) * q)⁻¹ = (p : G) * ((q : G) * z * (q : G)⁻¹) * (p : G)⁻¹
        group) }
  have hcong := hP.card_modEq_card_fixedPoints T
  by_contra hno
  have hfix : MulAction.fixedPoints (Subgroup.zpowers x) T = {1} := by
    ext z
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hz
      by_contra hz1
      have h := congrArg Subtype.val (hz ⟨x, Subgroup.mem_zpowers x⟩)
      change x * (z : G) * x⁻¹ = z at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact hno ⟨z, z.2, fun h1 => hz1 (Subtype.ext h1), h.symm⟩
    · rintro rfl p
      exact Subtype.ext (by change (p : G) * 1 * (p : G)⁻¹ = 1; group)
  rw [hfix, Nat.card_coe_set_eq, Set.ncard_singleton] at hcong
  exact hT hcong

theorem exists_involution_of_ne_one {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) {x z : G} (hzT : z ∈ T) (hz1 : z ≠ 1) (hzx : z * x = x * z) :
    ∃ t ∈ T, orderOf t = 2 ∧ t * x = x * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := T ⊓ Subgroup.centralizer ({x} : Set G) with hC
  have hzC : z ∈ C := ⟨hzT, Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff.mp hh]
    exact hzx.symm⟩
  have hCp : IsPGroup 2 C := hT.to_le inf_le_left
  have hnt : Nontrivial C := ⟨⟨⟨z, hzC⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩
  obtain ⟨n, hn0, hn⟩ := hCp.nontrivial_iff_card.mp hnt
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := C) 2
    (hn.symm ▸ dvd_pow_self 2 (ne_of_gt hn0))
  refine ⟨t, t.2.1, by rw [Subgroup.orderOf_coe, ht], ?_⟩
  exact (Subgroup.mem_centralizer_iff.mp t.2.2 x (Set.mem_singleton x)).symm

theorem kgu35_holds : Ch4.KGU35 := by
  intro X _ _ S hSn hS hC F _ _ _ R K hR1 hR2 hKS _ hKR _ _
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSm : StatedClassicalModel ↥S .PSU 3 5 1 := hS
  by_cases hRS : R ⊓ S = ⊥
  · left
    refine ⟨hRS, ?_⟩
    let ψ : ↥R →* Outer ↥S :=
      (QuotientGroup.mk' (inner ↥S)).comp ((MulAut.conjNormal (H := S)).comp R.subtype)
    have hψ : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro r hr
      have hin : MulAut.conjNormal (H := S) (r : X) ∈ inner ↥S :=
        (QuotientGroup.eq_one_iff _).mp hr
      obtain ⟨s, hs⟩ := hin
      have hcen : (s : X)⁻¹ * r ∈ Subgroup.centralizer (S : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have h := congrArg (fun φ : MulAut ↥S => ((φ ⟨u, hu⟩ : ↥S) : X)) hs
        simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] at h
        calc u * ((s : X)⁻¹ * r) = (s : X)⁻¹ * ((s : X) * u * (s : X)⁻¹) * r := by group
          _ = (s : X)⁻¹ * ((r : X) * u * (r : X)⁻¹) * r := by rw [h]
          _ = (s : X)⁻¹ * r * u := by group
      rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcen
      have hrRS : (r : X) ∈ R ⊓ S := ⟨r.2, hcen ▸ s.2⟩
      rw [hRS, Subgroup.mem_bot] at hrRS
      exact Subtype.ext hrRS
    have hdvd : Nat.card R ∣ 6 := by
      have := Subgroup.card_dvd_of_injective ψ hψ
      rwa [card_outer_of_model hSm] at this
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hR2
    rw [hk] at hdvd ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hR1 (Subgroup.eq_bot_of_card_eq R (by rw [hk, pow_zero]))
    have hk1 : k ≤ 1 := by
      by_contra h
      have : 2 ^ 2 ∣ 6 := dvd_trans (pow_dvd_pow 2 (by omega)) hdvd
      norm_num at this
    obtain rfl : k = 1 := by omega
    norm_num
  · right
    intro x hxK hx5
    have hxS : x ∈ S := hKS hxK
    have hxR := hKR hxK
    have hTS : R ⊓ S ≤ S := inf_le_right
    have hT2 : IsPGroup 2 ↥(R ⊓ S) := hR2.to_le inf_le_left
    have hxT : x ∈ Subgroup.normalizer ((R ⊓ S : Subgroup X) : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [Subgroup.mem_inf, Subgroup.mem_inf]
      constructor
      · rintro ⟨hzR, hzS⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hxR z).mp hzR, hSn.conj_mem z hzS x⟩
      · rintro ⟨hzR, hzS⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp hxR z).mpr hzR, ?_⟩
        have := hSn.conj_mem _ hzS x⁻¹
        simpa [mul_assoc] using this
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
    have hcardS : Nat.card S = 126000 :=
      (CFSG.RankThree.Classical.unitary_three_five_model _ hSm).1
    have hk4 : k ≤ 4 := by
      have h1 : 2 ^ k ∣ 2 ^ 4 * 7875 := by
        rw [← hk, show 2 ^ 4 * 7875 = 126000 by norm_num, ← hcardS]
        exact Subgroup.card_dvd_of_le hTS
      have h2 : Nat.Coprime (2 ^ k) 7875 := Nat.Coprime.pow_left k (by norm_num)
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (h2.dvd_of_dvd_mul_right h1)
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hRS (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    obtain ⟨t, htT, ht2, htx⟩ : ∃ t ∈ R ⊓ S, orderOf t = 2 ∧ t * x = x * t := by
      by_cases h16 : k = 4
      · subst h16
        have hcT : Nat.card ((R ⊓ S).subgroupOf S) = 16 := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv, hk]
          norm_num
        have hAut : IsPGroup 2 (MulAut ↥(R ⊓ S)) :=
          (aut_isPGroup_of_card hSm _ hcT).of_equiv
            (MulAut.congr (Subgroup.subgroupOfEquivOfLe hTS))
        have hcomm := commute_of_aut_isPGroup hAut
          (orderOf_dvd_iff_pow_eq_one.mp (by rw [hx5])) hxT
        obtain hbot | ⟨z, hzT, hz1⟩ := Subgroup.bot_or_exists_ne_one (R ⊓ S)
        · exact absurd hbot hRS
        · exact exists_involution_of_ne_one hT2 hzT hz1 (hcomm z hzT)
      · have hmod : ¬ Nat.card ↥(R ⊓ S) ≡ 1 [MOD 5] := by
          rw [hk]
          interval_cases k <;> first | omega | decide
        obtain ⟨z, hzT, hz1, hzx⟩ := exists_ne_one_commute hx5 hxT hmod
        exact exists_involution_of_ne_one hT2 hzT hz1 hzx
    have htS : t ∈ S := hTS htT
    obtain ⟨a, b, hab, hcl⟩ := star_of_model hSm (x := ⟨x, hxS⟩) (t := ⟨t, htS⟩)
      (by rw [Subgroup.orderOf_mk, hx5]) (by rw [Subgroup.orderOf_mk, ht2])
      (Subtype.ext htx)
    refine ⟨a, a.2, b, b.2, by simpa using congrArg Subtype.val hab, fun g hg => ?_⟩
    have hmap : Subgroup.closure ({(a : X), (b : X)} : Set X) =
        (Subgroup.closure ({a, b} : Set ↥S)).map S.subtype := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [hmap] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨h5, hc⟩ := hcl g' hg'
    exact ⟨by simpa using congrArg Subtype.val h5, by simpa using congrArg Subtype.val hc⟩

end CFSG.Quasithin.H13.KGU35
