module

public import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.Milestones.OO_odd_order_solvable
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Pair

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem lA_congr [Finite G] {A : Subgroup G} {c c' : G}
    (h : Subgroup.zpowers c = Subgroup.zpowers c') : lA A c = lA A c' := by
  have hC := centralizer_singleton_eq_of_zpowers_eq h
  unfold lA thetaComponentsAt
  rw [hC, h]

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro m
    obtain ⟨y, rfl⟩ := e.surjective m
    rw [← map_mul, ← map_mul, hx y]
  rw [hY, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans e.map_one.symm)

variable {A L : Subgroup G} {c : G}

theorem not_mem_of_center_eq_bot (h : Sec13Data G A c L)
    (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥) : c ∉ L := by
  intro hcL
  obtain ⟨η, -⟩ := exists_lBarEquiv h.mem_thetaComponentsAt
  have hmem : ((mkC (L := L) h.mem_A : lBarA c L A) :
      Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) ∈
      Sec12.lBar c L :=
    ⟨⟨c, le_normalizer_zpowers_of_mem h.mem_thetaComponentsAt hcL⟩,
      Subgroup.mem_subgroupOf.mpr hcL, rfl⟩
  have hcen : η.symm ⟨_, hmem⟩ ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply η.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    have h1 := Subgroup.mem_center_iff.mp (mkC_mem_center h)
      ⟨(η w : _), lBar_le_lBarA (η w).2⟩
    have h3 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul] at h3 ⊢
    exact h3
  rw [hZ, Subgroup.mem_bot] at hcen
  apply mkC_ne_one h
  apply Subtype.ext
  have h2 := congrArg η hcen
  rw [MulEquiv.apply_symm_apply, map_one] at h2
  have h4 := congrArg Subtype.val h2
  simpa using h4

theorem mk_commute_of_le_sup {K E : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c)
    (hL : L ∈ thetaComponentsAt 3 c) (hKL : K ≠ L) (hEL : E ≤ Subgroup.zpowers c ⊔ L)
    {x k : Subgroup.normalizer (Subgroup.zpowers c : Set G)} (hx : (x : G) ∈ E)
    (hk : (k : G) ∈ K) :
    QuotientGroup.mk' (aschbacherSolvableCore 3
        (Subgroup.normalizer (Subgroup.zpowers c : Set G))) x * QuotientGroup.mk' _ k =
      QuotientGroup.mk' _ k * QuotientGroup.mk' _ x := by
  revert x k
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hN
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 N) with hπ
  intro x k hx hk
  have hKN : K ≤ N := le_normalizer_zpowers_of_mem hK
  have hLN : L ≤ N := le_normalizer_zpowers_of_mem hL
  have hK₁ := subgroupOf_normalizer_mem_thetaComponents hK
  have hL₁ := subgroupOf_normalizer_mem_thetaComponents hL
  have hne₁ : K.subgroupOf N ≠ L.subgroupOf N := by
    intro h
    apply hKL
    have h' := congrArg (Subgroup.map N.subtype) h
    rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hKN, inf_eq_left.mpr hLN] at h'
  have hKc := isComponent_map_of_mem_thetaComponents Nat.prime_three hK₁
  have hLc := isComponent_map_of_mem_thetaComponents Nat.prime_three hL₁
  have hneb : (K.subgroupOf N).map π ≠ (L.subgroupOf N).map π := fun h =>
    hne₁ ((theta_component_quotient_correspondence Nat.prime_three).1.injOn hK₁ hL₁ h)
  have hcomm := (LocalCores.distinct_components_commute hKc hLc).resolve_left hneb
  have hkb : π k ∈ (K.subgroupOf N).map π :=
    Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hk)
  have hKL' : ∀ y ∈ (L.subgroupOf N).map π, y * π k = π k * y := fun y hy =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hkb)
      y hy
  have hcLn : (Subgroup.zpowers c : Subgroup G) ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun l hl => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hL hl)
  have hx' : (x : G) ∈ ((Subgroup.zpowers c ⊔ L : Subgroup G) : Set G) := hEL hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcLn] at hx'
  obtain ⟨y, hy, l, hl, hyl⟩ := Set.mem_mul.mp hx'
  have hyN : y ∈ N := (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer (Subgroup.mem_zpowers c)))
    hy
  have hlN : l ∈ N := hLN hl
  have hxe : x = ⟨y, hyN⟩ * ⟨l, hlN⟩ := Subtype.ext hyl.symm
  have hyk : (⟨y, hyN⟩ : N) * k = k * ⟨y, hyN⟩ := by
    apply Subtype.ext
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hkc := Subgroup.mem_centralizer_singleton_iff.mp
      (Sec6.le_centralizer_of_mem_thetaComponentsAt hK hk)
    exact ((Commute.zpow_left (show Commute c (k : G) from hkc.symm) i)).eq
  have hlk := hKL' (π ⟨l, hlN⟩) (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hl))
  rw [hxe, map_mul, mul_assoc, hlk, ← mul_assoc, ← map_mul, hyk, map_mul, mul_assoc]

theorem exists_twoSubgroup_of_mk_commute {K E : Subgroup G} (hK : K ∈ thetaComponentsAt 3 c)
    (hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) (hE3 : IsPGroup 3 E)
    (hcomm : ∀ x k : Subgroup.normalizer (Subgroup.zpowers c : Set G), (x : G) ∈ E →
      (k : G) ∈ K →
      QuotientGroup.mk' (aschbacherSolvableCore 3
          (Subgroup.normalizer (Subgroup.zpowers c : Set G))) x * QuotientGroup.mk' _ k =
        QuotientGroup.mk' _ k * QuotientGroup.mk' _ x) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hN
  set θ := aschbacherSolvableCore 3 N with hθ
  set π := QuotientGroup.mk' θ with hπ
  have hK₁ := subgroupOf_normalizer_mem_thetaComponents hK
  set Kb := (K.subgroupOf N).map π with hKb
  have hKc := isComponent_map_of_mem_thetaComponents Nat.prime_three hK₁
  have h2 : 2 ∣ Nat.card Kb := by
    by_contra hodd
    have hodd' : Odd (Nat.card Kb) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
    have hsol : Group.IsSolvable Kb := CFSG.Milestones.odd_order_solvable hodd'
    have hperf : Group.IsPerfect Kb := hKc.1.1
    have hnt : Nontrivial Kb := by
      obtain ⟨a, b, hab⟩ := hKc.1.2.2
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact hab (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isSolvable Kb hsol
  obtain ⟨T⟩ : Nonempty (Sylow 2 Kb) := inferInstance
  have hT1 : (T : Subgroup Kb) ≠ ⊥ := T.ne_bot_of_dvd_card h2
  set Tb := (T : Subgroup Kb).map Kb.subtype with hTb
  set Y := Tb.comap π with hY
  have hY3 : ¬ 3 ∣ Nat.card Y := by
    intro h3
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 3 h3
    have hyT : π y ∈ Tb := y.2
    have h1 : π y = 1 := by
      obtain ⟨t, htT, ht⟩ := hyT
      obtain ⟨m, hm⟩ := T.isPGroup' ⟨t, htT⟩
      have ha : (π (y : N)) ^ 3 = 1 := by
        rw [← map_pow]
        have : (y : N) ^ 3 = 1 := by
          rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
        rw [this, map_one]
      have hb : (π (y : N)) ^ 2 ^ m = 1 := by
        rw [← ht]
        have := congrArg (fun z : T => ((z : Kb) : N ⧸ θ)) hm
        simpa using this
      have hcop : Nat.Coprime 3 (2 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
      have := pow_gcd_eq_one.mpr ⟨ha, hb⟩
      rwa [hcop, pow_one] at this
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdvd : orderOf (y : N) ∣ Nat.card θ := Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_coe, hy] at hdvd
    exact three_not_dvd_card_aschbacherSolvableCore hdvd
  set E₁ := E.subgroupOf N with hE₁
  have hE₁3 : IsPGroup 3 E₁ := hE3.of_equiv (Subgroup.subgroupOfEquivOfLe hEN).symm
  have hconj : ∀ e : N, (e : G) ∈ E → ∀ z ∈ Y, e * z * e⁻¹ ∈ Y := by
    intro e he z hz
    have hzK : π z ∈ Kb := by
      obtain ⟨t, -, ht⟩ := hz
      rw [← ht]
      exact t.2
    obtain ⟨k, hk, hkz⟩ := hzK
    have hc := hcomm e k he (Subgroup.mem_subgroupOf.mp hk)
    change π (e * z * e⁻¹) ∈ Tb
    have hez : π (e * z * e⁻¹) = π z := by
      rw [map_mul, map_mul, map_inv, ← hkz]
      change π e * π k * (π e)⁻¹ = π k
      rw [hc, mul_inv_cancel_right]
    rw [hez]
    exact hz
  have hE₁Y : E₁ ≤ Subgroup.normalizer (Y : Set N) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro z
    refine ⟨hconj e (Subgroup.mem_subgroupOf.mp he) z, fun hz => ?_⟩
    have h1 := hconj e⁻¹ (Subgroup.mem_subgroupOf.mp (E₁.inv_mem he)) _ hz
    simpa [mul_assoc] using h1
  have hbot : E₁ ≤ Subgroup.normalizer ((⊥ : Subgroup N) : Set N) := by
    intro e _
    rw [Subgroup.mem_normalizer_iff]
    intro z
    simp only [Subgroup.mem_bot]
    constructor
    · rintro rfl
      group
    · intro h
      have : z = e⁻¹ * (e * z * e⁻¹) * e := by group
      rw [this, h]
      group
  obtain ⟨R, ⟨Q, hQR⟩, -, hER⟩ := CFSG.ABGLocalTools.exists_invariant_isSylowOf_ge_of_coprime
    Nat.prime_three Nat.prime_two hE₁3 hE₁Y hY3 bot_le IsPGroup.of_bot hbot
  have h2T : 2 ∣ Nat.card (T : Subgroup Kb) := T.dvd_card_of_dvd_card h2
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2T
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective θ (((t : Kb) : N ⧸ θ))
  have hyY : y ∈ Y := by
    change π y ∈ Tb
    rw [hπ, hy]
    exact ⟨t, t.2, rfl⟩
  have h2Y : 2 ∣ Nat.card Y := by
    have h1 : orderOf (((t : Kb) : N ⧸ θ)) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
    have h3 : orderOf (((t : Kb) : N ⧸ θ)) ∣ orderOf y := by
      rw [← hy]
      exact orderOf_map_dvd _ _
    have h4 : orderOf y ∣ Nat.card Y := by
      rw [← Subgroup.orderOf_mk y hyY]
      exact orderOf_dvd_natCard _
    rw [h1] at h3
    exact h3.trans h4
  have hQ1 : (Q : Subgroup Y) ≠ ⊥ := Q.ne_bot_of_dvd_card h2Y
  refine ⟨R.map N.subtype, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective, ← hQR,
      Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective]
    exact hQ1
  · rw [← hQR]
    exact (Q.isPGroup'.map _).map _
  · intro e he
    have he₁ : (⟨e, hEN he⟩ : N) ∈ E₁ := Subgroup.mem_subgroupOf.mpr he
    exact Subgroup.le_normalizer_map N.subtype ⟨_, hER he₁, rfl⟩

theorem facts_of_not_mem (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (h : Sec13Data G A c L) (hcL : c ∉ L) :
    (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12)) ∧
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ ∧
    (Nat.card (A ⊓ L : Subgroup G) = 9 ∨ Sec8.IsZ3PGLThreePi (lBarA c L A)) := by
  have hspor' := hspor
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor'
  have hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  rcases cases131 h131 hspor hSLC h with ⟨-, h9, -, hc⟩ | ⟨-, h9, hMJ, -⟩ |
      ⟨-, hPGL, -, -⟩ | ⟨hcL', -⟩
  · rcases hc with ⟨hL3, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · refine ⟨Or.inr (Or.inl hL3), ?_, Or.inl h9⟩
      obtain ⟨p, e, hp, he, hcase⟩ := hL3
      rcases hcase with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
      · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSL p e he hq3).2
      · by_cases hq2 : 2 < p ^ e
        · exact center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU p e he hq3 hq2).2
        · exfalso
          have h2 : p ^ e = 2 := by
            have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
            omega
          obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
          have := isSolvable_projSU_two
          have hsol : Group.IsSolvable (L ⧸ aschbacherSolvableCore 3 L) :=
            Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
          have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) := by
            obtain ⟨a, b, hab⟩ := hq.2.2
            by_contra hn
            rw [not_nontrivial_iff_subsingleton] at hn
            apply hab
            have : Subsingleton ((L ⧸ aschbacherSolvableCore 3 L) ⧸
                Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) :=
              QuotientGroup.mk_surjective.subsingleton
            exact Subsingleton.elim _ _
          have := hq.1
          exact Group.IsPerfect.not_isSolvable _ hsol
    · exact ⟨Or.inr (Or.inr (Or.inl ⟨φ⟩)), center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2,
        Or.inl h9⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨φ⟩))), center_eq_bot_of_mulEquiv φ hM22z,
        Or.inl h9⟩
  · rcases hMJ with hM | hJ
    · obtain ⟨φ⟩ := hM
      obtain ⟨ψ⟩ := nonempty_thetaQuot_equiv h hM12p φ
      exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨ψ⟩))), center_eq_bot_of_mulEquiv ψ hM12z,
        Or.inl h9⟩
    · obtain ⟨φ⟩ := hJ
      obtain ⟨ψ⟩ := nonempty_thetaQuot_equiv h hJ2p φ
      exact ⟨Or.inl ⟨ψ⟩, center_eq_bot_of_mulEquiv ψ hJ2z, Or.inl h9⟩
  · obtain ⟨hL3, hZ, -⟩ := facts_of_isZ3PGLThreePi h hPGL
    exact ⟨Or.inr (Or.inl hL3), hZ, Or.inr hPGL⟩
  · exact absurd hcL' hcL

theorem le_zpowers_sup_of_card_inf (h : Sec13Data G A c L) (hcL : c ∉ L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) : A ≤ Subgroup.zpowers c ⊔ L := by
  set S := (A ⊓ L) ⊔ Subgroup.zpowers c with hS
  have hle : S ≤ A := sup_le inf_le_left (Subgroup.zpowers_le.mpr h.mem_A)
  have hlt : A ⊓ L < S := by
    refine lt_of_le_of_ne le_sup_left fun he => hcL ?_
    have : c ∈ A ⊓ L := by
      rw [he]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    exact this.2
  have h1 := Subgroup.card_lt_of_lt hlt
  have h2 : Nat.card (A ⊓ L : Subgroup G) ∣ Nat.card S := Subgroup.card_dvd_of_le le_sup_left
  have h3 : Nat.card S ∣ Nat.card A := Subgroup.card_dvd_of_le hle
  rw [h.card_eq] at h3
  rw [h9] at h1 h2
  have h4 : Nat.card S = 27 := by
    have h5 := Nat.le_of_dvd (by norm_num) h3
    obtain ⟨k, hk⟩ := h2
    have hk3 : k ≤ 3 := by omega
    interval_cases k <;> simp_all
  have heq : S = A := Subgroup.eq_of_le_of_card_ge hle (by rw [h4, h.card_eq])
  rw [← heq]
  exact sup_le (inf_le_right.trans le_sup_right) le_sup_left

theorem moreover_of_not_mem (h131 : Item131) (hspor : SporadicModels131) (hSLC : SLTwoCenter)
    (h : Sec13Data G A c L) (hcL : c ∉ L) :
    ∀ K ∈ thetaComponentsAt 3 c, 3 ∣ Nat.card K → K = L := by
  intro K hK h3
  obtain ⟨-, hZ, h9 | hPGL⟩ := facts_of_not_mem h131 hspor hSLC h hcL
  · refine eq_of_mem_thetaComponentsAt_of_maximal h.orderOf_eq h.mem_thetaComponentsAt hZ
      (le_zpowers_sup_of_card_inf h hcL h9) h.isElemAbelian ?_ hK h3
    intro F hF hAF
    rw [h.eq_of_le hF hAF]
  · by_contra hKL
    obtain ⟨-, -, D, hDL, hD, hD9⟩ := facts_of_isZ3PGLThreePi h hPGL
    have hLC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
    have hc3 : c ^ 3 = 1 := by rw [← h.orderOf_eq]; exact pow_orderOf_eq_one c
    have hcD : ∀ x ∈ Subgroup.zpowers c, ∀ y ∈ D, x * y = y * x := by
      intro x hx y hy
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hyc := Subgroup.mem_centralizer_singleton_iff.mp (hLC (hDL hy))
      exact (Commute.zpow_left (show Commute c y from hyc.symm) i).eq
    set E := Subgroup.zpowers c ⊔ D with hEdef
    have hEab : CFSG.Assembly.IsElemAbelian 3 E :=
      isElemAbelian_sup (isElemAbelian_zpowers hc3) hD hcD
    have hinf : Subgroup.zpowers c ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_bot]
      by_contra hx1
      have hxo : orderOf x = 3 := by
        refine orderOf_eq_prime ?_ hx1
        exact (isElemAbelian_zpowers hc3).2 x hx.1
      have hle : Subgroup.zpowers x ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hx.1
      have heq : Subgroup.zpowers x = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hxo,
          h.orderOf_eq])
      have hcx : c ∈ Subgroup.zpowers x := heq ▸ Subgroup.mem_zpowers c
      exact hcL (hDL ((Subgroup.zpowers_le.mpr hx.2) hcx))
    have hcard : Nat.card E = 27 := by
      have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcD).1
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, h.orderOf_eq, hD9] at h1
      exact h1
    have hEL : E ≤ Subgroup.zpowers c ⊔ L := sup_le_sup_left hDL _
    have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
      (sup_le (Subgroup.zpowers_le.mpr hcC) (hDL.trans hLC)).trans
        (centralizer_le_normalizer_zpowers c)
    have hE3 : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hEab.2 x x.2)⟩
    obtain ⟨U, hU1, hU2, hEU⟩ := exists_twoSubgroup_of_mk_commute hK hEN hE3
      (fun x k hx hk => mk_commute_of_le_sup hK h.mem_thetaComponentsAt hKL hEL hx hk)
    have hEE : E ∈ partTwoE G := ⟨hEab, hcard, U, hU1, hU2, hEU⟩
    have hmax : ∀ F : Subgroup G, CFSG.Assembly.IsElemAbelian 3 F → E ≤ F →
        Nat.card F ≤ Nat.card E := by
      intro F hF hEF
      obtain ⟨F', hFF', hF'⟩ :=
        Finite.exists_le_maximal (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) hF
      have hF'F : F' ∈ partTwoF G :=
        ⟨hF'.1, fun B hB hFB => le_antisymm (hF'.2 hB hFB) hFB, E, hEE, hEF.trans hFF'⟩
      rw [(h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1] at hF'F
      rw [hcard, ← hF'F.2.1]
      exact Subgroup.card_le_of_le hFF'
    exact hKL (eq_of_mem_thetaComponentsAt_of_maximal h.orderOf_eq h.mem_thetaComponentsAt hZ
      hEL hEab hmax hK h3)

end Pair

end CFSG.RankThree.PartTwo.Sec13
