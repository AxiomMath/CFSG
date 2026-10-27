module

public import CFSG.RankThree.PartTwo.Sec16.Item16KFactsProofNoSz
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofLin
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofSz
public import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki

public section

namespace CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

open Matrix CFSG.Blueprint
open CFSG.RankThree.PartTwo.Sec16.Steps166 CFSG.RankThree.PartTwo.Sec16.KSL3PiNoSzProof

section Minimal

variable {G Q : Type*} [Group G] [Finite G] [Group Q] {φ : G →* Q}

omit [Finite G] in
theorem map_eq_bot_of_le_ker {H : Subgroup G} (hH : H ≤ φ.ker) : H.map φ = ⊥ :=
  (Subgroup.map_eq_bot_iff H).mpr hH

omit [Finite G] in
theorem isPerfect_of_minimal (hφ : Function.Surjective φ)
    (hmin : ∀ H : Subgroup G, H.map φ = ⊤ → H = ⊤) (hQp : Group.IsPerfect Q) :
    Group.IsPerfect G := by
  refine Group.isPerfect_def.mpr (hmin _ ?_)
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ,
    ← commutator_def, hQp.commutator_eq_top]

theorem sylow_normal_of_minimal (hφ : Function.Surjective φ)
    (hmin : ∀ H : Subgroup G, H.map φ = ⊤ → H = ⊤) (ℓ : ℕ) [Fact ℓ.Prime] (P : Sylow ℓ φ.ker) :
    ((P : Subgroup φ.ker).map φ.ker.subtype).Normal := by
  have hF := Sylow.normalizer_sup_eq_top P
  have h1 := congrArg (Subgroup.map φ) hF
  rw [Subgroup.map_sup, Subgroup.map_top_of_surjective φ hφ, map_eq_bot_of_le_ker le_rfl,
    sup_bot_eq] at h1
  exact Subgroup.normalizer_eq_top_iff.mp (hmin _ h1)

theorem isNilpotent_ker_of_minimal (hφ : Function.Surjective φ)
    (hmin : ∀ H : Subgroup G, H.map φ = ⊤ → H = ⊤) : Group.IsNilpotent φ.ker :=
  (Group.isNilpotent_of_finite_tfae.out 1 4).mpr fun ℓ hℓ P => by
    have := hℓ
    exact (sylow_normal_of_minimal hφ hmin ℓ P).of_map_subtype

omit [Finite G] in
theorem card_eq_card_ker_mul (hφ : Function.Surjective φ) :
    Nat.card G = Nat.card φ.ker * Nat.card Q := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, mul_comm]

theorem not_dvd_card_ker_of_minimal (hφ : Function.Surjective φ)
    (hmin : ∀ H : Subgroup G, H.map φ = ⊤ → H = ⊤) {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (hQℓ : ¬ ℓ ∣ Nat.card Q) : ¬ ℓ ∣ Nat.card φ.ker := by
  obtain ⟨P⟩ : Nonempty (Sylow ℓ φ.ker) := inferInstance
  set R := (P : Subgroup φ.ker).map φ.ker.subtype with hR
  have hRn : R.Normal := sylow_normal_of_minimal hφ hmin ℓ P
  have hRN : R ≤ φ.ker := Subgroup.map_subtype_le _
  have hRcard : Nat.card R = Nat.card (P : Subgroup φ.ker) :=
    Subgroup.card_map_of_injective φ.ker.subtype_injective
  obtain ⟨k, hk⟩ := (P.isPGroup').exists_card_eq
  have hidx : ¬ ℓ ∣ R.index := by
    rw [← Subgroup.relIndex_mul_index hRN]
    have h1 : R.relIndex φ.ker = (P : Subgroup φ.ker).index := by
      rw [Subgroup.relIndex, hR, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective φ.ker.subtype_injective]
    have h2 : φ.ker.index = Nat.card Q := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφ, Subgroup.card_top]
    rw [h1, h2]
    intro h
    rcases (Nat.Prime.dvd_mul hℓ.out).mp h with h | h
    · exact P.not_dvd_index h
    · exact hQℓ h
  have hcop : Nat.Coprime (Nat.card R) R.index := by
    rw [hRcard, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hℓ.out).mpr hidx)
  obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hHtop : H = ⊤ := by
    refine hmin H ?_
    have h1 := congrArg (Subgroup.map φ) hH.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective φ hφ, map_eq_bot_of_le_ker hRN,
      bot_sup_eq] at h1
    exact h1
  have hRbot : R = ⊥ := by
    have h1 := hH.disjoint
    rw [hHtop, disjoint_top] at h1
    exact h1
  have hP1 : Nat.card (P : Subgroup φ.ker) = 1 := by
    rw [← hRcard, hRbot, Subgroup.card_bot]
  intro hdvd
  have h1 := P.dvd_card_of_dvd_card hdvd
  rw [hP1] at h1
  exact hℓ.out.one_lt.ne' (Nat.dvd_one.mp h1)

end Minimal

section Linear

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem le_normalizer_map_of_normal {X : Subgroup (GL (Fin 3) K)} {R : Subgroup X}
    (hR : R.Normal) : X ≤ Subgroup.normalizer (R.map X.subtype : Set (GL (Fin 3) K)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨r, hr, rfl⟩
    refine ⟨⟨x, hx⟩ * r * ⟨x, hx⟩⁻¹, hR.conj_mem r hr _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  · rintro ⟨r, hr, hrn⟩
    refine ⟨⟨x, hx⟩⁻¹ * r * ⟨x, hx⟩, ?_, ?_⟩
    · have := hR.conj_mem r hr ⟨x, hx⟩⁻¹
      rwa [inv_inv] at this
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hrn ⊢
      rw [hrn]
      group

theorem eq_bot_of_normal_isPGroup {p : ℕ} [Fact p.Prime] [CharP K p]
    {X : Subgroup (GL (Fin 3) K)} (hXp : Group.IsPerfect X) (hX3 : ¬ 3 ∣ Nat.card X)
    {R : Subgroup X} (hRn : R.Normal) (hR : IsPGroup p R) (hR1 : R ≠ ⊥) : X = ⊥ := by
  have hRG : IsPGroup p (R.map X.subtype) := hR.map X.subtype
  have hRG1 : R.map X.subtype ≠ ⊥ := fun h =>
    hR1 ((Subgroup.map_eq_bot_iff_of_injective R X.subtype_injective).mp h)
  obtain ⟨W, hW, hW0, hWt⟩ :=
    exists_invariant_of_isPGroup hRG hRG1 (le_normalizer_map_of_normal hRn)
  exact eq_bot_of_invariant X hXp hX3 W hW hW0 hWt

omit [Finite K] in
theorem det_eq_one_of_isPerfect {X : Subgroup (GL (Fin 3) K)} (hXp : Group.IsPerfect X) :
    ∀ x ∈ X, (x : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  intro x hx
  have h1 := Sec6.BThreeCensus.map_eq_one_of_isPerfect hXp
    (Matrix.GeneralLinearGroup.det.comp X.subtype) ⟨x, hx⟩
  have h2 := congrArg Units.val h1
  simpa using h2

omit [Finite K] in
theorem le_normalizer_center_of_normal {X : Subgroup (GL (Fin 3) K)} {N : Subgroup X}
    (hNn : N.Normal) : X ≤ Subgroup.normalizer
      ((((Subgroup.center N).map N.subtype).map X.subtype : Subgroup (GL (Fin 3) K)) :
        Set (GL (Fin 3) K)) := by
  refine le_normalizer_map_of_normal ⟨fun z hz x => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hz
  have hzN : x * (z : X) * x⁻¹ ∈ N := hNn.conj_mem _ z.2 x
  refine ⟨⟨x * (z : X) * x⁻¹, hzN⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_center_iff]
  rw [SetLike.mem_coe] at hz
  intro w
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have hw : x⁻¹ * (w : X) * x ∈ N := by
    have := hNn.conj_mem _ w.2 x⁻¹
    simpa using this
  have h1 := Subgroup.mem_center_iff.mp hz ⟨_, hw⟩
  have h2 := congrArg (fun u : N => (u : X)) h1
  simp only [Subgroup.coe_mul] at h2
  calc (w : X) * (x * z * x⁻¹) = x * ((x⁻¹ * w * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * w * x)) * x⁻¹ := by rw [h2]
    _ = x * z * x⁻¹ * w := by group

theorem eq_one_of_mem_of_commute {X : Subgroup (GL (Fin 3) K)}
    (hXp : Group.IsPerfect X) (hX3 : ¬ 3 ∣ Nat.card X) (hX1 : X ≠ ⊥) {m : GL (Fin 3) K}
    (hmX : m ∈ X) (hm : ∀ g ∈ X, g * m = m * g) : m = 1 := by
  by_cases hsc : ∃ c : K, (m : Matrix (Fin 3) (Fin 3) K) = c • 1
  · obtain ⟨c, hc⟩ := hsc
    have hc3 : c ^ 3 = 1 := by
      have := det_eq_one_of_isPerfect hXp m hmX
      rw [hc, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at this
      exact this
    have hm3 : m ^ 3 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hc, smul_pow, one_pow, hc3, one_smul, Units.val_one]
    have hord : orderOf m ∣ Nat.gcd 3 (Nat.card X) := by
      refine Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm3) ?_
      have := orderOf_dvd_natCard (⟨m, hmX⟩ : X)
      rwa [Subgroup.orderOf_mk] at this
    have hgcd : Nat.gcd 3 (Nat.card X) = 1 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hX3
    rw [hgcd, Nat.dvd_one, orderOf_eq_one_iff] at hord
    exact hord
  · push Not at hsc
    exact absurd (eq_bot_of_commute_of_not_scalar X hXp hX3 m hsc fun g hg =>
      congrArg Units.val (hm g hg)) hX1

theorem center_eq_bot_of_normal {X : Subgroup (GL (Fin 3) K)}
    (hXp : Group.IsPerfect X) (hX3 : ¬ 3 ∣ Nat.card X) (hX1 : X ≠ ⊥) {N : Subgroup X}
    (hNn : N.Normal) (hNK : (Nat.card N : K) ≠ 0) : Subgroup.center N = ⊥ := by
  classical
  set M : Subgroup (GL (Fin 3) K) := ((Subgroup.center N).map N.subtype).map X.subtype with hM
  have hMmem : ∀ m ∈ M, ∃ z : N, z ∈ Subgroup.center N ∧ ((z : X) : GL (Fin 3) K) = m := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  have hMX : M ≤ X := Subgroup.map_subtype_le _
  have hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
    intro x hx y hy
    obtain ⟨z, hz, rfl⟩ := hMmem x hx
    obtain ⟨z', -, rfl⟩ := hMmem y hy
    have h1 := Subgroup.mem_center_iff.mp hz z'
    have h2 := congrArg (fun w : N => ((w : X) : GL (Fin 3) K)) h1
    simp only [Subgroup.coe_mul] at h2
    exact h2.symm
  have hMn : ∀ m ∈ M, m ^ Nat.card N = 1 := by
    intro m hm
    obtain ⟨z, -, rfl⟩ := hMmem m hm
    rw [← Subgroup.coe_pow, ← Subgroup.coe_pow, pow_card_eq_one', Subgroup.coe_one,
      Subgroup.coe_one]
  have hcent := le_centralizer_of_le_normalizer hMc hMn hNK (le_normalizer_center_of_normal hNn)
    hXp hX3
  rw [eq_bot_iff]
  intro z hz
  have h1 := eq_one_of_mem_of_commute hXp hX3 hX1 (hMX ⟨_, ⟨z, hz, rfl⟩, rfl⟩)
    fun g hg => hcent g hg _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  rw [Subgroup.mem_bot]
  exact Subtype.ext (Subtype.ext h1)

theorem false_of_minimal
    (X : Subgroup (GL (Fin 3) K)) {Q : Type} [Group Q] {p f : ℕ} (hQ : SuzukiModel Q p f)
    (φ : X →* Q) (hφ : Function.Surjective φ)
    (hmin : ∀ H : Subgroup X, H.map φ = ⊤ → H = ⊤) : False := by
  classical
  have : Finite Q := KFacts.KP7.finite_of_suzukiModel hQ
  have hQ3 : ¬ 3 ∣ Nat.card Q := KFacts.KP7.three_not_dvd_card hQ
  have hX1 : X ≠ ⊥ := by
    intro h
    have hQ5 := five_dvd_card_of_suzukiModel hQ
    have hQ1 : Nat.card Q = 1 := by
      have h1 := card_eq_card_ker_mul hφ
      have h2 : Nat.card X = 1 := by rw [h, Subgroup.card_bot]
      rw [h2] at h1
      exact (Nat.eq_one_of_mul_eq_one_left h1.symm)
    rw [hQ1] at hQ5
    norm_num at hQ5
  have hXp : Group.IsPerfect X := isPerfect_of_minimal hφ hmin (isPerfect_of_suzukiModel hQ)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hN3 := not_dvd_card_ker_of_minimal hφ hmin hQ3
  have hX3 : ¬ 3 ∣ Nat.card X := by
    rw [card_eq_card_ker_mul hφ]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact hN3 h
    · exact hQ3 h
  obtain ⟨p', hp'⟩ := CharP.exists K
  have hp'prime : p'.Prime := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hprime, -⟩ := FiniteField.card K p'
    exact hprime
  have : Fact p'.Prime := ⟨hp'prime⟩
  have hNp : ¬ p' ∣ Nat.card φ.ker := by
    intro hdvd
    obtain ⟨P⟩ : Nonempty (Sylow p' φ.ker) := inferInstance
    have hRn := sylow_normal_of_minimal hφ hmin p' P
    refine hX1 (eq_bot_of_normal_isPGroup hXp hX3 hRn (P.isPGroup'.map _) fun h => ?_)
    have h1 : Nat.card (P : Subgroup φ.ker) = 1 := by
      rw [← Subgroup.card_map_of_injective φ.ker.subtype_injective, h, Subgroup.card_bot]
    have h2 := P.dvd_card_of_dvd_card hdvd
    rw [h1] at h2
    exact hp'prime.one_lt.ne' (Nat.dvd_one.mp h2)
  have hnK : (Nat.card φ.ker : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K p']
    exact hNp
  have hZ := center_eq_bot_of_normal hXp hX3 hX1 (φ.normal_ker) hnK
  have hNnil := isNilpotent_ker_of_minimal hφ hmin
  have hNbot : φ.ker = ⊥ := by
    by_contra hne
    have : Nontrivial φ.ker := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsNilpotent.center_ne_bot (G := φ.ker) hZ
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hNbot
  exact false_of_suzukiModel hXp
    (suzukiModel_of_mulEquiv (MulEquiv.ofBijective φ ⟨hφinj, hφ⟩) hQ)

theorem noSzSection_glThree :
    ∀ X : Subgroup (GL (Fin 3) K), NoSzSection X := by
  classical
  intro X
  induction h : Nat.card X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
    intro Y N _ p f hSz
    by_cases hY : Y = ⊤
    ·
      subst hY
      set φ : X →* (⊤ : Subgroup X) ⧸ N :=
        (QuotientGroup.mk' N).comp (Subgroup.topEquiv.symm.toMonoidHom) with hφ
      have hφs : Function.Surjective φ :=
        (QuotientGroup.mk'_surjective N).comp Subgroup.topEquiv.symm.surjective
      refine false_of_minimal X hSz φ hφs fun H hH => ?_
      by_contra hne
      set H' := H.map X.subtype with hH'
      have hlt : Nat.card H' < n := by
        rw [← h, hH', Subgroup.card_map_of_injective X.subtype_injective]
        exact (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hne)).trans_eq Subgroup.card_top
      have hNo : NoSzSection H := noSzSection_of_injective
        (H.equivMapOfInjective X.subtype X.subtype_injective).toMonoidHom
        (H.equivMapOfInjective X.subtype X.subtype_injective).injective (ih _ hlt H' rfl)
      refine false_of_surjective hNo (φ.comp H.subtype) ?_ hSz
      intro q
      have hq : q ∈ H.map φ := by rw [hH]; exact Subgroup.mem_top q
      obtain ⟨x, hx, rfl⟩ := hq
      exact ⟨⟨x, hx⟩, rfl⟩
    ·
      set Y' := Y.map X.subtype with hY'
      have hlt : Nat.card Y' < n := by
        rw [← h, hY', Subgroup.card_map_of_injective X.subtype_injective]
        exact (Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hY)).trans_eq Subgroup.card_top
      have hNo : NoSzSection Y := noSzSection_of_injective
        (Y.equivMapOfInjective X.subtype X.subtype_injective).toMonoidHom
        (Y.equivMapOfInjective X.subtype X.subtype_injective).injective (ih _ hlt Y' rfl)
      exact false_of_surjective hNo (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hSz

end Linear

end CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProof

namespace CFSG.RankThree.PartTwo.Sec16

theorem ksGL3NoSz_holds :
    KSGL3NoSz := fun _ _ _ X N _ _ _ hSz =>
  KSL3PiNoSzProof.false_of_surjective (SuzukiSectionProof.noSzSection_glThree X)
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hSz

theorem kSL3PiNoSz_holds :
    KSL3PiNoSz :=
  kSL3PiNoSz_of ksGL3NoSz_holds

end CFSG.RankThree.PartTwo.Sec16
