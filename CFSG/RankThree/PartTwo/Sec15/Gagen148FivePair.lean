module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
public import CFSG.RankThree.PartOne.S11d.FinalLemmas
public import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
public import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
public import CFSG.RankThree.PartTwo.Sec15.Item1424StepsProofCore
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofGrow
public import CFSG.RankThree.PartTwo.Sec15.Liebeck159FieldCent
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem exists_pow_eq_one_mem_normalizer_not_mem {p : ℕ} [Fact p.Prime] {S A : Subgroup G}
    (hS : IsPGroup p S) (hAS : A ≤ S) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAp : ∀ a ∈ A, a ^ p = 1) {u v : G} (hu : u ∈ S) (hv : v ∈ S) (hup : u ^ p = 1)
    (hvp : v ^ p = 1) (huv : u * v ≠ v * u) :
    ∃ g ∈ S ⊓ Subgroup.normalizer (A : Set G), g ^ p = 1 ∧ g ∉ A := by
  by_contra hcon
  push Not at hcon
  set R : Subgroup G := S ⊓ Subgroup.normalizer (A : Set G) with hR
  have hAR : A ≤ R := le_inf hAS Subgroup.le_normalizer
  have hkey : ∀ x ∈ S, x ∈ Subgroup.normalizer (R : Set G) → x ∈ R := by
    intro x hxS hxN
    have hmap : A.map (MulAut.conj x).toMonoidHom ≤ A := by
      rintro _ ⟨a, ha, rfl⟩
      have hxa : MulAut.conj x a ∈ R := by
        rw [MulAut.conj_apply]
        exact (Subgroup.mem_normalizer_iff.mp hxN a).mp (hAR ha)
      refine hcon (MulAut.conj x a) hxa ?_
      rw [MulAut.conj_apply, conj_pow, hAp a ha, mul_one, mul_inv_cancel]
    have heq : A.map (MulAut.conj x).toMonoidHom = A :=
      Subgroup.eq_of_le_of_card_ge hmap
        (by rw [Subgroup.card_map_of_injective (MulAut.conj x).injective])
    exact ⟨hxS, Subgroup.mem_normalizer_iff_map_conj_eq.mpr (by simpa using heq)⟩
  have hSR : S = R :=
    CFSG.AGLEmbedding.eq_of_isPGroup_of_le_of_normalizer hS inf_le_left hkey
  have huA : u ∈ A := hcon u (hSR ▸ hu) hup
  have hvA : v ∈ A := hcon v (hSR ▸ hv) hvp
  exact huv (hAc u huA v hvA)

theorem exists_noncomm_of_sylow_lift {M C : Type*} [Group M] [Finite M] [Group C]
    (f : M →* C) (hker : ∀ z : M, f z = 1 → ∀ k : ℕ, z ^ 3 ^ k = 1 → z = 1) (S : Sylow 3 M)
    {Q : Subgroup C} (hQ : IsPGroup 3 Q) (hQf : Q ≤ f.range) {x y : C} (hxQ : x ∈ Q)
    (hyQ : y ∈ Q) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y ≠ y * x) :
    ∃ u ∈ (S : Subgroup M), ∃ v ∈ (S : Subgroup M), u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v ≠ v * u := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set g : M →* f.range := f.rangeRestrict with hg
  have hgs : Function.Surjective g := f.rangeRestrict_surjective
  have : Finite f.range := Finite.of_surjective g hgs
  let T₀ : Sylow 3 f.range := S.mapSurjective hgs
  have hQ' : IsPGroup 3 (Q.subgroupOf f.range) := hQ.comap_subtype
  obtain ⟨T, hQT⟩ := hQ'.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq f.range T₀ T
  have hconj : ∀ q ∈ Q.subgroupOf f.range, ∃ u ∈ (S : Subgroup M), g u = h⁻¹ * q * h := by
    intro q hq
    have hqT : q ∈ ((h • T₀ : Sylow 3 f.range) : Subgroup f.range) := hh ▸ hQT hq
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hqT
    obtain ⟨t, ht, rfl⟩ := hqT
    have ht' : t ∈ (S : Subgroup M).map g := ht
    obtain ⟨u, hu, hut⟩ := Subgroup.mem_map.mp ht'
    refine ⟨u, hu, ?_⟩
    rw [hut]
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  have hcube : ∀ z : f.range, z ^ 3 = 1 → (h⁻¹ * z * h) ^ 3 = 1 := by
    intro z hz
    rw [show h⁻¹ * z * h = h⁻¹ * z * h⁻¹⁻¹ by rw [inv_inv], conj_pow, hz, mul_one, mul_inv_cancel]
  have hlift : ∀ (z : C) (hz : z ∈ Q), z ^ 3 = 1 → ∃ u ∈ (S : Subgroup M), u ^ 3 = 1 ∧
      g u = h⁻¹ * (⟨z, hQf hz⟩ : f.range) * h := by
    intro z hz hz3
    obtain ⟨u, hu, hgu⟩ := hconj ⟨z, hQf hz⟩ hz
    refine ⟨u, hu, ?_, hgu⟩
    have hz3' : (⟨z, hQf hz⟩ : f.range) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    have h1 : f (u ^ 3) = 1 := by
      have hg3 : g (u ^ 3) = 1 := by rw [map_pow, hgu]; exact hcube _ hz3'
      exact congrArg Subtype.val hg3
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨u, hu⟩
    refine hker (u ^ 3) h1 k ?_
    rw [← pow_mul, mul_comm, pow_mul]
    have hk' : u ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [hk', one_pow]
  obtain ⟨u, hu, hu3, hgu⟩ := hlift x hxQ hx
  obtain ⟨v, hv, hv3, hgv⟩ := hlift y hyQ hy
  refine ⟨u, hu, v, hv, hu3, hv3, fun hcomm => hxy ?_⟩
  have h1 : g (u * v) = g (v * u) := by rw [hcomm]
  rw [map_mul, map_mul, hgu, hgv] at h1
  have h2 := congrArg (fun z => h * z * h⁻¹) h1
  simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at h2
  exact congrArg Subtype.val h2

theorem aschbacherSolvableCore_eq_bot_of_isoLThreePi_two {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi X 2 (3 * n)) :
    aschbacherSolvableCore 3 X = ⊥ := by
  have hs : IsSimpleGroup X := Proof1424Steps.isSimpleGroup_of_isoLThreePi_two (by omega) hX
  have h9 : 9 ∣ Nat.card X :=
    Proof155w2.nine_dvd_card_of_isLThreePi ⟨2, 3 * n, ⟨Nat.prime_two⟩, by omega, hX⟩
  rcases (aschbacherSolvableCore_normal 3 X).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have h3 := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
    rw [h, Subgroup.card_top] at h3
    exact h3 (dvd_trans (by norm_num) h9)

theorem exists_pair_inf_centralizer {X : Subgroup G}
    (hθ : aschbacherSolvableCore 3 X = ⊥) {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G))
    (h : ∃ Q : Subgroup (X ⧸ aschbacherSolvableCore 3 X),
      Q ≤ Sec8.barCentralizer (Subgroup.zpowers a) X ∧ IsPGroup 3 Q ∧
        ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x) :
    ∃ Q : Subgroup G, Q ≤ X ⊓ Subgroup.centralizer {a} ∧ IsPGroup 3 Q ∧
      ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨Q, hQle, hQ⟩ := h
  obtain ⟨Q', hQ'le, hQ'⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Liebeck159.exists_isPGroup_pair_map
    (X.subtype.comp (thetaBotEquiv hθ).toMonoidHom)
    (Subtype.val_injective.comp (thetaBotEquiv hθ).injective)
    (T := Sec8.barCentralizer (Subgroup.zpowers a) X) ⟨Q, hQle, hQ⟩
  refine ⟨Q', hQ'le.trans ?_, hQ'⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨w, rfl⟩ := (thetaBotEquiv hθ).symm.surjective y
  rw [thetaBotEquiv_symm_apply] at hy
  have hy1 := (KFacts.mem_barCentralizer_zpowers_iff ha _).mp hy
  have hy' : (compAction X ⟨a, ha⟩) w = w := by
    have := congrArg (thetaBotEquiv hθ) hy1
    rwa [thetaQuotMulAut_mk, thetaBotEquiv_mk, thetaBotEquiv_mk] at this
  have hy'' : a * (w : G) * a⁻¹ = w := congrArg Subtype.val hy'
  have hw : (X.subtype.comp (thetaBotEquiv hθ).toMonoidHom)
      ((thetaBotEquiv hθ).symm w) = (w : G) := by
    simp [MonoidHom.comp_apply]
  rw [hw]
  exact ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hy'').symm⟩

section Certs


theorem exists_noncomm_of_isSylowOf_inf_centralizer {A Y J : Subgroup G} [(ker148 A Y).Normal]
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hJ : J ≤ Y ⊔ A)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {c : G} (hcA : c ∈ A) (hc3 : c ^ 3 = 1)
    {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥(img148 A Y J) 2 (3 * n))
    (hfield : KFacts.InducesStdKind (img148 A Y J) (alpha148 A Y c hcA) .field)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 3 S (J ⊓ Subgroup.centralizer {c})) :
    ∃ u ∈ S, ∃ v ∈ S, u ^ 3 = 1 ∧ v ^ 3 = 1 ∧ u * v ≠ v * u := by
  have hθ : aschbacherSolvableCore 3 ↥(img148 A Y J) = ⊥ :=
    aschbacherSolvableCore_eq_bot_of_isoLThreePi_two hn hX
  have hX' : Sec4.IsoLThreePi
      (↥(img148 A Y J) ⧸ aschbacherSolvableCore 3 ↥(img148 A Y J)) 2 (3 * n) :=
    Sec8.Item82OneProof.isoLThreePi_of_mulEquiv (thetaBotEquiv hθ) hX
  have ha3 : alpha148 A Y c hcA ^ 3 = 1 := by
    rw [alpha148_eq_mk', ← map_pow]
    have : (⟨c, Subgroup.mem_sup_right hcA⟩ : ↥(Y ⊔ A)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  have haN := hfield.mem_normalizer
  obtain ⟨Q₁, hQ₁le, hQ₁3, x, hx, y, hy, hx3, hy3, hxy⟩ := exists_pair_inf_centralizer hθ haN
    (CFSG.RankThree.PartTwo.Sec15.Liebeck159.exists_noncomm_isPGroup_barCentralizer_of_field
      hn hX' ha3 hfield)
  have hcent : img148 A Y J ⊓ Subgroup.centralizer {alpha148 A Y c hcA} =
      img148 A Y (J ⊓ Subgroup.centralizer {c}) :=
    Main148.img148_inf_centralizer_alpha148 hAY hJ hAJ hcA hc3
  set M : Subgroup G := J ⊓ Subgroup.centralizer {c} with hM
  have hMJA : M ≤ Y ⊔ A := inf_le_left.trans hJ
  let f : ↥M →* (↥(Y ⊔ A) ⧸ ker148 A Y) :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hMJA)
  have hfrange : f.range = img148 A Y M := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : ∀ z : M, f z = 1 → ∀ k : ℕ, z ^ 3 ^ k = 1 → z = 1 := by
    intro z hz k hk
    have h1 : (z : G) ∈ pPrimeCoreOf 3 Y :=
      (mk'_ker148_eq_one_iff (A := A) (Y := Y) (g := Subgroup.inclusion hMJA z)).mp hz
    have h2 : (z : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subtype.ext (eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 Y) h1 h2)
  have hQf : Q₁ ≤ f.range := by
    rw [hfrange, ← hcent]
    exact hQ₁le
  obtain ⟨S', hS'⟩ := hS
  obtain ⟨u, hu, v, hv, hu3, hv3, huv⟩ :=
    exists_noncomm_of_sylow_lift f hker S' hQ₁3 hQf hx hy hx3 hy3 hxy
  have hmem : ∀ w ∈ (S' : Subgroup M), (w : G) ∈ S := by
    intro w hw
    have : (w : G) ∈ (S' : Subgroup M).map M.subtype := ⟨w, hw, rfl⟩
    rw [hS'] at this
    exact this
  exact ⟨(u : G), hmem u hu, (v : G), hmem v hv,
    by simpa using congrArg Subtype.val hu3,
    by simpa using congrArg Subtype.val hv3,
    fun hcomm => huv (Subtype.ext hcomm)⟩

theorem exists_isPGroup_mem_not_mem_of_field {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    [(ker148 A Y).Normal] (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA3 : ∀ a ∈ A, a ^ 3 = 1) {c : G} (hcA : c ∈ A)
    {n : ℕ} (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥(img148 A Y (deltaZero A LB Y)) 2 (3 * n))
    (hfield : KFacts.InducesStdKind (img148 A Y (deltaZero A LB Y)) (alpha148 A Y c hcA)
      .field) :
    ∃ R : Subgroup G, IsPGroup 3 R ∧ A ≤ R ∧ R ≤ Subgroup.normalizer (A : Set G) ∧
      R ≤ Subgroup.normalizer (Y : Set G) ∧ ∃ g ∈ R, g ^ 3 = 1 ∧ g ∉ A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let J : Subgroup G := deltaZero A LB Y
  let M : Subgroup G := J ⊓ Subgroup.centralizer {c}
  let E : Subgroup G := M ⊔ A
  have hJY : J ≤ Y := deltaZero_le Y
  have hJ : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have hAJ : A ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2
  have hc3 : c ^ 3 = 1 := hA3 c hcA
  have hA3' : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA3 g g.2)⟩
  obtain ⟨S, hS, hAS⟩ :=
    CFSG.RankThree.PartOne.exists_isSylowOf_ge (K := E) (Q := A) le_sup_right hA3'
  have hAcent : A ≤ Subgroup.centralizer ({c} : Set G) := by
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hAc a ha c hcA)
  have hAM : A ≤ Subgroup.normalizer (M : Set G) := by
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hAJ ha, hAcent.trans Subgroup.le_normalizer ha⟩
  have hEM : E ≤ Subgroup.normalizer (M : Set G) :=
    sup_le Subgroup.le_normalizer hAM
  have hMS : CFSG.ABGLocalTools.IsSylowOf 3 (S ⊓ M) M :=
    hS.inf_of_le_normalizer (le_sup_left : M ≤ E) hEM
  obtain ⟨u, hu, v, hv, hu3, hv3, huv⟩ :=
    exists_noncomm_of_isSylowOf_inf_centralizer hAY hJ hAJ hcA hc3 hn hX hfield hMS
  have hS3 : IsPGroup 3 S := hS.isPGroup
  obtain ⟨g, hg, hg3, hgA⟩ :=
    exists_pow_eq_one_mem_normalizer_not_mem (p := 3) hS3 hAS hAc hA3 hu.1 hv.1 hu3 hv3 huv
  refine ⟨S ⊓ Subgroup.normalizer (A : Set G), hS3.to_le inf_le_left,
    le_inf hAS Subgroup.le_normalizer, inf_le_right, ?_, g, hg, hg3, hgA⟩
  have hENY : E ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le (inf_le_left.trans (hJY.trans Subgroup.le_normalizer)) hAY
  exact inf_le_left.trans (hS.le.trans hENY)

end Certs

end CFSG.RankThree.PartTwo.Sec15.GagenL3
