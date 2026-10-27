module

public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofTransport
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofLift
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofGrow
import CFSG.RankThree.PartTwo.Sec15.Item1424StepsProofCore
import CFSG.RankThree.PartTwo.Sec15.Liebeck159FieldCent
public import CFSG.RankThree.PartTwo.Sec15.HypR
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15 CFSG.GH74.GLS

private theorem exists_noncomm_of_sylow_lift {M C : Type*} [Group M] [Finite M] [Group C]
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

private theorem aschbacherSolvableCore_eq_bot_of_isoLThreePi_two {X : Type} [Group X] [Finite X]
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

variable {G : Type} [Group G] [Finite G]

private theorem exists_pair_inf_centralizer {X : Subgroup G}
    (hθ : aschbacherSolvableCore 3 X = ⊥) {a : G} (ha : a ∈ Subgroup.normalizer (X : Set G))
    (h : ∃ Q : Subgroup (X ⧸ aschbacherSolvableCore 3 X),
      Q ≤ Sec8.barCentralizer (Subgroup.zpowers a) X ∧ IsPGroup 3 Q ∧
        ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x) :
    ∃ Q : Subgroup G, Q ≤ X ⊓ Subgroup.centralizer {a} ∧ IsPGroup 3 Q ∧
      ∃ x ∈ Q, ∃ y ∈ Q, x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨Q, hQle, hQ⟩ := h
  obtain ⟨Q', hQ'le, hQ'⟩ := exists_isPGroup_pair_map
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
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    Subgroup.coe_subtype]
  exact ⟨w.2, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hy'').symm⟩

private theorem normalizer_inf_le_normalizer_inf_centralizer (J : Subgroup G) (c : G) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (J : Set G) ≤
      Subgroup.normalizer ((J ⊓ Subgroup.centralizer {c} : Subgroup G) : Set G) := by
  set K : Subgroup G := Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
    Subgroup.normalizer (J : Set G) with hK
  have key : ∀ g ∈ K, ∀ x ∈ J ⊓ Subgroup.centralizer {c}, g * x * g⁻¹ ∈ J ⊓
      Subgroup.centralizer {c} := by
    rintro g ⟨hgc, hgJ⟩ x ⟨hxJ, hxc⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgJ x).mp hxJ, ?_⟩
    have h1 : g⁻¹ * c * g ∈ Subgroup.zpowers c := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgc) c).mp
        (Subgroup.mem_zpowers c)
      simpa using this
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hxc' : Commute x c := Subgroup.mem_centralizer_singleton_iff.mp hxc
    have hx2 : x * (g⁻¹ * c * g) = (g⁻¹ * c * g) * x := by
      rw [← hm]
      exact (hxc'.zpow_right m).eq
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc g * x * g⁻¹ * c = g * (x * (g⁻¹ * c * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * c * g) * x) * g⁻¹ := by rw [hx2]
      _ = c * (g * x * g⁻¹) := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have h := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at h

private theorem centralizer_le_normalizer_zpowers (c : G) :
    Subgroup.centralizer {c} ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
  intro x hx
  have hx' : Commute x c := Subgroup.mem_centralizer_singleton_iff.mp hx
  refine Subgroup.centralizer_le_normalizer _ ?_
  refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  exact (hx'.symm.zpow_left m).eq

section Certs


variable {A L J K P : Subgroup G} {c : G} [(ker148 A J).Normal]

theorem leaf2_omega_ne (hR : Sec15R G A c L) (hcA : c ∈ A)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) (hJΔ : J = deltaZero A (lB A) J) {n : ℕ}
    (hn : 1 ≤ n) (hX : Sec4.IsoLThreePi ↥(img148 A J (deltaZero A (lB A) J)) 2 (3 * n))
    (hsplit : img148 A J (deltaZero A (lB A) J ⊔ A) =
      img148 A J (deltaZero A (lB A) J) ⊔ Subgroup.zpowers (alpha148 A J c hcA))
    (hfield : KFacts.InducesStdKind (img148 A J (deltaZero A (lB A) J)) (alpha148 A J c hcA)
      .field)
    (hK : K ≤ L ⊓ J) (hKn : Sec4.IsoLThreePi ↥(img148 A J K) 2 n)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (J : Set G)))
    (hAP : A ≤ P) : A ≠ omegaOneThree P := by
  have h13 := hR.toSec14Std.toSec13Data
  have hc3 : c ^ 3 = 1 := by
    have := pow_orderOf_eq_one c
    rwa [h13.orderOf_eq] at this
  rw [← hJΔ] at hX hfield
  have ha3 : alpha148 A J c hcA ^ 3 = 1 := by
    rw [alpha148_eq_mk', ← map_pow]
    have : (⟨c, Subgroup.mem_sup_right hcA⟩ : ↥(J ⊔ A)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [this, map_one]
  set X : Subgroup (↥(J ⊔ A) ⧸ ker148 A J) := img148 A J J with hXdef
  have hθ : aschbacherSolvableCore 3 ↥X = ⊥ :=
    aschbacherSolvableCore_eq_bot_of_isoLThreePi_two hn hX
  have hX' : Sec4.IsoLThreePi (↥X ⧸ aschbacherSolvableCore 3 ↥X) 2 (3 * n) :=
    Sec8.Item82OneProof.isoLThreePi_of_mulEquiv (thetaBotEquiv hθ) hX
  have haN : alpha148 A J c hcA ∈ Subgroup.normalizer (X : Set (↥(J ⊔ A) ⧸ ker148 A J)) :=
    hfield.mem_normalizer
  obtain ⟨Q₁, hQ₁le, hQ₁3, x, hx, y, hy, hx3, hy3, hxy⟩ := exists_pair_inf_centralizer hθ haN
    (exists_noncomm_isPGroup_barCentralizer_of_field hn hX' ha3 hfield)
  have hcent : img148 A J J ⊓ Subgroup.centralizer {alpha148 A J c hcA} =
      img148 A J (J ⊓ Subgroup.centralizer {c}) :=
    Main148.img148_inf_centralizer_alpha148 hAJ le_sup_left hAJ hcA hc3
  set M : Subgroup G := J ⊓ Subgroup.centralizer {c} with hM
  have hMJA : M ≤ J ⊔ A := inf_le_left.trans le_sup_left
  let f : ↥M →* (↥(J ⊔ A) ⧸ ker148 A J) :=
    (QuotientGroup.mk' (ker148 A J)).comp (Subgroup.inclusion hMJA)
  have hfrange : f.range = img148 A J M := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hker : ∀ z : M, f z = 1 → ∀ k : ℕ, z ^ 3 ^ k = 1 → z = 1 := by
    intro z hz k hk
    have h1 : (z : G) ∈ pPrimeCoreOf 3 J :=
      (mk'_ker148_eq_one_iff (A := A) (Y := J) (g := Subgroup.inclusion hMJA z)).mp hz
    have h2 : (z : G) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subtype.ext (eq_one_of_pow_three_pow_eq_one148 (coprime_card_pPrimeCoreOf 3 J) h1 h2)
  have hMK : M ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (J : Set G) :=
    le_inf (inf_le_right.trans (centralizer_le_normalizer_zpowers c))
      (inf_le_left.trans Subgroup.le_normalizer)
  have hMsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ M) M :=
    hP.inf_of_le_normalizer hMK (normalizer_inf_le_normalizer_inf_centralizer J c)
  obtain ⟨S, hS⟩ := hMsyl
  have hQf : Q₁ ≤ f.range := by
    rw [hfrange, ← hcent]
    exact hQ₁le
  obtain ⟨u, hu, v, hv, hu3, hv3, huv⟩ :=
    exists_noncomm_of_sylow_lift f hker S hQ₁3 hQf hx hy hx3 hy3 hxy
  have hmem : ∀ w ∈ (S : Subgroup M), (w : G) ∈ P := by
    intro w hw
    have : (w : G) ∈ (S : Subgroup M).map M.subtype := ⟨w, hw, rfl⟩
    rw [hS] at this
    exact this.1
  intro hΩ
  have hu' : (u : G) ∈ A := by
    rw [hΩ]
    exact Subgroup.subset_closure ⟨hmem u hu, by simpa using congrArg Subtype.val hu3⟩
  have hv' : (v : G) ∈ A := by
    rw [hΩ]
    exact Subgroup.subset_closure ⟨hmem v hv, by simpa using congrArg Subtype.val hv3⟩
  exact huv (Subtype.ext (h13.commute hu' hv'))

end Certs

end CFSG.RankThree.PartTwo.Sec15.Liebeck159
