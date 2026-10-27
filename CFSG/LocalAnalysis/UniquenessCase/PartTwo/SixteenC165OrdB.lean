module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56NormA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56NormB
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryAutGalois

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups Matrix

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

private theorem finite_W (S : OmegaModel W) : Finite W :=
  Finite.of_injective (S.e : W → Multiplicative (OmI → S.K)) S.e.injective

private theorem finite_mulAut (S : OmegaModel W) : Finite (MulAut W) := by
  haveI := finite_W S
  exact Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective

private theorem eq_of_smul_eq_smul {a b : S.K} (h : ∀ w : W, S.smul a w = S.smul b w) :
    a = b := by
  have h1 := congrFun (congrArg S.vec (h (S.ofVec (Pi.single (Sum.inl 0) 1)))) (Sum.inl 0)
  simpa [S.vec_smul, S.vec_ofVec] using h1

private noncomputable def twistFun (g : ↥(omegaNorm S)) : S.K ≃+* S.K :=
  Classical.choose (exists_ringEquiv_of_mem_normalizer S g.2)

private theorem twistFun_spec (g : ↥(omegaNorm S)) :
    ∀ (c : S.K) (w : W), (g : MulAut W) (S.smul c w) =
      S.smul (twistFun S g c) ((g : MulAut W) w) :=
  Classical.choose_spec (exists_ringEquiv_of_mem_normalizer S g.2)

private theorem twistFun_unique {g : ↥(omegaNorm S)} {σ : S.K ≃+* S.K}
    (hσ : ∀ (c : S.K) (w : W), (g : MulAut W) (S.smul c w) =
      S.smul (σ c) ((g : MulAut W) w)) :
    σ = twistFun S g := by
  ext c
  apply eq_of_smul_eq_smul S
  intro w'
  obtain ⟨w, rfl⟩ := (g : MulAut W).surjective w'
  rw [← hσ c w, ← twistFun_spec S g c w]

private theorem twistFun_mul (g h : ↥(omegaNorm S)) :
    twistFun S (g * h) = twistFun S g * twistFun S h := by
  symm
  apply twistFun_unique S (g := g * h)
  intro c w
  change (g : MulAut W) ((h : MulAut W) (S.smul c w)) =
    S.smul ((twistFun S g * twistFun S h) c) ((g : MulAut W) ((h : MulAut W) w))
  rw [twistFun_spec S h c w, twistFun_spec S g (twistFun S h c) ((h : MulAut W) w),
    RingAut.mul_apply]

private noncomputable def twistHom : ↥(omegaNorm S) →* (S.K ≃+* S.K) :=
  MonoidHom.mk' (twistFun S) (twistFun_mul S)

private theorem twistHom_spec (g : ↥(omegaNorm S)) :
    ∀ (c : S.K) (w : W), (g : MulAut W) (S.smul c w) =
      S.smul (twistHom S g c) ((g : MulAut W) w) :=
  twistFun_spec S g

private theorem twistHom_ker (g : ↥(omegaNorm S)) :
    twistHom S g = 1 ↔ (g : MulAut W) ∈ linSub S := by
  constructor
  · intro h
    rw [mem_linSub_iff]
    intro c w
    rw [twistHom_spec S g c w, h, RingAut.one_apply]
  · intro hg
    symm
    apply twistFun_unique S (g := g)
    intro c w
    rw [RingAut.one_apply]
    exact (mem_linSub_iff S).mp hg c w

private noncomputable def omegaCodRestrict {M : Type} [Group M] (φ : M →* MulAut W)
    (hφ : φ.range ≤ omegaNorm S) : M →* ↥(omegaNorm S) :=
  φ.codRestrict (omegaNorm S) (fun m => hφ ⟨m, rfl⟩)

private theorem comap_linSub_eq_ker {M : Type} [Group M] (φ : M →* MulAut W)
    (hφ : φ.range ≤ omegaNorm S) :
    (linSub S).comap φ = ((twistHom S).comp (omegaCodRestrict S φ hφ)).ker := by
  ext m
  rw [Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact (twistHom_ker S (omegaCodRestrict S φ hφ m)).symm

theorem card_ringEquiv_eight (hK : Nat.card S.K = 8) : Nat.card (S.K ≃+* S.K) = 3 :=
  CFSG.AGLEmbedding.UnitaryModel.card_ringEquiv S.K 2 3 (by rw [hK]; norm_num)

theorem exists_twistHom :
    ∃ θ : ↥(omegaNorm S) →* (S.K ≃+* S.K),
      (∀ (g : ↥(omegaNorm S)) (c : S.K) (w : W),
        (g : MulAut W) (S.smul c w) = S.smul (θ g c) ((g : MulAut W) w)) ∧
      ∀ g : ↥(omegaNorm S), θ g = 1 ↔ (g : MulAut W) ∈ linSub S :=
  ⟨twistHom S, twistHom_spec S, twistHom_ker S⟩

theorem normal_comap_linSub {M : Type} [Group M] (φ : M →* MulAut W)
    (hφ : φ.range ≤ omegaNorm S) : ((linSub S).comap φ).Normal := by
  rw [comap_linSub_eq_ker S φ hφ]
  exact MonoidHom.normal_ker _

theorem isPGroup_quotient_comap_linSub (hK : Nat.card S.K = 8) {M : Type} [Group M]
    (φ : M →* MulAut W) (hφ : φ.range ≤ omegaNorm S) [((linSub S).comap φ).Normal] :
    IsPGroup 3 (M ⧸ (linSub S).comap φ) := by
  have hdvd : Nat.card ((twistHom S).comp (omegaCodRestrict S φ hφ)).range ∣ 3 := by
    rw [← card_ringEquiv_eight S hK]
    exact Subgroup.card_subgroup_dvd_card _
  refine IsPGroup.of_card_dvd_pow (p := 3) (n := 1) ?_
  rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
        (comap_linSub_eq_ker S φ hφ)).toEquiv,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange
        ((twistHom S).comp (omegaCodRestrict S φ hφ))).toEquiv]
  simpa using hdvd

theorem omegaNorm_inf_linSub_le_sup : omegaNorm S ⊓ linSub S ≤ scalarSub S ⊔ isoSub S := by
  intro g hg
  obtain ⟨hgN, hgL⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨c, hc0, hcQ⟩ := exists_similitude_of_linear S hgN hgL
  obtain ⟨e, he⟩ := FiniteField.isSquare_of_char_two (ringChar.eq S.K 2) c
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hc0 (by simpa using he)
  let u : S.Kˣ := Units.mk0 e he0
  let z : MulAut W := smulAutHom S u
  have hz : z ∈ scalarSub S := ⟨u, rfl⟩
  have hzlin : z ∈ linSub S := scalarSub_le_linSub S hz
  let h : MulAut W := z⁻¹ * g
  have hhlin : h ∈ linSub S := mul_mem (inv_mem hzlin) hgL
  have hz_inv : z⁻¹ = smulAut S u⁻¹ := by
    show (smulAutHom S u)⁻¹ = smulAut S u⁻¹
    exact (map_inv (smulAutHom S) u).symm
  have hcoef : ((u⁻¹ : S.Kˣ) : S.K) ^ 2 * c = 1 := by
    have hu : ((u⁻¹ : S.Kˣ) : S.K) = e⁻¹ := rfl
    rw [hu, he]
    field_simp
  have hh : h ∈ isoSub S := by
    rw [mem_isoSub_iff]
    refine ⟨hhlin, fun w => ?_⟩
    show S.Q (z⁻¹ (g w)) = S.Q w
    calc S.Q (z⁻¹ (g w)) = ((u⁻¹ : S.Kˣ) : S.K) ^ 2 * S.Q (g w) := by
          rw [hz_inv, smulAut_apply, Q_smul]
      _ = ((u⁻¹ : S.Kˣ) : S.K) ^ 2 * (c * S.Q w) := by rw [hcQ w]
      _ = (((u⁻¹ : S.Kˣ) : S.K) ^ 2 * c) * S.Q w := by ring
      _ = S.Q w := by rw [hcoef, one_mul]
  have hgh : z * h = g := by
    show z * (z⁻¹ * g) = g
    group
  rw [← hgh]
  exact Subgroup.mul_mem_sup hz hh

theorem mem_scalarSub_sup_isoSub_iff {g : MulAut W} :
    g ∈ scalarSub S ⊔ isoSub S ↔ ∃ z ∈ scalarSub S, ∃ h ∈ isoSub S, z * h = g := by
  let P : Subgroup (MulAut W) :=
    { carrier := {g | ∃ z ∈ scalarSub S, ∃ h ∈ isoSub S, z * h = g}
      one_mem' := ⟨1, (scalarSub S).one_mem, 1, (isoSub S).one_mem, by simp⟩
      mul_mem' := by
        rintro g g' ⟨z, hz, h, hh, rfl⟩ ⟨z', hz', h', hh', rfl⟩
        have hlin : h ∈ linSub S := ((mem_isoSub_iff S).mp hh).1
        refine ⟨z * z', mul_mem hz hz', h * h', mul_mem hh hh', ?_⟩
        calc z * z' * (h * h') = z * (z' * h) * h' := by group
          _ = z * (h * z') * h' := by rw [scalarSub_commute S hz' hlin]
          _ = z * h * (z' * h') := by group
      inv_mem' := by
        rintro g ⟨z, hz, h, hh, rfl⟩
        have hlin : h ∈ linSub S := ((mem_isoSub_iff S).mp hh).1
        refine ⟨z⁻¹, inv_mem hz, h⁻¹, inv_mem hh, ?_⟩
        rw [mul_inv_rev]
        exact scalarSub_commute S (inv_mem hz) (inv_mem hlin) }
  have hle : scalarSub S ⊔ isoSub S ≤ P := by
    refine sup_le ?_ ?_
    · intro z hz
      exact ⟨z, hz, 1, (isoSub S).one_mem, by simp⟩
    · intro h hh
      exact ⟨1, (scalarSub S).one_mem, h, hh, by simp⟩
  exact ⟨fun hg => hle hg, fun hg => by
    obtain ⟨z, hz, h, hh, rfl⟩ := hg
    exact Subgroup.mul_mem_sup hz hh⟩

theorem card_omegaNorm_inf_linSub_dvd (hK : Nat.card S.K = 8) :
    Nat.card ↥(omegaNorm S ⊓ linSub S) ∣ 2 ^ 7 * 3 ^ 4 * 7 ^ 3 := by
  have hdvd : Nat.card ↥(omegaNorm S ⊓ linSub S) ∣
      Nat.card ↥(scalarSub S ⊔ isoSub S) :=
    Subgroup.card_dvd_of_le (omegaNorm_inf_linSub_le_sup S)
  rw [card_scalarSub_sup_isoSub S hK] at hdvd
  simpa [show 7 * 508032 = 2 ^ 7 * 3 ^ 4 * 7 ^ 3 by norm_num] using hdvd

theorem relIndex_inf_linSub_dvd_three (hK : Nat.card S.K = 8) {X : Subgroup (MulAut W)}
    (hX : X ≤ omegaNorm S) : (X ⊓ linSub S).relIndex X ∣ 3 := by
  let θX : ↥X →* (S.K ≃+* S.K) := (twistHom S).comp (Subgroup.inclusion hX)
  have hker : θX.ker = (X ⊓ linSub S).subgroupOf X := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change twistHom S (Subgroup.inclusion hX x) = 1 ↔
      (x : MulAut W) ∈ X ∧ (x : MulAut W) ∈ linSub S
    have hx := twistHom_ker S (Subgroup.inclusion hX x)
    rw [Subgroup.coe_inclusion] at hx
    rw [hx]
    simp
  have hrange : Nat.card θX.range ∣ 3 := by
    rw [← card_ringEquiv_eight S hK]
    exact Subgroup.card_subgroup_dvd_card θX.range
  change ((X ⊓ linSub S).subgroupOf X).index ∣ 3
  rw [← hker, Subgroup.index_ker]
  exact hrange

theorem le_linSub_of_isPGroup (hK : Nat.card S.K = 8) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {P : Subgroup (MulAut W)} (hP : IsPGroup p P) (hPN : P ≤ omegaNorm S) : P ≤ linSub S := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite ↥P := by
    haveI := finite_mulAut S
    exact Finite.of_injective (Subtype.val) Subtype.coe_injective
  have hrel3 : (P ⊓ linSub S).relIndex P ∣ 3 := relIndex_inf_linSub_dvd_three S hK hPN
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hrelP : (P ⊓ linSub S).relIndex P ∣ p ^ k := by
    change ((P ⊓ linSub S).subgroupOf P).index ∣ p ^ k
    rw [← hk]
    exact Subgroup.index_dvd_card _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hrelP
  have hcop : Nat.Coprime (p ^ j) 3 :=
    ((Nat.coprime_primes hp Nat.prime_three).mpr hp3).pow_left j
  have hpj1 : p ^ j = 1 := by
    rw [hj] at hrel3
    exact Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hrel3
  have hrel1 : (P ⊓ linSub S).relIndex P = 1 := by rw [hj, hpj1]
  have hle : P ≤ P ⊓ linSub S := Subgroup.relIndex_eq_one.mp hrel1
  exact (le_inf_iff.mp hle).2

theorem le_isoSub_of_isPGroup_of_le_linSub (hK : Nat.card S.K = 8) {p : ℕ} (hp : p.Prime)
    (hp7 : p ≠ 7) {P : Subgroup (MulAut W)} (hP : IsPGroup p P)
    (hPN : P ≤ omegaNorm S ⊓ linSub S) : P ≤ isoSub S := by
  intro x hx
  have hx5 : x ∈ scalarSub S ⊔ isoSub S :=
    omegaNorm_inf_linSub_le_sup S (hPN hx)
  obtain ⟨z, hz, h, hh, hzh⟩ := (mem_scalarSub_sup_isoSub_iff S).mp hx5
  have hlin : h ∈ linSub S := ((mem_isoSub_iff S).mp hh).1
  have hcomm : Commute z h := scalarSub_commute S hz hlin
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hxpow : x ^ p ^ k = 1 := by
    have := congrArg (Subtype.val) hk
    simpa using this
  have h1 : z ^ p ^ k * h ^ p ^ k = 1 := by
    rw [← Commute.mul_pow hcomm (p ^ k), hzh, hxpow]
  have h2 : z ^ p ^ k = (h ^ p ^ k)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have hzpow_sc : z ^ p ^ k ∈ scalarSub S := Subgroup.pow_mem _ hz _
  have hzpow_iso : z ^ p ^ k ∈ isoSub S := by
    rw [h2]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hh _)
  have hzpow1 : z ^ p ^ k = 1 := by
    have hbot : z ^ p ^ k ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← scalarSub_inf_isoSub S]
      exact ⟨hzpow_sc, hzpow_iso⟩
    exact Subgroup.mem_bot.mp hbot
  have hz7 : orderOf z ∣ 7 := by
    rw [← card_scalarSub S hK]
    exact Subgroup.orderOf_dvd_natCard (scalarSub S) hz
  have hzpk_dvd : orderOf z ∣ p ^ k := orderOf_dvd_of_pow_eq_one hzpow1
  have hcop : Nat.Coprime 7 (p ^ k) :=
    ((Nat.coprime_primes Nat.prime_seven hp).mpr (Ne.symm hp7)).pow_right k
  have hord1 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop hz7 hzpk_dvd
  have hz1 : z = 1 := orderOf_eq_one_iff.mp hord1
  rw [← hzh, hz1, one_mul]
  exact hh

theorem le_isoSub_of_isPGroup (hK : Nat.card S.K = 8) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hp7 : p ≠ 7) {P : Subgroup (MulAut W)} (hP : IsPGroup p P) (hPN : P ≤ omegaNorm S) :
    P ≤ isoSub S :=
  le_isoSub_of_isPGroup_of_le_linSub S hK hp hp7 hP
    (le_inf hPN (le_linSub_of_isPGroup S hK hp hp3 hP hPN))

theorem card_omegaNorm_dvd (hK : Nat.card S.K = 8) :
    Nat.card ↥(omegaNorm S) ∣ 2 ^ 7 * 3 ^ 5 * 7 ^ 3 := by
  have hrel : (omegaNorm S ⊓ linSub S).relIndex (omegaNorm S) ∣ 3 :=
    relIndex_inf_linSub_dvd_three S hK (X := omegaNorm S) le_rfl
  have hinfl : Nat.card ↥(omegaNorm S ⊓ linSub S) ∣ 2 ^ 7 * 3 ^ 4 * 7 ^ 3 :=
    card_omegaNorm_inf_linSub_dvd S hK
  have hmul := Subgroup.relIndex_mul_card (H := omegaNorm S ⊓ linSub S) (K := omegaNorm S)
  rw [inf_of_le_left inf_le_left] at hmul
  rw [← hmul]
  rw [← show 3 * (2 ^ 7 * 3 ^ 4 * 7 ^ 3) = 2 ^ 7 * 3 ^ 5 * 7 ^ 3 by norm_num]
  exact Nat.mul_dvd_mul hrel hinfl

theorem scalarSub_le_omegaNorm : scalarSub S ≤ omegaNorm S := by
  intro z hz
  refine Subgroup.centralizer_le_normalizer (S.omega : Set (MulAut W)) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (scalarSub_commute S hz (fun c w => omega_smul S hh c w)).symm

theorem normal_scalarSub_subgroupOf : ((scalarSub S).subgroupOf (omegaNorm S)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (scalarSub_le_omegaNorm S)]
  intro h k hh hk
  obtain ⟨u, rfl⟩ := hh
  refine ⟨Units.mk0 ((twistHom S ⟨k, hk⟩) (u : S.K)) ?_, ?_⟩
  · intro hzero
    exact u.ne_zero ((twistHom S ⟨k, hk⟩).injective (by simpa using hzero))
  · ext w
    show S.smul ((twistHom S ⟨k, hk⟩) (u : S.K)) w = (k * smulAutHom S u * k⁻¹) w
    rw [MulAut.mul_apply, MulAut.mul_apply]
    rw [show smulAutHom S u (k⁻¹ w) = S.smul (u : S.K) (k⁻¹ w) from rfl]
    rw [twistHom_spec S ⟨k, hk⟩ (u : S.K) (k⁻¹ w), MulAut.apply_inv_self]

theorem scalarSub_le_of_isPGroup_seven (hK : Nat.card S.K = 8) {X : Subgroup (MulAut W)}
    (hX : IsPGroup 7 X) (hXN : X ≤ omegaNorm S) (hcard : 7 ^ 3 ≤ Nat.card X) :
    scalarSub S ≤ X := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let N : Subgroup (MulAut W) := omegaNorm S
  have hXN' : X ≤ N := hXN
  haveI : Finite ↥X := by
    haveI := finite_mulAut S
    exact Finite.of_injective (Subtype.val) Subtype.coe_injective
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hk3 : 3 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).mp hcard
  have hNdvd : Nat.card ↥N ∣ 2 ^ 7 * 3 ^ 5 * 7 ^ 3 := card_omegaNorm_dvd S hK
  have hcop0 : Nat.Coprime 7 (2 ^ 7 * 3 ^ 5) := by
    have h72 : Nat.Coprime 7 2 :=
      (Nat.coprime_primes Nat.prime_seven Nat.prime_two).mpr (by norm_num)
    have h73 : Nat.Coprime 7 3 :=
      (Nat.coprime_primes Nat.prime_seven Nat.prime_three).mpr (by norm_num)
    exact (h72.pow_right 7).mul_right (h73.pow_right 5)
  have hk3' : k ≤ 3 := by
    have hXdiv : 7 ^ k ∣ 2 ^ 7 * 3 ^ 5 * 7 ^ 3 := by
      rw [← hk]
      exact (Subgroup.card_dvd_of_le hXN').trans hNdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 7)).mp
      ((hcop0.pow_left k).dvd_of_dvd_mul_left hXdiv)
  have hXcard : Nat.card ↥X = 7 ^ 3 := by rw [hk, le_antisymm hk3' hk3]
  let X' : Subgroup ↥N := X.subgroupOf N
  have hX'card : Nat.card ↥X' = 7 ^ 3 := by
    rw [show Nat.card ↥X' = Nat.card ↥X from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXN').toEquiv]
    exact hXcard
  have hX'P : IsPGroup 7 X' :=
    hX.of_injective (Subgroup.subgroupOfEquivOfLe hXN').toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXN').injective
  haveI : Finite ↥N := by
    haveI := finite_mulAut S
    exact Finite.of_injective (Subtype.val) Subtype.coe_injective
  obtain ⟨Q, hX'Q⟩ := hX'P.exists_le_sylow
  haveI : Finite ↥Q := Finite.of_injective (Subtype.val) Subtype.coe_injective
  obtain ⟨j, hj⟩ := Q.isPGroup'.exists_card_eq
  have hjle3 : j ≤ 3 := by
    have hQdiv : 7 ^ j ∣ 2 ^ 7 * 3 ^ 5 * 7 ^ 3 := by
      rw [← hj]
      exact (Subgroup.card_subgroup_dvd_card (Q : Subgroup ↥N)).trans hNdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 7)).mp
      ((hcop0.pow_left j).dvd_of_dvd_mul_left hQdiv)
  have hQle : Nat.card ↥Q ≤ 7 ^ 3 := by
    rw [show Nat.card ↥Q = 7 ^ j from hj]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).mpr hjle3
  have hX'Qeq : X' = Q := by
    refine Subgroup.eq_of_le_of_card_ge hX'Q ?_
    rw [hX'card]
    exact hQle
  let Z' : Subgroup ↥N := (scalarSub S).subgroupOf N
  have hZ'normal : Z'.Normal := normal_scalarSub_subgroupOf S
  have hZ'card : Nat.card ↥Z' = 7 := by
    rw [show Nat.card ↥Z' = Nat.card ↥(scalarSub S) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show scalarSub S ≤ N from
        scalarSub_le_omegaNorm S)).toEquiv]
    exact card_scalarSub S hK
  have hZ'pg : IsPGroup 7 Z' :=
    IsPGroup.of_card (p := 7) (n := 1) (by rw [hZ'card]; norm_num)
  have hZ'Q : Z' ≤ Q := by
    haveI := hZ'normal
    exact IsPGroup.le_sylow_of_normal hZ'pg Q
  have hZ'X' : Z' ≤ X' := by
    rw [hX'Qeq]
    exact hZ'Q
  intro z hz
  have hzN : z ∈ omegaNorm S := scalarSub_le_omegaNorm S hz
  have hzZ' : (⟨z, hzN⟩ : ↥N) ∈ Z' := by
    rw [Subgroup.mem_subgroupOf]
    exact hz
  have hzX' : (⟨z, hzN⟩ : ↥N) ∈ X' := hZ'X' hzZ'
  exact Subgroup.mem_subgroupOf.mp hzX'

theorem scalarSub_le_of_seven_pow_three_dvd (hK : Nat.card S.K = 8) {B : Subgroup (MulAut W)}
    (hBN : B ≤ omegaNorm S) (hB : 7 ^ 3 ∣ Nat.card B) : scalarSub S ≤ B := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Finite ↥B := by
    haveI := finite_mulAut S
    exact Finite.of_injective (Subtype.val) Subtype.coe_injective
  let P : Sylow 7 ↥B := default
  have hB0 : Nat.card B ≠ 0 := Nat.card_pos.ne'
  have hle : 3 ≤ Nat.factorization (Nat.card B) 7 :=
    (Nat.prime_seven.pow_dvd_iff_le_factorization hB0).mp hB
  have hPge : 7 ^ 3 ≤ Nat.card ↥P := by
    rw [show Nat.card ↥P = 7 ^ Nat.factorization (Nat.card ↥B) 7 from
      Sylow.card_eq_multiplicity P]
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 7)).mpr hle
  let X : Subgroup (MulAut W) := (P : Subgroup ↥B).map B.subtype
  have hXcard : Nat.card X = Nat.card ↥P := Subgroup.card_map_of_injective B.subtype_injective
  have hXge : 7 ^ 3 ≤ Nat.card X := by rw [hXcard]; exact hPge
  have hXpg : IsPGroup 7 X := P.isPGroup'.map B.subtype
  have hXN : X ≤ omegaNorm S := (Subgroup.map_subtype_le (P : Subgroup ↥B)).trans hBN
  have hleX : scalarSub S ≤ X := scalarSub_le_of_isPGroup_seven S hK hXpg hXN hXge
  exact hleX.trans (Subgroup.map_subtype_le (P : Subgroup ↥B))

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
