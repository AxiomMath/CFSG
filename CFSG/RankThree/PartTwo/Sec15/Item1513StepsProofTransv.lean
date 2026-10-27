module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Proof
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511 CFSG.RankThree.PartTwo.Sec15.Proof1513

@[expose] def KS1513Z3PGLOrderThree : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec8.IsZ3PGLThreePi X → ¬ Group.IsSolvable X →
    ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      E ⊔ commutator X = ⊤ →
      (∃ x ∈ commutator X, (∃ v : ℕ, x ^ 3 ^ v = 1) ∧ x ∈ Subgroup.normalizer (E : Set X) ∧
        x ∉ Subgroup.centralizer (E : Set X)) →
      ∃ s ∈ commutator X, s ^ 3 = 1 ∧ s ∈ Subgroup.normalizer (E : Set X) ∧
        s ∉ Subgroup.centralizer (E : Set X)

namespace Proof1513Steps

section Lift

variable {M : Type*} [Group M] [Finite M]

theorem eq_one_of_mem_isPGroup {R N : Subgroup M} (hR : IsPGroup 3 R) (hN : ¬ 3 ∣ Nat.card N)
    {x : M} (hxR : x ∈ R) (hxN : x ∈ N) : x = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨x, hxR⟩
  exact eq_one_of_mem_of_pow_three_pow hN hxN (k := k) (by simpa using congrArg Subtype.val hk)

omit [Finite M] in
theorem isPGroup_zpowers_of_pow_three {s : M} (hs3 : s ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers s) := by
  have hord : orderOf s ∣ 3 ^ 1 := by
    rw [pow_one]
    exact orderOf_dvd_of_pow_eq_one hs3
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])

theorem exists_lift_of_quot {N : Subgroup M} [N.Normal] (hN : ¬ 3 ∣ Nat.card N)
    {A U : Subgroup M} (hAU : A ≤ U) (hA : IsPGroup 3 A) {s : M ⧸ N}
    (hsU : s ∈ U.map (QuotientGroup.mk' N)) (hs3 : s ^ 3 = 1)
    (hsA : s ∈ Subgroup.normalizer
      ((A.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N))) :
    ∃ r ∈ U, r ^ 3 = 1 ∧ QuotientGroup.mk' N r = s ∧
      r ∈ Subgroup.normalizer (A : Set M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' N with hπ
  set P₃ := Subgroup.zpowers s ⊔ A.map π with hP₃
  have hP₃3 : IsPGroup 3 P₃ := IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three hs3)
    (hA.map π) (Subgroup.zpowers_le.mpr hsA)
  have hP₃U : P₃ ≤ U.map π := sup_le (Subgroup.zpowers_le.mpr hsU) (Subgroup.map_mono hAU)
  set Q := U ⊓ P₃.comap π with hQ
  have hAQ : A ≤ Q :=
    le_inf hAU fun x hx => Subgroup.mem_sup_right (Subgroup.mem_map_of_mem π hx)
  let ψ : Q →* P₃ := (π.comp Q.subtype).codRestrict P₃ fun q => q.2.2
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    obtain ⟨u, hu, rfl⟩ := hP₃U hy
    exact ⟨⟨u, hu, hy⟩, rfl⟩
  obtain ⟨R, hAR⟩ := (hA.comap_subtype (K := Q)).exists_le_sylow
  set R' := (R : Subgroup Q).map Q.subtype with hR'
  have hR'3 : IsPGroup 3 R' := R.isPGroup'.map Q.subtype
  have hAR' : A ≤ R' := fun x hx => ⟨⟨x, hAQ hx⟩, hAR hx, rfl⟩
  have htop : (R.mapSurjective hψ : Subgroup P₃) = ⊤ :=
    ((R.mapSurjective hψ).is_maximal' (hP₃3.to_subgroup ⊤) le_top).symm
  have hsP : (⟨s, Subgroup.mem_sup_left (Subgroup.mem_zpowers s)⟩ : P₃) ∈
      (R.mapSurjective hψ : Subgroup P₃) := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [Sylow.coe_mapSurjective] at hsP
  obtain ⟨q, hqR, hqs⟩ := hsP
  have hπq : π (q : M) = s := congrArg Subtype.val hqs
  have hqR' : (q : M) ∈ R' := ⟨q, hqR, rfl⟩
  refine ⟨q, q.2.1, ?_, hπq, ?_⟩
  ·
    have hqN : (q : M) ^ 3 ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, ← hπ, hπq, hs3]
    exact eq_one_of_mem_isPGroup hR'3 hN (pow_mem hqR' 3) hqN
  ·
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hy : (q : M) * x * (q : M)⁻¹ ∈ R' :=
      mul_mem (mul_mem hqR' (hAR' hx)) (inv_mem hqR')
    have hπy : π ((q : M) * x * (q : M)⁻¹) ∈ A.map π := by
      rw [map_mul, map_mul, map_inv, hπq]
      exact (Subgroup.mem_normalizer_iff.mp hsA (π x)).mp (Subgroup.mem_map_of_mem π hx)
    obtain ⟨x', hx', hxx'⟩ := hπy
    have hd : x'⁻¹ * ((q : M) * x * (q : M)⁻¹) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ, map_mul, map_inv, hxx',
        inv_mul_cancel]
    have h1 := eq_one_of_mem_isPGroup hR'3 hN (mul_mem (inv_mem (hAR' hx')) hy) hd
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact hx'

end Lift

section Elements

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizerMonoidHom_eq_one_iff {A : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (A : Set G)) :
    A.normalizerMonoidHom ⟨k, hk⟩ = 1 ↔ k ∈ Subgroup.centralizer (A : Set G) := by
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h2 := congrArg (fun σ : MulAut A => ((σ ⟨x, hx⟩ : A) : G)) h1
    simp only [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply] at h2
    calc x * k = k * x * k⁻¹ * k := by rw [h2]
      _ = k * x := by group
  · intro hC
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [Sec4.normalizerMonoidHom_apply_coe, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp hC x x.2
    rw [← this, mul_inv_cancel_right]

theorem exists_threeElem_of_autIn {A K : Subgroup G} {σ : MulAut A} (hσ : σ ∈ Sec4.autIn K A)
    (hσ3 : orderOf σ = 3) :
    ∃ k ∈ K ⊓ Subgroup.normalizer (A : Set G), (∃ v : ℕ, k ^ 3 ^ v = 1) ∧
      k ∉ Subgroup.centralizer (A : Set G) := by
  obtain ⟨k, hkN, hkK, hkσ⟩ := Sec4.mem_autIn_iff.mp hσ
  obtain ⟨v, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos k).ne' 3 (by norm_num)
  refine ⟨k ^ m, ⟨pow_mem hkK m, pow_mem hkN m⟩, ⟨v, ?_⟩, fun hC => ?_⟩
  · rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  · have hpow : (⟨k ^ m, pow_mem hkN m⟩ : Subgroup.normalizer (A : Set G)) =
        ⟨k, hkN⟩ ^ m := Subtype.ext (by simp)
    have h1 := (normalizerMonoidHom_eq_one_iff (pow_mem hkN m)).mpr hC
    rw [hpow, map_pow, hkσ] at h1
    exact hm3 (hσ3 ▸ orderOf_dvd_of_pow_eq_one h1)

theorem pow_three_eq_one_of_m12 (h414 : Sec4.Item4_14_local) {K : Subgroup G}
    (hM : Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃* CFSG.Blueprint.NativeSporadic.M12))
    {k : G} (hkK : k ∈ K) {v : ℕ} (hk : k ^ 3 ^ v = 1) : k ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 ↥K with hθ
  set t : ↥K ⧸ θ := QuotientGroup.mk' θ ⟨k, hkK⟩ with ht
  have htv : t ^ 3 ^ v = 1 := by
    rw [ht, ← map_pow]
    have : (⟨k, hkK⟩ : ↥K) ^ 3 ^ v = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have htp : IsPGroup 3 (Subgroup.zpowers t) := by
    have hord : orderOf t ∣ 3 ^ v := orderOf_dvd_of_pow_eq_one htv
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hord
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨P, hP⟩ := htp.exists_le_sylow
  obtain ⟨⟨-, -, hexp⟩, -⟩ := h414 _ hM P
  have htP : t ∈ (P : Subgroup _) := hP (Subgroup.mem_zpowers t)
  have ht3 : t ^ 3 = 1 := by
    have h1 := Monoid.pow_exponent_eq_one (⟨t, htP⟩ : (P : Subgroup _))
    rw [hexp] at h1
    simpa using congrArg Subtype.val h1
  have hkθ : (⟨k, hkK⟩ : ↥K) ^ 3 ∈ θ := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, ← ht, ht3]
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).2.2.1
  have h1 : (⟨k, hkK⟩ : ↥K) ^ 3 = 1 := by
    refine eq_one_of_mem_of_pow_three_pow hθ3 hkθ (k := v) ?_
    rw [← pow_mul, mul_comm, pow_mul]
    have : (⟨k, hkK⟩ : ↥K) ^ 3 ^ v = 1 := Subtype.ext (by simpa using hk)
    rw [this, one_pow]
  simpa using congrArg Subtype.val h1

theorem exists_order_three_of_pgl (hKf : KS1513Z3PGLOrderThree) {A K : Subgroup G} {a : G}
    (hDa : Sec13Data G A a K) (hPGL : Sec8.IsZ3PGLThreePi (lBarA a K A)) {k : G}
    (hk : k ∈ K ⊓ Subgroup.normalizer (A : Set G)) {v : ℕ} (hkv : k ^ 3 ^ v = 1)
    (hkC : k ∉ Subgroup.centralizer (A : Set G)) :
    ∃ w ∈ K ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 ∧
      w ∉ Subgroup.centralizer (A : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.normalizer (Subgroup.zpowers a : Set G) with hH
  set θ := aschbacherSolvableCore 3 ↥H with hθ
  set π := QuotientGroup.mk' θ with hπ
  set X := lBarA a K A with hX
  set ψ := aBarHom hDa with hψ
  set E : Subgroup ↥X := ψ.range with hE
  set Λ : Subgroup ↥X := (Sec12.lBar a K).subgroupOf X with hΛ
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥H) Nat.prime_three).2.2.1
  have hcomm : commutator ↥X = Λ :=
    le_antisymm (commutator_lBarA_le hDa) (lBar_le_commutator hDa)
  have hAH : A ≤ H := hDa.A_le_normalizer_zpowers
  have hKH : K ≤ H := le_normalizer_zpowers_of_mem hDa.mem_thetaComponentsAt
  have hEab : CFSG.Assembly.IsElemAbelian 3 E := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨u, rfl⟩⟩ := x
      obtain ⟨_, ⟨v, rfl⟩⟩ := y
      apply Subtype.ext
      show ψ u * ψ v = ψ v * ψ u
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hDa.commute u.2 v.2)
    · rintro _ ⟨u, rfl⟩
      rw [← map_pow]
      have : u ^ 3 = 1 := Subtype.ext (by simpa using hDa.isElemAbelian.2 u u.2)
      rw [this, map_one]
  have hE27 : Nat.card E = 27 := by
    rw [hE, ← Nat.card_congr (MonoidHom.ofInjective (aBarHom_injective hDa)).toEquiv,
      hDa.card_eq]
  have hEtop : E ⊔ commutator ↥X = ⊤ := by
    rw [hcomm, sup_comm]
    exact lBar_sup_range_aBarHom hDa
  have hnsol : ¬ Group.IsSolvable ↥X := by
    intro hs
    have : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hDa
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot _).mpr (subgroupOf_lBar_ne_bot hDa)
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hconj : ∀ {g : G} (hgK : g ∈ K) (hgN : g ∈ Subgroup.normalizer (A : Set G)) (u : ↥A),
      (⟨π ⟨g, hKH hgK⟩, Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hgK))⟩ : ↥X) * ψ u *
        (⟨π ⟨g, hKH hgK⟩, Subgroup.mem_map_of_mem _
          (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hgK))⟩ : ↥X)⁻¹ =
        ψ ⟨g * u * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgN u).mp u.2⟩ := by
    intro g hgK hgN u
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hψ, aBarHom_apply, ← map_inv]
    rw [← map_mul, ← map_mul]
    congr 1
  set x : ↥X := ⟨π ⟨k, hKH hk.1⟩, Subgroup.mem_map_of_mem _
    (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left hk.1))⟩ with hx
  have hxcomm : x ∈ commutator ↥X := by
    rw [hcomm]
    exact Subgroup.mem_subgroupOf.mpr ⟨⟨k, hKH hk.1⟩, Subgroup.mem_subgroupOf.mpr hk.1, rfl⟩
  have hxN : x ∈ Subgroup.normalizer (E : Set ↥X) := by
    refine Subgroup.mem_normalizer_fintype fun e he => ?_
    obtain ⟨u, rfl⟩ := he
    rw [hx, hconj hk.1 hk.2 u]
    exact ⟨_, rfl⟩
  have hxC : x ∉ Subgroup.centralizer (E : Set ↥X) := by
    intro hxc
    apply hkC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := Subgroup.mem_centralizer_iff.mp hxc (ψ ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
    have h2 : x * ψ ⟨y, hy⟩ * x⁻¹ = ψ ⟨y, hy⟩ := by rw [← h1, mul_inv_cancel_right]
    rw [hx, hconj hk.1 hk.2 ⟨y, hy⟩] at h2
    have h3 := congrArg Subtype.val (aBarHom_injective hDa h2)
    simp only at h3
    calc y * k = k * y * k⁻¹ * k := by rw [h3]
      _ = k * y := by group
  have hxv : x ^ 3 ^ v = 1 := by
    apply Subtype.ext
    have h1 : (⟨k, hKH hk.1⟩ : ↥H) ^ 3 ^ v = 1 := Subtype.ext (by simpa using hkv)
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    show (π ⟨k, hKH hk.1⟩) ^ 3 ^ v = 1
    rw [← map_pow, h1, map_one]
  obtain ⟨s, hsc, hs3, hsN, hsC⟩ := hKf ↥X hPGL hnsol E hEab hE27 hEtop
    ⟨x, hxcomm, ⟨v, hxv⟩, hxN, hxC⟩
  set U := (K ⊔ A).subgroupOf H with hU
  set A' := A.subgroupOf H with hA'
  have hA'U : A' ≤ U := fun g hg =>
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hg))
  have hA'3 : IsPGroup 3 A' := fun g => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hDa.isElemAbelian.2 _ (Subgroup.mem_subgroupOf.mp g.2)))⟩
  have hsU : (s : ↥H ⧸ θ) ∈ U.map π := s.2
  have hs3' : (s : ↥H ⧸ θ) ^ 3 = 1 := by simpa using congrArg Subtype.val hs3
  have hEmap : ∀ y : ↥A, ((ψ y : ↥X) : ↥H ⧸ θ) = π ⟨(y : G), hAH y.2⟩ := fun y => rfl
  have hsA : (s : ↥H ⧸ θ) ∈ Subgroup.normalizer
      ((A'.map π : Subgroup (↥H ⧸ θ)) : Set (↥H ⧸ θ)) := by
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
    have hψy : π y = ((ψ ⟨y, hyA⟩ : ↥X) : ↥H ⧸ θ) := rfl
    have hmem := (Subgroup.mem_normalizer_iff.mp hsN (ψ ⟨y, hyA⟩)).mp ⟨⟨y, hyA⟩, rfl⟩
    obtain ⟨y', hy'⟩ := hmem
    refine ⟨⟨(y' : G), hAH y'.2⟩, Subgroup.mem_subgroupOf.mpr y'.2, ?_⟩
    rw [hψy]
    have := congrArg Subtype.val hy'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [← this, hEmap]
  obtain ⟨r, hrU, hr3, hπr, hrN⟩ := exists_lift_of_quot hθ3 hA'U hA'3 hsU hs3' hsA
  have hrKA : (r : G) ∈ K ⊔ A := Subgroup.mem_subgroupOf.mp hrU
  have hrA : (r : G) ∈ Subgroup.normalizer (A : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp hrN ⟨y, hAH hy⟩).mp
      (Subgroup.mem_subgroupOf.mpr hy)
    simpa using Subgroup.mem_subgroupOf.mp h1
  have hsΛ : (s : ↥H ⧸ θ) ∈ Sec12.lBar a K := by
    have := hcomm ▸ hsc
    exact Subgroup.mem_subgroupOf.mp this
  have hrK : (r : G) ∈ K := by
    have hset : ((K ⊔ A : Subgroup G) : Set G) = (K : Set G) * (A : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left K A hDa.le_normalizer
    have hrKA' : (r : G) ∈ ((K ⊔ A : Subgroup G) : Set G) := hrKA
    rw [hset] at hrKA'
    obtain ⟨k', hk', y, hy, hky⟩ := hrKA'
    have hr : r = ⟨k', hKH hk'⟩ * ⟨y, hAH hy⟩ := Subtype.ext hky.symm
    have hy3 : (⟨y, hAH hy⟩ : ↥H) ^ 3 ^ 1 = 1 :=
      Subtype.ext (by simpa using hDa.isElemAbelian.2 y hy)
    have hπy : QuotientGroup.mk' θ (⟨y, hAH hy⟩ : ↥H) ∈ Sec12.lBar a K := by
      have e : (⟨y, hAH hy⟩ : ↥H) = (⟨k', hKH hk'⟩ : ↥H)⁻¹ * r := by rw [hr]; group
      rw [e, map_mul, map_inv]
      refine mul_mem (inv_mem ⟨⟨k', hKH hk'⟩, Subgroup.mem_subgroupOf.mpr hk', rfl⟩) ?_
      rw [← hπ, hπr]
      exact hsΛ
    have hyK : y ∈ K := mem_of_mk_mem_lBar hDa.mem_thetaComponentsAt hy3 hπy
    rw [← hky]
    exact mul_mem hk' hyK
  refine ⟨r, ⟨hrK, hrA⟩, by simpa using congrArg Subtype.val hr3, fun hrC => hsC ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [← hπr, hEmap, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hrC (u : G) u.2)

theorem exists_central_of_normal {Q X : Subgroup G} (hQ : IsPGroup 3 Q)
    (hQX : Q ≤ Subgroup.normalizer (X : Set G)) (hne : Q ⊓ X ≠ ⊥) :
    ∃ z ∈ Q ⊓ X, z ≠ 1 ∧ ∀ q ∈ Q, q * z = z * q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hnormal : (X.subgroupOf Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQX
  have hsub : X.subgroupOf Q ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro g hg
    have : (⟨g, hg.1⟩ : ↥Q) ∈ X.subgroupOf Q := hg.2
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hsub)
  refine ⟨(z : G), ⟨z.2, hz.1⟩, fun h1 => hz1 (Subtype.ext (Subtype.ext h1)), fun q hq => ?_⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz.2 ⟨q, hq⟩)

theorem card_inf_centralizer_eq_nine {A K : Subgroup G} {a : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27) (haA : a ∈ A)
    (ha3 : orderOf a = 3) (haK : a ∉ K) (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) {w : G}
    (hw : w ∈ K ⊓ Subgroup.normalizer (A : Set G)) (hw3 : w ^ 3 = 1)
    (hwC : w ∉ Subgroup.centralizer (A : Set G)) :
    Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hxA, hxw⟩ : ∃ x ∈ A, x * w ≠ w * x := by
    by_contra hall
    push Not at hall
    exact hwC (Subgroup.mem_centralizer_iff.mpr hall)
  set f₀ := x * w * x⁻¹ * w⁻¹ with hf₀
  have hf₀K : f₀ ∈ K :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hAK hxA) w).mp hw.1) (inv_mem hw.1)
  have hf₀A : f₀ ∈ A := by
    have h1 : w * x⁻¹ * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hw.2 x⁻¹).mp (inv_mem hxA)
    have e : f₀ = x * (w * x⁻¹ * w⁻¹) := by rw [hf₀]; group
    rw [e]
    exact mul_mem hxA h1
  have hf₀1 : f₀ ≠ 1 := by
    intro h1
    apply hxw
    have h2 : x * w * x⁻¹ = w := by rw [← mul_inv_eq_one]; exact h1
    calc x * w = x * w * x⁻¹ * x := by group
      _ = w * x := by rw [h2]
  set B := A ⊓ K with hB
  have hBne : B ≠ ⊥ := by
    intro h
    apply hf₀1
    have : f₀ ∈ B := ⟨hf₀A, hf₀K⟩
    rwa [h, Subgroup.mem_bot] at this
  have hwB : w ∈ Subgroup.normalizer (B : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hw.2, Subgroup.le_normalizer hw.1⟩
  have hB3 : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hA.2 _ g.2.1)⟩
  set Q := Subgroup.zpowers w ⊔ B with hQ
  have hQ3 : IsPGroup 3 Q := IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three hw3)
    hB3 (Subgroup.zpowers_le.mpr hwB)
  have hQB : Q ≤ Subgroup.normalizer (B : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hwB) Subgroup.le_normalizer
  have hQB' : Q ⊓ B ≠ ⊥ := by rwa [inf_eq_right.mpr le_sup_right]
  obtain ⟨f, hfQB, hf1, hfc⟩ := exists_central_of_normal hQ3 hQB hQB'
  have hfB : f ∈ B := hfQB.2
  have hfw : w * f = f * w := hfc w (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  have hf3 : orderOf f = 3 := orderOf_eq_prime (hA.2 f hfB.1) hf1
  have haw : a * w = w * a := (Subgroup.mem_centralizer_singleton_iff.mp (hKa hw.1)).symm
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers f = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    by_contra hy1
    have hya : Subgroup.zpowers y = Subgroup.zpowers a := by
      have hle : Subgroup.zpowers y ≤ Subgroup.zpowers a := Subgroup.zpowers_le.mpr hy.1
      have hy3 : orderOf y = 3 := by
        have h1 : orderOf y ∣ 3 := ha3 ▸ orderOf_dvd_of_mem_zpowers hy.1
        rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) (by simpa using hy1)
        · exact h
      exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hy3,
        ha3])
    apply haK
    have hya' : a ∈ Subgroup.zpowers y := hya ▸ Subgroup.mem_zpowers a
    exact (Subgroup.zpowers_le.mpr hfB.2) ((Subgroup.zpowers_le.mpr hy.2) hya')
  have hafN : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers f : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    rw [Set.mem_singleton_iff.mp hy]
    exact (hA.1.is_comm.comm ⟨a, haA⟩ ⟨f, hfB.1⟩ |> congrArg Subtype.val).symm
  have hD9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers f : Subgroup G) = 9 := by
    have h1 := Sec6.card_sup_mul_card_inf hafN
    rw [hdisj, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, ha3, hf3] at h1
    exact h1
  have hDle : Subgroup.zpowers a ⊔ Subgroup.zpowers f ≤
      A ⊓ Subgroup.centralizer ({w} : Set G) := by
    refine sup_le (Subgroup.zpowers_le.mpr ⟨haA, ?_⟩) (Subgroup.zpowers_le.mpr ⟨hfB.1, ?_⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr haw
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hfw.symm
  have hge : 9 ≤ Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) :=
    hD9 ▸ Subgroup.card_le_of_le hDle
  have hdvd : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) ≠ 27 := by
    intro h
    apply hwC
    have hEq : A ⊓ Subgroup.centralizer ({w} : Set G) = A :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, h27])
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyC : y ∈ A ⊓ Subgroup.centralizer ({w} : Set G) := by
      rw [hEq]
      exact hy
    exact Subgroup.mem_centralizer_singleton_iff.mp hyC.2
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  interval_cases j <;> simp_all

end Elements

end Proof1513Steps

open Proof1513Steps

theorem step1513Transv_of
    (h131 : Item131) (h414 : Sec4.Item4_14_local)
    (hKf : KS1513Z3PGLOrderThree) : Step1513Transv := by
  intro G _ _ A c L a K hctx
  have h := hctx.toSec15R
  have hDa := (sec15R_point h hctx.zpowers_a_mem hctx.mem_lA_a).toSec13Data
  have haK : a ∉ K := h.hypS.2.2 a hctx.zpowers_a_mem K hctx.mem_lA_a
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  have hw : ∃ w ∈ K ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 ∧
      w ∉ Subgroup.centralizer (A : Set G) := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hDa with ⟨-, -, hprod, htyp⟩ |
        ⟨-, -, hMJ, ⟨e3⟩⟩ | ⟨-, hPGL, ⟨e3⟩, -⟩ | ⟨haK', -⟩
    ·
      exfalso
      rcases hctx.type_a with hP | ⟨⟨φ⟩⟩
      · exact Proof1514.false_of_prod_of_isZ3PGLThreePi hDa haK hprod hP
      · obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hDa hM12p hM12z φ
        rcases htyp with ⟨⟨p, e, hp, -, hL3⟩, -⟩ | ⟨⟨χ⟩, -⟩ | ⟨⟨χ⟩, -⟩
        · exact KFacts.KS14.not_isoLThreePi_M12 p e (isoLThreePi_of_mulEquiv ψ hL3)
        · exact (Proof1514.isEmpty_mulEquiv_M12_of_A7 χ).false ψ
        · exact (Proof1514.isEmpty_mulEquiv_M12_of_M22 χ).false ψ
    ·
      have hcard : Nat.card (Sec4.autIn K A) = 6 := by
        rw [Nat.card_congr e3.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        rfl
      obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := Sec4.autIn K A) 3
        (by rw [hcard]; norm_num)
      obtain ⟨k, hk, ⟨v, hkv⟩, hkC⟩ := exists_threeElem_of_autIn σ.2
        (by rw [← Subgroup.orderOf_coe] at hσ; exact hσ)
      have hM : Nonempty (↥K ⧸ aschbacherSolvableCore 3 ↥K ≃*
          CFSG.Blueprint.NativeSporadic.M12) := by
        rcases hMJ with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
        · obtain ⟨-, -, -, hψ⟩ := facts_of_prod hDa hM12p hM12z φ
          exact hψ
        · exfalso
          obtain ⟨-, -, hprod, ⟨ψ⟩⟩ := facts_of_prod hDa hJ2p hJ2z φ
          rcases hctx.type_a with hP | ⟨⟨φ'⟩⟩
          · exact Proof1514.false_of_prod_of_isZ3PGLThreePi hDa haK hprod hP
          · obtain ⟨-, -, -, ⟨ψ'⟩⟩ := facts_of_prod hDa hM12p hM12z φ'
            exact (Proof1514.isEmpty_mulEquiv_M12_of_J2 ψ).false ψ'
      exact ⟨k, hk, pow_three_eq_one_of_m12 h414 hM hk.1 hkv, hkC⟩
    ·
      obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := Sec4.autIn K A) 3
        (by rw [Nat.card_congr e3.toEquiv, Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)),
          Nat.card_zmod])
      obtain ⟨k, hk, ⟨v, hkv⟩, hkC⟩ := exists_threeElem_of_autIn σ.2
        (by rw [← Subgroup.orderOf_coe] at hσ; exact hσ)
      exact exists_order_three_of_pgl hKf hDa hPGL hk hkv hkC
    · exact (haK haK').elim
  obtain ⟨w, hwKW, hw3, hwC⟩ := hw
  exact ⟨w, hwKW, hw3, card_inf_centralizer_eq_nine hDa.isElemAbelian hDa.card_eq hDa.mem_A
    hDa.orderOf_eq haK hDa.le_centralizer hDa.le_normalizer hwKW hw3 hwC⟩

end CFSG.RankThree.PartTwo.Sec15
