module

public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Sub
import CFSG.RankThree.PartTwo.Sec15.Item156Res4ProofON
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof155w

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_top_of_isPGroup_quotient_of_isPerfect {B : Type*} [Group B] [Finite B]
    (hB : Group.IsPerfect B) (N : Subgroup B) [N.Normal] (hN : IsPGroup 2 (B ⧸ N)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have : Nontrivial (B ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  have hperf : Group.IsPerfect (B ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have : Group.IsNilpotent (B ⧸ N) := hN.isNilpotent
  exact Group.IsPerfect.not_isSolvable (B ⧸ N) inferInstance

omit [Finite G] in
theorem open_isSubnormal_top_of_isSubnormal {H : Type*} [Group H] {K : Subgroup H}
    (hK : K.IsSubnormal) : CFSG.Open.IsSubnormal K ⊤ :=
  CFSG.Open.IsSubnormal.of_mathlib hK

theorem le_normalizer_of_mem_thetaComponentsIn_of_two {M Y Q : Subgroup G}
    (hY : Y ∈ thetaComponentsIn M) (hQM : Q ≤ M) (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQ : IsPGroup 2 Q) : Q ≤ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨hYM, hY'⟩ := mem_thetaComponentsIn_iff.mp hY
  set K := Y.subgroupOf M with hK
  set N := Q.subgroupOf M with hN
  have hKp : Group.IsPerfect ↥K := hY'.1
  have hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMQ
  have hN2 : IsPGroup 2 N := hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
  have hgen : K ≤ Subgroup.closure (QuasithinUnique.L246C127.oddPPow K) :=
    QuasithinUnique.L246C127.le_closure_oddPPow
      (fun N' _ hN' => eq_top_of_isPGroup_quotient_of_isPerfect hKp N' hN')
  have hNK : N ≤ Subgroup.normalizer (K : Set ↥M) :=
    QuasithinUnique.L246C127.le_normalizer_of_isSubnormal
      (open_isSubnormal_top_of_isSubnormal hY'.2.1) le_top
      (by
        have e : N.subgroupOf ⊤ = N.comap (⊤ : Subgroup ↥M).subtype := rfl
        rw [e]
        exact hNn.comap _) hN2 hgen
  intro q hq
  have h1 := Subgroup.le_normalizer_map M.subtype
    ⟨⟨q, hQM hq⟩, hNK (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  rwa [hK, Subgroup.map_subgroupOf_eq_of_le hYM] at h1

omit [Finite G] in
theorem inv_pow_mul_pow_mem {P : Subgroup G} {z : G} (hz : z ∈ Subgroup.normalizer (P : Set G))
    {p : G} (hp : p ∈ P) (n : ℕ) : (z ^ n)⁻¹ * (z * p) ^ n ∈ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hz' : z⁻¹ ∈ Subgroup.normalizer (P : Set G) := inv_mem hz
    have h1 : z⁻¹ * ((z ^ n)⁻¹ * (z * p) ^ n) * z⁻¹⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hz' _).mp ih
    have he : (z ^ (n + 1))⁻¹ * (z * p) ^ (n + 1) =
        (z⁻¹ * ((z ^ n)⁻¹ * (z * p) ^ n) * z⁻¹⁻¹) * p := by
      rw [pow_succ, pow_succ]
      group
    rw [he]
    exact mul_mem h1 hp

theorem oPrimeResidualOf_sup_le_sup {Z P : Subgroup G}
    (hZP : Z ≤ Subgroup.normalizer (P : Set G)) :
    oPrimeResidualOf 3 (Z ⊔ P) ≤ oPrimeResidualOf 3 Z ⊔ P := by
  refine Proof156Res4.oRes3_le_of_forall' fun y hy k hk => ?_
  have hy' : y ∈ ((Z : Set G) * (P : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right Z P hZP]
    exact hy
  obtain ⟨z, hz, p, hp, rfl⟩ := hy'
  have hzk : z ^ 3 ^ k ∈ P := by
    have h1 := inv_pow_mul_pow_mem (hZP hz) hp (3 ^ k)
    rw [hk, mul_one] at h1
    simpa using inv_mem h1
  by_cases hk0 : k = 0
  · subst hk0
    have hzP : z ∈ P := by simpa using hzk
    exact mul_mem (Subgroup.mem_sup_right hzP) (Subgroup.mem_sup_right hp)
  obtain ⟨e, r, hr3, hor⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 3 (by norm_num)
  have hzr : (z ^ r) ^ 3 ^ e = 1 := by rw [← pow_mul, mul_comm, ← hor, pow_orderOf_eq_one]
  have hzrK : z ^ r ∈ oPrimeResidualOf 3 Z := Proof156Res4.mem_oRes3_of_pow' (pow_mem hz r) hzr
  have hcop : Nat.Coprime r (3 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hr3).symm
  have hk1 : 1 < 3 ^ k := Nat.one_lt_pow hk0 (by norm_num)
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hk1
  have hrs : r * s = 3 ^ k * (r * s / 3 ^ k) + 1 := by
    have := Nat.div_add_mod (r * s) (3 ^ k)
    omega
  have hmem : (z ^ r) ^ s ∈ oPrimeResidualOf 3 Z := pow_mem hzrK s
  set m := r * s / 3 ^ k with hm
  have hrs' : r * s = 3 ^ k * m + 1 := hrs
  have hc : Commute z ((z ^ 3 ^ k) ^ m) := ((Commute.refl z).pow_right _).pow_right _
  have he : z = (z ^ r) ^ s * ((z ^ 3 ^ k) ^ m)⁻¹ := by
    rw [← pow_mul z r s, hrs', pow_succ, pow_mul, ← hc.eq, mul_inv_cancel_right]
  have hzP : ((z ^ 3 ^ k) ^ m)⁻¹ ∈ P := inv_mem (pow_mem hzk _)
  rw [he]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left hmem) (Subgroup.mem_sup_right hzP))
    (Subgroup.mem_sup_right hp)

omit [Finite G] in
theorem le_sup_theta_of_map_eq_top {X W : Subgroup G}
    (hW : (W.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) = ⊤) :
    X ≤ W ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  intro x hx
  obtain ⟨w, hw, hwx⟩ : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨x, hx⟩ ∈
      (W.subgroupOf X).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)) :=
    hW ▸ Subgroup.mem_top _
  have hθ : w⁻¹ * ⟨x, hx⟩ ∈ aschbacherSolvableCore 3 ↥X := by
    rw [← QuotientGroup.eq]
    exact hwx
  have h1 : ((w⁻¹ * ⟨x, hx⟩ : ↥X) : G) ∈ inSubgroup (aschbacherSolvableCore 3) X := ⟨_, hθ, rfl⟩
  have h2 : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
  have h3 : x = (w : G) * ((w⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [h3]
  exact mul_mem (Subgroup.mem_sup_left h2) (Subgroup.mem_sup_right h1)

theorem le_delta_of_cover_of_j2
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {Z X : Subgroup G} (hZX : Z ≤ X) (hZc : Z ≤ Subgroup.centralizer ({c} : Set G))
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hXΔ : X ≤ delta A (lB A) X) (hcov : X ≤ Z ⊔ CFSG.Open.pCoreOf 2 X) :
    Z ≤ delta A (lB A) Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.Open.pCoreOf 2 X with hOdef
  set D := delta A (lB A) Z with hDdef
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) X
  have hXO : X ≤ Subgroup.normalizer (O : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hAO : A ≤ Subgroup.normalizer (O : Set G) :=
    hAX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  have hZH : Z ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hZc.trans (centralizer_singleton_le_normalizer_zpowers c)
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hO2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hmem : ∀ R : Subgroup G, R ≤ Z → ¬ 3 ∣ Nat.card R →
      A ≤ Subgroup.normalizer (R : Set G) → R ≤ D := fun R hRZ hR3 hAR =>
    le_delta (mem_scriptQ_of_hj_point h hJ ⟨hRZ.trans hZH,
      (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩).1 hRZ
  have hDZ : D ≤ Z := delta_le Z
  have hQ : ∀ Q ∈ collectionIn (scriptQ A (lB A)) X, Q ≤ D ⊔ O := by
    rintro Q ⟨hQ, hQX⟩
    have hQO : IsPiSubgroup (piCompl 3) (Q ⊔ O) := isPiSubgroup_piCompl_sup hQ.1.2.1
      ((isPiSubgroup_piCompl_iff Nat.prime_three O).mpr hO3) (hQX.trans hXO)
    have hR : (Q ⊔ O) ⊓ Z ≤ D := hmem _ inf_le_right
      (fun h3 => (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hQO
        (h3.trans (Subgroup.card_dvd_of_le inf_le_left)))
      ((le_inf (le_normalizer_sup hQ.1.2.2 hAO) hAZ).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
    intro q hq
    have hqX : q ∈ ((Z ⊔ O : Subgroup G) : Set G) := hcov (hQX hq)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Z O (hZX.trans hXO)] at hqX
    obtain ⟨l, hl, o, ho, rfl⟩ := hqX
    have hlR : l ∈ (Q ⊔ O) ⊓ Z := by
      refine Subgroup.mem_inf.mpr ⟨?_, hl⟩
      have hlo : l = (l * o) * o⁻¹ := by group
      rw [hlo]
      exact mul_mem (Subgroup.mem_sup_left hq) (inv_mem (Subgroup.mem_sup_right ho))
    exact mul_mem (Subgroup.mem_sup_left (hR hlR)) (Subgroup.mem_sup_right ho)
  have hXle : X ≤ D ⊔ O := hXΔ.trans (show delta A (lB A) X ≤ D ⊔ O from sSup_le hQ)
  have hZO : Z ⊓ O ≤ D := hmem _ inf_le_left
    (fun h3 => hO3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right)))
    ((le_inf hAZ hAO).trans Subgroup.inf_normalizer_le_normalizer_inf)
  intro z hz
  have hz' : z ∈ ((D ⊔ O : Subgroup G) : Set G) := hXle (hZX hz)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right D O ((hDZ.trans hZX).trans hXO)] at hz'
  obtain ⟨δ, hδ, o, ho, rfl⟩ := hz'
  have hoZ : o ∈ Z := by
    have he : o = δ⁻¹ * (δ * o) := by group
    rw [he]
    exact mul_mem (inv_mem (hDZ hδ)) hz
  exact mul_mem hδ (hZO ⟨hoZ, ho⟩)

theorem commutator_le_theta_of_le_thetaQuotCentralizer {W L : Subgroup G}
    (hW : W ≤ Sec4.thetaQuotCentralizer L) :
    ⁅W, L⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [Subgroup.commutator_le]
  intro w hw l hl
  obtain ⟨-, hwl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hW hw)
  have h1 := hwl l hl
  have h2 := (Subgroup.mem_normalizer_iff.mp (Sec6.le_normalizer_theta L hl) _).mp h1
  have he : l * (l⁻¹ * (w * l * w⁻¹)) * l⁻¹ = ⁅w, l⁆ := by
    rw [commutatorElement_def]
    group
  rwa [he] at h2

omit [Finite G] in
theorem le_sup_inf_of_le {Z Z' W : Subgroup G} (hZW : Z ≤ Subgroup.normalizer (W : Set G))
    (hZZ' : Z ≤ Z') (hZ'le : Z' ≤ Z ⊔ W) : Z' ≤ Z ⊔ (Z' ⊓ W) := by
  intro x hx
  have hx' : x ∈ ((Z ⊔ W : Subgroup G) : Set G) := hZ'le hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Z W hZW] at hx'
  obtain ⟨z, hz, w, hw, rfl⟩ := hx'
  have hwZ' : w ∈ Z' := by
    have he : w = z⁻¹ * (z * w) := by group
    rw [he]
    exact mul_mem (inv_mem (hZZ' hz)) hx
  exact mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right ⟨hwZ', hw⟩)

end CFSG.RankThree.PartTwo.Sec15.Proof155w
