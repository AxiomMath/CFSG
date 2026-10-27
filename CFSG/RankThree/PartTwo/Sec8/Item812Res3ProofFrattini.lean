module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofYNormal
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.KFacts.K72SLPiAut
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofCenter

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (localRank projSp)

namespace Item812Res3

theorem exists_mem_conj_eq_of_inv_mul_mem {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {x y : G} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : x⁻¹ * y ∈ N) : ∃ t ∈ N, t * y * t⁻¹ = x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := N ⊔ Subgroup.zpowers y with hP
  have hyP : y ∈ P := Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hxP : x ∈ P := by
    have : x = y * (x⁻¹ * y)⁻¹ := by group
    rw [this]
    exact P.mul_mem hyP (P.inv_mem (Subgroup.mem_sup_left hxy))
  set X' := (Subgroup.zpowers x).subgroupOf P with hX'
  set Y' := (Subgroup.zpowers y).subgroupOf P with hY'
  have hpow : ∀ {u : G}, u ^ 3 = 1 → ∀ v ∈ Subgroup.zpowers u, v ^ 3 = 1 := by
    intro u hu v hv
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    rw [← zpow_natCast (u ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  have hX'p : IsPGroup 3 X' := fun v => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hpow hx _ (Subgroup.mem_subgroupOf.mp v.2)))⟩
  have hY'p : IsPGroup 3 Y' := fun v => ⟨1, Subtype.ext (Subtype.ext (by
    simpa using hpow hy _ (Subgroup.mem_subgroupOf.mp v.2)))⟩
  obtain ⟨T, hXT⟩ := hX'p.exists_le_sylow
  obtain ⟨p, hp⟩ := KFacts.exists_conj_mem_sylow T hY'p
  have hyT : p * ⟨y, hyP⟩ * p⁻¹ ∈ (T : Subgroup P) :=
    hp _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers y))
  have hxT : (⟨x, hxP⟩ : P) ∈ (T : Subgroup P) :=
    hXT (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
  obtain ⟨n, hn, v, hv, hnv⟩ := Subgroup.mem_sup_of_normal_left.mp p.2
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hconj : ((p * ⟨y, hyP⟩ * p⁻¹ : P) : G) = n * y * n⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hnv]
    have hc : y ^ j * y = y * y ^ j := (Commute.zpow_left (Commute.refl y) j).eq
    calc n * y ^ j * y * (n * y ^ j)⁻¹ = n * (y ^ j * y) * (y ^ j)⁻¹ * n⁻¹ := by group
      _ = n * (y * y ^ j) * (y ^ j)⁻¹ * n⁻¹ := by rw [hc]
      _ = n * y * n⁻¹ := by group
  have hmemN : x⁻¹ * (n * y * n⁻¹) ∈ N := by
    have e : x⁻¹ * (n * y * n⁻¹) = (x⁻¹ * y) * (y⁻¹ * n * y * n⁻¹) := by group
    rw [e]
    refine N.mul_mem hxy (N.mul_mem ?_ (N.inv_mem hn))
    have := (inferInstance : N.Normal).conj_mem n hn y⁻¹
    simpa [mul_assoc] using this
  have hmemT : (⟨x, hxP⟩ : P)⁻¹ * (p * ⟨y, hyP⟩ * p⁻¹) ∈ (T : Subgroup P) :=
    (T : Subgroup P).mul_mem ((T : Subgroup P).inv_mem hxT) hyT
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨_, hmemT⟩
  have hk' : (x⁻¹ * (n * y * n⁻¹)) ^ 3 ^ k = 1 := by
    have h1 := congrArg (fun w : (T : Subgroup P) => ((w : P) : G)) hk
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv,
      OneMemClass.coe_one] at h1
    rw [← hconj]
    simpa using h1
  have h1 := KFacts.eq_one_of_pow_three_pow_eq_one hN hmemN hk'
  refine ⟨n, hn, ?_⟩
  have : n * y * n⁻¹ = x := by
    have := congrArg (fun w => x * w) h1
    simpa using this
  exact this

variable {G : Type} [Group G] [Finite G]

theorem mem_zpowers_of_thetaQuotMulAut_eq_one (h3 : localRank 3 G ≤ 3) {a : G}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a)
    {M : Type} [Group M] (hM : IsYModel M) (e : Y ⧸ aschbacherSolvableCore 3 Y ≃* M)
    {w : G} (hwa : w * a = a * w) (hw3 : w ^ 3 = 1)
    (hwN : w ∈ Subgroup.normalizer (Y : Set G))
    (hwtriv : thetaQuotMulAut Y (compAction Y ⟨w, hwN⟩) = 1) : w ∈ Subgroup.zpowers a := by
  classical
  by_contra hwz
  obtain ⟨hZ, s₁, s₂, V, hs₁, hs₁', hs₂, hs₂', hs, hV3, hV2, hV₁, hV₂⟩ := hM
  have hp : Nat.Prime 3 := Nat.prime_three
  set H := Subgroup.centralizer ({a} : Set G) with hH
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  set N := aschbacherSolvableCore 3 H with hN
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨η, hη⟩ := exists_thetaQuotient_mulEquiv_map hp hY₀.2.1
  set ι := Y₀.equivMapOfInjective H.subtype H.subtype_injective with hι
  set Θ := Item812Res2.thetaQuotEquiv ι with hΘ
  set ψ : M ≃* Y₀.map π := e.symm.trans (Θ.symm.trans η) with hψ
  have haH : a ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hwH : w ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hwa
  set z := π ⟨a, haH⟩ with hz
  set w' := π ⟨w, hwH⟩ with hw'
  have hzc : ∀ y, z * y = y * z := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [hz, hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
  have ha3' : (⟨a, haH⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hw3' : (⟨w, hwH⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hw3)
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, ha3', map_one]
  have hww3 : w' ^ 3 = 1 := by rw [hw', ← map_pow, hw3', map_one]
  have hz1 : z ≠ 1 := by
    intro h1
    have hmem : (⟨a, haH⟩ : H) ∈ N := by
      rwa [hz, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have h31 : (⟨a, haH⟩ : H) ^ 3 ^ 1 = 1 := by rw [pow_one]; exact ha3'
    have h2 := KFacts.eq_one_of_pow_three_pow_eq_one hN3 hmem h31
    exact ha1 (by simpa using congrArg Subtype.val h2)
  have hwz' : w' ∉ Subgroup.zpowers z := by
    rintro ⟨k, hk⟩
    apply hwz
    have hmem : (⟨w, hwH⟩ : H) * (⟨a, haH⟩ : H) ^ (-k) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_zpow, ← hz,
        ← hw', ← hk, zpow_neg, mul_inv_cancel]
    have hcomm : Commute (⟨w, hwH⟩ : H) (⟨a, haH⟩ : H) := Subtype.ext hwa
    have hpow3 : ((⟨w, hwH⟩ : H) * (⟨a, haH⟩ : H) ^ (-k)) ^ 3 ^ 1 = 1 := by
      rw [pow_one, (hcomm.zpow_right (-k)).mul_pow, hw3', one_mul, ← zpow_natCast,
        ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3', one_zpow]
    have h1 := KFacts.eq_one_of_pow_three_pow_eq_one hN3 hmem hpow3
    refine ⟨k, ?_⟩
    have h2 : (⟨w, hwH⟩ : H) = (⟨a, haH⟩ : H) ^ k := by
      rw [← mul_inv_eq_one, ← zpow_neg]
      exact h1
    simpa using (congrArg Subtype.val h2).symm
  have hzw : z * w' = w' * z := hzc w'
  have hF9 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers w' : Subgroup (H ⧸ N)) = 9 := by
    rw [card_sup_zpowers_eq_sq Nat.prime_three hz3 hz1 hww3 hwz' hzw]
    norm_num
  have hFab := isElemAbelian_sup_zpowers hz3 hww3 hzw
  have hwK : ∀ k ∈ Y₀.map π, w' * k = k * w' := by
    rintro _ ⟨y₀, hy₀, rfl⟩
    have hy₁mem : (⟨w, hwH⟩ : H) * y₀ * (⟨w, hwH⟩ : H)⁻¹ ∈ Y₀ := by
      have h1 : w * (y₀ : G) * w⁻¹ ∈ Y₀.map H.subtype :=
        (Subgroup.mem_normalizer_iff.mp hwN _).mp ⟨y₀, hy₀, rfl⟩
      obtain ⟨y₁, hy₁, hy₁e⟩ := h1
      have : y₁ = (⟨w, hwH⟩ : H) * y₀ * (⟨w, hwH⟩ : H)⁻¹ := Subtype.ext hy₁e
      rwa [← this]
    set y₁ : Y₀ := ⟨_, hy₁mem⟩ with hy₁
    have hcls : ((y₁ : Y₀) : Y₀ ⧸ aschbacherSolvableCore 3 Y₀) =
        ((⟨y₀, hy₀⟩ : Y₀) : Y₀ ⧸ aschbacherSolvableCore 3 Y₀) := by
      apply Θ.injective
      have h1 : Θ ((⟨y₀, hy₀⟩ : Y₀) : Y₀ ⧸ aschbacherSolvableCore 3 Y₀) =
          ((ι ⟨y₀, hy₀⟩ : Y₀.map H.subtype) :
            Y₀.map H.subtype ⧸ aschbacherSolvableCore 3 (Y₀.map H.subtype)) := rfl
      have h2 : Θ ((y₁ : Y₀) : Y₀ ⧸ aschbacherSolvableCore 3 Y₀) =
          ((ι y₁ : Y₀.map H.subtype) :
            Y₀.map H.subtype ⧸ aschbacherSolvableCore 3 (Y₀.map H.subtype)) := rfl
      have h3 : ι y₁ = compAction (Y₀.map H.subtype) ⟨w, hwN⟩ (ι ⟨y₀, hy₀⟩) := by
        apply Subtype.ext
        have h4 := normalizerMonoidHom_apply_coe hwN (ι ⟨y₀, hy₀⟩)
        refine Eq.trans ?_ h4.symm
        rfl
      rw [h1, h2, h3, ← thetaQuotMulAut_mk, hwtriv, MulAut.one_apply]
    have hπ1 : π (y₁ : H) = π y₀ := by
      have h1 := congrArg (fun q => (η q : H ⧸ N)) hcls
      simp only [hη] at h1
      exact h1
    change π ⟨w, hwH⟩ * π y₀ = π y₀ * π ⟨w, hwH⟩
    calc π ⟨w, hwH⟩ * π y₀ = π ⟨w, hwH⟩ * π y₀ * (π ⟨w, hwH⟩)⁻¹ * π ⟨w, hwH⟩ := by group
      _ = π (y₁ : H) * π ⟨w, hwH⟩ := by rw [hy₁]; simp only [map_mul, map_inv]
      _ = π y₀ * π ⟨w, hwH⟩ := by rw [hπ1]
  have hFK : ∀ f ∈ (Subgroup.zpowers z ⊔ Subgroup.zpowers w' : Subgroup (H ⧸ N)),
      ∀ k ∈ Y₀.map π, f * k = k * f := by
    have hle : (Subgroup.zpowers z ⊔ Subgroup.zpowers w' : Subgroup (H ⧸ N)) ≤
        Subgroup.centralizer (Y₀.map π : Set (H ⧸ N)) := by
      refine sup_le ((Subgroup.zpowers_le).mpr ?_) ((Subgroup.zpowers_le).mpr ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro k _
        exact (hzc k).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (hwK k hk).symm
    intro f hf k hk
    exact (Subgroup.mem_centralizer_iff.mp (hle hf) k hk).symm
  have h4 := four_le_localRank_of_centralizes hZ ψ hs₁ hs₁' hs₂ hs₂' hs hV3 hV2 hV₁ hV₂ hFab hF9
    hFK
  have h5 := CFSG.RankThree.Classical2.localRank_quotient_le hp (by norm_num) N hN3
  have h6 := CFSG.RankThree.PartOne.PlaneAux.localRank_le_of_injective hp H.subtype
    H.subtype_injective
  omega

theorem exists_mul_eq_of_mem (h3 : localRank 3 G ≤ 3) {A : Subgroup G} (hAF : A ∈ partTwoF G)
    (hA81 : Nat.card A = 81) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {Y : Subgroup G}
    (hY : Y ∈ thetaComponentsAt 3 a) {M : Type} [Group M] (hM : IsYModel M)
    (e : Y ⧸ aschbacherSolvableCore 3 Y ≃* M)
    (hinn : ∀ β : MulAut M, β ^ 3 = 1 → KFacts.IsInnerAut β)
    (hAN : A ≤ Subgroup.normalizer (Y : Set G)) {x : G} (hxA : x ∈ A) :
    ∃ (i : ℤ) (s : G), s ∈ Y ∧ s ^ 3 = 1 ∧ x = a ^ i * s := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAab, hAmax, -⟩ := hAF
  have hAc : ∀ y ∈ A, ∀ y' ∈ A, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  have hAc' : ∀ y y' : A, y * y' = y' * y := fun y y' => hAab.1.is_comm.comm y y'
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ :=
    (IsYModel.of_mulEquiv e.symm hM).1
  have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt_three hY
  set ρ : A →* MulAut (Y ⧸ aschbacherSolvableCore 3 Y) :=
    (thetaQuotMulAut Y).comp ((compAction Y).comp (Subgroup.inclusion hAN)) with hρ
  have hρapply : ∀ y : A, ρ y = thetaQuotMulAut Y (compAction Y ⟨y, hAN y.2⟩) := fun y => rfl
  have haker : ρ ⟨a, haA⟩ = 1 := by
    rw [hρapply]
    have h1 : compAction Y ⟨a, hAN haA⟩ = 1 := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      change a * (l : G) * a⁻¹ = (l : G)
      have hla : (l : G) * a = a * l := Subgroup.mem_centralizer_singleton_iff.mp (hYa l.2)
      rw [← hla, mul_inv_cancel_right]
    rw [h1, map_one]
  have hao : orderOf (⟨a, haA⟩ : A) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using ha3))
      (fun h1 => ha1 (by simpa using congrArg Subtype.val h1))
  have hkerEq : ρ.ker = Subgroup.zpowers (⟨a, haA⟩ : A) := by
    refine le_antisymm (fun y hy => ?_) ((Subgroup.zpowers_le).mpr haker)
    have hy' : (y : G) ∈ Subgroup.zpowers a :=
      mem_zpowers_of_thetaQuotMulAut_eq_one h3 ha3 ha1 hY hM e (hAc y y.2 a haA)
        (hAab.2 y y.2) (hAN y.2) hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy'
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hkercard : Nat.card ρ.ker = 3 := by rw [hkerEq, Nat.card_zpowers, hao]
  have hrangecard : Nat.card ρ.range = 27 := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker, hA81, hkercard] at h1
    omega
  have hrinn : ∀ β ∈ ρ.range, KFacts.IsInnerAut β := by
    rintro _ ⟨y, rfl⟩
    have hy3 : y ^ 3 = 1 := Subtype.ext (by simpa using hAab.2 y y.2)
    have hβ3 : ρ y ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
    have h1 := hinn (MulAut.congr e (ρ y)) (by rw [← map_pow, hβ3, map_one])
    exact (KFacts.isInnerAut_congr e _).mp h1
  set Y0 := ρ.range.comap (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →*
    MulAut (Y ⧸ aschbacherSolvableCore 3 Y)) with hY0
  have hconjinj := Item812Res2.mulAutConj_injective hZ
  have hY0map : Y0.map (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →*
      MulAut (Y ⧸ aschbacherSolvableCore 3 Y)) = ρ.range := by
    rw [hY0, Subgroup.map_comap_eq]
    exact inf_eq_right.mpr fun β hβ => hrinn β hβ
  have hY0card : Nat.card Y0 = 27 := by
    rw [← hrangecard, ← hY0map, Subgroup.card_map_of_injective hconjinj]
  have hY0fix : ∀ (a' : G) (ha' : a' ∈ A), ∀ y ∈ Y0,
      thetaQuotMulAut Y (compAction Y ⟨a', hAN ha'⟩) y = y := by
    intro a' ha' y hy
    obtain ⟨d, hd⟩ := hy
    have hcomm : ρ ⟨a', ha'⟩ * ρ d = ρ d * ρ ⟨a', ha'⟩ := by
      rw [← map_mul, ← map_mul, hAc' ⟨a', ha'⟩ d]
    have h1 : ρ ⟨a', ha'⟩ * MulAut.conj y * (ρ ⟨a', ha'⟩)⁻¹ = MulAut.conj y := by
      rw [← hd, hcomm]
      group
    rw [KFacts.mul_mulAutConj_mul_inv] at h1
    exact hconjinj h1
  have hY0ab : CFSG.Assembly.IsElemAbelian 3 Y0 := by
    refine ⟨⟨⟨fun y y' => Subtype.ext (hconjinj ?_)⟩⟩, fun y hy => hconjinj ?_⟩
    · obtain ⟨d, hd⟩ := y.2
      obtain ⟨d', hd'⟩ := y'.2
      simp only [Subgroup.coe_mul, map_mul]
      rw [← hd, ← hd', ← map_mul, ← map_mul, hAc' d d']
    · obtain ⟨d, hd⟩ := hy
      rw [map_pow, ← hd, ← map_pow,
        show d ^ 3 = 1 from Subtype.ext (by simpa using hAab.2 d d.2), map_one, map_one]
  obtain ⟨S₀, hS₀A, hS₀Y, hdisj⟩ := Item812Res2.exists_le_of_fixed hAab hAmax hAN hY0ab hY0fix
  have hqinj : ∀ s ∈ S₀, ∀ t ∈ S₀, QuotientGroup.mk' (aschbacherSolvableCore 3 Y) s =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) t → s = t := by
    intro s hs t ht hst
    have h1 : t⁻¹ * s ∈ aschbacherSolvableCore 3 Y := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hst
      have := (aschbacherSolvableCore 3 Y).inv_mem hst
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : t⁻¹ * s ∈ S₀ ⊓ aschbacherSolvableCore 3 Y :=
      ⟨S₀.mul_mem (S₀.inv_mem ht) hs, h1⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  have hS₀card : Nat.card S₀ = 27 := by
    rw [← hY0card, ← hS₀Y]
    refine le_antisymm ?_ ?_
    · refine Nat.card_le_card_of_injective
        (fun s : S₀ => (⟨QuotientGroup.mk' (aschbacherSolvableCore 3 Y) s,
          Subgroup.mem_map_of_mem _ s.2⟩ :
            S₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)))) ?_
      intro s t hst
      exact Subtype.ext (hqinj s s.2 t t.2 (congrArg Subtype.val hst))
    · refine Nat.card_le_card_of_surjective
        (fun s : S₀ => (⟨QuotientGroup.mk' (aschbacherSolvableCore 3 Y) s,
          Subgroup.mem_map_of_mem _ s.2⟩ :
            S₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Y)))) ?_
      rintro ⟨_, s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  set S := S₀.map Y.subtype with hS
  have hScard : Nat.card S = 27 := by
    rw [hS, Subgroup.card_map_of_injective Y.subtype_injective, hS₀card]
  have hinf : Subgroup.zpowers a ⊓ S = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hza, hzS⟩
    obtain ⟨z₀, hz₀, rfl⟩ := hzS
    have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) z₀ ∈
        Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
      rw [Subgroup.mem_center_iff]
      intro w
      induction w using QuotientGroup.induction_on with
      | H w =>
        change QuotientGroup.mk' (aschbacherSolvableCore 3 Y) w *
            QuotientGroup.mk' (aschbacherSolvableCore 3 Y) z₀ =
          QuotientGroup.mk' (aschbacherSolvableCore 3 Y) z₀ *
            QuotientGroup.mk' (aschbacherSolvableCore 3 Y) w
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hza
        have hwa : (w : G) * a = a * w := Subgroup.mem_centralizer_singleton_iff.mp (hYa w.2)
        simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at hk ⊢
        rw [← hk]
        exact (Commute.zpow_right (show Commute (w : G) a from hwa) k).eq
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    have h2 : z₀ ∈ S₀ ⊓ aschbacherSolvableCore 3 Y := ⟨hz₀, hcen⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    rw [h2]
    exact Subgroup.one_mem _
  have hcommaS : ∀ u ∈ Subgroup.zpowers a, ∀ s ∈ S, u * s = s * u := by
    intro u hu s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact hAc _ (A.zpow_mem haA k) _ (hS₀A hs)
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommaS
  have hao' : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hao', hScard] at hcard
  have hle : Subgroup.zpowers a ⊔ S ≤ A :=
    sup_le ((Subgroup.zpowers_le).mpr haA) hS₀A
  have heq : Subgroup.zpowers a ⊔ S = A :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hA81, hcard])
  have hx' : x ∈ ((Subgroup.zpowers a ⊔ S : Subgroup G) : Set G) := by
    rw [heq]
    exact hxA
  rw [hset] at hx'
  obtain ⟨u, hu, s, hs, hus⟩ := hx'
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ⟨i, s, Subgroup.map_subtype_le S₀ hs, hAab.2 s (hS₀A hs), hus.symm⟩

end Item812Res3

section Final


@[expose] def KF812AutY : Prop :=
  ∀ (M : Type) [Group M], (Nonempty (M ≃* alternatingGroup (Fin 9)) ∨
      Nonempty (M ≃* projSp 3 (GaloisField 2 1))) →
    (∀ β : MulAut M, β ^ 3 = 1 → KFacts.IsInnerAut β) ∧
      ∀ β : MulAut M, ∀ x : M, x ^ 3 = 1 →
        (∃ y : M, β x = y * x * y⁻¹) ∧ ∃ y : M, β x = y * x⁻¹ * y⁻¹

open Item812Res3 in
theorem fin812Frattini_of (hK : KF812AutY) : Fin812Frattini := by
  intro G _ _ A c L a b X Y n h g hg
  classical
  have h3 := h.toTheoremFourHyp.localRank_three.le
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ y ∈ A, ∀ y' ∈ A, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  have haA : a ∈ A := h.a_mem
  have ha1 : a ≠ 1 := h.a_ne_one
  have ha3 : a ^ 3 = 1 := hAab.2 a haA
  have hbA : b ∈ A := h.mem_pairOmega.1
  have hY := h.mem_thetaComponentsAt_Y
  have hYa : Y ≤ Subgroup.centralizer ({a} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt_three hY
  have hNY := h.normalizer_zpowers_le_normalizer_Y
  have hAN : A ≤ Subgroup.normalizer (Y : Set G) := fun y hy =>
    hNY (Item812Res2.mem_normalizer_zpowers_of_commute (hAc y hy a haA))
  obtain ⟨M, _, hM, ⟨e⟩, hKM⟩ : ∃ (M : Type) (_ : Group M), IsYModel M ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* M) ∧
      (Nonempty (M ≃* alternatingGroup (Fin 9)) ∨
        Nonempty (M ≃* projSp 3 (GaloisField 2 1))) := by
    rcases h.item89_Y with h9 | h6
    · exact ⟨_, inferInstance, isYModel_alternatingGroup_nine, h9,
        Or.inl ⟨MulEquiv.refl _⟩⟩
    · exact ⟨_, inferInstance, isYModel_projSp_three_two, h6, Or.inr ⟨MulEquiv.refl _⟩⟩
  obtain ⟨hinn, hcls⟩ := hK M hKM
  obtain ⟨i, s, hsY, hs3, hbs⟩ :=
    exists_mul_eq_of_mem h3 h.mem_partTwoF h.card_eq haA ha1 hY hM e hinn hAN hbA
  have hsa : s * a = a * s := Subgroup.mem_centralizer_singleton_iff.mp (hYa hsY)
  have hgY := hNY hg
  set β := thetaQuotMulAut Y (compAction Y ⟨g, hgY⟩) with hβ
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hq
  have hgs : g * s * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgY s).mp hsY
  have hβs : β (q ⟨s, hsY⟩) = q ⟨g * s * g⁻¹, hgs⟩ := rfl
  have hlift : ∀ (v : Y), v ^ 3 = 1 → β (q ⟨s, hsY⟩) = q v →
      ∃ u ∈ Y, g * s * g⁻¹ = u * (v : G) * u⁻¹ ∧ ∀ w ∈ Y, w * a = a * w := by
    intro v hv3 hβv
    have hmem : (⟨g * s * g⁻¹, hgs⟩ : Y)⁻¹ * v ∈ aschbacherSolvableCore 3 Y := by
      rw [← QuotientGroup.eq, ← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply, ← hq,
        ← hβs, hβv]
    obtain ⟨-, -, hN3, -⟩ :=
      solvable_prime_complement_core_characterization (H := Y) Nat.prime_three
    have hgs3 : (⟨g * s * g⁻¹, hgs⟩ : Y) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      rw [conj_pow, hs3]
      group
    obtain ⟨t, -, ht⟩ := exists_mem_conj_eq_of_inv_mul_mem hN3 hgs3 hv3 hmem
    refine ⟨(t : G), t.2, ?_, fun w hw => ?_⟩
    · have := congrArg Subtype.val ht
      simpa using this.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hYa hw)
  have key : ∀ σ : Y, σ ^ 3 = 1 → (∃ y' : M, MulAut.congr e β (e (q ⟨s, hsY⟩)) =
      y' * e (q σ) * y'⁻¹) → ∃ u ∈ Y, g * s * g⁻¹ = u * (σ : G) * u⁻¹ := by
    rintro σ hσ3 ⟨y', hy'⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 Y) (e.symm y')
    have hβv : β (q ⟨s, hsY⟩) = q (w * σ * w⁻¹) := by
      apply e.injective
      have h1 : MulAut.congr e β (e (q ⟨s, hsY⟩)) = e (β (q ⟨s, hsY⟩)) := by
        simp [MulAut.congr_apply]
      rw [← h1, hy']
      simp only [map_mul, map_inv]
      rw [hw, MulEquiv.apply_symm_apply]
    have hv3 : (w * σ * w⁻¹ : Y) ^ 3 = 1 := by
      rw [conj_pow, hσ3]
      group
    obtain ⟨u, huY, hgsu, -⟩ := hlift _ hv3 hβv
    refine ⟨u * (w : G), Y.mul_mem huY w.2, ?_⟩
    rw [hgsu]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hsY3 : (⟨s, hsY⟩ : Y) ^ 3 = 1 := Subtype.ext (by simpa using hs3)
  have hx3 : e (q ⟨s, hsY⟩) ^ 3 = 1 := by rw [← map_pow, ← map_pow, hsY3, map_one, map_one]
  obtain ⟨hcls1, hcls2⟩ := hcls (MulAut.congr e β) (e (q ⟨s, hsY⟩)) hx3
  have hga : g * a * g⁻¹ ∈ Subgroup.zpowers a :=
    (Subgroup.mem_normalizer_iff.mp hg a).mp (Subgroup.mem_zpowers a)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hga
  have hao : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hjmod : a ^ j = a ^ (j % 3) := by
    have := zpow_mod_orderOf a j
    rw [hao] at this
    push_cast at this
    exact this.symm
  have hjcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  have hYc : ∀ u ∈ Y, u * a = a * u := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp (hYa hu)
  have hNk : ∀ u ∈ Y, u⁻¹ * g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := fun u hu =>
    Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Item812Res2.mem_normalizer_zpowers_of_commute (hYc u hu))) hg
  rcases hjcases with h0 | h1 | h2
  · exfalso
    rw [hjmod, h0, zpow_zero] at hj
    apply ha1
    have : a = g⁻¹ * (g * a * g⁻¹) * g := by group
    rw [this, ← hj]
    group
  ·
    rw [hjmod, h1, zpow_one] at hj
    obtain ⟨u, huY, hgsu⟩ := key ⟨s, hsY⟩ hsY3 (by
      obtain ⟨y', hy'⟩ := hcls1
      exact ⟨y', hy'⟩)
    have hgai : g * a ^ i * g⁻¹ = a ^ i := by rw [← conj_zpow, ← hj]
    have huai : u * a ^ i = a ^ i * u := (Commute.zpow_right (hYc u huY) i).eq
    refine ⟨u, huY, u⁻¹ * g, ⟨hNk u huY, ?_⟩, by group⟩
    refine Item812Res2.mem_normalizer_zpowers_of_commute ?_
    have hkb : u⁻¹ * g * b * (u⁻¹ * g)⁻¹ = b := by
      calc u⁻¹ * g * b * (u⁻¹ * g)⁻¹ = u⁻¹ * (g * a ^ i * g⁻¹) * (g * s * g⁻¹) * u := by
            rw [hbs]; group
        _ = u⁻¹ * a ^ i * (u * s * u⁻¹) * u := by rw [hgai, hgsu]
        _ = u⁻¹ * (a ^ i * u) * s := by group
        _ = u⁻¹ * (u * a ^ i) * s := by rw [huai]
        _ = b := by rw [hbs]; group
    calc u⁻¹ * g * b = u⁻¹ * g * b * (u⁻¹ * g)⁻¹ * (u⁻¹ * g) := by group
      _ = b * (u⁻¹ * g) := by rw [hkb]
  ·
    rw [hjmod, h2] at hj
    obtain ⟨u, huY, hgsu⟩ := key (⟨s, hsY⟩)⁻¹ (by rw [inv_pow, hsY3, inv_one]) (by
      obtain ⟨y', hy'⟩ := hcls2
      refine ⟨y', ?_⟩
      rw [hy', map_inv, map_inv])
    have hgai : g * a ^ i * g⁻¹ = a ^ (-i) := by
      rw [← conj_zpow, ← hj, ← zpow_mul]
      have h3i : a ^ ((2 : ℤ) * i) = a ^ (-i) * a ^ ((3 : ℤ) * i) := by
        rw [← zpow_add]
        ring_nf
      rw [h3i, zpow_mul, show a ^ (3 : ℤ) = 1 by rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num,
        zpow_natCast, ha3], one_zpow, mul_one]
    have huai : u * a ^ (-i) = a ^ (-i) * u := (Commute.zpow_right (hYc u huY) (-i)).eq
    have hsai : s⁻¹ * a ^ (-i) = a ^ (-i) * s⁻¹ :=
      ((Commute.zpow_right (show Commute s a from hsa) (-i)).inv_left).eq
    refine ⟨u, huY, u⁻¹ * g, ⟨hNk u huY, ?_⟩, by group⟩
    have hkb : u⁻¹ * g * b * (u⁻¹ * g)⁻¹ = b⁻¹ := by
      calc u⁻¹ * g * b * (u⁻¹ * g)⁻¹ = u⁻¹ * (g * a ^ i * g⁻¹) * (g * s * g⁻¹) * u := by
            rw [hbs]; group
        _ = u⁻¹ * a ^ (-i) * (u * s⁻¹ * u⁻¹) * u := by rw [hgai, hgsu]; rfl
        _ = u⁻¹ * (a ^ (-i) * u) * s⁻¹ := by group
        _ = u⁻¹ * (u * a ^ (-i)) * s⁻¹ := by rw [huai]
        _ = a ^ (-i) * s⁻¹ := by group
        _ = s⁻¹ * a ^ (-i) := hsai.symm
        _ = b⁻¹ := by rw [hbs]; group
    have hkinv : (u⁻¹ * g)⁻¹⁻¹ * b * (u⁻¹ * g)⁻¹ = b⁻¹ := by rw [inv_inv]; exact hkb
    have := mem_normalizer_zpowers_of_conj_eq_inv hkinv
    simpa using Subgroup.inv_mem _ this

end Final

end CFSG.RankThree.PartTwo.Sec8
