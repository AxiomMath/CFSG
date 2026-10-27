module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.GroupTheory.PCore.PrimeCoreImages
import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.ResProof

open CFSG CFSG.RankThree.LocalRank

variable {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]

omit [Finite X] [N.Normal] in
theorem pow_three_eq_one_of_mem (hN3 : Nat.card N = 3) {n : X} (hn : n ∈ N) : n ^ 3 = 1 := by
  have h := orderOf_dvd_natCard (⟨n, hn⟩ : N)
  rw [Subgroup.orderOf_mk, hN3] at h
  exact orderOf_dvd_iff_pow_eq_one.mp h

omit [Finite X] [N.Normal] in
theorem isPGroup_three (hN3 : Nat.card N = 3) : IsPGroup 3 N :=
  IsPGroup.of_card (n := 1) (by rw [hN3, pow_one])

omit [Finite X] in
theorem not_isQuasisimple_quotient [Group.IsPerfect X] (hNZ : N ≤ Subgroup.center X)
    (h : ¬ IsQuasisimple X) : ¬ IsQuasisimple (X ⧸ N) := fun hq =>
  h ((CFSG.LocalCores.isQuasisimple_iff_of_surjective inferInstance (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (by rwa [QuotientGroup.ker_mk'])).mpr hq)

theorem pCore_two_quotient_eq_map (hNZ : N ≤ Subgroup.center X) (hN3 : Nat.card N = 3) :
    CFSG.pCore 2 (X ⧸ N) = (CFSG.pCore 2 X).map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  set M := CFSG.pPrimeCore 3 X with hMdef
  apply le_antisymm
  · have hM : CFSG.pPrimeCore 3 (X ⧸ N) = M.map π :=
      CFSG.central_p_subgroup_prime_core_quotient N hNZ (isPGroup_three N hN3)
    have hle : CFSG.pCore 2 (X ⧸ N) ≤ CFSG.pPrimeCore 3 (X ⧸ N) := by
      refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X ⧸ N))
      rw [hk]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have hinj : ∀ m ∈ M, π m = 1 → m = 1 := by
      intro m hmM hm1
      have hmN : m ∈ N := (QuotientGroup.eq_one_iff m).mp hm1
      have h1 : orderOf m ∣ 3 := by
        rw [← hN3, ← Subgroup.orderOf_mk m hmN]
        exact orderOf_dvd_natCard _
      have h2 : orderOf m ∣ Nat.card M := by
        rw [← Subgroup.orderOf_mk m hmM]
        exact orderOf_dvd_natCard _
      have hcop : Nat.Coprime 3 (Nat.card M) := CFSG.pPrimeCore_coprime_card
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    set T : Subgroup X := M ⊓ (CFSG.pCore 2 (X ⧸ N)).comap π with hT
    have hMn : M.Normal := CFSG.pPrimeCore_normal
    have hCn : ((CFSG.pCore 2 (X ⧸ N)).comap π).Normal :=
      (CFSG.pCore_normal (p := 2) (G := X ⧸ N)).comap π
    have hTn : T.Normal := Subgroup.normal_inf_normal _ _
    have hT2 : IsPGroup 2 T := by
      intro t
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X ⧸ N)) ⟨π t, t.2.2⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 : π ((t : X) ^ 2 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      simpa using hinj _ (M.pow_mem t.2.1 _) h1
    have hTle : T ≤ CFSG.pCore 2 X := le_sSup ⟨hTn, hT2⟩
    intro y hy
    have hy' : y ∈ M.map π := hM ▸ hle hy
    obtain ⟨m, hm, rfl⟩ := hy'
    exact ⟨m, hTle ⟨hm, hy⟩, rfl⟩
  · exact le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := X)).map π (QuotientGroup.mk'_surjective N),
      (CFSG.pCore_isPGroup (p := 2) (G := X)).map π⟩

theorem pCore_two_quotient_eq_bot (hNZ : N ≤ Subgroup.center X) (hN3 : Nat.card N = 3)
    (hO2 : CFSG.pCore 2 X = ⊥) : CFSG.pCore 2 (X ⧸ N) = ⊥ := by
  rw [pCore_two_quotient_eq_map N hNZ hN3, hO2, Subgroup.map_bot]

theorem isQuasisimple_quotient_pCore_two_iff [Group.IsPerfect X] (hNZ : N ≤ Subgroup.center X)
    (hN3 : Nat.card N = 3) :
    IsQuasisimple (X ⧸ CFSG.pCore 2 X) ↔ IsQuasisimple ((X ⧸ N) ⧸ CFSG.pCore 2 (X ⧸ N)) := by
  have hmap := pCore_two_quotient_eq_map N hNZ hN3
  set π := QuotientGroup.mk' N with hπ
  have hle : CFSG.pCore 2 X ≤ (CFSG.pCore 2 (X ⧸ N)).comap π := by
    rw [hmap]
    exact Subgroup.le_comap_map _ _
  set f := QuotientGroup.map (CFSG.pCore 2 X) (CFSG.pCore 2 (X ⧸ N)) π hle with hf
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨(x : X ⧸ CFSG.pCore 2 X), rfl⟩
  have hker : f.ker ≤ Subgroup.center (X ⧸ CFSG.pCore 2 X) := by
    intro u hu
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ u
    have h1 : π x ∈ CFSG.pCore 2 (X ⧸ N) := by
      have := MonoidHom.mem_ker.mp hu
      rw [QuotientGroup.mk'_apply, hf, QuotientGroup.map_mk, QuotientGroup.eq_one_iff] at this
      exact this
    rw [hmap] at h1
    obtain ⟨t, ht, hte⟩ := h1
    have hn : t⁻¹ * x ∈ N := by
      rw [← QuotientGroup.eq]
      exact hte
    have hx : QuotientGroup.mk' (CFSG.pCore 2 X) x =
        QuotientGroup.mk' (CFSG.pCore 2 X) (t⁻¹ * x) := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
      simpa [mul_assoc] using
        (CFSG.pCore_normal (p := 2) (G := X)).conj_mem t⁻¹ (Subgroup.inv_mem _ ht) x⁻¹
    rw [hx, Subgroup.mem_center_iff]
    intro v
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ v
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hNZ hn) v]
  exact CFSG.LocalCores.isQuasisimple_iff_of_surjective inferInstance f hfs hker

omit [Finite X] in
theorem le_oddCore (hN3 : Nat.card N = 3) : N ≤ CFSG.oddCore X :=
  le_sSup ⟨inferInstance, by rw [hN3]; decide⟩

theorem oddCore_quotient (hN3 : Nat.card N = 3) :
    CFSG.oddCore (X ⧸ N) = (CFSG.oddCore X).map (QuotientGroup.mk' N) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGDGroups.oddCore_eq_pPrimeCore_two, CFSG.ABGDGroups.oddCore_eq_pPrimeCore_two]
  exact (CFSG.prime_complement_kernel_core_preimage (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) (by rw [QuotientGroup.ker_mk', hN3]; norm_num)).2.symm

theorem nonempty_quotient_oddCore_equiv (hN3 : Nat.card N = 3) :
    Nonempty ((X ⧸ N) ⧸ CFSG.oddCore (X ⧸ N) ≃* X ⧸ CFSG.oddCore X) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (oddCore_quotient N hN3)).trans
    (QuotientGroup.quotientQuotientEquivQuotient N (CFSG.oddCore X) (le_oddCore N hN3))⟩

theorem pRank_two_quotient (hN3 : Nat.card N = 3) :
    CFSG.Open.pRank 2 (⊤ : Subgroup (X ⧸ N)) = CFSG.Open.pRank 2 (⊤ : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.SectionRank.pRank_quotient_eq N (by rw [hN3]; norm_num)

section Theta

variable (hq : IsQuasisimple (X ⧸ aschbacherSolvableCore 3 X))
  (hZ : Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) =
    N.map (QuotientGroup.mk' (aschbacherSolvableCore 3 X)))

omit [Finite X] [N.Normal] in
include hZ in
theorem le_ker_centerQuot :
    N ≤ ((QuotientGroup.mk' (Subgroup.center (X ⧸ aschbacherSolvableCore 3 X))).comp
      (QuotientGroup.mk' (aschbacherSolvableCore 3 X))).ker := by
  intro n hn
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, hZ]
  exact Subgroup.mem_map_of_mem _ hn

@[expose] noncomputable def centerQuotHom :
    X ⧸ N →* (X ⧸ aschbacherSolvableCore 3 X) ⧸
      Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) :=
  QuotientGroup.lift N ((QuotientGroup.mk' (Subgroup.center (X ⧸ aschbacherSolvableCore 3 X))).comp
      (QuotientGroup.mk' (aschbacherSolvableCore 3 X))) (le_ker_centerQuot N hZ)

omit [Finite X] in
include hZ in
theorem centerQuotHom_mk (x : X) :
    centerQuotHom N hZ (x : X ⧸ N) =
      ((x : X ⧸ aschbacherSolvableCore 3 X) :
        (X ⧸ aschbacherSolvableCore 3 X) ⧸ Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)) :=
  rfl

omit [Finite X] in
include hZ in
theorem centerQuotHom_surjective : Function.Surjective (centerQuotHom N hZ) := by
  intro y
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)) y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 X) q
  exact ⟨(x : X ⧸ N), rfl⟩

omit [Finite X] in
include hZ in
theorem centerQuotHom_ker :
    (centerQuotHom N hZ).ker = (aschbacherSolvableCore 3 X).map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, centerQuotHom_mk, QuotientGroup.eq_one_iff,
      hZ] at hy
    obtain ⟨n, hn, hnx⟩ := hy
    have hθ : n⁻¹ * x ∈ aschbacherSolvableCore 3 X := by
      rw [← QuotientGroup.eq]
      exact hnx
    refine ⟨n⁻¹ * x, hθ, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h1 := (inferInstance : N.Normal).conj_mem n hn x⁻¹
    simpa [mul_assoc] using h1
  · rintro _ ⟨t, ht, rfl⟩
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, centerQuotHom_mk]
    have : ((t : X) : X ⧸ aschbacherSolvableCore 3 X) = 1 := (QuotientGroup.eq_one_iff t).mpr ht
    rw [this, QuotientGroup.mk_one]

include hq hZ in
theorem theta_quotient_eq :
    aschbacherSolvableCore 3 (X ⧸ N) = (centerQuotHom N hZ).ker := by
  have hθX := solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hθY := solvable_prime_complement_core_characterization (H := X ⧸ N) Nat.prime_three
  have : Group.IsSolvable (aschbacherSolvableCore 3 X) := hθX.1
  apply le_antisymm
  ·
    set S := (aschbacherSolvableCore 3 (X ⧸ N)).map (centerQuotHom N hZ) with hS
    have hSn : S.Normal := Subgroup.Normal.map inferInstance _ (centerQuotHom_surjective N hZ)
    have hSs : Group.IsSolvable S := by
      have : Group.IsSolvable (aschbacherSolvableCore 3 (X ⧸ N)) := hθY.1
      exact Group.isSolvable_of_surjective
        ((centerQuotHom N hZ).subgroupMap_surjective (aschbacherSolvableCore 3 (X ⧸ N)))
    have : IsSimpleGroup ((X ⧸ aschbacherSolvableCore 3 X) ⧸
        Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)) := hq.2.1
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).mp hbot
    · exfalso
      obtain ⟨hperf, -, a, b, hab⟩ := hq
      have : Nontrivial ((X ⧸ aschbacherSolvableCore 3 X) ⧸
          Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)) := ⟨⟨a * b, b * a, hab⟩⟩
      have : Group.IsPerfect ((X ⧸ aschbacherSolvableCore 3 X) ⧸
          Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)) := inferInstance
      rw [htop] at hSs
      set Q := (X ⧸ aschbacherSolvableCore 3 X) ⧸
        Subgroup.center (X ⧸ aschbacherSolvableCore 3 X) with hQ
      have hsol : Group.IsSolvable Q :=
        Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q) : (⊤ : Subgroup Q) →* Q))
          Subgroup.topEquiv.surjective
      exact Group.IsPerfect.not_isSolvable _ hsol
  ·
    rw [centerQuotHom_ker N hZ]
    refine hθY.2.2.2.1 _ (Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N))
      (Group.isSolvable_of_surjective
        ((QuotientGroup.mk' N).subgroupMap_surjective (aschbacherSolvableCore 3 X))) ?_
    exact fun h3 => hθX.2.2.1 (h3.trans (Subgroup.card_map_dvd _ _))

include hq hZ in
theorem nonempty_quotient_theta_equiv :
    Nonempty ((X ⧸ N) ⧸ aschbacherSolvableCore 3 (X ⧸ N) ≃*
      (X ⧸ aschbacherSolvableCore 3 X) ⧸ Subgroup.center (X ⧸ aschbacherSolvableCore 3 X)) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (theta_quotient_eq N hq hZ)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (centerQuotHom_surjective N hZ))⟩

end Theta

theorem exists_lift_involution_rank (hNZ : N ≤ Subgroup.center X) (hN3 : Nat.card N = 3)
    {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) {t : X ⧸ N} (ht : orderOf t = 2) {P : Subgroup (X ⧸ N)}
    (hPt : P ≤ Subgroup.centralizer {t}) (hP : 3 ≤ CFSG.pRank r P) :
    ∃ s : X, orderOf s = 2 ∧ ∃ P' : Subgroup X, P' ≤ Subgroup.centralizer {s} ∧
      3 ≤ CFSG.pRank r P' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' N with hπ
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N t
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  set s := x ^ 3 with hs
  have hπs : π s = t := by
    rw [hs, map_pow, hx]
    calc t ^ 3 = t ^ 2 * t := by rw [pow_succ]
      _ = t := by rw [ht2, one_mul]
  have hx2N : x ^ 2 ∈ N := by
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_pow]
    change (π x) ^ 2 = 1
    rw [hx, ht2]
  have hs2 : s ^ 2 = 1 := by
    rw [hs, ← pow_mul, show 3 * 2 = 2 * 3 by norm_num, pow_mul]
    exact pow_three_eq_one_of_mem N hN3 hx2N
  have hs1 : s ≠ 1 := fun h => ht1 (by rw [← hπs, h, map_one])
  refine ⟨s, orderOf_eq_prime hs2 hs1, P.comap π, ?_, ?_⟩
  ·
    intro y hy
    have hyt : π y * t = t * π y := Subgroup.mem_centralizer_singleton_iff.mp (hPt hy)
    set w := y * s * y⁻¹ * s⁻¹ with hw
    have hwN : w ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      change π (y * s * y⁻¹ * s⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hπs, hyt, mul_inv_cancel_right,
        mul_inv_cancel]
    have hwc : ∀ g : X, w * g = g * w := fun g => Subgroup.mem_center_iff.mp (hNZ hwN) g |>.symm
    have hconj : y * s * y⁻¹ = w * s := by rw [hw]; group
    have hsq : (y * s * y⁻¹) ^ 2 = 1 := by
      rw [conj_pow, hs2, mul_one, mul_inv_cancel]
    have hw2 : w ^ 2 = 1 := by
      have h1 : (w * s) ^ 2 = 1 := hconj ▸ hsq
      have h2 : (w * s) ^ 2 = w ^ 2 * s ^ 2 := by
        calc (w * s) ^ 2 = w * (s * w) * s := by rw [sq]; group
          _ = w * (w * s) * s := by rw [← hwc s]
          _ = w ^ 2 * s ^ 2 := by rw [sq, sq]; group
      rw [h2, hs2, mul_one] at h1
      exact h1
    have hw3 : w ^ 3 = 1 := pow_three_eq_one_of_mem N hN3 hwN
    have hw1 : w = 1 := by
      calc w = w ^ 3 * (w ^ 2)⁻¹ := by group
        _ = 1 := by rw [hw2, hw3, inv_one, one_mul]
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : y * s * y⁻¹ = s := by rw [hconj, hw1, one_mul]
    calc y * s = y * s * y⁻¹ * y := by group
      _ = s * y := by rw [this]
  ·
    have hr1 : 1 < r := hr.one_lt
    have : Fact r.Prime := ⟨hr⟩
    set f : P.comap π →* P := π.subgroupComap P with hf
    have hfs : Function.Surjective f :=
      π.subgroupComap_surjective P (QuotientGroup.mk'_surjective N)
    have hker : ¬ r ∣ Nat.card f.ker := by
      intro hrk
      have hle : f.ker.map (P.comap π).subtype ≤ N := by
        rintro _ ⟨y, hy, rfl⟩
        have h1 : π (y : X) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
        exact (QuotientGroup.eq_one_iff _).mp h1
      have hdvd : Nat.card f.ker ∣ 3 := by
        rw [← hN3, ← Subgroup.card_map_of_injective (P.comap π).subtype_injective]
        exact Subgroup.card_dvd_of_le hle
      exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hrk.trans hdvd))
    have e := QuotientGroup.quotientKerEquivOfSurjective f hfs
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top] at hP ⊢
    rw [← CFSG.SectionRank.pRank_quotient_eq f.ker hker,
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr1 e]
    exact hP

end CFSG.RankThree.PartTwo.Sec13.ResProof
