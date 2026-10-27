module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
import CFSG.Fischer.Classification.Recognition.Basic
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10LayerS6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase
open scoped commutatorElement

private theorem isQuasisimple_subgroupOf {G : Type} [Group G] {K J : Subgroup G} (hJK : J ≤ K)
    (hJq : CFSG.Open.IsQuasisimple ↥J) : CFSG.IsQuasisimple ↥(J.subgroupOf K) :=
  (CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple hJq).of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hJK)

private theorem isQuasisimple_map_solvableRadical {G : Type} [Group G] [Finite G]
    {K J : Subgroup G} (hJK : J ≤ K) (hJn : (J.subgroupOf K).Normal)
    (hJq : CFSG.Open.IsQuasisimple ↥J) :
    CFSG.IsQuasisimple ↥((J.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥K))) ∧
      ((J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K))).Normal := by
  have hJ'qs : CFSG.IsQuasisimple ↥(J.subgroupOf K) := isQuasisimple_subgroupOf hJK hJq
  haveI hJ'n : (J.subgroupOf K).Normal := hJn
  haveI : Group.IsPerfect ↥(J.subgroupOf K) := hJ'qs.1
  haveI : Nontrivial ↥(J.subgroupOf K) := CFSG.LocalCores.isQuasisimple_nontrivial hJ'qs
  have hnotR : ¬ J.subgroupOf K ≤ CFSG.solvableRadical ↥K := by
    intro hle
    haveI : Group.IsSolvable ↥(CFSG.solvableRadical ↥K) :=
      CFSG.Quasithin.A3.solvableRadical_isSolvable
    haveI : Group.IsSolvable ↥(J.subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable ↥(J.subgroupOf K) inferInstance
  refine ⟨?_, Subgroup.Normal.map hJn _ (QuotientGroup.mk'_surjective _)⟩
  refine CFSG.LocalCores.isQuasisimple_map hJ'qs _ ?_
  rwa [QuotientGroup.ker_mk']

theorem isSolvable_quotient_map_solvableRadical {G : Type} [Group G] [Finite G]
    {K J : Subgroup G} (h2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ J)
    [hLn : ((J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K))).Normal] :
    Group.IsSolvable ((↥K ⧸ CFSG.solvableRadical ↥K) ⧸
      (J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2' : ∀ x : ↥K, ∃ k : ℕ, x ^ 2 ^ k ∈ J.subgroupOf K := by
    intro x
    obtain ⟨k, hk⟩ := h2 x.1 x.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
  have h2g : IsPGroup 2 ((↥K ⧸ CFSG.solvableRadical ↥K) ⧸
      (J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K))) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨k, hk⟩ := h2' x
    refine ⟨k, ?_⟩
    have hxL : (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) (x ^ 2 ^ k) ∈
        (J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) :=
      Subgroup.mem_map.mpr ⟨x ^ 2 ^ k, hk, rfl⟩
    rw [← QuotientGroup.mk_pow ((J.subgroupOf K).map
        (QuotientGroup.mk' (CFSG.solvableRadical ↥K))) (QuotientGroup.mk x) (2 ^ k),
      QuotientGroup.eq_one_iff, ← QuotientGroup.mk_pow (CFSG.solvableRadical ↥K) x (2 ^ k),
      ← QuotientGroup.mk'_apply (CFSG.solvableRadical ↥K) (x ^ 2 ^ k)]
    exact hxL
  haveI := h2g.isNilpotent
  exact IsNilpotent.to_isSolvable

private theorem le_twoResidual_of_forall_pow_mem {Q : Type} [Group Q] [Finite Q]
    {J' : Subgroup Q} (hJq : Group.IsPerfect ↥J')
    (h2 : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ J') :
    J' ≤ twoResidual (⊤ : Subgroup Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro j hj
  rw [mem_twoResidual_iff]
  intro N _ hnorm hN2
  haveI hNn : N.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hnorm)
  haveI : Group.IsPerfect ↥J' := hJq
  haveI : Group.IsPerfect ↥(J'.map (QuotientGroup.mk' N)) :=
    Group.IsPerfect.map (QuotientGroup.mk' N)
  have h2g : IsPGroup 2 ↥(J'.map (QuotientGroup.mk' N)) := by
    rw [isPGroup_iff_pow_pow_eq_one]
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨k, hk⟩ := hN2 x (Subgroup.mem_top x)
    refine ⟨k, Subtype.ext ?_⟩
    show ((QuotientGroup.mk' N) x) ^ 2 ^ k = 1
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_pow N x (2 ^ k), QuotientGroup.eq_one_iff]
    exact hk
  have hbot : J'.map (QuotientGroup.mk' N) = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(J'.map (QuotientGroup.mk' N)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI : Group.IsSolvable ↥(J'.map (QuotientGroup.mk' N)) := by
      haveI := h2g.isNilpotent
      exact IsNilpotent.to_isSolvable
    exact Group.IsPerfect.not_isSolvable ↥(J'.map (QuotientGroup.mk' N)) inferInstance
  have hmem : J' ≤ (QuotientGroup.mk' N).ker := (Subgroup.map_eq_bot_iff J').mp hbot
  rw [QuotientGroup.ker_mk'] at hmem
  exact hmem hj

private theorem perfectCore_le_of_forall_pow_mem {Q : Type} [Group Q] [Finite Q]
    {J' : Subgroup Q} (hJn : J'.Normal)
    (h2 : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ J') :
    perfectCore (⊤ : Subgroup Q) ≤ J' := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hJ'n : J'.Normal := hJn
  have hsolv : Group.IsSolvable (Q ⧸ J') := by
    have h2g : IsPGroup 2 (Q ⧸ J') := by
      rw [isPGroup_iff_pow_pow_eq_one]
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨k, hk⟩ := h2 x
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow J' x (2 ^ k), QuotientGroup.eq_one_iff]
      exact hk
    haveI := h2g.isNilpotent
    exact IsNilpotent.to_isSolvable
  haveI : Group.IsSolvable (Q ⧸ J') := hsolv
  have hm : (perfectCore (⊤ : Subgroup Q)).map (QuotientGroup.mk' J') = ⊥ := by
    rw [map_perfectCore, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective J'),
      (isSolvable_iff_perfectCore_eq_bot (⊤ : Subgroup (Q ⧸ J'))).mp inferInstance]
  rw [← QuotientGroup.ker_mk' J']
  exact (Subgroup.map_eq_bot_iff _).mp hm

theorem twoResidual_eq_perfectCore_of_forall_pow_mem {Q : Type} [Group Q] [Finite Q]
    {J' : Subgroup Q} (hJn : J'.Normal) (hJperf : ⁅J', J'⁆ = J')
    (h2 : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ J') :
    twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q) := by
  have hle : twoResidual (⊤ : Subgroup Q) ≤ J' :=
    twoResidual_le_of_isTwoQuotient (H := ⊤) (N := J') le_top
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hJn]) (fun y _ => h2 y)
  have hge : J' ≤ twoResidual (⊤ : Subgroup Q) :=
    le_twoResidual_of_forall_pow_mem (Subgroup.isPerfect_iff.mpr hJperf) h2
  have hres : twoResidual (⊤ : Subgroup Q) = J' := le_antisymm hle hge
  have hpc : perfectCore (⊤ : Subgroup Q) = J' :=
    le_antisymm (perfectCore_le_of_forall_pow_mem hJn h2)
      (le_perfectCore_of_perfect le_top hJperf)
  rw [hres, hpc]

theorem pCore_oInftyE_eq_top_of_le {Q : Type} [Group Q] [Finite Q] {J' : Subgroup Q}
    (h2 : ∀ x : Q, ∃ k : ℕ, x ^ 2 ^ k ∈ J') (hle : J' ≤ oInftyE Q) :
    CFSG.pCore 2 (Q ⧸ oInftyE Q) = ⊤ := by
  rw [E1.pCore_two_quotient_eq_top_iff]
  intro x
  obtain ⟨k, hk⟩ := h2 x
  exact ⟨k, hle hk⟩

theorem commutator_barRad_ne_bot {G : Type} [Group G] [Finite G] {A K J : Subgroup G}
    (hJK : J ≤ K) (hAK : A ≤ K)
    (hAJ : ∃ a ∈ A, ∃ x ∈ J, ⁅a, x⁆ ∉ (CFSG.solvableRadical ↥K).map K.subtype) :
    ⁅(J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K)),
      E1.barRad ↥K (A.subgroupOf K)⁆ ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha, x, hx, hne⟩ := hAJ
  have haK : a ∈ K := hAK ha
  have hxK : x ∈ K := hJK hx
  let ā : ↥K := ⟨a, haK⟩
  let xq : ↥K := ⟨x, hxK⟩
  have hāB : (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) ā ∈
      E1.barRad ↥K (A.subgroupOf K) :=
    Subgroup.mem_map.mpr ⟨ā, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
  have hxL : (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) xq ∈
      (J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) :=
    Subgroup.mem_map.mpr ⟨xq, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hmem : ⁅(QuotientGroup.mk' (CFSG.solvableRadical ↥K)) ā,
      (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) xq⁆ = 1 := by
    have h1 : ⁅(QuotientGroup.mk' (CFSG.solvableRadical ↥K)) ā,
        (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) xq⁆ ∈
        ⁅E1.barRad ↥K (A.subgroupOf K),
          (J.subgroupOf K).map (QuotientGroup.mk' (CFSG.solvableRadical ↥K))⁆ :=
      Subgroup.commutator_mem_commutator hāB hxL
    rw [Subgroup.commutator_comm, hbot, Subgroup.mem_bot] at h1
    exact h1
  have hone : (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) ⁅ā, xq⁆ = 1 := by
    rw [map_commutatorElement]
    exact hmem
  have hRmem : ⁅ā, xq⁆ ∈ CFSG.solvableRadical ↥K := (QuotientGroup.eq_one_iff _).mp hone
  apply hne
  exact Subgroup.mem_map.mpr ⟨⁅ā, xq⁆, hRmem, map_commutatorElement K.subtype ā xq⟩

theorem eCaseII_of_normal_quasisimple {G : Type} [Group G] [Finite G] {T A K J : Subgroup G}
    (hJK : J ≤ K) (hJn : (J.subgroupOf K).Normal) (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hK2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ J)
    (hR : E1.IsTwoClosed (CFSG.solvableRadical ↥K)) (hAK : A ≤ K)
    (hAJ : ∃ a ∈ A, ∃ x ∈ J, ⁅a, x⁆ ∉ (CFSG.solvableRadical ↥K).map K.subtype) :
    ECaseII T A K := by
  set R : Subgroup ↥K := CFSG.solvableRadical ↥K with hRdef
  set J' : Subgroup ↥K := J.subgroupOf K with hJ'def
  set π : ↥K →* (↥K ⧸ R) := QuotientGroup.mk' R with hπdef
  set L : Subgroup (↥K ⧸ R) := J'.map π with hLdef
  have hJ'2 : ∀ x : ↥K, ∃ k : ℕ, x ^ 2 ^ k ∈ J' := by
    intro x
    obtain ⟨k, hk⟩ := hK2 x.1 x.2
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk⟩
  obtain ⟨hLqs, hLn⟩ := isQuasisimple_map_solvableRadical hJK hJn hJq
  have hsolv_quot : Group.IsSolvable ((↥K ⧸ R) ⧸ L) :=
    isSolvable_quotient_map_solvableRadical hK2 (hLn := hLn)
  have hlayer : CFSG.layer (↥K ⧸ R) = L :=
    CFSG.OddStandard.SmallF3.Omega.LayerS6.layer_eq_of_normal_quasisimple L hLqs hsolv_quot
  have hsup : CFSG.layer (↥K ⧸ R) =
      ⨆ t ∈ ((tA T A).subgroupOf K).map π, L.map (MulAut.conj t).toMonoidHom := by
    rw [hlayer]
    refine le_antisymm ?_ (iSup₂_le fun t _ => ?_)
    · refine le_iSup₂_of_le (1 : ↥K ⧸ R) ?_ ?_
      · exact Subgroup.mem_map.mpr ⟨1, Subgroup.one_mem _, map_one π⟩
      · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (by
          rw [Subgroup.normalizer_eq_top_iff.mpr hLn]; exact Subgroup.mem_top _)).ge
    · exact le_of_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp (by
        rw [Subgroup.normalizer_eq_top_iff.mpr hLn]; exact Subgroup.mem_top t))
  have hcomm_ne : ⁅L, E1.barRad ↥K (A.subgroupOf K)⁆ ≠ ⊥ :=
    commutator_barRad_ne_bot hJK hAK hAJ
  have halt : L = ⁅L, E1.barRad ↥K (A.subgroupOf K)⁆ := by
    have hBL : ⁅L, E1.barRad ↥K (A.subgroupOf K)⁆ ≤ L :=
      Subgroup.commutator_le_left L _
    have hN : (⁅L, E1.barRad ↥K (A.subgroupOf K)⁆.subgroupOf L).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hBL).mpr
        (Subgroup.normalizer_commutator_ge_left L _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLqs hN with htop | hcen
    · rw [Subgroup.subgroupOf_eq_top] at htop
      exact le_antisymm htop hBL
    · exfalso
      have hcomm : ⁅⁅L, E1.barRad ↥K (A.subgroupOf K)⁆, L⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        rintro n hn l hl
        have hn' : (⟨n, hBL hn⟩ : ↥L) ∈ ⁅L, E1.barRad ↥K (A.subgroupOf K)⁆.subgroupOf L := hn
        simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp (hcen hn') ⟨l, hl⟩)
      exact hcomm_ne (CFSG.LocalCores.perfect_double_commutator hLqs.1 hcomm)
  have hres_eq : twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K) :=
    twoResidual_eq_perfectCore_of_forall_pow_mem hJn
      (Subgroup.isPerfect_iff.mp (isQuasisimple_subgroupOf hJK hJq).1) hJ'2
  have hJ'le : J' ≤ oInftyE ↥K := by
    intro j hj
    show j ∈ (CFSG.layer (↥K ⧸ R)).comap π
    rw [hlayer]
    exact Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨j, hj, rfl⟩)
  refine ⟨hR, pCore_oInftyE_eq_top_of_le hJ'2 hJ'le, hres_eq, L,
    ⟨hLqs, hLn.isSubnormal⟩, hsup, Or.inl halt⟩

end CFSG.LocalAnalysis.WeakClosure81
