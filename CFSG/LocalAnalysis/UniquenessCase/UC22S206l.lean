module

public import CFSG.Quasithin.H13.A7BlkAct
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftA
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4L4Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptPre ptCore ptCore_le_ptPre ptHom ptHom_surjective ker_ptHom
  isPGroup_ker_ptHom isSimpleGroup_stabilizer stabEquiv le_pCore_of_normal)

variable {G : Type} [Group G]

theorem uc22s206l_eq_top_of_normal [Finite G] {L : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} {N : Subgroup ↥(ptCore α i)} (hN : N.Normal)
    {n : ↥(ptCore α i)} (hn : n ∈ N) (hn1 : ptHom α i n ≠ 1) : N = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hN
  haveI := isSimpleGroup_stabilizer (n := 9) (by norm_num) i
  have hsurj := ptHom_surjective α hα (by norm_num) i
  haveI : (N.map (ptHom α i)).Normal := hN.map _ hsurj
  have htop : N.map (ptHom α i) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (ptHom α i)) with h | h
    · have hmem : ptHom α i n ∈ N.map (ptHom α i) := mem_map_of_mem _ hn
      rw [h, Subgroup.mem_bot] at hmem
      exact absurd hmem hn1
    · exact h
  have h2 : IsPGroup 2 (↥(ptCore α i) ⧸ N) := by
    intro q
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hkN : ptHom α i k ∈ N.map (ptHom α i) := by
      rw [htop]
      exact mem_top _
    obtain ⟨m, hm, hmk⟩ := hkN
    have hk : m⁻¹ * k ∈ (ptHom α i).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmk, inv_mul_cancel]
    obtain ⟨a, ha⟩ := isPGroup_ker_ptHom α hker i ⟨_, hk⟩
    have ha' : (m⁻¹ * k) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    refine ⟨a, ?_⟩
    have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    have hmk' : QuotientGroup.mk' N k = QuotientGroup.mk' N (m⁻¹ * k) := by
      rw [map_mul, map_inv, hm1, inv_one, one_mul]
    rw [hmk', ← map_pow, ha', map_one]
  haveI : Group.IsPerfect ↥(ptCore α i) :=
    Subgroup.isPerfect_iff.2 (CFSG.Quasithin.perfectCore_perfect (ptPre α i))
  have hsub : Subsingleton (↥(ptCore α i) ⧸ N) := by
    by_contra hns
    haveI : Nontrivial (↥(ptCore α i) ⧸ N) := not_subsingleton_iff_nontrivial.1 hns
    exact Group.IsPerfect.not_isNilpotent (↥(ptCore α i) ⧸ N) h2.isNilpotent
  exact eq_top_iff.mpr fun k _ => (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)

open scoped Pointwise in
theorem uc22s206l_exists_not_normalizer [Finite G] {L : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} {Y : Type} [Group Y]
    (φ : ↥(ptCore α i) →* Y) {y : ↥(ptCore α i)} (hy : ptHom α i y ≠ 1) {J₀ : Subgroup Y}
    (hJ₀ : IsComponentOf J₀ ⊤) (hφ : ¬ φ.range ≤ normalizer (J₀ : Set Y)) :
    ∃ J : Subgroup Y, IsComponentOf J ⊤ ∧ φ y ∉ normalizer (J : Set Y) := by
  by_contra hcon
  push Not at hcon
  have hsmul : ∀ (g : Y) {J : Subgroup Y}, IsComponentOf J ⊤ →
      IsComponentOf (ConjAct.toConjAct g • J) ⊤ := by
    intro g J hJ
    rw [CFSG.LocalAnalysis.RankThreeUC.S15.perfect_le_normalizer_component_aux3]
    exact CFSG.LocalAnalysis.RankThreeUC.S15.layerIn_normal_aux1 ⊤ hJ g
  let N : Subgroup ↥(ptCore α i) :=
    ⨅ (J : Subgroup Y) (_ : IsComponentOf J ⊤), (normalizer (J : Set Y)).comap φ
  have hmem : ∀ k, k ∈ N ↔
      ∀ J : Subgroup Y, IsComponentOf J ⊤ → φ k ∈ normalizer (J : Set Y) := fun k => by
    simp only [N, Subgroup.mem_iInf, Subgroup.mem_comap]
  have hN : N.Normal := by
    refine ⟨fun n hn k => (hmem _).2 fun J hJ => ?_⟩
    have h1 := (hmem n).1 hn _ (hsmul (φ k)⁻¹ hJ)
    rw [← Subgroup.conjAct_pointwise_smul_iff] at h1 ⊢
    simp only [map_mul, map_inv, mul_smul] at h1 ⊢
    rw [h1, smul_inv_smul]
  have hNtop := uc22s206l_eq_top_of_normal α hα hker hN ((hmem y).2 hcon) hy
  apply hφ
  rintro _ ⟨k, rfl⟩
  have hk : k ∈ N := by
    rw [hNtop]
    exact mem_top k
  exact (hmem k).1 hk J₀ hJ₀

theorem uc22s206l_exists_not_normalizer_bar [Finite G] {L M : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} (hKM : ptCore α i ≤ M)
    {y : ↥(ptCore α i)} (hy : ptHom α i y ≠ 1) {J₀ : Subgroup (Bar2 M)}
    (hJ₀ : IsComponentOf J₀ ⊤)
    (hK : ¬ ((ptCore α i).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ≤
      normalizer (J₀ : Set (Bar2 M))) :
    ∃ J : Subgroup (Bar2 M), IsComponentOf J ⊤ ∧
      QuotientGroup.mk' (CFSG.pCore 2 ↥M) (Subgroup.inclusion hKM y) ∉
        normalizer (J : Set (Bar2 M)) := by
  refine uc22s206l_exists_not_normalizer α hα hker
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM)) hy hJ₀
    fun h => hK ?_
  rintro _ ⟨m, hm, rfl⟩
  exact h ⟨⟨(m : G), hm⟩, rfl⟩

theorem uc22s206l_nonempty_range [Finite G] {L : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} {Γ : Type} [Group Γ] [Finite Γ]
    (ψ : ↥(ptCore α i) →* Γ) (hψ : ψ.range ≠ ⊥) :
    Nonempty (Bar2 ψ.range ≃* alternatingGroup (Fin 8)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : ψ.ker ≤ (ptHom α i).ker := by
    intro k hk
    by_contra hk1
    apply hψ
    have htop := uc22s206l_eq_top_of_normal α hα hker ψ.normal_ker hk
      fun h => hk1 (MonoidHom.mem_ker.mpr h)
    rw [eq_bot_iff]
    rintro _ ⟨k', rfl⟩
    have hk' : k' ∈ ψ.ker := by
      rw [htop]
      exact mem_top k'
    rw [Subgroup.mem_bot]
    exact MonoidHom.mem_ker.mp hk'
  let π : ↥(ptCore α i) →* alternatingGroup (Fin 8) :=
    (stabEquiv i).toMonoidHom.comp (ptHom α i)
  have hπ : ψ.rangeRestrict.ker ≤ π.ker := by
    intro k hk
    rw [MonoidHom.ker_rangeRestrict] at hk
    show stabEquiv i (ptHom α i k) = 1
    rw [MonoidHom.mem_ker.mp (hle hk), map_one]
  let g := ψ.rangeRestrict.liftOfSurjective (MonoidHom.rangeRestrict_surjective ψ) ⟨π, hπ⟩
  have hg : ∀ k, g (ψ.rangeRestrict k) = π k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply ψ.rangeRestrict _
      (Function.rightInverse_surjInv (MonoidHom.rangeRestrict_surjective ψ)) ⟨π, hπ⟩ k
  have hgs : Function.Surjective g := by
    intro a
    obtain ⟨s, rfl⟩ := (stabEquiv i).surjective a
    obtain ⟨k, rfl⟩ := ptHom_surjective α hα (by norm_num) i s
    exact ⟨ψ.rangeRestrict k, hg k⟩
  have hg2 : IsPGroup 2 g.ker := by
    rintro ⟨t, ht⟩
    obtain ⟨k, rfl⟩ := MonoidHom.rangeRestrict_surjective ψ t
    have hk : k ∈ (ptHom α i).ker := by
      rw [MonoidHom.mem_ker, hg] at ht
      rw [MonoidHom.mem_ker]
      exact (stabEquiv i).injective (ht.trans (map_one (stabEquiv i)).symm)
    obtain ⟨a, ha⟩ := isPGroup_ker_ptHom α hker i ⟨k, hk⟩
    have hk1 : k ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    refine ⟨a, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, hk1, map_one]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (CFSG.Quasithin.J4L4.ker_eq_pCore_of_alt8 g hgs hg2).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hgs)⟩

theorem uc22s206l_ker_le {L M : Subgroup G} {α : ↥L →* alternatingGroup (Fin 9)} {i : Fin 9}
    (hKM : ptCore α i ≤ M) :
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM)).ker ≤
      CFSG.pCore 2 ↥(ptCore α i) := by
  refine le_pCore_of_normal (MonoidHom.normal_ker _) ?_
  rintro ⟨k, hk⟩
  have hkM : Subgroup.inclusion hKM k ∈ CFSG.pCore 2 ↥M := by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hk
    exact hk
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥M)) ⟨_, hkM⟩
  have ha' : Subgroup.inclusion hKM k ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  refine ⟨a, Subtype.ext (Subgroup.inclusion_injective hKM ?_)⟩
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one, map_pow, map_one]
  exact ha'

theorem uc22s206l_range_ne_bot [Finite G] {L : Subgroup G}
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} {Y : Type*} [Group Y]
    (φ : ↥(ptCore α i) →* Y) (hφ : φ.ker ≤ CFSG.pCore 2 ↥(ptCore α i)) : φ.range ≠ ⊥ := by
  haveI := isSimpleGroup_stabilizer (n := 9) (by norm_num) i
  intro hbot
  obtain ⟨s, hs⟩ := exists_ne (1 : ↥(MulAction.stabilizer (alternatingGroup (Fin 9)) i))
  obtain ⟨k, rfl⟩ := ptHom_surjective α hα (by norm_num) i s
  have hk : φ k = 1 := by
    have hmem : φ k ∈ φ.range := ⟨k, rfl⟩
    rwa [hbot, Subgroup.mem_bot] at hmem
  have hk2 := hφ (MonoidHom.mem_ker.mpr hk)
  rw [← ker_ptHom α hα hker (by norm_num) i, MonoidHom.mem_ker] at hk2
  exact hs hk2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
