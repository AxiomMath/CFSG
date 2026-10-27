module

public import CFSG.RankThree.PartTwo.Sec19.Item194Inputs
public import CFSG.RankThree.PartTwo.Sec19.Step1911EndKFact
public import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
public import CFSG.RankThree.PartTwo.Sec13.Item136E
public import CFSG.RankThree.PartTwo.Sec18.Item186a
public import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent
public import CFSG.RankThree.PartTwo.Sec21.CurtisTitsBridge
public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges
public import CFSG.LieType.Simplicity.Classical
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus projImage)

namespace Step1911EndProof

open Matrix

@[expose] noncomputable def statedProjEquivSelf {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : Subgroup (GL ι (GaloisField 2 1))) : StatedProj H ≃* H := by
  have hZ : (StatedScalars ι (GaloisField 2 1)).subgroupOf H = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨g, hg⟩ hgZ
    rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hgZ
    obtain ⟨u, hu⟩ := hgZ
    have hu1 : u = 1 := by
      have : Subsingleton (GaloisField 2 1)ˣ := by
        rw [← Finite.card_le_one_iff_subsingleton, Nat.card_units,
          GaloisField.card 2 1 one_ne_zero]
        norm_num
      exact Subsingleton.elim u 1
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [← hu, hu1, map_one]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot

theorem exists_mulEquiv_SL_of_isList194
    {X : Type} [Group X] (hX : IsList194 X) (hperf : Group.IsPerfect X) {z : X}
    (hz : z ∈ Subgroup.center X) (hz1 : z ≠ 1) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
  have hPSL : ∀ {m a : ℕ}, 3 ≤ m → 1 ≤ a → (X ≃* projSL m (GaloisField 2 a)) → False :=
    fun hm ha e => by
      have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X _ 2 _
        (Sec21.statedClassicalModel_psl_of_mulEquiv_projSL (by omega) ha (by omega) e)).2
      exact KFacts.false_of_isSimpleGroup_of_mulEquiv (MulEquiv.refl X) hperf hz hz1
  rcases hX with ⟨n, hn, he | he | he | ⟨K, _, _, -, he⟩⟩ | he | he | he | he | he |
    he | he | he | ⟨b, c, hirr, he⟩ | he <;> obtain ⟨e⟩ := he
  · exact ⟨n, hn, ⟨e⟩⟩
  · exact (hPSL le_rfl hn e).elim
  ·
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      exact (KFacts.false_of_center_eq_bot_of_mulEquiv
        ((e.trans (Sec4.projSpEquivStatedProj 2 _)).trans (statedProjEquivSelf _))
        (CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (by norm_num)) hz hz1).elim
    · have : IsSimpleGroup X :=
        CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp
          X 2 2 n (Sec21.statedClassicalModel_psp_of_mulEquiv_projSp hn2 e)
      exact (KFacts.false_of_isSimpleGroup_of_mulEquiv (MulEquiv.refl X) hperf hz hz1).elim
  · exact (KFacts.false_of_center_eq_bot_of_mulEquiv e
      CFSG.LieType.Chevalley.center_adjointGroup_eq_bot hz hz1).elim
  · have := Sec21.isSimpleGroup_projSU (m := 4) (n := 1) le_rfl le_rfl
    exact (KFacts.false_of_isSimpleGroup_of_mulEquiv e hperf hz hz1).elim
  · have := Sec21.isSimpleGroup_projSU (m := 4) (n := 3) le_rfl (by norm_num)
    exact (KFacts.false_of_isSimpleGroup_of_mulEquiv e hperf hz hz1).elim
  · exact (hPSL (by norm_num) le_rfl e).elim
  · exact (hPSL (by norm_num) (by norm_num) e).elim
  · exact (hPSL (by norm_num) le_rfl e).elim
  · exact (hPSL (by norm_num) le_rfl e).elim
  · exact (hPSL (by norm_num) le_rfl e).elim
  ·
    have : IsSimpleGroup X :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp
        X 3 2 1 ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, GaloisField 2 1, inferInstance,
          inferInstance, by rw [GaloisField.card 2 1 one_ne_zero],
          ⟨e.trans (Sec4.projSpEquivStatedProj 3 _)⟩⟩
    exact (KFacts.false_of_isSimpleGroup_of_mulEquiv (MulEquiv.refl X) hperf hz hz1).elim
  ·
    have := CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
      (n := 4) (K := GaloisField 2 1) le_rfl hirr
    exact (KFacts.false_of_isSimpleGroup_of_mulEquiv
      (e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
        (StatedOmega (StatedQuadMinus 4 (GaloisField 2 1) b c))).symm) hperf hz hz1).elim
  · have := alternatingGroup.isSimpleGroup (α := Fin 10) (by simp)
    exact (KFacts.false_of_isSimpleGroup_of_mulEquiv e hperf hz hz1).elim

theorem isSimpleGroup_projSU_three_three : IsSimpleGroup (projSU 3 3 1) :=
  CFSG.PGLModel.isSimpleGroup_projSU_of_admissible ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩

theorem isSimpleGroup_of_isSmall194 {X : Type} [Group X] (hX : IsSmall194 X) :
    IsSimpleGroup X := by
  rcases hX with h | h <;> obtain ⟨e⟩ := h
  · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · have := isSimpleGroup_projSU_three_three
    exact e.isSimpleGroup

theorem center_eq_bot_of_isSmall194 {X : Type} [Group X] (hX : IsSmall194 X)
    (hperf : Group.IsPerfect X) : Subgroup.center X = ⊥ := by
  have := isSimpleGroup_of_isSmall194 hX
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  exact KFacts.false_of_isSimpleGroup_of_mulEquiv (MulEquiv.refl X) hperf hz hz1

theorem exists_mulEquiv_SL_of_isList194_wide
    {X : Type} [Group X] (hX : IsList194 X ∨ IsSmall194 X) (hperf : Group.IsPerfect X) {z : X}
    (hz : z ∈ Subgroup.center X) (hz1 : z ≠ 1) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
  rcases hX with hX | hX
  · exact exists_mulEquiv_SL_of_isList194 hX hperf hz hz1
  · rw [center_eq_bot_of_isSmall194 hX hperf, Subgroup.mem_bot] at hz
    exact (hz1 hz).elim

theorem exists_scalar_of_mem_center {F : Type} [Field F]
    {s : Matrix.SpecialLinearGroup (Fin 3) F}
    (hs : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    ∃ r : F, r ^ 3 = 1 ∧ (s : Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) r := by
  obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hs
  exact ⟨r, by simpa using hr3, hr.symm⟩

theorem pow_three_eq_one_of_mem_center {F : Type} [Field F]
    {s : Matrix.SpecialLinearGroup (Fin 3) F}
    (hs : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    s ^ 3 = 1 := by
  obtain ⟨r, hr3, hr⟩ := exists_scalar_of_mem_center hs
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hr, ← map_pow, hr3, map_one,
    Matrix.SpecialLinearGroup.coe_one]

theorem eq_one_of_mem_center_two {s : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1)}
    (hs : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 1))) : s = 1 := by
  obtain ⟨r, hr3, hr⟩ := exists_scalar_of_mem_center hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    norm_num at hr3
  have hr1 : r = 1 := by
    have : Subsingleton (GaloisField 2 1)ˣ := by
      rw [← Finite.card_le_one_iff_subsingleton, Nat.card_units,
        GaloisField.card 2 1 one_ne_zero]
      norm_num
    have := Subsingleton.elim (Units.mk0 r hr0) 1
    simpa using congrArg Units.val this
  apply Subtype.ext
  rw [hr, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

section KStar

variable {G : Type} [Group G] {L K : Subgroup G}

@[expose] noncomputable def phiL (hLK : L ≤ K) : L →* K ⧸ CFSG.pCore 2 K :=
  (QuotientGroup.mk' (CFSG.pCore 2 K)).comp (Subgroup.inclusion hLK)

theorem phiL_apply (hLK : L ≤ K) (l : L) :
    phiL hLK l = ((⟨(l : G), hLK l.2⟩ : K) : K ⧸ CFSG.pCore 2 K) :=
  rfl

theorem mem_pCore_iff (k : K) :
    k ∈ CFSG.pCore 2 K ↔ (k : G) ∈ CFSG.Open.pCoreOf 2 K := (CFSG.mem_openPCoreOf_iff k).symm

theorem phiL_eq_one_iff (hLK : L ≤ K) (l : L) :
    phiL hLK l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 K := by
  rw [phiL_apply, QuotientGroup.eq_one_iff, mem_pCore_iff]

theorem phiL_surjective (hLK : L ≤ K) (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) :
    Function.Surjective (phiL hLK) := by
  intro q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hLN : L ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    hLK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hk : (k : G) ∈ ((L ⊔ CFSG.Open.pCoreOf 2 K : Subgroup G) : Set G) := by
    rw [← hKL]
    exact k.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hLN] at hk
  obtain ⟨l, hl, o, ho, hlo⟩ := hk
  refine ⟨⟨l, hl⟩, ?_⟩
  rw [phiL_apply, QuotientGroup.eq, mem_pCore_iff]
  have : (((⟨l, hLK hl⟩ : K)⁻¹ * k : K) : G) = o := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, ← hlo]
    group
  rw [this]
  exact ho

theorem mem_theta_of_phiL_eq_one [Finite G] (hLK : L ≤ K) {l : L} (hl : phiL hLK l = 1) :
    l ∈ aschbacherSolvableCore 3 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have h2 : IsPGroup 2 (phiL hLK).ker := by
    intro x
    have hx := (phiL_eq_one_iff hLK x).mp (MonoidHom.mem_ker.mp x.2)
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hx⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hle : (phiL hLK).ker ≤ CFSG.pCore 2 L := le_sSup ⟨inferInstance, h2⟩
  exact hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num) (hle hl)

theorem phiL_eq_one_of_mem_theta [Finite G] {M : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hLK : L ≤ K) (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (hZ3 : ∀ z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K), z ^ 3 = 1) {l : L}
    (hl : l ∈ aschbacherSolvableCore 3 L) : phiL hLK l = 1 := by
  have hθ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have hq := Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK
  set Z := (aschbacherSolvableCore 3 L).map (phiL hLK) with hZ
  have hθn : (aschbacherSolvableCore 3 L).Normal := by
    have := hθ.2.1
    infer_instance
  have hZn : Z.Normal := hθn.map _ (phiL_surjective hLK hKL)
  have : Group.IsSolvable (aschbacherSolvableCore 3 L) := hθ.1
  have hZs : Group.IsSolvable Z :=
    Group.isSolvable_of_surjective ((phiL hLK).subgroupMap_surjective _)
  have hZc : Z ≤ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hZn with ht | hc
    · exfalso
      have hsolv : Group.IsSolvable (K ⧸ CFSG.pCore 2 K) := by
        rw [ht] at hZs
        exact Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv : (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) ≃*
            (K ⧸ CFSG.pCore 2 K)) : (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) →*
              (K ⧸ CFSG.pCore 2 K))) Subgroup.topEquiv.surjective
      have : Nontrivial (K ⧸ CFSG.pCore 2 K) := CFSG.LocalCores.isQuasisimple_nontrivial hq
      have : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := hq.1
      exact Group.IsPerfect.not_isSolvable (K ⧸ CFSG.pCore 2 K) hsolv
    · exact hc
  have h3 := hZ3 _ (hZc (Subgroup.mem_map_of_mem _ hl))
  have hdvd3 : orderOf (phiL hLK l) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hdvdθ : orderOf (phiL hLK l) ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (orderOf_map_dvd _ l).trans (by
      have := Subgroup.orderOf_dvd_natCard (aschbacherSolvableCore 3 L) hl
      exact this)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h1 ▸ hdvdθ) hθ.2.2.1

theorem phiL_eq_one_iff_mem_theta [Finite G] {M : Subgroup G} (hK : K ∈ oTwoComponentsIn M)
    (hLK : L ≤ K) (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (hZ3 : ∀ z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K), z ^ 3 = 1) (l : L) :
    phiL hLK l = 1 ↔ l ∈ aschbacherSolvableCore 3 L :=
  ⟨mem_theta_of_phiL_eq_one hLK, phiL_eq_one_of_mem_theta hK hLK hKL hZ3⟩

theorem phiL_conj_mem_starIm (hLK : L ≤ K) {H : Subgroup G} {g : G} (hgH : g ∈ H)
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (hgL : g ∈ Subgroup.normalizer (L : Set G))
    {l : L} (hl : phiL hLK l ∈ starIm K H) :
    phiL hLK ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgL l).mp l.2⟩ ∈ starIm K H := by
  obtain ⟨k, hkH, hk⟩ := hl
  rw [QuotientGroup.mk'_apply, phiL_apply, QuotientGroup.eq, mem_pCore_iff] at hk
  have hgk : g * (k : G) * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgK k).mp k.2
  refine ⟨⟨g * (k : G) * g⁻¹, hgk⟩, Subgroup.mem_subgroupOf.mpr
    (H.mul_mem (H.mul_mem hgH (Subgroup.mem_subgroupOf.mp hkH)) (H.inv_mem hgH)), ?_⟩
  rw [QuotientGroup.mk'_apply, phiL_apply, QuotientGroup.eq, mem_pCore_iff]
  have hgO : g ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hgK
  have h1 := (Subgroup.mem_normalizer_iff.mp hgO _).mp hk
  convert h1 using 1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem phiL_mem_center (hLK : L ≤ K) (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K) {c : G}
    (hcL : c ∈ L) (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) :
    phiL hLK ⟨c, hcL⟩ ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨l, rfl⟩ := phiL_surjective hLK hKL q
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLc l.2))

theorem phiL_ne_one [Finite G] (hLK : L ≤ K) {c : G} (hcL : c ∈ L) (hc : orderOf c = 3) :
    phiL hLK ⟨c, hcL⟩ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h1
  have hO := (phiL_eq_one_iff hLK _).mp h1
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨c, hO⟩
  have hck : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd := orderOf_dvd_of_pow_eq_one hck
  rw [hc] at hdvd
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hdvd)
  omega

end KStar

theorem false_of_pair {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F] [CharP F 2]
    (Ψ : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F) {P : Subgroup Q} (hpar : IsProperParabolic P)
    {g₁ g₂ : GL (Fin 3) F}
    (h₁ : ∀ p ∈ P, ∃ p' ∈ P, Matrix.SpecialLinearGroup.toGL (Ψ p') =
      g₁ * Matrix.SpecialLinearGroup.toGL (Ψ p) * g₁⁻¹)
    (h₂ : ∀ p ∈ P, ∃ p' ∈ P, Matrix.SpecialLinearGroup.toGL (Ψ p') =
      g₂ * Matrix.SpecialLinearGroup.toGL (Ψ p) * g₂⁻¹)
    {r : F} (hr1 : r ≠ 1) (hr3 : r ^ 3 = 1)
    (hcomm : ((g₁ * g₂ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      r • ((g₂ * g₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPtop, T, hT⟩ := hpar
  set P' := P.map Ψ.toMonoidHom with hP'def
  have hP' : P' ≠ ⊤ := by
    intro h
    apply hPtop
    rw [eq_top_iff]
    intro p _
    have hp : Ψ.toMonoidHom p ∈ P' := h ▸ Subgroup.mem_top _
    obtain ⟨p', hp', hpp'⟩ := hp
    rwa [Ψ.injective hpp'] at hp'
  have hΨs : Function.Surjective Ψ.toMonoidHom := Ψ.surjective
  set T' := T.mapSurjective hΨs with hT'def
  have hT' : Subgroup.normalizer (T' : Set (Matrix.SpecialLinearGroup (Fin 3) F)) ≤ P' := by
    change Subgroup.normalizer (((T' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))) :
      Set (Matrix.SpecialLinearGroup (Fin 3) F)) ≤ P'
    rw [hT'def, Sylow.coe_mapSurjective, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hT
  have hn : ∀ {g : GL (Fin 3) F}, (∀ p ∈ P, ∃ p' ∈ P, Matrix.SpecialLinearGroup.toGL (Ψ p') =
      g * Matrix.SpecialLinearGroup.toGL (Ψ p) * g⁻¹) → ∀ s ∈ P', glConj g s ∈ P' := by
    intro g hg s hs
    obtain ⟨p, hp, rfl⟩ := hs
    obtain ⟨p', hp', hpp'⟩ := hg p hp
    refine ⟨p', hp', Matrix.SpecialLinearGroup.toGL_injective ?_⟩
    rw [toGL_glConj]
    exact hpp'
  exact false_of_normalizes_parabolic hP' hT' (hn h₁) (hn h₂) hr1 hr3 hcomm

theorem false_of_inner_pair {Q : Type} [Group Q] [Finite Q] {F : Type} [Field F] [Finite F]
    [CharP F 2] (Ψ : Q ≃* Matrix.SpecialLinearGroup (Fin 3) F) {P : Subgroup Q}
    (hpar : IsProperParabolic P) {x y : Q} (hx : ∀ p ∈ P, x⁻¹ * p * x ∈ P)
    (hy : ∀ p ∈ P, y⁻¹ * p * y ∈ P) (hxy : x * y ≠ y * x)
    (hζ : (x * y)⁻¹ * (y * x) ∈ Subgroup.center Q) : False := by
  set ζ := (x * y)⁻¹ * (y * x) with hζdef
  have hζ1 : ζ⁻¹ ≠ 1 := by
    intro h
    apply hxy
    have h' : ζ = 1 := inv_eq_one.mp h
    rw [hζdef] at h'
    calc x * y = x * y * ((x * y)⁻¹ * (y * x)) := by rw [h', mul_one]
      _ = y * x := by group
  have hζc : Ψ ζ⁻¹ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [Subgroup.mem_center_iff] at hζ ⊢
    intro s
    obtain ⟨q, rfl⟩ := Ψ.surjective s
    rw [← map_mul, ← map_mul]
    congr 1
    have := hζ q
    calc q * ζ⁻¹ = ζ⁻¹ * (ζ * q) * ζ⁻¹ := by group
      _ = ζ⁻¹ * (q * ζ) * ζ⁻¹ := by rw [this]
      _ = ζ⁻¹ * q := by group
  obtain ⟨r, hr3, hr⟩ := exists_scalar_of_mem_center hζc
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hζ1
    apply Ψ.injective
    rw [map_one]
    exact Subtype.ext (by rw [hr, map_one, Matrix.SpecialLinearGroup.coe_one])
  have hrel : x⁻¹ * y⁻¹ = ζ⁻¹ * (y⁻¹ * x⁻¹) := by
    rw [hζdef]
    group
  refine false_of_pair Ψ hpar (g₁ := Matrix.SpecialLinearGroup.toGL (Ψ x⁻¹))
    (g₂ := Matrix.SpecialLinearGroup.toGL (Ψ y⁻¹)) (fun p hp => ⟨_, hx p hp, ?_⟩)
    (fun p hp => ⟨_, hy p hp, ?_⟩) hr1 hr3 ?_
  · simp only [map_mul, map_inv, inv_inv]
  · simp only [map_mul, map_inv, inv_inv]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hrel, map_mul, map_mul]
    change (Ψ ζ⁻¹ : Matrix (Fin 3) (Fin 3) F) * ((Ψ (y⁻¹ * x⁻¹) : Matrix (Fin 3) (Fin 3) F)) =
      r • ((Ψ (y⁻¹ * x⁻¹) : Matrix (Fin 3) (Fin 3) F))
    rw [hr, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]

section Bar

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

@[expose] noncomputable def mkX (hD : Sec13Data G A c L) : L →* lBarA c L A :=
  ((QuotientGroup.mk' (aschbacherSolvableCore 3
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))).comp
    (Subgroup.inclusion (le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt))).codRestrict
    (lBarA c L A) fun m => Subgroup.mem_map_of_mem _
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left m.2))

theorem coe_mkX (hD : Sec13Data G A c L) (m : L) :
    ((mkX hD m : lBarA c L A) : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) =
      QuotientGroup.mk' _ ⟨(m : G), le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt m.2⟩ :=
  rfl

theorem mkX_mem (hD : Sec13Data G A c L) (m : L) :
    mkX hD m ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) :=
  Subgroup.mem_subgroupOf.mpr ⟨_, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩

theorem exists_mkX_eq (hD : Sec13Data G A c L) {w : lBarA c L A}
    (hw : w ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A)) : ∃ m : L, mkX hD m = w := by
  obtain ⟨n, hn, hnw⟩ := Subgroup.mem_subgroupOf.mp hw
  exact ⟨⟨n, Subgroup.mem_subgroupOf.mp hn⟩, Subtype.ext hnw⟩

theorem mkX_eq_one_iff (hD : Sec13Data G A c L) (m : L) :
    mkX hD m = 1 ↔ m ∈ aschbacherSolvableCore 3 L := by
  constructor
  · intro h
    obtain ⟨t, ht, htm⟩ := mem_theta_of_mk_eq_one hD.mem_thetaComponentsAt m.2
      (congrArg Subtype.val h)
    have : t = m := Subtype.ext htm
    rwa [← this]
  · intro h
    obtain ⟨η, hη⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
    apply Subtype.ext
    rw [coe_mkX, ← hη m]
    have : ((m : L ⧸ aschbacherSolvableCore 3 L)) = 1 := (QuotientGroup.eq_one_iff _).mpr h
    rw [this, map_one]
    rfl

theorem mkX_conj (hD : Sec13Data G A c L) {a : G} (ha : a ∈ A) (m : L) :
    mkX hD ⟨a * m * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha) m).mp m.2⟩ =
      aBarHom hD ⟨a, ha⟩ * mkX hD m * (aBarHom hD ⟨a, ha⟩)⁻¹ := by
  apply Subtype.ext
  simp only [coe_mkX, Subgroup.coe_mul, Subgroup.coe_inv, aBarHom_apply, ← map_mul, ← map_inv]
  rfl

theorem mkX_eq_iff {K : Subgroup G} (hD : Sec13Data G A c L) (hLK : L ≤ K)
    (hθ : ∀ m : L, phiL hLK m = 1 ↔ m ∈ aschbacherSolvableCore 3 L) (m₁ m₂ : L) :
    mkX hD m₁ = mkX hD m₂ ↔ phiL hLK m₁ = phiL hLK m₂ := by
  have h1 : ∀ {Y : Type} [Group Y] (f : L →* Y), f m₁ = f m₂ ↔ f (m₁⁻¹ * m₂) = 1 := by
    intro Y _ f
    rw [map_mul, map_inv, inv_mul_eq_one]
  rw [h1, h1, mkX_eq_one_iff, hθ]

theorem exists_pair_of_isHeisCentral (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ (a b : A) (w w' : lBarA c L A), w ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) ∧
      w' ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A) ∧
      (∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A),
        aBarHom hD a * w * v = v * (aBarHom hD a * w)) ∧
      (∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A),
        aBarHom hD b * w' * v = v * (aBarHom hD b * w')) ∧
      w * w' ≠ w' * w ∧
      ∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A),
        (w * w')⁻¹ * (w' * w) * v = v * ((w * w')⁻¹ * (w' * w)) := by
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  obtain ⟨U, hU, hUΛ, -, -⟩ := isHeisCentral_facts hD hH
  have hΛn : Λ.Normal := lBar_normal hD
  have hdec : ∀ x : lBarA c L A, ∃ a : A, ∃ w ∈ Λ, x = aBarHom hD a * w := by
    intro x
    have hAN : (aBarHom hD).range ≤ Subgroup.normalizer (Λ : Set (lBarA c L A)) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hΛn]
      exact le_top
    have hx : x ∈ ((Λ ⊔ (aBarHom hD).range : Subgroup _) : Set (lBarA c L A)) := by
      rw [lBar_sup_range_aBarHom hD]
      exact Subgroup.mem_top x
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hAN] at hx
    obtain ⟨w₀, hw₀, _, ⟨a, rfl⟩, rfl⟩ := hx
    refine ⟨a, (aBarHom hD a)⁻¹ * w₀ * aBarHom hD a, ?_, by group⟩
    have := hΛn.conj_mem w₀ hw₀ (aBarHom hD a)⁻¹
    rwa [inv_inv] at this
  have hUnc : ∃ u ∈ U, ∃ u' ∈ U, u * u' ≠ u' * u := by
    by_contra hall
    push Not at hall
    have htop : Subgroup.center U = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hall y y.2 x x.2)
    have h3 := hU.1.2.2.2
    rw [htop, Subgroup.card_top, hU.2.1] at h3
    norm_num at h3
  obtain ⟨u, hu, u', hu', huu'⟩ := hUnc
  obtain ⟨a, w, hw, rfl⟩ := hdec u
  obtain ⟨b, w', hw', rfl⟩ := hdec u'
  have hc1 : ∀ v ∈ Λ, aBarHom hD a * w * v = v * (aBarHom hD a * w) := fun v hv =>
    hUΛ _ hu v hv
  have hc2 : ∀ v ∈ Λ, aBarHom hD b * w' * v = v * (aBarHom hD b * w') := fun v hv =>
    hUΛ _ hu' v hv
  have hab : aBarHom hD a * aBarHom hD b = aBarHom hD b * aBarHom hD a := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commute a.2 b.2)
  have e1 : aBarHom hD a * w * (aBarHom hD b * w') =
      aBarHom hD a * aBarHom hD b * (w' * w) := by
    have := hc2 w hw
    calc aBarHom hD a * w * (aBarHom hD b * w') =
        aBarHom hD a * (w * (aBarHom hD b * w')) := by group
      _ = aBarHom hD a * (aBarHom hD b * w' * w) := by rw [this]
      _ = aBarHom hD a * aBarHom hD b * (w' * w) := by group
  have e2 : aBarHom hD b * w' * (aBarHom hD a * w) =
      aBarHom hD a * aBarHom hD b * (w * w') := by
    have := hc1 w' hw'
    calc aBarHom hD b * w' * (aBarHom hD a * w) =
        aBarHom hD b * (w' * (aBarHom hD a * w)) := by group
      _ = aBarHom hD b * (aBarHom hD a * w * w') := by rw [this]
      _ = aBarHom hD b * aBarHom hD a * (w * w') := by group
      _ = aBarHom hD a * aBarHom hD b * (w * w') := by rw [hab]
  refine ⟨a, b, w, w', hw, hw', hc1, hc2, fun h => huu' ?_, fun v hv => ?_⟩
  · rw [e1, e2, h]
  · have hz : (w * w')⁻¹ * (w' * w) = (aBarHom hD b * w' * (aBarHom hD a * w))⁻¹ *
        (aBarHom hD a * w * (aBarHom hD b * w')) := by
      rw [e1, e2]
      group
    rw [hz]
    exact hUΛ _ (U.mul_mem (U.inv_mem (U.mul_mem hu' hu)) (U.mul_mem hu hu')) v hv

theorem phiL_conj_eq {K : Subgroup G} (hD : Sec13Data G A c L) (hLK : L ≤ K)
    (hθ : ∀ m : L, phiL hLK m = 1 ↔ m ∈ aschbacherSolvableCore 3 L) {a : G} (ha : a ∈ A)
    {l : L} (hc : ∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A),
      aBarHom hD ⟨a, ha⟩ * mkX hD l * v = v * (aBarHom hD ⟨a, ha⟩ * mkX hD l)) (m : L) :
    phiL hLK ⟨a * m * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha) m).mp m.2⟩ =
      (phiL hLK l)⁻¹ * phiL hLK m * phiL hLK l := by
  have h1 := hc _ (mkX_mem hD (l⁻¹ * m * l))
  have h2 : mkX hD ⟨a * m * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha) m).mp
      m.2⟩ = mkX hD (l⁻¹ * m * l) := by
    rw [mkX_conj hD ha]
    rw [map_mul, map_mul, map_inv] at h1 ⊢
    set B := aBarHom hD ⟨a, ha⟩
    set W := mkX hD l
    set V := mkX hD m
    calc B * V * B⁻¹ = B * W * (W⁻¹ * V * W) * (B * W)⁻¹ := by group
      _ = W⁻¹ * V * W * (B * W) * (B * W)⁻¹ := by rw [h1]
      _ = W⁻¹ * V * W := by group
  rw [(mkX_eq_iff hD hLK hθ _ _).mp h2, map_mul, map_mul, map_inv]

theorem false_of_isHeisCentral {K H : Subgroup G} (hD : Sec13Data G A c L)
    (hH : Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L)) (hLK : L ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (hθ : ∀ m : L, phiL hLK m = 1 ↔ m ∈ aschbacherSolvableCore 3 L)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (Ψ : K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hpar : IsProperParabolic (starIm K H))
    (hAP : ∀ (a : G) (ha : a ∈ A) (m : L), phiL hLK m ∈ starIm K H →
      phiL hLK ⟨a * m * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha) m).mp m.2⟩ ∈
        starIm K H) : False := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, w, w', hw, hw', hc1, hc2, hne, hz⟩ :=
    exists_pair_of_isHeisCentral hD hH
  obtain ⟨l, rfl⟩ := exists_mkX_eq hD hw
  obtain ⟨l', rfl⟩ := exists_mkX_eq hD hw'
  have hφs := phiL_surjective hLK hKL
  have hconj : ∀ (g : G) (hg : g ∈ A) (l₀ : L),
      (∀ v ∈ (Sec12.lBar c L).subgroupOf (lBarA c L A),
        aBarHom hD ⟨g, hg⟩ * mkX hD l₀ * v = v * (aBarHom hD ⟨g, hg⟩ * mkX hD l₀)) →
      ∀ p ∈ starIm K H, (phiL hLK l₀)⁻¹ * p * phiL hLK l₀ ∈ starIm K H := by
    intro g hg l₀ hc p hp
    obtain ⟨m, rfl⟩ := hφs p
    rw [← phiL_conj_eq hD hLK hθ hg hc m]
    exact hAP g hg m hp
  refine false_of_inner_pair Ψ hpar (x := phiL hLK l) (y := phiL hLK l')
    (fun p hp => by simpa using hconj a ha l hc1 p hp)
    (fun p hp => by simpa using hconj b hb l' hc2 p hp) ?_ ?_
  · intro h
    apply hne
    rw [← map_mul, ← map_mul] at h ⊢
    exact (mkX_eq_iff hD hLK hθ _ _).mpr h
  · rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨m, rfl⟩ := hφs q
    have h1 := hz _ (mkX_mem hD m)
    simp only [← map_mul, ← map_inv] at h1 ⊢
    exact ((mkX_eq_iff hD hLK hθ _ _).mp h1).symm

theorem card_slPi_eq {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : Sec4.PiField π p f K)
    (hq : Sec4.ModThree π (p ^ f)) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card (Sec4.slPi π 3 (p ^ f) K) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :
    π = true ∧ Nat.card K = 2 ^ n := by
  have := hK.finite
  have hp := hK.prime
  have hf := hK.one_le
  cases π
  · exfalso
    rw [Nat.card_congr (Sec4.slPiFalseEquiv p f K).toEquiv,
      KFacts.card_unitarySU_three hK.unitary] at hcard
    have hp3 : p ≠ 3 := by
      rintro rfl
      have h3 : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
      change 3 ^ f % 3 = 2 at hq
      omega
    rcases Nat.lt_or_ge n 3 with hn3 | hn3
    · obtain rfl : n = 2 := by omega
      obtain ⟨x, hx⟩ : ∃ x, x = p ^ f := ⟨_, rfl⟩
      rw [← hx] at hcard
      have hx2 : 2 ≤ x := hx ▸ le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      rcases Nat.lt_or_ge x 5 with hx5 | hx5
      · interval_cases x <;> norm_num at hcard
      · have h4 := KFacts.su3Order_lt (x := 4) (y := x) (by norm_num) (by omega)
        norm_num at h4 hcard
        omega
    · exact KFacts.su3Order_ne_sl3Order hp hp3 hf rfl
        (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn3)) hcard
  · refine ⟨rfl, ?_⟩
    let _ := Fintype.ofFinite K
    rw [Nat.card_congr (Sec4.slPiTrueEquiv (p ^ f) K).toEquiv, KFacts.card_SL_three,
      Fintype.card_eq_nat_card] at hcard
    by_contra hne
    have hK1 : 1 ≤ Nat.card K := Nat.card_pos
    have h2n : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := KFacts.sl3Order_lt hK1 h
      omega
    · have := KFacts.sl3Order_lt h2n h
      omega

theorem false_of_isSLThreePiTwo {K H : Subgroup G} (hD : Sec13Data G A c L)
    (hSL : Sec4.IsSLThreePiTwo (lBarA c L A)) (hLK : L ≤ K)
    (hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K)
    (hθ : ∀ m : L, phiL hLK m = 1 ↔ m ∈ aschbacherSolvableCore 3 L) {n : ℕ} (hn : 2 ≤ n)
    (ψ : K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n))
    (hpar : IsProperParabolic (starIm K H))
    (hAP : ∀ (a : G) (ha : a ∈ A) (m : L), phiL hLK m ∈ starIm K H →
      phiL hLK ⟨a * m * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha) m).mp m.2⟩ ∈
        starIm K H) : False := by
  obtain ⟨π, p, f, F, _, ⟨D⟩⟩ := exists_sLTwoData hSL
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L A) with hΛ
  have hΛn : Λ.Normal := lBar_normal hD
  have hΛp : Group.IsPerfect Λ := isPerfect_subgroupOf_lBar hD
  have hΛ1 : Λ ≠ ⊥ := subgroupOf_lBar_ne_bot hD
  have hq2 : 2 < p ^ f := by
    by_contra hq2
    have hp := D.piField.prime
    have hf := D.piField.one_le
    have h2 : p ^ f = 2 := by
      have : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
      omega
    have := D.isSolvable_of_two h2
    have : Group.IsSolvable Λ := Group.isSolvable_of_isSolvable_injective Λ.subtype_injective
    have : Nontrivial Λ := (Subgroup.nontrivial_iff_ne_bot Λ).mpr hΛ1
    exact Group.IsPerfect.not_isSolvable Λ inferInstance
  have hL₀ : D.L₀ = Λ := le_antisymm (D.le_of_normal hq2 hΛn hΛp hΛ1) (D.le_of_isPerfect hΛp)
  have hmem : ∀ m : L, mkX hD m ∈ D.L₀ := fun m => hL₀ ▸ mkX_mem hD m
  obtain ⟨χ, hχ⟩ : ∃ χ : L →* Sec4.slPi π 3 (p ^ f) F,
      ∀ m : L, χ m = D.e ⟨mkX hD m, hmem m⟩ :=
    ⟨D.e.toMonoidHom.comp ((mkX hD).codRestrict D.L₀ hmem), fun m => rfl⟩
  have hχs : Function.Surjective χ := by
    intro s
    obtain ⟨w, rfl⟩ := D.e.surjective s
    obtain ⟨m, hm⟩ := exists_mkX_eq hD (show (w : lBarA c L A) ∈ Λ from hL₀ ▸ w.2)
    refine ⟨m, ?_⟩
    rw [hχ]
    congr 1
    exact Subtype.ext hm
  have hker : (phiL hLK).ker = χ.ker := by
    ext m
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hθ, ← mkX_eq_one_iff hD, hχ,
      MulEquiv.map_eq_one_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  obtain ⟨Ψ₀, hΨ₀⟩ : ∃ Ψ₀ : K ⧸ CFSG.pCore 2 K ≃* Sec4.slPi π 3 (p ^ f) F,
      ∀ m : L, Ψ₀ (phiL hLK m) = χ m := by
    refine ⟨(QuotientGroup.quotientKerEquivOfSurjective _ (phiL_surjective hLK hKL)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective χ hχs)), fun m => ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective _ (phiL_surjective hLK hKL)).symm
        (phiL hLK m) = (m : L ⧸ (phiL hLK).ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, h1, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
    rfl
  have hcard : Nat.card (Sec4.slPi π 3 (p ^ f) F) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1) := by
    rw [← Nat.card_congr Ψ₀.toEquiv, Nat.card_congr ψ.toEquiv]
    let _ := Fintype.ofFinite (GaloisField 2 n)
    rw [KFacts.card_SL_three, Fintype.card_eq_nat_card, GaloisField.card 2 n (by omega)]
  obtain ⟨rfl, hFcard⟩ := card_slPi_eq D.piField D.modThree hn hcard
  have : Finite F := D.piField.finite
  let _ := Fintype.ofFinite F
  have hchar : CharP F 2 := by
    obtain ⟨k, hkp, hk⟩ := FiniteField.card F (ringChar F)
    rw [Fintype.card_eq_nat_card, hFcard] at hk
    have h2 : 2 ∣ ringChar F ^ (k : ℕ) := hk ▸ dvd_pow_self 2 (by omega)
    exact ringChar.of_eq ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hkp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : K ⧸ CFSG.pCore 2 K ≃* Matrix.SpecialLinearGroup (Fin 3) F,
      ∀ m : L, Matrix.SpecialLinearGroup.toGL (Ψ (phiL hLK m)) = (χ m : GL (Fin 3) F) :=
    ⟨Ψ₀.trans (Sec4.slPiTrueEquiv (p ^ f) F), fun m => by
      rw [MulEquiv.trans_apply, Sec4.toGL_slPiTrueEquiv, hΨ₀]⟩
  have hAN : (aBarHom hD).range ≤ Subgroup.normalizer (D.L₀ : Set (lBarA c L A)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr D.normal]
    exact le_top
  have hdec : ∀ x : lBarA c L A, ∃ a : A, ∃ w ∈ D.L₀, x = w * aBarHom hD a := by
    intro x
    have hx : x ∈ ((D.L₀ ⊔ (aBarHom hD).range : Subgroup _) : Set (lBarA c L A)) := by
      rw [hL₀, lBar_sup_range_aBarHom hD]
      exact Subgroup.mem_top x
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hAN] at hx
    obtain ⟨w, hw, _, ⟨a, rfl⟩, rfl⟩ := hx
    exact ⟨a, w, hw, rfl⟩
  have huC : ∀ h ∈ D.L₀, h * D.u = D.u * h := Subgroup.mem_centralizer_iff.mp D.mem_centralizer
  obtain ⟨⟨a₁, ha₁⟩, w₁, hw₁, hux⟩ := hdec D.u
  obtain ⟨⟨a₂, ha₂⟩, w₂, hw₂, hax⟩ := hdec D.a
  obtain ⟨l₁, hl₁def⟩ : ∃ l₁, l₁ = w₁⁻¹ := ⟨_, rfl⟩
  have hl₁ : l₁ ∈ D.L₀ := hl₁def ▸ D.L₀.inv_mem hw₁
  have hA₁ : aBarHom hD ⟨a₁, ha₁⟩ = D.u * l₁ := by
    have : aBarHom hD ⟨a₁, ha₁⟩ = w₁⁻¹ * D.u := by rw [hux]; group
    rw [this, ← hl₁def, huC _ hl₁]
  obtain ⟨l₂, hl₂def⟩ : ∃ l₂, l₂ = D.a⁻¹ * w₂⁻¹ * D.a := ⟨_, rfl⟩
  have hl₂ : l₂ ∈ D.L₀ := by
    have := D.normal.conj_mem _ (D.L₀.inv_mem hw₂) D.a⁻¹
    rw [hl₂def]
    simpa using this
  have hA₂ : aBarHom hD ⟨a₂, ha₂⟩ = D.a * l₂ := by
    have : aBarHom hD ⟨a₂, ha₂⟩ = w₂⁻¹ * D.a := by rw [hax]; group
    rw [this, hl₂def]
    group
  obtain ⟨z, hzdef⟩ : ∃ z, z = D.u * D.a * D.u⁻¹ * D.a⁻¹ := ⟨_, rfl⟩
  have hzL : z ∈ D.L₀ := hzdef ▸ D.comm_mem.1
  have hzC : ∀ h ∈ D.L₀, h * z = z * h :=
    Subgroup.mem_centralizer_iff.mp (by rw [hzdef]; exact D.comm_mem.2)
  have hzc : Sec4.slPiTrueEquiv (p ^ f) F (D.e ⟨z, hzL⟩) ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨t, rfl⟩ := (D.e.trans (Sec4.slPiTrueEquiv (p ^ f) F)).surjective s
    rw [MulEquiv.trans_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (hzC t t.2)
  obtain ⟨s₀, hs₀3, hs₀⟩ := exists_scalar_of_mem_center hzc
  have hζ : (((D.e ⟨z, hzL⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = scalar (Fin 3) s₀ := by
    rw [← Sec4.toGL_slPiTrueEquiv (D.e ⟨z, hzL⟩)]
    exact hs₀
  have hs₀1 : s₀ ≠ 1 := by
    rintro rfl
    apply D.comm_ne
    have h1 : D.e ⟨z, hzL⟩ = 1 :=
      Subtype.ext (Units.ext (by rw [hζ, map_one]; rfl))
    rw [← hzdef]
    exact congrArg Subtype.val ((MulEquiv.map_eq_one_iff D.e).mp h1)
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    norm_num at hs₀3
  have hζc : ∀ g : GL (Fin 3) F,
      ((D.e ⟨z, hzL⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F) * g =
        g * ((D.e ⟨z, hzL⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F) := by
    intro g
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hζ]
    exact Matrix.scalar_commute s₀ (fun r' => Commute.all _ _) (g : Matrix (Fin 3) (Fin 3) F)
  have hza : D.a * z * D.a⁻¹ = z := by
    have h1 := D.act ⟨z, hzL⟩
    rw [mul_assoc D.y, hζc D.y⁻¹, mul_inv_cancel_left] at h1
    exact congrArg Subtype.val (D.e.injective (Subtype.ext h1))
  obtain ⟨m₀, hm₀def⟩ : ∃ m₀, m₀ = D.a⁻¹ * l₁ * D.a := ⟨_, rfl⟩
  have hm₀ : m₀ ∈ D.L₀ := by
    have := D.normal.conj_mem _ hl₁ D.a⁻¹
    rw [hm₀def]
    simpa using this
  have hA12 : aBarHom hD ⟨a₁, ha₁⟩ * aBarHom hD ⟨a₂, ha₂⟩ =
      aBarHom hD ⟨a₂, ha₂⟩ * aBarHom hD ⟨a₁, ha₁⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hD.commute ha₁ ha₂)
  rw [hA₁, hA₂] at hA12
  have hX : z * m₀ * l₂ = l₂ * l₁ := by
    have hza' : D.a * z = z * D.a := by
      calc D.a * z = D.a * z * D.a⁻¹ * D.a := by group
        _ = z * D.a := by rw [hza]
    have hzu : z * D.u = D.u * z := huC z hzL
    have hul₂ : l₂ * D.u = D.u * l₂ := huC _ hl₂
    have key : D.a * D.u * (z * m₀ * l₂) = D.a * D.u * (l₂ * l₁) := by
      calc D.a * D.u * (z * m₀ * l₂) = D.a * (D.u * z) * m₀ * l₂ := by group
        _ = D.a * (z * D.u) * m₀ * l₂ := by rw [hzu]
        _ = (D.a * z) * D.u * m₀ * l₂ := by group
        _ = (z * D.a) * D.u * m₀ * l₂ := by rw [hza']
        _ = D.u * l₁ * (D.a * l₂) := by rw [hzdef, hm₀def]; group
        _ = D.a * l₂ * (D.u * l₁) := hA12
        _ = D.a * (l₂ * D.u) * l₁ := by group
        _ = D.a * (D.u * l₂) * l₁ := by rw [hul₂]
        _ = D.a * D.u * (l₂ * l₁) := by group
    exact mul_left_cancel key
  have hXL : (⟨z, hzL⟩ : D.L₀) * ⟨m₀, hm₀⟩ * ⟨l₂, hl₂⟩ = ⟨l₂, hl₂⟩ * ⟨l₁, hl₁⟩ :=
    Subtype.ext hX
  have hXG := congrArg (fun t : D.L₀ =>
    ((D.e t : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F)) hXL
  simp only [map_mul, Subgroup.coe_mul] at hXG
  have hm₀act : ((D.e ⟨l₁, hl₁⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F) =
      D.y * ((D.e ⟨m₀, hm₀⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F) * D.y⁻¹ := by
    have h1 := D.act ⟨m₀, hm₀⟩
    have heq : (⟨D.a * m₀ * D.a⁻¹, D.normal.conj_mem m₀ hm₀ D.a⟩ : D.L₀) = ⟨l₁, hl₁⟩ :=
      Subtype.ext (show D.a * m₀ * D.a⁻¹ = l₁ by rw [hm₀def]; group)
    rw [heq] at h1
    exact h1
  set E₁ : GL (Fin 3) F := ((D.e ⟨l₁, hl₁⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F)
    with hE₁
  set E₂ : GL (Fin 3) F := ((D.e ⟨l₂, hl₂⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F)
    with hE₂
  set Z₀ : GL (Fin 3) F := ((D.e ⟨z, hzL⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F)
    with hZ₀
  have hEm : ((D.e ⟨m₀, hm₀⟩ : Sec4.slPi true 3 (p ^ f) F) : GL (Fin 3) F) =
      D.y⁻¹ * E₁ * D.y := by
    rw [hm₀act]
    group
  rw [hEm] at hXG
  have hrel : D.y * E₂ * E₁ = Z₀ * (E₁ * (D.y * E₂)) := by
    calc D.y * E₂ * E₁ = D.y * (E₂ * E₁) := by group
      _ = D.y * (Z₀ * (D.y⁻¹ * E₁ * D.y) * E₂) := by rw [← hXG]
      _ = (D.y * Z₀) * D.y⁻¹ * E₁ * (D.y * E₂) := by group
      _ = (Z₀ * D.y) * D.y⁻¹ * E₁ * (D.y * E₂) := by rw [hζc D.y]
      _ = Z₀ * (E₁ * (D.y * E₂)) := by group
  have hcomm : ((E₁ * (D.y * E₂) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      s₀⁻¹ • ((D.y * E₂ * E₁ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [hrel, Units.val_mul Z₀, hζ, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
      smul_smul, inv_mul_cancel₀ hs₀0, one_smul]
  have hn₁ : ∀ q ∈ starIm K H, ∃ q' ∈ starIm K H, Matrix.SpecialLinearGroup.toGL (Ψ q') =
      E₁ * Matrix.SpecialLinearGroup.toGL (Ψ q) * E₁⁻¹ := by
    intro q hq
    obtain ⟨m, rfl⟩ := phiL_surjective hLK hKL q
    refine ⟨_, hAP a₁ ha₁ m hq, ?_⟩
    rw [hΨ, hΨ, hχ, hχ]
    have hw' : l₁ * mkX hD m * l₁⁻¹ ∈ D.L₀ :=
      D.L₀.mul_mem (D.L₀.mul_mem hl₁ (hmem m)) (D.L₀.inv_mem hl₁)
    have hw : (⟨mkX hD ⟨a₁ * m * a₁⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha₁)
        m).mp m.2⟩, hmem _⟩ : D.L₀) = ⟨l₁, hl₁⟩ * ⟨mkX hD m, hmem m⟩ * ⟨l₁, hl₁⟩⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mkX_conj hD ha₁, hA₁]
      calc D.u * l₁ * mkX hD m * (D.u * l₁)⁻¹ = D.u * (l₁ * mkX hD m * l₁⁻¹) * D.u⁻¹ := by
            group
        _ = l₁ * mkX hD m * l₁⁻¹ := by rw [← huC _ hw', mul_inv_cancel_right]
    rw [hw, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hE₁]
  have hn₂ : ∀ q ∈ starIm K H, ∃ q' ∈ starIm K H, Matrix.SpecialLinearGroup.toGL (Ψ q') =
      (D.y * E₂) * Matrix.SpecialLinearGroup.toGL (Ψ q) * (D.y * E₂)⁻¹ := by
    intro q hq
    obtain ⟨m, rfl⟩ := phiL_surjective hLK hKL q
    refine ⟨_, hAP a₂ ha₂ m hq, ?_⟩
    rw [hΨ, hΨ, hχ, hχ]
    have hw' : l₂ * mkX hD m * l₂⁻¹ ∈ D.L₀ :=
      D.L₀.mul_mem (D.L₀.mul_mem hl₂ (hmem m)) (D.L₀.inv_mem hl₂)
    have hw : (⟨mkX hD ⟨a₂ * m * a₂⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha₂)
        m).mp m.2⟩, hmem _⟩ : D.L₀) =
        ⟨D.a * (l₂ * mkX hD m * l₂⁻¹) * D.a⁻¹, D.normal.conj_mem _ hw' D.a⟩ := by
      apply Subtype.ext
      change mkX hD ⟨a₂ * m * a₂⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha₂)
        m).mp m.2⟩ = D.a * (l₂ * mkX hD m * l₂⁻¹) * D.a⁻¹
      rw [mkX_conj hD ha₂, hA₂]
      group
    rw [hw, D.act ⟨l₂ * mkX hD m * l₂⁻¹, hw'⟩]
    have h3 : (⟨l₂ * mkX hD m * l₂⁻¹, hw'⟩ : D.L₀) =
        ⟨l₂, hl₂⟩ * ⟨mkX hD m, hmem m⟩ * ⟨l₂, hl₂⟩⁻¹ := rfl
    rw [h3, map_mul, map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hE₂]
    group
  exact false_of_pair Ψ hpar hn₁ hn₂ (r := s₀⁻¹) (inv_ne_one.mpr hs₀1)
    (by rw [inv_pow, hs₀3, inv_one]) hcomm

end Bar

end Step1911EndProof

open Step1911EndProof

end CFSG.RankThree.PartTwo.Sec19
