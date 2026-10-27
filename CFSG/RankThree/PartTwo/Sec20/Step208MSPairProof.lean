module

public import CFSG.RankThree.PartTwo.Sec20.Item208OneProof
public import CFSG.RankThree.PartOne.S8.Statements
import CFSG.RankThree.PartTwo.Sec20.Step2054Proof
import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.RankThree.PartTwo.Sec18.Rem187
import CFSG.Adapters.RankTwoModelTransports
import CFSG.RankThree.PartOne.S12.ModelTransport
import CFSG.Open.PGLModelStated
public import CFSG.RankThree.PartTwo.Sec20.Alt20

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.Assembly.LowTwoRank (StatedSL StatedProj StatedScalars)
open scoped Pointwise

@[expose] def KFactL3OddThreeRank : Prop :=
  ∀ n : ℕ, Odd n → ∀ (X : Type) [Group X] [Finite X],
    Nonempty (X ≃* projSL 3 (GaloisField 2 n)) → CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1

theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem eq_one_of_pow_three_eq_one {n : ℕ} (hn : Odd n) {x : GaloisField 2 n}
    (hx : x ^ 3 = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    norm_num at hx
  let u : (GaloisField 2 n)ˣ := Units.mk0 x hx0
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [u, hx])
  have hdvd3 : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu3
  have hcard : Nat.card (GaloisField 2 n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n hn.pos.ne']
  have : Fintype (GaloisField 2 n)ˣ := Fintype.ofFinite _
  have hdvdc : orderOf u ∣ 2 ^ n - 1 := by
    rw [← hcard, Nat.card_eq_fintype_card]
    exact orderOf_dvd_card
  have hmod := two_pow_mod_three_of_odd hn
  have h1 : orderOf u = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
    · exact h
    · exfalso
      rw [h] at hdvdc
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
  have hu1 : u = 1 := orderOf_eq_one_iff.mp h1
  have := congrArg Units.val hu1
  simpa [u] using this

theorem statedScalars_subgroupOf_statedSL_eq_bot {n : ℕ} (hn : Odd n) :
    (StatedScalars (Fin 3) (GaloisField 2 n)).subgroupOf (StatedSL 3 (GaloisField 2 n)) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨g, hg⟩ hgs
  rw [Subgroup.mem_subgroupOf] at hgs
  obtain ⟨u, rfl⟩ := hgs
  rw [CFSG.RankThree.PartOne.statedSL_eq_det_ker, MonoidHom.mem_ker] at hg
  have hdet : ((Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.scalar (Fin 3) u) :
      (GaloisField 2 n)ˣ) : GaloisField 2 n) = 1 := by
    rw [hg]
    rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have hu : (u : GaloisField 2 n) = 1 := eq_one_of_pow_three_eq_one hn hdet
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change Matrix.GeneralLinearGroup.scalar (Fin 3) u = 1
  rw [show u = 1 from Units.ext hu, map_one]

noncomputable def statedProjEquivStatedSL {n : ℕ} (hn : Odd n) :
    StatedProj (StatedSL 3 (GaloisField 2 n)) ≃* ↥(StatedSL 3 (GaloisField 2 n)) :=
  (QuotientGroup.quotientMulEquivOfEq (statedScalars_subgroupOf_statedSL_eq_bot hn)).trans
    QuotientGroup.quotientBot

noncomputable def projSLEquivStatedSL {n : ℕ} (hn : Odd n) :
    ↥(projSL 3 (GaloisField 2 n)) ≃* ↥(StatedSL 3 (GaloisField 2 n)) :=
  ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartOne.projImage_statedSL_eq_projSL 3 _))).symm.trans
    (statedProjEquivStatedSL hn)

noncomputable def projSLEquivStatedProj (n : ℕ) :
    ↥(projSL 3 (GaloisField 2 n)) ≃* StatedProj (StatedSL 3 (GaloisField 2 n)) :=
  CFSG.PGLModel.projSLEquivStatedProj 3 (GaloisField 2 n)

theorem center_statedSL_eq_bot {n : ℕ} (hn : Odd n) :
    Subgroup.center ↥(StatedSL 3 (GaloisField 2 n)) = ⊥ := by
  set e := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (GaloisField 2 n)
  rw [← Subgroup.map_center_eq e, eq_bot_iff]
  rintro _ ⟨A, hA, rfl⟩
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := eq_one_of_pow_three_eq_one hn hr
  have hA1 : A = 1 := by
    apply Subtype.ext
    rw [← hrA, hr1, map_one]
    rfl
  rw [hA1, map_one]
  exact Subgroup.one_mem _

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_top_of_sup_pCore_eq_top {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    {P : Subgroup K} [P.Normal] (hP : P ⊔ CFSG.pCore 2 K = ⊤) : P = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (CFSG.pCore 2 K).map (QuotientGroup.mk' P) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective P y
    have hx : x ∈ P ⊔ CFSG.pCore 2 K := hP ▸ Subgroup.mem_top x
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨b, hb, ?_⟩
    rw [map_mul, show QuotientGroup.mk' P a = 1 from (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
  have h2 : IsPGroup 2 (K ⧸ P) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := K)).map (QuotientGroup.mk' P)
    rw [hmap] at this
    exact this.of_equiv Subgroup.topEquiv
  have : Group.IsSolvable (K ⧸ P) := by
    have := h2.isNilpotent
    infer_instance
  have : Group.IsPerfect (K ⧸ P) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  have := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
    (G := K ⧸ P)
  exact QuotientGroup.subsingleton_iff.mp this

omit [Finite G] in
theorem isSolvable_of_map_le_center {K : Type} [Group K] [Finite K] {P : Subgroup K}
    (hP : P.map (QuotientGroup.mk' (CFSG.pCore 2 K)) ≤
      Subgroup.center (K ⧸ CFSG.pCore 2 K)) : Group.IsSolvable P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : P →* K ⧸ CFSG.pCore 2 K := (QuotientGroup.mk' (CFSG.pCore 2 K)).comp P.subtype
  have hrange : φ.range ≤ Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hP
  have hcomm : ∀ a b : φ.range, a * b = b * a := fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.mp (hrange a.2) b).symm)
  have : Group.IsSolvable φ.range := Group.isSolvable_of_comm hcomm
  have hker : IsPGroup 2 φ.ker := by
    intro x
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := K)
      ⟨((x : P) : K), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp x.2)⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  have : Group.IsSolvable φ.ker := by
    have := hker.isNilpotent
    infer_instance
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ.rangeRestrict
    (by rw [MonoidHom.ker_rangeRestrict, Subgroup.range_subtype])

theorem mem_cComp_of_quasisimple {K X : Subgroup G} (hKX : K ≤ X)
    (hXK : X ≤ Subgroup.normalizer (K : Set G)) (hK1 : K ≠ ⊥) (hKp : ⁅K, K⁆ = K)
    (hq : CFSG.IsQuasisimple (K ⧸ CFSG.pCore 2 K)) : K ∈ CFSG.Quasithin.cComp X := by
  refine ⟨hK1, hKp, CFSG.Quasithin.A3.subnormal_of_normal hKX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXK), ?_⟩
  intro K' hK'K hK'1 hK'p hK'sub
  have hsubK := CFSG.Quasithin.A3.subnormal_of_le_of_le hK'sub hK'K.le hKX
  obtain ⟨P, hPK, hPn, hK'P⟩ := CFSG.Quasithin.A3.subnormal_exists_normal_of_lt hsubK hK'K
  have : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hKp
  set P' : Subgroup K := P.subgroupOf K with hP'
  have hPle : P ≤ K := hPK.le
  have hQn : (P'.map (QuotientGroup.mk' (CFSG.pCore 2 K))).Normal :=
    hPn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hQn with htop | hcen
  ·
    have hsup : P' ⊔ CFSG.pCore 2 K = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (CFSG.pCore 2 K)) P'
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have : P'.Normal := hPn
    have hP'top := eq_top_of_sup_pCore_eq_top hsup
    apply hPK.ne
    apply le_antisymm hPle
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ P' := hP'top ▸ Subgroup.mem_top _
    exact this
  ·
    have hPs : Group.IsSolvable P' := isSolvable_of_map_le_center hcen
    have : Group.IsSolvable P :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe hPle).symm.toMonoidHom) (MulEquiv.injective _)
    have : Group.IsSolvable K' :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK'P)
        (Subgroup.inclusion_injective hK'P)
    have : Group.IsPerfect K' := Subgroup.isPerfect_iff.mpr hK'p
    have := CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
      (G := K')
    exact hK'1 (Subgroup.eq_bot_of_subsingleton K')

theorem charTwo_of_pCoreOf_le (hchar : CFSG.Assembly.IsCharTwoType G) {M X : Subgroup G}
    (hM : CFSG.Assembly.IsTwoLocal M) (hXM : X ≤ M) (hOX : CFSG.Open.pCoreOf 2 M ≤ X) :
    CFSG.QuasithinUnique.CharTwo X := by
  have hF := generalizedFitting_eq_of_pCoreOf_le hchar hM hXM hOX
  rintro x ⟨hxX, hxC⟩
  exact mem_pCoreOf_of_forall_commute hF hxX fun y hy =>
    (Subgroup.mem_centralizer_iff.mp hxC y hy).symm

theorem isKGroupCat_of_ne_top (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G) {X : Subgroup G} (hX : X ≠ ⊤) :
    CFSG.SectionRank.IsKGroupCat X :=
  ((KCore.KProperNonab.kGroupNonab CFSG.Assembly.inCatalog_isoInvariant hK X hX).mono_of_finite
    hbridge).kGroupAllSimple CFSG.SectionRank.catalog_isoInvariant
    CFSG.SectionRank.catalog_containsAbelianSimple

omit [Finite G] in
theorem relIndex_sup_eq_of_le_normalizer {H N : Subgroup G}
    (h : H ≤ Subgroup.normalizer (N : Set G)) : N.relIndex (H ⊔ N) = N.relIndex H := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient H N h).toEquiv.symm

theorem mem_of_pow_three_eq_one {K T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hT : IsPGroup 2 T) {x : G} (hx : x ∈ K ⊔ T) (hx3 : x ^ 3 = 1) : x ∈ K := by
  have hXK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hZK : Subgroup.zpowers x ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.zpowers_le.mpr hx).trans hXK
  have h1 : K.relIndex (Subgroup.zpowers x ⊔ K) ∣ 3 := by
    rw [relIndex_sup_eq_of_le_normalizer hZK]
    exact (Subgroup.relIndex_dvd_card _ _).trans
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx3)
  have h2 : K.relIndex (Subgroup.zpowers x ⊔ K) ∣ K.relIndex (K ⊔ T) := by
    have hle : Subgroup.zpowers x ⊔ K ≤ K ⊔ T := sup_le (Subgroup.zpowers_le.mpr hx) le_sup_left
    exact Dvd.intro _ (Subgroup.relIndex_mul_relIndex K _ _ le_sup_right hle)
  have h3 : K.relIndex (K ⊔ T) ∣ Nat.card T := by
    rw [sup_comm, relIndex_sup_eq_of_le_normalizer hTK]
    exact Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  rw [hk] at h3
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h4 : K.relIndex (Subgroup.zpowers x ⊔ K) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) (h2.trans h3)
  rw [Subgroup.relIndex_eq_one] at h4
  exact h4 (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

theorem pRank_three_le {K T : Subgroup G} (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hT : IsPGroup 2 T) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥(K ⊔ T)) ≤
      CFSG.Open.pRank 3 (⊤ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : CFSG.Open.IsElemAbelian 3 (⊥ : Subgroup ↥(K ⊔ T)) :=
    ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩
  refine csSup_le ⟨0, ⊥, bot_le, hbot, by rw [Subgroup.card_bot, pow_zero]⟩ ?_
  rintro k ⟨E, -, hEab, hEc⟩
  refine le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
    ?_
  set E₁ : Subgroup G := E.map (K ⊔ T).subtype with hE₁
  have hE₁3 : ∀ x ∈ E₁, x ^ 3 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have := hEab.2 y hy
    simpa using congrArg Subtype.val this
  have hE₁K : E₁ ≤ K := fun x hx =>
    mem_of_pow_three_eq_one hTK hT (by obtain ⟨y, -, rfl⟩ := hx; exact y.2) (hE₁3 x hx)
  set E₃ : Subgroup ↥K := E₁.subgroupOf K with hE₃
  set φ := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hinj : Function.Injective (φ.comp E₃.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have hy1 : ((y : ↥K) : G) ^ 3 = 1 := hE₁3 _ (Subgroup.mem_subgroupOf.mp y.2)
    obtain ⟨j, hj⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥K)
      ⟨(y : ↥K), (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)⟩
    have hj' : ((y : ↥K) : G) ^ (2 ^ j) = 1 := by
      have := congrArg (fun z => ((z : ↥K) : G)) (congrArg Subtype.val hj)
      simpa using this
    have h1 : ((y : ↥K) : G) = 1 := Sec18.eq_one_of_pow_three_of_pow_two_pow hy1 hj'
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  refine ⟨E₃.map φ, le_top, ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_⟩
  · obtain ⟨_, ⟨u, hu, rfl⟩⟩ := a
    obtain ⟨_, ⟨v, hv, rfl⟩⟩ := b
    apply Subtype.ext
    change φ u * φ v = φ v * φ u
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hu' : (u : G) ∈ E₁ := Subgroup.mem_subgroupOf.mp hu
    have hv' : (v : G) ∈ E₁ := Subgroup.mem_subgroupOf.mp hv
    obtain ⟨u', hu'', hu'e⟩ := hu'
    obtain ⟨v', hv'', hv'e⟩ := hv'
    change (u : G) * v = v * u
    rw [← hu'e, ← hv'e]
    exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨u', hu''⟩ ⟨v', hv''⟩ |> congrArg Subtype.val)
  · rintro _ ⟨u, hu, rfl⟩
    rw [← map_pow]
    have : u ^ 3 = 1 := Subtype.ext (by simpa using hE₁3 _ (Subgroup.mem_subgroupOf.mp hu))
    rw [this, map_one]
  · have h1 : Nat.card (E₃.map φ) = Nat.card E₃ := by
      have : E₃.map φ = (φ.comp E₃.subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [this]
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
    rw [h1, hE₃, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₁K).toEquiv, hE₁,
      Subgroup.card_map_of_injective (K ⊔ T).subtype_injective, hEc]

theorem stronglyQuasithin_of (hG : TheoremFourHyp G) {M X : Subgroup G}
    (hM : CFSG.Assembly.IsTwoLocal M) (hXM : X ≤ M)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    CFSG.Open.SQTKTauCeti.StronglyQuasithin X := by
  intro p hp hp2
  change CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2
  by_cases hp3 : p = 3
  · subst hp3
    exact h3
  · have hp4 : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by decide)
    have hp5 : 3 < p := by
      have := hp.two_le
      omega
    calc CFSG.Open.pRank p (⊤ : Subgroup X) ≤ CFSG.Open.pRank p ((⊤ : Subgroup X).map X.subtype) :=
          Sec18.pRank_subgroupOf_le p hp ⊤
      _ = CFSG.Open.pRank p X := by rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ ≤ CFSG.Open.pRank p M :=
          CFSG.RankThreeEvenClassification.Helpers.pRank_mono p hp hXM
      _ ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
          Sec18.pRank_le_localRank_of_isTwoLocal hp hM
      _ ≤ 2 := by
          have := hG.localRank_lt p hp hp5
          omega

theorem step208MSPair_core (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hrank : KFactL3OddThreeRank) (h321 : Sec3.Item321Split)
    {A M L N : Subgroup G} {c : G} {T : Subgroup G} (hT : Ctx20 G A M L N c T)
    (hKC : kTwenty M c ∈ oTwoComponentsIn M) (hKN : ¬ kTwenty M c ≤ N)
    (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M}) (hTN : T ≤ N)
    (h2 : ∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
      ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G))
    (h3 : KIsL3 M c)
    (hx : ∃ x : G, x ∉ M ∧ x ∈ Subgroup.normalizer (sTwenty M N c T : Set G)) :
    CFSG.Quasithin.IsMSPair (kTwenty M c ⊔ T) (sTwenty M N c T) ∧
      kTwenty M c ∈ CFSG.Quasithin.cComp (kTwenty M c ⊔ T) ∧
      ((kTwenty M c ⊔ T : Subgroup G) : Set G) =
        (kTwenty M c : Set G) * (sTwenty M N c T : Set G) ∧
      ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥(kTwenty M c) →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        Fintype.card F = 2 ^ n ∧ CFSG.Quasithin.IsModO2Surj (kTwenty M c) α := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup G := hT.isSimpleGroup
  set K := kTwenty M c with hKdef
  set S := sTwenty M N c T with hSdef
  obtain ⟨n, hn, ⟨e⟩⟩ := h3
  have hM := hT.mem_scriptM.1
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hTM : T ≤ M := hT.sylow.le
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hTM.trans hMK
  have hXK : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hXM : K ⊔ T ≤ M := sup_le hKM hTM
  have hT2 : IsPGroup 2 T := hT.sylow.isPGroup
  obtain ⟨P, hP, hP2, hMP⟩ := hM.1
  have hM2 : CFSG.Assembly.IsTwoLocal M := ⟨P, hP, hP2, hMP⟩
  have hMtop : M ≠ ⊤ := by
    rw [hMP]
    exact normalizer_ne_top_of_isPGroup_two hT.nonabelian hP2 hP
  have hK1 := Sec18.ne_bot_of_mem_oTwoComponentsIn hKC
  have hKp := Sec18.commutator_eq_of_mem_oTwoComponentsIn hKC
  have hq := Sec18.isQuasisimple_of_mem_oTwoComponentsIn hKC
  have hcomp : K ∈ CFSG.Quasithin.cComp (K ⊔ T) :=
    mem_cComp_of_quasisimple le_sup_left hXK hK1 hKp hq
  have hTX : CFSG.ABGLocalTools.IsSylowOf 2 T (K ⊔ T) := hT.sylow.of_le le_sup_right hXM
  have hSX : S ≤ K ⊔ T := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hSM : S ≤ M := hSX.trans hXM
  have hQS : CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ S := by
    have hQT : CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ T := pCoreOf_le_of_isSylowOf hTX
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) (hQT.trans hTN))
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hKS : K ⊔ S = K ⊔ T := by
    refine le_antisymm (sup_le le_sup_left hSX) ?_
    rw [← sup_pCoreOf_eq_core h321 hT hKC h2 ⟨n, hn, ⟨e⟩⟩]
    exact sup_le le_sup_left (hQS.trans le_sup_right)
  have hmul : ((K ⊔ T : Subgroup G) : Set G) = (K : Set G) * (S : Set G) := by
    rw [← hKS]
    exact Subgroup.coe_mul_of_right_le_normalizer_left K S (hSM.trans hMK)
  set eSL : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥(StatedSL 3 (GaloisField 2 n)) :=
    e.trans (projSLEquivStatedSL hn) with heSL
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := by
    have h := Subgroup.map_center_eq eSL
    rw [center_statedSL_eq_bot hn] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ eSL.injective).mp h
  have hcardF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn.pos.ne'
  have hLie : CFSG.Quasithin.IsRankTwoLie2Derived
      ((↥K ⧸ CFSG.pCore 2 ↥K) ⧸ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) := by
    refine Or.inl ⟨n, ⟨Nat.prime_two, hn.pos, by norm_num, by simp, by simp⟩, GaloisField 2 n,
      inferInstance, inferInstance, hcardF, ⟨?_⟩⟩
    exact (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans (e.trans (projSLEquivStatedProj n)))
  have hSQT : CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥(K ⊔ T) := by
    refine stronglyQuasithin_of hT.toTheoremFourHyp hM2 hXM ?_
    have h1 := pRank_three_le hTK hT2
    have h2' := hrank n hn (↥K ⧸ CFSG.pCore 2 ↥K) ⟨e⟩
    omega
  have hKgroup : CFSG.SectionRank.IsKGroupCat ↥(K ⊔ T) :=
    isKGroupCat_of_ne_top hbridge hT.kProper fun h => hMtop (top_le_iff.mp (h ▸ hXM))
  have hchar2 : CFSG.QuasithinUnique.CharTwo (K ⊔ T) :=
    charTwo_of_pCoreOf_le hT.charTwoType hM2 hXM
      ((pCoreOf_le_of_isSylowOf hT.sylow).trans le_sup_right)
  have hlt : (K ⊔ T) ⊓ N < K ⊔ T := by
    refine lt_of_le_of_ne inf_le_left fun h => hKN ?_
    exact le_sup_left.trans (h ▸ inf_le_right)
  have hodd : ¬ 2 ∣ ((K ⊔ T) ⊓ N).relIndex (K ⊔ T) :=
    not_dvd_relIndex_of_isSylowOf_le hTX (le_inf le_sup_right hTN) inf_le_left
  set α : ↥K →* ↥(StatedSL 3 (GaloisField 2 n)) :=
    eSL.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hα
  have hαs : Function.Surjective α := eSL.surjective.comp (QuotientGroup.mk'_surjective _)
  have hαk : α.ker = CFSG.pCore 2 ↥K := by
    ext x
    rw [MonoidHom.mem_ker, hα, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ eSL.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  refine ⟨⟨⟨⟨hSQT, hKgroup⟩, hchar2, K, hcomp, hmul, hLie⟩,
    Or.inl ⟨(K ⊔ T) ⊓ N, hlt, hodd, rfl⟩, ?_⟩,
    hcomp, hmul, n, GaloisField 2 n, inferInstance, inferInstance, α, ?_, hαs, hαk⟩
  ·
    intro C hCS hC1 hCchar hCN
    obtain ⟨x, hxM, hxS⟩ := hx
    have hxC : x ∈ Subgroup.normalizer (C : Set G) := by
      have : (C.subgroupOf S).Characteristic := hCchar
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (C.subgroupOf S) hxS
      rwa [Subgroup.map_subgroupOf_eq_of_le hCS] at h
    obtain ⟨M', hM', hNM'⟩ := exists_mem_scriptM_of_isTwoLocal
      (X := ((K ⊔ T : Subgroup G) : Set G))
      ⟨C, hC1, (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hCS, rfl⟩ hCN
    rw [h204] at hM'
    rw [Set.mem_singleton_iff.mp hM'] at hNM'
    exact hxM (hNM' hxC)
  · rw [Fintype.card_eq_nat_card, hcardF]

theorem step208MSPair_of (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hrank : KFactL3OddThreeRank) (h189 : Sec18.Item189) (h204 : Item204One)
    (h321 : Sec3.Item321Split) (hx : Step208X) : Step208MSPair := by
  intro G _ _ A M L N c T hT hTN h2 h3
  obtain ⟨hKC, hKN, -⟩ := item189_case_one h189 hT h3
  obtain ⟨x, -, hxM, -, hxS⟩ := hx G A M L N c T hT hTN
  exact step208MSPair_core hbridge hrank h321 hT.toCtx20 hKC hKN (h204 G A M L N c T hT) hTN h2
    h3 ⟨x, hxM, hxS⟩

end CFSG.RankThree.PartTwo.Sec20
