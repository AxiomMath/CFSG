module

public import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofE
public import CFSG.RankThree.PartTwo.Sec16.Item166Proof
public import CFSG.RankThree.PartTwo.Sec13.Item138N
import CFSG.RankThree.PartTwo.Sec16.Item165StepsProofClaim164
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec15.NoModNine
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

@[expose] def KS165U : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (n : ℕ), 2 ^ n % 3 = 2 → 2 ^ n % 9 ≠ 8 →
    CFSG.IsQuasisimple Q → ¬ 3 ∣ Nat.card (Subgroup.center Q) →
    Nonempty (Q ⧸ Subgroup.center Q ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 n) →
    ∀ B : Subgroup Q, CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 →
    ∀ T : Subgroup (MulAut Q), IsPGroup 2 T →
      (∀ b ∈ B, ∀ t ∈ T, MulAut.conj b * t * (MulAut.conj b)⁻¹ ∈ T) → T = ⊥

namespace Steps165

variable {G : Type} [Group G] [Finite G]

theorem cover_prod_of_std {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h1514 : Item1514S17) (hMeets : Claim1715Meets)
    (hA7 : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) :
    Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) := by
  rcases h1514 G A c L Y₀ h Y₀ h.mem_y0Star (hMeets G A c L Y₀ h) with
      ⟨hY, -, -, hprod, -⟩ | ⟨⟨ψ⟩, -⟩ | ⟨-, -, -, -, hnot, -⟩
  · refine ⟨?_, hprod⟩
    rwa [inf_of_le_right h.le_y0] at hY
  · exact (hA7.false ψ).elim
  · exact absurd h.le_y0 (hnot Y₀ h.mem_y0Star)

theorem isEmpty_alt7_of_projSU {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (hq : 2 ^ n % 3 = 2)
    (φ : X ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 n) :
    IsEmpty (X ≃* alternatingGroup (Fin 7)) := by
  refine ⟨fun ψ => ?_⟩
  have hK := piField_galoisField_two 2 n hn
  apply card_projImage_slPi_ne_alt7 hK hq
  rw [← projSU_eq, Nat.card_congr (φ.symm.trans ψ).toEquiv, nat_card_alternatingGroup,
    Nat.card_fin]
  decide

theorem isEmpty_alt7_of_projSL {X : Type} [Group X] {n : ℕ} (hn : 1 ≤ n) (hq : 2 ^ n % 3 = 1)
    (φ : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n)) :
    IsEmpty (X ≃* alternatingGroup (Fin 7)) := by
  refine ⟨fun ψ => ?_⟩
  have hK := piField_galoisField 2 n hn
  apply card_projImage_slPi_ne_alt7 hK hq
  rw [← projSL_eq, Nat.card_congr (φ.symm.trans ψ).toEquiv, nat_card_alternatingGroup,
    Nat.card_fin]
  decide

theorem quotCenter_facts {L Y₀ : Subgroup G} (hLY : L ≤ Y₀)
    (hY : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀)
    (hQ : CFSG.IsQuasisimple (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))
    (hL : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    Nonempty ((↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ⧸ Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ≃*
        ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∧
      ¬ 3 ∣ Nat.card (Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀)) := by
  set Q := ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ with hQdef
  have : Group.IsPerfect Q := hQ.1
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  set f : ↥L →* Q := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hLY)
    with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y₀) q
    have hy' : y ∈ ((L : Set G) * (CFSG.Open.pCoreOf 2 Y₀ : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L _
        (hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)), ← hY]
      exact hy
    obtain ⟨l, hl, t, ht, hlt⟩ := hy'
    refine ⟨⟨l, hl⟩, ?_⟩
    rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    rw [CFSG.Open.pCoreOf] at ht
    obtain ⟨t', ht', ht't⟩ := ht
    have : (Subgroup.inclusion hLY ⟨l, hl⟩)⁻¹ * ⟨y, hy⟩ = t' := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [← hlt, ← ht't]
      simp
    rw [this]
    exact ht'
  set g : ↥L →* Q ⧸ Subgroup.center Q := (QuotientGroup.mk' (Subgroup.center Q)).comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective _).comp hfs
  set θ := aschbacherSolvableCore 3 ↥L with hθdef
  have hθsol : Group.IsSolvable θ :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hθker : θ ≤ g.ker := by
    have hnorm : (θ.map g).Normal := Subgroup.Normal.map inferInstance g hgs
    have hsolT : Group.IsSolvable (θ.map g) :=
      Group.isSolvable_of_surjective (g.subgroupMap_surjective θ)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (θ.map g) with h0 | h1
    · exact (Subgroup.map_eq_bot_iff _).mp h0
    · exfalso
      have : Group.IsSolvable (Q ⧸ Subgroup.center Q) := by
        rw [h1] at hsolT
        exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom)
          (MulEquiv.surjective _)
      exact Group.IsPerfect.not_isSolvable (Q ⧸ Subgroup.center Q) this
  set gbar := QuotientGroup.lift θ g hθker with hgbar
  have hgbs : Function.Surjective gbar := by
    intro x
    obtain ⟨l, rfl⟩ := hgs x
    exact ⟨(l : ↥L ⧸ θ), rfl⟩
  have hgbi : Function.Injective gbar := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal gbar.ker with h0 | h1
    · exact h0
    · exfalso
      obtain ⟨x, y, hxy⟩ := hQ.2.2
      apply hxy
      obtain ⟨x', rfl⟩ := hgbs x
      obtain ⟨y', rfl⟩ := hgbs y
      have hx' : gbar x' = 1 := by rw [← MonoidHom.mem_ker, h1]; exact Subgroup.mem_top _
      have hy' : gbar y' = 1 := by rw [← MonoidHom.mem_ker, h1]; exact Subgroup.mem_top _
      rw [hx', hy']
  refine ⟨⟨(MulEquiv.ofBijective gbar ⟨hgbi, hgbs⟩).symm⟩, fun h3 => hθ3 ?_⟩
  have hker : g.ker ≤ θ := by
    intro l hl
    have h1 : gbar (l : ↥L ⧸ θ) = 1 := hl
    have h2 : (l : ↥L ⧸ θ) = 1 := hgbi (h1.trans (map_one gbar).symm)
    exact (QuotientGroup.eq_one_iff l).mp h2
  have hZ : Subgroup.center Q ≤ θ.map f := by
    intro z hz
    obtain ⟨l, rfl⟩ := hfs z
    refine ⟨l, hker ?_, rfl⟩
    rw [MonoidHom.mem_ker, hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hz
  exact h3.trans ((Subgroup.card_dvd_of_le hZ).trans (Subgroup.card_map_dvd θ f))

omit [Finite G] in
theorem actQuotPCore_of_mem {Y : Subgroup G} {a : G} (ha : a ∈ Y)
    (haN : a ∈ Subgroup.normalizer (Y : Set G)) :
    actQuotPCore Y ⟨a, haN⟩ = MulAut.conj (((⟨a, ha⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    change Crit167.quotPCoreAut ↥Y (Y.normalizerMonoidHom ⟨a, haN⟩) (y : ↥Y ⧸ CFSG.pCore 2 ↥Y) =
      ((⟨a, ha⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y) * (y : ↥Y ⧸ CFSG.pCore 2 ↥Y) *
        (((⟨a, ha⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y))⁻¹
    rw [Crit167.quotPCoreAut_apply_mk, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1

theorem isSimpleGroup_thetaQuot_of_projSU {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) {n : ℕ} (hn : 1 ≤ n) (hq : 2 ^ n % 3 = 2)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 n) :
    IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hL
  by_cases hq2 : 2 < 2 ^ n
  · have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
      center_eq_bot_of_mulEquiv φ (isPerfect_center_projSU 2 n hn hq hq2).2
    have : IsSimpleGroup ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := hQ.2.1
    have e : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃*
          ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact e.symm.isSimpleGroup
  · exfalso
    have hn1 : n = 1 := by
      have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) _
      have h2 : 2 ^ n = 2 := by omega
      exact Nat.pow_right_injective le_rfl (show 2 ^ n = 2 ^ 1 by rw [h2, pow_one])
    subst hn1
    have : Group.IsSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      have := isSolvable_projSU_two
      exact Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    obtain ⟨hperf, -, a, b, hab⟩ := hQ
    have : Nontrivial ((↥L ⧸ aschbacherSolvableCore 3 ↥L) ⧸
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := ⟨⟨a * b, b * a, hab⟩⟩
    have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      (QuotientGroup.mk_surjective (s := Subgroup.center _)).nontrivial
    have := hperf
    exact Group.IsPerfect.not_isSolvable (↥L ⧸ aschbacherSolvableCore 3 ↥L) inferInstance

theorem exists_image_inf {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    ∃ B : Subgroup (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀), CFSG.Assembly.IsElemAbelian 3 B ∧
      Nat.card B = 9 ∧ ∀ b ∈ B, ∃ (a : G) (ha : a ∈ Y₀), a ∈ A ∧
        b = (((⟨a, ha⟩ : ↥Y₀)) : ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hALY : A ⊓ L ≤ Y₀ := inf_le_right.trans h.le_y0
  set fA : ↥(A ⊓ L) →* ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hALY) with hfA
  have hinj : Function.Injective fA := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hfA, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx3 : (x : G) ^ 3 = 1 := h.isElemAbelian.2 x x.2.1
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y₀) ⟨_, hx⟩
    have hk' : (x : G) ^ 2 ^ k = 1 := by
      have := congrArg (fun z : ↥(CFSG.pCore 2 ↥Y₀) => ((z : ↥Y₀) : G)) hk
      simpa using this
    have h1 : orderOf (x : G) ∣ Nat.gcd 3 (2 ^ k) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one hk')
    have hg : Nat.gcd 3 (2 ^ k) = 1 :=
      Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h1
    rw [Subgroup.mem_bot]
    exact Subtype.ext h1
  refine ⟨fA.range, ⟨⟨⟨fun x y => ?_⟩⟩, fun b hb => ?_⟩, ?_, fun b hb => ?_⟩
  · obtain ⟨_, u, rfl⟩ := x
    obtain ⟨_, v, rfl⟩ := y
    apply Subtype.ext
    change fA u * fA v = fA v * fA u
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h.commute u.2.1 v.2.1)
  · obtain ⟨u, rfl⟩ := hb
    rw [← map_pow]
    have : u ^ 3 = 1 := Subtype.ext (by simpa using h.isElemAbelian.2 u u.2.1)
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, h9]
  · obtain ⟨u, rfl⟩ := hb
    exact ⟨u, hALY u.2, u.2.1, rfl⟩

end Steps165

theorem centU165_of (h1514 : Item1514S17) (hMeets : Claim1715Meets) (h138 : Item138N)
    (hK : KS165U) : CentU165 := by
  intro G _ _ A c L Y₀ h hU S hS
  obtain ⟨n, hn, hq, ⟨φ⟩⟩ := hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hY, hprod⟩ := Steps165.cover_prod_of_std h h1514 hMeets
    (Steps165.isEmpty_alt7_of_projSU hn hq φ)
  have hmod := not_modNine_of_inner h.toSec15R h138 KFacts.kSL3PiOrder3TypeC hn
    (Or.inr ⟨hq, ⟨φ⟩⟩) hprod
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 :=
    card_inf_eq_nine h.toSec13Data (isPerfect_lBar h.toSec13Data) hprod.some
  have hQq : CFSG.IsQuasisimple (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) := h.mem_y0Star.prop.1.2.2.2
  obtain ⟨⟨e⟩, hZ3⟩ := Steps165.quotCenter_facts h.le_y0 hY hQq
    (Steps165.isSimpleGroup_thetaQuot_of_projSU h.mem_lA.1 hn hq φ)
  obtain ⟨B, hBe, hB9, hBA⟩ := Steps165.exists_image_inf h h9
  have hSM : S ≤ Subgroup.normalizer (Y₀ : Set G) := h.qStar_le S hS
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
  set T := (S.subgroupOf (Subgroup.normalizer (Y₀ : Set G))).map (actQuotPCore Y₀) with hT
  have hT2 : IsPGroup 2 T := hS2.comap_subtype.map _
  have hTn : ∀ b ∈ B, ∀ t ∈ T, MulAut.conj b * t * (MulAut.conj b)⁻¹ ∈ T := by
    intro b hb t ht
    obtain ⟨a, ha, haA, rfl⟩ := hBA b hb
    obtain ⟨⟨s, hsN⟩, hsS, rfl⟩ := ht
    have haN : a ∈ Subgroup.normalizer (Y₀ : Set G) := Subgroup.le_normalizer ha
    have has : a * s * a⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp (hAS haA) s).mp hsS
    refine ⟨⟨a, haN⟩ * ⟨s, hsN⟩ * ⟨a, haN⟩⁻¹, Subgroup.mem_subgroupOf.mpr has, ?_⟩
    rw [map_mul, map_mul, map_inv, Steps165.actQuotPCore_of_mem ha haN]
  have hT1 := hK _ n hq (fun h8 => hmod (Or.inr h8)) hQq hZ3 ⟨e.trans φ⟩ B hBe hB9 T hT2 hTn
  rw [Subgroup.commutator_le]
  intro y hy s hs
  have hs1 : actQuotPCore Y₀ ⟨s, hSM hs⟩ = 1 := by
    have hmem : actQuotPCore Y₀ ⟨s, hSM hs⟩ ∈ T :=
      ⟨⟨s, hSM hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
    rw [hT1] at hmem
    exact hmem
  have hsc := (mem_sectionCentralizer_of_actQuotPCore_eq_one (hSM hs) hs1).2 y hy
  have e' : ⁅y, s⁆ = (s * y * s⁻¹ * y⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e']
  exact Subgroup.inv_mem _ hsc

end CFSG.RankThree.PartTwo.Sec16
