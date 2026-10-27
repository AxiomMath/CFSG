module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec16.Item167ProofCrit
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
import CFSG.RankThree.PartTwo.KFacts.KP7Suzuki
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.RankThree.PartTwo.Sec14.Item1411Strong

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

section Suzuki

theorem suzukiModel_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {p f : ℕ}
    (h : CFSG.Blueprint.SuzukiModel H' p f) : CFSG.Blueprint.SuzukiModel H p f := by
  obtain ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, hK, hKf, hf, hcard, ⟨e.trans e'⟩⟩

theorem isSimpleGroup_of_suzukiModel {H : Type} [Group H]
    {p f : ℕ} (h : CFSG.Blueprint.SuzukiModel H p f) : IsSimpleGroup H := by
  obtain ⟨-, a, ha, K, hK, hKf, rfl, hcard, ⟨e⟩⟩ := h
  have := (CFSG.LieType.Ree.suzuki_simple (K := K) ha hcard).2.2
  exact e.isSimpleGroup

end Suzuki

section Perfect

theorem ker_eq_top_of_not_suzukiModel_section {K T : Type}
    [Group K] [Group T] [Finite K] [Group.IsPerfect K] {θ : Subgroup K} [θ.Normal]
    (hθ : Group.IsSolvable θ) {p f : ℕ} (hSz : CFSG.Blueprint.SuzukiModel (K ⧸ θ) p f)
    (hT : ∀ (X : Subgroup T) (N : Subgroup X) [N.Normal],
      ¬ CFSG.Blueprint.SuzukiModel (X ⧸ N) p f)
    (φ : K →* T) : φ.ker = ⊤ := by
  have : IsSimpleGroup (K ⧸ θ) := isSimpleGroup_of_suzukiModel hSz
  set C := φ.ker with hC
  have hCθ : (C ⊔ θ).Normal := Subgroup.sup_normal C θ
  have : ((C ⊔ θ).map (QuotientGroup.mk' θ)).Normal :=
    Subgroup.Normal.map hCθ _ (QuotientGroup.mk'_surjective θ)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C ⊔ θ).map (QuotientGroup.mk' θ))
    with h0 | h1
  ·
    exfalso
    have hCle : C ≤ θ := by
      intro x hx
      have : QuotientGroup.mk' θ x ∈ (C ⊔ θ).map (QuotientGroup.mk' θ) :=
        ⟨x, le_sup_left (a := C) hx, rfl⟩
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
      exact this
    set ψ := φ.rangeRestrict with hψ
    have hψs : Function.Surjective ψ := φ.rangeRestrict_surjective
    set N := θ.map ψ with hN
    have hNn : N.Normal := Subgroup.Normal.map inferInstance ψ hψs
    set χ := (QuotientGroup.mk' N).comp ψ with hχ
    have hχs : Function.Surjective χ := (QuotientGroup.mk'_surjective N).comp hψs
    have hker : χ.ker = θ := by
      ext x
      rw [MonoidHom.mem_ker, hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hxy : x * y⁻¹ ∈ C := by
          rw [hC, MonoidHom.mem_ker, map_mul, map_inv, ← MonoidHom.coe_rangeRestrict φ,
            ← MonoidHom.coe_rangeRestrict φ]
          rw [← hψ, ← hyx]
          simp
        have := θ.mul_mem (hCle hxy) hy
        simpa using this
      · intro hx
        exact ⟨x, hx, rfl⟩
    have e : K ⧸ θ ≃* (φ.range ⧸ N) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective χ hχs)
    exact hT φ.range N (suzukiModel_of_mulEquiv e.symm hSz)
  ·
    have hCθK : C ⊔ θ = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' θ)) h1
      rwa [Subgroup.comap_top, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
        sup_assoc, sup_idem] at this
    set π := QuotientGroup.mk' C with hπ
    have hθmap : θ.map π = ⊤ := by
      have hC0 : C.map π = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
      calc θ.map π = C.map π ⊔ θ.map π := by rw [hC0, bot_sup_eq]
        _ = (C ⊔ θ).map π := (Subgroup.map_sup C θ π).symm
        _ = ⊤ := by rw [hCθK, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]; exact
            QuotientGroup.mk'_surjective C
    have hsurj : Function.Surjective (π.comp θ.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype, hθmap]
    have hsol : Group.IsSolvable (K ⧸ C) := Group.isSolvable_of_surjective hsurj
    by_contra hne
    have : Nontrivial (K ⧸ C) := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply hne
      exact eq_top_iff.mpr fun x _ => (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isSolvable (K ⧸ C) hsol

end Perfect

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def actQuotPCore (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  (Crit167.quotPCoreAut ↥Y).comp Y.normalizerMonoidHom

theorem mem_sectionCentralizer_of_actQuotPCore_eq_one {Y : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (Y : Set G)) (h1 : actQuotPCore Y ⟨m, hm⟩ = 1) :
    m ∈ sectionCentralizer (Subgroup.normalizer (Y : Set G)) Y (CFSG.Open.pCoreOf 2 Y) := by
  refine ⟨hm, fun y hy => ?_⟩
  have h := congrArg (fun σ : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) =>
    σ ((⟨y, hy⟩ : ↥Y) : ↥Y ⧸ CFSG.pCore 2 ↥Y)) h1
  simp only [actQuotPCore, MonoidHom.comp_apply, Crit167.quotPCoreAut_apply_mk, MulAut.one_apply]
    at h
  rw [QuotientGroup.eq] at h
  set a := Y.normalizerMonoidHom ⟨m, hm⟩ ⟨y, hy⟩ with ha
  have ha' : (a : G) = m * y * m⁻¹ :=
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨m, hm⟩ ⟨y, hy⟩
  have h2 : a * (⟨y, hy⟩ : ↥Y)⁻¹ ∈ CFSG.pCore 2 ↥Y := by
    have h3 := (CFSG.pCore_normal (p := 2) (G := ↥Y)).conj_mem _ (inv_mem h) ⟨y, hy⟩
    simpa [mul_assoc] using h3
  have h4 : ((a * (⟨y, hy⟩ : ↥Y)⁻¹ : ↥Y) : G) ∈ CFSG.Open.pCoreOf 2 Y := by
    rw [CFSG.Open.pCoreOf]
    exact ⟨_, h2, rfl⟩
  simpa [ha'] using h4

end Action

@[expose] def Step166Theta : Prop :=
  ∀ (G : Type) [Group G] [Finite G], TheoremFourHyp G → ∀ X K : Subgroup G,
    K ∈ thetaComponentsIn X → ∀ n : ℕ,
      CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n →
        CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K

@[expose] def Gen166 {G : Type} [Group G] [Finite G] (A : Subgroup G) (c : G) : Prop :=
  ∀ X ∈ scriptY A, X = delta A (lB A) X → ∀ K ∈ thetaComponentsIn X,
    (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) →
      CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K →
        ∃ U ∈ scriptQPiStar A (lB A) K (piOf 2),
          K = (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ K) ⊔ U

@[expose] def Step166Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Gen166 A c

@[expose] def Step166GenHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Gen166 A c

@[expose] def NoSz166 {G : Type} [Group G] (Y₀ : Subgroup G) : Prop :=
  ∀ (X : Subgroup (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) (N : Subgroup ↥X) [N.Normal] (p f : ℕ),
    ¬ CFSG.Blueprint.SuzukiModel (↥X ⧸ N) p f

@[expose] def Step166NoSz : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → NoSz166 Y₀

section One

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

omit [Finite G] in
theorem isPerfect_of_mem_thetaComponentsIn {X K : Subgroup G} (hK : K ∈ thetaComponentsIn X) :
    Group.IsPerfect ↥K := by
  obtain ⟨hKX, hK'⟩ := mem_thetaComponentsIn_iff.mp hK
  have : Group.IsPerfect ↥(K.subgroupOf X) := hK'.1
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKX).toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hKX).surjective

theorem rank3II_16_6_1_of (h : Sec17Std G A c L Y₀)
    (htheta : Step166Theta) (hgen : Gen166 A c) (hnosz : NoSz166 Y₀) {X : Subgroup G}
    (hX : X ∈ scriptY A) (hXΔ : X = delta A (lB A) X) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn X)
    (hSz : ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ aschbacherSolvableCore 3 ↥K) 2 n) :
    CFSG.pCore 2 ↥K = aschbacherSolvableCore 3 ↥K ∧
      (K : Set G) ⊆ sectionCentralizer (Subgroup.normalizer (Y₀ : Set G)) Y₀
        (CFSG.Open.pCoreOf 2 Y₀) := by
  obtain ⟨n, hn⟩ := hSz
  have hθ := htheta G h.toTheoremFourHyp X K hK n hn
  refine ⟨hθ, ?_⟩
  obtain ⟨U, hU, hKU⟩ := hgen X hX hXΔ K hK ⟨n, hn⟩ hθ
  have hKM : K ≤ Subgroup.normalizer (Y₀ : Set G) := by
    rw [hKU]
    refine sup_le (inf_le_left.trans h.normalizer_c_le) ?_
    exact HeadProof.le_M_of_mem_scriptQPi_two h ⟨⟨hU.prop.1.1, le_top⟩, hU.prop.2⟩
  have : Group.IsPerfect ↥K := isPerfect_of_mem_thetaComponentsIn hK
  set φ := (actQuotPCore Y₀).comp (Subgroup.inclusion hKM) with hφ
  have hker : φ.ker = ⊤ :=
    ker_eq_top_of_not_suzukiModel_section
      (LocalRank.solvable_prime_complement_core_characterization (H := ↥K) Nat.prime_three).1 hn
      (fun X' N _ => hnosz X' N 2 n) φ
  intro k hk
  have h1 : φ ⟨k, hk⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact Subgroup.mem_top _
  exact mem_sectionCentralizer_of_actQuotPCore_eq_one (hKM hk) h1

end One

section NoSzHJ

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem nonempty_quot_center_mulEquiv_j2
    (h : Sec17Std G A c L Y₀) (h1523 : Item1523 A (lB A) L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    Nonempty ((↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ⧸ Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) ≃*
      CFSG.Blueprint.NativeSporadic.J2) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eJ⟩ := hJ
  set Q := ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ with hQdef
  have hQ : CFSG.IsQuasisimple Q := h.mem_y0Star.prop.1.2.2.2
  have : Group.IsPerfect Q := hQ.1
  have : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  have hLY : L ≤ Y₀ := h.le_y0
  have hY₀eq : Y₀ = L ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
    have h1 := (h1523 ⟨eJ⟩ Y₀ h.mem_y0Star).1
    rwa [inf_of_le_right hLY] at h1
  set f : ↥L →* Q := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y₀)).comp (Subgroup.inclusion hLY)
    with hf
  have hfs : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y₀) q
    have hy' : y ∈ ((L : Set G) * (CFSG.Open.pCoreOf 2 Y₀ : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L _
        (hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₀)), ← hY₀eq]
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
    (LocalRank.solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
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
  have : IsSimpleGroup (↥L ⧸ θ) :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 eJ
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
  exact ⟨(MulEquiv.ofBijective gbar ⟨hgbi, hgbs⟩).symm.trans eJ⟩

theorem not_suzukiModel_section_of_j2
    (h : Sec17Std G A c L Y₀)
    (h1523 : Item1523 A (lB A) L)
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    (X : Subgroup (MulAut (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀))) (N : Subgroup ↥X) [N.Normal]
    (p f : ℕ) : ¬ CFSG.Blueprint.SuzukiModel (↥X ⧸ N) p f := by
  set Q := ↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀ with hQdef
  have hQ : CFSG.IsQuasisimple Q := h.mem_y0Star.prop.1.2.2.2
  have : Group.IsPerfect Q := hQ.1
  obtain ⟨e⟩ := nonempty_quot_center_mulEquiv_j2 h h1523 hJ
  have hcard : Nat.card (MulAut Q) ∣ 1209600 := by
    have h1 := Subgroup.card_dvd_of_injective _
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective Q)
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      (CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model).2.2.2.2.1]
      at h1
    exact h1
  have : Finite (MulAut Q) := KFacts.KP7.finite_mulAut Q
  refine KFacts.KP7.not_suzukiModel_section (fun h13 => ?_) (fun h2 => ?_) X N
  · have := h13.trans hcard
    norm_num at this
  · have := h2.trans hcard
    norm_num at this

end NoSzHJ

section StepsTwo

variable {G : Type} [Group G] [Finite G]

@[expose] def Omega166 (A Y₀ : Subgroup G) : Prop :=
  ∀ K₀ Z : Subgroup G, K₀ = delta A (lB A) K₀ →
    (∃ m : ℕ, CFSG.Blueprint.SuzukiModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) 2 m) → K₀ ≤ Z →
      Z ∈ scriptY3Star A (lB A) → Z ≤ Subgroup.normalizer (Y₀ : Set G)

@[expose] def Sol166 (A Y₀ : Subgroup G) : Prop :=
  Omega166 A Y₀ → ∀ X ∈ scriptY3Star A (lB A), ¬ Group.IsSolvable ↥X →
    ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) → Group.IsSolvable ↥(pPrimeCoreOf 3 X)

@[expose] def Ctr166 (A Y₀ : Subgroup G) : Prop :=
  ∀ X ∈ scriptY3Star A (lB A), ¬ Group.IsSolvable ↥X → Group.IsSolvable ↥(pPrimeCoreOf 3 X) →
    oPrimeResidualOf 3 X ≠ ⊥ → X ≤ Subgroup.normalizer (Y₀ : Set G)

end StepsTwo

@[expose] def Step166Omega : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Omega166 A Y₀

@[expose] def Step166OmegaHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Omega166 A Y₀

@[expose] def Step166Sol : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Sol166 A Y₀

@[expose] def Step166SolHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Sol166 A Y₀

@[expose] def Step166Ctr : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → Ctr166 A Y₀

@[expose] def Step166CtrHJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ →
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
        Ctr166 A Y₀

section Two

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem rank3II_16_6_2_of (hΩ : Omega166 A Y₀) (hsol : Sol166 A Y₀) (hctr : Ctr166 A Y₀)
    {X : Subgroup G} (hX : X ∈ scriptY3 A (lB A))
    (hns : ¬ Group.IsSolvable ↥X) : X ≤ Subgroup.normalizer (Y₀ : Set G) := by
  obtain ⟨X', hXX', hX'⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY3 A (lB A))) hX
  have hns' : ¬ Group.IsSolvable ↥X' := fun hs =>
    hns (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXX'))
  refine hXX'.trans ?_
  by_contra hM
  have hs := hsol hΩ X' hX' hns' hM
  have hK : oPrimeResidualOf 3 X' ≠ ⊥ := by
    intro h0
    apply hns'
    have h3 := Sec14.not_three_dvd_of_oPrimeResidualOf_eq_bot h0
    have hle : X' ≤ pPrimeCoreOf 3 X' :=
      le_pPrimeCoreOf le_rfl Subgroup.le_normalizer
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  exact hM (hctr X' hX' hns' hs hK)

end Two

section Item

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem rank3II_16_6_of (h : Sec17Std G A c L Y₀)
    (htheta : Step166Theta) (hgen : Gen166 A c) (hnosz : NoSz166 Y₀) (hΩ : Omega166 A Y₀)
    (hsol : Sol166 A Y₀) (hctr : Ctr166 A Y₀) : Item166 A (lB A) := by
  intro Y hY
  obtain rfl := h.eq_of_mem_y0Star hY
  exact ⟨fun X hX hXΔ K hK hSz => rank3II_16_6_1_of h htheta hgen hnosz hX hXΔ hK hSz,
    fun X hX hns => rank3II_16_6_2_of hΩ hsol hctr hX hns⟩

end Item

theorem noSz166_hj_of
    (h1523 : Sec15.Item1523R) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
      Sec17Std G A c L Y₀ →
        Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
          NoSz166 Y₀ :=
  fun G _ _ A c L _ h hJ X N _ p f =>
    not_suzukiModel_section_of_j2 h (h1523 G A c L h.toSec15R) hJ X N p f

theorem item166S17_of (htheta : Step166Theta)
    (hgen : Step166Gen) (hnosz : Step166NoSz) (hΩ : Step166Omega) (hsol : Step166Sol)
    (hctr : Step166Ctr) : Item166S17 := fun G _ _ A c L Y₀ h =>
  rank3II_16_6_of h htheta (hgen G A c L Y₀ h) (hnosz G A c L Y₀ h) (hΩ G A c L Y₀ h)
    (hsol G A c L Y₀ h) (hctr G A c L Y₀ h)

end CFSG.RankThree.PartTwo.Sec16
