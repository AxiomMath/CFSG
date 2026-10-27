module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepPGL
import CFSG.RankThree.PartTwo.Sec14.Item148StepPGLAbel
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec13.Item13Basic

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def KF148ONInner : Prop :=
  ∀ (Λ : Type) [Group Λ] [Finite Λ], Group.IsPerfect Λ →
    Sec4.IsTripleCover Λ CFSG.Blueprint.NativeSporadic.ON →
    ∀ (σ : MulAut Λ), σ ^ 3 = 1 → ∀ (P : Subgroup Λ), Group.IsPerfect ↥P →
      P.map σ.toMonoidHom = P → ∀ [Fact (Nat.Prime 7)],
      (∃ f : ↥P →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1),
        Function.Surjective f) →
      ∃ x ∈ P, ∀ y : Λ, σ y = x * y * x⁻¹

namespace Item148Point

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_perfect_le148 {A K Le : Subgroup G} {e : G}
    (hAe : A ≤ Subgroup.centralizer ({e} : Set G)) (hLe : Le ∈ thetaComponentsAt 3 e)
    (hKLe : K ≤ Le) (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hKp : Group.IsPerfect ↥K)
    (hK1 : K ≠ ⊥) : A ≤ Subgroup.normalizer (Le : Set G) := by
  intro a ha
  have hLe' : Le.map (MulAut.conj a).toMonoidHom ∈ thetaComponentsAt 3 e :=
    Sec6.map_conj_mem_thetaComponentsAt (hAe ha) hLe
  have hKLe' : K ≤ Le.map (MulAut.conj a).toMonoidHom := by
    intro k hk
    refine ⟨a⁻¹ * k * a, hKLe ?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hAK (A.inv_mem ha)) k).mp hk
      rwa [inv_inv] at h
    · simp [MulAut.conj_apply, mul_assoc]
  have heq : Le = Le.map (MulAut.conj a).toMonoidHom :=
    Sec6.eq_of_mem_thetaComponentsIn_of_le hLe hLe' hKp hK1 hKLe hKLe'
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm

theorem innerOn_img148_of_kf148ONInner (hON : KF148ONInner) {A Y : Subgroup G}
    [(ker148 A Y).Normal] {K Le : Subgroup G} (hKLe : K ≤ Le) (hKM : K ≤ Y ⊔ A)
    [hKp : Group.IsPerfect ↥K] (hLp : Group.IsPerfect (↥Le ⧸ aschbacherSolvableCore 3 ↥Le))
    (hTC : Sec4.IsTripleCover (↥Le ⧸ aschbacherSolvableCore 3 ↥Le)
      CFSG.Blueprint.NativeSporadic.ON)
    [Fact (Nat.Prime 7)]
    (φ : ↥(img148 A Y K) ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))
    {a : G} (haA : a ∈ A) (haLe : a ∈ Subgroup.normalizer (Le : Set G))
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (ha3 : a ^ 3 = 1) :
    InnerOn148 (img148 A Y K) (alpha148 A Y a haA) := by
  classical
  set θL := aschbacherSolvableCore 3 ↥Le with hθL
  set ι : ↥K →* ↥Le ⧸ θL := (QuotientGroup.mk' θL).comp (Subgroup.inclusion hKLe) with hι
  set ρ₀ : ↥K →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion hKM) with hρ₀
  have hρ₀mem : ∀ y : ↥K, ρ₀ y ∈ img148 A Y K := fun y =>
    mem_img148_iff.mpr ⟨y, hKM y.2, y.2, rfl⟩
  set ρ : ↥K →* ↥(img148 A Y K) := ρ₀.codRestrict _ hρ₀mem with hρ
  have hρsurj : Function.Surjective ρ := by
    rintro ⟨z, hz⟩
    obtain ⟨g, hg, hgK, rfl⟩ := mem_img148_iff.mp hz
    exact ⟨⟨g, hgK⟩, rfl⟩
  have hS : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
    Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
  have hSK : IsSimpleGroup ↥(img148 A Y K) := φ.isSimpleGroup
  have hKαp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
  have hker : ι.ker ≤ ρ.ker := by
    have hθs : Group.IsSolvable ↥θL :=
      (solvable_prime_complement_core_characterization Nat.prime_three).1
    have hle : ι.ker.map (Subgroup.inclusion hKLe) ≤ θL := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : ι y = 1 := hy
      exact (QuotientGroup.eq_one_iff _).mp hy'
    have hs1 : Group.IsSolvable ↥(ι.ker.map (Subgroup.inclusion hKLe)) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)
    have hs : Group.IsSolvable ↥ι.ker :=
      Group.isSolvable_of_isSolvable_injective
        (f := (ι.ker.equivMapOfInjective _ (Subgroup.inclusion_injective hKLe)).toMonoidHom)
        (MulEquiv.injective _)
    have hNn : (ι.ker.map ρ).Normal := (MonoidHom.normal_ker ι).map ρ hρsurj
    have hNs : Group.IsSolvable ↥(ι.ker.map ρ) :=
      Group.isSolvable_of_surjective (ρ.subgroupMap_surjective ι.ker)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ι.ker.map ρ) with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      rw [ht] at hNs
      have : Group.IsSolvable ↥(img148 A Y K) :=
        Group.isSolvable_of_surjective (f := (Subgroup.topEquiv).toMonoidHom)
          (MulEquiv.surjective _)
      exact Group.IsPerfect.not_isSolvable ↥(img148 A Y K) this
  set f₀ : ↥K →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1) :=
    φ.toMonoidHom.comp ρ with hf₀
  have hker₀ : ι.ker ≤ f₀.ker := fun y hy => by
    rw [MonoidHom.mem_ker] at hy ⊢
    have h1 : ρ y = 1 := hker hy
    simp [hf₀, h1]
  set f : ↥ι.range →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1) :=
    (QuotientGroup.lift ι.ker f₀ hker₀).comp
      (QuotientGroup.quotientKerEquivRange ι).symm.toMonoidHom with hf
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨w, rfl⟩ := φ.surjective z
    obtain ⟨y, rfl⟩ := hρsurj w
    refine ⟨⟨ι y, y, rfl⟩, ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivRange ι).symm ⟨ι y, y, rfl⟩ =
        ((y : ↥K) : ↥K ⧸ ι.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    simp only [hf, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h1,
      QuotientGroup.lift_mk, hf₀]
  set σ : MulAut (↥Le ⧸ θL) :=
    Sec4.thetaQuotMulAut ↥Le (Le.normalizerMonoidHom ⟨a, haLe⟩) with hσdef
  have hconjK : ∀ y : ↥K, a * (y : G) * a⁻¹ ∈ K := fun y =>
    (Subgroup.mem_normalizer_iff.mp haK y).mp y.2
  have hσι : ∀ y : ↥K, σ (ι y) = ι ⟨a * (y : G) * a⁻¹, hconjK y⟩ := by
    intro y
    rw [hσdef, hι, MonoidHom.comp_apply, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
    rfl
  have hσ3 : σ ^ 3 = 1 := by
    have h1 : (⟨a, haLe⟩ : Subgroup.normalizer (Le : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hσdef, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hσP : ι.range.map σ.toMonoidHom = ι.range := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨_, (hσι y).symm⟩
    · rintro _ ⟨y, rfl⟩
      have hy' : a⁻¹ * (y : G) * a ∈ K := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haK) y).mp y.2
        rwa [inv_inv] at h
      refine ⟨ι ⟨_, hy'⟩, ⟨_, rfl⟩, ?_⟩
      change σ (ι ⟨_, hy'⟩) = ι y
      rw [hσι]
      congr 1
      apply Subtype.ext
      simp [mul_assoc]
  have hPp : Group.IsPerfect ↥ι.range :=
    Group.IsPerfect.ofSurjective (f := ι.rangeRestrict) ι.rangeRestrict_surjective
  obtain ⟨x, ⟨k₀, rfl⟩, hx⟩ := hON _ hLp hTC σ hσ3 ι.range hPp hσP ⟨f, hfsurj⟩
  refine ⟨ρ₀ k₀, hρ₀mem k₀, fun z hz => ?_⟩
  obtain ⟨g, hg, hgK, rfl⟩ := mem_img148_iff.mp hz
  obtain ⟨y, rfl⟩ : ∃ y : ↥K, (y : G) = g := ⟨⟨g, hgK⟩, rfl⟩
  have h1 : σ (ι y) = ι (k₀ * y * k₀⁻¹) := by
    rw [hx, map_mul, map_mul, map_inv]
  rw [hσι] at h1
  have h3 : (⟨a * (y : G) * a⁻¹, hconjK y⟩ : ↥K)⁻¹ * (k₀ * y * k₀⁻¹) ∈ ρ.ker := by
    refine hker ?_
    rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
  have h4 : ρ₀ ⟨a * (y : G) * a⁻¹, hconjK y⟩ = ρ₀ (k₀ * y * k₀⁻¹) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h3
    exact congrArg Subtype.val h3
  have e1 : alpha148 A Y a haA * QuotientGroup.mk' (ker148 A Y) ⟨(y : G), hg⟩ *
      (alpha148 A Y a haA)⁻¹ = ρ₀ ⟨a * (y : G) * a⁻¹, hconjK y⟩ := by
    rw [alpha148_eq_mk', ← map_inv, ← map_mul, ← map_mul]
    rfl
  have e2 : QuotientGroup.mk' (ker148 A Y) ⟨(y : G), hg⟩ = ρ₀ y := rfl
  rw [e1, h4, e2, map_mul, map_mul, map_inv]

end Item148Point

section Steps


theorem step148PGLON_of (hON : KF148ONInner) : Step148PGLON := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl hTC h7
  have := ker148_normal hY.2
  obtain ⟨hfact, ⟨φ⟩⟩ := h7
  have hAF : A ∈ partTwoF G := h.mem_partTwoF
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have hJM : J ≤ Y ⊔ A := hJY.trans le_sup_left
  have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  obtain ⟨-, -, -, -, -, hK, hKΔ, hKLe, hLe, -⟩ := hP
  have hKYC : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hKM : K ≤ Y ⊔ A := (hKYC.trans inf_le_left).trans le_sup_left
  have hKp : Group.IsPerfect K := isPerfect_of_mem_thetaComponentsIn hK
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_eq_deltaZero hKΔ
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hx he)
  have hS : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
    Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
  have hK1 : K ≠ ⊥ := by
    rintro rfl
    have hbot : img148 A Y (⊥ : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨g, -, hg, rfl⟩ := mem_img148_iff.mp hz
      rw [Subgroup.mem_bot] at hg
      subst hg
      exact map_one _
    have : Subsingleton ↥(img148 A Y (⊥ : Subgroup G)) := by
      rw [hbot]
      infer_instance
    have hnt := hS.toNontrivial
    have hss : Subsingleton ↥(CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
      φ.symm.injective.subsingleton
    exact not_nontrivial_iff_subsingleton.mpr hss hnt
  have hALe : A ≤ Subgroup.normalizer (Le : Set G) :=
    Item148Point.le_normalizer_of_perfect_le148 hAe hLe hKLe hAK hKp hK1
  have hLp : Group.IsPerfect (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) :=
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLe).1
  have hEq : img148 A Y K = img148 A Y J := halt
  have hin : ∀ (a : G) (ha : a ∈ A), ∃ k : ℕ,
      InnerOn148 (img148 A Y J) (alpha148 A Y a ha * alpha148 A Y e he ^ k) := by
    intro a ha
    refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, ← hEq]
    exact Item148Point.innerOn_img148_of_kf148ONInner hON hKLe hKM hLp hTC φ ha (hALe ha)
      (hAK ha) (hA3 a ha)
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 hJM
  have hZ : Subgroup.center ↥(img148 A Y J) = ⊥ :=
    kf148CenterL3 _ hJp (Or.inr ⟨7, 1, hfact, by norm_num, le_rfl,
      Or.inl ⟨(MulEquiv.subgroupCongr hEq).symm.trans φ⟩⟩)
  have hCJ := sectionCentralizer_subset_of_le (Y := Y) hKJ hkt.1
  have hA : A = Subgroup.zpowers e ⊔ (A ⊓ J) :=
    eq_zpowers_sup_inf_of_innerOn hAF hAY hJY hAJ he hZ hCJ hin
  obtain ⟨p, f, -, hpgl'⟩ := hpgl
  exact false_of_isZ3PGLThreeAt148 kf148PGLAbel hJM he hA hpgl'

@[expose] def Step148PGLSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        (∃ (p f : ℕ), 1 ≤ f ∧
          (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)) →
        Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) Y) ≤ img148 A Y J ⊔
            (img148 A Y (deltaZero A (lB A) Y) ⊓
              Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) ∨
          Case148Seven A (lB A) Y

@[expose] def Step148PGLCent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec14Std G A c L → ∀ (Y : Subgroup G) (hY : Y ∈ scriptY A), ¬ Group.IsSolvable ↥Y →
      Ind148 A (lB A) Y → (∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B') →
      ∀ (B Q : Subgroup G) (e : G) (K Le : Subgroup G), IsPoint148 A (lB A) Y B Q e K Le →
      (letI := ker148_normal hY.2; KType148 A Y e K Le) →
      ∀ (_he : e ∈ A) (J : Subgroup G), J ∈ thetaComponentsIn Y → K ≤ J →
        A ≤ Subgroup.normalizer (J : Set G) →
        (letI := ker148_normal hY.2; Lift148Eq A Y K J) →
        (∃ (p f : ℕ), 1 ≤ f ∧
          (letI := ker148_normal hY.2; IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f)) →
        Subgroup.zpowers e ∈ omegaA A → Le ∈ lA A e →
        letI := ker148_normal hY.2
        img148 A Y (deltaZero A (lB A) Y) ⊓
            Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) ≤
          img148 A Y J ∨
          Case148Seven A (lB A) Y

theorem step148PGLImg_of (hSp : Step148PGLSplit) (hCe : Step148PGLCent) : Step148PGLImg := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA
  have := ker148_normal hY.2
  rcases hSp G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA with
    hsplit | h7
  · rcases hCe G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ
      hLeA with hcent | h7
    · refine Or.inl (le_antisymm (hsplit.trans (sup_le le_rfl hcent)) ?_)
      have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1).trans inf_le_left
      have hKX : K ≤ deltaZero A (lB A) Y :=
        hP.2.2.2.2.2.2.1.le.trans (deltaZero_mono148 hKY)
      have hEq : img148 A Y K = img148 A Y J := halt
      rw [← hEq]
      exact img148_mono hKX
    · exact Or.inr h7
  · exact Or.inr h7

theorem step148PGLSplit_of_step148PGLImg (h : Step148PGLImg) : Step148PGLSplit := by
  intro G _ _ A c L hS Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA
  rcases h G A c L hS Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA with
    hXJ | h7
  · exact Or.inl (hXJ.le.trans le_sup_left)
  · exact Or.inr h7

theorem step148PGLCent_of_step148PGLImg (h : Step148PGLImg) : Step148PGLCent := by
  intro G _ _ A c L hS Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA
  rcases h G A c L hS Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hpgl heΩ hLeA with
    hXJ | h7
  · exact Or.inl (inf_le_left.trans hXJ.le)
  · exact Or.inr h7

end Steps

end CFSG.RankThree.PartTwo.Sec14
