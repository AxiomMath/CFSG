module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlag
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1ILongRootConj
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IPerfect
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OddCenter
public import CFSG.Timmesfeld.RankOne.SL2
public import CFSG.Timmesfeld.Bridge.RootSetsSyl
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartOne.S11c.Sec66TGroup
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434AltPerm
public import CFSG.GroupTheory.ConjTransport
public import CFSG.Timmesfeld.Bridge.LocalA
public import CFSG.Timmesfeld.Bridge.NoPolarConnected
public import CFSG.Timmesfeld.Bridge.RootSets
public import CFSG.Timmesfeld.Bridge.RootSetsCases
public import CFSG.Timmesfeld.Bridge.RootSetsKernel
public import CFSG.Timmesfeld.Exceptional.Residual
public import CFSG.Timmesfeld.Moufang.Three

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

private theorem rckRPirg_odd_center_of_surjective {P Q : Type*} [Group P] [Group Q]
    (hP : Group.IsPerfect P) (f : P →* Q) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center P) (hodd : Odd (Nat.card (Subgroup.center P))) :
    Odd (Nat.card (Subgroup.center Q)) := by
  have : Group.IsPerfect P := hP
  rw [CFSG.RankThree.PartOne.Sec66T.center_eq_map_of_perfect f hsurj hker]
  exact hodd.of_dvd_nat (Subgroup.card_map_dvd (H := Subgroup.center P) f)

private theorem rckRPirg_subgroupOf_map_conj {G : Type*} [Group G] {H P : Subgroup G}
    (hP : P ≤ H) (y : H) :
    (P.map (MulAut.conj (y : G)).toMonoidHom).subgroupOf H =
      (P.subgroupOf H).map (MulAut.conj y).toMonoidHom := by
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_subgroupOf] at hz
    obtain ⟨p, hp, hpz⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_map.mpr ⟨⟨p, hP hp⟩, hp, ?_⟩
    exact Subtype.ext hpz
  · rintro ⟨p, hp, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨(p : G), hp, rfl⟩

private theorem rckRPirg_map_map_conj {G L : Type*} [Group G] [Group L]
    (j : G →* L) (P : Subgroup G) (y : G) :
    (P.map (MulAut.conj y).toMonoidHom).map j =
      (P.map j).map (MulAut.conj (j y)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

private theorem rckRPirg_map_conj_mul {U G L : Type*} [Group U] [Group G] [Group L]
    (κ : U →* G) (j : G →* L) (H : Subgroup U) (u w : U) :
    (((H.map (MulAut.conj w).toMonoidHom).map (MulAut.conj u).toMonoidHom).map κ).map j =
      ((H.map κ).map j).map (MulAut.conj (j (κ (u * w)))).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
  ext x
  simp [MulAut.conj_apply, map_mul, mul_assoc]

private theorem rckRPirg_factorization_two {N m f : ℕ} (hN : N = 2 ^ f * m) (hm : Odd m) :
    N.factorization 2 = f := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hm
    omega
  have hnot : ¬ 2 ∣ m := by
    rintro ⟨k, hk⟩
    obtain ⟨l, hl⟩ := hm
    omega
  rw [hN, Nat.factorization_mul (pow_ne_zero f (by norm_num)) hm0]
  simp [Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hnot]

private theorem rckRPirg_exists_conj_eq_of_card {H : Type*} [Group H] [Finite H]
    {f : ℕ} {P Q : Subgroup H} (hfac : (Nat.card H).factorization 2 = f)
    (hP : Nat.card P = 2 ^ f) (hQ : Nat.card Q = 2 ^ f) :
    ∃ y : H, P.map (MulAut.conj y).toMonoidHom = Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQfull : Nat.card Q = 2 ^ (Nat.card H).factorization 2 := by rw [hfac, hQ]
  have hPfull : 2 ^ f = 2 ^ (Nat.card H).factorization 2 := by rw [hfac]
  have hPQ : IsPGroup 2 P := IsPGroup.of_card hP
  obtain ⟨y, hle⟩ :=
    CFSG.RankThree.PartTwo.Sec4.Item434AltPerm.exists_le_map_conj_of_card
      (G := H) hQfull hPQ
  have hPeq : P = Q.map (MulAut.conj y).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hQ, hP, hPfull]
  refine ⟨y⁻¹, ?_⟩
  rw [hPeq]
  exact CFSG.GroupTheory.map_conj_map_conj_inv y Q

theorem card_rootGroup_specialLinear {m : ℕ} {F : Type} [Field F]
    {γ : Fin (SpecialLinear.rootDatum m F).rank → ℤ}
    (hγ : γ ∈ (SpecialLinear.rootDatum m F).roots) :
    Nat.card (SpecialLinear.rootGroup m F γ) = Nat.card F := by
  change γ ∈ roots (SpecialLinear.isFiniteType_A m) ∅ at hγ
  rw [SpecialLinear.roots_eq] at hγ
  obtain ⟨i, j, hij, hto⟩ := hγ
  rw [SpecialLinear.rootGroup_eq m F hij hto]
  change Nat.card ((Matrix.SpecialLinearGroup.transvectionHom hij :
      Multiplicative F →* Matrix.SpecialLinearGroup (Fin (m + 1)) F).range) = Nat.card F
  have hf : Function.Injective (Matrix.SpecialLinearGroup.transvectionHom hij :
      Multiplicative F →* Matrix.SpecialLinearGroup (Fin (m + 1)) F) := by
    intro a b hab
    have hab' : Multiplicative.toAdd a = Multiplicative.toAdd b := by
      apply Matrix.SpecialLinearGroup.transvection_injective hij
      simpa [Matrix.SpecialLinearGroup.transvectionHom_apply] using hab
    exact Multiplicative.toAdd.injective hab'
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hf, Subgroup.card_top]
  exact (Nat.card_congr (Multiplicative.ofAdd (α := F))).symm

theorem card_rootGroup_specialLinear_galoisField {p k q : ℕ} [Fact p.Prime] (hq : q ≠ 0)
    {β : Fin (SpecialLinear.rootDatum k (GaloisField p q)).rank → ℤ}
    (hβ : β ∈ (SpecialLinear.rootDatum k (GaloisField p q)).roots) :
    Nat.card ((SpecialLinear.rootDatum k (GaloisField p q)).rootGroup β) = p ^ q := by
  have h := card_rootGroup_specialLinear (m := k) (F := GaloisField p q) hβ
  rw [GaloisField.card (p := p) q hq] at h
  exact h

@[expose] def RCKRPRootFlags
    {G : Type} [Group G] {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (j : G →* GL ι F)
    (B : Option ((ι → F) → (ι → F) → F)) {t : StatedLieTag} {k g : ℕ} (κ : (ggU t k g).K →* G) :
    Prop :=
  ∀ β ∈ (ggU t k g).D.roots,
    (GGLongRoot (ggU t k g).D β ∨ (((t = .PSp ∧ k = 2) ∨ t = .F4) ∧ 2 • β ∉ (ggU t k g).D.roots)) →
    ∀ u : (ggU t k g).K, GLGeoFlag B ((ggRootSub (ggU t k g).D κ β u).map j)

@[expose] def RCKRPFlaggedModel
    {G : Type} [Group G] {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (j : G →* GL ι F)
    (B : Option ((ι → F) → (ι → F) → F)) (J' : Subgroup G) : Prop :=
  ∃ (t : StatedLieTag) (k g : ℕ) (κ : (ggU t k g).K →* G), RCKNormalizedModel t k g ∧ κ.range = J' ∧
    (∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU t k g).K) ∧ RCKRPRootFlags j B κ

theorem rckRP_exists_rootSub_of_model
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] {G : Type} [Group G]
    (φ : G →* X) (hφk : φ.ker ≤ Subgroup.center G)
    {J' : Subgroup G} {J R Rm : Subgroup X} (hJ : J'.map φ = J)
    (hJq : CFSG.Assembly.IsQuasisimple ↥J) (hpos : GGRootPosJ J R Rm)
    {t : StatedLieTag} {k g : ℕ} (κ : (ggU t k g).K →* G) (hnorm : RCKNormalizedModel t k g)
    (hκr : κ.range = J')
    (hκz : ∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU t k g).K) :
    ∃ β ∈ (ggU t k g).D.roots,
      (GGLongRoot (ggU t k g).D β ∨
        (((t = .PSp ∧ k = 2) ∨ t = .F4) ∧ 2 • β ∉ (ggU t k g).D.roots)) ∧
      ∃ u : (ggU t k g).K, (ggRootSub (ggU t k g).D κ β u).map φ = R := by
  let ψ : (ggU t k g).K →* X := φ.comp κ
  have hψr : ψ.range = J := by
    dsimp [ψ]
    rw [MonoidHom.range_comp, hκr, hJ]
  have hψk : ψ.ker ≤ Subgroup.center (ggU t k g).K := by
    intro y hy
    apply hκz y
    apply hφk
    simpa [ψ] using hy
  obtain ⟨htag, hadm⟩ := hnorm
  have htags : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨
      t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 := htag
  have hoddK : Odd (Nat.card (Subgroup.center (ggU t k g).K)) :=
    CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_ggU htags hadm
  have hperf : Group.IsPerfect (ggU t k g).K :=
    Group.isPerfect_def.mpr (CFSG.StandardType.RCKK1I.rckK1I_ggU_perfect htag hadm)
  have hoddψ : Odd (Nat.card (Subgroup.center ↥ψ.range)) :=
    rckRPirg_odd_center_of_surjective hperf ψ.rangeRestrict ψ.rangeRestrict_surjective
      (by rw [MonoidHom.ker_rangeRestrict]; exact hψk) hoddK
  have hoddJ : Odd (Nat.card (Subgroup.center ↥J)) := by
    rwa [hψr] at hoddψ
  obtain ⟨β, u, hβ, hclause, hR, -⟩ :=
    (hIRG X J R Rm hJq hoddJ hpos).1 t k g ψ ⟨htag, hadm⟩ hψr hψk
  refine ⟨β, hβ, hclause, u, ?_⟩
  rw [hR]
  simp only [ggRootSub, ψ]
  rw [Subgroup.map_map]

theorem rckRP_glGeoFlag_of_flaggedModel
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] {G : Type} [Group G]
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (j : G →* GL ι F)
    {B : Option ((ι → F) → (ι → F) → F)} (φ : G →* X) (hφk : φ.ker ≤ Subgroup.center G)
    {J' : Subgroup G} {J R Rm : Subgroup X} (hJ : J'.map φ = J)
    (hJq : CFSG.Assembly.IsQuasisimple ↥J)
    (hpos : GGRootPosJ J R Rm) (hM : RCKRPFlaggedModel j B J') :
    ∃ R' : Subgroup G, R'.map φ = R ∧ GLGeoFlag B (R'.map j) := by
  obtain ⟨t, k, g, κ, hnorm, hκr, hκz, hflags⟩ := hM
  obtain ⟨β, hβ, hclause, u, hR⟩ :=
    rckRP_exists_rootSub_of_model hIRG φ hφk hJ hJq hpos κ hnorm hκr hκz
  exact ⟨ggRootSub (ggU t k g).D κ β u, hR, hflags β hβ hclause u⟩

theorem rckRP_exists_rootSub_eq_of_long
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] {G : Type} [Group G]
    (φ : G →* X) (hφk : φ.ker ≤ Subgroup.center G)
    {J' : Subgroup G} {J R Rm : Subgroup X} (hJ : J'.map φ = J)
    (hJq : CFSG.Assembly.IsQuasisimple ↥J) (hpos : GGRootPosJ J R Rm)
    {t : StatedLieTag} {k g : ℕ} (κ : (ggU t k g).K →* G) (hnorm : RCKNormalizedModel t k g)
    (hnot : ¬ ((t = .PSp ∧ k = 2) ∨ t = .F4)) (hκr : κ.range = J')
    (hκz : ∀ y, κ y ∈ Subgroup.center G → y ∈ Subgroup.center (ggU t k g).K)
    {β₀ : Fin (ggU t k g).D.rank → ℤ} (hl₀ : GGLongRoot (ggU t k g).D β₀) :
    ∃ c : (ggU t k g).K, (ggRootSub (ggU t k g).D κ β₀ c).map φ = R := by
  obtain ⟨β, hβ, hclause, u, hR⟩ :=
    rckRP_exists_rootSub_of_model hIRG φ hφk hJ hJq hpos κ hnorm hκr hκz
  have hlong : GGLongRoot (ggU t k g).D β := by
    rcases hclause with h | ⟨hshort, -⟩
    · exact h
    · exact absurd hshort hnot
  obtain ⟨w, hw⟩ := CFSG.StandardType.RCKK1I.rckK1I_longRootConj hnorm.1 hnorm.2
    (ggLongRoot_mem_roots hl₀) hl₀ hβ hlong
  refine ⟨u * w, ?_⟩
  rw [← hR, ggRootSub, ggRootSub, ← hw, CFSG.GroupTheory.map_conj_map_conj]

theorem rckRP_card_map_ggRootSub
    {G X : Type} [Group G] [Group X] {t : StatedLieTag} {k g : ℕ}
    (hnorm : RCKNormalizedModel t k g) (κ : (ggU t k g).K →* G) (φ : G →* X)
    (hker : (φ.comp κ).ker ≤ Subgroup.center (ggU t k g).K)
    {β : Fin (ggU t k g).D.rank → ℤ} (hβ : β ∈ (ggU t k g).D.roots) (u : (ggU t k g).K) :
    Nat.card ((ggRootSub (ggU t k g).D κ β u).map φ) =
      Nat.card ((ggU t k g).D.rootGroup β) := by
  classical
  obtain ⟨htag, hadm⟩ := hnorm
  have htD : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨
      t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 := htag
  have : Finite (ggU t k g).K := CFSG.StandardType.LieKnownR2.OddCenter.finite_ggU htD hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (Subgroup.center (ggU t k g).K)) :=
    CFSG.StandardType.LieKnownR2.OddCenter.odd_card_center_ggU htD hadm
  have hmod : CFSG.ClassicalInvolution.ModelFacts.modelUniv t k 2 g Nat.prime_two = ggU t k g := by
    rcases htD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  have hfund : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    rcases htD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have hp : IsPGroup 2 ((ggU t k g).D.rootGroup β) := by
    have h := CFSG.LieType.HighestRoot.isPGroup_rootGroup_modelUniv t k 2 g Nat.prime_two hfund hadm
    rw [hmod] at h
    exact h β hβ
  let S : Subgroup (ggU t k g).K := ((ggU t k g).D.rootGroup β).map (MulAut.conj u).toMonoidHom
  have hS : Nat.card S = Nat.card ((ggU t k g).D.rootGroup β) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective
  have hSp : IsPGroup 2 S := hp.map (MulAut.conj u).toMonoidHom
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hSp
  have hdisj : Disjoint S (φ.comp κ).ker :=
    (Subgroup.disjoint_of_coprime_natCard
      (by rw [hn]; exact hodd.coprime_two_left.pow_left n)).mono_right hker
  have hinj : Set.InjOn (φ.comp κ) (S : Set (ggU t k g).K) := by
    intro a ha b hb hab
    have hone : a * b⁻¹ = 1 := Subgroup.disjoint_def.mp hdisj (S.mul_mem ha (S.inv_mem hb))
      (by rw [MonoidHom.mem_ker, map_mul, map_inv, hab, mul_inv_cancel])
    exact mul_inv_eq_one.mp hone
  show Nat.card ↥((S.map κ).map φ) = _
  rw [Subgroup.map_map, ← hS]
  have h := Nat.card_image_of_injOn hinj
  rw [← Subgroup.coe_map] at h
  exact h

theorem rckRP_rootFlags_of_long
    {G : Type} [Group G] {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] (j : G →* GL ι F)
    {B : Option ((ι → F) → (ι → F) → F)}
    (hiso : ∀ y : G, ∀ b ∈ B, ∀ m m' : ι → F,
      b ((j y : Matrix ι ι F).mulVec m) ((j y : Matrix ι ι F).mulVec m') = b m m')
    {t : StatedLieTag} {k g : ℕ} (hnorm : RCKNormalizedModel t k g)
    (hnot : ¬ ((t = .PSp ∧ k = 2) ∨ t = .F4)) (κ : (ggU t k g).K →* G)
    {β₀ : Fin (ggU t k g).D.rank → ℤ} (hβ₀ : β₀ ∈ (ggU t k g).D.roots)
    (hl₀ : GGLongRoot (ggU t k g).D β₀)
    (hflag₀ : GLGeoFlag B ((((ggU t k g).D.rootGroup β₀).map κ).map j)) :
    RCKRPRootFlags j B κ := by
  intro β hβ hclause u
  have hlong : GGLongRoot (ggU t k g).D β := by
    rcases hclause with h | ⟨hshort, -⟩
    · exact h
    · exact absurd hshort hnot
  obtain ⟨htag, hadm⟩ := hnorm
  obtain ⟨w, hw⟩ :=
    CFSG.StandardType.RCKK1I.rckK1I_longRootConj htag hadm hβ₀ hl₀ hβ hlong
  have hmap : (ggRootSub (ggU t k g).D κ β u).map j =
      ((((ggU t k g).D.rootGroup β₀).map κ).map j).map
        (MulAut.conj (j (κ (u * w)))).toMonoidHom := by
    rw [ggRootSub, ← hw]
    exact rckRPirg_map_conj_mul κ j ((ggU t k g).D.rootGroup β₀) u w
  rw [hmap]
  exact glGeoFlag_map_conj hflag₀ (j (κ (u * w))) (hiso (κ (u * w)))

theorem rckRP_rootFlags_PSL_two
    {G : Type} [Group G] [Finite G] {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (j : G →* GL ι F) {B : Option ((ι → F) → (ι → F) → F)}
    (hiso : ∀ y : G, ∀ b ∈ B, ∀ m m' : ι → F,
      b ((j y : Matrix ι ι F).mulVec m) ((j y : Matrix ι ι F).mulVec m') = b m m')
    {f : ℕ} (hf : 2 ≤ f) (κ : (ggU .PSL 2 f).K →* G) (hκ : κ.ker ≤ Subgroup.center (ggU .PSL 2 f).K)
    {P₀ : Subgroup G} (hP₀ : P₀ ≤ κ.range) (hcard : Nat.card P₀ = 2 ^ f)
    (hflag : GLGeoFlag B (P₀.map j)) :
    RCKRPRootFlags j B κ := by
  classical
  intro β hβ hclause u
  have hfne : f ≠ 0 := by omega
  have hcenter : Subgroup.center (ggU .PSL 2 f).K = ⊥ := by
    change Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) = ⊥
    exact CFSG.Timmesfeld.RankOne.center_SL2_eq_bot (K := GaloisField 2 f)
  have hkerbot : κ.ker = ⊥ := le_bot_iff.mp (hκ.trans (le_of_eq hcenter))
  have hκinj : Function.Injective κ := (MonoidHom.ker_eq_bot_iff κ).mp hkerbot
  let H : Subgroup G := κ.range
  have : Finite H := by
    dsimp [H]
    infer_instance
  have hcardK : Nat.card (ggU .PSL 2 f).K = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    change Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) = _
    exact CFSG.Timmesfeld.Bridge.card_SL_two_galoisField_two f hfne
  have hcardH : Nat.card H = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hκinj).toEquiv]
    exact hcardK
  have hm_odd : Odd ((2 ^ f) ^ 2 - 1) :=
    CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := f) (n := 2)
      (by omega) (by norm_num)
  have hfac : (Nat.card H).factorization 2 = f :=
    rckRPirg_factorization_two hcardH hm_odd
  have hroot : Nat.card ((ggU .PSL 2 f).D.rootGroup β) = 2 ^ f := by
    change Nat.card ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup β) = 2 ^ f
    exact card_rootGroup_specialLinear_galoisField (k := 1) (q := f) hfne hβ
  have hPcard : Nat.card (ggRootSub (ggU .PSL 2 f).D κ β u) = 2 ^ f := by
    change Nat.card ((((ggU .PSL 2 f).D.rootGroup β).map
      (MulAut.conj u).toMonoidHom).map κ) = 2 ^ f
    rw [Subgroup.card_map_of_injective hκinj,
      Subgroup.card_map_of_injective (MulAut.conj u).injective]
    exact hroot
  have hPle : ggRootSub (ggU .PSL 2 f).D κ β u ≤ κ.range := by
    intro x hx
    obtain ⟨y, -, hyx⟩ := Subgroup.mem_map.mp hx
    exact ⟨y, hyx⟩
  have hP' : Nat.card ((ggRootSub (ggU .PSL 2 f).D κ β u).subgroupOf H) = 2 ^ f := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv]
    exact hPcard
  have hQ' : Nat.card (P₀.subgroupOf H) = 2 ^ f := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀).toEquiv]
    exact hcard
  obtain ⟨y, hyconj⟩ := rckRPirg_exists_conj_eq_of_card (H := H) hfac hQ' hP'
  have hmap_le : P₀.map (MulAut.conj (y : G)).toMonoidHom ≤ κ.range := by
    rintro _ ⟨p, hp, rfl⟩
    exact κ.range.mul_mem (κ.range.mul_mem y.2 (hP₀ hp)) (κ.range.inv_mem y.2)
  have hP_eq : ggRootSub (ggU .PSL 2 f).D κ β u =
      P₀.map (MulAut.conj (y : G)).toMonoidHom := by
    calc ggRootSub (ggU .PSL 2 f).D κ β u
        = ((ggRootSub (ggU .PSL 2 f).D κ β u).subgroupOf H).map H.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hPle).symm
      _ = ((P₀.subgroupOf H).map (MulAut.conj y).toMonoidHom).map H.subtype := by
            rw [hyconj]
      _ = ((P₀.map (MulAut.conj (y : G)).toMonoidHom).subgroupOf H).map H.subtype := by
            rw [← rckRPirg_subgroupOf_map_conj hP₀ y]
      _ = P₀.map (MulAut.conj (y : G)).toMonoidHom :=
            Subgroup.map_subgroupOf_eq_of_le hmap_le
  rw [hP_eq, rckRPirg_map_map_conj j P₀ (y : G)]
  exact glGeoFlag_map_conj hflag (j (y : G)) (hiso (y : G))

end CFSG.StandardType.RCKRP
