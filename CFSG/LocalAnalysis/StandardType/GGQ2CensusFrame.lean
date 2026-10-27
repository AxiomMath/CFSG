module

public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelOfLin
public import CFSG.LocalAnalysis.StandardType.GGQ2CensusBridge
public import CFSG.LocalAnalysis.StandardType.GGQ2CensusFrameReal
import CFSG.LocalAnalysis.StandardType.GGQTwoNoTwoNodeKSide

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

structure GGQ2LinOn (p : ℕ) [Fact p.Prime] (V : Type) [AddCommGroup V] [Module (ZMod p) V] where
  ι : Type
  [instFintype : Fintype ι]
  [instDecEq : DecidableEq ι]
  coxeter : CoxeterMatrix ι
  cartan : Matrix ι ι ℤ
  coroot : ι → V
  root : ι → Dual (ZMod p) V
  a : ι
  b : ι
  a_ne_b : a ≠ b
  a_leaf : ∃! c, c ≠ a ∧ cartan a c ≠ 0
  isWeyl : GGIsWeylMatrix coxeter
  isCartan : GGIntCartan coxeter cartan
  pairing : ∀ i j, root i (coroot j) = (cartan i j : ZMod p)

attribute [instance] GGQ2LinOn.instFintype GGQ2LinOn.instDecEq

@[expose, reducible] def GGQ2LinOn.toLin {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (W : GGQ2LinOn p V) : GGQ2Lin p where
  ι := W.ι
  coxeter := W.coxeter
  cartan := W.cartan
  V := V
  coroot := W.coroot
  root := W.root
  a := W.a
  b := W.b
  a_ne_b := W.a_ne_b
  a_leaf := W.a_leaf
  isWeyl := W.isWeyl
  isCartan := W.isCartan
  pairing := W.pairing

@[expose] def Candidate (R : RawFrameData) (vx : R.V) (j : R.Code) (z : R.V) (k : R.Code) :
    Prop :=
  R.admissible k ∧ R.occurs (Submodule.span (ZMod 3) {z}) k ∧
    R.cent k = Submodule.span (ZMod 3) {z} ∧ R.normalizerGroup j ≤ R.normalizerGroup k ∧
    vx ∉ R.cent k

@[expose] def CommonWitness (R : RawFrameData) (vx z : R.V) (ℓ k : R.Code) : Prop :=
  ∃ W : GGQ2LinOn 3 R.V,
    W.toLin.parab {i | i ≠ W.a} = R.normalizerGroup ℓ ∧
    W.toLin.parab {i | i ≠ W.b} = R.normalizerGroup k ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {vx}) ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {z})

@[expose] def AmbientWitness (R : RawFrameData) (vx z : R.V) (ℓ k : R.Code) : Prop :=
  ∃ W : GGQ2LinOn 3 R.V,
    W.toLin.parab {i | i ≠ W.a} = R.normalizerGroup ℓ ∧
    W.toLin.simpleRefl W.a ∈ R.normalizerGroup ℓ ⊔ R.normalizerGroup k ∧
    (∀ v, (∀ i ∈ {i | i ≠ W.a}, W.root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {vx}) ∧
    (∀ i, i ≠ W.a → i ≠ W.b → W.root i z = 0) ∧
    W.toLin.Basis ∧ ((W.cartan.det : ℤ) : ZMod 3) ≠ 0 ∧
    ((W.cartan.submatrix (fun i : {i // i ≠ W.a} => (i : W.ι))
      (fun i : {i // i ≠ W.a} => (i : W.ι))).det : ZMod 3) ≠ 0

@[expose] def CensusCases (R : RawFrameData) : Prop :=
  ∀ vx : R.V, vx ≠ 0 →
  ∀ ℓ : R.Code, R.admissible ℓ → R.occurs (Submodule.span (ZMod 3) {vx}) ℓ →
    R.cent ℓ = Submodule.span (ZMod 3) {vx} → vx ∉ R.inside ℓ →
  ∀ U : Submodule (ZMod 3) R.V, finrank (ZMod 3) U = 2 → vx ∈ U →
  ∀ j : R.Code, R.admissible j → R.occurs U j → R.cent j = U → R.inside j ≤ R.inside ℓ →
    R.normalizerGroup j ≤ R.normalizerGroup ℓ →
    (∃ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} ∧ ∃ k, Candidate R vx j z k ∧
        CommonWitness R vx z ℓ k) ∨
    (∃ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} ∧ ∃ k, Candidate R vx j z k ∧
        z ∉ R.inside k ∧ TwoNodeLabels 3 (R.label k) (R.label j)) ∨
    TwoNodeLabels 3 (R.label ℓ) (R.label j) ∨
    (∀ z ∈ U, z ∉ Submodule.span (ZMod 3) {vx} → ∀ k, Candidate R vx j z k →
        R.inside j ≤ R.inside k →
        TwoNodeLabels 3 (R.label k) (R.label j) ∨ AmbientWitness R vx z ℓ k)

@[expose] def AmbModelAtFrame (R : RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 → GGQTwoI1 Bs D J → x ∉ L → ∀ [Fact p.Prime],
    (¬ ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ((GGQTwoTwoNodeRowAt p L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt p K J ∧ y ∉ K))) →
    (∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      ¬ Nonempty (GGQTwoModel p Bs x y D L J K)) →
    ∀ {y : G} {K : Subgroup G}, GGNbr p B x D J y K →
      ¬ GGQTwoTwoNodeRowAt p L J → ¬ GGQTwoTwoNodeRowAt p K J →
      GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) →
      ActualFrame (ggG0 p B x L D J) Bs R →
        ∃ M : GGQTwoAmbModel p Bs x y L (L ⊔ K), GGQTwoAmbBasis M ∧
          ((M.cartan.det : ℤ) : ZMod p) ≠ 0 ∧
          ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
            (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod p) ≠ 0

theorem ambModelFromFrameInput_of_at (catalogue : FrameKind → RawFrameData)
    (h : ∀ kind, AmbModelAtFrame (catalogue kind)) : AmbModelFromFrameInput catalogue := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ hrow hno y K hnb hr1 hr2 hW kind hF
  exact h kind hS hp hI1 hxL hrow hno hnb hr1 hr2 hW hF

theorem ambModelFromFrameInput_of_halves (catalogue : FrameKind → RawFrameData)
    (hcl : ∀ kind, IsClassical kind → AmbModelAtFrame (catalogue kind))
    (hex : ∀ mode, AmbModelAtFrame (catalogue (.exceptional mode))) :
    AmbModelFromFrameInput catalogue := by
  refine ambModelFromFrameInput_of_at catalogue fun kind => ?_
  cases kind with
  | exceptional mode => exact hex mode
  | _ => exact hcl _ (by simp [IsClassical])

private theorem ggQ2CensusFrame_exists_code {G : Type} [Group G] {H E : Subgroup G}
    {R : RawFrameData} (real : Realization H E R) {A : Subgroup G} (hA : A ≤ E) {X : Subgroup G}
    (hX : IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G))) :
    ∃ c : R.Code, R.admissible c ∧ R.occurs (ggLinImage (p := 3) real.coord A) c ∧
      real.component c = X := by
  obtain ⟨c, hc, hocc, hXc⟩ := (real.occurs_iff A hA X).mp hX
  exact ⟨c, hc, hocc, hXc.symm⟩

private theorem ggQ2CensusFrame_zpowers_ne {G : Type} [Group G] {x y : G} {D : Subgroup G}
    (hD : D = Subgroup.closure {x, y}) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hcard : Nat.card D = 9) :
    y ∉ Subgroup.zpowers x ∧ x ∉ Subgroup.zpowers y := by
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have h1 : y ∉ Subgroup.zpowers x := by
    intro h
    have hDx : D = Subgroup.zpowers x := by
      rw [hD, closure_pair_eq_sup, sup_eq_left.mpr (Subgroup.zpowers_le.mpr h)]
    rw [hDx, Nat.card_zpowers, hox] at hcard
    norm_num at hcard
  refine ⟨h1, ?_⟩
  intro h
  have hDy : D = Subgroup.zpowers y := by
    rw [hD, closure_pair_eq_sup, sup_eq_right.mpr (Subgroup.zpowers_le.mpr h)]
  rw [hDy, Nat.card_zpowers, hoy] at hcard
  norm_num at hcard

theorem ggQ2CensusFrame_codeL {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hBs : GGBstar 3 B Bs) (hx1 : x ≠ 1) (hxBs : x ∈ Bs)
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S)
    (hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G))) :
    ∃ ℓ : R.Code, R.admissible ℓ ∧
      R.occurs ((ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) ℓ ∧
      R.cent ℓ = (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∧
      real.component ℓ = L ∧
      (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∈ R.inside ℓ ↔ x ∈ L) := by
  have hEq : Subgroup.centralizer (Subgroup.zpowers x : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hX : IsComponentOf L
      (ggG0 3 B x L D J ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set G)) := by
    rw [hEq]
    exact hLcomp.of_le_of_le (le_inf (le_ggG0_left 3 B x L D J) hLcomp.1) inf_le_right
  obtain ⟨ℓ, hℓadm, hℓocc₀, hℓcomp⟩ :=
    ggQ2CensusFrame_exists_code real (Subgroup.zpowers_le.mpr hxBs) hX
  have hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs.2.1 hxBs hx1 hLcomp.1 hcyc
  have hspan : (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
      = ggLinImage (p := 3) real.coord (Subgroup.zpowers x) :=
    span_singleton_eq_ggLinImage real.coord hxBs
  refine ⟨ℓ, hℓadm, ?_, ?_, hℓcomp, ?_⟩
  · rw [hspan]; exact hℓocc₀
  · rw [← real.cent_eq ℓ hℓadm, hℓcomp, ← ggLinImage_inf_left (p := 3) real.coord
      (Subgroup.centralizer (L : Set G)), hker, hspan]
  · rw [← real.inside_eq ℓ hℓadm, hℓcomp, ofMul_mem_ggLinImage]

private theorem ggQ2CensusFrame_codeJ {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hI1 : GGQTwoI1 Bs D J) (hDJ : LargeEvenStdSub 3 B x L D J) (hDleBs : D ≤ Bs)
    (hJcomp : IsComponentOf J (ggG0 3 B x L D J ⊓ Subgroup.centralizer (D : Set G))) :
    ∃ j : R.Code, R.admissible j ∧ R.occurs (ggLinImage (p := 3) real.coord D) j ∧
      R.cent j = ggLinImage (p := 3) real.coord D ∧ real.component j = J := by
  obtain ⟨j, hjadm, hjocc, hjcomp⟩ := ggQ2CensusFrame_exists_code real hDleBs hJcomp
  have hBsJ : Bs ⊓ Subgroup.centralizer (J : Set G) = D := by
    refine le_antisymm ?_ ?_
    · intro b hb
      exact hI1 b hb.1 (fun j' hj' => (Subgroup.mem_centralizer_iff.mp hb.2 j' hj').symm)
    · intro d hd
      refine Subgroup.mem_inf.mpr ⟨hDleBs hd, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro j' hj'
      exact (Subgroup.mem_centralizer_iff.mp (hDJ.1.2.2.2.2.2.1.1 hj').2 d hd).symm
  refine ⟨j, hjadm, hjocc, ?_, hjcomp⟩
  rw [← real.cent_eq j hjadm, hjcomp, ← ggLinImage_inf_left (p := 3) real.coord
    (Subgroup.centralizer (J : Set G)), hBsJ]

private theorem ggQ2CensusFrame_nbrData {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hxBs : x ∈ Bs) {j : R.Code} {z : R.V} {k : R.Code}
    (hcand : Candidate R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) j z k)
    (hzx : z ∉ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)))
    (hzD : z ∈ ggLinImage (p := 3) real.coord D) :
    ∃ b : ↥Bs, (b : G) ∈ D ∧ (b : G) ∉ Subgroup.zpowers x ∧
      real.coord (Additive.ofMul b) = z ∧
      R.occurs (ggLinImage (p := 3) real.coord (Subgroup.zpowers (b : G))) k ∧
      IsComponentOf (real.component k)
        (ggG0 3 B x L D J ⊓ Subgroup.centralizer ({(b : G)} : Set G)) := by
  set b : ↥Bs := Additive.toMul (real.coord.symm z) with hbdef
  have hvecz : real.coord (Additive.ofMul b) = z := by
    rw [hbdef, ofMul_toMul, AddEquiv.apply_symm_apply]
  have hbD : (b : G) ∈ D := by
    rw [← ofMul_mem_ggLinImage (p := 3) real.coord D b, hvecz]
    exact hzD
  have hbz : (b : G) ∉ Subgroup.zpowers x := by
    intro hb
    apply hzx
    rw [← hvecz, span_singleton_eq_ggLinImage (p := 3) real.coord hxBs, ofMul_mem_ggLinImage]
    exact hb
  have hspan : ggLinImage (p := 3) real.coord (Subgroup.zpowers (b : G)) = (ZMod 3) ∙ z := by
    rw [← span_singleton_eq_ggLinImage (p := 3) real.coord b.2, hvecz]
  have hocc : R.occurs (ggLinImage (p := 3) real.coord (Subgroup.zpowers (b : G))) k := by
    rw [hspan]; exact hcand.2.1
  have hXcomp : IsComponentOf (real.component k)
      (ggG0 3 B x L D J ⊓ Subgroup.centralizer ({(b : G)} : Set G)) := by
    have h1 : IsComponentOf (real.component k)
        (ggG0 3 B x L D J ⊓ Subgroup.centralizer (Subgroup.zpowers (b : G) : Set G)) :=
      (real.occurs_iff (Subgroup.zpowers (b : G)) (Subgroup.zpowers_le.mpr b.2)
        (real.component k)).mpr ⟨k, hcand.1, hocc, rfl⟩
    have hEq : Subgroup.centralizer (Subgroup.zpowers (b : G) : Set G)
        = Subgroup.centralizer ({(b : G)} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rwa [hEq] at h1
  exact ⟨b, hbD, hbz, hvecz, hocc, hXcomp⟩

private theorem ggQ2CensusFrame_nbrNbr {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hmov : RawInsideMoved R) (hLB : GGLBalanceInput) (hI : GGThmIHyp 3 B x L)
    (hDJ : LargeEvenStdSub 3 B x L D J) (hpJ : 3 ∣ Nat.card J) (hBs : GGBstar 3 B Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) (hxBs : x ∈ Bs)
    {j : R.Code} (hjadm : R.admissible j) (hjcomp : real.component j = J) {z : R.V}
    {k : R.Code} {b : ↥Bs}
    (hcand : Candidate R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) j z k)
    (hbD : (b : G) ∈ D) (hbz : (b : G) ∉ Subgroup.zpowers x)
    (hocc : R.occurs (ggLinImage (p := 3) real.coord (Subgroup.zpowers (b : G))) k)
    (hXcomp : IsComponentOf (real.component k)
      (ggG0 3 B x L D J ⊓ Subgroup.centralizer ({(b : G)} : Set G))) :
    GGNbr 3 B x D J (b : G) (real.component k) := by
  have hcomm : ∀ a ∈ Bs, ∀ c ∈ Bs, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (hBs.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  have hxN : x ∈ Subgroup.normalizer (real.component k : Set G) :=
    Realization.mem_normalizer_component real hmov hcomm (Subgroup.zpowers_le.mpr b.2)
      hcand.1 hocc hxBs (hBsN hxBs)
  have hxC : x ∉ Subgroup.centralizer (real.component k : Set G) := by
    intro hx
    refine hcand.2.2.2.2 ?_
    rw [← real.cent_eq k hcand.1, ofMul_mem_ggLinImage]
    exact hx
  have hpX : 3 ∣ Nat.card (real.component k) := by
    obtain ⟨b0, hb0E, hb0X, hb0ne⟩ := Realization.exists_mem_component_ne_one real hmov hcand.1
    have h3 : b0 ^ 3 = 1 := hBs.2.1.2 b0 hb0E
    have ho : orderOf b0 = 3 := orderOf_eq_prime h3 hb0ne
    have hdvd : orderOf b0 ∣ Nat.card (real.component k) :=
      Subgroup.orderOf_dvd_natCard (real.component k) hb0X
    rwa [ho] at hdvd
  have hJX : ⁅J, real.component k⁆ ≠ ⊥ := by
    have h := Realization.commutator_component_ne_bot real hmov hjadm hcand.1 hcand.2.2.2.1
    rwa [hjcomp] at h
  exact ggNbr_of_isComponentOf_ggG0_inf_centralizer hLB hI hDJ hpJ hbD hbz hXcomp hxN hxC hpX hJX

theorem ggQ2CensusFrame_nbr {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hmov : RawInsideMoved R) (hLB : GGLBalanceInput) (hI : GGThmIHyp 3 B x L)
    (hDJ : LargeEvenStdSub 3 B x L D J) (hpJ : 3 ∣ Nat.card J) (hBs : GGBstar 3 B Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G)) (hxBs : x ∈ Bs)
    {j : R.Code} (hjadm : R.admissible j) (hjcomp : real.component j = J) {z : R.V}
    {k : R.Code}
    (hcand : Candidate R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) j z k)
    (hzx : z ∉ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)))
    (hzD : z ∈ ggLinImage (p := 3) real.coord D) :
    ∃ b : ↥Bs, (b : G) ∈ D ∧ (b : G) ∉ Subgroup.zpowers x ∧
      real.coord (Additive.ofMul b) = z ∧
      GGNbr 3 B x D J (b : G) (real.component k) := by
  obtain ⟨b, hbD, hbz, hvecz, hocc, hXcomp⟩ :=
    ggQ2CensusFrame_nbrData real hxBs hcand hzx hzD
  exact ⟨b, hbD, hbz, hvecz,
    ggQ2CensusFrame_nbrNbr real hmov hLB hI hDJ hpJ hBs hBsN hxBs hjadm hjcomp hcand
      hbD hbz hocc hXcomp⟩

theorem ggQ2CensusFrame_codes {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hS : GGQTwoSetting 3 B Bs x L D J) (hI1 : GGQTwoI1 Bs D J) (hxBs : x ∈ Bs) :
    ∃ ℓ j : R.Code,
      R.admissible ℓ ∧
      R.occurs ((ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) ℓ ∧
      R.cent ℓ = (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∧
      real.component ℓ = L ∧
      (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∈ R.inside ℓ ↔ x ∈ L) ∧
      R.admissible j ∧ R.occurs (ggLinImage (p := 3) real.coord D) j ∧
      R.cent j = ggLinImage (p := 3) real.coord D ∧ real.component j = J ∧
      R.inside j ≤ R.inside ℓ ∧ R.normalizerGroup j ≤ R.normalizerGroup ℓ ∧
      real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ≠ 0 ∧
      finrank (ZMod 3) (ggLinImage (p := 3) real.coord D) = 2 ∧
      real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∈ ggLinImage (p := 3) real.coord D := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hBs : GGBstar 3 B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hSstar : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hLcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hSstar.2.2.2.1
  have hDleBs : D ≤ Bs := hDJ.1.1.trans hBs.1
  have hJcomp : IsComponentOf J (ggG0 3 B x L D J ⊓ Subgroup.centralizer (D : Set G)) :=
    ggQ2_isComponentOf_jointCentralizer hS
  have hJL : J ≤ L := hDJ.1.2.2.2.2.2.1.1.trans inf_le_left
  obtain ⟨ℓ, hℓadm, hℓocc, hℓcent, hℓcomp, hvxℓ⟩ :=
    ggQ2CensusFrame_codeL real hBs hx1 hxBs hSstar.2.2.2.2 hLcomp
  obtain ⟨j, hjadm, hjocc, hjcent, hjcomp⟩ :=
    ggQ2CensusFrame_codeJ real hI1 hDJ hDleBs hJcomp
  have hinsj : R.inside j = ggLinImage (p := 3) real.coord J := by
    rw [← real.inside_eq j hjadm, hjcomp]
  have hinsℓ : R.inside ℓ = ggLinImage (p := 3) real.coord L := by
    rw [← real.inside_eq ℓ hℓadm, hℓcomp]
  have hins : R.inside j ≤ R.inside ℓ := by
    rw [hinsj, hinsℓ]; exact ggLinImage_mono (p := 3) real.coord hJL
  have hnorm : R.normalizerGroup j ≤ R.normalizerGroup ℓ := by
    rw [← real.normalizer_eq j hjadm, ← real.normalizer_eq ℓ hℓadm, hjcomp, hℓcomp]
    exact Subgroup.map_mono (ggAutomizer_mono Bs hJL)
  have hUfin : finrank (ZMod 3) (ggLinImage (p := 3) real.coord D) = 2 :=
    finrank_ggLinImage_of_card (p := 3) real.coord hDleBs (n := 2) hDJ.1.2.2.1
  have hxU : real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
      ∈ ggLinImage (p := 3) real.coord D := by
    rw [ofMul_mem_ggLinImage]; exact hDJ.1.2.2.2.1
  have hvx0 : real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) = 0 := by
      rw [← real.coord.injective.eq_iff, h0, map_zero]
    have h2 : (⟨x, hxBs⟩ : ↥Bs) = 1 := by simpa using Additive.ofMul.injective h1
    exact hx1 (by simpa using congrArg Subtype.val h2)
  exact ⟨ℓ, j, hℓadm, hℓocc, hℓcent, hℓcomp, hvxℓ, hjadm, hjocc, hjcent, hjcomp, hins, hnorm,
    hvx0, hUfin, hxU⟩

theorem ggQ2CensusFrame_setup {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) (hxBs : x ∈ Bs) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) :
    y ∉ Subgroup.zpowers x ∧ x ∉ Subgroup.zpowers y ∧ y ∈ Bs ∧
      ∃ ℓ j : R.Code,
        R.admissible ℓ ∧
        R.occurs ((ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) ℓ ∧
        R.cent ℓ = (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∧
        real.component ℓ = L ∧
        (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∈ R.inside ℓ ↔ x ∈ L) ∧
        R.admissible j ∧ R.occurs (ggLinImage (p := 3) real.coord D) j ∧
        R.cent j = ggLinImage (p := 3) real.coord D ∧ real.component j = J ∧
        R.inside j ≤ R.inside ℓ ∧ R.normalizerGroup j ≤ R.normalizerGroup ℓ ∧
        real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ≠ 0 ∧
        finrank (ZMod 3) (ggLinImage (p := 3) real.coord D) = 2 ∧
        real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
          ∈ ggLinImage (p := 3) real.coord D := by
  have hBs : GGBstar 3 B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hx1 : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hyBs : y ∈ Bs := hBs.1 hnb.1.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  have hcardD : Nat.card D = 9 := by rw [hDJ.1.2.2.1]; norm_num
  obtain ⟨hyx, hxy⟩ := ggQ2CensusFrame_zpowers_ne hnb.2.1 hx1 hy1
    (hBs.2.1.2 x hxBs) (hBs.2.1.2 y hyBs) hcardD
  exact ⟨hyx, hxy, hyBs, ggQ2CensusFrame_codes real hS hI1 hxBs⟩

theorem ggQ2CensusFrame_commonModel {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hmov : RawInsideMoved R) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hS : GGQTwoSetting 3 B Bs x L D J) (hxBs : x ∈ Bs)
    {ℓ j : R.Code} (hℓadm : R.admissible ℓ) (hℓcomp : real.component ℓ = L)
    (hjadm : R.admissible j) (hjcomp : real.component j = J) {z : R.V} {k : R.Code}
    (hcand : Candidate R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) j z k)
    (hzx : z ∉ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)))
    (hzU : z ∈ ggLinImage (p := 3) real.coord D) (hW : CommonWitness R
      (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) z ℓ k) :
    ∃ (y' : G) (K' : Subgroup G), GGNbr 3 B x D J y' K' ∧
      Nonempty (GGQTwoModel 3 Bs x y' D L J K') := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hBs : GGBstar 3 B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hpJ : 3 ∣ Nat.card J := hP G 3 B x L D J hI hDJ
  have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.2.2
  obtain ⟨b, hbD, hbz, hvecz, hnbr⟩ :=
    ggQ2CensusFrame_nbr real hmov hLB hI hDJ hpJ hBs hBsN hxBs hjadm hjcomp hcand hzx hzU
  obtain ⟨W, hWL, hWK, hfixx, hfixy⟩ := hW
  have hLlin : (ggAutomizer L Bs).map (ggLin (p := 3) real.coord)
      = W.toLin.parab {i | i ≠ W.a} := by
    rw [hWL, ← real.normalizer_eq ℓ hℓadm, hℓcomp]
  have hKlin : (ggAutomizer (real.component k) Bs).map (ggLin (p := 3) real.coord)
      = W.toLin.parab {i | i ≠ W.b} := by
    rw [hWK, ← real.normalizer_eq k hcand.1]
  have hfixy' : ∀ v, (∀ i ∈ {i | i ≠ W.b}, W.root i v = 0) ↔
      v ∈ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨(b : G), b.2⟩ : ↥Bs)) := by
    simpa [hvecz] using hfixy
  exact ⟨b, real.component k, hnbr,
    ⟨GGQ2Lin.toModel (p := 3) (by norm_num) W.toLin real.coord hxBs b.2 hLlin hKlin
      hfixx hfixy'⟩⟩

private theorem ggQ2CensusFrame_caseA {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hmov : RawInsideMoved R) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hS : GGQTwoSetting 3 B Bs x L D J) (hxBs : x ∈ Bs) {y : G} {K : Subgroup G}
    (hno : ∀ (y' : G) (K' : Subgroup G), GGNbr 3 B x D J y' K' →
      ¬ Nonempty (GGQTwoModel 3 Bs x y' D L J K'))
    {ℓ j : R.Code} (hℓadm : R.admissible ℓ) (hℓcomp : real.component ℓ = L)
    (hjadm : R.admissible j) (hjcomp : real.component j = J) {z : R.V} {k : R.Code}
    (hcand : Candidate R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) j z k)
    (hzx : z ∉ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)))
    (hzU : z ∈ ggLinImage (p := 3) real.coord D) (hW : CommonWitness R
      (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) z ℓ k) :
    ∃ M : GGQTwoAmbModel 3 Bs x y L (L ⊔ K), GGQTwoAmbBasis M ∧
      ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 ∧
      ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod 3) ≠ 0 := by
  obtain ⟨y', K', hnbr, hM⟩ := ggQ2CensusFrame_commonModel real hmov hLB hP hS hxBs hℓadm hℓcomp
    hjadm hjcomp hcand hzx hzU hW
  exact (hno y' K' hnbr hM).elim

private theorem ggQ2CensusFrame_caseB {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hmov : RawInsideMoved R) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hxBs : x ∈ Bs) {y : G} {K : Subgroup G}
    (hrow : ¬ ∃ (y' : G) (K' : Subgroup G), GGNbr 3 B x D J y' K' ∧
      ((GGQTwoTwoNodeRowAt 3 L J ∧ x ∉ L) ∨ (GGQTwoTwoNodeRowAt 3 K' J ∧ y' ∉ K')))
    {j : R.Code} (hjadm : R.admissible j)
    (hjcomp : real.component j = J) {z : R.V} {k : R.Code}
    (hcand : Candidate R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) j z k)
    (hzx : z ∉ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)))
    (hzU : z ∈ ggLinImage (p := 3) real.coord D)
    (hzk : z ∉ R.inside k) (htwo : TwoNodeLabels 3 (R.label k) (R.label j)) :
    ∃ M : GGQTwoAmbModel 3 Bs x y L (L ⊔ K), GGQTwoAmbBasis M ∧
      ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 ∧
      ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod 3) ≠ 0 := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hBs : GGBstar 3 B Bs := hS.1.1.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hpJ : 3 ∣ Nat.card J := hP G 3 B x L D J hI hDJ
  have hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hS.1.2.2.2.2
  obtain ⟨b, hbD, hbz, hvecz, hnbr⟩ :=
    ggQ2CensusFrame_nbr real hmov hLB hI hDJ hpJ hBs hBsN hxBs hjadm hjcomp hcand hzx hzU
  have hrowK : GGQTwoTwoNodeRowAt 3 (real.component k) J :=
    (markedRow_iff 3 (real.component k) J).mpr
      ⟨R.label k, R.label j, real.marked k hcand.1, hjcomp ▸ real.marked j hjadm, htwo⟩
  have hbX : (b : G) ∉ real.component k := by
    intro hb
    refine hzk ?_
    rw [← real.inside_eq k hcand.1, ← hvecz, ofMul_mem_ggLinImage]
    exact hb
  exact (hrow ⟨(b : G), real.component k, hnbr, Or.inr ⟨hrowK, hbX⟩⟩).elim

theorem ggQ2CensusFrame_caseKCode {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hS : GGQTwoSetting 3 B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hyBs : y ∈ Bs) {j : R.Code} (hjadm : R.admissible j) (hjcomp : real.component j = J) :
    ∃ k : R.Code, R.admissible k ∧
      R.occurs ((ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) k ∧
      R.cent k = (ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ∧
      real.component k = K ∧ R.inside j ≤ R.inside k := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  have hKc : IsComponentOf K (Subgroup.centralizer ({y} : Set G)) :=
    (isComponentOf_of_isNeighborOf hI.2.2.2.2.2.2.2 (isNeighborOf_of_ggNbr hDJ hnb)).1
  have hKcomp : IsComponentOf K
      (ggG0 3 B x L D J ⊓ Subgroup.centralizer (Subgroup.zpowers y : Set G)) := by
    have h1 : IsComponentOf K (ggG0 3 B x L D J ⊓ Subgroup.centralizer ({y} : Set G)) :=
      hKc.of_le_of_le (le_inf (le_ggG0_of_ggNbr hnb) hKc.1) inf_le_right
    have hEq : Subgroup.centralizer (Subgroup.zpowers y : Set G)
        = Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    rwa [← hEq] at h1
  obtain ⟨k, hkadm, hkocc₀, hkcomp⟩ :=
    ggQ2CensusFrame_exists_code real (Subgroup.zpowers_le.mpr hyBs) hKcomp
  have hBsK : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y :=
    ggQ2_bstar_centralizer_nbr_eq_zpowers hLB hP hS hI1 hnb
  have hspanY : (ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
      = ggLinImage (p := 3) real.coord (Subgroup.zpowers y) :=
    span_singleton_eq_ggLinImage real.coord hyBs
  have hkocc : R.occurs ((ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) k := by
    rw [hspanY]; exact hkocc₀
  have hkcent : R.cent k = (ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) := by
    rw [← real.cent_eq k hkadm, hkcomp, ← ggLinImage_inf_left (p := 3) real.coord
      (Subgroup.centralizer (K : Set G)), hBsK, hspanY]
  have hinsk : R.inside k = ggLinImage (p := 3) real.coord K := by
    rw [← real.inside_eq k hkadm, hkcomp]
  have hinsj : R.inside j = ggLinImage (p := 3) real.coord J := by
    rw [← real.inside_eq j hjadm, hjcomp]
  refine ⟨k, hkadm, hkocc, hkcent, hkcomp, ?_⟩
  rw [hinsj, hinsk]
  exact ggLinImage_mono (p := 3) real.coord (le_of_ggNbr hLB hI hDJ
    (hP G 3 B x L D J hI hDJ) hnb)

theorem ggQ2CensusFrame_caseDCand {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hS : GGQTwoSetting 3 B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) (hxBs : x ∈ Bs) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hyx : y ∉ Subgroup.zpowers x)
    (hxy : x ∉ Subgroup.zpowers y) (hyBs : y ∈ Bs)
    {j : R.Code} (hjadm : R.admissible j) (hjcomp : real.component j = J) :
    ∃ k : R.Code, R.admissible k ∧
      R.occurs ((ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) k ∧
      R.cent k = (ZMod 3) ∙ real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ∧
      real.component k = K ∧ R.inside j ≤ R.inside k ∧
      Candidate R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) j
        (real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) k ∧
      real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) ∈ ggLinImage (p := 3) real.coord D ∧
      real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
        ∉ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by
  have hI : GGThmIHyp 3 B x L := hS.1.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hS.1.1.2.2
  obtain ⟨k, hkadm, hkocc, hkcent, hkcomp, hinsJK⟩ :=
    ggQ2CensusFrame_caseKCode real hLB hP hS hI1 hnb hyBs hjadm hjcomp
  have hvyx : real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
      ∉ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by
    intro hmem
    apply hyx
    rw [← ofMul_mem_ggLinImage (p := 3) real.coord (Subgroup.zpowers x) (⟨y, hyBs⟩ : ↥Bs),
      ← span_singleton_eq_ggLinImage (p := 3) real.coord hxBs]
    exact hmem
  have hvxK : real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ∉ R.cent k := by
    rw [hkcent]
    intro hmem
    apply hxy
    rw [← ofMul_mem_ggLinImage (p := 3) real.coord (Subgroup.zpowers y) (⟨x, hxBs⟩ : ↥Bs),
      ← span_singleton_eq_ggLinImage (p := 3) real.coord hyBs]
    exact hmem
  have hnormjk : R.normalizerGroup j ≤ R.normalizerGroup k := by
    rw [← real.normalizer_eq j hjadm, ← real.normalizer_eq k hkadm, hjcomp, hkcomp]
    exact Subgroup.map_mono (ggAutomizer_mono Bs (le_of_ggNbr hLB hI hDJ
      (hP G 3 B x L D J hI hDJ) hnb))
  have hvyU : real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))
      ∈ ggLinImage (p := 3) real.coord D := by
    rw [ofMul_mem_ggLinImage, hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  exact ⟨k, hkadm, hkocc, hkcent, hkcomp, hinsJK,
    ⟨hkadm, hkocc, hkcent, hnormjk, hvxK⟩, hvyU, hvyx⟩

private theorem ggQ2CensusFrame_caseDAmb {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x y : G} {L D J K : Subgroup G} {R : RawFrameData}
    (real : Realization (ggG0 3 B x L D J) Bs R) (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    {ℓ k : R.Code} (hℓadm : R.admissible ℓ) (hℓcomp : real.component ℓ = L)
    (hkadm : R.admissible k) (hkcomp : real.component k = K)
    (hamb : AmbientWitness R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)))
      (real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) ℓ k) :
    ∃ M : GGQTwoAmbModel 3 Bs x y L (L ⊔ K), GGQTwoAmbBasis M ∧
      ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 ∧
      ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod 3) ≠ 0 := by
  obtain ⟨W, hWL, hWa, hfix, hyJ, hB, hdet, hdetA⟩ := hamb
  have hsubℓ : ggAutomizer (real.component ℓ) Bs = ggAutomizer L Bs := by rw [hℓcomp]
  have hsubk : ggAutomizer (real.component k) Bs = ggAutomizer K Bs := by rw [hkcomp]
  have hmem : W.toLin.simpleRefl W.a ∈
      (ggAutomizer L Bs).map (ggLin (p := 3) real.coord) ⊔
        (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) := by
    rw [← hsubℓ, ← hsubk, real.normalizer_eq ℓ hℓadm, real.normalizer_eq k hkadm]
    exact hWa
  exact GGQ2Lin.exists_ambModel (p := 3) (by norm_num) W.toLin real.coord hxBs hyBs
    (by rw [hWL, ← real.normalizer_eq ℓ hℓadm, hℓcomp])
    (mem_map_ggAutomizer_sup (p := 3) real.coord hmem) hfix hyJ hB hdet hdetA

private theorem ggQ2CensusFrame_caseD {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {R : RawFrameData} (real : Realization (ggG0 3 B x L D J) Bs R)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hS : GGQTwoSetting 3 B Bs x L D J)
    (hI1 : GGQTwoI1 Bs D J) (hxBs : x ∈ Bs) {y : G} {K : Subgroup G}
    (hnb : GGNbr 3 B x D J y K) (hr2 : ¬ GGQTwoTwoNodeRowAt 3 K J)
    (hyx : y ∉ Subgroup.zpowers x) (hxy : x ∉ Subgroup.zpowers y) (hyBs : y ∈ Bs)
    {ℓ j : R.Code} (hℓadm : R.admissible ℓ) (hℓcomp : real.component ℓ = L)
    (hjadm : R.admissible j) (hjcomp : real.component j = J)
    (hres : ∀ z ∈ ggLinImage (p := 3) real.coord D,
      z ∉ (ZMod 3) ∙ real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) →
      ∀ k, Candidate R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) j z k →
      R.inside j ≤ R.inside k →
      TwoNodeLabels 3 (R.label k) (R.label j) ∨
        AmbientWitness R (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) z ℓ k) :
    ∃ M : GGQTwoAmbModel 3 Bs x y L (L ⊔ K), GGQTwoAmbBasis M ∧
      ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 ∧
      ((M.cartan.submatrix (fun i : {k // k ≠ M.a} => (i : M.ι))
        (fun i : {k // k ≠ M.a} => (i : M.ι))).det : ZMod 3) ≠ 0 := by
  obtain ⟨k, hkadm, hkocc, hkcent, hkcomp, hinsJK, hcandK, hvyU, hvyx⟩ :=
    ggQ2CensusFrame_caseDCand real hLB hP hS hI1 hxBs hnb hyx hxy hyBs hjadm hjcomp
  rcases hres (real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) hvyU hvyx k hcandK hinsJK with
    htwo | hamb
  · exact (hr2 ((markedRow_iff 3 K J).mpr
      ⟨R.label k, R.label j, hkcomp ▸ real.marked k hkadm, hjcomp ▸ real.marked j hjadm,
        htwo⟩)).elim
  · exact ggQ2CensusFrame_caseDAmb real hxBs hyBs hℓadm hℓcomp hkadm hkcomp hamb

theorem ambModelAtFrame_of_censusCases (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {R : RawFrameData} (hmov : RawInsideMoved R) (hC : CensusCases R) : AmbModelAtFrame R := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL _ hrow hno y K hnb hr1 hr2 _ hF
  subst hp
  obtain ⟨real⟩ := hF
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hS.1.1.1.2.2.2.2.2.2.1.2.1
  obtain ⟨hyx, hxy, hyBs, ℓ, j, hℓadm, hℓocc, hℓcent, hℓcomp, hvxℓ, hjadm, hjocc, hjcent,
    hjcomp, hins, hnorm, hvx0, hUfin, hxU⟩ :=
    ggQ2CensusFrame_setup real hS hI1 hxBs hnb
  rcases hC (real.coord (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))) hvx0 ℓ hℓadm hℓocc hℓcent
    (fun h => hxL (hvxℓ.mp h))
    (ggLinImage (p := 3) real.coord D) hUfin hxU j hjadm hjocc hjcent hins hnorm with
    ⟨z, hzU, hzx, k, hcand, hW⟩ | ⟨z, hzU, hzx, k, hcand, hzk, htwo⟩ | htwo | hres
  · exact ggQ2CensusFrame_caseA real hmov hLB hP hS hxBs hno hℓadm hℓcomp hjadm hjcomp
      hcand hzx hzU hW
  · exact ggQ2CensusFrame_caseB real hmov hLB hP hS hxBs hrow hjadm hjcomp hcand hzx hzU
      hzk htwo
  · exact (hr1 ((markedRow_iff 3 L J).mpr
      ⟨R.label ℓ, R.label j, hℓcomp ▸ real.marked ℓ hℓadm, hjcomp ▸ real.marked j hjadm,
        htwo⟩)).elim
  · exact ggQ2CensusFrame_caseD real hLB hP hS hI1 hxBs hnb hr2 hyx hxy hyBs hℓadm hℓcomp
      hjadm hjcomp hres
