module

public import CFSG.LocalAnalysis.WeakClosure81.PSpFourOrthogonalModel
public import CFSG.Quasithin.Background.E1RelativeGeneration
public import CFSG.CGT.Timmesfeld75.Sec4SixAux
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalComponentGeneration
public import CFSG.ClassicalGroups.Orthogonal.FourCentralizerFusion
public import CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveConjugate
public import CFSG.Quasithin.EmptyFaithful.PGLTwoPrimeElementaryGeneration
public import CFSG.GroupTheory.ConjNormalFaithful
public import CFSG.GroupTheory.PrescribedSylowNormalization
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Blueprint
open scoped commutatorElement

@[expose] def Asch4_12ASAboveFive : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (T : Subgroup Q) (p : ℕ),
    p.Prime → 5 < p →
    IsSimpleGroup ↥(CFSG.generalizedFitting Q) →
    (∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a) →
    LieModel ↥(CFSG.generalizedFitting Q) .PSp 2 p 1 →
    IsSylowIn 2 T ⊤ →
    CFSG.generalizedFitting Q ⊔ T = ⊤ →
    InE 1 (⊤ : Subgroup Q)

theorem almostSimpleData_conjNormal
    {Q : Type} [Group Q] [Finite Q] (T : Subgroup Q)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Q))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Q), a * b ≠ b * a)
    (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting Q ⊔ T = ⊤) :
    let F0 := CFSG.generalizedFitting Q
    let psi := MulAut.conjNormal (H := F0)
    AlmostSimpleData F0 psi.range (T.map psi) := by
  let F0 := CFSG.generalizedFitting Q
  letI : F0.Normal := by
    simpa [F0] using (CFSG.LocalCores.generalized_fitting_characteristic (G := Q)).2
  haveI : IsSimpleGroup F0 := by simpa [F0] using hs
  let psi : Q →* MulAut F0 := MulAut.conjNormal (H := F0)
  have hC : Subgroup.centralizer (F0 : Set Q) ≤ F0 := by
    simpa [F0] using CFSG.centralizer_generalizedFitting_le Q
  have hZ : Subgroup.center F0 = ⊥ := by
    simpa [F0] using (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := F0) hnab).2
  have hpsi : Function.Injective psi := by
    simpa [psi] using (Subgroup.conjNormal_injective_of_centralizer_le (N := F0) hC hZ)
  have hconj : psi.comp F0.subtype = (MulAut.conj : F0 →* MulAut F0) := by
    ext x y
    simpa [psi] using congrArg (fun f : MulAut F0 => (f : F0 → F0) y)
      (MulAut.conjNormal_val (H := F0) (h := x))
  have hinn : F0.map psi = innAutOf F0 := by
    rw [innAutOf, ← hconj, MonoidHom.range_comp, Subgroup.range_subtype]
  exact ⟨by rw [← hinn]; exact Subgroup.map_le_range psi F0,
    (by
      have h := (isSylowIn_map_of_injective hpsi (P := T) (H := ⊤)).mpr hT
      simpa [psi, Subgroup.map_top] using h),
    (by
      have h := congrArg (Subgroup.map psi) hFT
      rw [Subgroup.map_sup, Subgroup.map_top, hinn] at h
      exact h)⟩

theorem exists_orthogonal_representation_of_fitting_simple
    {p : ℕ} {K : Type} [Field K] [Finite K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5)
    {Qgrp : Type} [Group Qgrp] [Finite Qgrp] (T : Subgroup Qgrp)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Qgrp))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Qgrp), a * b ≠ b * a)
    (hLie : LieModel ↥(CFSG.generalizedFitting Qgrp) .PSp 2 p 1)
    (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting Qgrp ⊔ T = ⊤) :
    let F0 := CFSG.generalizedFitting Qgrp
    let psi := MulAut.conjNormal (H := F0)
    let B := psi.range
    let Saut := T.map psi
    ∃ ρ : MulAut F0 →* TauCeti.QuadraticMap.orthogonalGroup Q,
      Function.Injective ρ ∧
      ρ.range = Q.specialOrthogonalWithin ∧
      (innAutOf F0).map ρ = commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ∧
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ B.map ρ ∧
      B.map ρ ≤ Q.specialOrthogonalWithin ∧
      IsSylowIn 2 (Saut.map ρ) (B.map ρ) ∧
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ⊔ Saut.map ρ = B.map ρ := by
  let F0 := CFSG.generalizedFitting Qgrp
  letI : F0.Normal := by
    simpa [F0] using (CFSG.LocalCores.generalized_fitting_characteristic (G := Qgrp)).2
  haveI : IsSimpleGroup F0 := by simpa [F0] using hs
  let psi : Qgrp →* MulAut F0 := MulAut.conjNormal (H := F0)
  let B := psi.range
  let Saut := T.map psi
  have hAS : AlmostSimpleData F0 B Saut := by
    simpa [B, Saut, psi, F0] using
      almostSimpleData_conjNormal (Q := Qgrp) T hs hnab hT hFT
  obtain ⟨ρ, hρinj, hρrange, hinnρ, htrans⟩ :=
    exists_orthogonal_model_of_lieModel_psp_prime (p := p) (K := K) (V := V)
      hp hp2 hK Q hQ hdim F0 hLie
  obtain ⟨h1, h2, h3, h4⟩ := htrans B Saut hAS
  exact ⟨ρ, hρinj, hρrange, hinnρ, h1, h2, h3, h4⟩

section Setup

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

structure AboveFiveSetup
    (Q : QuadraticForm K V) (Qgrp : Type) [Group Qgrp] [Finite Qgrp]
    (T : Subgroup Qgrp) where
  ρ : MulAut ↥(CFSG.generalizedFitting Qgrp) →*
    TauCeti.QuadraticMap.orthogonalGroup Q
  G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q)
  hG : G = (MulAut.conjNormal (H := CFSG.generalizedFitting Qgrp)).range.map ρ
  hρinj : Function.Injective ρ
  hρrange : ρ.range = Q.specialOrthogonalWithin
  hinn : (innAutOf ↥(CFSG.generalizedFitting Qgrp)).map ρ =
    commutator (TauCeti.QuadraticMap.orthogonalGroup Q)
  hAS : AlmostSimpleData ↥(CFSG.generalizedFitting Qgrp)
    (MulAut.conjNormal (H := CFSG.generalizedFitting Qgrp)).range
    (T.map (MulAut.conjNormal (H := CFSG.generalizedFitting Qgrp)))
  hL : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ≤ G
  hGSO : G ≤ Q.specialOrthogonalWithin
  hSylow : IsSylowIn 2
    ((T.map (MulAut.conjNormal (H := CFSG.generalizedFitting Qgrp))).map ρ) G
  hsup : commutator (TauCeti.QuadraticMap.orthogonalGroup Q) ⊔
    ((T.map (MulAut.conjNormal (H := CFSG.generalizedFitting Qgrp))).map ρ) = G
  e : Qgrp ≃* G
  hF0map : (CFSG.generalizedFitting Qgrp).map e.toMonoidHom =
    (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).subgroupOf G
  hTmap : T.map e.toMonoidHom =
    ((T.map (MulAut.conjNormal (H := CFSG.generalizedFitting Qgrp))).map ρ).subgroupOf G
  hFstar : CFSG.generalizedFitting G =
    (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).subgroupOf G

theorem exists_aboveFiveSetup
    {p : ℕ} {K : Type} [Field K] [Finite K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p)
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5)
    {Qgrp : Type} [Group Qgrp] [Finite Qgrp] (T : Subgroup Qgrp)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Qgrp))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Qgrp), a * b ≠ b * a)
    (hLie : LieModel ↥(CFSG.generalizedFitting Qgrp) .PSp 2 p 1)
    (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting Qgrp ⊔ T = ⊤) :
    Nonempty (AboveFiveSetup (K := K) (V := V) Q Qgrp T) := by
  let F0 := CFSG.generalizedFitting Qgrp
  letI : F0.Normal := by
    simpa [F0] using (CFSG.LocalCores.generalized_fitting_characteristic (G := Qgrp)).2
  haveI : IsSimpleGroup F0 := by simpa [F0] using hs
  let psi : Qgrp →* MulAut F0 := MulAut.conjNormal (H := F0)
  let B := psi.range
  let Saut := T.map psi
  have hAS : AlmostSimpleData F0 B Saut := by
    simpa [B, Saut, psi, F0] using
      almostSimpleData_conjNormal (Q := Qgrp) T hs hnab hT hFT
  obtain ⟨ρ, hρinj, hρrange, hinnρ, hL, hGSO, hSylow, hsup⟩ :=
    exists_orthogonal_representation_of_fitting_simple (p := p) (K := K) (V := V)
      hp hp2 hK Q hQ hdim T hs hnab hLie hT hFT
  let G : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q) := B.map ρ
  let phi : Qgrp →* TauCeti.QuadraticMap.orthogonalGroup Q := ρ.comp psi
  have hC : Subgroup.centralizer (F0 : Set Qgrp) ≤ F0 := by
    simpa [F0] using CFSG.centralizer_generalizedFitting_le Qgrp
  have hZ : Subgroup.center F0 = ⊥ := by
    simpa [F0] using (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := F0) hnab).2
  have hpsi : Function.Injective psi := by
    simpa [psi] using (Subgroup.conjNormal_injective_of_centralizer_le (N := F0) hC hZ)
  have hconj : psi.comp F0.subtype = (MulAut.conj : F0 →* MulAut F0) := by
    ext x y
    simpa [psi] using congrArg (fun f : MulAut F0 => (f : F0 → F0) y)
      (MulAut.conjNormal_val (H := F0) (h := x))
  have hinn : F0.map psi = innAutOf F0 := by
    rw [innAutOf, ← hconj, MonoidHom.range_comp, Subgroup.range_subtype]
  have hphi : Function.Injective phi := by
    intro x y h
    exact hpsi (hρinj h)
  have hrange : phi.range = G := by
    rw [MonoidHom.range_comp]
  let e0 : Qgrp ≃* phi.range := MonoidHom.ofInjective hphi
  let e : Qgrp ≃* G := e0.trans (MulEquiv.subgroupCongr hrange)
  have he_apply (x : Qgrp) :
      (e x : TauCeti.QuadraticMap.orthogonalGroup Q) = phi x := rfl
  have hF0phi : F0.map phi =
      commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
    change Subgroup.map (ρ.comp psi) F0 = _
    rw [← Subgroup.map_map, hinn, hinnρ]
  have hF0map : F0.map e.toMonoidHom =
      (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).subgroupOf G := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxL : phi x ∈ commutator (TauCeti.QuadraticMap.orthogonalGroup Q) := by
        rw [← hF0phi]
        exact Subgroup.mem_map_of_mem phi hx
      exact Subgroup.mem_subgroupOf.mpr (by simpa [he_apply] using hxL)
    · intro hy
      have hyL : (y : TauCeti.QuadraticMap.orthogonalGroup Q) ∈
          commutator (TauCeti.QuadraticMap.orthogonalGroup Q) :=
        Subgroup.mem_subgroupOf.mp hy
      have hpre : (y : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ F0.map phi := by
        rw [hF0phi]
        exact hyL
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hpre
      exact ⟨x, hx, Subtype.ext hxy⟩
  have hTmap : T.map e.toMonoidHom = (Saut.map ρ).subgroupOf G := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      have hxT : phi x ∈ Saut.map ρ := by
        change ρ (psi x) ∈ Subgroup.map ρ (T.map psi)
        exact Subgroup.mem_map_of_mem ρ (Subgroup.mem_map_of_mem psi hx)
      simpa [he_apply] using hxT
    · intro hy
      have hyT : (y : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ Saut.map ρ :=
        Subgroup.mem_subgroupOf.mp hy
      have hpre : (y : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ T.map phi := by
        change (y : TauCeti.QuadraticMap.orthogonalGroup Q) ∈ T.map (ρ.comp psi)
        rw [show Saut = T.map psi from rfl] at hyT
        rw [← Subgroup.map_map]
        exact hyT
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hpre
      exact ⟨x, hx, Subtype.ext hxy⟩
  have hFstar : CFSG.generalizedFitting G =
      (commutator (TauCeti.QuadraticMap.orthogonalGroup Q)).subgroupOf G := by
    have h := CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
    rw [← h, hF0map]
  exact ⟨{
    ρ := ρ
    G := G
    hG := rfl
    hρinj := hρinj
    hρrange := hρrange
    hinn := hinnρ
    hAS := hAS
    hL := hL
    hGSO := hGSO
    hSylow := hSylow
    hsup := hsup
    e := e
    hF0map := hF0map
    hTmap := hTmap
    hFstar := hFstar }⟩

theorem weakClosure_eq_bot_of_no_two_of_card_lt_four
    {G : Type*} [Group G] [Finite G] {T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : IsInvColl ⊤ Ω)
    (h2 : ∀ A ∈ Ω, Nat.card A ≠ 2)
    (h4 : ∀ A ∈ Ω, A ≤ T → Nat.card A < 4) :
    weakClosure T Ω = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun A hA => iSup_le fun hAT => ?_)
  have hp : IsPGroup 2 A := CFSG.Quasithin.E1.isPGroup_of_isElemAbelian (hΩ.isElemAbelian A hA)
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hne2 := h2 A hA
  have hlt4 := h4 A hA hAT
  rcases k with _ | _ | k
  · exact le_bot_iff.mpr (Subgroup.card_eq_one.mp (by simpa using hk))
  · exact absurd (by simpa using hk) hne2
  · exfalso
    apply hlt4.not_ge
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

end Setup

section Assembly

variable {K : Type} {V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {Qform : QuadraticForm K V} {Qgrp : Type} [Group Qgrp] [Finite Qgrp] {T : Subgroup Qgrp}

noncomputable def setupF0Equiv
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T) :
    ↥(CFSG.generalizedFitting Qgrp) ≃*
      ↥((commutator (TauCeti.QuadraticMap.orthogonalGroup Qform)).subgroupOf S.G) :=
  (Subgroup.equivMapOfInjective (CFSG.generalizedFitting Qgrp)
    S.e.toMonoidHom S.e.injective).trans (MulEquiv.subgroupCongr S.hF0map)

theorem setupFstar_simple
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Qgrp)) :
    IsSimpleGroup ↥(CFSG.generalizedFitting S.G) := by
  rw [S.hFstar]
  exact (setupF0Equiv S).symm.isSimpleGroup

theorem setupFstar_nonab
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Qgrp), a * b ≠ b * a) :
    ∃ a b : ↥(CFSG.generalizedFitting S.G), a * b ≠ b * a := by
  rw [S.hFstar]
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨setupF0Equiv S a, setupF0Equiv S b, ?_⟩
  intro h
  have h' : setupF0Equiv S (a * b) = setupF0Equiv S (b * a) := by
    simpa [map_mul] using h
  exact hab ((setupF0Equiv S).injective h')

theorem sup_normal_eq_top_of_isSylowIn_conj
    {G : Type*} [Group G] [Finite G] {L T T₀ : Subgroup G} [hL : L.Normal]
    (hT : IsSylowIn 2 T ⊤) (hT₀ : IsSylowIn 2 T₀ ⊤)
    (hsup : L ⊔ T = ⊤) : L ⊔ T₀ = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, -, hconj⟩ := CFSG.Quasithin.B6.isSylowTwoOf_exists_conj
    (S := T) (T := T₀) hT hT₀
  have hgL : g ∈ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have hLc : CFSG.Quasithin.B6.conjSub g L = L :=
    CFSG.Quasithin.B6.conjSub_eq_self hgL
  calc L ⊔ T₀ = L ⊔ CFSG.Quasithin.B6.conjSub g T := by rw [hconj]
    _ = CFSG.Quasithin.B6.conjSub g L ⊔ CFSG.Quasithin.B6.conjSub g T := by
        rw [hLc]
    _ = CFSG.Quasithin.B6.conjSub g (L ⊔ T) :=
        (OrderIso.map_sup (CFSG.Quasithin.B6.conjSub g) L T).symm
    _ = CFSG.Quasithin.B6.conjSub g ⊤ := by rw [hsup]
    _ = ⊤ := OrderIso.map_top _

theorem aboveFive_inE_of_setup
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Qgrp))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Qgrp), a * b ≠ b * a)
    (T₀ : Subgroup S.G) (hT₀ : IsSylowIn 2 T₀ ⊤)
    (hsupT₀ : (commutator (TauCeti.QuadraticMap.orthogonalGroup Qform)).subgroupOf S.G ⊔ T₀ = ⊤)
    (hNonzero : ∀ Ω : Set (Subgroup S.G), IsInvColl ⊤ Ω →
      (∀ A ∈ Ω, Nat.card A ≠ 2) →
      (∃ A ∈ Ω, A ≤ T₀ ∧ 4 ≤ Nat.card A) →
      eGen 1 ⊤ T₀ Ω ⊔
        (⊤ ⊓ Subgroup.normalizer (weakClosure T₀ Ω)) = ⊤) :
    InE 1 (⊤ : Subgroup Qgrp) := by
  haveI : Finite ↥S.G := Finite.of_surjective S.e.toMonoidHom S.e.surjective
  haveI hsimple : IsSimpleGroup ↥(CFSG.generalizedFitting S.G) := setupFstar_simple S hs
  have hFstarTop : CFSG.generalizedFitting S.G ⊔ T₀ = ⊤ := by
    rw [S.hFstar]
    exact hsupT₀
  have hII : ∀ A : Subgroup S.G, A ≤ T₀ → Nat.card A = 2 → IsE 1 ⊤ T₀ A ⊤ := by
    intro A hAT hA
    exact isE_one_top_of_fstar_simple T₀ A (setupFstar_nonab S hnab) hT₀ hFstarTop hAT hA
  have hEFor : InEFor 1 ⊤ T₀ := by
    refine inEFor_top_of_noTwo hT₀ hII ?_
    intro Ω hΩ h2
    by_cases h4 : ∃ A ∈ Ω, A ≤ T₀ ∧ 4 ≤ Nat.card A
    · exact hNonzero Ω hΩ h2 h4
    · push Not at h4
      have hsmall : ∀ A ∈ Ω, A ≤ T₀ → Nat.card A < 4 := by
        intro A hA hAT
        have hnot := h4 A hA hAT
        omega
      rw [weakClosure_eq_bot_of_no_two_of_card_lt_four hΩ h2 hsmall]
      rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance, inf_top_eq, sup_top_eq]
  have hInE : InE 1 (⊤ : Subgroup S.G) := (inE_iff_inEFor hT₀).mpr hEFor
  have hmap := CFSG.Quasithin.E1.Eleven.inE_map_mulEquiv S.e.symm hInE
  rwa [Subgroup.map_top_of_surjective _ S.e.symm.surjective] at hmap

theorem pgl2_join_of_surjective
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p) (hp : 5 < p)
    {G : Type*} [Group G] [Finite G] (π : G →* CFSG.GorensteinWalter.PGL2 K)
    (hπ : Function.Surjective π)
    {S B : Subgroup G} (hS : IsSylowIn 2 S ⊤) (hBS : B ≤ S)
    (hBmap : CFSG.Open.IsElemAbelian 2 (B.map π)) (hBmapne : B.map π ≠ ⊥) :
    (S.map π) ⊔
      (⨆ I ∈ {I : Subgroup (CFSG.GorensteinWalter.PGL2 K) |
        IsE 1 ⊤ (S.map π) (B.map π) I}, I) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSmap : IsSylowIn 2 (S.map π) ⊤ := isSylowIn_two_map_top hπ hS
  have hBSmap : B.map π ≤ S.map π := Subgroup.map_mono hBS
  exact CFSG.Quasithin.E22L2.pgl2_prime_sup_isE_one_eq_top_of_elemAbelian
    hK hp hSmap hBSmap hBmap hBmapne

theorem tPositiveDerived_eq_comap_frameX2
    {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (F : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel.FrameData Q) :
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived F =
      (CFSG.ClassicalGroups.Orthogonal.frameX2 F).comap
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype := by
  rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived,
    CFSG.ClassicalGroups.Orthogonal.frameX2,
    CFSG.ClassicalGroups.Orthogonal.frameW2_eq_t_eigenspace]

theorem tPositiveDerived_map_subtype_eq_frameX2
    {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (F : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel.FrameData Q)
    (hq5 : 5 ≤ Nat.card K) :
    (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived F).map
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
        CFSG.ClassicalGroups.Orthogonal.frameX2 F := by
  rw [tPositiveDerived_eq_comap_frameX2, Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hX2D : CFSG.ClassicalGroups.Orthogonal.frameX2 F ≤
      CFSG.RankThree.Classical2.orthDerived Q := by
    rw [← CFSG.ClassicalGroups.Orthogonal.supportedOrthDerived_sup_eq_orthDerived F hq5]
    exact le_sup_right
  have hX2O : CFSG.ClassicalGroups.Orthogonal.frameX2 F ≤
      TauCeti.QuadraticMap.orthogonalGroup Q :=
    hX2D.trans (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (Q := Q))
  exact inf_eq_right.mpr hX2O

theorem tPositiveDerived_conj_map_subtype_eq_frameX1
    {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (F : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel.FrameData Q)
    (hq5 : 5 ≤ Nat.card K) :
    (((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived F).map
      (MulAut.conj F.sO).toMonoidHom)).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype =
      CFSG.ClassicalGroups.Orthogonal.frameX1 F := by
  rw [Subgroup.map_map]
  have hcomp : (TauCeti.QuadraticMap.orthogonalGroup Q).subtype.comp
      (MulAut.conj F.sO).toMonoidHom =
      (MulAut.conj F.s).toMonoidHom.comp
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, tPositiveDerived_map_subtype_eq_frameX2 F hq5]
  exact CFSG.ClassicalGroups.Orthogonal.supportedOrthDerived_frameW2_map_conj_s F

structure AboveFiveFixedFrame
    [FiniteDimensional K V]
    {Qform : QuadraticForm K V} {Qgrp : Type} [Group Qgrp] [Finite Qgrp]
    {T : Subgroup Qgrp}
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T) where
  F : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel.FrameData Qform
  W : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.FiveDimensionalWreathData F
  T₀ : Sylow 2 S.G
  P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Qform)
  hP : P = (T₀ : Subgroup S.G).map S.G.subtype
  hT₀coe : P = W.S.map (Qform.specialOrthogonalWithin).subtype ⊓ S.G
  hT₀ : IsSylowIn 2 (T₀ : Subgroup S.G) ⊤
  hsup : (commutator (TauCeti.QuadraticMap.orthogonalGroup Qform)).subgroupOf S.G ⊔
    (T₀ : Subgroup S.G) = ⊤
  hzP : F.zO ∈ P
  htP : F.tO ∈ P
  hzord : orderOf F.zO = 2
  htord : orderOf F.tO = 2
  hzt : F.tO ∉ Subgroup.zpowers F.zO
  hcenter : (Subgroup.center T₀).map
      (S.G.subtype.comp (T₀ : Subgroup S.G).subtype) = Subgroup.zpowers F.zO
  hnormalFour_le : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.normalFour F ≤ P
  hnormalFour_card : Nat.card (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.normalFour F) = 4
  hnormalFour_normal :
    ((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.normalFour F).subgroupOf P).Normal

theorem exists_aboveFiveFixedFrame
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (hodd : Odd (Nat.card K))
    (hQ : Qform.polarBilin.Nondegenerate)
    (hdim : Module.finrank K V = 5) :
    Nonempty (AboveFiveFixedFrame S) := by
  classical
  let F : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel.FrameData Qform :=
    Classical.choice (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalLocalModel.exists_frameData
      hodd hdim Qform hQ)
  obtain ⟨W, T₀, hPmap, hzP, htP, hzord, htord, hzt, hcenter, hnf_le, hnf_card, hnf_normal⟩ :=
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.fixed_frame_sylow
      F hodd hQ hdim S.G S.hL S.hGSO
  let P : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Qform) :=
    (T₀ : Subgroup S.G).map S.G.subtype
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀ : IsSylowIn 2 (T₀ : Subgroup S.G) ⊤ := by
    refine ⟨le_top, T₀.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact T₀.not_dvd_index
  let P0 : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Qform) :=
    (T.map (MulAut.conjNormal (H := CFSG.generalizedFitting Qgrp))).map S.ρ
  have hP0le : P0 ≤ S.G := by
    rw [S.hG]
    exact Subgroup.map_mono (by
      rw [← S.hAS.2.2]
      exact le_sup_right)
  have hTg : IsSylowIn 2 (P0.subgroupOf S.G) ⊤ := by
    have h := (isSylowIn_subgroupOf_iff (P := P0) (K := S.G) (H := S.G)
      hP0le le_rfl).mpr S.hSylow
    simpa using h
  have hsupTg : (commutator (TauCeti.QuadraticMap.orthogonalGroup Qform)).subgroupOf S.G ⊔
      P0.subgroupOf S.G = ⊤ := by
    rw [← Subgroup.subgroupOf_sup S.hL hP0le, S.hsup, Subgroup.subgroupOf_self]
  haveI : (commutator (TauCeti.QuadraticMap.orthogonalGroup Qform)).Normal := by
    rw [commutator_def]
    exact Subgroup.commutator_normal ⊤ ⊤
  haveI : ((commutator (TauCeti.QuadraticMap.orthogonalGroup Qform)).subgroupOf S.G).Normal :=
    Subgroup.Normal.subgroupOf inferInstance S.G
  have hsup := sup_normal_eq_top_of_isSylowIn_conj hTg hT₀ hsupTg
  exact ⟨{
    F := F
    W := W
    T₀ := T₀
    P := P
    hP := rfl
    hT₀coe := by simpa [P] using hPmap
    hT₀ := hT₀
    hsup := hsup
    hzP := by simpa [P] using hzP
    htP := by simpa [P] using htP
    hzord := hzord
    htord := htord
    hzt := hzt
    hcenter := hcenter
    hnormalFour_le := by simpa [P] using hnf_le
    hnormalFour_card := hnf_card
    hnormalFour_normal := by simpa [P] using hnf_normal
  }⟩

theorem fixedFrame_sO_mem_P
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S) : FF.F.sO ∈ FF.P := by
  rw [FF.hT₀coe]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · refine Subgroup.mem_map.mpr ⟨FF.F.sSO, ?_, rfl⟩
    rw [FF.W.hScoe]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers FF.F.sSO)
  · exact S.hL (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.sO_mem_derived FF.F)

theorem fixedFrame_derived_sup_P
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S) :
    commutator (TauCeti.QuadraticMap.orthogonalGroup Qform) ⊔ FF.P = S.G := by
  have h := congrArg (Subgroup.map S.G.subtype) FF.hsup
  simpa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le S.hL, FF.hP,
    Subgroup.map_top, Subgroup.range_subtype] using h

theorem fixedFrame_component_join_X2
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hq5 : 5 ≤ Nat.card K) :
    (FF.T₀ : Subgroup S.G) ⊔
      ((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived FF.F).subgroupOf
        S.G) = ⊤ := by
  let O := TauCeti.QuadraticMap.orthogonalGroup Qform
  let j : O →* (V ≃ₗ[K] V) := Subgroup.subtype O
  let Plin : Subgroup (V ≃ₗ[K] V) := FF.P.map j
  let Glin : Subgroup (V ≃ₗ[K] V) := S.G.map j
  have hGen : CFSG.RankThree.Classical2.orthDerived Qform ⊔ Plin = Glin := by
    have h := congrArg (Subgroup.map j) (fixedFrame_derived_sup_P S FF)
    rw [Subgroup.map_sup] at h
    rw [CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_eq_map_commutator]
    exact h
  have hs : FF.F.s ∈ Plin := by
    exact Subgroup.mem_map.mpr ⟨FF.F.sO, fixedFrame_sO_mem_P S FF, rfl⟩
  have hjoinLin : Plin ⊔ CFSG.ClassicalGroups.Orthogonal.frameX2 FF.F = Glin :=
    CFSG.ClassicalGroups.Orthogonal.frameT_sup_frameX2_eq_of_derived_sup_eq
      FF.F hq5 hs hGen
  have hjoinO : FF.P ⊔
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived FF.F = S.G := by
    apply Subgroup.map_injective (f := O.subtype) (Subgroup.subtype_injective O)
    rw [Subgroup.map_sup, tPositiveDerived_map_subtype_eq_frameX2 FF.F hq5]
    simpa [Plin, Glin, j] using hjoinLin
  have hXle : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived FF.F ≤ S.G :=
    (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived_le_commutator FF.F).trans
      S.hL
  apply Subgroup.map_injective (f := S.G.subtype) (Subgroup.subtype_injective S.G)
  rw [Subgroup.map_sup, ← FF.hP, Subgroup.map_subgroupOf_eq_of_le hXle, Subgroup.map_top,
    Subgroup.range_subtype]
  exact hjoinO

theorem fixedFrame_component_join_X1
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hq5 : 5 ≤ Nat.card K) :
    (FF.T₀ : Subgroup S.G) ⊔
      (((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived FF.F).map
        (MulAut.conj FF.F.sO).toMonoidHom).subgroupOf S.G) = ⊤ := by
  let O := TauCeti.QuadraticMap.orthogonalGroup Qform
  let j : O →* (V ≃ₗ[K] V) := Subgroup.subtype O
  let Plin : Subgroup (V ≃ₗ[K] V) := FF.P.map j
  let Glin : Subgroup (V ≃ₗ[K] V) := S.G.map j
  have hGen : CFSG.RankThree.Classical2.orthDerived Qform ⊔ Plin = Glin := by
    have h := congrArg (Subgroup.map j) (fixedFrame_derived_sup_P S FF)
    rw [Subgroup.map_sup] at h
    rw [CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_eq_map_commutator]
    exact h
  have hs : FF.F.s ∈ Plin := by
    exact Subgroup.mem_map.mpr ⟨FF.F.sO, fixedFrame_sO_mem_P S FF, rfl⟩
  have hjoinLin : Plin ⊔ CFSG.ClassicalGroups.Orthogonal.frameX1 FF.F = Glin :=
    CFSG.ClassicalGroups.Orthogonal.frameT_sup_frameX1_eq_of_derived_sup_eq
      FF.F hq5 hs hGen
  have hjoinO : FF.P ⊔
      ((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived FF.F).map
        (MulAut.conj FF.F.sO).toMonoidHom) = S.G := by
    apply Subgroup.map_injective (f := O.subtype) (Subgroup.subtype_injective O)
    rw [Subgroup.map_sup, tPositiveDerived_conj_map_subtype_eq_frameX1 FF.F hq5]
    simpa [Plin, Glin, j] using hjoinLin
  have hX1le : ((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived FF.F).map
      (MulAut.conj FF.F.sO).toMonoidHom) ≤ S.G :=
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.XConj_le_G FF.F S.G S.hL
  apply Subgroup.map_injective (f := S.G.subtype) (Subgroup.subtype_injective S.G)
  rw [Subgroup.map_sup, ← FF.hP, Subgroup.map_subgroupOf_eq_of_le hX1le, Subgroup.map_top,
    Subgroup.range_subtype]
  exact hjoinO

theorem eGen_sup_normalizer_eq_top_of_localPackage
    {p : ℕ} [Finite K] [FiniteDimensional K V] [Fact p.Prime]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K)
    (hK : Nat.card K = p) (hp : 5 < p)
    {Ω : Set (Subgroup S.G)} (hΩ : E1.IsInvColl ⊤ Ω)
    {A' : Subgroup S.G} (hA'Ω : A' ∈ Ω) (hA'T : A' ≤ (FF.T₀ : Subgroup S.G))
    (hA'ab : CFSG.Open.IsElemAbelian 2 A')
    (Kloc : Subgroup S.G) (Y : Subgroup S.G)
    (hYle : Y ≤ Kloc)
    (hjoin : (FF.T₀ : Subgroup S.G) ⊔ Y = ⊤)
    (hτ : E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤ (FF.T₀ : Subgroup S.G) ⊓ Kloc)
    (hSyl : IsSylowIn 2 ((FF.T₀ : Subgroup S.G) ⊓ Kloc) Kloc)
    (π : ↥Kloc →* CFSG.GorensteinWalter.PGL2 K)
    (hπ : Function.Surjective π)
    (hker2 : IsPGroup 2 ↥π.ker)
    (hB : CFSG.Open.IsElemAbelian 2 ((A'.subgroupOf Kloc).map π))
    (hBne : (A'.subgroupOf Kloc).map π ≠ ⊥) :
    E1.eGen 1 ⊤ (FF.T₀ : Subgroup S.G) Ω ⊔
      (⊤ ⊓ Subgroup.normalizer (E1.weakClosure (FF.T₀ : Subgroup S.G) Ω)) = ⊤ := by
  classical
  let T0 : Subgroup S.G := FF.T₀
  let P : Subgroup S.G := T0 ⊓ Kloc
  let Smap : Subgroup (CFSG.GorensteinWalter.PGL2 K) := (P.subgroupOf Kloc).map π
  let Bmap : Subgroup (CFSG.GorensteinWalter.PGL2 K) := (A'.subgroupOf Kloc).map π
  let N : Subgroup S.G :=
    E1.eGen 1 ⊤ T0 Ω ⊔ (⊤ ⊓ Subgroup.normalizer (E1.weakClosure T0 Ω))
  haveI : Finite ↥S.G := Finite.of_surjective S.e.toMonoidHom S.e.surjective
  have hT0 : IsSylowIn 2 T0 ⊤ := by simpa [T0] using FF.hT₀
  have hA'T0 : A' ≤ T0 := by simpa [T0] using hA'T
  have hjoin' : T0 ⊔ Y = ⊤ := by simpa [T0] using hjoin
  have hτ' : E1.tauOf ⊤ T0 A' ≤ T0 ⊓ Kloc := by simpa [T0] using hτ
  have hSyl' : IsSylowIn 2 (T0 ⊓ Kloc) Kloc := by simpa [T0] using hSyl
  have hBS : A'.subgroupOf Kloc ≤ P.subgroupOf Kloc := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact Subgroup.mem_inf.mpr ⟨hA'T0 hx, x.property⟩
  have hSsub : IsSylowIn 2 (P.subgroupOf Kloc) ⊤ := by
    have hPle : P ≤ Kloc := by simpa [P] using (inf_le_right : T0 ⊓ Kloc ≤ Kloc)
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := P) (K := Kloc)
      (H := Kloc) hPle le_rfl).mpr hSyl'
    simpa [P] using h
  have hgen : Smap ⊔
      (⨆ I ∈ {I : Subgroup (CFSG.GorensteinWalter.PGL2 K) |
        E1.IsE 1 ⊤ Smap Bmap I}, I) = ⊤ :=
    pgl2_join_of_surjective (K := K) (G := ↥Kloc) hK hp π hπ hSsub hBS
      (by simpa [Bmap] using hB) (by simpa [Bmap] using hBne)
  have hKle : Kloc ≤ N := by
    have h := E1.relative_generation_le_eGen_sup_normalizer (n := 1)
      (G := S.G) (T := T0) (A := A') (K := Kloc) (Γ := CFSG.GorensteinWalter.PGL2 K)
      hT0 hA'T0 hA'ab hτ' hSyl' π hπ hker2 (by simpa [P, Smap, Bmap] using hgen) hΩ hA'Ω
    simpa [N] using h
  have hTle : T0 ≤ N := by
    have h := (E1.le_normalizer_weakClosure hΩ).trans
      (le_sup_right : Subgroup.normalizer (E1.weakClosure T0 Ω) ≤
        E1.eGen 1 ⊤ T0 Ω ⊔ Subgroup.normalizer (E1.weakClosure T0 Ω))
    simpa [N] using h
  have htop : (⊤ : Subgroup S.G) ≤ N := by
    rw [← hjoin']
    exact sup_le hTle (hYle.trans hKle)
  exact top_le_iff.mp htop

theorem fixedFrame_P_le_centralizer_zO
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S) :
    FF.P ≤ Subgroup.centralizer ({FF.F.zO} :
      Set (TauCeti.QuadraticMap.orthogonalGroup Qform)) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hzmem : FF.F.zO ∈ (Subgroup.center FF.T₀).map
      (S.G.subtype.comp (FF.T₀ : Subgroup S.G).subtype) := by
    rw [FF.hcenter]
    exact Subgroup.mem_zpowers FF.F.zO
  rcases Subgroup.mem_map.mp hzmem with ⟨zT, hzTcenter, hzTmap⟩
  rw [FF.hP] at hy
  rcases Subgroup.mem_map.mp hy with ⟨yT, hyT, rfl⟩
  let yT' : FF.T₀ := ⟨yT, hyT⟩
  have hcomm : yT' * zT = zT * yT' :=
    (Subgroup.mem_center_iff.mp hzTcenter) yT'
  have hmap := congrArg (S.G.subtype.comp (FF.T₀ : Subgroup S.G).subtype) hcomm
  rw [map_mul, map_mul, hzTmap] at hmap
  simpa using hmap

theorem fixedFrame_P_le_G
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S) : FF.P ≤ S.G := by
  rw [FF.hP]
  exact Subgroup.map_subtype_le (FF.T₀ : Subgroup S.G)

theorem fixedFrame_z_mem_G
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S) : FF.F.zO ∈ S.G :=
  fixedFrame_P_le_G S FF FF.hzP

theorem fixedFrame_A_le_centralizer_z
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    {zG : S.G} (hzG : (zG : TauCeti.QuadraticMap.orthogonalGroup Qform) = FF.F.zO)
    {A : Subgroup S.G} (hAT : A ≤ (FF.T₀ : Subgroup S.G)) :
    A ≤ Subgroup.centralizer ({zG} : Set S.G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hxP : (x : TauCeti.QuadraticMap.orthogonalGroup Qform) ∈ FF.P := by
    rw [FF.hP]
    exact Subgroup.mem_map.mpr ⟨x, hAT hx, rfl⟩
  have hxcz : (x : TauCeti.QuadraticMap.orthogonalGroup Qform) * FF.F.zO =
      FF.F.zO * (x : TauCeti.QuadraticMap.orthogonalGroup Qform) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (fixedFrame_P_le_centralizer_zO S FF hxP)
  simpa [hzG] using hxcz

private theorem exists_mem_ne_one_ne_of_four_le_card
    {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    (hA4 : 4 ≤ Nat.card A) (z : G) :
    ∃ a ∈ A, a ≠ 1 ∧ a ≠ z := by
  obtain ⟨x, hx, y, hy, hx1, hy1, hxy⟩ :=
    CFSG.CGT.Timmesfeld75.exists_ne_one_ne_of_four_le_card A hA4
  by_cases hxz : x = z
  · exact ⟨y, hy, hy1, fun hyz => hxy (hxz.trans hyz.symm)⟩
  · exact ⟨x, hx, hx1, hxz⟩

def localPackageOfFixedFrame
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K) :
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.TPositiveLocalPackage
      FF.F hodd (by omega : 3 < Nat.card K) S.G S.hL S.hGSO := by
  classical
  have hTstd : FF.W.S.map (Qform.specialOrthogonalWithin).subtype =
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathO FF.F FF.W.D := by
    rw [show (FF.W.S : Subgroup (Qform.specialOrthogonalWithin)) =
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathSub FF.F FF.W.D from FF.W.hScoe,
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathSub_map_eq]
  have hPw : (FF.T₀ : Subgroup S.G).map S.G.subtype =
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathO FF.F FF.W.D ⊓ S.G := by
    rw [← FF.hP, FF.hT₀coe, hTstd]
  exact CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPackageOfData
    FF.F hodd (by omega : 3 < Nat.card K) FF.W S.G FF.T₀ S.hL S.hGSO hPw

theorem localS_sylowIn_centralizer_tz
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) :
    IsSylowIn 2
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G)
      ((S.G ⊓ Subgroup.centralizer ({FF.F.zO} :
          Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) ⊓
        Subgroup.centralizer ({FF.F.tO} :
          Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) := by
  classical
  have hPw : FF.P = CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathO FF.F FF.W.D ⊓ S.G := by
    have hTstd : FF.W.S.map (Qform.specialOrthogonalWithin).subtype =
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathO FF.F FF.W.D := by
      rw [show (FF.W.S : Subgroup (Qform.specialOrthogonalWithin)) =
          CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathSub FF.F FF.W.D from FF.W.hScoe,
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathSub_map_eq]
    rw [FF.hT₀coe, hTstd]
  have hSleP : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤
      FF.P := by
    intro x hx
    rw [hPw]
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have hSleH : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤
      ((S.G ⊓ Subgroup.centralizer ({FF.F.zO} :
          Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) ⊓
        Subgroup.centralizer ({FF.F.tO} :
          Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) := by
    rw [le_inf_iff]
    refine ⟨?_, CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS_le_C0
      FF.F FF.W S.G⟩
    rw [le_inf_iff]
    refine ⟨?_, ?_⟩
    · rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
      exact inf_le_right
    · exact hSleP.trans (fixedFrame_P_le_centralizer_zO S FF)
  have hHleCG : ((S.G ⊓ Subgroup.centralizer ({FF.F.zO} :
        Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) ⊓
      Subgroup.centralizer ({FF.F.tO} :
        Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) ≤
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localCG FF.F S.G := by
    rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localCG]
    rw [le_inf_iff]
    refine ⟨?_, ?_⟩
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_right
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS0 : CFSG.Quasithin.IsSylowIn 2
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G)
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localCG FF.F S.G) :=
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS_sylowIn_CG
      FF.F hodd FF.W S.G S.hL S.hGSO
  have hSO : CFSG.ABGLocalTools.IsSylowOf 2
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G)
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localCG FF.F S.G) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hS0.le, hS0.isPGroup, hS0.not_dvd_relIndex⟩
  have hSO' := CFSG.ABGLocalTools.isSylowOf_iff.mp (hSO.of_le hSleH hHleCG)
  exact ⟨hSO'.1, hSO'.2.1, hSO'.2.2⟩

theorem exists_actualFusionData
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K))
    {A : Subgroup S.G} (hAab : CFSG.Open.IsElemAbelian 2 A)
    (hA4 : 4 ≤ Nat.card A) (hAT : A ≤ (FF.T₀ : Subgroup S.G)) :
    ∃ (a : S.G) (_haA : a ∈ A),
      a ≠ 1 ∧ a ≠ (⟨FF.F.zO, fixedFrame_z_mem_G S FF⟩ : S.G) ∧
      ∃ (R : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Qform))
        (h : TauCeti.QuadraticMap.orthogonalGroup Qform),
        h ∈ (S.G ⊓ Subgroup.centralizer ({FF.F.zO} :
          Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) ∧
        IsSylowIn 2 R
          ((S.G ⊓ Subgroup.centralizer ({FF.F.zO} :
            Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) ⊓
            Subgroup.centralizer ({(a : TauCeti.QuadraticMap.orthogonalGroup Qform)} :
              Set (TauCeti.QuadraticMap.orthogonalGroup Qform))) ∧
        (A.map S.G.subtype) ≤ R ∧
        R ≤ Subgroup.centralizer
          ({h * FF.F.tO * h⁻¹} :
            Set (TauCeti.QuadraticMap.orthogonalGroup Qform)) := by
  classical
  haveI : Finite S.G := Finite.of_surjective S.e.toMonoidHom S.e.surjective
  let O := TauCeti.QuadraticMap.orthogonalGroup Qform
  let zO : O := FF.F.zO
  let zG : S.G := ⟨zO, fixedFrame_z_mem_G S FF⟩
  let H : Subgroup O := S.G ⊓ Subgroup.centralizer ({zO} : Set O)
  let AO : Subgroup O := A.map S.G.subtype
  have hAO_le_H : AO ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.property, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyH : y ∈ Subgroup.centralizer ({zG} : Set S.G) :=
      fixedFrame_A_le_centralizer_z S FF rfl hAT hy
    have hc : y * zG = zG * y := Subgroup.mem_centralizer_singleton_iff.mp hyH
    simpa [zO, zG] using congrArg (fun w : S.G => (w : O)) hc
  obtain ⟨a, haA, ha1, haz⟩ := exists_mem_ne_one_ne_of_four_le_card hA4 zG
  have ha2 : a * a = 1 := hAab.2 a haA
  let aO : O := a
  have haO_H : aO ∈ H :=
    hAO_le_H (Subgroup.mem_map.mpr ⟨a, haA, rfl⟩)
  let aHG : H := ⟨aO, haO_H⟩
  have haHG2 : aHG * aHG = 1 := by
    apply Subtype.ext
    simpa [aHG, aO] using congrArg (fun w : S.G => (w : O)) ha2
  have haHG1 : aHG ≠ 1 := by
    intro h
    have hO : (a : O) = 1 := by
      have := congrArg (fun x : H => (x : O)) h
      simpa [aHG, aO] using this
    exact ha1 (Subtype.ext hO)
  have hazO : (aHG : O) ≠ zO := by
    intro h
    exact haz (Subtype.ext h)
  let Ah : Subgroup H := AO.subgroupOf H
  have hAh_p : IsPGroup 2 Ah := by
    have hAO_p : IsPGroup 2 AO := (CFSG.Quasithin.E1.isPGroup_of_isElemAbelian hAab).map S.G.subtype
    exact hAO_p.of_equiv (Subgroup.subgroupOfEquivOfLe hAO_le_H).symm
  have hAh_le_Ca : Ah ≤ Subgroup.centralizer ({aHG} : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hxAO : (x : O) ∈ AO := hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxAO
    have hcomm : (y : O) * aO = aO * (y : O) := by
      have := CFSG.Quasithin.E1.commute_of_isElemAbelian hAab hy haA
      simpa [aO] using congrArg (fun w : S.G => (w : O)) this
    have hxy : (x : O) = (y : O) := hyx.symm
    calc (x : O) * (aHG : O) = (y : O) * aO := by rw [hxy]
      _ = aO * (y : O) := hcomm
      _ = (aHG : O) * (x : O) := by rw [← hxy]
  let Ca : Subgroup H := Subgroup.centralizer ({aHG} : Set H)
  let AhCa : Subgroup Ca := Ah.subgroupOf Ca
  have hAhCa_p : IsPGroup 2 AhCa :=
    hAh_p.of_equiv (Subgroup.subgroupOfEquivOfLe hAh_le_Ca).symm
  obtain ⟨Rin, hAhCa_le_Rin⟩ := hAhCa_p.exists_le_sylow
  have hfuse := CFSG.ClassicalGroups.Orthogonal.FourCentralizerFusion.exists_conj_tO_mem_center_sylow
    (F := FF.F) hodd (G := S.G) S.hL S.hGSO aHG haHG2 haHG1 hazO Rin
  obtain ⟨hHG, hhcenter⟩ := hfuse
  let incl : Ca →* O := H.subtype.comp Ca.subtype
  have hincl : Function.Injective incl := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  let R : Subgroup O := (Rin : Subgroup Ca).map incl
  have htop : Subgroup.map incl ⊤ = H ⊓ Subgroup.centralizer ({aO} : Set O) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact ⟨by simpa [incl] using y.val.property, by
        change incl y ∈ Subgroup.centralizer ({aO} : Set O)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hc : (y.val : H) * aHG = aHG * (y.val : H) :=
          Subgroup.mem_centralizer_singleton_iff.mp y.property
        have := congrArg (fun w : H => (w : O)) hc
        simpa [incl, aO] using this⟩
    · rintro ⟨hxH, hxC⟩
      let xH : H := ⟨x, hxH⟩
      have hxCa : xH ∈ Ca := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        simpa [aO] using (Subgroup.mem_centralizer_singleton_iff.mp hxC)
      exact ⟨⟨xH, hxCa⟩, Subgroup.mem_top _, rfl⟩
  have hR_sylow : IsSylowIn 2 R
      (H ⊓ Subgroup.centralizer ({aO} : Set O)) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hs : IsSylowIn 2 (Rin : Subgroup Ca) ⊤ := by
      refine ⟨le_top, Rin.isPGroup', ?_⟩
      rw [Subgroup.relIndex_top_right]
      exact Rin.not_dvd_index
    have h := (CFSG.Quasithin.E1.isSylowIn_map_of_injective hincl (f := incl)
      (P := (Rin : Subgroup Ca)) (H := ⊤)).mpr hs
    simpa [R, htop] using h
  have hA_le_R : AO ≤ R := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    let yAO : AO := ⟨y, Subgroup.mem_map.mpr ⟨y, hy, rfl⟩⟩
    let yH : H := ⟨y, hAO_le_H yAO.property⟩
    have hyAh : yH ∈ Ah := yAO.property
    have hyCa : yH ∈ Ca := hAh_le_Ca hyAh
    let yCa : Ca := ⟨yH, hyCa⟩
    have hyRin : yCa ∈ (Rin : Subgroup Ca) := hAhCa_le_Rin (Subgroup.mem_subgroupOf.mpr hyAh)
    exact Subgroup.mem_map.mpr ⟨yCa, hyRin, rfl⟩
  have hfuseR : R ≤ Subgroup.centralizer ({hHG * FF.F.tO * hHG⁻¹} : Set O) := by
    intro r hr
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases Subgroup.mem_map.mp hr with ⟨r0, hr0, hr0r⟩
    let r0Rin : Rin := ⟨r0, hr0⟩
    rcases Subgroup.mem_map.mp hhcenter with ⟨z, hzcenter, hzmap⟩
    have hzcomm : z * r0Rin = r0Rin * z := ((Subgroup.mem_center_iff.mp hzcenter) r0Rin).symm
    let inclRin : Rin →* O := incl.comp (Rin : Subgroup Ca).subtype
    have hmap := congrArg (fun x : Rin => inclRin x) hzcomm
    simp only [map_mul] at hmap
    have hmap' : (incl z : O) * (incl r0Rin : O) = (incl r0Rin : O) * (incl z : O) := by
      simpa [inclRin] using hmap
    have hzmap' : incl z = hHG * FF.F.tO * hHG⁻¹ := hzmap
    rw [hzmap'] at hmap'
    have hr0r' : incl r0Rin = r := hr0r
    rw [hr0r'] at hmap'
    exact hmap'.symm
  refine ⟨a, haA, ha1, haz, R, (hHG : O), hHG.property, ?_, hA_le_R, ?_⟩
  · simpa [H, zO, aO] using hR_sylow
  · simpa [O] using hfuseR

theorem setup_pCore_bot
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Qgrp))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Qgrp), a * b ≠ b * a) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup S.G) = ⊥ := by
  classical
  haveI : Finite S.G := Finite.of_surjective S.e.toMonoidHom S.e.surjective
  let L : Subgroup S.G := CFSG.generalizedFitting S.G
  haveI : L.Normal := by
    simpa [L, S.hFstar] using
      (CFSG.LocalCores.generalized_fitting_characteristic (G := S.G)).2
  haveI : IsSimpleGroup ↥L := by
    simpa [L] using setupFstar_simple S hs
  have hnc : ∃ a b : ↥L, a * b ≠ b * a := by
    simpa [L] using setupFstar_nonab S hnab
  have hC : Subgroup.centralizer (L : Set S.G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxF : x ∈ L := CFSG.centralizer_generalizedFitting_le (G := S.G) hx
    have hz : (⟨x, hxF⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx (y : S.G) y.property
    rw [CFSG.Quasithin.Vol2.Ch11.SecE3.center_eq_bot_of_simple (X := L) hnc,
      Subgroup.mem_bot] at hz
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hz)
  exact CFSG.Quasithin.E1.pCoreOf_top_eq_bot_of_normal_simple L hnc hC

theorem fixedFrame_P_isPGroup
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S) : IsPGroup 2 FF.P := by
  rw [FF.hP]
  exact FF.T₀.isPGroup'.map S.G.subtype

theorem fixedFrame_P_le_H
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S) :
    FF.P ≤ S.G ⊓ Subgroup.centralizer ({FF.F.zO} :
      Set (TauCeti.QuadraticMap.orthogonalGroup Qform)) :=
  le_inf (fixedFrame_P_le_G S FF) (fixedFrame_P_le_centralizer_zO S FF)

theorem localS_le_P
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S) :
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ FF.P := by
  have hPw : FF.P = CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathO FF.F FF.W.D ⊓ S.G := by
    have hTstd : FF.W.S.map (Qform.specialOrthogonalWithin).subtype =
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathO FF.F FF.W.D := by
      rw [show (FF.W.S : Subgroup (Qform.specialOrthogonalWithin)) =
          CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathSub FF.F FF.W.D from FF.W.hScoe,
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalSylow.wreathSub_map_eq]
    rw [FF.hT₀coe, hTstd]
  intro x hx
  rw [hPw]
  exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_left hx.1, hx.2⟩

theorem exists_normalized_A
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K))
    (hpc : CFSG.Open.pCoreOf 2 (⊤ : Subgroup S.G) = ⊥)
    {Ω : Set (Subgroup S.G)} (hΩ : E1.IsInvColl ⊤ Ω)
    {A : Subgroup S.G} (hAΩ : A ∈ Ω) (hAab : CFSG.Open.IsElemAbelian 2 A)
    (hA4 : 4 ≤ Nat.card A) (hAT : A ≤ (FF.T₀ : Subgroup S.G)) :
    ∃ A' : Subgroup S.G,
      A' ∈ Ω ∧ A' ≤ (FF.T₀ : Subgroup S.G) ∧ A' ≤
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
          FF.F FF.W S.G).subgroupOf S.G ∧
      CFSG.Open.IsElemAbelian 2 A' ∧ 4 ≤ Nat.card A' ∧
      E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
          FF.F FF.W S.G).subgroupOf S.G := by
  classical
  haveI : Finite S.G := Finite.of_surjective S.e.toMonoidHom S.e.surjective
  let O := TauCeti.QuadraticMap.orthogonalGroup Qform
  let zO : O := FF.F.zO
  let tO : O := FF.F.tO
  let H : Subgroup O := S.G ⊓ Subgroup.centralizer ({zO} : Set O)
  have hPp : IsPGroup 2 FF.P := fixedFrame_P_isPGroup S FF
  have hPH : FF.P ≤ H := by simpa [H, zO] using fixedFrame_P_le_H S FF
  have hSP : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G ≤ FF.P := localS_le_P S FF
  have hS : IsSylowIn 2
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G)
      (H ⊓ Subgroup.centralizer ({tO} : Set O)) := by
    simpa [H, zO, tO] using localS_sylowIn_centralizer_tz S FF hodd
  obtain ⟨a, haA, _ha1, _haz, R, h, hhH, hR, hA_le_R, hfuse⟩ :=
    exists_actualFusionData S FF hodd hAab hA4 hAT
  have hR' : IsSylowIn 2 R (H ⊓ Subgroup.centralizer ({(a : O)} : Set O)) := by
    simpa [H, zO] using hR
  obtain ⟨g, hgH, hRg_le_S, hcentral⟩ :=
    CFSG.GroupTheory.exists_conj_map_le_and_centralizer_inf_eq_of_isSylowIn
      (P := FF.P) (S := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G)
      (H := H) (R := R) (a := (a : O)) (t := tO) (h := h)
      hPp hPH hSP hS hR' hhH hfuse
  have hgG : g ∈ S.G := (Subgroup.mem_inf.mp hgH).1
  let gG : S.G := ⟨g, hgG⟩
  let A' : Subgroup S.G := A.map (MulAut.conj gG).toMonoidHom
  have hA'Ω : A' ∈ Ω := hΩ.conj A hAΩ gG (Subgroup.mem_top gG)
  have hA'O_le_S : (A'.map S.G.subtype) ≤
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    have hzR : (z : O) ∈ R := hA_le_R (Subgroup.mem_map.mpr ⟨z, hz, rfl⟩)
    have hxRg : ((MulAut.conj gG) z : O) ∈ R.map (MulAut.conj g).toMonoidHom := by
      refine Subgroup.mem_map.mpr ⟨(z : O), hzR, ?_⟩
      rfl
    exact hRg_le_S hxRg
  have hA'S : A' ≤ (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G).subgroupOf S.G := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hA'O_le_S (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  have hA'T : A' ≤ (FF.T₀ : Subgroup S.G) := by
    intro x hx
    have hxS := hA'S hx
    have hxP : (x : O) ∈ FF.P := hSP hxS
    rw [FF.hP] at hxP
    rcases Subgroup.mem_map.mp hxP with ⟨t, ht, htx⟩
    exact Subtype.ext htx ▸ ht
  have hA'card : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj gG).injective
  have hA'ab : CFSG.Open.IsElemAbelian 2 A' := hΩ.isElemAbelian A' hA'Ω
  have htau : E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
        FF.F FF.W S.G).subgroupOf S.G := by
    intro x hx
    let a' : S.G := gG * a * gG⁻¹
    have ha' : a' ∈ A' := by
      exact Subgroup.mem_map.mpr ⟨a, haA, by simp [a', MulAut.conj_apply]⟩
    have hcommPC : ⁅x, a'⁆ ∈ CFSG.Open.pCoreOf 2 (⊤ : Subgroup S.G) :=
      ((E1.mem_tauOf_of_le (le_top : (FF.T₀ : Subgroup S.G) ≤ ⊤)).mp hx).2 a' ha'
    rw [hpc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcommPC
    have hxT : x ∈ (FF.T₀ : Subgroup S.G) := (E1.tauOf_le ⊤ (FF.T₀ : Subgroup S.G) A') hx
    have hxP : (x : O) ∈ FF.P := by
      rw [FF.hP]
      exact Subgroup.mem_map.mpr ⟨x, hxT, rfl⟩
    have hxca : (x : O) ∈ Subgroup.centralizer ({g * (a : O) * g⁻¹} : Set O) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := congrArg (fun w : S.G => (w : O)) hcommPC
      simpa [a', gG, mul_assoc] using this
    have hxRg : (x : O) ∈ R.map (MulAut.conj g).toMonoidHom := by
      rw [← hcentral]
      exact Subgroup.mem_inf.mpr ⟨hxP, hxca⟩
    exact Subgroup.mem_subgroupOf.mpr (hRg_le_S hxRg)
  exact ⟨A', hA'Ω, hA'T, hA'S, hA'ab, by omega, htau⟩

theorem localS_subgroupOf_eq_inf_localK
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K) :
    (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G).subgroupOf S.G =
      (FF.T₀ : Subgroup S.G) ⊓
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
          FF.F FF.W S.G).subgroupOf S.G := by
  classical
  let pkg := localPackageOfFixedFrame S FF hodd hq5
  have hKleG : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
      FF.F FF.W S.G ≤ S.G := pkg.K_le_CG.trans inf_le_left
  have hSleG : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G ≤ S.G := by
    rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
    exact inf_le_right
  apply Subgroup.map_injective (f := S.G.subtype) (Subgroup.subtype_injective S.G)
  rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective S.G), ← FF.hP,
    Subgroup.map_subgroupOf_eq_of_le hKleG,
    Subgroup.map_subgroupOf_eq_of_le hSleG]
  have hW : pkg.W = FF.W := rfl
  have hP : pkg.P = FF.P := by rw [FF.hP]; rfl
  have hS := pkg.S_eq_P_inf_K
  rw [hW, hP] at hS
  exact hS

theorem localS_subgroupOf_eq_inf_localKConj
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K) :
    (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G).subgroupOf S.G =
      (FF.T₀ : Subgroup S.G) ⊓
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
          FF.F FF.W S.G).subgroupOf S.G := by
  classical
  let pkg := localPackageOfFixedFrame S FF hodd hq5
  let pkgC := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.conjugatePackageOf
    FF.F hodd (by omega : 3 < Nat.card K) S.G S.hL S.hGSO pkg
  have hSleG : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G ≤ S.G := by
    rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
    exact inf_le_right
  have hKleG : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
      FF.F FF.W S.G ≤ S.G := by
    change CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F ⊔
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ S.G
    exact sup_le pkgC.X_conj_le_G hSleG
  apply Subgroup.map_injective (f := S.G.subtype) (Subgroup.subtype_injective S.G)
  rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective S.G), ← FF.hP,
    Subgroup.map_subgroupOf_eq_of_le hKleG,
    Subgroup.map_subgroupOf_eq_of_le hSleG]
  have hW : pkgC.base.W = FF.W := rfl
  have hP : pkgC.base.P = FF.P := by rw [FF.hP]; rfl
  have hS := pkgC.S_eq_P_inf_KConj
  rw [hW, hP] at hS
  exact hS

theorem aboveFive_localData_of_basePackage
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K)
    {A' : Subgroup S.G}
    (hτ : E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
        FF.F FF.W S.G).subgroupOf S.G)
    (hBne : let Kloc : Subgroup S.G :=
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
          FF.F FF.W S.G).subgroupOf S.G
      let eK : ↥Kloc ≃* CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
          FF.F FF.W S.G :=
        Subgroup.subgroupOfEquivOfLe (by
          show CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
            FF.F FF.W S.G ≤ S.G
          exact (localPackageOfFixedFrame S FF hodd hq5).K_le_CG.trans inf_le_left)
      ((A'.subgroupOf Kloc).map
        ((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi
          FF.F hodd FF.W S.G).comp eK.toMonoidHom)) ≠ ⊥) :
    ∃ Kloc : Subgroup S.G,
      (FF.T₀ : Subgroup S.G) ⊔ Kloc = ⊤ ∧
      E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤ (FF.T₀ : Subgroup S.G) ⊓ Kloc ∧
      IsSylowIn 2 ((FF.T₀ : Subgroup S.G) ⊓ Kloc) Kloc ∧
      ∃ π : ↥Kloc →* CFSG.GorensteinWalter.PGL2 K,
        Function.Surjective π ∧ IsPGroup 2 ↥π.ker ∧
        (A'.subgroupOf Kloc).map π ≠ ⊥ := by
  classical
  let pkg := localPackageOfFixedFrame S FF hodd hq5
  let Kloc : Subgroup S.G :=
    (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
      FF.F FF.W S.G).subgroupOf S.G
  let Y : Subgroup S.G :=
    (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localX
      FF.F).subgroupOf S.G
  let eK : ↥Kloc ≃* CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
      FF.F FF.W S.G :=
    Subgroup.subgroupOfEquivOfLe (by
      show CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
        FF.F FF.W S.G ≤ S.G
      exact pkg.K_le_CG.trans inf_le_left)
  let pi0 := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi
    FF.F hodd FF.W S.G
  let piG : ↥Kloc →* CFSG.GorensteinWalter.PGL2 K := pi0.comp eK.toMonoidHom
  have hKleG : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
      FF.F FF.W S.G ≤ S.G := pkg.K_le_CG.trans inf_le_left
  have hSleG : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G ≤ S.G := by
    rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
    exact inf_le_right
  have hSyl : IsSylowIn 2 ((FF.T₀ : Subgroup S.G) ⊓ Kloc) Kloc := by
    have h := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff (p := 2)
      (P := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G)
      (K := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK FF.F FF.W S.G)
      (H := S.G) hSleG hKleG).mpr pkg.S_sylow_K
    have heq := localS_subgroupOf_eq_inf_localK S FF hodd hq5
    simpa [Kloc, heq] using h
  have hτ' : E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤ (FF.T₀ : Subgroup S.G) ⊓ Kloc := by
    have heq := localS_subgroupOf_eq_inf_localK S FF hodd hq5
    simpa [Kloc, heq] using hτ
  have hYle : Y ≤ Kloc := by
    intro x hx
    have hxO : (x : TauCeti.QuadraticMap.orthogonalGroup Qform) ∈
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerived FF.F :=
      Subgroup.mem_subgroupOf.mp (by simpa [Y] using hx)
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left hxO
  have hjoin : (FF.T₀ : Subgroup S.G) ⊔ Y = ⊤ := by
    simpa [Y, CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localX] using
      fixedFrame_component_join_X2 S FF hq5
  have htop : (FF.T₀ : Subgroup S.G) ⊔ Kloc = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = (FF.T₀ : Subgroup S.G) ⊔ Y := hjoin.symm
      _ ≤ (FF.T₀ : Subgroup S.G) ⊔ Kloc := sup_le_sup le_rfl hYle
  have hπ : Function.Surjective piG := pkg.pi_surjective.comp eK.surjective
  have hker : IsPGroup 2 ↥piG.ker := by
    change IsPGroup 2 ↥(Subgroup.comap eK.toMonoidHom
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi
        FF.F hodd FF.W S.G).ker)
    exact pkg.pi_ker_isPGroup.comap_of_injective eK.toMonoidHom eK.injective
  exact ⟨Kloc, htop, hτ', hSyl, piG, hπ, hker,
    by simpa [Kloc, eK, piG, pi0] using hBne⟩

theorem aboveFive_localData_of_conjugatePackage
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K)
    {A' : Subgroup S.G}
    (hτ : E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
        FF.F FF.W S.G).subgroupOf S.G)
    (hBne : let Kloc : Subgroup S.G :=
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
          FF.F FF.W S.G).subgroupOf S.G
      let eK : ↥Kloc ≃* CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
          FF.F FF.W S.G :=
        Subgroup.subgroupOfEquivOfLe (by
          show CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
            FF.F FF.W S.G ≤ S.G
          change CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F ⊔
            CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ S.G
          exact sup_le (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.XConj_le_G
            FF.F S.G S.hL) (by
              rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
              exact inf_le_right))
      ((A'.subgroupOf Kloc).map
        ((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
          FF.F hodd FF.W S.G S.hL).comp eK.toMonoidHom)) ≠ ⊥) :
    ∃ Kloc : Subgroup S.G,
      (FF.T₀ : Subgroup S.G) ⊔ Kloc = ⊤ ∧
      E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤ (FF.T₀ : Subgroup S.G) ⊓ Kloc ∧
      IsSylowIn 2 ((FF.T₀ : Subgroup S.G) ⊓ Kloc) Kloc ∧
      ∃ π : ↥Kloc →* CFSG.GorensteinWalter.PGL2 K,
        Function.Surjective π ∧ IsPGroup 2 ↥π.ker ∧
        (A'.subgroupOf Kloc).map π ≠ ⊥ := by

  classical
  let pkg := localPackageOfFixedFrame S FF hodd hq5
  let pkgC := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.conjugatePackageOf
    FF.F hodd (by omega : 3 < Nat.card K) S.G S.hL S.hGSO pkg
  let Kloc : Subgroup S.G :=
    (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
      FF.F FF.W S.G).subgroupOf S.G
  let Y : Subgroup S.G :=
    (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj
      FF.F).subgroupOf S.G
  let eK : ↥Kloc ≃* CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
      FF.F FF.W S.G :=
    Subgroup.subgroupOfEquivOfLe (by
      show CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
        FF.F FF.W S.G ≤ S.G
      change CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F ⊔
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ S.G
      exact sup_le (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.XConj_le_G
        FF.F S.G S.hL) (by
          rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
          exact inf_le_right))
  let pi0 := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
    FF.F hodd FF.W S.G S.hL
  let piG : ↥Kloc →* CFSG.GorensteinWalter.PGL2 K := pi0.comp eK.toMonoidHom
  have hKleG : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
      FF.F FF.W S.G ≤ S.G := by
    change CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F ⊔
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ S.G
    exact sup_le pkgC.X_conj_le_G (by
      rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
      exact inf_le_right)
  have hSleG : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G ≤ S.G := by
    rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
    exact inf_le_right
  have hSyl : IsSylowIn 2 ((FF.T₀ : Subgroup S.G) ⊓ Kloc) Kloc := by
    have h := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff (p := 2)
      (P := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G)
      (K := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj FF.F FF.W S.G)
      (H := S.G) hSleG hKleG).mpr pkgC.S_sylow_KConj
    have heq := localS_subgroupOf_eq_inf_localKConj S FF hodd hq5
    simpa [Kloc, heq] using h
  have hτ' : E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤ (FF.T₀ : Subgroup S.G) ⊓ Kloc := by
    have heq := localS_subgroupOf_eq_inf_localKConj S FF hodd hq5
    simpa [Kloc, heq] using hτ
  have hYle : Y ≤ Kloc := by
    intro x hx
    have hxO : (x : TauCeti.QuadraticMap.orthogonalGroup Qform) ∈
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F :=
      Subgroup.mem_subgroupOf.mp (by simpa [Y] using hx)
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left hxO
  have hjoin : (FF.T₀ : Subgroup S.G) ⊔ Y = ⊤ := by
    simpa [Y, CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj] using
      fixedFrame_component_join_X1 S FF hq5
  have hπ : Function.Surjective piG := pkgC.piConj_surjective.comp eK.surjective
  have hker : IsPGroup 2 ↥piG.ker := by
    change IsPGroup 2 ↥(Subgroup.comap eK.toMonoidHom
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
        FF.F hodd FF.W S.G S.hL).ker)
    exact pkgC.piConj_ker_isPGroup.comap_of_injective eK.toMonoidHom eK.injective
  have htop : (FF.T₀ : Subgroup S.G) ⊔ Kloc = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = (FF.T₀ : Subgroup S.G) ⊔ Y := hjoin.symm
      _ ≤ (FF.T₀ : Subgroup S.G) ⊔ Kloc := sup_le_sup le_rfl hYle
  exact ⟨Kloc, htop, hτ', hSyl, piG, hπ, hker,
    by simpa [Kloc, eK, piG, pi0] using hBne⟩

private theorem subgroupOf_equiv_map_eq
    {O : Type*} [Group O] {G KO : Subgroup O} (hKO : KO ≤ G)
    (A : Subgroup G) :
    (A.subgroupOf (KO.subgroupOf G)).map
        (Subgroup.subgroupOfEquivOfLe hKO).toMonoidHom =
      (A.map G.subtype).subgroupOf KO := by
  apply Subgroup.map_injective (f := KO.subtype) (Subgroup.subtype_injective KO)
  rw [Subgroup.map_map]
  have hcomp : KO.subtype.comp
      (Subgroup.subgroupOfEquivOfLe hKO).toMonoidHom =
      G.subtype.comp (KO.subgroupOf G).subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
    Subgroup.map_inf _ _ _ (Subgroup.subtype_injective G),
    Subgroup.map_subgroupOf_eq_of_le hKO,
    Subgroup.subgroupOf_map_subtype]

theorem base_or_conj_localImage_ne_bot
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K)
    {A' : Subgroup S.G} (hA'ab : CFSG.Open.IsElemAbelian 2 A')
    (hA4 : 4 ≤ Nat.card A')
    (hA'S : A' ≤ (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G).subgroupOf S.G) :
    let O := TauCeti.QuadraticMap.orthogonalGroup Qform
    let AO : Subgroup O := A'.map S.G.subtype
    let BO : Subgroup (CFSG.GorensteinWalter.PGL2 K) :=
      (AO.subgroupOf (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
        FF.F FF.W S.G)).map
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi FF.F hodd FF.W S.G)
    let BC : Subgroup (CFSG.GorensteinWalter.PGL2 K) :=
      (AO.subgroupOf (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
        FF.F FF.W S.G)).map
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
          FF.F hodd FF.W S.G S.hL)
    BO ≠ ⊥ ∨ BC ≠ ⊥ := by
  classical
  let O := TauCeti.QuadraticMap.orthogonalGroup Qform
  let AO : Subgroup O := A'.map S.G.subtype
  let BO : Subgroup (CFSG.GorensteinWalter.PGL2 K) :=
    (AO.subgroupOf (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
      FF.F FF.W S.G)).map
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi FF.F hodd FF.W S.G)
  let BC : Subgroup (CFSG.GorensteinWalter.PGL2 K) :=
    (AO.subgroupOf (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
      FF.F FF.W S.G)).map
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
        FF.F hodd FF.W S.G S.hL)
  have hAO_le_S : AO ≤ CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hA'S hy)
  have hSleK : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G ≤ CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
        FF.F FF.W S.G := le_sup_right
  have hSleKC : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS
      FF.F FF.W S.G ≤ CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
        FF.F FF.W S.G := le_sup_right
  have hkerBase : (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi
      FF.F hodd FF.W S.G).ker =
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localC
        FF.F FF.W S.G).subgroupOf
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
          FF.F FF.W S.G) :=
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi_ker_eq
      FF.F hodd (by omega : 3 < Nat.card K) FF.W S.G
  have hkerConj : (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
      FF.F hodd FF.W S.G S.hL).ker =
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localCConj
        FF.F FF.W S.G).subgroupOf
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
          FF.F FF.W S.G) :=
    CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj_ker_eq
      FF.F hodd (by omega : 3 < Nat.card K) FF.W S.G S.hL
  change BO ≠ ⊥ ∨ BC ≠ ⊥
  by_contra h
  push Not at h
  obtain ⟨hBO, hBC⟩ := h
  have hAOC : AO ≤ Subgroup.centralizer
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localX FF.F : Set O) := by
    intro x hx
    have hxK : x ∈ CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK FF.F FF.W S.G :=
      hSleK (hAO_le_S hx)
    have hxker : (⟨x, hxK⟩ : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
        FF.F FF.W S.G) ∈
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi FF.F hodd FF.W S.G).ker := by
      rw [Subgroup.map_eq_bot_iff] at hBO
      exact hBO (Subgroup.mem_subgroupOf.mpr hx)
    rw [hkerBase] at hxker
    exact (Subgroup.mem_subgroupOf.mp hxker).2
  have hAOC' : AO ≤ Subgroup.centralizer
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F : Set O) := by
    intro x hx
    have hxK : x ∈ CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj FF.F FF.W S.G :=
      hSleKC (hAO_le_S hx)
    have hxker : (⟨x, hxK⟩ : CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
        FF.F FF.W S.G) ∈
        (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj FF.F hodd FF.W S.G S.hL).ker := by
      rw [Subgroup.map_eq_bot_iff] at hBC
      exact hBC (Subgroup.mem_subgroupOf.mpr hx)
    rw [hkerConj] at hxker
    exact (Subgroup.mem_subgroupOf.mp hxker).2
  have hbot : AO ≤ (⊥ : Subgroup O) := by
    have h := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS_common_centralizer_eq_bot
      FF.F hodd (by omega : 3 < Nat.card K) FF.W S.G S.hL S.hGSO
    intro x hx
    rw [← h]
    exact ⟨⟨hAO_le_S hx, hAOC hx⟩, hAOC' hx⟩
  have hAO_eq : AO = ⊥ := le_bot_iff.mp hbot
  have hA'_bot : A' = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective A' (Subgroup.subtype_injective S.G)).mp hAO_eq
  have : Nat.card A' = 1 := by rw [hA'_bot]; simp
  omega

theorem baseLocalImage_eq
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K)
    (A' : Subgroup S.G) :
    let KO := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
      FF.F FF.W S.G
    let Kloc : Subgroup S.G := KO.subgroupOf S.G
    let eK : ↥Kloc ≃* ↥KO :=
      Subgroup.subgroupOfEquivOfLe (by
        show KO ≤ S.G
        exact (localPackageOfFixedFrame S FF hodd hq5).K_le_CG.trans inf_le_left)
    (A'.subgroupOf Kloc).map eK.toMonoidHom =
      (A'.map S.G.subtype).subgroupOf KO := by
  classical
  let KO := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
    FF.F FF.W S.G
  let Kloc : Subgroup S.G := KO.subgroupOf S.G
  let eK : ↥Kloc ≃* ↥KO :=
    Subgroup.subgroupOfEquivOfLe (by
      show KO ≤ S.G
      exact (localPackageOfFixedFrame S FF hodd hq5).K_le_CG.trans inf_le_left)
  have hKO : KO ≤ S.G := (localPackageOfFixedFrame S FF hodd hq5).K_le_CG.trans inf_le_left
  simpa [KO, Kloc, eK] using subgroupOf_equiv_map_eq (G := S.G) hKO A'

theorem conjLocalImage_eq
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K)
    (A' : Subgroup S.G) :
    let KO := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
      FF.F FF.W S.G
    let Kloc : Subgroup S.G := KO.subgroupOf S.G
    let eK : ↥Kloc ≃* ↥KO :=
      Subgroup.subgroupOfEquivOfLe (by
        show KO ≤ S.G
        change CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F ⊔
          CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ S.G
        exact sup_le (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.XConj_le_G
          FF.F S.G S.hL) (by
            rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
            exact inf_le_right))
    (A'.subgroupOf Kloc).map eK.toMonoidHom =
      (A'.map S.G.subtype).subgroupOf KO := by
  classical
  let KO := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
    FF.F FF.W S.G
  let Kloc : Subgroup S.G := KO.subgroupOf S.G
  let eK : ↥Kloc ≃* ↥KO :=
    Subgroup.subgroupOfEquivOfLe (by
      show KO ≤ S.G
      change CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F ⊔
        CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ S.G
      exact sup_le (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.XConj_le_G
        FF.F S.G S.hL) (by
          rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
          exact inf_le_right))
  have hKO : KO ≤ S.G := by
    change CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F ⊔
      CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ S.G
    exact sup_le (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.XConj_le_G
      FF.F S.G S.hL) (by
        rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
        exact inf_le_right)
  simpa [KO, Kloc, eK] using subgroupOf_equiv_map_eq (G := S.G) hKO A'

theorem aboveFive_nonzero_localData
    [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Qgrp))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Qgrp), a * b ≠ b * a) :
    ∀ Ω : Set (Subgroup S.G), E1.IsInvColl ⊤ Ω →
      (∃ A ∈ Ω, A ≤ (FF.T₀ : Subgroup S.G) ∧ 4 ≤ Nat.card A) →
      ∃ A' : Subgroup S.G,
        A' ∈ Ω ∧ A' ≤ (FF.T₀ : Subgroup S.G) ∧
        CFSG.Open.IsElemAbelian 2 A' ∧ 4 ≤ Nat.card A' ∧
        ∃ Kloc : Subgroup S.G,
          (FF.T₀ : Subgroup S.G) ⊔ Kloc = ⊤ ∧
          E1.tauOf ⊤ (FF.T₀ : Subgroup S.G) A' ≤ (FF.T₀ : Subgroup S.G) ⊓ Kloc ∧
          IsSylowIn 2 ((FF.T₀ : Subgroup S.G) ⊓ Kloc) Kloc ∧
          ∃ π : ↥Kloc →* CFSG.GorensteinWalter.PGL2 K,
            Function.Surjective π ∧ IsPGroup 2 ↥π.ker ∧
            (A'.subgroupOf Kloc).map π ≠ ⊥ := by

  classical
  intro Ω hΩ h4
  obtain ⟨A, hAΩ, hAT, hA4⟩ := h4
  have hAab : CFSG.Open.IsElemAbelian 2 A := hΩ.isElemAbelian A hAΩ
  have hpc : CFSG.Open.pCoreOf 2 (⊤ : Subgroup S.G) = ⊥ := setup_pCore_bot S hs hnab
  obtain ⟨A', hA'Ω, hA'T, hA'S, hA'ab, hA'4, hτ⟩ :=
    exists_normalized_A S FF hodd hpc hΩ hAΩ hAab hA4 hAT
  let O := TauCeti.QuadraticMap.orthogonalGroup Qform
  let AO : Subgroup O := A'.map S.G.subtype
  let BO : Subgroup (CFSG.GorensteinWalter.PGL2 K) :=
    (AO.subgroupOf (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK
      FF.F FF.W S.G)).map
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi FF.F hodd FF.W S.G)
  let BC : Subgroup (CFSG.GorensteinWalter.PGL2 K) :=
    (AO.subgroupOf (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
      FF.F FF.W S.G)).map
      (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
        FF.F hodd FF.W S.G S.hL)
  have hchoice : BO ≠ ⊥ ∨ BC ≠ ⊥ := by
    simpa [BO, BC, AO] using base_or_conj_localImage_ne_bot S FF hodd hq5 hA'ab hA'4 hA'S
  rcases hchoice with hBO | hBC
  ·
    let KO := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localK FF.F FF.W S.G
    let Kloc : Subgroup S.G := KO.subgroupOf S.G
    let eK : ↥Kloc ≃* ↥KO :=
      Subgroup.subgroupOfEquivOfLe (by
        show KO ≤ S.G
        exact (localPackageOfFixedFrame S FF hodd hq5).K_le_CG.trans inf_le_left)
    have hEq : (A'.subgroupOf Kloc).map
        ((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi
          FF.F hodd FF.W S.G).comp eK.toMonoidHom) = BO := by
      rw [← Subgroup.map_map]
      have h := baseLocalImage_eq S FF hodd hq5 A'
      simpa [KO, Kloc, eK, BO, AO] using congrArg
        (Subgroup.map (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPi
          FF.F hodd FF.W S.G)) h
    obtain ⟨Kloc', htop, hτ', hSyl, π, hπ, hker, hBne'⟩ :=
      aboveFive_localData_of_basePackage S FF hodd hq5 hτ
        (by simpa [← hEq] using hBO)
    exact ⟨A', hA'Ω, hA'T, hA'ab, hA'4, Kloc', htop, hτ', hSyl, π, hπ, hker, hBne'⟩
  ·
    let KO := CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localKConj
      FF.F FF.W S.G
    let Kloc : Subgroup S.G := KO.subgroupOf S.G
    let eK : ↥Kloc ≃* ↥KO :=
      Subgroup.subgroupOfEquivOfLe (by
        show KO ≤ S.G
        change CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositive.tPositiveDerivedConj FF.F ⊔
          CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS FF.F FF.W S.G ≤ S.G
        exact sup_le (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.XConj_le_G
          FF.F S.G S.hL) (by
            rw [CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localS]
            exact inf_le_right))
    have hEq : (A'.subgroupOf Kloc).map
        ((CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
          FF.F hodd FF.W S.G S.hL).comp eK.toMonoidHom) = BC := by
      rw [← Subgroup.map_map]
      have h := conjLocalImage_eq S FF hodd hq5 A'
      simpa [KO, Kloc, eK, BC, AO] using congrArg
        (Subgroup.map (CFSG.ClassicalGroups.Orthogonal.FiveDimensionalTPositiveSylow.localPiConj
          FF.F hodd FF.W S.G S.hL)) h
    obtain ⟨Kloc', htop, hτ', hSyl, π, hπ, hker, hBne'⟩ :=
      aboveFive_localData_of_conjugatePackage S FF hodd hq5 hτ
        (by simpa [← hEq] using hBC)
    exact ⟨A', hA'Ω, hA'T, hA'ab, hA'4, Kloc', htop, hτ', hSyl, π, hπ, hker, hBne'⟩

theorem aboveFive_nonzero_branch
    {p : ℕ} [Fact p.Prime] [Finite K] [FiniteDimensional K V]
    (S : AboveFiveSetup (K := K) (V := V) Qform Qgrp T)
    (FF : AboveFiveFixedFrame S)
    (hodd : Odd (Nat.card K)) (hq5 : 5 ≤ Nat.card K)
    (hK : Nat.card K = p) (hp : 5 < p)
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting Qgrp))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting Qgrp), a * b ≠ b * a) :
    ∀ Ω : Set (Subgroup S.G), E1.IsInvColl ⊤ Ω →
      (∀ A ∈ Ω, Nat.card A ≠ 2) →
      (∃ A ∈ Ω, A ≤ (FF.T₀ : Subgroup S.G) ∧ 4 ≤ Nat.card A) →
      E1.eGen 1 ⊤ (FF.T₀ : Subgroup S.G) Ω ⊔
        (⊤ ⊓ Subgroup.normalizer (E1.weakClosure (FF.T₀ : Subgroup S.G) Ω)) = ⊤ := by
  classical
  intro Ω hΩ _h2 h4
  obtain ⟨A', hA'Ω, hA'T, hA'ab, hA'4, Kloc, htop, hτ', hSyl, π, hπ, hker, hBne⟩ :=
    aboveFive_nonzero_localData S FF hodd hq5 hs hnab Ω hΩ h4
  exact eGen_sup_normalizer_eq_top_of_localPackage S FF hodd hq5 hK hp hΩ hA'Ω hA'T hA'ab
    Kloc Kloc le_rfl htop hτ' hSyl π hπ hker ((hA'ab.subgroupOf Kloc).map π) hBne

theorem asch4_12ASAboveFive_holds :
    Asch4_12ASAboveFive := by
  intro Q _ _ T p hp hp5 hs hnab hLie hT hFT
  haveI : Fact p.Prime := ⟨hp⟩
  let K := ZMod p
  let V := ↥(CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointSubmodule K)
  let Qform : QuadraticForm K V :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointForm K
  have hK : Nat.card K = p := Nat.card_zmod p
  have hp2 : p ≠ 2 := by omega
  have hq5 : 5 ≤ Nat.card K := by rw [hK]; omega
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact hp.odd_of_ne_two hp2
  have h2 : (2 : K) ≠ 0 := by
    intro h
    change ((2 : ℕ) : ZMod p) = 0 at h
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
    omega
  have hQ : Qform.polarBilin.Nondegenerate :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjointForm_nondegenerate h2
  have hdim : Module.finrank K V = 5 :=
    CFSG.ComponentClassification.CatalogueBOrthogonalFive.selfAdjoint_finrank h2
  obtain ⟨S⟩ := exists_aboveFiveSetup (K := K) (V := V) hp hp2 hK Qform hQ hdim T hs hnab hLie hT hFT
  let FF : AboveFiveFixedFrame S :=
    Classical.choice (exists_aboveFiveFixedFrame (K := K) (V := V) S hodd hQ hdim)
  exact aboveFive_inE_of_setup S hs hnab (FF.T₀ : Subgroup S.G) FF.hT₀ FF.hsup
    (aboveFive_nonzero_branch S FF hodd hq5 hK hp5 hs hnab)

end Assembly

end CFSG.LocalAnalysis.WeakClosure81

end
