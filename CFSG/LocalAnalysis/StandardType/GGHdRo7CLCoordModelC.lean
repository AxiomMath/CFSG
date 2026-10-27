module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordAux
public import CFSG.LocalAnalysis.StandardType.GGSpLiftReflGen
public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusLift
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallASpLift
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGTwAutBasic
public import CFSG.LocalAnalysis.StandardType.GGTwSUFacts
public import CFSG.LocalAnalysis.StandardType.GGTwSUSigned
public import CFSG.LocalAnalysis.StandardType.GGTwSURank
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelA
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

variable {G : Type} [Group G] [Finite G]

open CFSG.StandardType CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

private lemma hdRo7CLCoordAux_eq_one_of_mem_centralizer_of_center_eq_bot {X : Subgroup G}
    (hX : Subgroup.center X = ⊥) {z : G} (hzX : z ∈ X)
    (hzC : z ∈ Subgroup.centralizer (X : Set G)) : z = 1 := by
  have hz : (⟨z, hzX⟩ : X) ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2
  have hz1 : (⟨z, hzX⟩ : X) ∈ (⊥ : Subgroup X) := by
    rw [← hX]
    exact hz
  simpa using Subgroup.mem_bot.mp hz1

private def hdRo7CLCoordAux_prodHom (Bs X : Subgroup G) :
    ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) →* ↥Bs where
  toFun q := ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' q r := by
    apply Subtype.ext
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    have h : (r.1 : G) * (q.2 : G) = (q.2 : G) * (r.1 : G) :=
      Subgroup.mem_centralizer_iff.mp q.2.2.2 (r.1 : G) r.1.2.2
    calc ((q.1 : G) * (r.1 : G)) * ((q.2 : G) * (r.2 : G))
        = (q.1 : G) * ((r.1 : G) * (q.2 : G)) * (r.2 : G) := by group
      _ = (q.1 : G) * ((q.2 : G) * (r.1 : G)) * (r.2 : G) := by rw [h]
      _ = ((q.1 : G) * (q.2 : G)) * ((r.1 : G) * (r.2 : G)) := by group

private lemma hdRo7CLCoordAux_prodHom_bijective {p : ℕ} {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hZ : Subgroup.center X = ⊥) (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    Function.Bijective (hdRo7CLCoordAux_prodHom Bs X) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨x, hx⟩, ⟨c, hc⟩⟩ ⟨⟨x', hx'⟩, ⟨c', hc'⟩⟩ h
    have h' : x * c = x' * c' := congrArg Subtype.val h
    have hxX : x ∈ X := hx.2
    have hx'X : x' ∈ X := hx'.2
    have hcC : c ∈ Subgroup.centralizer (X : Set G) := hc.2
    have hc'C : c' ∈ Subgroup.centralizer (X : Set G) := hc'.2
    have hz_eq : x'⁻¹ * x = c' * c⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * c) * c⁻¹ := by group
        _ = x'⁻¹ * (x' * c') * c⁻¹ := by rw [h']
        _ = c' * c⁻¹ := by group
    have hzX : x'⁻¹ * x ∈ X := X.mul_mem (X.inv_mem hx'X) hxX
    have hzC : x'⁻¹ * x ∈ Subgroup.centralizer (X : Set G) := by
      rw [hz_eq]
      exact (Subgroup.centralizer (X : Set G)).mul_mem hc'C
        ((Subgroup.centralizer (X : Set G)).inv_mem hcC)
    have hz1 : x'⁻¹ * x = 1 := hdRo7CLCoordAux_eq_one_of_mem_centralizer_of_center_eq_bot hZ hzX hzC
    have hxeq : x = x' := (inv_mul_eq_one.mp hz1).symm
    have hceq : c = c' := by
      apply mul_left_cancel (a := x)
      rw [← hxeq] at h'
      exact h'
    exact Prod.ext (Subtype.ext hxeq) (Subtype.ext hceq)
  · intro b
    obtain ⟨x, hx, c, hc, hbc⟩ := ggBstar_split_of_inner hBs hZ hnorm hinner b.1 b.2
    exact ⟨(⟨x, hx⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩

private noncomputable def hdRo7CLCoordAux_prodEquiv {p : ℕ} {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hZ : Subgroup.center X = ⊥) (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹) :
    ↥(Bs ⊓ X) × ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≃* ↥Bs :=
  MulEquiv.ofBijective (hdRo7CLCoordAux_prodHom Bs X) (hdRo7CLCoordAux_prodHom_bijective hBs hZ hnorm hinner)

private noncomputable def hdRo7CLCoordAux_subgroupOfEquiv (Bs X : Subgroup G) :
    ↥((Bs ⊓ X).subgroupOf X) ≃* ↥(Bs ⊓ X) where
  toFun x := ⟨((x : ↥X) : G), Subgroup.mem_subgroupOf.mp x.2⟩
  invFun x := ⟨⟨(x : G), x.2.2⟩, Subgroup.mem_subgroupOf.mpr x.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl
  map_mul' x y := Subtype.ext rfl

private lemma hdRo7CLCoordAux_card_subgroupOf (Bs X : Subgroup G) :
    Nat.card ↥((Bs ⊓ X).subgroupOf X) = Nat.card ↥(Bs ⊓ X) :=
  Nat.card_congr (hdRo7CLCoordAux_subgroupOfEquiv Bs X).toEquiv

private def hdRo7CLCoordAux_SignedData (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ X)),
    Function.Injective τ ∧ Function.Surjective τ ∧
    (∀ i : Fin k, ∃ w : X, ∀ f,
      (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (SpCoord.sgnAut i f) : G)) ∧
    (∀ σ : Equiv.Perm (Fin k), ∃ w : X, ∀ f,
      (w : G) * (τ f : G) * (w : G)⁻¹ = (τ (SpCoord.permAut σ f) : G)) ∧
    ∀ g : X, (∀ e : ↥(Bs ⊓ X), ∃ e' : ↥(Bs ⊓ X),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', (g : G) * (τ f : G) * (g : G)⁻¹ = (τ f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i)

private lemma hdRo7CLCoordAux_signedData_of_signedEltSC {p : ℕ} {B Bs X : Subgroup G}
    (hBs : GGBstar p B Bs) (hZ : Subgroup.center X = ⊥)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hEab : IsElemAbelian p (Bs ⊓ X)) (h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ X))
    (h : GGTorusSignedEltSC p ↥X) : hdRo7CLCoordAux_SignedData p Bs X := by
  have hEab' : IsElemAbelian p ((Bs ⊓ X).subgroupOf X) := hEab.subgroupOf X
  have h3' : p ^ 3 ≤ Nat.card ↥((Bs ⊓ X).subgroupOf X) := by
    rw [hdRo7CLCoordAux_card_subgroupOf]; exact h3
  have hsc : ∀ g : ↥X, (∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e = e * g) → g ^ p = 1 →
      g ∈ (Bs ⊓ X).subgroupOf X := by
    intro g hgc hgp
    rw [Subgroup.mem_subgroupOf] at ⊢
    refine Subgroup.mem_inf.mpr ⟨hBs.2.2.2 (g : G) ?_ ?_, g.2⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨e, he, c, hc, rfl⟩ := ggBstar_split_of_inner hBs hZ hnorm hinner b hb
      have hge : (g : G) * (e : G) = (e : G) * (g : G) := by
        have h1 := hgc ⟨(e : G), he.2⟩ (Subgroup.mem_subgroupOf.mpr he)
        simpa only [Subgroup.coe_mul] using congrArg Subtype.val h1
      have hgc' : (g : G) * (c : G) = (c : G) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp hc.2 (g : G) g.2
      have key : (g : G) * ((e : G) * (c : G)) = ((e : G) * (c : G)) * (g : G) := by
        calc (g : G) * ((e : G) * (c : G)) = ((g : G) * e) * c := by group
          _ = ((e : G) * g) * c := by rw [hge]
          _ = (e : G) * ((g : G) * c) := by group
          _ = (e : G) * ((c : G) * (g : G)) := by rw [hgc']
          _ = ((e : G) * (c : G)) * (g : G) := by group
      exact key.symm
    · simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hgp
  obtain ⟨k, τ, hτinj, hτrange, hsgn, hperm, hnorm⟩ :=
    h ((Bs ⊓ X).subgroupOf X) hEab' h3' hsc
  let eτ : (Fin k → Multiplicative (ZMod p)) ≃* ↥(Bs ⊓ X) :=
    (MonoidHom.ofInjective hτinj).trans
      ((MulEquiv.subgroupCongr hτrange).trans (hdRo7CLCoordAux_subgroupOfEquiv Bs X))
  have hcoe : ∀ f, (eτ.toMonoidHom f : G) = (τ f : G) := fun f => rfl
  refine ⟨k, eτ.toMonoidHom, eτ.injective, eτ.surjective, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨w, hw⟩ := hsgn i
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.sgnAut i f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro σ
    obtain ⟨w, hw⟩ := hperm σ
    refine ⟨w, fun f => ?_⟩
    rw [hcoe f, hcoe (SpCoord.permAut σ f)]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using congrArg Subtype.val (hw f)
  · intro g hg
    have hg' : ∀ e ∈ (Bs ⊓ X).subgroupOf X, g * e * g⁻¹ ∈ (Bs ⊓ X).subgroupOf X := by
      intro e he
      rw [Subgroup.mem_subgroupOf] at he
      obtain ⟨e', he'⟩ := hg ⟨(e : G), he⟩
      rw [Subgroup.mem_subgroupOf]
      have h1 : ((g * e * g⁻¹ : ↥X) : G) = (e' : G) := by
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using he'
      rw [h1]
      exact e'.2
    obtain ⟨π, ε, hε, hrel⟩ := hnorm g hg'
    refine ⟨π, ε, hε, fun f f' hff' => hrel f f' ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hcoe f, hcoe f'] at hff'
    exact hff'

open CFSG.StandardType CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem hdRo7CLCoordAux_recipe_symplectic {lab : LargeEvenLabel}
    (htag : lab.tag = LargeEvenLieTag.B ∨ lab.tag = LargeEvenLieTag.C)
    {Q : LargeEvenRawCont} (h : LargeEvenRawDatum lab Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2 ^ lab.n ∧
      Q (LargeEvenProj (LargeEvenSpGroup K lab.rank))
        (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K lab.rank))
          (LargeEvenGSpSet K lab.rank))
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K lab.rank))) := by
  rcases htag with hB | hC
  · unfold LargeEvenRawDatum at h
    rw [hB] at h
    unfold LargeEvenRecipeSymplectic at h
    obtain ⟨K, hKfield, hKfin, hKcard, hQ⟩ := h
    refine ⟨K, hKfield, hKfin, charP_two_of_card hKcard, hKcard, ?_⟩
    simpa using hQ
  · unfold LargeEvenRawDatum at h
    rw [hC] at h
    unfold LargeEvenRecipeSymplectic at h
    obtain ⟨K, hKfield, hKfin, hKcard, hQ⟩ := h
    refine ⟨K, hKfield, hKfin, charP_two_of_card hKcard, hKcard, ?_⟩
    simpa using hQ

theorem hdRo7CLCoordAux_innerDiagOnLabel_of_row
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G)
    (hRig : GGLabelRigidInput) (hH : GGResHyp p B Bs x L D J y K)
    (hrow : GGResRowAt ggRowCorank2C p J L) :
    GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L := by
  obtain ⟨labJ, labL, hJ2, hL2, _, hHasL, hp3, htagJ, hnJ, htagL, hnL, hrank⟩ := hrow
  have hID : GGInnerDiagOn Bs L := hH.2.2.1.1
  exact largeEvenMarking_mono
    (fun lab' R _ I F θ hθ => by
      obtain ⟨rfl, hBsN, hBs3⟩ := hθ
      exact ⟨⟨hp3, htagL, hnL, hdRo7CLCoordAux_rank_ge_five hJ2 hnJ htagJ hrank⟩, hBsN, hBs3⟩)
    (ggInnerDiagOn_relabel hRig hID hL2 hHasL)

omit [Finite G] in
theorem hdRo7CLCoordAux_torus_data_of_innerDiag
    (p : ℕ) (Bs L : Subgroup G)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L) :
    ∃ (R : Type) (_ : Group R) (I : Set (MulAut R)) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
      (_hBsN : Bs ≤ Subgroup.normalizer (L : Set G)),
      commutator ↥L = ⊤ ∧ GGTorusSignedEltSC p R ∧ GGCenterPrime p R ∧
      Subgroup.center R = ⊥ ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧
      (∀ b ∈ Bs, ∃ φ ∈ I,
        LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ) := by
  classical
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨_, _, _, _, _, _, _, hS, _, _⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hp3, htag, hn, h5⟩ := hS
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, hQK⟩ :=
    hdRo7CLCoordAux_recipe_symplectic htag hraw
  obtain ⟨_, _, hθ⟩ := hQK
  obtain ⟨θ, _, hBsN, hBs3⟩ := hθ
  have hp : Nat.Prime p := by rw [hp3]; norm_num
  have hp2 : p ≠ 2 := by omega
  have h2rank : 2 ≤ lab.rank := by
    have h := hlab
    unfold LargeEvenInLambda2 at h
    rcases htag with hB | hC
    · rw [hB] at h; exact h.2.1
    · rw [hC] at h; exact h.2.1
  have : NeZero lab.rank := ⟨by omega⟩
  have hpK : p ∣ Nat.card K + 1 := by rw [hKcard, hn, hp3]; norm_num
  exact ⟨LargeEvenProj (LargeEvenSpGroup K lab.rank), inferInstance,
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K lab.rank)) (LargeEvenGSpSet K lab.rank),
    θ, hBsN, hperf,
    ggSpNonsplitSignedEltInput_holds K lab.rank p h2rank hp hpK,
    ggCenterPrime_sp (K := K) hp hp2,
    TableBSymp.center_spProj_eq_bot,
    TableBSymp.sp_I_subset_inn,
    hBs3⟩

theorem hdRo7CLCoordAux_ker_gamma_eq (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (y : G) (K : Subgroup G) (hH : GGResHyp p B Bs x L D J y K)
    {hBsN : Bs ≤ Subgroup.normalizer (L : Set G)} :
    (ggGamma L hBsN).ker = (Subgroup.zpowers x).subgroupOf Bs := by
  ext b
  rw [MonoidHom.mem_ker, ggGamma_eq_one_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hbC
    have hb : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := ⟨b.2, hbC⟩
    rwa [hdRo7CLCoordAux_bstar_centralizer_eq hH] at hb
  · intro hbx
    have hb : (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rwa [hdRo7CLCoordAux_bstar_centralizer_eq hH]
    exact hb.2

open CFSG.StandardType CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC {X : Type} [Group X]
    {tag : LargeEvenLieTag} (htag : tag = .B ∨ tag = .C) {n f : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f)
    (hX : GGHasLabel ⟨tag, n, f⟩ X) : StatedClassicalModel X .PSp n 2 f := by
  rcases htag with rfl | rfl
  · obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
    refine ⟨⟨Nat.prime_two, hf, by omega, ?_⟩, K, hF, hfin, hK, ⟨e⟩⟩
    intro h
    simp only [Prod.mk.injEq] at h
    omega
  · obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hX
    refine ⟨⟨Nat.prime_two, hf, by omega, ?_⟩, K, hF, hfin, hK, ⟨e⟩⟩
    intro h
    simp only [Prod.mk.injEq] at h
    omega

theorem hdRo7CLCoordAux_center_L_eq_bot_of_hasLabel
    (L : Subgroup G) (hperf : commutator ↥L = ⊤) (lab : LargeEvenLabel)
    (htag : lab.tag = .B ∨ lab.tag = .C) (hn : lab.n = 1) (h4 : 4 ≤ lab.rank)
    (hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L)) :
    Subgroup.center ↥L = ⊥ := by
  have hmodel : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp lab.rank 2 lab.n :=
    hdRo7CLCoordAux_statedClassicalModel_of_hasLabel_BC htag (by omega) (by omega) hhas
  obtain ⟨φ, hinj, hrange⟩ :=
    ggSpLiftInput_holds G L lab.rank lab.n (by omega) hperf hmodel
  have hZsp : Subgroup.center (StatedSp lab.rank (GaloisField 2 lab.n)) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have he := Subgroup.map_center_eq (MonoidHom.ofInjective hinj)
  rw [hZsp, Subgroup.map_bot] at he
  rw [← hrange]
  exact he.symm

theorem hdRo7CLCoordAux_center_L_eq_bot_of_innerDiag
    (p : ℕ) (Bs L : Subgroup G)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank) p Bs L) :
    Subgroup.center ↥L = ⊥ := by
  have hperf : commutator ↥L = ⊤ := hM.1
  obtain ⟨lab, _, hhas, _, _, _, _, _, hS, _, _⟩ := largeEvenMarking_exists_hasLabel hM
  obtain ⟨-, htag, hn, h5⟩ := hS
  exact hdRo7CLCoordAux_center_L_eq_bot_of_hasLabel L hperf lab htag hn (by omega) hhas

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

variable {G : Type} [Group G] [Finite G]

theorem hdRo7CLCoordAux_signedModelSC_data_of_outdiagPrime
    (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) (y : G) (K : Subgroup G)
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3)
    (R : Type) [Group R] (I : Set (MulAut R)) (θ : ↥L ⧸ Subgroup.center ↥L ≃* R)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hTSC : GGTorusSignedEltSC p R) (hCP : GGCenterPrime p R)
    (hcenter : Subgroup.center R = ⊥) (hI : GGOutdiagPrime p R I)
    (hperf : commutator ↥L = ⊤)
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥L => (l' : G) = b⁻¹ * (l : G) * b) φ) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥(ggGamma L hBsN).range),
      3 ≤ k ∧
      (∀ n : ↥L, MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L)) →
        GGTorusWeylElt p (ggGamma L hBsN).range n) ∧
      (∀ i : Fin k, ∃ (n : ↥L)
        (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L))),
        ggConjAut (ggGamma L hBsN).range hn = MulAut.congr Θ (sgnAut i)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ (n : ↥L)
        (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L))),
        ggConjAut (ggGamma L hBsN).range hn = MulAut.congr Θ (permAut σ)) ∧
      ∀ (n : ↥L)
        (hn : MulAut.conj n ∈ Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L))),
        IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut (ggGamma L hBsN).range hn)) := by
  classical
  have hp : Nat.Prime p := hH.1.tableB_facts.1
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  set A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range with hAdef
  have hAab : IsElemAbelian p A := by
    refine isElemAbelian_range (fun a b => ?_) (fun a => ?_) (ggGamma L hBsN)
    · exact Subtype.ext (TableB.IsElemAbelian.comm hH.1.tableB_facts.2.1 a.2 b.2)
    · exact Subtype.ext (hH.1.tableB_facts.2.1.2 a a.2)
  have hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : ↥L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨φ, hφ, hφind⟩ := hBs3 (b⁻¹) (Bs.inv_mem b.2)
    refine ⟨φ, hφ, fun l => ?_⟩
    have hcoe : (((ggGamma L hBsN b) l : ↥L) : G) = (b : G) * (l : G) * (b : G)⁻¹ :=
      ggGamma_coe L hBsN b l
    exact hφind l ((ggGamma L hBsN b) l) (by simpa using hcoe)
  have hker : (ggGamma L hBsN).ker = (Subgroup.zpowers x).subgroupOf Bs :=
    hdRo7CLCoordAux_ker_gamma_eq p B Bs x L D J y K hH
  have hcardker : Nat.card ↥((Subgroup.zpowers x).subgroupOf Bs) = p := by
    have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxBs)).toEquiv,
      Nat.card_zpowers]
    exact orderOf_eq_prime (hdRo7CLCoordAux_x_pow_eq_one hH) (hdRo7CLCoordAux_x_ne_one hH)
  have hcardA : Nat.card A * p = Nat.card ↥Bs := by
    have h1 := TableB.card_range_mul_card_ker (ggGamma L hBsN)
    rw [hker, hcardker] at h1
    simpa only [hAdef] using h1
  have h3 : p ^ 3 ≤ Nat.card A := by
    have h4 : p ^ 4 ≤ Nat.card ↥Bs := hdRo7CLCoordAux_card_bstar_ge hH
    have hle : p ^ 3 * p ≤ Nat.card A * p := by
      calc p ^ 3 * p = p ^ 4 := by ring
        _ ≤ Nat.card ↥Bs := h4
        _ = Nat.card A * p := hcardA.symm
    exact Nat.le_of_mul_le_mul_right hle hp.pos
  have hsc : GGTorusSelfCent p A :=
    ggTorusSelfCent_ggGamma hBsN hH.1.2.1.2.2.2
  have hψ : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
  have hker' : (ggQuotHom θ).ker ≤ Subgroup.center ↥L := by
    rw [ker_ggQuotHom]
  have hAI' : ∀ a ∈ A, ∃ φ ∈ {φ ∈ I | φ ^ p = 1},
      ∀ l : ↥L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    exact ⟨φ, ⟨hφI, ggTw_pow_eq_one_of_lift hψ hφ (hAab.2 a ha)⟩, hφ⟩
  obtain ⟨k, Θ, hk, hW, hS, hP, hN⟩ :=
    exists_signedModelSC (I := {φ ∈ I | φ ^ p = 1}) hp hp2
      (fun φ hφ => hI φ hφ.1 hφ.2) hcenter hCP hTSC hψ hker' hperf hAab hAI' h3 hsc
  exact ⟨k, Θ, hk, hW, hS, hP, hN⟩

end CFSG.StandardType.HdRo7C

end
