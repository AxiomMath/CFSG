module
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1ONorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDL1InvFixO
public import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1PhanTransfer
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1OAutFix
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1OHyp
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
import CFSG.LocalAnalysis.StandardType.GGQTwoBlockAsmPair
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux5
import CFSG.LocalAnalysis.StandardType.GGResidualRk1FrameRest
import CFSG.RankThree.PartOne.S11d.OrthCaseH
import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Main8

public section

namespace CFSG.StandardType.QTwo
open CFSG.Assembly
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions (omegaGroup mem_omegaGroup)
open CFSG.ClassicalInvolution.PhanDn (suEndN)
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary (coordBlockSU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open QuadraticMap (polarBilin)
open Multiplicative
private theorem p9uOCnt_trans_conj_mul {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W)
    (f g : W ≃ₗ[K] W) :
    e.trans ((f * g).trans e.symm) =
      (e.trans (f.trans e.symm)) * (e.trans (g.trans e.symm)) := by
  ext x
  simp only [LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply]
private def p9uOCnt_conjHom {K : Type*} [Field K] {V W : Type*} [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) :
    (W ≃ₗ[K] W) →* (V ≃ₗ[K] V) where
  toFun g := e.trans (g.trans e.symm)
  map_one' := by
    ext x
    simp only [LinearEquiv.trans_apply, LinearEquiv.coe_one, id, LinearEquiv.symm_apply_apply]
  map_mul' f g := p9uOCnt_trans_conj_mul e f g
private theorem p9uOCnt_conjHom_injective {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) :
    Function.Injective (p9uOCnt_conjHom e) := by
  intro f g hfg
  ext x
  have h := congrArg (fun φ : V ≃ₗ[K] V => φ (e.symm x)) hfg
  have h' : e.symm (f x) = e.symm (g x) := by
    simpa [p9uOCnt_conjHom, LinearEquiv.trans_apply] using h
  exact e.symm.injective h'
private theorem p9uOCnt_center_eq_bot {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hZ : Subgroup.center ↥L = ⊥)
    {z : ↥(orthDerived Φ.Q)} (hz : ∀ y, z * y = y * z) : z = 1 := by
  have hmem : ∀ y : ↥(orthDerived Φ.Q), Φ.ψ y ∈ L := by
    intro y
    have h : Φ.ψ y ∈ Φ.ψ.range := ⟨y, rfl⟩
    rwa [Φ.hrange] at h
  have hc : (⟨Φ.ψ z, hmem z⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    have hg' : (l : G) ∈ Φ.ψ.range := by rw [Φ.hrange]; exact l.2
    obtain ⟨y, hy⟩ := hg'
    apply Subtype.ext
    show (l : G) * Φ.ψ z = Φ.ψ z * (l : G)
    rw [← hy, ← map_mul, ← map_mul, hz y]
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : Φ.ψ z = 1 := congrArg Subtype.val hc
  exact Φ.hinj (by rw [h1, map_one])
private theorem p9uOCnt_beta_eq_one {p : ℕ} {G : Type} [Group G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hZ : Subgroup.center ↥L = ⊥) {b : ↥Bs}
    (hb : (b : G) ∈ Subgroup.centralizer (L : Set G)) : Φ.β b = 1 := by
  have hmem : ∀ y : ↥(orthDerived Φ.Q), Φ.ψ y ∈ L := by
    intro y
    have h : Φ.ψ y ∈ Φ.ψ.range := ⟨y, rfl⟩
    rwa [Φ.hrange] at h
  have hconj : ∀ y : ↥(orthDerived Φ.Q), Φ.β b * y * (Φ.β b)⁻¹ = y := by
    intro y
    apply Φ.hinj
    rw [Φ.hcompat b y]
    have h1 := (Subgroup.mem_centralizer_iff.mp hb) (Φ.ψ y) (hmem y)
    rw [h1.symm]
    group
  have hc : ∀ y : ↥(orthDerived Φ.Q), Φ.β b * y = y * (Φ.β b) := by
    intro y
    calc Φ.β b * y = (Φ.β b * y * (Φ.β b)⁻¹) * (Φ.β b) := by group
      _ = y * (Φ.β b) := by rw [hconj y]
  exact p9uOCnt_center_eq_bot Φ hZ hc
theorem qtwoDL1_baseO_centChart_of_torus_fixed (ha₀ : GGLNoncyclicInput) {G : Type}
    [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥L = ⊥) [Algebra Φ.F (GaloisField 2 2)] (C : QTwoDL1ONormChart Φ)
    {i j k : Fin Φ.r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {w₀ w₁ : ↥(orthDerived Φ.Q)}
    (hw₀ : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (SpCoord.permAut (Equiv.swap i j) f))
    (hw₁ : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (SpCoord.permAut (Equiv.swap j k) f))
    {r₀ r₀' : MulAut ↥Bs}
    (hr₀ : ∀ s : ↥Bs, ((r₀ s : ↥Bs) : G) = Φ.ψ w₀ * (s : G) * (Φ.ψ w₀)⁻¹)
    (hr₀' : ∀ s : ↥Bs, ((r₀' s : ↥Bs) : G) = Φ.ψ w₁ * (s : G) * (Φ.ψ w₁)⁻¹)
    (hrep : ∀ α : MulAut ↥(orthDerived Φ.Q),
      (∀ (f : Fin Φ.r → Multiplicative (ZMod p)), f i = f j → f j = f k →
        ∀ t : ↥(orthDerived Φ.Q), (t : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ f → α t = t) →
      ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q,
        ∀ y : ↥(orthDerived Φ.Q),
          (α y : Φ.V ≃ₗ[Φ.F] Φ.V) = g * (y : Φ.V ≃ₗ[Φ.F] Φ.V) * g⁻¹) :
    Nat.card ↥(ggOTwoPrime (L ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G) : Set G))) ≤ 216 ∧
      ∀ c ∈ Subgroup.centralizer
          ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G) : Set G),
        (∃ n : ℕ, c ^ (2 ^ n) = 1) →
          ∃ t ∈ ggOTwoPrime (L ⊓ Subgroup.centralizer
              ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G) : Set G)),
            ∀ y ∈ L, c * y * c⁻¹ = t * y * t⁻¹ := by
  classical
  have hpp : p.Prime := (ggRouteCfg_prime hcfg).1
  have : Fact p.Prime := ⟨hpp⟩
  have hBN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hcfg.1.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.1.1.2.2.2.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hS.2.2.2.1.1
  have hxBs : x ∈ Bs := hcfg.1.1.2.1.1 hS.2.1
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    ha₀ G p B x L hcfg.1.1.1
  let A : Subgroup G := (ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G)
  let eL : ↥(orthDerived Φ.Q) ≃* ↥L :=
    (MonoidHom.ofInjective Φ.hinj).trans (MulEquiv.subgroupCongr Φ.hrange)
  have heL : ∀ z : ↥(orthDerived Φ.Q), ((eL z : ↥L) : G) = Φ.ψ z := fun z => rfl
  have hQ : (polarBilin Φ.Q).Nondegenerate := qtwoDL1_oChart_nondeg Φ C
  have hfin : Module.finrank Φ.F Φ.V = 2 * Φ.r := qtwoDL1_oChart_finrank Φ C
  have h5f : 5 ≤ Module.finrank Φ.F Φ.V := by
    have hr := Φ.hr
    rw [hfin]
    omega
  have hωD : omegaGroup Φ.Q hQ ≤ orthDerived Φ.Q :=
    CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ
      (CFSG.RankThree.PartOne.exists_threeSingular_of_dim Φ.Q hQ Φ.hr hfin)
  have hxcent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := hLx hl
    rw [Subgroup.mem_centralizer_iff] at h
    simpa using (h x (Set.mem_singleton x)).symm
  have hβx : Φ.β ⟨x, hxBs⟩ = 1 := p9uOCnt_beta_eq_one Φ hZ hxcent
  have hxA : x ∈ A :=
    (qtwoDL1_oChart_mem_hyp_iff Φ hZ hBN hw₀ hw₁ hr₀ hr₀' ⟨x, hxBs⟩).mpr
      ⟨1, by
        rw [map_one]
        simpa using congrArg (fun z : ↥(orthDerived Φ.Q) => (z : Φ.V ≃ₗ[Φ.F] Φ.V)) hβx,
        rfl, rfl⟩
  have hcN : ∀ c ∈ Subgroup.centralizer (A : Set G),
      c ∈ Subgroup.normalizer (L : Set G) := by
    intro c hc
    apply mem_normalizer_of_sstar hS hnc
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact Subgroup.mem_centralizer_iff.mp hc x hxA
  constructor
  ·
    let J : Finset (Fin Φ.r) := {i, j, k}
    let SUblock : Subgroup
        ((Fin Φ.r → GaloisField 2 2) ≃ₗ[Φ.F] (Fin Φ.r → GaloisField 2 2)) :=
      (coordBlockSU (GaloisField 2 2) 2 1 J).map
        (suEndN (F := Φ.F) (unitaryInvolution (GaloisField 2 2) 2 1) Φ.r)
    have hJcard : J.card = 3 := by
      simp only [J]
      exact Finset.card_triple_eq_three_iff.mpr ⟨hij, hik, hjk⟩
    have hK4 : Nat.card (GaloisField 2 2) = 4 := by
      rw [GaloisField.card (p := 2) (n := 2) (by norm_num)]
      norm_num
    have hSUcard : Nat.card ↥SUblock ≤ 216 := by
      rw [Subgroup.card_map_of_injective
        (CFSG.ClassicalInvolution.PhanDn.suEndN_injective
          (unitaryInvolution (GaloisField 2 2) 2 1) Φ.r)]
      rw [natCard_coordBlockSU, hJcard, qTwoS34_card_Su_three hK4]
    let conjHom : (Φ.V ≃ₗ[Φ.F] Φ.V) →*
        ((Fin Φ.r → GaloisField 2 2) ≃ₗ[Φ.F] (Fin Φ.r → GaloisField 2 2)) :=
      p9uOCnt_conjHom C.χ.symm
    let Θ : Subgroup ↥(orthDerived Φ.Q) :=
      (SUblock.comap conjHom).subgroupOf (orthDerived Φ.Q)
    have hΘcard : Nat.card ↥Θ ≤ 216 := by
      have hinj : Function.Injective
          (conjHom.comp (orthDerived Φ.Q).subtype) :=
        (p9uOCnt_conjHom_injective C.χ.symm).comp Subtype.val_injective
      have hle : Θ.map (conjHom.comp (orthDerived Φ.Q).subtype) ≤ SUblock := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
        exact Subgroup.mem_subgroupOf.mp hw
      calc Nat.card ↥Θ = Nat.card ↥(Θ.map (conjHom.comp (orthDerived Φ.Q).subtype)) :=
            (Subgroup.card_map_of_injective hinj).symm
        _ ≤ Nat.card ↥SUblock := Subgroup.card_le_of_le hle
        _ ≤ 216 := hSUcard
    have hker : ggOTwoPrime (L ⊓ Subgroup.centralizer (A : Set G)) ≤ Θ.map Φ.ψ := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro y ⟨hy, hy2⟩
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyL, hyC⟩ := hy
      obtain ⟨n, hn⟩ := hy2
      have hyrange : y ∈ Φ.ψ.range := by rw [Φ.hrange]; exact hyL
      obtain ⟨u, hu⟩ := hyrange
      have hψu : Φ.ψ u = y := hu
      have huO : (u : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q :=
        Subgroup.commutator_le_self _ u.2
      have hu2 : (u : Φ.V ≃ₗ[Φ.F] Φ.V) ^ (2 ^ n) = 1 := by
        have h := congrArg (fun z : ↥(orthDerived Φ.Q) => (z : Φ.V ≃ₗ[Φ.F] Φ.V)) (show
          u ^ (2 ^ n) = 1 from by
            apply Φ.hinj
            simp [map_pow, hψu, hn])
        simpa using h
      have hgc : ∀ f : Fin Φ.r → Multiplicative (ZMod p), f i = f j → f j = f k →
          (u : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f = Φ.Δ.τ f * (u : Φ.V ≃ₗ[Φ.F] Φ.V) := by
        intro f hfi hfj
        obtain ⟨b, hb⟩ := Φ.hβsurj (Φ.Δ.τ f) (le_of_eq Φ.Δ.τ_range ⟨f, rfl⟩)
        have hbA : (b : G) ∈ A :=
          (qtwoDL1_oChart_mem_hyp_iff Φ hZ hBN hw₀ hw₁ hr₀ hr₀' b).mpr ⟨f, hb, hfi, hfj⟩
        have hyb : (b : G) * y = y * (b : G) :=
          Subgroup.mem_centralizer_iff.mp hyC (b : G) hbA
        have hconj : Φ.β b * u * (Φ.β b)⁻¹ = u := by
          apply Φ.hinj
          rw [Φ.hcompat b u, hψu]
          have h1 : (b : G) * y * (b : G)⁻¹ = y := by rw [hyb]; group
          rw [h1]
        have hkey : (Φ.Δ.τ f) * (u : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.Δ.τ f)⁻¹ =
            (u : Φ.V ≃ₗ[Φ.F] Φ.V) := by
          have h := congrArg (fun z : ↥(orthDerived Φ.Q) => (z : Φ.V ≃ₗ[Φ.F] Φ.V)) hconj
          simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
          rw [hb] at h
          exact h
        calc (u : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f
            = ((Φ.Δ.τ f) * (u : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.Δ.τ f)⁻¹) * (Φ.Δ.τ f) := by
              rw [hkey]
          _ = Φ.Δ.τ f * (u : Φ.V ≃ₗ[Φ.F] Φ.V) := by group
      obtain ⟨⟨s, hs, hsu⟩, -⟩ := qtwoDL1_oChart_block Φ hF C hij hjk hik huO hgc ⟨n, hu2⟩
      have hconjEq : conjHom (u : Φ.V ≃ₗ[Φ.F] Φ.V) = suEndN (F := Φ.F)
          (unitaryInvolution (GaloisField 2 2) 2 1) Φ.r s := by
        refine LinearEquiv.ext (fun x => ?_)
        obtain ⟨v, rfl⟩ := C.χ.surjective x
        simpa [conjHom, p9uOCnt_conjHom, LinearEquiv.trans_apply] using hsu v
      have huΘ : u ∈ Θ := Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_comap.mpr (by
          rw [hconjEq]
          exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩))
      exact Subgroup.mem_map.mpr ⟨u, huΘ, hψu⟩
    calc Nat.card ↥(ggOTwoPrime (L ⊓ Subgroup.centralizer (A : Set G)))
        ≤ Nat.card ↥(Θ.map Φ.ψ) := Subgroup.card_le_of_le hker
      _ = Nat.card ↥Θ := Subgroup.card_map_of_injective Φ.hinj
      _ ≤ 216 := hΘcard
  ·
    intro c hc h2
    obtain ⟨n, hn⟩ := h2
    have hcN' : c ∈ Subgroup.normalizer (L : Set G) := hcN c hc
    let αL : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨c, hcN'⟩
    have hαLcoe : ∀ z : ↥L, ((αL z : ↥L) : G) = c * (z : G) * c⁻¹ := fun z =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨c, hcN'⟩ z
    have hαLpow : αL ^ (2 ^ n) = 1 := by
      have hpow : (⟨c, hcN'⟩ : Subgroup.normalizer (L : Set G)) ^ (2 ^ n) = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, hn]
      have h := map_pow (Subgroup.normalizerMonoidHom L)
        (⟨c, hcN'⟩ : Subgroup.normalizer (L : Set G)) (2 ^ n)
      rw [hpow, map_one] at h
      simpa [αL] using h.symm
    let α : MulAut ↥(orthDerived Φ.Q) := eL.trans (αL.trans eL.symm)
    have hαsym : ∀ z : ↥(orthDerived Φ.Q), eL (α z) = αL (eL z) := by
      intro z
      simp [α, MulEquiv.trans_apply]
    have hαpow_apply : ∀ (m : ℕ) (z : ↥(orthDerived Φ.Q)),
        (α ^ m) z = eL.symm ((αL ^ m) (eL z)) := by
      intro m
      induction m with
      | zero => intro z; simp [α]
      | succ m ih =>
        intro z
        rw [pow_succ', MulAut.mul_apply, ih]
        have h1 : α (eL.symm ((αL ^ m) (eL z))) =
            eL.symm (αL ((αL ^ m) (eL z))) := by
          simp [α, MulEquiv.trans_apply]
        rw [h1, pow_succ', MulAut.mul_apply]
    have hαn : α ^ (2 ^ n) = 1 := by
      apply MulEquiv.ext
      intro z
      rw [hαpow_apply, hαLpow, MulAut.one_apply, MulEquiv.symm_apply_apply, MulAut.one_apply]
    have hατ : ∀ (f : Fin Φ.r → Multiplicative (ZMod p)), f i = f j → f j = f k →
        ∀ t : ↥(orthDerived Φ.Q), (t : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ f → α t = t := by
      intro f hfi hfj t ht
      obtain ⟨b, hb⟩ := Φ.hβsurj (Φ.Δ.τ f) (le_of_eq Φ.Δ.τ_range ⟨f, rfl⟩)
      have hbA : (b : G) ∈ A :=
        (qtwoDL1_oChart_mem_hyp_iff Φ hZ hBN hw₀ hw₁ hr₀ hr₀' b).mpr ⟨f, hb, hfi, hfj⟩
      have hcb : (b : G) * c = c * (b : G) :=
        Subgroup.mem_centralizer_iff.mp hc (b : G) hbA
      have hαLcomm : ∀ w : ↥L, αL (Subgroup.normalizerMonoidHom L ⟨(b : G), hBN b.2⟩ w) =
          Subgroup.normalizerMonoidHom L ⟨(b : G), hBN b.2⟩ (αL w) := by
        intro w
        apply Subtype.ext
        rw [hαLcoe, Subgroup.normalizerMonoidHom_apply_apply_coe,
          Subgroup.normalizerMonoidHom_apply_apply_coe, hαLcoe]
        calc c * ((b : G) * (w : G) * (b : G)⁻¹) * c⁻¹
            = (c * (b : G)) * (w : G) * (c * (b : G))⁻¹ := by group
          _ = ((b : G) * c) * (w : G) * ((b : G) * c)⁻¹ := by rw [hcb.symm]
          _ = (b : G) * (c * (w : G) * c⁻¹) * (b : G)⁻¹ := by group
      have heLconj : ∀ w : ↥(orthDerived Φ.Q),
          eL (Φ.β b * w * (Φ.β b)⁻¹) =
            Subgroup.normalizerMonoidHom L ⟨(b : G), hBN b.2⟩ (eL w) := by
        intro w
        apply Subtype.ext
        rw [heL, Φ.hcompat, Subgroup.normalizerMonoidHom_apply_apply_coe, heL]
      have hαcomm : ∀ z : ↥(orthDerived Φ.Q),
          α (Φ.β b * z * (Φ.β b)⁻¹) = Φ.β b * α z * (Φ.β b)⁻¹ := by
        intro z
        apply eL.injective
        rw [hαsym, heLconj, hαLcomm, ← hαsym, ← heLconj]
      have hcentral : ∀ z : ↥(orthDerived Φ.Q),
          ((Φ.β b)⁻¹ * α (Φ.β b)) * z = z * ((Φ.β b)⁻¹ * α (Φ.β b)) := by
        intro z
        have h := hαcomm (α.symm z)
        simp only [map_mul, map_inv, MulEquiv.apply_symm_apply] at h
        have hconj : ((Φ.β b)⁻¹ * α (Φ.β b)) * z *
            (((Φ.β b)⁻¹ * α (Φ.β b))⁻¹) = z := by
          calc ((Φ.β b)⁻¹ * α (Φ.β b)) * z * (((Φ.β b)⁻¹ * α (Φ.β b))⁻¹)
              = (Φ.β b)⁻¹ * (α (Φ.β b) * z * (α (Φ.β b))⁻¹) * Φ.β b := by group
            _ = (Φ.β b)⁻¹ * (Φ.β b * z * (Φ.β b)⁻¹) * Φ.β b := by rw [h]
            _ = z := by group
        calc ((Φ.β b)⁻¹ * α (Φ.β b)) * z
            = (((Φ.β b)⁻¹ * α (Φ.β b)) * z *
                (((Φ.β b)⁻¹ * α (Φ.β b))⁻¹)) * ((Φ.β b)⁻¹ * α (Φ.β b)) := by group
          _ = z * ((Φ.β b)⁻¹ * α (Φ.β b)) := by rw [hconj]
      have hαb : α (Φ.β b) = Φ.β b :=
        (inv_mul_eq_one.mp (p9uOCnt_center_eq_bot Φ hZ hcentral)).symm
      have htβ : t = Φ.β b := Subtype.ext (ht.trans hb.symm)
      simpa only [htβ] using hαb
    obtain ⟨g, hgO, hgact⟩ := hrep α hατ
    have hgpow : g ^ (2 ^ n) = 1 := by
      have hgp : ∀ (m : ℕ) (z : ↥(orthDerived Φ.Q)),
          ((α ^ m) z : Φ.V ≃ₗ[Φ.F] Φ.V) =
            g ^ m * (z : Φ.V ≃ₗ[Φ.F] Φ.V) * (g ^ m)⁻¹ := by
        intro m
        induction m with
        | zero => intro z; simp
        | succ m ih =>
          intro z
          rw [pow_succ', MulAut.mul_apply]
          rw [hgact ((α ^ m) z), ih z, pow_succ']
          group
      have hcen : ∀ z : ↥(orthDerived Φ.Q),
          (g ^ (2 ^ n)) * (z : Φ.V ≃ₗ[Φ.F] Φ.V) * (g ^ (2 ^ n))⁻¹ =
            (z : Φ.V ≃ₗ[Φ.F] Φ.V) := by
        intro z
        have h1 : ((α ^ (2 ^ n)) z : ↥(orthDerived Φ.Q)) = z := by
          rw [hαn, MulAut.one_apply]
        calc (g ^ (2 ^ n)) * (z : Φ.V ≃ₗ[Φ.F] Φ.V) * (g ^ (2 ^ n))⁻¹
            = ((α ^ (2 ^ n)) z : Φ.V ≃ₗ[Φ.F] Φ.V) := (hgp (2 ^ n) z).symm
          _ = (z : Φ.V ≃ₗ[Φ.F] Φ.V) := by rw [h1]
      exact CFSG.HardMathSupport.Timmesfeld.CrossChar.orth2_isometry_eq_one hF hQ h5f
        (pow_mem hgO (2 ^ n)) hcen
    have hgτ : ∀ f : Fin Φ.r → Multiplicative (ZMod p), f i = f j → f j = f k →
        g * Φ.Δ.τ f = Φ.Δ.τ f * g := by
      intro f hfi hfj
      let t : ↥(orthDerived Φ.Q) := ⟨Φ.Δ.τ f, Φ.hA (le_of_eq Φ.Δ.τ_range ⟨f, rfl⟩)⟩
      have h := hgact t
      rw [hατ f hfi hfj t rfl] at h
      change Φ.Δ.τ f = g * Φ.Δ.τ f * g⁻¹ at h
      calc g * Φ.Δ.τ f = (g * Φ.Δ.τ f * g⁻¹) * g := by group
        _ = Φ.Δ.τ f * g := by rw [← h]
    obtain ⟨⟨s₂, hs₂, hs₂eq⟩, hgω⟩ :=
      qtwoDL1_oChart_block Φ hF C hij hjk hik hgO hgτ ⟨n, hgpow⟩
    have hgD : g ∈ orthDerived Φ.Q := hωD hgω
    let gg : ↥(orthDerived Φ.Q) := ⟨g, hgD⟩
    have hgg : (gg : Φ.V ≃ₗ[Φ.F] Φ.V) = g := rfl
    refine ⟨Φ.ψ gg, ?_, ?_⟩
    · apply Subgroup.subset_closure
      constructor
      · refine ⟨?_, ?_⟩
        · have h : Φ.ψ gg ∈ Φ.ψ.range := ⟨gg, rfl⟩
          rwa [Φ.hrange] at h
        · change Φ.ψ gg ∈ Subgroup.centralizer (A : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          have h1 : a ∈ ggHyperplane Bs r₀ :=
            (inf_le_left : A ≤ ggHyperplane Bs r₀) ha
          have hABs : a ∈ Bs := Subgroup.map_subtype_le _ h1
          have hβa := (qtwoDL1_oChart_mem_hyp_iff Φ hZ hBN hw₀ hw₁ hr₀ hr₀'
            ⟨a, hABs⟩).mp (by exact ha)
          obtain ⟨f, hf, hfi, hfj⟩ := hβa
          have hτg := hgτ f hfi hfj
          have htconj : a * Φ.ψ gg * a⁻¹ = Φ.ψ gg := by
            rw [← Φ.hcompat ⟨a, hABs⟩ gg]
            congr 1
            apply Subtype.ext
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
            rw [hf]
            calc (Φ.Δ.τ f : Φ.V ≃ₗ[Φ.F] Φ.V) * (gg : Φ.V ≃ₗ[Φ.F] Φ.V) *
                (Φ.Δ.τ f)⁻¹
                = (gg : Φ.V ≃ₗ[Φ.F] Φ.V) * (Φ.Δ.τ f) * (Φ.Δ.τ f)⁻¹ := by
                  rw [hτg]
              _ = (gg : Φ.V ≃ₗ[Φ.F] Φ.V) := by group
          calc a * Φ.ψ gg = (a * Φ.ψ gg * a⁻¹) * a := by group
            _ = Φ.ψ gg * a := by rw [htconj]
      · refine ⟨n, ?_⟩
        have hp : gg ^ (2 ^ n) = 1 := by
          apply Subtype.ext
          rw [Subgroup.coe_pow, Subgroup.coe_one]
          simpa [hgg] using hgpow
        rw [← map_pow, hp, map_one]
    · rintro y hy
      have hyr : y ∈ Φ.ψ.range := by rw [Φ.hrange]; exact hy
      obtain ⟨z, rfl⟩ := hyr
      have hαz : α z = gg * z * gg⁻¹ := by
        apply Subtype.ext
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv, hgg] using hgact z
      have h1 : c * Φ.ψ z * c⁻¹ = Φ.ψ (α z) := by
        rw [← heL (α z), hαsym, hαLcoe (eL z), heL z]
      have h2' : Φ.ψ (α z) = Φ.ψ gg * Φ.ψ z * (Φ.ψ gg)⁻¹ := by
        rw [hαz, map_mul, map_mul, map_inv]
      calc c * Φ.ψ z * c⁻¹ = Φ.ψ (α z) := h1
        _ = Φ.ψ gg * Φ.ψ z * (Φ.ψ gg)⁻¹ := h2'

theorem qtwoDL1_baseO_centChart (ha₀ : GGLNoncyclicInput) {G : Type}
    [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hF : Nat.card Φ.F = 2)
    (hZ : Subgroup.center ↥L = ⊥) [Algebra Φ.F (GaloisField 2 2)] (C : QTwoDL1ONormChart Φ)
    {i j k : Fin Φ.r} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {w₀ w₁ : ↥(orthDerived Φ.Q)}
    (hw₀ : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (SpCoord.permAut (Equiv.swap i j) f))
    (hw₁ : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (SpCoord.permAut (Equiv.swap j k) f))
    {r₀ r₀' : MulAut ↥Bs}
    (hr₀ : ∀ s : ↥Bs, ((r₀ s : ↥Bs) : G) = Φ.ψ w₀ * (s : G) * (Φ.ψ w₀)⁻¹)
    (hr₀' : ∀ s : ↥Bs, ((r₀' s : ↥Bs) : G) = Φ.ψ w₁ * (s : G) * (Φ.ψ w₁)⁻¹) :
    Nat.card ↥(ggOTwoPrime (L ⊓ Subgroup.centralizer
        ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G) : Set G))) ≤ 216 ∧
      ∀ c ∈ Subgroup.centralizer
          ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G) : Set G),
        (∃ n : ℕ, c ^ (2 ^ n) = 1) →
          ∃ t ∈ ggOTwoPrime (L ⊓ Subgroup.centralizer
              ((ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' : Subgroup G) : Set G)),
            ∀ y ∈ L, c * y * c⁻¹ = t * y * t⁻¹ := by
  have : Fact p.Prime := ⟨(ggRouteCfg_prime hcfg).1⟩
  exact qtwoDL1_baseO_centChart_of_torus_fixed ha₀ hcfg Φ hF hZ C hij hjk hik
    hw₀ hw₁ hr₀ hr₀' (qtwoDL1_orthAut_of_torus_fixed Φ hF C hij hjk hik)

end CFSG.StandardType.QTwo

end
