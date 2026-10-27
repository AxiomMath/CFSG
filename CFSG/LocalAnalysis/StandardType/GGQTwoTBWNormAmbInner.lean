module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbModelBridge
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Transport
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGQTwoInputs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoS5Dispatch
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylA
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE7
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE8
import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Lin
import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
import CFSG.LocalAnalysis.StandardType.GGQTwoWeylInnerSmall

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def GGQ2Lin.WeylInnerLeaf {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (e : D.ι) : Prop :=
  ∃ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (f : Fin n ≃ {k // k ≠ e}),
    (∀ i j, D.cartan (f i) (f j) = C i j) ∧ GGQ2WeylInner n C

private lemma ggQ2tbi_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

theorem ggQ2tbi_mem_zpowers_of_smul {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x : G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (model : Additive ↥Bs ≃+ V) (ψ : MulAut ↥Bs) (hx : x ∈ Bs) (c : ZMod p)
    (h : ggLin (p := p) model ψ (model (Additive.ofMul ⟨x, hx⟩)) =
      c • model (Additive.ofMul ⟨x, hx⟩)) :
    ψ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
  rw [zpow_natCast]
  have h2 : Additive.ofMul (ψ ⟨x, hx⟩) = Additive.ofMul (⟨x, hx⟩ ^ c.val) := by
    apply model.injective
    rw [← ggLin_apply_ofMul (p := p) model ψ ⟨x, hx⟩, h]
    conv_lhs => rw [← ZMod.natCast_zmod_val c]
    rw [Nat.cast_smul_eq_nsmul, ofMul_pow, map_nsmul]
  exact (Additive.ofMul.injective h2).symm

private theorem ggQ2tbi_transvectionFree {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {L H : Subgroup G} (M : GGQTwoAmbModel p Bs x y L H)
    (hNT : GGNoTransvection p Bs) : TransvectionFree (M.parabL {k | k ≠ M.a}) := by
  rintro g hg ⟨u, ψ, hu, hψ, hψu, hgv⟩
  have hg' : g ∈ (ggAutomizer L Bs).map (ggLin (p := p) M.model) := by
    rw [← M.parabL_L]
    exact hg
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hg'
  have hφ' : φ ∈ ggInduced ⊤ Bs := by
    have h := ggAutomizer_mono Bs (le_top : L ≤ ⊤) hφ
    rw [ggAutomizer_eq] at h
    exact h
  exact hNT φ hφ' (ggIsTransvection_of_apply M.model hu hψ hψu hgv)

theorem ggQ2_tbwNormAmb_of_weylInnerLeaf (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h5 : GGQTwoCentralizerInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) [Fact p.Prime]
    {y : G} {K : Subgroup G} (M : GGQTwoAmbModel p Bs x y L (L ⊔ K)) (hbas : GGQTwoAmbBasis M)
    (hin : M.toLin.WeylInnerLeaf M.a) {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφx : ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV}) :
    ∃ c : ZMod p, c ≠ 0 ∧ ∃ w ∈ M.toLin.parab {k | k ≠ M.a}, ∀ i : {k // k ≠ M.a},
      ggLin (p := p) M.model φ (M.coroot i) = c • w (M.coroot i) := by
  subst hp
  classical
  have hH : GGCorFiveTwentyHyp 3 B Bs x L D J := hS.1
  have hAJS : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
  obtain ⟨c₀, hc₀⟩ := Submodule.mem_span_singleton.mp hφx
  have hφxg : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) :=
    ggQ2tbi_mem_zpowers_of_smul M.model φ M.hx c₀ hc₀.symm
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggQ2_lineStab_normalizes_L hLB hP hH hAJS M.hx hφ hφxg
  let T : M.V ≃ₗ[ZMod 3] M.V := ggLin (p := 3) M.model φ
  have hTnorm : T ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod 3] M.V)) := by
    rw [M.parabL_L]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model)
      (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  have hTF : TransvectionFree (M.parabL {k | k ≠ M.a}) := ggQ2tbi_transvectionFree M hH.2.2.2.1
  obtain ⟨n, C, f, hC, hW⟩ := hin
  have hind : LinearIndependent (ZMod 3)
      (fun i : {k // k ≠ M.toLin.a} => M.toLin.coroot i) :=
    hbas.1.comp (fun i : {k // k ≠ M.a} => (i : M.ι)) Subtype.val_injective
  have hdim : Module.finrank (ZMod 3) M.toLin.V ≤ Fintype.card {k // k ≠ M.toLin.a} + 1 := by
    have hcardΛ : Fintype.card {k // k ≠ M.a} = Fintype.card M.ι - 1 := Set.card_ne_eq M.a
    have hcardι : 0 < Fintype.card M.ι := Fintype.card_pos_iff.mpr ⟨M.a⟩
    have h2 : Module.finrank (ZMod 3) M.V = Fintype.card M.ι := hbas.2.symm
    change Module.finrank (ZMod 3) M.V ≤ Fintype.card {k // k ≠ M.a} + 1
    omega
  obtain ⟨w, hw, hconj⟩ := GGQ2Lin.inner_of_transport M.toLin C f hC hind hdim hTF hW T hTnorm
  let w₁ : M.V ≃ₗ[ZMod 3] M.V := w
  have hw₁ : w₁ ∈ M.parabL {k | k ≠ M.a} := hw
  have hconj₁ : ∀ g ∈ M.parabL {k | k ≠ M.a}, T * g * T⁻¹ = w₁ * g * w₁⁻¹ :=
    fun g hg => hconj g hg
  set S : M.V ≃ₗ[ZMod 3] M.V := w₁⁻¹ * T with hSdef
  have hcommS : ∀ g ∈ M.parabL {k | k ≠ M.a}, S * g = g * S := by
    intro g hg
    have h1 : S * g * S⁻¹ = g := by
      rw [hSdef]
      calc (w₁⁻¹ * T) * g * (w₁⁻¹ * T)⁻¹ = w₁⁻¹ * (T * g * T⁻¹) * w₁ := by group
        _ = w₁⁻¹ * (w₁ * g * w₁⁻¹) * w₁ := by rw [hconj₁ g hg]
        _ = g := by group
    calc S * g = (S * g * S⁻¹) * S := by group
      _ = g * S := by rw [h1]
  have hcommS' : ∀ g ∈ M.parabL {k | k ≠ M.a}, ∀ v : M.V, S (g v) = g (S v) := by
    intro g hg v
    have h := congrArg (fun e : M.V ≃ₗ[ZMod 3] M.V => e v) (hcommS g hg)
    simpa only [LinearEquiv.mul_apply] using h
  obtain ⟨c, hc⟩ := GGQ2Lin.exists_scalar_of_commute rfl M.toLin M.xV M.fixed_lin
    (GGQ2Lin.reflTransGen_compl_leaf rfl M.toLin) (S : M.V →ₗ[ZMod 3] M.V) (fun g hg v => by
      let g₁ : M.V ≃ₗ[ZMod 3] M.V := g
      let v₁ : M.V := v
      have h' : (S : M.V →ₗ[ZMod 3] M.V) (g₁ v₁) = g₁ ((S : M.V →ₗ[ZMod 3] M.V) v₁) :=
        hcommS' g₁ hg v₁
      show (S : M.V →ₗ[ZMod 3] M.V) (g₁ v₁) - g₁ ((S : M.V →ₗ[ZMod 3] M.V) v₁) ∈
        Submodule.span (ZMod 3) {M.xV}
      rw [h', sub_self]
      exact Submodule.zero_mem _)
  have h2 : (2 : ZMod 3) ≠ 0 := ggQ2tbi_two_ne_zero
  have hSh : ∀ i : {k // k ≠ M.a}, S (M.coroot i) = c • M.coroot i := by
    intro i
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (hc (M.coroot i))
    let r : M.V ≃ₗ[ZMod 3] M.V := M.toLin.simpleRefl (i : M.ι)
    have hri : r ∈ M.parabL {k | k ≠ M.a} := Subgroup.subset_closure ⟨(i : M.ι), i.2, rfl⟩
    have hrx : r M.xV = M.xV := (M.fixed_lin M.xV).mpr (Submodule.mem_span_singleton_self _) r hri
    have hrh : r (M.coroot i) = -M.coroot i := by
      have h := ggQ2xKDt_simpleRefl_apply M.toLin (i : M.ι) (M.coroot i)
      have h2' : M.toLin.root (i : M.ι) (M.toLin.coroot (i : M.ι)) = 2 :=
        M.toLin.root_coroot_self (i : M.ι)
      change r (M.coroot i) = M.coroot i - M.toLin.root (i : M.ι) (M.coroot i) • M.coroot i at h
      rw [h]
      change M.coroot i - M.toLin.root (i : M.ι) (M.toLin.coroot (i : M.ι)) • M.coroot i =
        -M.coroot i
      rw [h2']
      module
    have hSi : S (M.coroot i) = c • M.coroot i + t • M.xV := by
      have h' : (S : M.V →ₗ[ZMod 3] M.V) (M.coroot i) - c • M.coroot i = t • M.xV := ht.symm
      rw [← h']
      simp
    have hcom := hcommS' r hri (M.coroot i)
    rw [hrh, map_neg, hSi, map_add, map_smul, map_smul, hrh, hrx] at hcom
    have htx : t • M.xV = 0 := by
      have h3 : (2 * t) • M.xV = 0 := by
        have h4 : (2 * t) • M.xV = (c • -M.coroot i + t • M.xV) - -(c • M.coroot i + t • M.xV) := by
          module
        rw [h4, ← hcom, sub_self]
      rw [mul_smul] at h3
      exact (smul_eq_zero.mp h3).resolve_left h2
    rw [hSi, htx, add_zero]
  have hc0 : c ≠ 0 := by
    intro hc0
    let ib : {k // k ≠ M.a} := ⟨M.b, M.a_ne_b.symm⟩
    have h0 : S (M.coroot ib) = 0 := by rw [hSh ib, hc0, zero_smul]
    have hb0 : M.coroot ib = 0 := by
      have h' := congrArg S.symm h0
      rwa [S.symm_apply_apply, map_zero] at h'
    have hroot : M.toLin.root (ib : M.ι) (M.toLin.coroot (ib : M.ι)) = 2 :=
      M.toLin.root_coroot_self (ib : M.ι)
    change M.root ib (M.coroot ib) = 2 at hroot
    rw [hb0, map_zero] at hroot
    exact h2 hroot.symm
  refine ⟨c, hc0, w, hw, fun i => ?_⟩
  have hT : T = w₁ * S := by
    rw [hSdef, ← mul_assoc, mul_inv_cancel, one_mul]
  change T (M.coroot i) = c • w₁ (M.coroot i)
  rw [hT, LinearEquiv.mul_apply, hSh i, map_smul]

end CFSG.StandardType
