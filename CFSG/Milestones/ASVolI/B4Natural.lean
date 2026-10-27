module

public import CFSG.GroupTheory.GLnTwoSplitting.FirstCohomology
public import CFSG.GroupTheory.GLnTwoSplitting.Main
public import CFSG.GroupTheory.GLnTwoSplitting.SpecialLinear
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.Milestones.ASVolI.B4
public import CFSG.Open.StatedZModTwo
public import CFSG.Quasithin.Background.F918D2
public import CFSG.Quasithin.Background.FFC5Coh3
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBruhat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42A57Def
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3
public import CFSG.Quasithin.Background.A3Structure36BCases
public import CFSG.Quasithin.Background.A3Structure36BCommon
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStar
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2Conj
public import CFSG.Quasithin.Background.D2Cyclic
public import CFSG.Quasithin.Background.FFC5Case1
public import CFSG.Quasithin.Background.FFC5Main
public import CFSG.Quasithin.Background.FFC5Piece
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB4
public import CFSG.Quasithin.Background.SmithB42Alt7Model
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.H13.J4Classes
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.Cent11Base
public import Certificates.Kernel.J4Count.Fix11
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.ASVolI

open CFSG.Open

section Gaschutz

variable {Γ : Type*} [Group Γ] {W V : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_odd_nsmul {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {k : ℕ}
    (hk : Odd k) (x : M) : k • x = x := by
  obtain ⟨j, rfl⟩ := hk
  rw [add_nsmul, mul_nsmul, one_nsmul, two_nsmul, CFSG.GroupTheory.GLnTwoSplitting.two_add_self,
    nsmul_zero, zero_add]

theorem burnsideB49_gaschutz_section (ρW : Γ →* (W ≃ₗ[ZMod 2] W)) (ρV : Γ →* (V ≃ₗ[ZMod 2] V))
    (S : Subgroup Γ) (hodd : Odd S.index)
    (q : V →ₗ[ZMod 2] W) (hq : ∀ g v, q (ρV g v) = ρW g (q v))
    (Φ : W →ₗ[ZMod 2] V) (hΦ : ∀ x, q (Φ x) = x)
    (hΦS : ∀ s ∈ S, ∀ x, Φ (ρW s x) = ρV s (Φ x)) :
    ∃ Φ' : W →ₗ[ZMod 2] V, (∀ x, q (Φ' x) = x) ∧ ∀ g x, Φ' (ρW g x) = ρV g (Φ' x) := by
  classical
  have hfin : S.FiniteIndex := ⟨hodd.pos.ne'⟩
  haveI : Finite (Γ ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ S) := Fintype.ofFinite _
  let Ψ : Γ → (W →ₗ[ZMod 2] V) := fun g =>
    ((ρV g : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) ∘ₗ Φ ∘ₗ ((ρW g⁻¹ : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)
  have hΨapp : ∀ g y, Ψ g y = ρV g (Φ (ρW g⁻¹ y)) := fun g y => rfl
  have key : ∀ s ∈ S, ∀ z, ρV s (Φ (ρW s⁻¹ z)) = Φ z := by
    intro s hs z
    rw [← hΦS s hs, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hΨS : ∀ g, ∀ s ∈ S, Ψ (g * s) = Ψ g := by
    intro g s hs
    ext y
    rw [hΨapp, hΨapp]
    have h1 : ρV (g * s) (Φ (ρW (g * s)⁻¹ y)) = ρV g (ρV s (Φ (ρW s⁻¹ (ρW g⁻¹ y)))) := by
      simp [mul_inv_rev, map_mul]
    rw [h1, key s hs]
  let Ψ' : Γ ⧸ S → (W →ₗ[ZMod 2] V) := Quotient.lift Ψ (fun a b hab => by
    have hab' := QuotientGroup.leftRel_apply.mp hab
    have := hΨS a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hΨ' : ∀ g, Ψ' (QuotientGroup.mk g) = Ψ g := fun g => rfl
  have hΨh : ∀ (h : Γ) (x : Γ ⧸ S) (y : W), Ψ' x (ρW h y) = ρV h (Ψ' (h⁻¹ • x) y) := by
    intro h x y
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, hΨ', hΨ', hΨapp, hΨapp]
      simp [mul_inv_rev, map_mul]
  have hq1 : ∀ g y, q (Ψ g y) = y := by
    intro g y
    rw [hΨapp, hq, hΦ, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨∑ x : Γ ⧸ S, Ψ' x, fun y => ?_, fun g y => ?_⟩
  · rw [LinearMap.sum_apply, map_sum]
    have h1 : ∀ x : Γ ⧸ S, q (Ψ' x y) = y := fun x => by
      induction x using QuotientGroup.induction_on with
      | H g => exact hq1 g y
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    exact burnsideB49_odd_nsmul hodd y
  · rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    rw [Finset.sum_congr rfl (fun x _ => hΨh g x y)]
    exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ (fun x => rfl)

theorem burnsideB49_fixed_of_odd_index {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Γ →* (X ≃ₗ[ZMod 2] X)) (Y : Submodule (ZMod 2) X) (S : Subgroup Γ)
    (hodd : Odd S.index) (x₁ : X) (hx₁ : ∀ γ, ρ γ x₁ + x₁ ∈ Y) (hS : ∀ s ∈ S, ρ s x₁ = x₁) :
    ∃ x : X, x + x₁ ∈ Y ∧ ∀ γ, ρ γ x = x := by
  classical
  have hfin : S.FiniteIndex := ⟨hodd.pos.ne'⟩
  haveI : Finite (Γ ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ S) := Fintype.ofFinite _
  let δ : Γ → X := fun γ => ρ γ x₁ + x₁
  have hδS : ∀ g, ∀ s ∈ S, δ (g * s) = δ g := by
    intro g s hs
    simp only [δ, map_mul, LinearEquiv.mul_apply, hS s hs]
  let δ' : Γ ⧸ S → X := Quotient.lift δ (fun a b hab => by
    have hab' := QuotientGroup.leftRel_apply.mp hab
    have := hδS a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hδ' : ∀ g, δ' (QuotientGroup.mk g) = δ g := fun g => rfl
  have hδh : ∀ (h : Γ) (x : Γ ⧸ S), ρ h (δ' x) = δ' (h • x) + δ h := by
    intro h x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, hδ', hδ']
      simp only [δ, map_mul, LinearEquiv.mul_apply, map_add]
      have h2 : (2 : ℕ) • x₁ = 0 := by
        rw [two_nsmul]
        exact CFSG.GroupTheory.GLnTwoSplitting.two_add_self x₁
      calc ρ h (ρ g x₁) + ρ h x₁ = ρ h (ρ g x₁) + ρ h x₁ + 2 • x₁ := by rw [h2, add_zero]
        _ = _ := by abel
  set u : X := ∑ x : Γ ⧸ S, δ' x with hu
  have hmem : u ∈ Y := Submodule.sum_mem _ fun x _ => by
    induction x using QuotientGroup.induction_on with
    | H g => exact hx₁ g
  have hρu : ∀ h, ρ h u = u + δ h := by
    intro h
    rw [hu, map_sum, Finset.sum_congr rfl (fun x _ => hδh h x), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    have h1 : ∑ x : Γ ⧸ S, δ' (h • x) = ∑ x : Γ ⧸ S, δ' x :=
      Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun x => rfl)
    rw [h1]
    have h2 : Nat.card (Γ ⧸ S) • δ h = δ h := burnsideB49_odd_nsmul hodd (δ h)
    rw [h2]
  refine ⟨x₁ + u, ?_, fun γ => ?_⟩
  · have : x₁ + u + x₁ = u := by
      calc x₁ + u + x₁ = (x₁ + x₁) + u := by abel
        _ = u := by rw [CFSG.GroupTheory.GLnTwoSplitting.two_add_self, zero_add]
    rw [this]
    exact hmem
  · rw [map_add, hρu]
    have : ρ γ x₁ = x₁ + δ γ := by
      simp only [δ]
      calc ρ γ x₁ = ρ γ x₁ + (x₁ + x₁) := by rw [CFSG.GroupTheory.GLnTwoSplitting.two_add_self, add_zero]
        _ = x₁ + (ρ γ x₁ + x₁) := by abel
    rw [this]
    calc x₁ + δ γ + (u + δ γ) = x₁ + u + (δ γ + δ γ) := by abel
      _ = x₁ + u := by rw [CFSG.GroupTheory.GLnTwoSplitting.two_add_self, add_zero]

end Gaschutz

section GLForm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

abbrev burnsideB49_tv (φ : Module.Dual (ZMod 2) W) (w : W) (h : φ w = 0) :
    W ≃ₗ[ZMod 2] W :=
  LinearEquiv.transvection (f := φ) (v := w) h

theorem burnsideB49_tv_apply {φ : Module.Dual (ZMod 2) W} {w : W} (h : φ w = 0) (x : W) :
    burnsideB49_tv φ w h x = x + φ x • w := rfl

theorem burnsideB49_tv_zero {φ : Module.Dual (ZMod 2) W} (h : φ 0 = 0) :
    burnsideB49_tv φ 0 h = 1 := by
  ext x
  rw [burnsideB49_tv_apply, smul_zero, add_zero]
  rfl

theorem burnsideB49_tv_mul {φ : Module.Dual (ZMod 2) W} {w w' : W} (h : φ w = 0) (h' : φ w' = 0)
    (h'' : φ (w + w') = 0) :
    burnsideB49_tv φ w h * burnsideB49_tv φ w' h' = burnsideB49_tv φ (w + w') h'' :=
  transvection_mul_transvection_left h h' h''

theorem burnsideB49_tv_mul_self {φ : Module.Dual (ZMod 2) W} {w : W} (h : φ w = 0) :
    burnsideB49_tv φ w h * burnsideB49_tv φ w h = 1 :=
  transvection_mul_self h

theorem burnsideB49_tv_inv {φ : Module.Dual (ZMod 2) W} {w : W} (h : φ w = 0) :
    (burnsideB49_tv φ w h)⁻¹ = burnsideB49_tv φ w h :=
  transvection_inv h

@[expose] def burnsideB49_stab (φ : Module.Dual (ZMod 2) W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {g | ∀ x, φ (g x) = φ x}
  mul_mem' := by
    intro a b ha hb x
    rw [LinearEquiv.mul_apply, ha, hb]
  one_mem' := fun x => rfl
  inv_mem' := by
    intro a ha x
    have := ha (a⁻¹ x)
    rw [show a (a⁻¹ x) = x from by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl] at this
    exact this.symm

theorem burnsideB49_mem_stab {φ : Module.Dual (ZMod 2) W} {g : W ≃ₗ[ZMod 2] W} :
    g ∈ burnsideB49_stab φ ↔ ∀ x, φ (g x) = φ x := Iff.rfl

theorem burnsideB49_conj_tv {φ : Module.Dual (ZMod 2) W} {w : W} (h : φ w = 0)
    {g : W ≃ₗ[ZMod 2] W} (hg : g ∈ burnsideB49_stab φ) (h' : φ (g w) = 0) :
    g * burnsideB49_tv φ w h * g⁻¹ = burnsideB49_tv φ (g w) h' := by
  ext x
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, burnsideB49_tv_apply, burnsideB49_tv_apply,
    map_add, map_smul]
  have h1 : g (g⁻¹ x) = x := by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  have h2 : φ (g⁻¹ x) = φ x := by
    have := hg (g⁻¹ x)
    rw [h1] at this
    exact this.symm
  rw [h1, h2]

theorem burnsideB49_stab_index_odd [FiniteDimensional (ZMod 2) W] {φ : Module.Dual (ZMod 2) W}
    (hφ : φ ≠ 0) : Odd (burnsideB49_stab φ).index := by
  letI : MulAction (W ≃ₗ[ZMod 2] W) (Module.Dual (ZMod 2) W) :=
    { smul := fun g f => f ∘ₗ (g.symm : W →ₗ[ZMod 2] W)
      one_smul := fun f => by ext x; rfl
      mul_smul := fun g h f => by ext x; rfl }
  have hsmul : ∀ (g : W ≃ₗ[ZMod 2] W) (f : Module.Dual (ZMod 2) W) (x : W),
      (g • f) x = f (g.symm x) := fun _ _ _ => rfl
  have hstab : MulAction.stabilizer (W ≃ₗ[ZMod 2] W) φ = burnsideB49_stab φ := by
    ext g
    rw [MulAction.mem_stabilizer_iff, burnsideB49_mem_stab]
    constructor
    · intro hg x
      have := congrArg (fun f : Module.Dual (ZMod 2) W => f (g x)) hg
      simp only [hsmul, LinearEquiv.symm_apply_apply] at this
      exact this.symm
    · intro hg
      ext x
      rw [hsmul]
      have := hg (g.symm x)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
  have horbit : MulAction.orbit (W ≃ₗ[ZMod 2] W) φ = {ψ : Module.Dual (ZMod 2) W | ψ ≠ 0} := by
    ext ψ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨g, rfl⟩ h0
      apply hφ
      ext x
      have := congrArg (fun f : Module.Dual (ZMod 2) W => f (g x)) h0
      simp only [hsmul, LinearEquiv.symm_apply_apply, LinearMap.zero_apply] at this
      simpa using this
    · intro hψ
      obtain ⟨g, -, hg⟩ := exists_comp_eq_of_apply_eq_zero (e₀ := (0 : W)) hψ hφ (map_zero ψ)
        (map_zero φ)
      refine ⟨g, ?_⟩
      ext x
      rw [hsmul]
      have := congrArg (fun f : Module.Dual (ZMod 2) W => f (g.symm x)) hg
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      exact this.symm
  rw [← hstab, MulAction.index_stabilizer, horbit]
  have hne : ({0}ᶜ : Set (Module.Dual (ZMod 2) W)) = {ψ | ψ ≠ 0} := by
    ext ψ; simp
  haveI : Finite (Module.Dual (ZMod 2) W) := Module.finite_of_finite (ZMod 2)
  rw [← hne, Set.ncard_compl _ (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]
  have hcard : Nat.card (Module.Dual (ZMod 2) W) =
      2 ^ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) W) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  have hpos : 0 < Module.finrank (ZMod 2) (Module.Dual (ZMod 2) W) := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨φ, hφ⟩
  rw [hcard]
  obtain ⟨j, hj⟩ : ∃ j, Module.finrank (ZMod 2) (Module.Dual (ZMod 2) W) = j + 1 :=
    ⟨Module.finrank (ZMod 2) (Module.Dual (ZMod 2) W) - 1, by omega⟩
  rw [hj, pow_succ]
  have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  exact ⟨2 ^ j - 1, by omega⟩

theorem burnsideB49_mem_span_pair {a b x : W} :
    x ∈ Submodule.span (ZMod 2) {a, b} ↔ x = 0 ∨ x = a ∨ x = b ∨ x = a + b := by
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨c, d, rfl⟩
    rcases zmod_two_eq_zero_or_one c with rfl | rfl <;>
      rcases zmod_two_eq_zero_or_one d with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem burnsideB49_exists_stab_single [FiniteDimensional (ZMod 2) W] {φ : Module.Dual (ZMod 2) W}
    {a b : W} (ha : a ≠ 0) (hb : b ≠ 0) (haφ : φ a = 0) (hbφ : φ b = 0) :
    ∃ g ∈ burnsideB49_stab φ, g a = b := by
  by_cases hab : a = b
  · exact ⟨1, Subgroup.one_mem _, by rw [hab]; rfl⟩
  have hnot : a ∉ Submodule.span (ZMod 2) {a + b} := by
    rw [Submodule.mem_span_singleton]
    rintro ⟨c, hc⟩
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul] at hc
      exact ha hc.symm
    · rw [one_smul] at hc
      exact hb (by simpa using hc)
  obtain ⟨f, hf, hfa⟩ := exists_dual_eq_one_of_notMem hnot
  have hfab : f (a + b) = 0 := hf _ (Submodule.mem_span_singleton_self _)
  have hfb : f b = 1 := by
    rw [map_add, hfa] at hfab
    have : f b = f b + 0 := (add_zero _).symm
    have h2 : (1 : ZMod 2) + f b = 0 := hfab
    revert h2
    generalize f b = y
    revert y
    decide
  have hφd : φ (a + b) = 0 := by rw [map_add, haφ, hbφ, add_zero]
  refine ⟨LinearEquiv.transvection hfab, ?_, ?_⟩
  · intro x
    rw [transvection_apply, map_add, map_smul, hφd, smul_zero, add_zero]
  · rw [transvection_apply, hfa, one_smul]
    calc a + (a + b) = (a + a) + b := by abel
      _ = b := by rw [two_add_self, zero_add]

theorem burnsideB49_exists_stab_pair [FiniteDimensional (ZMod 2) W] {φ : Module.Dual (ZMod 2) W}
    {a₁ a₂ b₁ b₂ : W} (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0) (ha : a₁ ≠ a₂) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (hb : b₁ ≠ b₂) (h₁ : φ a₁ = 0) (h₂ : φ a₂ = 0) (h₃ : φ b₁ = 0) (h₄ : φ b₂ = 0) :
    ∃ g ∈ burnsideB49_stab φ, g a₁ = b₁ ∧ g a₂ = b₂ := by
  obtain ⟨σ, hσ, hσa⟩ := burnsideB49_exists_stab_single ha₁ hb₁ h₁ h₃
  set c := σ a₂ with hc
  have hc0 : c ≠ 0 := fun h => ha₂ (σ.injective (by rw [← hc, h, map_zero]))
  have hcb : c ≠ b₁ := fun h => ha (σ.injective (by rw [hσa, ← h]))
  have hφc : φ c = 0 := by rw [hc, hσ a₂, h₂]
  by_cases hcb₂ : c = b₂
  · exact ⟨σ, hσ, hσa, hcb₂⟩
  have hnot : c ∉ Submodule.span (ZMod 2) {b₁, c + b₂} := by
    rw [burnsideB49_mem_span_pair]
    rintro (h | h | h | h)
    · exact hc0 h
    · exact hcb h
    · exact hb₂ (by simpa using h)
    · apply hb
      have h' : c + 0 = c + (b₁ + b₂) := by
        calc c + 0 = c := add_zero c
          _ = b₁ + (c + b₂) := h
          _ = c + (b₁ + b₂) := by abel
      exact (two_add_eq_iff.1 (add_left_cancel h').symm).trans (zero_add _)
  obtain ⟨f, hf, hfc⟩ := exists_dual_eq_one_of_notMem hnot
  have hfb₁ : f b₁ = 0 := hf _ (Submodule.subset_span (by simp))
  have hfd : f (c + b₂) = 0 := hf _ (Submodule.subset_span (by simp))
  have hφd : φ (c + b₂) = 0 := by rw [map_add, hφc, h₄, add_zero]
  refine ⟨LinearEquiv.transvection hfd * σ, ?_, ?_, ?_⟩
  · intro x
    rw [LinearEquiv.mul_apply, transvection_apply, map_add, map_smul, hφd, smul_zero, add_zero,
      hσ x]
  · rw [LinearEquiv.mul_apply, hσa, transvection_apply, hfb₁, zero_smul, add_zero]
  · rw [LinearEquiv.mul_apply, ← hc, transvection_apply, hfc, one_smul]
    calc c + (c + b₂) = (c + c) + b₂ := by abel
      _ = b₂ := by rw [two_add_self, zero_add]

section Quad

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_exists_two_ne_one {G : Type*} [Group G] (E : Subgroup G)
    (hE : Nat.card E = 4) : ∃ e₁ e₂ : G, e₁ ∈ E ∧ e₂ ∈ E ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₁ ≠ e₂ := by
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite E
  have h2 : 2 < Fintype.card E := by
    rw [← Nat.card_eq_fintype_card, hE]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.1 h2
  by_cases ha : (a : G) = 1
  · refine ⟨b, c, b.2, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (Subtype.ext (by rw [ha, h]))
    · intro h
      exact hac (Subtype.ext (by rw [ha, h]))
  · by_cases hb : (b : G) = 1
    · refine ⟨a, c, a.2, c.2, ha, ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (Subtype.ext (by rw [hb, h]))
    · exact ⟨a, b, a.2, b.2, ha, hb, fun h => hab (Subtype.ext h)⟩

theorem burnsideB49_quad_conj (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    {φ : Module.Dual (ZMod 2) W} {u u' : W} (hu : φ u = 0) (hu' : φ u' = 0)
    (hP : ∀ v : V, ρ (burnsideB49_tv φ u hu) (ρ (burnsideB49_tv φ u' hu') v - v) =
      ρ (burnsideB49_tv φ u' hu') v - v)
    {σ : W ≃ₗ[ZMod 2] W} (hσ : σ ∈ burnsideB49_stab φ) (hσu : φ (σ u) = 0)
    (hσu' : φ (σ u') = 0) (v : V) :
    ρ (burnsideB49_tv φ (σ u) hσu) (ρ (burnsideB49_tv φ (σ u') hσu') v - v) =
      ρ (burnsideB49_tv φ (σ u') hσu') v - v := by
  rw [← burnsideB49_conj_tv hu hσ hσu, ← burnsideB49_conj_tv hu' hσ hσu']
  have h1 : ∀ x : V, ρ σ (ρ σ⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h2 : ∀ x : V, ρ σ⁻¹ (ρ σ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  set v₀ := ρ σ⁻¹ v with hv₀
  have hv : v = ρ σ v₀ := (h1 v).symm
  have hA : ρ (σ * burnsideB49_tv φ u' hu' * σ⁻¹) v = ρ σ (ρ (burnsideB49_tv φ u' hu') v₀) := by
    simp only [map_mul, LinearEquiv.mul_apply, hv₀]
  have hB : ρ (σ * burnsideB49_tv φ u' hu' * σ⁻¹) v - v =
      ρ σ (ρ (burnsideB49_tv φ u' hu') v₀ - v₀) := by
    rw [hA, map_sub, ← hv]
  rw [hB]
  have hC : ρ (σ * burnsideB49_tv φ u hu * σ⁻¹) (ρ σ (ρ (burnsideB49_tv φ u' hu') v₀ - v₀)) =
      ρ σ (ρ (burnsideB49_tv φ u hu) (ρ (burnsideB49_tv φ u' hu') v₀ - v₀)) := by
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [h2]
  rw [hC, hP]

theorem burnsideB49_Q_quadratic [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) {φ : Module.Dual (ZMod 2) W}
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) (hE4 : Nat.card E = 4)
    (hEtr : ∀ e ∈ E, e ≠ 1 → ∃ (w : W) (h : φ w = 0), e = burnsideB49_tv φ w h)
    (hEquad : ∀ e ∈ E, ∀ e' ∈ E, ∀ v : V, ρ e (ρ e' v - v) = ρ e' v - v)
    (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V) :
    ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
      ρ (burnsideB49_tv φ w' h') v - v := by
  obtain ⟨e₁, e₂, he₁, he₂, h1, h2, h12⟩ := burnsideB49_exists_two_ne_one E hE4
  obtain ⟨w₁, hw₁, rfl⟩ := hEtr e₁ he₁ h1
  obtain ⟨w₂, hw₂, rfl⟩ := hEtr e₂ he₂ h2
  have hw₁0 : w₁ ≠ 0 := by
    rintro rfl
    exact h1 (burnsideB49_tv_zero hw₁)
  have hw₂0 : w₂ ≠ 0 := by
    rintro rfl
    exact h2 (burnsideB49_tv_zero hw₂)
  have hw₁₂ : w₁ ≠ w₂ := by
    rintro rfl
    exact h12 rfl
  by_cases hw0 : w = 0
  · subst hw0
    rw [burnsideB49_tv_zero h]
    simp
  by_cases hw'0 : w' = 0
  · subst hw'0
    rw [burnsideB49_tv_zero h']
    simp
  by_cases hww' : w = w'
  · subst hww'
    obtain ⟨σ, hσ, hσw⟩ := burnsideB49_exists_stab_single hw₁0 hw0 hw₁ h
    have hP := burnsideB49_quad_conj ρ hw₁ hw₁ (fun v => hEquad _ he₁ _ he₁ v) hσ
      (by rw [hσw]; exact h) (by rw [hσw]; exact h) v
    simpa [hσw] using hP
  · obtain ⟨σ, hσ, hσ₁, hσ₂⟩ := burnsideB49_exists_stab_pair hw₁0 hw₂0 hw₁₂ hw0 hw'0 hww' hw₁ hw₂
      h h'
    have hP := burnsideB49_quad_conj ρ hw₁ hw₂ (fun v => hEquad _ he₁ _ he₂ v) hσ
      (by rw [hσ₁]; exact h) (by rw [hσ₂]; exact h') v
    simpa [hσ₁, hσ₂] using hP

end Quad

section Sec

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_rho_inv_apply (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (g : W ≃ₗ[ZMod 2] W) (x : V) : ρ g⁻¹ (ρ g x) = x := by
  rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

@[expose] def burnsideB49_alphaFun (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (φ : Module.Dual (ZMod 2) W)
    (v : V) (y : ↥(LinearMap.ker φ)) : V :=
  ρ (burnsideB49_tv φ (y : W) (LinearMap.mem_ker.1 y.2)) v - v

theorem burnsideB49_alphaFun_zero (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (φ : Module.Dual (ZMod 2) W) (v : V) : burnsideB49_alphaFun ρ φ v 0 = 0 := by
  unfold burnsideB49_alphaFun
  rw [show burnsideB49_tv φ ((0 : ↥(LinearMap.ker φ)) : W) (LinearMap.mem_ker.1 (0 : ↥(LinearMap.ker φ)).2) = 1 from
    burnsideB49_tv_zero _, map_one]
  exact sub_self v

theorem burnsideB49_alphaFun_add (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V))
    (φ : Module.Dual (ZMod 2) W) (v : V)
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v) (y y' : ↥(LinearMap.ker φ)) :
    burnsideB49_alphaFun ρ φ v (y + y') =
      burnsideB49_alphaFun ρ φ v y + burnsideB49_alphaFun ρ φ v y' := by
  have hy := LinearMap.mem_ker.1 y.2
  have hy' := LinearMap.mem_ker.1 y'.2
  have hyy' : φ ((y : W) + y') = 0 := by rw [map_add, hy, hy', add_zero]
  unfold burnsideB49_alphaFun
  have h1 : burnsideB49_tv φ ((y + y' : ↥(LinearMap.ker φ)) : W)
      (LinearMap.mem_ker.1 (y + y').2) = burnsideB49_tv φ (y : W) hy * burnsideB49_tv φ (y' : W) hy' := by
    rw [burnsideB49_tv_mul hy hy' hyy']
  rw [h1, map_mul, LinearEquiv.mul_apply]
  have h2 := hQ (y : W) (y' : W) hy hy' v
  rw [map_sub, sub_eq_iff_eq_add] at h2
  rw [h2]
  abel

theorem burnsideB49_section_of_kfix
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ : Module.Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v)
    (v : V) (hvq : q v = w₀)
    (hv : ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ρ k v = v) :
    ∃ Φ : W →ₗ[ZMod 2] V, (∀ x, q (Φ x) = x) ∧
      ∀ s ∈ burnsideB49_stab φ, ∀ x, Φ (s x) = ρ s (Φ x) := by
  classical
  let a : W → V := fun y => if h : φ y = 0 then ρ (burnsideB49_tv φ y h) v - v else 0
  have ha : ∀ y (h : φ y = 0), a y = ρ (burnsideB49_tv φ y h) v - v := fun y h => by
    simp only [a, dif_pos h]
  let p : W → W := fun x => x + φ x • w₀
  have hp0 : ∀ x, φ (p x) = 0 := fun x => by
    simp only [p, map_add, map_smul, hw₀, smul_eq_mul, mul_one]
    exact zmod_two_add_self _
  have hpadd : ∀ x x', p (x + x') = p x + p x' := fun x x' => by
    simp only [p, map_add, add_smul]
    abel
  have ha0 : a 0 = 0 := by
    rw [ha 0 (map_zero φ), burnsideB49_tv_zero (map_zero φ), map_one]
    exact sub_self v
  have haadd : ∀ y y', φ y = 0 → φ y' = 0 → a (y + y') = a y + a y' := fun y y' hy hy' => by
    have := burnsideB49_alphaFun_add ρ φ v hQ ⟨y, LinearMap.mem_ker.2 hy⟩
      ⟨y', LinearMap.mem_ker.2 hy'⟩
    unfold burnsideB49_alphaFun at this
    rw [ha y hy, ha y' hy', ha (y + y') (by rw [map_add, hy, hy', add_zero])]
    exact this
  have hasmul : ∀ (c : ZMod 2) y, φ y = 0 → a (c • y) = c • a y := fun c y hy => by
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · simp [ha0]
    · simp
  have haq : ∀ y, φ y = 0 → q (a y) = y := fun y hy => by
    rw [ha y hy, map_sub, hq, hvq, burnsideB49_tv_apply, hw₀, one_smul]
    abel
  have haQ : ∀ (u y : W) (hu : φ u = 0), φ y = 0 → ρ (burnsideB49_tv φ u hu) (a y) = a y :=
    fun u y hu hy => by rw [ha y hy]; exact hQ u y hu hy v
  have haK : ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ∀ y, φ y = 0 →
      ρ k (a y) = a (k y) := fun k hk hkw y hy => by
    have hky : φ (k y) = 0 := by rw [hk, hy]
    have hkv := hv k hk hkw
    rw [ha y hy, ha (k y) hky, map_sub, hkv]
    have hc := burnsideB49_conj_tv hy (burnsideB49_mem_stab.2 hk) hky
    have h1 : ρ k (ρ (burnsideB49_tv φ y hy) v) = ρ (burnsideB49_tv φ (k y) hky) v := by
      conv_rhs => rw [← hkv, ← hc]
      simp only [map_mul, LinearEquiv.mul_apply, burnsideB49_rho_inv_apply]
    rw [h1]
  let Φfun : W → V := fun x => φ x • v + a (p x)
  have hΦadd : ∀ x x', Φfun (x + x') = Φfun x + Φfun x' := fun x x' => by
    simp only [Φfun, map_add, add_smul, hpadd]
    rw [haadd _ _ (hp0 x) (hp0 x')]
    abel
  let Φ : W →ₗ[ZMod 2] V := AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' Φfun hΦadd)
  have hΦ : ∀ x, Φ x = φ x • v + a (p x) := fun x => rfl
  have E1 : ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ∀ x, Φ (k x) = ρ k (Φ x) := by
    intro k hk hkw x
    have hpk : p (k x) = k (p x) := by
      simp only [p, map_add, map_smul, hk, hkw]
    rw [hΦ, hΦ, hpk, map_add (ρ k), map_smul (ρ k), hv k hk hkw, hk,
      haK k hk hkw (p x) (hp0 x)]
  have E2 : ∀ (u : W) (hu : φ u = 0) x, Φ (burnsideB49_tv φ u hu x) =
      ρ (burnsideB49_tv φ u hu) (Φ x) := by
    intro u hu x
    have hφt : φ (burnsideB49_tv φ u hu x) = φ x := by
      rw [burnsideB49_tv_apply, map_add, map_smul, hu, smul_zero, add_zero]
    have hpt : p (burnsideB49_tv φ u hu x) = p x + φ x • u := by
      show burnsideB49_tv φ u hu x + φ (burnsideB49_tv φ u hu x) • w₀ = p x + φ x • u
      rw [hφt, burnsideB49_tv_apply]
      simp only [p]
      abel
    have hau : ρ (burnsideB49_tv φ u hu) v = a u + v := by
      rw [ha u hu]
      abel
    rw [hΦ, hΦ, hφt, hpt, haadd _ _ (hp0 x) (by rw [map_smul, hu, smul_zero]),
      hasmul _ _ hu, map_add, map_smul, hau, haQ u _ hu (hp0 x), smul_add]
    abel
  refine ⟨Φ, fun x => ?_, fun s hs x => ?_⟩
  · rw [hΦ, map_add, map_smul, hvq, haq _ (hp0 x)]
    simp only [p]
    calc φ x • w₀ + (x + φ x • w₀) = x + (φ x • w₀ + φ x • w₀) := by abel
      _ = x := by rw [two_add_self, add_zero]
  · have hs' := burnsideB49_mem_stab.1 hs
    have hu : φ (s w₀ + w₀) = 0 := by
      rw [map_add, hs', hw₀]
      exact zmod_two_add_self _
    set u := s w₀ + w₀ with hu_def
    set k := burnsideB49_tv φ u hu * s with hk_def
    have hk : ∀ x, φ (k x) = φ x := fun x => by
      rw [hk_def, LinearEquiv.mul_apply, burnsideB49_tv_apply, map_add, map_smul, hu, smul_zero,
        add_zero, hs']
    have hkw : k w₀ = w₀ := by
      rw [hk_def, LinearEquiv.mul_apply, burnsideB49_tv_apply, hs', hw₀, one_smul, hu_def]
      calc s w₀ + (s w₀ + w₀) = (s w₀ + s w₀) + w₀ := by abel
        _ = w₀ := by rw [two_add_self, zero_add]
    have hsk : s = burnsideB49_tv φ u hu * k := by
      rw [hk_def, ← mul_assoc, burnsideB49_tv_mul_self, one_mul]
    conv_lhs => rw [hsk, LinearEquiv.mul_apply, E2, E1 k hk hkw]
    conv_rhs => rw [hsk, map_mul, LinearEquiv.mul_apply]

theorem burnsideB49_isCompl_of_section {q : V →ₗ[ZMod 2] W} {Φ' : W →ₗ[ZMod 2] V}
    (h : ∀ x, q (Φ' x) = x) : IsCompl (LinearMap.ker q) (LinearMap.range Φ') := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    rintro x hx ⟨y, rfl⟩
    rw [LinearMap.mem_ker, h] at hx
    rw [hx, map_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have : v = (v - Φ' (q v)) + Φ' (q v) := by abel
    rw [this]
    refine Submodule.add_mem_sup ?_ ⟨q v, rfl⟩
    rw [LinearMap.mem_ker, map_sub, h, sub_self]

theorem burnsideB49_complement_of_kfix [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0) {w₀ : W} (hw₀ : φ w₀ = 1)
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v)
    (v : V) (hvq : q v = w₀)
    (hv : ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ρ k v = v) :
    ∃ U' : Submodule (ZMod 2) V, (∀ g, ∀ x ∈ U', ρ g x ∈ U') ∧ IsCompl (LinearMap.ker q) U' := by
  obtain ⟨Φ, hΦ, hΦS⟩ := burnsideB49_section_of_kfix ρ q hq hw₀ hQ v hvq hv
  obtain ⟨Φ', hΦ', hΦ'G⟩ := burnsideB49_gaschutz_section (MonoidHom.id (W ≃ₗ[ZMod 2] W)) ρ
    (burnsideB49_stab φ) (burnsideB49_stab_index_odd hφ) q hq Φ hΦ hΦS
  refine ⟨LinearMap.range Φ', ?_, burnsideB49_isCompl_of_section hΦ'⟩
  rintro g _ ⟨y, rfl⟩
  exact ⟨g y, hΦ'G g y⟩

end Sec

end GLForm

section KLevi

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def burnsideB49_K (φ : Module.Dual (ZMod 2) W) (w₀ : W) : Subgroup (W ≃ₗ[ZMod 2] W) where
  carrier := {k | (∀ x, φ (k x) = φ x) ∧ k w₀ = w₀}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨fun x => by rw [LinearEquiv.mul_apply, ha, hb], by rw [LinearEquiv.mul_apply, hb', ha']⟩
  one_mem' := ⟨fun x => rfl, rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun x => ?_, ?_⟩
    · have := ha (a⁻¹ x)
      rw [show a (a⁻¹ x) = x from by rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl] at this
      exact this.symm
    · exact (LinearEquiv.symm_apply_eq a).2 ha'.symm

theorem burnsideB49_mem_K {φ : Module.Dual (ZMod 2) W} {w₀ : W} {k : W ≃ₗ[ZMod 2] W} :
    k ∈ burnsideB49_K φ w₀ ↔ (∀ x, φ (k x) = φ x) ∧ k w₀ = w₀ := Iff.rfl

theorem burnsideB49_K_le_stab (φ : Module.Dual (ZMod 2) W) (w₀ : W) :
    burnsideB49_K φ w₀ ≤ burnsideB49_stab φ := fun _ hk => hk.1

theorem burnsideB49_map_ker {φ : Module.Dual (ZMod 2) W} {k : W ≃ₗ[ZMod 2] W}
    (hk : ∀ x, φ (k x) = φ x) :
    (LinearMap.ker φ).map (k : W →ₗ[ZMod 2] W) = LinearMap.ker φ := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [hk, hz]
  · intro hy
    refine ⟨k.symm y, ?_, k.apply_symm_apply y⟩
    have := hk (k.symm y)
    rw [k.apply_symm_apply, hy] at this
    exact this.symm

@[expose] noncomputable def burnsideB49_Kres (φ : Module.Dual (ZMod 2) W) (w₀ : W) :
    ↥(burnsideB49_K φ w₀) →* (↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) where
  toFun k := (k : W ≃ₗ[ZMod 2] W).ofSubmodules (LinearMap.ker φ) (LinearMap.ker φ)
    (burnsideB49_map_ker k.2.1)
  map_one' := by
    ext w
    rfl
  map_mul' k k' := by
    ext w
    rfl

theorem burnsideB49_Kres_apply {φ : Module.Dual (ZMod 2) W} {w₀ : W}
    (k : ↥(burnsideB49_K φ w₀)) (y : ↥(LinearMap.ker φ)) :
    ((burnsideB49_Kres φ w₀ k y : ↥(LinearMap.ker φ)) : W) = (k : W ≃ₗ[ZMod 2] W) y := rfl

section Extend

variable (φ : Module.Dual (ZMod 2) W) {w₀ : W} (hw₀ : φ w₀ = 1)

include hw₀

theorem burnsideB49_proj_mem (x : W) : φ (x + φ x • w₀) = 0 := by
  rw [map_add, map_smul, hw₀, smul_eq_mul, mul_one]
  exact zmod_two_add_self _

@[expose] noncomputable def burnsideB49_proj : W →ₗ[ZMod 2] ↥(LinearMap.ker φ) :=
  LinearMap.codRestrict (LinearMap.ker φ) (LinearMap.id + φ.smulRight w₀)
    (fun x => LinearMap.mem_ker.2 (burnsideB49_proj_mem φ hw₀ x))

theorem burnsideB49_proj_apply (x : W) :
    ((burnsideB49_proj φ hw₀ x : ↥(LinearMap.ker φ)) : W) = x + φ x • w₀ := rfl

@[expose] noncomputable def burnsideB49_extendLin (T : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ)) :
    W →ₗ[ZMod 2] W :=
  (LinearMap.ker φ).subtype ∘ₗ T ∘ₗ burnsideB49_proj φ hw₀ + φ.smulRight w₀

theorem burnsideB49_extendLin_apply (T : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ)) (x : W) :
    burnsideB49_extendLin φ hw₀ T x = ((T (burnsideB49_proj φ hw₀ x) : ↥(LinearMap.ker φ)) : W) +
      φ x • w₀ := rfl

theorem burnsideB49_phi_extendLin (T : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ)) (x : W) :
    φ (burnsideB49_extendLin φ hw₀ T x) = φ x := by
  rw [burnsideB49_extendLin_apply, map_add, map_smul, hw₀, smul_eq_mul, mul_one,
    LinearMap.mem_ker.1 (T (burnsideB49_proj φ hw₀ x)).2, zero_add]

theorem burnsideB49_proj_extendLin (T : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ)) (x : W) :
    burnsideB49_proj φ hw₀ (burnsideB49_extendLin φ hw₀ T x) = T (burnsideB49_proj φ hw₀ x) := by
  apply Subtype.ext
  rw [burnsideB49_proj_apply, burnsideB49_phi_extendLin, burnsideB49_extendLin_apply]
  calc ((T (burnsideB49_proj φ hw₀ x) : ↥(LinearMap.ker φ)) : W) + φ x • w₀ + φ x • w₀
      = (T (burnsideB49_proj φ hw₀ x) : W) + (φ x • w₀ + φ x • w₀) := by abel
    _ = _ := by rw [two_add_self, add_zero]

theorem burnsideB49_extendLin_comp (T₁ T₂ : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ))
    (x : W) :
    burnsideB49_extendLin φ hw₀ T₁ (burnsideB49_extendLin φ hw₀ T₂ x) =
      burnsideB49_extendLin φ hw₀ (T₁ ∘ₗ T₂) x := by
  rw [burnsideB49_extendLin_apply, burnsideB49_proj_extendLin, burnsideB49_phi_extendLin,
    burnsideB49_extendLin_apply]
  rfl

theorem burnsideB49_extendLin_one (x : W) :
    burnsideB49_extendLin φ hw₀ (LinearMap.id) x = x := by
  rw [burnsideB49_extendLin_apply]
  change (x + φ x • w₀) + φ x • w₀ = x
  calc x + φ x • w₀ + φ x • w₀ = x + (φ x • w₀ + φ x • w₀) := by abel
    _ = x := by rw [two_add_self, add_zero]

@[expose] noncomputable def burnsideB49_extend (T : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) :
    W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofLinear (burnsideB49_extendLin φ hw₀ T.toLinearMap)
    (burnsideB49_extendLin φ hw₀ T.symm.toLinearMap)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, burnsideB49_extendLin_comp]
      have : (T.toLinearMap ∘ₗ T.symm.toLinearMap) = LinearMap.id := by
        exact LinearMap.ext fun y => T.apply_symm_apply y
      rw [this, burnsideB49_extendLin_one]
      rfl)
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, burnsideB49_extendLin_comp]
      have : (T.symm.toLinearMap ∘ₗ T.toLinearMap) = LinearMap.id := by
        exact LinearMap.ext fun y => T.symm_apply_apply y
      rw [this, burnsideB49_extendLin_one]
      rfl)

theorem burnsideB49_extend_apply (T : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) (x : W) :
    burnsideB49_extend φ hw₀ T x = ((T (burnsideB49_proj φ hw₀ x) : ↥(LinearMap.ker φ)) : W) +
      φ x • w₀ := rfl

theorem burnsideB49_extend_mem_K (T : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) :
    burnsideB49_extend φ hw₀ T ∈ burnsideB49_K φ w₀ := by
  refine ⟨fun x => burnsideB49_phi_extendLin φ hw₀ T.toLinearMap x, ?_⟩
  rw [burnsideB49_extend_apply, hw₀, one_smul]
  have : burnsideB49_proj φ hw₀ w₀ = 0 := by
    apply Subtype.ext
    rw [burnsideB49_proj_apply, hw₀, one_smul]
    exact two_add_self w₀
  rw [this, map_zero]
  simp

theorem burnsideB49_Kres_extend (T : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) :
    burnsideB49_Kres φ w₀ ⟨burnsideB49_extend φ hw₀ T, burnsideB49_extend_mem_K φ hw₀ T⟩ = T := by
  ext y
  rw [burnsideB49_Kres_apply, burnsideB49_extend_apply, LinearMap.mem_ker.1 y.2, zero_smul, add_zero]
  congr 2
  apply Subtype.ext
  rw [burnsideB49_proj_apply, LinearMap.mem_ker.1 y.2, zero_smul, add_zero]

theorem burnsideB49_Kres_surjective : Function.Surjective (burnsideB49_Kres φ w₀) := fun T =>
  ⟨⟨burnsideB49_extend φ hw₀ T, burnsideB49_extend_mem_K φ hw₀ T⟩, burnsideB49_Kres_extend φ hw₀ T⟩

theorem burnsideB49_Kres_injective : Function.Injective (burnsideB49_Kres φ w₀) := by
  rw [injective_iff_map_eq_one]
  intro k hk
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  have h1 : (k : W ≃ₗ[ZMod 2] W) (x + φ x • w₀) = x + φ x • w₀ := by
    have := congrArg (fun T : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ) =>
      (T (burnsideB49_proj φ hw₀ x) : W)) hk
    exact this
  rw [map_add, map_smul, k.2.2] at h1
  have h2 := add_right_cancel h1
  rw [h2]
  simp

omit hw₀ in
theorem burnsideB49_finrank_ker [FiniteDimensional (ZMod 2) W] {w₀ : W} (hw₀ : φ w₀ = 1) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker φ) + 1 = Module.finrank (ZMod 2) W := by
  have h := LinearMap.finrank_range_add_finrank_ker φ
  have hr : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨c • w₀, by rw [map_smul, hw₀, smul_eq_mul, mul_one]⟩
  rw [hr, finrank_top, Module.finrank_self] at h
  omega

end Extend

omit [Module (ZMod 2) W] in
theorem burnsideB49_hom_eq_zero_of_perfect {G : Type*} [Group G] (hG : Group.IsPerfect G)
    {M : Type*} [AddCommGroup M] {f : G → M} (h : ∀ g k, f (g * k) = f g + f k) :
    ∀ g, f g = 0 := by
  let ψ : G →* Multiplicative M :=
    { toFun := fun g => Multiplicative.ofAdd (f g)
      map_one' := by
        have := h 1 1
        rw [mul_one] at this
        apply Multiplicative.toAdd.injective
        simpa using this
      map_mul' := fun g k => h g k }
  intro g
  have : g ∈ commutator G := by rw [hG.commutator_eq_top]; trivial
  have h2 : g ∈ ψ.ker := Abelianization.commutator_subset_ker ψ this
  exact Multiplicative.toAdd.injective (MonoidHom.mem_ker.1 h2)

theorem burnsideB49_K_perfect [FiniteDimensional (ZMod 2) W] {φ : Module.Dual (ZMod 2) W} {w₀ : W}
    (hw₀ : φ w₀ = 1) (h3 : 3 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker φ)) :
    Group.IsPerfect ↥(burnsideB49_K φ w₀) :=
  have := isPerfect_linearEquiv h3
  Group.IsPerfect.ofSurjective
    (f := (MulEquiv.ofBijective (burnsideB49_Kres φ w₀)
      ⟨burnsideB49_Kres_injective φ hw₀, burnsideB49_Kres_surjective φ hw₀⟩).symm.toMonoidHom)
    (MulEquiv.ofBijective (burnsideB49_Kres φ w₀)
      ⟨burnsideB49_Kres_injective φ hw₀, burnsideB49_Kres_surjective φ hw₀⟩).symm.surjective

section KFixNat

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_kfix_nat [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ : Module.Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1) (hdim : 5 ≤ Module.finrank (ZMod 2) W)
    (θ : W ≃ₗ[ZMod 2] ↥(LinearMap.ker q))
    (hθ : ∀ g w, ((θ (g w) : ↥(LinearMap.ker q)) : V) = ρ g ((θ w : ↥(LinearMap.ker q)) : V)) :
    ∃ v : V, q v = w₀ ∧ ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ρ k v = v := by
  have hker := burnsideB49_finrank_ker φ hw₀
  obtain ⟨x₀, hx₀⟩ := hqs w₀
  have hmem : ∀ k : ↥(burnsideB49_K φ w₀), ρ k x₀ - x₀ ∈ LinearMap.ker q := fun k => by
    rw [LinearMap.mem_ker, map_sub, hq, hx₀, k.2.2, sub_self]
  let δ : ↥(burnsideB49_K φ w₀) → W := fun k => θ.symm ⟨ρ k x₀ - x₀, hmem k⟩
  have hδθ : ∀ k, ((θ (δ k) : ↥(LinearMap.ker q)) : V) = ρ k x₀ - x₀ := fun k => by
    simp only [δ, LinearEquiv.apply_symm_apply]
  have hδcoc : ∀ k k' : ↥(burnsideB49_K φ w₀),
      δ (k * k') = δ k + (k : W ≃ₗ[ZMod 2] W) (δ k') := by
    intro k k'
    apply θ.injective
    apply Subtype.ext
    rw [hδθ, map_add, Submodule.coe_add, hδθ, hθ, hδθ, Subgroup.coe_mul, map_mul,
      LinearEquiv.mul_apply, map_sub]
    abel
  have hperf := burnsideB49_K_perfect hw₀ (by omega)
  have hε : ∀ k : ↥(burnsideB49_K φ w₀), φ (δ k) = 0 := by
    refine burnsideB49_hom_eq_zero_of_perfect hperf (f := fun k => φ (δ k)) ?_
    intro k k'
    simp only [hδcoc, map_add]
    rw [k.2.1]
  let δE : ↥(burnsideB49_K φ w₀) → ↥(LinearMap.ker φ) := fun k => ⟨δ k, LinearMap.mem_ker.2 (hε k)⟩
  have hδE : ∀ k k' : ↥(burnsideB49_K φ w₀),
      δE (k * k') = δE k + burnsideB49_Kres φ w₀ k (δE k') := by
    intro k k'
    apply Subtype.ext
    exact hδcoc k k'
  have hdE : 4 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker φ) := by omega
  obtain ⟨w, hw⟩ := exists_eq_of_isCocycle hdE (burnsideB49_Kres φ w₀)
    (fun f d h => burnsideB49_Kres_surjective φ hw₀ (LinearEquiv.transvection h)) δE hδE
    (fun k hk => by
      have : k = 1 := burnsideB49_Kres_injective φ hw₀ (by rw [hk, map_one])
      subst this
      apply Subtype.ext
      apply θ.injective
      apply Subtype.ext
      rw [hδθ]
      simp)
  refine ⟨x₀ + ((θ (w : W) : ↥(LinearMap.ker q)) : V), ?_, ?_⟩
  · rw [map_add, hx₀]
    have := (θ (w : W)).2
    rw [LinearMap.mem_ker.1 this, add_zero]
  · intro k hk hkw
    set u : V := ((θ (w : W) : ↥(LinearMap.ker q)) : V) with hu
    have hkK : k ∈ burnsideB49_K φ w₀ := ⟨hk, hkw⟩
    have h1 := hw ⟨k, hkK⟩
    have h2 : ρ k x₀ - x₀ = ρ k u + u := by
      rw [← hδθ ⟨k, hkK⟩]
      have : δ ⟨k, hkK⟩ = k (w : W) + (w : W) := congrArg Subtype.val h1
      rw [this, map_add, Submodule.coe_add, hθ]
    rw [sub_eq_iff_eq_add] at h2
    rw [map_add, h2]
    calc ρ k u + u + x₀ + ρ k u = (ρ k u + ρ k u) + u + x₀ := by abel
      _ = x₀ + u := by rw [two_add_self, zero_add, add_comm]

end KFixNat

section KFixDual

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_Kres_symm_apply {φ : Module.Dual (ZMod 2) W} {w₀ : W}
    (k : ↥(burnsideB49_K φ w₀)) (y : ↥(LinearMap.ker φ)) :
    (((burnsideB49_Kres φ w₀ k).symm y : ↥(LinearMap.ker φ)) : W) = (k : W ≃ₗ[ZMod 2] W).symm y := by
  rw [LinearEquiv.eq_symm_apply]
  have := burnsideB49_Kres_apply k ((burnsideB49_Kres φ w₀ k).symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

@[expose] noncomputable def burnsideB49_KresDual (φ : Module.Dual (ZMod 2) W) (w₀ : W) :
    ↥(burnsideB49_K φ w₀) →* (Module.Dual (ZMod 2) ↥(LinearMap.ker φ) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) ↥(LinearMap.ker φ)) where
  toFun k := (burnsideB49_Kres φ w₀ k).symm.dualMap
  map_one' := by
    ext ψ y
    rfl
  map_mul' k k' := by
    ext ψ y
    rfl

theorem burnsideB49_KresDual_apply (φ : Module.Dual (ZMod 2) W) (w₀ : W)
    (k : ↥(burnsideB49_K φ w₀)) (ψ : Module.Dual (ZMod 2) ↥(LinearMap.ker φ))
    (y : ↥(LinearMap.ker φ)) :
    burnsideB49_KresDual φ w₀ k ψ y = ψ ((burnsideB49_Kres φ w₀ k).symm y) := rfl

theorem burnsideB49_kfix_dual [FiniteDimensional (ZMod 2) W] [Finite V]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ : Module.Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1) (hdim : 5 ≤ Module.finrank (ZMod 2) W)
    (θ' : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ↥(LinearMap.ker q))
    (hθ' : ∀ g w (u u' : ↥(LinearMap.ker q)), ρ g (u' : V) = (u : V) → θ' (g w) u = θ' w u') :
    ∃ v : V, q v = w₀ ∧ ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ρ k v = v := by
  have hker := burnsideB49_finrank_ker φ hw₀
  haveI : Finite ↥(LinearMap.ker q) := inferInstance
  haveI : FiniteDimensional (ZMod 2) ↥(LinearMap.ker q) := Module.Finite.of_finite
  let Θ : ↥(LinearMap.ker q) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W :=
    (Module.evalEquiv (ZMod 2) ↥(LinearMap.ker q)).trans θ'.dualMap
  have hΘ : ∀ u w, Θ u w = θ' w u := fun u w => rfl
  have hΘg : ∀ (g : W ≃ₗ[ZMod 2] W) (u u' : ↥(LinearMap.ker q)), ρ g (u : V) = (u' : V) →
      ∀ w, Θ u' w = Θ u (g.symm w) := by
    intro g u u' h w
    rw [hΘ, hΘ]
    have := hθ' g (g.symm w) u' u h
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨x₀, hx₀⟩ := hqs w₀
  have hmem : ∀ k : ↥(burnsideB49_K φ w₀), ρ k x₀ - x₀ ∈ LinearMap.ker q := fun k => by
    rw [LinearMap.mem_ker, map_sub, hq, hx₀, k.2.2, sub_self]
  have hmem2 : ∀ k : ↥(burnsideB49_K φ w₀), ∀ y : V, y ∈ LinearMap.ker q →
      ρ k y ∈ LinearMap.ker q := fun k y hy => by
    rw [LinearMap.mem_ker, hq, LinearMap.mem_ker.1 hy, map_zero]
  let δ : ↥(burnsideB49_K φ w₀) → Module.Dual (ZMod 2) W := fun k => Θ ⟨ρ k x₀ - x₀, hmem k⟩
  have hδcoc : ∀ (k k' : ↥(burnsideB49_K φ w₀)) (w : W),
      δ (k * k') w = δ k w + δ k' ((k : W ≃ₗ[ZMod 2] W).symm w) := by
    intro k k' w
    have h1 : (⟨ρ ↑(k * k') x₀ - x₀, hmem (k * k')⟩ : ↥(LinearMap.ker q)) =
        ⟨ρ k x₀ - x₀, hmem k⟩ + ⟨ρ k (ρ k' x₀ - x₀), hmem2 k _ (hmem k')⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_add, Subgroup.coe_mul, map_mul, LinearEquiv.mul_apply, map_sub]
      abel
    have h2 : δ (k * k') = Θ ⟨ρ k x₀ - x₀, hmem k⟩ + Θ ⟨ρ k (ρ k' x₀ - x₀), hmem2 k _ (hmem k')⟩ := by
      simp only [δ]
      rw [h1, map_add]
    rw [h2, LinearMap.add_apply]
    congr 1
    exact hΘg k ⟨ρ k' x₀ - x₀, hmem k'⟩ _ rfl w
  have hperf := burnsideB49_K_perfect hw₀ (by omega)
  have hε : ∀ k : ↥(burnsideB49_K φ w₀), δ k w₀ = 0 := by
    refine burnsideB49_hom_eq_zero_of_perfect hperf (f := fun k => δ k w₀) ?_
    intro k k'
    simp only [hδcoc]
    have : (k : W ≃ₗ[ZMod 2] W).symm w₀ = w₀ := (LinearEquiv.symm_apply_eq _).2 k.2.2.symm
    rw [this]
  let δE : ↥(burnsideB49_K φ w₀) → Module.Dual (ZMod 2) ↥(LinearMap.ker φ) :=
    fun k => (δ k) ∘ₗ (LinearMap.ker φ).subtype
  have hδE : ∀ k k' : ↥(burnsideB49_K φ w₀),
      δE (k * k') = δE k + burnsideB49_KresDual φ w₀ k (δE k') := by
    intro k k'
    ext y
    simp only [δE, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.add_apply,
      burnsideB49_KresDual_apply, hδcoc, burnsideB49_Kres_symm_apply]
  have hdE : 4 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker φ) := by omega
  haveI : FiniteDimensional (ZMod 2) ↥(LinearMap.ker φ) := inferInstance
  have hρ : ∀ (f' : Module.Dual (ZMod 2) (Module.Dual (ZMod 2) ↥(LinearMap.ker φ)))
      (d' : Module.Dual (ZMod 2) ↥(LinearMap.ker φ)) (h : f' d' = 0),
      ∃ k : ↥(burnsideB49_K φ w₀), burnsideB49_KresDual φ w₀ k = LinearEquiv.transvection h := by
    intro f' d' h
    obtain ⟨x, hx⟩ := (Module.evalEquiv (ZMod 2) ↥(LinearMap.ker φ)).surjective f'
    have hx' : ∀ ψ, f' ψ = ψ x := fun ψ => by rw [← hx]; rfl
    have hd'x : d' x = 0 := by rw [← hx' d']; exact h
    obtain ⟨k, hk⟩ := burnsideB49_Kres_surjective φ hw₀ (LinearEquiv.transvection hd'x)
    refine ⟨k, ?_⟩
    ext ψ y
    rw [burnsideB49_KresDual_apply, hk]
    have hsymm : (LinearEquiv.transvection hd'x).symm = LinearEquiv.transvection hd'x := by
      have := transvection_inv hd'x
      exact this
    have e1 : (LinearEquiv.transvection hd'x) y = y + d' y • x := transvection_apply hd'x y
    have e2 : (LinearEquiv.transvection h ψ) = ψ + f' ψ • d' := transvection_apply h ψ
    rw [hsymm, e1, e2, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hx' ψ,
      smul_eq_mul, smul_eq_mul, mul_comm]
  have hker : ∀ k : ↥(burnsideB49_K φ w₀), burnsideB49_KresDual φ w₀ k = 1 → δE k = 0 := by
    intro k hk
    have hk1 : k = 1 := by
      apply burnsideB49_Kres_injective φ hw₀
      rw [map_one]
      have hT : ∀ y, (burnsideB49_Kres φ w₀ k).symm y = y := by
        intro y
        have h0 : (burnsideB49_Kres φ w₀ k).symm y - y = 0 := by
          rw [← Module.forall_dual_apply_eq_zero_iff (ZMod 2)]
          intro ψ
          have := congrArg (fun T : Module.Dual (ZMod 2) ↥(LinearMap.ker φ) ≃ₗ[ZMod 2]
              Module.Dual (ZMod 2) ↥(LinearMap.ker φ) => T ψ y) hk
          simp only [burnsideB49_KresDual_apply] at this
          change ψ (((burnsideB49_Kres φ w₀ k).symm) y) = ψ y at this
          rw [map_sub, this, sub_self]
        exact sub_eq_zero.1 h0
      apply LinearEquiv.ext
      intro y
      have := hT ((burnsideB49_Kres φ w₀ k) y)
      rw [LinearEquiv.symm_apply_apply] at this
      exact this.symm
    subst hk1
    ext y
    simp only [δE, δ, LinearMap.comp_apply, Submodule.subtype_apply]
    have : (⟨ρ ((1 : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) x₀ - x₀, hmem 1⟩ :
        ↥(LinearMap.ker q)) = 0 := by
      apply Subtype.ext
      simp
    rw [this, map_zero]
    rfl
  have hdE' : 4 ≤ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) ↥(LinearMap.ker φ)) := by
    rw [Subspace.dual_finrank_eq]
    exact hdE
  obtain ⟨ψ, hψ⟩ := exists_eq_of_isCocycle hdE' (burnsideB49_KresDual φ w₀) hρ δE hδE hker
  let Ψ₁ : Module.Dual (ZMod 2) W := ψ ∘ₗ burnsideB49_proj φ hw₀
  let u : ↥(LinearMap.ker q) := Θ.symm Ψ₁
  have hΘu : Θ u = Ψ₁ := LinearEquiv.apply_symm_apply _ _
  have hkey : ∀ (k : ↥(burnsideB49_K φ w₀)) (w : W),
      δ k w = Ψ₁ ((k : W ≃ₗ[ZMod 2] W).symm w) + Ψ₁ w := by
    intro k w
    have hw : w = ((burnsideB49_proj φ hw₀ w : ↥(LinearMap.ker φ)) : W) + φ w • w₀ := by
      rw [burnsideB49_proj_apply]
      calc w = w + (φ w • w₀ + φ w • w₀) := by rw [two_add_self, add_zero]
        _ = _ := by abel
    have hδw : δ k w = δ k ((burnsideB49_proj φ hw₀ w : ↥(LinearMap.ker φ)) : W) := by
      conv_lhs => rw [hw]
      rw [map_add, map_smul, hε k, smul_zero, add_zero]
    have h2 := congrArg (fun f : Module.Dual (ZMod 2) ↥(LinearMap.ker φ) =>
      f (burnsideB49_proj φ hw₀ w)) (hψ k)
    simp only [δE, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.add_apply,
      burnsideB49_KresDual_apply] at h2
    have hproj : (burnsideB49_Kres φ w₀ k).symm (burnsideB49_proj φ hw₀ w) =
        burnsideB49_proj φ hw₀ ((k : W ≃ₗ[ZMod 2] W).symm w) := by
      apply Subtype.ext
      rw [burnsideB49_Kres_symm_apply, burnsideB49_proj_apply, burnsideB49_proj_apply, map_add,
        map_smul]
      have h3 : (k : W ≃ₗ[ZMod 2] W).symm w₀ = w₀ := (LinearEquiv.symm_apply_eq _).2 k.2.2.symm
      have h4 : φ ((k : W ≃ₗ[ZMod 2] W).symm w) = φ w := by
        have := k.2.1 ((k : W ≃ₗ[ZMod 2] W).symm w)
        rw [LinearEquiv.apply_symm_apply] at this
        exact this.symm
      rw [h3, h4]
    rw [hδw, h2, hproj]
    rfl
  refine ⟨x₀ + (u : V), ?_, ?_⟩
  · rw [map_add, hx₀, LinearMap.mem_ker.1 u.2, add_zero]
  · intro k hk hkw
    have hkK : k ∈ burnsideB49_K φ w₀ := ⟨hk, hkw⟩
    have hm3 : ρ k (u : V) + (u : V) ∈ LinearMap.ker q := add_mem (hmem2 ⟨k, hkK⟩ _ u.2) u.2
    have h1 : (⟨ρ k x₀ - x₀, hmem ⟨k, hkK⟩⟩ : ↥(LinearMap.ker q)) = ⟨ρ k (u : V) + (u : V), hm3⟩ := by
      apply Θ.injective
      ext w
      have e1 : Θ ⟨ρ k x₀ - x₀, hmem ⟨k, hkK⟩⟩ w = δ ⟨k, hkK⟩ w := rfl
      have e2 : Θ ⟨ρ k (u : V) + (u : V), hm3⟩ =
          Θ ⟨ρ k (u : V), hmem2 ⟨k, hkK⟩ _ u.2⟩ + Θ u := by
        rw [← map_add]
        rfl
      have e3 := hΘg k u ⟨ρ k (u : V), hmem2 ⟨k, hkK⟩ _ u.2⟩ rfl w
      rw [e1, hkey, e2, LinearMap.add_apply, e3, hΘu]
    have h2 : ρ k x₀ - x₀ = ρ k (u : V) + (u : V) := congrArg Subtype.val h1
    rw [sub_eq_iff_eq_add] at h2
    rw [map_add, h2]
    calc ρ k (u : V) + (u : V) + x₀ + ρ k (u : V) = (ρ k (u : V) + ρ k (u : V)) + (u : V) + x₀ := by abel
      _ = x₀ + (u : V) := by rw [two_add_self, zero_add, add_comm]

end KFixDual

section Core

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_exists_one {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0) : ∃ w₀, φ w₀ = 1 := by
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra! h
    exact hφ (LinearMap.ext h)
  exact ⟨x, zmod_two_eq_one_of_ne_zero hx⟩

theorem burnsideB49_core_nat [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    (hdim : 5 ≤ Module.finrank (ZMod 2) W) (θ : W ≃ₗ[ZMod 2] ↥(LinearMap.ker q))
    (hθ : ∀ g w, ((θ (g w) : ↥(LinearMap.ker q)) : V) = ρ g ((θ w : ↥(LinearMap.ker q)) : V))
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) (hE4 : Nat.card E = 4)
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0)
    (hEtr : ∀ e ∈ E, e ≠ 1 → ∃ (w : W) (h : φ w = 0), e = burnsideB49_tv φ w h)
    (hEquad : ∀ e ∈ E, ∀ e' ∈ E, ∀ v : V, ρ e (ρ e' v - v) = ρ e' v - v) :
    ∃ U' : Submodule (ZMod 2) V, (∀ g, ∀ x ∈ U', ρ g x ∈ U') ∧
      IsCompl (LinearMap.ker q) U' := by
  obtain ⟨w₀, hw₀⟩ := burnsideB49_exists_one hφ
  obtain ⟨v, hvq, hv⟩ := burnsideB49_kfix_nat ρ q hqs hq hw₀ hdim θ hθ
  exact burnsideB49_complement_of_kfix ρ q hq hφ hw₀
    (fun w w' h h' v => burnsideB49_Q_quadratic ρ E hE4 hEtr hEquad w w' h h' v) v hvq hv

theorem burnsideB49_core_dual [FiniteDimensional (ZMod 2) W] [Finite V]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    (hdim : 5 ≤ Module.finrank (ZMod 2) W)
    (θ' : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ↥(LinearMap.ker q))
    (hθ' : ∀ g w (u u' : ↥(LinearMap.ker q)), ρ g (u' : V) = (u : V) → θ' (g w) u = θ' w u')
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) (hE4 : Nat.card E = 4)
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0)
    (hEtr : ∀ e ∈ E, e ≠ 1 → ∃ (w : W) (h : φ w = 0), e = burnsideB49_tv φ w h)
    (hEquad : ∀ e ∈ E, ∀ e' ∈ E, ∀ v : V, ρ e (ρ e' v - v) = ρ e' v - v) :
    ∃ U' : Submodule (ZMod 2) V, (∀ g, ∀ x ∈ U', ρ g x ∈ U') ∧
      IsCompl (LinearMap.ker q) U' := by
  obtain ⟨w₀, hw₀⟩ := burnsideB49_exists_one hφ
  obtain ⟨v, hvq, hv⟩ := burnsideB49_kfix_dual ρ q hqs hq hw₀ hdim θ' hθ'
  exact burnsideB49_complement_of_kfix ρ q hq hφ hw₀
    (fun w w' h h' v => burnsideB49_Q_quadratic ρ E hE4 hEtr hEquad w w' h h' v) v hvq hv

end Core

end KLevi

section Interface

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

@[expose] def burnsideB49_autLin {X : Type*} [CommGroup X] (hX : ∀ x : X, x ^ 2 = 1) :
    MulAut X ≃* (F2Vec X hX ≃ₗ[ZMod 2] F2Vec X hX) where
  toFun g :=
    let e : F2Vec X hX ≃+ F2Vec X hX :=
      { toFun := fun x => F2Vec.ofV hX (g (F2Vec.toV hX x))
        invFun := fun x => F2Vec.ofV hX (g.symm (F2Vec.toV hX x))
        left_inv := fun x => by
          simp only [F2Vec.toV_ofV, MulEquiv.symm_apply_apply, F2Vec.ofV_toV]
        right_inv := fun x => by
          simp only [F2Vec.toV_ofV, MulEquiv.apply_symm_apply, F2Vec.ofV_toV]
        map_add' := fun x y => by
          rw [F2Vec.toV_add, map_mul, F2Vec.ofV_mul] }
    e.toLinearEquiv (fun c x => ZMod.map_smul e.toAddMonoidHom c x)
  invFun f :=
    { toFun := fun x => F2Vec.toV hX (f (F2Vec.ofV hX x))
      invFun := fun x => F2Vec.toV hX (f.symm (F2Vec.ofV hX x))
      left_inv := fun x => by
        simp only [F2Vec.ofV_toV, LinearEquiv.symm_apply_apply, F2Vec.toV_ofV]
      right_inv := fun x => by
        simp only [F2Vec.ofV_toV, LinearEquiv.apply_symm_apply, F2Vec.toV_ofV]
      map_mul' := fun x y => by
        rw [F2Vec.ofV_mul, map_add, F2Vec.toV_add] }
  left_inv g := MulEquiv.ext fun x => rfl
  right_inv f := LinearEquiv.ext fun x => rfl
  map_mul' g h := LinearEquiv.ext fun x => rfl

theorem burnsideB49_autLin_apply {X : Type*} [CommGroup X] (hX : ∀ x : X, x ^ 2 = 1)
    (g : MulAut X) (x : F2Vec X hX) :
    burnsideB49_autLin hX g x = F2Vec.ofV hX (g (F2Vec.toV hX x)) := rfl

section Quot

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)

include hV in
theorem burnsideB49_hW : ∀ x : V ⧸ U, x ^ 2 = 1 := fun x =>
  QuotientGroup.induction_on x fun v => by
    rw [← QuotientGroup.mk_pow, hV v, QuotientGroup.mk_one]

abbrev burnsideB49_W : Type := F2Vec (V ⧸ U) (burnsideB49_hW hV U)

variable (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)

include hG in
theorem burnsideB49_map_eq (g : ↥G) : U.map ((g : MulAut V) : V ≃* V).toMonoidHom = U := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hG g g.2 u hu
  · intro hy
    refine ⟨(g : MulAut V)⁻¹ y, hG g⁻¹ (G.inv_mem g.2) y hy, ?_⟩
    change (g : MulAut V) ((g : MulAut V)⁻¹ y) = y
    rw [← MulAut.mul_apply, mul_inv_cancel]
    rfl

@[expose] noncomputable def burnsideB49_quotAut (g : ↥G) : MulAut (V ⧸ U) :=
  QuotientGroup.congr U U ((g : MulAut V) : V ≃* V) (burnsideB49_map_eq U G hG g)

theorem burnsideB49_quotAut_mk (g : ↥G) (v : V) :
    burnsideB49_quotAut U G hG g (QuotientGroup.mk v) = QuotientGroup.mk ((g : MulAut V) v) :=
  QuotientGroup.congr_mk _ _ _ _ v

@[expose] noncomputable def burnsideB49_iota :
    ↥G →* (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) where
  toFun g := burnsideB49_autLin (burnsideB49_hW hV U) (burnsideB49_quotAut U G hG g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      change F2Vec.ofV _ (burnsideB49_quotAut U G hG 1 (QuotientGroup.mk v)) = F2Vec.ofV _ (QuotientGroup.mk v)
      rw [burnsideB49_quotAut_mk]
      rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      change F2Vec.ofV _ (burnsideB49_quotAut U G hG (g * h) (QuotientGroup.mk v)) =
        F2Vec.ofV _ (burnsideB49_quotAut U G hG g (burnsideB49_quotAut U G hG h (QuotientGroup.mk v)))
      rw [burnsideB49_quotAut_mk, burnsideB49_quotAut_mk, burnsideB49_quotAut_mk]
      rfl

@[expose] noncomputable def burnsideB49_q : F2Vec V hV →ₗ[ZMod 2] burnsideB49_W hV U :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk' (fun x => F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk (F2Vec.toV hV x)))
      (fun x y => by
        rw [F2Vec.toV_add, QuotientGroup.mk_mul, F2Vec.ofV_mul]))

theorem burnsideB49_q_apply (x : F2Vec V hV) :
    burnsideB49_q hV U x = F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk (F2Vec.toV hV x)) := rfl

theorem burnsideB49_q_surjective : Function.Surjective (burnsideB49_q hV U) := by
  intro w
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (F2Vec.toV (burnsideB49_hW hV U) w)
  exact ⟨F2Vec.ofV hV v, by rw [burnsideB49_q_apply, F2Vec.toV_ofV, hv, F2Vec.ofV_toV]⟩

theorem burnsideB49_mem_ker_q (x : F2Vec V hV) :
    x ∈ LinearMap.ker (burnsideB49_q hV U) ↔ F2Vec.toV hV x ∈ U := by
  rw [LinearMap.mem_ker, burnsideB49_q_apply, ← QuotientGroup.eq_one_iff]
  constructor
  · intro h
    have := congrArg (F2Vec.toV (burnsideB49_hW hV U)) h
    exact this
  · intro h
    have : F2Vec.toV (burnsideB49_hW hV U) (F2Vec.ofV (burnsideB49_hW hV U)
        (QuotientGroup.mk (F2Vec.toV hV x))) = 1 := h
    exact this

theorem burnsideB49_q_equiv (g : ↥G) (x : F2Vec V hV) :
    burnsideB49_q hV U (burnsideB49_autLin hV (g : MulAut V) x) =
      burnsideB49_iota hV U G hG g (burnsideB49_q hV U x) := by
  rw [burnsideB49_q_apply, burnsideB49_q_apply]
  change F2Vec.ofV _ (QuotientGroup.mk ((g : MulAut V) (F2Vec.toV hV x))) =
    F2Vec.ofV _ (burnsideB49_quotAut U G hG g (QuotientGroup.mk (F2Vec.toV hV x)))
  rw [burnsideB49_quotAut_mk]

end Quot

section Facts

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G : Subgroup (MulAut V)} {U : Subgroup V} {π : ↥(StatedSL n K) →* ↥G}

theorem burnsideB49_coords
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π) :
    ∃ β : ↥U →* Multiplicative (Fin n → K), Function.Bijective β ∧
      ∀ (γ : ↥(StatedSL n K)) (u : ↥U) (hu : ((π γ : ↥G) : MulAut V) (u : V) ∈ U),
        β ⟨((π γ : ↥G) : MulAut V) (u : V), hu⟩ =
          Multiplicative.ofAdd ((((γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).mulVec
            (Multiplicative.toAdd (β u))) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord (D := FFModel.nat (StatedSL n K)) rfl rfl
    hreal
  let β' : ↥U →* Multiplicative (Fin n → K) := β
  have hinj : Function.Injective β' := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (Subgroup.mem_bot.1 this)
  exact ⟨β', ⟨hinj, hβs⟩, fun γ u hu => hβe γ u hu⟩

theorem burnsideB49_eq_one_of_mulVec {γ : Matrix (Fin n) (Fin n) K}
    (h : ∀ x : Fin n → K, γ.mulVec x = x) : γ = 1 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem burnsideB49_eq_one_of_act
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π) (γ : ↥(StatedSL n K))
    (hg : ∀ u ∈ U, ((π γ : ↥G) : MulAut V) u = u) : γ = 1 := by
  obtain ⟨β, hβb, hβe⟩ := burnsideB49_coords hreal
  have hmat : ∀ x : Fin n → K, (((γ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).mulVec x = x := by
    intro x
    obtain ⟨u, hu⟩ := hβb.2 (Multiplicative.ofAdd x)
    have hU : ((π γ : ↥G) : MulAut V) (u : V) ∈ U := hreal.2.2.2.1 (π γ) u u.2
    have h1 := hβe γ u hU
    have h2 : (⟨((π γ : ↥G) : MulAut V) (u : V), hU⟩ : ↥U) = u := Subtype.ext (hg u u.2)
    rw [h2, hu] at h1
    have := congrArg Multiplicative.toAdd h1
    simp only [toAdd_ofAdd] at this
    exact this.symm
  have : (γ : GL (Fin n) K) = 1 := by
    apply Units.ext
    exact burnsideB49_eq_one_of_mulVec hmat
  exact Subtype.ext this

theorem burnsideB49_faithfulU
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π) :
    ∀ g : ↥G, (∀ u ∈ U, (g : MulAut V) u = u) → g = 1 := by
  intro g hg
  obtain ⟨γ, rfl⟩ : ∃ γ : ↥(StatedSL n K), π γ = g := hreal.1 g
  rw [burnsideB49_eq_one_of_act hreal γ hg, map_one]

theorem burnsideB49_pi_injective
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  exact burnsideB49_eq_one_of_act hreal γ (fun u _ => by rw [hγ]; rfl)

theorem burnsideB49_card_U [Finite K]
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π) :
    Nat.card ↥U = Nat.card K ^ n := by
  obtain ⟨β, hβb, -⟩ := burnsideB49_coords hreal
  rw [Nat.card_congr (Equiv.ofBijective β hβb)]
  change Nat.card (Fin n → K) = _
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end Facts

end Interface

section Transport

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)

@[expose] noncomputable def burnsideB49_thetaNat (φ : V ⧸ U ≃* ↥U) :
    burnsideB49_W hV U ≃ₗ[ZMod 2] ↥(LinearMap.ker (burnsideB49_q hV U)) :=
  AddEquiv.toLinearEquiv
    { toFun := fun w => ⟨F2Vec.ofV hV ((φ (F2Vec.toV (burnsideB49_hW hV U) w) : ↥U) : V),
        (burnsideB49_mem_ker_q hV U _).2 (by
          rw [F2Vec.toV_ofV]
          exact (φ _).2)⟩
      invFun := fun x => F2Vec.ofV (burnsideB49_hW hV U)
        (φ.symm ⟨F2Vec.toV hV (x : F2Vec V hV), (burnsideB49_mem_ker_q hV U _).1 x.2⟩)
      left_inv := fun w => by
        simp only [F2Vec.toV_ofV, Subtype.coe_eta, MulEquiv.symm_apply_apply, F2Vec.ofV_toV]
      right_inv := fun x => by
        apply Subtype.ext
        simp only [F2Vec.toV_ofV, MulEquiv.apply_symm_apply, F2Vec.ofV_toV]
      map_add' := fun w w' => by
        apply Subtype.ext
        simp only [F2Vec.toV_add, map_mul, Subgroup.coe_mul, F2Vec.ofV_mul]
        rfl }
    (fun c x => ZMod.map_smul _ c x)

variable (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)

theorem burnsideB49_thetaNat_equiv (φ : V ⧸ U ≃* ↥U)
    (hφ : ∀ g ∈ G, ∀ v : V, ((φ (QuotientGroup.mk ((g : MulAut V) v)) : ↥U) : V) =
      (g : MulAut V) ((φ (QuotientGroup.mk v) : ↥U) : V))
    (g : ↥G) (w : burnsideB49_W hV U) :
    ((burnsideB49_thetaNat hV U φ (burnsideB49_iota hV U G hG g w) :
        ↥(LinearMap.ker (burnsideB49_q hV U))) : F2Vec V hV) =
      burnsideB49_autLin hV (g : MulAut V)
        ((burnsideB49_thetaNat hV U φ w : ↥(LinearMap.ker (burnsideB49_q hV U))) : F2Vec V hV) := by
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (F2Vec.toV (burnsideB49_hW hV U) w)
  have hw : w = F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v) := by
    rw [hv, F2Vec.ofV_toV]
  subst hw
  have h1 : burnsideB49_iota hV U G hG g (F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v)) =
      F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk ((g : MulAut V) v)) := by
    change F2Vec.ofV _ (burnsideB49_quotAut U G hG g (QuotientGroup.mk v)) = _
    rw [burnsideB49_quotAut_mk]
  rw [h1]
  change F2Vec.ofV hV ((φ (QuotientGroup.mk ((g : MulAut V) v)) : ↥U) : V) =
    F2Vec.ofV hV ((g : MulAut V) ((φ (QuotientGroup.mk v) : ↥U) : V))
  rw [hφ g g.2 v]

@[expose] noncomputable def burnsideB49_charFun (f : DualGrp ↥U) :
    Module.Dual (ZMod 2) ↥(LinearMap.ker (burnsideB49_q hV U)) :=
  AddMonoidHom.toZModLinearMap 2
    (AddMonoidHom.mk' (fun x => Multiplicative.toAdd
      (f ⟨F2Vec.toV hV (x : F2Vec V hV), (burnsideB49_mem_ker_q hV U _).1 x.2⟩))
      (fun x y => by
        have : (⟨F2Vec.toV hV ((x + y : ↥(LinearMap.ker (burnsideB49_q hV U))) : F2Vec V hV),
            (burnsideB49_mem_ker_q hV U _).1 (x + y).2⟩ : ↥U) =
            ⟨F2Vec.toV hV (x : F2Vec V hV), (burnsideB49_mem_ker_q hV U _).1 x.2⟩ *
            ⟨F2Vec.toV hV (y : F2Vec V hV), (burnsideB49_mem_ker_q hV U _).1 y.2⟩ := rfl
        rw [this, map_mul, toAdd_mul]))

theorem burnsideB49_charFun_apply (f : DualGrp ↥U) (x : ↥(LinearMap.ker (burnsideB49_q hV U))) :
    burnsideB49_charFun hV U f x = Multiplicative.toAdd
      (f ⟨F2Vec.toV hV (x : F2Vec V hV), (burnsideB49_mem_ker_q hV U _).1 x.2⟩) := rfl

@[expose] noncomputable def burnsideB49_charOf
    (ψ : Module.Dual (ZMod 2) ↥(LinearMap.ker (burnsideB49_q hV U))) : DualGrp ↥U where
  toFun u := Multiplicative.ofAdd
    (ψ ⟨F2Vec.ofV hV (u : V), (burnsideB49_mem_ker_q hV U _).2 u.2⟩)
  map_one' := by
    have : (⟨F2Vec.ofV hV ((1 : ↥U) : V), (burnsideB49_mem_ker_q hV U _).2 (1 : ↥U).2⟩ :
        ↥(LinearMap.ker (burnsideB49_q hV U))) = 0 := rfl
    rw [this, map_zero]
    rfl
  map_mul' a b := by
    have : (⟨F2Vec.ofV hV ((a * b : ↥U) : V), (burnsideB49_mem_ker_q hV U _).2 (a * b).2⟩ :
        ↥(LinearMap.ker (burnsideB49_q hV U))) =
        ⟨F2Vec.ofV hV (a : V), (burnsideB49_mem_ker_q hV U _).2 a.2⟩ +
        ⟨F2Vec.ofV hV (b : V), (burnsideB49_mem_ker_q hV U _).2 b.2⟩ := rfl
    rw [this, map_add]
    rfl

theorem burnsideB49_charOf_charFun (f : DualGrp ↥U) :
    burnsideB49_charOf hV U (burnsideB49_charFun hV U f) = f := by
  apply DFunLike.ext
  intro u
  change Multiplicative.ofAdd (Multiplicative.toAdd (f ⟨F2Vec.toV hV (F2Vec.ofV hV (u : V)), _⟩)) = f u
  rw [ofAdd_toAdd]
  rfl

theorem burnsideB49_charFun_charOf
    (ψ : Module.Dual (ZMod 2) ↥(LinearMap.ker (burnsideB49_q hV U))) :
    burnsideB49_charFun hV U (burnsideB49_charOf hV U ψ) = ψ := by
  apply LinearMap.ext
  intro x
  rw [burnsideB49_charFun_apply]
  change Multiplicative.toAdd (Multiplicative.ofAdd
    (ψ ⟨F2Vec.ofV hV (F2Vec.toV hV (x : F2Vec V hV)), _⟩)) = ψ x
  rw [toAdd_ofAdd]
  rfl

theorem burnsideB49_charFun_mul (f g : DualGrp ↥U) :
    burnsideB49_charFun hV U (f * g) = burnsideB49_charFun hV U f + burnsideB49_charFun hV U g := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.add_apply, burnsideB49_charFun_apply, burnsideB49_charFun_apply,
    burnsideB49_charFun_apply]
  change Multiplicative.toAdd (f _ * g _) = _
  rw [toAdd_mul]

@[expose] noncomputable def burnsideB49_thetaDual (φ : V ⧸ U ≃* DualGrp ↥U) :
    burnsideB49_W hV U ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ↥(LinearMap.ker (burnsideB49_q hV U)) :=
  AddEquiv.toLinearEquiv
    { toFun := fun w => burnsideB49_charFun hV U (φ (F2Vec.toV (burnsideB49_hW hV U) w))
      invFun := fun ψ => F2Vec.ofV (burnsideB49_hW hV U) (φ.symm (burnsideB49_charOf hV U ψ))
      left_inv := fun w => by
        simp only [burnsideB49_charOf_charFun, MulEquiv.symm_apply_apply, F2Vec.ofV_toV]
      right_inv := fun ψ => by
        simp only [F2Vec.toV_ofV, MulEquiv.apply_symm_apply, burnsideB49_charFun_charOf]
      map_add' := fun w w' => by
        simp only [F2Vec.toV_add, map_mul, burnsideB49_charFun_mul] }
    (fun c x => ZMod.map_smul _ c x)

theorem burnsideB49_thetaDual_equiv (φ : V ⧸ U ≃* DualGrp ↥U)
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u')
    (g : ↥G) (w : burnsideB49_W hV U)
    (u u' : ↥(LinearMap.ker (burnsideB49_q hV U)))
    (h : burnsideB49_autLin hV (g : MulAut V) (u' : F2Vec V hV) = (u : F2Vec V hV)) :
    burnsideB49_thetaDual hV U φ (burnsideB49_iota hV U G hG g w) u =
      burnsideB49_thetaDual hV U φ w u' := by
  obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (F2Vec.toV (burnsideB49_hW hV U) w)
  have hw : w = F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v) := by
    rw [hv, F2Vec.ofV_toV]
  subst hw
  have h1 : burnsideB49_iota hV U G hG g (F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v)) =
      F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk ((g : MulAut V) v)) := by
    change F2Vec.ofV _ (burnsideB49_quotAut U G hG g (QuotientGroup.mk v)) = _
    rw [burnsideB49_quotAut_mk]
  rw [h1]
  change burnsideB49_charFun hV U (φ (QuotientGroup.mk ((g : MulAut V) v))) u =
    burnsideB49_charFun hV U (φ (QuotientGroup.mk v)) u'
  rw [burnsideB49_charFun_apply, burnsideB49_charFun_apply]
  congr 1
  exact hφ g g.2 v ⟨F2Vec.toV hV (u : F2Vec V hV), (burnsideB49_mem_ker_q hV U _).1 u.2⟩
    ⟨F2Vec.toV hV (u' : F2Vec V hV), (burnsideB49_mem_ker_q hV U _).1 u'.2⟩
    (congrArg (F2Vec.toV hV) h)

end Transport

section Bijective

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

theorem burnsideB49_card_GL_eq {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (n : ℕ) :
    Nat.card (GL (Fin n) K) = Nat.card (GL (Fin n) (ZMod 2)) := by
  haveI := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field, Matrix.card_GL_field, hK', ZMod.card]

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {n : ℕ} {K : Type}
  [Field K] [Finite K] {G : Subgroup (MulAut V)} {U : Subgroup V} {π : ↥(StatedSL n K) →* ↥G}

theorem burnsideB49_finrank_W (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U) :
    Module.finrank (ZMod 2) (burnsideB49_W hV U) = n := by
  have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (hV u)
  have hcardU : Nat.card ↥U = 2 ^ n := by rw [burnsideB49_card_U hreal, hK]
  have hcardW : Nat.card (burnsideB49_W hV U) = 2 ^ n := by
    rw [← hcardU]
    change Nat.card (Additive (V ⧸ U)) = _
    rw [Nat.card_congr Additive.toMul]
    rcases hquot with ⟨φ, -⟩ | ⟨φ, -⟩
    · exact Nat.card_congr φ.toEquiv
    · rw [Nat.card_congr φ.toEquiv, card_dualGrp hU2]
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := burnsideB49_W hV U)
  rw [Nat.card_zmod, hcardW] at h2
  exact (Nat.pow_right_injective le_rfl h2).symm

theorem burnsideB49_hG (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π) :
    ∀ g ∈ G, ∀ u ∈ U, (g : MulAut V) u ∈ U := fun g hg u hu => hreal.2.2.2.1 ⟨g, hg⟩ u hu

theorem burnsideB49_iota_injective
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U) :
    Function.Injective (burnsideB49_iota hV U G (burnsideB49_hG hreal)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hfix : ∀ x : V ⧸ U, burnsideB49_quotAut U G (burnsideB49_hG hreal) g x = x := by
    intro x
    have := congrArg (fun T : burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U =>
      F2Vec.toV (burnsideB49_hW hV U) (T (F2Vec.ofV (burnsideB49_hW hV U) x))) hg
    exact this
  apply burnsideB49_faithfulU hreal g
  intro u hu
  rcases hquot with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · obtain ⟨x, hx⟩ := φ.surjective ⟨u, hu⟩
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 := hφ g g.2 v
    rw [← burnsideB49_quotAut_mk U G (burnsideB49_hG hreal) g v, hfix, hx] at h1
    exact h1.symm
  · by_contra hne
    have hU2 : ∀ u : ↥U, u ^ 2 = 1 := fun u => Subtype.ext (hV u)
    have hne' : (⟨(g : MulAut V) u, burnsideB49_hG hreal g g.2 u hu⟩ : ↥U) * ⟨u, hu⟩⁻¹ ≠ 1 := by
      intro h
      apply hne
      have := mul_inv_eq_one.1 h
      exact congrArg Subtype.val this
    obtain ⟨f, hf⟩ := exists_dualChar_ne_one hU2 hne'
    obtain ⟨x, hx⟩ := φ.surjective f
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    have h1 := hφ g g.2 v ⟨(g : MulAut V) u, burnsideB49_hG hreal g g.2 u hu⟩ ⟨u, hu⟩ rfl
    rw [← burnsideB49_quotAut_mk U G (burnsideB49_hG hreal) g v, hfix, hx] at h1
    apply hf
    rw [map_mul, map_inv, h1, mul_inv_cancel]

theorem burnsideB49_iota_bijective (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U) :
    Function.Bijective (burnsideB49_iota hV U G (burnsideB49_hG hreal)) := by
  have hinj := burnsideB49_iota_injective hV hreal hquot
  refine ⟨hinj, ?_⟩
  haveI : Finite (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) :=
    Finite.of_injective (fun f : burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U =>
      (f : burnsideB49_W hV U → burnsideB49_W hV U)) fun _ _ h => LinearEquiv.ext (congrFun h)
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hfr := burnsideB49_finrank_W hV hK hreal hquot
  have hcardGL : Nat.card (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) =
      Nat.card (GL (Fin n) (ZMod 2)) :=
    CFSG.GroupTheory.GLnTwoSplitting.card_linearEquiv_eq hfr
  have hcardG : Nat.card ↥G = Nat.card (GL (Fin n) (ZMod 2)) := by
    rw [← burnsideB49_card_GL_eq hK n]
    have hbij : Function.Bijective π := ⟨burnsideB49_pi_injective hreal, hreal.1⟩
    rw [← Nat.card_congr (Equiv.ofBijective π hbij), CFSG.Open.StatedAPI.statedSL_eq_top_of_card_two hK n]
    exact Nat.card_congr Subgroup.topEquiv.toEquiv
  exact ((Nat.bijective_iff_injective_and_card _).2 ⟨hinj, by rw [hcardG, hcardGL]⟩).2

end Bijective

section TransData

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem burnsideB49_transvection_data (E : Subgroup (W ≃ₗ[ZMod 2] W)) (hE4 : Nat.card E = 4)
    (hrank : ∀ e ∈ E, e ≠ 1 → ∃ w : W, w ≠ 0 ∧ ∀ x, e x + x = 0 ∨ e x + x = w)
    (haxis : ∀ e ∈ E, e ≠ 1 → ∀ e' ∈ E, e' ≠ 1 → ∀ x, e x = x ↔ e' x = x) :
    ∃ φ : Module.Dual (ZMod 2) W, φ ≠ 0 ∧ ∀ e ∈ E, e ≠ 1 →
      ∃ (w : W) (h : φ w = 0), e = burnsideB49_tv φ w h := by
  classical
  obtain ⟨e₀, -, he₀, -, h₀1, -, -⟩ := burnsideB49_exists_two_ne_one E hE4
  obtain ⟨w₀, hw₀0, hw₀⟩ := hrank e₀ he₀ h₀1
  let φf : W → ZMod 2 := fun x => if e₀ x + x = 0 then 0 else 1
  have hφf : ∀ x, φf x • w₀ = e₀ x + x := by
    intro x
    simp only [φf]
    split_ifs with h
    · rw [zero_smul, h]
    · rw [one_smul]
      exact (hw₀ x).resolve_left h |>.symm
  have hφadd : ∀ x y, φf (x + y) = φf x + φf y := by
    intro x y
    have h1 : φf (x + y) • w₀ = φf x • w₀ + φf y • w₀ := by
      rw [hφf, hφf, hφf, map_add]
      abel
    have h2 : (φf (x + y) + (φf x + φf y)) • w₀ = 0 := by
      rw [add_smul, add_smul, h1]
      calc φf x • w₀ + φf y • w₀ + (φf x • w₀ + φf y • w₀) =
          (φf x • w₀ + φf x • w₀) + (φf y • w₀ + φf y • w₀) := by abel
        _ = 0 := by rw [two_add_self, two_add_self, add_zero]
    rcases smul_eq_zero.1 h2 with h | h
    · exact (two_add_eq_iff.1 h).trans (zero_add _)
    · exact absurd h hw₀0
  let φ : Module.Dual (ZMod 2) W := AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' φf hφadd)
  have hφ : ∀ x, φ x = φf x := fun x => rfl
  have hφ0 : φ ≠ 0 := by
    intro h
    apply h₀1
    apply LinearEquiv.ext
    intro x
    have := hφf x
    rw [← hφ, h, LinearMap.zero_apply, zero_smul] at this
    exact (two_add_eq_iff.1 this.symm).trans (zero_add x)
  refine ⟨φ, hφ0, ?_⟩
  intro e he he1
  obtain ⟨w, hw0, hw⟩ := hrank e he he1
  have hex : ∀ x, e x + x = φ x • w := by
    intro x
    rcases zmod_two_eq_zero_or_one (φ x) with h | h
    · have h0 : e₀ x = x := by
        have h' : e₀ x + x = 0 := by
          have := hφf x
          rw [← hφ, h, zero_smul] at this
          exact this.symm
        exact (two_add_eq_iff.1 h').trans (zero_add x)
      have h1 : e x = x := (haxis e₀ he₀ h₀1 e he he1 x).1 h0
      rw [h, zero_smul, h1]
      exact two_add_self x
    · have h0 : e₀ x ≠ x := by
        intro h0
        have h' : e₀ x + x = 0 := by rw [h0]; exact two_add_self x
        have := hφf x
        rw [← hφ, h, one_smul, h'] at this
        exact hw₀0 this
      have h1 : e x ≠ x := fun h1 => h0 ((haxis e₀ he₀ h₀1 e he he1 x).2 h1)
      rw [h, one_smul]
      refine (hw x).resolve_left ?_
      intro h'
      exact h1 ((two_add_eq_iff.1 h').trans (zero_add x))
  have hφw : φ w = 0 := by
    by_contra hne
    have h1 : φ w = 1 := zmod_two_eq_one_of_ne_zero hne
    have h2 := hex w
    rw [h1, one_smul] at h2
    have h3 : e w = 0 := by
      have := two_add_eq_iff.1 h2
      rw [this, two_add_self]
    exact hw0 (e.injective (by rw [h3, map_zero]))
  refine ⟨w, hφw, ?_⟩
  apply LinearEquiv.ext
  intro x
  rw [burnsideB49_tv_apply]
  have h4 := hex x
  rw [two_add_eq_iff] at h4
  rw [h4, add_comm]

end TransData

section QuotRange

variable {V : Type} [CommGroup V] [Finite V] (U : Subgroup V)

theorem burnsideB49_card_range (R : Subgroup V) (hUR : U ≤ R) :
    Nat.card ↥R = Nat.card ((QuotientGroup.mk' U).comp R.subtype).range * Nat.card ↥U := by
  set φR : ↥R →* V ⧸ U := (QuotientGroup.mk' U).comp R.subtype with hφR
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φR.ker
  have h2 : Nat.card (↥R ⧸ φR.ker) = Nat.card φR.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φR).toEquiv
  have h3 : φR.ker = U.subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    simp only [hφR, MonoidHom.comp_apply, Subgroup.subtype_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff _
  have h4 : Nat.card ↥(U.subgroupOf R) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUR).toEquiv
  rw [h1, h2, h3, h4]

end QuotRange

section RankOne

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)

theorem burnsideB49_rank_one (g : ↥G)
    (hT : Nat.card ↥(commV (Subgroup.zpowers (g : MulAut V)) ⊔ U) = Nat.card ↥U * 2 ^ 1) :
    ∃ w : burnsideB49_W hV U, w ≠ 0 ∧ ∀ x : burnsideB49_W hV U,
      burnsideB49_iota hV U G hG g x + x = 0 ∨ burnsideB49_iota hV U G hG g x + x = w := by
  set R : Subgroup V := commV (Subgroup.zpowers (g : MulAut V)) ⊔ U with hR
  have hUR : U ≤ R := le_sup_right
  have hc := burnsideB49_card_range U R hUR
  set S' := ((QuotientGroup.mk' U).comp R.subtype).range with hS'
  have hUpos : 0 < Nat.card ↥U := Nat.card_pos
  have hS2 : Nat.card S' = 2 := by
    rw [hT] at hc
    have : Nat.card ↥U * 2 ^ 1 = Nat.card ↥U * Nat.card S' := by rw [hc, mul_comm]
    have h2 := Nat.eq_of_mul_eq_mul_left hUpos this
    omega
  obtain ⟨s, hs1, hsu⟩ := (Nat.card_eq_two_iff' (1 : S')).1 hS2
  refine ⟨F2Vec.ofV (burnsideB49_hW hV U) (s : V ⧸ U), ?_, fun x => ?_⟩
  · intro h
    apply hs1
    apply Subtype.ext
    exact h
  · obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (F2Vec.toV (burnsideB49_hW hV U) x)
    have hx : x = F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v) := by
      rw [hv, F2Vec.ofV_toV]
    subst hx
    have hmem : (g : MulAut V) v * v⁻¹ ∈ R :=
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(g : MulAut V), Subgroup.mem_zpowers _, v, rfl⟩)
    have htS : (QuotientGroup.mk ((g : MulAut V) v * v⁻¹) : V ⧸ U) ∈ S' :=
      ⟨⟨(g : MulAut V) v * v⁻¹, hmem⟩, rfl⟩
    have hsum : burnsideB49_iota hV U G hG g (F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v)) +
        F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v) =
        F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk ((g : MulAut V) v * v⁻¹)) := by
      have h1 : burnsideB49_iota hV U G hG g
          (F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v)) =
          F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk ((g : MulAut V) v)) := by
        change F2Vec.ofV _ (burnsideB49_quotAut U G hG g (QuotientGroup.mk v)) = _
        rw [burnsideB49_quotAut_mk]
      rw [h1, ← F2Vec.ofV_mul, ← QuotientGroup.mk_mul]
      congr 2
      have : v⁻¹ = v := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two]
        exact hV v
      rw [this]
    rw [hsum]
    by_cases h1 : (QuotientGroup.mk ((g : MulAut V) v * v⁻¹) : V ⧸ U) = 1
    · left
      rw [h1]
      rfl
    · right
      congr 1
      have := hsu ⟨_, htS⟩ (fun h => h1 (congrArg Subtype.val h))
      exact congrArg Subtype.val this

end RankOne

section Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)

@[expose] noncomputable def burnsideB49_rho
    (hb : Function.Bijective (burnsideB49_iota hV U G hG)) :
    (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) →*
      (F2Vec V hV ≃ₗ[ZMod 2] F2Vec V hV) :=
  (burnsideB49_autLin hV).toMonoidHom.comp
    (G.subtype.comp (MulEquiv.ofBijective (burnsideB49_iota hV U G hG) hb).symm.toMonoidHom)

theorem burnsideB49_rho_iota (hb : Function.Bijective (burnsideB49_iota hV U G hG)) (g : ↥G) :
    burnsideB49_rho hV U G hG hb (burnsideB49_iota hV U G hG g) =
      burnsideB49_autLin hV (g : MulAut V) := by
  have : (MulEquiv.ofBijective (burnsideB49_iota hV U G hG) hb).symm
      (burnsideB49_iota hV U G hG g) = g := by
    have := (MulEquiv.ofBijective (burnsideB49_iota hV U G hG) hb).symm_apply_apply g
    exact this
  simp only [burnsideB49_rho, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.subtype_apply]
  rw [this]

theorem burnsideB49_q_rho (hb : Function.Bijective (burnsideB49_iota hV U G hG))
    (g' : burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) (x : F2Vec V hV) :
    burnsideB49_q hV U (burnsideB49_rho hV U G hG hb g' x) = g' (burnsideB49_q hV U x) := by
  obtain ⟨g, rfl⟩ := hb.2 g'
  rw [burnsideB49_rho_iota]
  exact burnsideB49_q_equiv hV U G hG g x

theorem burnsideB49_iota_fix_iff (g : ↥G) (v : V) :
    burnsideB49_iota hV U G hG g (F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v)) =
        F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v) ↔
      v ∈ CFSG.ASVolI.ChB.axisPre U (g : MulAut V) := by
  have h1 : burnsideB49_iota hV U G hG g (F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v)) =
      F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk ((g : MulAut V) v)) := by
    change F2Vec.ofV _ (burnsideB49_quotAut U G hG g (QuotientGroup.mk v)) = _
    rw [burnsideB49_quotAut_mk]
  rw [h1]
  constructor
  · intro h
    have h2 : (QuotientGroup.mk ((g : MulAut V) v) : V ⧸ U) = QuotientGroup.mk v := h
    rw [QuotientGroup.eq] at h2
    have := U.inv_mem h2
    rw [mul_inv_rev, inv_inv, mul_comm] at this
    exact this
  · intro h
    show (QuotientGroup.mk ((g : MulAut V) v) : V ⧸ U) = QuotientGroup.mk v
    rw [QuotientGroup.eq]
    have := U.inv_mem h
    rw [mul_inv, inv_inv] at this
    exact this

theorem burnsideB49_toV_sub (a b : F2Vec V hV) :
    F2Vec.toV hV (a - b) = F2Vec.toV hV a * (F2Vec.toV hV b)⁻¹ := by
  rw [← div_eq_mul_inv]
  rfl

variable {n : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL n K) →* ↥G}

theorem burnsideB49_E_data (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    (E : Subgroup (MulAut V)) (hE : CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U 1 E)
    (hq : CFSG.Quasithin.IsQuadratic E) :
    ∃ (E' : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U)),
      Nat.card E' = 4 ∧ ∃ φ : Module.Dual (ZMod 2) (burnsideB49_W hV U), φ ≠ 0 ∧
        (∀ e ∈ E', e ≠ 1 → ∃ (w : burnsideB49_W hV U) (h : φ w = 0), e = burnsideB49_tv φ w h) ∧
        (∀ e ∈ E', ∀ e' ∈ E', ∀ v : F2Vec V hV,
          burnsideB49_rho hV U G (burnsideB49_hG hreal) (burnsideB49_iota_bijective hV hK hreal hquot) e
            (burnsideB49_rho hV U G (burnsideB49_hG hreal)
              (burnsideB49_iota_bijective hV hK hreal hquot) e' v - v) =
          burnsideB49_rho hV U G (burnsideB49_hG hreal)
              (burnsideB49_iota_bijective hV hK hreal hquot) e' v - v) := by
  set hG := burnsideB49_hG hreal with hGdef
  set hb := burnsideB49_iota_bijective hV hK hreal hquot with hbdef
  obtain ⟨hEG, hE4, hTr, H, hH⟩ := hE
  set ι := burnsideB49_iota hV U G hG with hι
  let E' : Subgroup (burnsideB49_W hV U ≃ₗ[ZMod 2] burnsideB49_W hV U) := (E.subgroupOf G).map ι
  have hcard : Nat.card E' = 4 := by
    rw [Subgroup.card_map_of_injective hb.1, ← hE4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEG).toEquiv
  have hmem : ∀ e ∈ E', ∃ g : ↥G, (g : MulAut V) ∈ E ∧ ι g = e := by
    rintro e ⟨g, hg, rfl⟩
    exact ⟨g, hg, rfl⟩
  have hne : ∀ g : ↥G, ι g ≠ 1 → g ≠ 1 := fun g h h' => h (by rw [h', map_one])
  have hne' : ∀ g : ↥G, g ≠ 1 → (g : MulAut V) ≠ 1 := fun g h h' => h (Subtype.ext h')
  have hrank : ∀ e ∈ E', e ≠ 1 → ∃ w : burnsideB49_W hV U, w ≠ 0 ∧
      ∀ x, e x + x = 0 ∨ e x + x = w := by
    intro e he he1
    obtain ⟨g, hgE, rfl⟩ := hmem e he
    exact burnsideB49_rank_one hV U G hG g (hTr _ hgE (hne' g (hne g he1)))
  have haxis : ∀ e ∈ E', e ≠ 1 → ∀ e' ∈ E', e' ≠ 1 → ∀ x, e x = x ↔ e' x = x := by
    intro e he he1 e' he' he1' x
    obtain ⟨g, hgE, rfl⟩ := hmem e he
    obtain ⟨g', hgE', rfl⟩ := hmem e' he'
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (F2Vec.toV (burnsideB49_hW hV U) x)
    have hx : x = F2Vec.ofV (burnsideB49_hW hV U) (QuotientGroup.mk v) := by
      rw [hv, F2Vec.ofV_toV]
    subst hx
    rw [burnsideB49_iota_fix_iff, burnsideB49_iota_fix_iff,
      hH _ hgE (hne' g (hne g he1)), hH _ hgE' (hne' g' (hne g' he1'))]
  obtain ⟨φ, hφ0, hφ⟩ := burnsideB49_transvection_data E' hcard hrank haxis
  refine ⟨E', hcard, φ, hφ0, hφ, ?_⟩
  intro e he e' he' v
  obtain ⟨g, hgE, rfl⟩ := hmem e he
  obtain ⟨g', hgE', rfl⟩ := hmem e' he'
  rw [burnsideB49_rho_iota, burnsideB49_rho_iota]
  have hcomm : ((g' : MulAut V) (F2Vec.toV hV v) * (F2Vec.toV hV v)⁻¹) ∈ CFSG.Quasithin.commV E :=
    Subgroup.subset_closure ⟨(g' : MulAut V), hgE', F2Vec.toV hV v, rfl⟩
  have hfix : (g : MulAut V) ((g' : MulAut V) (F2Vec.toV hV v) * (F2Vec.toV hV v)⁻¹) =
      (g' : MulAut V) (F2Vec.toV hV v) * (F2Vec.toV hV v)⁻¹ :=
    (CFSG.Quasithin.mem_fixV.1 (hq hcomm)) (g : MulAut V) hgE
  have hsub : ∀ h : MulAut V, F2Vec.toV hV (burnsideB49_autLin hV h v - v) =
      h (F2Vec.toV hV v) * (F2Vec.toV hV v)⁻¹ := fun h => by
    rw [burnsideB49_toV_sub]
    rfl
  apply Additive.toMul.injective
  change F2Vec.toV hV _ = F2Vec.toV hV _
  rw [burnsideB49_autLin_apply, F2Vec.toV_ofV, hsub]
  exact hfix

end Assembly

section Final

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V))

@[expose] def burnsideB49_subOfSub (U' : Submodule (ZMod 2) (F2Vec V hV)) : Subgroup V where
  carrier := {v | F2Vec.ofV hV v ∈ U'}
  one_mem' := U'.zero_mem
  mul_mem' := fun {a b} ha hb => by
    change F2Vec.ofV hV (a * b) ∈ U'
    rw [F2Vec.ofV_mul]
    exact U'.add_mem ha hb
  inv_mem' := fun {a} ha => by
    have : a⁻¹ = a := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two]
      exact hV a
    rw [this]
    exact ha

theorem burnsideB49_splits_of_complement (hG : ∀ g ∈ G, ∀ u ∈ U, g u ∈ U)
    (U' : Submodule (ZMod 2) (F2Vec V hV))
    (hinv : ∀ g : ↥G, ∀ x ∈ U', burnsideB49_autLin hV (g : MulAut V) x ∈ U')
    (hc : IsCompl (LinearMap.ker (burnsideB49_q hV U)) U') :
    CFSG.ASVolI.ChB.SplitsOver G U := by
  refine ⟨burnsideB49_subOfSub hV U', fun g hg u hu => ?_, ?_, ?_⟩
  · have := hinv ⟨g, hg⟩ (F2Vec.ofV hV u) hu
    exact this
  · rw [eq_bot_iff]
    intro v hv
    have h1 : F2Vec.ofV hV v ∈ LinearMap.ker (burnsideB49_q hV U) ⊓ U' :=
      ⟨(burnsideB49_mem_ker_q hV U _).2 (by rw [F2Vec.toV_ofV]; exact hv.1), hv.2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h1
    have : v = 1 := by
      have := congrArg (F2Vec.toV hV) h1
      exact this
    rw [this]
    exact Subgroup.one_mem _
  · rw [eq_top_iff]
    intro v _
    have h1 : F2Vec.ofV hV v ∈ LinearMap.ker (burnsideB49_q hV U) ⊔ U' := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    have hv : v = F2Vec.toV hV a * F2Vec.toV hV b := by
      have := congrArg (F2Vec.toV hV) hab
      exact this.symm
    rw [hv]
    exact Subgroup.mul_mem_sup ((burnsideB49_mem_ker_q hV U a).1 ha) (by
      change F2Vec.ofV hV (F2Vec.toV hV b) ∈ U'
      exact hb)

variable {n : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL n K) →* ↥G}

include hV in
theorem burnsideB49_part1_big (hn : 5 ≤ n) (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    (E : Subgroup (MulAut V)) (hE : CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U 1 E)
    (hq : CFSG.Quasithin.IsQuadratic E) : CFSG.ASVolI.ChB.SplitsOver G U := by
  set hG := burnsideB49_hG hreal with hGdef
  set hb := burnsideB49_iota_bijective hV hK hreal hquot with hbdef
  obtain ⟨E', hE4, φ, hφ0, hEtr, hEquad⟩ := burnsideB49_E_data hV U G hK hreal hquot E hE hq
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hdim : 5 ≤ Module.finrank (ZMod 2) (burnsideB49_W hV U) := by
    rw [burnsideB49_finrank_W hV hK hreal hquot]
    exact hn
  have hqs := burnsideB49_q_surjective hV U
  have hqe := burnsideB49_q_rho hV U G hG hb
  obtain ⟨U', hinv', hc⟩ : ∃ U' : Submodule (ZMod 2) (F2Vec V hV),
      (∀ g : ↥G, ∀ x ∈ U', burnsideB49_autLin hV (g : MulAut V) x ∈ U') ∧
        IsCompl (LinearMap.ker (burnsideB49_q hV U)) U' := by
    rcases hquot with ⟨φ_, hφ_⟩ | ⟨φ_, hφ_⟩
    · obtain ⟨U', hinv, hc⟩ := burnsideB49_core_nat (burnsideB49_rho hV U G hG hb)
        (burnsideB49_q hV U) hqs hqe hdim (burnsideB49_thetaNat hV U φ_)
        (fun g' w => by
          obtain ⟨g, rfl⟩ := hb.2 g'
          rw [burnsideB49_rho_iota]
          exact burnsideB49_thetaNat_equiv hV U G hG φ_ hφ_ g w)
        E' hE4 hφ0 hEtr hEquad
      exact ⟨U', fun g x hx => by
        have := hinv (burnsideB49_iota hV U G hG g) x hx
        rwa [burnsideB49_rho_iota] at this, hc⟩
    · obtain ⟨U', hinv, hc⟩ := burnsideB49_core_dual (burnsideB49_rho hV U G hG hb)
        (burnsideB49_q hV U) hqs hqe hdim (burnsideB49_thetaDual hV U φ_)
        (fun g' w u u' h => by
          obtain ⟨g, rfl⟩ := hb.2 g'
          rw [burnsideB49_rho_iota] at h
          exact burnsideB49_thetaDual_equiv hV U G hG φ_ hφ_ g w u u' h)
        E' hE4 hφ0 hEtr hEquad
      exact ⟨U', fun g x hx => by
        have := hinv (burnsideB49_iota hV U G hG g) x hx
        rwa [burnsideB49_rho_iota] at this, hc⟩
  exact burnsideB49_splits_of_complement hV U G hG U' hinv' hc

end Final

section PFix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_quad_form [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) {φ φ' : Module.Dual (ZMod 2) W}
    (hφ : φ ≠ 0) (hφ' : φ' ≠ 0)
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v)
    (w w' : W) (h : φ' w = 0) (h' : φ' w' = 0) (v : V) :
    ρ (burnsideB49_tv φ' w h) (ρ (burnsideB49_tv φ' w' h') v - v) =
      ρ (burnsideB49_tv φ' w' h') v - v := by
  obtain ⟨g, -, hg⟩ := exists_comp_eq_of_apply_eq_zero (e₀ := (0 : W)) hφ hφ' (map_zero φ)
    (map_zero φ')
  have hgx : ∀ x, φ (g x) = φ' x := fun x => by
    have := congrArg (fun f : Module.Dual (ZMod 2) W => f x) hg
    simpa using this
  have hconj : ∀ (u : W) (hu : φ' u = 0) (hu' : φ (g u) = 0),
      burnsideB49_tv φ' u hu = g⁻¹ * burnsideB49_tv φ (g u) hu' * g := by
    intro u hu hu'
    apply LinearEquiv.ext
    intro x
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, burnsideB49_tv_apply, burnsideB49_tv_apply]
    have : g⁻¹ (g x + φ (g x) • g u) = x + φ' x • u := by
      rw [← map_smul, ← map_add]
      change g.symm (g (x + φ (g x) • u)) = _
      rw [LinearEquiv.symm_apply_apply, hgx]
    exact this.symm
  have hu : φ (g w) = 0 := by rw [hgx, h]
  have hu' : φ (g w') = 0 := by rw [hgx, h']
  have h1 : ∀ x : V, ρ g⁻¹ (ρ g x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
  have h2 : ∀ x : V, ρ g (ρ g⁻¹ x) = x := fun x => by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  rw [hconj w h hu, hconj w' h' hu']
  set v₀ := ρ g v with hv₀
  have hA : ρ (g⁻¹ * burnsideB49_tv φ (g w') hu' * g) v =
      ρ g⁻¹ (ρ (burnsideB49_tv φ (g w') hu') v₀) := by
    simp only [map_mul, LinearEquiv.mul_apply, hv₀]
  have hv : v = ρ g⁻¹ v₀ := (h1 v).symm
  have hB : ρ (g⁻¹ * burnsideB49_tv φ (g w') hu' * g) v - v =
      ρ g⁻¹ (ρ (burnsideB49_tv φ (g w') hu') v₀ - v₀) := by
    rw [hA, map_sub, ← hv]
  rw [hB]
  have hC : ρ (g⁻¹ * burnsideB49_tv φ (g w) hu * g) (ρ g⁻¹ (ρ (burnsideB49_tv φ (g w') hu') v₀ - v₀)) =
      ρ g⁻¹ (ρ (burnsideB49_tv φ (g w) hu) (ρ (burnsideB49_tv φ (g w') hu') v₀ - v₀)) := by
    simp only [map_mul, LinearEquiv.mul_apply]
    rw [h2]
  rw [hC, hQ (g w) (g w') hu hu' v₀]

theorem burnsideB49_Pfix [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ φ' : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0) (hφ' : φ' ≠ 0)
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v)
    {w₀ : W} (hw₀ : φ' w₀ = 0) :
    ∃ x₁ : V, q x₁ = w₀ ∧ ∀ (w : W) (h : φ' w = 0), ρ (burnsideB49_tv φ' w h) x₁ = x₁ := by
  obtain ⟨u₁, hu₁⟩ := burnsideB49_exists_one hφ'
  obtain ⟨y, hy⟩ := hqs u₁
  refine ⟨ρ (burnsideB49_tv φ' w₀ hw₀) y - y, ?_, fun w h => ?_⟩
  · rw [map_sub, hq, hy, burnsideB49_tv_apply, hu₁, one_smul]
    abel
  · exact burnsideB49_quad_form ρ hφ hφ' hQ w w₀ h hw₀ y

theorem burnsideB49_card_GL_two : Nat.card (GL (Fin 2) (ZMod 2)) = 6 := by
  rw [Matrix.card_GL_field, ZMod.card]
  simp [Fin.prod_univ_two]

theorem burnsideB49_card_K_two [FiniteDimensional (ZMod 2) W] {φ : Module.Dual (ZMod 2) W}
    {w₀ : W} (hw₀ : φ w₀ = 1) (hdim : Module.finrank (ZMod 2) ↥(LinearMap.ker φ) = 2) :
    Nat.card ↥(burnsideB49_K φ w₀) = 6 := by
  have hbij : Function.Bijective (burnsideB49_Kres φ w₀) :=
    ⟨burnsideB49_Kres_injective φ hw₀, burnsideB49_Kres_surjective φ hw₀⟩
  rw [Nat.card_congr (MulEquiv.ofBijective _ hbij).toEquiv]
  rw [card_linearEquiv_eq hdim, burnsideB49_card_GL_two]

theorem burnsideB49_exists_form_vec {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E] (h2 : 2 ≤ Module.finrank (ZMod 2) E) :
    ∃ (μ : Module.Dual (ZMod 2) E) (w : E), μ ≠ 0 ∧ w ≠ 0 ∧ μ w = 0 := by
  obtain ⟨y, hy⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < Module.finrank (ZMod 2) E)
  obtain ⟨μ, hμ, hμy⟩ := exists_dual_eq_one_of_notMem (S := ⊥) (w := y)
    (by rw [Submodule.mem_bot]; exact hy)
  have hker := burnsideB49_finrank_ker μ hμy
  obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.1
    (by omega : 0 < Module.finrank (ZMod 2) ↥(LinearMap.ker μ))
  refine ⟨μ, (x : E), ?_, fun h => hx (Subtype.ext h), LinearMap.mem_ker.1 x.2⟩
  intro h
  rw [h] at hμy
  simp at hμy

theorem burnsideB49_kfix_three [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0) {w₀ : W} (hw₀ : φ w₀ = 1)
    (hdim : Module.finrank (ZMod 2) W = 3)
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v) :
    ∃ v : V, q v = w₀ ∧ ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ρ k v = v := by
  have hker := burnsideB49_finrank_ker φ hw₀
  have hdI : Module.finrank (ZMod 2) ↥(LinearMap.ker φ) = 2 := by omega
  obtain ⟨μ, w₁', hμ, hw₁', hμw₁⟩ := burnsideB49_exists_form_vec (E := ↥(LinearMap.ker φ)) (by omega)
  set φ' : Module.Dual (ZMod 2) W := μ ∘ₗ burnsideB49_proj φ hw₀ with hφ'
  have hφ'x : ∀ x, φ' x = μ (burnsideB49_proj φ hw₀ x) := fun x => rfl
  have hproj_w₀ : burnsideB49_proj φ hw₀ w₀ = 0 := by
    apply Subtype.ext
    rw [burnsideB49_proj_apply, hw₀, one_smul]
    exact two_add_self w₀
  have hproj_ker : ∀ y : ↥(LinearMap.ker φ), burnsideB49_proj φ hw₀ (y : W) = y := by
    intro y
    apply Subtype.ext
    rw [burnsideB49_proj_apply, LinearMap.mem_ker.1 y.2, zero_smul, add_zero]
  have hφ'w₀ : φ' w₀ = 0 := by rw [hφ'x, hproj_w₀, map_zero]
  have hφ'0 : φ' ≠ 0 := by
    intro h
    apply hμ
    apply LinearMap.ext
    intro y
    have := congrArg (fun f : Module.Dual (ZMod 2) W => f (y : W)) h
    simp only [hφ'x, hproj_ker, LinearMap.zero_apply] at this
    exact this
  set w₁ : W := (w₁' : W) with hw₁
  have hφw₁ : φ w₁ = 0 := LinearMap.mem_ker.1 w₁'.2
  have hφ'w₁ : φ' w₁ = 0 := by rw [hφ'x, hw₁, hproj_ker]; exact hμw₁
  have hw₁0 : w₁ ≠ 0 := fun h => hw₁' (Subtype.ext h)
  set a := burnsideB49_tv φ' w₁ hφ'w₁ with ha
  have haK : a ∈ burnsideB49_K φ w₀ :=
    ⟨fun x => by rw [ha, burnsideB49_tv_apply, map_add, map_smul, hφw₁, smul_zero, add_zero],
      by rw [ha, burnsideB49_tv_apply, hφ'w₀, zero_smul, add_zero]⟩
  obtain ⟨y₀, hy₀⟩ := burnsideB49_exists_one hφ'0
  have ha1 : a ≠ 1 := by
    intro h
    have := congrArg (fun T : W ≃ₗ[ZMod 2] W => T y₀) h
    simp only [ha, burnsideB49_tv_apply, hy₀, one_smul] at this
    change y₀ + w₁ = y₀ at this
    exact hw₁0 (by simpa using this)
  have ha2 : a * a = 1 := burnsideB49_tv_mul_self hφ'w₁
  obtain ⟨x₁, hx₁q, hx₁⟩ := burnsideB49_Pfix ρ q hqs hq hφ hφ'0 hQ hφ'w₀
  let aK : ↥(burnsideB49_K φ w₀) := ⟨a, haK⟩
  have haK2 : aK ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two]
    exact ha2
  have haK1 : aK ≠ 1 := fun h => ha1 (congrArg Subtype.val h)
  let P : Subgroup ↥(burnsideB49_K φ w₀) := Subgroup.zpowers aK
  have hPcard : Nat.card ↥P = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime haK2 haK1
  have hKcard := burnsideB49_card_K_two hw₀ hdI
  have hPindex : P.index = 3 := by
    have := Subgroup.card_mul_index P
    rw [hPcard, hKcard] at this
    omega
  let ρK : ↥(burnsideB49_K φ w₀) →* (V ≃ₗ[ZMod 2] V) := ρ.comp (burnsideB49_K φ w₀).subtype
  let Fix : Subgroup ↥(burnsideB49_K φ w₀) :=
    { carrier := {γ | ρK γ x₁ = x₁}
      mul_mem' := fun {a b} ha hb => by
        change ρK (a * b) x₁ = x₁
        rw [map_mul, LinearEquiv.mul_apply, hb, ha]
      one_mem' := by
        change ρK 1 x₁ = x₁
        rw [map_one]; rfl
      inv_mem' := fun {a} ha => by
        change ρK a⁻¹ x₁ = x₁
        have : ρK a⁻¹ (ρK a x₁) = x₁ := by
          rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rw [ha] at this
        exact this }
  have haFix : aK ∈ Fix := hx₁ w₁ hφ'w₁
  have hPFix : P ≤ Fix := (Subgroup.zpowers_le).2 haFix
  obtain ⟨x, hxY, hxfix⟩ := burnsideB49_fixed_of_odd_index ρK (LinearMap.ker q) P
    (by rw [hPindex]; exact ⟨1, rfl⟩) x₁
    (fun γ => by
      rw [LinearMap.mem_ker, map_add]
      change q (ρ (γ : W ≃ₗ[ZMod 2] W) x₁) + q x₁ = 0
      rw [hq, hx₁q, γ.2.2]
      exact two_add_self w₀)
    (fun s hs => hPFix hs)
  refine ⟨x, ?_, fun k hk hkw => hxfix ⟨k, hk, hkw⟩⟩
  have := LinearMap.mem_ker.1 hxY
  rw [map_add, hx₁q] at this
  exact (two_add_eq_iff.1 this).trans (zero_add _)

theorem burnsideB49_core_three [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    (hdim : Module.finrank (ZMod 2) W = 3)
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) (hE4 : Nat.card E = 4)
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0)
    (hEtr : ∀ e ∈ E, e ≠ 1 → ∃ (w : W) (h : φ w = 0), e = burnsideB49_tv φ w h)
    (hEquad : ∀ e ∈ E, ∀ e' ∈ E, ∀ v : V, ρ e (ρ e' v - v) = ρ e' v - v) :
    ∃ U' : Submodule (ZMod 2) V, (∀ g, ∀ x ∈ U', ρ g x ∈ U') ∧
      IsCompl (LinearMap.ker q) U' := by
  obtain ⟨w₀, hw₀⟩ := burnsideB49_exists_one hφ
  have hQ := fun w w' h h' v => burnsideB49_Q_quadratic ρ E hE4 hEtr hEquad w w' h h' v
  obtain ⟨v, hvq, hv⟩ := burnsideB49_kfix_three ρ q hqs hq hφ hw₀ hdim hQ
  exact burnsideB49_complement_of_kfix ρ q hq hφ hw₀ hQ v hvq hv

end PFix

section FinalThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) {n : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL n K) →* ↥G}

include hV in
theorem burnsideB49_part1_three (hn : n = 3) (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    (E : Subgroup (MulAut V)) (hE : CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U 1 E)
    (hq : CFSG.Quasithin.IsQuadratic E) : CFSG.ASVolI.ChB.SplitsOver G U := by
  set hG := burnsideB49_hG hreal with hGdef
  set hb := burnsideB49_iota_bijective hV hK hreal hquot with hbdef
  obtain ⟨E', hE4, φ, hφ0, hEtr, hEquad⟩ := burnsideB49_E_data hV U G hK hreal hquot E hE hq
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) (burnsideB49_W hV U) = 3 := by
    rw [burnsideB49_finrank_W hV hK hreal hquot]
    exact hn
  have hqs := burnsideB49_q_surjective hV U
  have hqe := burnsideB49_q_rho hV U G hG hb
  obtain ⟨U', hinv, hc⟩ := burnsideB49_core_three (burnsideB49_rho hV U G hG hb)
    (burnsideB49_q hV U) hqs hqe hdim E' hE4 hφ0 hEtr hEquad
  refine burnsideB49_splits_of_complement hV U G hG U' (fun g x hx => ?_) hc
  have := hinv (burnsideB49_iota hV U G hG g) x hx
  rwa [burnsideB49_rho_iota] at this

end FinalThree

section FourIso

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] noncomputable def burnsideB49_toMat (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (T : E ≃ₗ[ZMod 2] E) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  LinearMap.toMatrix' (b.toLinearMap ∘ₗ T.toLinearMap ∘ₗ b.symm.toLinearMap)

theorem burnsideB49_toMat_mulVec (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (T : E ≃ₗ[ZMod 2] E) (y : E) :
    (burnsideB49_toMat b T).mulVec (b y) = b (T y) := by
  unfold burnsideB49_toMat
  rw [LinearMap.toMatrix'_mulVec]
  simp

theorem burnsideB49_toMat_mul (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (T T' : E ≃ₗ[ZMod 2] E) :
    burnsideB49_toMat b (T * T') = burnsideB49_toMat b T * burnsideB49_toMat b T' := by
  unfold burnsideB49_toMat
  rw [← LinearMap.toMatrix'_comp]
  congr 1
  apply LinearMap.ext
  intro x
  simp

theorem burnsideB49_toMat_one (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    burnsideB49_toMat b 1 = 1 := by
  unfold burnsideB49_toMat
  rw [← LinearMap.toMatrix'_id]
  congr 1
  apply LinearMap.ext
  intro x
  simp

theorem burnsideB49_toMat_det (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (T : E ≃ₗ[ZMod 2] E) :
    (burnsideB49_toMat b T).det = 1 := by
  have h : burnsideB49_toMat b T * burnsideB49_toMat b T⁻¹ = 1 := by
    rw [← burnsideB49_toMat_mul, mul_inv_cancel, burnsideB49_toMat_one]
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h2
  generalize (burnsideB49_toMat b T).det = a at h2
  generalize (burnsideB49_toMat b T⁻¹).det = c at h2
  revert a c
  decide

@[expose] noncomputable def burnsideB49_toSL (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    (E ≃ₗ[ZMod 2] E) →* (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) where
  toFun T := ⟨burnsideB49_toMat b T, burnsideB49_toMat_det b T⟩
  map_one' := Subtype.ext (burnsideB49_toMat_one b)
  map_mul' T T' := Subtype.ext (burnsideB49_toMat_mul b T T')

theorem burnsideB49_toSL_mulVec (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (T : E ≃ₗ[ZMod 2] E) (y : E) :
    ((burnsideB49_toSL b T : (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (b y) = b (T y) :=
  burnsideB49_toMat_mulVec b T y

theorem burnsideB49_toSL_injective (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    Function.Injective (burnsideB49_toSL b) := by
  rw [injective_iff_map_eq_one]
  intro T hT
  apply LinearEquiv.ext
  intro y
  have := burnsideB49_toSL_mulVec b T y
  rw [hT] at this
  have h1 : b (T y) = b y := by
    rw [← this]
    simp
  exact b.injective h1

theorem burnsideB49_toSL_surjective (b : E ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    Function.Surjective (burnsideB49_toSL b) := by
  intro γ
  let T : E ≃ₗ[ZMod 2] E := b.trans ((Matrix.SpecialLinearGroup.toLin' γ).trans b.symm)
  refine ⟨T, ?_⟩
  apply Subtype.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  change (burnsideB49_toMat b T).mulVec x = (γ : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec x
  have := burnsideB49_toMat_mulVec b T (b.symm x)
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]
  change b (b.symm ((Matrix.SpecialLinearGroup.toLin' γ) (b (b.symm x)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, Matrix.SpecialLinearGroup.toLin'_apply]
  exact Matrix.toLin'_apply _ _

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def burnsideB49_rhoU
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hq : ∀ g v, q (ρ g v) = g (q v)) :
    (W ≃ₗ[ZMod 2] W) →* AddMonoid.End ↥(LinearMap.ker q) where
  toFun g :=
    { toFun := fun u => ⟨ρ g (u : V), by
        rw [LinearMap.mem_ker, hq, LinearMap.mem_ker.1 u.2, map_zero]⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun u u' => by
        apply Subtype.ext
        simp }
  map_one' := by
    apply AddMonoidHom.ext
    intro u
    apply Subtype.ext
    show ρ 1 (u : V) = u
    rw [map_one]
    rfl
  map_mul' g h := by
    apply AddMonoidHom.ext
    intro u
    apply Subtype.ext
    show ρ (g * h) (u : V) = ρ g (ρ h (u : V))
    rw [map_mul]
    rfl

theorem burnsideB49_rhoU_apply (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hq : ∀ g v, q (ρ g v) = g (q v)) (g : W ≃ₗ[ZMod 2] W) (u : ↥(LinearMap.ker q)) :
    ((burnsideB49_rhoU ρ q hq g u : ↥(LinearMap.ker q)) : V) = ρ g (u : V) := rfl

@[expose] noncomputable def burnsideB49_KSL [FiniteDimensional (ZMod 2) W]
    {φ : Module.Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)
    (b : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) :
    ↥(burnsideB49_K φ w₀) ≃* (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  MulEquiv.ofBijective ((burnsideB49_toSL b).comp (burnsideB49_Kres φ w₀))
    ⟨(burnsideB49_toSL_injective b).comp (burnsideB49_Kres_injective φ hw₀),
      (burnsideB49_toSL_surjective b).comp (burnsideB49_Kres_surjective φ hw₀)⟩

theorem burnsideB49_KSL_mulVec [FiniteDimensional (ZMod 2) W]
    {φ : Module.Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)
    (b : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (k : ↥(burnsideB49_K φ w₀))
    (y : ↥(LinearMap.ker φ)) :
    ((burnsideB49_KSL hw₀ b k : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
      Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (b y) = b (burnsideB49_Kres φ w₀ k y) :=
  burnsideB49_toSL_mulVec b (burnsideB49_Kres φ w₀ k) y

end FourIso

section KFixFour

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin CFSG.Quasithin.JonesParshall

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_fourSetup [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0) {w₀ : W} (hw₀ : φ w₀ = 1)
    (hdI : 2 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker φ))
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v) :
    ∃ (a : W ≃ₗ[ZMod 2] W) (x₁ : V), a ∈ burnsideB49_K φ w₀ ∧ a ≠ 1 ∧ a * a = 1 ∧
      q x₁ = w₀ ∧ ρ a x₁ = x₁ := by
  obtain ⟨μ, w₁', hμ, hw₁', hμw₁⟩ := burnsideB49_exists_form_vec (E := ↥(LinearMap.ker φ)) hdI
  set φ' : Module.Dual (ZMod 2) W := μ ∘ₗ burnsideB49_proj φ hw₀ with hφ'
  have hφ'x : ∀ x, φ' x = μ (burnsideB49_proj φ hw₀ x) := fun x => rfl
  have hproj_w₀ : burnsideB49_proj φ hw₀ w₀ = 0 := by
    apply Subtype.ext
    rw [burnsideB49_proj_apply, hw₀, one_smul]
    exact two_add_self w₀
  have hproj_ker : ∀ y : ↥(LinearMap.ker φ), burnsideB49_proj φ hw₀ (y : W) = y := by
    intro y
    apply Subtype.ext
    rw [burnsideB49_proj_apply, LinearMap.mem_ker.1 y.2, zero_smul, add_zero]
  have hφ'w₀ : φ' w₀ = 0 := by rw [hφ'x, hproj_w₀, map_zero]
  have hφ'0 : φ' ≠ 0 := by
    intro h
    apply hμ
    apply LinearMap.ext
    intro y
    have := congrArg (fun f : Module.Dual (ZMod 2) W => f (y : W)) h
    simp only [hφ'x, hproj_ker, LinearMap.zero_apply] at this
    exact this
  set w₁ : W := (w₁' : W) with hw₁
  have hφw₁ : φ w₁ = 0 := LinearMap.mem_ker.1 w₁'.2
  have hφ'w₁ : φ' w₁ = 0 := by rw [hφ'x, hw₁, hproj_ker]; exact hμw₁
  have hw₁0 : w₁ ≠ 0 := fun h => hw₁' (Subtype.ext h)
  set a := burnsideB49_tv φ' w₁ hφ'w₁ with ha
  have haK : a ∈ burnsideB49_K φ w₀ :=
    ⟨fun x => by rw [ha, burnsideB49_tv_apply, map_add, map_smul, hφw₁, smul_zero, add_zero],
      by rw [ha, burnsideB49_tv_apply, hφ'w₀, zero_smul, add_zero]⟩
  obtain ⟨y₀, hy₀⟩ := burnsideB49_exists_one hφ'0
  have ha1 : a ≠ 1 := by
    intro h
    have := congrArg (fun T : W ≃ₗ[ZMod 2] W => T y₀) h
    simp only [ha, burnsideB49_tv_apply, hy₀, one_smul] at this
    change y₀ + w₁ = y₀ at this
    exact hw₁0 (by simpa using this)
  obtain ⟨x₁, hx₁q, hx₁⟩ := burnsideB49_Pfix ρ q hqs hq hφ hφ'0 hQ hφ'w₀
  exact ⟨a, x₁, haK, ha1, burnsideB49_tv_mul_self hφ'w₁, hx₁q, hx₁ w₁ hφ'w₁⟩

theorem burnsideB49_proj_ker {φ : Module.Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)
    (y : ↥(LinearMap.ker φ)) : burnsideB49_proj φ hw₀ (y : W) = y := by
  apply Subtype.ext
  rw [burnsideB49_proj_apply, LinearMap.mem_ker.1 y.2, zero_smul, add_zero]

theorem burnsideB49_proj_K [FiniteDimensional (ZMod 2) W] {φ : Module.Dual (ZMod 2) W} {w₀ : W}
    (hw₀ : φ w₀ = 1) (k : ↥(burnsideB49_K φ w₀)) (x : W) :
    burnsideB49_proj φ hw₀ ((k : W ≃ₗ[ZMod 2] W) x) =
      burnsideB49_Kres φ w₀ k (burnsideB49_proj φ hw₀ x) := by
  apply Subtype.ext
  rw [burnsideB49_proj_apply, burnsideB49_Kres_apply, burnsideB49_proj_apply, map_add, map_smul,
    k.2.2, k.2.1]

theorem burnsideB49_kfix_four_nat [FiniteDimensional (ZMod 2) W]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0) {w₀ : W} (hw₀ : φ w₀ = 1)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (θ : W ≃ₗ[ZMod 2] ↥(LinearMap.ker q))
    (hθ : ∀ g w, ((θ (g w) : ↥(LinearMap.ker q)) : V) = ρ g ((θ w : ↥(LinearMap.ker q)) : V))
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v) :
    ∃ v : V, q v = w₀ ∧ ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ρ k v = v := by
  have hker := burnsideB49_finrank_ker φ hw₀
  have hdI : Module.finrank (ZMod 2) ↥(LinearMap.ker φ) = 3 := by omega
  obtain ⟨a, x₁, haK, ha1, ha2, hx₁q, hax₁⟩ :=
    burnsideB49_fourSetup ρ q hqs hq hφ hw₀ (by omega) hQ
  let b : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) ↥(LinearMap.ker φ) hdI).equivFun
  let κ := burnsideB49_KSL hw₀ b
  let μU : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End ↥(LinearMap.ker q) :=
    (burnsideB49_rhoU ρ q hq).comp ((burnsideB49_K φ w₀).subtype.comp κ.symm.toMonoidHom)
  have hμU : ∀ γ u, ((μU γ u : ↥(LinearMap.ker q)) : V) =
      ρ ((κ.symm γ : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) (u : V) := fun γ u => rfl
  have hmem : ∀ γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      ρ ((κ.symm γ : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) x₁ + x₁ ∈ LinearMap.ker q := by
    intro γ
    rw [LinearMap.mem_ker, map_add, hq, hx₁q, (κ.symm γ).2.2]
    exact two_add_self w₀
  let f : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) → ↥(LinearMap.ker q) := fun γ =>
    ⟨ρ ((κ.symm γ : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) x₁ + x₁, hmem γ⟩
  have hf : f ∈ Z1A μU := by
    intro γ γ'
    apply Subtype.ext
    simp only [f, Submodule.coe_add, hμU, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, map_add]
    have h2 : x₁ + x₁ = 0 := two_add_self x₁
    calc ρ (κ.symm γ) (ρ (κ.symm γ') x₁) + x₁ =
        ρ (κ.symm γ) (ρ (κ.symm γ') x₁) + x₁ + (ρ (κ.symm γ) x₁ + ρ (κ.symm γ) x₁) := by
          rw [two_add_self, add_zero]
      _ = _ := by abel
  have hθs : ∀ (g : W ≃ₗ[ZMod 2] W) (u : ↥(LinearMap.ker q)),
      θ.symm ((burnsideB49_rhoU ρ q hq g) u) = g (θ.symm u) := by
    intro g u
    apply θ.injective
    apply Subtype.ext
    rw [LinearEquiv.apply_symm_apply]
    have := hθ g (θ.symm u)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  let qn : ↥(LinearMap.ker q) →+ (Fin 3 → ZMod 2) :=
    ((b : ↥(LinearMap.ker φ) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) ∘ₗ burnsideB49_proj φ hw₀ ∘ₗ
      (θ.symm : ↥(LinearMap.ker q) →ₗ[ZMod 2] W)).toAddMonoidHom
  have hqn : ∀ (_ : Unit) (γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (u : ↥(LinearMap.ker q)),
      qn (μU γ u) = muF2 3 γ (qn u) := by
    intro _ γ u
    set k : ↥(burnsideB49_K φ w₀) := κ.symm γ with hk
    have hγ : κ k = γ := by rw [hk, MulEquiv.apply_symm_apply]
    have h1 : θ.symm (μU γ u) = (k : W ≃ₗ[ZMod 2] W) (θ.symm u) := hθs _ u
    change b (burnsideB49_proj φ hw₀ (θ.symm (μU γ u))) = (γ : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec
      (b (burnsideB49_proj φ hw₀ (θ.symm u)))
    rw [h1, burnsideB49_proj_K hw₀ k, ← hγ, burnsideB49_KSL_mulVec hw₀ b k]
  have hsurj : ∀ n : Unit → (Fin 3 → ZMod 2), ∃ m : ↥(LinearMap.ker q), ∀ i : Unit, qn m = n i := by
    intro n
    refine ⟨θ ((b.symm (n ()) : ↥(LinearMap.ker φ)) : W), fun _ => ?_⟩
    change b (burnsideB49_proj φ hw₀ (θ.symm (θ ((b.symm (n ()) : ↥(LinearMap.ker φ)) : W)))) = n ()
    rw [LinearEquiv.symm_apply_apply, burnsideB49_proj_ker, LinearEquiv.apply_symm_apply]
  have hker' : ∀ u : ↥(LinearMap.ker q), (∀ _ : Unit, qn u = 0) →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), μU γ u = u := by
    intro u hu γ
    set k : ↥(burnsideB49_K φ w₀) := κ.symm γ with hk
    have hu0 : b (burnsideB49_proj φ hw₀ (θ.symm u)) = 0 := hu ()
    have hproj0 : burnsideB49_proj φ hw₀ (θ.symm u) = 0 := by
      have := congrArg b.symm hu0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at this
    set x := θ.symm u with hx
    have hxw : x = φ x • w₀ := by
      have h1 : ((burnsideB49_proj φ hw₀ x : ↥(LinearMap.ker φ)) : W) = 0 := by
        rw [hproj0]; rfl
      rw [burnsideB49_proj_apply] at h1
      have h2 := two_add_eq_iff.1 h1
      rw [zero_add] at h2
      exact h2
    have hkx : (k : W ≃ₗ[ZMod 2] W) x = x := by
      conv_lhs => rw [hxw]
      rw [map_smul, k.2.2]
      exact hxw.symm
    apply θ.symm.injective
    have h1 : θ.symm (μU γ u) = (k : W ≃ₗ[ZMod 2] W) (θ.symm u) := hθs _ u
    rw [h1]
    exact hkx
  let aK : ↥(burnsideB49_K φ w₀) := ⟨a, haK⟩
  have haS2 : κ aK * κ aK = 1 := by
    rw [← map_mul]
    have : aK * aK = 1 := Subtype.ext ha2
    rw [this, map_one]
  have haS1 : κ aK ≠ 1 := by
    intro h
    apply ha1
    have := κ.injective (h.trans (map_one κ).symm)
    exact congrArg Subtype.val this
  have h0 : f (κ aK) = μU (κ aK) 0 - 0 := by
    apply Subtype.ext
    simp only [f, Submodule.coe_add, MulEquiv.symm_apply_apply, map_zero, sub_zero]
    change ρ a x₁ + x₁ = 0
    rw [hax₁]
    exact two_add_self x₁
  have hB := FFC.mem_B1A_of_quot (μ := μU) (q := fun _ : Unit => qn) hqn hsurj hker' haS2 haS1 hf h0
  obtain ⟨m, hm⟩ := hB
  refine ⟨x₁ + (m : V), ?_, fun k hk hkw => ?_⟩
  · rw [map_add, hx₁q, LinearMap.mem_ker.1 m.2, add_zero]
  · set kK : ↥(burnsideB49_K φ w₀) := ⟨k, hk, hkw⟩ with hkK
    have h1 := congrFun hm (κ kK)
    simp only [coboundaryA_apply, f, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Submodule.coe_sub, hμU, MulEquiv.symm_apply_apply] at h2
    rw [map_add]
    have h3 : ρ k (m : V) = ρ k x₁ + x₁ + (m : V) := by
      change ρ ((kK : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) (m : V) - (m : V) = _ at h2
      rw [sub_eq_iff_eq_add] at h2
      exact h2
    rw [h3]
    calc ρ k x₁ + (ρ k x₁ + x₁ + (m : V)) = (ρ k x₁ + ρ k x₁) + x₁ + (m : V) := by abel
      _ = x₁ + (m : V) := by rw [two_add_self, zero_add]

theorem burnsideB49_expand {φ : Module.Dual (ZMod 2) W}
    (b : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) (ψ : Module.Dual (ZMod 2) W)
    (z : ↥(LinearMap.ker φ)) :
    ψ (z : W) = ∑ j : Fin 3, (b z) j * ψ ((b.symm (Pi.single j 1) : ↥(LinearMap.ker φ)) : W) := by
  have h0 : b z = ∑ j : Fin 3, (b z) j • (Pi.single j 1 : Fin 3 → ZMod 2) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : z = ∑ j : Fin 3, (b z) j • b.symm (Pi.single j 1) := by
    calc z = b.symm (b z) := (b.symm_apply_apply z).symm
      _ = b.symm (∑ j : Fin 3, (b z) j • (Pi.single j 1 : Fin 3 → ZMod 2)) := by rw [← h0]
      _ = _ := by rw [map_sum]; simp only [map_smul]
  conv_lhs => rw [h1]
  rw [Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Submodule.coe_smul, map_smul, smul_eq_mul]

theorem burnsideB49_kfix_four_dual [FiniteDimensional (ZMod 2) W]
    [Finite V]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0) {w₀ : W} (hw₀ : φ w₀ = 1)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (θ' : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ↥(LinearMap.ker q))
    (hθ' : ∀ g w (u u' : ↥(LinearMap.ker q)), ρ g (u' : V) = (u : V) → θ' (g w) u = θ' w u')
    (hQ : ∀ (w w' : W) (h : φ w = 0) (h' : φ w' = 0) (v : V),
      ρ (burnsideB49_tv φ w h) (ρ (burnsideB49_tv φ w' h') v - v) =
        ρ (burnsideB49_tv φ w' h') v - v) :
    ∃ v : V, q v = w₀ ∧ ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ρ k v = v := by
  have hker := burnsideB49_finrank_ker φ hw₀
  have hdI : Module.finrank (ZMod 2) ↥(LinearMap.ker φ) = 3 := by omega
  obtain ⟨a, x₁, haK, ha1, ha2, hx₁q, hax₁⟩ :=
    burnsideB49_fourSetup ρ q hqs hq hφ hw₀ (by omega) hQ
  haveI : Finite ↥(LinearMap.ker q) := inferInstance
  haveI : FiniteDimensional (ZMod 2) ↥(LinearMap.ker q) := Module.Finite.of_finite
  let Θ : ↥(LinearMap.ker q) ≃ₗ[ZMod 2] Module.Dual (ZMod 2) W :=
    (Module.evalEquiv (ZMod 2) ↥(LinearMap.ker q)).trans θ'.dualMap
  have hΘ : ∀ u w, Θ u w = θ' w u := fun u w => rfl
  have hΘg : ∀ (g : W ≃ₗ[ZMod 2] W) (u u' : ↥(LinearMap.ker q)), ρ g (u : V) = (u' : V) →
      ∀ w, Θ u' w = Θ u (g.symm w) := by
    intro g u u' h w
    rw [hΘ, hΘ]
    have := hθ' g (g.symm w) u' u h
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  let b : ↥(LinearMap.ker φ) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) ↥(LinearMap.ker φ) hdI).equivFun
  let κt : ↥(burnsideB49_K φ w₀) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (burnsideB49_KSL hw₀ b).trans (invTransposeSL 3 (ZMod 2))
  let μU : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) →* AddMonoid.End ↥(LinearMap.ker q) :=
    (burnsideB49_rhoU ρ q hq).comp ((burnsideB49_K φ w₀).subtype.comp κt.symm.toMonoidHom)
  have hμU : ∀ γ u, ((μU γ u : ↥(LinearMap.ker q)) : V) =
      ρ ((κt.symm γ : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) (u : V) := fun γ u => rfl
  have hmem : ∀ γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      ρ ((κt.symm γ : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) x₁ + x₁ ∈ LinearMap.ker q := by
    intro γ
    rw [LinearMap.mem_ker, map_add, hq, hx₁q, (κt.symm γ).2.2]
    exact two_add_self w₀
  let f : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) → ↥(LinearMap.ker q) := fun γ =>
    ⟨ρ ((κt.symm γ : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) x₁ + x₁, hmem γ⟩
  have hf : f ∈ Z1A μU := by
    intro γ γ'
    apply Subtype.ext
    simp only [f, Submodule.coe_add, hμU, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply, map_add]
    calc ρ (κt.symm γ) (ρ (κt.symm γ') x₁) + x₁ =
        ρ (κt.symm γ) (ρ (κt.symm γ') x₁) + x₁ + (ρ (κt.symm γ) x₁ + ρ (κt.symm γ) x₁) := by
          rw [two_add_self, add_zero]
      _ = _ := by abel
  let yb : Fin 3 → W := fun i => ((b.symm (Pi.single i 1) : ↥(LinearMap.ker φ)) : W)
  let qd : ↥(LinearMap.ker q) →+ (Fin 3 → ZMod 2) :=
    AddMonoidHom.mk' (fun u i => Θ u (yb i)) (fun u u' => by
      funext i
      simp only [map_add, LinearMap.add_apply, Pi.add_apply])
  have hqd_apply : ∀ u i, qd u i = Θ u (yb i) := fun u i => rfl
  have hqd : ∀ (_ : Unit) (γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) (u : ↥(LinearMap.ker q)),
      qd (μU γ u) = muF2 3 γ (qd u) := by
    intro _ γ u
    set k : ↥(burnsideB49_K φ w₀) := κt.symm γ with hk
    have hγ : burnsideB49_KSL hw₀ b k = invTransposeSL 3 (ZMod 2) γ := by
      have : κt k = γ := by rw [hk, MulEquiv.apply_symm_apply]
      have h2 : invTransposeSL 3 (ZMod 2) (burnsideB49_KSL hw₀ b k) = γ := this
      rw [← h2]
      exact ((invTransposeSL 3 (ZMod 2)).symm_apply_apply _).symm
    funext i
    rw [hqd_apply]
    have hg := hΘg (k : W ≃ₗ[ZMod 2] W) u (μU γ u) (hμU γ u ▸ rfl) (yb i)
    rw [hg]
    have hky : (k : W ≃ₗ[ZMod 2] W).symm (yb i) =
        ((burnsideB49_Kres φ w₀ k⁻¹ (b.symm (Pi.single i 1)) : ↥(LinearMap.ker φ)) : W) := by
      rw [burnsideB49_Kres_apply]
      rfl
    rw [hky, burnsideB49_expand b (Θ u)]
    show _ = ((γ : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec (qd u)) i
    simp only [Matrix.mulVec, dotProduct, hqd_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcol : b (burnsideB49_Kres φ w₀ k⁻¹ (b.symm (Pi.single i 1))) j =
        (γ : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j := by
      have h1 := burnsideB49_KSL_mulVec hw₀ b k⁻¹ (b.symm (Pi.single i 1))
      rw [LinearEquiv.apply_symm_apply] at h1
      rw [← h1]
      have h2 : burnsideB49_KSL hw₀ b k⁻¹ = invTransposeSL 3 (ZMod 2) γ⁻¹ := by
        rw [map_inv, hγ, map_inv]
      rw [h2, invTransposeSL_coe, inv_inv]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hcol]
  have hsurj : ∀ n : Unit → (Fin 3 → ZMod 2), ∃ m : ↥(LinearMap.ker q), ∀ i : Unit, qd m = n i := by
    intro n
    let ψ : Module.Dual (ZMod 2) W :=
      (L3Dual.dotDual (n ())) ∘ₗ (b : ↥(LinearMap.ker φ) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) ∘ₗ
        burnsideB49_proj φ hw₀
    refine ⟨Θ.symm ψ, fun _ => ?_⟩
    funext i
    rw [hqd_apply, LinearEquiv.apply_symm_apply]
    change n () ⬝ᵥ b (burnsideB49_proj φ hw₀ ((b.symm (Pi.single i 1) : ↥(LinearMap.ker φ)) : W)) = n () i
    rw [burnsideB49_proj_ker, LinearEquiv.apply_symm_apply]
    simp [dotProduct_single]
  have hker' : ∀ u : ↥(LinearMap.ker q), (∀ _ : Unit, qd u = 0) →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), μU γ u = u := by
    intro u hu γ
    set k : ↥(burnsideB49_K φ w₀) := κt.symm γ with hk
    have hΘy : ∀ i, Θ u (yb i) = 0 := fun i => congrFun (hu ()) i
    have hΘker : ∀ z : ↥(LinearMap.ker φ), Θ u (z : W) = 0 := by
      intro z
      rw [burnsideB49_expand b (Θ u) z]
      exact Finset.sum_eq_zero fun j _ => by rw [hΘy j, mul_zero]
    have hΘx : ∀ x : W, Θ u x = φ x • Θ u w₀ := by
      intro x
      have hx : x = ((burnsideB49_proj φ hw₀ x : ↥(LinearMap.ker φ)) : W) + φ x • w₀ := by
        rw [burnsideB49_proj_apply]
        calc x = x + (φ x • w₀ + φ x • w₀) := by rw [two_add_self, add_zero]
          _ = _ := by abel
      conv_lhs => rw [hx]
      rw [map_add, hΘker, zero_add, map_smul]
    have hφk : ∀ x, φ ((k : W ≃ₗ[ZMod 2] W).symm x) = φ x := by
      intro x
      have := k.2.1 ((k : W ≃ₗ[ZMod 2] W).symm x)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    apply Θ.injective
    apply LinearMap.ext
    intro x
    have hg := hΘg (k : W ≃ₗ[ZMod 2] W) u (μU γ u) (hμU γ u ▸ rfl) x
    rw [hg, hΘx ((k : W ≃ₗ[ZMod 2] W).symm x), hΘx x, hφk]
  let aK : ↥(burnsideB49_K φ w₀) := ⟨a, haK⟩
  have haS2 : κt aK * κt aK = 1 := by
    rw [← map_mul]
    have : aK * aK = 1 := Subtype.ext ha2
    rw [this, map_one]
  have haS1 : κt aK ≠ 1 := by
    intro h
    apply ha1
    have := κt.injective (h.trans (map_one κt).symm)
    exact congrArg Subtype.val this
  have h0 : f (κt aK) = μU (κt aK) 0 - 0 := by
    apply Subtype.ext
    simp only [f, Submodule.coe_add, MulEquiv.symm_apply_apply, map_zero, sub_zero]
    change ρ a x₁ + x₁ = 0
    rw [hax₁]
    exact two_add_self x₁
  have hB := FFC.mem_B1A_of_quot (μ := μU) (q := fun _ : Unit => qd) hqd hsurj hker' haS2 haS1 hf h0
  obtain ⟨m, hm⟩ := hB
  refine ⟨x₁ + (m : V), ?_, fun k hk hkw => ?_⟩
  · rw [map_add, hx₁q, LinearMap.mem_ker.1 m.2, add_zero]
  · set kK : ↥(burnsideB49_K φ w₀) := ⟨k, hk, hkw⟩ with hkK
    have h1 := congrFun hm (κt kK)
    simp only [coboundaryA_apply, f, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Submodule.coe_sub, hμU, MulEquiv.symm_apply_apply] at h2
    rw [map_add]
    have h3 : ρ k (m : V) = ρ k x₁ + x₁ + (m : V) := by
      change ρ ((kK : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) (m : V) - (m : V) = _ at h2
      rw [sub_eq_iff_eq_add] at h2
      exact h2
    rw [h3]
    calc ρ k x₁ + (ρ k x₁ + x₁ + (m : V)) = (ρ k x₁ + ρ k x₁) + x₁ + (m : V) := by abel
      _ = x₁ + (m : V) := by rw [two_add_self, zero_add]

end KFixFour

section CoreF1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem burnsideB49_core_f1 [FiniteDimensional (ZMod 2) W]
    [Finite V]
    (ρ : (W ≃ₗ[ZMod 2] W) →* (V ≃ₗ[ZMod 2] V)) (q : V →ₗ[ZMod 2] W)
    (hqs : Function.Surjective q) (hq : ∀ g v, q (ρ g v) = g (q v))
    (hdim : 3 ≤ Module.finrank (ZMod 2) W)
    (hU : (∃ θ : W ≃ₗ[ZMod 2] ↥(LinearMap.ker q),
        ∀ g w, ((θ (g w) : ↥(LinearMap.ker q)) : V) = ρ g ((θ w : ↥(LinearMap.ker q)) : V)) ∨
      (∃ θ' : W ≃ₗ[ZMod 2] Module.Dual (ZMod 2) ↥(LinearMap.ker q),
        ∀ g w (u u' : ↥(LinearMap.ker q)), ρ g (u' : V) = (u : V) → θ' (g w) u = θ' w u'))
    (E : Subgroup (W ≃ₗ[ZMod 2] W)) (hE4 : Nat.card E = 4)
    {φ : Module.Dual (ZMod 2) W} (hφ : φ ≠ 0)
    (hEtr : ∀ e ∈ E, e ≠ 1 → ∃ (w : W) (h : φ w = 0), e = burnsideB49_tv φ w h)
    (hEquad : ∀ e ∈ E, ∀ e' ∈ E, ∀ v : V, ρ e (ρ e' v - v) = ρ e' v - v) :
    ∃ U' : Submodule (ZMod 2) V, (∀ g, ∀ x ∈ U', ρ g x ∈ U') ∧
      IsCompl (LinearMap.ker q) U' := by
  obtain ⟨w₀, hw₀⟩ := burnsideB49_exists_one hφ
  have hQ := fun w w' h h' v => burnsideB49_Q_quadratic ρ E hE4 hEtr hEquad w w' h h' v
  obtain ⟨v, hvq, hv⟩ : ∃ v : V, q v = w₀ ∧
      ∀ k : W ≃ₗ[ZMod 2] W, (∀ x, φ (k x) = φ x) → k w₀ = w₀ → ρ k v = v := by
    have hcases : Module.finrank (ZMod 2) W = 3 ∨ Module.finrank (ZMod 2) W = 4 ∨
        5 ≤ Module.finrank (ZMod 2) W := by omega
    rcases hcases with h3 | h4 | h5
    · exact burnsideB49_kfix_three ρ q hqs hq hφ hw₀ h3 hQ
    · rcases hU with ⟨θ, hθ⟩ | ⟨θ', hθ'⟩
      · exact burnsideB49_kfix_four_nat ρ q hqs hq hφ hw₀ h4 θ hθ hQ
      · exact burnsideB49_kfix_four_dual ρ q hqs hq hφ hw₀ h4 θ' hθ' hQ
    · rcases hU with ⟨θ, hθ⟩ | ⟨θ', hθ'⟩
      · exact burnsideB49_kfix_nat ρ q hqs hq hw₀ h5 θ hθ
      · exact burnsideB49_kfix_dual ρ q hqs hq hw₀ h5 θ' hθ'
  exact burnsideB49_complement_of_kfix ρ q hq hφ hw₀ hQ v hvq hv

end CoreF1

section FinalF1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (U : Subgroup V)
  (G : Subgroup (MulAut V)) {n : ℕ} {K : Type} [Field K] [Finite K] {π : ↥(StatedSL n K) →* ↥G}

include hV in
theorem burnsideB49_part1_f1 (hn : 3 ≤ n) (hK : Nat.card K = 2)
    (hreal : (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    (E : Subgroup (MulAut V)) (hE : CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U 1 E)
    (hq : CFSG.Quasithin.IsQuadratic E) : CFSG.ASVolI.ChB.SplitsOver G U := by
  set hG := burnsideB49_hG hreal with hGdef
  set hb := burnsideB49_iota_bijective hV hK hreal hquot with hbdef
  obtain ⟨E', hE4, φ, hφ0, hEtr, hEquad⟩ := burnsideB49_E_data hV U G hK hreal hquot E hE hq
  haveI : Finite (burnsideB49_W hV U) := inferInstance
  haveI : FiniteDimensional (ZMod 2) (burnsideB49_W hV U) := Module.Finite.of_finite
  have hdim : 3 ≤ Module.finrank (ZMod 2) (burnsideB49_W hV U) := by
    rw [burnsideB49_finrank_W hV hK hreal hquot]
    exact hn
  have hqs := burnsideB49_q_surjective hV U
  have hqe := burnsideB49_q_rho hV U G hG hb
  obtain ⟨U', hinv', hc⟩ : ∃ U' : Submodule (ZMod 2) (F2Vec V hV),
      (∀ g : ↥G, ∀ x ∈ U', burnsideB49_autLin hV (g : MulAut V) x ∈ U') ∧
        IsCompl (LinearMap.ker (burnsideB49_q hV U)) U' := by
    have hU : (∃ θ : burnsideB49_W hV U ≃ₗ[ZMod 2] ↥(LinearMap.ker (burnsideB49_q hV U)),
        ∀ g w, ((θ (g w) : ↥(LinearMap.ker (burnsideB49_q hV U))) : F2Vec V hV) =
          burnsideB49_rho hV U G hG hb g ((θ w : ↥(LinearMap.ker (burnsideB49_q hV U))) : F2Vec V hV)) ∨
        (∃ θ' : burnsideB49_W hV U ≃ₗ[ZMod 2]
            Module.Dual (ZMod 2) ↥(LinearMap.ker (burnsideB49_q hV U)),
          ∀ g w (u u' : ↥(LinearMap.ker (burnsideB49_q hV U))),
            burnsideB49_rho hV U G hG hb g (u' : F2Vec V hV) = (u : F2Vec V hV) →
              θ' (g w) u = θ' w u') := by
      rcases hquot with ⟨φ_, hφ_⟩ | ⟨φ_, hφ_⟩
      · refine Or.inl ⟨burnsideB49_thetaNat hV U φ_, fun g' w => ?_⟩
        obtain ⟨g, rfl⟩ := hb.2 g'
        rw [burnsideB49_rho_iota]
        exact burnsideB49_thetaNat_equiv hV U G hG φ_ hφ_ g w
      · refine Or.inr ⟨burnsideB49_thetaDual hV U φ_, fun g' w u u' h => ?_⟩
        obtain ⟨g, rfl⟩ := hb.2 g'
        rw [burnsideB49_rho_iota] at h
        exact burnsideB49_thetaDual_equiv hV U G hG φ_ hφ_ g w u u' h
    obtain ⟨U', hinv, hc⟩ := burnsideB49_core_f1 (burnsideB49_rho hV U G hG hb)
      (burnsideB49_q hV U) hqs hqe hdim hU E' hE4 hφ0 hEtr hEquad
    exact ⟨U', fun g x hx => by
      have := hinv (burnsideB49_iota hV U G hG g) x hx
      rwa [burnsideB49_rho_iota] at this, hc⟩
  exact burnsideB49_splits_of_complement hV U G hG U' hinv' hc

end FinalF1

section AddGaschutz

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49_odd_nsmul_add {M : Type*} [AddCommGroup M] (hM : ∀ x : M, x + x = 0) {k : ℕ}
    (hk : Odd k) (x : M) : k • x = x := by
  obtain ⟨j, rfl⟩ := hk
  rw [add_nsmul, mul_nsmul, one_nsmul, two_nsmul, hM x, nsmul_zero, zero_add]


theorem burnsideB49_end_mul_apply {M : Type*} [AddCommGroup M] (f g : AddMonoid.End M) (x : M) :
    (f * g) x = f (g x) := rfl

theorem burnsideB49_end_one_apply {M : Type*} [AddCommGroup M] (x : M) :
    (1 : AddMonoid.End M) x = x := rfl

variable {Γ : Type*} [Group Γ] {W V : Type*} [AddCommGroup W] [AddCommGroup V]

theorem burnsideB49_gaschutz_add (hV : ∀ x : V, x + x = 0)
    (ρW : Γ →* AddMonoid.End W) (ρV : Γ →* AddMonoid.End V)
    (S : Subgroup Γ) (hodd : Odd S.index)
    (q : V →+ W) (hq : ∀ g v, q (ρV g v) = ρW g (q v))
    (Φ : W →+ V) (hΦ : ∀ x, q (Φ x) = x)
    (hΦS : ∀ s ∈ S, ∀ x, Φ (ρW s x) = ρV s (Φ x)) :
    ∃ Φ' : W →+ V, (∀ x, q (Φ' x) = x) ∧ ∀ g x, Φ' (ρW g x) = ρV g (Φ' x) := by
  classical
  have hfin : S.FiniteIndex := ⟨hodd.pos.ne'⟩
  haveI : Finite (Γ ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ S) := Fintype.ofFinite _
  let Ψ : Γ → (W →+ V) := fun g =>
    (ρV g).comp (Φ.comp (ρW g⁻¹))
  have hΨapp : ∀ g y, Ψ g y = ρV g (Φ (ρW g⁻¹ y)) := fun g y => rfl
  have key : ∀ s ∈ S, ∀ z, ρV s (Φ (ρW s⁻¹ z)) = Φ z := by
    intro s hs z
    rw [← hΦS s hs, ← burnsideB49_end_mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hΨS : ∀ g, ∀ s ∈ S, Ψ (g * s) = Ψ g := by
    intro g s hs
    ext y
    rw [hΨapp, hΨapp]
    have h1 : ρV (g * s) (Φ (ρW (g * s)⁻¹ y)) = ρV g (ρV s (Φ (ρW s⁻¹ (ρW g⁻¹ y)))) := by
      simp [mul_inv_rev, map_mul]
    rw [h1, key s hs]
  let Ψ' : Γ ⧸ S → (W →+ V) := Quotient.lift Ψ (fun a b hab => by
    have hab' := QuotientGroup.leftRel_apply.mp hab
    have := hΨS a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hΨ' : ∀ g, Ψ' (QuotientGroup.mk g) = Ψ g := fun g => rfl
  have hΨh : ∀ (h : Γ) (x : Γ ⧸ S) (y : W), Ψ' x (ρW h y) = ρV h (Ψ' (h⁻¹ • x) y) := by
    intro h x y
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, hΨ', hΨ', hΨapp, hΨapp]
      have e1 : ∀ a, ρV h (ρV (h⁻¹ * g) a) = ρV g a := fun a => by
        rw [← burnsideB49_end_mul_apply, ← map_mul, mul_inv_cancel_left]
      have e2 : ρW (h⁻¹ * g)⁻¹ y = ρW g⁻¹ (ρW h y) := by
        rw [mul_inv_rev, inv_inv, map_mul]
        rfl
      rw [e1, e2]
  have hq1 : ∀ g y, q (Ψ g y) = y := by
    intro g y
    rw [hΨapp, hq, hΦ, ← burnsideB49_end_mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨∑ x : Γ ⧸ S, Ψ' x, fun y => ?_, fun g y => ?_⟩
  · rw [AddMonoidHom.finset_sum_apply, map_sum]
    have h1 : ∀ x : Γ ⧸ S, q (Ψ' x y) = y := fun x => by
      induction x using QuotientGroup.induction_on with
      | H g => exact hq1 g y
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    exact burnsideB49_odd_nsmul_add (fun x : W => by
      have := hV (Φ x)
      have h2 := congrArg q this
      rw [map_add, map_zero, hΦ] at h2
      exact h2) hodd y
  · rw [AddMonoidHom.finset_sum_apply, AddMonoidHom.finset_sum_apply, map_sum]
    rw [Finset.sum_congr rfl (fun x _ => hΨh g x y)]
    exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ (fun x => rfl)

theorem burnsideB49_fixed_add {X : Type*} [AddCommGroup X] (hX : ∀ x : X, x + x = 0)
    (ρ : Γ →* AddMonoid.End X) (Y : AddSubgroup X) (S : Subgroup Γ)
    (hodd : Odd S.index) (x₁ : X) (hx₁ : ∀ γ, ρ γ x₁ + x₁ ∈ Y) (hS : ∀ s ∈ S, ρ s x₁ = x₁) :
    ∃ x : X, x + x₁ ∈ Y ∧ ∀ γ, ρ γ x = x := by
  classical
  have hfin : S.FiniteIndex := ⟨hodd.pos.ne'⟩
  haveI : Finite (Γ ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ S) := Fintype.ofFinite _
  let δ : Γ → X := fun γ => ρ γ x₁ + x₁
  have hδS : ∀ g, ∀ s ∈ S, δ (g * s) = δ g := by
    intro g s hs
    simp only [δ, map_mul, burnsideB49_end_mul_apply, hS s hs]
  let δ' : Γ ⧸ S → X := Quotient.lift δ (fun a b hab => by
    have hab' := QuotientGroup.leftRel_apply.mp hab
    have := hδS a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hδ' : ∀ g, δ' (QuotientGroup.mk g) = δ g := fun g => rfl
  have hδh : ∀ (h : Γ) (x : Γ ⧸ S), ρ h (δ' x) = δ' (h • x) + δ h := by
    intro h x
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, hδ', hδ']
      simp only [δ, map_mul, burnsideB49_end_mul_apply, map_add]
      calc ρ h (ρ g x₁) + ρ h x₁ = ρ h (ρ g x₁) + ρ h x₁ + (x₁ + x₁) := by rw [hX, add_zero]
        _ = _ := by abel
  set u : X := ∑ x : Γ ⧸ S, δ' x with hu
  have hmem : u ∈ Y := AddSubgroup.sum_mem _ fun x _ => by
    induction x using QuotientGroup.induction_on with
    | H g => exact hx₁ g
  have hρu : ∀ h, ρ h u = u + δ h := by
    intro h
    rw [hu, map_sum, Finset.sum_congr rfl (fun x _ => hδh h x), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    have h1 : ∑ x : Γ ⧸ S, δ' (h • x) = ∑ x : Γ ⧸ S, δ' x :=
      Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun x => rfl)
    rw [h1]
    have h2 : Nat.card (Γ ⧸ S) • δ h = δ h := burnsideB49_odd_nsmul_add hX hodd (δ h)
    rw [h2]
  refine ⟨x₁ + u, ?_, fun γ => ?_⟩
  · have : x₁ + u + x₁ = u := by
      calc x₁ + u + x₁ = (x₁ + x₁) + u := by abel
        _ = u := by rw [hX, zero_add]
    rw [this]
    exact hmem
  · rw [map_add, hρu]
    have : ρ γ x₁ = x₁ + δ γ := by
      simp only [δ]
      calc ρ γ x₁ = ρ γ x₁ + (x₁ + x₁) := by rw [hX, add_zero]
        _ = x₁ + (ρ γ x₁ + x₁) := by abel
    rw [this]
    calc x₁ + δ γ + (u + δ γ) = x₁ + u + (δ γ + δ γ) := by abel
      _ = x₁ + u := by rw [hX, add_zero]

end AddGaschutz

section MatTool

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type*} [Field F]

@[expose] def burnsideB49_vec3 (y : Fin 2 → F) (c : F) : Fin 3 → F := ![y 0, y 1, c]

@[expose] def burnsideB49_ysub (x : Fin 3 → F) : Fin 2 → F := ![x 0, x 1]

theorem burnsideB49_vec3_ysub (x : Fin 3 → F) :
    burnsideB49_vec3 (burnsideB49_ysub x) (x 2) = x := by
  funext i
  fin_cases i <;> simp [burnsideB49_vec3, burnsideB49_ysub]

theorem burnsideB49_vec3_zero2 (y : Fin 2 → F) (c : F) :
    burnsideB49_vec3 y c 2 = c := by simp [burnsideB49_vec3]

theorem burnsideB49_ysub_vec3 (y : Fin 2 → F) (c : F) :
    burnsideB49_ysub (burnsideB49_vec3 y c) = y := by
  funext i
  fin_cases i <;> simp [burnsideB49_vec3, burnsideB49_ysub]

theorem burnsideB49_vec3_add (y y' : Fin 2 → F) (c c' : F) :
    burnsideB49_vec3 y c + burnsideB49_vec3 y' c' = burnsideB49_vec3 (y + y') (c + c') := by
  funext i
  fin_cases i <;> simp [burnsideB49_vec3]

theorem burnsideB49_vec3_ext {x x' : Fin 3 → F} (h : burnsideB49_ysub x = burnsideB49_ysub x')
    (h2 : x 2 = x' 2) : x = x' := by
  rw [← burnsideB49_vec3_ysub x, ← burnsideB49_vec3_ysub x', h, h2]

@[expose] def burnsideB49_tauM (w : Fin 2 → F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, 0, w 0; 0, 1, w 1; 0, 0, 1]

theorem burnsideB49_tauM_det (w : Fin 2 → F) : (burnsideB49_tauM w).det = 1 := by
  simp [burnsideB49_tauM, Matrix.det_fin_three]

@[expose] def burnsideB49_tau (w : Fin 2 → F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨burnsideB49_tauM w, burnsideB49_tauM_det w⟩

@[expose] def burnsideB49_kapM (M : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![M 0 0, M 0 1, 0; M 1 0, M 1 1, 0; 0, 0, 1]

theorem burnsideB49_kapM_det (M : Matrix (Fin 2) (Fin 2) F) :
    (burnsideB49_kapM M).det = M.det := by
  simp [burnsideB49_kapM, Matrix.det_fin_three, Matrix.det_fin_two]

@[expose] def burnsideB49_kap (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨burnsideB49_kapM (M : Matrix (Fin 2) (Fin 2) F), by
    rw [burnsideB49_kapM_det]; exact M.2⟩

theorem burnsideB49_tau_zero : burnsideB49_tau (0 : Fin 2 → F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideB49_tau, burnsideB49_tauM]

theorem burnsideB49_tau_add (w w' : Fin 2 → F) :
    burnsideB49_tau (w + w') = burnsideB49_tau w * burnsideB49_tau w' := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB49_tau, burnsideB49_tauM, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem burnsideB49_kap_one : burnsideB49_kap (1 : Matrix.SpecialLinearGroup (Fin 2) F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideB49_kap, burnsideB49_kapM]

theorem burnsideB49_kap_mul (M N : Matrix.SpecialLinearGroup (Fin 2) F) :
    burnsideB49_kap (M * N) = burnsideB49_kap M * burnsideB49_kap N := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB49_kap, burnsideB49_kapM, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]

theorem burnsideB49_kap_tau (M : Matrix.SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    burnsideB49_kap M * burnsideB49_tau w =
      burnsideB49_tau ((M : Matrix (Fin 2) (Fin 2) F).mulVec w) * burnsideB49_kap M := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB49_kap, burnsideB49_kapM, burnsideB49_tau, burnsideB49_tauM, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.sum_univ_three, Matrix.mulVec, dotProduct]

theorem burnsideB49_tau_mulVec (w : Fin 2 → F) (x : Fin 3 → F) :
    ((burnsideB49_tau w : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x =
      burnsideB49_vec3 (burnsideB49_ysub x + x 2 • w) (x 2) := by
  funext i
  fin_cases i <;>
    simp [burnsideB49_tau, burnsideB49_tauM, burnsideB49_vec3, burnsideB49_ysub, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, mul_comm]

theorem burnsideB49_kap_mulVec (M : Matrix.SpecialLinearGroup (Fin 2) F) (x : Fin 3 → F) :
    ((burnsideB49_kap M : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x =
      burnsideB49_vec3 ((M : Matrix (Fin 2) (Fin 2) F).mulVec (burnsideB49_ysub x)) (x 2) := by
  funext i
  fin_cases i <;>
    simp [burnsideB49_kap, burnsideB49_kapM, burnsideB49_vec3, burnsideB49_ysub, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three, Fin.sum_univ_two]

end MatTool

section SLFacts

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type*} [Field F]

@[expose] def burnsideB49_sl2 (a b c d : F) (h : a * d - b * c = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![a, b; c, d], by simp [Matrix.det_fin_two, h]⟩

theorem burnsideB49_sl2_transitive (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) F,
      (M : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨burnsideB49_sl2 0 (-(v 1)⁻¹) (v 1) 0 (by field_simp; ring), ?_⟩
    funext i
    fin_cases i
    · simp [burnsideB49_sl2, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
    · simp [burnsideB49_sl2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨burnsideB49_sl2 (v 0) 0 (v 1) (v 0)⁻¹ (by field_simp; ring), ?_⟩
    funext i
    fin_cases i
    · simp [burnsideB49_sl2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [burnsideB49_sl2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

@[expose] def burnsideB49_shear (a : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  burnsideB49_sl2 1 a 0 1 (by ring)

theorem burnsideB49_shear_zero : burnsideB49_shear (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [burnsideB49_shear, burnsideB49_sl2]

theorem burnsideB49_shear_add (a b : F) :
    burnsideB49_shear (a + b) = burnsideB49_shear a * burnsideB49_shear b := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB49_shear, burnsideB49_sl2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem burnsideB49_shear_injective : Function.Injective (burnsideB49_shear (F := F)) := by
  intro a b h
  have := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) F =>
    (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [burnsideB49_shear, burnsideB49_sl2] using this

@[expose] def burnsideB49_shearHom : Multiplicative F →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun a := burnsideB49_shear (Multiplicative.toAdd a)
  map_one' := burnsideB49_shear_zero
  map_mul' a b := burnsideB49_shear_add _ _

theorem burnsideB49_card_sl2 {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← StatedAPI.card_statedSL, StatedAPI.card_statedSL_two]

theorem burnsideB49_card_sl3 {F : Type} [Field F] [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) := by
  rw [← StatedAPI.card_statedSL, StatedAPI.card_statedSL_three]

theorem burnsideB49_odd_index_shear {F : Type} [Field F] [Finite F] (hF : Even (Nat.card F)) :
    Odd (burnsideB49_shearHom (F := F)).range.index := by
  have hinj : Function.Injective (burnsideB49_shearHom (F := F)) := fun a b h =>
    Multiplicative.toAdd.injective (burnsideB49_shear_injective h)
  have hcard : Nat.card (burnsideB49_shearHom (F := F)).range = Nat.card F := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr Multiplicative.toAdd
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h1 := Subgroup.index_mul_card (burnsideB49_shearHom (F := F)).range
  rw [hcard, burnsideB49_card_sl2] at h1
  have h2 : (burnsideB49_shearHom (F := F)).range.index = Nat.card F ^ 2 - 1 :=
    Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card F by omega) (by rw [mul_comm]; exact h1)
  rw [h2]
  have h3 : Even (Nat.card F ^ 2) := Nat.even_pow.2 ⟨hF, by norm_num⟩
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) h3 odd_one

end SLFacts

section S1Sec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type*} [Field F]

@[expose] def burnsideB49_kapHom :
    Matrix.SpecialLinearGroup (Fin 2) F →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun := burnsideB49_kap
  map_one' := burnsideB49_kap_one
  map_mul' := burnsideB49_kap_mul

theorem burnsideB49_tau_inv (w : Fin 2 → F) :
    (burnsideB49_tau w)⁻¹ = burnsideB49_tau (-w) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← burnsideB49_tau_add, add_neg_cancel, burnsideB49_tau_zero]

@[expose] def burnsideB49_S1 : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) where
  carrier := {s | ∃ (w : Fin 2 → F) (M : Matrix.SpecialLinearGroup (Fin 2) F),
    s = burnsideB49_tau w * burnsideB49_kap M}
  one_mem' := ⟨0, 1, by rw [burnsideB49_tau_zero, burnsideB49_kap_one, one_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨w, M, rfl⟩ ⟨w', M', rfl⟩
    refine ⟨w + (M : Matrix (Fin 2) (Fin 2) F).mulVec w', M * M', ?_⟩
    rw [burnsideB49_tau_add, burnsideB49_kap_mul]
    calc burnsideB49_tau w * burnsideB49_kap M * (burnsideB49_tau w' * burnsideB49_kap M') =
        burnsideB49_tau w * (burnsideB49_kap M * burnsideB49_tau w') * burnsideB49_kap M' := by
          simp only [mul_assoc]
      _ = _ := by rw [burnsideB49_kap_tau]; simp only [mul_assoc]
  inv_mem' := by
    rintro _ ⟨w, M, rfl⟩
    refine ⟨-((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec w,
      M⁻¹, ?_⟩
    have hk : burnsideB49_kap M⁻¹ = (burnsideB49_kap M)⁻¹ := (burnsideB49_kapHom (F := F)).map_inv M
    rw [mul_inv_rev, ← hk, burnsideB49_tau_inv]
    have := burnsideB49_kap_tau M⁻¹ (-w)
    rw [this, Matrix.mulVec_neg]

theorem burnsideB49_tau_kap_mem_S1 (w : Fin 2 → F) (M : Matrix.SpecialLinearGroup (Fin 2) F) :
    burnsideB49_tau w * burnsideB49_kap M ∈ burnsideB49_S1 (F := F) := ⟨w, M, rfl⟩

theorem burnsideB49_card_S1 {F : Type} [Field F] [Finite F] :
    Nat.card (burnsideB49_S1 (F := F)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) * Nat.card F ^ 2 := by
  let ψ : Matrix.SpecialLinearGroup (Fin 2) F × (Fin 2 → F) → burnsideB49_S1 (F := F) :=
    fun p => ⟨burnsideB49_tau p.2 * burnsideB49_kap p.1, ⟨p.2, p.1, rfl⟩⟩
  have hinj : Function.Injective ψ := by
    rintro ⟨M, w⟩ ⟨M', w'⟩ h
    have h1 := congrArg (fun s : burnsideB49_S1 (F := F) =>
      ((s : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h
    simp only [ψ] at h1
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h1
    have hw : w = w' := by
      funext i
      fin_cases i
      · have := congrFun (congrFun h1 0) 2
        simpa [burnsideB49_tau, burnsideB49_tauM, burnsideB49_kap, burnsideB49_kapM,
          Matrix.mul_apply, Fin.sum_univ_three] using this
      · have := congrFun (congrFun h1 1) 2
        simpa [burnsideB49_tau, burnsideB49_tauM, burnsideB49_kap, burnsideB49_kapM,
          Matrix.mul_apply, Fin.sum_univ_three] using this
    have hM : M = M' := by
      apply Subtype.ext
      ext i j
      fin_cases i <;> fin_cases j
      · have := congrFun (congrFun h1 0) 0
        simpa [burnsideB49_tau, burnsideB49_tauM, burnsideB49_kap, burnsideB49_kapM,
          Matrix.mul_apply, Fin.sum_univ_three] using this
      · have := congrFun (congrFun h1 0) 1
        simpa [burnsideB49_tau, burnsideB49_tauM, burnsideB49_kap, burnsideB49_kapM,
          Matrix.mul_apply, Fin.sum_univ_three] using this
      · have := congrFun (congrFun h1 1) 0
        simpa [burnsideB49_tau, burnsideB49_tauM, burnsideB49_kap, burnsideB49_kapM,
          Matrix.mul_apply, Fin.sum_univ_three] using this
      · have := congrFun (congrFun h1 1) 1
        simpa [burnsideB49_tau, burnsideB49_tauM, burnsideB49_kap, burnsideB49_kapM,
          Matrix.mul_apply, Fin.sum_univ_three] using this
    rw [hw, hM]
  have hsurj : Function.Surjective ψ := by
    rintro ⟨s, w, M, rfl⟩
    exact ⟨(M, w), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective ψ ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_fun]
  simp

theorem burnsideB49_odd_index_S1 {F : Type} [Field F] [Finite F] (hF : Even (Nat.card F)) :
    Odd (burnsideB49_S1 (F := F)).index := by
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have h1 := Subgroup.index_mul_card (burnsideB49_S1 (F := F))
  rw [burnsideB49_card_S1, burnsideB49_card_sl2, burnsideB49_card_sl3] at h1
  have hpos : 0 < Nat.card F ^ 3 * (Nat.card F ^ 2 - 1) := by
    apply Nat.mul_pos (by positivity)
    have : 4 ≤ Nat.card F ^ 2 := by nlinarith
    omega
  have h2 : (burnsideB49_S1 (F := F)).index = Nat.card F ^ 3 - 1 := by
    generalize Nat.card F ^ 2 - 1 = t at h1 hpos
    generalize Nat.card F ^ 3 - 1 = s at h1 ⊢
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc (burnsideB49_S1 (F := F)).index * (Nat.card F ^ 3 * t) =
        (burnsideB49_S1 (F := F)).index * (Nat.card F * t * Nat.card F ^ 2) := by ring
      _ = Nat.card F ^ 3 * (t * s) := h1
      _ = s * (Nat.card F ^ 3 * t) := by ring
  rw [h2]
  have h3 : Even (Nat.card F ^ 3) := Nat.even_pow.2 ⟨hF, by norm_num⟩
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) h3 odd_one

end S1Sec

section Core3Sec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

structure burnsideB49_Core3 (F : Type) [Field F] (A : Type) [AddCommGroup A] where
  ρ : Matrix.SpecialLinearGroup (Fin 3) F →* AddMonoid.End A
  q : A →+ (Fin 3 → F)
  hq : ∀ s a, q (ρ s a) = (s : Matrix (Fin 3) (Fin 3) F).mulVec (q a)
  hqs : Function.Surjective q
  τ : Matrix.SpecialLinearGroup (Fin 3) F →* Matrix.SpecialLinearGroup (Fin 3) F
  β : A → (Fin 3 → F)
  hβ_add : ∀ u u', q u = 0 → q u' = 0 → β (u + u') = β u + β u'
  hβ_inj : ∀ u u', q u = 0 → q u' = 0 → β u = β u' → u = u'
  hβ_surj : ∀ x, ∃ u, q u = 0 ∧ β u = x
  hβ : ∀ s u, q u = 0 → β (ρ s u) = (τ s : Matrix (Fin 3) (Fin 3) F).mulVec (β u)

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]

@[expose] def burnsideB49_QuadHyp (D : burnsideB49_Core3 F A) : Prop :=
  ∀ (w w' : Fin 2 → F) (a : A), D.ρ (burnsideB49_tau w) (D.ρ (burnsideB49_tau w') a - a) =
    D.ρ (burnsideB49_tau w') a - a

theorem burnsideB49_rho_mul_apply (D : burnsideB49_Core3 F A) (s t : Matrix.SpecialLinearGroup (Fin 3) F)
    (a : A) : D.ρ (s * t) a = D.ρ s (D.ρ t a) := by
  rw [map_mul]
  rfl

theorem burnsideB49_rho_one_apply (D : burnsideB49_Core3 F A) (a : A) : D.ρ 1 a = a := by
  rw [map_one]
  rfl

@[expose] def burnsideB49_Dz (D : burnsideB49_Core3 F A) (z : A) (w : Fin 2 → F) : A :=
  D.ρ (burnsideB49_tau w) z - z

theorem burnsideB49_Dz_zero (D : burnsideB49_Core3 F A) (z : A) : burnsideB49_Dz D z 0 = 0 := by
  simp [burnsideB49_Dz, burnsideB49_tau_zero, burnsideB49_rho_one_apply]

theorem burnsideB49_Dz_add_arg (D : burnsideB49_Core3 F A) (hQ : burnsideB49_QuadHyp D) (z : A)
    (w w' : Fin 2 → F) :
    burnsideB49_Dz D z (w + w') = burnsideB49_Dz D z w + burnsideB49_Dz D z w' := by
  unfold burnsideB49_Dz
  rw [burnsideB49_tau_add, burnsideB49_rho_mul_apply]
  have h := hQ w w' z
  rw [map_sub] at h
  calc D.ρ (burnsideB49_tau w) (D.ρ (burnsideB49_tau w') z) - z
      = (D.ρ (burnsideB49_tau w) (D.ρ (burnsideB49_tau w') z) - D.ρ (burnsideB49_tau w) z) +
          (D.ρ (burnsideB49_tau w) z - z) := by abel
    _ = _ := by rw [h]; abel

theorem burnsideB49_Dz_add_vec (D : burnsideB49_Core3 F A) (z z' : A) (w : Fin 2 → F) :
    burnsideB49_Dz D (z + z') w = burnsideB49_Dz D z w + burnsideB49_Dz D z' w := by
  unfold burnsideB49_Dz
  rw [map_add]
  abel

theorem burnsideB49_Dz_fixed (D : burnsideB49_Core3 F A) (hQ : burnsideB49_QuadHyp D) (z : A)
    (w w' : Fin 2 → F) : D.ρ (burnsideB49_tau w') (burnsideB49_Dz D z w) = burnsideB49_Dz D z w :=
  hQ w' w z

theorem burnsideB49_q_tau (D : burnsideB49_Core3 F A) (w : Fin 2 → F) (a : A) :
    D.q (D.ρ (burnsideB49_tau w) a) =
      burnsideB49_vec3 (burnsideB49_ysub (D.q a) + (D.q a) 2 • w) ((D.q a) 2) := by
  rw [D.hq, burnsideB49_tau_mulVec]

theorem burnsideB49_ysub_sub (x x' : Fin 3 → F) :
    burnsideB49_ysub (x - x') = burnsideB49_ysub x - burnsideB49_ysub x' := by
  funext i
  fin_cases i <;> simp [burnsideB49_ysub]

theorem burnsideB49_q_Dz (D : burnsideB49_Core3 F A) (z : A) (w : Fin 2 → F) :
    D.q (burnsideB49_Dz D z w) = burnsideB49_vec3 ((D.q z) 2 • w) 0 := by
  unfold burnsideB49_Dz
  rw [map_sub, burnsideB49_q_tau]
  apply burnsideB49_vec3_ext
  · rw [burnsideB49_ysub_sub, burnsideB49_ysub_vec3, burnsideB49_ysub_vec3]
    abel
  · simp [burnsideB49_vec3]

end Core3Sec

section Core3Lifts

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F]

@[expose] def burnsideB49_cycM : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

@[expose] def burnsideB49_cyc : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨burnsideB49_cycM, by simp [burnsideB49_cycM, Matrix.det_fin_three]⟩

@[expose] def burnsideB49_gM (c : F) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, c, 1], by simp [Matrix.det_fin_three]⟩

theorem burnsideB49_cyc_tau_shear (a : F) :
    burnsideB49_cyc * burnsideB49_tau ![0, a] =
      burnsideB49_kap (burnsideB49_shear a) * burnsideB49_cyc := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB49_cyc, burnsideB49_cycM, burnsideB49_tau, burnsideB49_tauM, burnsideB49_kap,
      burnsideB49_kapM, burnsideB49_shear, burnsideB49_sl2, Matrix.mul_apply, Fin.sum_univ_three]

theorem burnsideB49_cyc_tau_g (c : F) :
    burnsideB49_cyc * burnsideB49_tau ![c, 0] = burnsideB49_gM c * burnsideB49_cyc := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [burnsideB49_cyc, burnsideB49_cycM, burnsideB49_tau, burnsideB49_tauM, burnsideB49_gM,
      Matrix.mul_apply, Fin.sum_univ_three]

variable {A : Type} [AddCommGroup A]

theorem burnsideB49_c3_quad_conj (D : burnsideB49_Core3 F A) (hQ : burnsideB49_QuadHyp D)
    (P : Matrix.SpecialLinearGroup (Fin 3) F) (w w' : Fin 2 → F) (a : A) :
    D.ρ (P * burnsideB49_tau w * P⁻¹) (D.ρ (P * burnsideB49_tau w' * P⁻¹) a - a) =
      D.ρ (P * burnsideB49_tau w' * P⁻¹) a - a := by
  have h1 : ∀ (t : Matrix.SpecialLinearGroup (Fin 3) F) (b : A),
      D.ρ (P * t * P⁻¹) b = D.ρ P (D.ρ t (D.ρ P⁻¹ b)) := by
    intro t b
    rw [burnsideB49_rho_mul_apply, burnsideB49_rho_mul_apply]
  have hPP : ∀ x, D.ρ P (D.ρ P⁻¹ x) = x := fun x => by
    rw [← burnsideB49_rho_mul_apply, mul_inv_cancel, burnsideB49_rho_one_apply]
  have hPP' : ∀ x, D.ρ P⁻¹ (D.ρ P x) = x := fun x => by
    rw [← burnsideB49_rho_mul_apply, inv_mul_cancel, burnsideB49_rho_one_apply]
  obtain ⟨b, rfl⟩ : ∃ b, a = D.ρ P b := ⟨D.ρ P⁻¹ a, (hPP a).symm⟩
  have e1 : ∀ t x, D.ρ (P * t * P⁻¹) (D.ρ P x) = D.ρ P (D.ρ t x) := fun t x => by
    rw [h1, hPP']
  rw [e1 (burnsideB49_tau w') b, ← map_sub (D.ρ P), e1 (burnsideB49_tau w), hQ w w' b]

theorem burnsideB49_Pfix_lift (D : burnsideB49_Core3 F A) (hQ : burnsideB49_QuadHyp D) (c : F) :
    ∃ x₁ : A, D.q x₁ = burnsideB49_vec3 0 c ∧
      ∀ a : F, D.ρ (burnsideB49_kap (burnsideB49_shear a)) x₁ = x₁ := by
  obtain ⟨y, hy⟩ := D.hqs (burnsideB49_vec3 ![0, 1] 0)
  have hg : burnsideB49_gM c = burnsideB49_cyc * burnsideB49_tau ![c, 0] * burnsideB49_cyc⁻¹ :=
    eq_mul_inv_of_mul_eq (burnsideB49_cyc_tau_g c).symm
  have hk : ∀ a : F, burnsideB49_kap (burnsideB49_shear a) =
      burnsideB49_cyc * burnsideB49_tau ![0, a] * burnsideB49_cyc⁻¹ := fun a =>
    eq_mul_inv_of_mul_eq (burnsideB49_cyc_tau_shear a).symm
  refine ⟨D.ρ (burnsideB49_gM c) y - y, ?_, fun a => ?_⟩
  · rw [map_sub, D.hq, hy]
    apply burnsideB49_vec3_ext
    · funext i
      fin_cases i <;> simp [burnsideB49_ysub, burnsideB49_gM, burnsideB49_vec3, Matrix.mulVec,
        dotProduct, Fin.sum_univ_three]
    · simp [burnsideB49_gM, burnsideB49_vec3, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · rw [hk a]
    have := burnsideB49_c3_quad_conj D hQ burnsideB49_cyc ![0, a] ![c, 0] y
    rw [← hg] at this
    exact this

theorem burnsideB49_fixed_ysub {x : Fin 3 → F}
    (h : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F,
      ((burnsideB49_kap M : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x
        = x) : burnsideB49_ysub x = 0 := by
  have h1 := h (burnsideB49_shear 1)
  have h2 := h (burnsideB49_sl2 1 0 1 1 (by ring))
  have h1' := congrFun h1 0
  have h1'' := congrFun h1 1
  have h2' := congrFun h2 0
  have h2'' := congrFun h2 1
  simp [burnsideB49_kap, burnsideB49_kapM, burnsideB49_shear, burnsideB49_sl2, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three] at h1' h1'' h2' h2''
  funext i
  fin_cases i
  · simpa [burnsideB49_ysub] using h2''
  · simpa [burnsideB49_ysub] using h1'

end Core3Lifts

section Core3Match

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F]

theorem burnsideB49_vec3_zero : burnsideB49_vec3 (0 : Fin 2 → F) 0 = 0 := by
  funext i
  fin_cases i <;> simp [burnsideB49_vec3]

theorem burnsideB49_vec3_sub (y y' : Fin 2 → F) (c c' : F) :
    burnsideB49_vec3 y c - burnsideB49_vec3 y' c' = burnsideB49_vec3 (y - y') (c - c') := by
  funext i
  fin_cases i <;> simp [burnsideB49_vec3]

theorem burnsideB49_vec3_two (i : Fin 3) (y : Fin 2 → F) (c : F) :
    burnsideB49_vec3 y c i = ![y 0, y 1, c] i := rfl

theorem burnsideB49_vec3_add_self [CharP F 2] (y : Fin 2 → F) (c : F) :
    burnsideB49_vec3 y c + burnsideB49_vec3 y c = 0 := by
  funext i
  fin_cases i <;> simp [burnsideB49_vec3, CharTwo.add_self_eq_zero]

variable {A : Type} [AddCommGroup A]

theorem burnsideB49_c3_Kfix [Finite F] [CharP F 2] (D : burnsideB49_Core3 F A)
    (hQ : burnsideB49_QuadHyp D) (hA : ∀ a : A, a + a = 0) (c : F) :
    ∃ z : A, D.q z = burnsideB49_vec3 0 c ∧
      ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z = z := by
  obtain ⟨x₁, hx₁q, hx₁⟩ := burnsideB49_Pfix_lift D hQ c
  have hF : Even (Nat.card F) := by
    haveI := Fintype.ofFinite F
    obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hn]
    exact (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)
  let ρΓ : Matrix.SpecialLinearGroup (Fin 2) F →* AddMonoid.End A :=
    D.ρ.comp (burnsideB49_kapHom (F := F))
  have hq1 : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) F, ρΓ γ x₁ + x₁ ∈ D.q.ker := by
    intro γ
    rw [AddMonoidHom.mem_ker, map_add]
    change D.q (D.ρ (burnsideB49_kap γ) x₁) + D.q x₁ = 0
    rw [D.hq, hx₁q, burnsideB49_kap_mulVec]
    simp only [burnsideB49_ysub_vec3, Matrix.mulVec_zero]
    exact burnsideB49_vec3_add_self _ _
  have hS : ∀ s ∈ (burnsideB49_shearHom (F := F)).range, ρΓ s x₁ = x₁ := by
    rintro s ⟨a, rfl⟩
    exact hx₁ (Multiplicative.toAdd a)
  obtain ⟨z, hz1, hz2⟩ := burnsideB49_fixed_add hA ρΓ D.q.ker (burnsideB49_shearHom (F := F)).range
    (burnsideB49_odd_index_shear hF) x₁ hq1 hS
  refine ⟨z, ?_, fun M => hz2 M⟩
  have h := hz1
  rw [AddMonoidHom.mem_ker, map_add] at h
  have h2 : D.q x₁ + D.q x₁ = 0 := by
    rw [hx₁q]
    exact burnsideB49_vec3_add_self _ _
  calc D.q z = D.q z + (D.q x₁ + D.q x₁) := by rw [h2, add_zero]
    _ = (D.q z + D.q x₁) + D.q x₁ := by abel
    _ = D.q x₁ := by rw [h, zero_add]
    _ = _ := hx₁q

theorem burnsideB49_Dz_equiv (D : burnsideB49_Core3 F A) (z : A)
    (hz : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z = z)
    (M : Matrix.SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    D.ρ (burnsideB49_kap M) (burnsideB49_Dz D z w) =
      burnsideB49_Dz D z ((M : Matrix (Fin 2) (Fin 2) F).mulVec w) := by
  unfold burnsideB49_Dz
  rw [map_sub, ← burnsideB49_rho_mul_apply, burnsideB49_kap_tau, burnsideB49_rho_mul_apply, hz M]

@[expose] def burnsideB49_nu (D : burnsideB49_Core3 F A) (z₁ z : A) (c : F) (w : Fin 2 → F) : A :=
  burnsideB49_Dz D z w - burnsideB49_Dz D z₁ (c • w)

theorem burnsideB49_nu_q (D : burnsideB49_Core3 F A) (z₁ z : A) (c : F)
    (hz₁q : D.q z₁ = burnsideB49_vec3 0 1) (hzq : D.q z = burnsideB49_vec3 0 c) (w : Fin 2 → F) :
    D.q (burnsideB49_nu D z₁ z c w) = 0 := by
  unfold burnsideB49_nu
  rw [map_sub, burnsideB49_q_Dz, burnsideB49_q_Dz, hz₁q, hzq, burnsideB49_vec3_sub]
  simp [burnsideB49_vec3]

theorem burnsideB49_nu_fixed (D : burnsideB49_Core3 F A) (hQ : burnsideB49_QuadHyp D) (z₁ z : A)
    (c : F) (w w' : Fin 2 → F) :
    D.ρ (burnsideB49_tau w') (burnsideB49_nu D z₁ z c w) = burnsideB49_nu D z₁ z c w := by
  unfold burnsideB49_nu
  rw [map_sub, burnsideB49_Dz_fixed D hQ, burnsideB49_Dz_fixed D hQ]

theorem burnsideB49_nu_equiv (D : burnsideB49_Core3 F A) (z₁ z : A)
    (hz₁K : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z₁ = z₁)
    (hzK : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z = z) (c : F)
    (M : Matrix.SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    D.ρ (burnsideB49_kap M) (burnsideB49_nu D z₁ z c w) =
      burnsideB49_nu D z₁ z c ((M : Matrix (Fin 2) (Fin 2) F).mulVec w) := by
  unfold burnsideB49_nu
  rw [map_sub, burnsideB49_Dz_equiv D z hzK, burnsideB49_Dz_equiv D z₁ hz₁K, Matrix.mulVec_smul]

theorem burnsideB49_nu_add (D : burnsideB49_Core3 F A) (hQ : burnsideB49_QuadHyp D) (z₁ z : A)
    (c : F) (w w' : Fin 2 → F) :
    burnsideB49_nu D z₁ z c (w + w') = burnsideB49_nu D z₁ z c w + burnsideB49_nu D z₁ z c w' := by
  unfold burnsideB49_nu
  rw [burnsideB49_Dz_add_arg D hQ, smul_add, burnsideB49_Dz_add_arg D hQ]
  abel

theorem burnsideB49_nu_zero (D : burnsideB49_Core3 F A) (z₁ z : A) (c : F) :
    burnsideB49_nu D z₁ z c 0 = 0 := by
  simp [burnsideB49_nu, burnsideB49_Dz_zero]

end Core3Match

section Core3Nat

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]

theorem burnsideB49_c3_beta_zero (D : burnsideB49_Core3 F A) : D.β 0 = 0 := by
  have h := D.hβ_add 0 0 (map_zero D.q) (map_zero D.q)
  rw [add_zero] at h
  simpa using h

theorem burnsideB49_c3_beta_sub (D : burnsideB49_Core3 F A) (a b : A) (ha : D.q a = 0)
    (hb : D.q b = 0) : D.β (a - b) = D.β a - D.β b := by
  have h := D.hβ_add (a - b) b (by rw [map_sub, ha, hb, sub_zero]) hb
  rw [sub_add_cancel] at h
  exact eq_sub_of_add_eq h.symm

theorem burnsideB49_mulVec_e0_shear (a : F) :
    ((burnsideB49_shear a : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      ![1, 0] = ![1, 0] := by
  funext i
  fin_cases i <;> simp [burnsideB49_shear, burnsideB49_sl2, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two]

theorem burnsideB49_c3_match_nat [CharP F 2] (D : burnsideB49_Core3 F A)
    (hQ : burnsideB49_QuadHyp D) (hA : ∀ a : A, a + a = 0) (hτ : ∀ s, D.τ s = s)
    (z₁ : A) (hz₁q : D.q z₁ = burnsideB49_vec3 0 1)
    (hz₁K : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z₁ = z₁)
    (z : A) (c : F) (hzq : D.q z = burnsideB49_vec3 0 c)
    (hzK : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z = z) :
    ∃ u : A, D.q u = 0 ∧ (∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) u = u) ∧
      ∀ w, burnsideB49_Dz D (z + u) w = burnsideB49_Dz D z₁ (c • w) := by
  have hνq : ∀ w, D.q (burnsideB49_nu D z₁ z c w) = 0 := burnsideB49_nu_q D z₁ z c hz₁q hzq
  have hβν : ∀ (s : Matrix.SpecialLinearGroup (Fin 3) F) w,
      D.β (D.ρ s (burnsideB49_nu D z₁ z c w)) =
        (s : Matrix (Fin 3) (Fin 3) F).mulVec (D.β (burnsideB49_nu D z₁ z c w)) := fun s w => by
    rw [D.hβ s _ (hνq w), hτ]
  have h3 : ∀ w, D.β (burnsideB49_nu D z₁ z c w) 2 = 0 := by
    intro w
    have h := hβν (burnsideB49_tau ![1, 0]) w
    rw [burnsideB49_nu_fixed D hQ z₁ z c w ![1, 0], burnsideB49_tau_mulVec] at h
    have h0 := congrFun h 0
    simpa [burnsideB49_vec3, burnsideB49_ysub] using h0
  have hy : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) F) w,
      burnsideB49_ysub (D.β (burnsideB49_nu D z₁ z c ((M : Matrix (Fin 2) (Fin 2) F).mulVec w))) =
        (M : Matrix (Fin 2) (Fin 2) F).mulVec (burnsideB49_ysub (D.β (burnsideB49_nu D z₁ z c w))) := by
    intro M w
    rw [← burnsideB49_nu_equiv D z₁ z hz₁K hzK c M w, hβν, burnsideB49_kap_mulVec,
      burnsideB49_ysub_vec3]
  set y : (Fin 2 → F) → (Fin 2 → F) := fun w =>
    burnsideB49_ysub (D.β (burnsideB49_nu D z₁ z c w)) with hydef
  have hye : y ![1, 0] 1 = 0 := by
    have h := hy (burnsideB49_shear 1) ![1, 0]
    rw [burnsideB49_mulVec_e0_shear] at h
    have h0 := congrFun h 0
    simp [burnsideB49_shear, burnsideB49_sl2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
    exact h0
  have hye' : y ![1, 0] = (y ![1, 0] 0) • (![1, 0] : Fin 2 → F) := by
    funext i
    fin_cases i
    · simp
    · simpa using hye
  set c'' : F := y ![1, 0] 0 with hc''
  obtain ⟨u, hu0, hu⟩ := D.hβ_surj (burnsideB49_vec3 0 c'')
  have hyw : ∀ w, y w = c'' • w := by
    intro w
    by_cases hw : w = 0
    · subst hw
      simp [hydef, burnsideB49_nu_zero, burnsideB49_c3_beta_zero, burnsideB49_ysub]
    · obtain ⟨M, hM⟩ := burnsideB49_sl2_transitive w hw
      have := hy M ![1, 0]
      rw [hM] at this
      change y w = (M : Matrix (Fin 2) (Fin 2) F).mulVec (y ![1, 0]) at this
      rw [this, hye', Matrix.mulVec_smul, hM]
  have hKu : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) u = u := by
    intro M
    apply D.hβ_inj _ _ (by rw [D.hq, hu0, Matrix.mulVec_zero]) hu0
    rw [D.hβ _ _ hu0, hτ, hu, burnsideB49_kap_mulVec, burnsideB49_ysub_vec3, Matrix.mulVec_zero,
      burnsideB49_vec3_zero2]
  have hνu : ∀ w, burnsideB49_nu D z₁ z c w = burnsideB49_Dz D u w := by
    intro w
    have hqDu : D.q (burnsideB49_Dz D u w) = 0 := by
      rw [burnsideB49_q_Dz, hu0]
      simp [burnsideB49_vec3_zero]
    apply D.hβ_inj _ _ (hνq w) hqDu
    have hq1 : D.q (D.ρ (burnsideB49_tau w) u) = 0 := by
      rw [D.hq, hu0, Matrix.mulVec_zero]
    unfold burnsideB49_Dz
    rw [burnsideB49_c3_beta_sub D _ _ hq1 hu0, D.hβ _ _ hu0, hτ, burnsideB49_tau_mulVec, hu]
    have hb := burnsideB49_vec3_ysub (D.β (burnsideB49_nu D z₁ z c w))
    rw [h3 w] at hb
    rw [← hb]
    have : burnsideB49_ysub (D.β (burnsideB49_nu D z₁ z c w)) = y w := rfl
    rw [this, hyw, burnsideB49_vec3_sub]
    congr 1
    · rw [burnsideB49_ysub_vec3, burnsideB49_vec3_zero2]
      simp
    · simp [burnsideB49_vec3]
  refine ⟨u, hu0, hKu, fun w => ?_⟩
  have hD : burnsideB49_Dz D z w = burnsideB49_nu D z₁ z c w + burnsideB49_Dz D z₁ (c • w) := by
    unfold burnsideB49_nu
    abel
  rw [burnsideB49_Dz_add_vec, hD, ← hνu w]
  calc burnsideB49_nu D z₁ z c w + burnsideB49_Dz D z₁ (c • w) + burnsideB49_nu D z₁ z c w
      = burnsideB49_Dz D z₁ (c • w) +
          (burnsideB49_nu D z₁ z c w + burnsideB49_nu D z₁ z c w) := by abel
    _ = _ := by rw [hA, add_zero]

end Core3Nat

section Core3Dual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]

theorem burnsideB49_invT_tau_mulVec (w : Fin 2 → F) (b : Fin 3 → F) :
    ((CFSG.Quasithin.JonesParshall.invTransposeSL 3 F (burnsideB49_tau w) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec b =
      ![b 0, b 1, b 2 - w 0 * b 0 - w 1 * b 1] := by
  rw [CFSG.Quasithin.JonesParshall.invTransposeSL_coe, burnsideB49_tau_inv]
  funext i
  fin_cases i <;>
    simp [burnsideB49_tau, burnsideB49_tauM, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Matrix.transpose_apply] <;> ring

theorem burnsideB49_invT_kap_mulVec (M : Matrix.SpecialLinearGroup (Fin 2) F) (t : F) :
    ((CFSG.Quasithin.JonesParshall.invTransposeSL 3 F (burnsideB49_kap M) :
        Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
      (burnsideB49_vec3 0 t) = burnsideB49_vec3 0 t := by
  have hk : burnsideB49_kap M⁻¹ = (burnsideB49_kap M)⁻¹ :=
    (burnsideB49_kapHom (F := F)).map_inv M
  rw [CFSG.Quasithin.JonesParshall.invTransposeSL_coe, ← hk]
  funext i
  fin_cases i <;>
    simp [burnsideB49_kap, burnsideB49_kapM, burnsideB49_vec3, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.transpose_apply]

theorem burnsideB49_c3_match_dual [CharP F 2] (D : burnsideB49_Core3 F A)
    (hQ : burnsideB49_QuadHyp D) (hA : ∀ a : A, a + a = 0)
    (hτ : ∀ s, D.τ s = CFSG.Quasithin.JonesParshall.invTransposeSL 3 F s)
    (z₁ : A) (hz₁q : D.q z₁ = burnsideB49_vec3 0 1)
    (hz₁K : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z₁ = z₁)
    (z : A) (c : F) (hzq : D.q z = burnsideB49_vec3 0 c)
    (hzK : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z = z) :
    ∀ w, burnsideB49_Dz D z w = burnsideB49_Dz D z₁ (c • w) := by
  have hνq : ∀ w, D.q (burnsideB49_nu D z₁ z c w) = 0 := burnsideB49_nu_q D z₁ z c hz₁q hzq
  have hβν : ∀ (s : Matrix.SpecialLinearGroup (Fin 3) F) w,
      D.β (D.ρ s (burnsideB49_nu D z₁ z c w)) =
        ((CFSG.Quasithin.JonesParshall.invTransposeSL 3 F s : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).mulVec (D.β (burnsideB49_nu D z₁ z c w)) := fun s w => by
    rw [D.hβ s _ (hνq w), hτ]
  have hc01 : ∀ w (w' : Fin 2 → F),
      w' 0 * D.β (burnsideB49_nu D z₁ z c w) 0 + w' 1 * D.β (burnsideB49_nu D z₁ z c w) 1 = 0 := by
    intro w w'
    have h := hβν (burnsideB49_tau w') w
    rw [burnsideB49_nu_fixed D hQ z₁ z c w w', burnsideB49_invT_tau_mulVec] at h
    have h2 := congrFun h 2
    simp at h2
    linear_combination h2
  have hys : ∀ w, burnsideB49_ysub (D.β (burnsideB49_nu D z₁ z c w)) = 0 := by
    intro w
    funext i
    fin_cases i
    · have := hc01 w ![1, 0]
      simpa [burnsideB49_ysub] using this
    · have := hc01 w ![0, 1]
      simpa [burnsideB49_ysub] using this
  have hβform : ∀ w, D.β (burnsideB49_nu D z₁ z c w) =
      burnsideB49_vec3 0 (D.β (burnsideB49_nu D z₁ z c w) 2) := by
    intro w
    have := burnsideB49_vec3_ysub (D.β (burnsideB49_nu D z₁ z c w))
    rw [hys w] at this
    exact this.symm
  have hconst : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) F) w,
      burnsideB49_nu D z₁ z c ((M : Matrix (Fin 2) (Fin 2) F).mulVec w) =
        burnsideB49_nu D z₁ z c w := by
    intro M w
    apply D.hβ_inj _ _ (hνq _) (hνq _)
    rw [← burnsideB49_nu_equiv D z₁ z hz₁K hzK c M w, hβν, hβform w,
      burnsideB49_invT_kap_mulVec]
  have hne : ∀ w : Fin 2 → F, w ≠ 0 →
      burnsideB49_nu D z₁ z c w = burnsideB49_nu D z₁ z c ![1, 0] := by
    intro w hw
    obtain ⟨M, hM⟩ := burnsideB49_sl2_transitive w hw
    rw [← hM]
    exact hconst M ![1, 0]
  have h01 : burnsideB49_nu D z₁ z c ![1, 0] = 0 := by
    have h1 := hne ![0, 1] (by
      intro h
      have := congrFun h 1
      simp at this)
    have h2 := hne (![1, 0] + ![0, 1]) (by
      intro h
      have := congrFun h 0
      simp at this)
    have h3 : (![1, 0] + ![0, 1] : Fin 2 → F) = ![1, 1] := by
      funext i
      fin_cases i <;> simp
    have h4 := burnsideB49_nu_add D hQ z₁ z c ![1, 0] ![0, 1]
    rw [h2, h1] at h4
    have h5 : burnsideB49_nu D z₁ z c ![1, 0] + burnsideB49_nu D z₁ z c ![1, 0] =
        burnsideB49_nu D z₁ z c ![1, 0] + 0 := by
      rw [add_zero]
      exact h4.symm
    exact (add_left_cancel h5)
  intro w
  have hw0 : burnsideB49_nu D z₁ z c w = 0 := by
    by_cases hw : w = 0
    · rw [hw]
      exact burnsideB49_nu_zero D z₁ z c
    · rw [hne w hw, h01]
  unfold burnsideB49_nu at hw0
  exact sub_eq_zero.1 hw0

end Core3Dual

section Core3Main

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49_exists_add_section {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (hG : ∀ x : G, x + x = 0) (f : G →+ H) (hf : Function.Surjective f) :
    ∃ s : H →+ G, ∀ x, f (s x) = x := by
  letI : Module (ZMod 2) G := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]; exact hG x)
  have hH : ∀ x : H, 2 • x = 0 := fun x => by
    obtain ⟨g, rfl⟩ := hf x
    rw [← map_nsmul, two_nsmul, hG g, map_zero]
  letI : Module (ZMod 2) H := AddCommGroup.zmodModule (n := 2) hH
  have hrange : LinearMap.range (AddMonoidHom.toZModLinearMap 2 f) = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact hf
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective
    (AddMonoidHom.toZModLinearMap 2 f) hrange
  refine ⟨(g : H →ₗ[ZMod 2] G).toAddMonoidHom, fun x => ?_⟩
  have := congrArg (fun T : H →ₗ[ZMod 2] H => T x) hg
  exact this

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]

theorem burnsideB49_even_card [Finite F] [CharP F 2] : Even (Nat.card F) := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn]
  exact (Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩)

theorem burnsideB49_c3_match [CharP F 2] (D : burnsideB49_Core3 F A) (hQ : burnsideB49_QuadHyp D)
    (hA : ∀ a : A, a + a = 0)
    (hτ : (∀ s, D.τ s = s) ∨ (∀ s, D.τ s = CFSG.Quasithin.JonesParshall.invTransposeSL 3 F s))
    (z₁ : A) (hz₁q : D.q z₁ = burnsideB49_vec3 0 1)
    (hz₁K : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z₁ = z₁)
    (z : A) (c : F) (hzq : D.q z = burnsideB49_vec3 0 c)
    (hzK : ∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z = z) :
    ∃ u : A, D.q u = 0 ∧ (∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) u = u) ∧
      ∀ w, burnsideB49_Dz D (z + u) w = burnsideB49_Dz D z₁ (c • w) := by
  rcases hτ with hτ | hτ
  · exact burnsideB49_c3_match_nat D hQ hA hτ z₁ hz₁q hz₁K z c hzq hzK
  · refine ⟨0, map_zero _, fun M => map_zero _, fun w => ?_⟩
    rw [add_zero]
    exact burnsideB49_c3_match_dual D hQ hA hτ z₁ hz₁q hz₁K z c hzq hzK w

@[expose] def burnsideB49_ZD (D : burnsideB49_Core3 F A) (hQ : burnsideB49_QuadHyp D)
    (hA : ∀ a : A, a + a = 0) (z₁ : A) : AddSubgroup A where
  carrier := {z | (∀ M : Matrix.SpecialLinearGroup (Fin 2) F, D.ρ (burnsideB49_kap M) z = z) ∧
    ∀ w, burnsideB49_Dz D z w = burnsideB49_Dz D z₁ ((D.q z) 2 • w)}
  zero_mem' := ⟨fun M => map_zero _, fun w => by
    have h1 : burnsideB49_Dz D 0 w = 0 := by simp [burnsideB49_Dz]
    have h2 : (D.q 0) 2 • w = 0 := by simp
    rw [h1, h2, burnsideB49_Dz_zero]⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun M => by rw [map_add, ha1, hb1], fun w => ?_⟩
    rw [burnsideB49_Dz_add_vec, ha2, hb2, map_add, Pi.add_apply, add_smul,
      burnsideB49_Dz_add_arg D hQ]
  neg_mem' := by
    rintro a ⟨ha1, ha2⟩
    rw [neg_eq_of_add_eq_zero_right (hA a)]
    exact ⟨ha1, ha2⟩

end Core3Main

section Core3Final

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]

@[expose] def burnsideB49_matEnd :
    Matrix.SpecialLinearGroup (Fin 3) F →* AddMonoid.End (Fin 3 → F) where
  toFun s := AddMonoidHom.mk' (fun x => (s : Matrix (Fin 3) (Fin 3) F).mulVec x)
    (Matrix.mulVec_add _)
  map_one' := AddMonoidHom.ext fun x => by
    change ((1 : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x
    simp
  map_mul' s t := AddMonoidHom.ext fun x => by
    change ((s * t : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x =
      (s : Matrix (Fin 3) (Fin 3) F).mulVec ((t : Matrix (Fin 3) (Fin 3) F).mulVec x)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem burnsideB49_matEnd_apply (s : Matrix.SpecialLinearGroup (Fin 3) F) (x : Fin 3 → F) :
    burnsideB49_matEnd s x = (s : Matrix (Fin 3) (Fin 3) F).mulVec x := rfl

theorem burnsideB49_core3 [Finite F] [CharP F 2] (D : burnsideB49_Core3 F A)
    (hQ : burnsideB49_QuadHyp D) (hA : ∀ a : A, a + a = 0)
    (hτ : (∀ s, D.τ s = s) ∨ (∀ s, D.τ s = CFSG.Quasithin.JonesParshall.invTransposeSL 3 F s)) :
    ∃ Φ : (Fin 3 → F) →+ A, (∀ x, D.q (Φ x) = x) ∧
      ∀ (s : Matrix.SpecialLinearGroup (Fin 3) F) x,
        Φ ((s : Matrix (Fin 3) (Fin 3) F).mulVec x) = D.ρ s (Φ x) := by
  classical
  obtain ⟨z₁, hz₁q, hz₁K⟩ := burnsideB49_c3_Kfix D hQ hA 1
  set ZD := burnsideB49_ZD D hQ hA z₁ with hZD
  let ε : ZD →+ F := (Pi.evalAddMonoidHom (fun _ : Fin 3 => F) 2).comp (D.q.comp ZD.subtype)
  have hε : Function.Surjective ε := by
    intro c
    obtain ⟨z, hzq, hzK⟩ := burnsideB49_c3_Kfix D hQ hA c
    obtain ⟨u, hu0, huK, hmatch⟩ := burnsideB49_c3_match D hQ hA hτ z₁ hz₁q hz₁K z c hzq hzK
    have hq2 : (D.q (z + u)) 2 = c := by
      rw [map_add, hu0, add_zero, hzq]
      simp [burnsideB49_vec3]
    refine ⟨⟨z + u, fun M => by rw [map_add, hzK, huK], fun w => ?_⟩, hq2⟩
    rw [hmatch w, hq2]
  obtain ⟨s, hs⟩ := burnsideB49_exists_add_section (fun x : ZD => Subtype.ext (hA x)) ε hε
  let Λhom : F →+ A := ZD.subtype.comp s
  have hΛ2 : ∀ c, (D.q (Λhom c)) 2 = c := fun c => hs c
  have hΛK : ∀ c (M : Matrix.SpecialLinearGroup (Fin 2) F), D.ρ (burnsideB49_kap M) (Λhom c) = Λhom c :=
    fun c M => (s c).2.1 M
  have hΛD : ∀ c w, burnsideB49_Dz D (Λhom c) w = burnsideB49_Dz D z₁ (c • w) := fun c w => by
    have h := (s c).2.2 w
    have h2 : (D.q ((s c : ZD) : A)) 2 = c := hs c
    rw [h2] at h
    exact h
  have hΛq : ∀ c, D.q (Λhom c) = burnsideB49_vec3 0 c := by
    intro c
    have h1 : burnsideB49_ysub (D.q (Λhom c)) = 0 := by
      apply burnsideB49_fixed_ysub
      intro M
      rw [← D.hq, hΛK]
    have := burnsideB49_vec3_ysub (D.q (Λhom c))
    rw [h1, hΛ2] at this
    exact this.symm
  let D₁hom : (Fin 2 → F) →+ A :=
    AddMonoidHom.mk' (burnsideB49_Dz D z₁) (burnsideB49_Dz_add_arg D hQ z₁)
  let ysubHom : (Fin 3 → F) →+ (Fin 2 → F) :=
    AddMonoidHom.mk' burnsideB49_ysub (fun x x' => by
      funext i
      fin_cases i <;> simp [burnsideB49_ysub])
  let Φ : (Fin 3 → F) →+ A :=
    Λhom.comp (Pi.evalAddMonoidHom (fun _ : Fin 3 => F) 2) + D₁hom.comp ysubHom
  have hΦapp : ∀ x, Φ x = Λhom (x 2) + burnsideB49_Dz D z₁ (burnsideB49_ysub x) := fun x => rfl
  have hΦq : ∀ x, D.q (Φ x) = x := by
    intro x
    rw [hΦapp, map_add, hΛq, burnsideB49_q_Dz, hz₁q]
    rw [burnsideB49_vec3_add]
    have : (burnsideB49_vec3 0 1 : Fin 3 → F) 2 = 1 := by simp [burnsideB49_vec3]
    rw [this, one_smul, zero_add, add_zero]
    exact burnsideB49_vec3_ysub x
  have hΦkap : ∀ (M : Matrix.SpecialLinearGroup (Fin 2) F) x,
      Φ ((burnsideB49_kap M : Matrix (Fin 3) (Fin 3) F).mulVec x) = D.ρ (burnsideB49_kap M) (Φ x) := by
    intro M x
    rw [hΦapp, hΦapp, burnsideB49_kap_mulVec, map_add, hΛK, burnsideB49_Dz_equiv D z₁ hz₁K]
    simp [burnsideB49_vec3, burnsideB49_ysub]
  have hΦtau : ∀ (w : Fin 2 → F) x,
      Φ ((burnsideB49_tau w : Matrix (Fin 3) (Fin 3) F).mulVec x) = D.ρ (burnsideB49_tau w) (Φ x) := by
    intro w x
    rw [hΦapp, hΦapp, burnsideB49_tau_mulVec, map_add]
    have h1 : D.ρ (burnsideB49_tau w) (Λhom (x 2)) = Λhom (x 2) + burnsideB49_Dz D z₁ ((x 2) • w) := by
      rw [← hΛD]
      unfold burnsideB49_Dz
      abel
    rw [h1, burnsideB49_Dz_fixed D hQ]
    simp only [burnsideB49_vec3_zero2, burnsideB49_ysub_vec3]
    rw [burnsideB49_Dz_add_arg D hQ]
    abel
  have hΦS : ∀ t ∈ burnsideB49_S1 (F := F), ∀ x,
      Φ (burnsideB49_matEnd t x) = D.ρ t (Φ x) := by
    rintro t ⟨w, M, rfl⟩ x
    rw [burnsideB49_matEnd_apply, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      hΦtau, hΦkap, burnsideB49_rho_mul_apply]
  obtain ⟨Φ', hΦ'q, hΦ'⟩ := burnsideB49_gaschutz_add hA burnsideB49_matEnd D.ρ burnsideB49_S1
    (burnsideB49_odd_index_S1 burnsideB49_even_card) D.q D.hq Φ hΦq hΦS
  exact ⟨Φ', hΦ'q, fun s x => hΦ' s x⟩

end Core3Final

section Trans3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def burnsideB49_slToStated (n : ℕ) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin n) K →* ↥(StatedSL n K) :=
  MonoidHom.codRestrict Matrix.SpecialLinearGroup.toGL (StatedSL n K) (fun s => by
    rw [StatedAPI.statedSL_eq_range_toGL]
    exact ⟨s, rfl⟩)

theorem burnsideB49_slToStated_coe {n : ℕ} {K : Type} [Field K]
    (s : Matrix.SpecialLinearGroup (Fin n) K) :
    (((burnsideB49_slToStated n K s : ↥(StatedSL n K)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = (s : Matrix (Fin n) (Fin n) K) := rfl

theorem burnsideB49_slToStated_surjective (n : ℕ) (K : Type) [Field K] :
    Function.Surjective (burnsideB49_slToStated n K) := by
  rintro ⟨γ, hγ⟩
  rw [StatedAPI.statedSL_eq_range_toGL] at hγ
  obtain ⟨s, hs⟩ := hγ
  exact ⟨s, Subtype.ext hs⟩

theorem burnsideB49_slToStated_injective (n : ℕ) (K : Type) [Field K] :
    Function.Injective (burnsideB49_slToStated n K) := by
  intro s t h
  apply Matrix.SpecialLinearGroup.toGL_injective
  exact congrArg Subtype.val h

variable {V : Type} [CommGroup V]

@[expose] def burnsideB49_addEnd : MulAut V →* AddMonoid.End (Additive V) where
  toFun g := AddMonoidHom.mk' (fun a => Additive.ofMul (g (Additive.toMul a))) (fun a b => by
    simp only [toMul_add, map_mul, ofMul_mul])
  map_one' := AddMonoidHom.ext fun a => rfl
  map_mul' g h := AddMonoidHom.ext fun a => rfl

theorem burnsideB49_addEnd_apply (g : MulAut V) (v : V) :
    burnsideB49_addEnd g (Additive.ofMul v) = Additive.ofMul (g v) := rfl

theorem burnsideB49_additive_exp2 (hV : ∀ v : V, v ^ 2 = 1) (a : Additive V) : a + a = 0 := by
  have := hV (Additive.toMul a)
  rw [sq] at this
  apply Additive.toMul.injective
  rw [toMul_add, this]
  rfl

end Trans3

section Coord3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}

structure burnsideB49_Coord3 (G : Subgroup (MulAut V)) (U : Subgroup V) (K : Type) [Field K]
    (π : ↥(StatedSL 3 K) →* ↥G) where
  σ : Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.SpecialLinearGroup (Fin 3) K
  hσ : (∀ s, σ s = s) ∨
    (∀ s, σ s = CFSG.Quasithin.JonesParshall.invTransposeSL 3 K s)
  qV : V →* Multiplicative (Fin 3 → K)
  hqs : Function.Surjective qV
  hker : ∀ v, qV v = 1 ↔ v ∈ U
  hqeq : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) K) (v : V),
    qV (((π (burnsideB49_slToStated 3 K γ) : ↥G) : MulAut V) v) =
      Multiplicative.ofAdd ((σ γ : Matrix (Fin 3) (Fin 3) K).mulVec
        (Multiplicative.toAdd (qV v)))
  β₀ : ↥U →* Multiplicative (Fin 3 → K)
  hβb : Function.Bijective β₀
  hβe : ∀ (γ : Matrix.SpecialLinearGroup (Fin 3) K) (u : ↥U)
    (hu : ((π (burnsideB49_slToStated 3 K γ) : ↥G) : MulAut V) (u : V) ∈ U),
    β₀ ⟨((π (burnsideB49_slToStated 3 K γ) : ↥G) : MulAut V) (u : V), hu⟩ =
      Multiplicative.ofAdd ((γ : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (β₀ u)))

theorem burnsideB49_sigma_invol (C : burnsideB49_Coord3 G U K π)
    (s : Matrix.SpecialLinearGroup (Fin 3) K) : C.σ (C.σ s) = s := by
  rcases C.hσ with h | h
  · rw [h, h]
  · rw [h, h]
    exact CFSG.Quasithin.JonesParshall.invTransposeFun_invTransposeFun s

open Classical in
@[expose] noncomputable def burnsideB49_Coord3.toCore3 (C : burnsideB49_Coord3 G U K π) :
    burnsideB49_Core3 K (Additive V) where
  ρ := burnsideB49_addEnd.comp (G.subtype.comp (π.comp ((burnsideB49_slToStated 3 K).comp C.σ)))
  q := AddMonoidHom.mk' (fun a => Multiplicative.toAdd (C.qV (Additive.toMul a))) (fun a b => by
    simp only [toMul_add, map_mul, toAdd_mul])
  hq := fun s a => by
    change Multiplicative.toAdd (C.qV (((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V)
      (Additive.toMul a))) = _
    rw [C.hqeq, toAdd_ofAdd, burnsideB49_sigma_invol]
    rfl
  hqs := fun x => by
    obtain ⟨v, hv⟩ := C.hqs (Multiplicative.ofAdd x)
    refine ⟨Additive.ofMul v, ?_⟩
    change Multiplicative.toAdd (C.qV v) = x
    rw [hv]
    rfl
  τ := C.σ
  β := fun a => if h : Additive.toMul a ∈ U then
    Multiplicative.toAdd (C.β₀ ⟨Additive.toMul a, h⟩) else 0
  hβ_add := fun u u' hu hu' => by
    have hu1 : Additive.toMul u ∈ U := (C.hker _).1 hu
    have hu1' : Additive.toMul u' ∈ U := (C.hker _).1 hu'
    have hu2 : Additive.toMul (u + u') ∈ U := by
      rw [toMul_add]
      exact U.mul_mem hu1 hu1'
    rw [dif_pos hu2, dif_pos hu1, dif_pos hu1']
    have : (⟨Additive.toMul (u + u'), hu2⟩ : ↥U) = ⟨Additive.toMul u, hu1⟩ * ⟨Additive.toMul u', hu1'⟩ :=
      Subtype.ext (toMul_add u u')
    rw [this, map_mul, toAdd_mul]
  hβ_inj := fun u u' hu hu' h => by
    have hu1 : Additive.toMul u ∈ U := (C.hker _).1 hu
    have hu1' : Additive.toMul u' ∈ U := (C.hker _).1 hu'
    rw [dif_pos hu1, dif_pos hu1'] at h
    have h2 := Multiplicative.toAdd.injective h
    have h3 := C.hβb.1 h2
    have h4 := congrArg Subtype.val h3
    exact Additive.toMul.injective h4
  hβ_surj := fun x => by
    obtain ⟨u₀, hu₀⟩ := C.hβb.2 (Multiplicative.ofAdd x)
    refine ⟨Additive.ofMul (u₀ : V), ?_, ?_⟩
    · change Multiplicative.toAdd (C.qV (u₀ : V)) = 0
      rw [(C.hker _).2 u₀.2]
      rfl
    · have hm : Additive.toMul (Additive.ofMul (u₀ : V)) ∈ U := u₀.2
      rw [dif_pos hm]
      change Multiplicative.toAdd (C.β₀ ⟨(u₀ : V), hm⟩) = x
      rw [hu₀]
      rfl
  hβ := fun s u hu => by
    have hu1 : Additive.toMul u ∈ U := (C.hker _).1 hu
    have hmem : ((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V) (Additive.toMul u) ∈ U := by
      rw [← C.hker, C.hqeq]
      have : Multiplicative.toAdd (C.qV (Additive.toMul u)) = 0 := by
        rw [(C.hker _).2 hu1]
        rfl
      rw [this, Matrix.mulVec_zero]
      rfl
    have hρ : Additive.toMul (((burnsideB49_addEnd.comp (G.subtype.comp
        (π.comp ((burnsideB49_slToStated 3 K).comp C.σ)))) s) u) =
        ((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V) (Additive.toMul u) := rfl
    have hmem' : Additive.toMul (((burnsideB49_addEnd.comp (G.subtype.comp
        (π.comp ((burnsideB49_slToStated 3 K).comp C.σ)))) s) u) ∈ U := by rw [hρ]; exact hmem
    rw [dif_pos hmem', dif_pos hu1]
    simp only [hρ]
    rw [C.hβe (C.σ s) ⟨Additive.toMul u, hu1⟩ hmem]
    rfl

end Coord3

section Core3Conj

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]

theorem burnsideB49_mulVec_mulVec_sl (g h : Matrix.SpecialLinearGroup (Fin 3) F) (x : Fin 3 → F) :
    (g : Matrix (Fin 3) (Fin 3) F).mulVec ((h : Matrix (Fin 3) (Fin 3) F).mulVec x) =
      ((g * h : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem burnsideB49_mulVec_one_sl (x : Fin 3 → F) :
    ((1 : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec x = x := by
  simp

theorem burnsideB49_mulVec_inj (g : Matrix.SpecialLinearGroup (Fin 3) F) {x y : Fin 3 → F}
    (h : (g : Matrix (Fin 3) (Fin 3) F).mulVec x = (g : Matrix (Fin 3) (Fin 3) F).mulVec y) :
    x = y := by
  have := congrArg (fun z => ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
    Matrix (Fin 3) (Fin 3) F).mulVec z) h
  simp only [burnsideB49_mulVec_mulVec_sl, inv_mul_cancel, burnsideB49_mulVec_one_sl] at this
  exact this

@[expose] def burnsideB49_Core3.conj (D : burnsideB49_Core3 F A)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) : burnsideB49_Core3 F A where
  ρ := D.ρ.comp (MulAut.conj g⁻¹).toMonoidHom
  q := (burnsideB49_matEnd g).comp D.q
  hq := fun s a => by
    change (g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q (D.ρ (g⁻¹ * s * g⁻¹⁻¹) a)) = _
    rw [D.hq, burnsideB49_mulVec_mulVec_sl, inv_inv]
    change _ = (s : Matrix (Fin 3) (Fin 3) F).mulVec ((g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q a))
    rw [burnsideB49_mulVec_mulVec_sl]
    have e : g * (g⁻¹ * s * g) = s * g := by group
    rw [e]
  hqs := fun y => by
    obtain ⟨a, ha⟩ := D.hqs ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F).1.mulVec y)
    refine ⟨a, ?_⟩
    change (g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q a) = y
    rw [ha, burnsideB49_mulVec_mulVec_sl, mul_inv_cancel, burnsideB49_mulVec_one_sl]
  τ := D.τ
  β := fun a => ((D.τ g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (D.β a)
  hβ_add := fun u u' hu hu' => by
    have hu1 : D.q u = 0 := by
      apply burnsideB49_mulVec_inj g
      change (g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q u) = _ at hu
      rw [hu, Matrix.mulVec_zero]
    have hu1' : D.q u' = 0 := by
      apply burnsideB49_mulVec_inj g
      change (g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q u') = _ at hu'
      rw [hu', Matrix.mulVec_zero]
    rw [D.hβ_add u u' hu1 hu1', Matrix.mulVec_add]
  hβ_inj := fun u u' hu hu' h => by
    have hu1 : D.q u = 0 := by
      apply burnsideB49_mulVec_inj g
      change (g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q u) = _ at hu
      rw [hu, Matrix.mulVec_zero]
    have hu1' : D.q u' = 0 := by
      apply burnsideB49_mulVec_inj g
      change (g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q u') = _ at hu'
      rw [hu', Matrix.mulVec_zero]
    apply D.hβ_inj u u' hu1 hu1'
    apply burnsideB49_mulVec_inj (D.τ g)
    exact h
  hβ_surj := fun x => by
    obtain ⟨u, hu, hβu⟩ := D.hβ_surj (((D.τ g)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F).1.mulVec x)
    refine ⟨u, ?_, ?_⟩
    · change (g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q u) = 0
      rw [hu, Matrix.mulVec_zero]
    · change ((D.τ g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (D.β u) = x
      rw [hβu, burnsideB49_mulVec_mulVec_sl, mul_inv_cancel, burnsideB49_mulVec_one_sl]
  hβ := fun s u hu => by
    have hu1 : D.q u = 0 := by
      apply burnsideB49_mulVec_inj g
      change (g : Matrix (Fin 3) (Fin 3) F).mulVec (D.q u) = _ at hu
      rw [hu, Matrix.mulVec_zero]
    change ((D.τ g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
      (D.β (D.ρ (g⁻¹ * s * g⁻¹⁻¹) u)) = _
    rw [D.hβ _ _ hu1, burnsideB49_mulVec_mulVec_sl, inv_inv]
    change _ = ((D.τ s : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
      (((D.τ g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (D.β u))
    rw [burnsideB49_mulVec_mulVec_sl]
    rw [map_mul, map_mul, map_inv]
    have e : D.τ g * ((D.τ g)⁻¹ * D.τ s * D.τ g) = D.τ s * D.τ g := by group
    rw [e]

theorem burnsideB49_core3_conj [Finite F] [CharP F 2] (D : burnsideB49_Core3 F A)
    (g : Matrix.SpecialLinearGroup (Fin 3) F) (hQ : burnsideB49_QuadHyp (D.conj g))
    (hA : ∀ a : A, a + a = 0)
    (hτ : (∀ s, D.τ s = s) ∨ (∀ s, D.τ s = CFSG.Quasithin.JonesParshall.invTransposeSL 3 F s)) :
    ∃ Φ : (Fin 3 → F) →+ A, (∀ x, D.q (Φ x) = x) ∧
      ∀ (s : Matrix.SpecialLinearGroup (Fin 3) F) x,
        Φ ((s : Matrix (Fin 3) (Fin 3) F).mulVec x) = D.ρ s (Φ x) := by
  obtain ⟨Φ', hq', he'⟩ := burnsideB49_core3 (D.conj g) hQ hA hτ
  refine ⟨Φ'.comp (burnsideB49_matEnd g), fun x => ?_, fun s x => ?_⟩
  · apply burnsideB49_mulVec_inj g
    have h := hq' ((g : Matrix (Fin 3) (Fin 3) F).mulVec x)
    exact h
  · have h := he' (g * s * g⁻¹) ((g : Matrix (Fin 3) (Fin 3) F).mulVec x)
    change Φ' ((g : Matrix (Fin 3) (Fin 3) F).mulVec ((s : Matrix (Fin 3) (Fin 3) F).mulVec x)) =
      D.ρ s (Φ' ((g : Matrix (Fin 3) (Fin 3) F).mulVec x))
    rw [burnsideB49_mulVec_mulVec_sl]
    have e1 : g * s = (g * s * g⁻¹) * g := by group
    rw [e1, ← burnsideB49_mulVec_mulVec_sl]
    rw [h]
    change D.ρ (g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹) _ = _
    congr 2
    group

end Core3Conj

section Coord3Nat

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_coord3_nat
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (φ : V ⧸ U ≃* ↥U)
    (hφ : ∀ g ∈ G, ∀ v : V, ((φ (QuotientGroup.mk ((g : MulAut V) v)) : ↥U) : V) =
      (g : MulAut V) ((φ (QuotientGroup.mk v) : ↥U) : V)) :
    Nonempty (burnsideB49_Coord3 G U K π) := by
  obtain ⟨β₀, hβb, hβe⟩ := burnsideB49_coords hreal
  refine ⟨{
    σ := MonoidHom.id _
    hσ := Or.inl (fun s => rfl)
    qV := β₀.comp (φ.toMonoidHom.comp (QuotientGroup.mk' U))
    hqs := ?_
    hker := ?_
    hqeq := ?_
    β₀ := β₀
    hβb := hβb
    hβe := ?_ }⟩
  · intro y
    obtain ⟨u, hu⟩ := hβb.2 y
    obtain ⟨x, hx⟩ := φ.surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨v, by simp [hx, hu]⟩
  · intro v
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    constructor
    · intro h
      have h1 : φ (QuotientGroup.mk v) = 1 := by
        apply hβb.1
        rw [h, map_one]
      have h2 : (QuotientGroup.mk v : V ⧸ U) = 1 := by
        apply φ.injective
        rw [h1, map_one]
      exact (QuotientGroup.eq_one_iff v).1 h2
    · intro hv
      have h2 : (QuotientGroup.mk v : V ⧸ U) = 1 := (QuotientGroup.eq_one_iff v).2 hv
      rw [h2, map_one, map_one]
  · intro γ v
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
      MonoidHom.id_apply]
    have hu : ((π (burnsideB49_slToStated 3 K γ) : ↥G) : MulAut V) ((φ (QuotientGroup.mk v) : ↥U) : V) ∈ U := by
      rw [← hφ _ (π (burnsideB49_slToStated 3 K γ)).2 v]
      exact (φ _).2
    have h1 : φ (QuotientGroup.mk (((π (burnsideB49_slToStated 3 K γ) : ↥G) : MulAut V) v)) =
        ⟨((π (burnsideB49_slToStated 3 K γ) : ↥G) : MulAut V) ((φ (QuotientGroup.mk v) : ↥U) : V), hu⟩ :=
      Subtype.ext (hφ _ (π (burnsideB49_slToStated 3 K γ)).2 v)
    rw [h1]
    exact hβe (burnsideB49_slToStated 3 K γ) _ hu
  · intro γ u hu
    exact hβe (burnsideB49_slToStated 3 K γ) u hu

end Coord3Nat

section SplitsSec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_splits_of_core3 (C : burnsideB49_Coord3 G U K π)
    (hπ : ∀ g : ↥G, ∃ γ, π γ = g)
    (Φ : (Fin 3 → K) →+ Additive V) (hΦq : ∀ x, C.toCore3.q (Φ x) = x)
    (hΦ : ∀ (s : Matrix.SpecialLinearGroup (Fin 3) K) x,
      Φ ((s : Matrix (Fin 3) (Fin 3) K).mulVec x) = C.toCore3.ρ s (Φ x)) :
    CFSG.ASVolI.ChB.SplitsOver G U := by
  let U' : Subgroup V :=
    { carrier := {v | ∃ x, Φ x = Additive.ofMul v}
      one_mem' := ⟨0, by rw [map_zero]; rfl⟩
      mul_mem' := by
        rintro a b ⟨x, hx⟩ ⟨y, hy⟩
        exact ⟨x + y, by rw [map_add, hx, hy]; rfl⟩
      inv_mem' := by
        rintro a ⟨x, hx⟩
        exact ⟨-x, by rw [map_neg, hx]; rfl⟩ }
  have hqU : ∀ v : V, C.toCore3.q (Additive.ofMul v) = 0 ↔ v ∈ U := fun v => by
    change Multiplicative.toAdd (C.qV v) = 0 ↔ v ∈ U
    rw [← C.hker]
    constructor
    · intro h
      exact Multiplicative.toAdd.injective h
    · intro h
      rw [h]
      rfl
  refine ⟨U', ?_, ?_, ?_⟩
  · rintro g hg u ⟨x, hx⟩
    obtain ⟨γ, hγ⟩ := hπ ⟨g, hg⟩
    obtain ⟨s', rfl⟩ := burnsideB49_slToStated_surjective 3 K γ
    refine ⟨((C.σ s' : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K).mulVec x, ?_⟩
    rw [hΦ, hx]
    change Additive.ofMul (((π (burnsideB49_slToStated 3 K (C.σ (C.σ s'))) : ↥G) : MulAut V) u) = _
    rw [burnsideB49_sigma_invol, hγ]
  · apply le_antisymm _ bot_le
    rintro v ⟨hvU, ⟨x, hx⟩⟩
    have h1 : C.toCore3.q (Φ x) = 0 := by
      rw [hx]
      exact (hqU v).2 hvU
    have h2 : x = 0 := by
      rw [← hΦq x]
      exact h1
    rw [Subgroup.mem_bot]
    have h3 : Φ x = 0 := by rw [h2, map_zero]
    rw [hx] at h3
    exact ofMul_eq_zero.1 h3
  · rw [eq_top_iff]
    intro v _
    have hw : Additive.toMul (Φ (C.toCore3.q (Additive.ofMul v))) ∈ U' :=
      ⟨C.toCore3.q (Additive.ofMul v), by rw [ofMul_toMul]⟩
    have hvw : v * (Additive.toMul (Φ (C.toCore3.q (Additive.ofMul v))))⁻¹ ∈ U := by
      rw [← hqU]
      have : Additive.ofMul (v * (Additive.toMul (Φ (C.toCore3.q (Additive.ofMul v))))⁻¹) =
          Additive.ofMul v - Φ (C.toCore3.q (Additive.ofMul v)) := by
        rw [ofMul_mul, ofMul_inv, ofMul_toMul, sub_eq_add_neg]
      rw [this, map_sub, hΦq, sub_self]
    have hv : v = (v * (Additive.toMul (Φ (C.toCore3.q (Additive.ofMul v))))⁻¹) *
        Additive.toMul (Φ (C.toCore3.q (Additive.ofMul v))) := by
      rw [inv_mul_cancel_right]
    rw [hv]
    exact Subgroup.mul_mem_sup hvw hw

end SplitsSec

section TraceForm

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem burnsideB49_exists_tr [CharP K 2] : ∃ t : K →+ ZMod 2, t 1 ≠ 0 := by
  have hV : ∀ x : Multiplicative K, x ^ 2 = 1 := fun x => by
    rw [sq]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul]
    exact CharTwo.add_self_eq_zero _
  have hx : (Multiplicative.ofAdd (1 : K)) ≠ 1 := by
    intro h
    exact one_ne_zero (Multiplicative.ofAdd.injective h)
  obtain ⟨f, hf⟩ := CFSG.Quasithin.exists_dualChar_ne_one hV hx
  refine ⟨AddMonoidHom.mk' (fun a => Multiplicative.toAdd (f (Multiplicative.ofAdd a)))
    (fun a b => by
      rw [ofAdd_add, map_mul, toAdd_mul]), ?_⟩
  intro h
  apply hf
  have : Multiplicative.toAdd (f (Multiplicative.ofAdd (1 : K))) = 0 := h
  exact Multiplicative.toAdd.injective this

@[expose] def burnsideB49_pair (t : K →+ ZMod 2) (y : Fin 3 → K) :
    Multiplicative (Fin 3 → K) →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (t (y ⬝ᵥ Multiplicative.toAdd x))
  map_one' := by simp
  map_mul' a b := by
    simp [dotProduct_add, map_add]

theorem burnsideB49_pair_apply (t : K →+ ZMod 2) (y : Fin 3 → K) (x : Multiplicative (Fin 3 → K)) :
    burnsideB49_pair t y x = Multiplicative.ofAdd (t (y ⬝ᵥ Multiplicative.toAdd x)) := rfl

@[expose] def burnsideB49_pairHom (t : K →+ ZMod 2) :
    Multiplicative (Fin 3 → K) →* CFSG.Quasithin.DualGrp (Multiplicative (Fin 3 → K)) where
  toFun y := burnsideB49_pair t (Multiplicative.toAdd y)
  map_one' := by
    apply MonoidHom.ext
    intro x
    change Multiplicative.ofAdd (t ((0 : Fin 3 → K) ⬝ᵥ Multiplicative.toAdd x)) = 1
    simp
  map_mul' a b := by
    apply MonoidHom.ext
    intro x
    change Multiplicative.ofAdd (t ((Multiplicative.toAdd a + Multiplicative.toAdd b) ⬝ᵥ
      Multiplicative.toAdd x)) = Multiplicative.ofAdd (t (Multiplicative.toAdd a ⬝ᵥ Multiplicative.toAdd x)) *
        Multiplicative.ofAdd (t (Multiplicative.toAdd b ⬝ᵥ Multiplicative.toAdd x))
    rw [add_dotProduct, map_add, ofAdd_add]

theorem burnsideB49_pairHom_injective (t : K →+ ZMod 2) (ht : t 1 ≠ 0) :
    Function.Injective (burnsideB49_pairHom t) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h : ∀ x : Multiplicative (Fin 3 → K), t (Multiplicative.toAdd y ⬝ᵥ Multiplicative.toAdd x) = 0 := by
    intro x
    have := congrArg (fun χ : CFSG.Quasithin.DualGrp (Multiplicative (Fin 3 → K)) => χ x) hy
    have h2 : Multiplicative.ofAdd (t (Multiplicative.toAdd y ⬝ᵥ Multiplicative.toAdd x)) = 1 := this
    exact Multiplicative.ofAdd.injective h2
  have hy0 : Multiplicative.toAdd y = 0 := by
    funext i
    by_contra hi
    have hi' : Multiplicative.toAdd y i ≠ 0 := hi
    have := h (Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd y i)⁻¹))
    rw [toAdd_ofAdd] at this
    have h3 : Multiplicative.toAdd y ⬝ᵥ Pi.single i (Multiplicative.toAdd y i)⁻¹ = 1 := by
      rw [dotProduct_single]
      exact mul_inv_cancel₀ hi'
    rw [h3] at this
    exact ht this
  apply Multiplicative.toAdd.injective
  rw [hy0]
  rfl

theorem burnsideB49_pairHom_bijective [Finite K] [CharP K 2] (t : K →+ ZMod 2) (ht : t 1 ≠ 0) :
    Function.Bijective (burnsideB49_pairHom t) := by
  have hV : ∀ x : Multiplicative (Fin 3 → K), x ^ 2 = 1 := fun x => by
    rw [sq]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul]
    funext i
    simp [CharTwo.add_self_eq_zero]
  have hinj := burnsideB49_pairHom_injective t ht
  refine (Nat.bijective_iff_injective_and_card _).2 ⟨hinj, ?_⟩
  rw [CFSG.Quasithin.card_dualGrp hV]

end TraceForm

section DualCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

@[expose] def burnsideB49_dualCongr {A B : Type*} [CommGroup A] [CommGroup B] (e : A ≃* B) :
    CFSG.Quasithin.DualGrp B ≃* CFSG.Quasithin.DualGrp A where
  toFun χ := χ.comp e.toMonoidHom
  invFun χ := χ.comp e.symm.toMonoidHom
  left_inv χ := by
    apply MonoidHom.ext
    intro b
    simp
  right_inv χ := by
    apply MonoidHom.ext
    intro a
    simp
  map_mul' χ ψ := by
    apply MonoidHom.ext
    intro a
    rfl

variable {K : Type} [Field K] [Finite K] [CharP K 2] {U : Type} [CommGroup U]

@[expose] noncomputable def burnsideB49_traceEquiv (t : K →+ ZMod 2) (ht : t 1 ≠ 0)
    (bI : U ≃* Multiplicative (Fin 3 → K)) :
    CFSG.Quasithin.DualGrp U ≃* Multiplicative (Fin 3 → K) :=
  (burnsideB49_dualCongr bI).symm.trans
    (MulEquiv.ofBijective (burnsideB49_pairHom t) (burnsideB49_pairHom_bijective t ht)).symm

theorem burnsideB49_traceEquiv_symm_apply (t : K →+ ZMod 2) (ht : t 1 ≠ 0)
    (bI : U ≃* Multiplicative (Fin 3 → K)) (z : Multiplicative (Fin 3 → K)) (u : U) :
    ((burnsideB49_traceEquiv t ht bI).symm z) u =
      Multiplicative.ofAdd (t (Multiplicative.toAdd z ⬝ᵥ Multiplicative.toAdd (bI u))) := by
  change ((burnsideB49_dualCongr bI) ((MulEquiv.ofBijective (burnsideB49_pairHom t)
    (burnsideB49_pairHom_bijective t ht)) z)) u = _
  rfl

theorem burnsideB49_traceEquiv_spec (t : K →+ ZMod 2) (ht : t 1 ≠ 0)
    (bI : U ≃* Multiplicative (Fin 3 → K)) (χ : CFSG.Quasithin.DualGrp U) (u : U) :
    χ u = Multiplicative.ofAdd (t (Multiplicative.toAdd (burnsideB49_traceEquiv t ht bI χ) ⬝ᵥ
      Multiplicative.toAdd (bI u))) := by
  rw [← burnsideB49_traceEquiv_symm_apply t ht bI, MulEquiv.symm_apply_apply]

theorem burnsideB49_traceEquiv_unique (t : K →+ ZMod 2) (ht : t 1 ≠ 0)
    (bI : U ≃* Multiplicative (Fin 3 → K)) (χ : CFSG.Quasithin.DualGrp U) (y : Fin 3 → K)
    (h : ∀ u, χ u = Multiplicative.ofAdd (t (y ⬝ᵥ Multiplicative.toAdd (bI u)))) :
    burnsideB49_traceEquiv t ht bI χ = Multiplicative.ofAdd y := by
  have : χ = (burnsideB49_traceEquiv t ht bI).symm (Multiplicative.ofAdd y) := by
    apply MonoidHom.ext
    intro u
    rw [burnsideB49_traceEquiv_symm_apply, h u, toAdd_ofAdd]
  rw [this, MulEquiv.apply_symm_apply]

end DualCoord

section Coord3Dual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_coord3_dual
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (φ : V ⧸ U ≃* CFSG.Quasithin.DualGrp ↥U)
    (hφ : ∀ g ∈ G, ∀ v : V, ∀ u u' : ↥U, (g : MulAut V) (u' : V) = (u : V) →
      (φ (QuotientGroup.mk ((g : MulAut V) v))) u = (φ (QuotientGroup.mk v)) u') :
    Nonempty (burnsideB49_Coord3 G U K π) := by
  obtain ⟨β₀, hβb, hβe⟩ := burnsideB49_coords hreal
  obtain ⟨t, ht⟩ := burnsideB49_exists_tr (K := K)
  let bI : ↥U ≃* Multiplicative (Fin 3 → K) := MulEquiv.ofBijective β₀ hβb
  let Ψ := burnsideB49_traceEquiv t ht bI
  let θ : V ⧸ U →* Multiplicative (Fin 3 → K) :=
    MonoidHom.mk' (fun x => Ψ (φ x)) (fun x y => by rw [map_mul φ, map_mul Ψ])
  have hθb : Function.Bijective θ := Ψ.bijective.comp φ.bijective
  let θe : V ⧸ U ≃* Multiplicative (Fin 3 → K) := MulEquiv.ofBijective θ hθb
  have hGU : ∀ x ∈ G, ∀ u ∈ U, (x : MulAut V) u ∈ U := fun g hg u hu =>
    hreal.2.2.2.1 ⟨g, hg⟩ u hu
  refine ⟨{
    σ := (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom
    hσ := Or.inr (fun s => rfl)
    qV := θ.comp (QuotientGroup.mk' U)
    hqs := ?_
    hker := ?_
    hqeq := ?_
    β₀ := β₀
    hβb := hβb
    hβe := ?_ }⟩
  · intro y
    obtain ⟨x, hx⟩ := hθb.2 y
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨v, hx⟩
  · intro v
    show θ (QuotientGroup.mk v) = 1 ↔ v ∈ U
    constructor
    · intro h
      have h2 : (QuotientGroup.mk v : V ⧸ U) = 1 := by
        apply θe.injective
        change θ (QuotientGroup.mk v) = θ 1
        rw [h, map_one]
      exact (QuotientGroup.eq_one_iff v).1 h2
    · intro hv
      have h2 : (QuotientGroup.mk v : V ⧸ U) = 1 := (QuotientGroup.eq_one_iff v).2 hv
      rw [h2, map_one]
  · intro γ v
    set g : ↥G := π (burnsideB49_slToStated 3 K γ) with hg
    show Ψ (φ (QuotientGroup.mk (((g : ↥G) : MulAut V) v))) = Multiplicative.ofAdd
      ((((CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom γ :
        Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec
        (Multiplicative.toAdd (Ψ (φ (QuotientGroup.mk v)))))
    apply burnsideB49_traceEquiv_unique t ht bI
    intro u
    obtain ⟨u', hu'⟩ : ∃ u' : ↥U, ((g : ↥G) : MulAut V) (u' : V) = (u : V) :=
      ⟨⟨((g : ↥G) : MulAut V)⁻¹ (u : V), hGU _ (G.inv_mem g.2) _ u.2⟩, by
        change ((g : ↥G) : MulAut V) (((g : ↥G) : MulAut V)⁻¹ (u : V)) = _
        rw [← MulAut.mul_apply, mul_inv_cancel]
        rfl⟩
    rw [hφ g g.2 v u u' hu', burnsideB49_traceEquiv_spec t ht bI (φ (QuotientGroup.mk v)) u']
    have hu1 : β₀ u = Multiplicative.ofAdd ((γ : Matrix (Fin 3) (Fin 3) K).mulVec
        (Multiplicative.toAdd (β₀ u'))) := by
      have hmem : ((g : ↥G) : MulAut V) (u' : V) ∈ U := hu' ▸ u.2
      have := hβe (burnsideB49_slToStated 3 K γ) u' hmem
      have h3 : (⟨((g : ↥G) : MulAut V) (u' : V), hmem⟩ : ↥U) = u := Subtype.ext hu'
      rw [h3] at this
      exact this
    have hu2 : Multiplicative.toAdd (β₀ u') = ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (β₀ u)) := by
      rw [hu1, toAdd_ofAdd, burnsideB49_mulVec_mulVec_sl, inv_mul_cancel, burnsideB49_mulVec_one_sl]
    have hbI' : Multiplicative.toAdd (bI u') = Multiplicative.toAdd (β₀ u') := rfl
    have hbI'' : Multiplicative.toAdd (bI u) = Multiplicative.toAdd (β₀ u) := rfl
    rw [hbI', hbI'', hu2]
    have hσ : ((CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom γ :
        Matrix.SpecialLinearGroup (Fin 3) K).1 =
        Matrix.transpose ((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      CFSG.Quasithin.JonesParshall.invTransposeSL_coe 3 K γ
    have hdot : ∀ (Y x : Fin 3 → K), Y ⬝ᵥ (((γ⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K).mulVec x) =
        (((CFSG.Quasithin.JonesParshall.invTransposeSL 3 K).toMonoidHom γ :
          Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec Y ⬝ᵥ x := by
      intro Y x
      rw [hσ, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [hdot]
  · intro γ u hu
    exact hβe (burnsideB49_slToStated 3 K γ) u hu

end Coord3Dual

section Three

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_coord3_exists
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U) :
    Nonempty (burnsideB49_Coord3 G U K π) := by
  rcases hquot with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact burnsideB49_coord3_nat hreal φ (fun g hg v => by
      have := hφ g hg v
      rw [this])
  · exact burnsideB49_coord3_dual hreal φ hφ

theorem burnsideB49_split_of_quad (hV : ∀ v : V, v ^ 2 = 1) (C : burnsideB49_Coord3 G U K π)
    (hπ : ∀ g : ↥G, ∃ γ, π γ = g) (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (hQ : burnsideB49_QuadHyp (C.toCore3.conj g)) : CFSG.ASVolI.ChB.SplitsOver G U := by
  obtain ⟨Φ, hΦq, hΦ⟩ := burnsideB49_core3_conj C.toCore3 g hQ (burnsideB49_additive_exp2 hV)
    C.hσ
  exact burnsideB49_splits_of_core3 C hπ Φ hΦq hΦ

end Three

section Bridge

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}

@[expose] def burnsideB49_rhoHat (C : burnsideB49_Coord3 G U K π) :
    Matrix.SpecialLinearGroup (Fin 3) K →* MulAut V :=
  G.subtype.comp (π.comp ((burnsideB49_slToStated 3 K).comp C.σ))

theorem burnsideB49_rhoHat_apply (C : burnsideB49_Coord3 G U K π)
    (s : Matrix.SpecialLinearGroup (Fin 3) K) :
    burnsideB49_rhoHat C s = ((π (burnsideB49_slToStated 3 K (C.σ s)) : ↥G) : MulAut V) := rfl

theorem burnsideB49_rhoHat_mem (C : burnsideB49_Coord3 G U K π)
    (s : Matrix.SpecialLinearGroup (Fin 3) K) : burnsideB49_rhoHat C s ∈ G :=
  (π (burnsideB49_slToStated 3 K (C.σ s))).2

theorem burnsideB49_qV_rhoHat (C : burnsideB49_Coord3 G U K π)
    (s : Matrix.SpecialLinearGroup (Fin 3) K) (v : V) :
    C.qV (burnsideB49_rhoHat C s v) = Multiplicative.ofAdd
      ((s : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (C.qV v))) := by
  have := C.hqeq (C.σ s) v
  rw [burnsideB49_sigma_invol] at this
  exact this

theorem burnsideB49_rhoHat_injective (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π) :
    Function.Injective (burnsideB49_rhoHat C) := by
  intro s t h
  have h1 : π (burnsideB49_slToStated 3 K (C.σ s)) = π (burnsideB49_slToStated 3 K (C.σ t)) :=
    Subtype.ext h
  have h2 := burnsideB49_pi_injective hreal h1
  have h3 := burnsideB49_slToStated_injective 3 K h2
  have := congrArg C.σ h3
  rwa [burnsideB49_sigma_invol, burnsideB49_sigma_invol] at this

theorem burnsideB49_rhoHat_surj (C : burnsideB49_Coord3 G U K π)
    (hπ : ∀ g : ↥G, ∃ γ, π γ = g) (e : MulAut V) (he : e ∈ G) :
    ∃ s, burnsideB49_rhoHat C s = e := by
  obtain ⟨γ, hγ⟩ := hπ ⟨e, he⟩
  obtain ⟨s', rfl⟩ := burnsideB49_slToStated_surjective 3 K γ
  refine ⟨C.σ s', ?_⟩
  rw [burnsideB49_rhoHat_apply, burnsideB49_sigma_invol, hγ]

theorem burnsideB49_axisPre_rhoHat (C : burnsideB49_Coord3 G U K π)
    (s : Matrix.SpecialLinearGroup (Fin 3) K) :
    CFSG.ASVolI.ChB.axisPre U (burnsideB49_rhoHat C s) =
      {v | (s : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (C.qV v)) =
        Multiplicative.toAdd (C.qV v)} := by
  ext v
  simp only [CFSG.ASVolI.ChB.axisPre, Set.mem_setOf_eq]
  rw [← C.hker, map_mul, map_inv, burnsideB49_qV_rhoHat, mul_inv_eq_one]
  constructor
  · intro h
    exact Multiplicative.ofAdd.injective h
  · intro h
    rw [h]
    exact ofAdd_toAdd _

end Bridge

section CardRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_card_sup_ker (C : burnsideB49_Coord3 G U K π) (H : Subgroup V) :
    Nat.card ↥(H ⊔ U) = Nat.card ↥U * Nat.card ↥(H.map C.qV) := by
  set H' : Subgroup V := H ⊔ U with hH'
  have hUH : U ≤ H' := le_sup_right
  let f : ↥H' →* Multiplicative (Fin 3 → K) := C.qV.comp H'.subtype
  have h1 := Subgroup.card_ker_mul_card_range f
  have hker : f.ker = U.subgroupOf H' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact C.hker _
  have hker2 : Nat.card f.ker = Nat.card ↥U := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUH).toEquiv
  have hrange : f.range = H.map C.qV := by
    ext y
    simp only [MonoidHom.mem_range, Subgroup.mem_map, f, MonoidHom.comp_apply,
      Subgroup.subtype_apply]
    constructor
    · rintro ⟨⟨x, hx⟩, rfl⟩
      rw [hH', Subgroup.mem_sup] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      refine ⟨a, ha, ?_⟩
      rw [map_mul, (C.hker b).2 hb, mul_one]
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, Subgroup.mem_sup_left ha⟩, rfl⟩
  rw [← h1, hker2, hrange]

@[expose] def burnsideB49_Te (e : MulAut V) : V →* V :=
  MonoidHom.mk' (fun v => e v * v⁻¹) (fun a b => by
    rw [map_mul, mul_inv, mul_mul_mul_comm])

theorem burnsideB49_Te_apply (e : MulAut V) (v : V) : burnsideB49_Te e v = e v * v⁻¹ := rfl

@[expose] def burnsideB49_Wn (s : Matrix.SpecialLinearGroup (Fin 3) K) : Submodule K (Fin 3 → K) :=
  LinearMap.range (Matrix.mulVecLin ((s : Matrix (Fin 3) (Fin 3) K) - 1))

theorem burnsideB49_mem_Wn (s : Matrix.SpecialLinearGroup (Fin 3) K) (w : Fin 3 → K) :
    w ∈ burnsideB49_Wn s ↔ ∃ y, (s : Matrix (Fin 3) (Fin 3) K).mulVec y - y = w := by
  unfold burnsideB49_Wn
  rw [LinearMap.mem_range]
  simp [Matrix.sub_mulVec]

theorem burnsideB49_map_Te (C : burnsideB49_Coord3 G U K π) (s : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((burnsideB49_Te (burnsideB49_rhoHat C s)).range.map C.qV : Set (Multiplicative (Fin 3 → K))) =
      Multiplicative.ofAdd '' (burnsideB49_Wn s : Set (Fin 3 → K)) := by
  ext m
  simp only [SetLike.mem_coe, Subgroup.mem_map, MonoidHom.mem_range, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨v, rfl⟩, rfl⟩
    refine ⟨(s : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (C.qV v)) -
      Multiplicative.toAdd (C.qV v), (burnsideB49_mem_Wn s _).2 ⟨_, rfl⟩, ?_⟩
    rw [burnsideB49_Te_apply, map_mul, map_inv, burnsideB49_qV_rhoHat, ofAdd_sub]
    rw [div_eq_mul_inv, ofAdd_toAdd]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, rfl⟩ := (burnsideB49_mem_Wn s w).1 hw
    obtain ⟨v, hv⟩ := C.hqs (Multiplicative.ofAdd y)
    refine ⟨_, ⟨v, rfl⟩, ?_⟩
    rw [burnsideB49_Te_apply, map_mul, map_inv, burnsideB49_qV_rhoHat, hv, ofAdd_sub, toAdd_ofAdd]
    rw [div_eq_mul_inv]

theorem burnsideB49_card_Wn (C : burnsideB49_Coord3 G U K π) (s : Matrix.SpecialLinearGroup (Fin 3) K) :
    Nat.card ↥((burnsideB49_Te (burnsideB49_rhoHat C s)).range.map C.qV) =
      Nat.card ↥(burnsideB49_Wn s) := by
  have h := burnsideB49_map_Te C s
  have h2 : Nat.card ↥((burnsideB49_Te (burnsideB49_rhoHat C s)).range.map C.qV) =
      Nat.card ↥(((burnsideB49_Te (burnsideB49_rhoHat C s)).range.map C.qV :
        Subgroup (Multiplicative (Fin 3 → K))) : Set (Multiplicative (Fin 3 → K))) := rfl
  rw [h2, h, Nat.card_image_of_injective Multiplicative.ofAdd.injective]
  rfl

end CardRank

section RankOne3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K]

theorem burnsideB49_det_rank_one (M : Matrix (Fin 3) (Fin 3) K) (u r : Fin 3 → K)
    (h : ∀ x, M.mulVec x = x + (r ⬝ᵥ x) • u) : M.det = 1 + r ⬝ᵥ u := by
  have hM : M = 1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit r := by
    ext i j
    have := congrFun (h (Pi.single j 1)) i
    simp [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, Matrix.mul_apply,
      Matrix.replicateCol, Matrix.replicateRow] at this ⊢
    rw [this]
    ring
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]

theorem burnsideB49_rank_one_of_card (s : Matrix.SpecialLinearGroup (Fin 3) K) (hs : s ≠ 1)
    (hcard : Nat.card ↥(burnsideB49_Wn s) ≤ Nat.card K) :
    ∃ u r : Fin 3 → K, u ≠ 0 ∧ r ≠ 0 ∧
      ∀ x, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x + (r ⬝ᵥ x) • u := by
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hpow := Module.natCard_eq_pow_finrank (K := K) (V := ↥(burnsideB49_Wn s))
  have hle : Module.finrank K ↥(burnsideB49_Wn s) ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have : Nat.card K ^ 2 ≤ Nat.card K ^ Module.finrank K ↥(burnsideB49_Wn s) :=
      Nat.pow_le_pow_right (by omega) hcon
    rw [← hpow] at this
    nlinarith
  have hne : ∃ y, (s : Matrix (Fin 3) (Fin 3) K).mulVec y ≠ y := by
    by_contra hcon
    push_neg at hcon
    apply hs
    apply Subtype.ext
    exact burnsideB49_eq_one_of_mulVec hcon
  obtain ⟨y, hy⟩ := hne
  have hge : 1 ≤ Module.finrank K ↥(burnsideB49_Wn s) := by
    by_contra hcon
    have h0 : Module.finrank K ↥(burnsideB49_Wn s) = 0 := by omega
    have hbot : burnsideB49_Wn s = ⊥ := Submodule.finrank_eq_zero.1 h0
    have hmem : (s : Matrix (Fin 3) (Fin 3) K).mulVec y - y ∈ burnsideB49_Wn s :=
      (burnsideB49_mem_Wn s _).2 ⟨y, rfl⟩
    rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hy hmem
  have hfr : Module.finrank K ↥(burnsideB49_Wn s) = 1 := le_antisymm hle hge
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hfr
  set u : Fin 3 → K := (v : Fin 3 → K) with hu
  have hu0 : u ≠ 0 := fun h => hv0 (Subtype.ext h)
  have hspan : ∀ x, ∃ c : K, c • u = (s : Matrix (Fin 3) (Fin 3) K).mulVec x - x := by
    intro x
    obtain ⟨c, hc⟩ := hv ⟨_, (burnsideB49_mem_Wn s _).2 ⟨x, rfl⟩⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (funext h)
  let r : Fin 3 → K := fun j => ((s : Matrix (Fin 3) (Fin 3) K) i₀ j - (1 : Matrix (Fin 3) (Fin 3) K) i₀ j) / u i₀
  have hx : ∀ x, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x + (r ⬝ᵥ x) • u := by
    intro x
    obtain ⟨c, hc⟩ := hspan x
    have h1 := congrFun hc i₀
    have h2 : (s : Matrix (Fin 3) (Fin 3) K).mulVec x i₀ - x i₀ = u i₀ * (r ⬝ᵥ x) := by
      simp only [r, dotProduct, Matrix.mulVec]
      rw [Finset.mul_sum]
      have : x i₀ = ∑ j, (1 : Matrix (Fin 3) (Fin 3) K) i₀ j * x j := by
        simp [Matrix.one_apply]
      rw [this, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    have h3 : c = r ⬝ᵥ x := by
      have : c * u i₀ = (r ⬝ᵥ x) * u i₀ := by
        simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h1
        rw [h1, h2]
        ring
      exact mul_right_cancel₀ hi₀ this
    rw [← h3, hc]
    abel
  refine ⟨u, r, hu0, ?_, hx⟩
  intro hr
  apply hs
  apply Subtype.ext
  apply burnsideB49_eq_one_of_mulVec
  intro x
  rw [hx, hr]
  simp

end RankOne3

section TransvRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_transv_rank (C : burnsideB49_Coord3 G U K π) {f : ℕ} (hf : Nat.card K = 2 ^ f)
    (s : Matrix.SpecialLinearGroup (Fin 3) K) (hs : s ≠ 1)
    (h : CFSG.ASVolI.ChB.IsTransvOnQuot U f (burnsideB49_rhoHat C s)) :
    ∃ u r : Fin 3 → K, u ≠ 0 ∧ r ≠ 0 ∧
      (∀ x, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x + (r ⬝ᵥ x) • u) ∧ r ⬝ᵥ u = 0 := by
  set e := burnsideB49_rhoHat C s with he
  have hRe : (burnsideB49_Te e).range ≤ CFSG.Quasithin.commV (Subgroup.zpowers e) := by
    rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, v, rfl⟩
  have h1 : Nat.card ↥((burnsideB49_Te e).range ⊔ U) ≤
      Nat.card ↥(CFSG.Quasithin.commV (Subgroup.zpowers e) ⊔ U) :=
    Subgroup.card_le_of_le (sup_le_sup_right hRe U)
  unfold CFSG.ASVolI.ChB.IsTransvOnQuot at h
  rw [h, burnsideB49_card_sup_ker C, burnsideB49_card_Wn C s] at h1
  have hU : 0 < Nat.card ↥U := Nat.card_pos
  have hcard : Nat.card ↥(burnsideB49_Wn s) ≤ Nat.card K := by
    rw [hf]
    exact Nat.le_of_mul_le_mul_left h1 hU
  obtain ⟨u, r, hu, hr, hx⟩ := burnsideB49_rank_one_of_card s hs hcard
  refine ⟨u, r, hu, hr, hx, ?_⟩
  have hdet := burnsideB49_det_rank_one (s : Matrix (Fin 3) (Fin 3) K) u r hx
  rw [s.2] at hdet
  have : r ⬝ᵥ u = 0 := by
    have h2 : (1 : K) + 0 = 1 + r ⬝ᵥ u := by rw [add_zero]; exact hdet
    exact (add_left_cancel h2).symm
  exact this

theorem burnsideB49_quad_R (C : burnsideB49_Coord3 G U K π) (E : Subgroup (MulAut V))
    (hq : CFSG.Quasithin.IsQuadratic E) (s s' : Matrix.SpecialLinearGroup (Fin 3) K)
    (hs : burnsideB49_rhoHat C s ∈ E) (hs' : burnsideB49_rhoHat C s' ∈ E) (a : Additive V) :
    C.toCore3.ρ s' (C.toCore3.ρ s a - a) = C.toCore3.ρ s a - a := by
  set v := Additive.toMul a with hv
  have hw : burnsideB49_rhoHat C s v * v⁻¹ ∈ CFSG.Quasithin.commV E :=
    Subgroup.subset_closure ⟨burnsideB49_rhoHat C s, hs, v, rfl⟩
  have h := (CFSG.Quasithin.mem_fixV.1 (hq hw)) (burnsideB49_rhoHat C s') hs'
  apply Additive.toMul.injective
  have e1 : Additive.toMul (C.toCore3.ρ s a - a) = burnsideB49_rhoHat C s v * v⁻¹ := by
    rw [toMul_sub, div_eq_mul_inv]
    rfl
  have e2 : Additive.toMul (C.toCore3.ρ s' (C.toCore3.ρ s a - a)) =
      burnsideB49_rhoHat C s' (Additive.toMul (C.toCore3.ρ s a - a)) := rfl
  rw [e2, e1, h]

@[expose] def burnsideB49_Etil (C : burnsideB49_Coord3 G U K π) (E : Subgroup (MulAut V)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
  E.comap (burnsideB49_rhoHat C)

theorem burnsideB49_card_Etil (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (E : Subgroup (MulAut V)) (hEG : E ≤ G) :
    Nat.card ↥(burnsideB49_Etil C E) = Nat.card ↥E := by
  apply Nat.card_congr
  refine Equiv.ofBijective (fun s => ⟨burnsideB49_rhoHat C s.1, s.2⟩) ⟨?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (Subtype.val : ↥E → MulAut V) hab
    exact Subtype.ext (burnsideB49_rhoHat_injective C hreal h1)
  · rintro ⟨e, he⟩
    obtain ⟨s, hs⟩ := burnsideB49_rhoHat_surj C hreal.1 e (hEG he)
    exact ⟨⟨s, by rw [burnsideB49_Etil, Subgroup.mem_comap, hs]; exact he⟩, Subtype.ext hs⟩

end TransvRank

section Normalize

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem burnsideB49_sl_ext (a b : Matrix.SpecialLinearGroup (Fin 3) K)
    (h : ∀ x, (a : Matrix (Fin 3) (Fin 3) K).mulVec x = (b : Matrix (Fin 3) (Fin 3) K).mulVec x) :
    a = b := by
  apply Subtype.ext
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem burnsideB49_exists_row (r : Fin 3 → K) (hr : r ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K, ∀ j, (g : Matrix (Fin 3) (Fin 3) K) 2 j = r j := by
  by_cases h2 : r 2 = 0
  · by_cases h1 : r 1 = 0
    · have h0 : r 0 ≠ 0 := by
        intro h0
        apply hr
        funext i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
      refine ⟨⟨!![0, (r 0)⁻¹, 0; 0, 0, 1; r 0, r 1, r 2], by
        simp [Matrix.det_fin_three, h0]⟩, fun j => ?_⟩
      fin_cases j <;> simp
    · refine ⟨⟨!![-(r 1)⁻¹, 0, 0; 0, 0, 1; r 0, r 1, r 2], by
        simp [Matrix.det_fin_three, h1, h2]⟩, fun j => ?_⟩
      fin_cases j <;> simp
  · refine ⟨⟨!![(r 2)⁻¹, 0, 0; 0, 1, 0; r 0, r 1, r 2], by
      simp [Matrix.det_fin_three, h2]⟩, fun j => ?_⟩
    fin_cases j <;> simp

end Normalize

section Normalize2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K]

theorem burnsideB49_exists_dot_one (r : Fin 3 → K) (hr : r ≠ 0) : ∃ x : Fin 3 → K, r ⬝ᵥ x = 1 := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hr (funext h)
  refine ⟨Pi.single i (r i)⁻¹, ?_⟩
  rw [dotProduct_single]
  exact mul_inv_cancel₀ hi

theorem burnsideB49_normalize (Et : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hnt : ∃ s ∈ Et, s ≠ 1)
    (hrk : ∀ s ∈ Et, s ≠ 1 → ∃ u r : Fin 3 → K, u ≠ 0 ∧ r ≠ 0 ∧
      (∀ x, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x + (r ⬝ᵥ x) • u) ∧ r ⬝ᵥ u = 0)
    (hax : ∀ s ∈ Et, s ≠ 1 → ∀ s' ∈ Et, s' ≠ 1 → ∀ x,
      (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x ↔ (s' : Matrix (Fin 3) (Fin 3) K).mulVec x = x) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 3) K) (w : Matrix.SpecialLinearGroup (Fin 3) K → Fin 2 → K),
      ∀ s ∈ Et, g * s * g⁻¹ = burnsideB49_tau (w s) := by
  obtain ⟨s₀, hs₀, hs₀1⟩ := hnt
  obtain ⟨u₀, r₀, hu₀, hr₀, hx₀, hd₀⟩ := hrk s₀ hs₀ hs₀1
  have hform : ∀ s ∈ Et, ∃ u : Fin 3 → K,
      ∀ x, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x + (r₀ ⬝ᵥ x) • u := by
    intro s hs
    by_cases hs1 : s = 1
    · subst hs1
      exact ⟨0, fun x => by simp⟩
    obtain ⟨u, r, hu, hr, hx, hd⟩ := hrk s hs hs1
    have hker : ∀ x, r₀ ⬝ᵥ x = 0 ↔ r ⬝ᵥ x = 0 := by
      intro x
      have := hax s₀ hs₀ hs₀1 s hs hs1 x
      rw [hx₀, hx] at this
      simpa [smul_eq_zero, hu₀, hu] using this
    obtain ⟨x₀, hx₀1⟩ := burnsideB49_exists_dot_one r₀ hr₀
    refine ⟨(r ⬝ᵥ x₀) • u, fun x => ?_⟩
    rw [hx]
    have h3 : r ⬝ᵥ x = (r₀ ⬝ᵥ x) * (r ⬝ᵥ x₀) := by
      have h1 : r₀ ⬝ᵥ (x - (r₀ ⬝ᵥ x) • x₀) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, hx₀1]
        simp
      have h2 := (hker _).1 h1
      rw [dotProduct_sub, dotProduct_smul, sub_eq_zero] at h2
      simpa [mul_comm] using h2
    rw [h3, mul_smul]
  choose! u hu using hform
  have hdet : ∀ s ∈ Et, r₀ ⬝ᵥ u s = 0 := by
    intro s hs
    have hd := burnsideB49_det_rank_one (s : Matrix (Fin 3) (Fin 3) K) (u s) r₀ (hu s hs)
    rw [s.2] at hd
    have h2 : (1 : K) + 0 = 1 + r₀ ⬝ᵥ u s := by rw [add_zero]; exact hd
    exact (add_left_cancel h2).symm
  obtain ⟨g, hg⟩ := burnsideB49_exists_row r₀ hr₀
  have hrow : ∀ z : Fin 3 → K, ((g : Matrix (Fin 3) (Fin 3) K).mulVec z) 2 = r₀ ⬝ᵥ z := by
    intro z
    simp only [Matrix.mulVec, dotProduct, hg]
  refine ⟨g, fun s => burnsideB49_ysub ((g : Matrix (Fin 3) (Fin 3) K).mulVec (u s)), fun s hs => ?_⟩
  apply burnsideB49_sl_ext
  intro y
  set z := ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec y with hz
  have hgz : (g : Matrix (Fin 3) (Fin 3) K).mulVec z = y := by
    rw [hz, burnsideB49_mulVec_mulVec_sl, mul_inv_cancel, burnsideB49_mulVec_one_sl]
  have h1 : ((g * s * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec y =
      (g : Matrix (Fin 3) (Fin 3) K).mulVec ((s : Matrix (Fin 3) (Fin 3) K).mulVec z) := by
    rw [burnsideB49_mulVec_mulVec_sl, burnsideB49_mulVec_mulVec_sl, mul_assoc]
  rw [h1, hu s hs z, Matrix.mulVec_add, hgz, Matrix.mulVec_smul, burnsideB49_tau_mulVec]
  have hy2 : r₀ ⬝ᵥ z = y 2 := by rw [← hrow, hgz]
  rw [hy2]
  have hg3 : ((g : Matrix (Fin 3) (Fin 3) K).mulVec (u s)) 2 = 0 := by rw [hrow, hdet s hs]
  funext i
  fin_cases i
  · simp [burnsideB49_vec3, burnsideB49_ysub]
  · simp [burnsideB49_vec3, burnsideB49_ysub]
  · simp [burnsideB49_vec3, hg3]

end Normalize2

section RootConjSec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]

@[expose] def burnsideB49_rootElt (i j : Fin 3) (h : i ≠ j) (c : K) :
    Matrix.SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j h c⟩

theorem burnsideB49_rootElt_coe (i j : Fin 3) (h : i ≠ j) (c : K) :
    ((burnsideB49_rootElt i j h c : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.single i j c := rfl

theorem burnsideB49_rootElt_add (i j : Fin 3) (h : i ≠ j) (c d : K) :
    burnsideB49_rootElt i j h c * burnsideB49_rootElt i j h d = burnsideB49_rootElt i j h (c + d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact Matrix.transvection_mul_transvection_same i j h c d

theorem burnsideB49_rootElt_zero (i j : Fin 3) (h : i ≠ j) :
    burnsideB49_rootElt i j h (0 : K) = 1 := by
  apply Subtype.ext
  simp [burnsideB49_rootElt]

theorem burnsideB49_rootElt_inv (i j : Fin 3) (h : i ≠ j) (c : K) :
    (burnsideB49_rootElt i j h c)⁻¹ = burnsideB49_rootElt i j h (-c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [burnsideB49_rootElt_add, add_neg_cancel, burnsideB49_rootElt_zero]

theorem burnsideB49_invT_rootElt (i j : Fin 3) (h : i ≠ j) (c : K) :
    CFSG.Quasithin.JonesParshall.invTransposeSL 3 K (burnsideB49_rootElt i j h c) =
      burnsideB49_rootElt j i h.symm (-c) := by
  apply Subtype.ext
  rw [CFSG.Quasithin.JonesParshall.invTransposeSL_coe, burnsideB49_rootElt_inv]
  change Matrix.transpose (1 + Matrix.single i j (-c)) = 1 + Matrix.single j i (-c)
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]

theorem burnsideB49_invT_invT (s : Matrix.SpecialLinearGroup (Fin 3) K) :
    CFSG.Quasithin.JonesParshall.invTransposeSL 3 K
      (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K s) = s :=
  CFSG.Quasithin.JonesParshall.invTransposeFun_invTransposeFun s

@[expose] def burnsideB49_RootConj (S : Set (Matrix.SpecialLinearGroup (Fin 3) K)) : Prop :=
  ∃ (a : Matrix.SpecialLinearGroup (Fin 3) K) (i j : Fin 3) (h : i ≠ j),
    ∀ s ∈ S, ∃ c : K, a⁻¹ * s * a = burnsideB49_rootElt i j h c

theorem burnsideB49_RootConj_invT (S : Set (Matrix.SpecialLinearGroup (Fin 3) K)) :
    burnsideB49_RootConj ((CFSG.Quasithin.JonesParshall.invTransposeSL 3 K) '' S) ↔
      burnsideB49_RootConj S := by
  have key : ∀ (S : Set (Matrix.SpecialLinearGroup (Fin 3) K)),
      burnsideB49_RootConj S →
      burnsideB49_RootConj ((CFSG.Quasithin.JonesParshall.invTransposeSL 3 K) '' S) := by
    rintro S ⟨a, i, j, h, hs⟩
    refine ⟨CFSG.Quasithin.JonesParshall.invTransposeSL 3 K a, j, i, h.symm, ?_⟩
    rintro _ ⟨s, hsS, rfl⟩
    obtain ⟨c, hc⟩ := hs s hsS
    refine ⟨-c, ?_⟩
    rw [← burnsideB49_invT_rootElt i j h c, ← hc, map_mul, map_mul, map_inv]
  constructor
  · intro hS
    have h2 := key _ hS
    have e : (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K) ''
        ((CFSG.Quasithin.JonesParshall.invTransposeSL 3 K) '' S) = S := by
      ext s
      simp only [Set.mem_image]
      constructor
      · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
        rw [burnsideB49_invT_invT]
        exact ht
      · intro hs
        exact ⟨_, ⟨s, hs, rfl⟩, burnsideB49_invT_invT s⟩
    rwa [e] at h2
  · exact key S

end RootConjSec

section InRoot

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_conj_coe (a t : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((π (burnsideB49_slToStated 3 K (a⁻¹ * t * a)) : ↥G) : MulAut V) =
      ((π (burnsideB49_slToStated 3 K a) : ↥G) : MulAut V)⁻¹ *
        ((π (burnsideB49_slToStated 3 K t) : ↥G) : MulAut V) *
        ((π (burnsideB49_slToStated 3 K a) : ↥G) : MulAut V) := by
  simp [map_mul, map_inv]

theorem burnsideB49_inRoot_iff_sigma (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (E : Subgroup (MulAut V)) (hEG : E ≤ G) :
    CFSG.ASVolI.ChB.InRootGroup G π E ↔
      burnsideB49_RootConj (C.σ '' (burnsideB49_Etil C E : Set (Matrix.SpecialLinearGroup (Fin 3) K))) := by
  constructor
  · rintro ⟨g', i, j, hij, h⟩
    obtain ⟨γ, rfl⟩ := hreal.1 g'
    obtain ⟨a, rfl⟩ := burnsideB49_slToStated_surjective 3 K γ
    refine ⟨a, i, j, hij, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have hsE : burnsideB49_rhoHat C s ∈ E := hs
    obtain ⟨s', c, hc, hπs'⟩ := h _ hsE
    refine ⟨c, ?_⟩
    have e1 : π s' = π (burnsideB49_slToStated 3 K (a⁻¹ * C.σ s * a)) := by
      apply Subtype.ext
      rw [hπs', burnsideB49_conj_coe]
      rfl
    have e2 := burnsideB49_pi_injective hreal e1
    apply Subtype.ext
    rw [burnsideB49_rootElt_coe, ← hc, e2]
    rfl
  · rintro ⟨a, i, j, hij, h⟩
    refine ⟨π (burnsideB49_slToStated 3 K a), i, j, hij, ?_⟩
    intro e he
    obtain ⟨s, hs⟩ := burnsideB49_rhoHat_surj C hreal.1 e (hEG he)
    have hsE : s ∈ burnsideB49_Etil C E := by
      rw [burnsideB49_Etil, Subgroup.mem_comap, hs]
      exact he
    obtain ⟨c, hc⟩ := h _ ⟨s, hsE, rfl⟩
    refine ⟨burnsideB49_slToStated 3 K (burnsideB49_rootElt i j hij c), c, ?_, ?_⟩
    · rfl
    · rw [← hc, burnsideB49_conj_coe, ← hs]
      rfl

end InRoot

section RootLine

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_inRoot_iff (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (E : Subgroup (MulAut V)) (hEG : E ≤ G) :
    CFSG.ASVolI.ChB.InRootGroup G π E ↔
      burnsideB49_RootConj (burnsideB49_Etil C E : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
  rw [burnsideB49_inRoot_iff_sigma C hreal E hEG]
  rcases C.hσ with h | h
  · have : C.σ '' (burnsideB49_Etil C E : Set (Matrix.SpecialLinearGroup (Fin 3) K)) =
        (burnsideB49_Etil C E : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
      ext s
      simp only [Set.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩
        rw [h t]
        exact ht
      · intro hs
        exact ⟨s, hs, h s⟩
    rw [this]
  · have : C.σ '' (burnsideB49_Etil C E : Set (Matrix.SpecialLinearGroup (Fin 3) K)) =
        (CFSG.Quasithin.JonesParshall.invTransposeSL 3 K) ''
          (burnsideB49_Etil C E : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
      ext s
      simp only [Set.mem_image]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, (h t).symm⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t, ht, h t⟩
    rw [this, burnsideB49_RootConj_invT]

theorem burnsideB49_proportional_of_det_zero (a b : Fin 2 → K) (ha : a ≠ 0)
    (h : a 0 * b 1 - a 1 * b 0 = 0) : ∃ c : K, b = c • a := by
  by_cases h0 : a 0 = 0
  · have h1 : a 1 ≠ 0 := by
      intro h1
      apply ha
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have hb0 : b 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.1 h).resolve_left h1
    refine ⟨b 1 / a 1, ?_⟩
    funext i
    fin_cases i
    · simp [hb0, h0]
    · simp [h1]
  · refine ⟨b 0 / a 0, ?_⟩
    funext i
    fin_cases i
    · simp [h0]
    · simp
      field_simp
      linear_combination h

theorem burnsideB49_rootConj_of_line (S : Set (Matrix.SpecialLinearGroup (Fin 3) K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (w : Matrix.SpecialLinearGroup (Fin 3) K → Fin 2 → K)
    (hw : ∀ s ∈ S, g * s * g⁻¹ = burnsideB49_tau (w s)) (w₀ : Fin 2 → K)
    (hl : ∀ s ∈ S, ∃ c : K, w s = c • w₀) : burnsideB49_RootConj S := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix.SpecialLinearGroup (Fin 2) K,
      ∀ s ∈ S, ∃ c : K, w s = c • (M : Matrix (Fin 2) (Fin 2) K).mulVec ![1, 0] := by
    by_cases hw0 : w₀ = 0
    · refine ⟨1, fun s hs => ⟨0, ?_⟩⟩
      obtain ⟨c, hc⟩ := hl s hs
      rw [hc, hw0]
      simp
    · obtain ⟨M, hMw⟩ := burnsideB49_sl2_transitive w₀ hw0
      exact ⟨M, fun s hs => by rw [hMw]; exact hl s hs⟩
  refine ⟨g⁻¹ * burnsideB49_kap M, 0, 2, by decide, fun s hs => ?_⟩
  obtain ⟨c, hc⟩ := hM s hs
  refine ⟨c, ?_⟩
  have h1 : burnsideB49_kap M * burnsideB49_tau (c • ![1, 0]) =
      burnsideB49_tau (w s) * burnsideB49_kap M := by
    rw [burnsideB49_kap_tau, Matrix.mulVec_smul, ← hc]
  have h2 : burnsideB49_tau (c • (![1, 0] : Fin 2 → K)) = burnsideB49_rootElt 0 2 (by decide) c := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideB49_tau, burnsideB49_tauM, burnsideB49_rootElt, Matrix.transvection,
        Matrix.single_apply]
  calc (g⁻¹ * burnsideB49_kap M)⁻¹ * s * (g⁻¹ * burnsideB49_kap M)
      = (burnsideB49_kap M)⁻¹ * (g * s * g⁻¹) * burnsideB49_kap M := by group
    _ = (burnsideB49_kap M)⁻¹ * burnsideB49_tau (w s) * burnsideB49_kap M := by rw [hw s hs]
    _ = burnsideB49_tau (c • ![1, 0]) := by
      have h3 : (burnsideB49_kap M)⁻¹ * burnsideB49_tau (w s) * burnsideB49_kap M =
          (burnsideB49_kap M)⁻¹ * (burnsideB49_tau (w s) * burnsideB49_kap M) := mul_assoc _ _ _
      rw [h3, ← h1]
      group
    _ = burnsideB49_rootElt 0 2 (by decide) c := h2

theorem burnsideB49_indep_of_not_root (S : Set (Matrix.SpecialLinearGroup (Fin 3) K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (w : Matrix.SpecialLinearGroup (Fin 3) K → Fin 2 → K)
    (hw : ∀ s ∈ S, g * s * g⁻¹ = burnsideB49_tau (w s)) (hnr : ¬ burnsideB49_RootConj S) :
    ∃ s₁ ∈ S, ∃ s₂ ∈ S, w s₁ 0 * w s₂ 1 - w s₁ 1 * w s₂ 0 ≠ 0 := by
  by_contra h
  push_neg at h
  apply hnr
  by_cases hex : ∃ s₁ ∈ S, w s₁ ≠ 0
  · obtain ⟨s₁, hs₁, hne⟩ := hex
    exact burnsideB49_rootConj_of_line S g w hw (w s₁) (fun s hs =>
      (burnsideB49_proportional_of_det_zero (w s₁) (w s) hne (h s₁ hs₁ s hs)))
  · push_neg at hex
    exact burnsideB49_rootConj_of_line S g w hw 0 (fun s hs => ⟨0, by rw [hex s hs]; simp⟩)

end RootLine

section RelSec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] {A : Type} [AddCommGroup A]

@[expose] def burnsideB49_Rel (D : burnsideB49_Core3 F A) (w w' : Fin 2 → F) : Prop :=
  ∀ a : A, D.ρ (burnsideB49_tau w') (D.ρ (burnsideB49_tau w) a - a) = D.ρ (burnsideB49_tau w) a - a

theorem burnsideB49_QuadHyp_iff (D : burnsideB49_Core3 F A) :
    burnsideB49_QuadHyp D ↔ ∀ w w', burnsideB49_Rel D w w' :=
  ⟨fun h w w' a => h w' w a, fun h w w' a => h w' w a⟩

theorem burnsideB49_Rel_zero_left (D : burnsideB49_Core3 F A) (w' : Fin 2 → F) :
    burnsideB49_Rel D 0 w' := by
  intro a
  simp [burnsideB49_tau_zero, burnsideB49_rho_one_apply]

theorem burnsideB49_Rel_zero_right (D : burnsideB49_Core3 F A) (w : Fin 2 → F) :
    burnsideB49_Rel D w 0 := by
  intro a
  simp [burnsideB49_tau_zero, burnsideB49_rho_one_apply]

theorem burnsideB49_Rel_add_right (D : burnsideB49_Core3 F A) {w w₁ w₂ : Fin 2 → F}
    (h₁ : burnsideB49_Rel D w w₁) (h₂ : burnsideB49_Rel D w w₂) :
    burnsideB49_Rel D w (w₁ + w₂) := by
  intro a
  rw [burnsideB49_tau_add, burnsideB49_rho_mul_apply, h₂, h₁]

theorem burnsideB49_Rel_neg_right (D : burnsideB49_Core3 F A) {w w' : Fin 2 → F}
    (h : burnsideB49_Rel D w w') : burnsideB49_Rel D w (-w') := by
  intro a
  have h1 := h a
  have h2 : D.ρ (burnsideB49_tau (-w')) (D.ρ (burnsideB49_tau w') (D.ρ (burnsideB49_tau w) a - a)) =
      D.ρ (burnsideB49_tau (-w')) (D.ρ (burnsideB49_tau w) a - a) := by rw [h1]
  rw [← burnsideB49_rho_mul_apply, ← burnsideB49_tau_add, neg_add_cancel, burnsideB49_tau_zero,
    burnsideB49_rho_one_apply] at h2
  exact h2.symm

theorem burnsideB49_Rel_iff_sum (D : burnsideB49_Core3 F A) (w w' : Fin 2 → F) :
    burnsideB49_Rel D w w' ↔ ∀ a : A, D.ρ (burnsideB49_tau (w + w')) a + a =
      D.ρ (burnsideB49_tau w) a + D.ρ (burnsideB49_tau w') a := by
  constructor
  · intro h a
    have h1 := h a
    rw [map_sub] at h1
    rw [add_comm w w', burnsideB49_tau_add, burnsideB49_rho_mul_apply]
    have h2 : D.ρ (burnsideB49_tau w') (D.ρ (burnsideB49_tau w) a) =
        D.ρ (burnsideB49_tau w) a - a + D.ρ (burnsideB49_tau w') a := by
      rw [← h1]
      abel
    rw [h2]
    abel
  · intro h a
    have h1 := h a
    rw [add_comm w w', burnsideB49_tau_add, burnsideB49_rho_mul_apply] at h1
    rw [map_sub]
    have : D.ρ (burnsideB49_tau w') (D.ρ (burnsideB49_tau w) a) =
        D.ρ (burnsideB49_tau w) a + D.ρ (burnsideB49_tau w') a - a := by
      rw [eq_sub_iff_add_eq]
      exact h1
    rw [this]
    abel

theorem burnsideB49_Rel_symm (D : burnsideB49_Core3 F A) {w w' : Fin 2 → F}
    (h : burnsideB49_Rel D w w') : burnsideB49_Rel D w' w := by
  rw [burnsideB49_Rel_iff_sum] at h ⊢
  intro a
  rw [add_comm w' w, h a, add_comm]

theorem burnsideB49_Rel_conj (D : burnsideB49_Core3 F A) (h : Matrix.SpecialLinearGroup (Fin 3) F)
    (θ : (Fin 2 → F) → (Fin 2 → F))
    (hθ : ∀ w, h * burnsideB49_tau w * h⁻¹ = burnsideB49_tau (θ w)) {w w' : Fin 2 → F}
    (hr : burnsideB49_Rel D w w') : burnsideB49_Rel D (θ w) (θ w') := by
  have hPP : ∀ x, D.ρ h (D.ρ h⁻¹ x) = x := fun x => by
    rw [← burnsideB49_rho_mul_apply, mul_inv_cancel, burnsideB49_rho_one_apply]
  have hPP' : ∀ x, D.ρ h⁻¹ (D.ρ h x) = x := fun x => by
    rw [← burnsideB49_rho_mul_apply, inv_mul_cancel, burnsideB49_rho_one_apply]
  have e1 : ∀ (u : Fin 2 → F) (x : A), D.ρ (burnsideB49_tau (θ u)) (D.ρ h x) =
      D.ρ h (D.ρ (burnsideB49_tau u) x) := by
    intro u x
    rw [← hθ u, burnsideB49_rho_mul_apply, burnsideB49_rho_mul_apply, hPP']
  intro a
  obtain ⟨b, rfl⟩ : ∃ b, a = D.ρ h b := ⟨D.ρ h⁻¹ a, (hPP a).symm⟩
  rw [e1 w b, ← map_sub (D.ρ h), e1 w' _, hr b]

end RelSec

section Spread1

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F]

@[expose] def burnsideB49_det2 (a b : Fin 2 → F) : F := a 0 * b 1 - a 1 * b 0

@[expose] def burnsideB49_tdSL (d : F) (hd : d ≠ 0) : Matrix.SpecialLinearGroup (Fin 3) F :=
  ⟨!![d, 0, 0; 0, 1, 0; 0, 0, d⁻¹], by simp [Matrix.det_fin_three, hd]⟩

@[expose] def burnsideB49_dtw (d : F) (w : Fin 2 → F) : Fin 2 → F := ![d ^ 2 * w 0, d * w 1]

theorem burnsideB49_tdSL_conj (d : F) (hd : d ≠ 0) (w : Fin 2 → F) :
    burnsideB49_tdSL d hd * burnsideB49_tau w * (burnsideB49_tdSL d hd)⁻¹ =
      burnsideB49_tau (burnsideB49_dtw d w) := by
  have h : burnsideB49_tdSL d hd * burnsideB49_tau w =
      burnsideB49_tau (burnsideB49_dtw d w) * burnsideB49_tdSL d hd := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [burnsideB49_tdSL, burnsideB49_tau, burnsideB49_tauM, burnsideB49_dtw, Matrix.mul_apply,
        Fin.sum_univ_three] <;> field_simp
  rw [h]
  group

theorem burnsideB49_kap_conj (M : Matrix.SpecialLinearGroup (Fin 2) F) (w : Fin 2 → F) :
    burnsideB49_kap M * burnsideB49_tau w * (burnsideB49_kap M)⁻¹ =
      burnsideB49_tau ((M : Matrix (Fin 2) (Fin 2) F).mulVec w) := by
  rw [burnsideB49_kap_tau]
  group

@[expose] def burnsideB49_shearU (u : Fin 2 → F) (c : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1 - c * u 0 * u 1, c * u 0 * u 0; -(c * u 1 * u 1), 1 + c * u 0 * u 1], by
    simp only [Matrix.det_fin_two_of]
    ring⟩

theorem burnsideB49_shearU_mulVec (u : Fin 2 → F) (c : F) (z : Fin 2 → F) :
    (burnsideB49_shearU u c : Matrix (Fin 2) (Fin 2) F).mulVec z =
      z + (c * burnsideB49_det2 u z) • u := by
  funext i
  fin_cases i <;>
    simp [burnsideB49_shearU, burnsideB49_det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring

theorem burnsideB49_det2_sl2 (M : Matrix.SpecialLinearGroup (Fin 2) F) (a b : Fin 2 → F) :
    burnsideB49_det2 ((M : Matrix (Fin 2) (Fin 2) F).mulVec a)
      ((M : Matrix (Fin 2) (Fin 2) F).mulVec b) = burnsideB49_det2 a b := by
  have hd : (M : Matrix (Fin 2) (Fin 2) F) 0 0 * (M : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (M : Matrix (Fin 2) (Fin 2) F) 0 1 * (M : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    have := M.2
    rwa [Matrix.det_fin_two] at this
  simp only [burnsideB49_det2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (a 0 * b 1 - a 1 * b 0) * hd

theorem burnsideB49_det2_dtw (d : F) (a b : Fin 2 → F) :
    burnsideB49_det2 (burnsideB49_dtw d a) (burnsideB49_dtw d b) = d ^ 3 * burnsideB49_det2 a b := by
  simp only [burnsideB49_det2, burnsideB49_dtw]
  simp
  ring

theorem burnsideB49_det2_self (a : Fin 2 → F) : burnsideB49_det2 a a = 0 := by
  simp only [burnsideB49_det2]
  ring

theorem burnsideB49_sl2_trans2 (v₁ v₂ : Fin 2 → F) (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) F, (M : Matrix (Fin 2) (Fin 2) F).mulVec v₁ = v₂ := by
  obtain ⟨Ma, hMa⟩ := burnsideB49_sl2_transitive v₂ h₂
  obtain ⟨Mb, hMb⟩ := burnsideB49_sl2_transitive v₁ h₁
  refine ⟨Ma * Mb⁻¹, ?_⟩
  rw [← hMb]
  have : (Mb⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) * Mb = 1 := inv_mul_cancel Mb
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
  have h3 : ((Mb⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec
      ((Mb : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0]) = ![1, 0] := by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, this]
    simp
  rw [h3, hMa]

variable {A : Type} [AddCommGroup A]

theorem burnsideB49_Rel_shear (D : burnsideB49_Core3 F A) {u u₂ : Fin 2 → F} (c : F)
    (h : burnsideB49_Rel D u u₂) :
    burnsideB49_Rel D u (u₂ + (c * burnsideB49_det2 u u₂) • u) := by
  have hθ : ∀ w, burnsideB49_kap (burnsideB49_shearU u c) * burnsideB49_tau w *
      (burnsideB49_kap (burnsideB49_shearU u c))⁻¹ =
      burnsideB49_tau ((burnsideB49_shearU u c : Matrix (Fin 2) (Fin 2) F).mulVec w) :=
    fun w => burnsideB49_kap_conj _ w
  have h1 := burnsideB49_Rel_conj D _ _ hθ h
  rw [burnsideB49_shearU_mulVec, burnsideB49_shearU_mulVec, burnsideB49_det2_self] at h1
  simpa [add_comm] using h1

theorem burnsideB49_Rel_twist (D : burnsideB49_Core3 F A) {u y : Fin 2 → F} (d : F) (hd : d ≠ 0)
    (hu : u ≠ 0) (h : burnsideB49_Rel D u y) :
    ∃ y', burnsideB49_Rel D u y' ∧ burnsideB49_det2 u y' = d ^ 3 * burnsideB49_det2 u y := by
  have hdu : burnsideB49_dtw d u ≠ 0 := by
    intro h0
    apply hu
    funext i
    have h0' := congrFun h0 i
    fin_cases i
    · simp [burnsideB49_dtw, hd] at h0'
      simpa using h0'
    · simp [burnsideB49_dtw, hd] at h0'
      simpa using h0'
  obtain ⟨M, hM⟩ := burnsideB49_sl2_trans2 _ _ hdu hu
  have hθ : ∀ w, (burnsideB49_kap M * burnsideB49_tdSL d hd) * burnsideB49_tau w *
      (burnsideB49_kap M * burnsideB49_tdSL d hd)⁻¹ =
      burnsideB49_tau ((M : Matrix (Fin 2) (Fin 2) F).mulVec (burnsideB49_dtw d w)) := by
    intro w
    have e : (burnsideB49_kap M * burnsideB49_tdSL d hd) * burnsideB49_tau w *
        (burnsideB49_kap M * burnsideB49_tdSL d hd)⁻¹ =
        burnsideB49_kap M * (burnsideB49_tdSL d hd * burnsideB49_tau w *
          (burnsideB49_tdSL d hd)⁻¹) * (burnsideB49_kap M)⁻¹ := by group
    rw [e, burnsideB49_tdSL_conj, burnsideB49_kap_conj]
  refine ⟨(M : Matrix (Fin 2) (Fin 2) F).mulVec (burnsideB49_dtw d y), ?_, ?_⟩
  · have h1 := burnsideB49_Rel_conj D _ _ hθ h
    rw [hM] at h1
    exact h1
  · have h2 := burnsideB49_det2_sl2 M (burnsideB49_dtw d u) (burnsideB49_dtw d y)
    rw [hM, burnsideB49_det2_dtw] at h2
    exact h2

end Spread1

section Cubes

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem burnsideB49_cubes_span (h8 : 8 ≤ Nat.card F) :
    AddSubgroup.closure {x : F | ∃ d : F, d ≠ 0 ∧ x = d ^ 3} = ⊤ := by
  classical
  set S := AddSubgroup.closure {x : F | ∃ d : F, d ≠ 0 ∧ x = d ^ 3} with hS
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hcube : ∀ d : F, d ≠ 0 → d ^ 3 ∈ S := fun d hd => AddSubgroup.subset_closure ⟨d, hd, rfl⟩
  have hone : (1 : F) ∈ S := by simpa using hcube 1 one_ne_zero
  have hmul1 : ∀ d : F, d ≠ 0 → ∀ y ∈ S, d ^ 3 * y ∈ S := by
    intro d hd y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      rw [← mul_pow]
      exact hcube _ (mul_ne_zero hd he)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact S.add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact S.neg_mem hx
  have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
    intro x hx y hy
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      exact hmul1 e he y hy
    | zero => simp
    | add x x' _ _ hx hx' => rw [add_mul]; exact S.add_mem hx hx'
    | neg x _ hx => rw [neg_mul]; exact S.neg_mem hx
  have hpow : ∀ x ∈ S, ∀ n : ℕ, x ^ n ∈ S := by
    intro x hx n
    induction n with
    | zero => simpa using hone
    | succ n ih => rw [pow_succ]; exact hmul _ ih _ hx
  haveI := Fintype.ofFinite F
  have hinv : ∀ x ∈ S, x ≠ 0 → x⁻¹ ∈ S := by
    intro x hx hx0
    have h1 : x ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
    have hq2 : 2 ≤ Fintype.card F := by
      have := h8
      rw [Nat.card_eq_fintype_card] at this
      omega
    have h3 : x⁻¹ = x ^ (Fintype.card F - 2) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ']
      have : Fintype.card F - 2 + 1 = Fintype.card F - 1 := by omega
      rw [this, h1]
    rw [h3]
    exact hpow x hx _
  have hp : ∀ x : F, x * x + x ∈ S := by
    intro x
    by_cases hx0 : x = 0
    · simp [hx0]
    by_cases hx1 : x + 1 = 0
    · have : x * x + x = 0 := by
        have hx : x = -1 := eq_neg_of_add_eq_zero_left hx1
        rw [hx]
        ring
      rw [this]
      exact S.zero_mem
    · have e : x * x + x = (x + 1) ^ 3 - x ^ 3 - 1 ^ 3 := by
        linear_combination (-(x * x + x)) * h2
      rw [e]
      exact S.sub_mem (S.sub_mem (hcube _ hx1) (hcube _ hx0)) (by simpa using hone)
  let ℘ : F →+ F := AddMonoidHom.mk' (fun x => x * x + x) (fun a b => by
    linear_combination (a * b) * h2)
  have hrange : ℘.range ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact hp x
  have hker : Nat.card ℘.ker ≤ 2 := by
    have hsub : (℘.ker : Set F) ⊆ ({0, 1} : Set F) := by
      intro x hx
      have hx' : x * x + x = 0 := hx
      have : x * (x + 1) = 0 := by linear_combination hx'
      rcases mul_eq_zero.1 this with h | h
      · left; exact h
      · right
        have : x = -1 := eq_neg_of_add_eq_zero_left h
        rw [this]
        exact (CharTwo.neg_eq (1 : F))
    have hc : Nat.card ↥(℘.ker : Set F) ≤ Nat.card ↥({0, 1} : Set F) :=
      Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2' : Nat.card ↥({0, 1} : Set F) = 2 := by
      rw [Nat.card_coe_set_eq, Set.ncard_pair zero_ne_one]
    have h3 : Nat.card ↥(℘.ker : Set F) = Nat.card ℘.ker := rfl
    rw [← h3]
    omega
  have hcard := AddSubgroup.card_ker_mul_card_range ℘
  have hrS : Nat.card ℘.range ≤ Nat.card S := AddSubgroup.card_le_of_le hrange
  have hq2S : Nat.card F ≤ 2 * Nat.card S := by
    have hpos : 0 < Nat.card ℘.range := Nat.card_pos
    calc Nat.card F = Nat.card ℘.ker * Nat.card ℘.range := hcard.symm
      _ ≤ 2 * Nat.card ℘.range := Nat.mul_le_mul_right _ hker
      _ ≤ 2 * Nat.card S := Nat.mul_le_mul_left _ hrS
  by_contra hne
  have hex : ∃ t : F, t ∉ S := by
    by_contra h
    push_neg at h
    exact hne (eq_top_iff.2 fun x _ => h x)
  obtain ⟨t, ht⟩ := hex
  have hinj : Function.Injective (fun p : S × S => (p.1 : F) + (p.2 : F) * t) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only at h
    have hb : (b : F) = b' := by
      by_contra hbb
      have hsub : ((b : F) - b') ≠ 0 := sub_ne_zero.2 hbb
      have h1 : ((b : F) - b') * t = (a' : F) - a := by linear_combination h
      have h2' : t = ((a' : F) - a) * ((b : F) - b')⁻¹ := by
        field_simp
        linear_combination h1
      apply ht
      rw [h2']
      exact hmul _ (S.sub_mem a'.2 a.2) _ (hinv _ (S.sub_mem b.2 b'.2) hsub)
    have hb' : b = b' := Subtype.ext hb
    subst hb'
    have : (a : F) = a' := by linear_combination h
    exact Prod.ext (Subtype.ext this) rfl
  have hle : Nat.card (S × S) ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at hle
  have hSpos : 0 < Nat.card S := Nat.card_pos
  nlinarith

end Cubes

section Spread2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {A : Type} [AddCommGroup A]

theorem burnsideB49_det2_add (u y y' : Fin 2 → F) :
    burnsideB49_det2 u (y + y') = burnsideB49_det2 u y + burnsideB49_det2 u y' := by
  simp only [burnsideB49_det2, Pi.add_apply]
  ring

theorem burnsideB49_det2_smul (u y : Fin 2 → F) (c : F) :
    burnsideB49_det2 u (c • y) = c * burnsideB49_det2 u y := by
  simp only [burnsideB49_det2, Pi.smul_apply, smul_eq_mul]
  ring

theorem burnsideB49_spread (D : burnsideB49_Core3 F A) (h8 : 8 ≤ Nat.card F)
    {u₁ u₂ : Fin 2 → F} (hΔ : burnsideB49_det2 u₁ u₂ ≠ 0) (hr : burnsideB49_Rel D u₁ u₂) :
    burnsideB49_QuadHyp D := by
  have hu₁ : u₁ ≠ 0 := by
    intro h
    apply hΔ
    rw [h]
    simp [burnsideB49_det2]
  set Δ := burnsideB49_det2 u₁ u₂ with hΔdef
  let Bsub : AddSubgroup (Fin 2 → F) :=
    { carrier := {y | burnsideB49_Rel D u₁ y}
      zero_mem' := burnsideB49_Rel_zero_right D u₁
      add_mem' := fun {a b} ha hb => burnsideB49_Rel_add_right D ha hb
      neg_mem' := fun {a} ha => burnsideB49_Rel_neg_right D ha }
  have hB : ∀ y, y ∈ Bsub ↔ burnsideB49_Rel D u₁ y := fun y => Iff.rfl
  let δ : (Fin 2 → F) →+ F := AddMonoidHom.mk' (fun y => burnsideB49_det2 u₁ y)
    (burnsideB49_det2_add u₁)
  have hA : ∀ e : F, e • u₁ ∈ Bsub := by
    intro e
    have h1 := burnsideB49_Rel_shear D (e / Δ) hr
    have h2 : (e / Δ) * burnsideB49_det2 u₁ u₂ = e := by
      rw [← hΔdef]
      field_simp
    rw [h2] at h1
    have h3 : u₂ + e • u₁ ∈ Bsub := h1
    have h4 : u₂ ∈ Bsub := hr
    have := Bsub.sub_mem h3 h4
    simpa using this
  have hBd : ∀ d : F, d ≠ 0 → d ^ 3 * Δ ∈ Bsub.map δ := by
    intro d hd
    obtain ⟨y', hy', hdet⟩ := burnsideB49_Rel_twist D d hd hu₁ hr
    exact ⟨y', hy', hdet⟩
  have hC : ∀ z : F, z ∈ Bsub.map δ := by
    have hcl : ∀ x ∈ AddSubgroup.closure {x : F | ∃ d : F, d ≠ 0 ∧ x = d ^ 3}, Δ * x ∈ Bsub.map δ := by
      intro x hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨d, hd, rfl⟩ := hx
        rw [mul_comm]
        exact hBd d hd
      | zero => simpa using (Bsub.map δ).zero_mem
      | add x y _ _ hx hy => rw [mul_add]; exact (Bsub.map δ).add_mem hx hy
      | neg x _ hx => rw [mul_neg]; exact (Bsub.map δ).neg_mem hx
    intro z
    have := hcl (z / Δ) (by rw [burnsideB49_cubes_span h8]; exact AddSubgroup.mem_top _)
    rwa [mul_div_cancel₀ _ hΔ] at this
  have hD : ∀ y, burnsideB49_Rel D u₁ y := by
    intro y
    obtain ⟨y', hy', hδ⟩ := hC (burnsideB49_det2 u₁ y)
    have hz : burnsideB49_det2 u₁ (y - y') = 0 := by
      have : burnsideB49_det2 u₁ y' = burnsideB49_det2 u₁ y := hδ
      have h5 := burnsideB49_det2_add u₁ (y - y') y'
      rw [sub_add_cancel, this] at h5
      have h6 : burnsideB49_det2 u₁ (y - y') = 0 := by
        have : burnsideB49_det2 u₁ y = burnsideB49_det2 u₁ (y - y') + burnsideB49_det2 u₁ y := h5
        have h7 : burnsideB49_det2 u₁ (y - y') + burnsideB49_det2 u₁ y = 0 + burnsideB49_det2 u₁ y := by
          rw [zero_add]; exact this.symm
        exact add_right_cancel h7
      exact h6
    obtain ⟨c, hc⟩ := burnsideB49_proportional_of_det_zero u₁ (y - y') hu₁ hz
    have hy : y = y' + c • u₁ := by
      rw [← hc]
      abel
    have : y ∈ Bsub := by
      rw [hy]
      exact Bsub.add_mem hy' (hA c)
    exact this
  rw [burnsideB49_QuadHyp_iff]
  intro x y
  by_cases hx : x = 0
  · rw [hx]
    exact burnsideB49_Rel_zero_left D y
  · obtain ⟨M, hM⟩ := burnsideB49_sl2_trans2 u₁ x hu₁ hx
    have hθ : ∀ w, burnsideB49_kap M * burnsideB49_tau w * (burnsideB49_kap M)⁻¹ =
        burnsideB49_tau ((M : Matrix (Fin 2) (Fin 2) F).mulVec w) :=
      fun w => burnsideB49_kap_conj M w
    have h1 := burnsideB49_Rel_conj D _ _ hθ
      (hD (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec y))
    rw [hM] at h1
    have h2 : (M : Matrix (Fin 2) (Fin 2) F).mulVec
        (((M⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).mulVec y) = y := by
      rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      simp
    rw [h2] at h1
    exact h1

end Spread2

section Assemble3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_E_normal (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (E : Subgroup (MulAut V))
    (hE : CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U f E) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 3) K)
      (w : Matrix.SpecialLinearGroup (Fin 3) K → Fin 2 → K),
      ∀ s ∈ burnsideB49_Etil C E, g * s * g⁻¹ = burnsideB49_tau (w s) := by
  obtain ⟨hEG, hE4, hEt, H, hH⟩ := hE
  have hcard := burnsideB49_card_Etil C hreal E hEG
  have hne1 : ∀ s : Matrix.SpecialLinearGroup (Fin 3) K, s ≠ 1 → burnsideB49_rhoHat C s ≠ 1 := by
    intro s hs h
    apply hs
    apply burnsideB49_rhoHat_injective C hreal
    rw [h, map_one]
  apply burnsideB49_normalize
  · by_contra hcon
    push_neg at hcon
    have : burnsideB49_Etil C E = ⊥ := by
      rw [eq_bot_iff]
      intro s hs
      exact Subgroup.mem_bot.2 (hcon s hs)
    have h1 : Nat.card ↥(burnsideB49_Etil C E) = 1 := by
      rw [this]
      exact Subgroup.card_bot
    rw [hcard, hE4] at h1
    omega
  · intro s hs hs1
    exact burnsideB49_transv_rank C hf s hs1 (hEt _ hs (hne1 s hs1))
  · intro s hs hs1 s' hs' hs1' x
    have h1 := hH _ hs (hne1 s hs1)
    have h2 := hH _ hs' (hne1 s' hs1')
    rw [burnsideB49_axisPre_rhoHat] at h1 h2
    obtain ⟨v, hv⟩ := C.hqs (Multiplicative.ofAdd x)
    have h3 : v ∈ {v | (s : Matrix (Fin 3) (Fin 3) K).mulVec (Multiplicative.toAdd (C.qV v)) =
        Multiplicative.toAdd (C.qV v)} ↔ v ∈ {v | (s' : Matrix (Fin 3) (Fin 3) K).mulVec
          (Multiplicative.toAdd (C.qV v)) = Multiplicative.toAdd (C.qV v)} := by
      rw [h1, h2]
    simp only [Set.mem_setOf_eq, hv, toAdd_ofAdd] at h3
    exact h3

theorem burnsideB49_quadHyp_of_E (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) (E : Subgroup (MulAut V))
    (hE : CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U f E) (hq : CFSG.Quasithin.IsQuadratic E)
    (hnr : ¬ CFSG.ASVolI.ChB.InRootGroup G π E) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) K, burnsideB49_QuadHyp (C.toCore3.conj g) := by
  obtain ⟨g, w, hw⟩ := burnsideB49_E_normal C hreal hf E hE
  have hnr' : ¬ burnsideB49_RootConj
      (burnsideB49_Etil C E : Set (Matrix.SpecialLinearGroup (Fin 3) K)) := by
    rw [← burnsideB49_inRoot_iff C hreal E hE.1]
    exact hnr
  obtain ⟨s₁, hs₁, s₂, hs₂, hΔ⟩ := burnsideB49_indep_of_not_root _ g w hw hnr'
  refine ⟨g, ?_⟩
  apply burnsideB49_spread (C.toCore3.conj g) h8 (u₁ := w s₁) (u₂ := w s₂) hΔ
  intro a
  have e1 : ∀ s ∈ burnsideB49_Etil C E, (C.toCore3.conj g).ρ (burnsideB49_tau (w s)) = C.toCore3.ρ s := by
    intro s hs
    change C.toCore3.ρ (g⁻¹ * burnsideB49_tau (w s) * g⁻¹⁻¹) = _
    rw [← hw s hs]
    congr 1
    group
  rw [e1 s₁ hs₁, e1 s₂ hs₂]
  exact burnsideB49_quad_R C E hq s₁ s₂ hs₁ hs₂ a

end Assemble3

section Three3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49_charP_two {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := g + 1) (by rw [← Nat.card_eq_fintype_card]; exact hK)

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_part1_three_big (hV : ∀ v : V, v ^ 2 = 1) {f : ℕ} (hf3 : 3 ≤ f)
    (hK : Nat.card K = 2 ^ f)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    (E : Subgroup (MulAut V)) (hE : CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U f E)
    (hq : CFSG.Quasithin.IsQuadratic E) (hnr : ¬ CFSG.ASVolI.ChB.InRootGroup G π E) :
    CFSG.ASVolI.ChB.SplitsOver G U := by
  haveI := burnsideB49_charP_two (K := K) (by omega) hK
  obtain ⟨C⟩ := burnsideB49_coord3_exists hreal hquot
  have h8 : 8 ≤ Nat.card K := by
    rw [hK]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  obtain ⟨g, hg⟩ := burnsideB49_quadHyp_of_E C hreal hK h8 E hE hq hnr
  exact burnsideB49_split_of_quad hV C hreal.1 g hg

end Three3

section TransvConverse

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V]

theorem burnsideB49_commV_zpowers (e : MulAut V) :
    CFSG.Quasithin.commV (Subgroup.zpowers e) = (burnsideB49_Te e).range := by
  apply le_antisymm
  · unfold CFSG.Quasithin.commV
    rw [Subgroup.closure_le]
    rintro _ ⟨x, hx, v, rfl⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    revert v
    refine Int.induction_on k ?_ ?_ ?_
    · intro v
      simp only [zpow_zero, MulAut.one_apply, mul_inv_cancel]
      exact one_mem _
    · intro i ih v
      have h1 := ih (e v)
      have h2 : burnsideB49_Te e v ∈ (burnsideB49_Te e).range := ⟨v, rfl⟩
      have h3 := Subgroup.mul_mem _ h1 h2
      have h4 : (e ^ ((i : ℤ) + 1)) v * v⁻¹ = ((e ^ (i : ℤ)) (e v) * (e v)⁻¹) * burnsideB49_Te e v := by
        rw [zpow_add_one, MulAut.mul_apply, burnsideB49_Te_apply]
        group
      show (e ^ ((i : ℤ) + 1)) v * v⁻¹ ∈ (burnsideB49_Te e).range
      rw [h4]
      exact h3
    · intro i ih v
      have h1 := ih (e⁻¹ v)
      have h2 : (burnsideB49_Te e (e⁻¹ v))⁻¹ ∈ (burnsideB49_Te e).range :=
        Subgroup.inv_mem _ ⟨e⁻¹ v, rfl⟩
      have h3 := Subgroup.mul_mem _ h1 h2
      have h4 : (e ^ (-(i : ℤ) - 1)) v * v⁻¹ =
          ((e ^ (-(i : ℤ))) (e⁻¹ v) * (e⁻¹ v)⁻¹) * (burnsideB49_Te e (e⁻¹ v))⁻¹ := by
        rw [zpow_sub_one, MulAut.mul_apply, burnsideB49_Te_apply]
        have : e (e⁻¹ v) = v := by
          rw [← MulAut.mul_apply, mul_inv_cancel]
          rfl
        rw [this]
        group
      show (e ^ (-(i : ℤ) - 1)) v * v⁻¹ ∈ (burnsideB49_Te e).range
      rw [h4]
      exact h3
  · rintro _ ⟨v, rfl⟩
    exact Subgroup.subset_closure ⟨e, Subgroup.mem_zpowers e, v, rfl⟩

end TransvConverse

section TransvConverse2

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_card_Wn_rank_one (s : Matrix.SpecialLinearGroup (Fin 3) K) (u r : Fin 3 → K)
    (hu : u ≠ 0) (hr : r ≠ 0)
    (hx : ∀ x, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x + (r ⬝ᵥ x) • u) :
    Nat.card ↥(burnsideB49_Wn s) = Nat.card K := by
  obtain ⟨x₀, hx₀⟩ := burnsideB49_exists_dot_one r hr
  symm
  apply Nat.card_congr
  refine (Equiv.ofBijective (fun c : K => (⟨c • u, ?_⟩ : ↥(burnsideB49_Wn s))) ⟨?_, ?_⟩)
  · rw [burnsideB49_mem_Wn]
    refine ⟨c • x₀, ?_⟩
    rw [hx, dotProduct_smul, hx₀]
    simp
  · intro c c' h
    have h2 : c • u = c' • u := congrArg Subtype.val h
    have h3 : (c - c') • u = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h3 with h4 | h4
    · exact sub_eq_zero.1 h4
    · exact absurd h4 hu
  · rintro ⟨w, hw⟩
    obtain ⟨z, rfl⟩ := (burnsideB49_mem_Wn s w).1 hw
    refine ⟨r ⬝ᵥ z, Subtype.ext ?_⟩
    show (r ⬝ᵥ z) • u = (s : Matrix (Fin 3) (Fin 3) K).mulVec z - z
    rw [hx z]
    simp

theorem burnsideB49_isTransv_of_rank_one (C : burnsideB49_Coord3 G U K π) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (s : Matrix.SpecialLinearGroup (Fin 3) K) (u r : Fin 3 → K)
    (hu : u ≠ 0) (hr : r ≠ 0)
    (hx : ∀ x, (s : Matrix (Fin 3) (Fin 3) K).mulVec x = x + (r ⬝ᵥ x) • u) :
    CFSG.ASVolI.ChB.IsTransvOnQuot U f (burnsideB49_rhoHat C s) := by
  unfold CFSG.ASVolI.ChB.IsTransvOnQuot
  rw [burnsideB49_commV_zpowers, burnsideB49_card_sup_ker C, burnsideB49_card_Wn C s,
    burnsideB49_card_Wn_rank_one s u r hu hr hx, hf]

end TransvConverse2

section FTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] [CharP K 2]

theorem burnsideB49_tau_injective : Function.Injective (burnsideB49_tau (F := K)) := by
  intro w w' h
  have h1 := congrArg (fun s : Matrix.SpecialLinearGroup (Fin 3) K =>
    (s : Matrix (Fin 3) (Fin 3) K)) h
  funext i
  fin_cases i
  · have := congrFun (congrFun h1 0) 2
    simpa [burnsideB49_tau, burnsideB49_tauM] using this
  · have := congrFun (congrFun h1 1) 2
    simpa [burnsideB49_tau, burnsideB49_tauM] using this

@[expose] def burnsideB49_zeta (K : Type) [Field K] [CharP K 2] : ZMod 2 →+* K :=
  ZMod.castHom (dvd_refl 2) K

@[expose] def burnsideB49_wxy (x y : Fin 2 → K) (m : ZMod 2 × ZMod 2) : Fin 2 → K :=
  burnsideB49_zeta K m.1 • x + burnsideB49_zeta K m.2 • y

theorem burnsideB49_wxy_add (x y : Fin 2 → K) (m m' : ZMod 2 × ZMod 2) :
    burnsideB49_wxy x y (m + m') = burnsideB49_wxy x y m + burnsideB49_wxy x y m' := by
  simp only [burnsideB49_wxy, Prod.fst_add, Prod.snd_add, map_add, add_smul]
  abel

@[expose] def burnsideB49_psi (x y : Fin 2 → K) :
    Multiplicative (ZMod 2 × ZMod 2) →* Matrix.SpecialLinearGroup (Fin 3) K :=
  MonoidHom.mk' (fun m => burnsideB49_tau (burnsideB49_wxy x y (Multiplicative.toAdd m)))
    (fun m m' => by
      rw [toAdd_mul, burnsideB49_wxy_add, burnsideB49_tau_add])

theorem burnsideB49_psi_apply (x y : Fin 2 → K) (m : Multiplicative (ZMod 2 × ZMod 2)) :
    burnsideB49_psi x y m = burnsideB49_tau (burnsideB49_wxy x y (Multiplicative.toAdd m)) := rfl

theorem burnsideB49_wxy_eq_zero (x y : Fin 2 → K) (hΔ : burnsideB49_det2 x y ≠ 0)
    (m : ZMod 2 × ZMod 2) (h : burnsideB49_wxy x y m = 0) : m = 0 := by
  have h1 : burnsideB49_det2 (burnsideB49_wxy x y m) y = 0 := by
    rw [h]
    simp [burnsideB49_det2]
  have h2 : burnsideB49_det2 (burnsideB49_wxy x y m) x = 0 := by
    rw [h]
    simp [burnsideB49_det2]
  have e1 : burnsideB49_det2 (burnsideB49_wxy x y m) y = burnsideB49_zeta K m.1 * burnsideB49_det2 x y := by
    simp only [burnsideB49_det2, burnsideB49_wxy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : burnsideB49_det2 (burnsideB49_wxy x y m) x = burnsideB49_zeta K m.2 * burnsideB49_det2 y x := by
    simp only [burnsideB49_det2, burnsideB49_wxy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hyx : burnsideB49_det2 y x ≠ 0 := by
    intro h0
    apply hΔ
    simp only [burnsideB49_det2] at h0 ⊢
    linear_combination -h0
  rw [e1] at h1
  rw [e2] at h2
  have z1 : burnsideB49_zeta K m.1 = 0 := (mul_eq_zero.1 h1).resolve_right hΔ
  have z2 : burnsideB49_zeta K m.2 = 0 := (mul_eq_zero.1 h2).resolve_right hyx
  have hinj : Function.Injective (burnsideB49_zeta K : ZMod 2 →+* K) := (burnsideB49_zeta K).injective
  have a1 : m.1 = 0 := hinj (by rw [z1, map_zero])
  have a2 : m.2 = 0 := hinj (by rw [z2, map_zero])
  exact Prod.ext a1 a2

theorem burnsideB49_psi_injective (x y : Fin 2 → K) (hΔ : burnsideB49_det2 x y ≠ 0) :
    Function.Injective (burnsideB49_psi x y) := by
  rw [injective_iff_map_eq_one]
  intro m hm
  have h1 : burnsideB49_tau (burnsideB49_wxy x y (Multiplicative.toAdd m)) = burnsideB49_tau 0 := by
    rw [burnsideB49_tau_zero]
    exact hm
  have h2 := burnsideB49_tau_injective h1
  have := burnsideB49_wxy_eq_zero x y hΔ _ h2
  apply Multiplicative.toAdd.injective
  exact this

end FTwo

section DepRoot

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem burnsideB49_single_smul (i j : Fin 3) (c : K) :
    (Matrix.single i j c : Matrix (Fin 3) (Fin 3) K) = c • Matrix.single i j (1 : K) := by
  ext a b
  simp [Matrix.single_apply]

theorem burnsideB49_dep_of_root (S : Set (Matrix.SpecialLinearGroup (Fin 3) K))
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (hr : burnsideB49_RootConj S)
    {s₁ s₂ : Matrix.SpecialLinearGroup (Fin 3) K} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S)
    {w₁ w₂ : Fin 2 → K} (hw₁ : g * s₁ * g⁻¹ = burnsideB49_tau w₁)
    (hw₂ : g * s₂ * g⁻¹ = burnsideB49_tau w₂) : burnsideB49_det2 w₁ w₂ = 0 := by
  obtain ⟨a, i, j, hij, h⟩ := hr
  obtain ⟨c₁, hc₁⟩ := h s₁ h₁
  obtain ⟨c₂, hc₂⟩ := h s₂ h₂
  set P : Matrix.SpecialLinearGroup (Fin 3) K := g * a with hP
  set Zm : Matrix (Fin 3) (Fin 3) K := (P : Matrix (Fin 3) (Fin 3) K) * Matrix.single i j (1 : K) *
    ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hZm
  have key : ∀ (c : K), ((P * burnsideB49_rootElt i j hij c * P⁻¹ :
      Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + c • Zm := by
    intro c
    have hPP : (P : Matrix (Fin 3) (Fin 3) K) *
        ((P⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
      rfl
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      burnsideB49_rootElt_coe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPP,
      burnsideB49_single_smul, Matrix.mul_smul, Matrix.smul_mul, hZm]
  have e1 : ∀ (s : Matrix.SpecialLinearGroup (Fin 3) K) (c : K), a⁻¹ * s * a = burnsideB49_rootElt i j hij c →
      g * s * g⁻¹ = P * burnsideB49_rootElt i j hij c * P⁻¹ := by
    intro s c hc
    rw [← hc, hP]
    group
  have t₁ := key c₁
  have t₂ := key c₂
  rw [← e1 s₁ c₁ hc₁, hw₁] at t₁
  rw [← e1 s₂ c₂ hc₂, hw₂] at t₂
  have a1 : w₁ 0 = c₁ * Zm 0 2 := by
    have := congrFun (congrFun t₁ 0) 2
    simpa [burnsideB49_tau, burnsideB49_tauM] using this
  have a2 : w₁ 1 = c₁ * Zm 1 2 := by
    have := congrFun (congrFun t₁ 1) 2
    simpa [burnsideB49_tau, burnsideB49_tauM] using this
  have b1 : w₂ 0 = c₂ * Zm 0 2 := by
    have := congrFun (congrFun t₂ 0) 2
    simpa [burnsideB49_tau, burnsideB49_tauM] using this
  have b2 : w₂ 1 = c₂ * Zm 1 2 := by
    have := congrFun (congrFun t₂ 1) 2
    simpa [burnsideB49_tau, burnsideB49_tauM] using this
  simp only [burnsideB49_det2]
  rw [a1, a2, b1, b2]
  ring

end DepRoot

section FTwoEp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}

@[expose] def burnsideB49_Ep (C : burnsideB49_Coord3 G U K π) (x y : Fin 2 → K) :
    Subgroup (MulAut V) :=
  ((burnsideB49_rhoHat C).comp (burnsideB49_psi x y)).range

theorem burnsideB49_Ep_mem_iff (C : burnsideB49_Coord3 G U K π) (x y : Fin 2 → K)
    (e : MulAut V) :
    e ∈ burnsideB49_Ep C x y ↔ ∃ m, burnsideB49_rhoHat C (burnsideB49_psi x y m) = e := Iff.rfl

theorem burnsideB49_Ep_le (C : burnsideB49_Coord3 G U K π) (x y : Fin 2 → K) :
    burnsideB49_Ep C x y ≤ G := by
  rintro e ⟨m, rfl⟩
  exact burnsideB49_rhoHat_mem C _

theorem burnsideB49_Ep_card (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (x y : Fin 2 → K) (hΔ : burnsideB49_det2 x y ≠ 0) : Nat.card ↥(burnsideB49_Ep C x y) = 4 := by
  have hinj : Function.Injective ((burnsideB49_rhoHat C).comp (burnsideB49_psi x y)) :=
    (burnsideB49_rhoHat_injective C hreal).comp (burnsideB49_psi_injective x y hΔ)
  rw [burnsideB49_Ep, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_zmod]

theorem burnsideB49_tau_ne_zero_of (w : Fin 2 → K) (h : burnsideB49_tau w ≠ 1) : w ≠ 0 := by
  intro hw
  apply h
  rw [hw, burnsideB49_tau_zero]

theorem burnsideB49_tau_rank_one (w : Fin 2 → K) (z : Fin 3 → K) :
    ((burnsideB49_tau w : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec z =
      z + ((Pi.single 2 (1 : K) : Fin 3 → K) ⬝ᵥ z) • burnsideB49_vec3 w 0 := by
  rw [burnsideB49_tau_mulVec]
  funext i
  fin_cases i <;> simp [burnsideB49_vec3, burnsideB49_ysub, dotProduct_single]

theorem burnsideB49_vec3_ne_zero (w : Fin 2 → K) (hw : w ≠ 0) : burnsideB49_vec3 w 0 ≠ 0 := by
  intro h
  apply hw
  funext i
  have := congrFun h (Fin.castSucc i)
  fin_cases i <;> simpa [burnsideB49_vec3] using this

theorem burnsideB49_single_ne_zero : (Pi.single 2 (1 : K) : Fin 3 → K) ≠ 0 := by
  intro h
  have := congrFun h 2
  simp at this

theorem burnsideB49_Ep_isTransv (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (x y : Fin 2 → K) (hΔ : burnsideB49_det2 x y ≠ 0) :
    CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U f (burnsideB49_Ep C x y) := by
  refine ⟨burnsideB49_Ep_le C x y, burnsideB49_Ep_card C hreal x y hΔ, ?_, ?_⟩
  · rintro e ⟨m, rfl⟩ hne
    have hs : burnsideB49_psi x y m ≠ 1 := by
      intro h
      apply hne
      change burnsideB49_rhoHat C (burnsideB49_psi x y m) = 1
      rw [h, map_one]
    have hw := burnsideB49_tau_ne_zero_of _ hs
    exact burnsideB49_isTransv_of_rank_one C hf _ _ _ (burnsideB49_vec3_ne_zero _ hw)
      burnsideB49_single_ne_zero (fun z => burnsideB49_tau_rank_one _ z)
  · refine ⟨{v | (Multiplicative.toAdd (C.qV v)) 2 = 0}, ?_⟩
    rintro e ⟨m, rfl⟩ hne
    have hs : burnsideB49_psi x y m ≠ 1 := by
      intro h
      apply hne
      change burnsideB49_rhoHat C (burnsideB49_psi x y m) = 1
      rw [h, map_one]
    have hw := burnsideB49_tau_ne_zero_of _ hs
    change CFSG.ASVolI.ChB.axisPre U (burnsideB49_rhoHat C (burnsideB49_psi x y m)) = _
    rw [burnsideB49_axisPre_rhoHat]
    ext v
    simp only [Set.mem_setOf_eq]
    rw [burnsideB49_psi_apply, burnsideB49_tau_rank_one]
    constructor
    · intro h
      have h1 : ((Pi.single 2 (1 : K) : Fin 3 → K) ⬝ᵥ Multiplicative.toAdd (C.qV v)) •
          burnsideB49_vec3 (burnsideB49_wxy x y (Multiplicative.toAdd m)) 0 = 0 := by
        have := h
        simpa using this
      rcases smul_eq_zero.1 h1 with h2 | h2
      · simpa [dotProduct_single] using h2
      · exact absurd h2 (burnsideB49_vec3_ne_zero _ hw)
    · intro h
      have : ((Pi.single 2 (1 : K) : Fin 3 → K) ⬝ᵥ Multiplicative.toAdd (C.qV v)) = 0 := by
        simpa [dotProduct_single] using h
      rw [this]
      simp

end FTwoEp

section FTwoFinal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] [CharP K 2] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_psi_one_zero (x y : Fin 2 → K) :
    burnsideB49_psi x y (Multiplicative.ofAdd ((1 : ZMod 2), (0 : ZMod 2))) = burnsideB49_tau x := by
  rw [burnsideB49_psi_apply, toAdd_ofAdd]
  simp [burnsideB49_wxy]

theorem burnsideB49_psi_zero_one (x y : Fin 2 → K) :
    burnsideB49_psi x y (Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 2))) = burnsideB49_tau y := by
  rw [burnsideB49_psi_apply, toAdd_ofAdd]
  simp [burnsideB49_wxy]

theorem burnsideB49_Ep_not_root (C : burnsideB49_Coord3 G U K π)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (x y : Fin 2 → K) (hΔ : burnsideB49_det2 x y ≠ 0) :
    ¬ CFSG.ASVolI.ChB.InRootGroup G π (burnsideB49_Ep C x y) := by
  intro h
  rw [burnsideB49_inRoot_iff C hreal _ (burnsideB49_Ep_le C x y)] at h
  have h1 : burnsideB49_tau x ∈ burnsideB49_Etil C (burnsideB49_Ep C x y) := by
    show burnsideB49_rhoHat C (burnsideB49_tau x) ∈ burnsideB49_Ep C x y
    rw [← burnsideB49_psi_one_zero x y]
    exact ⟨_, rfl⟩
  have h2 : burnsideB49_tau y ∈ burnsideB49_Etil C (burnsideB49_Ep C x y) := by
    show burnsideB49_rhoHat C (burnsideB49_tau y) ∈ burnsideB49_Ep C x y
    rw [← burnsideB49_psi_zero_one x y]
    exact ⟨_, rfl⟩
  apply hΔ
  exact burnsideB49_dep_of_root _ 1 h h1 h2 (w₁ := x) (w₂ := y) (by simp) (by simp)

theorem burnsideB49_Ep_Rel (C : burnsideB49_Coord3 G U K π) (x y : Fin 2 → K)
    (hq : CFSG.Quasithin.IsQuadratic (burnsideB49_Ep C x y)) :
    burnsideB49_Rel C.toCore3 x y := by
  intro a
  have h1 : burnsideB49_rhoHat C (burnsideB49_tau x) ∈ burnsideB49_Ep C x y := by
    rw [← burnsideB49_psi_one_zero x y]
    exact ⟨_, rfl⟩
  have h2 : burnsideB49_rhoHat C (burnsideB49_tau y) ∈ burnsideB49_Ep C x y := by
    rw [← burnsideB49_psi_zero_one x y]
    exact ⟨_, rfl⟩
  exact burnsideB49_quad_R C _ hq _ _ h1 h2 a

end FTwoFinal

section Spread3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {F : Type} [Field F] [Finite F] [CharP F 2] {A : Type} [AddCommGroup A]

theorem burnsideB49_exists_det2_ne (x : Fin 2 → F) (hx : x ≠ 0) : ∃ z : Fin 2 → F, burnsideB49_det2 x z ≠ 0 := by
  by_cases h0 : x 0 = 0
  · have h1 : x 1 ≠ 0 := by
      intro h1
      apply hx
      funext i
      fin_cases i
      · exact h0
      · exact h1
    refine ⟨![1, 0], ?_⟩
    simp [burnsideB49_det2, h1]
  · refine ⟨![0, 1], ?_⟩
    simp [burnsideB49_det2, h0]

theorem burnsideB49_spread2 (D : burnsideB49_Core3 F A)
    (hind : ∀ x y : Fin 2 → F, burnsideB49_det2 x y ≠ 0 → burnsideB49_Rel D x y) :
    burnsideB49_QuadHyp D := by
  rw [burnsideB49_QuadHyp_iff]
  intro x y
  by_cases hx : x = 0
  · rw [hx]
    exact burnsideB49_Rel_zero_left D y
  · obtain ⟨z, hz⟩ := burnsideB49_exists_det2_ne x hx
    by_cases hy : burnsideB49_det2 x y = 0
    · have h1 := hind x z hz
      have h2 : burnsideB49_Rel D x (y + z) := by
        apply hind
        rw [burnsideB49_det2_add, hy, zero_add]
        exact hz
      have h3 := burnsideB49_Rel_add_right D h2 (burnsideB49_Rel_neg_right D h1)
      simpa using h3
    · exact hind x y hy

end Spread3

section FinalThree

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49_QuadHyp_conj_one {F : Type} [Field F] {A : Type} [AddCommGroup A]
    (D : burnsideB49_Core3 F A) (h : burnsideB49_QuadHyp D) :
    burnsideB49_QuadHyp (D.conj 1) := by
  intro w w' a
  have := h w w' a
  simpa [burnsideB49_Core3.conj] using this

variable {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)} {U : Subgroup V}
  {K : Type} [Field K] [Finite K] {π : ↥(StatedSL 3 K) →* ↥G}

theorem burnsideB49_part1_three_two (hV : ∀ v : V, v ^ 2 = 1) (hK : Nat.card K = 2 ^ 2)
    (hreal : (CFSG.Quasithin.FFModel.nat (StatedSL 3 K)).RealizesVia G U ⊥ π)
    (hquot : CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U)
    (hE2 : ∀ E' : Subgroup (MulAut V), CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U 2 E' →
      ¬ CFSG.ASVolI.ChB.InRootGroup G π E' → CFSG.Quasithin.IsQuadratic E') :
    CFSG.ASVolI.ChB.SplitsOver G U := by
  haveI := burnsideB49_charP_two (K := K) (f := 2) (by omega) hK
  obtain ⟨C⟩ := burnsideB49_coord3_exists hreal hquot
  have hind : ∀ x y : Fin 2 → K, burnsideB49_det2 x y ≠ 0 → burnsideB49_Rel C.toCore3 x y :=
    fun x y hΔ => burnsideB49_Ep_Rel C x y
      (hE2 _ (burnsideB49_Ep_isTransv C hreal hK x y hΔ) (burnsideB49_Ep_not_root C hreal x y hΔ))
  exact burnsideB49_split_of_quad hV C hreal.1 1
    (burnsideB49_QuadHyp_conj_one _ (burnsideB49_spread2 C.toCore3 hind))

end FinalThree

section Part1All

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem burnsideB49_part1 :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (n f : ℕ), ((4 ≤ n ∧ f = 1) ∨ (n = 3 ∧ 1 ≤ f)) →
      ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
      ∀ (G : Subgroup (MulAut V)) (U : Subgroup V) (π : ↥(StatedSL n K) →* ↥G),
        (CFSG.Quasithin.FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π →
        (CFSG.ASVolI.ChB.QuotIsoSub G U ∨ CFSG.ASVolI.ChB.QuotIsoDual G U) →
        (∀ E : Subgroup (MulAut V), CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U f E →
          CFSG.Quasithin.IsQuadratic E →
          (n = 3 → ¬ CFSG.ASVolI.ChB.InRootGroup G π E) →
          (n = 3 → f = 2 → ∀ E' : Subgroup (MulAut V),
            CFSG.ASVolI.ChB.IsTransvFourGrpFixedAxis G U f E' →
              ¬ CFSG.ASVolI.ChB.InRootGroup G π E' → CFSG.Quasithin.IsQuadratic E') →
            CFSG.ASVolI.ChB.SplitsOver G U) := by
  intro V _ _ hV n f hnf K _ _ hK G U π hreal hquot E hE hq hnr hE2
  have hf1 : 1 ≤ f := by
    rcases hnf with ⟨_, h⟩ | ⟨_, h⟩
    · omega
    · exact h
  by_cases hf : f = 1
  · subst hf
    have hn : 3 ≤ n := by
      rcases hnf with ⟨h, _⟩ | ⟨h, _⟩
      · omega
      · omega
    exact burnsideB49_part1_f1 hV U G hn (by simpa using hK) hreal hquot E hE hq
  · have hn3 : n = 3 := by
      rcases hnf with ⟨_, h⟩ | ⟨h, _⟩
      · exact absurd h hf
      · exact h
    subst hn3
    by_cases hf2 : f = 2
    · subst hf2
      exact burnsideB49_part1_three_two hV hK hreal hquot (hE2 rfl rfl)
    · exact burnsideB49_part1_three_big hV (by omega) hK hreal hquot E hE hq (hnr rfl)

end Part1All

section Reduction

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
@[expose] def burnsideB49_Part2i : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n f : ℕ), ((4 ≤ n ∧ f = 1) ∨ (n = 3 ∧ 1 ≤ f)) →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
    ∀ (G : Subgroup (MulAut V)) (U : Subgroup V) (π : ↥(StatedSL n K) →* ↥G),
      (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π →
      (QuotIsoSub G U ∨ QuotIsoDual G U) →
      ∀ T : Subgroup (MulAut V), IsSylowTwoOf T G → ∀ A : Subgroup (MulAut V),
        IsFFStarOffender T A → SplitsOver G U

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
@[expose] def burnsideB49_Part2ii : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n f : ℕ), ((4 ≤ n ∧ f = 1) ∨ (n = 3 ∧ 1 ≤ f)) →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
    ∀ (G : Subgroup (MulAut V)) (U : Subgroup V) (π : ↥(StatedSL n K) →* ↥G),
      (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π →
      (QuotIsoSub G U ∨ QuotIsoDual G U) →
      ∀ T : Subgroup (MulAut V), IsSylowTwoOf T G → ∀ A : Subgroup (MulAut V),
        IsFFStarOffender T A → (n = 3 → QuotIsoSub G U ∧ qOf G = ((1 : ℚ) : WithTop ℚ))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
@[expose] def burnsideB49_Part2iii : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n f : ℕ), ((4 ≤ n ∧ f = 1) ∨ (n = 3 ∧ 1 ≤ f)) →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
    ∀ (G : Subgroup (MulAut V)) (U : Subgroup V) (π : ↥(StatedSL n K) →* ↥G),
      (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π →
      (QuotIsoSub G U ∨ QuotIsoDual G U) →
      ∀ T : Subgroup (MulAut V), IsSylowTwoOf T G → ∀ A : Subgroup (MulAut V),
        IsFFStarOffender T A →
        (n = 4 → QuotIsoDual G U → A = Jj T 0 ∧ rk ↥A = 4 ∧ qOf G = ((1 : ℚ) : WithTop ℚ))

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB in
@[expose] def burnsideB49_Part2iv : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (n f : ℕ), ((4 ≤ n ∧ f = 1) ∨ (n = 3 ∧ 1 ≤ f)) →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
    ∀ (G : Subgroup (MulAut V)) (U : Subgroup V) (π : ↥(StatedSL n K) →* ↥G),
      (FFModel.nat (StatedSL n K)).RealizesVia G U ⊥ π →
      (QuotIsoSub G U ∨ QuotIsoDual G U) →
      ∀ T : Subgroup (MulAut V), IsSylowTwoOf T G → ∀ A : Subgroup (MulAut V),
        IsFFStarOffender T A →
        (n = 5 → QuotIsoDual G U → qOf G = ((5 / 6 : ℚ) : WithTop ℚ) ∧
          ((IsElemAbelian 2 A ∧ Nat.card A = 16 ∧ ∃ P M : Subgroup (MulAut V),
              (IsSubspaceStab G U 1 P ∨ IsSubspaceStab G U 4 P) ∧ IsLeviComplement P M ∧ A ≤ M) ∨
            (IsElemAbelian 2 A ∧ (Nat.card A = 32 ∨ Nat.card A = 64) ∧ ∃ P : Subgroup (MulAut V),
              (IsSubspaceStab G U 2 P ∨ IsSubspaceStab G U 3 P) ∧ A ≤ pCoreOf 2 P)))

theorem burnsideB49_B_4_9_of_parts
    (h1 : burnsideB49_Part2i) (h2 : burnsideB49_Part2ii) (h3 : burnsideB49_Part2iii)
    (h4 : burnsideB49_Part2iv) : B_4_9 := by
  unfold B_4_9
  intro V _ _ hV n f hnf K _ _ hK G U π hreal hquot
  refine ⟨burnsideB49_part1 V hV n f hnf K hK G U π hreal hquot, ?_⟩
  intro T hT A hA
  exact ⟨h1 V hV n f hnf K hK G U π hreal hquot T hT A hA,
    h2 V hV n f hnf K hK G U π hreal hquot T hT A hA,
    h3 V hV n f hnf K hK G U π hreal hquot T hT A hA,
    h4 V hV n f hnf K hK G U π hreal hquot T hT A hA⟩

end Reduction

end CFSG.ASVolI
