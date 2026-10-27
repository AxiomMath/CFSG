module

public import CFSG.Quasithin.Background.SzG11SStmts
public import CFSG.Quasithin.Background.G117StepsB
public import CFSG.Quasithin.Background.G117A6Norm
public import CFSG.Quasithin.Background.SzG11SHat
public import CFSG.Quasithin.Background.G117A6
public import CFSG.Quasithin.Background.G117Layer
public import CFSG.Quasithin.Background.G117Lt2
public import CFSG.Quasithin.Background.G117Lt3
public import CFSG.Quasithin.Background.G117Lt4
public import CFSG.Quasithin.Background.G117Setup
public import CFSG.Quasithin.Background.G117StepsA
public import CFSG.Quasithin.Background.G93ApplyStmt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G117

namespace G117

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

variable [Finite V]

structure Ctx (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (m : ℕ) :
    Prop where
  setup : G11Setup B Γ v₁ W X X₀ L
  props : G116Props B Γ v₁ X L I
  faithful : FaithfulOn X I
  card : Nat.card X = 2 ^ m

namespace Ctx

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} {m : ℕ}
  (c : Ctx B Γ v₁ W X X₀ L I m)

include c

theorem h108 : G108Hyp B Γ v₁ W X X₀ L := c.setup.h108

theorem invariantH : Invariant (normalClosure Γ L) I := c.props.1.1

theorem invariantX : Invariant X I := props_invariantX c.props

theorem invariantK : Invariant (normalClosure Γ L ⊔ X) I :=
  c.invariantH.sup_subgroup c.invariantX

theorem isIrr : IsIrr (normalClosure Γ L) I :=
  (props_irrPlus c.props).isIrr c.h108.fixedSpace_H

theorem finrank_V_le : Module.finrank (ZMod 2) V ≤ 2 * (m + 1) := by
  have h := c.h108.toG101Hyp.dim_le_two_mul
  have hdvd : X₀.relIndex X ∣ 2 ^ m := by
    rw [← c.card]
    exact Subgroup.relIndex_dvd_card X₀ X
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hlog : Nat.log 2 (X₀.relIndex X) ≤ m := by
    rw [hjeq, Nat.log_pow Nat.one_lt_two]
    exact hj
  omega

theorem finrank_I_le : Module.finrank (ZMod 2) ↥I ≤ 2 * (m + 1) :=
  (Submodule.finrank_le I).trans c.finrank_V_le

theorem two_mul_finrank_le (hne : I ≠ ⊤) :
    2 * Module.finrank (ZMod 2) ↥I ≤ Module.finrank (ZMod 2) V := by
  have h108 := c.h108
  obtain ⟨U', hU'inv, hcompl⟩ := exists_invariant_compl h108.sSup_isIrr c.invariantH
  have hU'ne : U' ≠ ⊥ := by
    intro h
    rw [h] at hcompl
    apply hne
    simpa using hcompl.sup_eq_top
  obtain ⟨J, hJU, hJirr⟩ := exists_isIrr_le hU'inv hU'ne
  have hJplus : IrrPlus (normalClosure Γ L) J := hJirr.irrPlus h108.fixedSpace_H
  obtain ⟨φ, -⟩ := props_homogeneous c.props I J (props_irrPlus c.props) hJplus
  have h1 : Module.finrank (ZMod 2) ↥I = Module.finrank (ZMod 2) ↥J := LinearEquiv.finrank_eq φ
  have h2 : Module.finrank (ZMod 2) ↥J ≤ Module.finrank (ZMod 2) ↥U' := Submodule.finrank_mono hJU
  have h3 := Submodule.finrank_add_eq_of_isCompl hcompl
  omega

theorem g93 (hApply : G93ApplyStmt) :
    G93ConclDimensionOnly (restrictRange (normalClosure Γ L ⊔ X) I c.invariantK)
      (restrictRange (normalClosure Γ L) I c.invariantH) m := by
  have h108 := c.h108
  have hHΓ : normalClosure Γ L ≤ Γ := h108.H_le
  refine hApply V Γ (normalClosure Γ L ⊔ X) (normalClosure Γ L) L X I m c.invariantK c.invariantH
    c.setup.cx.sqtk (sup_le hHΓ h108.X_le) le_sup_left (fun k hk h hh => ?_) c.isIrr
    (props_faithful c.props) le_sup_right h108.toG101Hyp.X_isElemAbelian c.card c.faithful
    c.finrank_I_le h108.component (le_normalClosure Γ L) h108.noncomm
    (g118_hEq h108.component c.setup.numConj h108.fixedSpace_H (props_homogeneous c.props)
      (props_irrPlus c.props) (props_faithful c.props))
  exact normalClosure_normal Γ L k ((sup_le hHΓ h108.X_le : normalClosure Γ L ⊔ X ≤ Γ) hk) h hh

end Ctx

end G117

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G117

@[expose] def G117Step0 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case0 (G117.topH Γ L) m → False

@[expose] def G117Step2 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case2 (G117.topK Γ L X) (G117.topH Γ L) m → False

@[expose] def G117Step4 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case4 (G117.topH Γ L) m → False

@[expose] def G117Step6 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case6 (G117.topH Γ L) m → False

@[expose] def G117Step7 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case7 (G117.topH Γ L) m → False

@[expose] def G117Step9 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case9 (G117.topH Γ L) m → False

@[expose] def G117Step10 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case10 (G117.topH Γ L) m → False

@[expose] def G117Step12 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case12 (G117.topH Γ L) m → False

@[expose] def G117Step15 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case15 (G117.topH Γ L) m → False

@[expose] def G117Step16 : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L ⊤ m → G93Case16 (G117.topH Γ L) m → False

@[expose] def G117StepLt : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
    (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) (m : ℕ),
    G117.Ctx B Γ v₁ W X X₀ L I m → ∀ hH : Invariant (normalClosure Γ L) I,
    I ≠ ⊤ → Module.finrank (ZMod 2) V = 8 → m = 3 → Module.finrank (ZMod 2) ↥I = 4 →
      IsPermCoreModule (restrictRange (normalClosure Γ L) I hH) (alternatingGroup (Fin 6)) →
      EndIsField (restrictRange (normalClosure Γ L) I hH) 1 → False

theorem g11_7_of_steps (hApply : G93ApplyStmt) (s0 : G117Step0) (s2 : G117Step2)
    (s4 : G117Step4) (s6 : G117Step6) (s7 : G117Step7) (s9 : G117Step9) (s10 : G117Step10)
    (s12 : G117Step12) (s15 : G117Step15) (s16 : G117Step16) (sLt : G117StepLt) : G117Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs I hI
  suffices hnf : ¬ FaithfulOn X I from
    ⟨hnf, fun htop => hnf (by
      rw [htop]
      exact faithfulOn_iff.2 fun k _ hk => LinearEquiv.ext fun v => hk v Submodule.mem_top)⟩
  intro hfaith
  obtain ⟨m, hm⟩ := hs.h108.toG101Hyp.exists_card_X
  have c : G117.Ctx B Γ v₁ W X X₀ L I m := ⟨hs, hI, hfaith, hm⟩
  have hconcl := c.g93 hApply
  have hsd := G93ConclDimensionOnly.of_selfDual hconcl
    (G117.selfDual_restrictRange c.invariantH (G117.props_selfDual hI))
  by_cases htop : I = ⊤
  · subst htop
    rcases hsd with h0 | h2 | h4 | h6 | h7 | h9 | h10 | h12 | h15 | h16
    · exact s0 V B Γ v₁ W X X₀ L m c h0
    · exact s2 V B Γ v₁ W X X₀ L m c h2
    · exact s4 V B Γ v₁ W X X₀ L m c h4
    · exact s6 V B Γ v₁ W X X₀ L m c h6
    · exact s7 V B Γ v₁ W X X₀ L m c h7
    · exact s9 V B Γ v₁ W X X₀ L m c h9
    · exact s10 V B Γ v₁ W X X₀ L m c h10
    · exact s12 V B Γ v₁ W X X₀ L m c h12
    · exact s15 V B Γ v₁ W X X₀ L m c h15
    · exact s16 V B Γ v₁ W X X₀ L m c h16
  · have h2d : 2 * Module.finrank (ZMod 2) ↥I ≤ Module.finrank (ZMod 2) V :=
      c.two_mul_finrank_le htop
    have hd : Module.finrank (ZMod 2) V ≤ 2 * (m + 1) := c.finrank_V_le
    rcases hsd with h0 | h2 | h4 | h6 | h7 | h9 | h10 | h12 | h15 | h16
    · obtain ⟨⟨hm4, hd10, -⟩, -⟩ := h0
      have hd10' : Module.finrank (ZMod 2) ↥I = 10 := hd10
      omega
    · obtain ⟨⟨hm5, hd12, -⟩, -⟩ := h2
      have hd12' : Module.finrank (ZMod 2) ↥I = 12 := hd12
      omega
    · obtain ⟨⟨hm2, hd6, hm3, -⟩, -⟩ := h4
      have hd6' : Module.finrank (ZMod 2) ↥I = 6 := hd6
      omega
    · obtain ⟨n, ⟨hn2, hdn, hnm, hmn, -⟩, -⟩ := h6
      have hdn' : Module.finrank (ZMod 2) ↥I = 2 * n := hdn
      omega
    · obtain ⟨a, ⟨ha1, hda, ham, hma, -⟩, -⟩ := h7
      have hda' : Module.finrank (ZMod 2) ↥I = 4 * a := hda
      omega
    · obtain ⟨n, ⟨hn1, hdn, hnm, hmn, -, hperm⟩, hend, -⟩ := h9
      have hdn' : Module.finrank (ZMod 2) ↥I = 4 * n := hdn
      have hn : n = 1 := by omega
      subst hn
      exact sLt V B Γ v₁ W X X₀ L I m c c.invariantH htop (by omega) (by omega) (by omega)
        (hperm rfl) hend
    · obtain ⟨n, ⟨hn1, hdn, hnm, hmn, -⟩, -⟩ := h10
      have hdn' : Module.finrank (ZMod 2) ↥I = 6 * n := hdn
      omega
    · obtain ⟨⟨hm2, hd6, hm4, -⟩, -⟩ := h12
      have hd6' : Module.finrank (ZMod 2) ↥I = 6 := hd6
      omega
    · obtain ⟨n, ⟨hn2, hdn, hnm, hmn, -⟩, -⟩ := h15
      have hdn' : Module.finrank (ZMod 2) ↥I = 4 * n := hdn
      omega
    · obtain ⟨⟨hm3, hd8, -⟩, -⟩ := h16
      have hd8' : Module.finrank (ZMod 2) ↥I = 8 := hd8
      omega

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G117 CFSG.Assembly.LowTwoRank

namespace G117

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

section Conclusions

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ X : Subgroup (GLV V)}

theorem fix_concl2 (h : G112Concl2 Γ) : G112ConclusionFixS B Γ X := by
  unfold G112ConclusionFixS
  tauto

theorem fix_concl4 (h : G112Concl4 Γ) : G112ConclusionFixS B Γ X := by
  unfold G112ConclusionFixS
  tauto

theorem fix_concl5 (h : G112Concl5 B Γ) : G112ConclusionFixS B Γ X := by
  unfold G112ConclusionFixS
  tauto

theorem fix_concl6 (h : G112Concl6 Γ) : G112ConclusionFixS B Γ X := by
  unfold G112ConclusionFixS
  tauto

theorem fix_concl7 (h : G112Concl7S Γ X) : G112ConclusionFixS B Γ X := by
  unfold G112ConclusionFixS
  tauto

theorem fix_concl10 (h : G112Concl10 Γ X) : G112ConclusionFixS B Γ X := by
  unfold G112ConclusionFixS
  tauto

theorem fix_concl11 (h : G112Concl11 Γ) : G112ConclusionFixS B Γ X := by
  unfold G112ConclusionFixS
  tauto

theorem fix_concl13 (h : G112Concl13S Γ) : G112ConclusionFixS B Γ X := by
  unfold G112ConclusionFixS
  tauto

theorem fix_concl6' (h : G112Concl6U33S Γ) : G112ConclusionFixS B Γ X :=
  Or.inr (Or.inr h)

end Conclusions

variable [Finite V]

theorem step0 (h : NoConfigM12) : G117Step0 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h0
  obtain ⟨⟨hm, hd, hperm⟩, hend, -⟩ := h0
  have hdV : Module.finrank (ZMod 2) V = 10 := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  have hX : Nat.card ↥X = 16 := by
    rw [c.card, hm]
    norm_num
  exact h V B Γ v₁ W X X₀ L c.setup.toConf c.props (isPermCoreModule_of_restrictRange_top hperm)
    hX hdV (centralizer_trivial hend)

theorem step16 : G117Step16 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h16
  obtain ⟨⟨-, hd, hL28⟩, hend, -⟩ := h16
  obtain ⟨φ, -⟩ := hL28
  have hF := fstar_map_eq_normalClosure c.h108.component (centralizer_trivial hend)
  have hd8 : Module.finrank (ZMod 2) V = 8 := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  exact c.setup.cx.notConcl (fix_concl11 ⟨hd8, ⟨(fstarEquiv hF).trans ((restrictRangeTop _).trans
    (φ.trans (specialLinearGroupEquivStatedSL 2 (GaloisField 2 3)).symm))⟩⟩)

theorem step4 : G117Step4 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h4
  obtain ⟨⟨-, hd, -, hperm⟩, hend, -⟩ := h4
  obtain ⟨φ₀, β, hsurj, hker, hequ⟩ := isPermCoreModule_of_restrictRange_top hperm
  have hF := fstar_map_eq_normalClosure c.h108.component (centralizer_trivial hend)
  have hd6 : Module.finrank (ZMod 2) V = 6 := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    rcases (hker u).1 hu with h | ⟨he, -⟩
    · exact h
    · exact absurd he (by decide)
  let e : ↥(permCore 7) ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective β ⟨hinj, hsurj⟩
  refine c.setup.cx.notConcl (fix_concl4 ⟨hd6, (fstarEquiv hF).trans φ₀, e.symm, fun γ v => ?_⟩)
  set u : ↥(permCore 7) := e.symm v with hu
  have hmem := permAct_mem_permCore
    ((φ₀ (fstarEquiv hF γ) : ↥(alternatingGroup (Fin 7))) : Equiv.Perm (Fin 7)) u.2
  have h1 : β ⟨_, hmem⟩ = ((γ : ↥Γ) : GLV V) (β u) := hequ (fstarEquiv hF γ) u ⟨_, hmem⟩ rfl
  have h2 : β u = v := e.apply_symm_apply v
  have h3 : e.symm (((γ : ↥Γ) : GLV V) v) = ⟨_, hmem⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    show _ = β ⟨_, hmem⟩
    rw [h1, h2]
  rw [h3]
  rfl

theorem step6 (hL2 : NoConfigL2) : G117Step6 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h6
  obtain ⟨n, ⟨hn2, hd, -, -, hnat⟩, -, -⟩ := h6
  have hdV : Module.finrank (ZMod 2) V = 2 * n := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  by_cases hn3 : 3 ≤ n
  · exact hL2 V B Γ v₁ W X X₀ L c.setup.toConf c.props n hn3
      (isNaturalMatrixModule_of_restrictRange_top hnat)
  · have hn : n = 2 := by omega
    subst hn
    obtain ⟨φ, -⟩ := hnat
    have hcardH : Nat.card ↥(normalClosure Γ L) = 60 := by
      have h1 : Nat.card ↥(topH Γ L) = Nat.card ↥(normalClosure Γ L) := natCard_restrictRangeTop _
      rw [← h1, Nat.card_congr φ.toEquiv, natCard_statedSL_two (by norm_num)]
      norm_num
    exact c.setup.cx.notConcl (fix_concl2 ⟨by omega,
      Or.inl (ten_dvd_of_card_eq c.h108.L_le hcardH)⟩)

theorem step7 (hOm : NoConfigOm4Minus) : G117Step7 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h7
  obtain ⟨a, ⟨ha1, hd, -, -, ⟨φ⟩, b, b', hbb, hnat⟩, -, -⟩ := h7
  have hdV : Module.finrank (ZMod 2) V = 4 * a := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  by_cases ha2 : 2 ≤ a
  · exact hOm V B Γ v₁ W X X₀ L c.setup.toConf c.props a ha2 b b' hbb
      (isNaturalMatrixModule_of_restrictRange_top hnat)
  · have ha : a = 1 := by omega
    subst ha
    have hcardH : Nat.card ↥(normalClosure Γ L) = 60 := by
      have h1 : Nat.card ↥(topH Γ L) = Nat.card ↥(normalClosure Γ L) := natCard_restrictRangeTop _
      rw [← h1, Nat.card_congr φ.toEquiv, natCard_statedSL_two (by norm_num)]
      norm_num
    exact c.setup.cx.notConcl (fix_concl2 ⟨by omega,
      Or.inl (ten_dvd_of_card_eq c.h108.L_le hcardH)⟩)

theorem step9 (hSp : NoConfigSp4) : G117Step9 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h9
  obtain ⟨n, ⟨hn1, hd, -, -, hnat, hperm⟩, -, -⟩ := h9
  have hdV : Module.finrank (ZMod 2) V = 4 * n := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  by_cases hn2 : 2 ≤ n
  · exact hSp V B Γ v₁ W X X₀ L c.setup.toConf c.props n hn2
      (isNaturalMatrixModule_of_restrictRange_top hnat)
  · have hn : n = 1 := by omega
    subst hn
    obtain ⟨φ, -⟩ := hperm rfl
    have hcardH : Nat.card ↥(normalClosure Γ L) = 360 := by
      have h1 : Nat.card ↥(topH Γ L) = Nat.card ↥(normalClosure Γ L) := natCard_restrictRangeTop _
      rw [← h1, Nat.card_congr φ.toEquiv, natCard_alternatingGroup_six]
    have hdvd : Nat.card ↥(normalClosure Γ L) ∣ Nat.card ↥Γ :=
      Subgroup.card_dvd_of_le c.h108.H_le
    rw [hcardH] at hdvd
    exact c.setup.cx.notConcl (fix_concl2 ⟨by omega, Or.inl (Dvd.dvd.trans (by norm_num) hdvd)⟩)

theorem step10 (hG2 : NoConfigG2) (hD : G22DerivedFacts) : G117Step10 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h10
  obtain ⟨n, ⟨hn1, hd, -, -, hnat⟩, hend, -⟩ := h10
  have hdV : Module.finrank (ZMod 2) V = 6 * n := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  by_cases hn2 : 2 ≤ n
  · exact hG2 V B Γ v₁ W X X₀ L c.setup.toConf c.props n hn2
      (isG2NaturalModule_of_restrictRange_top hnat)
  · have hn : n = 1 := by omega
    subst hn
    have hnatV := isG2NaturalModule_of_restrictRange_top hnat
    obtain ⟨φ, -⟩ := hnat
    let e := (restrictRangeTop (normalClosure Γ L)).trans φ
    have hcardH : Nat.card ↥(normalClosure Γ L) = 6048 := by
      rw [Nat.card_congr e.toEquiv]
      exact hD.1
    have hautH : Nat.card (MulAut ↥(normalClosure Γ L)) = 12096 := by
      rw [Nat.card_congr (MulAut.congr e).toEquiv]
      exact hD.2
    have hC1 : Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact eq_one_of_commute_of_endIsField_one hend (Subgroup.mem_centralizer_iff.1 hx.2)
    have hle := natCard_le_aut_mul_centralizer (Γ := Γ) (normalClosure_normal Γ L)
    rw [hC1, Subgroup.card_bot, hautH] at hle
    have hdvd : Nat.card ↥(normalClosure Γ L) ∣ Nat.card ↥Γ :=
      Subgroup.card_dvd_of_le c.h108.H_le
    rw [hcardH] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hpos : 0 < Nat.card ↥Γ := Nat.card_pos
    have hk1 : k = 1 ∨ k = 2 := by omega
    rcases hk1 with rfl | rfl
    · have hHΓeq : normalClosure Γ L = Γ :=
        Subgroup.eq_of_le_of_card_ge c.h108.H_le (by omega)
      rw [hHΓeq] at hnatV
      exact c.setup.cx.notConcl (fix_concl6' ⟨⟨by omega, by omega⟩, hnatV⟩)
    · exact c.setup.cx.notConcl (fix_concl6 ⟨by omega, by omega⟩)

theorem step12 (h : A8OrthogonalFact) : G117Step12 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h12
  obtain ⟨⟨-, hd, -, hperm⟩, -, -⟩ := h12
  have hd6 : Module.finrank (ZMod 2) V = 6 := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  exact c.setup.cx.notConcl (fix_concl5 (h V B (normalClosure Γ L) Γ hd6
    (isPermCoreModule_of_restrictRange_top hperm) c.h108.alt c.h108.nondegenerate
    c.h108.isometry c.h108.H_le (normalClosure_normal Γ L)))

theorem step2 (hM22 : AutHatM22Bound) : G117Step2 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h2
  obtain ⟨⟨-, hd, ⟨N, hNnormal, hNindex, hN, hHN⟩, hcard⟩, hend, -⟩ := h2
  have hd12 : Module.finrank (ZMod 2) V = 12 := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  let e : ↥(normalClosure Γ L) ≃* ↥N :=
    (restrictRangeTop (normalClosure Γ L)).trans ((MulEquiv.subgroupCongr hHN).trans
      (N.equivMapOfInjective (topK Γ L X).subtype (topK Γ L X).subtype_injective).symm)
  have hautH : Nat.card (MulAut ↥(normalClosure Γ L)) ≤ 887040 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact hM22 ↥N hN
  have hC : Nat.card ↥(Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) ≤ 3 := by
    have h1 : Nat.card ↥(Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) ∣ 3 := by
      have := natCard_centralizer_dvd (K := normalClosure Γ L) (e := 2) (by norm_num) hend
      simpa using this
    exact (Subgroup.card_le_of_le inf_le_right).trans (Nat.le_of_dvd (by norm_num) h1)
  have hle := natCard_le_aut_mul_centralizer (Γ := Γ) (normalClosure_normal Γ L)
  have hup : Nat.card ↥Γ ≤ 2661120 :=
    hle.trans ((Nat.mul_le_mul hautH hC).trans (by norm_num))
  have hK : Nat.card ↥(normalClosure Γ L ⊔ X) ≤ Nat.card ↥Γ :=
    Subgroup.card_le_of_le (sup_le c.h108.H_le c.h108.X_le)
  have hKcard : Nat.card ↥(normalClosure Γ L ⊔ X) = 2661120 := by
    rw [← natCard_restrictRangeTop]
    exact hcard
  have hfinal : Nat.card ↥Γ = 2661120 := by omega
  have hHΓ : normalClosure Γ L ≤ Γ := c.h108.H_le
  have hNormΓ : ((normalClosure Γ L).subgroupOf Γ).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := normalClosure_normal Γ L (g : GLV V) g.2 (n : GLV V) hn
    simpa using this
  let e' : ↥((normalClosure Γ L).subgroupOf Γ) ≃* ↥N := (Subgroup.subgroupOfEquivOfLe hHΓ).trans e
  have hQ : CFSG.IsQuasisimple ↥((normalClosure Γ L).subgroupOf Γ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e'.symm hN.1
  have hZ : Nat.card ↥(Subgroup.center ↥((normalClosure Γ L).subgroupOf Γ)) = 3 :=
    (Nat.card_congr (Subgroup.centerCongr e'.symm).toEquiv).symm.trans hN.2.1
  have hCg : Nat.card ↥(Subgroup.centralizer (normalClosure Γ L : Set (GLV V))) ∣ 3 := by
    have := natCard_centralizer_dvd (K := normalClosure Γ L) (e := 2) (by norm_num) hend
    simpa using this
  have hC : Nat.card ↥(Subgroup.centralizer (((normalClosure Γ L).subgroupOf Γ : Subgroup ↥Γ) :
      Set ↥Γ)) ∣ 3 := by
    have hle : (Subgroup.centralizer (((normalClosure Γ L).subgroupOf Γ : Subgroup ↥Γ) :
        Set ↥Γ)).map Γ.subtype ≤ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' := Subgroup.mem_centralizer_iff.1 hz
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (hz' ⟨h, hHΓ hh⟩ hh)
    have h1 := Subgroup.card_dvd_of_le hle
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ Γ.subtype Γ.subtype_injective).toEquiv]
      at h1
    exact h1.trans hCg
  have hHat : IsHat ↥((normalClosure Γ L).subgroupOf Γ)
      ↥CFSG.Blueprint.NativeSporadic.M22 := by
    have hcen := Subgroup.map_center_eq e'
    refine ⟨hQ, hZ, ?_⟩
    obtain ⟨φ⟩ := hN.2.2
    exact ⟨(QuotientGroup.congr _ _ e' hcen).trans φ⟩
  have hcardN : Nat.card ↥N = 1330560 := by
    have hm := N.card_mul_index
    rw [hNindex, hcard] at hm
    omega
  have hcardH : Nat.card ↥((normalClosure Γ L).subgroupOf Γ) = 1330560 :=
    (Nat.card_congr e'.toEquiv).trans hcardN
  have hindex : ((normalClosure Γ L).subgroupOf Γ).index = 2 := by
    have hm := ((normalClosure Γ L).subgroupOf Γ).card_mul_index
    rw [hcardH, hfinal] at hm
    omega
  have h13S : G112Concl13S Γ :=
    ⟨⟨hd12, hfinal⟩, exists_normal_three_le_of_quasisimple _ hQ hZ hC,
      (normalClosure Γ L).subgroupOf Γ, hNormΓ, hindex, hHat⟩
  exact c.setup.cx.notConcl (fix_concl13 h13S)

end G117

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G117 CFSG.Assembly.LowTwoRank

namespace G117

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem step15 (hOm : NoConfigOm4Plus) (hOm4 : NoConfigOm4PlusFour) (hIso : Om4Plus4Iso) :
    G117Step15 := by
  intro V _ _ _ B Γ v₁ W X X₀ L m c h15
  obtain ⟨n, ⟨hn2, hd, -, -, hnat⟩, hend, -⟩ := h15
  have hdV : Module.finrank (ZMod 2) V = 4 * n := by
    have h1 : Module.finrank (ZMod 2) ↥(⊤ : Submodule (ZMod 2) V) = Module.finrank (ZMod 2) V :=
      finrank_top (ZMod 2) V
    omega
  by_cases hn3 : 3 ≤ n
  · exact hOm V B Γ v₁ W X X₀ L c.setup.toConf c.props n hn3
      (isNaturalMatrixModule_of_restrictRange_top hnat)
  · have hn : n = 2 := by omega
    subst hn
    have hnatV := isNaturalMatrixModule_of_restrictRange_top hnat
    have hXH : ¬ X ≤ normalClosure Γ L := fun h =>
      hOm4 V B Γ v₁ W X X₀ L c.setup.toConf c.props hnatV h
    have hnatV' := hnatV
    obtain ⟨φ, -⟩ := hnatV
    obtain ⟨ω⟩ := hIso
    let ι := φ.trans ω
    have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    have hcard4 : Fintype.card (GaloisField 2 2) = 4 := by
      rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
      norm_num
    obtain ⟨τ, γ, h1, h2, h3, h4, h5⟩ := exists_S3_in_SL2 (GaloisField 2 2) hcard4
    have hC : ∀ x ∈ Γ, (∀ h ∈ normalClosure Γ L, x * h = h * x) → x = 1 := by
      intro x hxΓ hx
      have hcent : x ∈ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) :=
        Subgroup.mem_centralizer_iff.2 fun h hh => (hx h hh).symm
      have h3' : x ^ 3 = 1 := by
        have := centralizer_pow_eq_one (K := normalClosure Γ L) (e := 2) (by norm_num) hend hcent
        simpa using this
      exact eq_one_of_central_of_prod_S3 c.setup.cx.sqtk c.h108.H_le ι h1 h2 h3 h4 h5 hxΓ
        (fun h hh => (hx h hh).symm) h3'
    have hF := fstar_map_eq_normalClosure c.h108.component hC
    have hnatF : IsNaturalMatrixModule ((CFSG.Open.genFittingFStar ↥Γ).map Γ.subtype)
        (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) := by
      rw [hF]
      exact hnatV'
    exact c.setup.cx.notConcl (fix_concl7 ⟨⟨by omega, ⟨(fstarEquiv hF).trans ι⟩, by
      rw [hF]
      exact hXH⟩, hnatF⟩)

end G117

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G117 CFSG.Open

namespace G117

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem step_lt (hE11 : E11Stmt) (hN6 : A6NormalizerBound) (hA6 : A6Facts) : G117StepLt := by
  intro V _ _ _ B Γ v₁ W X X₀ L I m c hH hne hV8 hm3 hI4 hperm hend
  obtain ⟨hAut, hD8, hE9⟩ := hA6
  have h108 := c.h108
  have hIplus : IrrPlus (normalClosure Γ L) I := props_irrPlus c.props
  have hhom := props_homogeneous c.props
  have hfaithH : FaithfulOn (normalClosure Γ L) I := props_faithful c.props
  have hHΓ : normalClosure Γ L ≤ Γ := h108.H_le
  have hNorm := normalClosure_normal Γ L
  have hperm0 := hperm
  obtain ⟨φ', -⟩ := hperm0
  let e : ↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 6)) :=
    (restrictRangeEquiv hH hfaithH).trans φ'
  have hH360 : Nat.card ↥(normalClosure Γ L) = 360 := by
    rw [Nat.card_congr e.toEquiv, natCard_alternatingGroup_six]
  have hX8 : Nat.card ↥X = 8 := by
    rw [c.card, hm3]
    norm_num
  have hXH : ¬ X ≤ normalClosure Γ L := by
    intro hXle
    let D : Subgroup ↥(alternatingGroup (Fin 6)) :=
      (X.subgroupOf (normalClosure Γ L)).map e.toMonoidHom
    have hDcard : Nat.card ↥D = 8 := by
      have h1 : Nat.card ↥D = Nat.card ↥(X.subgroupOf (normalClosure Γ L)) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv).symm
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXle).toEquiv, hX8]
    obtain ⟨a, b, hab⟩ := hD8 D hDcard
    apply hab
    obtain ⟨x, hx, hxa⟩ := a.2
    obtain ⟨y, hy, hyb⟩ := b.2
    apply Subtype.ext
    show (a : ↥(alternatingGroup (Fin 6))) * b = b * a
    rw [← hxa, ← hyb, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (h108.X_comm x.1 (Subgroup.mem_subgroupOf.1 hx) y.1
      (Subgroup.mem_subgroupOf.1 hy))

  have hcard3 : Nat.card (IrrSet Γ L) = 3 :=
    card_irrSet_eq_three h108 hE11 hIplus hhom hH hI4 hV8 hend
  have hne3 : ∀ J : IrrSet Γ L, J.1 ≠ ⊤ := by
    intro J hJ
    obtain ⟨φ, -⟩ := hhom I J.1 hIplus J.2
    have h1 : Module.finrank (ZMod 2) ↥I = Module.finrank (ZMod 2) ↥J.1 :=
      LinearEquiv.finrank_eq φ
    have h2 : Module.finrank (ZMod 2) ↥J.1 = Module.finrank (ZMod 2) V := by
      have h3 := LinearEquiv.finrank_eq (LinearEquiv.ofEq _ _ hJ)
      rw [h3]
      exact finrank_top (ZMod 2) V
    omega
  have hΓI : Nat.card ↥Γ = 3 * Nat.card ↥(stabilizerOf Γ I) :=
    card_eq_three_mul_card_stabilizer h108 hcard3 hne3 ⟨I, hIplus⟩
  have hKle : normalClosure Γ L ⊔ X ≤ stabilizerOf Γ I :=
    sup_le (fun k hk => ⟨hHΓ hk, c.invariantH.conjSub_eq hk⟩)
      (fun k hk => ⟨h108.X_le hk, c.invariantX.conjSub_eq hk⟩)
  have hK720 : 720 ≤ Nat.card ↥(normalClosure Γ L ⊔ X) := by
    have hHK : normalClosure Γ L ≤ normalClosure Γ L ⊔ X := le_sup_left
    obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hHK
    rw [hH360] at hk
    have hpos : 0 < Nat.card ↥(normalClosure Γ L ⊔ X) := Nat.card_pos
    have hk0 : k ≠ 0 := by
      rintro rfl
      omega
    have hk1 : k ≠ 1 := by
      rintro rfl
      apply hXH
      have : normalClosure Γ L = normalClosure Γ L ⊔ X :=
        Subgroup.eq_of_le_of_card_ge hHK (by rw [hk, hH360])
      rw [this]
      exact le_sup_right
    omega
  have hΓI720 : 720 ≤ Nat.card ↥(stabilizerOf Γ I) := hK720.trans (Subgroup.card_le_of_le hKle)
  have hΓ2160 : 2160 ≤ Nat.card ↥Γ := by omega
  set Cg : Subgroup (GLV V) := Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) with hCg
  have hAut1440 : Nat.card (MulAut ↥(normalClosure Γ L)) = 1440 := hAut _ ⟨e⟩
  have hle1 : Nat.card ↥Γ ≤ 1440 * Nat.card ↥Cg := by
    have := natCard_le_aut_mul_centralizer (Γ := Γ) hNorm
    rwa [hAut1440] at this
  have hC2 : 2 ≤ Nat.card ↥Cg := by
    by_contra hlt
    have h1 : Nat.card ↥Cg ≤ 1 := by omega
    have h2 := Nat.mul_le_mul_left 1440 h1
    omega
  let φ₃ : IrrSet Γ L ≃ Fin 3 := (Finite.equivFin (IrrSet Γ L)).trans (finCongr hcard3)
  let ρΓ : ↥Γ →* Equiv.Perm (Fin 3) :=
    (φ₃.permCongrHom : Equiv.Perm (IrrSet Γ L) →* Equiv.Perm (Fin 3)).comp (irrAct h108)
  have hρΓ : ∀ (γ : ↥Γ) (J : IrrSet Γ L), ρΓ γ (φ₃ J) = φ₃ (irrAct h108 γ J) := by
    intro γ J
    show φ₃ (irrAct h108 γ (φ₃.symm (φ₃ J))) = _
    rw [Equiv.symm_apply_apply]
  let ρ : ↥Cg →* Equiv.Perm (Fin 3) := ρΓ.comp (Subgroup.inclusion inf_le_left)
  have hρ : ∀ x : ↥Cg, ρ x = ρΓ ⟨(x : GLV V), x.2.1⟩ := fun x => rfl
  have hcommC : ∀ x : ↥Cg, ∀ h ∈ normalClosure Γ L, h * (x : GLV V) = (x : GLV V) * h :=
    fun x h hh => Subgroup.mem_centralizer_iff.1 x.2.2 h hh
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hfixall : ∀ J : Submodule (ZMod 2) V, IrrPlus (normalClosure Γ L) J →
        conjSub (x : GLV V) J = J := by
      intro J hJ
      have h1 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ (φ₃ ⟨J, hJ⟩)) (hρ x ▸ hx)
      simp only [Equiv.Perm.coe_one, id_eq, hρΓ] at h1
      have h2 := φ₃.injective h1
      exact congrArg Subtype.val h2
    exact Subtype.ext (eq_one_of_fixes_irr h108 hE11 hIplus hhom hH hend (hcommC x) hfixall)
  have hno2 : Nat.card ↥Cg ≠ 2 := by
    intro h2
    have hPn := normal_centralizer_subgroupOf (Γ := Γ) hNorm
    have hP2 : IsPGroup 2 ↥((Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf
        Γ) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Cg ≤ Γ)).toEquiv, h2]
      norm_num
    have hle := CFSG.LieType.BorelTits.le_pCore 2 hPn hP2
    have hbot := pCoreOf_eq_bot_of_isIrr_top h108.irreducible
    have hmap : ((Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf Γ).map
        Γ.subtype = Cg := Subgroup.map_subgroupOf_eq_of_le inf_le_left
    have hCbot : Cg = ⊥ := by
      rw [← hmap, ← le_bot_iff, ← hbot]
      exact Subgroup.map_mono hle
    rw [hCbot, Subgroup.card_bot] at h2
    omega
  have hno6 : Nat.card ↥Cg ≠ 6 := by
    intro h6
    obtain ⟨t, c', ht2, ht1, hc3, hc1, htc⟩ := exists_S3_of_card_six ρ hρinj h6
    obtain ⟨E, hE, hE9'⟩ := hE9 ↥(normalClosure Γ L) ⟨e⟩
    have hEcomm : ∀ a ∈ E.map (normalClosure Γ L).subtype, ∀ b ∈ E.map (normalClosure Γ L).subtype,
        a * b = b * a := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg (fun x : ↥E => ((x : ↥(normalClosure Γ L)) : GLV V))
        (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hE3 : ∀ a ∈ E.map (normalClosure Γ L).subtype, a ^ 3 = 1 := by
      rintro _ ⟨a, ha, rfl⟩
      exact congrArg (fun x : ↥(normalClosure Γ L) => (x : GLV V)) (hE.2 a ha)
    have hEcard : Nat.card ↥(E.map (normalClosure Γ L).subtype) = 9 := by
      rw [← hE9']
      exact (Nat.card_congr (Subgroup.equivMapOfInjective E (normalClosure Γ L).subtype
        (normalClosure Γ L).subtype_injective).toEquiv).symm
    have hEΓ : E.map (normalClosure Γ L).subtype ≤ Γ := by
      rintro _ ⟨a, -, rfl⟩
      exact hHΓ a.2
    have hEC : ∀ a ∈ E.map (normalClosure Γ L).subtype, ∀ z : ↥Cg,
        a * (z : GLV V) = (z : GLV V) * a := by
      rintro _ ⟨a, -, rfl⟩ z
      exact hcommC z a a.2
    exact no_E9_S3 (A := GLV V) (Γ := Γ) c.setup.cx.sqtk (t := (t : GLV V)) (c := (c' : GLV V))
      t.2.1 c'.2.1 hEΓ (congrArg Subtype.val ht2)
      (fun h => ht1 (Subtype.ext h)) (by
        have := congrArg Subtype.val hc3
        simpa using this) (fun h => hc1 (Subtype.ext h))
      (by
        have := congrArg Subtype.val htc
        simpa using this) hEcomm hE3 hEcard (fun a ha => hEC a ha t) (fun a ha => hEC a ha c')
  have hC3 : Nat.card ↥Cg = 3 := card_eq_three_of_injective ρ hρinj hC2 hno2 hno6
  have hCI : ∀ x : ↥Cg, conjSub (x : GLV V) I = I → x = 1 := by
    intro x hxI
    have h3 : ρ x ^ 3 = 1 := by
      rw [← map_pow]
      have : x ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥Cg) (x := x)
        rwa [hC3] at this
      rw [this, map_one]
    have hfixpt : ∃ i, ρ x i = i := by
      refine ⟨φ₃ ⟨I, hIplus⟩, ?_⟩
      rw [hρ, hρΓ]
      exact congrArg φ₃ (Subtype.ext hxI)
    have hsq := perm3_fix_sq _ hfixpt
    have h1 : ρ x = 1 := by
      calc ρ x = ρ x ^ 3 * (ρ x * ρ x)⁻¹ := by group
        _ = 1 := by rw [h3, hsq]; simp
    exact hρinj (h1.trans (map_one ρ).symm)
  have hΓIinv : Invariant (stabilizerOf Γ I) I := fun k hk u hu => by
    have h1 : conjSub k I = I := hk.2
    rw [← h1]
    exact apply_mem_conjSub hu
  have hΓI720' : Nat.card ↥(stabilizerOf Γ I) ≤ 720 := by
    have hinj : Function.Injective (restrictHom (stabilizerOf Γ I) I hΓIinv) := by
      rw [injective_iff_map_eq_one]
      intro k hk1
      rw [restrictHom_eq_one_iff] at hk1
      have hkΓ : (k : GLV V) ∈ Γ := stabilizerOf_le_self Γ I k.2
      have hkC : (k : GLV V) ∈ Cg := by
        refine ⟨hkΓ, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩
        have hconj : (k : GLV V) * h * (k : GLV V)⁻¹ = h := by
          have h1 : (k : GLV V) * h * (k : GLV V)⁻¹ * h⁻¹ = 1 := by
            refine faithfulOn_iff.1 hfaithH _ ?_ fun u hu => ?_
            · exact (normalClosure Γ L).mul_mem (hNorm k hkΓ h hh) ((normalClosure Γ L).inv_mem hh)
            · have hw : (h⁻¹ : GLV V) u ∈ I :=
                c.invariantH h⁻¹ ((normalClosure Γ L).inv_mem hh) u hu
              have e2 : (k : GLV V)⁻¹ ((h⁻¹ : GLV V) u) = (h⁻¹ : GLV V) u := by
                have := hk1 ((h⁻¹ : GLV V) u) hw
                have e3 : (k : GLV V)⁻¹ ((k : GLV V) ((h⁻¹ : GLV V) u)) = (h⁻¹ : GLV V) u := by simp
                rw [this] at e3
                exact e3
              show (k : GLV V) (h ((k : GLV V)⁻¹ ((h⁻¹ : GLV V) u))) = u
              rw [e2]
              have e4 : h ((h⁻¹ : GLV V) u) = u := by simp
              rw [e4]
              exact hk1 u hu
          exact mul_inv_eq_one.1 h1
        have : (k : GLV V) * h = h * (k : GLV V) := by
          rw [mul_inv_eq_iff_eq_mul] at hconj
          exact hconj
        exact this.symm
      have h2 := hCI ⟨k, hkC⟩ k.2.2
      have h3 : ((⟨k, hkC⟩ : ↥Cg) : GLV V) = 1 := congrArg Subtype.val h2
      exact Subtype.ext h3
    have hcard := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    have hR : Nat.card ↥(restrictRange (stabilizerOf Γ I) I hΓIinv) ≤ 720 := by
      refine hN6 ↥I (restrictRange (normalClosure Γ L) I hH) _ hperm ?_
      intro r hr h' hh'
      obtain ⟨k, hk, rfl⟩ := (mem_restrictRange_iff' hΓIinv).1 hr
      obtain ⟨h₀, hh₀, rfl⟩ := (mem_restrictRange_iff' hH).1 hh'
      refine (mem_restrictRange_iff' hH).2
        ⟨k * h₀ * k⁻¹, hNorm k (stabilizerOf_le_self Γ I hk) h₀ hh₀, ?_⟩
      ext i
      show k (h₀ ((k⁻¹ : GLV V) (i : V))) = (k * h₀ * k⁻¹) (i : V)
      rfl
    rw [hcard]
    exact hR
  have hΓfinal : Nat.card ↥Γ = 2160 := by omega
  have hab : ∀ a ∈ Γ, (∀ h ∈ normalClosure Γ L, a * h = h * a) → ∀ b ∈ Γ,
      (∀ h ∈ normalClosure Γ L, b * h = h * b) → a * b = b * a := by
    intro a ha hac b hb hbc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hCcyc : IsCyclic ↥Cg := isCyclic_of_prime_card hC3
    let a' : ↥Cg := ⟨a, ha, Subgroup.mem_centralizer_iff.2 fun h hh => (hac h hh).symm⟩
    let b' : ↥Cg := ⟨b, hb, Subgroup.mem_centralizer_iff.2 fun h hh => (hbc h hh).symm⟩
    let _ := hCcyc.commGroup
    exact congrArg Subtype.val (mul_comm a' b')
  have hlayer := layer_map_eq_normalClosure h108.component hab
  let eL : ↥(genFittingLayer ↥Γ) ≃* ↥(alternatingGroup (Fin 6)) :=
    ((Subgroup.equivMapOfInjective _ Γ.subtype Γ.subtype_injective).trans
      (MulEquiv.subgroupCongr hlayer)).trans e
  have hsimple : IsSimpleGroup ↥(normalClosure Γ L) := by
    have : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hH3 : ¬ IsPGroup 3 ↥(normalClosure Γ L) := by
    rw [IsPGroup.iff_card]
    rintro ⟨n, hn⟩
    rw [hH360] at hn
    have h5 : 5 ∣ 3 ^ n := hn ▸ (by norm_num : 5 ∣ 360)
    have := Nat.Prime.dvd_of_dvd_pow (by norm_num) h5
    omega
  have hC3p : IsPGroup 3 ↥Cg := IsPGroup.of_card (n := 1) (by rw [hC3]; norm_num)
  have hpc := pCore_three_eq hHΓ hNorm hsimple hH3 hC3p
  have hpcCard : Nat.card ↥(CFSG.pCore 3 ↥Γ) = 3 := by
    rw [hpc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Cg ≤ Γ)).toEquiv]
    exact hC3
  obtain ⟨x, hxX, J₀, hxmove⟩ : ∃ x ∈ X, ∃ J : IrrSet Γ L, conjSub x J.1 ≠ J.1 := by
    by_contra hall
    push Not at hall
    have hall' : ∀ J : IrrSet Γ L, J.1 = I := by
      intro J
      refine props_unique c.props J.1 J.2 (fun x hx u hu => ?_)
      rw [← hall x hx J]
      exact apply_mem_conjSub hu
    have hnt : Nontrivial (IrrSet Γ L) := Finite.one_lt_card_iff_nontrivial.1 (by omega)
    obtain ⟨J₁, J₂, hJ⟩ := exists_pair_ne (IrrSet Γ L)
    exact hJ (Subtype.ext ((hall' J₁).trans (hall' J₂).symm))
  have hxΓ : x ∈ Γ := h108.X_le hxX
  let xΓ : ↥Γ := ⟨x, hxΓ⟩
  have hτ2 : ρΓ xΓ * ρΓ xΓ = 1 := by
    rw [← map_mul]
    have : xΓ * xΓ = 1 := Subtype.ext (h108.X_sq x hxX)
    rw [this, map_one]
  have hτ1 : ρΓ xΓ ≠ 1 := by
    intro h1
    have h2 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ (φ₃ J₀)) h1
    simp only [Equiv.Perm.coe_one, id_eq, hρΓ] at h2
    exact hxmove (congrArg Subtype.val (φ₃.injective h2))
  have hPn := normal_centralizer_subgroupOf (Γ := Γ) hNorm
  refine c.setup.cx.notConcl (fix_concl10 ⟨hV8, hΓfinal, ⟨eL⟩, hpcCard, x, hxX, hxΓ, ?_⟩)
  intro y
  have hy : (y : ↥Γ) ∈ (Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf
      Γ := by
    rw [← hpc]
    exact y.2
  have hyC : ((y : ↥Γ) : GLV V) ∈ Cg := hy
  by_cases hy1 : (y : ↥Γ) = 1
  · rw [hy1]
    simp
  · have hz : xΓ * (y : ↥Γ) * xΓ⁻¹ ∈
        (Γ ⊓ Subgroup.centralizer (normalClosure Γ L : Set (GLV V))).subgroupOf Γ :=
      hPn.conj_mem _ hy xΓ
    have hzC : ((xΓ * (y : ↥Γ) * xΓ⁻¹ : ↥Γ) : GLV V) ∈ Cg := hz
    have hwC : (((y : ↥Γ)⁻¹ : ↥Γ) : GLV V) ∈ Cg := Cg.inv_mem hyC
    let yc : ↥Cg := ⟨((y : ↥Γ) : GLV V), hyC⟩
    have hyc1 : yc ≠ 1 := fun h => by
      have h' : ((yc : ↥Cg) : GLV V) = 1 := congrArg Subtype.val h
      exact hy1 (Subtype.ext h')
    have hσ1 : ρ yc ≠ 1 := fun h => hyc1 (hρinj (h.trans (map_one ρ).symm))
    have hσ3 : ρ yc ^ 3 = 1 := by
      rw [← map_pow]
      have : yc ^ 3 = 1 := by
        have := pow_card_eq_one' (G := ↥Cg) (x := yc)
        rwa [hC3] at this
      rw [this, map_one]
    have hconj := perm3_conj_inv _ _ hτ2 hτ1 hσ3 hσ1
    have heq : ρ ⟨((xΓ * (y : ↥Γ) * xΓ⁻¹ : ↥Γ) : GLV V), hzC⟩ =
        ρ ⟨(((y : ↥Γ)⁻¹ : ↥Γ) : GLV V), hwC⟩ := by
      rw [hρ, hρ]
      show ρΓ (xΓ * (y : ↥Γ) * xΓ⁻¹) = ρΓ (y : ↥Γ)⁻¹
      rw [map_mul, map_mul, map_inv, map_inv]
      exact hconj
    have h8 := hρinj heq
    have h9 : ((xΓ * (y : ↥Γ) * xΓ⁻¹ : ↥Γ) : GLV V) = (((y : ↥Γ)⁻¹ : ↥Γ) : GLV V) :=
      congrArg (fun z : ↥Cg => (z : GLV V)) h8
    exact Subtype.ext h9

end G117

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G117

theorem g11_7 (hApply : G93ApplyStmt) (hE11 : E11Stmt) (hM12 : NoConfigM12) (hL2 : NoConfigL2)
    (hOm4m : NoConfigOm4Minus) (hSp4 : NoConfigSp4) (hG2 : NoConfigG2)
    (hOm4p : NoConfigOm4Plus) (hOm4p4 : NoConfigOm4PlusFour) (hM22 : AutHatM22Bound)
    (hG22 : G22DerivedFacts) (hA8 : A8OrthogonalFact) (hOm4Iso : Om4Plus4Iso) : G117Stmt :=
  g11_7_of_steps hApply (G117.step0 hM12) (G117.step2 hM22) G117.step4 (G117.step6 hL2)
    (G117.step7 hOm4m) (G117.step9 hSp4) (G117.step10 hG2 hG22) (G117.step12 hA8)
    (G117.step15 hOm4p hOm4p4 hOm4Iso) G117.step16
    (G117.step_lt hE11 G117.a6NormalizerBound G117.a6Facts)

end SzG11S

end G11

end CFSG.Quasithin

