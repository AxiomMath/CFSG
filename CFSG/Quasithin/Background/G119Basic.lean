module

public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.Quasithin.Background.G11BridgeSQTK
public import CFSG.Quasithin.Background.G10Clifford
public import CFSG.Quasithin.Background.G11BridgeG10

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
theorem g119_isPerfect_normalClosure {Γ L : Subgroup (GLV V)} (hL : Group.IsPerfect ↥L) :
    Group.IsPerfect ↥(normalClosure Γ L) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact (normalClosure Γ L).mul_mem ((normalClosure Γ L).mul_mem
      ((normalClosure Γ L).mul_mem h₁ h₂) ((normalClosure Γ L).inv_mem h₁))
      ((normalClosure Γ L).inv_mem h₂)
  · unfold normalClosure
    rw [Subgroup.closure_le]
    rintro _ ⟨γ, hγ, l, hl, rfl⟩
    have hLL : ⁅L, L⁆ = L := Subgroup.commutator_eq_self (H := L)
    have hl' : l ∈ ⁅L, L⁆ := by rw [hLL]; exact hl
    have h1 : γ * l * γ⁻¹ ∈ (⁅L, L⁆).map (MulAut.conj γ).toMonoidHom :=
      ⟨l, hl', by simp [MulAut.conj_apply]⟩
    rw [Subgroup.map_commutator] at h1
    have hconj : L.map (MulAut.conj γ).toMonoidHom ≤
        Subgroup.closure {x | ∃ γ ∈ Γ, ∃ l ∈ L, x = γ * l * γ⁻¹} := by
      rintro _ ⟨l', hl'', rfl⟩
      exact Subgroup.subset_closure ⟨γ, hγ, l', hl'', by simp [MulAut.conj_apply]⟩
    exact Subgroup.commutator_mono hconj hconj h1

omit [Finite V] in
theorem g119_mem_centralizerIn_iff {X H : Subgroup (GLV V)} {x : GLV V} :
    x ∈ centralizerIn X H ↔ x ∈ X ∧ ∀ h ∈ H, h * x = x * h := by
  unfold centralizerIn
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

variable (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (GLV V)) (v₁ : V)
  (W : Submodule (ZMod 2) V) (X X₀ L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V)

structure G119Ctx : Prop where
  hyp : G108Hyp B Γ v₁ W X X₀ L
  sqtk : IsQuotientOfSQTKTauCeti ↥Γ
  irrPlus : IrrPlus (normalClosure Γ L) I
  v₁_mem : v₁ ∈ I
  invX : Invariant X I
  homog : Homogeneous (normalClosure Γ L)
  isotropic : Isotropic B I
  faithful : FaithfulOn (normalClosure Γ L) I
  not_autAll : ¬ AutAll (normalClosure Γ L) I
  rank : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) V
  fix : fixedSpace X = Submodule.span (ZMod 2) {v₁}
  cent : ∀ x ∈ centralizerIn X (normalClosure Γ L), ∀ i ∈ I, x i = i

variable {B Γ v₁ W X X₀ L I}

namespace G119Ctx

variable (c : G119Ctx B Γ v₁ W X X₀ L I)

include c

theorem fixedSpace_H : fixedSpace (normalClosure Γ L) = ⊥ := c.hyp.fixedSpace_H

theorem irr : IsIrr (normalClosure Γ L) I := c.irrPlus.isIrr c.fixedSpace_H

theorem irrPlus_isIrr {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) :
    IsIrr (normalClosure Γ L) J := hJ.isIrr c.fixedSpace_H

theorem irrPlus_two_lt {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) :
    2 < Module.finrank (ZMod 2) J := c.hyp.two_lt_finrank (c.irrPlus_isIrr hJ)

theorem two_lt : 2 < Module.finrank (ZMod 2) I := c.irrPlus_two_lt c.irrPlus

theorem hiso {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) :
    HIso (normalClosure Γ L) I J := c.homog I J c.irrPlus hJ

theorem finrank_eq {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) :
    Module.finrank (ZMod 2) J = Module.finrank (ZMod 2) I := (c.hiso hJ).finrank_eq.symm

theorem faithful_irrPlus {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) :
    FaithfulOn (normalClosure Γ L) J := by
  obtain ⟨φ, hφ⟩ := c.hiso hJ
  rw [faithfulOn_iff] at *
  have hF := (faithfulOn_iff).1 c.faithful
  intro h hh hhJ
  apply hF h hh
  intro i hi
  have hmem : h i ∈ I := c.irrPlus.1 h hh i hi
  have h1 := hφ h hh ⟨i, hi⟩ ⟨h i, hmem⟩ rfl
  have h2 : (φ ⟨i, hi⟩ : ↥J) = φ ⟨h i, hmem⟩ := by
    apply Subtype.ext
    rw [← h1]
    exact (hhJ _ (φ ⟨i, hi⟩).2).symm
  have h3 : (⟨i, hi⟩ : ↥I) = ⟨h i, hmem⟩ := φ.injective h2
  exact (congrArg Subtype.val h3).symm

theorem X_normalizes : ∀ x ∈ X, ∀ h ∈ normalClosure Γ L, x * h * x⁻¹ ∈ normalClosure Γ L :=
  c.hyp.X_normalizes_H

theorem X_le : X ≤ Γ := c.hyp.X_le

theorem H_le : normalClosure Γ L ≤ Γ := c.hyp.H_le

theorem conjSub_I {x : GLV V} (hx : x ∈ X) : conjSub x I = I := c.invX.conjSub_eq hx

theorem X_sq {x : GLV V} (hx : x ∈ X) : x * x = 1 := c.hyp.X_sq x hx

theorem X_comm {x y : GLV V} (hx : x ∈ X) (hy : y ∈ X) : x * y = y * x := c.hyp.X_comm x hx y hy

theorem irrPlus_conj {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) {x : GLV V}
    (hx : x ∈ X) : IrrPlus (normalClosure Γ L) (conjSub x J) :=
  ((c.irrPlus_isIrr hJ).conj_of_normal (normalClosure_normal Γ L) (c.X_le hx)).irrPlus
    c.fixedSpace_H

theorem invariant_orthogonal_H : Invariant (normalClosure Γ L) (B.orthogonal I) :=
  c.irrPlus.1.orthogonal c.hyp.H_isometry

theorem invariant_orthogonal_X : Invariant X (B.orthogonal I) :=
  c.invX.orthogonal fun k hk => c.hyp.isometry k (c.hyp.X_le hk)

theorem le_orthogonal : I ≤ B.orthogonal I := fun u hu => by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  exact fun n hn => c.isotropic n hn u hu

theorem finrank_orthogonal :
    Module.finrank (ZMod 2) ↥(B.orthogonal I) =
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) I :=
  LinearMap.BilinForm.finrank_orthogonal c.hyp.toG101Hyp.nondegenerate' I

theorem mem_centralizerIn_iff_fixes {x : GLV V} (hx : x ∈ X) :
    x ∈ centralizerIn X (normalClosure Γ L) ↔ ∀ i ∈ I, x i = i := by
  constructor
  · exact fun h => c.cent x h
  · intro hfix
    rw [g119_mem_centralizerIn_iff]
    refine ⟨hx, fun h hh => ?_⟩
    have hmemH : x * h * x⁻¹ * h⁻¹ ∈ normalClosure Γ L :=
      (normalClosure Γ L).mul_mem (c.X_normalizes x hx h hh) ((normalClosure Γ L).inv_mem hh)
    have hker : x * h * x⁻¹ * h⁻¹ ∈ centralizerOn (normalClosure Γ L) I := by
      refine ⟨hmemH, fun u hu => ?_⟩
      have h1 : h⁻¹ u ∈ I := c.irrPlus.1 h⁻¹ ((normalClosure Γ L).inv_mem hh) u hu
      have h2 : x⁻¹ (h⁻¹ u) = h⁻¹ u := by
        show x.symm (h⁻¹ u) = h⁻¹ u
        rw [LinearEquiv.symm_apply_eq]
        exact (hfix _ h1).symm
      have e : (x * h * x⁻¹ * h⁻¹ : GLV V) u = x (h (x⁻¹ (h⁻¹ u))) := rfl
      rw [e, h2]
      have : h (h⁻¹ u) = u := by simp
      rw [this]
      exact hfix u hu
    have hone : x * h * x⁻¹ * h⁻¹ = 1 := (faithfulOn_iff.1 c.faithful) _ hker.1 hker.2
    have : x * h * x⁻¹ = h := by
      have := congrArg (· * h) hone
      simpa using this
    have h3 : x * h = h * x := by
      have := congrArg (· * x) this
      simpa [mul_assoc] using this
    exact h3.symm

theorem exists_not_central : ∃ x ∈ X, x ∉ centralizerIn X (normalClosure Γ L) := by
  obtain ⟨x, hx, l, hl, hne⟩ := c.hyp.noncomm
  refine ⟨x, hx, fun hcen => hne ?_⟩
  obtain ⟨-, h2⟩ := g119_mem_centralizerIn_iff.1 hcen
  exact (h2 l (le_normalClosure Γ L hl)).symm

theorem inf_eq_bot_of_ne {J₁ J₂ : Submodule (ZMod 2) V} (h₁ : IrrPlus (normalClosure Γ L) J₁)
    (h₂ : IrrPlus (normalClosure Γ L) J₂) (hne : J₁ ≠ J₂) : J₁ ⊓ J₂ = ⊥ := by
  have hi₁ := c.irrPlus_isIrr h₁
  have hi₂ := c.irrPlus_isIrr h₂
  rcases hi₁.eq_bot_or_eq (hi₁.1.inf hi₂.1) inf_le_left with h | h
  · exact h
  · exfalso
    have hle : J₁ ≤ J₂ := h ▸ inf_le_right
    rcases hi₂.eq_bot_or_eq hi₁.1 hle with h' | h'
    · exact hi₁.ne_bot h'
    · exact hne h'

theorem v₁_not_mem {J : Submodule (ZMod 2) V} (hJ : IrrPlus (normalClosure Γ L) J) (hne : J ≠ I) :
    v₁ ∉ J := by
  intro hv
  have : v₁ ∈ J ⊓ I := ⟨hv, c.v₁_mem⟩
  rw [c.inf_eq_bot_of_ne hJ c.irrPlus hne] at this
  exact c.hyp.point ((Submodule.mem_bot _).1 this)

theorem isPerfect_H : Group.IsPerfect ↥(normalClosure Γ L) :=
  g119_isPerfect_normalClosure ⟨c.hyp.component.2.2.1⟩

theorem sqtk_sup : IsQuotientOfSQTKTauCeti ↥(normalClosure Γ L ⊔ X) :=
  IsQuotientOfSQTKTauCeti.of_le (sup_le c.H_le c.X_le) c.sqtk

theorem irr_sup : IsIrr (normalClosure Γ L ⊔ X) I := by
  refine ⟨c.irrPlus.1.sup_subgroup c.invX, c.irr.2.1, fun J hJ hbot hJI => ?_⟩
  exact c.irr.2.2 J (hJ.mono le_sup_left) hbot hJI

end G119Ctx

end G11

end CFSG.Quasithin
