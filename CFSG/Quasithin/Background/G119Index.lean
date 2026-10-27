module

public import CFSG.Quasithin.Background.G119Nat3
public import CFSG.Quasithin.Background.G119Group

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

namespace G119Ctx

variable (c : G119Ctx B Γ v₁ W X X₀ L I)

include c

theorem restrictHom_H_injective :
    Function.Injective (restrictHom (normalClosure Γ L) I c.irrPlus.1) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  apply Subtype.ext
  exact faithfulOn_iff.1 c.faithful (h : GLV V) h.2 (restrictHom_eq_one_iff.1 hh)

theorem isNatAltModule_of_natSym {n : ℕ} {x₀ : GLV V} (hx₀ : x₀ ∈ X)
    (hrk : Module.finrank (ZMod 2) (LinearMap.range (commMap x₀ I (c.conjSub_I hx₀))) = 1)
    (hnat : G119NatSymAction (restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1) n)
    (hdec : ∀ g ∈ restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1,
      g ∈ restrictRange (normalClosure Γ L) I c.irrPlus.1 ∨
        g * restrictEquiv x₀ I (c.conjSub_I hx₀) ∈
          restrictRange (normalClosure Γ L) I c.irrPlus.1) :
    IsNatAltModule (normalClosure Γ L) I n := by
  classical
  set H := normalClosure Γ L with hH
  set G' := restrictRange (H ⊔ X) I c.irr_sup.1 with hG'
  obtain ⟨θ, β, hrange, hker, hequiv, hswap⟩ := hnat
  have hHbG : restrictRange H I c.irrPlus.1 ≤ G' :=
    g119_restrictRange_mono le_sup_left c.irrPlus.1 c.irr_sup.1
  have hāG : restrictEquiv x₀ I (c.conjSub_I hx₀) ∈ G' :=
    restrictEquiv_mem_restrictRange c.irr_sup.1 (Subgroup.mem_sup_right hx₀)
  let ι : ↥H →* ↥G' :=
    (restrictHom H I c.irrPlus.1).codRestrict G' (fun h => hHbG ⟨h, rfl⟩)
  let ψ : ↥H →* Equiv.Perm (Fin n) := θ.toMonoidHom.comp ι
  have hιinj : Function.Injective ι := fun a b hab =>
    c.restrictHom_H_injective (congrArg Subtype.val hab)
  have hψinj : Function.Injective ψ := θ.injective.comp hιinj
  have hsign : ∀ h : ↥H, Equiv.Perm.sign (ψ h) = 1 := by
    have hperf : Group.IsPerfect ↥H := c.isPerfect_H
    have hker1 := Abelianization.commutator_subset_ker
      ((Equiv.Perm.sign : Equiv.Perm (Fin n) →* ℤˣ).comp ψ)
    rw [Group.IsPerfect.commutator_eq_top] at hker1
    intro h
    exact MonoidHom.mem_ker.1 (hker1 (Subgroup.mem_top h))
  have hψA : ψ.range ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨h, rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.2 (hsign h)
  have hs := hswap ⟨restrictEquiv x₀ I (c.conjSub_I hx₀), hāG⟩ hrk
  have hdec' : ∀ g' : Equiv.Perm (Fin n),
      g' ∈ ψ.range ∨ g' * θ ⟨restrictEquiv x₀ I (c.conjSub_I hx₀), hāG⟩ ∈ ψ.range := by
    intro g'
    obtain ⟨g, rfl⟩ := θ.surjective g'
    rcases hdec g.1 g.2 with hg | hg
    · left
      obtain ⟨h, hh⟩ := hg
      exact ⟨h, by
        show θ (ι h) = θ g
        congr 1
        exact Subtype.ext hh⟩
    · right
      obtain ⟨h, hh⟩ := hg
      refine ⟨h, ?_⟩
      show θ (ι h) = θ g * θ ⟨restrictEquiv x₀ I (c.conjSub_I hx₀), hāG⟩
      rw [← map_mul]
      congr 1
      exact Subtype.ext hh
  have hr : ψ.range = alternatingGroup (Fin n) :=
    g119_eq_alternatingGroup_of_decomp ψ.range hψA hs hdec'
  obtain ⟨φ, hφ⟩ := g119_mulEquiv_alternatingGroup_of_range ψ hψinj hr
  let β' : ↥(permCore n) →ₗ[ZMod 2] V :=
    { toFun := fun u => ((β u : ↥I) : V)
      map_add' := fun a b => by
        rw [map_add]
        rfl
      map_smul' := fun r a => by
        rcases zmod2_eq_zero_or_one r with rfl | rfl
        · simp
        · simp }
  have hβ'val : ∀ u, β' u = ((β u : ↥I) : V) := fun u => rfl
  refine ⟨φ, β', ?_, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨u, rfl⟩
      exact (β u).2
    · intro hv
      obtain ⟨u, hu⟩ := LinearMap.range_eq_top.1 hrange (⟨v, hv⟩ : ↥I)
      exact ⟨u, by rw [hβ'val, hu]⟩
  · intro u
    rw [← hker u, hβ'val]
    exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩
  · intro γ u u' hu
    have h1 := hequiv (ι γ) u u' (by rw [hu, hφ]; rfl)
    rw [hβ'val, hβ'val, h1]
    rfl

theorem relIndex_eq_two {n : ℕ} {x₀ : GLV V} (hx₀ : x₀ ∈ X)
    (hx₀C : x₀ ∉ centralizerIn X (normalClosure Γ L))
    (hrk : ∀ (y : GLV V) (hy : y ∈ X), y ∉ centralizerIn X (normalClosure Γ L) →
      Module.finrank (ZMod 2) (LinearMap.range (commMap y I (c.conjSub_I hy))) = 1)
    (hnat : G119NatSymAction (restrictRange (normalClosure Γ L ⊔ X) I c.irr_sup.1) n) :
    (centralizerIn X (normalClosure Γ L)).relIndex X = 2 := by
  classical
  obtain ⟨θ, β, -, -, -, hswap⟩ := hnat
  set C := centralizerIn X (normalClosure Γ L) with hC
  have hkey : ∀ y ∈ X, y ∉ C → y * x₀ ∈ C := by
    intro y hy hyC
    by_contra hyx
    have hyxX : y * x₀ ∈ X := X.mul_mem hy hx₀
    have hyG := c.restrictEquiv_mem_G hy
    have hāG := c.restrictEquiv_mem_G hx₀
    have hyxG := c.restrictEquiv_mem_G hyxX
    have hmulE : restrictEquiv (y * x₀) I (c.conjSub_I hyxX) =
        restrictEquiv y I (c.conjSub_I hy) * restrictEquiv x₀ I (c.conjSub_I hx₀) :=
      g119_restrictEquiv_mul _ _ _
    have hmul : (⟨restrictEquiv y I (c.conjSub_I hy), hyG⟩ : ↥(restrictRange
        (normalClosure Γ L ⊔ X) I c.irr_sup.1)) * ⟨restrictEquiv x₀ I (c.conjSub_I hx₀), hāG⟩ =
        ⟨restrictEquiv (y * x₀) I (c.conjSub_I hyxX), hyxG⟩ := Subtype.ext hmulE.symm
    have hsy := hswap ⟨restrictEquiv y I (c.conjSub_I hy), hyG⟩ (hrk y hy hyC)
    have hs0 := hswap ⟨restrictEquiv x₀ I (c.conjSub_I hx₀), hāG⟩ (hrk x₀ hx₀ hx₀C)
    have hsyx := hswap ⟨restrictEquiv (y * x₀) I (c.conjSub_I hyxX), hyxG⟩
      (hrk (y * x₀) hyxX hyx)
    have hcomm : θ ⟨restrictEquiv y I (c.conjSub_I hy), hyG⟩ *
        θ ⟨restrictEquiv x₀ I (c.conjSub_I hx₀), hāG⟩ =
        θ ⟨restrictEquiv x₀ I (c.conjSub_I hx₀), hāG⟩ *
          θ ⟨restrictEquiv y I (c.conjSub_I hy), hyG⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (c.restrictEquiv_comm hy hx₀)
    by_cases hne : θ ⟨restrictEquiv y I (c.conjSub_I hy), hyG⟩ =
        θ ⟨restrictEquiv x₀ I (c.conjSub_I hx₀), hāG⟩
    · have heq := θ.injective hne
      have hyxeq : restrictEquiv y I (c.conjSub_I hy) = restrictEquiv x₀ I (c.conjSub_I hx₀) :=
        congrArg Subtype.val heq
      apply hyx
      rw [c.mem_centralizerIn_iff_fixes hyxX]
      intro i hi
      have h2 : restrictEquiv y I (c.conjSub_I hy) * restrictEquiv x₀ I (c.conjSub_I hx₀) = 1 := by
        rw [hyxeq]
        exact c.restrictEquiv_sq hx₀
      have h3 := congrArg (fun e : GLV ↥I => ((e ⟨i, hi⟩ : ↥I) : V)) (hmulE.trans h2)
      simpa using h3
    · refine g119_not_isSwap_mul_of_commute hsy hs0 hcomm hne ?_
      rw [← map_mul, hmul]
      exact hsyx
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨x₀, hx₀⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
  by_cases hb : (b : GLV V) ∈ C
  · right
    refine ⟨hb, fun hba => hx₀C ?_⟩
    have := C.mul_mem (C.inv_mem hb) hba
    simpa using this
  · left
    exact ⟨hkey b b.2 hb, hb⟩

theorem three_le_finrank_fixed {x : GLV V} (hx : x ∈ X)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (commMap x I (c.conjSub_I hx))) = 1)
    (h4 : 4 ≤ Module.finrank (ZMod 2) I) :
    3 ≤ Module.finrank (ZMod 2) ↥(fixedSpace (Subgroup.zpowers x) ⊓ I) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (commMap x I (c.conjSub_I hx))
  have hfix : fixedSpace (Subgroup.zpowers x) ⊓ I =
      (LinearMap.ker (commMap x I (c.conjSub_I hx))).map I.subtype := by
    ext v
    constructor
    · rintro ⟨hv, hvI⟩
      refine ⟨⟨v, hvI⟩, ?_, rfl⟩
      show (⟨v, hvI⟩ : ↥I) ∈ LinearMap.ker (commMap x I (c.conjSub_I hx))
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [coe_commMap]
      have := hv x (Subgroup.mem_zpowers x)
      simp [this]
    · rintro ⟨⟨u, hu⟩, hker, rfl⟩
      refine ⟨fun k hk => ?_, hu⟩
      have hxu : x u = u := by
        have := congrArg Subtype.val (LinearMap.mem_ker.1 hker)
        rw [coe_commMap] at this
        exact sub_eq_zero.1 this
      have hle : Subgroup.zpowers x ≤ MulAction.stabilizer (GLV V) u :=
        Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 hxu)
      exact hle hk
  rw [hfix, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective I.subtype I.injective_subtype
    (LinearMap.ker (commMap x I (c.conjSub_I hx))))]
  omega

end G119Ctx

end G11

end CFSG.Quasithin
