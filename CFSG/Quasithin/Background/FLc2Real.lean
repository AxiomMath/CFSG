module

public import CFSG.Quasithin.Background.FLc2VModel
public import CFSG.Quasithin.Background.B4ModelsAction

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem vmodel_of_realizes {V : Type} [CommGroup V] {Γ : Type} [Group Γ] {A : Type} [CommGroup A]
    (act : Γ → A → A) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : Γ →* ↥H}
    (h : ({ Gam := Γ, Amb := A, act := act, sec := ⊤, ker := ⊥ } : FFModel).RealizesVia H U Z π) :
    ∃ β : ↥U →* A, Function.Surjective β ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
      (∀ (γ : Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) (u : V) ∈ U),
        β ⟨((π γ : ↥H) : MulAut V) (u : V), hu⟩ = act γ (β u)) ∧
      (∀ g : ↥H, ∀ u ∈ U, (g : MulAut V) u ∈ U) ∧ Function.Surjective π := by
  obtain ⟨hπs, -, -, hUinv, -, -, -, β', hβ's, hβ'k, hβ'eq⟩ := h
  let e : (↥(⊤ : Subgroup A) ⧸ (⊥ : Subgroup A).subgroupOf (⊤ : Subgroup A)) →* A :=
    QuotientGroup.lift _ (⊤ : Subgroup A).subtype (by
      intro x hx
      have : (x : A) ∈ (⊥ : Subgroup A) := Subgroup.mem_subgroupOf.1 hx
      exact (Subgroup.mem_bot.1 this))
  have he : ∀ m : ↥(⊤ : Subgroup A), e (QuotientGroup.mk m) = (m : A) := fun m => rfl
  have heinj : ∀ q, e q = 1 → q = 1 := by
    intro q hq
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    rw [he] at hq
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (by rw [hq]; exact (⊥ : Subgroup A).one_mem)
  have hes : Function.Surjective e := fun a => ⟨QuotientGroup.mk ⟨a, trivial⟩, rfl⟩
  refine ⟨e.comp β', hes.comp hβ's, fun u => ?_, fun γ u hu => ?_, hUinv, hπs⟩
  · constructor
    · intro hu
      exact (hβ'k u).1 (heinj _ hu)
    · intro hu
      have : β' u = 1 := (hβ'k u).2 hu
      show e (β' u) = 1
      rw [this, map_one]
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β' u)
    have h1 := hβ'eq γ u m hu (Subgroup.mem_top _) hm.symm
    show e (β' ⟨_, hu⟩) = act γ (e (β' u))
    rw [h1, ← hm, he, he]

@[expose] noncomputable def actW {n : ℕ} (g : SLt n)
    (a : Multiplicative (⋀[ZMod 2]^2 (Fin n → ZMod 2))) :
    Multiplicative (⋀[ZMod 2]^2 (Fin n → ZMod 2)) :=
  extSqAct (ZMod 2) n (specialLinearGroupEquivStatedSL n (ZMod 2) g) a

@[expose] noncomputable def rhoOf {V : Type} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)}
    (π : ↥(StatedSL n (ZMod 2)) →* ↥H) : SLt n →* MulAut V :=
  H.subtype.comp (π.comp (specialLinearGroupEquivStatedSL n (ZMod 2)).toMonoidHom)

theorem rhoOf_apply {V : Type} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)}
    (π : ↥(StatedSL n (ZMod 2)) →* ↥H) (g : SLt n) :
    rhoOf π g = ((π (specialLinearGroupEquivStatedSL n (ZMod 2) g) : ↥H) : MulAut V) := rfl

theorem rhoOf_mem {V : Type} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)}
    (π : ↥(StatedSL n (ZMod 2)) →* ↥H) (g : SLt n) : rhoOf π g ∈ H :=
  (π (specialLinearGroupEquivStatedSL n (ZMod 2) g)).2

theorem rhoOf_surj {V : Type} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H} (hπ : Function.Surjective π) :
    ∀ k ∈ H, ∃ g, rhoOf π g = k := by
  intro k hk
  obtain ⟨γ, hγ⟩ := hπ ⟨k, hk⟩
  exact ⟨(specialLinearGroupEquivStatedSL n (ZMod 2)).symm γ, by
    rw [rhoOf_apply, MulEquiv.apply_symm_apply, hγ]⟩

theorem vmodelNat {V : Type} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H}
    (h : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U Z π)
    (hZ : ∀ g ∈ H, ∀ z ∈ Z, g z = z) :
    Nonempty (VModel n (rhoOf π) U Z (Multiplicative (Vt n)) (fun g a => actM g a)) := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, -⟩ := vmodel_of_realizes (natAct (StatedSL n (ZMod 2))) h
  let σ := specialLinearGroupEquivStatedSL n (ZMod 2)
  refine ⟨?_⟩
  refine
    { β := β
      surj := hβs
      inv := fun g u hu => hUinv _ u hu
      ker := fun u hu => (hβk u).1 hu
      equiv := fun g u hu => ?_
      Zfix := fun g z hz => hZ _ (rhoOf_mem π g) z hz
      act_hom := fun g a b => map_mul (actM g) a b
      act_one := fun a => ?_
      act_mul := fun g k a => ?_ }
  · have h1 := hβe (σ g) u hu
    refine h1.trans ?_
    apply Multiplicative.toAdd.injective
    show _ = mat g *ᵥ _
    simp only [natAct]
    rw [toAdd_ofAdd]
    show (((σ g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))) *ᵥ _ = _
    rw [specialLinearGroupEquivStatedSL_coe]
  · show actM 1 a = a
    apply Multiplicative.toAdd.injective
    rw [toAdd_actM, mat_one, one_mulVec]
  · show actM (g * k) a = actM g (actM k a)
    apply Multiplicative.toAdd.injective
    rw [toAdd_actM, toAdd_actM, toAdd_actM, mat_mul, mulVec_mulVec]

theorem vmodelExtSq {V : Type} [CommGroup V] {n : ℕ} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H}
    (h : (FFModel.extSq (ZMod 2) n).RealizesVia H U Z π)
    (hZ : ∀ g ∈ H, ∀ z ∈ Z, g z = z) :
    Nonempty (VModel n (rhoOf π) U Z (Multiplicative (⋀[ZMod 2]^2 (Fin n → ZMod 2))) actW) := by
  obtain ⟨β, hβs, hβk, hβe, hUinv, -⟩ := vmodel_of_realizes (extSqAct (ZMod 2) n) h
  let σ := specialLinearGroupEquivStatedSL n (ZMod 2)
  refine ⟨?_⟩
  exact
    { β := β
      surj := hβs
      inv := fun g u hu => hUinv _ u hu
      ker := fun u hu => (hβk u).1 hu
      equiv := fun g u hu => hβe (σ g) u hu
      Zfix := fun g z hz => hZ _ (rhoOf_mem π g) z hz
      act_hom := fun g a b => extSqAct_mul (ZMod 2) n (σ g) a b
      act_one := fun a => extSqAct_one (ZMod 2) n a
      act_mul := fun g k a => by
        show extSqAct (ZMod 2) n (σ (g * k)) a =
          extSqAct (ZMod 2) n (σ g) (extSqAct (ZMod 2) n (σ k) a)
        rw [map_mul]
        exact extSqAct_mul_act (ZMod 2) n _ _ a }

end CFSG.Quasithin.FLc
