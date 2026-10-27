module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Group
public import CFSG.RankThree.GF2n.Stroth80.HeringSec118RT1Action
import CFSG.RankThree.GF2n.Stroth80.CarterSec11PiPre
public import CFSG.ClassicalGroups.SpecialLinear.Transitive

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement Matrix MatrixGroups

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ}

section TransportData

variable {m : ℕ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
  {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)}
  {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))}
  {W₁ W₂ : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)}
  {F : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
  {F' : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}

private theorem sigma0_injective (hc : Ctx M Q Z B)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    (hFinj : Function.Injective F) : Function.Injective σ₀ := by
  have hone : ∀ g : SL(m, K), σ₀ g = 1 → g = 1 := by
    intro g hg
    have hx1 : xbarHToXbar M Q Z B (1 : ↥(XbarH M Q Z B)) = σ₀ g := by
      rw [map_one, hg]
    have hρ1 : ρ g = 1 := by
      rw [hρ g 1 hx1]
      exact map_one (cmCommAct hc φ)
    have hmv : ∀ x : Fin m → K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x = x := by
      intro x
      apply hFinj
      rw [hFeq, hρ1]
      rfl
    have hmat : (g : Matrix (Fin m) (Fin m) K) = 1 := by
      ext i j
      have h := congrFun (hmv (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply] using h
    exact Subtype.ext hmat
  intro g g' h
  have h1 : σ₀ (g * g'⁻¹) = 1 := by
    rw [map_mul, h, map_inv, mul_inv_cancel]
  have h2 := hone (g * g'⁻¹) h1
  rwa [mul_inv_eq_one] at h2

private noncomputable def xbarPreToXbar (hc : Ctx M Q Z B) :
    ↥(XbarPre M Q Z B) →* ↥(Xbar M Q Z B) :=
  ((QuotientGroup.mk' (Q.subgroupOf M)).comp
    (Subgroup.inclusion (XbarPre_le_M hc))).codRestrict (Xbar M Q Z B)
      (fun s => (mem_XbarPre_iff hc (XbarPre_le_M hc s.2)).mp s.2)

private theorem coe_xbarPreToXbar (hc : Ctx M Q Z B) (s : ↥(XbarPre M Q Z B)) :
    ((xbarPreToXbar hc s : ↥(Xbar M Q Z B)) : Mbar M Q) =
      QuotientGroup.mk (⟨(s : G), XbarPre_le_M hc s.2⟩ : ↥M) := rfl

private theorem xbarPreToXbar_surjective (hc : Ctx M Q Z B) :
    Function.Surjective (xbarPreToXbar hc) := by
  rintro ⟨x, hx⟩
  obtain ⟨t, ht⟩ := QuotientGroup.mk_surjective x
  have htX : (t : G) ∈ XbarPre M Q Z B := (mem_XbarPre_iff hc t.2).mpr (ht ▸ hx)
  refine ⟨⟨(t : G), htX⟩, Subtype.ext ?_⟩
  change QuotientGroup.mk (⟨(t : G), XbarPre_le_M hc htX⟩ : ↥M) = x
  have hM : (⟨(t : G), XbarPre_le_M hc htX⟩ : ↥M) = t := Subtype.ext rfl
  rw [hM, ht]

private theorem xbarPreToXbar_eq_one_iff (hc : Ctx M Q Z B) (s : ↥(XbarPre M Q Z B)) :
    xbarPreToXbar hc s = 1 ↔ (s : G) ∈ Q := by
  rw [Subtype.ext_iff]
  change QuotientGroup.mk (⟨(s : G), XbarPre_le_M hc s.2⟩ : ↥M) = 1 ↔ (s : G) ∈ Q
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private noncomputable def xbarPreToGL (hc : Ctx M Q Z B)
    (σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)) :
    ↥(XbarPre M Q Z B) →* GL (Fin m) K :=
  (Matrix.SpecialLinearGroup.toGL (n := Fin m) (R := K)).comp
    (σ₀e.symm.toMonoidHom.comp (xbarPreToXbar hc))

private theorem xbarPreToGL_apply (hc : Ctx M Q Z B)
    (σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)) (s : ↥(XbarPre M Q Z B)) :
    xbarPreToGL hc σ₀e s = Matrix.SpecialLinearGroup.toGL (σ₀e.symm (xbarPreToXbar hc s)) :=
  rfl

private theorem xbarPreToGL_range (hc : Ctx M Q Z B)
    (σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)) :
    (xbarPreToGL hc σ₀e).range = StatedSL m K := by
  rw [xbarPreToGL, MonoidHom.range_comp,
    MonoidHom.range_eq_top_of_surjective (σ₀e.symm.toMonoidHom.comp (xbarPreToXbar hc))
      (σ₀e.symm.surjective.comp (xbarPreToXbar_surjective hc)),
    Subgroup.map_top]
  exact (CFSG.Open.StatedAPI.statedSL_eq_range_toGL m K).symm

private theorem xbarPreToGL_ker (hc : Ctx M Q Z B)
    (σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)) :
    (xbarPreToGL hc σ₀e).ker = Q.subgroupOf (XbarPre M Q Z B) := by
  ext s
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, xbarPreToGL_apply]
  rw [← map_one (Matrix.SpecialLinearGroup.toGL (n := Fin m) (R := K)),
    Matrix.SpecialLinearGroup.toGL_injective.eq_iff]
  have h1 : σ₀e.symm (xbarPreToXbar hc s) = 1 ↔ xbarPreToXbar hc s = 1 := by
    rw [← map_one σ₀e.symm, σ₀e.symm.injective.eq_iff]
  rw [h1, xbarPreToXbar_eq_one_iff hc s]

private noncomputable def imageAddEquiv (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w) :
    (Fin m → K) ≃+ ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype) :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨(F x : M₀.E), ⟨F x, hFW x, rfl⟩⟩
       map_zero' := by
         apply Subtype.ext
         exact congrArg (fun v : ↥(cmComm M Q Z B K γ M₀ φ) => (v : M₀.E)) (map_zero F)
       map_add' := fun x y => by
         apply Subtype.ext
         exact congrArg (fun v : ↥(cmComm M Q Z B K γ M₀ φ) => (v : M₀.E)) (map_add F x y) }
      : (Fin m → K) →+ ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype))
    ⟨fun x y h => by
      have h' : (F x : M₀.E) = (F y : M₀.E) :=
        congrArg (fun w : ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype) => (w : M₀.E)) h
      exact hFinj (Subtype.ext h'), fun w => by
      obtain ⟨w₀, hw₀, hw⟩ := w.2
      obtain ⟨x, hx⟩ := hFsurj w₀ hw₀
      refine ⟨x, Subtype.ext ?_⟩
      show (F x : M₀.E) = (w : M₀.E)
      rw [hx]
      exact hw⟩

private theorem imageAddEquiv_apply (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w) (x : Fin m → K) :
    ((imageAddEquiv (φ := φ) hFinj hFW hFsurj x :
      ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) : M₀.E) = (F x : M₀.E) := by
  rw [imageAddEquiv]
  rfl

private theorem image_invariant (hc : Ctx M Q Z B)
    (hσ₀ : Function.Surjective σ₀)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (hW₁ : ∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) :
    ∀ (s : ↥(XbarH M Q Z B)) (w : M₀.E),
      w ∈ W₁.map (cmComm M Q Z B K γ M₀ φ).subtype →
        φ (s : ↥(H0 M Z)) w ∈ W₁.map (cmComm M Q Z B K γ M₀ φ).subtype := by
  intro s w hw
  obtain ⟨w₀, hw₀, rfl⟩ := hw
  obtain ⟨g, hg⟩ := hσ₀ (xbarHToXbar M Q Z B s)
  refine ⟨ρ g w₀, hW₁ g w₀ hw₀, ?_⟩
  rw [hρ g s hg.symm]
  exact coe_cmCommAct hc φ s w₀

private theorem piPre_normalizer (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hV : ∀ (s : ↥(XbarH M Q Z B)) (w : M₀.E),
      w ∈ W₁.map (cmComm M Q Z B K γ M₀ φ).subtype →
        φ (s : ↥(H0 M Z)) w ∈ W₁.map (cmComm M Q Z B K γ M₀ φ).subtype) :
    XbarPre M Q Z B ≤
      Subgroup.normalizer (piPre M₀ (W₁.map (cmComm M Q Z B K γ M₀ φ).subtype) : Set G) := by
  intro s hs
  rw [mem_normalizer_iff_conjSubgroup_eq]
  exact Ctx.conjSubgroup_piPre_eq hc hD φ hφπ hV ⟨s, hs⟩


private abbrev preimageW₁ : Subgroup G :=
  piPre M₀ (W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)

private noncomputable def piToImage :
    ↥(preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) →* Multiplicative
      ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype) where
  toFun y := Multiplicative.ofAdd ⟨M₀.π (y : G), (mem_piPre M₀).mp y.2 |>.2⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    exact Subtype.ext (pi_one (M₀ := M₀))
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact M₀.π_mul (a : G) ((mem_piPre M₀).mp a.2).1 (b : G) ((mem_piPre M₀).mp b.2).1

private noncomputable def naturalHom (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w) :
    ↥(preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) →* Multiplicative (Fin m → K) :=
  (AddEquiv.toMultiplicative (imageAddEquiv (φ := φ) hFinj hFW hFsurj).symm).toMonoidHom.comp
    (piToImage (M₀ := M₀) (W₁ := W₁))

private theorem naturalHom_apply (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (y : ↥(preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁))) :
    Multiplicative.toAdd (naturalHom (φ := φ) hFinj hFW hFsurj y) =
      (imageAddEquiv (φ := φ) hFinj hFW hFsurj).symm
        ⟨M₀.π (y : G), ((mem_piPre M₀).mp y.2).2⟩ := rfl

private theorem naturalHom_surjective (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w) :
    Function.Surjective (naturalHom (φ := φ) hFinj hFW hFsurj) := by
  intro y
  let x : Fin m → K := Multiplicative.toAdd y
  set w : ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype) :=
    imageAddEquiv (φ := φ) hFinj hFW hFsurj x with hw
  obtain ⟨z, hzQ, hz⟩ := M₀.π_surj (w : M₀.E)
  have hzW : M₀.π z ∈ W₁.map (cmComm M Q Z B K γ M₀ φ).subtype := by
    rw [hz]
    exact w.2
  refine ⟨⟨z, (mem_piPre M₀).mpr ⟨hzQ, hzW⟩⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  change (imageAddEquiv (φ := φ) hFinj hFW hFsurj).symm
    ⟨M₀.π z, hzW⟩ = Multiplicative.toAdd y
  have hwz : (⟨M₀.π z, hzW⟩ : ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) = w :=
    Subtype.ext hz
  rw [hwz, hw]
  exact AddEquiv.symm_apply_apply _ x

private theorem naturalHom_ker (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w) :
    (naturalHom (φ := φ) hFinj hFW hFsurj).ker =
      Z.subgroupOf (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [show naturalHom (φ := φ) hFinj hFW hFsurj y = 1 ↔
      Multiplicative.toAdd (naturalHom (φ := φ) hFinj hFW hFsurj y) = 0 from
    ⟨fun h => by rw [h, toAdd_one], fun h => by
      rw [← ofAdd_toAdd (naturalHom (φ := φ) hFinj hFW hFsurj y), h, ofAdd_zero]⟩]
  rw [naturalHom_apply]
  constructor
  · intro h
    have h' : (⟨M₀.π (y : G), ((mem_piPre M₀).mp y.2).2⟩ :
        ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) = 0 := by
      have := congrArg (imageAddEquiv (φ := φ) hFinj hFW hFsurj) h
      simpa using this
    exact (M₀.π_ker (y : G) ((mem_piPre M₀).mp y.2).1).mp (Subtype.ext_iff.mp h')
  · intro hz
    have hw0 : (⟨M₀.π (y : G), ((mem_piPre M₀).mp y.2).2⟩ :
        ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) = 0 := by
      apply Subtype.ext
      exact (M₀.π_ker (y : G) ((mem_piPre M₀).mp y.2).1).mpr hz
    rw [hw0, map_zero]

private theorem naturalHom_equivariant (hc : Ctx M Q Z B)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (hFinj : Function.Injective F) (hFW : ∀ x, F x ∈ W₁)
    (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    (s : ↥(XbarPre M Q Z B))
    (v w : ↥(preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)))
    (hw : (w : G) = (s : G) * (v : G) * (s : G)⁻¹) :
    Multiplicative.toAdd (naturalHom (φ := φ) hFinj hFW hFsurj w) =
      ((xbarPreToGL hc σ₀e s : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
        Multiplicative.toAdd (naturalHom (φ := φ) hFinj hFW hFsurj v) := by
  classical
  obtain ⟨s', hs'⟩ := exists_XbarH_of_mem_XbarPre hc s.2
  let g : SL(m, K) := σ₀e.symm (xbarPreToXbar hc s)
  have hσ : σ₀ g = xbarPreToXbar hc s := by
    dsimp only [g]
    rw [← hσ₀e]
    exact σ₀e.apply_symm_apply (xbarPreToXbar hc s)
  have hg : xbarHToXbar M Q Z B s' = σ₀ g := by
    apply Subtype.ext
    rw [coe_xbarHToXbar, hσ]
    change QuotientGroup.mk (⟨((s' : ↥(H0 M Z)) : G),
      ((s' : ↥(H0 M Z)).2).1⟩ : ↥M) = (xbarPreToXbar hc s : Mbar M Q)
    rw [show (⟨((s' : ↥(H0 M Z)) : G), ((s' : ↥(H0 M Z)).2).1⟩ : ↥M) =
        ⟨s, XbarPre_le_M hc s.2⟩ from Subtype.ext hs']
    exact (coe_xbarPreToXbar hc s).symm
  have hρg : ρ g = cmCommAct hc φ s' := hρ g s' hg
  let x : Fin m → K :=
    Multiplicative.toAdd (naturalHom (φ := φ) hFinj hFW hFsurj v)
  have hx : x = (imageAddEquiv (φ := φ) hFinj hFW hFsurj).symm
      ⟨M₀.π (v : G), ((mem_piPre M₀).mp v.2).2⟩ :=
    naturalHom_apply (φ := φ) hFinj hFW hFsurj v
  have hv : (imageAddEquiv (φ := φ) hFinj hFW hFsurj x : M₀.E) = M₀.π (v : G) := by
    rw [hx, AddEquiv.apply_symm_apply]
  have hπw : M₀.π (w : G) = φ (s' : ↥(H0 M Z)) (M₀.π (v : G)) := by
    rw [hw, ← hs']
    exact hφπ (s' : ↥(H0 M Z)) (v : G) ((mem_piPre M₀).mp v.2).1
  have hval : (imageAddEquiv (φ := φ) hFinj hFW hFsurj
      ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) : M₀.E) = M₀.π (w : G) := by
    rw [hπw, ← hv]
    have h1 : (imageAddEquiv (φ := φ) hFinj hFW hFsurj
        ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) : M₀.E) =
        (F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) : M₀.E) :=
      imageAddEquiv_apply (φ := φ) hFinj hFW hFsurj _
    have h2 : (F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) : M₀.E) =
        (ρ g (F x) : M₀.E) :=
      congrArg (fun y : ↥(cmComm M Q Z B K γ M₀ φ) => (y : M₀.E)) (hFeq g x)
    have h3 : (F x : M₀.E) = M₀.π (v : G) := by
      rw [← imageAddEquiv_apply (φ := φ) hFinj hFW hFsurj x]
      exact hv
    rw [h1, h2, hρg, coe_cmCommAct, h3, ← hv]
  have hcoord : imageAddEquiv (φ := φ) hFinj hFW hFsurj
      ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) =
      (⟨M₀.π (w : G), ((mem_piPre M₀).mp w.2).2⟩ :
        ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) := by
    apply Subtype.ext
    exact hval
  rw [naturalHom_apply, naturalHom_apply, ← hx]
  rw [show (⟨M₀.π (w : G), ((mem_piPre M₀).mp w.2).2⟩ :
      ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) =
      imageAddEquiv (φ := φ) hFinj hFW hFsurj
        ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) from hcoord.symm]
  rw [AddEquiv.symm_apply_apply]
  rw [xbarPreToGL_apply]
  rfl

private theorem naturalRep_of_decomposition (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hσ₀ : Function.Surjective σ₀)
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (hW₁ : ∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁)
    (hFinj : Function.Injective F) (hFW : ∀ x, F x ∈ W₁)
    (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x)) :
    NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B)
      (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) Z Q := by
  classical
  let f := naturalHom (φ := φ) hFinj hFW hFsurj
  have hf_surj : Function.Surjective f := naturalHom_surjective (φ := φ) hFinj hFW hFsurj
  have hf_ker : f.ker = Z.subgroupOf (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) :=
    naturalHom_ker (φ := φ) hFinj hFW hFsurj
  haveI hZnorm : (Z.subgroupOf (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁))).Normal := by
    rw [← hf_ker]
    infer_instance
  let ψ : ↥(preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) ⧸
      Z.subgroupOf (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) ≃*
      Multiplicative (Fin m → K) :=
    (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf_surj)
  have hψ_mk : ∀ x, ψ (QuotientGroup.mk x) = f x := by
    intro x
    change (QuotientGroup.kerLift f) (QuotientGroup.mk x) = f x
    rfl
  have hnorm : XbarPre M Q Z B ≤
      Subgroup.normalizer (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) : Set G) :=
    piPre_normalizer hc hD hφπ (image_invariant hc hσ₀ hρ hW₁)
  refine ⟨xbarPreToGL hc σ₀e, xbarPreToGL_range hc σ₀e, xbarPreToGL_ker hc σ₀e,
    hnorm, hZnorm, ψ, ?_⟩
  intro s v w hw
  rw [hψ_mk w, hψ_mk v]
  exact naturalHom_equivariant hc hφπ hσ₀e hρ hFinj hFW hFsurj hFeq s v w hw


private noncomputable def projW₂ (hW : IsCompl W₁ W₂) :
    ↥(cmComm M Q Z B K γ M₀ φ) →ₗ[K] ↥W₂ :=
  W₂.projectionOnto W₁ hW.symm

private theorem projW₂_comm (hW : IsCompl W₁ W₂)
    (T : ↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))
    (hT₁ : ∀ w ∈ W₁, T w ∈ W₁) (hT₂ : ∀ w ∈ W₂, T w ∈ W₂)
    (v : ↥(cmComm M Q Z B K γ M₀ φ)) :
    ((projW₂ (φ := φ) hW (T v) : ↥W₂) : ↥(cmComm M Q Z B K γ M₀ φ)) =
      T ((projW₂ (φ := φ) hW v : ↥W₂) : ↥(cmComm M Q Z B K γ M₀ φ)) := by
  have hv : v ∈ W₁ ⊔ W₂ := by rw [hW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := Submodule.mem_sup.mp hv
  have hp₁W : projW₂ (φ := φ) hW v₁ = 0 :=
    (Submodule.projectionOnto_apply_eq_zero_iff hW.symm).mpr hv₁
  have hp₂W : projW₂ (φ := φ) hW v₂ = ⟨v₂, hv₂⟩ :=
    Submodule.projectionOnto_apply_left hW.symm ⟨v₂, hv₂⟩
  have hpT₁W : projW₂ (φ := φ) hW (T v₁) = 0 :=
    (Submodule.projectionOnto_apply_eq_zero_iff hW.symm).mpr (hT₁ v₁ hv₁)
  have hpT₂W : projW₂ (φ := φ) hW (T v₂) = ⟨T v₂, hT₂ v₂ hv₂⟩ :=
    Submodule.projectionOnto_apply_left hW.symm ⟨T v₂, hT₂ v₂ hv₂⟩
  calc
    ((projW₂ (φ := φ) hW (T (v₁ + v₂)) : ↥W₂) :
        ↥(cmComm M Q Z B K γ M₀ φ)) =
      ((projW₂ (φ := φ) hW (T v₁ + T v₂) : ↥W₂) :
        ↥(cmComm M Q Z B K γ M₀ φ)) := by rw [map_add]
    _ = ((projW₂ (φ := φ) hW (T v₁) + projW₂ (φ := φ) hW (T v₂) : ↥W₂) :
        ↥(cmComm M Q Z B K γ M₀ φ)) := by rw [map_add]
    _ = ((0 + ⟨T v₂, hT₂ v₂ hv₂⟩ : ↥W₂) : ↥(cmComm M Q Z B K γ M₀ φ)) := by
      rw [hpT₁W, hpT₂W]
    _ = T v₂ := by simp
    _ = T ((projW₂ (φ := φ) hW (v₁ + v₂) : ↥W₂) :
        ↥(cmComm M Q Z B K γ M₀ φ)) := by
      rw [map_add, hp₁W, hp₂W]
      simp

private noncomputable def dualAddEquiv (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w) :
    (Fin m → K) ≃+ ↥W₂ :=
  AddEquiv.ofBijective
    ({ toFun := fun x => ⟨F' x, hF'W x⟩
       map_zero' := Subtype.ext (map_zero F')
       map_add' := fun x y => Subtype.ext (map_add F' x y) } : (Fin m → K) →+ ↥W₂)
    ⟨fun x y h => hF'inj (Subtype.ext_iff.mp h), fun w => by
      obtain ⟨x, hx⟩ := hF'surj w w.2
      exact ⟨x, Subtype.ext hx⟩⟩


private noncomputable def piQToComm (htop : cmComm M Q Z B K γ M₀ φ = ⊤) :
    ↥Q →* Multiplicative ↥(cmComm M Q Z B K γ M₀ φ) where
  toFun y := Multiplicative.ofAdd
    ⟨M₀.π (y : G), by rw [htop]; exact Submodule.mem_top⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    exact Subtype.ext (pi_one (M₀ := M₀))
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact M₀.π_mul (a : G) a.2 (b : G) b.2

private noncomputable def dualHom (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hW : IsCompl W₁ W₂) (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w) :
    ↥Q →* Multiplicative (Fin m → K) :=
  (AddEquiv.toMultiplicative (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj).symm).toMonoidHom.comp
    ((projW₂ (φ := φ) hW).toAddMonoidHom.toMultiplicative.comp (piQToComm (φ := φ) htop))

private theorem dualHom_apply (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hW : IsCompl W₁ W₂) (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w)
    (y : ↥Q) :
    Multiplicative.toAdd (dualHom (φ := φ) htop hW hF'inj hF'W hF'surj y) =
      (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj).symm
        (projW₂ (φ := φ) hW ⟨M₀.π (y : G), by rw [htop]; exact Submodule.mem_top⟩) :=
  rfl

private theorem dualHom_eq_one_iff (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hW : IsCompl W₁ W₂) (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w)
    (y : ↥Q) :
    dualHom (φ := φ) htop hW hF'inj hF'W hF'surj y = 1 ↔
      (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj).symm
        (projW₂ (φ := φ) hW ⟨M₀.π (y : G), by rw [htop]; exact Submodule.mem_top⟩) = 0 := by
  rw [← ofAdd_toAdd (dualHom (φ := φ) htop hW hF'inj hF'W hF'surj y), ofAdd_eq_one]
  rfl

private theorem dualHom_surjective (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hW : IsCompl W₁ W₂) (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w) :
    Function.Surjective (dualHom (φ := φ) htop hW hF'inj hF'W hF'surj) := by
  intro y
  let x : Fin m → K := Multiplicative.toAdd y
  obtain ⟨z, hzQ, hz⟩ := M₀.π_surj
    ((dualAddEquiv (φ := φ) hF'inj hF'W hF'surj x :
      ↥W₂) : ↥(cmComm M Q Z B K γ M₀ φ))
  refine ⟨⟨z, hzQ⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [dualHom_apply]
  have hz' : (⟨M₀.π z, by rw [htop]; exact Submodule.mem_top⟩ :
      ↥(cmComm M Q Z B K γ M₀ φ)) =
      ((dualAddEquiv (φ := φ) hF'inj hF'W hF'surj x : ↥W₂) :
        ↥(cmComm M Q Z B K γ M₀ φ)) := Subtype.ext hz
  rw [hz']
  have hp : projW₂ (φ := φ) hW
      ((dualAddEquiv (φ := φ) hF'inj hF'W hF'surj x : ↥W₂) :
        ↥(cmComm M Q Z B K γ M₀ φ)) =
      dualAddEquiv (φ := φ) hF'inj hF'W hF'surj x :=
    Submodule.projectionOnto_apply_left hW.symm _
  rw [hp, AddEquiv.symm_apply_apply]

private theorem dualHom_ker (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hW : IsCompl W₁ W₂) (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w) :
    (dualHom (φ := φ) htop hW hF'inj hF'W hF'surj).ker =
      (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)).subgroupOf Q := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, dualHom_eq_one_iff]
  constructor
  · intro h
    have hp0 : projW₂ (φ := φ) hW ⟨M₀.π (y : G), by rw [htop]; exact Submodule.mem_top⟩ = 0 := by
      have := congrArg (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj) h
      simpa using this
    have hmem : (⟨M₀.π (y : G), by rw [htop]; exact Submodule.mem_top⟩ :
        ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W₁ :=
      (Submodule.projectionOnto_apply_eq_zero_iff hW.symm).mp hp0
    exact (mem_piPre M₀).mpr ⟨y.2, ⟨_, hmem, rfl⟩⟩
  · intro hy
    obtain ⟨hyQ, hmem⟩ := (mem_piPre M₀).mp hy
    obtain ⟨w, hw, hwπ⟩ := hmem
    have hmemW₁ : (⟨M₀.π (y : G), by rw [htop]; exact Submodule.mem_top⟩ :
        ↥(cmComm M Q Z B K γ M₀ φ)) ∈ W₁ := by
      rw [show (⟨M₀.π (y : G), by rw [htop]; exact Submodule.mem_top⟩ :
          ↥(cmComm M Q Z B K γ M₀ φ)) = w from Subtype.ext hwπ.symm]
      exact hw
    have hp0 : projW₂ (φ := φ) hW ⟨M₀.π (y : G), by rw [htop]; exact Submodule.mem_top⟩ = 0 :=
      (Submodule.projectionOnto_apply_eq_zero_iff hW.symm).mpr hmemW₁
    have := congrArg (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj).symm hp0
    simpa using this

private theorem dualHom_equivariant (hc : Ctx M Q Z B)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (hW₁ : ∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) (hW₂ : ∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂)
    (htop : cmComm M Q Z B K γ M₀ φ = ⊤) (hW : IsCompl W₁ W₂)
    (hF'inj : Function.Injective F') (hF'W : ∀ x, F' x ∈ W₂)
    (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w)
    (hF'eq : ∀ (g : SL(m, K)) x,
      F' (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) = ρ g (F' x))
    (s : ↥(XbarPre M Q Z B)) (v w : ↥Q)
    (hw : (w : G) = (s : G) * (v : G) * (s : G)⁻¹) :
    Multiplicative.toAdd (dualHom (φ := φ) htop hW hF'inj hF'W hF'surj w) =
      ((((xbarPreToGL hc σ₀e s)⁻¹ : GL (Fin m) K) :
        Matrix (Fin m) (Fin m) K))ᵀ *ᵥ
        Multiplicative.toAdd (dualHom (φ := φ) htop hW hF'inj hF'W hF'surj v) := by
  classical
  obtain ⟨s', hs'⟩ := exists_XbarH_of_mem_XbarPre hc s.2
  let g : SL(m, K) := σ₀e.symm (xbarPreToXbar hc s)
  have hσ : σ₀ g = xbarPreToXbar hc s := by
    dsimp only [g]
    rw [← hσ₀e]
    exact σ₀e.apply_symm_apply (xbarPreToXbar hc s)
  have hg : xbarHToXbar M Q Z B s' = σ₀ g := by
    apply Subtype.ext
    rw [coe_xbarHToXbar, hσ]
    change QuotientGroup.mk (⟨((s' : ↥(H0 M Z)) : G),
      ((s' : ↥(H0 M Z)).2).1⟩ : ↥M) = (xbarPreToXbar hc s : Mbar M Q)
    rw [show (⟨((s' : ↥(H0 M Z)) : G), ((s' : ↥(H0 M Z)).2).1⟩ : ↥M) =
        ⟨s, XbarPre_le_M hc s.2⟩ from Subtype.ext hs']
    exact (coe_xbarPreToXbar hc s).symm
  have hρg : ρ g = cmCommAct hc φ s' := hρ g s' hg
  let x : Fin m → K := Multiplicative.toAdd (dualHom (φ := φ) htop hW hF'inj hF'W hF'surj v)
  have hx : (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj x : ↥W₂) =
      projW₂ (φ := φ) hW ⟨M₀.π (v : G), by rw [htop]; exact Submodule.mem_top⟩ :=
    AddEquiv.apply_symm_apply _ _
  have hxV : (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj x :
      ↥(cmComm M Q Z B K γ M₀ φ)) =
      ((projW₂ (φ := φ) hW ⟨M₀.π (v : G), by rw [htop]; exact Submodule.mem_top⟩ :
        ↥W₂) : ↥(cmComm M Q Z B K γ M₀ φ)) :=
    congrArg (fun w : ↥W₂ => (w : ↥(cmComm M Q Z B K γ M₀ φ))) hx
  have hπw : M₀.π (w : G) = φ (s' : ↥(H0 M Z)) (M₀.π (v : G)) := by
    rw [hw, ← hs']
    exact hφπ (s' : ↥(H0 M Z)) (v : G) v.2
  have hmain : ((projW₂ (φ := φ) hW ⟨M₀.π (w : G), by rw [htop]; exact Submodule.mem_top⟩ :
      ↥W₂) : ↥(cmComm M Q Z B K γ M₀ φ)) =
      (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj
        (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) :
        ↥(cmComm M Q Z B K γ M₀ φ)) := by
    have hww : (⟨M₀.π (w : G), by rw [htop]; exact Submodule.mem_top⟩ :
        ↥(cmComm M Q Z B K γ M₀ φ)) =
        cmCommAct hc φ s' ⟨M₀.π (v : G), by rw [htop]; exact Submodule.mem_top⟩ := by
      apply Subtype.ext
      rw [coe_cmCommAct]
      exact hπw
    rw [hww, ← hρg]
    rw [projW₂_comm (φ := φ) hW (ρ g) (hW₁ g) (hW₂ g) _]
    rw [← hxV]
    have hD : (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj x :
        ↥(cmComm M Q Z B K γ M₀ φ)) = F' x := rfl
    rw [hD, ← hF'eq g x]
    rfl
  have hfinal : (dualAddEquiv (φ := φ) hF'inj hF'W hF'surj).symm
      (projW₂ (φ := φ) hW ⟨M₀.π (w : G), by rw [htop]; exact Submodule.mem_top⟩) =
      (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) := by
    rw [AddEquiv.symm_apply_eq]
    exact Subtype.ext hmain
  have hmat : ((((xbarPreToGL hc σ₀e s)⁻¹ : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K)) =
      (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)) := by
    rw [show xbarPreToGL hc σ₀e s = Matrix.SpecialLinearGroup.toGL g from rfl]
    rw [← map_inv (Matrix.SpecialLinearGroup.toGL) g]
    rfl
  rw [dualHom_apply, dualHom_apply, hfinal, hmat]
  dsimp only [x]
  rw [dualHom_apply]

private theorem naturalDualRep_of_decomposition (hc : Ctx M Q Z B)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (hW₁ : ∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) (hW₂ : ∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂)
    (htop : cmComm M Q Z B K γ M₀ φ = ⊤) (hW : IsCompl W₁ W₂)
    (hF'inj : Function.Injective F') (hF'W : ∀ x, F' x ∈ W₂)
    (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w)
    (hF'eq : ∀ (g : SL(m, K)) x,
      F' (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) = ρ g (F' x)) :
    NaturalDualRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) Q
      (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) Q := by
  classical
  let f := dualHom (φ := φ) htop hW hF'inj hF'W hF'surj
  have hf_surj : Function.Surjective f :=
    dualHom_surjective (φ := φ) htop hW hF'inj hF'W hF'surj
  have hf_ker : f.ker = (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)).subgroupOf Q :=
    dualHom_ker (φ := φ) htop hW hF'inj hF'W hF'surj
  haveI hN : ((preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)).subgroupOf Q).Normal := by
    rw [← hf_ker]
    infer_instance
  let ψ : ↥Q ⧸ (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)).subgroupOf Q ≃*
      Multiplicative (Fin m → K) :=
    (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf_surj)
  have hψ_mk : ∀ x, ψ (QuotientGroup.mk x) = f x := by
    intro x
    change (QuotientGroup.kerLift f) (QuotientGroup.mk x) = f x
    rfl
  have hnorm : XbarPre M Q Z B ≤ Subgroup.normalizer (Q : Set G) :=
    fun s hs => hc.hyp.Q_normal.2 (XbarPre_le_M hc hs)
  refine ⟨xbarPreToGL hc σ₀e, xbarPreToGL_range hc σ₀e, xbarPreToGL_ker hc σ₀e,
    hnorm, hN, ψ, ?_⟩
  intro s v w hw
  rw [hψ_mk w, hψ_mk v]
  exact dualHom_equivariant hc hφπ hσ₀e hρ hW₁ hW₂ htop hW hF'inj hF'W hF'surj hF'eq s v w hw


private theorem preimageW₁_le_Q :
    preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) ≤ Q :=
  fun _ hx => ((mem_piPre M₀).mp hx).1

private theorem Z_le_preimageW₁ (hc : Ctx M Q Z B) :
    Z ≤ preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) := by
  intro z hz
  have hzQ : z ∈ Q := hc.hyp.Z_normal.1 hz
  exact (mem_piPre M₀).mpr ⟨hzQ, by
    rw [(M₀.π_ker z hzQ).mpr hz]
    exact (W₁.map (cmComm M Q Z B K γ M₀ φ).subtype).zero_mem⟩

private theorem exists_XbarH_xbarHToXbar (hc : Ctx M Q Z B)
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (s : ↥(XbarPre M Q Z B)) :
    ∃ s' : ↥(XbarH M Q Z B), (s' : G) = (s : G) ∧
      xbarHToXbar M Q Z B s' = σ₀ (σ₀e.symm (xbarPreToXbar hc s)) := by
  obtain ⟨s', hs'⟩ := exists_XbarH_of_mem_XbarPre hc s.2
  refine ⟨s', hs', ?_⟩
  have hσ : σ₀ (σ₀e.symm (xbarPreToXbar hc s)) = xbarPreToXbar hc s := by
    rw [← hσ₀e]
    exact σ₀e.apply_symm_apply (xbarPreToXbar hc s)
  apply Subtype.ext
  rw [coe_xbarHToXbar, hσ]
  change QuotientGroup.mk (⟨((s' : ↥(H0 M Z)) : G),
    ((s' : ↥(H0 M Z)).2).1⟩ : ↥M) = (xbarPreToXbar hc s : Mbar M Q)
  rw [show (⟨((s' : ↥(H0 M Z)) : G), ((s' : ↥(H0 M Z)).2).1⟩ : ↥M) =
      ⟨s, XbarPre_le_M hc s.2⟩ from Subtype.ext hs']
  exact (coe_xbarPreToXbar hc s).symm

private theorem commutator_le_preimageW₁ (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hσ₀ : Function.Surjective σ₀) (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)),
      xbarHToXbar M Q Z B s = σ₀ g → ρ g = cmCommAct hc φ s)
    (hW₁ : ∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) :
    ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), XbarPre M Q Z B⁆ ≤
      preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) := by
  have hnorm : XbarPre M Q Z B ≤
      Subgroup.normalizer (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) : Set G) :=
    piPre_normalizer hc hD hφπ (image_invariant hc hσ₀ hρ hW₁)
  rw [Subgroup.commutator_le]
  intro x hx s hs
  have hsnorm : s ∈ Subgroup.normalizer
      (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) : Set G) := hnorm hs
  have h1 : s * x⁻¹ * s⁻¹ ∈ preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) :=
    (Subgroup.mem_normalizer_iff.mp hsnorm x⁻¹).mp (Subgroup.inv_mem _ hx)
  have e : ⁅x, s⁆ = x * (s * x⁻¹ * s⁻¹) := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)).mul_mem hx h1


private theorem mem_sup_of_commutator (hc : Ctx M Q Z B) {y : G} (hyQ : y ∈ Q)
    (s : ↥(XbarPre M Q Z B)) {y' : G}
    (hy'X : y' ∈ preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁))
    (hπ : M₀.π ⁅(s : G), y'⁆ = M₀.π y) :
    y ∈ Z ⊔ ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), XbarPre M Q Z B⁆ := by
  have hy'Q : y' ∈ Q := preimageW₁_le_Q hy'X
  have hcommQ : ⁅(s : G), y'⁆ ∈ Q := by
    have hcomm : ⁅(s : G), y'⁆ = (s : G) * y' * (s : G)⁻¹ * y'⁻¹ := by
      rw [commutatorElement_def]
    rw [hcomm]
    exact Q.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (XbarPre_le_M hc s.2)) y').mp hy'Q)
      (Q.inv_mem hy'Q)
  have hmemcomm : ⁅(s : G), y'⁆ ∈ ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁),
      XbarPre M Q Z B⁆ := by
    rw [show ⁅(s : G), y'⁆ = ⁅y', (s : G)⁆⁻¹ from
      (commutatorElement_inv (g₁ := y') (g₂ := (s : G))).symm]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hy'X s.2)
  have hyZ : y * ⁅(s : G), y'⁆⁻¹ ∈ Z := by
    apply (M₀.π_ker (y * ⁅(s : G), y'⁆⁻¹) (Q.mul_mem hyQ (Q.inv_mem hcommQ))).mp
    have hprod2 : M₀.π (y * ⁅(s : G), y'⁆⁻¹) =
        M₀.π y + M₀.π (⁅(s : G), y'⁆⁻¹) :=
      M₀.π_mul y hyQ _ (Q.inv_mem hcommQ)
    rw [hprod2, pi_inv hcommQ, hπ]
    abel
  have hyEq : y = (y * ⁅(s : G), y'⁆⁻¹) * ⁅(s : G), y'⁆ := by group
  rw [hyEq]
  exact (Z ⊔ ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), XbarPre M Q Z B⁆).mul_mem
    (Subgroup.mem_sup_left hyZ) (Subgroup.mem_sup_right hmemcomm)

private theorem exists_commutator_of_transvection (hc : Ctx M Q Z B)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hFinj : Function.Injective F) (hFW : ∀ x, F x ∈ W₁)
    (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    {y : G} (hyQ : y ∈ Q)
    (hmem : M₀.π y ∈ W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)
    (x : Fin m → K)
    (hx : (imageAddEquiv (φ := φ) hFinj hFW hFsurj) x = ⟨M₀.π y, hmem⟩)
    {x' : Fin m → K} {A : GL (Fin m) K} (hA : A ∈ StatedSL m K)
    (hAx : A *ᵥ x' = x' + x) :
    y ∈ Z ⊔ ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), XbarPre M Q Z B⁆ := by
  classical
  let F₁ := imageAddEquiv (φ := φ) hFinj hFW hFsurj
  let e : M₀.E := M₀.π (y : G)
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp
    (by rw [xbarPreToGL_range hc σ₀e]; exact hA)
  let g : SL(m, K) := σ₀e.symm (xbarPreToXbar hc s)
  have hg : Matrix.SpecialLinearGroup.toGL g = A := by
    rw [← xbarPreToGL_apply hc σ₀e s, hs]
  obtain ⟨s', hs'G, hs'X⟩ := exists_XbarH_xbarHToXbar hc hσ₀e s
  have hρg : ρ g = cmCommAct hc φ s' := hρ g s' hs'X
  let w' : ↥(cmComm M Q Z B K γ M₀ φ) :=
    ⟨(F₁ x' : M₀.E), by
      have h : (F₁ x' : M₀.E) ∈ (⊤ : Submodule K M₀.E) := Submodule.mem_top
      rwa [← htop] at h⟩
  have hw'F : w' = F x' :=
    Subtype.ext (imageAddEquiv_apply (φ := φ) hFinj hFW hFsurj x')
  obtain ⟨y', hy'Q, hy'π⟩ := M₀.π_surj (w' : M₀.E)
  have hy'X : y' ∈ preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) := by
    exact (mem_piPre M₀).mpr ⟨hy'Q, by rw [hy'π]; exact (F₁ x').2⟩
  let a : G := (s : G) * y' * (s : G)⁻¹
  have hcomm : ⁅(s : G), y'⁆ = a * y'⁻¹ := rfl
  have haQ : a ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (XbarPre_le_M hc s.2)) y').mp hy'Q
  have hπ1 : M₀.π a = φ (s' : ↥(H0 M Z)) (M₀.π y') := by
    have := hφπ (s' : ↥(H0 M Z)) y' hy'Q
    rwa [hs'G] at this
  have hwπ : (w' : M₀.E) = M₀.π y' := hy'π.symm
  have hcm : φ (s' : ↥(H0 M Z)) (M₀.π y') =
      (cmCommAct hc φ s' w' : M₀.E) := by
    rw [← hwπ, coe_cmCommAct]
  have hgw : (ρ g w' : M₀.E) = (F (g *ᵥ x') : M₀.E) := by
    rw [congrArg (fun v : ↥(cmComm M Q Z B K γ M₀ φ) => (v : M₀.E)) (hFeq g x'),
      ← hw'F]
  have hgx : g *ᵥ x' = x' + x := by
    rw [show (g : Matrix (Fin m) (Fin m) K) = (A : Matrix (Fin m) (Fin m) K) by
      rw [← hg]
      rfl, hAx]
  have hprod : M₀.π (a * y'⁻¹) = M₀.π a + M₀.π (y'⁻¹) :=
    M₀.π_mul a haQ (y'⁻¹) (Q.inv_mem hy'Q)
  have hπcomm : M₀.π ⁅(s : G), y'⁆ = e := by
    rw [hcomm, hprod, hπ1, pi_inv hy'Q, hcm, ← hρg, hgw, ← hwπ, hw'F, hgx, map_add,
      Submodule.coe_add, ← imageAddEquiv_apply (φ := φ) hFinj hFW hFsurj x, hx]
    abel
  exact mem_sup_of_commutator hc hyQ s hy'X hπcomm

private theorem preimageW₁_le_sup_commutator_of_ne_zero (hc : Ctx M Q Z B)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hFinj : Function.Injective F) (hFW : ∀ x, F x ∈ W₁)
    (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    (hm : 3 ≤ m) {y : G}
    (hy : y ∈ preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁))
    (he : M₀.π (y : G) ≠ 0) :
    y ∈ Z ⊔ ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), XbarPre M Q Z B⁆ := by
  classical
  have hyQ : y ∈ Q := preimageW₁_le_Q hy
  have hmem : M₀.π (y : G) ∈ W₁.map (cmComm M Q Z B K γ M₀ φ).subtype :=
    ((mem_piPre M₀).mp hy).2
  let e : M₀.E := M₀.π (y : G)
  let F₁ := imageAddEquiv (φ := φ) hFinj hFW hFsurj
  let x : Fin m → K := F₁.symm ⟨e, hmem⟩
  have hx : F₁ x = ⟨e, hmem⟩ := AddEquiv.apply_symm_apply F₁ _
  have hx0 : x ≠ 0 := by
    intro hx0
    apply he
    have h0 : (⟨e, hmem⟩ : ↥(W₁.map (cmComm M Q Z B K γ M₀ φ).subtype)) = 0 := by
      rw [← hx, hx0, map_zero]
    exact congrArg Subtype.val h0
  obtain ⟨j, hj⟩ : ∃ j : Fin m, x j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hx0 (funext h)
  have hm2 : 2 ≤ m := le_trans (by norm_num : 2 ≤ 3) hm
  obtain ⟨i, hij⟩ : ∃ i : Fin m, i ≠ j := by
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : (⟨0, by omega⟩ : Fin m) = j := h _
    have h1 : (⟨1, by omega⟩ : Fin m) = j := h _
    have h01 : (⟨0, by omega⟩ : Fin m) = (⟨1, by omega⟩ : Fin m) := h0.trans h1.symm
    exact absurd h01 (by simp)
  let x' : Fin m → K := Pi.single i 1
  have hx'ind : ∀ s t : K, s • x' + t • (x' + x) = 0 → s = 0 ∧ t = 0 := by
    intro s t hst
    have hj0 : (s • x' + t • (x' + x)) j = 0 := by rw [hst]; rfl
    have hxj : x' j = 0 := by simp [x', Pi.single_apply, hij]
    have htj : t * x j = 0 := by simpa [hxj] using hj0
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp htj with h | h
      · exact h
      · exact absurd h hj
    have hi0 : (s • x' + t • (x' + x)) i = 0 := by rw [hst]; rfl
    have hxi : x' i = 1 := by simp [x']
    have hsi : s = 0 := by simpa [hxi, ht0] using hi0
    exact ⟨hsi, ht0⟩
  obtain ⟨A, hA, hAx⟩ :=
    exists_statedSL_mulVec_eq_of_independent (x := x') (y := x' + x) hx'ind
  exact exists_commutator_of_transvection hc hφπ hσ₀e hρ htop hFinj hFW hFsurj hFeq
    hyQ hmem x hx hA hAx

private theorem preimageW₁_le_sup_commutator (hc : Ctx M Q Z B)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hFinj : Function.Injective F) (hFW : ∀ x, F x ∈ W₁)
    (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    (hm : 3 ≤ m) :
    preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) ≤
      Z ⊔ ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), XbarPre M Q Z B⁆ := by
  intro y hy
  have hyQ : y ∈ Q := preimageW₁_le_Q hy
  by_cases he : M₀.π (y : G) = 0
  · exact Subgroup.mem_sup_left ((M₀.π_ker (y : G) hyQ).mp he)
  · exact preimageW₁_le_sup_commutator_of_ne_zero hc hφπ hσ₀e hρ htop hFinj hFW hFsurj
      hFeq hm hy he

private theorem commutator_Z_XbarPre_le (hc : Ctx M Q Z B) :
    ⁅Z, XbarPre M Q Z B⁆ ≤ Z := by
  rw [Subgroup.commutator_le]
  intro z hz s hs
  have hcent : s ∈ Subgroup.centralizer (Z : Set G) := (XbarPre_le_H0 hc hs).2
  have hcomm : z * s = s * z := Subgroup.mem_centralizer_iff.mp hcent z hz
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
  exact Z.one_mem

private theorem Q_eq_sup_commutator (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (htop : cmComm M Q Z B K γ M₀ φ = ⊤) :
    Q = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ := by
  have h := piPre_cmComm_eq_sup_comm hc hD φ hφπ
  rwa [htop, piPre_top] at h

private theorem preimageW₁_eq_sup_commutator (hc : Ctx M Q Z B)
    (hD : GlobalModelData M Q Z γ M₀)
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y))
    (hσ₀ : Function.Surjective σ₀)
    {σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B)} (hσ₀e : ∀ g, σ₀e g = σ₀ g)
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    (hW₁ : ∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁)
    (hFinj : Function.Injective F) (hFW : ∀ x, F x ∈ W₁)
    (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    (hm : 3 ≤ m) :
    preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) =
      Z ⊔ ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), XbarPre M Q Z B⁆ :=
  le_antisymm
    (preimageW₁_le_sup_commutator hc hφπ hσ₀e hρ htop hFinj hFW hFsurj hFeq hm)
    (sup_le (Z_le_preimageW₁ hc)
      (commutator_le_preimageW₁ hc hD hφπ hσ₀ hρ hW₁))

end TransportData

theorem Ctx.cmLmChain_chain_of_rt1 (hc : Ctx M Q Z B) (hD : GlobalModelData M Q Z γ M₀)
    (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (g : ↥(H0 M Z)) (y : G), y ∈ Q →
      M₀.π ((g : G) * y * (g : G)⁻¹) = φ g (M₀.π y)) {m : ℕ} (hm : 3 ≤ m)
    {σ₀ : SL(m, K) →* ↥(Xbar M Q Z B)} (hσ₀ : Function.Surjective σ₀)
    {ρ : SL(m, K) →* (↥(cmComm M Q Z B K γ M₀ φ) ≃ₗ[K] ↥(cmComm M Q Z B K γ M₀ φ))}
    (hρ : ∀ (g : SL(m, K)) (s : ↥(XbarH M Q Z B)), xbarHToXbar M Q Z B s = σ₀ g →
      ρ g = cmCommAct hc φ s)
    (htop : cmComm M Q Z B K γ M₀ φ = ⊤)
    {W₁ W₂ : Submodule K ↥(cmComm M Q Z B K γ M₀ φ)} (hW : IsCompl W₁ W₂)
    (hW₁ : ∀ g, ∀ w ∈ W₁, ρ g w ∈ W₁) (hW₂ : ∀ g, ∀ w ∈ W₂, ρ g w ∈ W₂)
    {F : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hFinj : Function.Injective F)
    (hFW : ∀ x, F x ∈ W₁) (hFsurj : ∀ w ∈ W₁, ∃ x, F x = w)
    (hFeq : ∀ (g : SL(m, K)) x, F ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) = ρ g (F x))
    {F' : (Fin m → K) →+ ↥(cmComm M Q Z B K γ M₀ φ)}
    (hF'inj : Function.Injective F')
    (hF'W : ∀ x, F' x ∈ W₂) (hF'surj : ∀ w ∈ W₂, ∃ x, F' x = w)
    (hF'eq : ∀ (g : SL(m, K)) x,
      F' (((g⁻¹ : SL(m, K)) : Matrix (Fin m) (Fin m) K)ᵀ *ᵥ x) = ρ g (F' x)) :
    ∃ X₁ X₂ X₃ X₄ : Subgroup G,
      X₁ = Z ∧ X₁ ≤ X₂ ∧ X₂ ≤ X₃ ∧ X₃ ≤ X₄ ∧ X₄ = Q ∧
      ⁅X₁, XbarPre M Q Z B⁆ ≤ Z ∧
      X₂ = Z ⊔ ⁅X₃, XbarPre M Q Z B⁆ ∧ X₃ = X₂ ∧
      X₄ = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ ∧
      ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = Nat.card Z ∧
        NaturalRep (ι := Fin m) K' (StatedSL m K') (XbarPre M Q Z B) X₂ X₁ Q ∧
        NaturalDualRep (ι := Fin m) K' (StatedSL m K') (XbarPre M Q Z B) X₄ X₃ Q := by
  classical
  let hf : Function.Bijective σ₀ := ⟨sigma0_injective hc hρ hFeq hFinj, hσ₀⟩
  let σ₀e : SL(m, K) ≃* ↥(Xbar M Q Z B) := MulEquiv.ofBijective σ₀ hf
  have hσ₀e : ∀ g, σ₀e g = σ₀ g := fun g => rfl
  have hX₂ : preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁) =
      Z ⊔ ⁅preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), XbarPre M Q Z B⁆ :=
    preimageW₁_eq_sup_commutator hc hD hφπ hσ₀ hσ₀e hρ htop hW₁ hFinj hFW hFsurj hFeq hm
  have hnat : NaturalRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B)
      (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) Z Q :=
    naturalRep_of_decomposition hc hD hφπ hσ₀ hσ₀e hρ hW₁ hFinj hFW hFsurj hFeq
  have hdual : NaturalDualRep (ι := Fin m) K (StatedSL m K) (XbarPre M Q Z B) Q
      (preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁)) Q :=
    naturalDualRep_of_decomposition hc hφπ hσ₀e hρ hW₁ hW₂ htop hW hF'inj hF'W hF'surj hF'eq
  have hQ : Q = Z ⊔ ⁅Q, XbarPre M Q Z B⁆ := Q_eq_sup_commutator hc hD hφπ htop
  refine ⟨Z, preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁),
    preimageW₁ (φ := φ) (M₀ := M₀) (W₁ := W₁), Q, rfl, Z_le_preimageW₁ hc, le_rfl,
    preimageW₁_le_Q, rfl, commutator_Z_XbarPre_le hc, hX₂, rfl, hQ, K, inferInstance,
    inferInstance, hD.card, hnat, hdual⟩

end CFSG.RankThree.GF2n.Stroth80
