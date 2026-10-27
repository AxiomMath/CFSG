module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinTwoTBMain
public import CFSG.LocalAnalysis.StandardType.GGOrthKStructNormalizerAux
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoMoves
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9N3
import CFSG.Mathlib.GroupTheory.Automorphism.ConjCommute

public section

namespace CFSG.StandardType.FrameRoute

open Multiplicative CFSG.StandardType.ChoiceTwo

theorem isSignedPerm_of_spSignedGroup {s : ℕ}
    (α : MulAut (Fin s → Multiplicative (ZMod 3)))
    (hα : α.toEquiv ∈ SpJoin.spSignedGroup s 3) : SpCoord.IsSignedPerm α := by
  let f : MulAut (Fin s → Multiplicative (ZMod 3)) →*
      Equiv.Perm (Fin s → Multiplicative (ZMod 3)) :=
    { toFun := fun β => β.toEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hle : SpJoin.spSignedGroup s 3 ≤
      (SignedPermCount.signedPermSubgroup 3 s).map f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val + 1 < s
    · rw [SpJoin.spReflPerm_of_lt s 3 i hi]
      exact Subgroup.mem_map.mpr ⟨SpCoord.permAut (Equiv.swap i ⟨i.val + 1, hi⟩),
        SpCoord.isSignedPerm_permAut _, rfl⟩
    · rw [SpJoin.spReflPerm_of_not_lt s 3 i hi]
      exact Subgroup.mem_map.mpr ⟨SpCoord.sgnAut i, SpCoord.isSignedPerm_sgnAut i, rfl⟩
  obtain ⟨β, hβ, hβα⟩ := Subgroup.mem_map.mp (hle hα)
  have heq : β = α := MulEquiv.ext fun v => congrArg (fun γ : Equiv.Perm _ => γ v) hβα
  rw [← heq]
  exact hβ

theorem isSignedPerm_of_torus_weight_action {G : Type} [Group G] {s : ℕ}
    (D : LinTwoTB.TorusData G s)
    (wt : G → ℕ) {e : ℕ} (he : 0 < e)
    (hw : ∀ v, wt (D.el v) = e * LinTwoTv.hamWt v)
    (hwt : ∀ (α : MulAut G) x, wt (α x) = wt x)
    (α : MulAut G) (φ : MulAut (Fin s → Multiplicative (ZMod 3)))
    (hφ : ∀ f, α (D.el (fun i => toAdd (f i))) = D.el (fun i => toAdd (φ f i))) :
    SpCoord.IsSignedPerm φ := by
  have hHam : ∀ f, LinTwoTv.hamWt (fun i => toAdd (φ f i)) =
      LinTwoTv.hamWt (fun i => toAdd (f i)) := by
    intro f
    have hf := hwt α (D.el (fun i => toAdd (f i)))
    rw [hφ, hw, hw] at hf
    exact Nat.eq_of_mul_eq_mul_left he hf
  have hNorm : ∀ f : Fin s → Multiplicative (ZMod 3),
      okNorm_wt f = LinTwoTv.hamWt (fun i => toAdd (f i)) := by
    intro f
    simp only [okNorm_wt, LinTwoTv.hamWt]
    congr 1
  apply isSignedPerm_of_spSignedGroup φ
  apply okNorm_mem_spSignedGroup_of_weight φ
  intro f
  rw [hNorm, hNorm]
  exact hHam f

theorem exists_moveExp_of_torus_weight_action {G : Type} [Group G] {s : ℕ}
    (D : LinTwoTB.TorusData G s) (wt : G → ℕ) {e : ℕ} (he : 0 < e)
    (hw : ∀ v, wt (D.el v) = e * LinTwoTv.hamWt v)
    (hwt : ∀ (α : MulAut G) x, wt (α x) = wt x)
    (α : MulAut G) (φ : MulAut (Fin s → Multiplicative (ZMod 3)))
    (hφ : ∀ f, α (D.el (fun i => toAdd (f i))) = D.el (fun i => toAdd (φ f i))) :
    ∃ (π : Equiv.Perm (Fin s)) (η : Fin s → Bool),
      ∀ v, α (D.el v) = D.el (moveExp π η v) := by
  classical
  obtain ⟨π, ε, hε, hact⟩ := isSignedPerm_of_torus_weight_action D wt he hw hwt α φ hφ
  let η : Fin s → Bool := fun i => if ε (π.symm i) = 1 then false else true
  have hsgn : ∀ i a, ε (π.symm i) * a = sgnZ (η i) a := by
    intro i a
    rcases hε (π.symm i) with h | h <;>
      simp [η, h, sgnZ, show (-1 : ZMod 3) ≠ 1 by decide]
  refine ⟨π.symm, η, fun v => ?_⟩
  have hv : (fun i => toAdd (φ (fun j => ofAdd (v j)) i)) = moveExp π.symm η v := by
    funext i
    have h := hact (fun j => ofAdd (v j)) (π.symm i)
    rw [Equiv.apply_symm_apply, toAdd_ofAdd] at h
    rw [h, moveExp_apply]
    exact hsgn i _
  simpa only [toAdd_ofAdd, hv] using hφ (fun i => ofAdd (v i))

theorem exists_actor_equiv_of_torusData {G : Type} [Group G] {s : ℕ}
    (D : LinTwoTB.TorusData G s) {A : Subgroup (MulAut G)}
    (hZ : ∀ g h : G, MulAut.conj g = MulAut.conj h → g = h) (hA : D.IsTorusAut A) :
    ∃ Θ : (Fin s → Multiplicative (ZMod 3)) ≃* A,
      ∀ f, (Θ f : MulAut G) = MulAut.conj (D.el (fun i => toAdd (f i))) := by
  let μ : (Fin s → Multiplicative (ZMod 3)) ≃* Multiplicative (Fin s → ZMod 3) :=
    { toFun := fun f => ofAdd (fun i => toAdd (f i))
      invFun := fun v i => ofAdd (toAdd v i)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let t : Multiplicative (Fin s → ZMod 3) →* MulAut G :=
    (MulAut.conj : G →* MulAut G).comp D.ι
  have ht : Function.Injective t := fun v w h => D.inj (hZ _ _ h)
  have htr : t.range = A := by
    ext α
    rw [hA]
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨toAdd v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨ofAdd v, rfl⟩
  let Θ := μ.trans ((MonoidHom.ofInjective ht).trans (MulEquiv.subgroupCongr htr))
  exact ⟨Θ, fun _ => rfl⟩

theorem torus_action_of_normalizer_actor {G : Type} [Group G] {s : ℕ}
    (D : LinTwoTB.TorusData G s) {A : Subgroup (MulAut G)}
    (hZ : ∀ g h : G, MulAut.conj g = MulAut.conj h → g = h)
    (Θ : (Fin s → Multiplicative (ZMod 3)) ≃* A)
    (hΘ : ∀ f, (Θ f : MulAut G) = MulAut.conj (D.el (fun i => toAdd (f i))))
    (α : MulAut G) (hα : α ∈ Subgroup.normalizer (A : Set (MulAut G))) :
    ∀ f, α (D.el (fun i => toAdd (f i))) =
      D.el (fun i => toAdd (((MulAut.congr Θ).symm (ggConjAut A hα)) f i)) := by
  intro f
  let φ := (MulAut.congr Θ).symm (ggConjAut A hα)
  have heq : Θ (φ f) = ggConjAut A hα (Θ f) := by
    change Θ (Θ.symm (ggConjAut A hα (Θ f))) = _
    exact Θ.apply_symm_apply _
  apply hZ
  rw [← CFSG.mulAut_conj_mul_inv α]
  have h := congrArg Subtype.val heq
  rw [ggConjAut_apply, hΘ, hΘ] at h
  exact h.symm

theorem card_automizer_actor_torus_dvd {G : Type} [Group G] {s : ℕ}
    (D : LinTwoTB.TorusData G s) {A : Subgroup (MulAut G)}
    (hZ : ∀ g h : G, MulAut.conj g = MulAut.conj h → g = h) (hA : D.IsTorusAut A)
    (wt : G → ℕ) {e : ℕ} (he : 0 < e)
    (hw : ∀ v, wt (D.el v) = e * LinTwoTv.hamWt v)
    (hwt : ∀ (α : MulAut G) x, wt (α x) = wt x) :
    Nat.card (ggAutomizer (⊤ : Subgroup (MulAut G)) A) ∣ 2 ^ s * s.factorial := by
  obtain ⟨Θ, hΘ⟩ := exists_actor_equiv_of_torusData D hZ hA
  refine P9_N3a_card_dvd Θ fun α hα => ?_
  exact isSignedPerm_of_torus_weight_action D wt he hw hwt α _
    (torus_action_of_normalizer_actor D hZ Θ hΘ α hα)

theorem exists_conj_moveExp_of_torusData {G : Type} [Group G] {s : ℕ}
    (D : LinTwoTB.TorusData G s) (π : Equiv.Perm (Fin s)) (η : Fin s → Bool) :
    ∃ g : G, ∀ v, g * D.el v * g⁻¹ = D.el (moveExp π η v) := by
  classical
  let H : Subgroup (MulAut (Fin s → Multiplicative (ZMod 3))) :=
    { carrier := {α | ∃ g : G, ∀ f,
        g * D.el (fun i => toAdd (f i)) * g⁻¹ =
          D.el (fun i => toAdd (α f i))}
      one_mem' := ⟨1, fun f => by simp⟩
      mul_mem' := by
        rintro α β ⟨g, hg⟩ ⟨h, hh⟩
        refine ⟨g * h, fun f => ?_⟩
        calc
          (g * h) * D.el (fun i => toAdd (f i)) * (g * h)⁻¹ =
              g * (h * D.el (fun i => toAdd (f i)) * h⁻¹) * g⁻¹ := by group
          _ = g * D.el (fun i => toAdd (β f i)) * g⁻¹ := by rw [hh]
          _ = D.el (fun i => toAdd ((α * β) f i)) := hg (β f)
      inv_mem' := by
        rintro α ⟨g, hg⟩
        refine ⟨g⁻¹, fun f => ?_⟩
        have hf := hg (α⁻¹ f)
        rw [MulAut.apply_inv_self] at hf
        rw [inv_inv, ← hf]
        group }
  have hs : ∀ i : Fin s, SpCoord.sgnAut i ∈ H := by
    intro i
    refine ⟨D.sg i, fun f => ?_⟩
    rw [D.sg_conj]
    congr 1
  have ht : ∀ i j : Fin s, i ≠ j → SpCoord.permAut (Equiv.swap i j) ∈ H := by
    intro i j _
    refine ⟨D.sw i j, fun f => ?_⟩
    rw [D.sw_conj]
    simp only [LinTwoTB.swapV, SpCoord.permAut_apply, Equiv.Perm.coe_inv,
      Equiv.symm_swap, Function.comp_def]
  let ε : Fin s → ZMod 3 := fun i => if η i then -1 else 1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := by
    intro i
    cases hη : η i <;> simp [ε, hη]
  let α := SpCoord.diagAut ε (fun i => SpCoord.coord_sign_mul_self (hε i)) *
    SpCoord.permAut π.symm
  have hα : ∀ f i, toAdd (α f i) = sgnZ (η i) (toAdd (f (π i))) := by
    intro f i
    cases hη : η i <;>
      simp [α, ε, SpCoord.diagAut_apply, SpCoord.permAut_apply, MulAut.mul_apply, sgnZ, hη]
  have hSigned : SpCoord.IsSignedPerm α := by
    refine ⟨π.symm, fun i => ε (π.symm i), fun i => hε _, fun f i => ?_⟩
    rw [hα, Equiv.apply_symm_apply]
    cases hη : η (π.symm i) <;> simp [sgnZ, ε, hη]
  obtain ⟨g, hg⟩ := SpCoord.mem_of_isSignedPerm hs ht hSigned
  refine ⟨g, fun v => ?_⟩
  have hf : (fun i => toAdd (α (fun j => ofAdd (v j)) i)) = moveExp π η v := by
    funext i
    rw [hα]
    rfl
  simpa only [toAdd_ofAdd, hf] using hg (fun i => ofAdd (v i))

end CFSG.StandardType.FrameRoute

end
