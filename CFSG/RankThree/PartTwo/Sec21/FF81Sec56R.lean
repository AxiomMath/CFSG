module

public import CFSG.RankThree.PartTwo.Sec21.RudvalisFF81Sp6Over
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec56A
import CFSG.RankThree.GF2n.Stroth80.Sec311SLTorus
import CFSG.Quasithin.AppendixH.H14.H141Octad

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Quasithin.H13.MatNCert Matrix
open Sp6Over (GL7 GL6 M6 M7 V7 stab7 piM piHom)

variable {G : Type} [Group G] [Finite G]

namespace S56

theorem mulVec_succ {A : M7} (hA : A *ᵥ Pi.single 0 1 = Pi.single 0 1) (w : V7) (i : Fin 6) :
    (A *ᵥ w) i.succ = (piM A *ᵥ fun j => w j.succ) i := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, piM, Matrix.of_apply,
    Sp6Over.col_zero_of_fix hA i, zero_mul, zero_add]

theorem exists_coord {Z : Subgroup G} (hZ : CFSG.Open.IsElemAbelian 2 Z) (hc : Nat.card Z = 2 ^ 7)
    {s : G} (hsZ : s ∈ Z) (hs1 : s ≠ 1) :
    ∃ κ : ↥Z ≃* Multiplicative V7, κ ⟨s, hsZ⟩ = Multiplicative.ofAdd (Pi.single 0 1) := by
  obtain ⟨κ₀⟩ := CFSG.Quasithin.AppendixH.H14.exists_mulEquiv_elemAbelian_two Z hZ 7 hc
  have hx₀ : Multiplicative.toAdd (κ₀ ⟨s, hsZ⟩) ≠ 0 := fun h => hs1 (by
    have h1 : κ₀ ⟨s, hsZ⟩ = κ₀ 1 := by rw [map_one]; exact h
    exact congrArg Subtype.val (κ₀.injective h1))
  obtain ⟨M, hdet, hM⟩ :=
    CFSG.RankThree.GF2n.Stroth80.exists_det_one_mulVec_eq_single (p := 0) (q := 1) (by decide) hx₀
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  have hinv' : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  let φ : Multiplicative V7 ≃* Multiplicative V7 :=
    { toFun := fun v => Multiplicative.ofAdd (M *ᵥ Multiplicative.toAdd v)
      invFun := fun v => Multiplicative.ofAdd (M⁻¹ *ᵥ Multiplicative.toAdd v)
      left_inv := fun v => by simp [Matrix.mulVec_mulVec, hinv]
      right_inv := fun v => by simp [Matrix.mulVec_mulVec, hinv']
      map_mul' := fun v w => by simp [Matrix.mulVec_add] }
  exact ⟨κ₀.trans φ, by simp [φ, hM]⟩

variable {s₀ : G}

theorem center_conj : ∀ g ∈ Cen s₀, ∀ z ∈ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)),
    g * z * g⁻¹ ∈ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)) := fun _ hg _ hz => conj_mem_center hg hz

noncomputable def rho7 (κ : ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ≃* Multiplicative V7) :
    ↥(Cen s₀) →* GL7 :=
  Sp6Over.rhoT center_conj κ

theorem rho7_mulVec (κ : ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ≃* Multiplicative V7)
    {g : G} (hg : g ∈ Cen s₀) {z : G} (hz : z ∈ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) :
    ((rho7 κ ⟨g, hg⟩ : GL7) : M7) *ᵥ Multiplicative.toAdd (κ ⟨z, hz⟩) =
      Multiplicative.toAdd (κ ⟨g * z * g⁻¹, center_conj g hg z hz⟩) :=
  Sp6Over.rhoT_mulVec center_conj κ ⟨g, hg⟩ ⟨z, hz⟩

variable (hs : orderOf s₀ = 2) (κ : ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ≃* Multiplicative V7)
  (hκ : κ ⟨s₀, s₀_mem_center hs⟩ = Multiplicative.ofAdd (Pi.single 0 1))

include hκ in
theorem rho7_mem_stab (g : ↥(Cen s₀)) : rho7 κ g ∈ stab7 := by
  rw [Sp6Over.mem_stab7]
  have h := rho7_mulVec κ g.2 (s₀_mem_center hs)
  rw [hκ] at h
  have hgs : (g : G) * s₀ * (g : G)⁻¹ = s₀ := by
    rw [(Subgroup.mem_centralizer_singleton_iff.mp g.2), mul_inv_cancel_right]
  have he : (⟨(g : G) * s₀ * (g : G)⁻¹, center_conj (g : G) g.2 s₀ (s₀_mem_center hs)⟩ :
      ↥(Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)))) = ⟨s₀, s₀_mem_center hs⟩ := Subtype.ext hgs
  rw [he, hκ] at h
  exact h

noncomputable def rhoBar : ↥(Cen s₀) →* GL6 :=
  piHom.comp ((rho7 κ).codRestrict stab7 (rho7_mem_stab hs κ hκ))

theorem coe_rhoBar (g : ↥(Cen s₀)) :
    ((rhoBar hs κ hκ g : GL6) : M6) = piM ((rho7 κ g : GL7) : M7) := rfl

include hκ in
theorem conj_of_rhoBar_eq_one {g : G} (hg : g ∈ Cen s₀) (h1 : rhoBar hs κ hκ ⟨g, hg⟩ = 1)
    {z : G} (hz : z ∈ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) :
    g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * s₀ := by
  set A : M7 := ((rho7 κ ⟨g, hg⟩ : GL7) : M7) with hAdef
  have hA : A *ᵥ Pi.single 0 1 = Pi.single 0 1 := rho7_mem_stab hs κ hκ ⟨g, hg⟩
  have hpi : piM A = 1 := by
    have := congrArg (fun x : GL6 => (x : M6)) h1
    simpa only [coe_rhoBar, Units.val_one] using this
  set w := Multiplicative.toAdd (κ ⟨z, hz⟩) with hw
  have hAw := rho7_mulVec κ hg hz
  rw [← hAdef, ← hw] at hAw
  have htail : ∀ i : Fin 6, (A *ᵥ w) i.succ = w i.succ := fun i => by
    rw [mulVec_succ hA, hpi, Matrix.one_mulVec]
  have h01 : ∀ a c : ZMod 2, a = c ∨ a = c + 1 := by decide
  have hs' : Multiplicative.toAdd (κ ⟨s₀, s₀_mem_center hs⟩) = Pi.single 0 1 := by
    rw [hκ]; rfl
  rcases h01 ((A *ᵥ w) 0) (w 0) with h0 | h0
  · left
    have heq : A *ᵥ w = w := by
      ext i
      refine Fin.cases ?_ (fun i => htail i) i
      exact h0
    rw [heq] at hAw
    have := congrArg Subtype.val (κ.injective (Multiplicative.toAdd.injective hAw))
    exact this.symm
  · right
    have heq : A *ᵥ w = w + Pi.single 0 1 := by
      ext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [h0]
      · simp [htail i, Pi.single_apply, Fin.succ_ne_zero]
    rw [heq, ← hs', hw, ← toAdd_mul, ← map_mul] at hAw
    have := congrArg Subtype.val (κ.injective (Multiplicative.toAdd.injective hAw))
    exact this.symm

include hκ in
theorem card_cen_le {g : G} (hg : g ∈ Cen s₀) :
    Nat.card ↥((Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ⊓ Cen g) ≤
      2 * Nat.card {v : Fin 6 → ZMod 2 // ((rhoBar hs κ hκ ⟨g, hg⟩ : GL6) : M6) *ᵥ v = v} := by
  set A : M7 := ((rho7 κ ⟨g, hg⟩ : GL7) : M7) with hAdef
  have hA : A *ᵥ Pi.single 0 1 = Pi.single 0 1 := rho7_mem_stab hs κ hκ ⟨g, hg⟩
  rw [Sp6Over.card_T_inf_cen center_conj κ hg, coe_rhoBar]
  change Nat.card {v : V7 // A *ᵥ v = v} ≤ 2 * Nat.card {v : Fin 6 → ZMod 2 // piM A *ᵥ v = v}
  have hinj : Function.Injective (fun v : {v : V7 // A *ᵥ v = v} =>
      ((v.1 0, ⟨fun i => v.1 i.succ, by
        funext i
        rw [← mulVec_succ hA]
        exact congrFun v.2 i.succ⟩) : ZMod 2 × {w : Fin 6 → ZMod 2 // piM A *ᵥ w = w})) := by
    intro v v' h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    apply Subtype.ext
    funext i
    refine Fin.cases h.1 (fun i => congrFun h.2 i) i
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := ZMod 2), ZMod.card] at this

end S56

end CFSG.RankThree.PartTwo.Sec21.FF81
