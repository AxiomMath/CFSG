module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Quasi
public import CFSG.Quasithin.Background.G11Basic
public import CFSG.SignalizerFunctorTheorem.Quadratic.Toolkit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183k3_fixSub_le_of_not_centralizes {L Y : Subgroup (LGL 2 V)}
    (hL : CFSG.Open.IsQuasisimple ↥L)
    (hY : ∀ y ∈ Y, ∀ x ∈ L, y * x * y⁻¹ ∈ L) (hnc : ∃ y ∈ Y, ∃ x ∈ L, x * y ≠ y * x)
    {P : Submodule (ZMod 2) V} (hP : ∀ l ∈ L, ∀ p ∈ P, l p ∈ P) (hfix : P ≤ fixSub Y) :
    P ≤ fixSub L := by
  let K : Subgroup (LGL 2 V) :=
    { carrier := {x | x ∈ L ∧ ∀ p ∈ P, x p = p}
      one_mem' := ⟨L.one_mem, fun _ _ => rfl⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨L.mul_mem ha.1 hb.1, fun p hp => by
          rw [LinearEquiv.mul_apply, hb.2 p hp, ha.2 p hp]⟩
      inv_mem' := fun {a} ha =>
        ⟨L.inv_mem ha.1, fun p hp => by
          calc a⁻¹ p = a⁻¹ (a p) := by rw [ha.2 p hp]
            _ = p := a.symm_apply_apply p⟩ }
  have hKL : K ≤ L := fun x hx => hx.1
  have hKn : ∀ y ∈ L, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    refine ⟨L.mul_mem (L.mul_mem hy hk.1) (L.inv_mem hy), fun p hp => ?_⟩
    have hyp : y⁻¹ p ∈ P := hP y⁻¹ (L.inv_mem hy) p hp
    rw [show (y * k * y⁻¹) p = y (k (y⁻¹ p)) by simp only [LinearEquiv.mul_apply]]
    rw [hk.2 (y⁻¹ p) hyp]
    exact y.apply_symm_apply p
  rcases quasi_normal_dichotomy hL hKL hKn with hcent | htop
  · exfalso
    obtain ⟨y, hy, x, hx, hxy⟩ := hnc
    have hmod : ∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ quasiCentre L := by
      intro l hl
      have hmem : l * y * l⁻¹ * y⁻¹ ∈ K := by
        refine ⟨?_, ?_⟩
        · have h1 : y * l⁻¹ * y⁻¹ ∈ L := hY y hy l⁻¹ (L.inv_mem hl)
          rw [show l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) by group]
          exact L.mul_mem hl h1
        · intro p hp
          have hyinv : y⁻¹ p = p := hfix hp y⁻¹ (Y.inv_mem hy)
          have hlinv : l⁻¹ p ∈ P := hP l⁻¹ (L.inv_mem hl) p hp
          have hyl : y (l⁻¹ p) = l⁻¹ p := hfix hlinv y hy
          rw [show (l * y * l⁻¹ * y⁻¹) p = l (y (l⁻¹ (y⁻¹ p))) by
                simp only [LinearEquiv.mul_apply]]
          rw [hyinv, hyl]
          exact l.apply_symm_apply p
      have hinv : (l * y * l⁻¹ * y⁻¹)⁻¹ ∈ quasiCentre L :=
        (quasiCentre L).inv_mem (hcent hmem)
      rwa [show (l * y * l⁻¹ * y⁻¹)⁻¹ = y * l * y⁻¹ * l⁻¹ by group] at hinv
    have hcomm := quasi_comm_of_comm_mod_centre hL (fun l hl => hY y hy l hl) hmod
    exact hxy (hcomm x hx).symm
  · intro p hp
    rw [mem_fixSub]
    intro l hl
    have hlK : l ∈ K := htop ▸ hl
    exact hlK.2 p hp

theorem w183k3_fixSub_le_of_not_central {L X : Subgroup (LGL 2 V)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hXL : X ≤ L) (hX : ¬ X ≤ quasiCentre L)
    {P : Submodule (ZMod 2) V} (hP : ∀ l ∈ L, ∀ p ∈ P, l p ∈ P) (hfix : P ≤ fixSub X) :
    P ≤ fixSub L := by
  let K : Subgroup (LGL 2 V) :=
    { carrier := {x | x ∈ L ∧ ∀ p ∈ P, x p = p}
      one_mem' := ⟨L.one_mem, fun _ _ => rfl⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨L.mul_mem ha.1 hb.1, fun p hp => by
          rw [LinearEquiv.mul_apply, hb.2 p hp, ha.2 p hp]⟩
      inv_mem' := fun {a} ha =>
        ⟨L.inv_mem ha.1, fun p hp => by
          calc a⁻¹ p = a⁻¹ (a p) := by rw [ha.2 p hp]
            _ = p := a.symm_apply_apply p⟩ }
  have hKL : K ≤ L := fun x hx => hx.1
  have hKn : ∀ y ∈ L, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    refine ⟨L.mul_mem (L.mul_mem hy hk.1) (L.inv_mem hy), fun p hp => ?_⟩
    have hyp : y⁻¹ p ∈ P := hP y⁻¹ (L.inv_mem hy) p hp
    rw [show (y * k * y⁻¹) p = y (k (y⁻¹ p)) by simp only [LinearEquiv.mul_apply]]
    rw [hk.2 (y⁻¹ p) hyp]
    exact y.apply_symm_apply p
  have hXK : X ≤ K := fun x hx => ⟨hXL hx, fun p hp => hfix hp x hx⟩
  rcases quasi_normal_dichotomy hL hKL hKn with hcent | htop
  · exact absurd (hXK.trans hcent) hX
  · intro p hp
    rw [mem_fixSub]
    intro l hl
    have hlK : l ∈ K := htop ▸ hl
    exact hlK.2 p hp

theorem w183k3_commSpace_le_of_not_central {L X : Subgroup (LGL 2 V)}
    (hL : CFSG.Open.IsQuasisimple ↥L) (hXL : X ≤ L) (hX : ¬ X ≤ quasiCentre L)
    {P : Submodule (ZMod 2) V} (hP : ∀ l ∈ L, ∀ p ∈ P, l p ∈ P) (hcomm : commSpace X ⊤ ≤ P) :
    commSpace L ⊤ ≤ P := by
  let K : Subgroup (LGL 2 V) :=
    { carrier := {x | x ∈ L ∧ ∀ v : V, x v - v ∈ P}
      one_mem' := ⟨L.one_mem, fun v => by simp⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨L.mul_mem ha.1 hb.1, fun v => by
          rw [LinearEquiv.mul_apply]
          have h1 : a (b v) - a v ∈ P := by
            rw [← map_sub]
            exact hP a ha.1 (b v - v) (hb.2 v)
          have h2 : a v - v ∈ P := ha.2 v
          have he : a (b v) - v = (a (b v) - a v) + (a v - v) := by abel
          rw [he]
          exact P.add_mem h1 h2⟩
      inv_mem' := fun {a} ha =>
        ⟨L.inv_mem ha.1, fun v => by
          have h : v - a⁻¹ v ∈ P := by simpa using ha.2 (a⁻¹ v)
          simpa using P.neg_mem h⟩ }
  have hKL : K ≤ L := fun x hx => hx.1
  have hKn : ∀ y ∈ L, ∀ k ∈ K, y * k * y⁻¹ ∈ K := by
    intro y hy k hk
    refine ⟨L.mul_mem (L.mul_mem hy hk.1) (L.inv_mem hy), fun v => ?_⟩
    have hk' : k (y⁻¹ v) - y⁻¹ v ∈ P := hk.2 (y⁻¹ v)
    have he : (y * k * y⁻¹) v - v = y (k (y⁻¹ v) - y⁻¹ v) := by
      have h1 : (y * k * y⁻¹) v = y (k (y⁻¹ v)) := by
        simp only [LinearEquiv.mul_apply]
      rw [h1, map_sub]
      exact congrArg (fun w => y (k (y⁻¹ v)) - w) (y.apply_symm_apply v).symm
    rw [he]
    exact hP y hy _ hk'
  have hXK : X ≤ K := fun x hx =>
    ⟨hXL hx, fun v => hcomm (sub_mem_commSpace hx (Submodule.mem_top))⟩
  rcases quasi_normal_dichotomy hL hKL hKn with hcent | htop
  · exact absurd (hXK.trans hcent) hX
  · rw [commSpace_le_iff]
    intro l hl v _
    have hlK : l ∈ K := htop ▸ hl
    exact hlK.2 v

end CFSG.LocalAnalysis.WeakClosure81

end
