module

public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore

public section

namespace CFSG.StandardType

namespace TwE6TB

open CFSG CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem ggTorusModelSCr_of_scWeylModel {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hZ : Subgroup.center R = ⊥) (hIp : GGOutdiagPrime p R I)
    (hcp : GGCenterPrime p R) (h : GGSCWeylModel p r R) : GGTorusModelSCr p r R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap, hAΛ, hEab, hcardE, hscE⟩ :=
    exists_innerModel hp hZ hIp hcp ψ hψ hker hperf hA hAI hsc
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  set E : Subgroup R := A.comap Λ with hE
  have hrE : p ^ r ≤ Nat.card E := by rw [hcardE]; exact hr
  have h3E : p ^ 3 ≤ Nat.card E := by rw [hcardE]; exact h3
  obtain ⟨ΦE, w, hw⟩ := h E hEab hrE h3E hscE
  have hcommE : ∀ {x y : R}, x ∈ E → y ∈ E → x * y = y * x := by
    intro x y hx hy
    simpa using congrArg Subtype.val (hEab.1.is_comm.comm (⟨x, hx⟩ : E) (⟨y, hy⟩ : E))
  let Φ0 : E →* A :=
    { toFun := fun e => ⟨Λ e, e.2⟩
      map_one' := by apply Subtype.ext; exact map_one Λ
      map_mul' := fun e₁ e₂ => Subtype.ext (map_mul Λ (e₁ : R) (e₂ : R)) }
  have hΦ0bij : Function.Bijective Φ0 := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  let Φ0e : E ≃* A := MulEquiv.ofBijective Φ0 hΦ0bij
  let Φ : A ≃* Multiplicative (Fin 6 → ZMod p) := Φ0e.symm.trans ΦE
  let wtilde : Fin 6 → L' := fun i => (hψ (w i)).choose
  have hψt : ∀ i, ψ (wtilde i) = w i := fun i => (hψ (w i)).choose_spec
  refine ⟨Φ, wtilde, ?_, ?_⟩
  ·
    intro i a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have hψn : ψ (wtilde i) * e * (ψ (wtilde i))⁻¹ ∈ E := by
      have h1 : w i * e * (w i)⁻¹ ∈ E := by
        have h2 := hw i ⟨e, heE⟩
        rw [show w i * e * (w i)⁻¹ =
          (↑(ΦE.symm (Multiplicative.ofAdd (reflE6 p i
            (Multiplicative.toAdd (ΦE ⟨e, heE⟩))))) : R) from h2]
        exact (ΦE.symm _).2
      rwa [hψt i]
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e) (hEab.2 e heE)
    have hlx : Λ e = MulAut.conj x := hΛeq hx
    have hy : ψ (wtilde i * x * (wtilde i)⁻¹) = ψ (wtilde i) * e * (ψ (wtilde i))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hx]
    have hyp : (wtilde i * x * (wtilde i)⁻¹) ^ p = 1 := by
      rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    have hcomm : x * (wtilde i * x * (wtilde i)⁻¹) = (wtilde i * x * (wtilde i)⁻¹) * x :=
      commute_of_lift_pow_eq_one hp hker hcpL
        (by rw [hy, hx]; exact hcommE heE hψn) hyp
    have hform : wtilde i * (Λ e (wtilde i))⁻¹ = (wtilde i * x * (wtilde i)⁻¹) * x⁻¹ := by
      rw [hlx, MulAut.conj_apply]
      group
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (wtilde i * x * (wtilde i)⁻¹) x⁻¹ :=
        (show Commute x (wtilde i * x * (wtilde i)⁻¹) from hcomm).symm.inv_right
      rw [hform, hc.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
    · obtain ⟨e'', rfl⟩ := hAΛ a' ha'
      have he''E : e'' ∈ E := ha'
      obtain ⟨z, hz, hzp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e'') (hEab.2 e'' he''E)
      have hzx : z * x = x * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hx]; exact hcommE he''E heE) hxp
      have hzy : z * (wtilde i * x * (wtilde i)⁻¹) = (wtilde i * x * (wtilde i)⁻¹) * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hy]; exact hcommE he''E hψn) hyp
      have hcy : Commute z (wtilde i * x * (wtilde i)⁻¹) := hzy
      have hcx : Commute z x⁻¹ := (show Commute z x from hzx).inv_right
      rw [hform, hΛeq hz, MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  ·
    intro i a
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heA : Λ e ∈ A := he ▸ a.2
    let eE : E := ⟨e, heA⟩
    have haeq : a = Φ0e eE := Subtype.ext he.symm
    have hΦa : Φ (Φ0e eE) = ΦE eE := by
      show (Φ0e.symm.trans ΦE) (Φ0e eE) = ΦE eE
      rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have hΦsymm : ∀ y : Multiplicative (Fin 6 → ZMod p),
        ((Φ.symm y : A) : MulAut L') = Λ ((ΦE.symm y : E) : R) := by
      intro y
      have h1 : Φ.symm y = Φ0e (ΦE.symm y) := by
        rw [MulEquiv.symm_apply_eq]
        show y = Φ (Φ0e (ΦE.symm y))
        rw [show Φ = Φ0e.symm.trans ΦE from rfl, MulEquiv.trans_apply,
          MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply]
      rw [h1]
      rfl
    have hcnj : MulAut.conj (wtilde i) * Λ (eE : R) * (MulAut.conj (wtilde i))⁻¹ =
        Λ (w i * (eE : R) * (w i)⁻¹) := by
      rw [← hΛn (wtilde i), ← hψt i, map_mul, map_mul, map_inv]
    rw [haeq, hΦa, hΦsymm]
    change MulAut.conj (wtilde i) * Λ (eE : R) * (MulAut.conj (wtilde i))⁻¹ =
      Λ ((ΦE.symm (Multiplicative.ofAdd (reflE6 p i (Multiplicative.toAdd (ΦE eE))))) : R)
    rw [hcnj, hw i eE]

section FramePackage


theorem ggSCWeylModel_of_framePackage {p r : ℕ} [NeZero p] (hr : 4 ≤ r) {R : Type} [Group R]
    (h : GGTwE6FramePackage p R) : GGSCWeylModel p r R := by
  classical
  intro E hE hcard hcard3 hsc
  obtain ⟨t, m, ht, hm, hT, hAut⟩ := h
  have hp_pos : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hp4 : p ^ 4 ≤ Nat.card E := le_trans (Nat.pow_le_pow_right hp_pos hr) hcard
  obtain ⟨c, hEc⟩ := hT E hE hp4 hsc
  let F : Multiplicative (Fin 6 → ZMod p) → E := fun y =>
    ⟨c * t y * c⁻¹, by
      rw [hEc]
      exact ⟨t y, ⟨y, rfl⟩, by simp [MulAut.conj_apply]⟩⟩
  have hFmul : ∀ y z : Multiplicative (Fin 6 → ZMod p), F (y * z) = F y * F z := by
    intro y z
    apply Subtype.ext
    change c * t (y * z) * c⁻¹ = (c * t y * c⁻¹) * (c * t z * c⁻¹)
    rw [map_mul]
    group
  let Fhom : Multiplicative (Fin 6 → ZMod p) →* E := MonoidHom.mk' F hFmul
  have hFbij : Function.Bijective Fhom := by
    refine ⟨fun y z hyz => ?_, fun e => ?_⟩
    · have h1 : (MulAut.conj c) (t y) = (MulAut.conj c) (t z) := by
        simpa [Fhom, F, MulAut.conj_apply] using congrArg Subtype.val hyz
      exact ht ((MulAut.conj c).injective h1)
    · have he : (e : R) ∈ t.range.map (MulAut.conj c).toMonoidHom := by
        rw [← hEc]; exact e.2
      obtain ⟨x, hxr, hx⟩ := Subgroup.mem_map.mp he
      obtain ⟨y, rfl⟩ := hxr
      exact ⟨y, Subtype.ext (by simpa [Fhom, F, MulAut.conj_apply] using hx)⟩
  let X : Multiplicative (Fin 6 → ZMod p) ≃* E := MulEquiv.ofBijective Fhom hFbij
  let ΦE : E ≃* Multiplicative (Fin 6 → ZMod p) := X.symm
  have hΦE_symm : ∀ y : Multiplicative (Fin 6 → ZMod p),
      ((ΦE.symm y : E) : R) = c * t y * c⁻¹ := by
    intro y
    have h1 : ΦE.symm y = X y := by
      show X.symm.symm y = X y
      rw [MulEquiv.symm_symm]
    rw [h1]
    rfl
  have hΦE_F : ∀ y : Multiplicative (Fin 6 → ZMod p), ΦE (Fhom y) = y := by
    intro y
    show X.symm (X y) = y
    exact MulEquiv.symm_apply_apply X y
  refine ⟨ΦE, fun i => c * m (simple TwistTag.E6.tag i) * c⁻¹, ?_⟩
  intro i e
  obtain ⟨y, rfl⟩ := hFbij.2 e
  have hL : ((Fhom y : E) : R) = c * t y * c⁻¹ := rfl
  have hR : ((ΦE.symm (Multiplicative.ofAdd (reflE6 p i
        (Multiplicative.toAdd (ΦE (Fhom y))))) : E) : R)
      = c * t (Multiplicative.ofAdd (reflE6 p i (Multiplicative.toAdd (ΦE (Fhom y))))) * c⁻¹ :=
    hΦE_symm _
  rw [hL, hR, hΦE_F y]
  rw [show (c * m (simple TwistTag.E6.tag i) * c⁻¹) * (c * t y * c⁻¹) *
        (c * m (simple TwistTag.E6.tag i) * c⁻¹)⁻¹ =
      c * (m (simple TwistTag.E6.tag i) * t y * (m (simple TwistTag.E6.tag i))⁻¹) * c⁻¹
      from by group]
  have htorus : TableBExc.torusAct TwistTag.E6.tag p (simple TwistTag.E6.tag i)
      (Multiplicative.toAdd y) = TwE6TB.reflE6 p i (Multiplicative.toAdd y) :=
    ExcFrames.torusAct_simple_E6 i (Multiplicative.toAdd y)
  rw [show t y = t (Multiplicative.ofAdd (Multiplicative.toAdd y)) from rfl,
    hm (simple TwistTag.E6.tag i) (Multiplicative.toAdd y)]
  exact congrArg (fun z => c * t (Multiplicative.ofAdd z) * c⁻¹) htorus

end FramePackage

end TwE6TB

end CFSG.StandardType
