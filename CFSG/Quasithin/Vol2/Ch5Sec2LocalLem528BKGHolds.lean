module

public import CFSG.Quasithin.Background.A7Q528Main
public import CFSG.Quasithin.Background.SL3SmallGroup
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BKG

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin.B45Alt7
open scoped IsMulCommutative commutatorElement

theorem a7Q528Fact_holds : A7Q528Fact := by
  intro G _ _ X Q K hQX hXN hQab hQ2 hCQ hQcard ⟨α, hαs, hαker⟩ hQK hKX hQKc h7
  classical
  have : (Q.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hXN
  have : CFSG.IsElementaryAbelian 2 ↥Q :=
    { is_comm := ⟨fun a b => Subtype.ext (hQab a a.2 b b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun q =>
        Subtype.ext (by simpa using hQ2 q q.2) }
  let _ : MulDistribMulAction ↥X ↥Q := MulDistribMulAction.compHom ↥Q (SL3Small.conjAut hQX)
  set ρX : Representation (ZMod 2) ↥X (Additive ↥Q) :=
    CFSG.Theory.Representation.ofElementaryAbelianAction (A := ↥X) (G := ↥Q) (p := 2) with hρX
  have hρXapp : ∀ (x : ↥X) (q : ↥Q),
      ρX x (Additive.ofMul q) = Additive.ofMul (SL3Small.conjAut hQX x q) := fun x q => by
    rw [hρX, CFSG.Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
    rfl
  have hker : α.ker ≤ ρX.asGroupHom.ker := by
    intro x hx
    rw [hαker, Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    apply Units.ext
    rw [Representation.asGroupHom_apply, Units.val_one]
    apply LinearMap.ext
    intro w
    induction w using Additive.rec with
    | ofMul q =>
      rw [hρXapp, Module.End.one_apply]
      congr 1
      apply Subtype.ext
      rw [SL3Small.coe_conjAut, hQab _ hx _ q.2, mul_inv_cancel_right]
  set ρU : A7 →* (Module.End (ZMod 2) (Additive ↥Q))ˣ :=
    α.liftOfRightInverse (Function.surjInv hαs) (Function.rightInverse_surjInv hαs)
      ⟨ρX.asGroupHom, hker⟩ with hρU
  set ρ : Representation (ZMod 2) A7 (Additive ↥Q) := (Units.coeHom _).comp ρU with hρ
  have hρα : ∀ x : ↥X, ρ (α x) = ρX x := fun x => by
    rw [hρ, MonoidHom.comp_apply, hρU, MonoidHom.liftOfRightInverse_comp_apply]
    rfl
  set H : Subgroup A7 := (K.subgroupOf X).map α with hH
  have hcardH : Nat.card H = Q.relIndex K := by
    rw [hH, ← Subgroup.relIndex_ker, hαker, Subgroup.relIndex_subgroupOf hKX]
  have hnt : ∃ g v, ρ g v ≠ v := by
    by_contra hall
    push Not at hall
    set x := Function.surjInv hαs (gen7 false) with hx
    have hαx : α x = gen7 false := Function.surjInv_eq hαs _
    have hxc : (x : G) ∈ X ⊓ Subgroup.centralizer (Q : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 := hall (α x) (Additive.ofMul ⟨q, hq⟩)
      rw [hρα, hρXapp] at h1
      have h2 : (x : G) * q * (x : G)⁻¹ = q := by
        have h3 := congrArg (fun w : Additive ↥Q => ((Additive.toMul w : ↥Q) : G)) h1
        simpa [SL3Small.coe_conjAut] using h3
      have h4 := congrArg (· * (x : G)) h2
      simp only [inv_mul_cancel_right] at h4
      exact h4.symm
    have h1 : x ∈ α.ker := by
      rw [hαker, Subgroup.mem_subgroupOf]
      exact hCQ hxc
    rw [MonoidHom.mem_ker, hαx] at h1
    exact absurd h1 (by decide)
  have hspan : ∀ C : Submodule (ZMod 2) (Additive ↥Q), (∀ g ∈ H, ∀ v, ρ g v - v ∈ C) →
      C = ⊤ := by
    intro C hC
    let D : Subgroup ↥Q :=
      { carrier := {q | Additive.ofMul q ∈ C}
        mul_mem' := fun ha hb => C.add_mem ha hb
        one_mem' := C.zero_mem
        inv_mem' := fun ha => C.neg_mem ha }
    have hle : ⁅Q, K⁆ ≤ D.map Q.subtype := by
      rw [Subgroup.commutator_le]
      intro q hq k hk
      refine ⟨⟨q, hq⟩ * (SL3Small.conjAut hQX ⟨k, hKX hk⟩ ⟨q, hq⟩)⁻¹, ?_, ?_⟩
      · have e : Additive.ofMul (⟨q, hq⟩ * (SL3Small.conjAut hQX ⟨k, hKX hk⟩ ⟨q, hq⟩)⁻¹ : ↥Q) =
            -(ρ (α ⟨k, hKX hk⟩) (Additive.ofMul ⟨q, hq⟩) - Additive.ofMul ⟨q, hq⟩) := by
          rw [hρα, hρXapp, ofMul_mul, ofMul_inv]
          abel
        have h1 : Additive.ofMul
            (⟨q, hq⟩ * (SL3Small.conjAut hQX ⟨k, hKX hk⟩ ⟨q, hq⟩)⁻¹ : ↥Q) ∈ C := by
          rw [e]
          exact C.neg_mem (hC _ ⟨⟨k, hKX hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩ _)
        exact h1
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
          SL3Small.coe_conjAut]
        rw [commutatorElement_def]
        group
    have hQD : Q ≤ D.map Q.subtype := hQKc.symm.le.trans hle
    rw [eq_top_iff]
    intro w _
    induction w using Additive.rec with
    | ofMul q =>
      obtain ⟨q', hq', hqq'⟩ := hQD q.2
      have e : q' = q := Subtype.ext hqq'
      rw [← e]
      exact hq'
  have h7' : ¬ 7 ∣ Nat.card H := by
    rw [hcardH]
    exact h7
  obtain ⟨hcard4, hirr⟩ := A7Q528.main ρ H h7' hQcard hnt hspan
  refine ⟨hcard4, fun W hWQ hXW => ?_⟩
  let CW : Submodule (ZMod 2) (Additive ↥Q) :=
    { carrier := {w | ((Additive.toMul w : ↥Q) : G) ∈ W}
      add_mem' := fun {a b} ha hb => W.mul_mem ha hb
      zero_mem' := W.one_mem
      smul_mem' := fun c w hw => by
        have e : c • w = c.val • w := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 2), ZMod.natCast_zmod_val]
        show ((Additive.toMul (c • w) : ↥Q) : G) ∈ W
        rw [e, toMul_nsmul, Subgroup.coe_pow]
        exact W.pow_mem hw _ }
  have hCW : ∀ g, ∀ w ∈ CW, ρ g w ∈ CW := by
    intro g w hw
    obtain ⟨x, rfl⟩ := hαs g
    rw [hρα]
    induction w using Additive.rec with
    | ofMul q =>
      rw [hρXapp]
      show ((SL3Small.conjAut hQX x q : ↥Q) : G) ∈ W
      rw [SL3Small.coe_conjAut]
      exact (Subgroup.mem_normalizer_iff.mp (hXW x.2) q).mp hw
  rcases hirr CW hCW with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : Additive.ofMul (⟨w, hWQ hw⟩ : ↥Q) ∈ CW := hw
    rw [h, Submodule.mem_bot] at h1
    have h2 : (⟨w, hWQ hw⟩ : ↥Q) = 1 := h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  · right
    refine le_antisymm hWQ fun q hq => ?_
    have h1 : Additive.ofMul (⟨q, hq⟩ : ↥Q) ∈ CW := h ▸ Submodule.mem_top
    exact h1

end CFSG.Quasithin.H13
