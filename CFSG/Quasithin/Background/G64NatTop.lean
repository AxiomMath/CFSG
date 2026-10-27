module

public import CFSG.Quasithin.Background.G64NatSec

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {V : Type*} [CommGroup V]

theorem card_sup_mul_card_inf {M : Type*} [CommGroup M] (A B : Subgroup M) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card B (A ⊔ B)
  rw [inf_of_le_left le_sup_right, Subgroup.relIndex_sup_right] at h1
  have h2 := Subgroup.relIndex_mul_card B A
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

theorem RealizesVia.eq_one_of_trivial {D : FFModel} (hD : D.Faithful) {H : Subgroup (MulAut V)}
    {U Z : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) {x : MulAut V} (hx : x ∈ H)
    (htriv : ∀ u ∈ U, x u * u⁻¹ ∈ Z) : x = 1 := by
  obtain ⟨γ, hγ⟩ := h.1 ⟨x, hx⟩
  by_contra hx1
  have hγ1 : γ ≠ 1 := by
    intro h1
    apply hx1
    rw [h1, map_one] at hγ
    exact (congrArg Subtype.val hγ).symm
  obtain ⟨u, hu, hmv⟩ := RealizesVia.exists_moved hD h hγ1
  rw [hγ] at hmv
  exact hmv (htriv u hu)

variable {n : ℕ}

@[expose] noncomputable def natAut (γ : GL (Fin n) (ZMod 2)) :
    MulAut (Multiplicative (Fin n → ZMod 2)) where
  toFun x := Multiplicative.ofAdd (glLin n γ (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd ((glLin n γ).symm (Multiplicative.toAdd x))
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := by simp

theorem natAut_apply (γ : GL (Fin n) (ZMod 2)) (x : Multiplicative (Fin n → ZMod 2)) :
    natAut γ x = natAct (StatedSL n (ZMod 2)) ⟨γ, mem_statedSL_zmod γ⟩ x :=
  rfl

theorem exists_mulEquiv_vec [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 2 ^ n) :
    Nonempty (V ≃* Multiplicative (Fin n → ZMod 2)) := by
  classical
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero, ← sq]
    exact hV2 _
  have : Fintype (Additive V) := Fintype.ofFinite _
  have hfin : Module.finrank (ZMod 2) (Additive V) = n := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at h1
    have h2 : Nat.card (Additive V) = 2 ^ n := hcard
    rw [h2] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have : Module.Finite (ZMod 2) (Additive V) := Module.Finite.of_finite
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hfin
  let L : Additive V ≃+ (Fin n → ZMod 2) := b.equivFun.toAddEquiv
  exact ⟨{ toFun := fun v => Multiplicative.ofAdd (L (Additive.ofMul v))
           invFun := fun x => Additive.toMul (L.symm (Multiplicative.toAdd x))
           left_inv := fun v => by simp
           right_inv := fun x => by simp
           map_mul' := fun v w => by simp }⟩

theorem exists_gl_of_mulAut (A : MulAut (Multiplicative (Fin n → ZMod 2))) :
    ∃ γ : GL (Fin n) (ZMod 2), natAut γ = A := by
  let A' : (Fin n → ZMod 2) ≃+ (Fin n → ZMod 2) := MulEquiv.toAdditive A
  have hA : ∀ (c : ZMod 2) (x : Fin n → ZMod 2), A' (c • x) = c • A' x := by
    intro c x
    rcases CFSG.GroupTheory.GLnTwoSplitting.zmod_two_eq_zero_or_one c with rfl | rfl
    · simp
    · simp
  refine ⟨(glLin n).symm (A'.toLinearEquiv hA), MulEquiv.ext fun x => ?_⟩
  show Multiplicative.ofAdd (glLin n ((glLin n).symm (A'.toLinearEquiv hA))
    (Multiplicative.toAdd x)) = A x
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem realizesVia_top_of_card [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    (hcard : Nat.card V = 2 ^ n) :
    ∃ π : ↥(StatedSL n (ZMod 2)) →* ↥(⊤ : Subgroup (MulAut V)),
      (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia ⊤ ⊤ ⊥ π := by
  obtain ⟨E⟩ := exists_mulEquiv_vec hV2 hcard
  let ρ : ↥(StatedSL n (ZMod 2)) →* MulAut V :=
    { toFun := fun γ => (E.trans (natAut (γ : GL (Fin n) (ZMod 2)))).trans E.symm
      map_one' := by
        ext v
        show E.symm (natAut 1 (E v)) = v
        rw [natAut_apply]
        rw [show (⟨1, mem_statedSL_zmod 1⟩ : ↥(StatedSL n (ZMod 2))) = 1 from rfl, natAct_one,
          MulEquiv.symm_apply_apply]
      map_mul' := fun γ δ => by
        ext v
        show E.symm (natAut ((γ : GL (Fin n) (ZMod 2)) * (δ : GL (Fin n) (ZMod 2))) (E v)) =
          E.symm (natAut (γ : GL (Fin n) (ZMod 2)) (E (E.symm (natAut
            (δ : GL (Fin n) (ZMod 2)) (E v)))))
        rw [MulEquiv.apply_symm_apply, natAut_apply, natAut_apply, natAut_apply]
        rw [show (⟨(γ : GL (Fin n) (ZMod 2)) * (δ : GL (Fin n) (ZMod 2)), mem_statedSL_zmod _⟩ :
          ↥(StatedSL n (ZMod 2))) = γ * δ from rfl, natAct_mul_act] }
  let π : ↥(StatedSL n (ZMod 2)) →* ↥(⊤ : Subgroup (MulAut V)) :=
    ρ.codRestrict ⊤ fun _ => trivial
  refine ⟨π, realizesVia_nat_of ?_ le_top (fun _ _ _ => trivial) ?_
    (E.toMonoidHom.comp (⊤ : Subgroup V).subtype) ?_ ?_ ?_⟩
  · rintro ⟨ψ, -⟩
    obtain ⟨γ, hγ⟩ := exists_gl_of_mulAut ((E.symm.trans ψ).trans E)
    refine ⟨⟨γ, mem_statedSL_zmod γ⟩, Subtype.ext ?_⟩
    ext v
    show E.symm (natAut γ (E v)) = ψ v
    rw [hγ]
    simp
  · intro h z hz
    rw [Subgroup.mem_bot] at hz ⊢
    rw [hz, map_one]
  · intro y
    exact ⟨⟨E.symm y, trivial⟩, by simp⟩
  · intro u
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, Subgroup.mem_bot]
  · intro γ u hu
    show E (E.symm (natAut (γ : GL (Fin n) (ZMod 2)) (E u))) = _
    rw [MulEquiv.apply_symm_apply, natAut_apply]
    rfl

theorem exists_eq_on_of_natSL [Finite V] {H : Subgroup (MulAut V)} {W : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H}
    (h : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H W ⊥ π) {ψ : MulAut V}
    (hψ : ∀ w ∈ W, ψ w ∈ W) : ∃ x ∈ H, ∀ w ∈ W, x w = ψ w := by
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap h
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hfk u).1 hu))
  let F : ↥W ≃* Multiplicative (Fin n → ZMod 2) := MulEquiv.ofBijective f ⟨hfi, hfs⟩
  let ψW : ↥W →* ↥W := (ψ.toMonoidHom.comp W.subtype).codRestrict W fun w => hψ w w.2
  have hψWi : Function.Injective ψW := by
    intro x y hxy
    have := congrArg Subtype.val hxy
    exact Subtype.ext (ψ.injective this)
  have hψWs : Function.Surjective ψW := Finite.injective_iff_surjective.1 hψWi
  let ψE : ↥W ≃* ↥W := MulEquiv.ofBijective ψW ⟨hψWi, hψWs⟩
  obtain ⟨γ, hγ⟩ := exists_gl_of_mulAut ((F.symm.trans ψE).trans F)
  refine ⟨((π ⟨γ, mem_statedSL_zmod γ⟩ : ↥H) : MulAut V), (π _).2, fun w hw => ?_⟩
  have hu : ((π ⟨γ, mem_statedSL_zmod γ⟩ : ↥H) : MulAut V) w ∈ W := h.2.2.2.1 _ w hw
  have h1 := hfe ⟨γ, mem_statedSL_zmod γ⟩ ⟨w, hw⟩ hu
  have h2 : f ⟨ψ w, hψ w hw⟩ =
      natAct (StatedSL n (ZMod 2)) ⟨γ, mem_statedSL_zmod γ⟩ (f ⟨w, hw⟩) := by
    rw [← natAut_apply, hγ]
    show f ⟨ψ w, hψ w hw⟩ = F (ψE (F.symm (F ⟨w, hw⟩)))
    rw [MulEquiv.symm_apply_apply]
    rfl
  have := hfi (h1.trans h2.symm)
  exact congrArg Subtype.val this

end CFSG.Quasithin.G64
