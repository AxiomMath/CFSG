module

public import CFSG.Quasithin.Background.B4L3Fin
public import CFSG.Quasithin.Vol2.Ch4Sec3C136Norm
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI

open Matrix CFSG.Quasithin
open CFSG.Quasithin.H13.Ch4 (dact)

open Matrix.SpecialLinearGroup in
@[expose] def burnsideC135_y12 : L3.Γ := transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2)

open Matrix.SpecialLinearGroup in
@[expose] def burnsideC135_y23 : L3.Γ := transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 2)

open Matrix.SpecialLinearGroup in
@[expose] def burnsideC135_y31 : L3.Γ := transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : ZMod 2)

theorem burnsideC135_y12_invol : L3.IsInvol burnsideC135_y12 := by
  unfold L3.IsInvol burnsideC135_y12; decide +kernel

theorem burnsideC135_y23_invol : L3.IsInvol burnsideC135_y23 := by
  unfold L3.IsInvol burnsideC135_y23; decide +kernel

theorem burnsideC135_y31_invol : L3.IsInvol burnsideC135_y31 := by
  unfold L3.IsInvol burnsideC135_y31; decide +kernel

open Matrix.SpecialLinearGroup in
open scoped commutatorElement in
theorem burnsideC135_closure_gens :
    Subgroup.closure ({burnsideC135_y12, burnsideC135_y23, burnsideC135_y31} : Set L3.Γ) = ⊤ := by
  set H := Subgroup.closure ({burnsideC135_y12, burnsideC135_y23, burnsideC135_y31} : Set L3.Γ)
    with hH
  have h12 : burnsideC135_y12 ∈ H := Subgroup.subset_closure (by simp)
  have h23 : burnsideC135_y23 ∈ H := Subgroup.subset_closure (by simp)
  have h31 : burnsideC135_y31 ∈ H := Subgroup.subset_closure (by simp)
  have h02 : transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact L3.comm_mem h12 h23
  have h10 : transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (1 : Fin 3) ≠ 2 by decide)
      (show (2 : Fin 3) ≠ 0 by decide) (show (1 : Fin 3) ≠ 0 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact L3.comm_mem h23 h31
  have h21 : transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) ∈ H := by
    have := commutatorElement_transvection (show (2 : Fin 3) ≠ 0 by decide)
      (show (0 : Fin 3) ≠ 1 by decide) (show (2 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) (1 : ZMod 2)
    rw [mul_one] at this
    rw [← this]
    exact L3.comm_mem h31 h12
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j) (c : ZMod 2), transvection hij c ∈ H := by
    intro i j hij c
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [transvection_coeff_zero]; exact H.one_mem
    · fin_cases i <;> fin_cases j
      all_goals first | exact absurd rfl hij | assumption
  rw [eq_top_iff,
    ← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
      (ι := Fin 3) (K := ZMod 2)]
  rw [Subgroup.closure_le]
  rintro _ ⟨t, rfl⟩
  exact hall t.i t.j t.hij t.c

set_option maxRecDepth 100000 in
theorem burnsideC135_gens_cobound :
    ∀ v₁ v₂ v₃ : L3.Vec, ∃ w : L3.Vec,
      L3.act burnsideC135_y12 w - w = L3.act burnsideC135_y12 v₁ - v₁ ∧
      L3.act burnsideC135_y23 w - w = L3.act burnsideC135_y23 v₂ - v₂ ∧
      L3.act burnsideC135_y31 w - w = L3.act burnsideC135_y31 v₃ - v₃ := by
  unfold burnsideC135_y12 burnsideC135_y23 burnsideC135_y31
  decide +kernel

theorem burnsideC135_act_neg (g : L3.Γ) (v : L3.Vec) : L3.act g (-v) = -L3.act g v := by
  unfold L3.act
  exact Matrix.mulVec_neg _ _

theorem burnsideC135_coboundary_zmod {K : Type*} [Group K] {ρ : K →* L3.Γ}
    (hρ : Function.Surjective ρ) {f : K → L3.Vec}
    (hf : ∀ g h, f (g * h) = f g + L3.act (ρ g) (f h))
    (hker : ∀ a, ρ a = 1 → f a = 0) {t : K} (ht : L3.IsInvol (ρ t)) (hft : f t = 0) :
    ∃ m : L3.Vec, ∀ g, f g = L3.act (ρ g) m - m := by
  classical
  have hf1 : f 1 = 0 := hker 1 (map_one ρ)
  have hlift : ∀ g g', ρ g = ρ g' → f g = f g' := by
    intro g g' h
    have ha : ρ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    have e1 := hf g (g⁻¹ * g')
    rw [mul_inv_cancel_left, hker _ ha, L3.act_zero, add_zero] at e1
    exact e1.symm
  have hfinv : ∀ g, f g⁻¹ = -L3.act (ρ g⁻¹) (f g) := by
    intro g
    have e1 := hf g⁻¹ g
    rw [inv_mul_cancel, hf1] at e1
    exact eq_neg_of_add_eq_zero_left e1.symm
  have hinvol : ∀ g, L3.IsInvol (ρ g) → ∃ v, L3.act (ρ g) v - v = f g := by
    intro g hg
    obtain ⟨x, hx⟩ := L3.conj_invol ht hg
    obtain ⟨k, hk⟩ := hρ x
    have hg' : ρ (k * t * k⁻¹) = ρ g := by rw [map_mul, map_mul, map_inv, hk, hx]
    rw [← hlift _ _ hg']
    refine ⟨-f k, ?_⟩
    have e1 : f (k * t * k⁻¹) = f k + L3.act (ρ k) (f (t * k⁻¹)) := by
      rw [mul_assoc, hf]
    have e2 : f (t * k⁻¹) = L3.act (ρ t) (f k⁻¹) := by rw [hf, hft, zero_add]
    have h4 : L3.act (ρ k) (L3.act (ρ t) (L3.act (ρ k⁻¹) (f k))) = L3.act (ρ g) (f k) := by
      have h5 : ρ g = ρ k * (ρ t * ρ k⁻¹) := by rw [← hg', map_mul, map_mul, mul_assoc]
      rw [h5, L3.act_mul, L3.act_mul]
    have e3 : f (k * t * k⁻¹) = f k - L3.act (ρ g) (f k) := by
      rw [e1, e2, hfinv, burnsideC135_act_neg, burnsideC135_act_neg, h4]
      abel
    rw [e3, burnsideC135_act_neg]
    abel
  obtain ⟨k₁, hk₁⟩ := hρ burnsideC135_y12
  obtain ⟨k₂, hk₂⟩ := hρ burnsideC135_y23
  obtain ⟨k₃, hk₃⟩ := hρ burnsideC135_y31
  obtain ⟨v₁, hv₁⟩ := hinvol k₁ (hk₁ ▸ burnsideC135_y12_invol)
  obtain ⟨v₂, hv₂⟩ := hinvol k₂ (hk₂ ▸ burnsideC135_y23_invol)
  obtain ⟨v₃, hv₃⟩ := hinvol k₃ (hk₃ ▸ burnsideC135_y31_invol)
  rw [hk₁] at hv₁
  rw [hk₂] at hv₂
  rw [hk₃] at hv₃
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := burnsideC135_gens_cobound v₁ v₂ v₃
  rw [hv₁] at hw₁
  rw [hv₂] at hw₂
  rw [hv₃] at hw₃
  refine ⟨w, fun g => ?_⟩
  let P : L3.Γ → Prop := fun γ => ∀ g, ρ g = γ → f g = L3.act γ w - w
  have hgen : ∀ γ ∈ ({burnsideC135_y12, burnsideC135_y23, burnsideC135_y31} : Set L3.Γ),
      P γ := by
    intro γ hγ g hg
    rcases hγ with rfl | rfl | rfl
    · rw [hlift g k₁ (hg.trans hk₁.symm), hw₁]
    · rw [hlift g k₂ (hg.trans hk₂.symm), hw₂]
    · rw [hlift g k₃ (hg.trans hk₃.symm), hw₃]
  have hall : ∀ γ ∈ Subgroup.closure
      ({burnsideC135_y12, burnsideC135_y23, burnsideC135_y31} : Set L3.Γ), P γ := by
    intro γ hγ
    induction hγ using Subgroup.closure_induction with
    | mem x hx => exact hgen x hx
    | one =>
      intro g hg
      rw [hker g hg, L3.act_one, sub_self]
    | mul x y _ _ hx hy =>
      intro g hg
      obtain ⟨a, ha⟩ := hρ x
      have hb : ρ (a⁻¹ * g) = y := by rw [map_mul, map_inv, ha, hg, inv_mul_cancel_left]
      have e : g = a * (a⁻¹ * g) := by group
      rw [e, hf, hx a ha, hy _ hb, ha, L3.act_sub, L3.act_mul]
      abel
    | inv x _ hx =>
      intro g hg
      have hg' : ρ g⁻¹ = x := by rw [map_inv, hg, inv_inv]
      have e : g = (g⁻¹)⁻¹ := by group
      rw [e, hfinv, hx _ hg', map_inv, hg', L3.act_sub, ← L3.act_mul, inv_mul_cancel, L3.act_one]
      abel
  exact hall (ρ g) (by rw [burnsideC135_closure_gens]; exact Subgroup.mem_top _) g rfl

theorem burnsideC135_exists_coboundary_two {K : Type*} [Group K] {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2) {k : ℕ} {ρ : K →* Matrix.SpecialLinearGroup (Fin 3) F}
    (hρ : Function.Surjective ρ) {f : K → Fin k → Fin 3 → F}
    (hf : ∀ g h, f (g * h) = f g + dact (ρ g : Matrix (Fin 3) (Fin 3) F) (f h))
    (hker : ∀ a, ρ a = 1 → f a = 0) {t : K} (ht1 : ρ t ≠ 1) (ht2 : ρ t * ρ t = 1)
    (hft : f t = 0) :
    ∃ m : Fin k → Fin 3 → F, ∀ g, f g = dact (ρ g : Matrix (Fin 3) (Fin 3) F) m - m := by
  classical
  set e : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hF with he
  set ψ : F →+* ZMod 2 := e.symm.toRingHom with hψ
  set ρ' : K →* L3.Γ := (Matrix.SpecialLinearGroup.map ψ).comp ρ with hρ'
  have hψinj : Function.Injective ψ := e.symm.injective
  have hcoe : ∀ g, ((ρ' g : L3.Γ) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (ρ g : Matrix (Fin 3) (Fin 3) F).map ψ := fun g => rfl
  have hmapinj : ∀ γ δ : Matrix.SpecialLinearGroup (Fin 3) F,
      Matrix.SpecialLinearGroup.map ψ γ = Matrix.SpecialLinearGroup.map ψ δ → γ = δ := by
    intro γ δ h
    apply Subtype.ext
    funext i j
    have := congrArg (fun A : L3.Γ => (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j) h
    exact hψinj this
  have hρ'surj : Function.Surjective ρ' := by
    intro γ'
    let γ : Matrix.SpecialLinearGroup (Fin 3) F := Matrix.SpecialLinearGroup.map e.toRingHom γ'
    obtain ⟨g, hg⟩ := hρ γ
    refine ⟨g, Subtype.ext ?_⟩
    rw [hcoe, hg]
    funext i j
    show ψ (e (γ' i j)) = γ' i j
    exact e.symm_apply_apply _
  have hρ'1 : ∀ a, ρ' a = 1 → ρ a = 1 := by
    intro a ha
    apply hmapinj
    rw [map_one]
    exact ha
  have hinv : L3.IsInvol (ρ' t) := by
    refine ⟨?_, fun h => ht1 (hρ'1 t h)⟩
    show (Matrix.SpecialLinearGroup.map ψ) (ρ t) * (Matrix.SpecialLinearGroup.map ψ) (ρ t) = 1
    rw [← map_mul, ht2, map_one]
  have hmv : ∀ (g : K) (v : Fin 3 → F) (l : Fin 3),
      ψ (((ρ g : Matrix (Fin 3) (Fin 3) F).mulVec v) l) = L3.act (ρ' g) (fun l' => ψ (v l')) l := by
    intro g v l
    rw [RingHom.map_mulVec]
    unfold L3.act
    rw [hcoe]
    rfl
  have key : ∀ i : Fin k, ∃ m : L3.Vec, ∀ g, (fun l => ψ (f g i l)) = L3.act (ρ' g) m - m := by
    intro i
    refine burnsideC135_coboundary_zmod hρ'surj (f := fun g l => ψ (f g i l)) ?_ ?_ hinv ?_
    · intro g h
      funext l
      have e : f (g * h) i l = f g i l + ((ρ g : Matrix (Fin 3) (Fin 3) F).mulVec (f h i)) l := by
        rw [hf g h]
        rfl
      show ψ (f (g * h) i l) = ψ (f g i l) + L3.act (ρ' g) (fun l' => ψ (f h i l')) l
      rw [e, map_add, hmv]
    · intro a ha
      funext l
      rw [hker a (hρ'1 a ha)]
      simp
    · funext l
      rw [hft]
      simp
  choose m hm using key
  refine ⟨fun i l => e (m i l), fun g => ?_⟩
  funext i l
  apply hψinj
  have h1 := congrFun (hm i g) l
  have h2 : (fun l' => ψ (e (m i l'))) = m i := by
    funext l'
    exact e.symm_apply_apply _
  show ψ (f g i l) = ψ (((ρ g : Matrix (Fin 3) (Fin 3) F).mulVec (fun l' => e (m i l'))) l -
    e (m i l))
  have h3 : ψ (e (m i l)) = m i l := e.symm_apply_apply _
  rw [map_sub, hmv, h2, h3]
  exact h1

end CFSG.ASVolI

end
