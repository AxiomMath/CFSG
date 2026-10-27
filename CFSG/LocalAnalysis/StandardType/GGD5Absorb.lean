module

public import CFSG.LocalAnalysis.StandardType.GGD5AbsCoord
public import CFSG.LocalAnalysis.StandardType.GGD5AbsTwist

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

section Theta

variable {G : Type} [Group G] {Bs : Subgroup G} {x y : G} {L H : Subgroup G}

private noncomputable def lup10c_theta (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) : MulAut ↥Bs →* Matrix (Fin 5) (Fin 5) (ZMod 3) where
  toFun ψ := LinearMap.toMatrix'
    (κ.toLinearMap ∘ₗ (ggLin (p := 3) M.model ψ).toLinearMap ∘ₗ κ.symm.toLinearMap)
  map_one' := by
    have h : (κ.toLinearMap ∘ₗ (ggLin (p := 3) M.model (1 : MulAut ↥Bs)).toLinearMap ∘ₗ
        κ.symm.toLinearMap) = LinearMap.id := by
      refine LinearMap.ext fun v => ?_
      simp
    rw [h]
    exact LinearMap.toMatrix'_id
  map_mul' ψ φ := by
    have h : (κ.toLinearMap ∘ₗ (ggLin (p := 3) M.model (ψ * φ)).toLinearMap ∘ₗ
        κ.symm.toLinearMap) =
        (κ.toLinearMap ∘ₗ (ggLin (p := 3) M.model ψ).toLinearMap ∘ₗ κ.symm.toLinearMap) ∘ₗ
        (κ.toLinearMap ∘ₗ (ggLin (p := 3) M.model φ).toLinearMap ∘ₗ κ.symm.toLinearMap) := by
      refine LinearMap.ext fun v => ?_
      simp [map_mul, LinearEquiv.mul_apply]
    rw [h, LinearMap.toMatrix'_comp]

private theorem lup10c_theta_mulVec (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) (ψ : MulAut ↥Bs) (v : M.V) :
    (lup10c_theta M κ ψ).mulVec (κ v) = κ (ggLin (p := 3) M.model ψ v) := by
  show (LinearMap.toMatrix' _).mulVec _ = _
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  simp

private theorem lup10c_theta_eq (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) (ψ : MulAut ↥Bs) (A : Matrix (Fin 5) (Fin 5) (ZMod 3))
    (h : ∀ v : M.V, κ (ggLin (p := 3) M.model ψ v) = A.mulVec (κ v)) :
    lup10c_theta M κ ψ = A := by
  refine Matrix.toLin'.injective (LinearMap.ext fun u => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  obtain ⟨v, rfl⟩ := κ.surjective u
  rw [lup10c_theta_mulVec, h]

private theorem lup10c_theta_inv (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) (ψ : MulAut ↥Bs) :
    lup10c_theta M κ ψ⁻¹ = (lup10c_theta M κ ψ)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem lup10c_finish (M : GGQTwoAmbModel 3 Bs x y L H)
    (κ : M.V ≃ₗ[ZMod 3] (Fin 5 → ZMod 3)) {Ψ : MulAut ↥Bs} (D : Subgroup G)
    (hΨ : lup10c_theta M κ Ψ = 1 ∨ lup10c_theta M κ Ψ + 1 = 0) :
    ∀ b : ↥Bs, (b : G) ∈ D → ((Ψ b : ↥Bs) : G) ∈ D := by
  intro b hb
  have hmv := lup10c_theta_mulVec M κ Ψ
  rcases hΨ with h | h
  · have hid : ∀ v, ggLin (p := 3) M.model Ψ v = v := by
      intro v
      apply κ.injective
      rw [← hmv, h, Matrix.one_mulVec]
    have h1 := ggLin_apply_ofMul (p := 3) M.model Ψ b
    rw [hid] at h1
    have h2 : Ψ b = b := Additive.ofMul.injective (M.model.injective h1.symm)
    rw [h2]
    exact hb
  · have hneg : ∀ v, ggLin (p := 3) M.model Ψ v = -v := by
      intro v
      apply κ.injective
      have h' := congrArg (fun A : Matrix (Fin 5) (Fin 5) (ZMod 3) => A.mulVec (κ v)) h
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec] at h'
      rw [← hmv, map_neg]
      exact eq_neg_of_add_eq_zero_left h'
    have h1 := ggLin_apply_ofMul (p := 3) M.model Ψ b
    rw [hneg] at h1
    have h2 : Ψ b = b⁻¹ := by
      apply Additive.ofMul.injective
      apply M.model.injective
      rw [← h1, ofMul_inv, map_neg]
    rw [h2]
    simpa using Subgroup.inv_mem D hb

end Theta

theorem lup10d_absorb {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3) (hI1 : GGQTwoI1 Bs D J) (hxL : x ∉ L)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoAmbModel p Bs x y L (L ⊔ K)) (e : Fin 5 ≃ M.ι)
    (hecart : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D 5 i j) (he0 : M.a = e 0)
    (hV : Submodule.span (ZMod p)
      (insert M.xV (Set.range fun i : {k // k ≠ M.a} => M.coroot i)) = ⊤)
    (hbas : M.toLin.Basis) (hTF : lup10fa_TwistFacts)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφx : ggLin (p := p) M.model φ M.xV ∈ Submodule.span (ZMod p) {M.xV})
    (π : {k // k ≠ M.a} ≃ {k // k ≠ M.a}) (μ : {k // k ≠ M.a} → ZMod p) (c : ZMod p)
    (w : M.V ≃ₗ[ZMod p] M.V) (hSc : M.toLin.ScaledAut M.a π μ)
    (hw : w ∈ M.toLin.parab {k | k ≠ M.a})
    (hT : ∀ i : {k // k ≠ M.a},
      ggLin (p := p) M.model φ (M.coroot i) = c • μ i • w (M.coroot (π i)))
    (hπb : π ⟨M.b, M.a_ne_b.symm⟩ ≠ ⟨M.b, M.a_ne_b.symm⟩)
    (hπ1 : ∀ i : {k // k ≠ M.a}, (i : M.ι) = e 1 → ((π i : {k // k ≠ M.a}) : M.ι) ≠ e 1)
    (r' : MulAut ↥Bs) (hr' : r' ∈ ggAutomizer (ggG0 p B x L D J) Bs)
    (hlin : ggLin (p := p) M.model r' = ggLin (p := p) M.model (φ * M.simple M.a * φ⁻¹)) :
    ∃ ψ ∈ ggAutomizer (ggG0 p B x L D J) Bs,
      ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D := by
  subst hp
  have hx1 : x ≠ 1 := fun h => hxL (h ▸ L.one_mem)
  obtain ⟨κ, hκ1, hκs, hκx⟩ := lup10ab_coord M e hecart he0 hbas
  obtain ⟨w', hw'L, b0, γ, lam, c', hadm, -, hform⟩ :=
    lup10ab_twist_form M e hecart he0 hV hbas hx1 κ hκ1 (hκx hx1) hφx π μ c w hSc hw hT hπb hπ1
  have hcase := hTF b0 γ lam c' hadm
  obtain ⟨hclos0, -⟩ := hcase
  have hLG : L ≤ ggG0 3 B x L D J := le_ggG0_left 3 B x L D J
  have hKG : K ≤ ggG0 3 B x L D J := le_ggG0_of_ggNbr hnb
  have hw'A : w' ∈ ggAutomizer (ggG0 3 B x L D J) Bs := ggAutomizer_mono Bs hLG hw'L
  have hta : lup10ab_tau 4 = 0 := by decide
  have ha : M.a = e (lup10ab_tau 4) := by rw [he0, hta]
  have hsimple : ∀ i : Fin 5, M.simple (e (lup10ab_tau i)) ∈ ggAutomizer (ggG0 3 B x L D J) Bs := by
    intro i
    by_cases hi : i = 4
    · subst hi
      rw [← ha]
      exact ggAutomizer_mono Bs (sup_le hLG hKG) M.simple_a_mem
    · have hne : e (lup10ab_tau i) ≠ M.a := by
        rw [he0]
        intro h
        apply hi
        have h0 : lup10ab_tau i = 0 := e.injective h
        revert h0
        fin_cases i <;> simp [lup10ab_tau]
      have hmem : M.simple (e (lup10ab_tau i)) ∈ ggAutomizer L Bs := by
        rw [M.automizer_L]
        exact Subgroup.subset_closure ⟨_, hne, rfl⟩
      exact ggAutomizer_mono Bs hLG hmem
  set θ := lup10c_theta M κ with hθ
  have hθS : ∀ i : Fin 5, θ (M.simple (e (lup10ab_tau i))) = lup10fa_s i := fun i =>
    lup10c_theta_eq M κ _ _ (hκs i)
  have hθs4 : θ (M.simple M.a) = lup10fa_s 4 := by
    rw [ha]
    exact hθS 4
  set g := lup10fa_twist γ lam c' with hg
  set ψ1 : MulAut ↥Bs := w'⁻¹ * φ with hψ1
  have hθψ1 : θ ψ1 = g := lup10c_theta_eq M κ _ _ hform
  have hθψ1inv : θ ψ1⁻¹ = g⁻¹ := by rw [lup10c_theta_inv, hθψ1]
  have hr'eq : r' = φ * M.simple M.a * φ⁻¹ := ggLin_injective (p := 3) M.model hlin
  have hr''A : ψ1 * M.simple M.a * ψ1⁻¹ ∈ ggAutomizer (ggG0 3 B x L D J) Bs := by
    have h1 : ψ1 * M.simple M.a * ψ1⁻¹ = w'⁻¹ * r' * w' := by
      rw [hr'eq, hψ1]
      group
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hw'A) hr') hw'A
  have hθr'' : θ (ψ1 * M.simple M.a * ψ1⁻¹) = g * lup10fa_s 4 * g⁻¹ := by
    rw [map_mul, map_mul, hθψ1, hθs4, hθψ1inv]
  have hclos : ∀ m ∈ Submonoid.closure (lup10fa_gens γ lam c'),
      ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs, θ ψ = m := by
    intro m hm
    refine Submonoid.closure_induction (motive := fun m _ => ∃ ψ ∈ ggAutomizer (ggG0 3 B x L D J) Bs,
      θ ψ = m) ?_ ?_ ?_ hm
    · intro m hm
      rcases hm with ⟨i, rfl⟩ | hm
      · exact ⟨M.simple (e (lup10ab_tau i)), hsimple i, hθS i⟩
      · rw [Set.mem_singleton_iff] at hm
        subst hm
        exact ⟨ψ1 * M.simple M.a * ψ1⁻¹, hr''A, hθr''⟩
    · exact ⟨1, Subgroup.one_mem _, map_one θ⟩
    · rintro m n - - ⟨a, ha', rfl⟩ ⟨b, hb', rfl⟩
      exact ⟨a * b, Subgroup.mul_mem _ ha' hb', map_mul θ a b⟩
  rcases hclos0 with hgm | hgm
  · obtain ⟨ψ0, hψ0A, hψ0θ⟩ := hclos _ hgm
    refine ⟨ψ0⁻¹ * w'⁻¹, Subgroup.mul_mem _ (Subgroup.inv_mem _ hψ0A) (Subgroup.inv_mem _ hw'A), ?_⟩
    have hsc : θ (ψ0⁻¹ * w'⁻¹ * φ) = 1 := by
      have h1 : ψ0⁻¹ * w'⁻¹ * φ = ψ0⁻¹ * ψ1 := by rw [hψ1, mul_assoc]
      rw [h1, map_mul, hθψ1, ← hψ0θ, ← map_mul, inv_mul_cancel, map_one]
    exact lup10c_finish M κ D (Or.inl hsc)
  · obtain ⟨ψ0, hψ0A, hψ0θ⟩ := hclos _ hgm
    refine ⟨ψ0⁻¹ * w'⁻¹, Subgroup.mul_mem _ (Subgroup.inv_mem _ hψ0A) (Subgroup.inv_mem _ hw'A), ?_⟩
    have hsc : θ (ψ0⁻¹ * w'⁻¹ * φ) + 1 = 0 := by
      have h1 : ψ0⁻¹ * w'⁻¹ * φ = ψ0⁻¹ * ψ1 := by rw [hψ1, mul_assoc]
      have h2 : θ ψ0⁻¹ * θ ψ0 = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rw [hψ0θ, Matrix.mul_neg] at h2
      have h3 : θ ψ0⁻¹ * g = -1 := neg_eq_iff_eq_neg.mp h2
      rw [h1, map_mul, hθψ1, h3]
      exact neg_add_cancel 1
    exact lup10c_finish M κ D (Or.inr hsc)

end CFSG.StandardType

end
