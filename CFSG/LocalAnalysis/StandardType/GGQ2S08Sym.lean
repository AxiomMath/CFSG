module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2s08t2a_comm_formula {R V : Type} [CommRing R] [AddCommGroup V] [Module R V]
    (S T : V ≃ₗ[R] V) {x : V} {f : Module.Dual R V} (hfx : f x = 2)
    (hS : ∀ v, S v = v - f v • x) (hTx : T x = x) (v : V) :
    (S * T * S * T.symm) v = v + (f (T.symm v) - f v) • x := by
  have h1 : S (T.symm v) = T.symm v - f (T.symm v) • x := hS _
  have h2 : T (T.symm v - f (T.symm v) • x) = v - f (T.symm v) • x := by
    rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, hTx]
  have h3 : S (v - f (T.symm v) • x) =
      (v - f (T.symm v) • x) - f (v - f (T.symm v) • x) • x := hS _
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h1, h2, h3,
    map_sub, map_smul, hfx]
  module

private theorem ggQ2s08t2a_fix_coroot {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) (hp2 : p ≠ 2)
    {φ ν : MulAut ↥Bs} {x : V} {f : Module.Dual (ZMod p) V} (hfx : f x = 2)
    (hφx : ∀ v, (ggLin (p := p) ι) φ v = v - f v • x)
    (hν : ∀ b : ↥Bs, ν (b⁻¹ * φ b) = b⁻¹ * φ b) :
    (ggLin (p := p) ι) ν x = x := by
  have hf0 : f ≠ 0 := (ne_zero_of_apply_eq_two hp2 hfx).2
  obtain ⟨v₀, hv₀⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf0 (LinearMap.ext hcon)
  let b₀ : ↥Bs := Additive.toMul (ι.symm v₀)
  have hb₀ : ι (Additive.ofMul b₀) = v₀ := by simp [b₀]
  have hδ₀ : f v₀ • x = -ι (Additive.ofMul (b₀⁻¹ * φ b₀)) := by
    rw [ofMul_mul, map_add, ofMul_inv, map_neg, ← ggLin_apply_ofMul (p := p) ι φ b₀,
      hb₀, hφx v₀]
    abel
  have hTδ : (ggLin (p := p) ι) ν (ι (Additive.ofMul (b₀⁻¹ * φ b₀))) =
      ι (Additive.ofMul (b₀⁻¹ * φ b₀)) := by
    rw [ggLin_apply_ofMul (p := p), hν b₀]
  have h1 : (ggLin (p := p) ι) ν (f v₀ • x) = f v₀ • x := by
    rw [hδ₀, map_neg, hTδ]
  rw [map_smul] at h1
  have h3 : f v₀ • ((ggLin (p := p) ι) ν x - x) = 0 := by
    rw [smul_sub, h1, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h3).resolve_left hv₀)

theorem ggQ2s08_sym {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p = 3) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {g n : G} {φ ν : MulAut ↥Bs}
    (hg : GGQ2Ind Bs g φ) (hn : GGQ2Ind Bs n ν) (hR : GGIsReflection p φ)
    (hν : ∀ b : ↥Bs, ν (b⁻¹ * φ b) = b⁻¹ * φ b) (b : ↥Bs) :
    φ (b⁻¹ * ν b) = b⁻¹ * ν b := by
  haveI : Fact p.Prime := ⟨by rw [hp]; norm_num⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨V, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  letI : Finite V := Finite.of_equiv _ (Additive.ofMul.trans ι.toEquiv)
  obtain ⟨x, f, hfx, hφx⟩ := exists_of_ggIsReflection (p := p) ι hR
  obtain ⟨hx0, hf0⟩ := ne_zero_of_apply_eq_two hp2 hfx
  have hTx : (ggLin (p := p) ι) ν x = x := ggQ2s08t2a_fix_coroot ι hp2 hfx hφx hν
  have hφind : φ ∈ ggInduced ⊤ Bs := ⟨g, Subgroup.mem_top g, hg.1, hg.2⟩
  have hνind : ν ∈ ggInduced ⊤ Bs := ⟨n, Subgroup.mem_top n, hn.1, hn.2⟩
  let κ : MulAut ↥Bs := φ * ν * φ * ν⁻¹
  have hκ : κ ∈ ggInduced ⊤ Bs := by
    show φ * ν * φ * ν⁻¹ ∈ ggInduced ⊤ Bs
    exact mul_mem_ggInduced (mul_mem_ggInduced (mul_mem_ggInduced hφind hνind) hφind)
      (inv_mem_ggInduced hνind)
  let f'' : Module.Dual (ZMod p) V :=
    f.comp ((((ggLin (p := p) ι) ν).symm : V →ₗ[ZMod p] V) - LinearMap.id)
  have hfi_eq : ∀ u, f'' u = f (((ggLin (p := p) ι) ν).symm u) - f u := by
    intro u
    simp only [f'', LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_coe]
    rw [map_sub]
    rfl
  have hf''zero : ∀ u, f (((ggLin (p := p) ι) ν).symm u) - f u = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u₀, hu₀⟩ := hcon
    have hTix : ((ggLin (p := p) ι) ν).symm x = x := by
      have h := congrArg ((ggLin (p := p) ι) ν).symm hTx
      rw [LinearEquiv.symm_apply_apply] at h
      exact h.symm
    have hf''x : f'' x = 0 := by
      rw [hfi_eq x, hTix, sub_self]
    have hf''ne : f'' ≠ 0 := by
      intro h0
      have h : f'' u₀ = 0 := by simpa using congrArg (fun g => g u₀) h0
      rw [hfi_eq u₀] at h
      exact hu₀ h
    have hform : ∀ v, (ggLin (p := p) ι) κ v = v + f'' v • x := by
      intro v
      have hκlin : (ggLin (p := p) ι) κ =
          (ggLin (p := p) ι) φ * (ggLin (p := p) ι) ν * (ggLin (p := p) ι) φ *
            ((ggLin (p := p) ι) ν).symm := by
        show (ggLin (p := p) ι) (φ * ν * φ * ν⁻¹) = _
        simp only [map_mul, map_inv]
        rfl
      rw [hκlin, ggQ2s08t2a_comm_formula ((ggLin (p := p) ι) φ) ((ggLin (p := p) ι) ν)
        hfx hφx hTx v, hfi_eq v]
    exact hNT κ hκ (ggIsTransvection_of_apply ι hx0 hf''ne hf''x hform)
  refine (ggLin_fix_iff (p := p) ι φ (b⁻¹ * ν b)).mpr ?_
  have hv : ι (Additive.ofMul (b⁻¹ * ν b)) = (ggLin (p := p) ι) ν (ι (Additive.ofMul b)) -
      ι (Additive.ofMul b) := by
    rw [ofMul_mul, map_add, ofMul_inv, map_neg, ← ggLin_apply_ofMul (p := p) ι ν b]
    abel
  have hfv : f (ι (Additive.ofMul (b⁻¹ * ν b))) = 0 := by
    rw [hv, map_sub]
    have h1 := hf''zero ((ggLin (p := p) ι) ν (ι (Additive.ofMul b)))
    rw [LinearEquiv.symm_apply_apply, sub_eq_zero] at h1
    exact sub_eq_zero.mpr h1.symm
  have hφv := hφx (ι (Additive.ofMul (b⁻¹ * ν b)))
  rw [hφv, sub_eq_self, smul_eq_zero]
  exact Or.inl hfv

end CFSG.StandardType

end
