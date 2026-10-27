module

public import CFSG.CGT.Harada80.Dual
public import CFSG.Quasithin.H13.VolII16SLNat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.RankThree.PartTwo
open scoped Matrix

theorem s16c11_v1_cover_of_data {m : ℕ} (h1 : CFSG.CGT.Harada80.H1Natural m)
    {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
    (hW2 : ∀ w : W, w ^ 2 = 1)
    {ρ : ↥(omegaMinusTwo m) →* MulAut W}
    {β : W →* Multiplicative (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)}
    (hρH : ∀ g, ρ g ∈ H) (hρs : ∀ x ∈ H, ∃ g, ρ g = x)
    (hβs : Function.Surjective β) (hβk : ∀ w, β w = 1 ↔ w ∈ Z)
    (hβe : ∀ g w, Multiplicative.toAdd (β (ρ g w)) =
      ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (β w))
    (hZ : Z ≤ fixV H) (hcomm : commV H = ⊤) : Z = ⊥ := by
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.Quasithin.H13.VolI.modTwoW hW2
  let βa : Additive W →+ (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) :=
    CFSG.Quasithin.H13.VolI.addMap β
  let ρa : ↥(omegaMinusTwo m) →* AddMonoid.End (Additive W) :=
    CFSG.Quasithin.H13.VolI.addAct ρ
  have hβa : ∀ u : Additive W, βa u =
      Multiplicative.toAdd (β (Additive.toMul u)) := by
    intro u
    conv_lhs => rw [← ofMul_toMul u]
    exact CFSG.Quasithin.H13.VolI.addMap_ofMul β (Additive.toMul u)
  have hρa : ∀ (g : ↥(omegaMinusTwo m)) (u : Additive W),
      βa (ρa g u) = ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ βa u := by
    intro g u
    conv_lhs => rw [← ofMul_toMul u]
    rw [show ρa g (Additive.ofMul (Additive.toMul u)) =
        CFSG.Quasithin.H13.VolI.addAct ρ g (Additive.ofMul (Additive.toMul u)) from rfl,
      CFSG.Quasithin.H13.VolI.addAct_ofMul, CFSG.Quasithin.H13.VolI.addMap_ofMul,
      hβe g (Additive.toMul u), hβa u]
  have hβa_surj : Function.Surjective βa := by
    intro v
    obtain ⟨w, hw⟩ := hβs (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul w, by rw [hβa, toMul_ofMul, hw]; rfl⟩
  have hβa_ker : ∀ u : Additive W, βa u = 0 ↔ Additive.toMul u ∈ Z := by
    intro u
    rw [hβa u, toAdd_eq_zero]
    exact hβk (Additive.toMul u)
  have hgg : ∀ (g : ↥(omegaMinusTwo m)) (v : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2),
      ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ
        ((((g⁻¹ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ v) =
        v := by
    intro g v
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  by_contra hz1
  have hz0 : Additive.ofMul z ≠ 0 := fun hc => hz1 (Additive.ofMul.injective hc)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) hz0
  let φ : Additive W →+ ZMod 2 := f.toAddMonoidHom
  have hφz : φ (Additive.ofMul z) ≠ 0 := hf
  have hβaz : βa (Additive.ofMul z) = 0 := by
    rw [hβa, toMul_ofMul, (hβk z).2 hz]
    rfl
  let ψ : ↥(omegaMinusTwo m) → Additive W →+ ZMod 2 := fun g =>
    AddMonoidHom.mk' (fun u => φ (ρa g⁻¹ u) - φ u) (fun u v => by
      rw [map_add, map_add, map_add]
      abel)
  have hψ_ker : ∀ g, βa.ker ≤ (ψ g).ker := by
    intro g u hu
    rw [AddMonoidHom.mem_ker] at hu ⊢
    have hZu : Additive.toMul u ∈ Z := (hβa_ker u).1 hu
    have hfix : ρ (g⁻¹) (Additive.toMul u) = Additive.toMul u :=
      (mem_fixV.1 (hZ hZu)) (ρ (g⁻¹)) (hρH (g⁻¹))
    have hρu : ρa g⁻¹ u = u := by
      conv_lhs => rw [← ofMul_toMul u]
      rw [show ρa g⁻¹ (Additive.ofMul (Additive.toMul u)) =
          CFSG.Quasithin.H13.VolI.addAct ρ g⁻¹ (Additive.ofMul (Additive.toMul u)) from rfl,
        CFSG.Quasithin.H13.VolI.addAct_ofMul, hfix]
      rfl
    show φ (ρa g⁻¹ u) - φ u = 0
    rw [hρu, sub_self]
  let lam : ↥(omegaMinusTwo m) → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) →+ ZMod 2 := fun g =>
    βa.liftOfRightInverse (Function.surjInv hβa_surj) (Function.rightInverse_surjInv hβa_surj)
      ⟨ψ g, hψ_ker g⟩
  have hlam : ∀ g u, lam g (βa u) = ψ g u := by
    intro g u
    simp only [lam, AddMonoidHom.liftOfRightInverse_comp_apply]
  have hw : ∀ g, ∃ w : Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2,
      ∀ v, lam g v = QuadraticMap.polar (CFSG.CGT.Harada80.quadQ m) w v :=
    fun g => CFSG.CGT.Harada80.exists_polar_eq (lam g)
  choose w hw using hw
  have hψ_mul : ∀ g h u, ψ (g * h) u = ψ g u + ψ h (ρa g⁻¹ u) := by
    intro g h u
    show φ (ρa (g * h)⁻¹ u) - φ u =
      (φ (ρa g⁻¹ u) - φ u) + (φ (ρa h⁻¹ (ρa g⁻¹ u)) - φ (ρa g⁻¹ u))
    rw [mul_inv_rev]
    rw [show ρa (h⁻¹ * g⁻¹) u = ρa h⁻¹ (ρa g⁻¹ u) from by rw [map_mul]; rfl]
    abel
  have hw_coc : ∀ g h, w (g * h) = w g + ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
      Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ w h := by
    intro g h
    apply sub_eq_zero.mp
    apply CFSG.CGT.Harada80.eq_zero_of_polar_eq_zero
    intro v
    rw [QuadraticMap.polar_sub_left, sub_eq_zero]
    obtain ⟨u, rfl⟩ := hβa_surj v
    rw [← hw (g * h) (βa u), hlam (g * h) u, hψ_mul g h u, ← hlam g u,
      ← hlam h (ρa g⁻¹ u), hρa g⁻¹ u, hw g (βa u),
      hw h ((((g⁻¹ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ βa u)]
    have hp := CFSG.CGT.Harada80.polar_mulVec_of_mem (m := m)
      (g := (g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))) g.2 (w h)
      ((((g⁻¹ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ βa u)
    rw [hgg g (βa u)] at hp
    rw [← hp, ← QuadraticMap.polar_add_left]
  obtain ⟨a, ha⟩ := h1 w hw_coc
  have ha' : ∀ x : ↥(omegaMinusTwo m), w x =
      (((x : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a) - a :=
    fun x => ha x
  let M : Additive W →+ ZMod 2 := AddMonoidHom.mk'
    (fun u => φ u - QuadraticMap.polar (CFSG.CGT.Harada80.quadQ m) a (βa u)) (by
      intro u v
      rw [map_add, map_add, QuadraticMap.polar_add_right]
      abel)
  have hM : ∀ u, M u = φ u - QuadraticMap.polar (CFSG.CGT.Harada80.quadQ m) a (βa u) :=
    fun u => rfl
  have hMinv : ∀ g u, M (ρa g u) = M u := by
    intro g u
    have hφdiff : φ (ρa g u) - φ u =
        QuadraticMap.polar (CFSG.CGT.Harada80.quadQ m) (w (g⁻¹)) (βa u) := by
      have h2 : ψ (g⁻¹) u = φ (ρa g u) - φ u := by
        show (φ.comp (ρa (g⁻¹)⁻¹) - φ) u = φ (ρa g u) - φ u
        rw [inv_inv]
        rfl
      rw [← h2, ← hlam (g⁻¹) u, hw (g⁻¹) (βa u)]
    have hkey : QuadraticMap.polar (CFSG.CGT.Harada80.quadQ m)
        ((((g⁻¹ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a)
        (βa u) =
        QuadraticMap.polar (CFSG.CGT.Harada80.quadQ m) a
          (((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ βa u) := by
      have hp := CFSG.CGT.Harada80.polar_mulVec_of_mem (m := m)
        (g := (g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2))) g.2
        ((((g⁻¹ : ↥(omegaMinusTwo m)) : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
          Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a) (βa u)
      rw [hgg g a] at hp
      exact hp.symm
    have hφdiff' : φ (ρa g u) - φ u =
        QuadraticMap.polar (CFSG.CGT.Harada80.quadQ m) a
          (((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
            Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ βa u) -
        QuadraticMap.polar (CFSG.CGT.Harada80.quadQ m) a (βa u) := by
      rw [hφdiff, ha' g⁻¹, QuadraticMap.polar_sub_left, hkey]
    rw [hM, hM, hρa g u]
    linear_combination hφdiff'
  have hgen : ∀ w : W, w ∈ Subgroup.closure {x | ∃ g v, x = ρ g v * v⁻¹} :=
    CFSG.Quasithin.H13.VolI.mem_closure_of_commV hρH hρs hcomm
  have hMzero : M (Additive.ofMul z) = 0 :=
    CFSG.Quasithin.H13.VolI.invariant_form_eq_zero hgen hMinv z
  have hMeq : M (Additive.ofMul z) = φ (Additive.ofMul z) := by
    rw [hM, hβaz, QuadraticMap.polar_zero_right, sub_zero]
  exact hφz (by rw [← hMeq, hMzero])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
