module

public import CFSG.LocalAnalysis.StandardType.GGWAutCommon
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleSym

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem ggWAut_pm_of_conj_gen (R : Subgroup (V ≃ₗ[ZMod 3] V))
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r}) (habs : ZS.AbsIrred 3 R)
    {a w : V ≃ₗ[ZMod 3] V} (hw : w ∈ R)
    (h : ∀ r ∈ R, GGLinRefl r → a * r * a⁻¹ = w * r * w⁻¹) :
    (∀ v, a v = w v) ∨ (∀ v, a v = -(w v)) := by
  have hwR : w ∈ R := hw
  have hconj : ∀ x ∈ R, a * x * a⁻¹ = w * x * w⁻¹ := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {r | r ∈ R ∧ GGLinRefl r} := by
      rw [hgen] at hx
      exact hx
    refine Subgroup.closure_induction (p := fun x _ => a * x * a⁻¹ = w * x * w⁻¹)
      (fun t ht => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ih => ?_) hx'
    · exact h t ht.1 ht.2
    · group
    · rw [show a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) by group,
          show w * (x * y) * w⁻¹ = (w * x * w⁻¹) * (w * y * w⁻¹) by group, ihx, ihy]
    · rw [show a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ by group,
          show w * x⁻¹ * w⁻¹ = (w * x * w⁻¹)⁻¹ by group, ih]
  have hTcomm : ∀ x ∈ R, (w⁻¹ * a) * x = x * (w⁻¹ * a) := by
    intro x hx
    have h1 : a * x * a⁻¹ = w * x * w⁻¹ := hconj x hx
    calc (w⁻¹ * a) * x = w⁻¹ * (a * x * a⁻¹) * a := by group
      _ = w⁻¹ * (w * x * w⁻¹) * a := by rw [h1]
      _ = x * (w⁻¹ * a) := by group
  rcases ggWAut_schur_pm R habs (w⁻¹ * a) hTcomm with h1 | h1
  · left
    intro v
    have := congrArg (fun x : V => w x) (h1 v)
    simpa using this
  · right
    intro v
    have := congrArg (fun x : V => w x) (h1 v)
    simpa using this

theorem ggWAut_sym_norm [Module.Finite (ZMod 3) V] {N : ℕ} (hN : 5 ≤ N)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r})
    (habs : ZS.AbsIrred 3 R) (e : R ≃* Equiv.Perm (Fin N))
    (he : ∀ r : R, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)
    {a : V ≃ₗ[ZMod 3] V} (ha : a ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) :
    ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  classical
  have h01 : (⟨0, by omega⟩ : Fin N) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  let s0 : Equiv.Perm (Fin N) := Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩
  have hs0 : s0 ≠ 1 := by
    intro h
    exact h01 (Equiv.swap_eq_one_iff.mp h)
  let u0 : R := e.symm s0
  have hu0 : u0 ≠ 1 := by
    intro h
    apply hs0
    have := congrArg e h
    simpa [u0] using this
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hmem : (u0 : V ≃ₗ[ZMod 3] V) ∈ (⊥ : Subgroup (V ≃ₗ[ZMod 3] V)) := by
      rw [← hbot]; exact u0.2
    exact hu0 (Subtype.ext (Subgroup.mem_bot.mp hmem))
  obtain ⟨t₀, ht₀R, ht₀G⟩ : ∃ t : V ≃ₗ[ZMod 3] V, t ∈ R ∧ GGLinRefl t := by
    by_contra h
    have hclo : R ≤ (⊥ : Subgroup (V ≃ₗ[ZMod 3] V)) := by
      rw [hgen, Subgroup.closure_le]
      intro t ht
      exact (h ⟨t, ht.1, ht.2⟩).elim
    exact hRne (le_bot_iff.mp hclo)
  have ht₀refl : IsReflLin t₀ := (ggLinRefl_iff_isReflLin t₀).mp ht₀G
  let T₀ : R := ⟨t₀, ht₀R⟩
  obtain ⟨i₀, j₀, hij₀, he₀⟩ := he T₀ ht₀G
  have hsym_refl : ∀ t ∈ ggTransp N, IsReflLin (((e.symm t : R) : V ≃ₗ[ZMod 3] V)) := by
    intro t ht
    obtain ⟨p, q, hpq, ht'⟩ := ht
    obtain ⟨u, hu⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hij₀ hpq)
    have ht_eq : t = u * (e T₀) * u⁻¹ := by
      rw [ht', he₀, hu]
    have hsym : e.symm t = e.symm u * T₀ * (e.symm u)⁻¹ := by
      rw [ht_eq]
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [hsym]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, T₀] using
      ggQ2_isReflLin_conj ((e.symm u : R) : V ≃ₗ[ZMod 3] V) t₀ ht₀refl
  let conjA : R ≃* R :=
    { toFun := fun x => ⟨a * (x : V ≃ₗ[ZMod 3] V) * a⁻¹, by
        exact (Subgroup.mem_normalizer_iff.mp ha (x : V ≃ₗ[ZMod 3] V)).mp x.2⟩
      invFun := fun x => ⟨a⁻¹ * (x : V ≃ₗ[ZMod 3] V) * a, by
        refine (Subgroup.mem_normalizer_iff.mp ha (a⁻¹ * (x : V ≃ₗ[ZMod 3] V) * a)).mpr ?_
        rw [show a * (a⁻¹ * (x : V ≃ₗ[ZMod 3] V) * a) * a⁻¹ = (x : V ≃ₗ[ZMod 3] V) by group]
        exact x.2⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change a⁻¹ * (a * (x : V ≃ₗ[ZMod 3] V) * a⁻¹) * a = (x : V ≃ₗ[ZMod 3] V)
        group
      right_inv := by
        intro x
        apply Subtype.ext
        change a * (a⁻¹ * (x : V ≃ₗ[ZMod 3] V) * a) * a⁻¹ = (x : V ≃ₗ[ZMod 3] V)
        group
      map_mul' := by
        intro x y
        apply Subtype.ext
        change a * ((x : V ≃ₗ[ZMod 3] V) * (y : V ≃ₗ[ZMod 3] V)) * a⁻¹ =
          (a * (x : V ≃ₗ[ZMod 3] V) * a⁻¹) * (a * (y : V ≃ₗ[ZMod 3] V) * a⁻¹)
        group }
  let π : Equiv.Perm (Fin N) → Equiv.Perm (Fin N) := fun s => e (conjA (e.symm s))
  have hπe : ∀ x : R, π (e x) = e (conjA x) := by
    intro x
    dsimp only [π]
    rw [MulEquiv.symm_apply_apply]
  have hπT : ∀ t ∈ ggTransp N, π t ∈ ggTransp N := by
    intro t ht
    show e (conjA (e.symm t)) ∈ ggTransp N
    have hrefl : IsReflLin (((e.symm t : R) : V ≃ₗ[ZMod 3] V)) := hsym_refl t ht
    have hrefl' : IsReflLin (((conjA (e.symm t) : R) : V ≃ₗ[ZMod 3] V)) := by
      simpa [conjA] using
        ggQ2_isReflLin_conj a ((e.symm t : R) : V ≃ₗ[ZMod 3] V) hrefl
    have hG : GGLinRefl (((conjA (e.symm t) : R) : V ≃ₗ[ZMod 3] V)) :=
      (ggLinRefl_iff_isReflLin _).mpr hrefl'
    obtain ⟨i, j, hij, heq⟩ := he (conjA (e.symm t)) hG
    exact ⟨i, j, hij, heq⟩
  have hinj : Set.InjOn π (ggTransp N) := by
    intro s hs t ht hst
    have hst' : e (conjA (e.symm s)) = e (conjA (e.symm t)) := hst
    have h1 : conjA (e.symm s) = conjA (e.symm t) := e.injective hst'
    have h2 : e.symm s = e.symm t := conjA.injective h1
    exact e.symm.injective h2
  have hπ : ∀ s ∈ ggTransp N, ∀ t ∈ ggTransp N,
      π (s * t * s⁻¹) = π s * π t * (π s)⁻¹ := by
    intro s hs t ht
    show e (conjA (e.symm (s * t * s⁻¹))) =
      e (conjA (e.symm s)) * e (conjA (e.symm t)) * (e (conjA (e.symm s)))⁻¹
    simp only [map_mul, map_inv]
  obtain ⟨g, hg⟩ := ggQ2_quandle_aut_sym N hN π hπT hinj hπ
  let w : R := e.symm g
  have hconj_eq : ∀ r ∈ R, IsReflLin r →
      a * r * a⁻¹ = (w : V ≃ₗ[ZMod 3] V) * r * (w : V ≃ₗ[ZMod 3] V)⁻¹ := by
    intro r hrR hrrefl
    let Rr : R := ⟨r, hrR⟩
    have hRrG : GGLinRefl r := (ggLinRefl_iff_isReflLin r).mpr hrrefl
    have htr : e Rr ∈ ggTransp N := by
      obtain ⟨i, j, hij, heq⟩ := he Rr hRrG
      exact ⟨i, j, hij, heq⟩
    have hgtr : π (e Rr) = g * e Rr * g⁻¹ := hg (e Rr) htr
    rw [hπe Rr] at hgtr
    have hw_eq : conjA Rr = w * Rr * w⁻¹ := by
      apply e.injective
      rw [hgtr]
      simp only [map_mul, map_inv]
      rw [show e w = g from MulEquiv.apply_symm_apply e g]
    have hcoe := congrArg (fun x : R => (x : V ≃ₗ[ZMod 3] V)) hw_eq
    simpa [conjA, Rr, w, Subgroup.coe_mul, Subgroup.coe_inv] using hcoe
  exact ⟨(w : V ≃ₗ[ZMod 3] V), w.2,
    ggWAut_pm_of_conj_gen R hgen habs w.2
      (fun r hr hrefl => hconj_eq r hr ((ggLinRefl_iff_isReflLin r).mp hrefl))⟩

theorem ggWAut_E_norm {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (hInner : GGQ2WeylInner n C)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (habs : ZS.AbsIrred 3 R) (hW : GGWeylModel3 C R)
    {a : V ≃ₗ[ZMod 3] V} (ha : a ∈ Subgroup.normalizer (R : Set (V ≃ₗ[ZMod 3] V))) :
    ∃ r ∈ R, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  obtain ⟨z, α, hz, hspan, hα, hWeyl⟩ := hW
  have hnorm : a ∈ Subgroup.normalizer (ggQ2WeylOf z α : Set (V ≃ₗ[ZMod 3] V)) := by
    simpa only [hWeyl] using ha
  obtain ⟨w, hw, hconj⟩ := hInner z hz hspan α hα a hnorm
  have hwR : w ∈ R := by simpa only [hWeyl] using hw
  refine ⟨w, hwR, ?_⟩
  have hTcomm : ∀ x ∈ R, (w⁻¹ * a) * x = x * (w⁻¹ * a) := by
    intro x hx
    have hx' : x ∈ ggQ2WeylOf z α := by simpa only [hWeyl] using hx
    have h1 : a * x * a⁻¹ = w * x * w⁻¹ := hconj x hx'
    calc (w⁻¹ * a) * x = w⁻¹ * (a * x * a⁻¹) * a := by group
      _ = w⁻¹ * (w * x * w⁻¹) * a := by rw [h1]
      _ = x * (w⁻¹ * a) := by group
  rcases ggWAut_schur_pm R habs (w⁻¹ * a) hTcomm with h1 | h1
  · left
    intro v
    have := congrArg (fun x : V => w x) (h1 v)
    simpa using this
  · right
    intro v
    have := congrArg (fun x : V => w x) (h1 v)
    simpa using this

end CFSG.StandardType

end
