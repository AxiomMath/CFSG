module

public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBOrth

@[expose] def GGBstarElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E₀ : Subgroup R, IsElemAbelian p E₀ → p ^ r ≤ Nat.card E₀ → p ^ 3 ≤ Nat.card E₀ →
    ∀ φ : MulAut R, φ ^ p = 1 → (∀ e ∈ E₀, φ e = e) →
      ∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ e ∈ E₀, ∀ u ∈ U, e * u * e⁻¹ ∈ U) ∧
        ∀ u ∈ U, φ u ∈ U

section General

variable {G : Type*} [Group G]

theorem mulAut_mul_conj_mul_inv (φ : MulAut G) (e : G) :
    φ * MulAut.conj e * φ⁻¹ = MulAut.conj (φ e) := by
  ext x
  simp [MulAut.conj_apply]

@[expose] def stabSubgroup (U : Subgroup G) : Subgroup (MulAut G) where
  carrier := {ψ | U.map ψ.toMonoidHom = U}
  mul_mem' {a b} ha hb := by
    change U.map (a * b).toMonoidHom = U
    have : (a * b).toMonoidHom = a.toMonoidHom.comp b.toMonoidHom := by
      ext x
      rfl
    rw [this, ← Subgroup.map_map]
    change U.map b.toMonoidHom = U at hb
    change U.map a.toMonoidHom = U at ha
    rw [hb, ha]
  one_mem' := by
    change U.map (1 : MulAut G).toMonoidHom = U
    have : (1 : MulAut G).toMonoidHom = MonoidHom.id G := by
      ext x
      rfl
    rw [this, Subgroup.map_id]
  inv_mem' {a} ha := by
    change U.map a⁻¹.toMonoidHom = U
    change U.map a.toMonoidHom = U at ha
    conv_lhs => rw [← ha]
    rw [Subgroup.map_map]
    have : a⁻¹.toMonoidHom.comp a.toMonoidHom = MonoidHom.id G := by
      ext x
      exact a.symm_apply_apply x
    rw [this, Subgroup.map_id]

theorem mem_stabSubgroup_of_le [Finite G] {U : Subgroup G} {ψ : MulAut G}
    (h : ∀ u ∈ U, ψ u ∈ U) : ψ ∈ stabSubgroup U := by
  change U.map ψ.toMonoidHom = U
  have hle : U.map ψ.toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    exact h u hu
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [← Nat.card_congr (U.equivMapOfInjective _ ψ.injective).toEquiv]

end General

theorem ggBstarBound_of_elt {p r : ℕ} (hp : p.Prime) {R : Type} [Group R] [Finite R]
    {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGBstarElt p r R) : GGBstarBound p r R I := by
  intro Eb Eh hEbI hEb hr h3 hle hEh hcard
  have := TableBSymp.finite_mulAut (R := R)
  have hinj := mulAut_conj_injective hZ
  set E₀ := Eb.comap (MulAut.conj : R →* MulAut R) with hE₀
  have hmap : E₀.map (MulAut.conj : R →* MulAut R) = Eb := by
    rw [hE₀, Subgroup.map_comap_eq, inf_eq_right.mpr]
    intro φ hφ
    exact hI (hEbI hφ)
  have hcardE₀ : Nat.card E₀ = Nat.card Eb := by
    rw [Nat.card_congr (E₀.equivMapOfInjective _ hinj).toEquiv, hmap]
  have hE₀e : IsElemAbelian p E₀ := by
    refine ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hEb a.2 b.2
    · rw [map_pow, map_one]
      exact hEb.2 _ hx
  obtain ⟨φ, hφEh, hφEb⟩ : ∃ φ ∈ Eh, φ ∉ Eb := by
    by_contra hcon
    push Not at hcon
    have hle' : Eh ≤ Eb := hcon
    have h1 := Subgroup.card_le_of_le hle'
    have h2 : 0 < Nat.card Eb := Nat.card_pos
    have h4 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    nlinarith
  have hφp : φ ^ p = 1 := hEh.2 φ hφEh
  have hφfix : ∀ e ∈ E₀, φ e = e := by
    intro e he
    have hce : MulAut.conj e ∈ Eh := hle he
    have hcomm := TableB.IsElemAbelian.comm hEh hφEh hce
    apply hinj
    rw [← mulAut_mul_conj_mul_inv, hcomm, mul_inv_cancel_right]
  obtain ⟨U, hU, hU2, hUE, hUφ⟩ := h E₀ hE₀e (hcardE₀ ▸ hr) (hcardE₀ ▸ h3) φ hφp hφfix
  refine ⟨Eb ⊔ Subgroup.zpowers φ, ?_, sup_le hle (Subgroup.zpowers_le.mpr hφEh), U, hU, hU2, ?_⟩
  · refine lt_of_le_of_ne le_sup_left fun h' => hφEb ?_
    rw [h']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers φ)
  · have hle2 : Eb ⊔ Subgroup.zpowers φ ≤ stabSubgroup U := by
      refine sup_le ?_ (Subgroup.zpowers_le.mpr (mem_stabSubgroup_of_le hUφ))
      intro ψ hψ
      obtain ⟨e, rfl⟩ := hI (hEbI hψ)
      refine mem_stabSubgroup_of_le fun u hu => ?_
      have heE : e ∈ E₀ := by
        rw [hE₀, Subgroup.mem_comap]
        exact hψ
      rw [MulAut.conj_apply]
      exact hUE e heE u hu
    intro ψ hψ u hu
    have h1 : U.map ψ.toMonoidHom = U := hle2 hψ
    rw [← h1]
    exact ⟨u, hu, rfl⟩


theorem ggBstarElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (ψ : R ≃* R')
    (h : GGBstarElt p r R) : GGBstarElt p r R' := by
  intro E₀ hE₀ hr h3 φ hφ hφE
  set φ₀ : MulAut R := (MulAut.congr ψ).symm φ with hφ₀
  have hφ₀app : ∀ x, φ₀ x = ψ.symm (φ (ψ x)) := fun x => rfl
  have hcard : Nat.card (E₀.map ψ.symm.toMonoidHom) = Nat.card E₀ :=
    (Nat.card_congr (E₀.equivMapOfInjective _ ψ.symm.injective).toEquiv).symm
  obtain ⟨U, hU, hU2, hUE, hUφ⟩ := h (E₀.map ψ.symm.toMonoidHom) (TableB.isElemAbelian_map hE₀ _)
    (hcard ▸ hr) (hcard ▸ h3) φ₀ (by rw [hφ₀, ← map_pow, hφ, map_one]) (by
      rintro _ ⟨e, he, rfl⟩
      rw [hφ₀app]
      simp [hφE e he])
  refine ⟨U.map ψ.toMonoidHom, ?_, hU2.map _, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ ψ.injective]
    exact hU
  · rintro e he _ ⟨u, hu, rfl⟩
    refine ⟨ψ.symm e * u * (ψ.symm e)⁻¹, hUE _ ⟨e, he, rfl⟩ u hu, ?_⟩
    simp
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨φ₀ u, hUφ u hu, ?_⟩
    simp [hφ₀app]

section Parity

variable {G : Type*} [Group G]

theorem map_mulAut_mul (φ ψ : MulAut G) (Z : Subgroup G) :
    Z.map (φ * ψ).toMonoidHom = (Z.map ψ.toMonoidHom).map φ.toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

theorem map_mulAut_one (Z : Subgroup G) : Z.map (1 : MulAut G).toMonoidHom = Z := by
  have : (1 : MulAut G).toMonoidHom = MonoidHom.id G := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

theorem exists_invariant_of_dichotomy [Finite G] {p : ℕ} (hp : Odd p) (φ : MulAut G)
    (hφ : φ ^ p = 1) (F : Subgroup G → Prop) (Up Um : Subgroup G)
    (hF : ∀ P, F P → F (P.map φ.toMonoidHom)) (hKL : ∀ P, F P → P ≤ Up ∨ P ≤ Um)
    (hUU : Up ⊓ Um = ⊥)
    (hsupP : ∀ S : Set (Subgroup G), (∀ P ∈ S, F P ∧ P ≤ Up) → F (sSup S))
    (hsupM : ∀ S : Set (Subgroup G), (∀ P ∈ S, F P ∧ P ≤ Um) → F (sSup S))
    {Y : Subgroup G} (hY : F Y) (hYU : Y ≤ Up) (hY1 : Y ≠ ⊥) :
    ∃ Z, F Z ∧ Z ≠ ⊥ ∧ Z ≤ Up ∧ Z.map φ.toMonoidHom ≤ Z := by
  set Zp := sSup {P | F P ∧ P ≤ Up} with hZpdef
  set Zm := sSup {P | F P ∧ P ≤ Um} with hZmdef
  have hZp : F Zp := hsupP _ fun P hP => hP
  have hZm : F Zm := hsupM _ fun P hP => hP
  have hZpU : Zp ≤ Up := sSup_le fun P hP => hP.2
  have hZmU : Zm ≤ Um := sSup_le fun P hP => hP.2
  have hleP : ∀ P, F P → P ≤ Up → P ≤ Zp := fun P hP hPU => le_sSup ⟨hP, hPU⟩
  have hleM : ∀ P, F P → P ≤ Um → P ≤ Zm := fun P hP hPU => le_sSup ⟨hP, hPU⟩
  have hZp1 : Zp ≠ ⊥ := fun h => hY1 (le_bot_iff.mp (h ▸ hleP Y hY hYU))
  have hcardmap : ∀ P : Subgroup G, Nat.card (P.map φ.toMonoidHom) = Nat.card P := fun P =>
    (Nat.card_congr (P.equivMapOfInjective _ φ.injective).toEquiv).symm
  have hdisj : ∀ P : Subgroup G, P ≤ Up → P ≤ Um → P = ⊥ := fun P h1 h2 =>
    le_bot_iff.mp (hUU ▸ le_inf h1 h2)
  refine ⟨Zp, hZp, hZp1, hZpU, ?_⟩
  rcases hKL _ (hF _ hZp) with h | h
  · exact hleP _ (hF _ hZp) h
  · exfalso
    have h1 : Zp.map φ.toMonoidHom ≤ Zm := hleM _ (hF _ hZp) h
    rcases hKL _ (hF _ hZm) with h' | h'
    · have h2 : Zm.map φ.toMonoidHom ≤ Zp := hleP _ (hF _ hZm) h'
      have hc1 := Subgroup.card_le_of_le h1
      have hc2 := Subgroup.card_le_of_le h2
      rw [hcardmap] at hc1 hc2
      have he1 : Zp.map φ.toMonoidHom = Zm :=
        Subgroup.eq_of_le_of_card_ge h1 (by rw [hcardmap]; omega)
      have he2 : Zm.map φ.toMonoidHom = Zp :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [hcardmap]; omega)
      have hpow : ∀ n : ℕ, Zp.map (φ ^ (2 * n)).toMonoidHom = Zp := by
        intro n
        induction n with
        | zero => rw [mul_zero, pow_zero, map_mulAut_one]
        | succ n ih =>
          rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pow_succ', map_mulAut_mul, pow_succ',
            map_mulAut_mul, ih, he1, he2]
      obtain ⟨j, hj⟩ := hp
      have h3 : Zp.map (φ ^ p).toMonoidHom = Zm := by
        rw [hj, pow_succ', map_mulAut_mul, hpow j, he1]
      rw [hφ, map_mulAut_one] at h3
      exact hZp1 (hdisj Zp hZpU (h3 ▸ hZmU))
    · have h2 : Zm.map φ.toMonoidHom ≤ Zm := hleM _ (hF _ hZm) h'
      have he2 : Zm.map φ.toMonoidHom = Zm :=
        Subgroup.eq_of_le_of_card_ge h2 (by rw [hcardmap])
      have h3 : Zp.map φ.toMonoidHom ≤ Zm.map φ.toMonoidHom := he2.symm ▸ h1
      have h4 : Zp ≤ Zm := (Subgroup.map_le_map_iff_of_injective φ.injective).mp h3
      exact hZp1 (hdisj Zp hZpU (h4.trans hZmU))

end Parity

end TableBOrth

end CFSG.StandardType
