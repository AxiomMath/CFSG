module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11D
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem11C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD

variable {V : Type} [CommGroup V]

@[expose] def stabSubCh611 (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {g | ∀ w ∈ W, g w ∈ W ∧ g⁻¹ w ∈ W}
  one_mem' w hw := ⟨hw, hw⟩
  mul_mem' {a b} ha hb w hw := by
    refine ⟨(ha _ (hb w hw).1).1, ?_⟩
    rw [mul_inv_rev, MulAut.mul_apply]
    exact (hb _ (ha w hw).2).2
  inv_mem' {a} ha w hw := by
    rw [inv_inv]
    exact ⟨(ha w hw).2, (ha w hw).1⟩

@[expose] def restrictCh611 {W : Subgroup V} (g : MulAut V) (hg : g ∈ stabSubCh611 W) :
    ↥W ≃* ↥W where
  toFun w := ⟨g w, (hg w w.2).1⟩
  invFun w := ⟨g⁻¹ w, (hg w w.2).2⟩
  left_inv w := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem restrictCh611_apply {W : Subgroup V} (g : MulAut V) (hg : g ∈ stabSubCh611 W) (w : ↥W) :
    ((restrictCh611 g hg w : ↥W) : V) = g w := rfl

theorem mem_stabSubCh611_of_comm {W X : Subgroup V} (hXW : X ≤ W) {g : MulAut V}
    (hg : ∀ v : V, g v * v⁻¹ ∈ X) : g ∈ stabSubCh611 W := by
  intro w hw
  constructor
  · have := W.mul_mem (hXW (hg w)) hw
    simpa using this
  · have h1 := hg (g⁻¹ w)
    rw [MulAut.apply_inv_self] at h1
    have h2 := W.mul_mem (W.inv_mem (hXW h1)) hw
    simpa using h2

theorem transvGroup_le_stabSubCh611 (Gm : Subgroup (MulAut V)) {W X : Subgroup V}
    (hXW : X ≤ W) : transvGroup Gm X ≤ stabSubCh611 W := by
  unfold transvGroup
  rw [Subgroup.closure_le]
  rintro g ⟨-, hg⟩
  exact mem_stabSubCh611_of_comm hXW hg

@[expose] def transvSubCh611 (x : V) (hx : x ^ 2 = 1) : Subgroup (MulAut V) where
  carrier := {g | IsTransvCh611 x g}
  one_mem' u := Or.inl (by simp)
  mul_mem' {a b} ha hb u := by
    have e : (a * b) u * u⁻¹ = (a (b u) * (b u)⁻¹) * (b u * u⁻¹) := by
      rw [MulAut.mul_apply]
      group
    have hxx : x * x = 1 := by rw [← pow_two, hx]
    rw [e]
    rcases ha (b u) with h1 | h1 <;> rcases hb u with h2 | h2 <;> simp [h1, h2, hxx]
  inv_mem' {a} ha u := by
    have h1 := ha (a⁻¹ u)
    rw [MulAut.apply_inv_self] at h1
    have hxinv : x⁻¹ = x := by
      rw [inv_eq_iff_mul_eq_one, ← pow_two, hx]
    have e : a⁻¹ u * u⁻¹ = (u * (a⁻¹ u)⁻¹)⁻¹ := by group
    rw [e]
    rcases h1 with h1 | h1
    · left; rw [h1, inv_one]
    · right; rw [h1, hxinv]

theorem transvGroup_le_transvSubCh611 (Gm : Subgroup (MulAut V)) {x : V} (hx : x ^ 2 = 1) :
    transvGroup Gm (Subgroup.zpowers x) ≤ transvSubCh611 x hx := by
  unfold transvGroup
  rw [Subgroup.closure_le]
  rintro g ⟨-, hg⟩ u
  exact (mem_zpowers_iff_of_sq hx).mp (hg u)

namespace G31Out

variable {Gm : Subgroup (MulAut V)} {X₀ : Subgroup V} (D : G31Out Gm X₀)

abbrev V0 : Subgroup V := g31V (D.Δ ⟨0, D.hs⟩)

abbrev G0 : Subgroup (MulAut V) := g31G Gm (D.Δ ⟨0, D.hs⟩)

theorem g31G_le_stab (i : Fin D.s) : g31G Gm (D.Δ i) ≤ stabSubCh611 (g31V (D.Δ i)) :=
  iSup₂_le fun _ hX => transvGroup_le_stabSubCh611 Gm (le_g31V hX)

theorem g31G_le_Gm (i : Fin D.s) : g31G Gm (D.Δ i) ≤ Gm := g31G_le Gm _

theorem mem_orbit_of_mem {i : Fin D.s} {X : Subgroup V} (hX : X ∈ D.Δ i) :
    X ∈ orbitCh611 Gm X₀ := by
  rw [← D.union]
  exact Set.mem_iUnion.mpr ⟨i, hX⟩

theorem eq_of_eqOn (htop : g31V (orbitCh611 Gm X₀) = ⊤) {f f' : MulAut V}
    (h : ∀ i, ∀ v ∈ g31V (D.Δ i), f v = f' v) : f = f' := by
  have hle : (⨆ i, g31V (D.Δ i)) ≤ (f.toMonoidHom).eqLocus f'.toMonoidHom :=
    iSup_le fun i v hv => h i v hv
  rw [D.supV, htop] at hle
  ext v
  exact hle (Subgroup.mem_top v)

theorem eq_one_of_fix (htop : g31V (orbitCh611 Gm X₀) = ⊤) {i : Fin D.s} {g : MulAut V}
    (hg : g ∈ g31G Gm (D.Δ i)) (hfix : ∀ v ∈ g31V (D.Δ i), g v = v) : g = 1 := by
  refine D.eq_of_eqOn htop fun j v hv => ?_
  by_cases hij : i = j
  · subst hij
    exact hfix v hv
  · exact D.cent i j hij g hg v hv

theorem card_V0_eq_eight [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hX₀ : Nat.card X₀ = 2)
    (htop : g31V (orbitCh611 Gm X₀) = ⊤) {R : Subgroup (MulAut V)}
    (hRA : R ≤ transvGroup Gm X₀) (hR4 : Nat.card R = 4)
    (hstab : ∀ g ∈ Gm, X₀.map g.toMonoidHom = X₀ → ∀ r ∈ R, g * r * g⁻¹ ∈ R) :
    Nat.card D.V0 = 8 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x₀, hx₀X, hx₀1⟩ : ∃ x ∈ X₀, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : X₀ = ⊥ := (Subgroup.eq_bot_iff_forall X₀).mpr hcon
    rw [this, Subgroup.card_bot] at hX₀
    omega
  have hx₀2 : x₀ ^ 2 = 1 := hV x₀
  have hX₀eq : X₀ = Subgroup.zpowers x₀ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hx₀X)
    rw [hX₀, card_zpowers_of_sq hx₀2 hx₀1]
  have hX₀V0 : X₀ ≤ D.V0 := le_g31V D.mem0
  have hx₀V0 : x₀ ∈ D.V0 := hX₀V0 hx₀X
  have hAG0 : transvGroup Gm X₀ ≤ D.G0 := transvGroup_le_g31G Gm D.mem0
  have hAT : transvGroup Gm X₀ ≤ transvSubCh611 x₀ hx₀2 := by
    rw [hX₀eq]
    exact transvGroup_le_transvSubCh611 Gm hx₀2
  have hG0S : D.G0 ≤ stabSubCh611 D.V0 := D.g31G_le_stab ⟨0, D.hs⟩
  have hV0sq : ∀ w : ↥D.V0, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hx₀1' : (⟨x₀, hx₀V0⟩ : ↥D.V0) ≠ 1 := fun h1 => hx₀1 (congrArg Subtype.val h1)
  have htr : ∀ g (hg : g ∈ transvGroup Gm X₀), IsTransvCh611 (⟨x₀, hx₀V0⟩ : ↥D.V0)
      (restrictCh611 g (hG0S (hAG0 hg))) := by
    intro g hg w
    rcases hAT hg w with h1 | h1
    · left
      exact Subtype.ext (by simpa [restrictCh611_apply] using h1)
    · right
      exact Subtype.ext (by simpa [restrictCh611_apply] using h1)
  have hres1 : ∀ g (hg : g ∈ transvGroup Gm X₀), g ≠ 1 →
      restrictCh611 g (hG0S (hAG0 hg)) ≠ 1 := by
    intro g hg hg1 h1
    apply hg1
    refine D.eq_one_of_fix htop (hAG0 hg) fun v hv => ?_
    have := congrArg (fun φ : MulAut ↥D.V0 => ((φ ⟨v, hv⟩ : ↥D.V0) : V)) h1
    simpa [restrictCh611_apply] using this
  obtain ⟨t₀, ht₀R, ht₀1⟩ : ∃ t ∈ R, t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : R = ⊥ := (Subgroup.eq_bot_iff_forall R).mpr hcon
    rw [this, Subgroup.card_bot] at hR4
    omega
  have ht₀A : t₀ ∈ transvGroup Gm X₀ := hRA ht₀R
  have hAR : transvGroup Gm X₀ ≤ R := by
    intro τ hτ
    by_cases hτ1 : τ = 1
    · rw [hτ1]; exact R.one_mem
    obtain ⟨φ, hφx, hφ⟩ := exists_conj_transv_ch611 hV0sq hx₀1' (htr t₀ ht₀A) (htr τ hτ)
      (hres1 t₀ ht₀A ht₀1) (hres1 τ hτ hτ1)
    obtain ⟨g, hgG0, hgφ⟩ := D.aut φ
    have hgGm : g ∈ Gm := D.g31G_le_Gm _ hgG0
    have hgx : g x₀ = x₀ := by
      have := hgφ ⟨x₀, hx₀V0⟩
      rw [hφx] at this
      exact this
    have hgX : X₀.map g.toMonoidHom = X₀ := by
      rw [hX₀eq, map_zpowers_mulAut, hgx]
    have hginv : ∀ v (hv : v ∈ D.V0), g⁻¹ v = ((φ⁻¹ ⟨v, hv⟩ : ↥D.V0) : V) := by
      intro v hv
      apply g.injective
      rw [MulAut.apply_inv_self, hgφ]
      simp
    have hconj : g * t₀ * g⁻¹ = τ := by
      refine D.eq_of_eqOn htop fun i v hv => ?_
      by_cases hi : (⟨0, D.hs⟩ : Fin D.s) = i
      · subst hi
        have h1 := congrArg (fun ψ : MulAut ↥D.V0 => ((ψ ⟨v, hv⟩ : ↥D.V0) : V)) hφ
        simp only [MulAut.mul_apply, restrictCh611_apply] at h1
        rw [MulAut.mul_apply, MulAut.mul_apply, hginv v hv]
        rw [← h1]
        have hmem : t₀ ((φ⁻¹ ⟨v, hv⟩ : ↥D.V0) : V) ∈ D.V0 :=
          (hG0S (hAG0 ht₀A) _ (φ⁻¹ ⟨v, hv⟩).2).1
        have := hgφ ⟨_, hmem⟩
        rw [this]
        rfl
      · have h0 := D.cent _ i hi
        rw [MulAut.mul_apply, MulAut.mul_apply, h0 g⁻¹ (D.G0.inv_mem hgG0) v hv,
          h0 t₀ (hAG0 ht₀A) v hv, h0 g hgG0 v hv, h0 τ (hAG0 hτ) v hv]
    rw [← hconj]
    exact hstab g hgGm hgX t₀ ht₀R
  have hV0p : IsPGroup 2 ↥D.V0 := fun w => ⟨1, by rw [pow_one]; exact hV0sq w⟩
  obtain ⟨d, hd⟩ := hV0p.exists_card_eq
  have hA4 : Nat.card (transvGroup Gm X₀) ≤ 4 := hR4 ▸ Subgroup.card_le_of_le hAR
  have hcd := D.card d hd X₀ D.mem0
  have hpos : 0 < Nat.card ↥(transvGroup Gm X₀ ⊓
      fixingSubgroup (MulAut V) (g31V (D.Δ ⟨0, D.hs⟩) : Set V)) := Nat.card_pos
  have h1 : 2 ^ (d - 1) ≤ 4 := by
    calc 2 ^ (d - 1) ≤ 2 ^ (d - 1) * Nat.card ↥(transvGroup Gm X₀ ⊓
          fixingSubgroup (MulAut V) (g31V (D.Δ ⟨0, D.hs⟩) : Set V)) :=
          Nat.le_mul_of_pos_right _ hpos
      _ = Nat.card (transvGroup Gm X₀) := hcd.symm
      _ ≤ 4 := hA4
  have h8 := D.eight
  rw [hd] at h8 ⊢
  have hd3 : d ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 3 ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hd3' : 3 ≤ d := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have : d = 3 := le_antisymm hd3 hd3'
  rw [this]
  norm_num

end G31Out

end CFSG.Quasithin.H13
