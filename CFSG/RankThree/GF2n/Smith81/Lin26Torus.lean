module

public import CFSG.RankThree.GF2n.Smith81.Lin26Roots

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise Matrix

section Torus

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.inf_centralizer_Z_eq (hc : Ctx M Q Z B) :
    Q ⊓ Subgroup.centralizer (Z : Set G) = Q := by
  refine inf_eq_left.mpr ?_
  intro y hy
  exact Subgroup.mem_centralizer_iff.mpr fun z hz => hc.hyp.toHyp79.V_central hz hy

theorem Ctx.inducesSL2' (hc : Ctx M Q Z B) :
    ∃ (m : ℕ) (φ : ↥(Q ⊔ QB B) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m))
      (ψ : ↥(Z ⊔ B) ≃* Multiplicative (Fin 2 → GaloisField 2 m)),
      Nat.card Z = 2 ^ m ∧ Function.Surjective φ ∧
      (∀ (z : ↥(Q ⊔ QB B)) (w w' : ↥(Z ⊔ B)), (w' : G) = (z : G) * w * (z : G)⁻¹ →
        Multiplicative.toAdd (ψ w') =
          (φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)) *ᵥ Multiplicative.toAdd (ψ w)) ∧
      (Q.subgroupOf (Q ⊔ QB B)).map φ = Timmesfeld.upperUnipotent (GaloisField 2 m) ∧
      ((QB B).subgroupOf (Q ⊔ QB B)).map φ =
        Timmesfeld.lowerUnipotent (GaloisField 2 m) ∧
      ∀ w : ↥(Z ⊔ B), (w : G) ∈ Z ↔ Multiplicative.toAdd (ψ w) 1 = 0 := by
  obtain ⟨g, hg⟩ := hc.conj
  have hgV : conjSubgroup g Z ≠ Z := by rw [← hg]; exact hc.ne
  have hgQ : conjSubgroup g Z ≤ Q := by rw [← hg]; exact hc.le
  have hQB : QB B = conjSubgroup g Q := (Ctx.QB_eq hc hg).2
  have hPQ : Q = Q ⊓ Subgroup.centralizer (Z : Set G) := (Ctx.inf_centralizer_Z_eq hc).symm
  have h : Tim78.Hyp218 M Z Q Q (Z ⊔ conjSubgroup g Z) g :=
    ⟨hc.hyp.maxLocal, hc.hyp.fitting, hc.hyp.maxAb, hc.hyp.toHyp79.sq_eq_one, hc.hyp.ti, hgV,
      hgQ, hc.hyp.hQ, hPQ, rfl⟩
  obtain ⟨y, hy⟩ := h.exists_isOpp
  obtain ⟨x, hxW, hxV⟩ := h.exists_conj_eq_V1 hy
  obtain ⟨m, -, hm, φ, ψ, hs, hker, hcompat, hup, hlow, -, hV⟩ :=
    h.exists_natural hxW hxV hy hc.hyp.q4 (H := Q ⊔ conjSubgroup g Q) rfl
  subst hg
  rw [hQB]
  exact ⟨m, φ, ψ, hm, hs, hcompat, hup, hlow, hV⟩

theorem Ctx.torus_comm (hc : Ctx M Q Z B) {x : G} (hx : x ∈ Q ⊔ QB B)
    (hxZ : x ∈ Subgroup.normalizer (Z : Set G)) (hxY : x ∈ Subgroup.normalizer (B : Set G))
    {y g : G} (hy : y ∈ B) (hg : g ∈ Q) :
    ⁅x * y * x⁻¹, g⁆ = x⁻¹ * ⁅y, g⁆ * x := by
  by_cases hy1 : y = 1
  · subst hy1
    simp [commutatorElement_def]
  obtain ⟨m, φ, ψ, hZm, hs, hcompat, hup, hlow, hV⟩ := Ctx.inducesSL2' hc
  have hXW : ∀ u ∈ Q ⊔ QB B, ∀ w ∈ Z ⊔ B, u * w * u⁻¹ ∈ Z ⊔ B := fun u hu w hw =>
    (Subgroup.mem_normalizer_iff.mp (Ctx.sup_QB_le_normalizer_ZB hc hu) w).mp hw
  have hZW : Z ≤ Z ⊔ B := le_sup_left
  have hBW : B ≤ Z ⊔ B := le_sup_right
  have hgX : g ∈ Q ⊔ QB B := Subgroup.mem_sup_left hg
  have hxinv : x⁻¹ ∈ Q ⊔ QB B := Subgroup.inv_mem _ hx
  have hBa : ∀ (y' : G) (hy' : y' ∈ B),
      Multiplicative.toAdd (ψ ⟨y', hBW hy'⟩) 0 = 0 := by
    intro y' hy'
    have hl : Timmesfeld.RankOne.lowerElt (GaloisField 2 m) 1 ∈
        Timmesfeld.lowerUnipotent (GaloisField 2 m) :=
      (Timmesfeld.RankOne.mem_lowerUnipotent_iff (GaloisField 2 m)).2 ⟨1, rfl⟩
    rw [← hlow] at hl
    obtain ⟨u', hu', hφu'⟩ := Subgroup.mem_map.mp hl
    have hu'B : (u' : G) ∈ QB B := Subgroup.mem_subgroupOf.mp hu'
    have hcen := Ctx.B_central_QB hc hy' hu'B
    have h1 := hcompat u' ⟨y', hBW hy'⟩ ⟨y', hBW hy'⟩ (by
      show y' = (u' : G) * y' * (u' : G)⁻¹
      rw [← hcen]; group)
    rw [hφu'] at h1
    have h2 := congrFun h1 1
    simp [Timmesfeld.RankOne.lowerElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
    exact h2
  have hP10 : ((φ ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 m)) 1 0 = 0 := by
    set w₀ : ↥(Z ⊔ B) := ψ.symm (Multiplicative.ofAdd ![1, 0]) with hw₀
    have hw₀a : Multiplicative.toAdd (ψ w₀) = ![1, 0] := by
      rw [hw₀, MulEquiv.apply_symm_apply]; rfl
    have hw₀Z : (w₀ : G) ∈ Z := (hV w₀).mpr (by rw [hw₀a]; rfl)
    have hxw₀ : x * (w₀ : G) * x⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hxZ _).mp hw₀Z
    have h1 := (hV ⟨x * (w₀ : G) * x⁻¹, hZW hxw₀⟩).mp hxw₀
    have h2 := hcompat ⟨x, hx⟩ w₀ ⟨x * (w₀ : G) * x⁻¹, hZW hxw₀⟩ rfl
    rw [h2, hw₀a] at h1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
  have ha0 : Multiplicative.toAdd (ψ ⟨y, hBW hy⟩) 0 = 0 := hBa y hy
  have ha1 : Multiplicative.toAdd (ψ ⟨y, hBW hy⟩) 1 ≠ 0 := by
    intro h1
    apply hy1
    have h2 : Multiplicative.toAdd (ψ ⟨y, hBW hy⟩) = 0 := by
      funext i; fin_cases i
      · exact ha0
      · exact h1
    have h3 : ψ ⟨y, hBW hy⟩ = 1 := Multiplicative.toAdd.injective (by rw [h2]; rfl)
    have h4 : (⟨y, hBW hy⟩ : ↥(Z ⊔ B)) = 1 := ψ.injective (by rw [h3, map_one])
    exact congrArg Subtype.val h4
  have hxy : x * y * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hxY y).mp hy
  have hP01 : ((φ ⟨x, hx⟩ : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 2 m)) 0 1 = 0 := by
    have h1 := hBa _ hxy
    have h2 := hcompat ⟨x, hx⟩ ⟨y, hBW hy⟩ ⟨x * y * x⁻¹, hBW hxy⟩ rfl
    rw [h2] at h1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha0, mul_zero, zero_add] at h1
    exact (mul_eq_zero.mp h1).resolve_right ha1
  have hgG : φ ⟨g, hgX⟩ ∈ Timmesfeld.upperUnipotent (GaloisField 2 m) := by
    rw [← hup]
    exact Subgroup.mem_map.mpr ⟨⟨g, hgX⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  obtain ⟨s, hs'⟩ := (Timmesfeld.RankOne.mem_upperUnipotent_iff (GaloisField 2 m)).mp hgG
  have hcommco : ∀ (u : G) (hu : u ∈ Z ⊔ B), ∃ hcu : ⁅u, g⁆ ∈ Z ⊔ B,
      Multiplicative.toAdd (ψ ⟨⁅u, g⁆, hcu⟩) = Multiplicative.toAdd (ψ ⟨u, hu⟩) -
        (φ ⟨g, hgX⟩ : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)) *ᵥ
          Multiplicative.toAdd (ψ ⟨u, hu⟩) := by
    intro u hu
    have hw2 : g * u⁻¹ * g⁻¹ ∈ Z ⊔ B := hXW g hgX u⁻¹ ((Z ⊔ B).inv_mem hu)
    have hcu : ⁅u, g⁆ ∈ Z ⊔ B := by
      have e : ⁅u, g⁆ = u * (g * u⁻¹ * g⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]; exact (Z ⊔ B).mul_mem hu hw2
    refine ⟨hcu, ?_⟩
    have h1 := hcompat ⟨g, hgX⟩ ⟨u⁻¹, (Z ⊔ B).inv_mem hu⟩ ⟨g * u⁻¹ * g⁻¹, hw2⟩ rfl
    have hinv : ψ ⟨u⁻¹, (Z ⊔ B).inv_mem hu⟩ = (ψ ⟨u, hu⟩)⁻¹ := by
      rw [← map_inv]; rfl
    have hprod : (⟨⁅u, g⁆, hcu⟩ : ↥(Z ⊔ B)) = ⟨u, hu⟩ * ⟨g * u⁻¹ * g⁻¹, hw2⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      simp only [commutatorElement_def]; group
    rw [hprod, map_mul, toAdd_mul, h1, hinv, toAdd_inv, Matrix.mulVec_neg, sub_eq_add_neg]
  obtain ⟨hcy, hcy'⟩ := hcommco y (hBW hy)
  obtain ⟨hcu, hcu'⟩ := hcommco (x * y * x⁻¹) (hBW hxy)
  have hr : x⁻¹ * ⁅y, g⁆ * x ∈ Z ⊔ B := by
    have := hXW x⁻¹ hxinv ⁅y, g⁆ hcy
    simpa using this
  have hψr := hcompat ⟨x⁻¹, hxinv⟩ ⟨⁅y, g⁆, hcy⟩ ⟨x⁻¹ * ⁅y, g⁆ * x, hr⟩ (by simp)
  have hψu := hcompat ⟨x, hx⟩ ⟨y, hBW hy⟩ ⟨x * y * x⁻¹, hBW hxy⟩ rfl
  have hφinv : φ ⟨x⁻¹, hxinv⟩ = (φ ⟨x, hx⟩)⁻¹ := by
    rw [← map_inv]; rfl
  suffices h : ψ ⟨⁅x * y * x⁻¹, g⁆, hcu⟩ = ψ ⟨x⁻¹ * ⁅y, g⁆ * x, hr⟩ by
    have := ψ.injective h
    exact congrArg Subtype.val this
  apply Multiplicative.toAdd.injective
  rw [hcu', hψr, hcy', hψu, hφinv, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
    hs']
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha0, hP10, hP01,
      Timmesfeld.RankOne.upperElt] <;> ring

theorem Ctx.exists_torus (hc : Ctx M Q Z B) :
    ∃ x ∈ Q ⊔ QB B, x ∈ Subgroup.normalizer (Z : Set G) ∧
      x ∈ Subgroup.normalizer (B : Set G) ∧
      ∀ i : ℕ, 0 < i → i < Nat.card Z - 1 → ∀ v ∈ Z, x ^ i * v = v * x ^ i → v = 1 := by
  obtain ⟨m, φ, ψ, hZm, hs, hcompat, hup, hlow, hV⟩ := Ctx.inducesSL2' hc
  have hXW : ∀ u ∈ Q ⊔ QB B, ∀ w ∈ Z ⊔ B, u * w * u⁻¹ ∈ Z ⊔ B := fun u hu w hw =>
    (Subgroup.mem_normalizer_iff.mp (Ctx.sup_QB_le_normalizer_ZB hc hu) w).mp hw
  have hZW : Z ≤ Z ⊔ B := le_sup_left
  have hBW : B ≤ Z ⊔ B := le_sup_right
  have hq4 := hc.hyp.q4
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hZm
    omega
  have hcardF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m hm0
  have hBa : ∀ (y' : G) (hy' : y' ∈ B), Multiplicative.toAdd (ψ ⟨y', hBW hy'⟩) 0 = 0 := by
    intro y' hy'
    have hl : Timmesfeld.RankOne.lowerElt (GaloisField 2 m) 1 ∈
        Timmesfeld.lowerUnipotent (GaloisField 2 m) :=
      (Timmesfeld.RankOne.mem_lowerUnipotent_iff (GaloisField 2 m)).2 ⟨1, rfl⟩
    rw [← hlow] at hl
    obtain ⟨u', hu', hφu'⟩ := Subgroup.mem_map.mp hl
    have hu'B : (u' : G) ∈ QB B := Subgroup.mem_subgroupOf.mp hu'
    have hcen := Ctx.B_central_QB hc hy' hu'B
    have h1 := hcompat u' ⟨y', hBW hy'⟩ ⟨y', hBW hy'⟩ (by
      show y' = (u' : G) * y' * (u' : G)⁻¹
      rw [← hcen]; group)
    rw [hφu'] at h1
    have h2 := congrFun h1 1
    simp [Timmesfeld.RankOne.lowerElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h2
    exact h2
  have hBchar : ∀ (w : G) (hw : w ∈ Z ⊔ B), Multiplicative.toAdd (ψ ⟨w, hw⟩) 0 = 0 → w ∈ B := by
    intro w hw h0
    let f : ↥B → {v : Fin 2 → GaloisField 2 m // v 0 = 0} := fun y =>
      ⟨Multiplicative.toAdd (ψ ⟨y, hBW y.2⟩), hBa y y.2⟩
    have hfinj : Function.Injective f := by
      intro y y' h
      have h1 : Multiplicative.toAdd (ψ ⟨y, hBW y.2⟩) = Multiplicative.toAdd (ψ ⟨y', hBW y'.2⟩) :=
        congrArg Subtype.val h
      have h2 := ψ.injective (Multiplicative.toAdd.injective h1)
      exact Subtype.ext (Subtype.mk.inj h2)
    have hcardB : Nat.card ↥B = Nat.card (GaloisField 2 m) := by
      obtain ⟨g, hg⟩ := hc.conj
      rw [hg, card_conjSubgroup, hZm, hcardF]
    have hcardT : Nat.card {v : Fin 2 → GaloisField 2 m // v 0 = 0} =
        Nat.card (GaloisField 2 m) := by
      refine Nat.card_congr
        { toFun := fun v => v.1 1
          invFun := fun a => ⟨![0, a], rfl⟩
          left_inv := fun v => by
            apply Subtype.ext
            funext i
            fin_cases i
            · exact v.2.symm
            · rfl
          right_inv := fun a => rfl }
    have hbij : Function.Bijective f :=
      hfinj.bijective_of_nat_card_le (by rw [hcardB, hcardT])
    obtain ⟨y, hy⟩ := hbij.2 ⟨Multiplicative.toAdd (ψ ⟨w, hw⟩), h0⟩
    have h1 : Multiplicative.toAdd (ψ ⟨y, hBW y.2⟩) = Multiplicative.toAdd (ψ ⟨w, hw⟩) :=
      congrArg Subtype.val hy
    have h2 := ψ.injective (Multiplicative.toAdd.injective h1)
    have h3 : (y : G) = w := congrArg Subtype.val h2
    rw [← h3]
    exact y.2
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (GaloisField 2 m)ˣ)
  rw [Nat.card_units, hcardF] at ht
  obtain ⟨x', hx'⟩ := hs (Timmesfeld.ARS.NaturalModule.diagElt t)
  have hx'X : (x' : G) ∈ Q ⊔ QB B := x'.2
  have hact : ∀ (u : G) (hu : u ∈ Z ⊔ B),
      Multiplicative.toAdd (ψ ⟨(x' : G) * u * (x' : G)⁻¹, hXW _ hx'X u hu⟩) =
        (Timmesfeld.ARS.NaturalModule.diagElt t :
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) *ᵥ
          Multiplicative.toAdd (ψ ⟨u, hu⟩) := by
    intro u hu
    have := hcompat x' ⟨u, hu⟩ ⟨_, hXW _ hx'X u hu⟩ rfl
    rw [this, hx']
  refine ⟨(x' : G), hx'X, ?_, ?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have h1 := hact z (hZW hz)
    have h2 := (hV ⟨z, hZW hz⟩).mp hz
    refine (hV ⟨_, hXW _ hx'X z (hZW hz)⟩).mpr ?_
    rw [h1]
    simp [Timmesfeld.ARS.NaturalModule.coe_diagElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      h2]
  · refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have h1 := hact y (hBW hy)
    have h2 := hBa y hy
    refine hBchar _ (hXW _ hx'X y (hBW hy)) ?_
    rw [h1]
    simp [Timmesfeld.ARS.NaturalModule.coe_diagElt, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      h2]
  · intro i hi0 hi v hv hcomm
    have hvW : v ∈ Z ⊔ B := hZW hv
    have h1 := (hV ⟨v, hvW⟩).mp hv
    have hxi : ((x' ^ i : ↥(Q ⊔ QB B)) : G) = (x' : G) ^ i := Subgroup.coe_pow _ _ _
    have hconj : v = ((x' ^ i : ↥(Q ⊔ QB B)) : G) * v * ((x' ^ i : ↥(Q ⊔ QB B)) : G)⁻¹ := by
      rw [hxi, hcomm]; group
    have h2 := hcompat (x' ^ i) ⟨v, hvW⟩ ⟨v, hvW⟩ hconj
    have hpow : ∀ k : ℕ, (Timmesfeld.ARS.NaturalModule.diagElt t :
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)) ^ k =
        Timmesfeld.ARS.NaturalModule.diagElt (t ^ k) := by
      intro k
      induction k with
      | zero => simp [Timmesfeld.ARS.NaturalModule.diagElt_one]
      | succ k ih =>
        rw [pow_succ, ih, pow_succ, Timmesfeld.ARS.NaturalModule.diagElt_mul_diagElt]
    rw [map_pow, hx', hpow i] at h2
    have h3 := congrFun h2 0
    simp only [Timmesfeld.ARS.NaturalModule.coe_diagElt, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, zero_mul, add_zero] at h3
    have hne : ((t ^ i : (GaloisField 2 m)ˣ) : GaloisField 2 m) ≠ 1 := by
      intro h
      have := pow_ne_one_of_lt_orderOf (x := t) (n := i) (by omega) (by rw [ht, ← hZm]; omega)
      exact this (Units.ext h)
    have h4 : (((t ^ i : (GaloisField 2 m)ˣ) : GaloisField 2 m) - 1) *
        Multiplicative.toAdd (ψ ⟨v, hvW⟩) 0 = 0 := by
      rw [sub_mul, one_mul, ← h3, sub_self]
    have h5 : Multiplicative.toAdd (ψ ⟨v, hvW⟩) 0 = 0 :=
      (mul_eq_zero.mp h4).resolve_left (sub_ne_zero.mpr hne)
    have h6 : Multiplicative.toAdd (ψ ⟨v, hvW⟩) = 0 := by
      funext j
      fin_cases j
      · exact h5
      · exact h1
    have h7 : ψ ⟨v, hvW⟩ = 1 := Multiplicative.toAdd.injective (by rw [h6]; rfl)
    have h8 : (⟨v, hvW⟩ : ↥(Z ⊔ B)) = 1 := ψ.injective (by rw [h7, map_one])
    exact congrArg Subtype.val h8

end Torus

end CFSG.RankThree.GF2n.Smith81
