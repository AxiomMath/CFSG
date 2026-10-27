module

public import CFSG.Quasithin.MS93.M16Basic
public import CFSG.Quasithin.MS93.ML3Rec

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

theorem comm_mem_of_rootElt02 [CharP F 2] (ρ : SL3 F →* MulAut V) (S : Subgroup V)
    (hS : ∀ g : SL3 F, ∀ s ∈ S, ρ g s ∈ S)
    (h02 : ∀ (c : F) (v : V), ρ (rootElt 0 2 c) v * v⁻¹ ∈ S) (g : SL3 F) (v : V) :
    ρ g v * v⁻¹ ∈ S := by
  let H : Subgroup (SL3 F) :=
    { carrier := {g | ∀ v : V, ρ g v * v⁻¹ ∈ S}
      mul_mem' := fun {g k} hg hk v => by
        have he : ρ (g * k) v * v⁻¹ = ρ g (ρ k v * v⁻¹) * (ρ g v * v⁻¹) := by
          rw [rho_mul, map_mul (ρ g), map_inv (ρ g)]
          group
        rw [he]
        exact S.mul_mem (hS g _ (hk v)) (hg v)
      one_mem' := fun v => by simp
      inv_mem' := fun {g} hg v => by
        have he : ρ g⁻¹ v * v⁻¹ = (ρ g (ρ g⁻¹ v) * (ρ g⁻¹ v)⁻¹)⁻¹ := by
          rw [rho_rho_inv]
          group
        rw [he]
        exact S.inv_mem (hg _) }
  have hconj : ∀ k c, k * rootElt 0 2 c * k⁻¹ ∈ H := by
    intro k c v
    have he : ρ (k * rootElt 0 2 c * k⁻¹) v * v⁻¹ =
        ρ k (ρ (rootElt 0 2 c) (ρ k⁻¹ v) * (ρ k⁻¹ v)⁻¹) := by
      rw [rho_mul, rho_mul, map_mul (ρ k), map_inv (ρ k), rho_rho_inv]
    rw [he]
    exact hS k _ (h02 c _)
  have htop : H = ⊤ := by
    refine eq_top_of_rootElt_mem fun i j c hij => ?_
    obtain ⟨σ, hσ0, hσ2⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 2 = j := by
      revert i j; decide
    have := hconj (pmat σ) c
    rwa [pmat_conj_rootElt, hσ0, hσ2] at this
  exact (htop ▸ Subgroup.mem_top g : g ∈ H) v

theorem commV_le_of_rootElt02 [CharP F 2] (ρ : SL3 F →* MulAut V) (S : Subgroup V)
    (hS : ∀ g : SL3 F, ∀ s ∈ S, ρ g s ∈ S)
    (h02 : ∀ (c : F) (v : V), ρ (rootElt 0 2 c) v * v⁻¹ ∈ S) : commV ρ.range ≤ S := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨_, ⟨g, rfl⟩, v, rfl⟩
  exact comm_mem_of_rootElt02 ρ S hS h02 g v

@[expose] def pt (ρ : SL3 F →* MulAut V) (A : Subgroup V) (x : Fin 3 → F) : Subgroup V :=
  ⨆ (g : SL3 F) (_ : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = x),
    A.map (ρ g).toMonoidHom

theorem mul_mem_ptStab_of_mulVec {g g' : SL3 F} {c : F}
    (h : ((g' : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
      c • (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0])) :
    g⁻¹ * g' ∈ (ptStab : Subgroup (SL3 F)) := by
  rw [mem_ptStab_iff_mulVec_e0, coe_mul_mulVec, h, Matrix.mulVec_smul, ← coe_mul_mulVec,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  exact Submodule.smul_mem _ c (by simp [mem_pt0])

variable {ρ : SL3 F →* MulAut V} {A : Subgroup V}

theorem pt_eq (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A) {g : SL3 F}
    {x : Fin 3 → F} (hg : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = x) :
    pt ρ A x = A.map (ρ g).toMonoidHom := by
  refine le_antisymm (iSup₂_le fun g' hg' => ?_) (le_iSup₂_of_le g hg le_rfl)
  rw [map_rho_eq_map_rho hA (mul_mem_ptStab_of_mulVec (c := 1) (by rw [hg, hg', one_smul]))]

theorem pt_zero : pt ρ A 0 = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun g hg => ?_)
  exact absurd hg (ML3.mulVec_e0_ne_zero g)

theorem pt_smul (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A) {c : F}
    (hc : c ≠ 0) (x : Fin 3 → F) : pt ρ A (c • x) = pt ρ A x := by
  by_cases hx : x = 0
  · rw [hx, smul_zero]
  obtain ⟨g, hg⟩ := exists_mulVec_e0_eq hx
  rw [pt_eq hA hg, pt_eq hA (g := g * tor c 1 hc one_ne_zero)]
  · exact map_rho_eq_map_rho hA (by rw [inv_mul_cancel_left]; exact tor_mem_ptStab _ _ _ _)
  · rw [coe_mul_mulVec, tor_mulVec_e0, Matrix.mulVec_smul, hg]

theorem map_pt (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A) (g : SL3 F)
    (x : Fin 3 → F) :
    (pt ρ A x).map (ρ g).toMonoidHom = pt ρ A (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
  by_cases hx : x = 0
  · rw [hx, Matrix.mulVec_zero, pt_zero, Subgroup.map_bot]
  obtain ⟨k, hk⟩ := exists_mulVec_e0_eq hx
  rw [pt_eq hA hk, pt_eq hA (g := g * k) (by rw [coe_mul_mulVec, hk]), map_rho_mul]

theorem rho_mem_pt (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A) (g : SL3 F)
    {x : Fin 3 → F} {v : V} (hv : v ∈ pt ρ A x) :
    ρ g v ∈ pt ρ A (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
  rw [← map_pt hA]
  exact rho_mem_map_rho g hv

theorem pt_e0 (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A) :
    pt ρ A ![1, 0, 0] = A := by
  rw [pt_eq hA (g := 1) (by simp), map_rho_one]

theorem submoduleClosure_eq_iSup_pt :
    G6.submoduleClosure ρ.range A = ⨆ x : Fin 3 → F, pt ρ A x := by
  refine le_antisymm (iSup₂_le fun _ hg => ?_) (iSup_le fun x => iSup₂_le fun g _ =>
    le_iSup₂_of_le (ρ g) ⟨g, rfl⟩ le_rfl)
  obtain ⟨g, rfl⟩ := hg
  exact le_iSup_of_le (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0])
    (le_iSup₂_of_le g rfl le_rfl)

theorem wOff_eq_iSup_pt :
    wOff ρ A = ⨆ (x : Fin 3 → F) (_ : x 2 ≠ 0), pt ρ A x := by
  refine le_antisymm (iSup₂_le fun g hg => ?_) (iSup₂_le fun x hx => iSup₂_le fun g hg => ?_)
  · exact le_iSup₂_of_le (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) hg
      (le_iSup₂_of_le g rfl le_rfl)
  · exact le_iSup₂_of_le g (by rw [hg]; exact hx) le_rfl

theorem pt_le_wOff {x : Fin 3 → F} (hx : x 2 ≠ 0) : pt ρ A x ≤ wOff ρ A := by
  rw [wOff_eq_iSup_pt]
  exact le_iSup₂_of_le x hx le_rfl

theorem lnStab_apply22_ne_zero {g : SL3 F} (hg : g ∈ (lnStab : Subgroup (SL3 F))) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h
  have hdet := g.2
  rw [Matrix.det_fin_three, hg.1, hg.2, h] at hdet
  simp at hdet

theorem mulVec_apply2_of_mem_lnStab {g : SL3 F} (hg : g ∈ (lnStab : Subgroup (SL3 F)))
    (x : Fin 3 → F) :
    (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2 * x 2 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hg.1, hg.2]

theorem rho_mem_wOff (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A) {g : SL3 F}
    (hg : g ∈ (lnStab : Subgroup (SL3 F))) {v : V} (hv : v ∈ wOff ρ A) :
    ρ g v ∈ wOff ρ A := by
  have key : (wOff ρ A).map (ρ g).toMonoidHom ≤ wOff ρ A := by
    rw [wOff_eq_iSup_pt (A := A), Subgroup.map_iSup]
    refine iSup_le fun x => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hx => ?_
    rw [map_pt hA, ← wOff_eq_iSup_pt]
    refine pt_le_wOff ?_
    rw [mulVec_apply2_of_mem_lnStab hg]
    exact mul_ne_zero (lnStab_apply22_ne_zero hg) hx
  exact key (rho_mem_map_rho g hv)

theorem rho_conj_apply (g x : SL3 F) (v : V) : ρ (g * x * g⁻¹) (ρ g v) = ρ g (ρ x v) := by
  rw [rho_mul, rho_mul, rho_inv_rho]

theorem map_commOn_eq {g : SL3 F} {X X' : Subgroup (SL3 F)} {A' : Subgroup V}
    (hX : ∀ x ∈ X, g * x * g⁻¹ ∈ X') (hX' : ∀ x ∈ X', g⁻¹ * x * g ∈ X)
    (hA : A.map (ρ g).toMonoidHom = A') :
    (G6.commOn (X.map ρ) A).map (ρ g).toMonoidHom = G6.commOn (X'.map ρ) A' := by
  subst hA
  refine le_antisymm ?_ ?_
  · rw [map_rho_le_iff]
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨_, ⟨x, hx, rfl⟩, a, ha, rfl⟩ := hw
      have he : ρ g (ρ x a * a⁻¹) = ρ (g * x * g⁻¹) (ρ g a) * (ρ g a)⁻¹ := by
        rw [rho_conj_apply, map_mul (ρ g), map_inv (ρ g)]
      rw [he]
      exact G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨_, hX x hx, rfl⟩) (rho_mem_map_rho g ha)
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  · rw [G6.commOn_le_iff]
    rintro _ ⟨x, hx, rfl⟩ a ha
    rw [mem_map_rho] at ha
    rw [mem_map_rho]
    have he : ρ g⁻¹ (ρ x a * a⁻¹) = ρ (g⁻¹ * x * g) (ρ g⁻¹ a) * (ρ g⁻¹ a)⁻¹ := by
      rw [map_mul (ρ g⁻¹), map_inv (ρ g⁻¹), show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by group,
        rho_conj_apply]
    rw [he]
    exact G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨_, hX' x hx, rfl⟩) ha

theorem rootGroup_conj_pmat [CharP F 2] (σ : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (∀ x ∈ (rootGroup i j : Subgroup (SL3 F)), pmat σ * x * (pmat σ)⁻¹ ∈ rootGroup (σ i) (σ j)) ∧
    (∀ x ∈ (rootGroup (σ i) (σ j) : Subgroup (SL3 F)),
      (pmat σ)⁻¹ * x * pmat σ ∈ rootGroup i j) := by
  constructor
  · rintro _ ⟨c, rfl⟩
    rw [pmat_conj_rootElt]
    exact rootElt_mem_rootGroup _ _ c
  · rintro _ ⟨c, rfl⟩
    have h := pmat_conj_rootElt (F := F) σ⁻¹ (σ i) (σ j) c
    rw [pmat_inv, inv_inv] at h
    rw [pmat_inv, h]
    simpa using rootElt_mem_rootGroup (F := F) i j c

theorem qLn_elt_mulVec (a b : F) (x : Fin 3 → F) :
    ((rootElt 0 2 a * rootElt 1 2 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
      ![x 0 + a * x 2, x 1 + b * x 2, x 2] := by
  rw [coe_mul_mulVec, rootElt_mulVec (by decide), rootElt_mulVec (by decide)]
  funext k
  fin_cases k <;> simp

theorem le_pt_sup_commOn (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A)
    {p : Fin 3 → F} (hp : p 2 ≠ 0) :
    wOff ρ A ≤ pt ρ A p ⊔ G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) (wOff ρ A) := by
  refine (wOff_eq_iSup_pt (A := A)).le.trans (iSup₂_le fun x hx => ?_)
  set c := p 2 * (x 2)⁻¹ with hc
  have hc0 : c ≠ 0 := mul_ne_zero hp (inv_ne_zero hx)
  rw [← pt_smul hA hc0]
  set y := c • x with hy
  have hy2 : y 2 = p 2 := by
    rw [hy, Pi.smul_apply, smul_eq_mul, hc, mul_assoc, inv_mul_cancel₀ hx, mul_one]
  set u := rootElt 0 2 ((y 0 - p 0) / p 2) * rootElt 1 2 ((y 1 - p 1) / p 2) with hu
  have hup : ((u : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ p = y := by
    rw [hu, qLn_elt_mulVec]
    funext k
    fin_cases k <;> simp [div_mul_cancel₀ _ hp, hy2]
  have huq : u ∈ (qLn : Subgroup (SL3 F)) := mem_qLn_iff.mpr ⟨_, _, hu.symm⟩
  rw [← hup, ← map_pt hA, map_rho_le_iff]
  intro w hw
  have hwW : w ∈ wOff ρ A := pt_le_wOff hp hw
  have he : ρ u w = w * (ρ u w * w⁻¹) := by rw [mul_comm, inv_mul_cancel_right]
  rw [he]
  exact Subgroup.mul_mem_sup hw (G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨u, huq, rfl⟩) hwW)

theorem rootElt_mem_lnStab {i j : Fin 3} (hi : i ≠ 2) (c : F) :
    rootElt i j c ∈ (lnStab : Subgroup (SL3 F)) := by
  by_cases hij : i = j
  · rw [hij, rootElt_self]; exact Subgroup.one_mem _
  rw [mem_lnStab, coe_rootElt hij]
  simp [hi]

theorem pmat_mem_lnStab [CharP F 2] {σ : Equiv.Perm (Fin 3)} (hσ : σ 2 = 2) :
    pmat σ ∈ (lnStab : Subgroup (SL3 F)) := by
  rw [mem_lnStab, coe_pmat_apply, coe_pmat_apply]
  have h0 : (2 : Fin 3) ≠ σ 0 := fun h => absurd (σ.injective (hσ.trans h)) (by decide)
  have h1 : (2 : Fin 3) ≠ σ 1 := fun h => absurd (σ.injective (hσ.trans h)) (by decide)
  simp [h0, h1]

theorem map_le_submoduleClosure (D : Subgroup V) (g : SL3 F) :
    D.map (ρ g).toMonoidHom ≤ G6.submoduleClosure ρ.range D :=
  le_iSup₂_of_le (ρ g) ⟨g, rfl⟩ le_rfl

theorem le_submoduleClosure (D : Subgroup V) : D ≤ G6.submoduleClosure ρ.range D := by
  have := map_le_submoduleClosure (ρ := ρ) D 1
  rwa [map_rho_one] at this

theorem submoduleClosure_le_iff {D S : Subgroup V} :
    G6.submoduleClosure ρ.range D ≤ S ↔ ∀ g : SL3 F, D.map (ρ g).toMonoidHom ≤ S := by
  constructor
  · intro h g
    exact (map_le_submoduleClosure D g).trans h
  · intro h
    refine iSup₂_le fun _ hx => ?_
    obtain ⟨g, rfl⟩ := hx
    exact h g

theorem rho_mem_submoduleClosure {D : Subgroup V} (g : SL3 F) {v : V}
    (hv : v ∈ G6.submoduleClosure ρ.range D) : ρ g v ∈ G6.submoduleClosure ρ.range D := by
  have key : (G6.submoduleClosure ρ.range D).map (ρ g).toMonoidHom ≤
      G6.submoduleClosure ρ.range D := by
    rw [Subgroup.map_le_iff_le_comap, submoduleClosure_le_iff]
    intro k
    rw [← Subgroup.map_le_iff_le_comap, ← map_rho_mul]
    exact map_le_submoduleClosure D _
  exact key (rho_mem_map_rho g hv)

theorem rootElt20_21_mulVec (a b : F) (x : Fin 3 → F) :
    ((rootElt 2 0 a * rootElt 2 1 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x =
      ![x 0, x 1, x 2 + a * x 0 + b * x 1] := by
  rw [coe_mul_mulVec, rootElt_mulVec (by decide), rootElt_mulVec (by decide)]
  funext k
  fin_cases k <;> simp [add_assoc, add_comm (b * x 1)]

theorem exists_third_ne_zero {x : Fin 3 → F} (hx : x ≠ 0) :
    ∃ a b : F, x 2 + a * x 0 + b * x 1 ≠ 0 := by
  by_cases h2 : x 2 = 0
  · by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        exact hx (funext fun k => by fin_cases k <;> simp [h0, h1, h2])
      exact ⟨0, (x 1)⁻¹, by simp [h2, h1]⟩
    · exact ⟨(x 0)⁻¹, 0, by simp [h2, h0]⟩
  · exact ⟨0, 0, by simpa using h2⟩

@[expose] def commU (ρ : SL3 F →* MulAut V) (A : Subgroup V) : Subgroup V :=
  G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) (wOff ρ A)

theorem top_le_pt_e2_sup (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A)
    (hgen : G6.submoduleClosure ρ.range A = ⊤) :
    (⊤ : Subgroup V) ≤ pt ρ A ![0, 0, 1] ⊔ G6.submoduleClosure ρ.range (commU ρ A) := by
  rw [← hgen, submoduleClosure_eq_iSup_pt]
  refine iSup_le fun x => ?_
  by_cases hx : x = 0
  · rw [hx, pt_zero]; exact bot_le
  obtain ⟨a, b, hab⟩ := exists_third_ne_zero hx
  set h := rootElt 2 0 a * rootElt 2 1 b with hh
  have hhx : (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) 2 ≠ 0 := by
    rw [hh, rootElt20_21_mulVec]; simpa using hab
  have hhe : ((h⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
    have h1 : ((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = ![0, 0, 1] := by
      rw [hh, rootElt20_21_mulVec]; simp
    rw [← h1, ← coe_mul_mulVec, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec, h1]
  have hx' : x = ((h⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) := by
    rw [← coe_mul_mulVec, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec]
  rw [hx', ← map_pt hA]
  have h1 : pt ρ A (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) ≤
      pt ρ A ![0, 0, 1] ⊔ commU ρ A :=
    (pt_le_wOff hhx).trans (le_pt_sup_commOn hA (by simp))
  refine (Subgroup.map_mono h1).trans ?_
  rw [Subgroup.map_sup, map_pt hA, hhe]
  exact sup_le_sup_left (map_le_submoduleClosure _ _) _

theorem commU_le_commV : commU ρ A ≤ commV ρ.range := by
  rw [commU, G6.commOn_le_iff]
  rintro _ ⟨u, -, rfl⟩ w -
  exact comm_mem_commV ρ u w

theorem commV_eq_closure [CharP F 2]
    (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A)
    (hgen : G6.submoduleClosure ρ.range A = ⊤) :
    commV ρ.range = G6.submoduleClosure ρ.range (commU ρ A) := by
  refine le_antisymm ?_ ?_
  · refine commV_le_of_rootElt02 ρ _ (fun g s hs => rho_mem_submoduleClosure g hs)
      fun c v => ?_
    obtain ⟨a, ha, d, hd, rfl⟩ := Subgroup.mem_sup.mp (top_le_pt_e2_sup hA hgen
      (Subgroup.mem_top v))
    have he : ρ (rootElt 0 2 c) (a * d) * (a * d)⁻¹ =
        (ρ (rootElt 0 2 c) a * a⁻¹) * (ρ (rootElt 0 2 c) d * d⁻¹) := by
      rw [map_mul]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [he]
    refine Subgroup.mul_mem _ (le_submoduleClosure _ ?_) (Subgroup.mul_mem _
      (rho_mem_submoduleClosure _ hd) (Subgroup.inv_mem _ hd))
    exact G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨_, rootGroup_le_qLn
      (rootElt_mem_rootGroup 0 2 c), rfl⟩) (pt_le_wOff (by simp) ha)
  · rw [submoduleClosure_le_iff]
    intro g
    rw [map_rho_le_iff]
    intro v hv
    exact rho_mem_commV ρ g (commU_le_commV hv)

theorem top_le_pt_sup_commV [CharP F 2]
    (hA : ∀ g ∈ (ptStab : Subgroup (SL3 F)), ∀ w ∈ A, ρ g w ∈ A)
    (hgen : G6.submoduleClosure ρ.range A = ⊤) {x : Fin 3 → F} (hx : x ≠ 0) :
    (⊤ : Subgroup V) ≤ pt ρ A x ⊔ commV ρ.range := by
  obtain ⟨g₀, hg₀⟩ := exists_mulVec_e0_eq hx
  set g := g₀ * pmat (Equiv.swap 0 2) with hg
  have hge : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![0, 0, 1] = x := by
    rw [hg, coe_mul_mulVec, pmat_mulVec, ← hg₀]
    congr 1
    funext k
    fin_cases k <;> simp [Equiv.swap_apply_of_ne_of_ne]
  have h1 := top_le_pt_e2_sup hA hgen
  rw [← commV_eq_closure hA hgen] at h1
  have h2 := Subgroup.map_mono (f := (ρ g).toMonoidHom) h1
  rw [Subgroup.map_sup, map_pt hA, hge, map_rho_eq_self (fun g v hv => rho_mem_commV ρ g hv)] at h2
  refine le_trans ?_ h2
  intro v _
  exact ⟨ρ g⁻¹ v, Subgroup.mem_top _, rho_rho_inv ρ g v⟩

end CFSG.Quasithin.MS93.M16
