module

public import CFSG.Quasithin.MS93.M16Nat

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

theorem map_eq_of_rootElt [Finite V] {ρ : SL3 F →* MulAut V} {S : Subgroup V}
    (h : ∀ (i j : Fin 3) (c : F), i ≠ j → S.map (ρ (rootElt i j c)).toMonoidHom ≤ S)
    (g : SL3 F) : S.map (ρ g).toMonoidHom = S := by
  let H : Subgroup (SL3 F) :=
    { carrier := {g | S.map (ρ g).toMonoidHom = S}
      mul_mem' := fun {g k} hg hk => by
        change S.map (ρ (g * k)).toMonoidHom = S
        rw [map_rho_mul, hk, hg]
      one_mem' := map_rho_one ρ S
      inv_mem' := fun {g} hg => by
        change S.map (ρ g⁻¹).toMonoidHom = S
        conv_lhs => rw [← hg]
        rw [← map_rho_mul, inv_mul_cancel, map_rho_one] }
  have htop : H = ⊤ := by
    refine eq_top_of_rootElt_mem fun i j c hij => ?_
    change S.map (ρ (rootElt i j c)).toMonoidHom = S
    exact Subgroup.eq_of_le_of_card_ge (h i j c hij)
      (Subgroup.card_map_of_injective (ρ (rootElt i j c)).injective).ge
  exact (htop ▸ Subgroup.mem_top g : g ∈ H)

theorem rootElt_mulVec_single_of_ne {i j k : Fin 3} (hij : i ≠ j) (hk : k ≠ j) (c : F) :
    ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single k 1 = Pi.single k 1 := by
  rw [rootElt_mulVec hij]
  funext l
  simp [Pi.single_apply, Ne.symm hk]

theorem rootElt_mulVec_single [CharP F 2] {i j : Fin 3} (hij : i ≠ j) {σ : Equiv.Perm (Fin 3)}
    (h0 : σ 0 = i) (h1 : σ 1 = j) (c : F) :
    ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single j 1 =
      ((pmat σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![c, 1, 0] := by
  rw [rootElt_mulVec hij, pmat_mulVec]
  funext l
  by_cases hli : l = i
  · subst hli
    rw [← h0]
    simp [← h1, σ.injective.ne (show (0 : Fin 3) ≠ 1 by decide)]
  by_cases hlj : l = j
  · subst hlj
    rw [← h1]
    simp [← h0, σ.injective.ne (show (1 : Fin 3) ≠ 0 by decide)]
  have h2 : σ⁻¹ l = 2 := by
    have hn0 : σ⁻¹ l ≠ 0 := fun h => hli (by rw [← h0, ← h]; simp)
    have hn1 : σ⁻¹ l ≠ 1 := fun h => hlj (by rw [← h1, ← h]; simp)
    revert hn0 hn1
    generalize σ⁻¹ l = m
    revert m
    decide
  simp [hli, hlj, h2]

theorem pmat_mulVec_single [CharP F 2] (σ : Equiv.Perm (Fin 3)) (k : Fin 3) :
    ((pmat σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single k 1 = Pi.single (σ k) 1 := by
  rw [pmat_mulVec]
  funext l
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

theorem e0_eq_single : (![1, 0, 0] : Fin 3 → F) = Pi.single 0 1 := by
  funext k; fin_cases k <;> rfl

theorem e1_eq_single : (![0, 1, 0] : Fin 3 → F) = Pi.single 1 1 := by
  funext k; fin_cases k <;> rfl

section Spread

variable [CharP F 2] {ρ : SL3 F →* MulAut V} {𝒲 : Subgroup V} [Finite F] [Finite V]
  (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
  (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ≤ Nat.card F)
  (hN : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ≠
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom)
  (hW2 : ∀ r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲, ρ cyc r ∈ 𝒲)
include h𝒲 hR hN hW2

theorem pt_e1_eq :
    pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ![0, 1, 0] =
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom := by
  refine pt_eq (fun k hk r hr => ptStab_mem_R h𝒲 hR hN hW2 hk hr) ?_
  rw [p01_mulVec]
  funext k; fin_cases k <;> rfl

theorem pt_line_base (c : F) :
    pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ![c, 1, 0] ≤
      pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ![1, 0, 0] ⊔
        pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ![0, 1, 0] := by
  have hK := fun k (hk : k ∈ (ptStab : Subgroup (SL3 F))) r
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) =>
    ptStab_mem_R h𝒲 hR hN hW2 hk hr
  rw [pt_e0 hK, pt_e1_eq h𝒲 hR hN hW2, map_commOn02_p01 h𝒲, ← commOnU_eq h𝒲]
  have hg : rootElt 0 1 c * p01 ∈ (lnStab : Subgroup (SL3 F)) :=
    Subgroup.mul_mem _ (rootElt_mem_lnStab (by decide) c) p01_mem_lnStab
  rw [pt_eq hK (g := rootElt 0 1 c * p01)]
  · rw [← map_commOnU_eq h𝒲 hg]
    exact Subgroup.map_mono (commOn_mono (Subgroup.map_mono rootGroup_le_qLn) _)
  · rw [coe_mul_mulVec, p01_mulVec, rootElt_mulVec (by decide)]
    funext k; fin_cases k <;> simp

theorem pt_line_le (σ : Equiv.Perm (Fin 3)) (c : F) :
    pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)
        (((pmat σ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![c, 1, 0]) ≤
      pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) (Pi.single (σ 0) 1) ⊔
        pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) (Pi.single (σ 1) 1) := by
  have hK := fun k (hk : k ∈ (ptStab : Subgroup (SL3 F))) r
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) =>
    ptStab_mem_R h𝒲 hR hN hW2 hk hr
  rw [← pmat_mulVec_single, ← pmat_mulVec_single, ← map_pt hK, ← map_pt hK, ← map_pt hK,
    ← Subgroup.map_sup, ← e0_eq_single, ← e1_eq_single]
  exact Subgroup.map_mono (pt_line_base h𝒲 hR hN hW2 c)

theorem rootElt_map_iSup_le (i j : Fin 3) (c : F) (hij : i ≠ j) :
    (⨆ k : Fin 3, pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)
        (Pi.single k 1)).map (ρ (rootElt i j c)).toMonoidHom ≤
      ⨆ k : Fin 3, pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)
        (Pi.single k 1) := by
  have hK := fun k (hk : k ∈ (ptStab : Subgroup (SL3 F))) r
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) =>
    ptStab_mem_R h𝒲 hR hN hW2 hk hr
  rw [Subgroup.map_iSup]
  refine iSup_le fun k => ?_
  rw [map_pt hK]
  by_cases hk : k = j
  · subst hk
    obtain ⟨σ, h0, h1⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = k := by
      revert i k; decide
    rw [rootElt_mulVec_single hij h0 h1]
    refine (pt_line_le h𝒲 hR hN hW2 σ c).trans ?_
    rw [h0, h1]
    exact sup_le (le_iSup (fun k : Fin 3 => pt ρ _ (Pi.single k 1)) i)
      (le_iSup (fun k : Fin 3 => pt ρ _ (Pi.single k 1)) k)
  · rw [rootElt_mulVec_single_of_ne hij hk]
    exact le_iSup (fun k : Fin 3 => pt ρ _ (Pi.single k 1)) k

theorem closure_le_iSup :
    G6.submoduleClosure ρ.range (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ≤
      ⨆ k : Fin 3, pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)
        (Pi.single k 1) := by
  have hK := fun k (hk : k ∈ (ptStab : Subgroup (SL3 F))) r
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) =>
    ptStab_mem_R h𝒲 hR hN hW2 hk hr
  have hinv := map_eq_of_rootElt (ρ := ρ)
    (fun i j c hij => rootElt_map_iSup_le h𝒲 hR hN hW2 i j c hij)
  have hRle : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ≤
      ⨆ k : Fin 3, pt ρ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)
        (Pi.single k 1) := by
    conv_lhs => rw [← pt_e0 hK, e0_eq_single]
    exact le_iSup (fun k : Fin 3 => pt ρ _ (Pi.single k 1)) 0
  rw [submoduleClosure_le_iff]
  intro g
  rw [← hinv g]
  exact Subgroup.map_mono hRle

omit h𝒲 hR hN hW2 [Finite F] [Finite V] [CharP F 2] in
theorem iSup_pt_eq (R : Subgroup V) :
    (⨆ k : Fin 3, pt ρ R (Pi.single k 1)) =
      pt ρ R (Pi.single 0 1) ⊔ pt ρ R (Pi.single 1 1) ⊔ pt ρ R (Pi.single 2 1) := by
  refine le_antisymm (iSup_le fun k => ?_)
    (sup_le (sup_le (le_iSup (fun k : Fin 3 => pt ρ R (Pi.single k 1)) 0)
      (le_iSup (fun k : Fin 3 => pt ρ R (Pi.single k 1)) 1))
      (le_iSup (fun k : Fin 3 => pt ρ R (Pi.single k 1)) 2))
  fin_cases k
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

theorem card_closure_le :
    Nat.card ↥(G6.submoduleClosure ρ.range
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)) ≤ Nat.card F ^ 3 := by
  have hK := fun k (hk : k ∈ (ptStab : Subgroup (SL3 F))) r
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) =>
    ptStab_mem_R h𝒲 hR hN hW2 hk hr
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  have hpt : ∀ k : Fin 3, Nat.card ↥(pt ρ R (Pi.single k 1)) ≤ Nat.card F := by
    intro k
    obtain ⟨g, hg⟩ := exists_mulVec_e0_eq (F := F) (v := Pi.single k 1) (by simp)
    rw [pt_eq hK hg, Subgroup.card_map_of_injective (ρ g).injective]
    exact hR
  have hS := iSup_pt_eq (ρ := ρ) R
  calc Nat.card ↥(G6.submoduleClosure ρ.range R)
      ≤ Nat.card ↥(pt ρ R (Pi.single 0 1) ⊔ pt ρ R (Pi.single 1 1) ⊔
          pt ρ R (Pi.single 2 1)) :=
        Subgroup.card_le_of_le (hS ▸ closure_le_iSup h𝒲 hR hN hW2)
    _ ≤ Nat.card ↥(pt ρ R (Pi.single 0 1)) * Nat.card ↥(pt ρ R (Pi.single 1 1)) *
          Nat.card ↥(pt ρ R (Pi.single 2 1)) :=
        (card_sup_le_mul _ _).trans (Nat.mul_le_mul_right _ (card_sup_le_mul _ _))
    _ ≤ Nat.card F * Nat.card F * Nat.card F :=
        Nat.mul_le_mul (Nat.mul_le_mul (hpt 0) (hpt 1)) (hpt 2)
    _ = Nat.card F ^ 3 := by ring

omit h𝒲 hR hN hW2 [Finite F] [Finite V] in
theorem rootElt02_mul_p01 (b : F) : rootElt 0 2 b * p01 = p01 * rootElt 1 2 b := by
  have h := p01_conj (F := F) 1 2 b
  rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide),
    mul_inv_eq_iff_eq_mul] at h
  exact h.symm

omit h𝒲 hR hN hW2 [Finite F] [Finite V] in
theorem p12_mem_ptStab : (p12 : SL3 F) ∈ (ptStab : Subgroup (SL3 F)) := by
  change ((p12 : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ _
  rw [p12, coe_pmat_apply, coe_pmat_apply]
  simp [Equiv.swap_apply_of_ne_of_ne]

omit hW2 in
theorem comm_qPt_pt_e1 (hV : ∀ v : V, v ^ 2 = 1) {x : SL3 F}
    (hx : x ∈ (qPt : Subgroup (SL3 F))) {y : V}
    (hy : y ∈ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map
      (ρ p01).toMonoidHom) :
    ρ x y * y⁻¹ ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 := by
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  have hinv : ∀ w : V, w⁻¹ = w := fun w => by
    rw [inv_eq_iff_mul_eq_one, ← sq, hV]
  have hC0 : R.map (ρ p01).toMonoidHom ≤ G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲 := by
    rw [map_commOn02_p01 h𝒲]
    exact commOn_mono (Subgroup.map_mono (le_sup_right : (rootGroup 1 2 : Subgroup (SL3 F)) ≤
      rootGroup 0 2 ⊔ rootGroup 1 2)) _
  obtain ⟨a, b, rfl⟩ := mem_qPt_iff'.mp hx
  by_cases ha : a = 0
  · subst ha
    rw [rootElt_zero, one_mul, qLn_fix_commOnU h𝒲 hR (rootGroup_le_qLn
      (rootElt_mem_rootGroup 0 2 b)) (hC0 hy), mul_inv_cancel]
    exact Subgroup.one_mem _
  set x := rootElt 0 1 a * rootElt 0 2 b with hxdef
  have hxl : x ∈ (lnStab : Subgroup (SL3 F)) :=
    Subgroup.mul_mem _ (rootElt_mem_lnStab (by decide) a) (rootElt_mem_lnStab (by decide) b)
  have hxx : x * x = 1 := by
    rw [hxdef, mul_assoc, ← mul_assoc (rootElt 0 2 b), ((rootElt_commute (by decide)
      (by decide) b a).eq), mul_assoc, rootElt_mul_self, mul_one, rootElt_mul_self]
  set z := ρ x y * y⁻¹ with hz
  have hzC : z ∈ G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲 :=
    Subgroup.mul_mem _ (rho_mem_commOnU h𝒲 hxl (hC0 hy)) (Subgroup.inv_mem _ (hC0 hy))
  have hzfix : ρ x z = z := by
    rw [hz, map_mul (ρ x), map_inv (ρ x), ← rho_mul, hxx, map_one, MulAut.one_apply,
      hinv (ρ x y), hinv y, mul_comm]
  rw [commOnU_eq h𝒲, ← map_commOn02_p01 h𝒲] at hzC
  obtain ⟨r, hr, r₁, hr₁, hzr⟩ := Subgroup.mem_sup.mp hzC
  have hxr : ρ x r = r := by
    rw [hxdef, rho_mul, rootElt_fix_R h𝒲 hR (by decide) b hr,
      rootElt_fix_R h𝒲 hR (by decide) a hr]
  have hxr₁ : ρ x r₁ = r₁ := by
    rw [← hzr, map_mul, hxr] at hzfix
    exact mul_left_cancel hzfix
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr₁
  have hmem : ρ x (ρ p01 r') ∈ R.map (ρ (rootElt 0 1 a * p01)).toMonoidHom := by
    have he : ρ x (ρ p01 r') = ρ (rootElt 0 1 a * p01) (ρ (rootElt 1 2 b) r') := by
      rw [hxdef, ← rho_mul, ← rho_mul, mul_assoc, rootElt02_mul_p01, ← mul_assoc]
    rw [he, rootElt_fix_R h𝒲 hR (by decide) b hr']
    exact rho_mem_map_rho _ hr'
  have hmem' : ρ p01 r' ∈ R.map (ρ (rootElt 0 1 0 * p01)).toMonoidHom := by
    rw [rootElt_zero, one_mul]
    exact rho_mem_map_rho _ hr'
  change ρ x (ρ p01 r') = ρ p01 r' at hxr₁
  rw [hxr₁] at hmem
  have hbot := (caseN_inf_eq_bot h𝒲 hR hN).1
  have h01 : ρ p01 r' ∈ R ⊓ R.map (ρ p01).toMonoidHom := by
    rw [← inf_map_rootElt01_p01_of_ne h𝒲 hR (show (0 : F) ≠ a from Ne.symm ha)]
    exact ⟨hmem', hmem⟩
  rw [hbot, Subgroup.mem_bot] at h01
  change ρ (rootElt 0 1 a * rootElt 0 2 b) y * y⁻¹ ∈ R
  rw [← hz, ← hzr]
  change r * ρ p01 r' ∈ R
  rw [h01, mul_one]
  exact hr

omit h𝒲 hR hN hW2 [Finite F] [Finite V] in
theorem p12_conj_qPt {x : SL3 F} (hx : x ∈ (qPt : Subgroup (SL3 F))) :
    p12 * x * p12 ∈ (qPt : Subgroup (SL3 F)) := by
  obtain ⟨a, b, rfl⟩ := mem_qPt_iff'.mp hx
  have h1 := p12_conj (F := F) 0 1 a
  have h2 := p12_conj (F := F) 0 2 b
  rw [p12_inv, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), Equiv.swap_apply_left]
    at h1
  rw [p12_inv, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), Equiv.swap_apply_right]
    at h2
  have hpp : (p12 : SL3 F) * p12 = 1 := by rw [← mul_inv_cancel (p12 : SL3 F), p12_inv]
  have he : p12 * (rootElt 0 1 a * rootElt 0 2 b) * p12 =
      (p12 * rootElt 0 1 a * p12) * (p12 * rootElt 0 2 b * p12) := by
    rw [show (p12 * rootElt 0 1 a * p12) * (p12 * rootElt 0 2 b * p12) =
      p12 * rootElt 0 1 a * (p12 * p12) * rootElt 0 2 b * p12 by group, hpp]
    group
  rw [he, h1, h2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (rootElt_mem_rootGroup 0 2 a))
    (Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 b))

theorem comm_qPt_mem (hV : ∀ v : V, v ^ 2 = 1) {x : SL3 F}
    (hx : x ∈ (qPt : Subgroup (SL3 F))) {v : V}
    (hv : v ∈ G6.submoduleClosure ρ.range
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)) :
    ρ x v * v⁻¹ ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 := by
  have hK := fun k (hk : k ∈ (ptStab : Subgroup (SL3 F))) r
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) =>
    ptStab_mem_R h𝒲 hR hN hW2 hk hr
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  have hv' := closure_le_iSup h𝒲 hR hN hW2 hv
  rw [iSup_pt_eq] at hv'
  obtain ⟨y₀₁, hy₀₁, y₂, hy₂, rfl⟩ := Subgroup.mem_sup.mp hv'
  obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Subgroup.mem_sup.mp hy₀₁
  rw [← e0_eq_single, pt_e0 hK] at hy₀
  rw [← e1_eq_single, pt_e1_eq h𝒲 hR hN hW2] at hy₁
  have hxR : ∀ r ∈ R, ρ x r = r := fun r hr => by
    obtain ⟨a, b, rfl⟩ := mem_qPt_iff'.mp hx
    rw [rho_mul, rootElt_fix_R h𝒲 hR (by decide) b hr, rootElt_fix_R h𝒲 hR (by decide) a hr]
  have h1 := comm_qPt_pt_e1 h𝒲 hR hN hV hx hy₁
  have h2 : ρ x y₂ * y₂⁻¹ ∈ R := by
    have hp12 : (pt ρ R (Pi.single 1 1)).map (ρ p12).toMonoidHom = pt ρ R (Pi.single 2 1) := by
      rw [map_pt hK, p12, pmat_mulVec_single]
      rfl
    rw [← hp12, ← e1_eq_single, pt_e1_eq h𝒲 hR hN hW2] at hy₂
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy₂
    have hpp : (p12 : SL3 F) * p12 = 1 := by rw [← mul_inv_cancel (p12 : SL3 F), p12_inv]
    have e : ρ p12 (ρ (p12 * x * p12) y') = ρ x (ρ p12 y') := by
      rw [← rho_mul, ← rho_mul]
      congr 1
      rw [← mul_assoc, ← mul_assoc, hpp, one_mul]
    have he : ρ x (ρ p12 y') * (ρ p12 y')⁻¹ = ρ p12 (ρ (p12 * x * p12) y' * y'⁻¹) := by
      rw [map_mul (ρ p12), map_inv (ρ p12), e]
    change ρ x (ρ p12 y') * (ρ p12 y')⁻¹ ∈ R
    rw [he]
    exact hK _ p12_mem_ptStab _ (comm_qPt_pt_e1 h𝒲 hR hN hV (p12_conj_qPt hx) hy')
  have he : ρ x (y₀ * y₁ * y₂) * (y₀ * y₁ * y₂)⁻¹ =
      (ρ x y₁ * y₁⁻¹) * (ρ x y₂ * y₂⁻¹) := by
    rw [map_mul, map_mul, hxR y₀ hy₀]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [he]
  exact Subgroup.mul_mem _ h1 h2

end Spread

end CFSG.Quasithin.MS93.M16
