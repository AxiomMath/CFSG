module

public import CFSG.Quasithin.MS93.M16Pt
public import CFSG.Quasithin.MS93.M16Burn

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

theorem rootElt02_mulVec (d : F) (v : Fin 3 → F) :
    ((rootElt 0 2 d : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v + (d * v 2) • ![1, 0, 0] := by
  rw [rootElt_mulVec (by decide)]
  funext k
  fin_cases k <;> simp

theorem mulVec_e0_of_mem_ptStab {g : SL3 F} (hg : g ∈ (ptStab : Subgroup (SL3 F))) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
      (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0) • ![1, 0, 0] := by
  rw [mulVec_e0]
  funext k
  fin_cases k <;> simp [hg.1, hg.2]

theorem conj_mulVec (g h : SL3 F) (v : Fin 3 → F) :
    ((g * h * g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (((h : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v)) := by
  rw [coe_mul_mulVec, coe_mul_mulVec]

theorem mul_inv_mulVec (g : SL3 F) (v : Fin 3 → F) :
    ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) =
      v := by
  rw [← coe_mul_mulVec, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem conj_rootElt02 {g : SL3 F} (hp : g ∈ (ptStab : Subgroup (SL3 F)))
    (hl : g ∈ (lnStab : Subgroup (SL3 F))) (c : F) :
    g * rootElt 0 2 c * g⁻¹ = rootElt 0 2 (((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 0 *
      ((g⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2 * c) := by
  refine sl3_ext fun v => ?_
  rw [conj_mulVec, rootElt02_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, mul_inv_mulVec,
    mulVec_e0_of_mem_ptStab hp, mulVec_apply2_of_mem_lnStab (inv_mem hl), rootElt02_mulVec,
    smul_smul]
  congr 2
  ring

theorem qLn_elt_mulVec' (a b : F) (v : Fin 3 → F) :
    ((rootElt 0 2 a * rootElt 1 2 b : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v =
      v + (v 2) • ![a, b, 0] := by
  rw [qLn_elt_mulVec]
  funext k
  fin_cases k <;> simp [mul_comm]

theorem conj_mem_qLn {m : SL3 F} (hm : m ∈ (lnStab : Subgroup (SL3 F))) {u : SL3 F}
    (hu : u ∈ (qLn : Subgroup (SL3 F))) : m * u * m⁻¹ ∈ (qLn : Subgroup (SL3 F)) := by
  obtain ⟨a, b, rfl⟩ := mem_qLn_iff.mp hu
  set M := ((m : SL3 F) : Matrix (Fin 3) (Fin 3) F) with hM
  set e := ((m⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) 2 2 with he
  have h20 : M 2 0 = 0 := hm.1
  have h21 : M 2 1 = 0 := hm.2
  refine mem_qLn_iff.mpr ⟨e * (M 0 0 * a + M 0 1 * b), e * (M 1 0 * a + M 1 1 * b),
    (sl3_ext fun v => ?_).symm⟩
  rw [conj_mulVec, qLn_elt_mulVec', Matrix.mulVec_add, Matrix.mulVec_smul, mul_inv_mulVec,
    mulVec_apply2_of_mem_lnStab (inv_mem hm), qLn_elt_mulVec']
  funext k
  fin_cases k <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, ← hM, ← he, h20, h21] <;> ring

theorem rootElt_mem_ptStab {i j : Fin 3} (hj : j ≠ 0) (c : F) :
    rootElt i j c ∈ (ptStab : Subgroup (SL3 F)) := by
  by_cases hij : i = j
  · rw [hij, rootElt_self]; exact Subgroup.one_mem _
  change ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ _
  rw [coe_rootElt hij]
  simp [hj]

theorem commOn_mono {X Y : Subgroup (MulAut V)} (h : X ≤ Y) (A : Subgroup V) :
    G6.commOn X A ≤ G6.commOn Y A := by
  rw [G6.commOn_le_iff]
  intro x hx a ha
  exact G6.mem_commOn_of_mem (h hx) ha

variable {ρ : SL3 F →* MulAut V} {𝒲 : Subgroup V}

theorem map_commOn02_eq (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
    {g : SL3 F} (hp : g ∈ (ptStab : Subgroup (SL3 F))) (hl : g ∈ (lnStab : Subgroup (SL3 F))) :
    (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ g).toMonoidHom =
      G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 := by
  refine map_commOn_eq ?_ ?_ (map_rho_eq h𝒲 hl)
  · rintro _ ⟨c, rfl⟩
    rw [conj_rootElt02 hp hl]
    exact rootElt_mem_rootGroup _ _ _
  · rintro _ ⟨c, rfl⟩
    have h := conj_rootElt02 (inv_mem hp) (inv_mem hl) c
    rw [inv_inv] at h
    rw [h]
    exact rootElt_mem_rootGroup _ _ _

theorem rho_mem_commOn02 (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
    {g : SL3 F} (hp : g ∈ (ptStab : Subgroup (SL3 F))) (hl : g ∈ (lnStab : Subgroup (SL3 F)))
    {r : V} (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) :
    ρ g r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 := by
  rw [← map_commOn02_eq h𝒲 hp hl]
  exact rho_mem_map_rho g hr

theorem map_commOnU_eq (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
    {g : SL3 F} (hl : g ∈ (lnStab : Subgroup (SL3 F))) :
    (G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ g).toMonoidHom =
      G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲 := by
  refine map_commOn_eq (fun x hx => conj_mem_qLn hl hx) (fun x hx => ?_) (map_rho_eq h𝒲 hl)
  have := conj_mem_qLn (inv_mem hl) hx
  rwa [inv_inv] at this

theorem rho_mem_commOnU (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
    {g : SL3 F} (hl : g ∈ (lnStab : Subgroup (SL3 F))) {r : V}
    (hr : r ∈ G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲) :
    ρ g r ∈ G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲 := by
  rw [← map_commOnU_eq h𝒲 hl]
  exact rho_mem_map_rho g hr

theorem card_mul_relIndex' {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  rw [Subgroup.relIndex, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact Subgroup.card_mul_index _

theorem card_sup_mul_card_inf {G : Type*} [CommGroup G] (H K : Subgroup G) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 : Nat.card K * K.relIndex (H ⊔ K) = Nat.card ↥(H ⊔ K) :=
    card_mul_relIndex' le_sup_right
  have h2 : Nat.card ↥(H ⊓ K) * (H ⊓ K).relIndex H = Nat.card H :=
    card_mul_relIndex' inf_le_left
  rw [Subgroup.relIndex_sup_right, ← Subgroup.inf_relIndex_left] at h1
  rw [← h1, ← h2]
  ring

theorem card_spread_le [Finite V] {ι : Type*} [Fintype ι]
    (C J : Subgroup V) (S : ι → Subgroup V) (hJC : J ≤ C)
    (hSC : ∀ i, S i ≤ C) (hJS : ∀ i, J ≤ S i) (hSS : ∀ i i', i ≠ i' → S i ⊓ S i' = J) (r : ℕ)
    (hr : ∀ i, Nat.card (S i) = r) :
    Fintype.card ι * (r - Nat.card J) ≤ Nat.card C - Nat.card J := by
  classical
  have : Fintype V := Fintype.ofFinite V
  let t : ι → Finset V := fun i => (S i : Set V).toFinset \ (J : Set V).toFinset
  have hdisj : ∀ i ∈ (Finset.univ : Finset ι), ∀ i' ∈ (Finset.univ : Finset ι), i ≠ i' →
      Disjoint (t i) (t i') := by
    intro i _ i' _ hii'
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [t, Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hv hv'
    exact hv.2 (hSS i i' hii' ▸ ⟨hv.1, hv'.1⟩)
  have hcardS : ∀ i, (t i).card = r - Nat.card J := by
    intro i
    simp only [t]
    rw [Finset.card_sdiff_of_subset (Set.toFinset_subset_toFinset.mpr (hJS i)),
      ← Nat.card_eq_card_toFinset, ← Nat.card_eq_card_toFinset]
    show Nat.card ↥(S i) - Nat.card ↥J = r - Nat.card ↥J
    rw [hr i]
  have hsub : Finset.univ.biUnion t ⊆ (C : Set V).toFinset \ (J : Set V).toFinset := by
    intro v hv
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, t, Finset.mem_sdiff,
      Set.mem_toFinset, SetLike.mem_coe] at hv ⊢
    obtain ⟨i, hi, hj⟩ := hv
    exact ⟨hSC i hi, hj⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl (fun i _ => hcardS i), Finset.sum_const,
    Finset.card_univ, smul_eq_mul] at h1
  rw [Finset.card_sdiff_of_subset (Set.toFinset_subset_toFinset.mpr hJC),
    ← Nat.card_eq_card_toFinset, ← Nat.card_eq_card_toFinset] at h1
  exact h1

theorem arith_spread {q r j c : ℕ} (hj : 1 ≤ j) (hjr : j < r) (hrq : r ≤ q)
    (hc : c * j = r * r) (h : (q + 1) * (r - j) ≤ c - j) : j = 1 ∧ r = q := by
  have hcj : j ≤ c := by
    by_contra hlt
    push Not at hlt
    have : c * j < j * j := Nat.mul_lt_mul_of_pos_right hlt (by omega)
    nlinarith
  obtain ⟨d, rfl⟩ : ∃ d, r = j + d := ⟨r - j, by omega⟩
  have hd : 0 < d := by omega
  rw [show j + d - j = d by omega] at h
  have h2 : (q + 1) * d * j ≤ (c - j) * j := Nat.mul_le_mul_right j h
  rw [Nat.sub_mul, hc] at h2
  have h3 : (q + 1) * j ≤ j + d + j := by
    have h4 : (q + 1) * j * d ≤ (j + d + j) * d := by
      have : (j + d) * (j + d) - j * j = (j + d + j) * d := by
        rw [Nat.mul_self_sub_mul_self_eq]
        congr 1
        omega
      nlinarith
    exact Nat.le_of_mul_le_mul_right h4 hd
  have h5 : q * j ≤ j + d := by nlinarith
  have hj1 : j = 1 := by nlinarith
  subst hj1
  omega

section CharTwo

variable [CharP F 2]

@[expose] noncomputable def p01 : SL3 F := pmat (Equiv.swap 0 1)

@[expose] noncomputable def p02 : SL3 F := pmat (Equiv.swap 0 2)

@[expose] noncomputable def p12 : SL3 F := pmat (Equiv.swap 1 2)

theorem p01_conj (i j : Fin 3) (c : F) :
    p01 * rootElt i j c * p01⁻¹ = rootElt (Equiv.swap 0 1 i) (Equiv.swap 0 1 j) c :=
  pmat_conj_rootElt _ i j c

theorem p02_conj (i j : Fin 3) (c : F) :
    p02 * rootElt i j c * p02⁻¹ = rootElt (Equiv.swap 0 2 i) (Equiv.swap 0 2 j) c :=
  pmat_conj_rootElt _ i j c

theorem p12_conj (i j : Fin 3) (c : F) :
    p12 * rootElt i j c * p12⁻¹ = rootElt (Equiv.swap 1 2 i) (Equiv.swap 1 2 j) c :=
  pmat_conj_rootElt _ i j c

theorem p01_inv : (p01 : SL3 F)⁻¹ = p01 := by
  rw [p01, pmat_inv, Equiv.swap_inv]

theorem p02_inv : (p02 : SL3 F)⁻¹ = p02 := by
  rw [p02, pmat_inv, Equiv.swap_inv]

theorem p12_inv : (p12 : SL3 F)⁻¹ = p12 := by
  rw [p12, pmat_inv, Equiv.swap_inv]

theorem p01_mem_lnStab : (p01 : SL3 F) ∈ (lnStab : Subgroup (SL3 F)) :=
  pmat_mem_lnStab (by decide)

theorem p01_mulVec (x : Fin 3 → F) :
    ((p01 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = ![x 1, x 0, x 2] := by
  rw [p01, pmat_mulVec]
  funext k
  fin_cases k <;> rfl

theorem p02_mulVec (x : Fin 3 → F) :
    ((p02 : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x = ![x 2, x 1, x 0] := by
  rw [p02, pmat_mulVec]
  funext k
  fin_cases k <;> rfl

theorem map_commOn02_p01 (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲) :
    (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom =
      G6.commOn ((rootGroup 1 2 : Subgroup (SL3 F)).map ρ) 𝒲 := by
  have h := rootGroup_conj_pmat (F := F) (Equiv.swap 0 1) 0 2
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
  exact map_commOn_eq h.1 h.2 (map_rho_eq h𝒲 p01_mem_lnStab)

omit [CharP F 2] in
theorem commOnU_eq (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲) :
    G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲 =
      G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ⊔
        G6.commOn ((rootGroup 1 2 : Subgroup (SL3 F)).map ρ) 𝒲 := by
  refine le_antisymm ?_ (sup_le (commOn_mono (Subgroup.map_mono rootGroup_le_qLn) _)
    (commOn_mono (Subgroup.map_mono (le_sup_right : (rootGroup 1 2 : Subgroup (SL3 F)) ≤
      rootGroup 0 2 ⊔ rootGroup 1 2)) _))
  rw [G6.commOn_le_iff]
  rintro _ ⟨u, hu, rfl⟩ w hw
  obtain ⟨a, b, rfl⟩ := mem_qLn_iff.mp hu
  have hw' : ρ (rootElt 1 2 b) w ∈ 𝒲 := h𝒲 _ (rootElt_mem_lnStab (by decide) b) w hw
  have he : ρ (rootElt 0 2 a * rootElt 1 2 b) w * w⁻¹ =
      (ρ (rootElt 0 2 a) (ρ (rootElt 1 2 b) w) * (ρ (rootElt 1 2 b) w)⁻¹) *
        (ρ (rootElt 1 2 b) w * w⁻¹) := by
    rw [rho_mul]
    group
  change ρ (rootElt 0 2 a * rootElt 1 2 b) w * w⁻¹ ∈ _
  rw [he]
  exact Subgroup.mul_mem_sup
    (G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨_, rootElt_mem_rootGroup 0 2 a, rfl⟩) hw')
    (G6.mem_commOn_of_mem (Subgroup.mem_map.mpr ⟨_, rootElt_mem_rootGroup 1 2 b, rfl⟩) hw)

omit [CharP F 2] in
theorem rootElt_fix_R [Finite F] [Finite V]
    (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
    (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ≤ Nat.card F)
    {i j : Fin 3} (hij : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 2)) (c : F) {r : V}
    (hr : r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) :
    ρ (rootElt i j c) r = r := by
  have hj : j ≠ 0 := by rcases hij with h | h | h <;> rw [h.2] <;> decide
  have hi : i ≠ 2 := by rcases hij with h | h | h <;> rw [h.1] <;> decide
  refine rootElt_apply_eq_of_card_le ρ _ hR (fun c r hr => rho_mem_commOn02 h𝒲
    (rootElt_mem_ptStab hj c) (rootElt_mem_lnStab hi c) hr) (fun c c' hc hc' => ?_) c hr
  set t := c' * c⁻¹ with ht
  have ht0 : t ≠ 0 := mul_ne_zero hc' (inv_ne_zero hc)
  have htc : t * c = c' := by rw [ht, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨tor t 1 ht0 one_ne_zero, ?_, fun r hr => rho_mem_commOn02 h𝒲
      (tor_mem_ptStab _ _ _ _) (tor_mem_lnStab _ _ _ _) hr⟩
    rw [tor_conj_rootElt]
    simp [htc]
  · refine ⟨tor 1 t one_ne_zero ht0, ?_, fun r hr => rho_mem_commOn02 h𝒲
      (tor_mem_ptStab _ _ _ _) (tor_mem_lnStab _ _ _ _) hr⟩
    rw [tor_conj_rootElt]
    simp [htc]
  · refine ⟨tor t 1 ht0 one_ne_zero, ?_, fun r hr => rho_mem_commOn02 h𝒲
      (tor_mem_ptStab _ _ _ _) (tor_mem_lnStab _ _ _ _) hr⟩
    rw [tor_conj_rootElt]
    simp [htc]

omit [CharP F 2] in
theorem rho_conj_fix {g x x' : SL3 F} (hx : x = g * x' * g⁻¹) {r : V} (hr : ρ x' r = r) :
    ρ x (ρ g r) = ρ g r := by
  rw [hx, rho_conj_apply, hr]

theorem qLn_fix_commOnU [Finite F] [Finite V]
    (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
    (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ≤ Nat.card F)
    {u : SL3 F} (hu : u ∈ (qLn : Subgroup (SL3 F))) {r : V}
    (hr : r ∈ G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲) : ρ u r = r := by
  rw [commOnU_eq h𝒲, ← map_commOn02_p01 h𝒲] at hr
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := Subgroup.mem_sup.mp hr
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr₂
  obtain ⟨a, b, rfl⟩ := mem_qLn_iff.mp hu
  change ρ (rootElt 0 2 a * rootElt 1 2 b) (r₁ * ρ p01 r') = r₁ * ρ p01 r'
  rw [map_mul, rho_mul, rho_mul, rootElt_fix_R h𝒲 hR (by decide) b hr₁,
    rootElt_fix_R h𝒲 hR (by decide) a hr₁]
  have h1 : rootElt 1 2 b = p01 * rootElt 0 2 b * p01⁻¹ := by
    rw [p01_conj]; rfl
  have h0 : rootElt 0 2 a = p01 * rootElt 1 2 a * p01⁻¹ := by
    rw [p01_conj]; rfl
  rw [rho_conj_fix h1 (rootElt_fix_R h𝒲 hR (by decide) b hr'),
    rho_conj_fix h0 (rootElt_fix_R h𝒲 hR (by decide) a hr')]

omit [CharP F 2] in
theorem map_eq_of_fix {A : Subgroup V} {g : SL3 F} (h : ∀ v ∈ A, ρ g v = v) :
    A.map (ρ g).toMonoidHom = A := by
  refine le_antisymm (map_rho_le_iff.mpr fun v hv => (h v hv).symm ▸ hv) fun v hv => ?_
  exact ⟨v, hv, h v hv⟩

omit [CharP F 2] in
theorem map_rho_inf (A B : Subgroup V) (g : SL3 F) :
    (A ⊓ B).map (ρ g).toMonoidHom = A.map (ρ g).toMonoidHom ⊓ B.map (ρ g).toMonoidHom :=
  Subgroup.map_inf_eq A B (ρ g).toMonoidHom (ρ g).injective

theorem rootElt01_mul_p01 {c : F} (hc : c ≠ 0) :
    rootElt 0 1 c * p01 = rootElt 1 0 c⁻¹ * (tor c c⁻¹ hc (inv_ne_zero hc) * rootElt 0 1 c⁻¹) := by
  refine sl3_ext fun v => ?_
  rw [coe_mul_mulVec, coe_mul_mulVec, coe_mul_mulVec, p01_mulVec, rootElt_mulVec (by decide),
    rootElt_mulVec (by decide), rootElt_mulVec (by decide), coe_tor]
  funext k
  fin_cases k <;> simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, hc]
  · field_simp
    ring
  · linear_combination (-(c⁻¹ * v 1)) * (CharTwo.two_eq_zero (R := F))

theorem p01_mul_p01 : (p01 : SL3 F) * p01 = 1 := by
  rw [← mul_inv_cancel (p01 : SL3 F), p01_inv]

theorem rootElt10_eq (d : F) : rootElt 1 0 d = p01 * (rootElt 0 1 d * p01) := by
  have h := p01_conj (F := F) 0 1 d
  rw [p01_inv, Equiv.swap_apply_left, Equiv.swap_apply_right] at h
  rw [← mul_assoc, h]

section Points

variable [Finite F] [Finite V]
  (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
  (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ≤ Nat.card F)
include h𝒲 hR

theorem inf_map_rootElt01_p01 (a : F) :
    G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ⊓
        (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map
          (ρ (rootElt 0 1 a * p01)).toMonoidHom =
      G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ⊓
        (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom := by
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  have hx : ∀ v ∈ R, ρ (rootElt 0 1 a) v = v := fun v hv =>
    rootElt_fix_R h𝒲 hR (by decide) a hv
  rw [map_rho_mul]
  calc R ⊓ (R.map (ρ p01).toMonoidHom).map (ρ (rootElt 0 1 a)).toMonoidHom
      = R.map (ρ (rootElt 0 1 a)).toMonoidHom ⊓
          (R.map (ρ p01).toMonoidHom).map (ρ (rootElt 0 1 a)).toMonoidHom := by
        rw [map_eq_of_fix hx]
    _ = (R ⊓ R.map (ρ p01).toMonoidHom).map (ρ (rootElt 0 1 a)).toMonoidHom :=
        (map_rho_inf _ _ _).symm
    _ = R ⊓ R.map (ρ p01).toMonoidHom := map_eq_of_fix fun v hv => hx v hv.1

theorem inf_map_rootElt01_p01_of_ne {a b : F} (hab : a ≠ b) :
    (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map
        (ρ (rootElt 0 1 a * p01)).toMonoidHom ⊓
        (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map
          (ρ (rootElt 0 1 b * p01)).toMonoidHom =
      G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ⊓
        (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom := by
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  set c := b - a with hcdef
  have hc : c ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have e1 : rootElt 0 1 b * p01 = rootElt 0 1 a * (rootElt 0 1 c * p01) := by
    rw [← mul_assoc, ← rootElt_add, hcdef, add_sub_cancel]
  have hB : (tor c c⁻¹ hc (inv_ne_zero hc) * rootElt 0 1 c⁻¹ : SL3 F) ∈
      (ptStab : Subgroup (SL3 F)) ⊓ lnStab :=
    ⟨Subgroup.mul_mem _ (tor_mem_ptStab _ _ _ _) (rootElt_mem_ptStab (by decide) _),
      Subgroup.mul_mem _ (tor_mem_lnStab _ _ _ _) (rootElt_mem_lnStab (by decide) _)⟩
  have e3 : R.map (ρ (rootElt 0 1 c * p01)).toMonoidHom =
      (R.map (ρ (rootElt 0 1 c⁻¹ * p01)).toMonoidHom).map (ρ p01).toMonoidHom := by
    rw [rootElt01_mul_p01 hc, map_rho_mul, map_commOn02_eq h𝒲 hB.1 hB.2, rootElt10_eq,
      map_rho_mul]
  have key : R.map (ρ p01).toMonoidHom ⊓ R.map (ρ (rootElt 0 1 c * p01)).toMonoidHom =
      R ⊓ R.map (ρ p01).toMonoidHom := by
    rw [e3, ← map_rho_inf, inf_map_rootElt01_p01 (ρ := ρ) (𝒲 := 𝒲) h𝒲 hR, map_rho_inf,
      ← map_rho_mul,
      p01_mul_p01, map_rho_one, inf_comm]
  have hJ : ∀ v ∈ R ⊓ R.map (ρ p01).toMonoidHom, ρ (rootElt 0 1 a) v = v := fun v hv =>
    rootElt_fix_R h𝒲 hR (by decide) a hv.1
  rw [e1, map_rho_mul ρ R (rootElt 0 1 a), map_rho_mul ρ R (rootElt 0 1 a), ← map_rho_inf,
    key, map_eq_of_fix hJ]

theorem caseN_inf_eq_bot
    (hN : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ≠
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom) :
    G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ⊓
        (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom = ⊥ ∧
      Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) = Nat.card F := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  set R₁ := R.map (ρ p01).toMonoidHom with hR₁
  set C₀ := G6.commOn ((qLn : Subgroup (SL3 F)).map ρ) 𝒲 with hC₀def
  have hC₀ : C₀ = R ⊔ R₁ := by rw [hC₀def, commOnU_eq h𝒲, hR₁, map_commOn02_p01 h𝒲]
  have hRC : R ≤ C₀ := hC₀ ▸ le_sup_left
  let S : Option F → Subgroup V := fun o => o.elim R fun a =>
    R.map (ρ (rootElt 0 1 a * p01)).toMonoidHom
  have hcard_map : ∀ g : SL3 F, Nat.card ↥(R.map (ρ g).toMonoidHom) = Nat.card R := fun g =>
    Subgroup.card_map_of_injective (ρ g).injective
  have hSC : ∀ o, S o ≤ C₀ := by
    rintro (_ | a)
    · exact hRC
    · have hg : rootElt 0 1 a * p01 ∈ (lnStab : Subgroup (SL3 F)) :=
        Subgroup.mul_mem _ (rootElt_mem_lnStab (by decide) a) p01_mem_lnStab
      change R.map (ρ (rootElt 0 1 a * p01)).toMonoidHom ≤ C₀
      refine (Subgroup.map_mono hRC).trans ?_
      rw [hC₀def, map_commOnU_eq h𝒲 hg]
  have hJS : ∀ o, R ⊓ R₁ ≤ S o := by
    rintro (_ | a)
    · exact inf_le_left
    · change R ⊓ R₁ ≤ R.map (ρ (rootElt 0 1 a * p01)).toMonoidHom
      rw [← inf_map_rootElt01_p01 (ρ := ρ) (𝒲 := 𝒲) h𝒲 hR a]
      exact inf_le_right
  have hSS : ∀ o o', o ≠ o' → S o ⊓ S o' = R ⊓ R₁ := by
    rintro (_ | a) (_ | b) hne
    · exact absurd rfl hne
    · exact inf_map_rootElt01_p01 (ρ := ρ) (𝒲 := 𝒲) h𝒲 hR b
    · change R.map (ρ (rootElt 0 1 a * p01)).toMonoidHom ⊓ R = R ⊓ R₁
      rw [inf_comm]
      exact inf_map_rootElt01_p01 (ρ := ρ) (𝒲 := 𝒲) h𝒲 hR a
    · exact inf_map_rootElt01_p01_of_ne h𝒲 hR (fun h => hne (congrArg some h))
  have hr : ∀ o, Nat.card (S o) = Nat.card R := by
    rintro (_ | a)
    · rfl
    · exact hcard_map _
  have hcount := card_spread_le C₀ (R ⊓ R₁) S (inf_le_left.trans hRC) hSC hJS hSS _ hr
  rw [Fintype.card_option] at hcount
  have hprod : Nat.card C₀ * Nat.card ↥(R ⊓ R₁) = Nat.card R * Nat.card R := by
    rw [hC₀, card_sup_mul_card_inf, hR₁, hcard_map]
  have hj1 : 1 ≤ Nat.card ↥(R ⊓ R₁) := Nat.card_pos
  have hjr : Nat.card ↥(R ⊓ R₁) < Nat.card R := by
    refine lt_of_le_of_ne (Subgroup.card_le_of_le inf_le_left) fun h => hN ?_
    have h1 : R ⊓ R₁ = R := Subgroup.eq_of_le_of_card_ge inf_le_left h.ge
    have h2 : R ⊓ R₁ = R₁ := Subgroup.eq_of_le_of_card_ge inf_le_right
      (by rw [hR₁, hcard_map, ← h])
    rw [← h1, h2]
  rw [← Nat.card_eq_fintype_card] at hcount
  obtain ⟨hj, hrq⟩ := arith_spread hj1 hjr hR hprod hcount
  exact ⟨Subgroup.eq_bot_of_card_eq _ hj, hrq⟩

end Points

end CharTwo

end CFSG.Quasithin.MS93.M16
