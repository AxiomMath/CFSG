module

public import CFSG.Quasithin.MS93.M16Spr

public section

namespace CFSG.Quasithin.MS93.M16

open CFSG.Quasithin Matrix

variable {F : Type} [Field F] {V : Type*} [CommGroup V]

section CharTwo

variable [CharP F 2]

theorem conj_rootElt01_rootElt20 (s : F) :
    rootElt 0 1 s * rootElt 2 0 1 * (rootElt 0 1 s)⁻¹ = rootElt 2 0 1 * rootElt 2 1 s := by
  refine sl3_ext fun v => ?_
  rw [conj_mulVec, coe_mul_mulVec, ← rootElt_neg, rootElt_mulVec (by decide),
    rootElt_mulVec (by decide), rootElt_mulVec (by decide), rootElt_mulVec (by decide),
    rootElt_mulVec (by decide)]
  funext k
  fin_cases k <;> simp [CharTwo.neg_eq] <;> ring_nf
  simp [CharTwo.two_eq_zero]

theorem conj_rootElt10_rootElt21 (s : F) :
    rootElt 1 0 s * rootElt 2 1 1 * (rootElt 1 0 s)⁻¹ = rootElt 2 1 1 * rootElt 2 0 s := by
  refine sl3_ext fun v => ?_
  rw [conj_mulVec, coe_mul_mulVec, ← rootElt_neg, rootElt_mulVec (by decide),
    rootElt_mulVec (by decide), rootElt_mulVec (by decide), rootElt_mulVec (by decide),
    rootElt_mulVec (by decide)]
  funext k
  fin_cases k <;> simp [CharTwo.neg_eq] <;> ring_nf
  simp [CharTwo.two_eq_zero]

theorem p02_conj_eq {i j : Fin 3} {c : F} :
    rootElt (Equiv.swap 0 2 i) (Equiv.swap 0 2 j) c = p02 * rootElt i j c * p02 := by
  rw [← p02_conj, p02_inv]

theorem p02_mul_p02 : (p02 : SL3 F) * p02 = 1 := by
  rw [← mul_inv_cancel (p02 : SL3 F), p02_inv]

omit [CharP F 2] in
theorem qPt_le_ptLevi : (qPt : Subgroup (SL3 F)) ≤ ptLevi :=
  sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left))
    (le_sup_right.trans (le_sup_left.trans le_sup_left))

end CharTwo

section Rec

variable [CharP F 2] {ρ : SL3 F →* MulAut V} {𝒲 : Subgroup V} [Finite F] [Finite V]
  (h𝒲 : ∀ g ∈ (lnStab : Subgroup (SL3 F)), ∀ v ∈ 𝒲, ρ g v ∈ 𝒲)
  (hR : Nat.card ↥(G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲) ≤ Nat.card F)
  (hN : G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 ≠
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p01).toMonoidHom)
  (hW2 : ∀ r ∈ G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲, ρ cyc r ∈ 𝒲)
  (hV : ∀ v : V, v ^ 2 = 1)
include h𝒲 hR hN hW2 hV

theorem comm_qPt02_mem {x : SL3 F} (hx : x ∈ (qPt : Subgroup (SL3 F))) {v : V}
    (hv : v ∈ G6.submoduleClosure ρ.range
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)) :
    ρ (p02 * x * p02) v * v⁻¹ ∈
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map (ρ p02).toMonoidHom := by
  have h := comm_qPt_mem h𝒲 hR hN hW2 hV hx (rho_mem_submoduleClosure p02 hv)
  have e1 : ρ p02 (ρ x (ρ p02 v)) = ρ (p02 * x * p02) v := by rw [rho_mul, rho_mul]
  have e2 : ρ p02 (ρ p02 v) = v := by rw [← rho_mul, p02_mul_p02, map_one, MulAut.one_apply]
  have he : ρ (p02 * x * p02) v * v⁻¹ = ρ p02 (ρ x (ρ p02 v) * (ρ p02 v)⁻¹) := by
    rw [map_mul (ρ p02), map_inv (ρ p02), e1, e2]
  rw [he]
  exact rho_mem_map_rho _ h

omit hV in
theorem qPt02_fix {x : SL3 F} (hx : x ∈ (qPt : Subgroup (SL3 F))) {y : V}
    (hy : y ∈ (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲).map
      (ρ p02).toMonoidHom) :
    ρ (p02 * x * p02) y = y := by
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
  change ρ (p02 * x * p02) (ρ p02 r) = ρ p02 r
  exact rho_conj_fix (by rw [p02_inv]) (ptLevi_fix_R h𝒲 hR hN hW2 (qPt_le_ptLevi hx) hr)

theorem fix_of_lnLevi_fix {v : V}
    (hv : v ∈ G6.submoduleClosure ρ.range
      (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲))
    (hfix : ∀ g ∈ (lnLevi : Subgroup (SL3 F)), ρ g v = v) : v ∈ fixV ρ.range := by
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  have hY : ∀ {x : SL3 F}, x ∈ (qPt : Subgroup (SL3 F)) →
      ρ (p02 * x * p02) v * v⁻¹ ∈ R.map (ρ p02).toMonoidHom := fun hx =>
    comm_qPt02_mem h𝒲 hR hN hW2 hV hx hv
  have hfixY : ∀ {x : SL3 F}, x ∈ (qPt : Subgroup (SL3 F)) → ∀ y ∈ R.map (ρ p02).toMonoidHom,
      ρ (p02 * x * p02) y = y := fun hx y hy => qPt02_fix h𝒲 hR hN hW2 hx hy
  have hl01 : ∀ (s : F), ∀ y ∈ R.map (ρ p02).toMonoidHom, ρ (rootElt 0 1 s) y = y := by
    intro s y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    have he : rootElt 0 1 s = p02 * rootElt 2 1 s * p02 := by
      rw [← p02_conj_eq]; rfl
    exact rho_conj_fix (by rw [p02_inv]; exact he)
      (ptLevi_fix_R h𝒲 hR hN hW2 (rootGroup_le_ptLevi (by decide)
        (rootElt_mem_rootGroup 2 1 s)) hr)
  have hl10 : ∀ (s : F), ∀ y ∈ R.map (ρ p02).toMonoidHom, ρ (rootElt 1 0 s) y = y := by
    intro s y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    have he : rootElt 1 0 s = p02 * rootElt 1 2 s * p02 := by
      rw [← p02_conj_eq]; rfl
    exact rho_conj_fix (by rw [p02_inv]; exact he)
      (ptLevi_fix_R h𝒲 hR hN hW2 (rootGroup_le_ptLevi (by decide)
        (rootElt_mem_rootGroup 1 2 s)) hr)
  have h20 : ∀ c : F, rootElt 2 0 c = p02 * rootElt 0 2 c * p02 := fun c => by
    rw [← p02_conj_eq]; rfl
  have h21 : ∀ c : F, rootElt 2 1 c = p02 * rootElt 0 1 c * p02 := fun c => by
    rw [← p02_conj_eq]; rfl
  have hq02 : ∀ c : F, rootElt 0 2 c ∈ (qPt : Subgroup (SL3 F)) := fun c =>
    Subgroup.mem_sup_right (rootElt_mem_rootGroup 0 2 c)
  have hq01 : ∀ c : F, rootElt 0 1 c ∈ (qPt : Subgroup (SL3 F)) := fun c =>
    Subgroup.mem_sup_left (rootElt_mem_rootGroup 0 1 c)
  have hlnl : ∀ {i j : Fin 3} (c : F), ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2) ∨
      (i = 1 ∧ j = 2)) → rootElt i j c ∈ (lnLevi : Subgroup (SL3 F)) := by
    intro i j c h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (show (rootGroup 0 1 : Subgroup (SL3 F)) ≤ lnLevi from
        le_sup_left.trans (le_sup_left.trans le_sup_left)) (rootElt_mem_rootGroup 0 1 c)
    · exact (show (rootGroup 1 0 : Subgroup (SL3 F)) ≤ lnLevi from
        le_sup_right.trans (le_sup_left.trans le_sup_left)) (rootElt_mem_rootGroup 1 0 c)
    · exact (show (rootGroup 0 2 : Subgroup (SL3 F)) ≤ lnLevi from
        le_sup_right.trans le_sup_left) (rootElt_mem_rootGroup 0 2 c)
    · exact (show (rootGroup 1 2 : Subgroup (SL3 F)) ≤ lnLevi from
        le_sup_right) (rootElt_mem_rootGroup 1 2 c)
  have hv21 : ∀ s : F, ρ (rootElt 2 1 s) v = v := by
    intro s
    set a := ρ (rootElt 2 0 1) v * v⁻¹ with ha
    have haY : a ∈ R.map (ρ p02).toMonoidHom := by rw [ha, h20]; exact hY (hq02 1)
    set b := ρ (rootElt 2 1 s) v * v⁻¹ with hb
    have hbY : b ∈ R.map (ρ p02).toMonoidHom := by rw [hb, h21]; exact hY (hq01 s)
    have e1 : ρ (rootElt 2 0 1 * rootElt 2 1 s) v = ρ (rootElt 2 0 1) v := by
      rw [← conj_rootElt01_rootElt20, rho_mul, rho_mul,
        hfix _ (inv_mem (hlnl s (Or.inl ⟨rfl, rfl⟩))),
        show ρ (rootElt 2 0 1) v = a * v by rw [ha, inv_mul_cancel_right], map_mul,
        hl01 s a haY, hfix _ (hlnl s (Or.inl ⟨rfl, rfl⟩))]
    have e2 : ρ (rootElt 2 0 1 * rootElt 2 1 s) v = b * ρ (rootElt 2 0 1) v := by
      rw [rho_mul, show ρ (rootElt 2 1 s) v = b * v by rw [hb, inv_mul_cancel_right], map_mul,
        h20 1, hfixY (hq02 1) b hbY]
    rw [e1] at e2
    have hb1 : b = 1 := by
      have := congrArg (· * (ρ (rootElt 2 0 1) v)⁻¹) e2
      simpa using this.symm
    rw [hb, mul_inv_eq_one] at hb1
    exact hb1
  have hv20 : ∀ s : F, ρ (rootElt 2 0 s) v = v := by
    intro s
    set a := ρ (rootElt 2 1 1) v * v⁻¹ with ha
    have haY : a ∈ R.map (ρ p02).toMonoidHom := by rw [ha, h21]; exact hY (hq01 1)
    set b := ρ (rootElt 2 0 s) v * v⁻¹ with hb
    have hbY : b ∈ R.map (ρ p02).toMonoidHom := by rw [hb, h20]; exact hY (hq02 s)
    have e1 : ρ (rootElt 2 1 1 * rootElt 2 0 s) v = ρ (rootElt 2 1 1) v := by
      rw [← conj_rootElt10_rootElt21, rho_mul, rho_mul,
        hfix _ (inv_mem (hlnl s (Or.inr (Or.inl ⟨rfl, rfl⟩)))),
        show ρ (rootElt 2 1 1) v = a * v by rw [ha, inv_mul_cancel_right], map_mul,
        hl10 s a haY, hfix _ (hlnl s (Or.inr (Or.inl ⟨rfl, rfl⟩)))]
    have e2 : ρ (rootElt 2 1 1 * rootElt 2 0 s) v = b * ρ (rootElt 2 1 1) v := by
      rw [rho_mul, show ρ (rootElt 2 0 s) v = b * v by rw [hb, inv_mul_cancel_right], map_mul,
        h21 1, hfixY (hq01 1) b hbY]
    rw [e1] at e2
    have hb1 : b = 1 := by
      have := congrArg (· * (ρ (rootElt 2 1 1) v)⁻¹) e2
      simpa using this.symm
    rw [hb, mul_inv_eq_one] at hb1
    exact hb1
  have htop : fixer ρ (Subgroup.zpowers v) = ⊤ := by
    refine eq_top_of_rootElt_mem fun i j c hij => ?_
    have hv' : ρ (rootElt i j c) v = v := by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact hfix _ (hlnl c (Or.inl ⟨rfl, rfl⟩))
      · exact hfix _ (hlnl c (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      · exact hfix _ (hlnl c (Or.inr (Or.inl ⟨rfl, rfl⟩)))
      · exact absurd rfl hij
      · exact hfix _ (hlnl c (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
      · exact hv20 c
      · exact hv21 c
      · exact absurd rfl hij
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [map_zpow, hv']
  rw [mem_fixV_range]
  intro g
  exact (htop ▸ Subgroup.mem_top g : g ∈ fixer ρ (Subgroup.zpowers v)) v
    (Subgroup.mem_zpowers v)

theorem natEquiv_of_caseN (hfixV : fixV ρ.range = ⊥) :
    ∃ β : ↥(G6.submoduleClosure ρ.range
        (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲)) ≃*
        Multiplicative (Fin 3 → F),
      ∀ (g : SL3 F) (v w : ↥(G6.submoduleClosure ρ.range
          (G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲))), (w : V) = ρ g v →
        Multiplicative.toAdd (β w) =
          ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (β v) := by
  set R := G6.commOn ((rootGroup 0 2 : Subgroup (SL3 F)).map ρ) 𝒲 with hRdef
  set N := G6.submoduleClosure ρ.range R with hNdef
  have hcardR : Nat.card ↥R = Nat.card F := (caseN_inf_eq_bot h𝒲 hR hN).2
  have hRbot : R ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardR
    have : 1 < Nat.card F := Finite.one_lt_card
    omega
  obtain ⟨⟨w₀', hw₀R⟩, hw₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hRbot
  replace hw₀ : w₀' ≠ 1 := fun h => hw₀ (Subtype.ext h)
  set N₂ := Subgroup.closure (Set.range fun g : SL3 F => ρ g w₀') with hN₂
  have hN₂inv : ∀ g : SL3 F, ∀ v ∈ N₂, ρ g v ∈ N₂ := by
    intro g v hv
    induction hv using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact Subgroup.subset_closure ⟨g * k, rho_mul ρ g k w₀'⟩
    | one => simp
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  have hw₀N : w₀' ∈ N := le_submoduleClosure R hw₀R
  have hN₂le : N₂ ≤ N := by
    rw [hN₂, Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    exact rho_mem_submoduleClosure g hw₀N
  have hw₂mem : w₀' ∈ N₂ := Subgroup.subset_closure ⟨1, by simp⟩
  set ρ₂ := restr ρ N₂ hN₂inv with hρ₂
  set w₂ : ↥N₂ := ⟨w₀', hw₂mem⟩ with hw₂
  obtain ⟨β₂, hβ₂, -⟩ := exists_natEquiv_of_vecStab ρ₂ w₂
    (fun h => hw₀ (congrArg Subtype.val h))
    (fun g hg => Subtype.ext (ptLevi_fix_R h𝒲 hR hN hW2 hg hw₀R))
    (fun a ha a' ha' v => Subtype.ext (by
      change ρ a' (ρ a v * (v : V)⁻¹) = ρ a v * (v : V)⁻¹
      have hq : ρ a v * (v : V)⁻¹ ∈ R := comm_qPt_mem h𝒲 hR hN hW2 hV
        (Subgroup.mem_sup_left ha) (hN₂le v.2)
      exact ptLevi_fix_R h𝒲 hR hN hW2 (qPt_le_ptLevi (Subgroup.mem_sup_left ha')) hq))
    (fun v hv => by
      have h := fix_of_lnLevi_fix h𝒲 hR hN hW2 hV (hN₂le v.2)
        (fun g hg => congrArg Subtype.val (hv g hg))
      rw [hfixV, Subgroup.mem_bot] at h
      exact Subtype.ext h)
    (by
      have h := Subgroup.closure_closure_coe_preimage (k := Set.range fun g : SL3 F => ρ g w₀')
      rw [← h]
      congr 1
      ext x
      simp only [Set.mem_range, Set.mem_preimage]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, rfl⟩
      · rintro ⟨g, hg⟩
        exact ⟨g, Subtype.ext hg⟩)
  have hcard₂ : Nat.card N₂ = Nat.card F ^ 3 := by
    rw [Nat.card_congr β₂.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin]
  have hNN : N₂ = N := Subgroup.eq_of_le_of_card_ge hN₂le
    (by rw [hcard₂]; exact card_closure_le h𝒲 hR hN hW2)
  refine ⟨(MulEquiv.subgroupCongr hNN.symm).trans β₂, fun g v w hvw => ?_⟩
  have hw : (MulEquiv.subgroupCongr hNN.symm) w = ρ₂ g ((MulEquiv.subgroupCongr hNN.symm) v) :=
    Subtype.ext (by
      change (w : V) = ρ g v
      exact hvw)
  simp only [MulEquiv.trans_apply]
  rw [hw, hβ₂]

end Rec

end CFSG.Quasithin.MS93.M16
