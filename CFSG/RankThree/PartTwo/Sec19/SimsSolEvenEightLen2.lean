module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenEightP
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry CFSG.CGT.PushingUpLit.SolK
  CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

namespace Eight

section Bar

theorem barLen_mem_of_mem_heart {v : permBar 8}
    (hv : v ∈ (heartToBar : altHeart 8 →+ permBar 8).range) :
    barLen v = 0 ∨ barLen v = 2 ∨ barLen v = 4 := by
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [heartToBar_mk, barLen_mk]
  have hsum : ∑ i, (x : Fin 8 → ZMod 2) i = 0 := by
    simpa [evenWeight, AddMonoidHom.mem_ker] using x.2
  obtain ⟨k, hk⟩ := even_vecWt_of_sum_eq_zero hsum
  have hle := vecWt_le (x : Fin 8 → ZMod 2)
  omega

theorem card_heart_eight : Nat.card ↥(heartToBar : altHeart 8 →+ permBar 8).range = 2 ^ 6 := by
  rw [← CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_altHeart_even (n := 8) (by norm_num)
    (by decide)]
  exact Nat.card_congr (Equiv.ofInjective _ heartToBar_injective).symm

theorem card_le_two_mul_inf_heart (V : AddSubgroup (permBar 8)) :
    Nat.card V ≤ 2 * Nat.card ↥(V ⊓ (heartToBar : altHeart 8 →+ permBar 8).range) := by
  classical
  set U := (heartToBar : altHeart 8 →+ permBar 8).range with hU
  have hmemU : ∀ w : permBar 8, w ∈ U ↔ w ∈ Set.range (heartToBar (n := 8)) := fun w =>
    AddMonoidHom.mem_range
  by_cases hV : V ≤ U
  · rw [inf_eq_left.2 hV]
    omega
  obtain ⟨z₀, hz₀V, hz₀U⟩ := Set.not_subset.1 hV
  let f : ↥V → ↥(V ⊓ U) × Bool := fun z =>
    if hz : (z : permBar 8) ∈ U then (⟨z, AddSubgroup.mem_inf.2 ⟨z.2, hz⟩⟩, false)
    else (⟨z + z₀, AddSubgroup.mem_inf.2 ⟨V.add_mem z.2 hz₀V, (hmemU _).2
      (add_mem_range_heartToBar (fun h => hz ((hmemU _).2 h))
        (fun h => hz₀U ((hmemU _).2 h)))⟩⟩, true)
  have hf : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    by_cases ha : (a : permBar 8) ∈ U <;> by_cases hb : (b : permBar 8) ∈ U <;>
      simp only [ha, hb, dif_pos, dif_neg, not_false_eq_true, Prod.mk.injEq, Subtype.mk.injEq,
        reduceCtorEq, and_false, and_true] at hab
    · exact Subtype.ext hab
    · exact Subtype.ext (add_right_cancel hab)
  have h5 := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h5
  omega

theorem card_le_of_no_len_four (V : AddSubgroup (permBar 8)) (hV : ∀ v ∈ V, barLen v ≠ 4) :
    Nat.card V ≤ 8 ∧ (V ≤ (heartToBar : altHeart 8 →+ permBar 8).range → Nat.card V ≤ 4) := by
  set U := (heartToBar : altHeart 8 →+ permBar 8).range with hU
  have h4 : Nat.card ↥(V ⊓ U) ≤ 4 := by
    refine Comb.card_le_four_of_len_two (by norm_num) (V ⊓ U) fun v hv hv0 => ?_
    obtain ⟨hvV, hvU⟩ := AddSubgroup.mem_inf.1 hv
    rcases barLen_mem_of_mem_heart hvU with h | h | h
    · exact absurd (eq_zero_of_barLen_eq_zero h) hv0
    · exact h
    · exact absurd h (hV v hvV)
  have h2 : Nat.card V ≤ 2 * Nat.card ↥(V ⊓ U) := card_le_two_mul_inf_heart V
  refine ⟨by omega, fun hVU => ?_⟩
  rw [← inf_eq_left.2 hVU]
  exact h4

end Bar

section Group

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 8} (D : C.PiData)

theorem not_swap_two {J : Finset (Fin 8)} (hJ : J.card = 2) {σ : Perm (Fin 8)}
    (h : ∀ y, σ y ∈ J ↔ y ∉ J) : False := by
  have h1 : Jᶜ.card ≤ J.card := by
    refine Finset.card_le_card_of_injOn σ (fun y hy => ?_) σ.injective.injOn
    simp only [Finset.mem_coe, Finset.mem_compl] at hy ⊢
    exact (h y).2 hy
  rw [Finset.card_compl, Fintype.card_fin, hJ] at h1
  omega

theorem theta_TOf_len_two {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {a b : Fin 8} (hab : a ≠ b)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {a, b}) {t : ↥M}
    (ht : (t : G) ∈ TOf M x) : C.θ t = 1 ∨ C.θ t = swap a b := by
  have hJ : ({a, b} : Finset (Fin 8)).card = 2 := Finset.card_pair hab
  have hstab : C.thetaN x ≤ setStab {a, b} := by
    intro σ hσ
    obtain ⟨s, hsT, rfl⟩ := C.mem_thetaN.1 hσ
    rcases theta_stab_or_swap D hx hπ (TOf_le_C M x hsT) with h | h
    · exact h
    · exact (not_swap_two hJ h).elim
  have hfix := block_fixes (C.isPGroup_thetaN x)
    (fun σ hσ => setStab_le_compl _ (hstab hσ))
    (thetaN_normalized D hx hπ (Or.inr rfl))
    (by rw [Finset.card_compl, Fintype.card_fin, hJ]; omega)
  have hσ : C.θ t ∈ C.thetaN x := C.mem_thetaN.2 ⟨t, ht, rfl⟩
  have hfixc : ∀ y, y ∉ ({a, b} : Finset (Fin 8)) → C.θ t y = y := fun y hy =>
    hfix _ hσ y (Finset.mem_compl.2 hy)
  have hmem := mem_setStab.1 (hstab hσ)
  have ha : C.θ t a = a ∨ C.θ t a = b := by
    have := (hmem a).2 (by simp)
    simpa using this
  rcases ha with ha | ha
  · left
    have hb : C.θ t b = b := by
      have := (hmem b).2 (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact absurd ((C.θ t).injective (h.trans ha.symm)) (Ne.symm hab)
      · exact h
    refine Equiv.ext fun y => ?_
    by_cases hy : y ∈ ({a, b} : Finset (Fin 8))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
    · exact hfixc y hy
  · right
    have hb : C.θ t b = a := by
      have := (hmem b).2 (by simp)
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h | h
      · exact h
      · exact absurd ((C.θ t).injective (h.trans ha.symm)) hab.symm
    refine Equiv.ext fun y => ?_
    by_cases hy : y ∈ ({a, b} : Finset (Fin 8))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · rw [ha, swap_apply_left]
      · rw [hb, swap_apply_right]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      rw [hfixc y (by simp [hy.1, hy.2]), swap_apply_of_ne_of_ne hy.1 hy.2]

theorem barInd_add_barInd {n : ℕ} (A B : Finset (Fin n)) :
    barInd A + barInd B = barInd (symmDiff A B) := by
  unfold barInd
  rw [← QuotientAddGroup.mk_add]
  congr 1
  funext i
  simp only [Pi.add_apply, indVec, Finset.mem_symmDiff]
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]
  rfl

theorem comm_mul_comm (C' : Cfg G M X 8) (hR : Nat.card ↥(Rc X) ≤ 2) {t q₁ q₂ : G} (ht : t ∈ M)
    (h₁ : q₁ ∈ CFSG.Open.pCoreOf 2 M) (h₂ : q₂ ∈ CFSG.Open.pCoreOf 2 M) :
    t * (q₁ * q₂) * t⁻¹ * (q₁ * q₂)⁻¹ = (t * q₁ * t⁻¹ * q₁⁻¹) * (t * q₂ * t⁻¹ * q₂⁻¹) := by
  have hQ := C'.Q_comm hR
  have h1 : t * q₁ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M ht h₁
  have h2 : t * q₂ * t⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M ht h₂
  have c1 : (t * q₂ * t⁻¹) * q₁⁻¹ = q₁⁻¹ * (t * q₂ * t⁻¹) :=
    hQ _ h2 _ ((CFSG.Open.pCoreOf 2 M).inv_mem h₁)
  have c2 : q₂⁻¹ * q₁⁻¹ = q₁⁻¹ * q₂⁻¹ :=
    hQ _ ((CFSG.Open.pCoreOf 2 M).inv_mem h₂) _ ((CFSG.Open.pCoreOf 2 M).inv_mem h₁)
  calc t * (q₁ * q₂) * t⁻¹ * (q₁ * q₂)⁻¹
      = (t * q₁ * t⁻¹) * (t * q₂ * t⁻¹) * (q₂⁻¹ * q₁⁻¹) := by group
    _ = (t * q₁ * t⁻¹) * ((t * q₂ * t⁻¹) * q₁⁻¹) * q₂⁻¹ := by rw [c2]; group
    _ = (t * q₁ * t⁻¹) * (q₁⁻¹ * (t * q₂ * t⁻¹)) * q₂⁻¹ := by rw [c1]
    _ = (t * q₁ * t⁻¹ * q₁⁻¹) * (t * q₂ * t⁻¹ * q₂⁻¹) := by group

theorem exists_comm_len_four (hR : Nat.card ↥(Rc X) ≤ 2) {a b : Fin 8} (hab : a ≠ b) {t : ↥M}
    (ht : C.θ t = swap a b) :
    ∃ y : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ y)) = 4 ∧
      (t : G) * y = y * t := by
  classical
  set J : Finset (Fin 8) := {a, b} with hJ
  have hJc : Jᶜ.card = 6 := by rw [Finset.card_compl, Fintype.card_fin, hJ, Finset.card_pair hab]
  obtain ⟨A₁, hA₁J, hA₁⟩ := Finset.exists_subset_card_eq (s := Jᶜ) (n := 4) (by omega)
  obtain ⟨Cp, hCA, hC⟩ := Finset.exists_subset_card_eq (s := A₁) (n := 2) (by omega)
  set B : Finset (Fin 8) := Jᶜ \ A₁ with hB
  have hBc : B.card = 2 := by rw [hB, Finset.card_sdiff_of_subset hA₁J, hJc, hA₁]
  set A₂ : Finset (Fin 8) := Cp ∪ B with hA₂
  set A₃ : Finset (Fin 8) := (A₁ \ Cp) ∪ B with hA₃
  have hdisjB : ∀ S : Finset (Fin 8), S ⊆ A₁ → Disjoint S B := fun S hS =>
    Finset.disjoint_left.2 fun y hy hyB => (Finset.mem_sdiff.1 hyB).2 (hS hy)
  have hA₂c : A₂.card = 4 := by rw [hA₂, Finset.card_union_of_disjoint (hdisjB Cp hCA), hC, hBc]
  have hA₃c : A₃.card = 4 := by
    rw [hA₃, Finset.card_union_of_disjoint (hdisjB _ Finset.sdiff_subset),
      Finset.card_sdiff_of_subset hCA, hA₁, hC, hBc]
  have hsymm : symmDiff A₁ A₂ = A₃ := by
    ext y
    simp only [Finset.mem_symmDiff, hA₂, hA₃, Finset.mem_union, Finset.mem_sdiff, hB]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · push Not at h2
        exact Or.inl ⟨h1, h2.1⟩
      · rcases h1 with h1 | h1
        · exact absurd (hCA h1) h2
        · exact Or.inr h1
    · rintro (⟨h1, h2⟩ | h1)
      · refine Or.inl ⟨h1, ?_⟩
        push Not
        exact ⟨h2, fun _ => h1⟩
      · exact Or.inr ⟨Or.inr h1, h1.2⟩
  have heven : ∀ A : Finset (Fin 8), A.card = 4 →
      barInd A ∈ (heartToBar : altHeart 8 →+ permBar 8).range := fun A hA =>
    Comb.barVec_mem_range_heartToBar (by decide) (by rw [hA]; decide)
  obtain ⟨q₁, hq₁⟩ := exists_piQ_eq_of_heart D (heven A₁ hA₁)
  obtain ⟨q₂, hq₂⟩ := exists_piQ_eq_of_heart D (heven A₂ hA₂c)
  have hsub : ∀ A : Finset (Fin 8), A ⊆ Jᶜ → A.image (swap a b) = A := by
    intro A hA
    refine (image_eq_iff_mem_setStab _ A).2 fun y => ?_
    by_cases hya : y = a
    · subst hya
      have : y ∉ A := fun h => (Finset.mem_compl.1 (hA h)) (by simp [hJ])
      have h2 : b ∉ A := fun h => (Finset.mem_compl.1 (hA h)) (by simp [hJ])
      rw [swap_apply_left]
      exact iff_of_false h2 this
    by_cases hyb : y = b
    · subst hyb
      have : y ∉ A := fun h => (Finset.mem_compl.1 (hA h)) (by simp [hJ])
      have h2 : a ∉ A := fun h => (Finset.mem_compl.1 (hA h)) (by simp [hJ])
      rw [swap_apply_right]
      exact iff_of_false h2 this
    · rw [swap_apply_of_ne_of_ne hya hyb]
  have hA₂J : A₂ ⊆ Jᶜ := Finset.union_subset (hCA.trans hA₁J) Finset.sdiff_subset
  have hcomm : ∀ (q : ↥(CFSG.Open.pCoreOf 2 M)) (A : Finset (Fin 8)), A ⊆ Jᶜ →
      Multiplicative.toAdd (D.piQ q) = barInd A →
      (t : G) * q * (t : G)⁻¹ * (q : G)⁻¹ ∈ Rc X := by
    intro q A hA hq
    have htq : (t : G) * q * (t : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M := pCoreOf_normalized M t.2 q.2
    have hmem : (t : G) * q * (t : G)⁻¹ * (q : G)⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
      (CFSG.Open.pCoreOf 2 M).mul_mem htq ((CFSG.Open.pCoreOf 2 M).inv_mem q.2)
    have hc := D.piQ_conj t q ⟨_, htq⟩ rfl
    rw [hq, barAct_barInd, ht, hsub A hA] at hc
    refine (D.piQ_eq_one_iff ⟨_, hmem⟩).1 ?_
    have e : (⟨(t : G) * q * (t : G)⁻¹ * (q : G)⁻¹, hmem⟩ : ↥(CFSG.Open.pCoreOf 2 M)) =
        ⟨(t : G) * q * (t : G)⁻¹, htq⟩ * q⁻¹ := rfl
    rw [e, map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, hc, hq, add_neg_cancel, toAdd_one]
  have hr₁ := hcomm q₁ A₁ hA₁J hq₁
  have hr₂ := hcomm q₂ A₂ hA₂J hq₂
  have hq₃ : Multiplicative.toAdd (D.piQ (q₁ * q₂)) = barInd A₃ := by
    rw [map_mul, toAdd_mul, hq₁, hq₂, barInd_add_barInd, hsymm]
  have hlen : ∀ (q : ↥(CFSG.Open.pCoreOf 2 M)) (A : Finset (Fin 8)), A.card = 4 →
      Multiplicative.toAdd (D.piQ q) = barInd A → barLen (Multiplicative.toAdd (D.piQ q)) = 4 := by
    intro q A hA hq
    rw [hq, barLen_barInd, hA]
    rfl
  have hcomm_iff : ∀ q : G, (t : G) * q * (t : G)⁻¹ * q⁻¹ = 1 → (t : G) * q = q * t := by
    intro q h
    calc (t : G) * q = ((t : G) * q * (t : G)⁻¹ * q⁻¹) * q * t := by group
      _ = q * t := by rw [h, one_mul]
  have hRmem : ∀ r ∈ Rc X, r = 1 ∨ r ≠ 1 := fun r _ => em _
  by_cases h1 : (t : G) * q₁ * (t : G)⁻¹ * (q₁ : G)⁻¹ = 1
  · exact ⟨q₁, hlen q₁ A₁ hA₁ hq₁, hcomm_iff _ h1⟩
  by_cases h2 : (t : G) * q₂ * (t : G)⁻¹ * (q₂ : G)⁻¹ = 1
  · exact ⟨q₂, hlen q₂ A₂ hA₂c hq₂, hcomm_iff _ h2⟩
  refine ⟨q₁ * q₂, hlen _ A₃ hA₃c hq₃, hcomm_iff _ ?_⟩
  have hne1 : (⟨_, hr₁⟩ : ↥(Rc X)) ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  have hne2 : (⟨_, hr₂⟩ : ↥(Rc X)) ≠ 1 := fun h => h2 (congrArg Subtype.val h)
  have heq := congrArg Subtype.val (eq_of_card_le_two hR hne1 hne2)
  simp only at heq
  have e := comm_mul_comm C hR t.2 q₁.2 q₂.2
  rw [Subgroup.coe_mul, e, ← heq]
  exact Rc_mul_self hR hr₁

theorem barAct_swap_sub {n : ℕ} {a b : Fin n} (hab : a ≠ b) (v : permBar n) :
    barAct (swap a b) v - v = 0 ∨ barAct (swap a b) v - v = barInd {a, b} := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective v
  rw [barAct_mk, ← QuotientAddGroup.mk_sub]
  have hval : ∀ k, (vecPerm (swap a b) z - z) k =
      if k = a ∨ k = b then z b - z a else 0 := by
    intro k
    simp only [Pi.sub_apply, vecPerm_apply, swap_inv]
    by_cases hka : k = a
    · subst hka
      rw [swap_apply_left, if_pos (Or.inl rfl)]
    by_cases hkb : k = b
    · subst hkb
      rw [swap_apply_right, if_pos (Or.inr rfl)]
      have : ∀ s t : ZMod 2, s - t = t - s := by decide
      exact this _ _
    · rw [swap_apply_of_ne_of_ne hka hkb, sub_self, if_neg (by tauto)]
  rcases zmod_two_cases' (z b - z a) with h | h
  · left
    have : vecPerm (swap a b) z - z = 0 := funext fun k => by
      rw [hval k, h]
      split_ifs <;> rfl
    rw [this]
    rfl
  · right
    unfold barInd
    congr 1
    funext k
    rw [hval k, h]
    simp only [indVec, Finset.mem_insert, Finset.mem_singleton]

theorem centralizer_le_M_of_len_two (hR : Nat.card ↥(Rc X) ≤ 2)
    (h37 : ∀ y : ↥(CFSG.Open.pCoreOf 2 M), barLen (Multiplicative.toAdd (D.piQ y)) = 4 →
      ∀ g : G, g * (y : G) * g⁻¹ ∈ CFSG.Open.pCoreOf 2 M → g ∈ M)
    {x : G} (hx : x ∈ CFSG.Open.pCoreOf 2 M) {a b : Fin 8} (hab : a ≠ b)
    (hπ : Multiplicative.toAdd (D.piQ ⟨x, hx⟩) = barInd {a, b}) : CGOf x ≤ M := by
  classical
  by_contra hKM
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  set P := CFSG.Open.pCoreOf 2 (CGOf x) with hPdef
  set T := TOf M x with hTdef
  have hQab := C.Q_comm hR
  have hx1 : x ≠ 1 := by
    intro h
    subst h
    have h1 : D.piQ ⟨1, hx⟩ = 1 := by
      have : (⟨1, hx⟩ : ↥Q) = 1 := rfl
      rw [this, map_one]
    rw [h1, toAdd_one] at hπ
    have h2 := congrArg barLen hπ
    rw [barLen_barInd, Finset.card_pair hab, H4b.barLen_zero'] at h2
    norm_num at h2
  have hPQ := H4b.not_P_le_Q C hR hx hx1 hKM
  set H : Subgroup G := P ⊔ Q with hH
  have hH2 := H4b.isPGroup_sup C hR hx
  have hUT : H ⊓ M ≤ T := H4b.sup_inf_le_TOf C hR hx
  have hQH : Q ≠ H := fun h => hPQ (by
    have h' : P ≤ H := le_sup_left
    rw [← h] at h'
    exact h')
  obtain ⟨t, htH, htQ, htN⟩ := exists_mem_normalizer_of_lt hH2 le_sup_right hQH
  have htM : t ∈ M := by rw [← C.S.normalizer_Q_eq]; exact htN
  have htT : t ∈ T := hUT ⟨htH, htM⟩
  have hKQ : ∀ s (hs : s ∈ M), C.θ ⟨s, hs⟩ = 1 → s ∈ Q := by
    intro s hs h
    have hK : s ∈ C.K := C.mem_K.2 ⟨hs, h⟩
    rwa [C.K_eq_Q hR] at hK
  have hθt : C.θ ⟨t, htM⟩ = swap a b := by
    rcases theta_TOf_len_two D hx hab hπ (t := ⟨t, htM⟩) htT with h | h
    · exact absurd (hKQ t htM h) htQ
    · exact h
  have hTsplit : ∀ s ∈ T, s ∈ Q ∨ t⁻¹ * s ∈ Q := by
    intro s hs
    have hsM : s ∈ M := TOf_le_M M x hs
    rcases theta_TOf_len_two D hx hab hπ (t := ⟨s, hsM⟩) hs with h | h
    · exact Or.inl (hKQ s hsM h)
    · right
      have hM' : t⁻¹ * s ∈ M := M.mul_mem (M.inv_mem htM) hsM
      refine hKQ _ hM' ?_
      have : (⟨t⁻¹ * s, hM'⟩ : ↥M) = (⟨t, htM⟩)⁻¹ * ⟨s, hsM⟩ := rfl
      rw [this, map_mul, map_inv, hθt, h, inv_mul_cancel]
  obtain ⟨y, hy4, hyt⟩ := exists_comm_len_four D hR hab hθt
  have hyZ : ∀ s ∈ T, s * y = y * s := by
    intro s hs
    rcases hTsplit s hs with h | h
    · exact hQab s h y y.2
    · have e : s = t * (t⁻¹ * s) := by group
      rw [e, mul_assoc, hQab _ h y y.2, ← mul_assoc, hyt, mul_assoc]
  have hNT : Subgroup.normalizer (T : Set G) ≤ M := by
    intro g hg
    have hgyQ : g * y * g⁻¹ ∈ Q := by
      refine (C.centralizer_Q_eq hR).le (Subgroup.mem_centralizer_iff.2 ?_)
      intro q hq
      have hqT : q ∈ T := Q_le_TOf hQab hx hq
      have hq' : g⁻¹ * q * g ∈ T := by
        have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) q).1 hqT
        simpa using this
      have hc := hyZ _ hq'
      calc q * (g * y * g⁻¹) = g * ((g⁻¹ * q * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * q * g)) * g⁻¹ := by rw [hc]
        _ = g * y * g⁻¹ * q := by group
    exact h37 y hy4 g hgyQ
  have hTH : T ≤ H := by
    intro s hs
    rcases hTsplit s hs with h | h
    · exact (le_sup_right : Q ≤ H) h
    · have e : s = t * (t⁻¹ * s) := by group
      rw [e]
      exact H.mul_mem htH ((le_sup_right : Q ≤ H) h)
  have hHT : H = T := by
    by_contra hne
    obtain ⟨h, hhH, hhT, hhN⟩ := exists_mem_normalizer_of_lt hH2 hTH (Ne.symm hne)
    exact hhT (hUT ⟨hhH, hNT hhN⟩)
  have hPT : P ≤ T := hHT ▸ le_sup_left
  have hPM : P ≤ M := hPT.trans (TOf_le_M M x)
  obtain ⟨t', ht'P, ht'Q⟩ := Set.not_subset.1 hPQ
  have ht'M : t' ∈ M := hPM ht'P
  have hPsplit : ∀ s ∈ P, s ∈ Q ∨ t'⁻¹ * s ∈ Q := by
    intro s hs
    rcases hTsplit s (hPT hs) with h | h
    · exact Or.inl h
    · right
      rcases hTsplit t' (hPT ht'P) with h' | h'
      · exact absurd h' ht'Q
      · have e : t'⁻¹ * s = (t⁻¹ * t')⁻¹ * (t⁻¹ * s) := by group
        rw [e]
        exact Q.mul_mem (Q.inv_mem h') h
  set CQt : Subgroup G := Q ⊓ Subgroup.centralizer ({t'} : Set G) with hCQt
  have hcons := H4b.twoConstrained_P C hR hx hx1
  have hCQtP : CQt ≤ P := by
    intro q hq
    obtain ⟨hqQ, hqc⟩ := Subgroup.mem_inf.1 hq
    have hqt' : t' * q = q * t' := (Subgroup.mem_centralizer_singleton_iff.1 hqc).symm
    apply hcons
    refine Subgroup.mem_inf.2 ⟨H4b.Q_le_CGOf C hR hx hqQ,
      Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    rcases hPsplit s hs with h | h
    · exact hQab s h q hqQ
    · have e : s = t' * (t'⁻¹ * s) := by group
      rw [e, mul_assoc, hQab _ h q hqQ, ← mul_assoc, hqt', mul_assoc]
  have hcard11 : Nat.card ↥Q ≤ 4 * Nat.card ↥CQt := by
    let φ : ↥Q →* ↥Q :=
      { toFun := fun q => ⟨t' * q * t'⁻¹ * (q : G)⁻¹,
          Q.mul_mem (pCoreOf_normalized M ht'M q.2) (Q.inv_mem q.2)⟩
        map_one' := by ext; simp
        map_mul' := fun q₁ q₂ => by
          ext
          simp only [Subgroup.coe_mul]
          exact comm_mul_comm C hR ht'M q₁.2 q₂.2 }
    have hφ : ∀ q : ↥Q, (φ q : G) = t' * q * t'⁻¹ * (q : G)⁻¹ := fun q => rfl
    have h1 := Subgroup.card_ker_mul_card_range φ
    have hker : Nat.card φ.ker = Nat.card ↥CQt := by
      refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨((q : ↥Q) : G), ?_⟩) ⟨?_, ?_⟩)
      · refine Subgroup.mem_inf.2 ⟨(q : ↥Q).2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have h := congrArg Subtype.val (MonoidHom.mem_ker.1 q.2)
        rw [hφ] at h
        have : t' * (q : G) = (q : G) * t' := by
          calc t' * (q : G) = (t' * q * t'⁻¹ * (q : G)⁻¹) * q * t' := by group
            _ = q * t' := by rw [h]; simp
        exact this.symm
      · intro q₁ q₂ h
        exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
      · intro c
        obtain ⟨hcQ, hcc⟩ := Subgroup.mem_inf.1 c.2
        refine ⟨⟨⟨c, hcQ⟩, MonoidHom.mem_ker.2 (Subtype.ext ?_)⟩, rfl⟩
        rw [hφ]
        have : t' * (c : G) = (c : G) * t' := (Subgroup.mem_centralizer_singleton_iff.1 hcc).symm
        show t' * (c : G) * t'⁻¹ * (c : G)⁻¹ = 1
        rw [this]
        group
    have hrange : Nat.card φ.range ≤ 4 := by
      have hmem : ∀ r ∈ φ.range, (r : G) ∈ Rc X ∨ (r : G) * x⁻¹ ∈ Rc X := by
        rintro r ⟨q, rfl⟩
        have hconj := D.piQ_conj ⟨t', ht'M⟩ q ⟨_, pCoreOf_normalized M ht'M q.2⟩ rfl
        have hθ' : C.θ ⟨t', ht'M⟩ = swap a b := by
          rcases theta_TOf_len_two D hx hab hπ (t := ⟨t', ht'M⟩) (hPT ht'P) with h | h
          · exact absurd (hKQ t' ht'M h) ht'Q
          · exact h
        rw [hθ'] at hconj
        have hπφ : Multiplicative.toAdd (D.piQ (φ q)) =
            barAct (swap a b) (Multiplicative.toAdd (D.piQ q)) -
              Multiplicative.toAdd (D.piQ q) := by
          have e : φ q = ⟨_, pCoreOf_normalized M ht'M q.2⟩ * q⁻¹ := rfl
          rw [e, map_mul, map_inv, toAdd_mul, toAdd_inv, hconj, sub_eq_add_neg]
        rcases barAct_swap_sub hab (Multiplicative.toAdd (D.piQ q)) with h | h
        · left
          rw [h] at hπφ
          exact (D.piQ_eq_one_iff _).1 (Multiplicative.toAdd.injective hπφ)
        · right
          rw [h, ← hπ] at hπφ
          have hmem' : (φ q : G) * x⁻¹ ∈ Q := Q.mul_mem (φ q).2 (Q.inv_mem hx)
          refine (D.piQ_eq_one_iff ⟨_, hmem'⟩).1 ?_
          have e : (⟨(φ q : G) * x⁻¹, hmem'⟩ : ↥Q) = φ q * (⟨x, hx⟩)⁻¹ := rfl
          rw [e, map_mul, map_inv]
          apply Multiplicative.toAdd.injective
          rw [toAdd_mul, toAdd_inv, hπφ, add_neg_cancel, toAdd_one]
      let f : ↥φ.range → ↥(Rc X) × Bool := fun r =>
        if hr : ((r : ↥Q) : G) ∈ Rc X then (⟨_, hr⟩, false)
        else (⟨_, (hmem r r.2).resolve_left hr⟩, true)
      have hf : Function.Injective f := by
        intro r₁ r₂ h
        simp only [f] at h
        by_cases h1 : ((r₁ : ↥Q) : G) ∈ Rc X <;> by_cases h2 : ((r₂ : ↥Q) : G) ∈ Rc X <;>
          simp only [h1, h2, dif_pos, dif_neg, not_false_eq_true, Prod.mk.injEq,
            Subtype.mk.injEq, reduceCtorEq, and_false, and_true] at h
        · exact Subtype.ext (Subtype.ext h)
        · exact Subtype.ext (Subtype.ext (mul_right_cancel h))
      have h5 := Nat.card_le_card_of_injective f hf
      rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h5
      omega
    rw [hker] at h1
    calc Nat.card ↥Q = Nat.card ↥CQt * Nat.card φ.range := h1.symm
      _ ≤ Nat.card ↥CQt * 4 := Nat.mul_le_mul_left _ hrange
      _ = 4 * Nat.card ↥CQt := Nat.mul_comm _ _
  obtain ⟨g, hgK, hgM⟩ := Set.not_subset.1 hKM
  set B : Subgroup G := P ⊓ Q with hB
  set U : Subgroup G := conjSubgroup g B with hU
  have hUP : U ≤ P := fun u hu => by
    have h1 : g⁻¹ * u * g ∈ B := mem_conjSubgroup.1 hu
    have := pCoreOf_normalized _ hgK (Subgroup.mem_inf.1 h1).1
    simpa [mul_assoc] using this
  have hUM : U ≤ M := hUP.trans hPM
  set E : Subgroup G := U ⊓ Q with hE
  have hcardU : Nat.card ↥U = Nat.card ↥B :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hθU : Nat.card ↥((U.subgroupOf M).map C.θ) ≤ 2 := by
    have hval : ∀ σ ∈ (U.subgroupOf M).map C.θ, σ = 1 ∨ σ = swap a b := by
      rintro σ ⟨u, hu, rfl⟩
      exact theta_TOf_len_two D hx hab hπ (hPT (hUP (Subgroup.mem_subgroupOf.1 hu)))
    have hinj : Function.Injective (fun σ : ↥((U.subgroupOf M).map C.θ) =>
        decide ((σ : Perm (Fin 8)) = 1)) := by
      intro σ τ h
      simp only [decide_eq_decide] at h
      rcases hval σ σ.2 with h1 | h1 <;> rcases hval τ τ.2 with h2 | h2
      · exact Subtype.ext (h1.trans h2.symm)
      · exact absurd (h.1 h1) (by rw [h2]; exact fun e => hab.symm (by
          have := congrArg (fun f : Perm (Fin 8) => f a) e
          simpa using this))
      · exact absurd (h.2 h2) (by rw [h1]; exact fun e => hab.symm (by
          have := congrArg (fun f : Perm (Fin 8) => f a) e
          simpa using this))
      · exact Subtype.ext (h1.trans h2.symm)
    have h5 := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h5
  have hcardE : Nat.card ↥U ≤ 2 * Nat.card ↥E := by
    have h := C.card_eq_card_inf_mul hR hUM
    rw [h, Nat.mul_comm]
    exact Nat.mul_le_mul_right _ hθU
  have hCQtB : CQt ≤ B := le_inf hCQtP inf_le_left
  have h8 : Nat.card ↥Q ≤ 8 * Nat.card ↥E := by
    have := Subgroup.card_le_of_le hCQtB
    omega
  have hEQ : E ≤ Q := inf_le_right
  have hEno4 : ∀ (z : ↥Q), (z : G) ∈ E → barLen (Multiplicative.toAdd (D.piQ z)) ≠ 4 := by
    intro z hz h4
    obtain ⟨hzU, -⟩ := Subgroup.mem_inf.1 hz
    have h1 : g⁻¹ * z * g ∈ B := mem_conjSubgroup.1 hzU
    have h2 : g⁻¹ * (z : G) * g⁻¹⁻¹ ∈ Q := by simpa using (Subgroup.mem_inf.1 h1).2
    have := h37 z h4 g⁻¹ h2
    exact hgM (by simpa using M.inv_mem this)
  set VE : AddSubgroup (permBar 8) := Subgroup.toAddSubgroup' ((E.subgroupOf Q).map D.piQ)
    with hVE
  set VQ : AddSubgroup (permBar 8) := Subgroup.toAddSubgroup' ((Q.subgroupOf Q).map D.piQ)
    with hVQ
  set Uh := (heartToBar : altHeart 8 →+ permBar 8).range with hUh
  have hVE4 : ∀ v ∈ VE, barLen v ≠ 4 := by
    intro v hv
    rw [hVE, Subgroup.mem_toAddSubgroup', Subgroup.mem_map] at hv
    obtain ⟨z, hz, hzv⟩ := hv
    have := hEno4 z (Subgroup.mem_subgroupOf.1 hz)
    rwa [hzv] at this
  obtain ⟨hVE8, hVEU⟩ := card_le_of_no_len_four VE hVE4
  have hRpos : 0 < Nat.card ↥(Rc X) := Nat.card_pos
  have hEcard : Nat.card ↥E ≤ Nat.card ↥(Rc X) * Nat.card ↥VE := by
    have h := D.card_eq_card_inf_R_mul hEQ
    rw [h, hVE, card_toAddSubgroup']
    exact Nat.mul_le_mul_right _ (Subgroup.card_le_of_le inf_le_right)
  have hRQ : Rc X ≤ Q := by
    intro r hr
    rw [C.S.R_eq_inf] at hr
    exact (Subgroup.mem_inf.1 hr).1
  have hQcard : Nat.card ↥Q = Nat.card ↥(Rc X) * Nat.card ↥VQ := by
    have h := D.card_eq_card_inf_R_mul (le_refl Q)
    rw [inf_eq_right.2 hRQ] at h
    rw [h, hVQ, card_toAddSubgroup']
  have hUVQ : Uh ≤ VQ := by
    intro v hv
    obtain ⟨q, hq⟩ := exists_piQ_eq_of_heart D hv
    rw [hVQ, Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
    exact ⟨q, Subgroup.mem_subgroupOf.2 q.2, by rw [← hq]; rfl⟩
  have h64 : 2 ^ 6 ≤ Nat.card ↥VQ := card_heart_eight ▸ AddSubgroup.card_le_of_le hUVQ
  have hVEQ : VE ≤ VQ := by
    intro v hv
    rw [hVE, Subgroup.mem_toAddSubgroup', Subgroup.mem_map] at hv
    obtain ⟨z, hz, hzv⟩ := hv
    rw [hVQ, Subgroup.mem_toAddSubgroup', Subgroup.mem_map]
    exact ⟨z, Subgroup.mem_subgroupOf.2 z.2, hzv⟩
  have hkey : Nat.card ↥VQ ≤ 8 * Nat.card ↥VE := by
    have h1 : Nat.card ↥(Rc X) * Nat.card ↥VQ ≤ Nat.card ↥(Rc X) * (8 * Nat.card ↥VE) := by
      rw [← hQcard]
      calc Nat.card ↥Q ≤ 8 * Nat.card ↥E := h8
        _ ≤ 8 * (Nat.card ↥(Rc X) * Nat.card ↥VE) := Nat.mul_le_mul_left _ hEcard
        _ = Nat.card ↥(Rc X) * (8 * Nat.card ↥VE) := by ring
    exact Nat.le_of_mul_le_mul_left h1 hRpos
  by_cases hsub : VE ≤ Uh
  · have := hVEU hsub
    omega
  · apply hsub
    have hVQ64 : Nat.card ↥VQ ≤ 2 ^ 6 := by omega
    have heq : Uh = VQ :=
      AddSubgroup.eq_of_le_of_card_ge hUVQ (by rw [card_heart_eight]; exact hVQ64)
    rw [heq]
    exact hVEQ


end Group

end Eight

end CFSG.RankThree.PartTwo.Sec19.SolEven
