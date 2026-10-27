module

public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.RankThree.CentralLiftSO.SymplecticTriangular
public import CFSG.Quasithin.H13.A6S13820AutL3b
public import CFSG.Quasithin.H13.A6S13820AutT

public section

namespace CFSG.Quasithin.Background.Harris.AutBorel

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Lin2.Five
  CFSG.Quasithin.H13.A6
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (torusHom coe_torusHom)

section Matrices

variable {F : Type} [Field F] [CharP F 2]

theorem flagOrder_ι₀ : (flagOrder 2 (Sum.inl 0) : ℕ) = 0 := by rw [flagOrder_inl]; rfl
theorem flagOrder_ι₁ : (flagOrder 2 (Sum.inl 1) : ℕ) = 1 := by rw [flagOrder_inl]; rfl
theorem flagOrder_ι₂ : (flagOrder 2 (Sum.inr 0) : ℕ) = 3 := by rw [flagOrder_inr]; rfl
theorem flagOrder_ι₃ : (flagOrder 2 (Sum.inr 1) : ℕ) = 2 := by rw [flagOrder_inr]; rfl

theorem tauSp_mem_unipotent {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) :
    tauSp g ∈ unipotent 2 F := by
  rw [CFSG.RankThree.CentralLiftSO.Sp.mem_unipotent_iff_flag] at hg ⊢
  simp only [coe_tauSp]
  obtain ⟨h0, h1⟩ := hg
  generalize ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = M at h0 h1 ⊢
  have z10 : M (Sum.inl 1) (Sum.inl 0) = 0 := h0 _ _ (by rw [flagOrder_ι₀, flagOrder_ι₁]; decide)
  have z30 : M (Sum.inr 1) (Sum.inl 0) = 0 := h0 _ _ (by rw [flagOrder_ι₀, flagOrder_ι₃]; decide)
  have z31 : M (Sum.inr 1) (Sum.inl 1) = 0 := h0 _ _ (by rw [flagOrder_ι₁, flagOrder_ι₃]; decide)
  have z20 : M (Sum.inr 0) (Sum.inl 0) = 0 := h0 _ _ (by rw [flagOrder_ι₀, flagOrder_ι₂]; decide)
  have z21 : M (Sum.inr 0) (Sum.inl 1) = 0 := h0 _ _ (by rw [flagOrder_ι₁, flagOrder_ι₂]; decide)
  have z23 : M (Sum.inr 0) (Sum.inr 1) = 0 := h0 _ _ (by rw [flagOrder_ι₃, flagOrder_ι₂]; decide)
  have d0 := h1 (Sum.inl 0)
  have d1 := h1 (Sum.inl 1)
  have d2 := h1 (Sum.inr 0)
  have d3 := h1 (Sum.inr 1)
  refine ⟨?_, ?_⟩
  · simp only [Sum.forall, Fin.forall_fin_two, tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂,
      tauPair_ι₃, flagOrder_ι₀, flagOrder_ι₁, flagOrder_ι₂, flagOrder_ι₃]
    simp [z10, z30, z31, z20, z21, z23, d0, d1, d2, d3]
  · simp only [Sum.forall, Fin.forall_fin_two, tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂,
      tauPair_ι₃]
    simp [z10, z30, z21, z23, d0, d1, d2, d3]

theorem tauSp_torusHom (t : Fin 2 → Fˣ) :
    tauSp (torusHom t) = torusHom ![t 0 * t 1, t 0 * (t 1)⁻¹] := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_tauSp, coe_torusHom, coe_torusHom]
  refine Matrix.ext fun x y => ?_
  revert x y
  simp only [Sum.forall, Fin.forall_fin_two, tauMat_apply, tauPair_ι₀, tauPair_ι₁, tauPair_ι₂,
    tauPair_ι₃]
  simp [mul_comm]

omit [CharP F 2] in
theorem fieldSp_torusHom (σ : F ≃+* F) (t : Fin 2 → Fˣ) :
    fieldSp 2 F σ (torusHom t) = torusHom (fun i => Units.map σ.toMonoidHom (t i)) := by
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [coe_fieldSp, coe_torusHom, coe_torusHom]
  refine Matrix.ext fun x y => ?_
  revert x y
  simp only [Sum.forall, Fin.forall_fin_two]
  simp

omit [CharP F 2] in
theorem torusHom_mem_borel (t : Fin 2 → Fˣ) : torusHom t ∈ borelSubgroup 2 F :=
  torus_le_borelSubgroup ⟨t, rfl⟩

omit [CharP F 2] in
theorem diagHom_torusHom (t : Fin 2 → Fˣ) :
    diagHom 2 F ⟨torusHom t, torusHom_mem_borel t⟩ = t := by
  funext i
  apply Units.ext
  simp [diagHom, diagEntry, coe_torusHom]

end Matrices

section Torus

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem torusHom_pow_three_mem {C : Subgroup (StatedSp 2 F)}
    (hCn : (C.subgroupOf (Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)))).Normal)
    (hidx : C.relIndex (Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F))) ∣ 3)
    (w : Fin 2 → Fˣ) : torusHom (w ^ 3) ∈ C := by
  have hmem : torusHom w ∈ Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)) := by
    rw [normalizer_unipotent]
    exact torusHom_mem_borel w
  rw [map_pow]
  exact Aut20.pow_three_mem20 hCn hidx hmem

omit [CharP F 2] in
theorem eq_of_torusHom_mem {C : Subgroup (StatedSp 2 F)} {α : MulAut (StatedSp 2 F)}
    (hαS : (unipotent 2 F).map α.toMonoidHom = unipotent 2 F)
    (hcomm : ∀ c ∈ C, c⁻¹ * α c ∈ unipotent 2 F)
    (y : StatedSp 2 F) (β : StatedSp 2 F →* StatedSp 2 F) (hβ : Function.Injective β)
    (hβU : ∀ g ∈ unipotent 2 F, β g ∈ unipotent 2 F)
    (hα : ∀ g, α g = y * β g * y⁻¹)
    (bar : (Fin 2 → Fˣ) → (Fin 2 → Fˣ)) (hbar : ∀ t, β (torusHom t) = torusHom (bar t))
    (t : Fin 2 → Fˣ) (ht : torusHom t ∈ C) : bar t = t := by
  have hle : (unipotent 2 F).map β ≤ unipotent 2 F := by
    rintro _ ⟨g, hg, rfl⟩
    exact hβU g hg
  have hcard : Nat.card (unipotent 2 F) ≤ Nat.card ((unipotent 2 F).map β) := by
    rw [Subgroup.card_map_of_injective hβ]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hyN : y ∈ Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)) := by
    apply Aut20.mem_normalizer_of_conj_le20
    intro x hx
    rw [← heq] at hx
    obtain ⟨x', hx', rfl⟩ := hx
    have : α x' ∈ unipotent 2 F := by
      rw [← hαS]
      exact ⟨x', hx', rfl⟩
    rwa [hα] at this
  rw [normalizer_unipotent] at hyN
  have hc := hcomm _ ht
  rw [hα, hbar] at hc
  let Y : borelSubgroup 2 F := ⟨y, hyN⟩
  let A : borelSubgroup 2 F := ⟨torusHom t, torusHom_mem_borel t⟩
  let B' : borelSubgroup 2 F := ⟨torusHom (bar t), torusHom_mem_borel _⟩
  have hker : A⁻¹ * (Y * B' * Y⁻¹) ∈ (diagHom 2 F).ker := by
    rw [ker_diagHom, Subgroup.mem_subgroupOf]
    exact hc
  have hA : diagHom 2 F A = t := diagHom_torusHom t
  have hB : diagHom 2 F B' = bar t := diagHom_torusHom (bar t)
  rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, hA, hB,
    mul_comm (diagHom 2 F Y) (bar t), mul_inv_cancel_right] at hker
  exact (inv_mul_eq_one.mp hker).symm

omit [CharP F 2] in
theorem exists_torusHom_mem_ne_one (hF : Nat.card F = 4) {C : Subgroup (StatedSp 2 F)}
    (hCn : (C.subgroupOf (Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)))).Normal)
    (hidx : C.relIndex (Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F))) ∣ 3) :
    ∃ t : Fin 2 → Fˣ, t ≠ 1 ∧ torusHom t ∈ C := by
  set N := Subgroup.normalizer (unipotent 2 F : Set (StatedSp 2 F)) with hN
  have hmem : ∀ t : Fin 2 → Fˣ, torusHom t ∈ N := fun t => by
    rw [hN, normalizer_unipotent]
    exact torusHom_mem_borel t
  have := hCn
  let ψ : (Fin 2 → Fˣ) →* N := (torusHom : (Fin 2 → Fˣ) →* StatedSp 2 F).codRestrict N hmem
  let φ : (Fin 2 → Fˣ) →* N ⧸ C.subgroupOf N := (QuotientGroup.mk' (C.subgroupOf N)).comp ψ
  have hker : ∀ t, t ∈ φ.ker ↔ torusHom t ∈ C := fun t => by
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    rfl
  have hcard := L2Case.card_eq_ker_mul_range φ
  have hunits : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hdom : Nat.card (Fin 2 → Fˣ) = 9 := by
    rw [Nat.card_pi, Fin.prod_univ_two, hunits]
    norm_num
  have hq : Nat.card (N ⧸ C.subgroupOf N) ≤ 3 := by
    have : Nat.card (N ⧸ C.subgroupOf N) = C.relIndex N := rfl
    rw [this]
    exact Nat.le_of_dvd (by norm_num) hidx
  have hrange : Nat.card φ.range ≤ 3 := by
    have hfin : Finite (N ⧸ C.subgroupOf N) := by
      refine Nat.finite_of_card_ne_zero ?_
      intro h0
      rw [show Nat.card (N ⧸ C.subgroupOf N) = C.relIndex N from rfl] at h0
      rw [h0] at hidx
      norm_num at hidx
    exact (Nat.card_le_card_of_injective (fun x : φ.range => (x : N ⧸ C.subgroupOf N))
      Subtype.val_injective).trans hq
  have hk : 1 < Nat.card φ.ker := by
    rw [hdom] at hcard
    by_contra hle
    have : Nat.card φ.ker ≤ 1 := by omega
    have hpos : 0 < Nat.card φ.ker := Nat.card_pos
    have h1 : Nat.card φ.ker = 1 := by omega
    rw [h1] at hcard
    omega
  rw [Subgroup.one_lt_card_iff_ne_bot, Ne, Subgroup.eq_bot_iff_forall] at hk
  push Not at hk
  obtain ⟨t, ht, ht1⟩ := hk
  exact ⟨t, ht1, (hker t).1 ht⟩

end Torus

section F4

variable {F : Type} [Field F] [Finite F]

theorem four_elts (hF : Nat.card F = 4) {x : F} (hx0 : x ≠ 0) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) :
    ∀ z : F, z = 0 ∨ z = 1 ∨ z = x ∨ z = x ^ 2 := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hx2 : x ^ 2 ≠ 1 := fun h => hx1 (by linear_combination (-x) * h + hx3)
  have hxx : x ^ 2 ≠ x := fun h => hx1 (by
    have h' : x * (x - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h0 | h0
    · exact absurd h0 hx0
    · exact sub_eq_zero.1 h0)
  have hx20 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
  have hs : ({0, 1, x, x ^ 2} : Finset F).card = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, hF]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    all_goals simp [hx2.symm, hxx.symm, hx1.symm, hx20.symm, hx0.symm, one_ne_zero.symm]
  intro z
  have hz := Finset.eq_univ_of_card _ hs ▸ Finset.mem_univ z
  simpa using hz

theorem F4_contra (hF : Nat.card F = 4) (hc : ∀ a : F, a ≠ 0 → a ^ 3 = 1) (σ : F ≃+* F) {x y : F}
    (hx : x ≠ 0) (hy : y ≠ 0) (h1 : σ (x * y) = x) (h2 : σ (x * y⁻¹) = y) : x = 1 ∧ y = 1 := by
  have hσ0 : ∀ a : F, a ≠ 0 → σ a ≠ 0 := fun a ha h => ha (σ.injective (by rw [h, map_zero]))
  have hσ1 : ∀ a : F, a ≠ 1 → σ a ≠ 1 := fun a ha h => ha (σ.injective (by rw [h, map_one]))
  rw [map_mul] at h1
  rw [map_mul, map_inv₀] at h2
  have hs0 := hσ0 x hx
  have hr0 := hσ0 y hy
  have h2' : σ x = y * σ y :=
    calc σ x = (σ x * (σ y)⁻¹) * σ y := (inv_mul_cancel_right₀ hr0 _).symm
      _ = y * σ y := by rw [h2]
  by_cases hx1 : x = 1
  · subst hx1
    refine ⟨rfl, ?_⟩
    rw [map_one] at h1 h2'
    have hr : σ y = 1 := by simpa using h1
    rw [hr] at h2'
    simpa using h2'.symm
  · have hx3 := hc x hx
    have hs : σ x = x ∨ σ x = x ^ 2 := by
      rcases four_elts hF hx hx1 hx3 (σ x) with h | h | h | h
      · exact absurd h hs0
      · exact absurd h (hσ1 x hx1)
      · exact Or.inl h
      · exact Or.inr h
    exfalso
    by_cases hy1 : y = 1
    · subst hy1
      rw [map_one, mul_one] at h1 h2'
      exact hx1 (h1.symm.trans h2')
    · have hy3 := hc y hy
      have hr : σ y = y ∨ σ y = y ^ 2 := by
        rcases four_elts hF hy hy1 hy3 (σ y) with h | h | h | h
        · exact absurd h hr0
        · exact absurd h (hσ1 y hy1)
        · exact Or.inl h
        · exact Or.inr h
      rcases hs with hs | hs <;> rcases hr with hr | hr <;> rw [hs, hr] at h1 h2'
      · have h' : x * (y - 1) = 0 := by linear_combination h1
        rcases mul_eq_zero.1 h' with h0 | h0
        · exact hx h0
        · exact hy1 (sub_eq_zero.1 h0)
      · have h' : x * (y ^ 2 - 1) = 0 := by linear_combination h1
        rcases mul_eq_zero.1 h' with h0 | h0
        · exact hx h0
        · exact hy1 (by linear_combination (-y) * h0 + hy3)
      · have h' : x * (x * y - 1) = 0 := by linear_combination h1
        have hxy : x * y = 1 := by
          rcases mul_eq_zero.1 h' with h0 | h0
          · exact absurd h0 hx
          · exact sub_eq_zero.1 h0
        have hy' : y = x ^ 2 := by linear_combination x ^ 2 * hxy - y * hx3
        subst hy'
        have h'' : x * (x - 1) = 0 := by linear_combination h2' + x * hx3
        rcases mul_eq_zero.1 h'' with h0 | h0
        · exact hx h0
        · exact hx1 (sub_eq_zero.1 h0)
      · have hx2 : x ^ 2 = 1 := by linear_combination h2' + hy3
        exact hx1 (by linear_combination (-x) * hx2 + hx3)

omit [Finite F] in
theorem cube_eq_one_of_card_four [Finite F] (hF : Nat.card F = 4) : ∀ a : F, a ≠ 0 → a ^ 3 = 1 := by
  intro a ha
  have h := pow_card_eq_one' (G := Fˣ) (x := Units.mk0 a ha)
  have hu : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  rw [hu] at h
  simpa using congrArg Units.val h

end F4

section Conclude

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
theorem sigma_eq_one_of_bar {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (σ : F ≃+* F)
    {C : Subgroup (StatedSp 2 F)}
    (hcube : ∀ w : Fin 2 → Fˣ, torusHom (w ^ 3) ∈ C)
    (hn2 : n = 2 → ∃ t : Fin 2 → Fˣ, t ≠ 1 ∧ torusHom t ∈ C)
    (hbar : ∀ t, torusHom t ∈ C → (fun i => Units.map σ.toMonoidHom (t i)) = t) : σ = 1 := by
  have hcub : ∀ a : Fˣ, σ ((a : F) ^ 3) = (a : F) ^ 3 := by
    intro a
    have h := congrArg Units.val (congr_fun (hbar _ (hcube ![a, 1])) 0)
    simpa using h
  rcases Aut20.sigma_eq_one_of_fix_cubes20 hn hF σ hcub with h | h2
  · exact h
  · subst h2
    have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
    obtain ⟨t, ht1, htC⟩ := hn2 rfl
    have hfix := hbar t htC
    obtain ⟨i, hi⟩ : ∃ i, t i ≠ 1 := by
      by_contra hcon
      push Not at hcon
      exact ht1 (funext hcon)
    have hfi : σ (t i : F) = t i := by simpa using congrArg Units.val (congr_fun hfix i)
    have hc3 := cube_eq_one_of_card_four hF4
    have hx0 : (t i : F) ≠ 0 := Units.ne_zero _
    have hx1 : (t i : F) ≠ 1 := fun h => hi (Units.ext h)
    have h4 := four_elts hF4 hx0 hx1 (hc3 _ hx0)
    ext z
    rcases h4 z with rfl | rfl | rfl | rfl
    · simp
    · simp
    · simpa using hfi
    · simp [hfi]

omit [CharP F 2] in
theorem false_of_bar_graph {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (σ : F ≃+* F)
    {C : Subgroup (StatedSp 2 F)}
    (hcube : ∀ w : Fin 2 → Fˣ, torusHom (w ^ 3) ∈ C)
    (hn2 : n = 2 → ∃ t : Fin 2 → Fˣ, t ≠ 1 ∧ torusHom t ∈ C)
    (hbar : ∀ t, torusHom t ∈ C →
      (fun i => Units.map σ.toMonoidHom (![t 0 * t 1, t 0 * (t 1)⁻¹] i)) = t) : False := by
  have ha : ∀ a : Fˣ, a ^ 3 = 1 := by
    intro a
    have h := congrArg Units.val (congr_fun (hbar _ (hcube ![a, 1])) 1)
    simp at h
    have h' : (a : F) ^ 3 = 1 := σ.injective (by rw [map_pow, h, map_one])
    exact Units.ext (by simpa using h')
  have h2 : n = 2 := Aut20.n_eq_two_of_pow_nine20 hn hF fun a => by
    rw [show 9 = 3 * 3 from rfl, pow_mul, ha]
  subst h2
  have hF4 : Nat.card F = 4 := by rw [hF]; norm_num
  obtain ⟨t, ht1, htC⟩ := hn2 rfl
  have hfix := hbar t htC
  have h0 := congrArg Units.val (congr_fun hfix 0)
  have h1 := congrArg Units.val (congr_fun hfix 1)
  simp at h0 h1
  obtain ⟨hx, hy⟩ := F4_contra hF4 (cube_eq_one_of_card_four hF4) σ (Units.ne_zero (t 0))
    (Units.ne_zero (t 1)) (by simpa using h0) (by simpa using h1)
  have : ∀ i, t i = 1 := by
    rw [Fin.forall_fin_two]
    exact ⟨Units.ext hx, Units.ext hy⟩
  exact ht1 (funext this)

end Conclude

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem fieldSp_mem_unipotent (σ : F ≃+* F) {g : StatedSp 2 F} (hg : g ∈ unipotent 2 F) :
    fieldSp 2 F σ g ∈ unipotent 2 F := by
  rw [CFSG.RankThree.CentralLiftSO.Sp.mem_unipotent_iff_flag] at hg ⊢
  obtain ⟨h0, h1⟩ := hg
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · rw [coe_fieldSp, Matrix.map_apply, h0 x y hxy, map_zero]
  · rw [coe_fieldSp, Matrix.map_apply, h1 x, map_one]

theorem exists_form (α : MulAut (StatedSp 2 F)) :
    ∃ (y : StatedSp 2 F) (σ : F ≃+* F),
      (∀ g, α g = y * fieldSp 2 F σ g * y⁻¹) ∨
      (∀ g, α g = y * fieldSp 2 F σ (tauSp g) * y⁻¹) := by
  obtain ⟨A, σ, ε, hε, h⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow
      (MulAut.congr (projEquiv F) α)
  obtain ⟨p, hp⟩ := CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A
  obtain ⟨y, rfl⟩ := (projEquiv F).surjective p
  rw [← hp] at h
  refine ⟨y, σ, ?_⟩
  have key : ∀ g, projEquiv F (α g) =
      (MulAut.conj (projEquiv F y) * fieldAut 2 F σ * tauAut ^ ε :
        MulAut (StatedProj (StatedSp 2 F))) (projEquiv F g) := by
    intro g
    rw [← h]
    simp [MulAut.congr_apply]
  have hf : ∀ g, projEquiv F (fieldSp 2 F σ g) = fieldAut 2 F σ (projEquiv F g) :=
    fun g => (fieldAut_proj σ g).symm
  have hT : ∀ g, projEquiv F (tauSp g) = tauAut (projEquiv F g) := fun g => (tauAut_proj g).symm
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · left
    intro g
    apply (projEquiv F).injective
    rw [key, map_mul, map_mul, map_inv, hf]
    simp [MulAut.conj_apply]
  · right
    intro g
    apply (projEquiv F).injective
    rw [key, map_mul, map_mul, map_inv, hf, hT]
    simp [MulAut.conj_apply]

theorem inner_of_borel {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {C : Subgroup (StatedSp 2 F)} {α : MulAut (StatedSp 2 F)}
    (h : BorelAut13820 (unipotent 2 F) C α) : ∃ g, α = MulAut.conj g := by
  obtain ⟨-, -, -, hCn, hidx, -, hαS, hcomm⟩ := h
  have hn2 : n = 2 → ∃ t : Fin 2 → Fˣ, t ≠ 1 ∧ torusHom t ∈ C := fun h2 =>
    exists_torusHom_mem_ne_one (by rw [hF, h2]; norm_num) hCn hidx
  obtain ⟨y, σ, hy | hy⟩ := exists_form α
  · have hσ : σ = 1 := by
      refine sigma_eq_one_of_bar hn hF σ (torusHom_pow_three_mem hCn hidx) hn2 ?_
      intro t ht
      exact eq_of_torusHom_mem hαS hcomm y (fieldSp 2 F σ).toMonoidHom
        (fieldSp 2 F σ).injective (fun g hg => fieldSp_mem_unipotent σ hg) hy
        (fun t => fun i => Units.map σ.toMonoidHom (t i)) (fieldSp_torusHom σ) t ht
    refine ⟨y, MulEquiv.ext fun g => ?_⟩
    rw [hy g, hσ, map_one]
    simp [MulAut.conj_apply]
  · exfalso
    refine false_of_bar_graph hn hF σ (torusHom_pow_three_mem hCn hidx) hn2 ?_
    intro t ht
    exact eq_of_torusHom_mem hαS hcomm y
      ((fieldSp 2 F σ).toMonoidHom.comp tauSp)
      ((fieldSp 2 F σ).injective.comp (tauSp_bijective (F := F)).1)
      (fun g hg => fieldSp_mem_unipotent σ (tauSp_mem_unipotent hg)) hy
      (fun t => fun i => Units.map σ.toMonoidHom (![t 0 * t 1, t 0 * (t 1)⁻¹] i))
      (fun t => by
        show fieldSp 2 F σ (tauSp (torusHom t)) = _
        rw [tauSp_torusHom, fieldSp_torusHom]) t ht

end Main

theorem autBorel13820Sp4_holds : AutBorel13820Sp4 := by
  intro Q _ _ n hq hZ hn hP S C α h
  have hquot := Aut20.borelAut_quot20 hZ h
  obtain ⟨K, _, _, _, φ, hcard, hφ, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_symplectic hP hquot.1
  let Ψ : (Q ⧸ Subgroup.center Q) ≃* StatedSp 2 K := φ.trans (projEquiv K).symm
  have hSΨ : (Subgroup.map (QuotientGroup.mk' (Subgroup.center Q)) S).map Ψ.toMonoidHom =
      unipotent 2 K := by
    have h1 : (Subgroup.map (QuotientGroup.mk' (Subgroup.center Q)) S).map Ψ.toMonoidHom =
        ((Subgroup.map (QuotientGroup.mk' (Subgroup.center Q)) S).map φ.toMonoidHom).map
          (projEquiv K).symm.toMonoidHom := by
      simp only [Subgroup.map_map]
      rfl
    rw [h1, hφ, projUnipotent, Subgroup.map_map]
    have : ((projEquiv K).symm.toMonoidHom).comp (proj 2 K) = MonoidHom.id _ :=
      MonoidHom.ext fun g => (projEquiv K).symm_apply_apply g
    rw [this, Subgroup.map_id]
  have hquot' := Aut20.borelAut_mulEquiv20 Ψ hquot
  rw [hSΨ] at hquot'
  obtain ⟨g, hg⟩ := inner_of_borel hn hcard hquot'
  have hi : ∃ g, MulAut.congr Ψ (Aut20.quotCenterAut20 Q α) = MulAut.conj g := ⟨g, hg⟩
  have : Group.IsPerfect Q := hq.1
  obtain ⟨g', hg'⟩ := (Aut20.inner_congr_iff20 Ψ _).1 hi
  exact Aut20.inner_of_quot20 hg'

end CFSG.Quasithin.Background.Harris.AutBorel
