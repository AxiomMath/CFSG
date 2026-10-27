module

public import CFSG.Quasithin.Vol2.Ch12Sec6L20c

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126L1c S126FE S126N S126L19 S126L19b S126L19d S126L20 S126L20a S126L20c Equiv
open scoped IsMulCommutative commutatorElement

@[expose] def FactS8ElemAbE8 : Prop :=
  ∀ B : Subgroup (Equiv.Perm (Fin 8)), (∀ σ ∈ B, ∀ τ ∈ B, σ * τ = τ * σ) →
    (∀ σ ∈ B, σ * σ = 1) →
    Nat.card B ≤ 16 ∧
    (8 ≤ Nat.card B → ∃ a ∈ B, ∃ b ∈ B, b ≠ 1 ∧ ∃ u : Fin 8 → ZMod 2, ∑ i, u i = 0 ∧
      (∀ i, u (b i) = u i) ∧ (Finset.univ.filter fun i => u i + u (a i) ≠ 0).card ≠ 0 ∧
      (Finset.univ.filter fun i => u i + u (a i) ≠ 0).card ≠ 4) ∧
    (Nat.card B = 16 → ∃ a ∈ B, ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ 1 ∧ b₂ ≠ 1 ∧ b₁ ≠ b₂ ∧
      ∃ u : Fin 8 → ZMod 2, ∑ i, u i = 0 ∧ (∀ i, u (b₁ i) = u i) ∧ (∀ i, u (b₂ i) = u i) ∧
      (Finset.univ.filter fun i => u i + u (a i) ≠ 0).card ≠ 0 ∧
      (Finset.univ.filter fun i => u i + u (a i) ≠ 0).card ≠ 4)

namespace S126L22

theorem card_comap_of_le_range {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    {H : Subgroup Y} (hH : H ≤ f.range) :
    Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  let f' : ↥(H.comap f) →* ↥H := (f.comp (H.comap f).subtype).codRestrict H fun x => x.2
  have hsurj : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hH hy
    exact ⟨⟨x, hy⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f'.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f' hsurj).toEquiv] at h1
  rw [h1, mul_comm]
  congr 1
  refine Nat.card_congr
    { toFun := fun x => ⟨((x : ↥(H.comap f)) : X), ?_⟩
      invFun := fun y => ⟨⟨y, ?_⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · have h2 : f' x = 1 := x.2
    have h3 := congrArg Subtype.val h2
    exact h3
  · rw [Subgroup.mem_comap, y.2]
    exact H.one_mem
  · apply Subtype.ext
    exact y.2

@[expose] def fixSub (u : Fin 8 → ZMod 2) : Subgroup (Perm (Fin 8)) where
  carrier := {σ | ∀ i, u (σ i) = u i}
  one_mem' := fun i => rfl
  mul_mem' := fun {σ τ} hσ hτ i => by
    simp only [Set.mem_ofPred_eq] at hσ hτ
    rw [Perm.mul_apply, hσ, hτ]
  inv_mem' := fun {σ} hσ i => by
    simp only [Set.mem_ofPred_eq] at hσ ⊢
    rw [← hσ (σ⁻¹ i), ← Perm.mul_apply, mul_inv_cancel, Perm.one_apply]

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem exists_conj_le {M X : Subgroup G} (hT : quasithinIsSylowTwo T) (hTM : T ≤ M)
    (hXM : X ≤ M) (hX : IsPGroup 2 X) : ∃ m ∈ M, conjSubgroup X m⁻¹ ≤ T := by
  obtain ⟨m, hm, hmX⟩ := S126L19c.exists_conjSub_le hT hTM hXM hX
  refine ⟨m, hm, fun x hx => hmX ?_⟩
  rw [B6.mem_conjSub]
  rw [mem_conjSubgroup_iff, inv_inv] at hx
  exact hx

omit [IsMulCommutative ↥V] in
theorem normalizer_L_le (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) :=
  (facts h1222 hH).2.2.2.resolve_right hZ

theorem card_V128 (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : Nat.card V = 128 := by
  rw [card_V F, (part2 h1222 hH hZ).1]

theorem isPGroup_conj (h1222 : Stmt12_2_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) (g : G) :
    IsPGroup 2 (conjSubgroup V g) :=
  IsPGroup.of_card (n := 7) (by rw [E3.card_conjSubgroup, card_V128 h1222 F hH hZ]; norm_num)

theorem coreAct_fix {u : Fin 8 → ZMod 2} (hu0 : ∑ i, u i = 0) {σ : Perm (Fin 8)}
    (hσ : σ ∈ fixSub u) :
    coreAct 8 σ ⟨Multiplicative.ofAdd u, (mem_coreMod).2 hu0⟩ =
      ⟨Multiplicative.ofAdd u, (mem_coreMod).2 hu0⟩ := by
  apply Subtype.ext
  rw [coreAct_coe]
  apply Multiplicative.toAdd.injective
  funext i
  rw [permAct_apply, toAdd_ofAdd]
  have h1 := hσ (σ⁻¹ i)
  rw [← Perm.mul_apply, mul_inv_cancel, Perm.one_apply] at h1
  exact h1.symm

theorem card_ge_four_of_three {H R : Subgroup (Perm (Fin 8))} (hHR : H ≤ R)
    (hR : Nat.card R = 16) {b₁ b₂ : Perm (Fin 8)} (h₁ : b₁ ∈ H) (h₂ : b₂ ∈ H) (h₁1 : b₁ ≠ 1)
    (h₂1 : b₂ ≠ 1) (h12 : b₁ ≠ b₂) : 4 ≤ Nat.card H := by
  classical
  have h3 : 3 ≤ Nat.card H := by
    have hsub : ({1, b₁, b₂} : Finset (Perm (Fin 8))) ⊆ (H : Set (Perm (Fin 8))).toFinset := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Set.mem_toFinset]
      rcases hx with rfl | rfl | rfl
      · exact H.one_mem
      · exact h₁
      · exact h₂
    have h4 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨h₁1.symm, h₂1.symm⟩),
      Finset.card_insert_of_notMem (by simpa using h12), Finset.card_singleton] at h4
    have h5 : (H : Set (Perm (Fin 8))).toFinset.card = Nat.card H := by
      rw [← Nat.card_eq_card_toFinset]
      rfl
    omega
  have hdvd := Subgroup.card_dvd_of_le hHR
  rw [hR, show (16 : ℕ) = 2 ^ 4 by norm_num] at hdvd
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk] at h3 ⊢
  have hk2 : 2 ≤ k := by
    by_contra hc
    interval_cases k <;> simp at h3
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2

theorem main_claim (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (hS8 : FactS8ElemAbE8) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {g : G}
    (hk : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (L : Set G)) ≤ 1)
    (hVN : ¬ V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)) : False := by
  obtain ⟨E⟩ := exists_frame126E h1222 F hH hZ
  have hLV := normalizer_L_le h1222 hH hZ
  set Vg := conjSubgroup V g with hVgdef
  set A := Vg ⊓ Subgroup.normalizer (L : Set G) with hAdef
  have hAL : A ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hAV : A ≤ Subgroup.normalizer (V : Set G) := hAL.trans hLV
  have hAVg : A ≤ Vg := inf_le_left
  set ν := nu F hH hAL hAV with hνdef
  have hgN : g ∉ Subgroup.normalizer (V : Set G) := fun h => hVN (by
    rw [hVgdef, conjSubgroup_eq_iff_mem_normalizer.2 h]
    exact Subgroup.le_normalizer)
  have hr : (4 : ℕ∞) ≤ E3.rParam V := (rParam_bounds h331 h1222 h1262 F hH hfus).2 hZ
  have hVg128 : Nat.card Vg = 128 := by
    rw [hVgdef, E3.card_conjSubgroup, card_V128 h1222 F hH hZ]
  have hVg2 : IsPGroup 2 Vg := isPGroup_conj h1222 F hH hZ g
  have hCV : Nat.card ↥(Vg ⊓ Subgroup.centralizer (V : Set G)) ≤ 8 := by
    have h1 := hr.trans (E3.e3_4_two hVN)
    have h2 : 4 ≤ E3.mQuot Vg (Vg ⊓ Subgroup.centralizer (V : Set G)) := by exact_mod_cast h1
    have h3 := E3.card_eq_two_pow_mul hVg2
      (inf_le_left : Vg ⊓ Subgroup.centralizer (V : Set G) ≤ Vg)
    rw [hVg128] at h3
    have h4 : 2 ^ 4 ≤ 2 ^ E3.mQuot Vg (Vg ⊓ Subgroup.centralizer (V : Set G)) :=
      Nat.pow_le_pow_right (by norm_num) h2
    nlinarith
  have hA64 : 64 ≤ Nat.card A := by
    have h3 := E3.card_eq_two_pow_mul hVg2 hAVg
    rw [hVg128] at h3
    have h4 : 2 ^ E3.mQuot Vg A ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk
    nlinarith
  have hcardA : Nat.card A = Nat.card ν.ker * Nat.card ν.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ν.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ν).toEquiv, mul_comm]
  have hker : Nat.card ν.ker ≤ 8 := by
    refine le_trans (Nat.card_le_card_of_injective (fun x : ν.ker => (⟨((x : ↥A) : G),
      hAVg (x : ↥A).2, (nu_eq_one_iff F hH hAL hAV _).1 x.2⟩ :
        ↥(Vg ⊓ Subgroup.centralizer (V : Set G)))) ?_) hCV
    intro x y h
    have h' := congrArg (fun z : ↥(Vg ⊓ Subgroup.centralizer (V : Set G)) => (z : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hkpos : 0 < Nat.card ν.ker := Nat.card_pos
  have hR8 : 8 ≤ Nat.card ν.range := by nlinarith
  have hRcomm : ∀ σ ∈ ν.range, ∀ τ ∈ ν.range, σ * τ = τ * σ := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul,
      show x * y = y * x from Subtype.ext (conj_comm (hAVg x.2) (hAVg y.2))]
  have hRinv : ∀ σ ∈ ν.range, σ * σ = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_mul, show x * x = 1 from Subtype.ext (mul_self_conj h1222 hH (hAVg x.2)), map_one]
  obtain ⟨hR16, hW1, hW2⟩ := hS8 ν.range hRcomm hRinv
  obtain ⟨H, hHR, hH4, a, ha, u, hu0, huH, hw0, hw4⟩ : ∃ H : Subgroup (Perm (Fin 8)),
      H ≤ ν.range ∧ Nat.card ν.range ≤ 4 * Nat.card H ∧ ∃ a ∈ ν.range, ∃ u : Fin 8 → ZMod 2,
        ∑ i, u i = 0 ∧ H ≤ fixSub u ∧
        (Finset.univ.filter fun i => u i + u (a i) ≠ 0).card ≠ 0 ∧
        (Finset.univ.filter fun i => u i + u (a i) ≠ 0).card ≠ 4 := by
    by_cases h16 : Nat.card ν.range = 16
    · obtain ⟨a, ha, b₁, hb₁, b₂, hb₂, hb₁1, hb₂1, hb12, u, hu0, hu1, hu2, hw0, hw4⟩ := hW2 h16
      have hHR : Subgroup.closure {b₁, b₂} ≤ ν.range := (Subgroup.closure_le _).2 (by
        intro x hx
        rcases hx with rfl | rfl
        exacts [hb₁, hb₂])
      refine ⟨Subgroup.closure {b₁, b₂}, hHR, ?_, a, ha, u, hu0, (Subgroup.closure_le _).2 ?_, hw0,
        hw4⟩
      · have := card_ge_four_of_three hHR h16 (Subgroup.subset_closure (Set.mem_insert _ _))
          (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) hb₁1 hb₂1 hb12
        omega
      · intro x hx
        rcases hx with rfl | rfl
        exacts [hu1, hu2]
    · have hdvd : Nat.card ν.range ∣ 2 ^ 7 := by
        have h1 : Nat.card ν.range ∣ Nat.card A := Dvd.intro_left _ hcardA.symm
        have h2 : Nat.card A ∣ Nat.card Vg := Subgroup.card_dvd_of_le hAVg
        rw [hVg128] at h2
        exact h1.trans h2
      obtain ⟨k, -, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have h8 : Nat.card ν.range = 8 := by
        rw [hk'] at hR8 hR16 h16 ⊢
        have hk3 : 3 ≤ k := by
          by_contra hc
          interval_cases k <;> simp at hR8
        have hk4 : k ≤ 4 := by
          by_contra hc
          push Not at hc
          have : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hc
          omega
        interval_cases k
        · rfl
        · exact absurd rfl h16
      obtain ⟨a, ha, b, hb, hb1, u, hu0, hub, hw0, hw4⟩ := hW1 hR8
      refine ⟨Subgroup.zpowers b, Subgroup.zpowers_le.2 hb, ?_, a, ha, u, hu0,
        Subgroup.zpowers_le.2 hub, hw0, hw4⟩
      rw [h8, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hRinv b hb) hb1]
  set B : Subgroup G := (H.comap ν).map A.subtype with hBdef
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hcardB : Nat.card B = Nat.card ν.ker * Nat.card H := by
    rw [hBdef, Subgroup.card_map_of_injective A.subtype_injective,
      card_comap_of_le_range ν hHR]
  have hB16 : 16 ≤ Nat.card B := by
    rw [hcardB]
    nlinarith
  have hmB : E3.mQuot Vg B ≤ 3 := by
    have h3 := E3.card_eq_two_pow_mul hVg2 (hBA.trans hAVg)
    rw [hVg128] at h3
    by_contra hc
    push Not at hc
    have : 2 ^ 4 ≤ 2 ^ E3.mQuot Vg B := Nat.pow_le_pow_right (by norm_num) hc
    nlinarith
  have hCB : V ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (Vg : Set G) := by
    by_contra hc
    have h1 := E3.e3_4_one (le_inf (hBA.trans hAVg) (hBA.trans hAV)) hc
    have h2 : E3.rParam V ≤ 3 := h1.trans (by exact_mod_cast hmB)
    exact absurd (hr.trans h2) (by decide)
  set m : ↥(coreMod 8) := ⟨Multiplicative.ofAdd u, (mem_coreMod).2 hu0⟩ with hmdef
  set v : ↥V := E.γ.symm m with hvdef
  have hvB : (v : G) ∈ V ⊓ Subgroup.centralizer (B : Set G) := by
    refine ⟨v.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h1 := E.act x (hAL x.2) (hAV x.2) _ (actsAs_nu F hH hAL hAV x) v
      ⟨x * v * x⁻¹, conj_mem (hAV x.2) v⟩ rfl
    rw [hvdef, MulEquiv.apply_symm_apply, coreAct_fix hu0 (huH hx)] at h1
    have h2 : (⟨x * v * x⁻¹, conj_mem (hAV x.2) v⟩ : ↥V) = v := by
      apply E.γ.injective
      rw [h1, hvdef, MulEquiv.apply_symm_apply]
    have h3 : (x : G) * v * (x : G)⁻¹ = v := congrArg Subtype.val h2
    show (x : G) * v = v * x
    calc (x : G) * v = x * v * (x : G)⁻¹ * x := by group
      _ = v * x := by rw [h3]
  obtain ⟨xa, hxa⟩ := ha
  have hvN : (v : G) ∈ Subgroup.normalizer (Vg : Set G) := hCB hvB
  set w : ↥V := ⟨xa * v * xa⁻¹, conj_mem (hAV xa.2) v⟩ with hw
  have hcG : ((v * w⁻¹ : ↥V) : G) = v * xa * (v : G)⁻¹ * xa⁻¹ := by
    simp only [hw, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hcU : ((v * w⁻¹ : ↥V) : G) ∈ V ⊓ Vg := by
    refine ⟨(v * w⁻¹).2, ?_⟩
    rw [hcG]
    have h1 : (v : G) * xa * (v : G)⁻¹ ∈ Vg :=
      (Subgroup.mem_normalizer_iff.1 hvN _).1 (hAVg xa.2)
    exact Vg.mul_mem h1 (Vg.inv_mem (hAVg xa.2))
  have ha2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hRinv a ⟨xa, hxa⟩)
  have hγc : Multiplicative.toAdd ((E.γ (v * w⁻¹) : ↥(coreMod 8)) : PermMod 8) =
      fun i => u i + u (a i) := by
    have h1 := E.act xa (hAL xa.2) (hAV xa.2) _ (actsAs_nu F hH hAL hAV xa) v w rfl
    rw [map_mul, map_inv, h1, hvdef, MulEquiv.apply_symm_apply]
    funext i
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coreAct_coe, toAdd_mul, toAdd_inv, Pi.add_apply,
      Pi.neg_apply, permAct_apply, hxa, ha2, ZMod.neg_eq_self_mod_two]
    rfl
  have hc1 : ((v * w⁻¹ : ↥V) : G) ≠ 1 := by
    intro h
    have h2 : v * w⁻¹ = 1 := Subtype.ext h
    rw [h2, map_one] at hγc
    apply hw0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hi
    apply hi
    have := congrFun hγc i
    rw [← this]
    rfl
  obtain ⟨hcV, h4⟩ := wt4_of_mem_inter h331 h1222 h1262 F hH hfus hgN hcU hc1
  have h5 := ew_of_wt4 E h4
  apply hw4
  rw [← h5]
  change _ = (Finset.univ.filter fun i =>
    Multiplicative.toAdd ((E.γ (v * w⁻¹) : ↥(coreMod 8)) : PermMod 8) i ≠ 0).card
  rw [hγc]

omit [Finite G] [IsMulCommutative ↥V] in
theorem commutator_le_left_of {A B : Subgroup G} (h : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have h1 : y * x⁻¹ * y⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (h hy) _).1 (A.inv_mem hx)
  rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
  exact A.mul_mem hx h1

omit [Finite G] [IsMulCommutative ↥V] in
theorem commutator_le_right_of {A B : Subgroup G} (h : A ≤ Subgroup.normalizer (B : Set G)) :
    ⁅A, B⁆ ≤ B := by
  rw [Subgroup.commutator_comm]
  exact commutator_le_left_of h

theorem le_centralizer_of_le_T (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (hS8 : FactS8ElemAbE8) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {g : G} (hgT : conjSubgroup V g ≤ T) :
    conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := by
  by_contra hc
  have hne : ⁅V, conjSubgroup V g⁆ ≠ ⊥ := by
    rw [Ne, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hc
  by_cases hVN : V ≤ Subgroup.normalizer (conjSubgroup V g : Set G)
  · have hTV := (facts h1222 hH).2.1
    have hle1 : ⁅V, conjSubgroup V g⁆ ≤ V := commutator_le_left_of (hgT.trans hTV)
    have hle2 : ⁅V, conjSubgroup V g⁆ ≤ conjSubgroup V g := commutator_le_right_of hVN
    have hgN : g ∉ Subgroup.normalizer (V : Set G) := by
      intro h
      apply hne
      rw [conjSubgroup_eq_iff_mem_normalizer.2 h, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : ↥V) ⟨x, hx⟩)
    exact hZ (bot_of_hyp4 h331 h1222 h1262 F hH hfus ⟨hgN, hne, le_inf hle1 hle2⟩)
  · refine main_claim h331 h1222 h1262 hS8 F hH hfus hZ ?_ hVN
    rw [inf_eq_left.2 (hgT.trans hH.hyp.normalizes), E3.mQuot_self]
    exact zero_le_one

theorem le_centralizer_of_le_M (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (hS8 : FactS8ElemAbE8) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {g : G}
    (hgM : conjSubgroup V g ≤ Subgroup.normalizer (L : Set G)) :
    conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := by
  have hLV := normalizer_L_le h1222 hH hZ
  obtain ⟨m, hm, hmT⟩ := exists_conj_le hH.hyp.sylow hH.hyp.normalizes hgM
    (isPGroup_conj h1222 F hH hZ g)
  rw [conjSubgroup_conjSubgroup] at hmT
  have h1 := le_centralizer_of_le_T h331 h1222 h1262 hS8 F hH hfus hZ hmT
  have h2 := E3.conjSubgroup_mono_left m h1
  rwa [conjSubgroup_conjSubgroup, inv_mul_cancel_right, E3.conjSubgroup_centralizer,
    conjSubgroup_eq_iff_mem_normalizer.2 (hLV hm)] at h2

theorem le_normalizer_of_mQuot_le (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h1262 : Theorem12_6_2) (hS8 : FactS8ElemAbE8) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) {g : G}
    (hk : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (L : Set G)) ≤ 1) :
    conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) := by
  by_contra hVg
  refine main_claim h331 h1222 h1262 hS8 F hH hfus hZ hk fun hVN => hVg ?_
  have hNV := S126L20c.normalizer_V_le h331 h1222 F hH
  have hM : conjSubgroup V g⁻¹ ≤ Subgroup.normalizer (L : Set G) := by
    have h1 := E3.conjSubgroup_mono_left g⁻¹ hVN
    rw [E3.conjSubgroup_normalizer, E3.conjSubgroup_conj_inv] at h1
    exact h1.trans hNV
  have h1 := le_centralizer_of_le_M h331 h1222 h1262 hS8 F hH hfus hZ hM
  have h2 := E3.conjSubgroup_mono_left g h1
  rw [E3.conjSubgroup_inv_conj, E3.conjSubgroup_centralizer] at h2
  exact (Subgroup.le_centralizer_iff.1 h2).trans (Subgroup.centralizer_le_normalizer _)

theorem one_lt_wParam (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (hS8 : FactS8ElemAbE8) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hfus : ∀ u ∈ V, ∀ g : G, g * u * g⁻¹ ∈ V → ∃ l ∈ L, l * u * l⁻¹ = g * u * g⁻¹)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) : 1 < E3.wParam T V := by
  have hNV := S126L20c.normalizer_V_le h331 h1222 F hH
  have hle : ∀ j : ℕ, j ≤ 1 → E3.wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    intro j hj
    refine iSup₂_le fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm⟩ := hA
    refine le_inf hAT (hAg.trans ?_)
    have hk : E3.mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (L : Set G)) ≤
        1 := by
      calc _ ≤ E3.mQuot (conjSubgroup V g) A :=
            E3.mQuot_mono (le_inf hAg (hAT.trans hH.hyp.normalizes))
        _ = j := hm
        _ ≤ 1 := hj
    exact le_centralizer_of_le_M h331 h1222 h1262 hS8 F hH hfus hZ
      ((le_normalizer_of_mQuot_le h331 h1222 h1262 hS8 F hH hfus hZ hk).trans hNV)
  have h2 : (2 : ℕ∞) ≤ E3.wParam T V := by
    refine le_iInf₂ fun j hj => ?_
    by_contra hc
    push Not at hc
    have hj1 : j ≤ 1 := by
      have : (j : ℕ∞) < 2 := hc
      exact_mod_cast Order.le_of_lt_add_one (by simpa using this)
    exact hj (hle j hj1)
  exact lt_of_lt_of_le (by norm_num) h2

end S126L22

theorem lemma12_6_22_of (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) (h1262 : Theorem12_6_2)
    (h1219 : Lemma12_6_19) (hS8 : FactS8ElemAbE8) : Lemma12_6_22 := by
  intro G _ _ T L V _ F hH hZ
  have hfus := (h1219 G T L V F hH).1
  refine ⟨iSup₂_le fun A hA => ?_,
    fun g hk => S126L22.le_normalizer_of_mQuot_le h331 h1222 h1262 hS8 F hH hfus hZ hk,
    S126L22.one_lt_wParam h331 h1222 h1262 hS8 F hH hfus hZ⟩
  obtain ⟨hAT, g, hAg, hm⟩ := hA
  have hAeq : A = conjSubgroup V g :=
    (E3.mQuot_eq_zero_iff (S126L22.isPGroup_conj h1222 F hH hZ g) hAg).1 hm
  rw [hAeq] at hAT ⊢
  exact S126L22.le_centralizer_of_le_T h331 h1222 h1262 hS8 F hH hfus hZ hAT

end CFSG.Quasithin.H13
