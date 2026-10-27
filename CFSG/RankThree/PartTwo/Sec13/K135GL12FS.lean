module

public import CFSG.Quasithin.Vol2.GoldschmidtA128LinMain
public import CFSG.RankThree.PartTwo.Sec13.K135GL12Core

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.K135GL12

open CFSG.Quasithin.Vol2.A128.Lin

private noncomputable def gl12kSum {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    {d : ℕ} (R : (Fin d → ZMod 2) → Module.End F V) {ι : Type*} [Fintype ι]
    (lam : ι → Fin d → ZMod 2) : (∀ i, LinearMap.range (proj R (lam i))) →ₗ[F] V where
  toFun w := ∑ i, (w i : V)
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum]

private theorem gl12kSum_apply {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    {d : ℕ} {R : (Fin d → ZMod 2) → Module.End F V} {ι : Type*} [Fintype ι]
    {lam : ι → Fin d → ZMod 2} (w : ∀ i, LinearMap.range (proj R (lam i))) :
    gl12kSum R lam w = ∑ i, (w i : V) := rfl

private theorem gl12k_isWeight {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]
    {d : ℕ} {R : (Fin d → ZMod 2) → Module.End F V} (hR : IsRep R) {l : Fin d → ZMod 2} {w : V}
    (hw : w ∈ LinearMap.range (proj R l)) : IsWeight R l w := by
  obtain ⟨v, rfl⟩ := hw
  exact hR.isWeight_proj l v

private theorem gl12k_sum_injective {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] {d : ℕ} {R : (Fin d → ZMod 2) → Module.End F V} (hR : IsRep R) (h2 : (2 : F) ≠ 0)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {lam : ι → Fin d → ZMod 2}
    (hlam : Function.Injective lam) : Function.Injective (gl12kSum R lam) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  rw [gl12kSum_apply] at hw
  funext i
  apply Subtype.ext
  have h := congrArg (proj R (lam i)) hw
  rw [map_sum, map_zero] at h
  have hpj : ∀ j, proj R (lam i) (w j : V) = if lam i = lam j then (w j : V) else 0 :=
    fun j => proj_apply_of_isWeight h2 (gl12k_isWeight hR (w j).2)
  have hsum_eq : ∑ j, proj R (lam i) (w j : V) = (w i : V) := by
    rw [Finset.sum_eq_single i]
    · rw [hpj i, if_pos rfl]
    · intro j _ hj
      have hne : lam i ≠ lam j := fun h' => hj (hlam h').symm
      rw [hpj j, if_neg hne]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
  rw [hsum_eq] at h
  exact h

private theorem gl12k_sum_finrank_le {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {d : ℕ} {R : (Fin d → ZMod 2) → Module.End F V}
    (hR : IsRep R) (h2 : (2 : F) ≠ 0) (T : Finset (Fin d → ZMod 2)) {K : Submodule F V}
    (hK : ∀ l ∈ T, LinearMap.range (proj R l) ≤ K) :
    ∑ l ∈ T, Module.finrank F (LinearMap.range (proj R l)) ≤ Module.finrank F K := by
  have hinj := gl12k_sum_injective hR h2 (lam := fun i : T => (i : Fin d → ZMod 2))
    Subtype.val_injective
  have hle : LinearMap.range (gl12kSum R (fun i : T => (i : Fin d → ZMod 2))) ≤ K := by
    rintro _ ⟨w, rfl⟩
    rw [gl12kSum_apply]
    exact Submodule.sum_mem K fun i _ => hK _ i.2 (w i).2
  have e1 := LinearMap.finrank_range_of_inj hinj
  rw [Module.finrank_pi_fintype] at e1
  have e2 := Submodule.finrank_mono hle
  rw [e1, Finset.sum_coe_sort (s := T)
    (f := fun l => Module.finrank F (LinearMap.range (proj R l)))] at e2
  exact e2

private theorem gl12k_finrank_le_sum {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {d : ℕ} {R : (Fin d → ZMod 2) → Module.End F V}
    (hR : IsRep R) (h2 : (2 : F) ≠ 0) :
    Module.finrank F V ≤ ∑ l, Module.finrank F (LinearMap.range (proj R l)) := by
  have hsurj : Function.Surjective (gl12kSum R (fun l : Fin d → ZMod 2 => l)) := by
    intro v
    refine ⟨fun l => ⟨proj R l v, LinearMap.mem_range_self (proj R l) v⟩, ?_⟩
    rw [gl12kSum_apply]
    exact hR.sum_proj_apply h2 v
  have h1 := LinearMap.finrank_le_finrank_of_surjective hsurj
  rw [Module.finrank_pi_fintype] at h1
  exact h1

private theorem gl12k_card {d : ℕ} : (Finset.univ : Finset (Fin d → ZMod 2)).card = 2 ^ d := by
  simp [Finset.card_univ, Fintype.card_fun]

private theorem gl12k_count {d : ℕ} (l : Fin d → ZMod 2) :
    2 ^ (d - 1) - 1 ≤ ((Finset.univ.erase (0 : Fin d → ZMod 2)).filter
      (fun x => l ⬝ᵥ x = 0)).card := by
  have hA : 2 ^ (d - 1) ≤ (Finset.univ.filter (fun x : Fin d → ZMod 2 => l ⬝ᵥ x = 0)).card := by
    by_cases hl : l = 0
    · subst hl
      have hall : Finset.univ.filter (fun x : Fin d → ZMod 2 => (0 : Fin d → ZMod 2) ⬝ᵥ x = 0) =
          Finset.univ := by
        ext x
        simp
      rw [hall, gl12k_card]
      exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le d 1)
    · obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hl (funext hcon)
      have hli : l i = 1 := (zmod_two_cases _).resolve_left hi
      have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) i.isLt
      have he : l ⬝ᵥ (Pi.single i 1 : Fin d → ZMod 2) = 1 := by
        rw [dotProduct_single, hli, mul_one]
      have hBA : (Finset.univ.filter (fun x : Fin d → ZMod 2 => ¬ (l ⬝ᵥ x = 0))).card ≤
          (Finset.univ.filter (fun x : Fin d → ZMod 2 => l ⬝ᵥ x = 0)).card := by
        apply Finset.card_le_card_of_injOn (fun x => x + (Pi.single i 1 : Fin d → ZMod 2))
        · intro x hx
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
          rw [dotProduct_add, he]
          rcases zmod_two_cases (l ⬝ᵥ x) with h | h
          · exact absurd h hx
          · rw [h]
            decide
        · intro x _ y _ hxy
          exact add_right_cancel hxy
      have hsum : (Finset.univ.filter (fun x : Fin d → ZMod 2 => l ⬝ᵥ x = 0)).card +
          (Finset.univ.filter (fun x : Fin d → ZMod 2 => ¬ (l ⬝ᵥ x = 0))).card = 2 ^ d := by
        rw [Finset.card_filter_add_card_filter_not, gl12k_card]
      have h2d : 2 ^ d = 2 * 2 ^ (d - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      omega
  have h0 : (0 : Fin d → ZMod 2) ∈ Finset.univ.filter (fun x => l ⬝ᵥ x = 0) := by
    simp
  rw [Finset.filter_erase, Finset.card_erase_of_mem h0]
  omega

theorem gl12_fs_core {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {d : ℕ} {R : (Fin d → ZMod 2) → Module.End F V} (hR : IsRep R) {m : ℕ}
    (hfix : ∀ x : Fin d → ZMod 2, x ≠ 0 → Module.finrank F (LinearMap.ker (R x - 1)) ≤ m) :
    (2 ^ (d - 1) - 1) * Module.finrank F V ≤ m * (2 ^ d - 1) := by
  have h1 : Module.finrank F V ≤ ∑ l, Module.finrank F (LinearMap.range (proj R l)) :=
    gl12k_finrank_le_sum hR h2
  have h5 : ∀ x ∈ (Finset.univ.erase (0 : Fin d → ZMod 2)),
      ∑ l ∈ Finset.univ.filter (fun l => l ⬝ᵥ x = 0),
        Module.finrank F (LinearMap.range (proj R l)) ≤ m := by
    intro x hx
    have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
    have hK : ∀ l ∈ Finset.univ.filter (fun l => l ⬝ᵥ x = 0),
        LinearMap.range (proj R l) ≤ LinearMap.ker (R x - 1) := by
      intro l hl
      have hdot : l ⬝ᵥ x = 0 := (Finset.mem_filter.mp hl).2
      rintro _ ⟨v, rfl⟩
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hR.isWeight_proj l v x, chi_eq_one hdot,
        one_smul, Module.End.one_apply, sub_self]
    exact (gl12k_sum_finrank_le hR h2 _ hK).trans (hfix x hx0)
  have h4 : ∑ x ∈ (Finset.univ.erase (0 : Fin d → ZMod 2)),
      ∑ l ∈ Finset.univ.filter (fun l => l ⬝ᵥ x = 0),
        Module.finrank F (LinearMap.range (proj R l)) =
      ∑ l, ((Finset.univ.erase (0 : Fin d → ZMod 2)).filter (fun x => l ⬝ᵥ x = 0)).card *
        Module.finrank F (LinearMap.range (proj R l)) := by
    rw [Finset.sum_comm' (t' := Finset.univ)
      (s' := fun l => (Finset.univ.erase (0 : Fin d → ZMod 2)).filter (fun x => l ⬝ᵥ x = 0))]
    · simp only [Finset.sum_const, smul_eq_mul]
    · intro x l
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, and_true] <;>
        tauto
  have h6 : ∑ x ∈ (Finset.univ.erase (0 : Fin d → ZMod 2)), m = (2 ^ d - 1) * m := by
    rw [Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : Fin d → ZMod 2)), gl12k_card]
  calc (2 ^ (d - 1) - 1) * Module.finrank F V
      ≤ (2 ^ (d - 1) - 1) * ∑ l, Module.finrank F (LinearMap.range (proj R l)) :=
        Nat.mul_le_mul_left _ h1
    _ = ∑ l, (2 ^ (d - 1) - 1) * Module.finrank F (LinearMap.range (proj R l)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ l, ((Finset.univ.erase (0 : Fin d → ZMod 2)).filter (fun x => l ⬝ᵥ x = 0)).card *
          Module.finrank F (LinearMap.range (proj R l)) :=
        Finset.sum_le_sum fun l _ => Nat.mul_le_mul_right _ (gl12k_count l)
    _ = ∑ x ∈ (Finset.univ.erase (0 : Fin d → ZMod 2)),
          ∑ l ∈ Finset.univ.filter (fun l => l ⬝ᵥ x = 0),
            Module.finrank F (LinearMap.range (proj R l)) := h4.symm
    _ ≤ ∑ x ∈ (Finset.univ.erase (0 : Fin d → ZMod 2)), m := Finset.sum_le_sum h5
    _ = (2 ^ d - 1) * m := h6
    _ = m * (2 ^ d - 1) := Nat.mul_comm _ _

theorem gl12_n_le_eight_of_elemAbelian_two_aux {S X : Type} [Group S] [Group X] [Finite X] {n : ℕ}
    (hFS : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V] {d : ℕ}
        {R : (Fin d → ZMod 2) → Module.End (ZMod 3) V}, IsRep R → ∀ {m : ℕ}, (∀ x : Fin d → ZMod 2,
        x ≠ 0 → Module.finrank (ZMod 3) (LinearMap.ker (R x - 1)) ≤ m) → (2 ^ (d - 1) - 1) *
        Module.finrank (ZMod 3) V ≤ m * (2 ^ d - 1))
    (ρ : X →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) (K : Subgroup X) [K.Normal]
    (hodd : Odd (Nat.card K)) (e : X ⧸ K ≃* S)
    (hinv : ∀ t : X, orderOf t = 2 →
      Nat.card {v : Fin n → ZMod 3 //
        Matrix.mulVec ((ρ t : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
          Matrix (Fin n) (Fin n) (ZMod 3)) v = v} ≤ 3 ^ 4)
    (U : Subgroup S) (hU2 : ∀ x ∈ U, x ^ 2 = 1) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hcard : Nat.card U = 2 ^ 5) : n ≤ 8 := by
  obtain ⟨Q, hQdef⟩ : ∃ Q : Subgroup (X ⧸ K), Q = U.map e.symm.toMonoidHom := ⟨_, rfl⟩
  have hQcard : Nat.card Q = 2 ^ 5 := by
    rw [hQdef, Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
    exact hcard
  have hQ : IsPGroup 2 Q := IsPGroup.of_card hQcard
  obtain ⟨T, hT, hTQ⟩ := gl12_exists_pSubgroup_map_eq K Q hQ
  have hmemT : ∀ a ∈ T, QuotientGroup.mk' K a ∈ Q := fun a ha => by
    rw [← hTQ]
    exact Subgroup.mem_map_of_mem _ ha
  have hmemQ : ∀ a ∈ T, ∃ u ∈ U, e.symm.toMonoidHom u = QuotientGroup.mk' K a := by
    intro a ha
    have h := hmemT a ha
    rw [hQdef] at h
    exact Subgroup.mem_map.mp h
  have hTK : ∀ t : X, t ∈ T → t ∈ K → t = 1 := by
    intro t htT htK
    obtain ⟨k, hk⟩ := hT ⟨t, htT⟩
    have hk' : t ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hdvd : orderOf t ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hoddt : Odd (orderOf t) := by
      have h1 : orderOf (⟨t, htK⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hodd h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hj0 : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact h
      · exfalso
        obtain ⟨m, hm⟩ := hoddt
        obtain ⟨c, hc⟩ : 2 ∣ orderOf t := by
          rw [hj]
          exact dvd_pow_self 2 h.ne'
        omega
    have h1 : orderOf t = 1 := by rw [hj, hj0, pow_zero]
    exact orderOf_eq_one_iff.1 h1
  have hinj : ∀ a ∈ T, ∀ b ∈ T, QuotientGroup.mk' K a = QuotientGroup.mk' K b → a = b := by
    intro a ha b hb hab
    have h1 : a⁻¹ * b ∈ T := T.mul_mem (T.inv_mem ha) hb
    have h2 : a⁻¹ * b ∈ K := by
      rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker, map_mul, map_inv, hab, inv_mul_cancel]
    exact inv_mul_eq_one.1 (hTK _ h1 h2)
  have hsq : ∀ t ∈ T, t ^ 2 = 1 := by
    intro t ht
    obtain ⟨u, hu, hue⟩ := hmemQ t ht
    have h1 : QuotientGroup.mk' K (t ^ 2) = 1 := by
      rw [map_pow, ← hue, ← map_pow, hU2 u hu, map_one]
    have h2 : t ^ 2 ∈ K := by
      rw [← QuotientGroup.ker_mk' K, MonoidHom.mem_ker]
      exact h1
    exact hTK _ (T.pow_mem ht 2) h2
  have hcommT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := by
    intro a ha b hb
    apply hinj (a * b) (T.mul_mem ha hb) (b * a) (T.mul_mem hb ha)
    obtain ⟨ua, hua, hea⟩ := hmemQ a ha
    obtain ⟨ub, hub, heb⟩ := hmemQ b hb
    rw [map_mul, map_mul, ← hea, ← heb, ← map_mul, ← map_mul, hUc ua hua ub hub]
  have hsqT : ∀ t : T, t * t = 1 := fun t => Subtype.ext (by
    simpa [pow_two] using hsq t.1 t.2)
  have hcommT' : ∀ a b : T, a * b = b * a := fun a b => Subtype.ext (by
    simpa using hcommT a.1 a.2 b.1 b.2)
  have hTcard : Nat.card T = 2 ^ 5 := by
    have hbij : Function.Bijective
        (fun t : T => (⟨QuotientGroup.mk' K (t : X), hmemT (t : X) t.2⟩ : Q)) := by
      constructor
      · intro a b hab
        have h : QuotientGroup.mk' K (a : X) = QuotientGroup.mk' K (b : X) :=
          congrArg Subtype.val hab
        exact Subtype.ext (hinj (a : X) a.2 (b : X) b.2 h)
      · intro q
        have hq : (q : X ⧸ K) ∈ T.map (QuotientGroup.mk' K) := by
          rw [hTQ]
          exact q.2
        obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.mp hq
        exact ⟨⟨t, ht⟩, Subtype.ext hte⟩
    rw [← hQcard]
    exact Nat.card_congr (Equiv.ofBijective _ hbij)
  obtain ⟨d, ⟨φ⟩⟩ := exists_mulEquiv_zmod_two hsqT hcommT'
  have hdcard : Nat.card T = 2 ^ d := by
    rw [← Nat.card_congr φ.toEquiv]
    show Nat.card (Fin d → ZMod 2) = 2 ^ d
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_fin_fun, Nat.card_zmod]
  have hd5 : d = 5 := by
    have h : 2 ^ d = 2 ^ 5 := by rw [← hdcard, hTcard]
    exact Nat.pow_right_injective (le_refl 2) h
  subst hd5
  let g : (Fin 5 → ZMod 2) → X := fun x => ((φ (Multiplicative.ofAdd x) : T) : X)
  let R : (Fin 5 → ZMod 2) → Module.End (ZMod 3) (Fin n → ZMod 3) := fun x =>
    Matrix.toLin' ((ρ (g x) : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
      Matrix (Fin n) (Fin n) (ZMod 3))
  have hR : IsRep R := by
    refine ⟨?_, ?_⟩
    · simp [R, g, ofAdd_zero, Module.End.one_eq_id]
    · intro x y
      simp [R, g, ofAdd_add, Matrix.toLin'_mul, Module.End.mul_eq_comp]
  have hfix : ∀ x : Fin 5 → ZMod 2, x ≠ 0 →
      Module.finrank (ZMod 3) (LinearMap.ker (R x - 1)) ≤ 4 := by
    intro x hx
    have ht1 : g x ≠ 1 := by
      intro h
      apply hx
      have h' : φ (Multiplicative.ofAdd x) = 1 := Subtype.ext h
      exact ofAdd_eq_one.1 (φ.map_eq_one_iff.1 h')
    have ht2 : g x ^ 2 = 1 := hsq (g x) (φ (Multiplicative.ofAdd x)).2
    have hord : orderOf (g x) = 2 := orderOf_eq_prime ht2 ht1
    have hbd := hinv (g x) hord
    have hkereq : Nat.card (LinearMap.ker (R x - 1)) = Nat.card {v : Fin n → ZMod 3 //
        Matrix.mulVec ((ρ (g x) : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
          Matrix (Fin n) (Fin n) (ZMod 3)) v = v} := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      simp [R, LinearMap.mem_ker, sub_eq_zero]
    have hpow : Nat.card (LinearMap.ker (R x - 1)) =
        3 ^ Module.finrank (ZMod 3) (LinearMap.ker (R x - 1)) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 3), Nat.card_zmod]
    have hle : 3 ^ Module.finrank (ZMod 3) (LinearMap.ker (R x - 1)) ≤ 3 ^ 4 := by
      rw [← hpow, hkereq]
      exact hbd
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  have hbound := hFS hR hfix
  rw [Module.finrank_fin_fun] at hbound
  norm_num at hbound
  omega

theorem gl12_n_le_eight_of_elemAbelian_two {S X : Type} [Group S] [Group X] [Finite X] {n : ℕ}
    (ρ : X →* Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) (K : Subgroup X) [K.Normal]
    (hodd : Odd (Nat.card K)) (e : X ⧸ K ≃* S)
    (hinv : ∀ t : X, orderOf t = 2 →
      Nat.card {v : Fin n → ZMod 3 //
        Matrix.mulVec ((ρ t : Matrix.GeneralLinearGroup (Fin n) (ZMod 3)) :
          Matrix (Fin n) (Fin n) (ZMod 3)) v = v} ≤ 3 ^ 4)
    (U : Subgroup S) (hU2 : ∀ x ∈ U, x ^ 2 = 1) (hUc : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x)
    (hcard : Nat.card U = 2 ^ 5) : n ≤ 8 :=
  gl12_n_le_eight_of_elemAbelian_two_aux
    (fun {V} _ _ _ {d} {R} hR {m} hfix => gl12_fs_core (by decide) hR hfix)
    ρ K hodd e hinv U hU2 hUc hcard

end CFSG.RankThree.PartTwo.Sec13.K135GL12
