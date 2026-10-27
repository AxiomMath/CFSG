module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderClassicalCore
public import CFSG.LocalAnalysis.StandardType.GGSixBstarRestSL

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace NoOffPSLRest

open NoOffenderClassical

section Weight

variable {G : Type*} [Group G] {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_supp_perm_of_single {p : ℕ} (hp : p.Prime) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {Bs : Subgroup G} {κ : G → ι → Fˣ} (h : Coords p Bs κ) (hBp : ∀ b ∈ Bs, b ^ p = 1)
    {e : G} (heB : e ∈ Subgroup.normalizer (Bs : Set G))
    (hsingle : ∀ b ∈ Bs, ∀ i, (∀ j, κ b j ≠ 1 ↔ j = i) →
      ∃ i', ∀ j, κ (e * b * e⁻¹) j ≠ 1 ↔ j = i') :
    ∃ τ : Equiv.Perm ι, ∀ b ∈ Bs, ∀ i, κ (e * b * e⁻¹) (τ i) = 1 ↔ κ b i = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Fact p.Prime := ⟨hp⟩
  have hconj : ∀ b ∈ Bs, e * b * e⁻¹ ∈ Bs := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp heB b).mp hb
  set ζu : Fˣ := (hζ.isUnit hp.ne_zero).unit with hζudef
  have hζu : (ζu : F) = ζ := IsUnit.unit_spec _
  have hζup : ζu ^ p = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, hζu, hζ.pow_eq_one, Units.val_one])
  have hζu1 : ζu ≠ 1 := fun h1 => hζ.ne_one hp.one_lt (by rw [← hζu, h1, Units.val_one])
  have hgen : ∀ z₀ z : Fˣ, z₀ ^ p = 1 → z₀ ≠ 1 → z ^ p = 1 → ∃ c < p, z₀ ^ c = z := by
    intro z₀ z hz₀ hz₀1 hz
    have ho : orderOf z₀ = p := orderOf_eq_prime hz₀ hz₀1
    have hprim : IsPrimitiveRoot (z₀ : F) p :=
      IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr ho)
    obtain ⟨c, hc, hcz⟩ := hprim.eq_pow_of_pow_eq_one (ξ := (z : F))
      (by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one])
    exact ⟨c, hc, Units.ext (by rw [Units.val_pow_eq_pow_val, hcz])⟩
  have hord : ∀ z : Fˣ, z ^ p = 1 → z ≠ 1 → ∀ c : ℕ, z ^ c = 1 ↔ p ∣ c := by
    intro z hz hz1 c
    rw [← orderOf_eq_prime hz hz1]
    exact orderOf_dvd_iff_pow_eq_one.symm
  have haxis : ∀ i, ∃ a ∈ Bs, κ a = Pi.mulSingle i ζu := fun i => h.surj _ fun j => by
    by_cases hj : j = i
    · rw [hj, Pi.mulSingle_eq_same, hζup]
    · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  choose a ha hai using haxis
  have hsupp : ∀ i j, κ (a i) j ≠ 1 ↔ j = i := fun i j => by
    rw [hai]
    by_cases hj : j = i
    · subst hj
      simp only [Pi.mulSingle_eq_same, ne_eq, hζu1, not_false_eq_true]
    · simp only [Pi.mulSingle_eq_of_ne hj, ne_eq, not_true_eq_false, hj]
  choose τ₀ hτ₀ using fun i => hsingle (a i) (ha i) i (hsupp i)
  set w : ι → Fˣ := fun i => κ (e * a i * e⁻¹) (τ₀ i) with hw
  have hw1 : ∀ i, w i ≠ 1 := fun i => (hτ₀ i (τ₀ i)).mpr rfl
  have hwp : ∀ i, w i ^ p = 1 := fun i =>
    h.pow_p (hconj _ (ha i)) (by rw [conj_pow, hBp _ (ha i), mul_one, mul_inv_cancel]) (τ₀ i)
  have hκa : ∀ i, κ (e * a i * e⁻¹) = Pi.mulSingle (τ₀ i) (w i) := fun i => by
    funext j
    by_cases hj : j = τ₀ i
    · subst hj
      rw [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hj]
      by_contra hne
      exact hj ((hτ₀ i j).mp hne)
  have hinj : Function.Injective τ₀ := by
    intro i i' hii'
    by_contra hne
    obtain ⟨c, -, hc⟩ := hgen (w i) (w i') (hwp i) (hw1 i) (hwp i')
    have h1 : κ (e * a i ^ c * e⁻¹) = κ (e * a i' * e⁻¹) := by
      rw [← conj_pow, h.pow (hconj _ (ha i)), hκa, hκa, ← Pi.mulSingle_pow, hc, hii']
    have h2 : e * a i ^ c * e⁻¹ = e * a i' * e⁻¹ :=
      h.inj _ (hconj _ (Bs.pow_mem (ha i) c)) _ (hconj _ (ha i')) h1
    have h3 : a i ^ c = a i' := by
      have := congrArg (fun y => e⁻¹ * y * e) h2
      simpa [mul_assoc] using this
    have h4 := congrFun (congrArg κ h3) i'
    rw [h.pow (ha i), hai, hai, ← Pi.mulSingle_pow, Pi.mulSingle_eq_of_ne (Ne.symm hne),
      Pi.mulSingle_eq_same] at h4
    exact hζu1 h4.symm
  have hbij : Function.Bijective τ₀ := ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩
  have key : ∀ N : ℕ, ∀ b ∈ Bs, (Finset.univ.filter fun j => κ b j ≠ 1).card = N →
      ∀ l, (κ (e * b * e⁻¹) (τ₀ l) = 1 ↔ κ b l = 1) := by
    intro N
    induction N with
    | zero =>
      intro b hb hN l
      have hb1 : b = 1 := by
        refine h.inj b hb 1 Bs.one_mem (funext fun j => ?_)
        rw [h.one, Pi.one_apply]
        by_contra hne
        have hj : j ∈ Finset.univ.filter fun j => κ b j ≠ 1 := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hne
        rw [Finset.card_eq_zero.mp hN] at hj
        exact Finset.notMem_empty j hj
      subst hb1
      rw [mul_one, mul_inv_cancel, h.one]
      simp only [Pi.one_apply]
    | succ N ih =>
      intro b hb hN l
      obtain ⟨j, hj⟩ : ∃ j, κ b j ≠ 1 := by
        obtain ⟨j, hj⟩ := Finset.card_pos.mp (by rw [hN]; exact Nat.succ_pos N)
        exact ⟨j, by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj⟩
      obtain ⟨c, hcp, hc⟩ := hgen ζu (κ b j) hζup hζu1 (h.pow_p hb (hBp b hb) j)
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hc
        exact hj hc.symm
      set b' := b * a j ^ (p - c) with hb'
      have hb'm : b' ∈ Bs := Bs.mul_mem hb (Bs.pow_mem (ha j) _)
      have hκb' : ∀ l, κ b' l = κ b l * (Pi.mulSingle j (ζu ^ (p - c)) : ι → Fˣ) l := fun l => by
        rw [hb', h.mul _ hb _ (Bs.pow_mem (ha j) _), h.pow (ha j), hai, ← Pi.mulSingle_pow,
          Pi.mul_apply]
      have hb'j : κ b' j = 1 := by
        rw [hκb', Pi.mulSingle_eq_same, ← hc, ← pow_add, Nat.add_sub_cancel' hcp.le, hζup]
      have hb'l : ∀ l, l ≠ j → κ b' l = κ b l := fun l hl => by
        rw [hκb', Pi.mulSingle_eq_of_ne hl, mul_one]
      have hN' : (Finset.univ.filter fun l => κ b' l ≠ 1).card = N := by
        have hset : (Finset.univ.filter fun l => κ b' l ≠ 1) =
            (Finset.univ.filter fun l => κ b l ≠ 1).erase j := by
          ext l
          by_cases hl : l = j
          · subst hl
            simp [hb'j]
          · simp [hl, hb'l l hl]
        rw [hset, Finset.card_erase_of_mem (by simpa using hj), hN, Nat.add_sub_cancel]
      have ih' := ih b' hb'm hN'
      have hbb' : b = b' * a j ^ c := by
        rw [hb', mul_assoc, ← pow_add, Nat.sub_add_cancel hcp.le, hBp _ (ha j), mul_one]
      have hκeb : ∀ l', κ (e * b * e⁻¹) l' =
          κ (e * b' * e⁻¹) l' * (Pi.mulSingle (τ₀ j) (w j ^ c) : ι → Fˣ) l' := by
        intro l'
        have e1 : e * b * e⁻¹ = (e * b' * e⁻¹) * (e * a j * e⁻¹) ^ c := by
          rw [hbb', conj_pow]
          group
        rw [e1, h.mul _ (hconj _ hb'm) _ (Bs.pow_mem (hconj _ (ha j)) c),
          h.pow (hconj _ (ha j)), hκa, Pi.mul_apply, ← Pi.mulSingle_pow]
      by_cases hl : l = j
      · subst hl
        rw [hκeb, Pi.mulSingle_eq_same, (ih' l).mpr hb'j, one_mul]
        constructor
        · intro h1
          exact absurd (Nat.eq_zero_of_dvd_of_lt ((hord _ (hwp l) (hw1 l) c).mp h1) hcp) hc0
        · intro h1
          exact absurd h1 hj
      · rw [hκeb, Pi.mulSingle_eq_of_ne (fun h' => hl (hinj h')), mul_one, ← hb'l l hl]
        exact ih' l
  refine ⟨Equiv.ofBijective τ₀ hbij, fun b hb i => ?_⟩
  rw [Equiv.ofBijective_apply]
  exact key _ b hb rfl i

end Weight

section Fix

variable {F : Type} [Field F]

theorem card_fix_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (P Q M : Matrix ι ι F)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Nat.card {v : ι → F // (P * M * Q) *ᵥ v = v} = Nat.card {v : ι → F // M *ᵥ v = v} := by
  refine Nat.card_congr
    { toFun := fun v => ⟨Q *ᵥ v.1, ?_⟩
      invFun := fun w => ⟨P *ᵥ w.1, ?_⟩
      left_inv := fun v => Subtype.ext ?_
      right_inv := fun w => Subtype.ext ?_ }
  · calc M *ᵥ (Q *ᵥ v.1) = Q *ᵥ ((P * M * Q) *ᵥ v.1) := by
          rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQP,
            Matrix.one_mul]
      _ = Q *ᵥ v.1 := by rw [v.2]
  · calc (P * M * Q) *ᵥ (P *ᵥ w.1) = P *ᵥ (M *ᵥ w.1) := by
          rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (P * M), hQP, Matrix.mul_one]
      _ = P *ᵥ w.1 := by rw [w.2]
  · change P *ᵥ (Q *ᵥ v.1) = v.1
    rw [mulVec_mulVec, hPQ, one_mulVec]
  · change Q *ᵥ (P *ᵥ w.1) = w.1
    rw [mulVec_mulVec, hQP, one_mulVec]

theorem card_fix_map {ι : Type*} [Fintype ι] (σ : F ≃+* F) (M : Matrix ι ι F) :
    Nat.card {v : ι → F // M.map σ *ᵥ v = v} = Nat.card {v : ι → F // M *ᵥ v = v} := by
  have key : ∀ v : ι → F, M.map σ *ᵥ (σ ∘ v) = σ ∘ (M *ᵥ v) := fun v => funext fun i =>
    (RingHom.map_mulVec (σ : F →+* F) M v i).symm
  refine Nat.card_congr
    { toFun := fun v => ⟨σ.symm ∘ v.1, ?_⟩
      invFun := fun w => ⟨σ ∘ w.1, ?_⟩
      left_inv := fun v => Subtype.ext (funext fun i => σ.apply_symm_apply _)
      right_inv := fun w => Subtype.ext (funext fun i => σ.symm_apply_apply _) }
  · have h1 := key (σ.symm ∘ v.1)
    have h2 : σ ∘ (σ.symm ∘ v.1) = v.1 := funext fun i => σ.apply_symm_apply _
    rw [h2, v.2] at h1
    funext i
    have h3 := congrFun h1 i
    simp only [Function.comp_apply] at h3 ⊢
    rw [h3, σ.symm_apply_apply]
  · rw [key, w.2]

theorem card_fix_submatrix {ι κ : Type*} [Fintype ι] [Fintype κ] (ε : ι ≃ κ)
    (M : Matrix κ κ F) :
    Nat.card {v : ι → F // M.submatrix ε ε *ᵥ v = v} = Nat.card {v : κ → F // M *ᵥ v = v} := by
  refine Nat.card_congr
    { toFun := fun v => ⟨v.1 ∘ ε.symm, ?_⟩
      invFun := fun w => ⟨w.1 ∘ ε, ?_⟩
      left_inv := fun v => Subtype.ext (funext fun i => by simp)
      right_inv := fun w => Subtype.ext (funext fun i => by simp) }
  · have h1 := v.2
    rw [submatrix_mulVec_equiv] at h1
    funext k
    have h2 := congrFun h1 (ε.symm k)
    simpa using h2
  · have h3 : (w.1 ∘ ε) ∘ ε.symm = w.1 := funext fun k => by simp
    rw [submatrix_mulVec_equiv, h3, w.2]

theorem blockDiagonal_mulVec_apply {m o : Type*} [Fintype m] [Fintype o] [DecidableEq o]
    (D : o → Matrix m m F) (v : m × o → F) (a : m) (i : o) :
    (blockDiagonal D *ᵥ v) (a, i) = (D i *ᵥ fun b => v (b, i)) a := by
  simp only [mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [ite_mul]

theorem card_fix_nsCore [Finite F] {e s r p : ℕ} {C : Matrix (Fin e) (Fin e) F}
    (hCp : C ^ p = 1) (hunit : ∀ j : ℕ, ¬ p ∣ j → IsUnit (C ^ j - 1)) (k : Fin s → ℕ) :
    Nat.card {v : (Fin e × Fin s) ⊕ Fin r → F // SLNS.nsCore C k *ᵥ v = v} =
      Nat.card F ^ (e * (Finset.univ.filter fun i => p ∣ k i).card + r) := by
  classical
  have hfix : ∀ v : (Fin e × Fin s) ⊕ Fin r → F, SLNS.nsCore C k *ᵥ v = v ↔
      ∀ a i, ¬ p ∣ k i → v (Sum.inl (a, i)) = 0 := by
    intro v
    have h1 : SLNS.nsCore C k *ᵥ v = v ↔ (SLNS.nsCore C k - 1) *ᵥ v = 0 := by
      rw [sub_mulVec, one_mulVec, sub_eq_zero]
    rw [h1, RestSL.nsCore_sub_one, fromBlocks_mulVec]
    simp only [zero_mulVec, add_zero]
    constructor
    · intro h0 a i hi
      have h4 : (C ^ k i - 1) *ᵥ (fun b => v (Sum.inl (b, i))) = 0 := by
        funext a'
        have h2 := congrFun h0 (Sum.inl (a', i))
        simp only [Sum.elim_inl, Pi.zero_apply] at h2
        rw [blockDiagonal_mulVec_apply] at h2
        simpa using h2
      obtain ⟨u, hu⟩ := hunit (k i) hi
      have h3 : (fun b => v (Sum.inl (b, i))) = 0 :=
        calc (fun b => v (Sum.inl (b, i))) =
            (((u⁻¹ : (Matrix (Fin e) (Fin e) F)ˣ) : Matrix (Fin e) (Fin e) F) *
              (u : Matrix (Fin e) (Fin e) F)) *ᵥ
              (fun b => v (Sum.inl (b, i))) := by rw [Units.inv_mul, one_mulVec]
          _ = 0 := by rw [← mulVec_mulVec, hu, h4, mulVec_zero]
      exact congrFun h3 a
    · intro h0
      funext x
      rcases x with ⟨a, i⟩ | j
      · simp only [Sum.elim_inl, Pi.zero_apply]
        rw [blockDiagonal_mulVec_apply]
        by_cases hi : p ∣ k i
        · have hCk : C ^ k i = 1 := by
            obtain ⟨c, hc⟩ := hi
            rw [hc, pow_mul, hCp, one_pow]
          rw [hCk, sub_self, zero_mulVec, Pi.zero_apply]
        · have h5 : (fun b => (v ∘ Sum.inl) (b, i)) = 0 := funext fun b => h0 b i hi
          rw [h5, mulVec_zero, Pi.zero_apply]
      · simp
  have e1 : {v : (Fin e × Fin s) ⊕ Fin r → F // SLNS.nsCore C k *ᵥ v = v} ≃
      ((Fin e × {i : Fin s // p ∣ k i}) ⊕ Fin r → F) :=
    { toFun := fun v x =>
        Sum.elim (fun y => v.1 (Sum.inl (y.1, y.2.1))) (fun j => v.1 (Sum.inr j)) x
      invFun := fun w => ⟨fun x => Sum.elim (fun y : Fin e × Fin s =>
          if h : p ∣ k y.2 then w (Sum.inl (y.1, ⟨y.2, h⟩)) else 0) (fun j => w (Sum.inr j)) x,
        (hfix _).mpr fun a i hi => by simp [hi]⟩
      left_inv := fun v => by
        apply Subtype.ext
        funext x
        rcases x with ⟨a, i⟩ | j
        · by_cases hi : p ∣ k i
          · simp [hi]
          · simp [hi, (hfix v.1).mp v.2 a i hi]
        · simp
      right_inv := fun w => by
        funext x
        rcases x with ⟨a, ⟨i, hi⟩⟩ | j
        · simp [hi]
        · simp }
  rw [Nat.card_congr e1, Nat.card_fun, Nat.card_sum, Nat.card_prod, Nat.card_fin, Nat.card_fin,
    Nat.card_eq_fintype_card (α := {i : Fin s // p ∣ k i}), Fintype.card_subtype]

theorem card_fix_nsMat [Finite F] {n e s r p : ℕ} (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    {C : Matrix (Fin e) (Fin e) F} (hCp : C ^ p = 1)
    (hunit : ∀ j : ℕ, ¬ p ∣ j → IsUnit (C ^ j - 1)) (k : Fin s → ℕ) :
    Nat.card {v : Fin n → F // SLNS.nsMat ε C k *ᵥ v = v} =
      Nat.card F ^ (e * (Finset.univ.filter fun i => p ∣ k i).card + r) := by
  rw [SLNS.nsMat, card_fix_submatrix, card_fix_nsCore hCp hunit]

theorem card_filter_eq_of_card_fix_eq [Finite F] {n e s r p : ℕ}
    (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) F} (hCp : C ^ p = 1)
    (hunit : ∀ j : ℕ, ¬ p ∣ j → IsUnit (C ^ j - 1)) (he : e ≠ 0) {k k' : Fin s → ℕ}
    (h : Nat.card {v : Fin n → F // SLNS.nsMat ε C k *ᵥ v = v} =
      Nat.card {v : Fin n → F // SLNS.nsMat ε C k' *ᵥ v = v}) :
    (Finset.univ.filter fun i => p ∣ k i).card = (Finset.univ.filter fun i => p ∣ k' i).card := by
  rw [card_fix_nsMat ε hCp hunit, card_fix_nsMat ε hCp hunit] at h
  have h2 := Nat.pow_right_injective (Finite.one_lt_card (α := F)) h
  have h3 : e * (Finset.univ.filter fun i => p ∣ k i).card =
      e * (Finset.univ.filter fun i => p ∣ k' i).card := Nat.add_right_cancel h2
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he) h3

end Fix

end NoOffPSLRest

end CFSG.StandardType
