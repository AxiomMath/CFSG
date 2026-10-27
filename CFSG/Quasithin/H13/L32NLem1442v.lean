module

public import CFSG.Quasithin.H13.L32NLem1442t
public import CFSG.Quasithin.H13.L32NLem1442u
public import CFSG.Quasithin.H13.L32NLem1442r

public section

namespace CFSG.Quasithin.H13.L1442V

open Matrix Equiv Equiv.Perm Mat8Cert L1442M G9MCert L1442U

theorem closure_S3 :
    Subgroup.closure ({finRotate 3, swap (0 : Fin 3) 1} : Set (Perm (Fin 3))) = ⊤ :=
  closure_prime_cycle_swap (by rw [Fintype.card_fin]; exact Nat.prime_three) isCycle_finRotate
    support_finRotate ⟨0, 1, by decide, rfl⟩

theorem closure_S5 :
    Subgroup.closure ({finRotate 5, swap (0 : Fin 5) 1} : Set (Perm (Fin 5))) = ⊤ :=
  closure_prime_cycle_swap (by rw [Fintype.card_fin]; exact Nat.prime_five) isCycle_finRotate
    support_finRotate ⟨0, 1, by decide, rfl⟩

@[expose] def a5a : alternatingGroup (Fin 5) :=
  ⟨swap 0 1 * swap 2 3, by rw [mem_alternatingGroup]; decide⟩

@[expose] def a5b : alternatingGroup (Fin 5) :=
  ⟨finRotate 5, by rw [mem_alternatingGroup]; decide⟩

theorem closure_A5 : Subgroup.closure ({a5a, a5b} : Set (alternatingGroup (Fin 5))) = ⊤ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.closure ({a5a, a5b} : Set (alternatingGroup (Fin 5)))
  have ha : a5a ∈ H := Subgroup.subset_closure (by simp)
  have hb : a5b ∈ H := Subgroup.subset_closure (by simp)
  have hab : a5a * a5b ∈ H := H.mul_mem ha hb
  have d2 := Subgroup.orderOf_dvd_natCard H ha
  have d5 := Subgroup.orderOf_dvd_natCard H hb
  have d3 := Subgroup.orderOf_dvd_natCard H hab
  rw [orderOf_eq_prime (p := 2) (by decide) (by decide)] at d2
  rw [orderOf_eq_prime (p := 5) (by decide) (by decide)] at d5
  rw [orderOf_eq_prime (p := 3) (by decide) (by decide)] at d3
  have hG : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide
  have hdvd : Nat.card H ∣ 60 := hG ▸ Subgroup.card_subgroup_dvd_card H
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hle : Nat.card H ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
  have h30 : 30 ∣ Nat.card H := by omega
  by_contra hne
  have hlt : Nat.card H ≠ 60 := fun h => hne (Subgroup.eq_top_of_card_eq H (by rw [h, hG]))
  have hc : Nat.card H = 30 := by omega
  have hidx : H.index = 2 := by
    have := H.index_mul_card
    rw [hc, hG] at this
    omega
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h | h
  · rw [h, Subgroup.card_bot] at hc; omega
  · exact hne h

theorem closure_prod {K : Type*} [Group K] {a b : K}
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) :
    Subgroup.closure ({(swap (0 : Fin 3) 1, 1), (finRotate 3 * swap 0 1, 1), (1, a), (1, b)} :
      Set (Perm (Fin 3) × K)) = ⊤ := by
  set H := Subgroup.closure ({(swap (0 : Fin 3) 1, 1), (finRotate 3 * swap 0 1, 1), (1, a),
    (1, b)} : Set (Perm (Fin 3) × K))
  have h1 : (swap (0 : Fin 3) 1, (1 : K)) ∈ H := Subgroup.subset_closure (by simp)
  have h2 : (finRotate 3 * swap (0 : Fin 3) 1, (1 : K)) ∈ H := Subgroup.subset_closure (by simp)
  have h3 : ((1 : Perm (Fin 3)), a) ∈ H := Subgroup.subset_closure (by simp)
  have h4 : ((1 : Perm (Fin 3)), b) ∈ H := Subgroup.subset_closure (by simp)
  have hc : (finRotate 3, (1 : K)) ∈ H := by
    have h := H.mul_mem h2 (H.inv_mem h1)
    have he : (finRotate 3 * swap (0 : Fin 3) 1, (1 : K)) * (swap (0 : Fin 3) 1, (1 : K))⁻¹ =
        (finRotate 3, 1) := Prod.ext (by simp) (by simp)
    rwa [he] at h
  have hl : ∀ u : Perm (Fin 3), (u, (1 : K)) ∈ H := by
    intro u
    have hle : (Subgroup.closure ({finRotate 3, swap (0 : Fin 3) 1} : Set (Perm (Fin 3)))).map
        (MonoidHom.inl (Perm (Fin 3)) K) ≤ H := by
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · exact hc
      · exact h1
    rw [closure_S3] at hle
    exact hle ⟨u, Subgroup.mem_top u, rfl⟩
  have hr : ∀ k : K, ((1 : Perm (Fin 3)), k) ∈ H := by
    intro k
    have hle : (Subgroup.closure ({a, b} : Set K)).map (MonoidHom.inr (Perm (Fin 3)) K) ≤ H := by
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with rfl | rfl
      · exact h3
      · exact h4
    rw [hab] at hle
    exact hle ⟨k, Subgroup.mem_top k, rfl⟩
  rw [eq_top_iff]
  rintro ⟨u, k⟩ -
  have h := H.mul_mem (hl u) (hr k)
  rwa [Prod.mk_mul_mk, mul_one, one_mul] at h

@[expose] def wordsOK (B : List (List ℕ)) : List (List ℕ) → List (List ℕ) → Bool
  | [], _ => true
  | c :: A, w :: W => (c == evalW B w) && wordsOK B A W
  | _ :: _, [] => false

theorem words_of_ok {B : List (List ℕ)} :
    ∀ {A W : List (List ℕ)}, wordsOK B A W = true → ∀ c ∈ A, ∃ w, c = evalW B w
  | [], _, _ => fun c hc => absurd hc List.not_mem_nil
  | c :: A, w :: W, h => by
    simp only [wordsOK, Bool.and_eq_true, beq_iff_eq] at h
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact ⟨w, h.1⟩
    · exact words_of_ok h.2 c' hc'
  | _ :: _, [], h => by simp [wordsOK] at h

theorem genSub_le_of_words {A B : List (List ℕ)} (hB : ∀ g ∈ B, Valid8 g)
    (hBu : ∀ g ∈ B, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g)
    (hw : ∀ c ∈ A, ∃ w, c = evalW B w) : genSub A ≤ genSub B := by
  refine (Subgroup.closure_le _).mpr fun g hg => ?_
  obtain ⟨w, hw⟩ := hw _ hg
  obtain ⟨u, hu, hu'⟩ := exists_evalW B hB hBu w
  have : g = u := Units.ext (by rw [hu', ← hw, dec8_colsOf])
  rw [this]
  exact hu

theorem cols_g5s0 : colsOf (g5s0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = s0c := by decide +kernel

theorem cols_g5s1 : colsOf (g5s1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = s1c := by decide +kernel

theorem g5s0_val : (g5s0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 s0c := by
  rw [← cols_g5s0, dec8_colsOf]

theorem g5s1_val : (g5s1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 s1c := by
  rw [← cols_g5s1, dec8_colsOf]

theorem valid8_all {L : List (List ℕ)} (h : L.all validB = true) : ∀ g ∈ L, Valid8 g :=
  fun g hg => valid8_of_validB (List.all_eq_true.mp h g hg)

theorem ours_unit {x y : List ℕ} (hx : Valid8 (blk x)) (hy : Valid8 (blk y))
    (hy4 : Valid8 (pow8 (blk y) 4)) (hxx : mul8 (blk x) (blk x) = one8)
    (hyy : mul8 (blk y) (pow8 (blk y) 4) = one8) (hyy' : mul8 (pow8 (blk y) 4) (blk y) = one8) :
    ∀ g ∈ [s0c, s1c, blk x, blk y], ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact ⟨g5s0, g5s0_val⟩
  · exact ⟨g5s1, g5s1_val⟩
  · exact ⟨unitOf hx hx hxx hxx, rfl⟩
  · exact ⟨unitOf hy hy4 hyy hyy', rfl⟩

theorem genSub_eq_g5 {x y : List ℕ} {b₁ b₂ : Bool} {W W' : List (List ℕ)}
    (hval : ∀ g ∈ [s0c, s1c, blk x, blk y], Valid8 g) (hy4 : Valid8 (pow8 (blk y) 4))
    (hxx : mul8 (blk x) (blk x) = one8) (hyy : mul8 (blk y) (pow8 (blk y) 4) = one8)
    (hyy' : mul8 (pow8 (blk y) 4) (blk y) = one8)
    (h1 : wordsOK (L1442Q.gensG b₁ b₂) [s0c, s1c, blk x, blk y] W = true)
    (h2 : wordsOK [s0c, s1c, blk x, blk y] (L1442Q.gensG b₁ b₂) W' = true) :
    genSub [s0c, s1c, blk x, blk y] = g5 b₁ b₂ := by
  rw [L1442Q.g5_eq]
  have hx : Valid8 (blk x) := hval _ (by simp)
  have hy : Valid8 (blk y) := hval _ (by simp)
  exact le_antisymm
    (genSub_le_of_words (L1442Q.formCheck_spec b₁ b₂).1 (L1442Q.gensG_unit b₁ b₂)
      (words_of_ok h1))
    (genSub_le_of_words hval (ours_unit hx hy hy4 hxx hyy hyy') (words_of_ok h2))

theorem genSub_S5a : genSub [s0c, s1c, blk [3, 2, 9, 7], blk [6, 11, 7, 9]] = g5 true true :=
  genSub_eq_g5 (W := [[0], [1], [5, 2, 4, 2], [4, 4, 2, 4, 3, 2]])
    (W' := [[0], [1], [2, 3, 2, 3, 3, 3, 2, 3, 2], [3, 3, 2, 3, 2, 3, 3, 3, 3], [3, 3, 2, 3, 3, 2],
      [3, 2, 3, 2, 3, 3, 2]])
    (valid8_all (by decide +kernel)) (valid8_of_validB (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem genSub_S5b : genSub [s0c, s1c, blk [1, 8, 4, 2], blk [6, 12, 5, 4]] = g5 true false :=
  genSub_eq_g5 (W := [[0], [1], [3, 2, 3, 3, 2, 3, 2], [3, 3, 3, 3, 2, 3, 3, 2, 3]])
    (W' := [[0], [1], [3, 3, 3, 3, 2, 3], [2, 3, 3, 2]])
    (valid8_all (by decide +kernel)) (valid8_of_validB (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem genSub_A5a :
    genSub [s0c, s1c, blk [10, 15, 9, 14], blk [5, 10, 14, 7]] = g5 false true :=
  genSub_eq_g5 (W := [[0], [1], [2, 3, 4, 2], [2, 4, 3, 2, 4, 2]])
    (W' := [[0], [1], [3, 2, 3, 3, 2], [3, 3, 2, 3, 3, 3, 2, 3, 2], [2, 3, 2, 3]])
    (valid8_all (by decide +kernel)) (valid8_of_validB (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem genSub_A5b : genSub [s0c, s1c, blk [5, 12, 4, 6], blk [6, 12, 5, 4]] = g5 false false :=
  genSub_eq_g5 (W := [[0], [1], [2, 3, 3], [2, 2, 3, 2]])
    (W' := [[0], [1], [3, 2, 3, 3, 3, 2, 3], [2, 3, 3]])
    (valid8_all (by decide +kernel)) (valid8_of_validB (by decide +kernel)) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

@[expose] noncomputable def cu (u : GL (Fin 8) (ZMod 2)) : List ℕ :=
  colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2))

theorem cu_mul (u v : GL (Fin 8) (ZMod 2)) : cu (u * v) = mul8 (cu u) (cu v) := by
  rw [cu, Units.val_mul, colsOf_mul]
  rfl

theorem cu_one : cu 1 = one8 := by rw [cu, Units.val_one, colsOf_one]

theorem cu_pow (u : GL (Fin 8) (ZMod 2)) (k : ℕ) : cu (u ^ k) = pow8 (cu u) k := by
  induction k with
  | zero => rw [pow_zero, cu_one]; rfl
  | succ k ih => rw [pow_succ', cu_mul, ih]; rfl

theorem eq_one_of_cu {u : GL (Fin 8) (ZMod 2)} (h : cu u = one8) : u = 1 :=
  S7Cert.eq_of_colsOf_eq (by rw [show colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = cu u from rfl,
    h, Units.val_one, colsOf_one])

theorem iff_of_map_eq {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Γ : Subgroup (V ≃ₗ[ZMod 2] V)} {e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    {G : Subgroup (GL (Fin 8) (ZMod 2))} (h : Γ.map (L14411.matOf e) = G)
    (φ : V ≃ₗ[ZMod 2] V) :
    φ ∈ Γ ↔ ∃ γ ∈ G, ∀ v, e (φ v) = (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v) := by
  constructor
  · intro hφ
    exact ⟨L14411.matOf e φ, h ▸ ⟨φ, hφ, rfl⟩, fun v => (L14411.matOf_mulVec e φ v).symm⟩
  · rintro ⟨γ, hγ, hγv⟩
    rw [← h] at hγ
    obtain ⟨φ', hφ', rfl⟩ := hγ
    have : φ = φ' := L14411.matOf_injective e ((L14411.matOf_eq_iff e φ _).mpr hγv)
    rw [this]
    exact hφ'

theorem conj_c3 (u : Perm (Fin 3)) : u⁻¹ * finRotate 3 * u = finRotate 3 ∨
    u⁻¹ * finRotate 3 * u = finRotate 3 * finRotate 3 := by
  revert u
  decide

section Gen

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem exists_model_gen {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hdim : Module.finrank (ZMod 2) V = 8)
    (hirr : ∀ J : Submodule (ZMod 2) V, (∀ γ ∈ Γ, ∀ v ∈ J, γ v ∈ J) → J = ⊥ ∨ J = ⊤)
    {K : Type} [Group K] (ψ : ↥Γ ≃* (Perm (Fin 3) × K)) {a b : K}
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) (ha2 : a * a = 1) (ha1 : a ≠ 1)
    (hb5 : b ^ 5 = 1) (hb1 : b ≠ 1) {R : List ℕ → List ℕ → Bool}
    (hR : ∀ ρ : K →* GL (Fin 8) (ZMod 2), R (cu (ρ a)) (cu (ρ b)) = true) {ms : List Model}
    (hms : ∀ m ∈ ms, Valid8 (blk m.1) ∧ Valid8 (blk m.2.1))
    (hclass : ∀ x ∈ invs, x ≠ one4 → R (blk x) (blk y0) = true →
      ∃ c ic, ∃ m ∈ ms, verifyC x y0 c ic m.1 m.2.1 = true) :
    ∃ m ∈ ms, ∃ e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2),
      Γ.map (L14411.matOf e) = genSub [s0c, s1c, blk m.1, blk m.2.1] := by
  classical
  obtain ⟨sΓ, hsΓ⟩ : ∃ x : ↥Γ, x = ψ.symm (swap 0 1, 1) := ⟨_, rfl⟩
  obtain ⟨tΓ, htΓ⟩ : ∃ x : ↥Γ, x = ψ.symm (finRotate 3, 1) := ⟨_, rfl⟩
  obtain ⟨kΓ, hkΓ⟩ : ∃ f : K →* ↥Γ, f = ψ.symm.toMonoidHom.comp (MonoidHom.inr _ _) := ⟨_, rfl⟩
  have hkΓv : ∀ k, kΓ k = ψ.symm (1, k) := fun k => by rw [hkΓ]; rfl
  obtain ⟨s, hs⟩ : ∃ x : V ≃ₗ[ZMod 2] V, x = sΓ := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ x : V ≃ₗ[ZMod 2] V, x = tΓ := ⟨_, rfl⟩
  have hcoe : ∀ x y : Perm (Fin 3) × K,
      ((ψ.symm x : ↥Γ) : V ≃ₗ[ZMod 2] V) * ((ψ.symm y : ↥Γ) : V ≃ₗ[ZMod 2] V) =
        ((ψ.symm (x * y) : ↥Γ) : V ≃ₗ[ZMod 2] V) := fun x y => by
    rw [map_mul, Subgroup.coe_mul]
  have hone : ((ψ.symm 1 : ↥Γ) : V ≃ₗ[ZMod 2] V) = 1 := by rw [map_one, Subgroup.coe_one]
  have ht3 : ∀ v, t (t (t v)) = v := by
    intro v
    have h : t * (t * t) = 1 := by
      rw [ht, htΓ, hcoe, hcoe, ← hone]
      congr 2
      exact Prod.ext (show finRotate 3 * (finRotate 3 * finRotate 3) = (1 : Perm (Fin 3)) by
        decide) (by simp)
    exact congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) h
  have hs2 : ∀ v, s (s v) = v := by
    intro v
    have h : s * s = 1 := by
      rw [hs, hsΓ, hcoe, ← hone]
      congr 2
      exact Prod.ext (show swap (0 : Fin 3) 1 * swap 0 1 = 1 by decide) (by simp)
    exact congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) h
  have hst : ∀ v, s (t v) = t (t (s v)) := by
    intro v
    have h : s * t = t * (t * s) := by
      rw [hs, ht, hsΓ, htΓ, hcoe, hcoe, hcoe]
      congr 2
      exact Prod.ext (show swap (0 : Fin 3) 1 * finRotate 3 =
        finRotate 3 * (finRotate 3 * swap 0 1) by decide) (by simp)
    exact congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) h
  have ht1 : t ≠ 1 := by
    intro h
    have h1 : tΓ = 1 := Subtype.ext (by rw [← ht, h]; rfl)
    rw [htΓ, ← map_one ψ.symm] at h1
    have h2 : finRotate 3 = (1 : Perm (Fin 3)) := congrArg Prod.fst (ψ.symm.injective h1)
    exact absurd h2 (by decide)
  have hnorm : ∀ γ ∈ Γ, γ⁻¹ * t * γ = t ∨ γ⁻¹ * t * γ = t * t := by
    intro γ hγ
    have hγ' : γ = ((ψ.symm (ψ ⟨γ, hγ⟩) : ↥Γ) : V ≃ₗ[ZMod 2] V) := by
      rw [ψ.symm_apply_apply]
    obtain ⟨⟨u, k⟩, huk⟩ : ∃ p, ψ ⟨γ, hγ⟩ = p := ⟨_, rfl⟩
    rw [huk] at hγ'
    have hinv : γ⁻¹ = ((ψ.symm (u⁻¹, k⁻¹) : ↥Γ) : V ≃ₗ[ZMod 2] V) := by
      rw [hγ', ← Subgroup.coe_inv, ← map_inv]
      rfl
    have hu := conj_c3 u
    rw [hinv, hγ', ht, htΓ, hcoe, hcoe]
    rcases hu with h | h
    · left
      congr 2
      exact Prod.ext h (by simp)
    · right
      rw [hcoe]
      congr 2
      exact Prod.ext h (by simp)
  have hk : ∀ k : K, s * (kΓ k : V ≃ₗ[ZMod 2] V) = (kΓ k : V ≃ₗ[ZMod 2] V) * s ∧
      t * (kΓ k : V ≃ₗ[ZMod 2] V) = (kΓ k : V ≃ₗ[ZMod 2] V) * t := by
    intro k
    rw [hs, ht, hsΓ, htΓ, hkΓv, hcoe, hcoe, hcoe, hcoe]
    exact ⟨by congr 2; exact Prod.ext (by simp) (by simp),
      by congr 2; exact Prod.ext (by simp) (by simp)⟩
  obtain ⟨e₀, hs₀, hts₀⟩ := exists_coordsS3 hdim (fix_eq_zero hirr ht1 hnorm) ht3 hs2 hst
  let ρ : (V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) → K →* GL (Fin 8) (ZMod 2) :=
    fun e => (L14411.matOf e).comp (Γ.subtype.comp kΓ)
  have hρ : ∀ e k, ρ e k = L14411.matOf e (kΓ k) := fun e k => rfl
  have hρinj : ∀ e, Function.Injective (ρ e) := by
    intro e x y h
    have h1 := L14411.matOf_injective e h
    have h2 : kΓ x = kΓ y := Subtype.ext h1
    rw [hkΓv, hkΓv] at h2
    exact congrArg Prod.snd (ψ.symm.injective h2)
  have hblk : ∀ e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2), L14411.matOf e s = g5s0 →
      L14411.matOf e (t * s) = g5s1 → ∀ k, ∃ xs ∈ all4, cu (ρ e k) = blk xs := by
    intro e h0 h1 k
    refine blk_of_comm (valid8_colsOf _) ?_ ?_
    · rw [← cols_g5s0, show colsOf (g5s0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = cu g5s0 from rfl,
        ← cu_mul, ← cu_mul, hρ, ← h0, ← map_mul, ← map_mul, (hk k).1]
    · have hcomm : (kΓ k : V ≃ₗ[ZMod 2] V) * (t * s) = t * s * (kΓ k : V ≃ₗ[ZMod 2] V) := by
        calc (kΓ k : V ≃ₗ[ZMod 2] V) * (t * s) = (kΓ k : V ≃ₗ[ZMod 2] V) * t * s :=
              (mul_assoc _ _ _).symm
          _ = t * (kΓ k : V ≃ₗ[ZMod 2] V) * s := by rw [(hk k).2]
          _ = t * ((kΓ k : V ≃ₗ[ZMod 2] V) * s) := mul_assoc _ _ _
          _ = t * (s * (kΓ k : V ≃ₗ[ZMod 2] V)) := by rw [(hk k).1]
          _ = t * s * (kΓ k : V ≃ₗ[ZMod 2] V) := (mul_assoc _ _ _).symm
      rw [← cols_g5s1, show colsOf (g5s1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = cu g5s1 from rfl,
        ← cu_mul, ← cu_mul, hρ, ← h1, ← map_mul, ← map_mul, hcomm]
  obtain ⟨ys, hys, hcy⟩ := hblk e₀ hs₀ hts₀ b
  have hy5 : ys ∈ ords5 := by
    refine mem_ords5 hys ?_ ?_
    · rw [← hcy, ← cu_pow, ← map_pow, hb5, map_one, cu_one]
    · intro h
      apply hb1
      apply hρinj e₀
      rw [map_one]
      exact eq_one_of_cu (hcy.trans h)
  obtain ⟨d, di, hv⟩ := norm_spec hy5
  obtain ⟨hvd, hvdi, hddi, hdid, hconj, hc0, hc1⟩ := verifyY_spec hv
  obtain ⟨e₁, he₁⟩ : ∃ e, e = e₀.trans (L14411.linOf (unitOf hvdi hvd hdid hddi)) := ⟨_, rfl⟩
  have hch₁ : ∀ φ, ((L14411.matOf e₁ φ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      dec8 (blk di) * (L14411.matOf e₀ φ : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 (blk d) := by
    intro φ
    rw [he₁]
    exact matOf_change e₀ hvdi hvd hdid hddi φ
  have hs₁ : L14411.matOf e₁ s = g5s0 := Units.ext (by
    rw [hch₁, hs₀, g5s0_val, dec8_conj hvd.1 rfl hdid hc0.symm])
  have hts₁ : L14411.matOf e₁ (t * s) = g5s1 := Units.ext (by
    rw [hch₁, hts₀, g5s1_val, dec8_conj hvd.1 rfl hdid hc1.symm])
  have hb₁ : ((ρ e₁ b : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      dec8 (blk y0) := by
    rw [hρ, hch₁, ← hρ, ← dec8_colsOf ((ρ e₀ b : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)), show colsOf ((ρ e₀ b : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = cu (ρ e₀ b) from rfl, hcy,
      dec8_conj hvd.1 rfl hdid hconj]
  obtain ⟨xs, hxs, hcx⟩ := hblk e₁ hs₁ hts₁ a
  have hcb₁ : cu (ρ e₁ b) = blk y0 := by
    rw [cu, hb₁, colsOf_dec8 (valid8_of_validB (by decide +kernel))]
  have hx2 : xs ∈ invs := by
    refine mem_invs hxs ?_
    rw [← hcx, ← cu_mul, ← map_mul, ha2, map_one, cu_one]
  have hx1 : xs ≠ one4 := by
    rintro rfl
    apply ha1
    apply hρinj e₁
    rw [map_one]
    exact eq_one_of_cu (hcx.trans (by decide))
  have hR₁ : R (blk xs) (blk y0) = true := by
    have h := hR (ρ e₁)
    rwa [hcx, hcb₁] at h
  obtain ⟨c, ic, m, hm, hvC⟩ := hclass xs hx2 hx1 hR₁
  obtain ⟨hvc, hvic, hcic, hicc, hcxm, hcym, hc0', hc1'⟩ := verifyC_spec hvC
  obtain ⟨e₂, he₂⟩ : ∃ e, e = e₁.trans (L14411.linOf (unitOf hvic hvc hicc hcic)) := ⟨_, rfl⟩
  have hch₂ : ∀ φ, ((L14411.matOf e₂ φ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      dec8 (blk ic) * (L14411.matOf e₁ φ : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 (blk c) := by
    intro φ
    rw [he₂]
    exact matOf_change e₁ hvic hvc hicc hcic φ
  have hs₂ : L14411.matOf e₂ s = g5s0 := Units.ext (by
    rw [hch₂, hs₁, g5s0_val, dec8_conj hvc.1 rfl hicc hc0'.symm])
  have hts₂ : L14411.matOf e₂ (t * s) = g5s1 := Units.ext (by
    rw [hch₂, hts₁, g5s1_val, dec8_conj hvc.1 rfl hicc hc1'.symm])
  obtain ⟨hm1, hm2⟩ := hms m hm
  have ha₂ : ((ρ e₂ a : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      dec8 (blk m.1) := by
    rw [hρ, hch₂, ← hρ, ← dec8_colsOf ((ρ e₁ a : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)), show colsOf ((ρ e₁ a : GL (Fin 8) (ZMod 2)) :
      Matrix (Fin 8) (Fin 8) (ZMod 2)) = cu (ρ e₁ a) from rfl, hcx,
      dec8_conj hvc.1 hm1.1 hicc hcxm]
  have hb₂ : ((ρ e₂ b : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      dec8 (blk m.2.1) := by
    rw [hρ, hch₂, ← hρ, hb₁, dec8_conj hvc.1 hm2.1 hicc hcym]
  refine ⟨m, hm, e₂, ?_⟩
  have hgen : Γ = Subgroup.closure {s, t * s, (kΓ a : V ≃ₗ[ZMod 2] V),
      (kΓ b : V ≃ₗ[ZMod 2] V)} := by
    have h1 : (⊤ : Subgroup (Perm (Fin 3) × K)).map (Γ.subtype.comp ψ.symm.toMonoidHom) = Γ := by
      rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
        MonoidHom.range_eq_top.mpr ψ.symm.surjective, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    refine h1.symm.trans ?_
    rw [← closure_prod hab, MonoidHom.map_closure]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton]
    have e1 : (Γ.subtype.comp ψ.symm.toMonoidHom) (swap 0 1, 1) = s := by rw [hs, hsΓ]; rfl
    have e2 : (Γ.subtype.comp ψ.symm.toMonoidHom) (finRotate 3 * swap 0 1, 1) = t * s := by
      rw [ht, hs, htΓ, hsΓ, hcoe, Prod.mk_mul_mk, mul_one]
      rfl
    have e3 : (Γ.subtype.comp ψ.symm.toMonoidHom) (1, a) = (kΓ a : V ≃ₗ[ZMod 2] V) := by
      rw [hkΓv]; rfl
    have e4 : (Γ.subtype.comp ψ.symm.toMonoidHom) (1, b) = (kΓ b : V ≃ₗ[ZMod 2] V) := by
      rw [hkΓv]; rfl
    rw [e1, e2, e3, e4]
  have hset : ({g5s0, g5s1, ρ e₂ a, ρ e₂ b} : Set (GL (Fin 8) (ZMod 2))) =
      {g : GL (Fin 8) (ZMod 2) |
        colsOf (g : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ [s0c, s1c, blk m.1, blk m.2.1]} := by
    have c3 : colsOf ((ρ e₂ a : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        blk m.1 := by rw [ha₂, colsOf_dec8 hm1]
    have c4 : colsOf ((ρ e₂ b : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
        blk m.2.1 := by rw [hb₂, colsOf_dec8 hm2]
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq, List.mem_cons,
      List.not_mem_nil, or_false]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact Or.inl cols_g5s0
      · exact Or.inr (Or.inl cols_g5s1)
      · exact Or.inr (Or.inr (Or.inl c3))
      · exact Or.inr (Or.inr (Or.inr c4))
    · rintro (h | h | h | h)
      · exact Or.inl (S7Cert.eq_of_colsOf_eq (h.trans cols_g5s0.symm))
      · exact Or.inr (Or.inl (S7Cert.eq_of_colsOf_eq (h.trans cols_g5s1.symm)))
      · exact Or.inr (Or.inr (Or.inl (S7Cert.eq_of_colsOf_eq (h.trans c3.symm))))
      · exact Or.inr (Or.inr (Or.inr (S7Cert.eq_of_colsOf_eq (h.trans c4.symm))))
  rw [hgen, MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton, hs₂, hts₂]
  rw [show L14411.matOf e₂ (kΓ a : V ≃ₗ[ZMod 2] V) = ρ e₂ a from rfl,
    show L14411.matOf e₂ (kΓ b : V ≃ₗ[ZMod 2] V) = ρ e₂ b from rfl, hset]
  rfl

end Gen

theorem relS5_of_hom (ρ : Perm (Fin 5) →* GL (Fin 8) (ZMod 2)) :
    relS5 (cu (ρ (swap 0 1))) (cu (ρ (finRotate 5))) = true := by
  have r1 : (swap (0 : Fin 5) 1 * finRotate 5) ^ 4 = 1 := by decide
  have r2 : (swap (0 : Fin 5) 1 * finRotate 5 ^ 4 * swap 0 1 * finRotate 5) ^ 3 = 1 := by
    decide +kernel
  have r3 : (swap (0 : Fin 5) 1 * finRotate 5 ^ 3 * swap 0 1 * finRotate 5 ^ 2) ^ 2 = 1 := by
    decide +kernel
  simp only [relS5, Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [← cu_mul, ← cu_pow, ← map_mul, ← map_pow, r1, map_one, cu_one]
  · rw [← cu_pow, ← cu_mul, ← cu_mul, ← cu_mul, ← cu_pow, ← map_pow, ← map_mul, ← map_mul,
      ← map_mul, ← map_pow, r2, map_one, cu_one]
  · rw [← cu_pow, ← cu_mul, ← cu_mul, ← cu_pow, ← cu_mul, ← cu_pow, ← map_pow, ← map_mul,
      ← map_mul, ← map_pow, ← map_mul, ← map_pow, r3, map_one, cu_one]

theorem relA5_of_hom (ρ : alternatingGroup (Fin 5) →* GL (Fin 8) (ZMod 2)) :
    relA5 (cu (ρ a5a)) (cu (ρ a5b)) = true := by
  have r1 : (a5a * a5b) ^ 3 = 1 := by decide
  simp only [relA5, beq_iff_eq]
  rw [← cu_mul, ← cu_pow, ← map_mul, ← map_pow, r1, map_one, cu_one]

theorem exists_model_of {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {Γ : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hdim : Module.finrank (ZMod 2) V = 8)
    (hirr : ∀ J : Submodule (ZMod 2) V, (∀ γ ∈ Γ, ∀ v ∈ J, γ v ∈ J) → J = ⊥ ∨ J = ⊤)
    (h9 : Nonempty (↥Γ ≃* (Perm (Fin 3) × Perm (Fin 5))) ∨
      Nonempty (↥Γ ≃* (Perm (Fin 3) × ↥(alternatingGroup (Fin 5))))) :
    ∃ (b₁ b₂ : Bool) (e : V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)), ∀ φ : V ≃ₗ[ZMod 2] V,
      φ ∈ Γ ↔ ∃ γ ∈ g5 b₁ b₂,
        ∀ v, e (φ v) = (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v) := by
  rcases h9 with h9 | h9
  · obtain ⟨ψ⟩ := h9
    obtain ⟨m, hm, e, he⟩ := exists_model_gen hdim hirr ψ (a := swap 0 1) (b := finRotate 5)
      (by rw [Set.pair_comm]; exact closure_S5) (by decide) (by decide) (by decide) (by decide)
      relS5_of_hom (ms := modelsS5)
      (by
        intro m hm
        simp only [modelsS5, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact ⟨valid8_of_validB (by decide +kernel), valid8_of_validB (by decide +kernel)⟩
        · exact ⟨valid8_of_validB (by decide +kernel), valid8_of_validB (by decide +kernel)⟩)
      (fun x hx _ hr => s5_spec hx hr)
    simp only [modelsS5, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨true, true, e, iff_of_map_eq (he.trans genSub_S5a)⟩
    · exact ⟨true, false, e, iff_of_map_eq (he.trans genSub_S5b)⟩
  · obtain ⟨ψ⟩ := h9
    obtain ⟨m, hm, e, he⟩ := exists_model_gen hdim hirr ψ (a := a5a) (b := a5b) closure_A5
      (by decide) (by decide) (by decide) (by decide) relA5_of_hom (ms := modelsA5)
      (by
        intro m hm
        simp only [modelsA5, List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact ⟨valid8_of_validB (by decide +kernel), valid8_of_validB (by decide +kernel)⟩
        · exact ⟨valid8_of_validB (by decide +kernel), valid8_of_validB (by decide +kernel)⟩)
      (fun x hx hx1 hr => a5_spec hx hx1 hr)
    simp only [modelsA5, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨false, true, e, iff_of_map_eq (he.trans genSub_A5a)⟩
    · exact ⟨false, false, e, iff_of_map_eq (he.trans genSub_A5b)⟩

end CFSG.Quasithin.H13.L1442V
