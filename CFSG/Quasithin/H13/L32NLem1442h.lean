module

public import CFSG.Quasithin.H13.L32NS8Model
public import Certificates.Certificate7235

public section

namespace CFSG.Quasithin.H13.S7Conj

open Mat8Cert L1442M

theorem s7ConjCheck_eq : s7ConjCheck = true :=
  Certificates.certificate7235

theorem check_parts :
    s7s8B = true ∧ nB = true ∧ orbB = true ∧ ∀ r ∈ reps, hB r = true := by
  have h := s7ConjCheck_eq
  simp only [s7ConjCheck, Bool.and_eq_true, List.all_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem c7_eq : c7 = colsOf (s7g0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  rw [c7, S7Cert.s7G_cols]
  rfl

theorem dec8_c7 : dec8 c7 = (s7g0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) := by
  rw [c7_eq, dec8_colsOf]

theorem valid8_c7 : Valid8 c7 := by
  rw [c7_eq]
  exact valid8_colsOf _

theorem length_iterate (j : ℕ) : ((mul8 c7)^[j] one8).length = 8 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', length_mul8, ih]

theorem dec8_iterate (j : ℕ) :
    dec8 ((mul8 c7)^[j] one8) = (s7g0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) ^ j := by
  induction j with
  | zero => rw [Function.iterate_zero_apply, dec8_one8, pow_zero]
  | succ j ih =>
    rw [Function.iterate_succ_apply', dec8_mul8 _ _ (length_iterate j), ih, dec8_c7, pow_succ']

theorem s7_le_s8 : s7 ≤ s8 := by
  rw [S7Cert.s7_eq]
  refine (Subgroup.closure_le _).mpr fun u hu => ?_
  have hu' : colsOf (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ S7Cert.s7G := hu
  have h := check_parts.1
  simp only [s7s8B, List.all_eq_true, s8H, Std.HashSet.contains_ofList, List.contains_iff_mem]
    at h
  exact (S8Cert.mem_s8_iff u).mpr (h _ hu')

theorem s7g0_mem_s7 : s7g0 ∈ s7 :=
  Subgroup.subset_closure (by simp)

theorem orderOf_s7g0 : orderOf s7g0 = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    decide +kernel
  · intro h
    have h1 := congrArg (fun u : GL (Fin 8) (ZMod 2) => (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) 0 1) h
    simp only [Units.val_one] at h1
    revert h1
    decide +kernel

theorem dec8_mul8_mul8 {A B C : List ℕ} (hB : B.length = 8) (hC : C.length = 8) :
    dec8 (mul8 (mul8 A B) C) = dec8 A * dec8 B * dec8 C := by
  rw [dec8_mul8 _ _ hC, dec8_mul8 _ _ hB]

theorem inv_eq_dec8 {u : GL (Fin 8) (ZMod 2)} {m m' : List ℕ}
    (hu : (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 m) (hm' : Valid8 m')
    (h : mul8 m m' = one8) : ((u⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) =
      dec8 m' := by
  have h1 : (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 m' = 1 := by
    rw [hu, ← dec8_mul8 _ _ hm'.1, h, dec8_one8]
  calc ((u⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2))
      = ((u⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *
          ((u : Matrix (Fin 8) (Fin 8) (ZMod 2)) * dec8 m') := by rw [h1, Matrix.mul_one]
    _ = dec8 m' := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

theorem length_le_card {gens L : List (List ℕ)} (hgens : ∀ g ∈ gens, Valid8 g)
    (hunit : ∀ g ∈ gens, ∃ u : GL (Fin 8) (ZMod 2), (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g)
    (hL : ∀ x ∈ L, ∃ w, x = evalW gens w) (hvalid : ∀ x ∈ L, Valid8 x) (hnd : L.Nodup) :
    L.length ≤ Nat.card (genSub gens) := by
  classical
  have hex : ∀ x : {x // x ∈ L}, ∃ u ∈ genSub gens,
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 x.1 := by
    intro x
    obtain ⟨w, hw⟩ := hL x.1 x.2
    rw [hw]
    exact exists_evalW gens hgens hunit w
  let f : {x // x ∈ L} → genSub gens := fun x => ⟨(hex x).choose, (hex x).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 := (hex x).choose_spec.2
    have h2 := (hex y).choose_spec.2
    have h3 : dec8 x.1 = dec8 y.1 := by
      rw [← h1, ← h2]
      exact congrArg (fun u : genSub gens => ((u : GL (Fin 8) (ZMod 2)) :
        Matrix (Fin 8) (Fin 8) (ZMod 2))) hxy
    apply Subtype.ext
    rw [← colsOf_dec8 (hvalid x.1 x.2), ← colsOf_dec8 (hvalid y.1 y.2), h3]
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_congr (Equiv.subtypeEquivRight fun x => (List.mem_toFinset (l := L) (a := x)).symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd] at this

theorem genSub_pair {A B : List ℕ} {a b : GL (Fin 8) (ZMod 2)}
    (ha : colsOf (a : Matrix (Fin 8) (Fin 8) (ZMod 2)) = A)
    (hb : colsOf (b : Matrix (Fin 8) (Fin 8) (ZMod 2)) = B) :
    genSub [A, B] = Subgroup.closure {a, b} := by
  unfold genSub
  congr 1
  ext u
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (S7Cert.eq_of_colsOf_eq (h.trans ha.symm))
    · exact Or.inr (S7Cert.eq_of_colsOf_eq (h.trans hb.symm))
  · rintro (rfl | rfl)
    · exact Or.inl ha
    · exact Or.inr hb

theorem exists_of_hB
    {r : List ℕ} {R : GL (Fin 8) (ZMod 2)} (hR : (R : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 r)
    (hrv : Valid8 r) (hB' : hB r = true)
    (hcard : Nat.card (Subgroup.closure ({s7g0, R} : Set (GL (Fin 8) (ZMod 2)))) = 5040) :
    ∃ m ∈ s8, m * s7g0 * m⁻¹ ∈ s7 ∧ m * R * m⁻¹ ∈ s7 := by
  have hgv : ∀ g ∈ [c7, r], Valid8 g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact valid8_c7
    · exact hrv
  have hunit : ∀ g ∈ [c7, r], ∃ u : GL (Fin 8) (ZMod 2),
      (u : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 g := by
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨s7g0, dec8_c7.symm⟩
    · exact ⟨R, hR⟩
  have hgen : genSub [c7, r] = Subgroup.closure {s7g0, R} :=
    genSub_pair (by rw [c7_eq]) (by rw [hR, colsOf_dec8 hrv])
  simp only [hB, Bool.and_eq_true, List.all_eq_true, S7Cert.validB_iff] at hB'
  obtain ⟨⟨⟨⟨hv, hnd⟩, hone⟩, -⟩, hrest⟩ := hB'
  set L := elemsOf [c7, r] 5041 with hL
  have hnd' := S7Cert.nodup_of_nodupB hnd
  have hone' : one8 ∈ L := by simpa using hone
  have hwords : ∀ x ∈ L, ∃ w, x = evalW [c7, r] w := fun x hx => S7Cert.mem_elemsOf hx
  by_cases hlen : L.length ≤ 5040
  · simp only [hlen, ↓reduceIte] at hrest
    simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, List.any_eq_true] at hrest
    obtain ⟨hcl, hor⟩ := hrest
    have hclosed : ∀ x ∈ L, ∀ g ∈ [c7, r], mul8 g x ∈ L := by
      simp only [closedB, List.all_eq_true, Std.HashSet.contains_ofList,
        List.contains_iff_mem] at hcl
      exact hcl
    have hc := card_genSub [c7, r] L hgv hunit hwords hv hone' hclosed hnd'
    rw [hgen, hcard] at hc
    rcases hor with h1 | ⟨p, hp, hpB⟩
    · exact absurd hc.symm h1
    · simp only [conjB, Bool.and_eq_true, beq_iff_eq, s7H, Std.HashSet.contains_ofList,
        List.contains_iff_mem, S7Cert.validB_iff] at hpB
      obtain ⟨⟨⟨hpv, hpm⟩, hpc⟩, hpr⟩ := hpB
      have hp1 : p.1 ∈ S8Cert.s8E := by
        obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
        exact hm
      obtain ⟨m, hm, hmd⟩ := S8Cert.exists_mem_s8 hp1
      have hmi := inv_eq_dec8 hmd hpv hpm
      refine ⟨m, hm, ?_, ?_⟩
      · obtain ⟨u, hu, hud⟩ := S7Cert.exists_mem_s7 hpc
        have : u = m * s7g0 * m⁻¹ := Units.ext (by
          rw [hud, dec8_mul8_mul8 valid8_c7.1 hpv.1, Units.val_mul, Units.val_mul, hmd, hmi,
            dec8_c7])
        rw [← this]
        exact hu
      · obtain ⟨u, hu, hud⟩ := S7Cert.exists_mem_s7 hpr
        have : u = m * R * m⁻¹ := Units.ext (by
          rw [hud, dec8_mul8_mul8 hrv.1 hpv.1, Units.val_mul, Units.val_mul, hmd, hmi, hR])
        rw [← this]
        exact hu
  · exfalso
    have hle := length_le_card hgv hunit hwords hv hnd'
    rw [hgen, hcard] at hle
    omega

theorem conj_mem_closure_pair {G : Type*} [Group G] (M a b : G) {y : G}
    (hy : y ∈ Subgroup.closure ({a, b} : Set G)) :
    M * y * M⁻¹ ∈ Subgroup.closure ({M * a * M⁻¹, M * b * M⁻¹} : Set G) := by
  have h := Subgroup.mem_map_of_mem (MulAut.conj M).toMonoidHom hy
  rw [MonoidHom.map_closure, Set.image_pair] at h
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h

theorem conj_mem_of_closure_pair {G : Type*} [Group G] {K : Subgroup G} {M a b : G}
    (ha : M * a * M⁻¹ ∈ K) (hb : M * b * M⁻¹ ∈ K) {y : G}
    (hy : y ∈ Subgroup.closure ({a, b} : Set G)) : M * y * M⁻¹ ∈ K := by
  have h := conj_mem_closure_pair M a b hy
  refine (Subgroup.closure_le K).mpr ?_ h
  rintro w (rfl | rfl)
  · exact ha
  · exact hb

theorem exists_pair {G : Type*} [Group G] {Y : Subgroup G} (φ : Equiv.Perm (Fin 7) ≃* ↥Y)
    {z : G} (hzY : z ∈ Y) (hz7 : orderOf z = 7) :
    ∃ h₀ ∈ Y, h₀ * h₀ = 1 ∧ h₀ ≠ 1 ∧ ∀ y ∈ Y, y ∈ Subgroup.closure ({z, h₀} : Set G) := by
  classical
  set σ' : Equiv.Perm (Fin 7) := φ.symm ⟨z, hzY⟩ with hσ'
  have hσ'7 : orderOf σ' = 7 := by rw [hσ', MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz7]
  have hcyc : σ'.IsCycle := Equiv.Perm.isCycle_of_prime_order''
    (by rw [Fintype.card_fin]; norm_num) (by rw [hσ'7, Fintype.card_fin])
  have hsupp : σ'.support = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [← hcyc.orderOf, hσ'7, Fintype.card_fin]
  set τ : Equiv.Perm (Fin 7) := Equiv.swap 0 1 with hτ
  have hcl : Subgroup.closure ({σ', τ} : Set (Equiv.Perm (Fin 7))) = ⊤ :=
    Equiv.Perm.closure_prime_cycle_swap (by rw [Fintype.card_fin]; norm_num) hcyc hsupp
      ⟨0, 1, by decide, rfl⟩
  refine ⟨((φ τ : ↥Y) : G), (φ τ).2, ?_, ?_, fun y hy => ?_⟩
  · rw [← Subgroup.coe_mul, ← map_mul, show τ * τ = 1 from Equiv.swap_mul_self 0 1, map_one,
      Subgroup.coe_one]
  · intro h1
    have h2 : φ τ = 1 := Subtype.ext h1
    have h3 : τ = 1 := by simpa using congrArg φ.symm h2
    exact absurd h3 (by decide)
  · set f : Equiv.Perm (Fin 7) →* G := Y.subtype.comp φ.toMonoidHom with hf
    have hmem : φ.symm ⟨y, hy⟩ ∈ Subgroup.closure ({σ', τ} : Set (Equiv.Perm (Fin 7))) := by
      rw [hcl]
      exact Subgroup.mem_top _
    have h1 := Subgroup.mem_map_of_mem f hmem
    rw [MonoidHom.map_closure, Set.image_pair] at h1
    have hfσ : f σ' = z := by simp [hf, hσ']
    have hfy : f (φ.symm ⟨y, hy⟩) = y := by simp [hf]
    rwa [hfσ, hfy] at h1

theorem exists_conj_seven {Y : Subgroup (GL (Fin 8) (ZMod 2))}
    (hY : Y ≤ s8) {y₀ c : GL (Fin 8) (ZMod 2)} (hy₀ : y₀ ∈ Y) (hy₀7 : orderOf y₀ = 7)
    (hc : c ∈ s8) (hc7 : orderOf c = 7) :
    ∃ g ∈ s8, ∃ z ∈ Y, g * z * g⁻¹ = c := by
  classical
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard8 : Nat.card ↥s8 = 40320 := S8Cert.card_s8
  have hsyl : ∀ P : Subgroup ↥s8, Nat.card P = 7 → IsPGroup 7 P ∧ ¬ 7 ∣ P.index := by
    intro P hP
    refine ⟨IsPGroup.of_card (n := 1) (by rw [hP]; norm_num), ?_⟩
    have h1 := P.card_mul_index
    rw [hP, hcard8] at h1
    have h2 : P.index = 5760 := by omega
    rw [h2]
    decide
  set P₁ : Subgroup ↥s8 := Subgroup.zpowers ⟨y₀, hY hy₀⟩ with hP₁
  set P₂ : Subgroup ↥s8 := Subgroup.zpowers ⟨c, hc⟩ with hP₂
  have hP₁c : Nat.card P₁ = 7 := by rw [hP₁, Nat.card_zpowers, Subgroup.orderOf_mk, hy₀7]
  have hP₂c : Nat.card P₂ = 7 := by rw [hP₂, Nat.card_zpowers, Subgroup.orderOf_mk, hc7]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥s8) ((hsyl P₁ hP₁c).1.toSylow (hsyl P₁ hP₁c).2)
    ((hsyl P₂ hP₂c).1.toSylow (hsyl P₂ hP₂c).2)
  have hcP : (⟨c, hc⟩ : ↥s8) ∈
      (((hsyl P₂ hP₂c).1.toSylow (hsyl P₂ hP₂c).2 : Sylow 7 ↥s8) : Subgroup ↥s8) :=
    Subgroup.mem_zpowers _
  rw [← hg, Sylow.coe_subgroup_smul] at hcP
  obtain ⟨t₀, ht₀, he⟩ := hcP
  refine ⟨(g : GL (Fin 8) (ZMod 2)), g.2, (t₀ : GL (Fin 8) (ZMod 2)), ?_, ?_⟩
  · have ht₀' : t₀ ∈ Subgroup.zpowers (⟨y₀, hY hy₀⟩ : ↥s8) := ht₀
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht₀'
    rw [SubgroupClass.coe_zpow]
    exact Y.zpow_mem hy₀ k
  · have := congrArg Subtype.val he
    simpa [MulAut.conj_apply] using this

theorem card_eq_of_conj {G : Type*} [Group G] {Y K : Subgroup G} {M : G}
    (hle : ∀ y ∈ Y, M * y * M⁻¹ ∈ K) (hge : ∀ k ∈ K, ∃ y ∈ Y, M * y * M⁻¹ = k) :
    Nat.card K = Nat.card Y := by
  have h : Y.map (MulAut.conj M).toMonoidHom = K := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hle y hy
    · intro k hk
      obtain ⟨y, hy, rfl⟩ := hge k hk
      exact ⟨y, hy, rfl⟩
  rw [← h, Subgroup.card_map_of_injective (MulAut.conj M).injective]

theorem mem_zpowers_pow {G : Type*} [Group G] [Finite G] {c : G} (hc7 : orderOf c = 7) {k : ℕ}
    (hk : c ^ k ≠ 1) : c ∈ Subgroup.zpowers (c ^ k) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7 : c ^ 7 = 1 := by rw [← hc7]; exact pow_orderOf_eq_one _
  have hle : Subgroup.zpowers (c ^ k) ≤ Subgroup.zpowers c :=
    (Subgroup.zpowers_le).mpr (Subgroup.npow_mem_zpowers _ _)
  have hc1 : Nat.card (Subgroup.zpowers (c ^ k)) = 7 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [← pow_mul, mul_comm, pow_mul, h7, one_pow]) hk
  have hc2 : Nat.card (Subgroup.zpowers c) = 7 := by rw [Nat.card_zpowers, hc7]
  rw [Subgroup.eq_of_le_of_card_ge hle (by rw [hc1, hc2])]
  exact Subgroup.mem_zpowers _

theorem exists_conj_s7
    {Y : Subgroup (GL (Fin 8) (ZMod 2))} (hY : Y ≤ s8)
    (φ : Equiv.Perm (Fin 7) ≃* ↥Y) : ∃ m ∈ s8, ∀ y ∈ Y, m * y * m⁻¹ ∈ s7 := by
  classical
  have hc7s8 : s7g0 ∈ s8 := s7_le_s8 s7g0_mem_s7
  have hσ7 : orderOf (finRotate 7) = 7 := by
    rw [(isCycle_finRotate (n := 5)).orderOf, support_finRotate, Finset.card_univ,
      Fintype.card_fin]
  have hy₀7 : orderOf ((φ (finRotate 7) : ↥Y) : GL (Fin 8) (ZMod 2)) = 7 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hσ7]
  obtain ⟨g', hg's8, z, hzY, hgz⟩ :=
    exists_conj_seven hY (φ (finRotate 7)).2 hy₀7 hc7s8 orderOf_s7g0
  have hz7 : orderOf z = 7 := by
    have h1 : orderOf (g' * z * g'⁻¹) = orderOf z := by
      rw [show g' * z * g'⁻¹ = MulAut.conj g' z from rfl, MulEquiv.orderOf_eq]
    rw [hgz, orderOf_s7g0] at h1
    exact h1.symm
  obtain ⟨h₀, hh₀Y, hh₀2, hh₀1, hY'⟩ := exists_pair φ hzY hz7
  set h₁ : GL (Fin 8) (ZMod 2) := g' * h₀ * g'⁻¹ with hh₁
  have hh₁s8 : h₁ ∈ s8 := s8.mul_mem (s8.mul_mem hg's8 (hY hh₀Y)) (s8.inv_mem hg's8)
  have hh₁2 : h₁ * h₁ = 1 := by
    rw [hh₁, show g' * h₀ * g'⁻¹ * (g' * h₀ * g'⁻¹) = g' * (h₀ * h₀) * g'⁻¹ by group, hh₀2]
    group
  have hh₁1 : h₁ ≠ 1 := by
    intro h1
    apply hh₀1
    calc h₀ = g'⁻¹ * (g' * h₀ * g'⁻¹) * g' := by group
      _ = 1 := by rw [← hh₁, h1]; group
  obtain ⟨-, hnB, horb, hreps⟩ := check_parts
  have hh₁inv : colsOf (h₁ : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ invs8 := by
    rw [invs8, List.mem_filter]
    refine ⟨(S8Cert.mem_s8_iff h₁).mp hh₁s8, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
    refine ⟨?_, ?_⟩
    · rw [← colsOf_mul, ← Units.val_mul, hh₁2, Units.val_one, colsOf_one]
    · intro h1
      apply hh₁1
      apply Units.ext
      rw [Units.val_one, ← dec8_colsOf (h₁ : Matrix (Fin 8) (Fin 8) (ZMod 2)), h1, dec8_one8]
  simp only [orbB, List.all_eq_true, List.any_eq_true, repsH, Std.HashSet.contains_ofList,
    List.contains_iff_mem] at horb
  obtain ⟨p, hp, hpr⟩ := horb _ hh₁inv
  simp only [nB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true,
    S7Cert.validB_iff] at hnB
  obtain ⟨⟨hpv, hpm⟩, c, hc, hpc⟩ := hnB p hp
  have hp1 : p.1 ∈ S8Cert.s8E := by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
    exact (List.mem_filter.mp hm).1
  obtain ⟨n, hn, hnd⟩ := S8Cert.exists_mem_s8 hp1
  have hni := inv_eq_dec8 hnd hpv hpm
  have hpv1 : Valid8 p.1 := (S7Cert.subB_spec S8Cert.s8Basic_spec.1).1 _ hp1
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  have hk6 : k < 6 := List.mem_range.mp hk
  have hnc : n * s7g0 * n⁻¹ = s7g0 ^ (k + 1) := by
    apply Units.ext
    have h1 := congrArg dec8 hpc
    rw [dec8_mul8 _ _ valid8_c7.1, dec8_mul8 _ _ hpv1.1, dec8_iterate, dec8_c7, ← hnd] at h1
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, h1, Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  set r := mul8 (mul8 p.1 (colsOf (h₁ : Matrix (Fin 8) (Fin 8) (ZMod 2)))) p.2 with hr
  set R : GL (Fin 8) (ZMod 2) := n * h₁ * n⁻¹ with hRdef
  have hR : (R : Matrix (Fin 8) (Fin 8) (ZMod 2)) = dec8 r := by
    rw [hr, dec8_mul8_mul8 (valid8_colsOf _).1 hpv.1, dec8_colsOf, hRdef, Units.val_mul,
      Units.val_mul, hnd, hni]
  have hrv : Valid8 r := valid8_mul8 (valid8_mul8 hpv1 (valid8_colsOf _)) hpv
  set M : GL (Fin 8) (ZMod 2) := n * g' with hM
  have hMz : M * z * M⁻¹ = s7g0 ^ (k + 1) := by
    rw [hM, show n * g' * z * (n * g')⁻¹ = n * (g' * z * g'⁻¹) * n⁻¹ by group, hgz, hnc]
  have hMh : M * h₀ * M⁻¹ = R := by
    rw [hM, hRdef, hh₁]
    group
  have hpow : s7g0 ^ (k + 1) ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [orderOf_s7g0] at this
    omega
  have hzp := mem_zpowers_pow orderOf_s7g0 hpow
  have hconjY : ∀ y ∈ Y,
      M * y * M⁻¹ ∈ Subgroup.closure ({s7g0, R} : Set (GL (Fin 8) (ZMod 2))) := by
    intro y hy
    refine conj_mem_of_closure_pair ?_ ?_ (hY' y hy)
    · rw [hMz]
      exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _
    · rw [hMh]
      exact Subgroup.subset_closure (by simp)
  have hcardY : Nat.card Y = 5040 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  have hge : ∀ w ∈ Subgroup.closure ({s7g0, R} : Set (GL (Fin 8) (ZMod 2))),
      ∃ y ∈ Y, M * y * M⁻¹ = w := by
    set K : Subgroup (GL (Fin 8) (ZMod 2)) := Y.map (MulAut.conj M).toMonoidHom with hK
    have hle : Subgroup.closure ({s7g0, R} : Set (GL (Fin 8) (ZMod 2))) ≤ K := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro w (rfl | rfl)
      · obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzp
        refine ⟨z ^ j, Y.zpow_mem hzY j, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, map_zpow, MulAut.conj_apply, hMz, hj]
      · refine ⟨h₀, hh₀Y, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hMh]
    intro w hw
    obtain ⟨y, hy, hyw⟩ := hle hw
    exact ⟨y, hy, hyw⟩
  have hcardK : Nat.card (Subgroup.closure ({s7g0, R} : Set (GL (Fin 8) (ZMod 2)))) = 5040 := by
    rw [card_eq_of_conj hconjY hge, hcardY]
  obtain ⟨m', hm', hm'c, hm'R⟩ := exists_of_hB hR hrv (hreps r hpr) hcardK
  refine ⟨m' * M, s8.mul_mem hm' (s8.mul_mem hn hg's8), fun y hy => ?_⟩
  rw [show m' * M * y * (m' * M)⁻¹ = m' * (M * y * M⁻¹) * m'⁻¹ by group]
  exact conj_mem_of_closure_pair hm'c hm'R (hconjY y hy)

end CFSG.Quasithin.H13.S7Conj
