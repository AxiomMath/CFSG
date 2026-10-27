module

public import CFSG.Quasithin.Recognition.Stroth.Str86U3Model

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin
open scoped Pointwise commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}

private theorem uJGL_zero_one_mem_ujSub (hK : Nat.card K = (2 ^ k) ^ 2) :
    CFSG.Quasithin.H.SU3.uJGL k 0 1 ∈ CFSG.Quasithin.H.SU3.ujSub k K := by
  refine CFSG.Quasithin.H.SU3.uJGL_mem_ujSub hK ?_
  rw [CFSG.Quasithin.H.SU3.traceHom_apply]
  simp [CharTwo.add_self_eq_zero]

private theorem exists_uJGL_one_mem_ujSub (hk : 1 ≤ k)
    (hK : Nat.card K = (2 ^ k) ^ 2) :
    ∃ b : K, CFSG.Quasithin.H.SU3.uJGL k 1 b ∈ CFSG.Quasithin.H.SU3.ujSub k K := by
  obtain ⟨u, hu, hu01⟩ :=
    CFSG.Quasithin.H.SU3.exists_ujSub_zero_one (K := K) (n := k) hk hK 1
  obtain ⟨a, b, hb, hu_eq⟩ := exists_uJGL_of_mem_ujSub (F := K) hK hu
  have h01 : ((CFSG.Quasithin.H.SU3.uJGL k a b : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 1 = 1 := by
    rw [← hu_eq]
    exact hu01
  have ha : a = 1 := by
    simpa [CFSG.Quasithin.H.SU3.coe_uJGL, CFSG.Quasithin.H.SU3.uJMat] using h01
  refine ⟨b, ?_⟩
  rw [hu_eq] at hu
  simpa [ha] using hu

private theorem uJSub_mulVec_third (hK : Nat.card K = (2 ^ k) ^ 2)
    {x : GL (Fin 3) K} (hx : x ∈ CFSG.Quasithin.H.SU3.ujSub k K) (v : Fin 3 → K) :
    ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 2 = v 2 := by
  obtain ⟨a, b, hb, rfl⟩ := exists_uJGL_of_mem_ujSub (F := K) hK hx
  rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
  rfl

private theorem uJSub_mulVec_first_of_third_eq_zero (hK : Nat.card K = (2 ^ k) ^ 2)
    {x : GL (Fin 3) K} (hx : x ∈ CFSG.Quasithin.H.SU3.ujSub k K)
    {v : Fin 3 → K} (hv : v 2 = 0) :
    ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ v) 1 = v 1 := by
  obtain ⟨a, b, hb, rfl⟩ := exists_uJGL_of_mem_ujSub (F := K) hK hx
  rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
  simp [hv]

private theorem ujSub_fixed_iff (hk : 2 ≤ k) (hK : Nat.card K = (2 ^ k) ^ 2)
    (v : Fin 3 → K) :
    (∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K,
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v) ↔
      v 1 = 0 ∧ v 2 = 0 := by
  constructor
  · intro hfix
    by_cases hv2 : v 2 = 0
    · by_cases hv1 : v 1 = 0
      · exact ⟨hv1, hv2⟩
      · obtain ⟨u, hu, hu01⟩ :=
          CFSG.Quasithin.H.SU3.exists_ujSub_zero_one (K := K) (n := k) (by omega) hK 1
        obtain ⟨a, b, hb, hu_eq⟩ := exists_uJGL_of_mem_ujSub (F := K) hK hu
        have h01 : ((CFSG.Quasithin.H.SU3.uJGL k a b : GL (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) 0 1 = 1 := by
          rw [← hu_eq]
          exact hu01
        have ha : a = 1 := by
          simpa [CFSG.Quasithin.H.SU3.coe_uJGL, CFSG.Quasithin.H.SU3.uJMat] using h01
        have h := hfix u hu
        rw [hu_eq, ha, CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec] at h
        have h0 : v 0 + v 1 = v 0 + 0 := by
          simpa [hv2] using congrFun h 0
        exact (hv1 (add_left_cancel h0)).elim
    · have h := hfix (CFSG.Quasithin.H.SU3.uJGL k 0 1)
        (uJGL_zero_one_mem_ujSub hK)
      rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec] at h
      have h0 : v 0 + v 2 = v 0 + 0 := by
        simpa using congrFun h 0
      exact (hv2 (add_left_cancel h0)).elim
  · rintro ⟨hv1, hv2⟩ x hx
    obtain ⟨a, b, hb, rfl⟩ := exists_uJGL_of_mem_ujSub (F := K) hK hx
    rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
    ext i
    fin_cases i <;> simp [hv1, hv2]

end Model

section Coords

variable {N S : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
  (Φ : Additive ↥N ≃+ (Fin 3 → K))

private noncomputable def coordTwoHom : ↥N →* Multiplicative K where
  toFun n := Multiplicative.ofAdd ((Φ (Additive.ofMul n)) 2)
  map_one' := by simp
  map_mul' a b := by
    rw [ofMul_mul, map_add, Pi.add_apply, ofAdd_add]

private theorem mem_coordTwo_ker_iff (n : ↥N) :
    n ∈ (coordTwoHom Φ).ker ↔ (Φ (Additive.ofMul n)) 2 = 0 := by
  change Multiplicative.ofAdd ((Φ (Additive.ofMul n)) 2) = 1 ↔ _
  rw [ofAdd_eq_one]

private noncomputable def coordOneTwoHom : ↥N →* Multiplicative (K × K) where
  toFun n := Multiplicative.ofAdd ((Φ (Additive.ofMul n)) 1, (Φ (Additive.ofMul n)) 2)
  map_one' := by simp
  map_mul' a b := by
    rw [ofMul_mul, map_add]
    change Multiplicative.ofAdd ((Φ (Additive.ofMul a)) 1 + (Φ (Additive.ofMul b)) 1,
      (Φ (Additive.ofMul a)) 2 + (Φ (Additive.ofMul b)) 2) = _
    rw [show ((Φ (Additive.ofMul a)) 1 + (Φ (Additive.ofMul b)) 1,
        (Φ (Additive.ofMul a)) 2 + (Φ (Additive.ofMul b)) 2) =
      ((Φ (Additive.ofMul a)) 1, (Φ (Additive.ofMul a)) 2) +
        ((Φ (Additive.ofMul b)) 1, (Φ (Additive.ofMul b)) 2) by rfl]
    rw [ofAdd_add]

private theorem mem_coordOneTwo_ker_iff (n : ↥N) :
    n ∈ (coordOneTwoHom Φ).ker ↔
      (Φ (Additive.ofMul n)) 1 = 0 ∧ (Φ (Additive.ofMul n)) 2 = 0 := by
  change Multiplicative.ofAdd ((Φ (Additive.ofMul n)) 1,
    (Φ (Additive.ofMul n)) 2) = 1 ↔ _
  rw [ofAdd_eq_one, Prod.ext_iff]
  simp

private noncomputable def lift (w : Fin 3 → K) : ↥N := (Φ.symm w).toMul

private theorem lift_spec (w : Fin 3 → K) :
    Φ (Additive.ofMul (lift Φ w)) = w := by
  rw [lift, ofMul_toMul]
  exact Φ.apply_symm_apply w

private theorem mul_conj_apply (hN : IsElemAbelian 2 N)
    (hSN : S ≤ Subgroup.normalizer (N : Set G))
    {a : ↥N} {s : G} (hs : s ∈ S) {x : GL (Fin 3) K}
    (hact : ∀ n n' : ↥N, (n' : G) = s * n * s⁻¹ →
      Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n)) :
    ∃ c : ↥N, (c : G) = ⁅(a : G), s⁆ ∧
      Φ (Additive.ofMul c) =
        Φ (Additive.ofMul a) + (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul a) := by
  let ca : ↥N := ⟨s * (a : G) * s⁻¹,
    (Subgroup.mem_normalizer_iff.mp (hSN hs) (a : G)).1 a.2⟩
  have hca : (ca : G) = s * (a : G) * s⁻¹ := rfl
  have hval : Φ (Additive.ofMul ca) =
      (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul a) :=
    hact a ca hca
  have h2 : (a : ↥N) * a = 1 := by
    apply Subtype.ext
    have := hN.2 (a : G) a.2
    simpa [pow_two] using this
  have ha_inv : (a : ↥N)⁻¹ = a := (eq_inv_of_mul_eq_one_left h2).symm
  have ha_invG : (a : G)⁻¹ = (a : G) := by
    simpa using congrArg Subtype.val ha_inv
  refine ⟨a * ca, ?_, ?_⟩
  · rw [Subgroup.coe_mul, hca, commutatorElement_def, ha_invG]
    group
  · rw [ofMul_mul, map_add, hval]

private theorem mem_map_subtype_iff (P : Subgroup ↥N) (n : ↥N) :
    (n : G) ∈ P.map N.subtype ↔ n ∈ P := by
  constructor
  · rintro ⟨m, hm, hmn⟩
    have : m = n := Subtype.ext hmn
    simpa [this] using hm
  · intro hn
    exact ⟨n, hn, rfl⟩

private theorem map_coordTwo_ker_eq_commutator (hN : IsElemAbelian 2 N)
    (hSN : S ≤ Subgroup.normalizer (N : Set G))
    (hk : 2 ≤ k) (hK : Nat.card K = (2 ^ k) ^ 2)
    (h3 : ∀ s ∈ S, ∃ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∀ n n' : ↥N,
      (n' : G) = s * n * s⁻¹ →
        Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n))
    (h4 : ∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∃ s ∈ S, ∀ n n' : ↥N,
      (n' : G) = s * n * s⁻¹ →
        Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n)) :
    (coordTwoHom Φ).ker.map N.subtype = ⁅N, S⁆ := by
  apply le_antisymm
  · rintro y ⟨c, hc, rfl⟩
    let v : Fin 3 → K := Φ (Additive.ofMul c)
    have hv2 : v 2 = 0 := (mem_coordTwo_ker_iff Φ c).1 hc
    obtain ⟨b0, hx0mem⟩ := exists_uJGL_one_mem_ujSub (by omega) hK
    obtain ⟨s0, hs0, hs0act⟩ := h4 (CFSG.Quasithin.H.SU3.uJGL k 1 b0) hx0mem
    let w1 : Fin 3 → K := ![0, v 0 + b0 * v 1, 0]
    let w2 : Fin 3 → K := ![0, 0, v 1]
    obtain ⟨c1, hc1G, hc1val⟩ :=
      mul_conj_apply Φ hN hSN hs0 hs0act (a := lift Φ w1)
    obtain ⟨c2, hc2G, hc2val⟩ :=
      mul_conj_apply Φ hN hSN hs0 hs0act (a := lift Φ w2)
    have hx1 : ((CFSG.Quasithin.H.SU3.uJGL k 1 b0 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ w1 = ![w1 1, w1 1, 0] := by
      rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
      ext i
      fin_cases i <;> simp [w1]
    have hx2 : ((CFSG.Quasithin.H.SU3.uJGL k 1 b0 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ w2 = ![b0 * w2 2, w2 2, w2 2] := by
      rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
      ext i
      fin_cases i <;> simp [w2]
    have hval1 : Φ (Additive.ofMul c1) =
        w1 + ((CFSG.Quasithin.H.SU3.uJGL k 1 b0 : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ w1 := by
      rw [hc1val, lift_spec]
    have hval2 : Φ (Additive.ofMul c2) =
        w2 + ((CFSG.Quasithin.H.SU3.uJGL k 1 b0 : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) *ᵥ w2 := by
      rw [hc2val, lift_spec]
    have hsum : Φ (Additive.ofMul (c1 * c2)) = v := by
      rw [ofMul_mul, map_add, hval1, hval2, hx1, hx2]
      ext i
      fin_cases i <;> simp [w1, w2, hv2, CharTwo.add_self_eq_zero, add_assoc]
    have hc_eq : c1 * c2 = c :=
      Additive.ofMul.injective (Φ.injective hsum)
    have hc1mem : (c1 : G) ∈ ⁅N, S⁆ := by
      rw [hc1G]
      exact Subgroup.commutator_mem_commutator (lift Φ w1).2 hs0
    have hc2mem : (c2 : G) ∈ ⁅N, S⁆ := by
      rw [hc2G]
      exact Subgroup.commutator_mem_commutator (lift Φ w2).2 hs0
    rw [← hc_eq]
    change (c1 : G) * (c2 : G) ∈ ⁅N, S⁆
    exact (⁅N, S⁆).mul_mem hc1mem hc2mem
  · rw [Subgroup.commutator_le]
    intro a ha s hs
    obtain ⟨x, hx, hact⟩ := h3 s hs
    obtain ⟨c, hcG, hcval⟩ := mul_conj_apply Φ hN hSN hs hact (a := ⟨a, ha⟩)
    refine Subgroup.mem_map.mpr ⟨c, ?_, hcG⟩
    rw [mem_coordTwo_ker_iff, hcval, Pi.add_apply, uJSub_mulVec_third hK hx,
      CharTwo.add_self_eq_zero]

private theorem map_coordOneTwo_ker_eq_inf_centralizer
    (hSN : S ≤ Subgroup.normalizer (N : Set G))
    (hk : 2 ≤ k) (hK : Nat.card K = (2 ^ k) ^ 2)
    (h3 : ∀ s ∈ S, ∃ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∀ n n' : ↥N,
      (n' : G) = s * n * s⁻¹ →
        Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n))
    (h4 : ∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∃ s ∈ S, ∀ n n' : ↥N,
      (n' : G) = s * n * s⁻¹ →
        Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n)) :
    (coordOneTwoHom Φ).ker.map N.subtype =
      N ⊓ Subgroup.centralizer (S : Set G) := by
  apply le_antisymm
  · rintro y ⟨n, hn, rfl⟩
    have hφ := (mem_coordOneTwo_ker_iff Φ n).1 hn
    refine Subgroup.mem_inf.mpr ⟨n.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨x, hx, hact⟩ := h3 s hs
    let n' : ↥N := ⟨s * (n : G) * s⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hSN hs) (n : G)).1 n.2⟩
    have hn' : (n' : G) = s * (n : G) * s⁻¹ := rfl
    have hfix : (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n) =
        Φ (Additive.ofMul n) :=
      (ujSub_fixed_iff hk hK _).2 hφ x hx
    have hval : Φ (Additive.ofMul n') = Φ (Additive.ofMul n) := by
      rw [hact n n' hn', hfix]
    have hn'_eq : n' = n := Additive.ofMul.injective (Φ.injective hval)
    have hconj : s * (n : G) * s⁻¹ = (n : G) := congrArg Subtype.val hn'_eq
    calc s * (n : G) = (s * (n : G) * s⁻¹) * s := by group
      _ = (n : G) * s := by rw [hconj]
  · rintro x ⟨hxN, hxC⟩
    let n : ↥N := ⟨x, hxN⟩
    refine Subgroup.mem_map.mpr ⟨n, ?_, rfl⟩
    rw [mem_coordOneTwo_ker_iff]
    refine (ujSub_fixed_iff hk hK _).1 ?_
    intro xx hxx
    obtain ⟨s, hs, hact⟩ := h4 xx hxx
    let n' : ↥N := ⟨s * x * s⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hSN hs) x).1 hxN⟩
    have hn' : (n' : G) = s * (n : G) * s⁻¹ := rfl
    have hxs : s * x * s⁻¹ = x := by
      have hcomm : s * x = x * s := ((Subgroup.mem_centralizer_iff.mp hxC) s hs)
      calc s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hcomm]
        _ = x := by group
    have hn'_eq : n' = n := Subtype.ext (hn'.trans hxs)
    have hfix := hact n n' hn'
    rw [hn'_eq] at hfix
    exact hfix.symm

private theorem map_coordOneTwo_ker_eq_commutator_commutator
    (hN : IsElemAbelian 2 N)
    (hSN : S ≤ Subgroup.normalizer (N : Set G))
    (hk : 2 ≤ k) (hK : Nat.card K = (2 ^ k) ^ 2)
    (h3 : ∀ s ∈ S, ∃ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∀ n n' : ↥N,
      (n' : G) = s * n * s⁻¹ →
        Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n))
    (h4 : ∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∃ s ∈ S, ∀ n n' : ↥N,
      (n' : G) = s * n * s⁻¹ →
        Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ Φ (Additive.ofMul n))
    (hP2 : (coordTwoHom Φ).ker.map N.subtype = ⁅N, S⁆) :
    (coordOneTwoHom Φ).ker.map N.subtype = ⁅⁅N, S⁆, S⁆ := by
  apply le_antisymm
  · rintro y ⟨c, hc, rfl⟩
    let v : Fin 3 → K := Φ (Additive.ofMul c)
    have hv1 : v 1 = 0 := ((mem_coordOneTwo_ker_iff Φ c).1 hc).1
    have hv2 : v 2 = 0 := ((mem_coordOneTwo_ker_iff Φ c).1 hc).2
    obtain ⟨b0, hx0mem⟩ := exists_uJGL_one_mem_ujSub (by omega) hK
    obtain ⟨s0, hs0, hs0act⟩ := h4 (CFSG.Quasithin.H.SU3.uJGL k 1 b0) hx0mem
    let w : Fin 3 → K := ![0, v 0, 0]
    obtain ⟨d, hdG, hdval⟩ :=
      mul_conj_apply Φ hN hSN hs0 hs0act (a := lift Φ w)
    have hxw : ((CFSG.Quasithin.H.SU3.uJGL k 1 b0 : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) *ᵥ w = ![w 1, w 1, 0] := by
      rw [CFSG.Quasithin.H.SU3.coe_uJGL, uJMat_mulVec]
      ext i
      fin_cases i <;> simp [w]
    have hval : Φ (Additive.ofMul d) = Φ (Additive.ofMul c) := by
      rw [hdval, lift_spec, hxw]
      ext i
      fin_cases i <;> simp [w, v, hv1, hv2, CharTwo.add_self_eq_zero]
    have hd_eq : d = c := Additive.ofMul.injective (Φ.injective hval)
    have hw2 : w 2 = 0 := by simp [w]
    have hwP2 : lift Φ w ∈ (coordTwoHom Φ).ker :=
      (mem_coordTwo_ker_iff Φ (lift Φ w)).2 (by rw [lift_spec]; exact hw2)
    have hwNS : ((lift Φ w : ↥N) : G) ∈ ⁅N, S⁆ := by
      rw [← hP2]
      exact Subgroup.mem_map.mpr ⟨lift Φ w, hwP2, rfl⟩
    have hdmem : (d : G) ∈ ⁅⁅N, S⁆, S⁆ := by
      rw [hdG]
      exact Subgroup.commutator_mem_commutator hwNS hs0
    rw [← hd_eq]
    exact hdmem
  · rw [Subgroup.commutator_le]
    intro a ha s hs
    have haP2 : a ∈ (coordTwoHom Φ).ker.map N.subtype := by
      rw [hP2]
      exact ha
    obtain ⟨an, han, hanG⟩ := Subgroup.mem_map.mp haP2
    obtain ⟨x, hx, hact⟩ := h3 s hs
    obtain ⟨d, hdG, hdval⟩ := mul_conj_apply Φ hN hSN hs hact (a := an)
    refine Subgroup.mem_map.mpr ⟨d, ?_, ?_⟩
    · rw [mem_coordOneTwo_ker_iff]
      have hv2 : (Φ (Additive.ofMul an)) 2 = 0 := (mem_coordTwo_ker_iff Φ an).1 han
      constructor
      · rw [hdval, Pi.add_apply, uJSub_mulVec_first_of_third_eq_zero hK hx hv2,
          CharTwo.add_self_eq_zero]
      · rw [hdval, Pi.add_apply, uJSub_mulVec_third hK hx, hv2,
          CharTwo.add_self_eq_zero]
    · change (d : G) = ⁅a, s⁆
      rw [hdG]
      change ⁅N.subtype an, s⁆ = ⁅a, s⁆
      rw [hanG]

end Coords

theorem str86_flag_coords_of_ujSub {N S : Subgroup G} (hN : IsElemAbelian 2 N)
    (hSN : S ≤ Subgroup.normalizer (N : Set G))
    {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ} (hk : 2 ≤ k)
    (hK : Nat.card K = (2 ^ k) ^ 2) (Φ : Additive ↥N ≃+ (Fin 3 → K))
    (h3 : ∀ s ∈ S, ∃ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∀ n n' : ↥N, (n' : G) = s * n * s⁻¹ →
      Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K).mulVec (Φ (Additive.ofMul n)))
    (h4 : ∀ x ∈ CFSG.Quasithin.H.SU3.ujSub k K, ∃ s ∈ S, ∀ n n' : ↥N, (n' : G) = s * n * s⁻¹ →
      Φ (Additive.ofMul n') = (x : Matrix (Fin 3) (Fin 3) K).mulVec (Φ (Additive.ofMul n))) :
    (∀ n : ↥N, (n : G) ∈ Subgroup.centralizer (S : Set G) ↔
      Φ (Additive.ofMul n) 1 = 0 ∧ Φ (Additive.ofMul n) 2 = 0) ∧
    ⁅N, S⁆ ≤ N ∧ (∀ n : ↥N, (n : G) ∈ ⁅N, S⁆ ↔ Φ (Additive.ofMul n) 2 = 0) ∧
    ⁅⁅N, S⁆, S⁆ ≤ N ∧ (∀ n : ↥N, (n : G) ∈ ⁅⁅N, S⁆, S⁆ ↔
      Φ (Additive.ofMul n) 1 = 0 ∧ Φ (Additive.ofMul n) 2 = 0) := by
  have hP2 := map_coordTwo_ker_eq_commutator Φ hN hSN hk hK h3 h4
  have hP1 := map_coordOneTwo_ker_eq_inf_centralizer Φ hSN hk hK h3 h4
  have hP1c := map_coordOneTwo_ker_eq_commutator_commutator Φ hN hSN hk hK h3 h4 hP2
  have hC : ∀ n : ↥N, (n : G) ∈ Subgroup.centralizer (S : Set G) ↔
      Φ (Additive.ofMul n) 1 = 0 ∧ Φ (Additive.ofMul n) 2 = 0 := by
    intro n
    have hinf : (n : G) ∈ N ⊓ Subgroup.centralizer (S : Set G) ↔
        (n : G) ∈ Subgroup.centralizer (S : Set G) := by
      rw [Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨n.2, h⟩⟩
    rw [← hinf, ← hP1, mem_map_subtype_iff (coordOneTwoHom Φ).ker n,
      mem_coordOneTwo_ker_iff]
  refine ⟨hC, ?_, ?_, ?_, ?_⟩
  · rw [← hP2]
    rintro x ⟨n, hn, rfl⟩
    exact n.2
  · intro n
    rw [← hP2, mem_map_subtype_iff (coordTwoHom Φ).ker n, mem_coordTwo_ker_iff]
  · rw [← hP1c]
    rintro x ⟨n, hn, rfl⟩
    exact n.2
  · intro n
    rw [← hP1c, mem_map_subtype_iff (coordOneTwoHom Φ).ker n,
      mem_coordOneTwo_ker_iff]

end CFSG.Quasithin.Stroth
