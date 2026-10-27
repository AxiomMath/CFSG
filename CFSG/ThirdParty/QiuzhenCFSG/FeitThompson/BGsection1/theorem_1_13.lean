module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_11

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise IsMulCommutative commutatorElement

public section

theorem CFSG.faithful_on_selfCentralizing_of_coprime {G A : Type*} [Group G] [Finite G]
    [Group A] [Finite A] [MulDistribMulAction A G] [FaithfulSMul A G]
    (C : Subgroup G) [C.Normal] [IsInvariant A G C]
    (hcent : Subgroup.centralizer (C : Set G) ≤ C)
    (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G)) :
    FaithfulSMul A C := by
  refine (faithfulSMul_iff (G := A) (α := C)).2 ?_
  intro a ha
  have hcop_a : Nat.Coprime (orderOf a) (Nat.card G) :=
    Nat.Coprime.of_dvd_left (orderOf_dvd_natCard a) hcoprime
  have haG : ∀ g : G, a • g = g := by
    intro g
    set x : G := g⁻¹ * (a • g) with hx_def
    have hx_centralizer : x ∈ Subgroup.centralizer (C : Set G) := by
      refine (Subgroup.mem_centralizer_iff (g := x) (s := (C : Set G))).2 ?_
      intro c hc
      have hc_fix : a • c = c := by
        have := congrArg Subtype.val (ha ⟨c, hc⟩)
        change ((a • (⟨c, hc⟩ : C) : C) : G) = c
        exact this
      have hconj : g * c * g⁻¹ ∈ C := Subgroup.Normal.conj_mem inferInstance c hc g
      have hconj_fix : a • (g * c * g⁻¹) = g * c * g⁻¹ := by
        have h := congrArg Subtype.val (ha ⟨g * c * g⁻¹, hconj⟩)
        have hcoe :
            ((a • (⟨g * c * g⁻¹, hconj⟩ : C) : C) : G) = a • (g * c * g⁻¹) := rfl
        simpa [hcoe] using h
      have hconj_eq : g * c * g⁻¹ = (a • g) * c * (a • g)⁻¹ := by
        have :
            (a • g) * c * (a • g)⁻¹ = g * c * g⁻¹ := by
          simpa [smul_mul', smul_inv', hc_fix, mul_assoc] using hconj_fix
        simpa using this.symm
      have h1 : g * c * g⁻¹ * (a • g) = (a • g) * c := by
        calc
          g * c * g⁻¹ * (a • g)
              = ((a • g) * c * (a • g)⁻¹) * (a • g) := by
                  simpa [mul_assoc] using congrArg (fun t => t * (a • g)) hconj_eq
          _ = (a • g) * c := by
              simp [mul_assoc]
      have h2 : c * g⁻¹ * (a • g) = g⁻¹ * (a • g) * c := by
        have := congrArg (fun t : G => g⁻¹ * t) h1
        simpa [mul_assoc] using this
      simpa [hx_def, mul_assoc] using h2
    have hx_mem_C : x ∈ C := hcent hx_centralizer
    have hx_fix : a • x = x := by
      have := congrArg Subtype.val (ha ⟨x, hx_mem_C⟩)
      change ((a • (⟨x, hx_mem_C⟩ : C) : C) : G) = x
      exact this
    have hx_fix_pow : ∀ n : ℕ, (a ^ n) • x = x := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          simp [pow_succ, mul_smul, hx_fix, ih]
    have ha_g : a • g = g * x := by
      simp [hx_def]
    have hpow : ∀ n : ℕ, (a ^ n) • g = g * x ^ n := by
      intro n
      induction n with
      | zero =>
          simp
      | succ n ih =>
          calc
            (a ^ (n + 1)) • g
                = (a ^ n) • (a • g) := by
                    simp [pow_succ, mul_smul]
            _ = (a ^ n) • (g * x) := by simp [ha_g]
            _ = ((a ^ n) • g) * ((a ^ n) • x) := by
                    simp [smul_mul']
            _ = (g * x ^ n) * x := by
                    simp [ih, hx_fix_pow n]
            _ = g * x ^ (n + 1) := by
                    simp [pow_succ, mul_assoc]
    have hx_pow_order : x ^ orderOf a = 1 := by
      have ha_pow : a ^ orderOf a = (1 : A) := pow_orderOf_eq_one a
      have : g = g * x ^ orderOf a := by
        calc
          g = (1 : A) • g := by simp
          _ = (a ^ orderOf a) • g := by simp [ha_pow]
          _ = g * x ^ orderOf a := hpow (orderOf a)
      have := congrArg (fun t : G => g⁻¹ * t) this
      simpa [mul_assoc] using this.symm
    have h_order_dvd : orderOf x ∣ orderOf a :=
      (orderOf_dvd_iff_pow_eq_one).2 hx_pow_order
    have h_order_one : orderOf x = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop_a h_order_dvd (orderOf_dvd_natCard x)
    have hx_one : x = 1 := (orderOf_eq_one_iff).1 h_order_one
    have : a • g = g * x := by
      simp [hx_def]
    simpa [hx_one] using this
  exact (faithfulSMul_iff (G := A) (α := G)).1 inferInstance a haG

def CFSG.theorem_1_13_critical_quotient_layer {G : Type*} [Group G] (K : Subgroup G)
    [K.Normal] {p : ℕ} : Subgroup (G ⧸ K) where
  carrier := {x : G ⧸ K | x ∈ Subgroup.center (G ⧸ K) ∧ x ^ p = 1}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    rcases hx with ⟨hxcent, hxpow⟩
    rcases hy with ⟨hycent, hypow⟩
    constructor
    · exact (Subgroup.center (G ⧸ K)).mul_mem hxcent hycent
    · have hxy : Commute x y := by
        exact (Subgroup.mem_center_iff.mp hxcent y).symm
      simpa [hxpow, hypow] using hxy.mul_pow p
  inv_mem' := by
    intro x hx
    rcases hx with ⟨hxcent, hxpow⟩
    constructor
    · exact (Subgroup.center (G ⧸ K)).inv_mem hxcent
    · simpa [inv_pow] using congrArg Inv.inv hxpow

def CFSG.theorem_1_13_critical_candidate {G : Type*} [Group G] (K : Subgroup G) [K.Normal]
    {p : ℕ} : Subgroup G :=
  Subgroup.centralizer (K : Set G) ⊓
    Subgroup.comap (QuotientGroup.mk' K) (theorem_1_13_critical_quotient_layer (K := K) (p := p))

theorem CFSG.theorem_1_13_critical_candidate_le_centralizer {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] {p : ℕ} :
    theorem_1_13_critical_candidate (K := K) (p := p) ≤ Subgroup.centralizer (K : Set G) :=
  inf_le_left

theorem CFSG.theorem_1_13_critical_candidate_contains {G : Type*} [Group G] (K : Subgroup G)
    [K.Normal] {p : ℕ} (hKcomm : IsMulCommutative K) :
    K ≤ theorem_1_13_critical_candidate (K := K) (p := p) := by
  intro x hx
  constructor
  · exact (Subgroup.le_centralizer_iff_isMulCommutative (K := K)).2 hKcomm hx
  · change ((QuotientGroup.mk' K) x) ∈ theorem_1_13_critical_quotient_layer (K := K) (p := p)
    have hxq : (QuotientGroup.mk' K) x = 1 := (QuotientGroup.eq_one_iff (N := K) x).2 hx
    constructor
    · simp [hxq]
    · simp [hxq]

theorem CFSG.theorem_1_13_critical_candidate_commutator_le {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] {p : ℕ} :
    ⁅theorem_1_13_critical_candidate (K := K) (p := p), ⊤⁆ ≤ K := by
  refine (Subgroup.commutator_le).2 ?_
  intro x hx g hg
  rw [← QuotientGroup.eq_one_iff (N := K)]
  rcases hx.2 with ⟨hxcent, -⟩
  let qx : G ⧸ K := QuotientGroup.mk' K x
  let qg : G ⧸ K := QuotientGroup.mk' K g
  have hcomm : qx * qg = qg * qx := by
    exact ((Subgroup.mem_center_iff.mp hxcent) qg).symm
  have hquot : qx * qg * (qx⁻¹ * qg⁻¹) = 1 := by
    calc
      qx * qg * (qx⁻¹ * qg⁻¹) = qg * qx * (qx⁻¹ * qg⁻¹) := by rw [hcomm]
      _ = 1 := by simp [mul_assoc]
  simpa [qx, qg, commutatorElement_def, map_mul, map_inv, mul_assoc] using hquot

theorem CFSG.theorem_1_13_critical_candidate_pow_mem {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] {p : ℕ} {x : G}
    (hx : x ∈ theorem_1_13_critical_candidate (K := K) (p := p)) :
    x ^ p ∈ K := by
  rw [← QuotientGroup.eq_one_iff (N := K)]
  change ((QuotientGroup.mk' K) (x ^ p)) = 1
  rcases hx.2 with ⟨-, hxpow⟩
  simpa using hxpow

theorem CFSG.mem_theorem_1_13_critical_candidate_iff {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] {p : ℕ} {x : G} :
    x ∈ theorem_1_13_critical_candidate (K := K) (p := p) ↔
      x ∈ Subgroup.centralizer (K : Set G) ∧ x ^ p ∈ K ∧ ∀ g : G, ⁅x, g⁆ ∈ K := by
  constructor
  · intro hx
    refine ⟨hx.1, theorem_1_13_critical_candidate_pow_mem (K := K) (p := p) hx, ?_⟩
    intro g
    exact theorem_1_13_critical_candidate_commutator_le (K := K) (p := p) <|
      Subgroup.commutator_mem_commutator (H₁ := theorem_1_13_critical_candidate (K := K) (p := p))
        (H₂ := (⊤ : Subgroup G)) hx (show g ∈ (⊤ : Subgroup G) by trivial)
  · rintro ⟨hxcent, hxpow, hcomm⟩
    constructor
    · exact hxcent
    · change ((QuotientGroup.mk' K) x) ∈ theorem_1_13_critical_quotient_layer (K := K) (p := p)
      constructor
      · rw [Subgroup.mem_center_iff]
        intro qg
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N := K) qg
        symm
        rw [← commutatorElement_eq_one_iff_mul_comm]
        have hqcomm : ⁅(QuotientGroup.mk' K) x, (QuotientGroup.mk' K) g⁆ = 1 := by
          have hcommK : (QuotientGroup.mk' K) ⁅x, g⁆ = 1 :=
            (QuotientGroup.eq_one_iff (N := K) ⁅x, g⁆).2 (hcomm g)
          simpa [map_commutatorElement] using hcommK
        exact hqcomm
      · simpa using (QuotientGroup.eq_one_iff (N := K) (x ^ p)).2 hxpow

theorem CFSG.theorem_1_13_critical_candidate_characteristic {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] {p : ℕ} (hKchar : K.Characteristic) :
    (theorem_1_13_critical_candidate (K := K) (p := p)).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ x hx
  rcases hx with ⟨y, hy, rfl⟩
  rcases (mem_theorem_1_13_critical_candidate_iff (K := K) (p := p) (x := y)).1 hy with
    ⟨hycent, hypow, hycomm⟩
  refine (mem_theorem_1_13_critical_candidate_iff (K := K) (p := p) (x := φ y)).2 ?_
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : φ.symm k ∈ K :=
      (Subgroup.characteristic_iff_le_comap.mp hKchar φ.symm) hk
    have hyk : φ.symm k * y = y * φ.symm k := hycent (φ.symm k) hk'
    calc
      k * φ y = φ (φ.symm k * y) := by simp [map_mul]
      _ = φ (y * φ.symm k) := by rw [hyk]
      _ = φ y * k := by simp [map_mul]
  · have hmapK : K.map φ.toMonoidHom ≤ K :=
      (Subgroup.characteristic_iff_map_le.mp hKchar) φ
    have hpowmap : φ (y ^ p) ∈ K.map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom hypow
    exact hmapK <| by
      simpa using hpowmap
  · intro g
    have hmapK : K.map φ.toMonoidHom ≤ K :=
      (Subgroup.characteristic_iff_map_le.mp hKchar) φ
    exact hmapK <| by
      simpa [map_commutatorElement] using
        Subgroup.mem_map_of_mem φ.toMonoidHom (hycomm (φ.symm g))

theorem CFSG.theorem_1_13_critical_candidate_contains_centerIn {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] {p : ℕ} (hKcomm : IsMulCommutative K) :
    K ≤ centerIn (G := G) (theorem_1_13_critical_candidate (K := K) (p := p)) := by
  intro x hx
  refine ⟨theorem_1_13_critical_candidate_contains (K := K) (p := p) hKcomm hx, ?_⟩
  change x ∈
    Subgroup.centralizer (theorem_1_13_critical_candidate (K := K) (p := p) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact
    (Subgroup.mem_centralizer_iff.mp
      (theorem_1_13_critical_candidate_le_centralizer (K := K) (p := p) hy) x hx).symm

theorem CFSG.theorem_1_13_critical_candidate_centerIn_eq {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] {p : ℕ} (hKchar : K.Characteristic) (hKcomm : IsMulCommutative K)
    (hKmax : ∀ B : Subgroup G, B.Characteristic → IsMulCommutative B → K ≤ B → B = K) :
    centerIn (G := G) (theorem_1_13_critical_candidate (K := K) (p := p)) = K := by
  let C : Subgroup G := theorem_1_13_critical_candidate (K := K) (p := p)
  have hCchar : C.Characteristic :=
    theorem_1_13_critical_candidate_characteristic (K := K) (p := p) hKchar
  have hcenter_char : (centerIn (G := G) C).Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ x hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨hyC, hycent⟩
    refine ⟨?_, ?_⟩
    · exact (Subgroup.characteristic_iff_map_le.mp hCchar φ) <|
        Subgroup.mem_map_of_mem φ.toMonoidHom hyC
    · change φ y ∈ Subgroup.centralizer (C : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      have hc' : φ.symm c ∈ C :=
        (Subgroup.characteristic_iff_le_comap.mp hCchar φ.symm) hc
      have hycomm : φ.symm c * y = y * φ.symm c := hycent (φ.symm c) hc'
      calc
        c * φ y = φ (φ.symm c * y) := by simp [map_mul]
        _ = φ (y * φ.symm c) := by rw [hycomm]
        _ = φ y * c := by simp [map_mul]
  have hcenter_comm : IsMulCommutative (centerIn (G := G) C) := by
    refine (Subgroup.le_centralizer_iff_isMulCommutative (K := centerIn (G := G) C)).1 ?_
    have hle₁ : centerIn (G := G) C ≤ C := inf_le_left
    have hle₂ : centerIn (G := G) C ≤ Subgroup.centralizer (C : Set G) := inf_le_right
    exact hle₂.trans
      (Subgroup.centralizer_le (show (centerIn (G := G) C : Set G) ⊆ (C : Set G) from hle₁))
  exact hKmax (centerIn (G := G) C) hcenter_char hcenter_comm <|
    theorem_1_13_critical_candidate_contains_centerIn (K := K) (p := p) hKcomm

theorem CFSG.theorem_1_13_critical_candidate_commutator_le_centerIn {G : Type*} [Group G]
    [Finite G] (K : Subgroup G) [K.Normal] {p : ℕ} (hKchar : K.Characteristic)
    (hKcomm : IsMulCommutative K)
    (hKmax : ∀ B : Subgroup G, B.Characteristic → IsMulCommutative B → K ≤ B → B = K) :
    ⁅theorem_1_13_critical_candidate (K := K) (p := p), ⊤⁆ ≤
      centerIn (G := G) (theorem_1_13_critical_candidate (K := K) (p := p)) := by
  rw [theorem_1_13_critical_candidate_centerIn_eq (K := K) (p := p) hKchar hKcomm hKmax]
  exact theorem_1_13_critical_candidate_commutator_le (K := K) (p := p)

theorem CFSG.theorem_1_13_critical_candidate_pow_mem_centerIn {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] {p : ℕ} {x : G} (hKchar : K.Characteristic)
    (hKcomm : IsMulCommutative K)
    (hKmax : ∀ B : Subgroup G, B.Characteristic → IsMulCommutative B → K ≤ B → B = K)
    (hx : x ∈ theorem_1_13_critical_candidate (K := K) (p := p)) :
    x ^ p ∈ centerIn (G := G) (theorem_1_13_critical_candidate (K := K) (p := p)) := by
  rw [theorem_1_13_critical_candidate_centerIn_eq (K := K) (p := p) hKchar hKcomm hKmax]
  exact theorem_1_13_critical_candidate_pow_mem (K := K) (p := p) hx

theorem CFSG.exists_nontrivial_mem_center_of_normal_p_subgroup {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] (N : Subgroup G) [N.Normal] (hN_ne_bot : N ≠ ⊥) :
    ∃ x : G, x ∈ N ∧ x ∈ Subgroup.center G ∧ x ≠ 1 ∧ x ^ p = 1 := by
  classical
  obtain ⟨M, hMnorm, hMN, hM_ne_bot, hMmin⟩ := exists_minimal_normal_le (G := G) N inferInstance hN_ne_bot
  let : IsMinimalNormal M := {
    minimal := by
      intro K hKnorm hKM
      by_cases hK_bot : K = ⊥
      · exact Or.inl hK_bot
      · exact Or.inr (hMmin K hKnorm hKM hK_bot)
  }
  have hGp : IsPGroup p G := Fact.out
  have : Group.IsNilpotent G := hGp.isNilpotent
  have : Group.IsSolvable G := by infer_instance
  have : Group.IsSolvable M := by infer_instance
  have hM_centerIn :
      M ≤ centerIn (G := G) (fittingSubgroup G) :=
    minimalNormal_solvable_le_centerIn_fittingSubgroup (G := G) M
  have hfit_top : fittingSubgroup G = ⊤ := fitting_eq_top_of_nilpotent (G := G)
  have hM_center' : M ≤ Subgroup.centralizer (Set.univ : Set G) := by
    simpa [centerIn, hfit_top] using hM_centerIn
  have hM_center : M ≤ Subgroup.center G := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_iff.mp (hM_center' hm)) g (by trivial)
  obtain ⟨q, hqprime, hMelem⟩ := minimalNormal_solvable_exists_isElementaryAbelian (M := M)
  let : IsElementaryAbelian q (↥M) := hMelem
  let : Fact (Nat.Prime q) := ⟨hqprime⟩
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hM_ne_bot
  obtain ⟨x, hx_ne⟩ := exists_ne (1 : M)
  have hpowq : x ^ q = 1 :=
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p q (↥M))) x
  have hMp : IsPGroup p M := hGp.to_subgroup M
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf (p := p) (G := M)).1 hMp x
  have horder_eq_q : orderOf x = q := orderOf_eq_prime hpowq hx_ne
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hx_ne
    apply Subtype.ext
    exact orderOf_eq_one_iff.mp (by simpa [hn0] using hn)
  have hpdvdq : p ∣ q := by
    rw [← horder_eq_q, hn]
    exact dvd_pow_self p hn0
  have hq_eq_p : q = p := by
    simpa [eq_comm] using
      (hqprime.dvd_iff_eq (Fact.out : Nat.Prime p).ne_one).1 hpdvdq
  refine ⟨x, hMN x.property, hM_center x.property, ?_, ?_⟩
  · intro hx1
    apply hx_ne
    apply Subtype.ext
    simpa using hx1
  · simpa [hq_eq_p] using congrArg Subtype.val hpowq

theorem CFSG.theorem_1_13_critical_candidate_selfCentralizing {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] (K : Subgroup G) [K.Normal]
    (hKchar : K.Characteristic) (hKcomm : IsMulCommutative K)
    (hKmax : ∀ B : Subgroup G, B.Characteristic → IsMulCommutative B → K ≤ B → B = K) :
    Subgroup.centralizer (theorem_1_13_critical_candidate (K := K) (p := p) : Set G) ≤
      theorem_1_13_critical_candidate (K := K) (p := p) := by
  let C : Subgroup G := theorem_1_13_critical_candidate (K := K) (p := p)
  let D : Subgroup G := Subgroup.centralizer (C : Set G)
  have hK_le_C : K ≤ C :=
    theorem_1_13_critical_candidate_contains (K := K) (p := p) hKcomm
  have hK_le_D : K ≤ D := by
    have hK_le_centerIn : K ≤ centerIn (G := G) C :=
      theorem_1_13_critical_candidate_contains_centerIn (K := K) (p := p) hKcomm
    exact hK_le_centerIn.trans inf_le_right
  have hDchar : D.Characteristic := by
    let : C.Characteristic := by
      dsimp [C]
      exact theorem_1_13_critical_candidate_characteristic (K := K) (p := p) hKchar
    dsimp [D]
    infer_instance
  let : D.Characteristic := hDchar
  by_contra hD_not_le_C
  let q : G →* G ⧸ K := QuotientGroup.mk' K
  let N : Subgroup (G ⧸ K) := D.map q
  have hN_ne_bot : N ≠ ⊥ := by
    intro hN_bot
    have hD_le_K : D ≤ K := by
      intro x hx
      have hxN : q x ∈ N := Subgroup.mem_map_of_mem q hx
      have hxbot : q x ∈ (⊥ : Subgroup (G ⧸ K)) := by
        simpa [N, hN_bot] using hxN
      have hxeq : q x = 1 := by simpa using hxbot
      exact (QuotientGroup.eq_one_iff _).mp hxeq
    exact hD_not_le_C (hD_le_K.trans hK_le_C)
  have hNnorm : N.Normal := by
    dsimp [N]
    infer_instance
  let : N.Normal := hNnorm
  let : Fact (IsPGroup p (G ⧸ K)) := ⟨(Fact.out : IsPGroup p G).to_quotient K⟩
  obtain ⟨xbar, hxbarN, hxbarcent, hxbar_ne, hxbarpow⟩ :=
    exists_nontrivial_mem_center_of_normal_p_subgroup (G := G ⧸ K) (p := p) N hN_ne_bot
  rcases hxbarN with ⟨x, hxD, rfl⟩
  have hxcentK : x ∈ Subgroup.centralizer (K : Set G) := by
    have hD_le_centK :
        D ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.centralizer_le (show (K : Set G) ⊆ (C : Set G) from hK_le_C)
    exact hD_le_centK hxD
  have hxpowK : x ^ p ∈ K := by
    have hxeq : q (x ^ p) = 1 := by simpa using hxbarpow
    exact (QuotientGroup.eq_one_iff _).mp hxeq
  have hxcommK : ∀ g : G, ⁅x, g⁆ ∈ K := by
    intro g
    have hqcomm : ⁅q x, q g⁆ = 1 := by
      apply (commutatorElement_eq_one_iff_mul_comm).2
      exact ((Subgroup.mem_center_iff.mp hxbarcent) (q g)).symm
    have hmapcomm : q ⁅x, g⁆ = 1 := by
      simpa [q, map_commutatorElement] using hqcomm
    exact (QuotientGroup.eq_one_iff _).mp hmapcomm
  have hxC : x ∈ C := by
    dsimp [C]
    exact (mem_theorem_1_13_critical_candidate_iff (K := K) (p := p) (x := x)).2
      ⟨hxcentK, hxpowK, hxcommK⟩
  have hxcenterIn : x ∈ centerIn (G := G) C := by
    refine ⟨hxC, ?_⟩
    simpa [D] using hxD
  have hxK : x ∈ K := by
    rw [← theorem_1_13_critical_candidate_centerIn_eq (K := K) (p := p) hKchar hKcomm hKmax]
    exact hxcenterIn
  have hxbar_one : q x = 1 := (QuotientGroup.eq_one_iff _).mpr hxK
  exact hxbar_ne hxbar_one

theorem CFSG.theorem_1_13_critical_candidate_commutator_le_center {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] (K : Subgroup G) [K.Normal]
    (hKchar : K.Characteristic) (hKcomm : IsMulCommutative K)
    (hKmax : ∀ B : Subgroup G, B.Characteristic → IsMulCommutative B → K ≤ B → B = K) :
    _root_.commutator (theorem_1_13_critical_candidate (K := K) (p := p)) ≤
      Subgroup.center (theorem_1_13_critical_candidate (K := K) (p := p)) := by
  let C : Subgroup G := theorem_1_13_critical_candidate (K := K) (p := p)
  have hcomm_map :
      (_root_.commutator C).map C.subtype ≤ (Subgroup.center C).map C.subtype := by
    rw [C.map_subtype_commutator, ← centerIn_eq_map_center_local]
    exact
      le_trans
        (Subgroup.commutator_mono (show C ≤ C by rfl) (show C ≤ (⊤ : Subgroup G) by exact le_top))
        (theorem_1_13_critical_candidate_commutator_le_centerIn (K := K) (p := p) hKchar hKcomm hKmax)
  intro x hx
  have hxmap : C.subtype x ∈ (_root_.commutator C).map C.subtype :=
    Subgroup.mem_map_of_mem C.subtype hx
  rcases hcomm_map hxmap with ⟨z, hz, hz_eq⟩
  exact C.subtype_injective (by simpa using hz_eq) ▸ hz

theorem CFSG.theorem_1_13_critical_candidate_pow_mem_center {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] [Fact (IsPGroup p G)] (K : Subgroup G) [K.Normal]
    (hKchar : K.Characteristic) (hKcomm : IsMulCommutative K)
    (hKmax : ∀ B : Subgroup G, B.Characteristic → IsMulCommutative B → K ≤ B → B = K)
    (x : theorem_1_13_critical_candidate (K := K) (p := p)) :
    x ^ p ∈ Subgroup.center (theorem_1_13_critical_candidate (K := K) (p := p)) := by
  let C : Subgroup G := theorem_1_13_critical_candidate (K := K) (p := p)
  have hxmap :
      ((x : G) ^ p) ∈ (Subgroup.center C).map C.subtype := by
    rw [← centerIn_eq_map_center_local]
    exact theorem_1_13_critical_candidate_pow_mem_centerIn (K := K) (p := p) hKchar hKcomm hKmax x.2
  rcases hxmap with ⟨z, hz, hz_eq⟩
  have hxpow_eq : x ^ p = z := by
    apply C.subtype_injective
    simpa using hz_eq.symm
  exact hxpow_eq.symm ▸ hz

theorem CFSG.exists_maximal_characteristic_abelian_subgroup {G : Type*} [Group G] [Finite G] :
    ∃ K : Subgroup G,
      K.Characteristic ∧
        IsMulCommutative K ∧
        ∀ B : Subgroup G, B.Characteristic → IsMulCommutative B → K ≤ B → B = K := by
  classical
  let s : Set (Subgroup G) := {K | K.Characteristic ∧ IsMulCommutative K}
  have hsfin : s.Finite := Set.toFinite s
  have hsne : s.Nonempty := by
    refine ⟨⊥, ?_⟩
    constructor <;> infer_instance
  obtain ⟨K, hKmax⟩ := hsfin.exists_maximal hsne
  refine ⟨K, hKmax.1.1, hKmax.1.2, ?_⟩
  intro B hBchar hBcomm hKB
  exact le_antisymm (hKmax.2 ⟨hBchar, hBcomm⟩ hKB) hKB


/-
**Kind**: Theorem
**Note**: Theorem 1.13
**Stmt**:
Let $p$ be an odd prime.
Let $G$ be a non-trivial $p$-group.
Then $G$ admits a characteristic subgroup $H$ with the following properties.
(a) $[H, G] \subset Z(H)$.
(b) $H$ has nilpotence class at most two.
(c) $H$ has exponent $p$.
(d) $C_{Aut(G)}(H)$ is a $p$-group.
-/


public theorem CFSG.theorem_1_13 {G : Type*} [Group G] [Finite G] [Nontrivial G] {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    [Fact (IsPGroup p G)] :
    ∃ H : Subgroup G,
      H.Characteristic ∧
        (⁅H, ⊤⁆ ≤ centerIn (G := G) H) ∧
        NilpotencyClassLe 2 (↥H) ∧
        (Monoid.exponent (↥H) = p) ∧
        IsPGroup p (↥(fixingSubgroup (M := MulAut G) (α := G) (H : Set G))) := by
  classical
  obtain ⟨K, hKchar, hKcomm, hKmax⟩ := exists_maximal_characteristic_abelian_subgroup (G := G)
  let C : Subgroup G := theorem_1_13_critical_candidate (K := K) (p := p)
  have hCchar : C.Characteristic :=
    theorem_1_13_critical_candidate_characteristic (K := K) (p := p) hKchar
  have hCself : Subgroup.centralizer (C : Set G) ≤ C :=
    theorem_1_13_critical_candidate_selfCentralizing (K := K) (p := p) hKchar hKcomm hKmax
  let H : Subgroup G := {
    carrier := {x : G | x ∈ C ∧ x ^ p = 1}
    one_mem' := by simp
    mul_mem' := by
      intro x y hx hy
      rcases hx with ⟨hxC, hxpow⟩
      rcases hy with ⟨hyC, hypow⟩
      constructor
      · exact C.mul_mem hxC hyC
      · let xC : C := ⟨x, hxC⟩
        let yC : C := ⟨y, hyC⟩
        have hxpowC : xC ^ p = 1 := by
          apply Subtype.ext
          simpa using hxpow
        have hypowC : yC ^ p = 1 := by
          apply Subtype.ext
          simpa using hypow
        have hxy :=
          classTwo_pthPower_hom (G := ↥C) (p := p) hpodd
            (theorem_1_13_critical_candidate_commutator_le_center (K := K) (p := p)
              hKchar hKcomm hKmax)
            (theorem_1_13_critical_candidate_pow_mem_center (K := K) (p := p)
              hKchar hKcomm hKmax) xC yC
        simpa [xC, yC, hxpowC, hypowC] using congrArg Subtype.val hxy
    inv_mem' := by
      intro x hx
      rcases hx with ⟨hxC, hxpow⟩
      constructor
      · exact C.inv_mem hxC
      · simpa [inv_pow] using congrArg Inv.inv hxpow
  }
  have hHchar : H.Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ x hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨hyC, hypow⟩
    constructor
    · exact (Subgroup.characteristic_iff_map_le.mp hCchar φ) <|
        Subgroup.mem_map_of_mem φ.toMonoidHom hyC
    · simpa using congrArg φ.toMonoidHom hypow
  have hK_le_C : K ≤ C :=
    theorem_1_13_critical_candidate_contains (K := K) (p := p) hKcomm
  have hK_le_centerIn_C : K ≤ centerIn (G := G) C :=
    theorem_1_13_critical_candidate_contains_centerIn (K := K) (p := p) hKcomm
  have hHcomm : ⁅H, ⊤⁆ ≤ centerIn (G := G) H := by
    refine (Subgroup.commutator_le).2 ?_
    intro h hh g hg
    rcases hh with ⟨hhC, hhpow⟩
    have hcommK : ⁅h, g⁆ ∈ K :=
      theorem_1_13_critical_candidate_commutator_le (K := K) (p := p) <|
        Subgroup.commutator_mem_commutator (H₁ := C) (H₂ := (⊤ : Subgroup G)) hhC
          (show g ∈ (⊤ : Subgroup G) by trivial)
    have hhcentK : h ∈ Subgroup.centralizer (K : Set G) :=
      theorem_1_13_critical_candidate_le_centralizer (K := K) (p := p) hhC
    have hcommute : Commute ⁅h, g⁆ h := by
      exact (Subgroup.mem_centralizer_iff.mp hhcentK) _ hcommK
    have hcomm_pow : ⁅h, g⁆ ^ p = 1 :=
      commutator_pow_eq_one_of_pow_eq_one_of_commute hcommute hhpow
    have hcomm_mem_H : ⁅h, g⁆ ∈ H := by
      exact ⟨hK_le_C hcommK, hcomm_pow⟩
    refine ⟨hcomm_mem_H, ?_⟩
    have hcomm_centC : ⁅h, g⁆ ∈ Subgroup.centralizer (C : Set G) :=
      (hK_le_centerIn_C hcommK).2
    exact show ⁅h, g⁆ ∈ Subgroup.centralizer (H : Set G) from by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp hcomm_centC) y hy.1
  have hGcard : ∃ n : ℕ, Nat.card G = p ^ n :=
    (IsPGroup.iff_card (p := p) (G := G)).1 (Fact.out : IsPGroup p G)
  have hHnil : NilpotencyClassLe 2 (↥H) :=
    nilpotencyClassLe_two_of_commutator_le_centerIn H hHcomm
  have htop_ne_bot : (⊤ : Subgroup G) ≠ ⊥ := top_ne_bot
  obtain ⟨z, -, hzcent, hz_ne, hzpow⟩ :=
    exists_nontrivial_mem_center_of_normal_p_subgroup (G := G) (p := p) (⊤ : Subgroup G) htop_ne_bot
  have hzC : z ∈ C := by
    refine (mem_theorem_1_13_critical_candidate_iff (K := K) (p := p) (x := z)).2 ?_
    refine ⟨?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (Subgroup.mem_center_iff.mp hzcent) k
    · simp [hzpow]
    · intro g
      have hzg : z * g = g * z := ((Subgroup.mem_center_iff.mp hzcent) g).symm
      have hcomm_eq : ⁅z, g⁆ = 1 := (commutatorElement_eq_one_iff_mul_comm).2 hzg
      simp [hcomm_eq]
  have hC_ne_bot : C ≠ ⊥ := by
    intro hC_bot
    have hzbot : z ∈ (⊥ : Subgroup G) := by simpa [hC_bot] using hzC
    exact hz_ne (by simpa using hzbot)
  have hCp : IsPGroup p (↥C) := (Fact.out : IsPGroup p G).to_subgroup C
  let : Fact (IsPGroup p (↥C)) := ⟨hCp⟩
  let : Nontrivial (↥C) := C.nontrivial_iff_ne_bot.mpr hC_ne_bot
  obtain ⟨n, hnpos, hcardC⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p) (G := ↥C) (hG := hCp)).mp inferInstance
  have hp_dvd_cardC : p ∣ Nat.card (↥C) := by
    rw [hcardC]
    exact dvd_pow_self p (ne_of_gt hnpos)
  have hOmega_le_H : (omega₁ (G := ↥C) (p := p)).map C.subtype ≤ H := by
    rw [omega₁, omega, MonoidHom.map_closure]
    refine (Subgroup.closure_le (K := H)).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x.2, by simpa [pow_one] using congrArg C.subtype hx⟩
  have hOmega_ne_bot :
      (omega₁ (G := ↥C) (p := p)).map C.subtype ≠ ⊥ :=
    omega₁_map_subtype_ne_bot (M := C) (p := p) hp_dvd_cardC
  have hH_ne_bot : H ≠ ⊥ := by
    intro hH_bot
    exact hOmega_ne_bot (le_bot_iff.mp (by simpa [hH_bot] using hOmega_le_H))
  have hHexponent : Monoid.exponent (↥H) = p := by
    let : Nontrivial (↥H) := H.nontrivial_iff_ne_bot.mpr hH_ne_bot
    refine (Monoid.exponent_eq_prime_iff (G := ↥H) (p := p) Fact.out).2 ?_
    intro x hx
    have hxpow : x ^ p = 1 := by
      apply Subtype.ext
      exact x.property.2
    exact orderOf_eq_prime hxpow hx
  let Afix : Subgroup (MulAut G) := fixingSubgroup (M := MulAut G) (α := G) (H : Set G)
  have hfixA : ∀ a : Afix, ∀ x : G, x ∈ H → a • x = x := by
    intro a x hx
    exact (mem_fixingSubgroup_iff (M := MulAut G) (s := (H : Set G))).1 a.2 x hx
  have hAfix_pgroup : IsPGroup p (↥Afix) := by
    refine (IsPGroup.iff_card (p := p) (G := ↥Afix)).2 ?_
    have hApos : Nat.card (↥Afix) ≠ 0 := Nat.card_pos.ne'
    refine ⟨(Nat.card (↥Afix)).primeFactorsList.length, ?_⟩
    rw [← List.prod_replicate, ← List.eq_replicate_of_mem, Nat.prod_primeFactorsList hApos]
    intro q hq
    obtain ⟨hqprime, hqdvd⟩ := (Nat.mem_primeFactorsList hApos).mp hq
    have : Fact q.Prime := ⟨hqprime⟩
    obtain ⟨a, haord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Afix) q hqdvd
    by_cases hqp : q = p
    · exact hqp
    · let B : Subgroup Afix := Subgroup.zpowers a
      have hBcard : Nat.card (↥B) = q := by
        simp [B, haord]
      have hqcop : Nat.Coprime q (Nat.card G) := by
        rcases hGcard with ⟨nG, hcardG⟩
        have hqp_coprime : Nat.Coprime q p := by
          exact hqprime.coprime_iff_not_dvd.mpr fun hqd => hqp <|
            (((Fact.out : Nat.Prime p).dvd_iff_eq hqprime.ne_one).1 hqd).symm
        simpa [hcardG] using hqp_coprime.pow_right nG
      have hBcop : Nat.Coprime (Nat.card (↥B)) (Nat.card G) := by
        simpa [hBcard] using hqcop
      have hBinv : IsInvariant B G C :=
        isInvariant_of_characteristic (A := B) (G := G) C
      let : IsInvariant B G C := hBinv
      have hΩB : ActsTriviallyOnSubgroup (A := B) (G := ↥C) (omega₁ (G := ↥C) (p := p)) := by
        intro b x hx
        apply Subtype.ext
        exact hfixA (b : Afix) (x : G) (hOmega_le_H (Subgroup.mem_map_of_mem C.subtype hx))
      have hBcopC : Nat.Coprime (Nat.card (↥B)) (Nat.card (↥C)) :=
        hBcop.of_dvd_right (Subgroup.card_subgroup_dvd_card C)
      have htrivC : ActsTrivially (A := B) (G := ↥C) :=
        theorem_1_11_direct (G := ↥C) (A := B) hpodd hBcopC hΩB
      have hBfaith : FaithfulSMul B C :=
        faithful_on_selfCentralizing_of_coprime (G := G) (A := B) (C := C) hCself hBcop
      let aB : B := ⟨a, Subgroup.mem_zpowers a⟩
      have haB_eq_one : aB = 1 :=
        (faithfulSMul_iff (G := B) (α := C)).1 hBfaith aB (htrivC aB)
      have ha_eq_one : a = 1 := by
        simpa [aB] using congrArg Subtype.val haB_eq_one
      have ha_ne_one : a ≠ 1 := by
        intro ha1
        exact hqprime.ne_one
          (haord.symm.trans <| by simp [ha1])
      exact (ha_ne_one ha_eq_one).elim
  exact ⟨H, hHchar, hHcomm, hHnil, hHexponent, hAfix_pgroup⟩


end
