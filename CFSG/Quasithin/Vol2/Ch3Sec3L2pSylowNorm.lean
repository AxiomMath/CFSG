module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S7b
public import CFSG.Walter.ReeOrder.JT.Section2

public section

namespace CFSG.Quasithin.H13

open scoped MatrixGroups

namespace L2pNorm

open DihedralGroup in
theorem eq_of_r_sq {k : ℕ} [NeZero k] {i : ZMod (2 * k)}
    (h1 : (r i : DihedralGroup (2 * k)) ≠ 1) (h2 : r i * r i = (1 : DihedralGroup (2 * k))) :
    i = k := by
  rw [r_mul_r, one_def, r.injEq, ← two_mul] at h2
  rcases (CFSG.GroupTheory.two_mul_eq_zero_iff_zmod i).mp h2 with h | h
  · exact absurd (by rw [h, ← one_def]) h1
  · exact h

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]

theorem centralizer_sylow_le (hK : Nat.card K = p) (hp : Odd p) (h5 : 5 ≤ p)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (P : Sylow 2 PSL(2, K)) :
    Subgroup.centralizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K)) ≤ P := by
  classical
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  have h8' : p ^ 1 % 8 = 3 ∨ p ^ 1 % 8 = 5 := by rw [pow_one]; exact h8
  set V : Subgroup PSL(2, K) := (P : Subgroup PSL(2, K)) with hVdef
  have hV : IsKleinFour V := CFSG.Walter.psl2_sylow_two_isKleinFour K hK1 hp one_pos h8' P
  have hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hV.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ V, x * x = 1 := fun x hx => by
    have h1 := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : ↥V)
    rw [hV.exponent_two, sq] at h1
    exact congrArg Subtype.val h1
  have hVC : V ≤ Subgroup.centralizer (V : Set PSL(2, K)) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
  obtain ⟨u, v, hu1, hv1, huv, huV, hvV⟩ :
      ∃ u v : PSL(2, K), u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u ∈ V ∧ v ∈ V := by
    have : Fintype ↥V := Fintype.ofFinite _
    have h2 : 2 < Fintype.card ↥V := by
      rw [← Nat.card_eq_fintype_card, hV.card_four]
      norm_num
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
    have hne : ∀ x y : ↥V, x ≠ y → (x : PSL(2, K)) ≠ y := fun x y h h' => h (Subtype.ext h')
    by_cases ha : (a : PSL(2, K)) = 1
    · refine ⟨b, c, fun hb => hab (Subtype.ext (ha.trans hb.symm)),
        fun hc => hac (Subtype.ext (ha.trans hc.symm)), hne b c hbc, b.2, c.2⟩
    · by_cases hb : (b : PSL(2, K)) = 1
      · exact ⟨a, c, ha, fun hc => hbc (Subtype.ext (hb.trans hc.symm)), hne a c hac, a.2, c.2⟩
      · exact ⟨a, b, ha, hb, hne a b hab, a.2, b.2⟩
  suffices hle : Nat.card (Subgroup.centralizer (V : Set PSL(2, K))) ≤ 4 by
    have := Subgroup.eq_of_le_of_card_ge hVC (by rw [hV.card_four]; exact hle)
    exact this.ge
  have huord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hsq u huV) hu1
  have hCu : Subgroup.centralizer (V : Set PSL(2, K)) ≤
      Subgroup.centralizer ({u} : Set PSL(2, K)) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huV)
  rcases (by omega : p = 5 ∨ 7 ≤ p) with rfl | h7
  ·
    have hC := ((CFSG.Walter.psl2_centralizer_involution K hK1 hp one_pos huord).1
      (by norm_num)).1
    calc Nat.card (Subgroup.centralizer (V : Set PSL(2, K)))
        ≤ Nat.card (Subgroup.centralizer ({u} : Set PSL(2, K))) := Subgroup.card_le_of_le hCu
      _ = 4 := by rw [hC]; norm_num
  ·
    obtain ⟨n, hn4, ⟨k, rfl⟩, -, ⟨eC⟩⟩ := CFSG.Walter.psl2_centralizer_involution_dihedral K
      hK1 hp one_pos (by rw [pow_one]; exact h7) huord
    rw [← two_mul] at eC
    have : NeZero k := ⟨by omega⟩
    set C := Subgroup.centralizer ({u} : Set PSL(2, K)) with hCdef
    have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
    have hvC : v ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr (hcomm v hvV u huV)
    have hinj : ∀ (x y : PSL(2, K)) (hx : x ∈ C) (hy : y ∈ C), x ≠ y →
        eC ⟨x, hx⟩ ≠ eC ⟨y, hy⟩ := fun x y hx hy hxy h =>
      hxy (congrArg Subtype.val (eC.injective h))
    have hsqC : ∀ (x : PSL(2, K)) (hx : x ∈ C), x ∈ V → eC ⟨x, hx⟩ * eC ⟨x, hx⟩ = 1 :=
      fun x hx hxV => by
        rw [← map_mul, ← map_one eC]
        exact congrArg eC (Subtype.ext (hsq x hxV))
    have h1C : ∀ (x : PSL(2, K)) (hx : x ∈ C), x ≠ 1 → eC ⟨x, hx⟩ ≠ 1 := fun x hx hx1 h =>
      hx1 (congrArg Subtype.val (eC.injective (h.trans (map_one eC).symm)))
    obtain ⟨x, hxV, hxC, j, hj⟩ :
        ∃ x ∈ V, ∃ hxC : x ∈ C, ∃ j, eC ⟨x, hxC⟩ = DihedralGroup.sr j := by
      rcases hEu : eC ⟨u, huC⟩ with i | j
      · rcases hEv : eC ⟨v, hvC⟩ with i' | j'
        · exfalso
          have hi := eq_of_r_sq (hEu ▸ h1C u huC hu1) (hEu ▸ hsqC u huC huV)
          have hi' := eq_of_r_sq (hEv ▸ h1C v hvC hv1) (hEv ▸ hsqC v hvC hvV)
          apply hinj u v huC hvC huv
          rw [hEu, hEv, hi, hi']
        · exact ⟨v, hvV, hvC, j', hEv⟩
      · exact ⟨u, huV, huC, j, hEu⟩
    have key : Nat.card (Subgroup.centralizer (V : Set PSL(2, K))) ≤
        Nat.card (Subgroup.centralizer ({DihedralGroup.sr j} : Set (DihedralGroup (2 * k)))) := by
      refine Nat.card_le_card_of_injective
        (fun y => ⟨eC ⟨y.1, hCu y.2⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩) ?_
      · rw [← hj, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp y.2 x hxV).symm
      · intro y₁ y₂ h
        have h' := congrArg Subtype.val h
        exact Subtype.ext (congrArg Subtype.val (eC.injective h') :)
    exact key.trans (CFSG.GorensteinWalter.card_centralizer_reflection_dihedral_even_le_four j)


theorem card_normalizer_sylow (hK : Nat.card K = p) (hp : Odd p) (h5 : 5 ≤ p)
    (h8 : p % 8 = 3 ∨ p % 8 = 5) (P : Sylow 2 PSL(2, K)) :
    Nat.card (Subgroup.normalizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K))) = 12 := by
  classical
  have hK1 : Nat.card K = p ^ 1 := by rw [pow_one]; exact hK
  have h8' : p ^ 1 % 8 = 3 ∨ p ^ 1 % 8 = 5 := by rw [pow_one]; exact h8
  have hK' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, Fact.out, hp, le_rfl, hK1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup PSL(2, K) := (P : Subgroup PSL(2, K)) with hVdef
  have hV : IsKleinFour V := CFSG.Walter.psl2_sylow_two_isKleinFour K hK1 hp one_pos h8' P
  set N₀ := Subgroup.normalizer (V : Set PSL(2, K)) with hN₀
  have hVN₀ : V ≤ N₀ := Subgroup.le_normalizer
  have hCV : Subgroup.centralizer (V : Set PSL(2, K)) = V := by
    refine le_antisymm (centralizer_sylow_le hK hp h5 h8 P) fun x hx => ?_
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact congrArg Subtype.val (hV.isMulCommutative.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  let := CFSG.Walter.JT.conjAct N₀ V le_rfl
  let φ : N₀ →* MulAut V := MulDistribMulAction.toMulAut N₀ V
  have hker : φ.ker = V.subgroupOf N₀ := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      have hnC : (n : PSL(2, K)) ∈ Subgroup.centralizer (V : Set PSL(2, K)) := by
        refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
        have := congrArg Subtype.val (DFunLike.congr_fun hn ⟨v, hv⟩)
        change (n : PSL(2, K)) * v * (n : PSL(2, K))⁻¹ = v at this
        calc v * n = ((n : PSL(2, K)) * v * (n : PSL(2, K))⁻¹) * n := by rw [this]
          _ = n * v := by group
      rw [hCV] at hnC
      exact hnC
    · intro hn
      ext v
      change (n : PSL(2, K)) * v * (n : PSL(2, K))⁻¹ = v
      have := hV.isMulCommutative.is_comm.comm ⟨(n : PSL(2, K)), hn⟩ v
      have := congrArg Subtype.val this
      change (n : PSL(2, K)) * v = v * n at this
      rw [this, mul_inv_cancel_right]
  have hcard : Nat.card N₀ = 4 * Nat.card φ.range := by
    have h1 := φ.ker.card_mul_index
    rw [Subgroup.index_ker, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVN₀).toEquiv,
      hV.card_four] at h1
    exact h1.symm
  have hdvd6 : Nat.card φ.range ∣ 6 := by
    rw [← CFSG.Walter.JT.PSL2Facts.card_mulAut_of_isKleinFour V]
    exact Subgroup.card_subgroup_dvd_card _
  have hodd : ¬ 2 ∣ Nat.card φ.range := by
    rintro ⟨c, hc⟩
    obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime (G := N₀) 2 (n := 3)
      (by rw [hcard, hc]; exact ⟨c, by ring⟩)
    have hW2 : IsPGroup 2 (W.map N₀.subtype) := (IsPGroup.of_card hW).map N₀.subtype
    obtain ⟨Q, hQ⟩ := hW2.exists_le_sylow
    have h4 := CFSG.Walter.psl2_sylow_two_card_eq_four K hK1 hp one_pos h8' Q
    have hdvd := Subgroup.card_dvd_of_le hQ
    rw [h4, Subgroup.card_map_of_injective N₀.subtype_injective, hW] at hdvd
    norm_num at hdvd
  have hne1 : Nat.card φ.range ≠ 1 := by
    intro h1
    rw [h1] at hcard
    have hN₀V : N₀ = V := (Subgroup.eq_of_le_of_card_ge hVN₀ (by rw [hcard, hV.card_four])).symm
    have hsimple : IsSimpleGroup PSL(2, K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [hK]; omega)
    have hNC : Subgroup.normalizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K)) ≤
        Subgroup.centralizer ((P : Subgroup PSL(2, K)) : Set PSL(2, K)) := by
      intro n hn
      have hnV : n ∈ V := by
        have hn' : n ∈ N₀ := hn
        rw [hN₀V] at hn'
        exact hn'
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact congrArg Subtype.val (hV.isMulCommutative.is_comm.comm ⟨m, hm⟩ ⟨n, hnV⟩)
    have hcomp := MonoidHom.ker_transferSylow_isComplement' P hNC
    have hXbig : 4 < Nat.card PSL(2, K) := by
      rw [CFSG.GorensteinWalter.psl2_card_formula K hK', hK]
      have : 5 * (5 ^ 2 - 1) ≤ p * (p ^ 2 - 1) :=
        Nat.mul_le_mul h5 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h5 2) 1)
      omega
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.transferSylow P hNC).ker with
      hb | ht
    · have := hcomp.card_mul_card
      rw [hb, Subgroup.card_bot, one_mul, ← hVdef, hV.card_four] at this
      omega
    · have := hcomp.card_mul_card
      rw [ht, Subgroup.card_top, ← hVdef, hV.card_four] at this
      have hpos : 0 < Nat.card PSL(2, K) := Nat.card_pos
      omega
  have h3 : Nat.card φ.range = 3 := by
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    have hle : Nat.card φ.range ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd6
    interval_cases h : Nat.card φ.range <;> simp_all
  rw [hcard, h3]

end L2pNorm

theorem factL2pSylowNorm_holds : FactL2pSylowNorm := by
  intro p hp hp3 h8 Q _ _ hQ S hS
  obtain ⟨⟨-, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hQ
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK1 : Nat.card K = p := by simpa using hK
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  let e' : Q ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  set S' : Subgroup PSL(2, K) := S.map e'.toMonoidHom with hS'
  have hS'2 : IsPGroup 2 S' := hS.2.1.map _
  have hS'i : ¬ 2 ∣ S'.index := by
    have h1 : S'.index = S.index := Subgroup.index_map_equiv S e'
    rw [h1]
    intro h2
    apply hS.2.2
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact h2
  have hN := L2pNorm.card_normalizer_sylow hK1 hodd (by omega) h8 (hS'2.toSylow hS'i)
  rw [IsPGroup.toSylow_coe, hS', ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective e'.injective] at hN
  exact hN

end CFSG.Quasithin.H13
