module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptA312Gen0
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.InspA312

abbrev SL2 (p : ℕ) : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod p)

theorem two_ne_zero_zmod (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')

theorem sl2_diag {p : ℕ} [Fact p.Prime] (x : SL2 p) (hb : x.1 0 1 = 0) (hc : x.1 1 0 = 0)
    (hd : x.1 1 1 = x.1 0 0) : x = 1 ∨ x = -1 := by
  have hdet : x.1 0 0 * x.1 1 1 - x.1 0 1 * x.1 1 0 = 1 := by
    have := x.2
    rwa [Matrix.det_fin_two] at this
  rw [hb, hc, hd] at hdet
  have hsq : (x.1 0 0 - 1) * (x.1 0 0 + 1) = 0 := by linear_combination hdet
  rcases mul_eq_zero.mp hsq with h | h
  · left
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd, Matrix.one_apply] <;>
      linear_combination h
  · right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, hd, Matrix.one_apply, Matrix.neg_apply] <;>
      linear_combination h

theorem sl2_involution_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x : SL2 p) (hx : x * x = 1) :
    x = 1 ∨ x = -1 := by
  have h2 := two_ne_zero_zmod p hp2
  have hM : x.1 * x.1 = 1 := by
    have := congrArg Subtype.val hx
    rwa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at this
  have hdet : x.1 0 0 * x.1 1 1 - x.1 0 1 * x.1 1 0 = 1 := by
    have := x.2
    rwa [Matrix.det_fin_two] at this
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] at e00 e01 e10
  by_cases hs : x.1 0 0 + x.1 1 1 = 0
  · exfalso
    have hd : x.1 1 1 = -x.1 0 0 := by linear_combination hs
    rw [hd] at hdet
    have h2' : (2 : ZMod p) = 0 := by linear_combination -hdet - e00
    exact h2 h2'
  · have hb : x.1 0 1 = 0 := by
      have : x.1 0 1 * (x.1 0 0 + x.1 1 1) = 0 := by linear_combination e01
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : x.1 1 0 = 0 := by
      have : x.1 1 0 * (x.1 0 0 + x.1 1 1) = 0 := by linear_combination e10
      exact (mul_eq_zero.mp this).resolve_right hs
    have ha2 : x.1 0 0 * x.1 0 0 = 1 := by
      rw [hb, hc] at e00
      linear_combination e00
    have had : x.1 0 0 * x.1 1 1 = 1 := by
      rw [hb, hc] at hdet
      linear_combination hdet
    have hd : x.1 1 1 = x.1 0 0 := by
      linear_combination (x.1 0 0) * had - (x.1 1 1) * ha2
    exact sl2_diag x hb hc hd

theorem sl2_not_comm (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ a b : SL2 p, a * b ≠ b * a := by
  let u : SL2 p := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let l : SL2 p := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  refine ⟨u, l, fun h => ?_⟩
  have h00 := congrArg (fun x : SL2 p => x.1 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h00
  have hu : u.1 = !![1, 1; 0, 1] := rfl
  have hl : l.1 = !![1, 0; 1, 1] := rfl
  rw [hu, hl] at h00
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem sl2_central_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (x : SL2 p)
    (hx : x ∈ Subgroup.center (SL2 p)) : x = 1 ∨ x = -1 := by
  rw [Subgroup.mem_center_iff] at hx
  let u : SL2 p := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  let l : SL2 p := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
  have hu := congrArg Subtype.val (hx u)
  have hl := congrArg Subtype.val (hx l)
  simp only [Matrix.SpecialLinearGroup.coe_mul] at hu hl
  have hc : x.1 1 0 = 0 := by
    have := congrFun (congrFun hu 0) 0
    simp [u, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hd : x.1 1 1 = x.1 0 0 := by
    have := congrFun (congrFun hu 0) 1
    simp [u, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hb : x.1 0 1 = 0 := by
    have := congrFun (congrFun hl 0) 0
    simp [l, Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  exact sl2_diag x hb hc hd

theorem neg_one_mem_center_sl2 (p : ℕ) [Fact p.Prime] : (-1 : SL2 p) ∈ Subgroup.center (SL2 p) := by
  rw [Subgroup.mem_center_iff]
  intro g
  simp

theorem neg_one_ne_one_sl2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : (-1 : SL2 p) ≠ 1 := by
  intro h
  have h00 := congrArg (fun x : SL2 p => x.1 0 0) h
  simp at h00
  exact two_ne_zero_zmod p hp2 (by linear_combination -h00)

theorem card_center_sl2 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Nat.card (Subgroup.center (SL2 p)) = 2 := by
  have hZ : Subgroup.center (SL2 p) = Subgroup.zpowers (-1) := by
    apply le_antisymm
    · intro x hx
      rcases sl2_central_eq p hp2 x hx with h | h
      · rw [h]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le]
      exact neg_one_mem_center_sl2 p
  rw [hZ, Nat.card_zpowers]
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · simp
  · exact neg_one_ne_one_sl2 p hp2

theorem center_map_equiv {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ∀ g, g * x = x * g := Subgroup.mem_center_iff.mp hx
    refine Subgroup.mem_center_iff.mpr (fun h => ?_)
    obtain ⟨g, rfl⟩ := e.surjective h
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hx' g]
  · intro hy
    have hy' : ∀ h, h * y = y * h := Subgroup.mem_center_iff.mp hy
    refine ⟨e.symm y, Subgroup.mem_center_iff.mpr (fun g => ?_), by simp⟩
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact hy' (e g)

theorem simple_sl2_mod_center (p : ℕ) [Fact p.Prime] (hp4 : 4 ≤ p) :
    IsSimpleGroup (SL2 p ⧸ Subgroup.center (SL2 p)) := by
  have hcard : 4 ≤ Nat.card (ZMod p) := by
    rw [Nat.card_zmod]
    omega
  exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard


theorem sl2_O2_card {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q} (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (hp4 : 4 ≤ p) (e : ↥B ≃* SL2 p)
    (hS : IsSimpleGroup (↥B ⧸ CFSG.pCore 2 ↥B)) (hN : 1 < Nat.card (↥B ⧸ CFSG.pCore 2 ↥B)) :
    Nat.card (CFSG.pCore 2 ↥B) = 2 := by
  have hcne : e.symm (-1) ≠ 1 := by
    intro h
    apply neg_one_ne_one_sl2 p hp2
    have := congrArg e h
    simpa using this
  have hcZ : e.symm (-1) ∈ Subgroup.center ↥B := by
    refine Subgroup.mem_center_iff.mpr (fun g => ?_)
    apply e.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_center_iff.mp (neg_one_mem_center_sl2 p) (e g)
  have hO_ne : CFSG.pCore 2 ↥B ≠ ⊥ := by
    intro hO0
    have hG : IsSimpleGroup ↥B := by
      have e' : (↥B ⧸ CFSG.pCore 2 ↥B) ≃* ↥B :=
        (QuotientGroup.quotientMulEquivOfEq hO0).trans QuotientGroup.quotientBot
      exact (MulEquiv.isSimpleGroup_congr e').mp hS
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥B) with h | h
    · apply hcne
      have hmem : e.symm (-1) ∈ Subgroup.center ↥B := hcZ
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · obtain ⟨a, b, hab⟩ := sl2_not_comm p hp2
      apply hab
      have hxc : e.symm a ∈ Subgroup.center ↥B := by
        rw [h]
        exact Subgroup.mem_top _
      have hc' := (Subgroup.mem_center_iff.mp hxc (e.symm b)).symm
      have := congrArg e hc'
      simpa using this
  obtain ⟨k, hk⟩ := pCore_card_two_pow B
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact hO_ne (Subgroup.eq_bot_of_card_eq _ hk)
  have h2dvd : 2 ∣ Nat.card (CFSG.pCore 2 ↥B) := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥(CFSG.pCore 2 ↥B)) 2 h2dvd
  have hy2 : y ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simp [hyord])
  have hyne : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hyord
    exact absurd hyord (by norm_num)
  have hy2' : (y : ↥B) * (y : ↥B) = 1 := by
    have := congrArg Subtype.val hy2
    simpa [sq] using this
  have hyne' : (y : ↥B) ≠ 1 := fun h => hyne (Subtype.ext h)
  have hinv : e (y : ↥B) * e (y : ↥B) = 1 := by
    rw [← map_mul, hy2', map_one]
  have hcases := sl2_involution_eq p hp2 (e (y : ↥B)) hinv
  have hey : e (y : ↥B) = -1 := by
    rcases hcases with h | h
    · exfalso
      apply hyne'
      apply e.injective
      rw [h, map_one]
    · exact h
  have hcO : e.symm (-1) ∈ CFSG.pCore 2 ↥B := by
    have : (y : ↥B) = e.symm (-1) := by
      rw [← hey, MulEquiv.symm_apply_apply]
    rw [← this]
    exact y.2
  have hZO : Subgroup.center ↥B ≤ CFSG.pCore 2 ↥B := by
    intro z hz
    have hz' : e z ∈ Subgroup.center (SL2 p) := by
      rw [← center_map_equiv e]
      exact Subgroup.mem_map_of_mem _ hz
    rcases sl2_central_eq p hp2 (e z) hz' with h | h
    · have : z = 1 := e.injective (by rw [h, map_one])
      rw [this]
      exact Subgroup.one_mem _
    · have : z = e.symm (-1) := by
        rw [← h, MulEquiv.symm_apply_apply]
      rw [this]
      exact hcO
  have hPSL : IsSimpleGroup (↥B ⧸ Subgroup.center ↥B) := by
    have e' : (↥B ⧸ Subgroup.center ↥B) ≃* (SL2 p ⧸ Subgroup.center (SL2 p)) :=
      QuotientGroup.congr (Subgroup.center ↥B) (Subgroup.center (SL2 p)) e (center_map_equiv e)
    exact (MulEquiv.isSimpleGroup_congr e').mpr (simple_sl2_mod_center p hp4)
  have hOZ : CFSG.pCore 2 ↥B ≤ Subgroup.center ↥B := by
    let φ : ↥B →* ↥B ⧸ Subgroup.center ↥B := QuotientGroup.mk' _
    have hφ : Function.Surjective φ := QuotientGroup.mk'_surjective _
    have hNn : ((CFSG.pCore 2 ↥B).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥B).map φ) with h | h
    · intro x hx
      have hmem : φ x ∈ (CFSG.pCore 2 ↥B).map φ := Subgroup.mem_map_of_mem φ hx
      rw [h, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).mp hmem
    · exfalso
      have htop : CFSG.pCore 2 ↥B = ⊤ := by
        apply le_antisymm le_top
        intro g _
        have hg : φ g ∈ (CFSG.pCore 2 ↥B).map φ := by
          rw [h]
          exact Subgroup.mem_top _
        obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.mp hg
        have hgo : o⁻¹ * g ∈ Subgroup.center ↥B := by
          have h1 : g⁻¹ * o ∈ Subgroup.center ↥B := (QuotientGroup.eq (s := Subgroup.center ↥B)).mp hoe.symm
          have h2 := (Subgroup.center ↥B).inv_mem h1
          simpa using h2
        have : g = o * (o⁻¹ * g) := by group
        rw [this]
        exact (CFSG.pCore 2 ↥B).mul_mem ho (hZO hgo)
      have hidx : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = 1 := by
        show Subgroup.index (CFSG.pCore 2 ↥B) = 1
        rw [htop, Subgroup.index_top]
      omega
  have hEq : CFSG.pCore 2 ↥B = Subgroup.center ↥B := le_antisymm hOZ hZO
  rw [hEq, Nat.card_congr (Subgroup.centerCongr e).toEquiv, card_center_sl2 p hp2]

theorem sl2_quot_eq {Q : Type} [Group Q] [Finite Q] {B : Subgroup Q} {p q : ℕ} [Fact p.Prime]
    (hp4 : 4 ≤ p) (hp2 : p ≠ 2) (hB : IsSL2 p ↥B) (hq : IsPSL 2 q 1 (↥B ⧸ CFSG.pCore 2 ↥B))
    (hqp : q.Prime) (hq2 : q % 2 = 1) : p = q := by
  obtain ⟨e⟩ := hB
  have hsimp := isSimpleGroup_of_isPSL hq
  have hN : 1 < Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) := Finite.one_lt_card
  have hO := sl2_O2_card p hp2 hp4 e hsimp hN
  have hBc : Nat.card ↥B = p * (p ^ 2 - 1) := card_sl2 (Fact.out) ⟨e⟩
  have hQc : Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) = q * (q ^ 2 - 1) / 2 := card_psl2_odd hq hq2
  have hmul := card_eq_quot_mul B
  rw [hO, hQc, hBc] at hmul
  have hq2d : 2 ∣ q * (q ^ 2 - 1) := by
    have hsq : q ^ 2 % 2 = 1 := by rw [Nat.pow_mod, hq2]
    exact Dvd.dvd.mul_left (by omega) q
  have hfin : p * (p ^ 2 - 1) = q * (q ^ 2 - 1) := by
    rw [hmul, Nat.div_mul_cancel hq2d]
  exact eq_of_mul_sq_sub_one_eq (by have := (Fact.out : p.Prime).two_le; omega)
    (by have := hqp.two_le; omega) hfin

end CFSG.Quasithin.H13.NF314ptA312
