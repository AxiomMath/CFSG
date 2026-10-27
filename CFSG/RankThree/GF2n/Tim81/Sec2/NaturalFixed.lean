module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7Conj
public import CFSG.CGT.Timmesfeld75.L2Basic
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzSmall
public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedCentre

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.QuasithinUnique.Setup.X7
open CFSG.CGT.Timmesfeld75 CFSG.Blueprint CFSG.LieType.Ree
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
  {W : Type} [AddCommMonoid W] [Module (ZMod 2) W]

private theorem utriElt_mulVec (s : F) (v : Fin 2 → F) :
    (utriElt s : Matrix (Fin 2) (Fin 2) F).mulVec v = ![v 0 + s * v 1, v 1] := by
  have h : v = ![v 0, v 1] := by ext i; fin_cases i <;> simp
  rw [h]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, utriElt_apply_00,
    utriElt_apply_01, utriElt_apply_10, utriElt_apply_11]

private theorem ltriElt_mulVec (s : F) (v : Fin 2 → F) :
    (ltriElt s : Matrix (Fin 2) (Fin 2) F).mulVec v = ![v 0, s * v 0 + v 1] := by
  have h : v = ![v 0, v 1] := by ext i; fin_cases i <;> simp
  rw [h]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ltriElt_apply_00,
    ltriElt_apply_01, ltriElt_apply_10, ltriElt_apply_11]

private theorem mem_fixedSub_utri_iff {ρ : Representation (ZMod 2) SL(2, F) W}
    {φ : W ≃+ (Fin 2 → F)}
    (hφ : ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w)) {w : W} :
    w ∈ fixedSub ρ (utri F) ↔ (φ w) 1 = 0 := by
  rw [mem_fixedSub]
  constructor
  · intro hw
    have h1 : ρ (utriElt (1 : F)) w = w := hw _ (utriElt_mem_utri 1)
    have h2 : (utriElt (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec (φ w) = φ w := by
      rw [← hφ, h1]
    rw [utriElt_mulVec] at h2
    have h3 := congrFun h2 0
    simp only [Matrix.cons_val_zero, one_mul] at h3
    exact add_left_cancel (a := (φ w) 0) (b := (φ w) 1) (c := 0) (by simpa using h3)
  · intro hw u hu
    obtain ⟨s, rfl⟩ := mem_utri_iff.1 hu
    apply φ.injective
    rw [hφ, utriElt_mulVec]
    ext i
    fin_cases i <;> simp [hw]

private theorem mem_fixedSub_ltri_iff {ρ : Representation (ZMod 2) SL(2, F) W}
    {φ : W ≃+ (Fin 2 → F)}
    (hφ : ∀ g w, φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w)) {w : W} :
    w ∈ fixedSub ρ (ltri F) ↔ (φ w) 0 = 0 := by
  rw [mem_fixedSub]
  constructor
  · intro hw
    have h1 : ρ (ltriElt (1 : F)) w = w := hw _ (ltriElt_mem_ltri 1)
    have h2 : (ltriElt (1 : F) : Matrix (Fin 2) (Fin 2) F).mulVec (φ w) = φ w := by
      rw [← hφ, h1]
    rw [ltriElt_mulVec] at h2
    have h3 := congrFun h2 1
    simp only [Matrix.cons_val_one, Matrix.head_cons, one_mul] at h3
    exact add_right_cancel (a := (φ w) 0) (b := (φ w) 1) (c := 0) (by simpa using h3)
  · intro hw u hu
    obtain ⟨t, rfl⟩ := mem_ltri_iff.1 hu
    apply φ.injective
    rw [hφ, ltriElt_mulVec]
    ext i
    fin_cases i <;> simp [hw]

theorem sup_fixedSub_conj_utri_eq_top (ρ : Representation (ZMod 2) SL(2, F) W)
    (hρ : IsNaturalModule ρ) {a b : SL(2, F)}
    (hne : conjSubgroup a (utri F) ≠ conjSubgroup b (utri F)) :
    fixedSub ρ (conjSubgroup a (utri F)) ⊔ fixedSub ρ (conjSubgroup b (utri F)) = ⊤ := by
  obtain ⟨φ, hφ⟩ := hρ
  obtain ⟨g, hg1, hg2⟩ := exists_conj_utri_ltri_of_ne hne
  rw [hg1, hg2, eq_top_iff]
  intro w _
  let u := φ (ρ g⁻¹ w)
  let v0 : Fin 2 → F := fun i => if i = 0 then u 0 else 0
  let v1 : Fin 2 → F := fun i => if i = 0 then 0 else u 1
  have huv : u = v0 + v1 := by
    ext i
    fin_cases i <;> simp [v0, v1]
  have hv0 : v0 1 = 0 := by simp [v0]
  have hv1 : v1 0 = 0 := by simp [v1]
  refine Submodule.mem_sup.2 ⟨ρ g (φ.symm v0), ?_, ρ g (φ.symm v1), ?_, ?_⟩
  · simp only [conjSubgroup]
    rw [mem_fixedSub_map_conj (ρ := ρ) g (utri F)]
    rw [show ρ g⁻¹ (ρ g (φ.symm v0)) = φ.symm v0 by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]]
    exact (mem_fixedSub_utri_iff hφ).2 (by rw [AddEquiv.apply_symm_apply]; exact hv0)
  · simp only [conjSubgroup]
    rw [mem_fixedSub_map_conj (ρ := ρ) g (ltri F)]
    rw [show ρ g⁻¹ (ρ g (φ.symm v1)) = φ.symm v1 by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]]
    exact (mem_fixedSub_ltri_iff hφ).2 (by rw [AddEquiv.apply_symm_apply]; exact hv1)
  · rw [← map_add, ← φ.symm.map_add, ← huv, AddEquiv.symm_apply_apply,
      ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

end SL2

section Sz

variable {a : ℕ} {K : Type} [Field K] [CharP K 2] [Fintype K]
  {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem suzukiS_zero_one_map_pow (c : ℕ) :
    (suzukiS a (0 : K) (1 : K)).map (· ^ 2 ^ c) = suzukiS a (0 : K) (1 : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiS, suzukiN, Matrix.map_apply]

private theorem suzukiS_zero_map_pow_mulVec (c : ℕ) (v : K) (u : Fin 4 → K)
    (h0 : u 0 = 0) (h1 : u 1 = 0) :
    ((suzukiS a 0 v).map (· ^ 2 ^ c)).mulVec u = u := by
  ext i
  fin_cases i <;>
    simp [suzukiS, suzukiN, Matrix.map_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      h0, h1]

private theorem suzukiW_map_pow (c : ℕ) :
    (suzukiW K).map (· ^ 2 ^ c) = suzukiW K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [suzukiW, Matrix.map_apply]

theorem mem_fixedSub_suzukiZ0_iff (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) {c : ℕ} {φ : W ≃+ (Fin 4 → K)}
    (hφ : ∀ g w, φ (ρ g w) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)).mulVec (φ w)) {w : W} :
    w ∈ fixedSub ρ (suzukiZ0 a K) ↔ (φ w) 0 = 0 ∧ (φ w) 1 = 0 := by
  rw [mem_fixedSub]
  constructor
  · intro hw
    have h1 : ρ (suzukiSElt a K 0 1) w = w :=
      hw _ ((mem_suzukiZ0_iff hK).2 ⟨1, rfl⟩)
    have h2 : ((suzukiS a (0 : K) (1 : K)).map (· ^ 2 ^ c)).mulVec (φ w) = φ w := by
      have hφ' := hφ (suzukiSElt a K 0 1) w
      rw [h1, coe_suzukiSElt] at hφ'
      exact hφ'.symm
    rw [suzukiS_zero_one_map_pow] at h2
    have h0 : (φ w) 0 = 0 := by
      have h3 := congrFun h2 2
      simp [suzukiS, suzukiN, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at h3
      exact add_right_cancel (a := (φ w) 0) (b := (φ w) 2) (c := 0) (by simpa using h3)
    refine ⟨h0, ?_⟩
    have h3 := congrFun h2 3
    simp [suzukiS, suzukiN, Matrix.mulVec, dotProduct, Fin.sum_univ_four, h0] at h3
    exact add_right_cancel (a := (φ w) 1) (b := (φ w) 3) (c := 0) (by simpa using h3)
  · rintro ⟨h0, h1⟩ z hz
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
    apply φ.injective
    rw [hφ]
    exact suzukiS_zero_map_pow_mulVec c v (φ w) h0 h1

private theorem mem_fixedSub_szZ_iff (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) {c : ℕ} {φ : W ≃+ (Fin 4 → K)}
    (hφ : ∀ g w, φ (ρ g w) =
      (((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ 2 ^ c)).mulVec (φ w)) {w : W} :
    w ∈ fixedSub ρ (szZ a K) ↔ (φ w) 2 = 0 ∧ (φ w) 3 = 0 := by
  have hsz : szZ a K = conjSubgroup (suzukiWElt a K) (suzukiZ0 a K) := rfl
  rw [hsz]
  simp only [conjSubgroup]
  rw [mem_fixedSub_map_conj (ρ := ρ) (suzukiWElt a K) (suzukiZ0 a K),
    mem_fixedSub_suzukiZ0_iff hK ρ hφ]
  have hW : φ (ρ (suzukiWElt a K)⁻¹ w) = ![φ w 3, φ w 2, φ w 1, φ w 0] := by
    rw [hφ]
    have hcoe : ((((suzukiWElt a K)⁻¹ : ↥(suzukiGroup a K)) : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K) = suzukiW K := by
      rw [suzukiWElt_inv]; exact coe_suzukiWElt (a := a) (K := K)
    rw [hcoe, suzukiW_map_pow, suzukiW_mulVec]
  rw [hW]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem natCard_fixedSub_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ) :
    Nat.card (fixedSub ρ (suzukiZ0 a K)) = Nat.card K ^ 2 := by
  obtain ⟨c, φ, hφ⟩ := hρ
  have h1 : Nat.card (fixedSub ρ (suzukiZ0 a K)) =
      Nat.card {u : Fin 4 → K // u 0 = 0 ∧ u 1 = 0} :=
    Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv (fun w => mem_fixedSub_suzukiZ0_iff hK ρ hφ))
  have h2 : Nat.card {u : Fin 4 → K // u 0 = 0 ∧ u 1 = 0} = Nat.card K ^ 2 := by
    have e : {u : Fin 4 → K // u 0 = 0 ∧ u 1 = 0} ≃ K × K :=
      { toFun := fun u => (u.1 2, u.1 3)
        invFun := fun p => ⟨![0, 0, p.1, p.2], by simp⟩
        left_inv := fun u => by
          apply Subtype.ext
          ext i
          fin_cases i <;> simp [u.2.1, u.2.2]
        right_inv := fun p => by simp }
    rw [Nat.card_congr e, Nat.card_prod, pow_two]
  rw [h1, h2]

private theorem natCard_fixedSub_szZ (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ) :
    Nat.card (fixedSub ρ (szZ a K)) = Nat.card K ^ 2 := by
  have hsz : szZ a K =
      (suzukiZ0 a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom := rfl
  rw [hsz]
  have h1 : Nat.card (fixedSub ρ
        ((suzukiZ0 a K).map (MulAut.conj (suzukiWElt a K)).toMonoidHom)) =
      Nat.card (fixedSub ρ (suzukiZ0 a K)) :=
    Nat.card_congr
      { toFun := fun w => ⟨ρ (suzukiWElt a K)⁻¹ w.1,
          (mem_fixedSub_map_conj (ρ := ρ) (suzukiWElt a K) (suzukiZ0 a K)).1 w.2⟩
        invFun := fun w => ⟨ρ (suzukiWElt a K) w.1, by
          rw [mem_fixedSub_map_conj (ρ := ρ) (suzukiWElt a K) (suzukiZ0 a K)]
          have h : ρ (suzukiWElt a K)⁻¹ (ρ (suzukiWElt a K) w.1) = w.1 := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply]
          rw [h]; exact w.2⟩
        left_inv := fun w => by
          apply Subtype.ext
          show ρ (suzukiWElt a K) (ρ (suzukiWElt a K)⁻¹ w.1) = w.1
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply]
        right_inv := fun w => by
          apply Subtype.ext
          show ρ (suzukiWElt a K)⁻¹ (ρ (suzukiWElt a K) w.1) = w.1
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] }
  rw [h1]
  exact natCard_fixedSub_suzukiZ0 hK ρ hρ

private theorem sup_fixedSub_szZ_szZ0 (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ) :
    fixedSub ρ (szZ a K) ⊔ fixedSub ρ (suzukiZ0 a K) = ⊤ := by
  obtain ⟨c, φ, hφ⟩ := hρ
  rw [eq_top_iff]
  intro w _
  let u := φ w
  let v0 : Fin 4 → K := ![u 0, u 1, 0, 0]
  let v1 : Fin 4 → K := ![0, 0, u 2, u 3]
  have huv : u = v0 + v1 := by
    ext i
    fin_cases i <;> simp [v0, v1]
  have hv0 : v0 2 = 0 ∧ v0 3 = 0 := by simp [v0]
  have hv1 : v1 0 = 0 ∧ v1 1 = 0 := by simp [v1]
  refine Submodule.mem_sup.2 ⟨φ.symm v0, ?_, φ.symm v1, ?_, ?_⟩
  · rw [mem_fixedSub_szZ_iff hK ρ hφ, AddEquiv.apply_symm_apply]
    simp [v0]
  · rw [mem_fixedSub_suzukiZ0_iff hK ρ hφ, AddEquiv.apply_symm_apply]
    simp [v1]
  · rw [← φ.symm.map_add, ← huv, AddEquiv.symm_apply_apply]

private theorem suzukiB_le_normalizer_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiB a K ≤ Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := by
  have hU : suzukiU a K ≤ Subgroup.centralizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact suzukiZ0_comm_suzukiU hK hz hu
  have hT : suzukiT a K ≤ Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) := by
    intro d hd
    obtain ⟨l, rfl⟩ := mem_suzukiT_iff.1 hd
    rw [mem_normalizer_iff_conjSubgroup_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
      change suzukiDElt a K l * suzukiSElt a K 0 v * (suzukiDElt a K l)⁻¹ ∈ suzukiZ0 a K
      rw [suzukiDElt_conj' hK]
      exact (mem_suzukiZ0_iff hK).mpr
        ⟨((↑l⁻¹ : K) ^ (2 ^ (a + 1) + 1)) * v, by simp⟩
    · rw [card_conjSubgroup]
  exact sup_le (hU.trans (Subgroup.centralizer_le_normalizer
    (G := ↥(suzukiGroup a K)) (suzukiZ0 a K : Set _))) hT

private theorem exists_conj_eq_szZ_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : ↥(suzukiGroup a K)}
    (hne : conjSubgroup x (szZ a K) ≠ conjSubgroup y (szZ a K)) :
    ∃ g : ↥(suzukiGroup a K),
      conjSubgroup g (conjSubgroup x (szZ a K)) = szZ a K ∧
      conjSubgroup g (conjSubgroup y (szZ a K)) = suzukiZ0 a K := by
  have hsz : szZ a K = conjSubgroup (suzukiWElt a K) (suzukiZ0 a K) := rfl
  have hx : conjSubgroup x (szZ a K) =
      conjSubgroup (x * suzukiWElt a K) (suzukiZ0 a K) := by
    rw [hsz, conjSubgroup_conjSubgroup]
  have hy : conjSubgroup y (szZ a K) =
      conjSubgroup (y * suzukiWElt a K) (suzukiZ0 a K) := by
    rw [hsz, conjSubgroup_conjSubgroup]
  set p := (x * suzukiWElt a K) • suzukiInfty K with hp
  set q := (y * suzukiWElt a K) • suzukiInfty K with hq
  have hpΩ : p ∈ suzukiOmega a K :=
    suzuki_smul_mem_suzukiOmega hK _ (suzukiInfty_mem_suzukiOmega a K)
  have hqΩ : q ∈ suzukiOmega a K :=
    suzuki_smul_mem_suzukiOmega hK _ (suzukiInfty_mem_suzukiOmega a K)
  have hpq : p ≠ q := by
    intro hpq
    apply hne
    have hB : (y * suzukiWElt a K)⁻¹ * (x * suzukiWElt a K) ∈ suzukiB a K := by
      have hstab : (y * suzukiWElt a K)⁻¹ * (x * suzukiWElt a K) ∈
          MulAction.stabilizer (↥(suzukiGroup a K)) (suzukiInfty K) := by
        rw [MulAction.mem_stabilizer_iff]
        calc ((y * suzukiWElt a K)⁻¹ * (x * suzukiWElt a K)) • suzukiInfty K
            = (y * suzukiWElt a K)⁻¹ • p := by rw [mul_smul]
          _ = (y * suzukiWElt a K)⁻¹ • q := by rw [hpq]
          _ = suzukiInfty K := inv_smul_smul _ _
      rwa [(suzuki_ovoid_stabilizer hK).1] at hstab
    have hN : (y * suzukiWElt a K)⁻¹ * (x * suzukiWElt a K) ∈
        Subgroup.normalizer (suzukiZ0 a K : Set ↥(suzukiGroup a K)) :=
      suzukiB_le_normalizer_suzukiZ0 hK hB
    have hZeq : conjSubgroup (x * suzukiWElt a K) (suzukiZ0 a K) =
        conjSubgroup (y * suzukiWElt a K) (suzukiZ0 a K) := by
      rw [conjSubgroup_eq_conjSubgroup_iff]
      have hinv : (x * suzukiWElt a K)⁻¹ * (y * suzukiWElt a K) =
          ((y * suzukiWElt a K)⁻¹ * (x * suzukiWElt a K))⁻¹ := by group
      rw [hinv]
      exact inv_mem hN
    rw [hx, hy, hZeq]
  obtain ⟨-, h2tr, -, -, -⟩ := suzuki_ovoid_double_transitivity hK
  obtain ⟨g, hgp, hgq⟩ := h2tr p hpΩ q hqΩ
    (suzukiLine a K (0 : K) (0 : K)) (suzukiLine_mem_suzukiOmega a K (0 : K) (0 : K))
    (suzukiInfty K) (suzukiInfty_mem_suzukiOmega a K)
    hpq (suzukiLine_ne_suzukiInfty (a := a) (0 : K) (0 : K))
  have hgp' : (g * (x * suzukiWElt a K)) • suzukiInfty K =
      (suzukiWElt a K) • suzukiInfty K := by
    rw [mul_smul, hgp]
    exact (suzuki_ovoid_weyl_action a hK).1.symm
  have hB1 : (suzukiWElt a K)⁻¹ * (g * (x * suzukiWElt a K)) ∈ suzukiB a K := by
    have hstab : (suzukiWElt a K)⁻¹ * (g * (x * suzukiWElt a K)) ∈
        MulAction.stabilizer (↥(suzukiGroup a K)) (suzukiInfty K) := by
      rw [MulAction.mem_stabilizer_iff]
      calc ((suzukiWElt a K)⁻¹ * (g * (x * suzukiWElt a K))) • suzukiInfty K
          = (suzukiWElt a K)⁻¹ • ((g * (x * suzukiWElt a K)) • suzukiInfty K) :=
            mul_smul _ _ _
        _ = (suzukiWElt a K)⁻¹ • ((suzukiWElt a K) • suzukiInfty K) := by rw [hgp']
        _ = suzukiInfty K := inv_smul_smul _ _
    rwa [(suzuki_ovoid_stabilizer hK).1] at hstab
  have hZ1 : conjSubgroup ((suzukiWElt a K)⁻¹ * (g * (x * suzukiWElt a K)))
      (suzukiZ0 a K) = suzukiZ0 a K :=
    mem_normalizer_iff_conjSubgroup_eq.1 (suzukiB_le_normalizer_suzukiZ0 hK hB1)
  have hB2 : g * (y * suzukiWElt a K) ∈ suzukiB a K := by
    have hstab : g * (y * suzukiWElt a K) ∈
        MulAction.stabilizer (↥(suzukiGroup a K)) (suzukiInfty K) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hgq]
    rwa [(suzuki_ovoid_stabilizer hK).1] at hstab
  refine ⟨g, ?_, ?_⟩
  · rw [hx, conjSubgroup_conjSubgroup, hsz]
    conv_lhs =>
      rw [show g * (x * suzukiWElt a K) =
        suzukiWElt a K * ((suzukiWElt a K)⁻¹ * (g * (x * suzukiWElt a K))) by group]
    rw [← conjSubgroup_conjSubgroup, hZ1]
  · rw [hy, conjSubgroup_conjSubgroup]
    exact mem_normalizer_iff_conjSubgroup_eq.1 (suzukiB_le_normalizer_suzukiZ0 hK hB2)

theorem natCard_fixedSub_conj_szZ (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ)
    (x : ↥(suzukiGroup a K)) :
    Nat.card (fixedSub ρ (conjSubgroup x (szZ a K))) = Nat.card K ^ 2 := by
  simp only [conjSubgroup] at *
  have h1 : Nat.card (fixedSub ρ ((szZ a K).map (MulAut.conj x).toMonoidHom)) =
      Nat.card (fixedSub ρ (szZ a K)) :=
    Nat.card_congr
      { toFun := fun w => ⟨ρ x⁻¹ w.1, (mem_fixedSub_map_conj (ρ := ρ) x (szZ a K)).1 w.2⟩
        invFun := fun w => ⟨ρ x w.1, by
          rw [mem_fixedSub_map_conj (ρ := ρ) x (szZ a K)]
          have h : ρ x⁻¹ (ρ x w.1) = w.1 := by
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
              Module.End.one_apply]
          rw [h]; exact w.2⟩
        left_inv := fun w => by
          apply Subtype.ext
          show ρ x (ρ x⁻¹ w.1) = w.1
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
            Module.End.one_apply]
        right_inv := fun w => by
          apply Subtype.ext
          show ρ x⁻¹ (ρ x w.1) = w.1
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] }
  rw [h1]
  exact natCard_fixedSub_szZ hK ρ hρ

theorem sup_fixedSub_conj_szZ_eq_top (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ρ : Representation (ZMod 2) ↥(suzukiGroup a K) W) (hρ : IsSzNatural ρ)
    {x y : ↥(suzukiGroup a K)}
    (hne : conjSubgroup x (szZ a K) ≠ conjSubgroup y (szZ a K)) :
    fixedSub ρ (conjSubgroup x (szZ a K)) ⊔ fixedSub ρ (conjSubgroup y (szZ a K)) = ⊤ := by
  obtain ⟨g, hg1, hg2⟩ := exists_conj_eq_szZ_suzukiZ0 hK hne
  have hH1 : conjSubgroup x (szZ a K) = conjSubgroup g⁻¹ (szZ a K) := by
    have h := congrArg (conjSubgroup g⁻¹) hg1
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
    exact h
  have hH2 : conjSubgroup y (szZ a K) = conjSubgroup g⁻¹ (suzukiZ0 a K) := by
    have h := congrArg (conjSubgroup g⁻¹) hg2
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
    exact h
  have hmain := sup_fixedSub_szZ_szZ0 hK ρ hρ
  rw [hH1, hH2, eq_top_iff]
  intro w _
  have htop : ρ g w ∈ fixedSub ρ (szZ a K) ⊔ fixedSub ρ (suzukiZ0 a K) := by
    rw [hmain]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at htop
  obtain ⟨A, hA, B, hB, hAB⟩ := htop
  refine Submodule.mem_sup.2 ⟨ρ g⁻¹ A, ?_, ρ g⁻¹ B, ?_, ?_⟩
  · simp only [conjSubgroup]
    rw [mem_fixedSub_map_conj (ρ := ρ) g⁻¹ (szZ a K)]
    rw [show ρ (g⁻¹)⁻¹ (ρ g⁻¹ A) = A by
      rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]]
    exact hA
  · simp only [conjSubgroup]
    rw [mem_fixedSub_map_conj (ρ := ρ) g⁻¹ (suzukiZ0 a K)]
    rw [show ρ (g⁻¹)⁻¹ (ρ g⁻¹ B) = B by
      rw [inv_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]]
    exact hB
  · rw [← map_add, hAB, show ρ g⁻¹ (ρ g w) = w by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]]

end Sz
