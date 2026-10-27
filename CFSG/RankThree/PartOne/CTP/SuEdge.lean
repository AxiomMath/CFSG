module

public import CFSG.RankThree.PartOne.CTP.SuAut
public import CFSG.RankThree.PartOne.CTP.Su4Pair
public import CFSG.RankThree.PartOne.CTP.EdgeGeneric

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.LieType.Universal.Unitary (SUid SU conjTr antidiag conjEquiv)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_apply unitaryInvolution_involutive)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped MatrixGroups

section Numerics

theorem unitaryInvolution_eq_self_of_pow_eq_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {f p : ℕ}
    (hpq : p ∣ 2 ^ f - 1) {l : K} (hl : l ^ p = 1) : unitaryInvolution K 2 f l = l := by
  rw [unitaryInvolution_apply]
  obtain ⟨m, hm⟩ := hpq
  have h1 : l ^ (2 ^ f - 1) = 1 := by rw [hm, pow_mul, hl, one_pow]
  have hpos : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  calc l ^ 2 ^ f = l ^ (2 ^ f - 1 + 1) := by rw [Nat.sub_add_cancel hpos]
    _ = l := by rw [pow_succ, h1, one_mul]

theorem sq_sub_one_eq (q : ℕ) (hq : 1 ≤ q) : q ^ 2 - 1 = (q + 1) * (q - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.sub_eq_of_eq_add]
  ring

theorem card_su_two_lt_card_sl_two {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    Nat.card (SU (unitaryInvolution K 2 f) 2) < Nat.card SL(2, K) := by
  rw [CFSG.LieType.Steinberg.card_SU_two hK,
    CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two K, hK]
  generalize 2 ^ f = q at hq ⊢
  have h4 : q ≤ q ^ 2 := by nlinarith
  have h6 : 1 < q ^ 2 := by nlinarith
  have h5 : q ^ 2 * 2 ≤ (q ^ 2) ^ 2 := by nlinarith
  have h3 : q + 1 < (q ^ 2) ^ 2 := by omega
  calc q * (q ^ 2 - 1) ≤ q * q ^ 2 := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = q ^ 2 * q := by ring
    _ < q ^ 2 * ((q ^ 2) ^ 2 - 1) :=
        Nat.mul_lt_mul_of_pos_left (by omega) (by positivity)

end Numerics

section Edge

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {G : Type} [Group G]

include h in
theorem su_edge_pair (hf : 2 ≤ f) (θ : SUid (unitaryInvolution K 2 f) 4 →* G)
    (hker : θ.ker ≤ Subgroup.center (SUid (unitaryInvolution K 2 f) 4)) {p : ℕ}
    (hp : p.Prime) (hpq : p ∣ 2 ^ f - 1) {E A B : Subgroup G} [CFSG.IsElementaryAbelian p E]
    (hE : EdgeTorus p E A B) (hAB : A ⊔ B = θ.range) {KA KB : Type} [Field KA] [Field KB]
    [Finite KA] [Finite KB] (hKA : Nat.card KA = 2 ^ f) (hKB : Nat.card KB = (2 ^ f) ^ 2)
    (ρA : SL(2, KA) ≃* ↥A) (ρB : SL(2, KB) ≃* ↥B)
    (hz : ¬ (E ⊓ A ≤ Subgroup.centralizer (B : Set G))) :
    ∃ (Q : GL (Fin 4) K) (hQ : conjTr (unitaryInvolution K 2 f) (Q : Matrix (Fin 4) (Fin 4) K) *
        (Q : Matrix (Fin 4) (Fin 4) K) = antidiag 4),
      A.comap θ = (lbEmb (unitaryInvolution K 2 f)).range.map (conjEquiv Q hQ).toMonoidHom ∧
      B.comap θ = (sbEmb (unitaryInvolution K 2 f)
        (unitaryInvolution_involutive h.card_eq_sq)).range.map (conjEquiv Q hQ).toMonoidHom := by
  classical
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hθ : Function.Injective θ := injective_of_ker_le_center_su h hq4 θ hker
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    have h2 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
    omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hmK : p ∣ Nat.card K - 1 := by
    rw [hK]
    refine hpq.trans ?_
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow (2 ^ f) 1 2
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd_natCard_sub_one hmK
  have : NeZero p := ⟨hp.ne_zero⟩
  have hσ := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hK
  have hfix : ∀ l : K, l ^ p = 1 → unitaryInvolution K 2 f l = l := fun l hl =>
    unitaryInvolution_eq_self_of_pow_eq_one hpq hl
  have hAle : A ≤ θ.range := by rw [← hAB]; exact le_sup_left
  have hBle : B ≤ θ.range := by rw [← hAB]; exact le_sup_right
  obtain ⟨φA, hφA, hθφA, hA₀⟩ := exists_lift_of_equiv θ hθ hAle ρA
  obtain ⟨φB, hφB, hθφB, hB₀⟩ := exists_lift_of_equiv θ hθ hBle ρB
  have hperfA : Group.IsPerfect (SL(2, KA)) := isPerfect_sl2 (by rw [hKA]; exact hq4)
  have hperfB : Group.IsPerfect (SL(2, KB)) := isPerfect_sl2 (by rw [hKB]; nlinarith)
  have : Group.IsPerfect (A.comap θ) := by
    rw [hA₀]
    exact Group.IsPerfect.range φA
  have : Group.IsPerfect (B.comap θ) := by
    rw [hB₀]
    exact Group.IsPerfect.range φB
  have hcardA : Nat.card (A.comap θ) = Nat.card (SU (unitaryInvolution K 2 f) 2) := by
    rw [hA₀, CFSG.LieType.Steinberg.card_SU_two hK, card_range_sl2 (K := KA) rfl φA hφA,
      CFSG.LieType.Steinberg.card_specialLinearGroup_fin_two KA, hKA]
  have hcardB : Nat.card (B.comap θ) = Nat.card SL(2, K) := by
    rw [hB₀]
    exact card_range_sl2 (by rw [hKB, hK]) φB hφB
  obtain ⟨tA, htA⟩ := exists_sl2_orderOf_eq (L := KA)
  obtain ⟨tB, htB⟩ := exists_sl2_orderOf_eq (L := KB)
  have hordA : orderOf (φA tA) = 2 ^ f - 1 := by
    rw [orderOf_injective φA hφA, htA, hKA]
  have hordB : orderOf (φB (tB ^ (2 ^ f + 1))) = 2 ^ f - 1 := by
    have hdvd : 2 ^ f + 1 ∣ orderOf tB := by
      rw [htB, hKB, sq_sub_one_eq _ (by omega)]
      exact ⟨2 ^ f - 1, rfl⟩
    rw [orderOf_injective φB hφB, orderOf_pow_of_dvd (by omega) hdvd, htB, hKB,
      sq_sub_one_eq _ (by omega)]
    exact Nat.mul_div_cancel_left _ (by omega)
  obtain ⟨eA, heAE, hAcen, ⟨yB, hyB, hyBne⟩, -, hAord⟩ := hE.exists_centralizing hp
  obtain ⟨eB, heBE, hBcen, ⟨yA, hyA, hyAne⟩, -, hBord⟩ := hE.symm.exists_centralizing hp
  have hXA : eA ∈ Subgroup.normalizer (θ.range : Set G) := by
    rw [← hAB]
    exact mem_normalizer_sup (le_normalizer_of_dec hE.decA heAE)
      (le_normalizer_of_dec hE.decB heAE)
  have hXB : eB ∈ Subgroup.normalizer (θ.range : Set G) := by
    rw [← hAB]
    exact mem_normalizer_sup (le_normalizer_of_dec hE.decA heBE)
      (le_normalizer_of_dec hE.decB heBE)
  have heApow : eA ^ p = 1 := by rw [← hAord]; exact pow_orderOf_eq_one eA
  have heBpow : eB ^ p = 1 := by rw [← hBord]; exact pow_orderOf_eq_one eB
  obtain ⟨gA, hgApow, hgA⟩ := exists_su_of_normalizes h hq4 θ hθ hXA hpodd heApow hordA
    (by rw [hθφA]; exact hAcen _ (ρA tA).2)
  obtain ⟨gB, hgBpow, hgB⟩ := exists_su_of_normalizes h hq4 θ hθ hXB hpodd heBpow hordB
    (by rw [hθφB]; exact hBcen _ (ρB (tB ^ (2 ^ f + 1))).2)
  have hcA : ∀ a ∈ A.comap θ, a * gA = gA * a := fun a ha =>
    commute_of_conj hθ hgA (hAcen _ ha)
  have hcB : ∀ b ∈ B.comap θ, b * gB = gB * b := fun b hb =>
    commute_of_conj hθ hgB (hBcen _ hb)
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : SUid (unitaryInvolution K 2 f) 4, θ b₀ = yB := hBle hyB
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : SUid (unitaryInvolution K 2 f) 4, θ a₀ = yA := hAle hyA
  have hmovB : ∃ b ∈ B.comap θ, gA * b ≠ b * gA :=
    ⟨b₀, by rw [Subgroup.mem_comap, hb₀]; exact hyB,
      not_commute_of_conj hgA (by rw [hb₀]; exact hyBne)⟩
  have hmovA : ∃ a ∈ A.comap θ, gB * a ≠ a * gB :=
    ⟨a₀, by rw [Subgroup.mem_comap, ha₀]; exact hyA,
      not_commute_of_conj hgB (by rw [ha₀]; exact hyAne)⟩
  have hgA1 : gA ≠ 1 := by
    rintro rfl
    obtain ⟨b, -, hb⟩ := hmovB
    exact hb (by simp)
  have hgB1 : gB ≠ 1 := by
    rintro rfl
    obtain ⟨a, -, ha⟩ := hmovA
    exact ha (by simp)
  have hee : eA * eB = eB * eA :=
    congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := E)).comm (⟨eA, heAE⟩ : E) ⟨eB, heBE⟩)
  have hcom : gA * gB = gB * gA :=
    commute_of_conj_of_center_bot hθ (center_suid_four_eq_bot h hq4) hgA hgB hee
  obtain ⟨z, hzEA, hzC⟩ : ∃ z ∈ E ⊓ A, z ∉ Subgroup.centralizer (B : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hz fun z hz' => hcon z hz'
  obtain ⟨zs, hzs⟩ : ∃ zs : SUid (unitaryInvolution K 2 f) 4, θ zs = z := hAle hzEA.2
  have hzsA : zs ∈ A.comap θ := by rw [Subgroup.mem_comap, hzs]; exact hzEA.2
  have hzsp : zs ^ p = 1 := by
    apply hθ
    rw [map_pow, hzs, map_one]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian z hzEA.1
  have hzsg : zs * gB = gB * zs := by
    refine commute_of_conj hθ hgB ?_
    rw [hzs]
    exact (congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := E)).comm (⟨eB, heBE⟩ : E) ⟨z, hzEA.1⟩))
  have hzsB : ¬ ∀ b ∈ B.comap θ, zs * b = b * zs := by
    intro hall
    apply hzC
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨b, hb⟩ := hBle hy
    have hb' : b ∈ B.comap θ := by rw [Subgroup.mem_comap, hb]; exact hy
    have := congrArg θ (hall b hb')
    rw [map_mul, map_mul, hzs, hb] at this
    exact this.symm
  have hA1 : A.comap θ ≠ ⊥ := by
    intro h0
    have hmem : φA tA ∈ A.comap θ := by
      change θ (φA tA) ∈ A
      rw [hθφA]
      exact (ρA tA).2
    rw [h0, Subgroup.mem_bot] at hmem
    have h4 := hordA
    rw [hmem, orderOf_one] at h4
    omega
  have hB1 : B.comap θ ≠ ⊥ := by
    intro h0
    have hmem : φB tB ∈ B.comap θ := by
      change θ (φB tB) ∈ B
      rw [hθφB]
      exact (ρB tB).2
    rw [h0, Subgroup.mem_bot] at hmem
    have h4 : orderOf (φB tB) = 1 := by rw [hmem, orderOf_one]
    rw [orderOf_injective φB hφB, htB, hKB] at h4
    have : 4 ≤ (2 ^ f) ^ 2 := by nlinarith
    omega
  exact su4_pair hσ hζ hfix (card_su_two_lt_card_sl_two hq4 hK) hgApow hgBpow hgA1 hgB1 hcom
    hA1 hB1 hcardA hcardB hcA hcB hmovB hzsA hzsp hzsg hzsB

end Edge

end CFSG.RankThree.PartOne.CTP
