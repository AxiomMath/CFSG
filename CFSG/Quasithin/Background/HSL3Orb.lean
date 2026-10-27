module

public import CFSG.Quasithin.Background.HSL3Fix

public section

namespace CFSG.Quasithin

namespace H

namespace SL3One

open CFSG.Open CFSG.Assembly.LowTwoRank SL3Pair
open scoped Matrix

theorem exists_two_ne {α : Type*} [Finite α] (h : 3 ≤ Nat.card α) (o : α) :
    ∃ x y : α, x ≠ o ∧ y ≠ o ∧ x ≠ y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ : ∃ x, x ≠ o := by
    by_contra h'
    push Not at h'
    have : Subsingleton α := ⟨fun p q => (h' p).trans (h' q).symm⟩
    have := Finite.card_le_one_iff_subsingleton.mpr this
    omega
  have hsurj : Function.Surjective (![o, x] : Fin 2 → α) := by
    intro y
    by_cases hy : y = o
    · exact ⟨0, by simp [hy]⟩
    · exact ⟨1, by simp [hcon y x hy hx]⟩
  have h2 := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h2
  omega

variable {K : Type} [Field K] [Finite K]

theorem eq_zero_or_eq_of_cross_eq_zero (hK : Nat.card K = 2) {y z : Fin 3 → K} (hz : z ≠ 0)
    (h : y ⨯₃ z = 0) : y = 0 ∨ y = z := by
  have hdep : ¬ LinearIndependent K ![z, y] := by
    rw [← crossProduct_ne_zero_iff_linearIndependent, not_not, ← cross_anticomm, h, neg_zero]
  rw [LinearIndependent.pair_iff' hz] at hdep
  push Not at hdep
  obtain ⟨μ, hμ⟩ := hdep
  rcases eq_zero_or_eq_one_of_card hK μ with rfl | rfl
  · left
    rw [← hμ, zero_smul]
  · right
    rw [← hμ, one_smul]

theorem cross_ne_zero (hK : Nat.card K = 2) {u v : Fin 3 → K} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u ≠ v) : u ⨯₃ v ≠ 0 := by
  rw [crossProduct_ne_zero_iff_linearIndependent, LinearIndependent.pair_iff' hu]
  intro μ hμ
  rcases eq_zero_or_eq_one_of_card hK μ with rfl | rfl
  · rw [zero_smul] at hμ
    exact hv hμ.symm
  · rw [one_smul] at hμ
    exact huv hμ

theorem eq_zero_or_eq_cross (hK : Nat.card K = 2) {y u v : Fin 3 → K} (hu : u ≠ 0)
    (hv : v ≠ 0) (huv : u ≠ v) (h1 : y ⬝ᵥ u = 0) (h2 : y ⬝ᵥ v = 0) : y = 0 ∨ y = u ⨯₃ v := by
  apply eq_zero_or_eq_of_cross_eq_zero hK (cross_ne_zero hK hu hv huv)
  rw [cross_cross_eq_smul_sub_smul', h2, dotProduct_comm u y, h1, zero_smul, zero_smul, sub_zero]

theorem exists_dot_eq_one_of_two (hK : Nat.card K = 2) {A B : Set (Fin 3 → K)}
    (hA : ∃ u ∈ A, ∃ v ∈ A, u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v)
    (hB : ∃ x ∈ B, ∃ y ∈ B, x ≠ 0 ∧ y ≠ 0 ∧ x ≠ y) :
    ∃ a ∈ A, ∃ b ∈ B, b ⬝ᵥ a = 1 := by
  obtain ⟨u, huA, v, hvA, hu, hv, huv⟩ := hA
  obtain ⟨x, hxB, y, hyB, hx, hy, hxy⟩ := hB
  by_contra hcon
  push Not at hcon
  have h0 : ∀ a ∈ A, ∀ b ∈ B, b ⬝ᵥ a = 0 := fun a ha b hb =>
    (eq_zero_or_eq_one_of_card hK _).resolve_right (hcon a ha b hb)
  have hx' := (eq_zero_or_eq_cross hK hu hv huv (h0 u huA x hxB) (h0 v hvA x hxB)).resolve_left hx
  have hy' := (eq_zero_or_eq_cross hK hu hv huv (h0 u huA y hyB) (h0 v hvA y hyB)).resolve_left hy
  exact hxy (hx'.trans hy'.symm)

theorem exists_two_orth (hK : Nat.card K = 2) {b : Fin 3 → K} (hb : b ≠ 0) :
    ∃ w w' : Fin 3 → K, b ⬝ᵥ w = 0 ∧ b ⬝ᵥ w' = 0 ∧ w ≠ 0 ∧ w' ≠ 0 ∧ w ≠ w' := by
  have hcard : Nat.card {x : Fin 3 → K // b ⬝ᵥ x = 0} = 4 := by
    rw [card_orth hb, hK]
    norm_num
  obtain ⟨⟨w, hw⟩, ⟨w', hw'⟩, h1, h2, h3⟩ :=
    exists_two_ne (α := {x : Fin 3 → K // b ⬝ᵥ x = 0}) (by rw [hcard]; norm_num)
      ⟨0, dotProduct_zero b⟩
  exact ⟨w, w', hw, hw', fun h => h1 (Subtype.ext h), fun h => h2 (Subtype.ext h),
    fun h => h3 (Subtype.ext h)⟩

variable [CharP K 2]

theorem exists_order_three (hK : Nat.card K = 2) {a b : Fin 3 → K} (hab : b ⬝ᵥ a = 1) :
    ∃ θ ∈ StatedSL 3 K, pairHom θ ^ 3 = 1 ∧ pairHom θ ≠ 1 ∧
      ∀ x : PairMod K, pairHom θ x = x →
        (Multiplicative.toAdd x.1 = 0 ∨ Multiplicative.toAdd x.1 = a) ∧
        (Multiplicative.toAdd x.2 = 0 ∨ Multiplicative.toAdd x.2 = b) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_dotProduct] at hab
    exact zero_ne_one hab
  obtain ⟨w, w', hbw, hbw', hw0, hw'0, hww'⟩ := exists_two_orth hK hb0
  have hbeq : b = w ⨯₃ w' :=
    (eq_zero_or_eq_cross hK hw0 hw'0 hww' hbw hbw').resolve_left hb0
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hψw : (a ⨯₃ w) ⬝ᵥ w = 0 := cross_dot_self a w
  have hψ'w' : (a ⨯₃ w') ⬝ᵥ w' = 0 := cross_dot_self a w'
  have hψw' : (a ⨯₃ w) ⬝ᵥ w' = 1 := by
    rw [dotProduct_comm, triple_product_permutation, ← hbeq, dotProduct_comm, hab]
  have hψ'w : (a ⨯₃ w') ⬝ᵥ w = 1 := by
    rw [dotProduct_comm, triple_product_permutation, ← cross_anticomm, ← hbeq, dotProduct_neg,
      dotProduct_comm, hab, CharTwo.neg_eq]
  set ψ := a ⨯₃ w with hψ
  set ψ' := a ⨯₃ w' with hψ'
  set θ : GL (Fin 3) K := trvGL hψw * trvGL hψ'w' with hθ
  have key : ∀ x : Fin 3 → K,
      (θ : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x + (ψ' ⬝ᵥ x) • w' + (ψ ⬝ᵥ x + ψ' ⬝ᵥ x) • w ∧
        ψ ⬝ᵥ ((θ : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = ψ ⬝ᵥ x + ψ' ⬝ᵥ x ∧
        ψ' ⬝ᵥ ((θ : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = ψ ⬝ᵥ x := by
    intro x
    have e : (θ : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
        x + (ψ' ⬝ᵥ x) • w' + (ψ ⬝ᵥ x + ψ' ⬝ᵥ x) • w := by
      rw [hθ, Units.val_mul, ← Matrix.mulVec_mulVec, coe_trvGL, coe_trvGL,
        one_add_vecMulVec_mulVec, one_add_vecMulVec_mulVec, dotProduct_add, dotProduct_smul,
        hψw', smul_eq_mul, mul_one]
    refine ⟨e, ?_, ?_⟩
    · rw [e]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hψw, hψw']
      ring
    · rw [e]
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hψ'w, hψ'w']
      linear_combination (ψ' ⬝ᵥ x) * h2
  have hθ3m : (θ : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    refine Matrix.ext_iff_mulVec.mpr fun x => ?_
    rw [pow_succ, pow_succ, pow_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.one_mulVec]
    obtain ⟨e1, p1, q1⟩ := key x
    obtain ⟨e2, p2, q2⟩ := key ((θ : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
    obtain ⟨e3, -, -⟩ := key ((θ : Matrix (Fin 3) (Fin 3) K) *ᵥ
      ((θ : Matrix (Fin 3) (Fin 3) K) *ᵥ x))
    rw [e3, p2, q2, e2, p1, q1, e1]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination ((ψ ⬝ᵥ x + ψ' ⬝ᵥ x) * w' i + (3 * (ψ ⬝ᵥ x) + 2 * (ψ' ⬝ᵥ x)) * w i) * h2
  have hθ3 : θ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hθ3m, Units.val_one])
  have hli : LinearIndependent K ![w, w'] :=
    crossProduct_ne_zero_iff_linearIndependent.mp (cross_ne_zero hK hw0 hw'0 hww')
  have hψ0 : ψ ≠ 0 := by
    intro h
    rw [h, zero_dotProduct] at hψw'
    exact zero_ne_one hψw'
  have hψ'0 : ψ' ≠ 0 := by
    intro h
    rw [h, zero_dotProduct] at hψ'w
    exact zero_ne_one hψ'w
  have hψψ' : ψ ≠ ψ' := by
    intro h
    rw [h, hψ'w] at hψw
    exact one_ne_zero hψw
  have hcross : ψ ⨯₃ ψ' = a := by
    rw [hψ', cross_cross_eq_smul_sub_smul', hψw', dot_self_cross, one_smul, zero_smul, sub_zero]
  have hfix1 : ∀ x : Fin 3 → K, (θ : Matrix (Fin 3) (Fin 3) K) *ᵥ x = x → x = 0 ∨ x = a := by
    intro x hx
    obtain ⟨e1, -, -⟩ := key x
    rw [e1, add_assoc, add_eq_left] at hx
    obtain ⟨hpq, hq⟩ := LinearIndependent.pair_iff.mp hli _ _ (by rw [add_comm]; exact hx)
    have hp : ψ ⬝ᵥ x = 0 := by
      rw [hq, add_zero] at hpq
      exact hpq
    rw [← hcross]
    exact eq_zero_or_eq_cross hK hψ0 hψ'0 hψψ' (by rw [dotProduct_comm]; exact hp)
      (by rw [dotProduct_comm]; exact hq)
  have hfix2 : ∀ y : Fin 3 → K,
      ((dualGL θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ y = y → y = 0 ∨ y = b := by
    intro y hy
    have hy' : ∀ x, y ⬝ᵥ ((θ : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = y ⬝ᵥ x := by
      intro x
      conv_lhs => rw [← hy]
      rw [coe_dualGL, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hw := hy' w
    have hw' := hy' w'
    rw [(key w).1, hψw, hψ'w] at hw
    rw [(key w').1, hψw', hψ'w'] at hw'
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul] at hw hw'
    have hyw : y ⬝ᵥ w = 0 := by linear_combination hw'
    have hyw' : y ⬝ᵥ w' = 0 := by linear_combination hw - hyw
    rw [hbeq]
    exact eq_zero_or_eq_cross hK hw0 hw'0 hww' hyw hyw'
  refine ⟨θ, Subgroup.mul_mem _ (trvGL_mem hψw) (trvGL_mem hψ'w'), ?_, ?_, ?_⟩
  · rw [← map_pow, hθ3, map_one]
  · intro h
    have h1 : θ = 1 := pairHom_injective (h.trans (map_one pairHom).symm)
    have hw := hfix1 w (by rw [h1, Units.val_one, Matrix.one_mulVec])
    rcases hw with hw | hw
    · exact hw0 hw
    · rw [hw, hab] at hbw
      exact one_ne_zero hbw
  · intro x hx
    have h1 : (θ : Matrix (Fin 3) (Fin 3) K) *ᵥ Multiplicative.toAdd x.1 =
        Multiplicative.toAdd x.1 :=
      congrArg (fun y : PairMod K => Multiplicative.toAdd y.1) hx
    have h2 : ((dualGL θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        Multiplicative.toAdd x.2 = Multiplicative.toAdd x.2 :=
      congrArg (fun y : PairMod K => Multiplicative.toAdd y.2) hx
    exact ⟨hfix1 _ h1, hfix2 _ h2⟩

omit [CharP K 2] in
theorem card_V₁_two (hK : Nat.card K = 2) : Nat.card ↥(V₁ K) = 8 := by
  have e : ↥(V₁ K) ≃ StdMod (Fin 3) K :=
    { toFun := fun x => (x : PairMod K).1
      invFun := fun v => ⟨(v, 1), mem_V₁.mpr rfl⟩
      left_inv := fun x => Subtype.ext (Prod.ext rfl (mem_V₁.mp x.2).symm)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, card_stdMod, hK, Fintype.card_fin]
  norm_num

omit [CharP K 2] in
theorem card_V₂_two (hK : Nat.card K = 2) : Nat.card ↥(V₂ K) = 8 := by
  have e : ↥(V₂ K) ≃ StdMod (Fin 3) K :=
    { toFun := fun x => (x : PairMod K).2
      invFun := fun v => ⟨(1, v), mem_V₂.mpr rfl⟩
      left_inv := fun x => Subtype.ext (Prod.ext (mem_V₂.mp x.2).symm rfl)
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, card_stdMod, hK, Fintype.card_fin]
  norm_num

omit [CharP K 2] in
theorem exists_two_of_card_V₁ {U : Subgroup (PairMod K)}
    (h : 3 ≤ Nat.card ↥(U ⊓ V₁ K)) :
    ∃ u ∈ {a : Fin 3 → K | ((Multiplicative.ofAdd a, 1) : PairMod K) ∈ U},
      ∃ v ∈ {a : Fin 3 → K | ((Multiplicative.ofAdd a, 1) : PairMod K) ∈ U},
        u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_ne h 1
  have hxe : ((Multiplicative.ofAdd (Multiplicative.toAdd (x : PairMod K).1), 1) : PairMod K) =
      x := Prod.ext rfl (mem_V₁.mp x.2.2).symm
  have hye : ((Multiplicative.ofAdd (Multiplicative.toAdd (y : PairMod K).1), 1) : PairMod K) =
      y := Prod.ext rfl (mem_V₁.mp y.2.2).symm
  refine ⟨Multiplicative.toAdd (x : PairMod K).1, ?_, Multiplicative.toAdd (y : PairMod K).1, ?_,
    fun h => hx (Subtype.ext ?_), fun h => hy (Subtype.ext ?_), fun h => hxy (Subtype.ext ?_)⟩
  · change _ ∈ U
    rw [hxe]
    exact x.2.1
  · change _ ∈ U
    rw [hye]
    exact y.2.1
  · rw [← hxe, h]
    rfl
  · rw [← hye, h]
    rfl
  · rw [← hxe, ← hye, h]

omit [CharP K 2] in
theorem exists_two_of_card_V₂ {U : Subgroup (PairMod K)}
    (h : 3 ≤ Nat.card ↥(U ⊓ V₂ K)) :
    ∃ u ∈ {b : Fin 3 → K | ((1, Multiplicative.ofAdd b) : PairMod K) ∈ U},
      ∃ v ∈ {b : Fin 3 → K | ((1, Multiplicative.ofAdd b) : PairMod K) ∈ U},
        u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v := by
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_two_ne h 1
  have hxe : ((1, Multiplicative.ofAdd (Multiplicative.toAdd (x : PairMod K).2)) : PairMod K) =
      x := Prod.ext (mem_V₂.mp x.2.2).symm rfl
  have hye : ((1, Multiplicative.ofAdd (Multiplicative.toAdd (y : PairMod K).2)) : PairMod K) =
      y := Prod.ext (mem_V₂.mp y.2.2).symm rfl
  refine ⟨Multiplicative.toAdd (x : PairMod K).2, ?_, Multiplicative.toAdd (y : PairMod K).2, ?_,
    fun h => hx (Subtype.ext ?_), fun h => hy (Subtype.ext ?_), fun h => hxy (Subtype.ext ?_)⟩
  · change _ ∈ U
    rw [hxe]
    exact x.2.1
  · change _ ∈ U
    rw [hye]
    exact y.2.1
  · rw [← hxe, h]
    rfl
  · rw [← hye, h]
    rfl
  · rw [← hxe, ← hye, h]

omit [CharP K 2] in
theorem exists_dot_eq_one_of_card (hK : Nat.card K = 2) {U : Subgroup (PairMod K)}
    (h1 : 3 ≤ Nat.card ↥(U ⊓ V₁ K)) (h2 : 3 ≤ Nat.card ↥(U ⊓ V₂ K)) :
    ∃ a b : Fin 3 → K, b ⬝ᵥ a = 1 ∧ ((Multiplicative.ofAdd a, 1) : PairMod K) ∈ U ∧
      ((1, Multiplicative.ofAdd b) : PairMod K) ∈ U := by
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_dot_eq_one_of_two hK (exists_two_of_card_V₁ h1) (exists_two_of_card_V₂ h2)
  exact ⟨a, b, hab, ha, hb⟩

theorem three_le_of_hyperplane (hK : Nat.card K = 2) {U : Subgroup (PairMod K)}
    (hU : Nat.card U * 2 = 2 ^ 6) :
    3 ≤ Nat.card ↥(U ⊓ V₁ K) ∧ 3 ≤ Nat.card ↥(U ⊓ V₂ K) := by
  have hV := card_pairMod_two hK
  have h1 := card_mul_le_card_inf_mul_card_sup U (V₁ K)
  have h2 := card_mul_le_card_inf_mul_card_sup U (V₂ K)
  rw [card_V₁_two hK] at h1
  rw [card_V₂_two hK] at h2
  have hs1 : Nat.card ↥(U ⊔ V₁ K) ≤ 2 ^ 6 := hV ▸ Subgroup.card_le_card_group _
  have hs2 : Nat.card ↥(U ⊔ V₂ K) ≤ 2 ^ 6 := hV ▸ Subgroup.card_le_card_group _
  constructor
  · by_contra h
    push Not at h
    have := Nat.mul_le_mul (Nat.le_of_lt_succ h) hs1
    omega
  · by_contra h
    push Not at h
    have := Nat.mul_le_mul (Nat.le_of_lt_succ h) hs2
    omega

omit [CharP K 2] in
theorem card_fixV_le_four (hK : Nat.card K = 2) {x : MulAut (StdMod (Fin 3) K)} (hx : x ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers x)) ≤ 4 := by
  have hne : fixV (Subgroup.zpowers x) ≠ ⊤ := by
    intro h
    apply hx
    refine MulEquiv.ext fun v => ?_
    rw [MulAut.one_apply]
    exact H.mem_fixV_zpowers_iff.mp (h ▸ Subgroup.mem_top v)
  have h1 := Subgroup.card_mul_index (fixV (Subgroup.zpowers x))
  rw [card_stdMod, hK, Fintype.card_fin] at h1
  have h2 : (fixV (Subgroup.zpowers x)).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
  have h3 : Nat.card ↥(fixV (Subgroup.zpowers x)) * 2 ≤
      Nat.card ↥(fixV (Subgroup.zpowers x)) * (fixV (Subgroup.zpowers x)).index := by
    have h0 : (fixV (Subgroup.zpowers x)).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    exact Nat.mul_le_mul_left _ (by omega)
  omega

theorem three_le_of_fix (hK : Nat.card K = 2) {p : MulAut (PairMod K)} (hpN : p ∈ pairNorm K)
    (hp1 : p ≠ 1) {U : Subgroup (PairMod K)} (hU : ∀ u ∈ U, p u = u)
    (hU16 : Nat.card U * 4 = 2 ^ 6) :
    3 ≤ Nat.card ↥(U ⊓ V₁ K) ∧ 3 ≤ Nat.card ↥(U ⊓ V₂ K) := by
  have hUfix : U ≤ fixV (Subgroup.zpowers p) := fun u hu =>
    H.mem_fixV_zpowers_iff.mpr (hU u hu)
  have hcardU : Nat.card U = 16 := by omega
  have h16 : 16 ≤ Nat.card ↥(fixV (Subgroup.zpowers p)) :=
    hcardU ▸ Subgroup.card_le_of_le hUfix
  have hpS : p ∈ pairSub K := by
    by_contra hpS
    obtain ⟨x, y, hxy⟩ := mem_pairSub_iff.mp ((mem_pairSub_or hpN).resolve_left hpS)
    have hp : p = swapAut K * pairAut x y := by
      rw [← hxy, ← mul_assoc, swapAut_mul_self, one_mul]
    have key : ∀ u : PairMod K, p u = u → u.1 = y u.2 := by
      intro u hu
      rw [hp, MulAut.mul_apply, pairAut_apply, swapAut_apply] at hu
      exact (congrArg Prod.fst hu).symm
    have hinj : Function.Injective
        (fun v : ↥(fixV (Subgroup.zpowers p)) => (v : PairMod K).2) := by
      intro v w h
      have h' : (v : PairMod K).2 = (w : PairMod K).2 := h
      apply Subtype.ext
      refine Prod.ext ?_ h'
      rw [key _ (H.mem_fixV_zpowers_iff.mp v.2), key _ (H.mem_fixV_zpowers_iff.mp w.2), h']
    have h8 := Nat.card_le_card_of_injective _ hinj
    rw [card_stdMod, hK, Fintype.card_fin] at h8
    omega
  obtain ⟨γ, -, rfl⟩ := mem_pairSL_of_mem_pairSub hK hpN hpS
  have hγ1 : γ ≠ 1 := fun h => hp1 (by rw [h, map_one])
  have hx1 : matAut γ ≠ 1 := fun h => hγ1 (matHom_injective (by rw [map_one, matHom_apply, h]))
  have hy1 : matAut (dualGL γ) ≠ 1 := fun h => hγ1 (by
    have h' : dualGL γ = 1 := matHom_injective (by rw [map_one, matHom_apply, h])
    rw [← dualGL_dualGL γ, h', ← dualHom_apply, map_one])
  have hF₁ := card_fixV_le_four hK hx1
  have hF₂ := card_fixV_le_four hK hy1
  have key : ∀ u : PairMod K, pairHom γ u = u →
      matAut γ u.1 = u.1 ∧ matAut (dualGL γ) u.2 = u.2 := by
    intro u hu
    rw [pairHom_apply, pairAut_apply] at hu
    exact ⟨congrArg Prod.fst hu, congrArg Prod.snd hu⟩
  have hprod : Nat.card ↥(fixV (Subgroup.zpowers (pairHom γ))) ≤
      Nat.card ↥(fixV (Subgroup.zpowers (matAut γ))) *
        Nat.card ↥(fixV (Subgroup.zpowers (matAut (dualGL γ)))) := by
    rw [← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun v => (⟨(v : PairMod K).1, ?_⟩, ⟨(v : PairMod K).2, ?_⟩)) ?_
    · exact H.mem_fixV_zpowers_iff.mpr (key _ (H.mem_fixV_zpowers_iff.mp v.2)).1
    · exact H.mem_fixV_zpowers_iff.mpr (key _ (H.mem_fixV_zpowers_iff.mp v.2)).2
    · intro v w h
      have h1 := congrArg (fun z => (z.1 : StdMod (Fin 3) K)) h
      have h2 := congrArg (fun z => (z.2 : StdMod (Fin 3) K)) h
      exact Subtype.ext (Prod.ext h1 h2)
  have hUeq : U = fixV (Subgroup.zpowers (pairHom γ)) := by
    refine Subgroup.eq_of_le_of_card_ge hUfix ?_
    have := Nat.mul_le_mul hF₁ hF₂
    omega
  have hpos : 4 ≤ Nat.card ↥(fixV (Subgroup.zpowers (matAut γ))) ∧
      4 ≤ Nat.card ↥(fixV (Subgroup.zpowers (matAut (dualGL γ)))) := by
    constructor
    · by_contra h
      push Not at h
      have := Nat.mul_le_mul (Nat.le_of_lt_succ h) hF₂
      omega
    · by_contra h
      push Not at h
      have := Nat.mul_le_mul hF₁ (Nat.le_of_lt_succ h)
      omega
  constructor
  · refine le_trans (by omega) (Nat.card_le_card_of_injective
      (fun v : ↥(fixV (Subgroup.zpowers (matAut γ))) =>
        (⟨((v : StdMod (Fin 3) K), 1), Subgroup.mem_inf.mpr ⟨?_, mem_V₁.mpr rfl⟩⟩ :
          ↥(U ⊓ V₁ K))) ?_)
    · rw [hUeq, H.mem_fixV_zpowers_iff, pairHom_apply, pairAut_apply,
        H.mem_fixV_zpowers_iff.mp v.2, map_one]
    · intro v w h
      exact Subtype.ext (congrArg (fun z : ↥(U ⊓ V₁ K) => (z : PairMod K).1) h)
  · refine le_trans (by omega) (Nat.card_le_card_of_injective
      (fun v : ↥(fixV (Subgroup.zpowers (matAut (dualGL γ)))) =>
        (⟨(1, (v : StdMod (Fin 3) K)), Subgroup.mem_inf.mpr ⟨?_, mem_V₂.mpr rfl⟩⟩ :
          ↥(U ⊓ V₂ K))) ?_)
    · rw [hUeq, H.mem_fixV_zpowers_iff, pairHom_apply, pairAut_apply,
        H.mem_fixV_zpowers_iff.mp v.2, map_one]
    · intro v w h
      exact Subtype.ext (congrArg (fun z : ↥(U ⊓ V₂ K) => (z : PairMod K).2) h)

theorem exists_order_three_le (hK : Nat.card K = 2) {U : Subgroup (PairMod K)}
    (h1 : 3 ≤ Nat.card ↥(U ⊓ V₁ K)) (h2 : 3 ≤ Nat.card ↥(U ⊓ V₂ K)) :
    ∃ θ ∈ StatedSL 3 K, pairHom θ ^ 3 = 1 ∧ pairHom θ ≠ 1 ∧
      ∀ x : PairMod K, pairHom θ x = x → x ∈ U := by
  obtain ⟨a, b, hab, ha, hb⟩ := exists_dot_eq_one_of_card hK h1 h2
  obtain ⟨θ, hθ, h3, hne, hfix⟩ := exists_order_three hK hab
  refine ⟨θ, hθ, h3, hne, fun x hx => ?_⟩
  obtain ⟨hx1, hx2⟩ := hfix x hx
  have hxe : x = (x.1, 1) * (1, x.2) := Prod.ext (mul_one _).symm (one_mul _).symm
  have hm1 : ((x.1, 1) : PairMod K) ∈ U := by
    rcases hx1 with h | h
    · have : x.1 = 1 := Multiplicative.toAdd.injective h
      rw [this]
      exact U.one_mem
    · have : x.1 = Multiplicative.ofAdd a := Multiplicative.toAdd.injective h
      rw [this]
      exact ha
  have hm2 : ((1, x.2) : PairMod K) ∈ U := by
    rcases hx2 with h | h
    · have : x.2 = 1 := Multiplicative.toAdd.injective h
      rw [this]
      exact U.one_mem
    · have : x.2 = Multiplicative.ofAdd b := Multiplicative.toAdd.injective h
      rw [this]
      exact hb
  rw [hxe]
  exact U.mul_mem hm1 hm2

theorem H4_SL3One_V0 {V : Type*} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : BinaryNaturalSL H V₁ ⊥ 3 1) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom)) {U : Subgroup V}
    (hU : Nat.card U * 2 = Nat.card V ∨ (Nat.card U * 4 = Nat.card V ∧
      ∃ p ∈ Subgroup.normalizer (H : Set (MulAut V)), p ≠ 1 ∧ ∀ u ∈ U, p u = u)) :
    ∃ θ ∈ H, θ ^ 3 = 1 ∧ θ ≠ 1 ∧ ∀ v : V, θ v = v → v ∈ U := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two le_rfl hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  obtain ⟨e, he⟩ := exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod K) := Finite.of_equiv V e.toEquiv
  have hcardV : Nat.card V = 2 ^ 6 := (Nat.card_congr e.toEquiv).trans (card_pairMod_two hK2)
  set U' := U.map e.toMonoidHom with hU'
  have hcardU' : Nat.card U' = Nat.card U :=
    Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective
  have hbounds : 3 ≤ Nat.card ↥(U' ⊓ SL3Pair.V₁ K) ∧ 3 ≤ Nat.card ↥(U' ⊓ V₂ K) := by
    rcases hU with h | ⟨h, p, hp, hp1, hpU⟩
    · exact three_le_of_hyperplane hK2 (by rw [hcardU', h, hcardV])
    · have hpN : congrHom e p ∈ pairNorm K := by
        have h3 : (Subgroup.normalizer (H : Set (MulAut V))).map (congrHom e) =
            Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut (PairMod K))) :
              Set (MulAut (PairMod K))) :=
          Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
        rw [pairNorm, ← he, ← h3]
        exact ⟨p, hp, rfl⟩
      have hpe1 : congrHom e p ≠ 1 := fun h' =>
        hp1 (congrHom_injective e (h'.trans (map_one _).symm))
      refine three_le_of_fix hK2 hpN hpe1 (fun u hu => ?_) (by rw [hcardU', h, hcardV])
      obtain ⟨v, hv, rfl⟩ := hu
      change e (p (e.symm (e v))) = e v
      rw [MulEquiv.symm_apply_apply, hpU v hv]
  obtain ⟨θ', hθ', h3, hne, hfix⟩ := exists_order_three_le hK2 hbounds.1 hbounds.2
  have hθ'H : pairHom θ' ∈ H.map (congrHom e) := by
    rw [he]
    exact ⟨θ', hθ', rfl⟩
  obtain ⟨θ, hθH, hθe⟩ := hθ'H
  refine ⟨θ, hθH, ?_, ?_, fun v hv => ?_⟩
  · apply congrHom_injective e
    rw [map_pow, hθe, h3, map_one]
  · intro h
    apply hne
    rw [← hθe, h, map_one]
  · have hx : pairHom θ' (e v) = e v := by
      rw [← hθe, congrHom_apply, MulEquiv.symm_apply_apply, hv]
    obtain ⟨u, hu, hue⟩ := hfix (e v) hx
    have : u = v := e.injective hue
    rw [← this]
    exact hu

end SL3One

end H

end CFSG.Quasithin
