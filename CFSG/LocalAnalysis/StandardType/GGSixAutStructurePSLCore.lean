module

public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSLFixed

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace AutPSL

section Lift

variable {n : ℕ} {K : Type*} [Field K] [Finite K] [CharP K 2]

theorem odd_card_scalars : Odd (Nat.card (scalars n K)) := by
  classical
  have : Fintype (scalars n K) := Fintype.ofFinite _
  by_contra h
  rw [Nat.not_odd_iff_even, even_iff_two_dvd, Nat.card_eq_fintype_card] at h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 h
  obtain ⟨c, -, hc⟩ := x.2
  have hpow : x ^ Nat.card Kˣ = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((x : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ Nat.card Kˣ = 1
    rw [hc, ← map_pow (Matrix.scalar (Fin n)), ← Units.val_pow_eq_pow_val, pow_card_eq_one',
      Units.val_one, map_one]
  have hdvd := orderOf_dvd_of_pow_eq_one hpow
  rw [hx] at hdvd
  exact (Nat.not_even_iff_odd.mpr odd_card_units) (even_iff_two_dvd.mpr hdvd)

theorem eq_one_of_mem_scalars_of_pow {z : SpecialLinearGroup (Fin n) K} (hz : z ∈ scalars n K)
    {a : ℕ} (ha : z ^ 2 ^ a = 1) : z = 1 := by
  have h1 : orderOf z ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf z ∣ Nat.card (scalars n K) := Subgroup.orderOf_dvd_natCard _ hz
  have hcop : Nat.Coprime (2 ^ a) (Nat.card (scalars n K)) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr odd_card_scalars)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_lift (Q : Subgroup (projectiveSL n K)) (hQ : IsPGroup 2 Q) :
    ∃ S : Subgroup (SpecialLinearGroup (Fin n) K), IsPGroup 2 S ∧
      S.map (proj n K) = Q ∧ S ⊓ scalars n K = ⊥ ∧
      ∀ x : SpecialLinearGroup (Fin n) K, proj n K x ∈ Q → (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := scalars n K
  set Qt := Q.comap (proj n K)
  have hZQt : Z ≤ Qt := fun z hz => by
    change proj n K z ∈ Q
    rw [proj_eq_one_iff.mpr hz]
    exact Q.one_mem
  have hcardQt : Nat.card (Z.subgroupOf Qt) * Nat.card Q = Nat.card Qt := by
    set g : Qt →* projectiveSL n K := (proj n K).comp Qt.subtype
    have hgk : g.ker = Z.subgroupOf Qt := by
      ext a
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      exact proj_eq_one_iff
    have hgr : g.range = Q := by
      ext e
      constructor
      · rintro ⟨a, rfl⟩
        exact a.2
      · intro he
        obtain ⟨A, rfl⟩ := proj_surjective n K e
        exact ⟨⟨A, he⟩, rfl⟩
    rw [← Subgroup.card_ker_mul_card_range g, hgk, hgr]
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have hdvd : 2 ^ k ∣ Nat.card Qt := ⟨Nat.card (Z.subgroupOf Qt), by rw [← hcardQt, hk, mul_comm]⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  set S := H.map Qt.subtype
  have hScard : Nat.card S = 2 ^ k := by
    rw [Subgroup.card_map_of_injective Qt.subtype_injective, hH]
  have hS2 : IsPGroup 2 S := IsPGroup.of_card hScard
  have hSQt : S ≤ Qt := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hSZ : S ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxS, hxZ⟩
    have hx : x ^ 2 ^ k = 1 := by
      rw [← hScard]
      have := pow_card_eq_one' (G := S) (x := ⟨x, hxS⟩)
      exact congrArg Subtype.val this
    rw [Subgroup.mem_bot]
    exact eq_one_of_mem_scalars_of_pow hxZ hx
  have hSQ : S.map (proj n K) = Q := by
    have hinj : Function.Injective ((proj n K).comp S.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro a ha
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, proj_eq_one_iff] at ha
      have h : (a : SpecialLinearGroup (Fin n) K) ∈ S ⊓ Z := ⟨a.2, ha⟩
      rw [hSZ, Subgroup.mem_bot] at h
      rw [Subgroup.mem_bot]
      exact Subtype.ext h
    have hrange : ((proj n K).comp S.subtype).range = S.map (proj n K) := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hSQt hx
    · rw [hk, ← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hScard]
  refine ⟨S, hS2, hSQ, hSZ, fun x hxQ ⟨a, ha⟩ => ?_⟩
  rw [← hSQ] at hxQ
  obtain ⟨s, hsS, hs⟩ := hxQ
  have hz : s⁻¹ * x ∈ Z := proj_eq_proj_iff.mp hs
  have hzc : s⁻¹ * x ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
    rw [← scalars_eq_center]
    exact hz
  have hcomm : Commute s⁻¹ x := by
    have hz' := Subgroup.mem_center_iff.mp hzc s
    change s⁻¹ * x = x * s⁻¹
    calc s⁻¹ * x = (s⁻¹ * x) * s * s⁻¹ := by group
      _ = s * (s⁻¹ * x) * s⁻¹ := by rw [← hz']
      _ = x * s⁻¹ := by group
  have hsk : s ^ 2 ^ k = 1 := by
    rw [← hScard]
    have := pow_card_eq_one' (G := S) (x := ⟨s, hsS⟩)
    exact congrArg Subtype.val this
  have hz1 : (s⁻¹ * x) ^ 2 ^ (a + k) = 1 := by
    rw [hcomm.mul_pow, inv_pow, pow_add, pow_mul, pow_mul, ha, one_pow, mul_one, ← pow_mul,
      mul_comm, pow_mul, hsk, one_pow, inv_one]
  have hone := eq_one_of_mem_scalars_of_pow hz hz1
  rw [← inv_mul_eq_one.mp hone]
  exact hsS

omit [Finite K] [CharP K 2] in
theorem conj_mem_lift {Q : Subgroup (projectiveSL n K)}
    {S : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hS2 : IsPGroup 2 S) (hSQ : S.map (proj n K) = Q)
    (hS : ∀ x : SpecialLinearGroup (Fin n) K, proj n K x ∈ Q → (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ S)
    {y : SpecialLinearGroup (Fin n) K}
    (hy : ∀ q ∈ Q, proj n K y * q * (proj n K y)⁻¹ ∈ Q) {s : SpecialLinearGroup (Fin n) K}
    (hs : s ∈ S) : y * s * y⁻¹ ∈ S := by
  refine hS _ ?_ ?_
  · rw [map_mul, map_mul, map_inv]
    exact hy _ (hSQ ▸ ⟨s, hs, rfl⟩)
  · obtain ⟨k, hk⟩ := hS2 ⟨s, hs⟩
    refine ⟨k, ?_⟩
    have hk' : s ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [conj_pow, hk', mul_one, mul_inv_cancel]

end Lift

section Fix

variable {n : ℕ} {K : Type*} [Field K]

@[expose] def fixVec (S : Subgroup (SpecialLinearGroup (Fin n) K)) : Submodule K (Fin n → K) where
  carrier := {v | ∀ s ∈ S, ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  add_mem' := by
    intro v w hv hw s hs
    rw [Matrix.mulVec_add, hv s hs, hw s hs]
  zero_mem' := fun s _ => Matrix.mulVec_zero _
  smul_mem' := by
    intro c v hv s hs
    rw [Matrix.mulVec_smul, hv s hs]

theorem mem_fixVec {S : Subgroup (SpecialLinearGroup (Fin n) K)} {v : Fin n → K} :
    v ∈ fixVec S ↔
      ∀ s ∈ S, ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
  Iff.rfl

theorem mulVec_mem_fixVec {S : Subgroup (SpecialLinearGroup (Fin n) K)}
    {y : SpecialLinearGroup (Fin n) K} (hy : ∀ s ∈ S, y⁻¹ * s * y ∈ S) {v : Fin n → K}
    (hv : v ∈ fixVec S) : ((y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈
      fixVec S := by
  intro s hs
  have h := hv _ (hy s hs)
  have hyy : ((y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((y⁻¹ * s * y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      (s : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) := by
    change ((y * (y⁻¹ * s * y) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((s * y : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [show y * (y⁻¹ * s * y) = s * y by group]
  rw [Matrix.mulVec_mulVec, ← hyy, ← Matrix.mulVec_mulVec, h]

theorem exists_ne_zero_mem_fixVec [Finite K] [CharP K 2]
    {S : Subgroup (SpecialLinearGroup (Fin n) K)}
    (hS : IsPGroup 2 S) (U : Submodule K (Fin n → K))
    (hU : ∀ s ∈ S, ∀ u ∈ U,
      ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ u ∈ U)
    {u₀ : Fin n → K} (hu₀ : u₀ ∈ U) (hu₀0 : u₀ ≠ 0) :
    ∃ u ∈ U, u ≠ 0 ∧ u ∈ fixVec S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : MulAction S U :=
    { smul := fun s u => ⟨((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        (u : Fin n → K), hU s s.2 u u.2⟩
      one_smul := fun u => Subtype.ext (Matrix.one_mulVec _)
      mul_smul := fun s t u => Subtype.ext (by
        change (((s * t : S) : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          (u : Fin n → K) = ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
            (((t : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (u : Fin n → K))
        rw [Matrix.mulVec_mulVec]
        rfl) }
  have h2 : 2 ∣ Nat.card U := by
    have hord : addOrderOf (⟨u₀, hu₀⟩ : U) = 2 := by
      refine addOrderOf_eq_prime ?_ ?_
      · apply Subtype.ext
        change (2 : ℕ) • u₀ = 0
        rw [two_nsmul]
        funext i
        exact CharTwo.add_self_eq_zero (u₀ i)
      · intro h
        exact hu₀0 (congrArg Subtype.val h)
    exact hord ▸ addOrderOf_dvd_natCard _
  have h0 : (0 : U) ∈ MulAction.fixedPoints S U := fun s => Subtype.ext (by
    change ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (0 : Fin n → K) = 0
    exact Matrix.mulVec_zero _)
  obtain ⟨b, hb, hne⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point U h2 h0
  refine ⟨b, b.2, fun h => hne (Subtype.ext h.symm), fun s hs => ?_⟩
  exact congrArg Subtype.val (hb ⟨s, hs⟩)

theorem eq_bot_of_forall_single_mem {S : Subgroup (SpecialLinearGroup (Fin n) K)}
    (h : ∀ i, Pi.single i (1 : K) ∈ fixVec S) : S = ⊥ := by
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  change ((s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1
  ext i j
  have := congrFun (h j s hs) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [this, Matrix.one_apply, Pi.single_apply]

theorem single_mem_of_transvection {W : Submodule K (Fin n → K)} {a b : Fin n} (hab : a ≠ b)
    (hT : ∀ w ∈ W, ((SpecialLinearGroup.transvection hab (1 : K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    {w : Fin n → K} (hw : w ∈ W) (hwb : w b ≠ 0) : Pi.single a (1 : K) ∈ W := by
  have h := W.sub_mem (hT w hw) hw
  rw [transvection_mulVec, add_sub_cancel_left, one_mul] at h
  have h2 := W.smul_mem (w b)⁻¹ h
  rwa [← Pi.single_smul', smul_eq_mul, inv_mul_cancel₀ hwb] at h2

theorem single_mem_of_pair {W : Submodule K (Fin n → K)} {a b c d : Fin n} (hba : b ≠ a)
    (hcd : c ≠ d) (hda : d ≠ a)
    (hY : ∀ w ∈ W, ((SpecialLinearGroup.transvection hba (1 : K) *
      SpecialLinearGroup.transvection hcd (1 : K) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W)
    (ha : Pi.single a (1 : K) ∈ W) : Pi.single b (1 : K) ∈ W := by
  have h := W.sub_mem (hY _ ha) ha
  have e : ((SpecialLinearGroup.transvection hba (1 : K) *
      SpecialLinearGroup.transvection hcd (1 : K) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) *ᵥ Pi.single a 1 = Pi.single a 1 + Pi.single b 1 := by
    change (((SpecialLinearGroup.transvection hba (1 : K) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * ((SpecialLinearGroup.transvection hcd (1 : K) :
        SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ Pi.single a 1 = _
    rw [← Matrix.mulVec_mulVec, transvection_mulVec, transvection_mulVec]
    simp [hda]
  rwa [e, add_sub_cancel_left] at h

end Fix

end AutPSL

end CFSG.StandardType
