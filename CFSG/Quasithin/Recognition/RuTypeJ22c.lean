module

public import CFSG.Quasithin.Recognition.RuTypeJ22b

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G]

theorem conj_mem_of_pow_eq_one [Finite G] {C U : Subgroup G} {b : G} {n : ℕ}
    (hbn : b ^ n = 1) (hcop : Nat.Coprime n (U.relIndex C).factorial)
    (hbC : ∀ x ∈ C, b * x * b⁻¹ ∈ C) (hbC' : ∀ x ∈ C, b⁻¹ * x * b ∈ C)
    (hbU : ∀ x ∈ U, b * x * b⁻¹ ∈ U) (hbU' : ∀ x ∈ U, b⁻¹ * x * b ∈ U)
    (hUn : (U.subgroupOf C).Normal) : ∀ x ∈ C, x⁻¹ * (b * x * b⁻¹) ∈ U := by
  let e : C ≃* C :=
    { toFun := fun x => ⟨b * x * b⁻¹, hbC x x.2⟩
      invFun := fun x => ⟨b⁻¹ * x * b, hbC' x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  have he : (U.subgroupOf C).map (e : C →* C) = U.subgroupOf C := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (hbU x (Subgroup.mem_subgroupOf.mp hx))
    · intro hy
      refine ⟨⟨b⁻¹ * y * b, hbC' y y.2⟩,
        Subgroup.mem_subgroupOf.mpr (hbU' y (Subgroup.mem_subgroupOf.mp hy)), ?_⟩
      exact Subtype.ext (by simp [e, mul_assoc])
  let σ : Equiv.Perm (C ⧸ U.subgroupOf C) := (QuotientGroup.congr _ _ e he).toEquiv
  have hσ : ∀ (k : ℕ) (x : C), (σ ^ k) (QuotientGroup.mk x) =
      QuotientGroup.mk ⟨b ^ k * x * (b ^ k)⁻¹, by
        induction k with
        | zero => simp
        | succ k ih =>
          have := hbC _ ih
          simpa [pow_succ', mul_assoc] using this⟩ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      simp only [σ, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
      rw [QuotientGroup.congr_mk]
      congr 1
      exact Subtype.ext (by simp [e, pow_succ', mul_assoc])
  have hσn : σ ^ n = 1 := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [hσ, Equiv.Perm.one_apply]
      congr 1
      exact Subtype.ext (by simp [hbn])
  have hσ1 : σ = 1 := by
    have h1 : orderOf σ ∣ n := orderOf_dvd_of_pow_eq_one hσn
    have h2 : orderOf σ ∣ (U.relIndex C).factorial := by
      have := orderOf_dvd_natCard σ
      have hc : Nat.card (C ⧸ U.subgroupOf C) = U.relIndex C := rfl
      rwa [Nat.card_perm, hc] at this
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2
    rwa [orderOf_eq_one_iff] at this
  intro x hx
  have := hσ 1 ⟨x, hx⟩
  rw [hσ1, pow_one, Equiv.Perm.one_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf] at this
  simpa using this

namespace RuDataN

variable (N : RuDataN G)

abbrev K : Subgroup G :=
  ((SemidirectProduct.inl : SL(2, F4) →* SigmaL2F4).range.comap N.φ).map (ruH N.T).subtype

theorem mem_K_iff {k : G} : k ∈ N.K ↔ ∃ hk : k ∈ ruH N.T, (N.φ ⟨k, hk⟩).right = 1 := by
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨A, hA⟩, rfl⟩
    refine ⟨hk, ?_⟩
    simp only [Subgroup.coe_subtype]
    rw [← hA]
    rfl
  · rintro ⟨hk, h1⟩
    refine ⟨⟨k, hk⟩, ⟨(N.φ ⟨k, hk⟩).left, ?_⟩, rfl⟩
    ext
    · rfl
    · exact h1.symm

theorem K_le_H : N.K ≤ ruH N.T := Subgroup.map_subtype_le _

variable [Finite G]

theorem exists_lift_pow_five {X : SigmaL2F4} (hX : X ^ 5 = 1) :
    ∃ c : ruH N.T, N.φ c = X ∧ (c : G) ^ 5 = 1 := by
  obtain ⟨c₀, hc₀⟩ := N.φ_surj X
  have hc5 : c₀ ^ 5 ∈ N.φ.ker := by rw [MonoidHom.mem_ker, map_pow, hc₀, hX]
  rw [N.φ_ker, Subgroup.mem_subgroupOf] at hc5
  have hQ : ((c₀ : G) ^ 5) ^ (2 ^ 11) = 1 := by
    have h := orderOf_dvd_natCard (⟨_, hc5⟩ : ruQ N.T)
    rw [N.toRuData.card_Q] at h
    have := orderOf_dvd_iff_pow_eq_one.mp h
    simpa using congrArg Subtype.val this
  refine ⟨c₀ ^ (2 ^ 12), ?_, ?_⟩
  · rw [map_pow, hc₀]
    have : (2 : ℕ) ^ 12 = 5 * 819 + 1 := by norm_num
    rw [this, pow_succ, pow_mul, hX, one_pow, one_mul]
  · simp only [Subgroup.coe_pow]
    rw [← pow_mul, show 2 ^ 12 * 5 = 5 * 2 ^ 11 * 2 by norm_num, pow_mul, pow_mul, hQ, one_pow]

theorem relIndex_U_HC : (ruU N.L N.T).relIndex N.HC = 4 := by
  have h := Subgroup.relIndex_mul_card (ruU N.L N.T) N.HC
  rw [inf_eq_left.mpr N.U_le_HC, N.card_HC, N.toRuData.card_U] at h
  omega

omit [Finite G] in
theorem conj_mem_HC {h x : G} (hh : h ∈ ruH N.T) (hx : x ∈ N.HC) : h * x * h⁻¹ ∈ N.HC := by
  obtain ⟨hxH, hxc⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hh hxH) (inv_mem hh),
    Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
  have hu' : h⁻¹ * u * h ∈ ruU N.L N.T := by
    have := N.conj_mem_U (inv_mem hh) hu
    simpa using this
  have := Subgroup.mem_centralizer_iff.mp hxc _ hu'
  calc u * (h * x * h⁻¹) = h * ((h⁻¹ * u * h) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * u * h)) * h⁻¹ := by rw [this]
    _ = h * x * h⁻¹ * u := by group

theorem comm_HC_of_pow_five {b : G} (hb : b ∈ ruH N.T) (hb5 : b ^ 5 = 1) :
    ∀ x ∈ N.HC, b * x * b⁻¹ * x⁻¹ ∈ ruU N.L N.T := by
  intro x hx
  have h := conj_mem_of_pow_eq_one hb5 (by rw [N.relIndex_U_HC]; decide)
    (fun y hy => N.conj_mem_HC hb hy) (fun y hy => by simpa using N.conj_mem_HC (inv_mem hb) hy)
    (fun y hy => N.conj_mem_U hb hy) (fun y hy => by simpa using N.conj_mem_U (inv_mem hb) hy)
    ⟨fun y hy g => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact N.conj_mem_U (Subgroup.mem_inf.mp g.2).1 hy⟩ x hx
  have e : b * x * b⁻¹ * x⁻¹ = x * (x⁻¹ * (b * x * b⁻¹)) * x⁻¹ := by group
  rw [e]
  exact N.conj_mem_U (Subgroup.mem_inf.mp hx).1 h

@[expose] def kerHC : Subgroup G where
  carrier := {h | h ∈ ruH N.T ∧ ∀ x ∈ N.HC, h * x * h⁻¹ * x⁻¹ ∈ ruU N.L N.T}
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨mul_mem ha hb, fun x hx => ?_⟩
    have e : a * b * x * (a * b)⁻¹ * x⁻¹ =
        (a * (b * x * b⁻¹ * x⁻¹) * a⁻¹) * (a * x * a⁻¹ * x⁻¹) := by group
    rw [e]
    exact mul_mem (N.conj_mem_U ha (hbx x hx)) (hax x hx)
  inv_mem' := by
    rintro a ⟨ha, hax⟩
    refine ⟨inv_mem ha, fun x hx => ?_⟩
    have e : a⁻¹ * x * a⁻¹⁻¹ * x⁻¹ = a⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [e]
    exact N.conj_mem_U (inv_mem ha) (inv_mem (hax x hx))

theorem comm_K_HC {k : G} (hk : k ∈ N.K) : ∀ x ∈ N.HC, k * x * k⁻¹ * x⁻¹ ∈ ruU N.L N.T := by
  suffices k ∈ N.kerHC from this.2
  obtain ⟨hkH, hk1⟩ := N.mem_K_iff.mp hk
  set A := (N.φ ⟨k, hkH⟩).left
  have hφk : N.φ ⟨k, hkH⟩ = SemidirectProduct.inl A := by
    ext
    · rfl
    · exact hk1
  obtain ⟨C, hC5, hD5⟩ := Sigma.exists_mul_pow_five A
  obtain ⟨c, hc, hc5⟩ := N.exists_lift_pow_five (X := SemidirectProduct.inl C)
    (by rw [← map_pow, hC5, map_one])
  obtain ⟨d, hd, hd5⟩ := N.exists_lift_pow_five (X := SemidirectProduct.inl (C⁻¹ * A))
    (by rw [← map_pow, hD5, map_one])
  have hq : (c * d)⁻¹ * ⟨k, hkH⟩ ∈ N.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, hc, hd, hφk, ← map_mul, mul_inv_cancel_left,
      inv_mul_cancel]
  rw [N.φ_ker, Subgroup.mem_subgroupOf] at hq
  have hkeq : k = c * d * (((c * d)⁻¹ * ⟨k, hkH⟩ : ruH N.T) : G) := by simp; group
  rw [hkeq]
  refine mul_mem (mul_mem ⟨c.2, N.comm_HC_of_pow_five c.2 hc5⟩ ⟨d.2, N.comm_HC_of_pow_five d.2 hd5⟩)
    ⟨pCoreOf_le 2 _ hq, fun x hx => (N.two.QU_elem _ hq x (N.HC_le_Q hx)).1⟩

theorem comm_K_mem_U_iff {q : G} (hq : q ∈ ruQ N.T) :
    (∀ k ∈ N.K, k * q * k⁻¹ * q⁻¹ ∈ ruU N.L N.T) ↔ q ∈ N.HC := by
  constructor
  · intro h
    by_contra hqC
    have hne : Multiplicative.toAdd (N.ψQ ⟨q, hq⟩) ≠ 0 := by
      intro h0
      apply hqC
      have : (⟨q, hq⟩ : ruQ N.T) ∈ N.ψQ.ker :=
        Multiplicative.toAdd.injective (by rw [h0, toAdd_one])
      rw [N.ψQ_ker, Subgroup.mem_subgroupOf] at this
      exact this
    obtain ⟨A, hA⟩ := Sigma.exists_sl_smul_ne _ hne
    apply hA
    obtain ⟨⟨k, hkH⟩, hk⟩ := N.φ_surj (SemidirectProduct.inl A)
    have hkK : k ∈ N.K := N.mem_K_iff.mpr ⟨hkH, by rw [hk]; rfl⟩
    have hmem : k * q * k⁻¹ * q⁻¹ ∈ N.HC := N.U_le_HC (h k hkK)
    have hmemQ : k * q * k⁻¹ ∈ ruQ N.T := N.conj_mem_Q hkH hq
    have e1 : N.ψQ ⟨k * q * k⁻¹, hmemQ⟩ = N.ψQ ⟨q, hq⟩ := by
      have : (⟨k * q * k⁻¹, hmemQ⟩ : ruQ N.T) * (⟨q, hq⟩ : ruQ N.T)⁻¹ ∈ N.ψQ.ker := by
        rw [N.ψQ_ker, Subgroup.mem_subgroupOf]
        exact hmem
      rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at this
      exact this
    have e2 := N.ψQ_conj ⟨k, hkH⟩ ⟨q, hq⟩
    simp only at e2
    rw [e1, hk, Sigma.sigmaAct_inl] at e2
    exact e2.symm
  · intro hqC k hk
    have := N.comm_K_HC hk q hqC
    exact this

end RuDataN

end CFSG.Quasithin.RuType
