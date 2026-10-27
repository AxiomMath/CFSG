module

public import CFSG.Quasithin.Background.F6Examples
public import CFSG.Quasithin.EmptyFaithful.S146A0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

private def d3FunG : DihedralGroup 3 → Equiv.Perm (Fin 3)
  | DihedralGroup.r i => Equiv.subRight (i : Fin 3)
  | DihedralGroup.sr i => Equiv.subLeft (i : Fin 3)

private def d3HomG : DihedralGroup 3 →* Equiv.Perm (Fin 3) where
  toFun := d3FunG
  map_one' := by decide
  map_mul' := by decide

theorem nonempty_dihedral_three_equiv_perm : Nonempty (DihedralGroup 3 ≃* Equiv.Perm (Fin 3)) :=
  ⟨MulEquiv.ofBijective d3HomG (by constructor <;> decide)⟩

section Quotient

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_pow_mem_of_mem_sup_two {H₂ T₀ : Subgroup G} (hT₀ : IsPGroup 2 T₀)
    (hT₀H₂ : T₀ ≤ Subgroup.normalizer (H₂ : Set G)) {x : G} (hx : x ∈ H₂ ⊔ T₀) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ H₂ := by
  have hx' : x ∈ ((H₂ ⊔ T₀ : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left H₂ T₀ hT₀H₂] at hx'
  obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hx'
  obtain ⟨j, hj⟩ := hT₀ ⟨b, hb⟩
  have hj' : b ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨y', hy', hpow⟩ := A4.exists_pow_mul_eq hy (hT₀H₂ hb) (2 ^ j)
  exact ⟨j, by rw [hpow, hj', mul_one]; exact hy'⟩

theorem oTwoQuot_sup_equiv_perm {H₁ H₂ T₀ Q : Subgroup G}
    (hH₂H₁ : H₂ ≤ Subgroup.normalizer (H₁ : Set G))
    (hT₀H₁ : T₀ ≤ Subgroup.normalizer (H₁ : Set G))
    (hT₀H₂ : T₀ ≤ Subgroup.normalizer (H₂ : Set G))
    (hT₀ : IsPGroup 2 T₀) (hT₀sup : T₀ ≤ H₁ ⊔ H₂)
    (hinf : H₁ ⊓ H₂ = Q) (hQ : IsPGroup 2 Q) (hdih : SecIso H₂ Q (DihedralGroup 3)) :
    Nonempty (OTwoQuot (H₂ ⊔ T₀) ≃* Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨hQn, ⟨e₂⟩⟩ := hdih
  obtain ⟨eD⟩ := nonempty_dihedral_three_equiv_perm
  set X : Subgroup G := H₂ ⊔ T₀ with hXdef
  have hH₂X : H₂ ≤ X := le_sup_left
  have hXH₁ : X ≤ Subgroup.normalizer (H₁ : Set G) := sup_le hH₂H₁ hT₀H₁
  have hN₁ : (H₁.subgroupOf X).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hXH₁ g.2) (n : G)).mp hn
    simpa using this⟩
  set Q₀ := ↥X ⧸ H₁.subgroupOf X with hQ₀
  set ψ : ↥X →* Q₀ := QuotientGroup.mk' (H₁.subgroupOf X) with hψ
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  set Φ : ↥H₂ →* Q₀ := ψ.comp (Subgroup.inclusion hH₂X) with hΦ
  have hΦker : Φ.ker = Q.subgroupOf H₂ := by
    ext x
    rw [MonoidHom.mem_ker, hΦ, MonoidHom.comp_apply, hψ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, ← hinf,
      Subgroup.mem_inf]
    simp only [Subgroup.coe_inclusion]
    exact ⟨fun h => ⟨h, x.2⟩, fun h => h.1⟩
  have hΦs : Function.Surjective Φ := by
    intro q
    obtain ⟨x, rfl⟩ := hψs q
    have hx' : (x : G) ∈ ((H₂ ⊔ T₀ : Subgroup G) : Set G) := x.2
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H₂ T₀ hT₀H₂] at hx'
    obtain ⟨h₂, hh₂, y, hy, hxy⟩ := Set.mem_mul.mp hx'
    have hy' : y ∈ ((H₁ ⊔ H₂ : Subgroup G) : Set G) := hT₀sup hy
    rw [Subgroup.coe_mul_of_right_le_normalizer_left H₁ H₂ hH₂H₁] at hy'
    obtain ⟨a, ha, b, hb, hyab⟩ := Set.mem_mul.mp hy'
    refine ⟨⟨h₂ * b, H₂.mul_mem hh₂ hb⟩, ?_⟩
    rw [hΦ, MonoidHom.comp_apply, hψ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hxeq : (x : G) = (h₂ * a * h₂⁻¹) * (h₂ * b) := by
      rw [← hxy, ← hyab]; group
    have hnorm : h₂ ∈ Subgroup.normalizer (H₁ : Set G) := hH₂H₁ hh₂
    have hnorm2 : h₂ * b ∈ Subgroup.normalizer (H₁ : Set G) := hH₂H₁ (H₂.mul_mem hh₂ hb)
    have h1 : h₂ * a * h₂⁻¹ ∈ H₁ := (Subgroup.mem_normalizer_iff.mp hnorm a).mp ha
    change (h₂ * b)⁻¹ * (x : G) ∈ H₁
    have h2 : (h₂ * b)⁻¹ * (x : G) = (h₂ * b)⁻¹ * (h₂ * a * h₂⁻¹) * (h₂ * b)⁻¹⁻¹ := by
      rw [hxeq]; group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnorm2) _).mp h1
  let e₁ : (↥H₂ ⧸ Q.subgroupOf H₂) ≃* Q₀ :=
    (QuotientGroup.quotientMulEquivOfEq hΦker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective Φ hΦs)
  let eQ : Q₀ ≃* Equiv.Perm (Fin 3) := (e₁.symm.trans e₂).trans eD
  have hker : CFSG.Open.pCore 2 ↥X = H₁.subgroupOf X := by
    refine le_antisymm ?_ ?_
    ·
      set N := CFSG.Open.pCore 2 ↥X with hN
      have hNn : N.Normal := CFSG.LieType.BorelTits.pCore_normal 2
      have hNp : IsPGroup 2 N := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact CFSG.LieType.BorelTits.pCore_isPGroup 2
      have hmapn : (N.map ψ).Normal := Subgroup.Normal.map hNn ψ hψs
      have hmapp : IsPGroup 2 ↥(N.map ψ) := hNp.map ψ
      have hmapn' : ((N.map ψ).map eQ.toMonoidHom).Normal :=
        Subgroup.Normal.map hmapn eQ.toMonoidHom eQ.surjective
      have hmapp' : IsPGroup 2 ↥((N.map ψ).map eQ.toMonoidHom) := hmapp.map eQ.toMonoidHom
      have hle : (N.map ψ).map eQ.toMonoidHom ≤ CFSG.Open.pCore 2 (Equiv.Perm (Fin 3)) :=
        le_pCore 2 hmapn' hmapp'
      rw [F6.pCore_perm_three_eq_bot, le_bot_iff] at hle
      intro n hn
      have h1 : eQ (ψ n) ∈ (N.map ψ).map eQ.toMonoidHom :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem ψ hn)
      rw [hle, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at h1
      rw [hψ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    ·
      refine le_pCore 2 hN₁ ?_
      intro n
      have hn1 : (n : G) ∈ H₁ := Subgroup.mem_subgroupOf.mp n.2
      obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup_two hT₀ hT₀H₂ (x := ((n : ↥X) : G)) n.1.2
      have hk1 : ((n : ↥X) : G) ^ 2 ^ k ∈ H₁ := H₁.pow_mem hn1 _
      have hkQ : ((n : ↥X) : G) ^ 2 ^ k ∈ Q := by rw [← hinf]; exact ⟨hk1, hk⟩
      obtain ⟨a, ha⟩ := hQ ⟨_, hkQ⟩
      refine ⟨k + a, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg Subtype.val ha
      simpa [pow_add, pow_mul] using this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans eQ⟩

end Quotient

end CFSG.Quasithin
