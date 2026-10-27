module

public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma43KFacts
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21

section TwoEl

variable {M : Type*} [Group M]

theorem Is2El.map {N : Type*} [Group N] (f : M →* N) {x : M} (hx : Is2El x) : Is2El (f x) := by
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, by rw [← map_pow, hm, map_one]⟩

theorem Is2El.of_pow {x : M} (hx : Is2El x) (k : ℕ) : Is2El (x ^ k) := by
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, by rw [← pow_mul, mul_comm, pow_mul, hm, one_pow]⟩

theorem Is2El.inv {x : M} (hx : Is2El x) : Is2El x⁻¹ := by
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, by rw [inv_pow, hm, inv_one]⟩

theorem Is2El.mul {x y : M} (h : Commute x y) (hx : Is2El x) (hy : Is2El y) : Is2El (x * y) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  refine ⟨m + n, ?_⟩
  rw [h.mul_pow]
  have h1 : x ^ 2 ^ (m + n) = 1 := by
    rw [pow_add, pow_mul, hm, one_pow]
  have h2 : y ^ 2 ^ (m + n) = 1 := by
    rw [add_comm, pow_add, pow_mul, hn, one_pow]
  rw [h1, h2, one_mul]

theorem Is2El.of_mem_pGroup {Q : Subgroup M} (hQ : IsPGroup 2 Q) {x : M} (hx : x ∈ Q) :
    Is2El x := by
  obtain ⟨m, hm⟩ := hQ ⟨x, hx⟩
  exact ⟨m, congrArg Subtype.val hm⟩

theorem Is2El.eq_one_of_pow_odd {x : M} (hx : Is2El x) {n : ℕ} (hn : Odd n) (h : x ^ n = 1) :
    x = 1 := by
  obtain ⟨m, hm⟩ := hx
  have := pow_gcd_eq_one.mpr ⟨hm, h⟩
  rwa [(Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hn)), pow_one] at this

theorem Is2El.eq_one_of_odd_card {C : Subgroup M} (hC : Odd (Nat.card C)) {x : M} (hxC : x ∈ C)
    (hx : Is2El x) : x = 1 := by
  refine hx.eq_one_of_pow_odd hC ?_
  have := pow_card_eq_one' (x := (⟨x, hxC⟩ : C))
  exact congrArg Subtype.val this

end TwoEl

section NormAut

variable {G : Type} [Group G]

noncomputable def normAut (H : Subgroup G) {M : Type*} [Group M] (e : H ≃* M) :
    Nor H →* MulAut M :=
  (MulAut.congr e).toMonoidHom.comp
    ((MulAut.congr (Subgroup.subgroupOfEquivOfLe
      (Subgroup.le_normalizer (H := H)))).toMonoidHom.comp
      (@MulAut.conjNormal (Nor H) _ (H.subgroupOf (Nor H)) Subgroup.normal_in_normalizer))

theorem normAut_apply (H : Subgroup G) {M : Type*} [Group M] (e : H ≃* M) (g : Nor H) (m : M) :
    ((e.symm (normAut H e g m) : H) : G) = (g : G) * (e.symm m : G) * (g : G)⁻¹ := by
  simp [normAut, MulAut.congr_apply, MulAut.conjNormal_apply]

theorem normAut_eq_self_iff (H : Subgroup G) {M : Type*} [Group M] (e : H ≃* M) (g : Nor H)
    (x : H) : normAut H e g (e x) = e x ↔ (g : G) * x * (g : G)⁻¹ = x := by
  rw [← e.symm.injective.eq_iff, MulEquiv.symm_apply_apply, ← Subtype.coe_inj,
    normAut_apply, MulEquiv.symm_apply_apply]

theorem normAut_eq_one_iff (H : Subgroup G) {M : Type*} [Group M] (e : H ≃* M) (g : Nor H) :
    normAut H e g = 1 ↔ ∀ x ∈ H, (g : G) * x * (g : G)⁻¹ = x := by
  constructor
  · intro h x hx
    have := (normAut_eq_self_iff H e g ⟨x, hx⟩).mp (by rw [h]; rfl)
    exact this
  · intro h
    refine MulEquiv.ext fun m => ?_
    obtain ⟨x, rfl⟩ := e.surjective m
    exact (normAut_eq_self_iff H e g x).mpr (h x x.2)

theorem normAut_of_mem (H : Subgroup G) {M : Type*} [Group M] (e : H ≃* M) (s : H) :
    normAut H e ⟨(s : G), Subgroup.le_normalizer s.2⟩ = MulAut.conj (e s) := by
  refine MulEquiv.ext fun m => ?_
  rw [← e.symm.injective.eq_iff, ← Subtype.coe_inj, normAut_apply]
  simp [MulAut.conj_apply]

end NormAut

section Good

variable {G : Type} [Group G]

@[expose] def Good43 (σ x : G) : Prop :=
  ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≤ Cen x ⊓ Cen σ →
    (∀ c ∈ Cen x ⊓ Cen σ, ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) → Q ≤ Subgroup.zpowers σ

theorem is2El_subtype {H : Subgroup G} (x : H) (h : Is2El (x : G)) : Is2El x := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m, Subtype.ext (by simpa using hm)⟩

end Good

end CFSG.RankThree.PartTwo.Sec21.FF79
