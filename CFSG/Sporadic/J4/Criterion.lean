module

public import CFSG.GroupActions.PrimitiveNormalTransitive
public import CFSG.GroupActions.StabilizerFactorization
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.Sporadic.J4

theorem isSimpleGroup_of_conj_product {G Ω : Type*} [Group G] [Finite G] [Finite Ω]
    [MulAction G Ω] [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    (hΩ : 2 ≤ Nat.card Ω) (a b g : G) (hgen : Subgroup.closure ({a, b} : Set G) = ⊤) (ω : Ω)
    {p q : ℕ} (hp : (a * b) ^ p = 1) (hq : (a * (g⁻¹ * (a * b) * g)) ^ q = 1)
    (hpc : p.Coprime (Nat.card (MulAction.stabilizer G ω)))
    (hqc : q.Coprime (Nat.card (MulAction.stabilizer G ω))) : IsSimpleGroup G := by
  classical
  let _ : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (Nat.lt_of_succ_le hΩ)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne Ω
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G x y
  have hh1 : h ≠ 1 := by
    rintro rfl
    exact hxy (by simpa using hh)
  let _ : Nontrivial G := ⟨⟨h, 1, hh1⟩⟩
  rw [isSimpleGroup_iff]
  refine ⟨inferInstance, fun N hN => ?_⟩
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  right
  let _ : N.Normal := hN
  let _ : MulAction.IsPretransitive N Ω :=
    CFSG.GroupActions.isPretransitive_of_normal_ne_bot N hNbot
  let φ : G →* G ⧸ N := QuotientGroup.mk' N
  have hcard : Nat.card (G ⧸ N) ∣ Nat.card (MulAction.stabilizer G ω) :=
    CFSG.GroupActions.quotient_card_dvd_stabilizer_card N ω
  have key : ∀ {k : ℕ} (z : G), z ^ k = 1 →
      k.Coprime (Nat.card (MulAction.stabilizer G ω)) → φ z = 1 := by
    intro k z hz hk
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes hk
    · exact (orderOf_map_dvd φ z).trans (orderOf_dvd_of_pow_eq_one hz)
    · exact (orderOf_dvd_natCard (φ z)).trans hcard
  set c := a * b with hc
  have h1 : φ c = 1 := key c hp hpc
  have h2 := key _ hq hqc
  rw [map_mul, map_mul, map_mul, map_inv, h1, mul_one, inv_mul_cancel, mul_one] at h2
  have hb : φ b = 1 := by
    have : φ c = φ a * φ b := by rw [hc, map_mul]
    rw [h1, h2, one_mul] at this
    exact this.symm
  apply top_le_iff.mp
  rw [← hgen]
  apply (Subgroup.closure_le N).mpr
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact (QuotientGroup.eq_one_iff _).mp h2
  · exact (QuotientGroup.eq_one_iff _).mp hb

end CFSG.Sporadic.J4
