module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSL3

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.CGT.T75N

theorem card_modEq_card_fixedPoints_of_iterate {α : Type*} [Finite α] {p : ℕ} [Fact p.Prime]
    (f : α → α) (hf : f^[p] = id) :
    Nat.card α ≡ Nat.card (Function.fixedPoints f) [MOD p] := by
  classical
  have := Fintype.ofFinite α
  let f' : Function.End α := f
  have hf' : f' ^ p ^ 1 = 1 := by
    rw [pow_one]
    show (f' ^ p : Function.End α) = 1
    have : ∀ k : ℕ, ((f' ^ k : Function.End α) : α → α) = f^[k] := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ, Function.iterate_succ]
        show ((f' ^ k : Function.End α) : α → α) ∘ f = _
        rw [ih]
    exact (this p).trans hf
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f') (p := p) (n := 1) hf'
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

variable {G : Type} [Group G]

@[expose] def conjQ (Q : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    ↥Q →* ↥Q where
  toFun q := ⟨g * q * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg q).mp q.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjQ (Q : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G)) (q : ↥Q) :
    ((conjQ Q hg q : ↥Q) : G) = g * q * g⁻¹ := rfl

theorem center_le_comap_conjQ (Q : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    Subgroup.center ↥Q ≤ (Subgroup.center ↥Q).comap (conjQ Q hg) := by
  intro z hz
  rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
  intro q
  apply Subtype.ext
  have hq' : g⁻¹ * (q : G) * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) q).mp q.2
    simpa using this
  have h := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨_, hq'⟩)
  simp only [Subgroup.coe_mul] at h
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_conjQ]
  calc (q : G) * (g * z * g⁻¹) = g * ((g⁻¹ * q * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * q * g)) * g⁻¹ := by rw [h]
    _ = g * z * g⁻¹ * q := by group

abbrev quotZ (Q : Subgroup G) : Type _ := ↥Q ⧸ Subgroup.center ↥Q

@[expose] noncomputable def conjW (Q : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) : quotZ Q →* quotZ Q :=
  QuotientGroup.map _ _ (conjQ Q hg) (center_le_comap_conjQ Q hg)

theorem conjW_mk (Q : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G)) (q : ↥Q) :
    conjW Q hg (q : quotZ Q) = ((conjQ Q hg q : ↥Q) : quotZ Q) :=
  QuotientGroup.map_mk _ _ _ _ q

theorem mk_eq_mk_iff (Q : Subgroup G) (a b : ↥Q) :
    (a : quotZ Q) = (b : quotZ Q) ↔
      (a : G)⁻¹ * b ∈ Subgroup.centralizer (Q : Set G) := by
  rw [QuotientGroup.eq, Subgroup.mem_center_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h q hq
    have := congrArg Subtype.val (h ⟨q, hq⟩)
    simpa using this
  · intro h q
    apply Subtype.ext
    simpa using h q q.2

theorem conjW_congr (Q : Subgroup G) {g g' : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hg' : g' ∈ Subgroup.normalizer (Q : Set G)) (h : g = g') (w : quotZ Q) :
    conjW Q hg w = conjW Q hg' w := by
  subst h
  rfl

theorem conjW_mul_apply (Q : Subgroup G) {g h : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (hh : h ∈ Subgroup.normalizer (Q : Set G)) (hgh : g * h ∈ Subgroup.normalizer (Q : Set G))
    (w : quotZ Q) : conjW Q hgh w = conjW Q hg (conjW Q hh w) := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
  rw [conjW_mk, conjW_mk, conjW_mk]
  congr 1
  apply Subtype.ext
  simp only [coe_conjQ]
  group

theorem conjW_one_apply (Q : Subgroup G) (h1 : (1 : G) ∈ Subgroup.normalizer (Q : Set G))
    (w : quotZ Q) : conjW Q h1 w = w := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
  rw [conjW_mk]
  congr 1
  apply Subtype.ext
  simp [coe_conjQ]

theorem conjW_pow_apply (Q : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (Q : Set G))
    (k : ℕ) (w : quotZ Q) :
    conjW Q (Subgroup.pow_mem _ hg k) w = (conjW Q hg)^[k] w := by
  induction k generalizing w with
  | zero =>
    rw [conjW_congr Q _ (Subgroup.one_mem _) (pow_zero g), conjW_one_apply]
    rfl
  | succ k ih =>
    rw [conjW_congr Q _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hg k) hg) (pow_succ g k),
      conjW_mul_apply Q (Subgroup.pow_mem _ hg k) hg, ih, ← Function.iterate_succ_apply]

theorem conjW_eq_self_of_mem (Q : Subgroup G)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Q : Set G))
    {q' : G} (hq' : q' ∈ Q) (w : quotZ Q) :
    conjW Q (Subgroup.le_normalizer hq') w = w := by
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
  rw [conjW_mk, mk_eq_mk_iff, coe_conjQ]
  have := hcomm q' hq' (q : G)⁻¹ (Q.inv_mem q.2)
  simpa [mul_assoc] using this

theorem conjW_comm (Q : Subgroup G)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ ∈ Subgroup.centralizer (Q : Set G))
    {y x : G} (hy : y ∈ Subgroup.normalizer (Q : Set G)) (hx : x ∈ Subgroup.normalizer (Q : Set G))
    (hyx : y * x * y⁻¹ * x⁻¹ ∈ Q) (w : quotZ Q) :
    conjW Q hy (conjW Q hx w) = conjW Q hx (conjW Q hy w) := by
  have hyxN := Subgroup.mul_mem _ hy hx
  have hxyN := Subgroup.mul_mem _ hx hy
  have hqN : y * x * y⁻¹ * x⁻¹ ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hyx
  have h1 : y * x = (y * x * y⁻¹ * x⁻¹) * (x * y) := by group
  rw [← conjW_mul_apply Q hy hx hyxN, ← conjW_mul_apply Q hx hy hxyN]
  have h2 : conjW Q hyxN w = conjW Q (Subgroup.mul_mem _ hqN hxyN) w :=
    conjW_congr Q hyxN _ h1 w
  rw [h2, conjW_mul_apply Q hqN hxyN, conjW_eq_self_of_mem Q hcomm hyx]

end CFSG.RankThree.PartTwo.Sec20.Res2
