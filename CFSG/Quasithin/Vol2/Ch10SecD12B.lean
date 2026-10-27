module

public import CFSG.Quasithin.Vol2.Ch10SecD31F

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

structure Data10212 (T L I : Subgroup G) (m a0 r0 : ℕ) : Prop where
  rank_quot : m ≤ mQuot (fsuUL T L I) (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G))
  rank_le : ∀ E : Subgroup G, E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G) →
    IsElemAbelian 2 E → mQuot E (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) ≤ r0
  a_le : ∀ E : Subgroup G, E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G) →
    IsElemAbelian 2 E → ¬ E ≤ Subgroup.centralizer (fsuUL T L I : Set G) → ∀ q : ℕ,
    (∀ B : Subgroup G, B ≤ E → mQuot E B < q →
      fsuUL T L I ⊓ Subgroup.centralizer (B : Set G) =
        fsuUL T L I ⊓ Subgroup.centralizer (E : Set G)) → q ≤ a0
  fix : ∀ b ∈ Subgroup.normalizer (fsuUL T L I : Set G), b ^ 2 = 1 →
    ∃ v ∈ fsuUL T L I, v ∉ Subgroup.centralizer (fsuL0 T L : Set G) ∧ b * v = v * b
  r0_lt : r0 < m

structure GenFaithful (T L I : Subgroup G) : Prop where
  faithful : ∀ x ∈ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G),
    (∀ v ∈ fsuUL T L I, x * v * x⁻¹ * v⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G)) →
      x ∈ Subgroup.centralizer (fsuUL T L I : Set G)
  gen : ∀ Y : Subgroup G, (∀ v ∈ fsuUL T L I, v ∉ Subgroup.centralizer (fsuL0 T L : Set G) →
    L ⊓ Subgroup.centralizer ({v} : Set G) ≤ Y) → L ≤ Y
  odd_prime : ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)

omit [Finite G] in
theorem a_le_of_rank_le {r0 : ℕ} (hr : ∀ E : Subgroup G,
    E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G) → IsElemAbelian 2 E →
      mQuot E (E ⊓ Subgroup.centralizer (fsuUL T L I : Set G)) ≤ r0) (E : Subgroup G)
    (hE : E ≤ fsuM T L ⊓ Subgroup.normalizer (fsuUL T L I : Set G)) (hEa : IsElemAbelian 2 E)
    (hEC : ¬ E ≤ Subgroup.centralizer (fsuUL T L I : Set G)) (q : ℕ)
    (hq : ∀ B : Subgroup G, B ≤ E → mQuot E B < q →
      fsuUL T L I ⊓ Subgroup.centralizer (B : Set G) =
        fsuUL T L I ⊓ Subgroup.centralizer (E : Set G)) : q ≤ r0 := by
  refine le_trans ?_ (hr E hE hEa)
  by_contra hlt
  push Not at hlt
  have h1 := hq _ inf_le_left hlt
  apply hEC
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : v ∈ fsuUL T L I ⊓ Subgroup.centralizer
      ((E ⊓ Subgroup.centralizer (fsuUL T L I : Set G) : Subgroup G) : Set G) := by
    refine ⟨hv, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (Subgroup.mem_centralizer_iff.mp hy.2 v hv).symm
  rw [h1] at hv'
  exact (Subgroup.mem_centralizer_iff.mp hv'.2 x hx).symm

theorem fix_of_card (h : Hyp10 G T L I) {m : ℕ}
    (hm : m ≤ mQuot (fsuUL T L I) (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)))
    (hc : Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) < 2 ^ m) :
    ∀ b ∈ Subgroup.normalizer (fsuUL T L I : Set G), b ^ 2 = 1 →
      ∃ v ∈ fsuUL T L I, v ∉ Subgroup.centralizer (fsuL0 T L : Set G) ∧ b * v = v * b := by
  intro b hbN hb2
  have : IsMulCommutative ↥(fsuUL T L I) := ⟨⟨fun x y => Subtype.ext
    (show (x : G) * y = y * x from congrArg Subtype.val
      ((SecA.isElemAbelian_fsuVM h).1.is_comm.comm ⟨x, V1_le_V x.2⟩ ⟨y, V1_le_V y.2⟩))⟩⟩
  have hsq := SecC.sq_eq_one_fsuUL h
  set x : MulAut ↥(fsuUL T L I) := conjAct (fsuUL T L I) ⟨b, hbN⟩ with hx
  have hx2 : x ^ 2 = 1 := by
    rw [hx, ← map_pow]
    have : (⟨b, hbN⟩ : Subgroup.normalizer (fsuUL T L I : Set G)) ^ 2 = 1 :=
      Subtype.ext (by simpa using hb2)
    rw [this, map_one]
  have h1 := card_commV_mul_card_fixV hsq x
  have h2 := Subgroup.card_le_of_le (commV_zpowers_le_fixV_b4 hsq hx2)
  by_contra hcon
  push Not at hcon
  have hle : fixV (Subgroup.zpowers x) ≤ cV1 T L I := by
    intro v hv
    rw [mem_fixV_zpowers_iff] at hv
    have hv' : b * (v : G) * b⁻¹ = v := by
      rw [← A1b.conjAct_coe (fsuUL T L I) ⟨b, hbN⟩ v]
      exact congrArg Subtype.val hv
    rw [Subgroup.mem_subgroupOf]
    by_contra hvL
    refine hcon v v.2 hvL ?_
    calc b * (v : G) = b * v * b⁻¹ * b := by group
      _ = v * b := by rw [hv']
  have h3 := Subgroup.card_le_of_le hle
  have h4 : Nat.card ↥(cV1 T L I) =
      Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) := by
    rw [cV1, card_subgroupOf_eq, inf_comm]
  have h5 := card_eq_two_pow_mul (V := fsuUL T L I)
    ((SecA.isPGroup_fsuVM h).to_le V1_le_V) (inf_le_left :
      fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G) ≤ fsuUL T L I)
  set z := Nat.card ↥(fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G))
  have hz : 0 < z := Nat.card_pos
  have h6 : 2 ^ m ≤ 2 ^ mQuot (fsuUL T L I)
      (fsuUL T L I ⊓ Subgroup.centralizer (fsuL0 T L : Set G)) :=
    Nat.pow_le_pow_right (by norm_num) hm
  have h7 : Nat.card ↥(fsuUL T L I) ≤ z * z := by
    calc Nat.card ↥(fsuUL T L I) = Nat.card (commV (Subgroup.zpowers x)) *
          Nat.card (fixV (Subgroup.zpowers x)) := h1.symm
      _ ≤ Nat.card (fixV (Subgroup.zpowers x)) * Nat.card (fixV (Subgroup.zpowers x)) :=
          Nat.mul_le_mul_right _ h2
      _ ≤ z * z := Nat.mul_le_mul (h3.trans h4.le) (h3.trans h4.le)
  have h8 : 2 ^ m * z ≤ Nat.card ↥(fsuUL T L I) := by
    rw [h5]
    exact Nat.mul_le_mul_right _ h6
  have h9 : z * z < 2 ^ m * z := Nat.mul_lt_mul_of_pos_right hc hz
  omega

theorem hypE322 (h : Hyp10 G T L I) : E3.HypE322 T (fsuVM T L I) :=
  ⟨⟨le_top, h.fsu.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.fsu.sylow.2⟩,
    SecA.fsuVM_le_T h, SecA.le_normalizer_fsuVM T L I⟩

theorem mem_fsuM_of_le_conjSubgroup (h1013 : Stmt10_1_3) (h : Hyp10 G T L I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)) {g : G}
    (hL0 : fsuL0 T L ≤ conjSubgroup (fsuM T L) g) : g ∈ fsuM T L := by
  have hres := h1013 G T L I h p hp hp2 hpL
  have hle : (fsuL0 T L).map (MulAut.conj g).toMonoidHom ≤ fsuL0 T L := by
    rw [← hres]
    unfold oPrimeResidualOf
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨hxM, k, hk⟩, rfl⟩
    apply Subgroup.subset_closure
    have hx0 : x ∈ fsuL0 T L := hres ▸ Subgroup.subset_closure ⟨hxM, k, hk⟩
    have hxg := hL0 hx0
    rw [mem_conjSubgroup_iff] at hxg
    refine ⟨by simpa [MulAut.conj_apply] using hxg, k, ?_⟩
    rw [orderOf_injective _ (MulAut.conj g).injective, hk]
  have heq : (fsuL0 T L).map (MulAut.conj g).toMonoidHom = fsuL0 T L :=
    Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  exact heq

end CFSG.Quasithin.Vol2.Ch10.SecD
