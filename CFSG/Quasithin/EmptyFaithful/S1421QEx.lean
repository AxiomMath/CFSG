module

public import CFSG.Quasithin.EmptyFaithful.S1421QShapeDefs
public import CFSG.LocalAnalysis.SectionRank.EvenCover.LinearCover
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.EvenCover Matrix
open scoped commutatorElement

namespace QEx

theorem cube_eq_one_of_scalar_mem {K : Type} [Field K] {x : StatedSL 3 K} {c : Kˣ}
    (hc : Matrix.GeneralLinearGroup.scalar (Fin 3) c = (x : GL (Fin 3) K)) :
    (c : K) ^ 3 = 1 := by
  have hx : ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    have h : (x : GL (Fin 3) K) ∈ (SpecialLinearGroup.toGL :
        SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range := by
      rw [← statedSL_eq_range_toGL]
      exact x.2
    obtain ⟨B, hB⟩ := h
    rw [← hB]
    exact B.prop
  rw [← hc, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hx
  exact hx

theorem eq_one_or_eq_or_eq_sq {K : Type} [Field K] {c c' : K} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hc'3 : c' ^ 3 = 1) : c' = 1 ∨ c' = c ∨ c' = c ^ 2 := by
  have hs : c ^ 2 + c + 1 = 0 := by
    have h : (c - 1) * (c ^ 2 + c + 1) = 0 := by linear_combination hc3
    rcases mul_eq_zero.1 h with h | h
    · exact absurd (sub_eq_zero.1 h) hc1
    · exact h
  have h : (c' - 1) * (c' - c) * (c' - c ^ 2) = 0 := by
    linear_combination hc'3 - (c' ^ 2 - c * c' + c - 1) * hs
  rcases mul_eq_zero.1 h with h | h
  · rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (Or.inl (sub_eq_zero.1 h))
  · exact Or.inr (Or.inr (sub_eq_zero.1 h))

theorem eq_bot_or_eq_scalars {K : Type} [Field K] (F : Subgroup (StatedSL 3 K))
    (hF : F ≤ (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K)) :
    F = ⊥ ∨ F = (StatedScalars (Fin 3) K).subgroupOf (StatedSL 3 K) := by
  by_cases hbot : F = ⊥
  · exact Or.inl hbot
  refine Or.inr (le_antisymm hF fun d hd => ?_)
  obtain ⟨⟨k, hkF⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 (hF hkF))
  obtain ⟨c', hc'⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 hd)
  have hc3 : (c : K) ^ 3 = 1 := cube_eq_one_of_scalar_mem hc
  have hc'3 : (c' : K) ^ 3 = 1 := cube_eq_one_of_scalar_mem hc'
  have hc1 : (c : K) ≠ 1 := by
    intro h
    apply hk1
    have hc1' : c = 1 := Units.ext h
    apply Subtype.ext
    apply Subtype.ext
    rw [← hc, hc1', map_one]
    rfl
  rcases eq_one_or_eq_or_eq_sq hc3 hc1 hc'3 with h | h | h
  · have : c' = 1 := Units.ext h
    have hd1 : d = 1 := by
      apply Subtype.ext
      rw [← hc', this, map_one]
      rfl
    rw [hd1]
    exact F.one_mem
  · have : c' = c := Units.ext h
    have hdk : d = k := by
      apply Subtype.ext
      rw [← hc', this, hc]
    rw [hdk]
    exact hkF
  · have : c' = c ^ 2 := Units.ext (by simpa using h)
    have hdk : d = k ^ 2 := by
      apply Subtype.ext
      rw [← hc', this, map_pow, hc]
      rfl
    rw [hdk]
    exact F.pow_mem hkF 2

section Cover


theorem equiv_psl_or_sl_of_odd_center {K : Type} [Field K] [Finite K] [CharP K 2]
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL 3 K)) :
    Nonempty (L ≃* StatedProj (StatedSL 3 K)) ∨ Nonempty (L ≃* StatedSL 3 K) := by
  obtain ⟨φ, hφ, hker, -⟩ := even_linear_perfect_odd_cover_map (by norm_num : 2 ≤ 3) hodd e
  rcases eq_bot_or_eq_scalars φ.ker hker with h | h
  · exact Or.inr ⟨(MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).1 h, hφ⟩).symm⟩
  · exact Or.inl ⟨(QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.trans
      (QuotientGroup.quotientMulEquivOfEq h)⟩

theorem equiv_psp_of_odd_center {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ}
    {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (hodd : Odd (Nat.card (Subgroup.center L)))
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSp r K)) :
    Nonempty (L ≃* StatedProj (StatedSp r K)) :=
  ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq (center_eq_bot_of_even_symplectic hodd e).symm)).trans e⟩

end Cover

theorem charP_two_of_card_two_pow {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) : CharP F 2 := by
  have : Fintype F := Fintype.ofFinite F
  exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hF])

theorem odd_card_center_of_odd_orderOf {X : Type} [Group X] [Finite X]
    (hodd : ∀ x ∈ Subgroup.center X, Odd (orderOf x)) : Odd (Nat.card (Subgroup.center X)) := by
  by_contra h
  have h2 : 2 ∣ Nat.card (Subgroup.center X) := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) 2 h2
  have h1 := hodd x x.2
  rw [Subgroup.orderOf_coe, hx] at h1
  exact absurd h1 (by decide)

theorem eq_one_of_central_pow_two {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.pCore 2 Q = ⊥)
    {z : Q} (hz : z ∈ Subgroup.center Q) {k : ℕ} (hk : z ^ 2 ^ k = 1) : z = 1 := by
  have h2 : IsPGroup 2 (Subgroup.zpowers z) := by
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hm])
  have hWn : (Subgroup.zpowers z).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hz)
  have hle := CFSG.LieType.BorelTits.le_pCore 2 hWn h2
  rw [hQ] at hle
  exact Subgroup.mem_bot.1 (hle (Subgroup.mem_zpowers z))

theorem odd_orderOf_of_central {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.pCore 2 Q = ⊥) {z : Q}
    (hz : z ∈ Subgroup.center Q) : Odd (orderOf z) := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' 2 (by norm_num)
  have h1 : (z ^ m) ^ 2 ^ a = 1 := by
    rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one]
  have h2 : z ^ m = 1 := eq_one_of_central_pow_two hQ (Subgroup.pow_mem _ hz m) h1
  exact Odd.of_dvd_nat (Nat.odd_iff.mpr (by omega)) (orderOf_dvd_of_pow_eq_one h2)

theorem isPerfect_oTwoQuot_of_commutator_eq {G : Type} [Group G] {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) : Group.IsPerfect (OTwoQuot K) := by
  have hKp : Group.IsPerfect ↥K := by
    refine ⟨?_⟩
    rw [commutator_def]
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype, hK]
  exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K))
    (QuotientGroup.mk'_surjective _)

end QEx

open QEx

theorem exactType_of_isCentralL3Sp4
    {n : ℕ} (_hn : 2 ≤ n) {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hodd : ∀ x ∈ Subgroup.center X, Odd (orderOf x)) (h : IsCentralL3Sp4 n X) :
    IsPSL 3 2 n X ∨ IsSL3 (2 ^ n) X ∨ IsPSp4 2 n X := by
  have hcard : Odd (Nat.card (Subgroup.center X)) := odd_card_center_of_odd_orderOf hodd
  rcases h with h | h
  · obtain ⟨hadm, K, iK, iFin, hK, ⟨e⟩⟩ := h
    have : CharP K 2 := charP_two_of_card_two_pow hK
    rcases equiv_psl_or_sl_of_odd_center hcard e with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
    · exact Or.inl ⟨hadm, K, iK, iFin, hK, ⟨e'⟩⟩
    · exact Or.inr (Or.inl ⟨K, iK, iFin, hK, ⟨e'⟩⟩)
  · obtain ⟨hadm, K, iK, iFin, hK, ⟨e⟩⟩ := h
    have : CharP K 2 := charP_two_of_card_two_pow hK
    obtain ⟨e'⟩ := equiv_psp_of_odd_center hcard e
    exact Or.inr (Or.inr ⟨hadm, K, iK, iFin, hK, ⟨e'⟩⟩)

theorem exactType_oTwoQuot
    {G : Type} [Group G] [Finite G] {K : Subgroup G} (hK : ⁅K, K⁆ = K) {n : ℕ} (hn : 2 ≤ n)
    (h : IsCentralL3Sp4 n (OTwoQuot K)) :
    IsPSL 3 2 n (OTwoQuot K) ∨ IsSL3 (2 ^ n) (OTwoQuot K) ∨ IsPSp4 2 n (OTwoQuot K) := by
  have : Group.IsPerfect (OTwoQuot K) := isPerfect_oTwoQuot_of_commutator_eq hK
  exact exactType_of_isCentralL3Sp4 hn
    (fun x hx => odd_orderOf_of_central (pCore_two_quot_eq_bot K) hx) h

end CFSG.Quasithin
