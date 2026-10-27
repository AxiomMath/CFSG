module

public import CFSG.RankThree.CentralLift.ClassicalScalarCover
public import CFSG.RankThree.Classical.UnitaryRankWitness
public import CFSG.RankThree.Classical2.OrthogonalDefiningPrimeRank

public section

namespace CFSG.RankThree.CentralLift

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LieType.Universal.Spin
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply statedOmega_eq_comap
  mem_statedScalars_iff)
open CFSG.RankThree.Classical2 (ProjOrthDerived orthDerived)

theorem eq_bot_of_isPGroup_of_not_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH : IsPGroup p H) (h : ¬p ∣ Nat.card H) : H = ⊥ := by
  obtain ⟨k, hk⟩ := hH.exists_card_eq
  rcases k with _ | k
  · exact Subgroup.eq_bot_of_card_eq H (by rw [hk, pow_zero])
  · exact absurd (hk ▸ dvd_pow_self p (Nat.succ_ne_zero k)) h

theorem card_dvd_of_nonempty_mulEquiv_quotient {G C : Type*} [Group G] [Group C]
    {D B : Subgroup G} [(B.subgroupOf D).Normal] (h : Nonempty (C ≃* D ⧸ B.subgroupOf D)) :
    Nat.card C ∣ Nat.card D := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact Subgroup.card_quotient_dvd_card _

theorem exists_top_cover {L T : Type*} [Group L] [Group T] (e : L ⧸ Subgroup.center L ≃* T) :
    ∃ φ : (⊤ : Subgroup L) →* T, Function.Surjective φ ∧
      φ.ker ≤ Subgroup.center (⊤ : Subgroup L) := by
  refine ⟨(e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).comp
    (⊤ : Subgroup L).subtype, fun t => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy⟩ := e.surjective t
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) y
    exact ⟨⟨x, Subgroup.mem_top x⟩, hy⟩
  · have hx' : (x : L) ∈ Subgroup.center L := by
      have h := CFSG.LieType.Steinberg.ker_comp_mk' (Subgroup.center L) e
      rw [← h]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.1 hx' y)

theorem nonempty_statedProj_mulEquiv_projOrthDerived {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) :
    Nonempty (StatedProj (StatedOmega Q₀) ≃* ProjOrthDerived Q) := by
  have hmap : (StatedOmega Q₀).map (toLinEquiv ι K).toMonoidHom = orthDerived Q := by
    rw [statedOmega_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _
  let e₁ : StatedOmega Q₀ ≃* orthDerived Q :=
    ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr hmap)
  have he₁ : ∀ A : StatedOmega Q₀,
      ((e₁ A : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) = toLinEquiv ι K A := fun _ => rfl
  refine ⟨QuotientGroup.congr _ _ e₁ ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff] at hy
    rw [Subgroup.mem_subgroupOf]
    exact hy
  · intro hx
    refine ⟨e₁.symm x, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    rw [Subgroup.mem_subgroupOf] at hx
    have h1 : ((e₁ (e₁.symm x) : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) = x := by
      rw [MulEquiv.apply_symm_apply]
    rw [he₁] at h1
    rw [h1]
    exact hx

section Rank

variable {L : Type*} [Group L] [Finite L]

theorem four_mul_le_localRank_of_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) (h7 : 7 ≤ Fintype.card ι)
    (hB : (QuadraticMap.polarBilin Q).Nondegenerate)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega Q₀)) : 4 * f ≤ localRank p L := by
  obtain ⟨e'⟩ := nonempty_statedProj_mulEquiv_projOrthDerived hQ
  obtain ⟨φ, hφ, hker⟩ := exists_top_cover (e.trans e')
  exact CFSG.RankThree.Classical2.le_localRank_of_orthogonal_defining_prime ⊤ hp hp3 hf hK Q
    (by rwa [Module.finrank_fintype_fun_eq_card]) hB φ hφ hker

theorem four_mul_le_localRank_of_omegaOdd {p f n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f) (hn : 3 ≤ n)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadOdd n K))) :
    4 * f ≤ localRank p L :=
  four_mul_le_localRank_of_orthogonal hp hp3 hf hK (coe_quadOdd n K) (by simp; omega)
    (nondegenerate_polarBilin_quadOdd n K (Ring.two_ne_zero
      (CFSG.LieType.Steinberg.ringChar_ne_two_of_card_eq_pow hp (by omega) hK))) e

theorem four_mul_le_localRank_of_omegaPlus {p f n : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f) (hn : 4 ≤ n)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadPlus n K))) :
    4 * f ≤ localRank p L :=
  four_mul_le_localRank_of_orthogonal hp hp3 hf hK (coe_quadPlus n K) (by simp; omega)
    (nondegenerate_polarBilin_quadPlus n K) e

theorem four_mul_le_localRank_of_omegaMinus {p f n : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f) (hn : 4 ≤ n)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c))) :
    4 * f ≤ localRank p L :=
  four_mul_le_localRank_of_orthogonal hp hp3 hf hK (coe_quadMinus n K b c) (by simp; omega)
    (nondegenerate_polarBilin_quadMinus_of_finite n K hirr) e

theorem four_mul_le_localRank_of_unitary {p f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hf : 1 ≤ f)
    {K : Type} [Field K] (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 5 ≤ n)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU n (p ^ f) K)) : 4 * f ≤ localRank p L := by
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  obtain ⟨φ, hφ, hker⟩ := exists_top_cover (e.trans (unitaryPSUEquiv h (by omega)).symm)
  have := (CFSG.RankThree.Classical.unitary_defining_prime_central_cover_two_local_rank_witness
    ⊤ h hp3 (by omega) φ hφ hker).2.2.1 2 (by norm_num) (by omega)
  calc 4 * f = f * 2 ^ 2 := by ring
    _ ≤ localRank p L := this

theorem sub_two_le_localRank_of_unitary {p ℓ f : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hℓ : ℓ.Prime)
    (hℓodd : Odd ℓ) (hf : 1 ≤ f) {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) {n : ℕ}
    (hn : 3 ≤ n) (hpn : p ∣ n) (hpq : p ∣ ℓ ^ f + 1)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU n (ℓ ^ f) K)) :
    n - 2 ≤ localRank p L := by
  have h : UnitaryFieldData ℓ f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hℓ2 : ℓ ≠ 2 := hℓodd.ne_two_of_dvd_nat (dvd_refl ℓ)
  obtain ⟨φ, hφ, hker⟩ := exists_top_cover (e.trans (unitaryPSUEquiv h (by omega)).symm)
  obtain ⟨u, -, hu, V, hV, hVab, hVcard⟩ :=
    CFSG.RankThree.Classical2.unitary_split_prime_central_cover_two_local_rank ⊤ h hp hp3 hpq hn φ
      hφ hker
  simp only [hℓ2, hpn, ↓reduceIte] at hVcard
  have := CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian hp hu
    (le_inf_iff.mp hV).2 hVab hVcard
  omega

end Rank

section Center

variable {p ℓ f n : ℕ} {L : Type} [Group L] [Finite L]

omit [Finite L] in
theorem ker_center_cover {T : Type*} [Group T] (e : L ⧸ Subgroup.center L ≃* T) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))).ker = Subgroup.center L :=
  CFSG.LieType.Steinberg.ker_comp_mk' _ e

theorem symplectic_quasisimple_prime_center_trivial (hp : p.Prime) (hp3 : 3 < p)
    (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L)) (hℓodd : Odd ℓ)
    (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp n ℓ f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨⟨hℓ, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have : Group.IsPerfect L := hL.1
  have : Fact p.Prime := ⟨hp⟩
  have hker := ker_center_cover e
  obtain ⟨⟨_, -, -, -, -, -, hiso⟩, hD⟩ := symplectic_exact_scalar_cover hp hp3 hℓ hℓodd hf hK
    (by omega) (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hZ)
  have hcard := card_dvd_of_nonempty_mulEquiv_quotient hiso
  rw [hker] at hcard
  refine eq_bot_of_isPGroup_of_not_dvd hZ fun hdvd => ?_
  have h1 := Nat.le_of_dvd Nat.card_pos (hdvd.trans hcard)
  omega

theorem omegaPlus_small_local_rank_prime_center_trivial (hp : p.Prime) (hp3 : 3 < p)
    (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L)) (hloc : localRank p L ≤ 2)
    (hℓodd : Odd ℓ) (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .POmegaPlus n ℓ f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨⟨hℓ, hf, hn⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have hn4 : 4 ≤ n := hn
  have : Group.IsPerfect L := hL.1
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpℓ : p = ℓ
  · subst hpℓ
    have := four_mul_le_localRank_of_omegaPlus hp hp3 hf hK hn4 e
    omega
  have hker := ker_center_cover e
  obtain ⟨⟨_, -, -, -, -, -, hiso⟩, hD⟩ := omegaPlus_exact_scalar_cover hp hp3 hℓ hℓodd hpℓ hf hK
    (by omega) (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hZ)
  have hcard := card_dvd_of_nonempty_mulEquiv_quotient hiso
  rw [hker] at hcard
  refine eq_bot_of_isPGroup_of_not_dvd hZ fun hdvd => ?_
  have h1 := Nat.le_of_dvd Nat.card_pos (hdvd.trans hcard)
  omega

theorem unitary_small_local_rank_prime_center_trivial_of_defining_or_three (hp : p.Prime)
    (hp3 : 3 < p) (hL : CFSG.IsQuasisimple L) (hZ : IsPGroup p (Subgroup.center L))
    (hloc : localRank p L ≤ 2) (hℓodd : Odd ℓ) (hcase : p = ℓ ∨ n = 3)
    (hM : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n ℓ f) :
    Subgroup.center L = ⊥ := by
  obtain ⟨⟨hℓ, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hM
  have hn3 : 3 ≤ n := hn
  have : Group.IsPerfect L := hL.1
  have : Fact p.Prime := ⟨hp⟩
  by_cases hodd : p = ℓ ∧ n ≠ 3 ∧ ¬Even n
  · obtain ⟨rfl, h3, hne⟩ := hodd
    have hn5 : 5 ≤ n := by
      rcases Nat.even_or_odd n with h | ⟨k, rfl⟩
      · exact absurd h hne
      · omega
    have := four_mul_le_localRank_of_unitary hp hp3 hf hK hn5 e
    omega
  have hcase' : n = 3 ∨ (p = ℓ ∧ Even n) := by
    rcases hcase with hpl | h3
    · by_cases h3 : n = 3
      · exact Or.inl h3
      · exact Or.inr ⟨hpl, by_contra fun hne => hodd ⟨hpl, h3, hne⟩⟩
    · exact Or.inl h3
  have hker := ker_center_cover e
  obtain ⟨⟨_, -, -, -, -, -, hiso⟩, hD⟩ := unitary_exact_scalar_cover_of_three_or_defining hp hp3
    hℓ hℓodd hf hK hn3 hcase' (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hZ)
  have hcard := card_dvd_of_nonempty_mulEquiv_quotient hiso
  rw [hker] at hcard
  refine eq_bot_of_isPGroup_of_not_dvd hZ fun hdvd => ?_
  have hpg : p ∣ Nat.gcd n (ℓ ^ f + 1) := (hdvd.trans hcard).trans hD
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpq : p ∣ ℓ ^ f + 1 := hpg.trans (Nat.gcd_dvd_right _ _)
  rcases hcase' with h3 | ⟨hpl, -⟩
  · rw [h3] at hpn
    have := Nat.le_of_dvd (by norm_num) hpn
    omega
  · rw [← hpl] at hpq
    have h2 : p ∣ 1 := (Nat.dvd_add_right (dvd_pow_self p (by omega))).1 hpq
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)

end Center

end CFSG.RankThree.CentralLift
