module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGapFourCent
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.AGLEmbedding.RankLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

variable {A : Type} [Group A]

theorem s15GapFour_conj_mem_centralizer_map (X : Subgroup A) (a : A) {z : A}
    (hz : z ∈ centralizer (X : Set A)) :
    a * z * a⁻¹ ∈ centralizer ((X.map (MulAut.conj a).toMonoidHom : Subgroup A) : Set A) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hw
  have h := Subgroup.mem_centralizer_iff.1 hz x hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc a * x * a⁻¹ * (a * z * a⁻¹) = a * (x * z) * a⁻¹ := by group
    _ = a * (z * x) * a⁻¹ := by rw [h]
    _ = a * z * a⁻¹ * (a * x * a⁻¹) := by group

theorem s15GapFour_exists_two_conj [Finite A] (M K : Subgroup A)
    (hcard : Set.ncard {X : Subgroup A | ∃ φ ∈ M, X = K.map (MulAut.conj φ).toMonoidHom} ≤ 2) :
    ∃ φ ∈ M, ∀ x ∈ M, K.map (MulAut.conj x).toMonoidHom = K ∨
      K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj φ).toMonoidHom := by
  classical
  haveI : Finite (Subgroup A) := Finite.of_injective _ SetLike.coe_injective
  set 𝒦 : Set (Subgroup A) :=
    {X | ∃ φ ∈ M, X = K.map (MulAut.conj φ).toMonoidHom} with h𝒦
  by_cases hall : ∀ x ∈ M, K.map (MulAut.conj x).toMonoidHom = K
  · exact ⟨1, M.one_mem, fun x hx => Or.inl (hall x hx)⟩
  · push Not at hall
    obtain ⟨x₀, hx₀M, hx₀⟩ := hall
    refine ⟨x₀, hx₀M, fun x hx => ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hK : K ∈ 𝒦 := ⟨1, M.one_mem, (s15GapFour_map_conj_one K).symm⟩
    have hK0 : K.map (MulAut.conj x₀).toMonoidHom ∈ 𝒦 := ⟨x₀, hx₀M, rfl⟩
    have hKx : K.map (MulAut.conj x).toMonoidHom ∈ 𝒦 := ⟨x, hx, rfl⟩
    have hsub : ({K, K.map (MulAut.conj x₀).toMonoidHom, K.map (MulAut.conj x).toMonoidHom} :
        Set (Subgroup A)) ⊆ 𝒦 := by
      intro X hX
      rcases hX with rfl | rfl | rfl
      · exact hK
      · exact hK0
      · exact hKx
    have h3 : ({K, K.map (MulAut.conj x₀).toMonoidHom, K.map (MulAut.conj x).toMonoidHom} :
        Set (Subgroup A)).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨_, _, _, fun h => hx₀ h.symm, fun h => h1 h.symm, fun h => h2 h.symm,
        rfl⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega

theorem s15GapFour_pRank_le_two (hAut : RAutRank153) [Finite A] {M K : Subgroup A}
    (hK : s15ListTwo ↥K) (hZ : Subgroup.center ↥K = ⊥)
    (hcard : Set.ncard {X : Subgroup A | ∃ φ ∈ M, X = K.map (MulAut.conj φ).toMonoidHom} ≤ 2)
    (hfaith : ∀ y ∈ M, (∀ x ∈ M, x * y * x⁻¹ ∈ centralizer (K : Set A)) → y = 1)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) : CFSG.Open.pRank q M ≤ 2 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hq1 : 1 < q := hq.one_lt
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  obtain ⟨φ, hφM, hφ⟩ := s15GapFour_exists_two_conj M K hcard
  have hnorm : ∀ y ∈ M, y ^ q = 1 → y ∈ normalizer (K : Set A) := fun y hy hyq =>
    s15GapFour_mem_normalizer_of_odd M K hcard hy hqodd hyq
  set c : A →* A := (MulAut.conj φ⁻¹).toMonoidHom with hc
  have hcy : ∀ y : A, c y = φ⁻¹ * y * φ := fun y => by simp [hc, MulAut.conj_apply]
  set P : Subgroup A :=
    M ⊓ normalizer (K : Set A) ⊓ (normalizer (K : Set A)).comap c with hP
  have hEP : ∀ E : Subgroup A, E ≤ M → IsElemAbelian q E → E ≤ P := by
    intro E hEM hE y hy
    have hyq : y ^ q = 1 := hE.2 y hy
    refine ⟨⟨hEM hy, hnorm y (hEM hy) hyq⟩, ?_⟩
    have hcyM : c y ∈ M := by
      rw [hcy]
      exact M.mul_mem (M.mul_mem (M.inv_mem hφM) (hEM hy)) hφM
    have hcyq : (c y) ^ q = 1 := by rw [← map_pow, hyq, map_one]
    exact hnorm (c y) hcyM hcyq
  have hMP : CFSG.Open.pRank q M ≤ CFSG.Open.pRank q P := by
    refine CFSG.SectionRank.pRank_le hq1 fun E hEM hE => ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hE)
    have hn' : n ≤ CFSG.Open.pRank q P := CFSG.SectionRank.le_pRank hq1 (hEP E hEM hE) hE hn
    rw [hn]
    exact Nat.pow_le_pow_right hq.pos hn'
  refine hMP.trans ?_
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup P]
  set ρ₁ : ↥P →* MulAut ↥K := K.normalizerMonoidHom.comp
    (Subgroup.inclusion (fun y (hy : y ∈ P) => hy.1.2) : ↥P →* ↥(normalizer (K : Set A)))
    with hρ₁
  set ρ₂ : ↥P →* MulAut ↥K := K.normalizerMonoidHom.comp
    ((c.comp P.subtype).codRestrict (normalizer (K : Set A)) fun y => y.2.2) with hρ₂
  have hker₁ : ∀ y : ↥P, ρ₁ y = 1 → (y : A) ∈ centralizer (K : Set A) := by
    intro y hy
    have hy' : (⟨(y : A), y.2.1.2⟩ : ↥(normalizer (K : Set A))) ∈ K.normalizerMonoidHom.ker :=
      MonoidHom.mem_ker.2 hy
    rw [Subgroup.normalizerMonoidHom_ker] at hy'
    exact hy'
  have hker₂ : ∀ y : ↥P, ρ₂ y = 1 → c (y : A) ∈ centralizer (K : Set A) := by
    intro y hy
    have hy' : (⟨c (y : A), y.2.2⟩ : ↥(normalizer (K : Set A))) ∈ K.normalizerMonoidHom.ker :=
      MonoidHom.mem_ker.2 hy
    rw [Subgroup.normalizerMonoidHom_ker] at hy'
    exact hy'
  have hinj : ∀ y : ↥P, ρ₁ y = 1 → ρ₂ y = 1 → y = 1 := by
    intro y h1 h2
    have hy1 := hker₁ y h1
    have hy2 := hker₂ y h2
    have hy2' : (y : A) ∈
        centralizer ((K.map (MulAut.conj φ).toMonoidHom : Subgroup A) : Set A) := by
      have h := s15GapFour_conj_mem_centralizer_map K φ hy2
      rw [hcy] at h
      simpa [mul_assoc] using h
    have hcen : ∀ x ∈ M, x * (y : A) * x⁻¹ ∈ centralizer (K : Set A) := by
      intro x hx
      have e1 : (K.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom = K := by
        rw [← s15GapFour_map_conj_mul, mul_inv_cancel, s15GapFour_map_conj_one]
      have hmem : (y : A) ∈ centralizer ((K.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup A) :
          Set A) := by
        rcases hφ x⁻¹ (M.inv_mem hx) with h | h
        · rw [h]; exact hy1
        · rw [h]; exact hy2'
      have h := s15GapFour_conj_mem_centralizer_map _ x hmem
      rwa [e1] at h
    exact Subtype.ext (hfaith y y.2.1.1 hcen)
  have hbot : ρ₁.ker ⊓ ρ₂.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨h1, h2⟩
    exact Subgroup.mem_bot.2 (hinj y (MonoidHom.mem_ker.1 h1) (MonoidHom.mem_ker.1 h2))
  have hzero : CFSG.Open.pRank q (⊥ : Subgroup ↥P) = 0 := by
    refine Nat.le_zero.1 (CFSG.SectionRank.pRank_le hq1 fun E hE _ => ?_)
    rw [le_bot_iff.1 hE, Subgroup.card_bot]
    simp
  have hAut1 : CFSG.Open.pRank q (⊤ : Subgroup (MulAut ↥K)) ≤ 1 :=
    s15GapFour_pRank_mulAut_le_one hAut hK hZ hq hq2
  have h1 := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hq ρ₁ (⊤ : Subgroup ↥P)
  have h2 := CFSG.AGLEmbedding.pRank_le_pRank_inf_ker_add_pRank_map hq ρ₂ ρ₁.ker
  have h3 : CFSG.Open.pRank q ((⊤ : Subgroup ↥P).map ρ₁) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hq1 le_top).trans hAut1
  have h4 : CFSG.Open.pRank q (ρ₁.ker.map ρ₂) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono hq1 le_top).trans hAut1
  rw [top_inf_eq] at h1
  rw [hbot, hzero] at h2
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
