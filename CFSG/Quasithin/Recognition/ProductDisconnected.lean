module

public import CFSG.GH74.Uniqueness.Section165GapFinal
public import CFSG.GH74.Bender.Suzuki

public section

namespace CFSG.Quasithin.Recognition

open CFSG.Blueprint CFSG.GH74.Uniqueness
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem isInvariantInvolutionSet_of_isConj {d : G} (hd : orderOf d = 2) :
    IsInvariantInvolutionSet {x : G | IsConj d x} := by
  refine ⟨fun z hz => ?_, fun z hz g => ?_⟩
  · obtain ⟨c, hc⟩ := (hz : IsConj d z)
    rw [← hc.orderOf_eq, hd]
  · refine (hz : IsConj d z).trans (isConj_iff.2 ⟨g⁻¹, ?_⟩)
    rw [inv_inv]

theorem isProductDisconnected_of_class (E : Subgroup G) (hE : E ≠ ⊤) (D : Set G)
    (hD2 : ∀ x ∈ D, orderOf x = 2) (ha : (D ∩ (E : Set G)).Nonempty)
    (hb : ∀ x ∈ D, x ∈ E → Subgroup.centralizer ({x} : Set G) ≤ E ∧
      ∀ y ∈ D, y ∈ E → ∃ e ∈ E, e * x * e⁻¹ = y)
    (hc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x → x ≠ y → x * y ∈ E →
      Subgroup.centralizer ({x * y} : Set G) ≤ E)
    (hDc : ∀ z ∈ D, ∀ g : G, g⁻¹ * z * g ∈ D) : IsProductDisconnected D E := by
  refine ⟨hE, ha, fun z hz hzE g => ⟨fun hg => ?_, fun hg => ?_⟩, fun u hu huE => ?_⟩
  · obtain ⟨e, heE, he⟩ := (hb z hz hzE).2 _ (hDc z hz g) hg
    have hc' : g * e ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : g * (e * z * e⁻¹) * g⁻¹ = z := by rw [he]; group
      calc g * e * z = g * (e * z * e⁻¹) * g⁻¹ * (g * e) := by group
        _ = z * (g * e) := by rw [h1]
    have hge : g * e ∈ E := (hb z hz hzE).1 hc'
    simpa using E.mul_mem hge (E.inv_mem heE)
  · exact E.mul_mem (E.mul_mem (E.inv_mem hg) hzE) hg
  · obtain ⟨hu2, x, hx, y, hy, hxy, rfl⟩ := hu
    have hne : x ≠ y := by
      rintro rfl
      have hx2 : x * x = 1 := by
        have := pow_orderOf_eq_one x
        rwa [hD2 x hx, pow_two] at this
      rw [hx2, orderOf_one] at hu2
      exact absurd hu2 (by norm_num)
    exact hc x hx y hy hxy hne huE

theorem fusionBenderBorel_of_isBenderGroup [Finite G] (h : CFSG.BenderSuzuki.IsBenderGroup G) :
    ∃ q k : ℕ, CFSG.Open.fusionBenderBorel G q k := by
  rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · have : Finite PSL(2, GaloisField 2 n) := Finite.of_equiv G e.toEquiv
    exact ⟨_, _, (CFSG.Open.bender_psl2_borel_full n hn).map_mulEquiv e.symm⟩
  · let e' : G ≃* CFSG.Open.Sz n :=
      e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz n))
    have : Finite (CFSG.Open.Sz n) := Finite.of_equiv G e'.toEquiv
    exact ⟨_, _, (CFSG.Open.bender_suzuki_borel_full n hn).map_mulEquiv e'.symm⟩
  · have hm : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
        CFSG.Models.benderPSU3Model_eq_psu3 n
    let e' : G ≃* CFSG.Open.PSU3 2 n := e.trans (MulEquiv.subgroupCongr hm)
    have : Finite (CFSG.Open.PSU3 2 n) := Finite.of_equiv G e'.toEquiv
    exact ⟨_, _, (CFSG.Open.bender_psu3_borel_full n hn).map_mulEquiv e'.symm⟩

theorem isStronglyEmbedded_normalizer_of_isBenderGroup [Finite G]
    (h : CFSG.BenderSuzuki.IsBenderGroup G) (S : Sylow 2 G) :
    IsStronglyEmbedded (Subgroup.normalizer ((S : Subgroup G) : Set G)) := by
  obtain ⟨q, k, hF⟩ := fusionBenderBorel_of_isBenderGroup h
  obtain ⟨hne, hev, hodd⟩ := (hF S).1
  exact ⟨hne, hev, hodd⟩

theorem lieModel_of_isBenderGroup (h : CFSG.BenderSuzuki.IsBenderGroup G) :
    (∃ f : ℕ, 2 ≤ f ∧ (LieModel G .PSL 2 2 f ∨ LieModel G .PSU 3 2 f)) ∨
      ∃ a : ℕ, 1 ≤ a ∧ LieModel G .twistedB2 0 2 (2 * a + 1) := by
  rcases h with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · refine Or.inl ⟨n, hn, Or.inl (Or.inl ⟨by decide, ?_⟩)⟩
    refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, GaloisField 2 n, inferInstance,
      inferInstance, GaloisField.card 2 n (by omega),
      ⟨e.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
        (GaloisField 2 n))⟩⟩
    · intro hq
      simp only [Prod.mk.injEq, true_and] at hq
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    · intro hq
      simp only [Prod.mk.injEq, true_and] at hq
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
  · refine Or.inr ⟨n, hn, Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))⟩
    exact CFSG.GH74.Bender.suzukiModel_of_mulEquiv_sz hn
      (e.trans (MulEquiv.subgroupCongr (CFSG.GH74.Bender.szModel_eq_sz n)))
  · exact Or.inl ⟨n, hn, Or.inr (Or.inl ⟨by decide,
      (CFSG.RankTwoShapes.statedClassicalModel_PSU_three_two_iff G n hn).2 ⟨e⟩⟩)⟩

theorem product_disconnected_bender_recognition
    [Finite G] (hs : IsSimpleGroup G)
    (hna : ∃ a b : G, a * b ≠ b * a) (E : Subgroup G) (hE : E ≠ ⊤) (D : Set G)
    (hD : ∃ d : G, orderOf d = 2 ∧ D = {x : G | IsConj d x})
    (ha : (D ∩ (E : Set G)).Nonempty)
    (hb : ∀ x ∈ D, x ∈ E → Subgroup.centralizer ({x} : Set G) ≤ E ∧
      ∀ y ∈ D, y ∈ E → ∃ e ∈ E, e * x * e⁻¹ = y)
    (hc : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x → x ≠ y → x * y ∈ E →
      Subgroup.centralizer ({x * y} : Set G) ≤ E) :
    IsStronglyEmbedded E ∧ (∃ S : Sylow 2 G, E = Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      ((∃ f : ℕ, 2 ≤ f ∧ (LieModel G .PSL 2 2 f ∨ LieModel G .PSU 3 2 f)) ∨
        ∃ a : ℕ, 1 ≤ a ∧ LieModel G .twistedB2 0 2 (2 * a + 1)) := by
  obtain ⟨d, hd, rfl⟩ := hD
  have hZ := isInvariantInvolutionSet_of_isConj hd
  have hPD := isProductDisconnected_of_class E hE _ hZ.1 ha hb hc hZ.2
  obtain ⟨hB, S, hS⟩ := S_CorZD_unconditional G hs hna _ E hZ hPD
  refine ⟨?_, ⟨S, hS⟩, lieModel_of_isBenderGroup hB⟩
  rw [hS]
  exact isStronglyEmbedded_normalizer_of_isBenderGroup hB S

end CFSG.Quasithin.Recognition
