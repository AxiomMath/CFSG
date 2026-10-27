module

public import CFSG.Quasithin.Background.F918V3Stmt
public import CFSG.Quasithin.Background.F918V3S1
public import CFSG.Quasithin.Background.F918V3S2
public import CFSG.Quasithin.Background.F918V3S3
public import CFSG.Quasithin.Background.F918V3Z3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

theorem d392_assemble (hS : D392Suzuki)
    (h3 : ∀ (W : Type) [CommGroup W] [Finite W] (M K : Subgroup (MulAut W)),
      IsQuotientOfSQTKTC ↥M → IsComponentOf K M → ¬ IsSuzukiComponent K → 3 ∣ Nat.card ↥K) :
    D392 := by
  intro W _ _ M Mp T L V hD hMp hqM hcase A hA hAT hunf
  have hSz := hS W M Mp T L V hD hMp hqM hcase A hA hAT hunf
  subst hMp
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, -⟩ := QhatStar_spec hA
  have hAM : A ≤ M := hA2.le
  have hAel : IsElemAbelian2 A := hA2.isElemAbelian2
  have hMn : ∀ m ∈ M, ∀ l ∈ Mp, m * l * m⁻¹ ∈ Mp := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal hm)) l).1 hl
  have hLle : Mp ≤ M := le_of_mem_cComp hD.hyp.comp
  have hperf : ⁅Mp, Mp⁆ = Mp := hD.hyp.comp.2.1
  have hL1 : Mp ≠ ⊥ := hD.hyp.comp.1
  have hAL : ∀ a ∈ A, ∀ y ∈ Mp, a⁻¹ * y * a ∈ Mp := by
    intro a ha y hy
    have := hMn a⁻¹ (M.inv_mem (hAM ha)) y hy
    simpa using this
  set B₀ : Subgroup (MulAut W) := A ⊓ Subgroup.centralizer (Mp : Set (MulAut W)) with hB₀
  have hB₀A : B₀ ≤ A := inf_le_left
  have hBL : ∀ b ∈ B₀, ∀ x ∈ Mp, b * x = x * b := fun b hb x hx =>
    (Subgroup.mem_centralizer_iff.mp hb.2 x hx).symm
  have hB₀ne : B₀ ≠ ⊥ := by
    obtain ⟨a, ha, ha1, hac⟩ := hunf
    intro h
    have : a ∈ B₀ := ⟨ha, Subgroup.mem_centralizer_iff.mpr fun x hx => (hac x hx).symm⟩
    rw [h, Subgroup.mem_bot] at this
    exact ha1 this
  have hB₀n : ∀ a ∈ A, ∀ b ∈ B₀, a * b * a⁻¹ ∈ B₀ := by
    intro a ha b hb
    refine ⟨A.mul_mem (A.mul_mem ha hb.1) (A.inv_mem ha), Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    have hy : a⁻¹ * x * a ∈ Mp := hAL a ha x hx
    have h1 := hBL b hb _ hy
    calc x * (a * b * a⁻¹) = a * ((a⁻¹ * x * a) * b) * a⁻¹ := by group
      _ = a * (b * (a⁻¹ * x * a)) * a⁻¹ := by rw [← h1]
      _ = a * b * a⁻¹ * x := by group
  have hO2 : pCoreOf 2 M = ⊥ := D31.pCoreOf_eq_bot hD.hyp
  have hL : IsComponentOf Mp M :=
    ⟨hLle, hD.hyp.comp.2.2.1, ⟨have := hD.hyp.quasi.1; Group.IsPerfect.commutator_eq_top,
      hD.hyp.quasi.2.1⟩⟩
  have hB₀2 : IsPGroup 2 B₀ := hAel.isPGroup.to_le hB₀A
  have hcentr : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ a ∈ A, ∀ x ∈ pCoreOf q M, a * x = x * a :=
    fun q hq hq3 => d392_centralizes_pCore hD hA hq hq3
  have hOcomm : ∀ (q : ℕ) (hq : q.Prime), ∀ x ∈ pCoreOf q M, ∀ l ∈ Mp, x * l = l * x := by
    intro q hq x hx l hl
    have : Fact q.Prime := ⟨hq⟩
    have hPn : ∀ m ∈ M, ∀ g ∈ pCoreOf q M, m * g * m⁻¹ ∈ pCoreOf q M := fun m hm g hg =>
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf q M hm) g).mp hg
    exact v3_commute_of_isPGroup_normal hq hD.hyp.quasi hperf hL1 hMn hLle
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup q M) hPn (CFSG.LieType.BorelTits.pCoreOf_le q M)
      x hx l hl
  rcases d392_exists_acted hO2 hL (hB₀A.trans hAM) hB₀2 hB₀ne hBL with
    ⟨q, hq, hq2, hqne⟩ | ⟨K, hK, hKL, hKB⟩
  ·
    have hq3 : q = 3 := by
      by_contra hq3
      apply hqne
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hcentr q hq hq3 b (hB₀A hb) x hx
    subst hq3
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨X, hXP, hXcard, hXA, hXB⟩ := d392_order_three
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 M) hAel
      (hAM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 M)) hB₀A hqne
    refine ⟨X, ?_, hXP.trans (CFSG.LieType.BorelTits.pCoreOf_le 3 M) |> fun h => h, ?_, hXA, hXB,
      Or.inr ⟨hXP, hXcard⟩, fun q' hq' hq3' => hcentr q' hq' hq3', hSz, ?_⟩
    · intro h
      rw [h] at hXcard
      simp at hXcard
    · intro x hx y hy
      exact hOcomm 3 Nat.prime_three x (hXP hx) y hy
    · rw [hXcard]
  ·
    have hKB' : ⁅K, B₀⁆ ≠ ⊥ := hKB
    obtain ⟨hX1, hXM, hXL, hXA, hXB⟩ := d392_component_case (M := M) (L := Mp) (A := A) (B₀ := B₀)
      (K := K) (X := ⨆ a ∈ A, conjAutSub a K) hAM hAL hB₀A hB₀n hK hKL hKB' rfl
    have hKns : ¬ IsSuzukiComponent K := by
      intro hsz
      apply hKB'
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact hSz K hK hsz hKL b (hB₀A hb) x hx
    have hKX : K ≤ ⨆ a ∈ A, conjAutSub a K := by
      have h1 : conjAutSub (1 : MulAut W) K = K := by
        ext x
        simp [conjAutSub, Subgroup.mem_map]
      calc K = conjAutSub (1 : MulAut W) K := h1.symm
        _ ≤ ⨆ a ∈ A, conjAutSub a K :=
          le_iSup₂ (f := fun a (_ : a ∈ A) => conjAutSub a K) 1 A.one_mem
    refine ⟨⨆ a ∈ A, conjAutSub a K, hX1, hXM, hXL, hXA, hXB, Or.inl ⟨K, hK, hKns, rfl⟩,
      fun q' hq' hq3' => hcentr q' hq' hq3', hSz, ?_⟩
    exact (h3 W M K hD.hyp.qsqtk hK hKns).trans (Subgroup.card_dvd_of_le hKX)

end CFSG.Quasithin
