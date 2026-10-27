module

public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped Pointwise

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem uc22r8100b_exists_conj {q : ℕ} [Fact q.Prime] {K S S' : Subgroup Γ}
    (hS : IsSylowOf q S K) (hS' : IsSylowOf q S' K) :
    ∃ k ∈ K, ∀ x : Γ, x ∈ S' ↔ k⁻¹ * x * k ∈ S := by
  obtain ⟨P, rfl⟩ := hS
  obtain ⟨P', rfl⟩ := hS'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P P'
  have hc : ∀ s : K, s ∈ ((g • P : Sylow q K) : Subgroup K) ↔ g⁻¹ * s * g ∈ (P : Subgroup K) := by
    intro s
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s', hs', rfl⟩
      have e : g⁻¹ * (g * s' * g⁻¹) * g = s' := by group
      simp only [MulAut.smul_def, MulAut.conj_apply]
      rw [e]
      exact hs'
    · intro hs
      exact ⟨g⁻¹ * s * g, hs, by simp [MulAut.smul_def]; group⟩
  refine ⟨g, g.2, fun x => ?_⟩
  rw [← hg]
  simp only [Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨g⁻¹ * s * g, (hc s).1 hs, by simp⟩
  · rintro ⟨s, hs, hsx⟩
    have e : g⁻¹ * (g * s * g⁻¹) * g = s := by group
    refine ⟨g * s * g⁻¹, (hc _).2 (by rw [e]; exact hs), ?_⟩
    have : x = (g : Γ) * s * (g : Γ)⁻¹ := by
      rw [hsx]
      group
    simpa using this.symm

theorem uc22r8100b_frattini {q : ℕ} [Fact q.Prime] {K S : Subgroup Γ} (hS : IsSylowOf q S K)
    {y : Γ} (hy : y ∈ normalizer (K : Set Γ)) :
    ∃ k ∈ K, k⁻¹ * y ∈ normalizer (S : Set Γ) := by
  have hSK : S ≤ K := hS.le
  set S' : Subgroup Γ := S.map (MulAut.conj y).toMonoidHom with hS'
  have hS'K : S' ≤ K := by
    rintro _ ⟨s, hs, rfl⟩
    simpa [MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.1 hy s).1 (hSK hs)
  have hS'S : IsSylowOf q S' K := by
    refine isSylowOf_of_card hS'K ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hS.card_eq]
  obtain ⟨k, hk, hkx⟩ := uc22r8100b_exists_conj hS hS'S
  refine ⟨k, hk, Subgroup.mem_normalizer_iff.2 fun h => ?_⟩
  have h1 : h ∈ S ↔ y * h * y⁻¹ ∈ S' := by
    constructor
    · intro hh
      exact ⟨h, hh, by simp [MulAut.conj_apply]⟩
    · rintro ⟨h', hh', hh'e⟩
      have e1 : (MulAut.conj y) h' = (MulAut.conj y) h := by
        simpa [MulAut.conj_apply] using hh'e
      rwa [← (MulAut.conj y).injective e1]
  rw [h1, hkx]
  have e : k⁻¹ * (y * h * y⁻¹) * k = k⁻¹ * y * h * (k⁻¹ * y)⁻¹ := by group
  rw [e]

theorem uc22r8100b_card_ker {Y K B : Subgroup Γ} (hBY : B ≤ Y)
    [(K.subgroupOf Y).Normal] :
    Nat.card ((QuotientGroup.mk' (K.subgroupOf Y)).comp (Subgroup.inclusion hBY)).ker =
      Nat.card (B ⊓ K : Subgroup Γ) := by
  apply Nat.card_congr
  have hmem : ∀ x : ↥B, x ∈ ((QuotientGroup.mk' (K.subgroupOf Y)).comp
      (Subgroup.inclusion hBY)).ker ↔ (x : Γ) ∈ K := by
    intro x
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff _
  exact
    { toFun := fun x => ⟨(x.1 : Γ), x.1.2, (hmem x.1).1 x.2⟩
      invFun := fun x => ⟨⟨x.1, (Subgroup.mem_inf.1 x.2).1⟩, (hmem _).2 (Subgroup.mem_inf.1 x.2).2⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl }

theorem uc22r8100b_exists_elemAbelian_le_normalizer {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K H S A : Subgroup Γ} (hKH : K ≤ H) (hH : H ≤ normalizer (K : Set Γ))
    (hS : IsSylowOf q S K) (hKS : ∀ y ∈ K, y ∈ normalizer (S : Set Γ) → orderOf y ≠ p)
    (hA : IsElemAbelian p A) (hAH : A ≤ H) :
    ∃ D : Subgroup Γ, D ≤ H ⊓ normalizer (S : Set Γ) ∧ IsElemAbelian p D ∧
      Nat.card A = Nat.card (A ⊓ K : Subgroup Γ) * Nat.card D := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  set Y : Subgroup Γ := K ⊔ A with hY
  have hKY : K ≤ Y := le_sup_left
  have hAY : A ≤ Y := le_sup_right
  have hYH : Y ≤ H := sup_le hKH hAH
  have hYN : Y ≤ normalizer (K : Set Γ) := hYH.trans hH
  set N : Subgroup Γ := Y ⊓ normalizer (S : Set Γ) with hN
  have hNY : N ≤ Y := inf_le_left
  have hNS : N ≤ normalizer (S : Set Γ) := inf_le_right
  obtain ⟨D, hD⟩ := exists_isSylowOf p N
  have hDN : D ≤ N := hD.le
  have hDY : D ≤ Y := hDN.trans hNY
  have hDp : IsPGroup p D := hD.isPGroup
  have hcop : ¬ p ∣ Nat.card (N ⊓ K : Subgroup Γ) := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(N ⊓ K)) p hdvd
    have hxK : (x : Γ) ∈ K := (Subgroup.mem_inf.1 x.2).2
    have hxS : (x : Γ) ∈ normalizer (S : Set Γ) := hNS (Subgroup.mem_inf.1 x.2).1
    exact hKS _ hxK hxS (by rw [Subgroup.orderOf_coe]; exact hx)
  have hDK : D ⊓ K = ⊥ := by
    have hQp : IsPGroup p ↥(D ⊓ K) := hDp.to_inf_left
    rcases hQp.card_eq_or_dvd with h1 | h1
    · exact Subgroup.card_eq_one.1 h1
    · exact absurd (h1.trans (Subgroup.card_dvd_of_le (inf_le_inf_right K hDN))) hcop
  haveI hKn : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 hYN
  let π : ↥Y →* ↥Y ⧸ K.subgroupOf Y := QuotientGroup.mk' (K.subgroupOf Y)
  let φA : ↥A →* ↥Y ⧸ K.subgroupOf Y := π.comp (Subgroup.inclusion hAY)
  let φN : ↥N →* ↥Y ⧸ K.subgroupOf Y := π.comp (Subgroup.inclusion hNY)
  have hπ1 : ∀ (k : Γ) (hk : k ∈ K) (hkY : k ∈ Y), π ⟨k, hkY⟩ = 1 := fun k hk hkY =>
    (QuotientGroup.eq_one_iff (⟨k, hkY⟩ : ↥Y)).2 (Subgroup.mem_subgroupOf.2 hk)
  have hφA : Function.Surjective φA := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : Γ) ∈ (K : Set Γ) * (A : Set Γ) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left K A (hAH.trans hH)]
        exact y.2
      obtain ⟨k, hk, a, ha, hka⟩ := Set.mem_mul.1 hy
      have hkY : k ∈ Y := hKY hk
      have haY : a ∈ Y := hAY ha
      have hyeq : y = ⟨k, hkY⟩ * ⟨a, haY⟩ := Subtype.ext hka.symm
      have hincl : Subgroup.inclusion hAY ⟨a, ha⟩ = (⟨a, haY⟩ : ↥Y) := rfl
      refine ⟨⟨a, ha⟩, ?_⟩
      change π (Subgroup.inclusion hAY ⟨a, ha⟩) = π y
      rw [hincl, hyeq, map_mul, hπ1 k hk hkY, one_mul]
  have hφN : Function.Surjective φN := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H y =>
      obtain ⟨k, hk, hkn⟩ := uc22r8100b_frattini hS (hYN y.2)
      have hkY : k ∈ Y := hKY hk
      have hnN : k⁻¹ * (y : Γ) ∈ N :=
        Subgroup.mem_inf.2 ⟨Y.mul_mem (Y.inv_mem hkY) y.2, hkn⟩
      have hincl : Subgroup.inclusion hNY ⟨k⁻¹ * (y : Γ), hnN⟩ = (⟨k, hkY⟩ : ↥Y)⁻¹ * y :=
        Subtype.ext rfl
      refine ⟨⟨k⁻¹ * (y : Γ), hnN⟩, ?_⟩
      change π (Subgroup.inclusion hNY ⟨k⁻¹ * (y : Γ), hnN⟩) = π y
      rw [hincl, map_mul, map_inv, hπ1 k hk hkY, inv_one, one_mul]
  have hQc : ∀ x y : ↥Y ⧸ K.subgroupOf Y, x * y = y * x := by
    haveI := hA.1
    intro x y
    obtain ⟨a, rfl⟩ := hφA x
    obtain ⟨b, rfl⟩ := hφA y
    rw [← map_mul, ← map_mul, mul_comm' a b]
  have hQe : ∀ x : ↥Y ⧸ K.subgroupOf Y, x ^ p = 1 := by
    intro x
    obtain ⟨a, rfl⟩ := hφA x
    have h : a ^ p = 1 := Subtype.ext (by simpa using hA.2 (a : Γ) a.2)
    rw [← map_pow, h, map_one]
  have hQp : IsPGroup p (↥Y ⧸ K.subgroupOf Y) := fun x => ⟨1, by rw [pow_one]; exact hQe x⟩
  obtain ⟨m, hm⟩ := hQp.exists_card_eq
  have hAcard : Nat.card A = Nat.card (A ⊓ K : Subgroup Γ) * p ^ m := by
    rw [← hm, ← uc22r8100b_card_ker hAY]
    exact (Subgroup.card_ker_mul_card_of_surjective hφA).symm
  have hNcard : Nat.card N = Nat.card (N ⊓ K : Subgroup Γ) * p ^ m := by
    rw [← hm, ← uc22r8100b_card_ker hNY]
    exact (Subgroup.card_ker_mul_card_of_surjective hφN).symm
  have hpos : 0 < Nat.card (N ⊓ K : Subgroup Γ) := Nat.card_pos
  have hfac : (Nat.card N).factorization p = m := by
    rw [hNcard, Nat.factorization_mul hpos.ne' (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hcop, hp.factorization_pow, Finsupp.single_eq_same,
      zero_add]
  have hDcard : Nat.card D = p ^ m := by rw [hD.card_eq, hfac]
  let ι : ↥D →* ↥Y ⧸ K.subgroupOf Y := π.comp (Subgroup.inclusion hDY)
  have hι : ∀ x : ↥D, ι x = 1 → x = 1 := by
    intro x hx
    have h1 : (x : Γ) ∈ K :=
      Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (Subgroup.inclusion hDY x)).1 hx)
    have h2 : (x : Γ) ∈ D ⊓ K := Subgroup.mem_inf.2 ⟨x.2, h1⟩
    rw [hDK] at h2
    exact Subtype.ext (Subgroup.mem_bot.1 h2)
  have hDel : IsElemAbelian p D := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have h : (a * b)⁻¹ * (b * a) = 1 := by
        apply hι
        rw [map_mul, map_inv, map_mul, map_mul, hQc (ι a) (ι b), inv_mul_cancel]
      exact inv_mul_eq_one.1 h
    · have h : (⟨x, hx⟩ : ↥D) ^ p = 1 := by
        apply hι
        rw [map_pow, hQe]
      simpa using congrArg Subtype.val h
  exact ⟨D, le_inf (hDY.trans hYH) (hDN.trans hNS), hDel, by rw [hDcard]; exact hAcard⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
