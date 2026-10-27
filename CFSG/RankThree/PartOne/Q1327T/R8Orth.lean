module

public import CFSG.RankThree.PartOne.Q1327T.R8Homo
import CFSG.RankThree.PartOne.Q1327T.R8Weir
import CFSG.GroupTheory.WeirSylow.Orthogonal
import CFSG.Timmesfeld.Orders.ClassicalOmega
import CFSG.RankThree.PartOne.KF.ClsOmegaMinusUpper
public import CFSG.RankThree.PartOne.N143X.EvenSmall

public section

namespace CFSG.RankThree.PartOne.Q1327T.R8

open CFSG CFSG.Assembly.LowTwoRank CFSG.GroupTheory.WeirSylow CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin
open scoped commutatorElement

theorem sp4_rank_cases {e : ℕ} (he : 0 < e) (hne : ¬ e ∣ 4) :
    (if Even e then 2 * 4 else 4) / e < 2 := by
  by_cases hev : Even e
  · rw [ite_eq_left hev]
    obtain ⟨k, hk⟩ := hev
    have h6 : 6 ≤ e := by
      by_contra h
      have : e = 2 ∨ e = 4 := by omega
      rcases this with rfl | rfl <;> exact hne (by norm_num)
    exact (Nat.div_lt_iff_lt_mul he).2 (by omega)
  · rw [ite_eq_right hev]
    have h3 : 3 ≤ e := by
      by_contra h
      have : e = 1 ∨ e = 2 := by omega
      rcases this with rfl | rfl
      · exact hne (by norm_num)
      · exact hev ⟨1, rfl⟩
    exact (Nat.div_lt_iff_lt_mul he).2 (by omega)

abbrev Om4 : Type := Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2

private theorem card_orthogonalMinus_eq_two_mul {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) =
      2 * Nat.card (StatedOmega (StatedQuadMinus 4 K b c)) := by
  have hpow : ∀ i : ℕ, ((Nat.card K : ℤ) ^ 2) ^ i = (Nat.card K : ℤ) ^ (2 * i) :=
    fun i => (pow_mul _ 2 i).symm
  have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ 12 * ((Nat.card K : ℤ) ^ 4 + 1) *
        ∏ i ∈ Finset.Icc 1 3, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    have := natCard_orthogonalGroup_quadMinus hirr 3
    simp only [hpow] at this
    exact this
  have hΩ : (Nat.card (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) : ℤ) =
      (Nat.card K : ℤ) ^ 12 * ((Nat.card K : ℤ) ^ 4 + 1) *
        ∏ i ∈ Finset.Icc 1 3, ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega_quadMinus (n := 4) (K := K)
      (by norm_num) hirr
  have hbot := CFSG.RankThree.PartOne.KFU.statedScalars_subgroupOf_statedOmega_quadMinus_eq_bot
    (K := K) (b := b) (c := c)
  have hproj : Nat.card (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) =
      Nat.card (StatedOmega (StatedQuadMinus 4 K b c)) :=
    (Nat.card_congr (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).toEquiv).symm
  rw [hproj] at hΩ
  zify
  rw [hO, hΩ]
  ring

private theorem isMinusType_quadMinus_four {K : Type} [Field K] [Finite K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : IsMinusType (quadMinus 4 K b c) := by
  refine ⟨?_, not_isPlusType_quadMinus (by norm_num) hirr⟩
  obtain ⟨-, T, hT, hT0⟩ := regular_quadMinus (n := 4) (K := K) (b := b) (c := c) (by norm_num)
    hirr
  refine ⟨T, ?_, hT0⟩
  rw [hT, Module.finrank_fintype_fun_eq_card]
  simp [Fintype.card_sum]

theorem mem_of_pPow_eq_one_of_index_two {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] (hN : N.index = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : G} {k : ℕ}
    (hx : x ^ (p ^ k) = 1) : x ∈ N := by
  have h1 : (QuotientGroup.mk' N x) ^ (p ^ k) = 1 := by rw [← map_pow, hx, map_one]
  have h2 : (QuotientGroup.mk' N x) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := G ⧸ N) (x := QuotientGroup.mk' N x)
    rwa [← Subgroup.index_eq_card, hN] at this
  have h3 : orderOf (QuotientGroup.mk' N x) ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have h4 : orderOf (QuotientGroup.mk' N x) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (p ^ k) 2 := by
    refine Nat.Coprime.pow_left k ?_
    exact (Nat.coprime_primes hp Nat.prime_two).2 hp2
  have h5 : orderOf (QuotientGroup.mk' N x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h3 h4
  have h6 : QuotientGroup.mk' N x = 1 := orderOf_eq_one_iff.1 h5
  exact (QuotientGroup.eq_one_iff x).1 h6

theorem false_of_plane_omegaMinus8 {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (F : Subgroup (GL Om4 K))
    (hFM : F ≤ StatedOmega (StatedQuadMinus 4 K b c)) [IsElementaryAbelian p F]
    (hFc : Nat.card F = p ^ 2)
    (hmax : ∀ D : Subgroup (GL Om4 K), D ≤ StatedOmega (StatedQuadMinus 4 K b c) →
      IsElementaryAbelian p D → F ≤ D → D ≤ Subgroup.centralizer (F : Set (GL Om4 K)) →
      Nat.card D ≤ Nat.card F) : False := by
  classical
  have hp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have hp1 : Odd p := hp.odd_of_ne_two hp2
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K 2 := N143X.charP_two_of_card hK
  have hKc : Fintype.card K = 2 ^ f := by rw [Fintype.card_eq_nat_card, hK]
  have hpK : ¬ p ∣ Fintype.card K := by rw [hKc]; exact not_dvd_two_pow hp hp2
  let Q : QuadraticForm K (Om4 → K) := quadMinus 4 K b c
  let O : Subgroup ((Om4 → K) ≃ₗ[K] (Om4 → K)) := TauCeti.QuadraticMap.orthogonalGroup Q
  let Φ : GL Om4 K ≃* ((Om4 → K) ≃ₗ[K] (Om4 → K)) := toLinEquiv Om4 K
  let Ω₀ : Subgroup ((Om4 → K) ≃ₗ[K] (Om4 → K)) := ⁅O, O⁆
  have hMeq : StatedOmega (StatedQuadMinus 4 K b c) = Ω₀.comap Φ.toMonoidHom :=
    statedOmega_eq_comap (coe_quadMinus 4 K b c)
  have : Finite ((Om4 → K) ≃ₗ[K] (Om4 → K)) :=
    Finite.of_injective (fun g : (Om4 → K) ≃ₗ[K] (Om4 → K) => (g : (Om4 → K) → (Om4 → K)))
      DFunLike.coe_injective
  have hΩO : Ω₀ ≤ O := by
    rw [Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    rw [commutatorElement_def]
    exact O.mul_mem (O.mul_mem (O.mul_mem h₁ h₂) (O.inv_mem h₁)) (O.inv_mem h₂)
  have hcardMΩ : Nat.card (StatedOmega (StatedQuadMinus 4 K b c)) = Nat.card Ω₀ := by
    have key : Ω₀.comap Φ.toMonoidHom = Ω₀.map Φ.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm Φ Ω₀
    rw [hMeq, key]
    exact Subgroup.card_map_of_injective (MulEquiv.injective _)
  have hcardO : Nat.card O = 2 * Nat.card Ω₀ := by
    have h1 := card_orthogonalMinus_eq_two_mul (K := K) (b := b) (c := c) hirr
    rw [hcardMΩ] at h1
    exact h1
  let N : Subgroup ↥O := Ω₀.subgroupOf O
  have hNnormal : N.Normal := by
    refine ⟨fun x hx y => ?_⟩
    have hxΩ : (x : (Om4 → K) ≃ₗ[K] (Om4 → K)) ∈ Ω₀ := hx
    have hxO : (x : (Om4 → K) ≃ₗ[K] (Om4 → K)) ∈ O := x.2
    have hcomm : ⁅(y : (Om4 → K) ≃ₗ[K] (Om4 → K)), (x : (Om4 → K) ≃ₗ[K] (Om4 → K))⁆ ∈ Ω₀ :=
      Subgroup.commutator_mem_commutator y.2 hxO
    show ((y * x * y⁻¹ : ↥O) : (Om4 → K) ≃ₗ[K] (Om4 → K)) ∈ Ω₀
    have : ((y * x * y⁻¹ : ↥O) : (Om4 → K) ≃ₗ[K] (Om4 → K)) =
        ⁅(y : (Om4 → K) ≃ₗ[K] (Om4 → K)), (x : (Om4 → K) ≃ₗ[K] (Om4 → K))⁆ *
          (x : (Om4 → K) ≃ₗ[K] (Om4 → K)) := by
      rw [commutatorElement_def]
      simp [mul_assoc]
    rw [this]
    exact Ω₀.mul_mem hcomm hxΩ
  have hNindex : N.index = 2 := by
    have h1 := Subgroup.card_mul_index N
    have h2 : Nat.card N = Nat.card Ω₀ := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩO).toEquiv
    rw [h2, hcardO] at h1
    have hpos : 0 < Nat.card Ω₀ := Nat.card_pos
    nlinarith
  have hpO : ∀ x : ↥O, x ^ p = 1 → (x : (Om4 → K) ≃ₗ[K] (Om4 → K)) ∈ Ω₀ := fun x hx =>
    mem_of_pPow_eq_one_of_index_two (N := N) hNindex hp hp2 (k := 1) (by simpa using hx)
  let Famb : Subgroup ((Om4 → K) ≃ₗ[K] (Om4 → K)) := F.map Φ.toMonoidHom
  have hFambel : IsElementaryAbelian p Famb := IsElementaryAbelian.map _
  have hFamb_le : Famb ≤ Ω₀ := by
    rintro _ ⟨x, hx, rfl⟩
    have : x ∈ Ω₀.comap Φ.toMonoidHom := hMeq ▸ hFM hx
    exact this
  let FO : Subgroup ↥O := Famb.subgroupOf O
  have hFOel : IsElementaryAbelian p FO := IsElementaryAbelian.subgroupOf (hFamb_le.trans hΩO)
  have hFOc : Nat.card FO = p ^ 2 := by
    rw [← hFc]
    calc Nat.card FO = Nat.card Famb :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hFamb_le.trans hΩO)).toEquiv
      _ = Nat.card F := Subgroup.card_map_of_injective (MulEquiv.injective _)
  refine false_of_homocyclic_sylow (F := FO) (r := 0) hFOc (fun D hD hFD hDc => ?_) (fun S => ?_)
  ·
    have hDsub : ∀ x ∈ D, (x : (Om4 → K) ≃ₗ[K] (Om4 → K)) ∈ Ω₀ := fun x hx =>
      hpO x (elemPow_eq_one_of_isElementaryAbelian (A := D) x hx)
    let Damb : Subgroup ((Om4 → K) ≃ₗ[K] (Om4 → K)) := D.map O.subtype
    have hDambel : IsElementaryAbelian p Damb := IsElementaryAbelian.map_subtype
    let Dgl : Subgroup (GL Om4 K) := Damb.map Φ.symm.toMonoidHom
    have hDglel : IsElementaryAbelian p Dgl := IsElementaryAbelian.map _
    have hmem : ∀ x : GL Om4 K, x ∈ Dgl ↔ Φ x ∈ Damb := by
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨Φ x, hx, by simp⟩
    have hDglM : Dgl ≤ StatedOmega (StatedQuadMinus 4 K b c) := by
      intro x hx
      rw [hMeq]
      obtain ⟨d, hd, hdx⟩ := (hmem x).1 hx
      show Φ x ∈ Ω₀
      rw [← hdx]
      exact hDsub d hd
    have hFDgl : F ≤ Dgl := by
      intro x hx
      rw [hmem]
      have hxFamb : Φ x ∈ Famb := ⟨x, hx, rfl⟩
      have hxO : Φ x ∈ O := hΩO (hFamb_le hxFamb)
      have : (⟨Φ x, hxO⟩ : ↥O) ∈ FO := hxFamb
      exact ⟨_, hFD this, rfl⟩
    have hcentGl : Dgl ≤ Subgroup.centralizer (F : Set (GL Om4 K)) := by
      intro d hd f hf
      obtain ⟨d', hd', hdd'⟩ := (hmem d).1 hd
      have hfF : (⟨Φ f, hΩO (hFamb_le ⟨f, hf, rfl⟩)⟩ : ↥O) ∈ FO := ⟨f, hf, rfl⟩
      have h3 := Subgroup.mem_centralizer_iff.1 (hDc hd') _ hfF
      have h2 : Φ f * Φ d = Φ d * Φ f := by
        have h4 := congrArg Subtype.val h3
        rw [← hdd']
        exact h4
      exact Φ.injective (by rw [map_mul, map_mul]; exact h2)
    have h1 := hmax Dgl hDglM hDglel hFDgl hcentGl
    have hcard : Nat.card D = Nat.card Dgl := by
      calc Nat.card D = Nat.card Damb := (Subgroup.card_map_of_injective O.subtype_injective).symm
        _ = Nat.card Dgl := (Subgroup.card_map_of_injective (MulEquiv.injective _)).symm
    calc Nat.card D = Nat.card Dgl := hcard
      _ ≤ Nat.card F := h1
      _ = p ^ 2 := hFc
      _ = p ^ (0 + 2) := by rw [zero_add]
  ·
    have hV : Module.finrank K (Om4 → K) = 2 * 4 := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp [Fintype.card_sum]
    have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
      nondegenerate_polarBilin_quadMinus_of_finite 4 K hirr
    have hmin : IsMinusType Q := isMinusType_quadMinus_four hirr
    obtain ⟨h1, h2, h3⟩ := sylow_orthogonal_even hp1 hpK (V := Om4 → K) (n := 4) (by norm_num)
      hV Q hQnd (ε := -1) (Or.inr ⟨rfl, hmin⟩) S
    have he : 0 < weirE p K := weirE_pos hpK
    have ha : 1 ≤ weirA p K := one_le_weirA hpK
    by_cases hdiv : (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 4 - 1
    ·
      have hnd : ¬ (p : ℤ) ∣ (Fintype.card K : ℤ) ^ 4 - (-1) := by
        rcases h3 with h | h
        · exact absurd (by simpa [sub_eq_add_neg] using hdiv) h
        · exact h
      obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp (4 - 1) K)) := inferInstance
      obtain ⟨φ⟩ := h2 hnd P'
      obtain ⟨ψ⟩ := sylow_Sp hp1 K hpK (4 - 1) P'
      obtain ⟨hle3, hcases⟩ := sp3_rank_cases he
      have hle3' : (if Even (weirE p K) then 2 * (4 - 1) else (4 - 1)) / weirE p K ≤ 3 := hle3
      refine ⟨(if Even (weirE p K) then 2 * (4 - 1) else (4 - 1)) / weirE p K, weirA p K, ha, ?_,
        hcases⟩
      obtain ⟨χ⟩ := nonempty_sigmaModel_mulEquiv_homo (p := p) (e := weirE p K)
        (a := weirA p K) (N := if Even (weirE p K) then 2 * (4 - 1) else (4 - 1)) (by omega)
      exact ⟨φ.trans (ψ.trans χ)⟩
    ·
      have h1' := h1 (by simpa [sub_eq_add_neg] using hdiv)
      obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp 4 K)) := inferInstance
      obtain ⟨φ⟩ := h1' P'
      obtain ⟨ψ⟩ := sylow_Sp hp1 K hpK 4 P'
      have hne : ¬ weirE p K ∣ 4 := fun h =>
        hdiv ((dvd_pow_sub_one_iff_weirE (p := p) (K := K) 4).2 h)
      have hlt2 := sp4_rank_cases he hne
      refine ⟨(if Even (weirE p K) then 2 * 4 else 4) / weirE p K, weirA p K, ha, ?_,
        Or.inl hlt2⟩
      obtain ⟨χ⟩ := nonempty_sigmaModel_mulEquiv_homo (p := p) (e := weirE p K)
        (a := weirA p K) (N := if Even (weirE p K) then 2 * 4 else 4) (by omega)
      exact ⟨φ.trans (ψ.trans χ)⟩

end CFSG.RankThree.PartOne.Q1327T.R8
