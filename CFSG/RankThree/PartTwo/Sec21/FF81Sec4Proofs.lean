module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Step0
import CFSG.RankThree.PartTwo.Sec21.FF81P51
import CFSG.RankThree.PartTwo.Sec21.FF81Fusion
import CFSG.RankThree.PartTwo.Sec21.FF81Prop33
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.LocalAnalysis.StandardType.GGSixFusion

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

theorem ff81_4_11 : FF81_4_11 := by
  intro hSp G _ _ b L B b₁ b₂ b₃ t₀ h4 h44 hYm
  have hB := h4.basis
  set Y := Y4 b₃ t₀
  obtain ⟨hS1, hS2, -, -, -, -, -⟩ := hSp G Y hYm
  have hB4 := hB.mono.1
  obtain ⟨hbB, hb1B, hb2B, hb3B⟩ := hB.mem
  have ht₀2 : t₀ * t₀ = 1 := by
    have := pow_orderOf_eq_one t₀
    rwa [h4.ht₀, sq] at this
  have ht₀inv : t₀⁻¹ = t₀ := inv_eq_of_mul_eq_one_right ht₀2
  have hLt : ∀ x ∈ L, x ∈ Cen t₀ := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp h4.ht₀L x hx)
  have hCtY : Cen t₀ ≤ Y := by
    show Cen t₀ ≤ Cen t₀ ⊔ OUpp 2 (Cen b₃); exact le_sup_left
  have hOY : OUpp 2 (Cen b₃) ≤ Y := by
    show OUpp 2 (Cen b₃) ≤ Cen t₀ ⊔ OUpp 2 (Cen b₃); exact le_sup_right
  have hb₃t : t₀ * b₃ = b₃ * t₀ := (Subgroup.mem_centralizer_iff.mp h4.ht₀L b₃ hB.hb₃).symm
  have hb₃b : b₃ * b = b * b₃ :=
    Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hB.hb₃)
  have htb : t₀ * b ∈ Cen b₃ := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc t₀ * b * b₃ = t₀ * (b₃ * b) := by rw [mul_assoc, hb₃b]
      _ = b₃ * (t₀ * b) := by rw [← mul_assoc, hb₃t, mul_assoc]
  have htb2 : (t₀ * b) ^ (2 ^ 1) = 1 := by
    have e : t₀ * b * t₀ = b⁻¹ := by rw [← h4.ht₀b, ht₀inv]
    calc (t₀ * b) ^ (2 ^ 1) = (t₀ * b * t₀) * b := by rw [pow_one, sq]; group
      _ = 1 := by rw [e, inv_mul_cancel]
  have htbY : t₀ * b ∈ Y := hOY ⟨⟨t₀ * b, htb⟩,
    Subgroup.subset_normalClosure ⟨1, Subtype.ext (by simpa using htb2)⟩, rfl⟩
  have hbY : b ∈ Y := by
    have : b = t₀ * (t₀ * b) := by rw [← mul_assoc, ht₀2, one_mul]
    rw [this]
    exact Y.mul_mem (hCtY (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) htbY
  have hBY : B ≤ Y := by
    rw [hB.mono.2.1]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hbY
    · exact hCtY (hLt _ hB.hb₁)
    · exact hCtY (hLt _ hB.hb₂)
    · exact hCtY (hLt _ hB.hb₃)
  have hO : ∀ k, {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D}.ncard = k → k ≤ 4 := by
    intro k hk
    rw [← hk]
    have hsub : {D | ∃ n ∈ Nor B, conjBy n (Subgroup.zpowers b) = D} ⊆ ConjLines B b := by
      rintro D ⟨n, hn, rfl⟩
      refine ⟨?_, n, rfl⟩
      rw [conjBy_zpowers]
      exact Subgroup.zpowers_le.mpr ((Subgroup.mem_normalizer_iff.mp hn b).mp hbB)
    have hfin : (ConjLines B b).Finite := by rw [h4.caseI.2]; exact Set.toFinite _
    refine (Set.ncard_le_ncard hsub hfin).trans ?_
    rw [h4.caseI.2]
    have e1 := Set.ncard_insert_le (Subgroup.zpowers b)
      ({Subgroup.zpowers b₁, Subgroup.zpowers b₂, Subgroup.zpowers b₃} : Set (Subgroup G))
    have e2 := Set.ncard_insert_le (Subgroup.zpowers b₁)
      ({Subgroup.zpowers b₂, Subgroup.zpowers b₃} : Set (Subgroup G))
    have e3 := Set.ncard_insert_le (Subgroup.zpowers b₂) ({Subgroup.zpowers b₃} : Set (Subgroup G))
    have e4 := Set.ncard_singleton (Subgroup.zpowers b₃)
    omega
  have hA : autOrder B = 384 := by
    rcases kf_prop51 G B b b₁ b₂ b₃ hB.mono hB.cenOdd hB.stab hB.meet with
      ⟨-, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, -, h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    all_goals have := hO _ h; omega
  have hC := hB.cenS_eq h44
  have hNcard : Nat.card (Nor B) = 2 ^ 7 * 3 ^ 5 := by
    have e := Subgroup.relIndex_mul_card (CenS B) (Nor B)
    rw [inf_of_le_left (Subgroup.centralizer_le_normalizer _)] at e
    have hA' : (CenS B).relIndex (Nor B) = 384 := hA
    rw [hA', show Subgroup.centralizer (B : Set G) = B from hC, hB4.2] at e
    rw [← e]; norm_num
  have hNY : Nor B ≤ Y := by
    have hYN := (hS2 B hBY hB4).1
    have := Subgroup.eq_of_le_of_card_ge (inf_le_right : Y ⊓ Nor B ≤ Nor B)
      (by rw [hYN, hNcard])
    rw [← this]
    exact inf_le_left
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 (Nor B)) := inferInstance
  set P' := (P : Subgroup (Nor B)).map (Nor B).subtype with hP'
  have hP'p : IsPGroup 3 P' := P.isPGroup'.map _
  have hP'N : P' ≤ Nor B := Subgroup.map_subtype_le _
  have hBP : B ≤ P' := by
    have hBp : IsPGroup 3 B := IsPGroup.of_card hB4.2
    have : (B.comap (Nor B).subtype).Normal := Subgroup.normal_in_normalizer
    have hle := (hBp.comap_of_injective (Nor B).subtype Subtype.coe_injective).le_sylow_of_normal P
    intro x hx
    exact ⟨⟨x, Subgroup.le_normalizer hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hP'Y : P' ≤ Y := hP'N.trans hNY
  obtain ⟨Q, hQ⟩ := (hP'p.comap_of_injective Y.subtype Subtype.coe_injective).exists_le_sylow
  set Q' := (Q : Subgroup Y).map Y.subtype with hQ'
  have hPQ : P' ≤ Q' := fun x hx => ⟨⟨x, hP'Y hx⟩, hQ (Subgroup.mem_comap.mpr hx), rfl⟩
  have hQ'p : IsPGroup 3 Q' := Q.isPGroup'.map _
  have hQsyl : IsSylowOf 3 Q' Y := by
    refine ⟨Subgroup.map_subtype_le _, hQ'p, ?_⟩
    show Nat.Coprime 3 ((Q'.subgroupOf Y).index)
    rw [hQ', show ((Q : Subgroup Y).map Y.subtype).subgroupOf Y = Q from
      Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective _]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr Q.not_dvd_index
  have hBQ' : B ≤ Q' := hBP.trans hPQ
  have hQ'N : Q' ≤ Nor B := by
    intro q hq
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    refine hS1 Q' hQsyl _ B ?_ hBQ' (isElemAb_conjBy hB4 q) hB4
    rintro _ ⟨x, hx, rfl⟩
    show q * x * q⁻¹ ∈ Q'
    exact Q'.mul_mem (Q'.mul_mem hq (hBQ' hx)) (Q'.inv_mem hq)
  have hQP : Q' ≤ P' := by
    have hmax := P.is_maximal' (Q := Q'.subgroupOf (Nor B))
      (hQ'p.comap_of_injective (Nor B).subtype Subtype.coe_injective)
      (fun x hx => Subgroup.mem_subgroupOf.mpr (hPQ ⟨x, hx, rfl⟩))
    intro q hq
    have : (⟨q, hQ'N hq⟩ : Nor B) ∈ (P : Subgroup (Nor B)) := by
      rw [← hmax]; exact Subgroup.mem_subgroupOf.mpr hq
    exact ⟨_, this, rfl⟩
  have hPeq : P' = Q' := le_antisymm hPQ hQP
  have hU : ∀ A : Subgroup G, A ≤ P' → IsElemAb 3 4 A → A = B := fun A hA hAe =>
    hS1 Q' hQsyl A B (hA.trans hPQ) hBQ' hAe hB4
  have hfus : ControlsFusionIn B := controlsFusionIn_of_unique hB4 P hU
  have hNP : Subgroup.normalizer (P' : Set G) ≤ Nor B := fun g hg =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hU _ (by
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hBP hx)) (isElemAb_conjBy hB4 g))
  obtain ⟨T, hT⟩ := CFSG.StandardType.exists_sylow_eq_map_of_normalizer_le P hNP
  have h3 : padicValNat 3 (Nat.card G) = 5 := by
    have e1 := T.card_eq_multiplicity
    have e2 := P.card_eq_multiplicity
    have e3 : Nat.card T = Nat.card P := by
      rw [show Nat.card T = Nat.card (T : Subgroup G) from rfl, hT,
        Subgroup.card_map_of_injective (Nor B).subtype_injective]
    have hf : (Nat.card (Nor B)).factorization 3 = 5 := by
      rw [hNcard, show (2 ^ 7 * 3 ^ 5 : ℕ) = 3 ^ 5 * 128 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    rw [e3, e2, hf] at e1
    rw [← Nat.factorization_def _ Nat.prime_three]
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) e1).symm
  refine ⟨h3, hBY, hNY, ?_⟩
  intro β hβY hβ3 g hgY
  obtain ⟨y₁, hy₁, hx⟩ := (hS2 B hBY hB4).2 β hβY hβ3
  have hgβ3 : orderOf (g * β * g⁻¹) = 3 := by
    rw [show g * β * g⁻¹ = MulAut.conj g β from rfl, MulEquiv.orderOf_eq]; exact hβ3
  obtain ⟨y₂, hy₂, hz⟩ := (hS2 B hBY hB4).2 _ hgY hgβ3
  obtain ⟨n, hn, hnx⟩ := hfus _ hx _ hz (y₂ * g * y₁⁻¹) (by group)
  refine ⟨y₂⁻¹ * n * y₁, Y.mul_mem (Y.mul_mem (Y.inv_mem hy₂) (hNY hn)) hy₁, ?_⟩
  calc y₂⁻¹ * n * y₁ * β * (y₂⁻¹ * n * y₁)⁻¹ = y₂⁻¹ * (n * (y₁ * β * y₁⁻¹) * n⁻¹) * y₂ := by
        group
    _ = y₂⁻¹ * (y₂ * (g * β * g⁻¹) * y₂⁻¹) * y₂ := by rw [hnx]
    _ = g * β * g⁻¹ := by group

end CFSG.RankThree.PartTwo.Sec21.FF81
