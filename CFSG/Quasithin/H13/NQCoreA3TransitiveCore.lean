module

public import CFSG.Quasithin.H13.NQCoreA3ShortCore
public import CFSG.Quasithin.SteinbergBNA7IndexTwoReversal

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq_bot_of_A3 {K : Subgroup G} (hK : IsShort2 K)
    (h3 : Nat.card (K ⧸ CFSG.pCore 2 K) = 3) : K ⊓ centralizer (K : Set G) = ⊥ := by
  obtain ⟨-, hUK, -, -, -, -, hUKC, -, -⟩ := SteinbergBS.ReversalPair.a3_data hK h3
  obtain ⟨-, -, hKU, -⟩ := SteinbergBS.ReversalPair.block_structure hK h3
    (hUK.trans le_normalizer) rfl le_rfl rfl rfl
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxC⟩ := mem_inf.mp hx
  have hxU : x ∈ blockQ K := by
    rw [← hKU]
    exact mem_inf.mpr ⟨hxK, centralizer_le (SetLike.coe_subset_coe.mpr hUK) hxC⟩
  rw [← hUKC]
  exact mem_inf.mpr ⟨hxU, hxC⟩

theorem card_le_nine_of_le_normalizer (he2 : CFSG.Assembly.evenRank G ≤ 2) {V E : Subgroup G}
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hE : E ≤ normalizer (V : Set G))
    (hE3 : CFSG.IsElementaryAbelian 3 E) : Nat.card E ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hk' : k ≤ CFSG.Open.pRank 3 (normalizer (V : Set G)) :=
    CFSG.SectionRank.le_pRank (by norm_num) hE
      ⟨hE3.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩ hk
  have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ ⟨V, hV, hV2, rfl⟩
  have he2' : CFSG.Open.evenRank G ≤ 2 := he2
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 9 := by norm_num

theorem le_two_of_commuting_A3_family (he2 : CFSG.Assembly.evenRank G ≤ 2) {r : ℕ}
    (Kf : Fin r → Subgroup G) (hK : ∀ i, IsShort2 (Kf i))
    (h3 : ∀ i, Nat.card (Kf i ⧸ CFSG.pCore 2 (Kf i)) = 3)
    (hcomm : ∀ i j, i ≠ j → ⁅Kf i, Kf j⁆ = ⊥)
    (hU2 : IsPGroup 2 (⨆ i, blockQ (Kf i) : Subgroup G)) : r ≤ 2 := by
  classical
  by_contra hr
  push Not at hr
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set U := ⨆ i, blockQ (Kf i) with hUdef
  have hKU : ∀ k, Kf k ≤ normalizer (U : Set G) := by
    intro k
    refine LieType.Steinberg.le_normalizer_iSup fun i => ?_
    by_cases hik : i = k
    · subst hik
      exact (SteinbergBS.ReversalPair.a3_data (hK i) (h3 i)).2.2.2.2.2.2.2.1
    · have h1 : Kf k ≤ centralizer (Kf i : Set G) :=
        commutator_eq_bot_iff_le_centralizer.mp (hcomm k i (Ne.symm hik))
      have h2 : blockQ (Kf i) ≤ Kf i := (SteinbergBS.ReversalPair.a3_data (hK i) (h3 i)).2.1
      exact h1.trans ((centralizer_le (SetLike.coe_subset_coe.mpr h2)).trans
        (centralizer_le_normalizer _))
  have hU1 : U ≠ ⊥ := by
    intro h
    have h1 : blockQ (Kf ⟨0, by omega⟩) ≤ U := le_iSup (fun i => blockQ (Kf i)) ⟨0, by omega⟩
    have h2 := (SteinbergBS.ReversalPair.a3_data (hK ⟨0, by omega⟩) (h3 ⟨0, by omega⟩)).2.2.1
    rw [h, le_bot_iff] at h1
    rw [h1, card_bot] at h2
    norm_num at h2
  let ι : Fin 3 → Fin r := fun j => ⟨j, by omega⟩
  have hι : Function.Injective ι := fun a b h => Fin.ext (congrArg Fin.val h :)
  have hc : ∀ j, ∃ c ∈ Kf (ι j), orderOf c = 3 := by
    intro j
    have h12 := (SteinbergBS.ReversalPair.a3_data (hK (ι j)) (h3 (ι j))).2.2.2.2.2.1
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := Kf (ι j)) 3 (by rw [h12]; norm_num)
    exact ⟨c, c.2, by rw [Subgroup.orderOf_coe, hc]⟩
  choose c hcK hco using hc
  set H : Fin 3 → Subgroup G := fun j => zpowers (c j) with hHdef
  have hHK : ∀ j, H j ≤ Kf (ι j) := fun j => zpowers_le.mpr (hcK j)
  have hcent : ∀ j k, j ≠ k → Kf (ι j) ≤ centralizer (Kf (ι k) : Set G) := fun j k hjk =>
    commutator_eq_bot_iff_le_centralizer.mp (hcomm _ _ (hι.ne hjk))
  have hHcomm : Pairwise fun j k : Fin 3 => ∀ x y : G, x ∈ H j → y ∈ H k → Commute x y :=
    fun j k hjk x y hx hy => (mem_centralizer_iff.mp (hcent j k hjk (hHK j hx)) y (hHK k hy)).symm
  have hind : iSupIndep H := by
    intro j
    rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    have h2 : (⨆ k, ⨆ (_ : k ≠ j), H k) ≤ centralizer (Kf (ι j) : Set G) :=
      iSup₂_le fun k hk => (hHK k).trans (hcent k j hk)
    have h3' := inf_centralizer_eq_bot_of_A3 (hK (ι j)) (h3 (ι j))
    rw [eq_bot_iff] at h3'
    exact mem_bot.mp (h3' (mem_inf.mpr ⟨hHK j hx1, h2 hx2⟩))
  set f := Subgroup.noncommPiCoprod hHcomm with hf
  have hfinj : Function.Injective f := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind
  have hfU : f.range ≤ normalizer (U : Set G) := by
    rw [hf, Subgroup.noncommPiCoprod_range]
    exact iSup_le fun j => (hHK j).trans (hKU (ι j))
  have hAcomm : ∀ a b : (∀ j, ↥(H j)), a * b = b * a := by
    intro a b
    funext j
    apply Subtype.ext
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (a j).2
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (b j).2
    change (a j : G) * (b j : G) = (b j : G) * (a j : G)
    rw [← hm, ← hn]
    exact (Commute.zpow_zpow_self (c j) m n).eq
  have hApow : ∀ a : (∀ j, ↥(H j)), a ^ 3 = 1 := by
    intro a
    funext j
    apply Subtype.ext
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (a j).2
    change (a j : G) ^ 3 = 1
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hco j,
      pow_orderOf_eq_one, one_zpow]
  have hAcard : Nat.card (∀ j, ↥(H j)) = 3 ^ 3 := by
    rw [Nat.card_pi]
    simp only [hHdef, Nat.card_zpowers, hco, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h27 := CFSG.SectionRank.le_pRank_of_injective (by norm_num) hAcomm hApow hAcard f hfinj hfU
  have he := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ ⟨U, hU1, hU2, rfl⟩
  have he2' : CFSG.Open.evenRank G ≤ 2 := he2
  omega

theorem two_local_rank_transitive_A3_family_common_normal_core
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G)
    (he2 : CFSG.Assembly.evenRank G ≤ 2) (T : Sylow 2 G) {M S : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hSM : M ≤ normalizer (S : Set G)) (hST : S ≤ T) {r : ℕ}
    (hr : 0 < r) (Kf : Fin r → Subgroup G) (hK : ∀ i, IsShort2 (Kf i))
    (h3 : ∀ i, Nat.card (Kf i ⧸ CFSG.pCore 2 (Kf i)) = 3)
    (hcomm : ∀ i j, i ≠ j → ⁅Kf i, Kf j⁆ = ⊥) (hSK : ∀ i, S ≤ normalizer (Kf i : Set G))
    (hUS : ∀ i, blockQ (Kf i) ≤ S)
    (hperm : ∀ t ∈ (T : Subgroup G), ∀ i, ∃ j, CFSG.conjugate (Kf i) t = Kf j)
    (htrans : ∀ i j, ∃ t ∈ (T : Subgroup G), CFSG.conjugate (Kf i) t = Kf j) :
    r ≤ 2 ∧
      (∀ a ∈ M, ∀ b ∈ M, ⁅CFSG.conjugate (blockQ (Kf ⟨0, hr⟩)) a,
        CFSG.conjugate (blockQ (Kf ⟨0, hr⟩)) b⁆ = ⊥) ∧
      conjJoin M (blockQ (Kf ⟨0, hr⟩)) ≠ ⊥ ∧
      IsElemAbelian 2 (conjJoin M (blockQ (Kf ⟨0, hr⟩))) ∧
      conjJoin M (blockQ (Kf ⟨0, hr⟩)) ≤ S ∧
      M ⊔ ((T : Subgroup G) ⊔ ⨆ i, Kf i) ≤
        normalizer (conjJoin M (blockQ (Kf ⟨0, hr⟩)) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 S := T.isPGroup'.to_le hST
  have hTsyl : IsSylowTwoOf (T : Subgroup G) M :=
    ⟨hTM, T.isPGroup', fun h2 => T.not_dvd_index (h2.trans (relIndex_dvd_index_of_le hTM))⟩
  have hr2 : r ≤ 2 := le_two_of_commuting_A3_family he2 Kf hK h3 hcomm
    (T.isPGroup'.to_le ((iSup_le hUS).trans hST))
  set K₁ := Kf ⟨0, hr⟩ with hK₁
  set U₁ := blockQ K₁ with hU₁
  obtain ⟨-, -, hUcard, hUexp, hUab, -, -, -, -⟩ := SteinbergBS.ReversalPair.a3_data (hK ⟨0, hr⟩)
    (h3 ⟨0, hr⟩)
  have hU1 : U₁ ≠ ⊥ := by
    intro h
    have h4 : Nat.card U₁ = 4 := hUcard
    rw [h, card_bot] at h4
    norm_num at h4
  have hcommU : ∀ x ∈ M, ⁅U₁, CFSG.conjugate U₁ x⁆ = ⊥ := by
    intro x hxM
    by_contra hx
    have hr12 : r = 1 ∨ r = 2 := by omega
    obtain ⟨_hr2, -, hT1idx, ⟨x₀, -, hx₀N, -, hx₀⟩, hflip⟩ :=
      SteinbergBN.A3_small_family_index_two_normalizer_reversal hTsyl hSM hS2 hr12 Kf hK h3
        hcomm hSK hUS hperm htrans x hxM hx
    set T₁ := (T : Subgroup G) ⊓ normalizer (K₁ : Set G) with hT₁
    have hT1idx' : T₁.relIndex T = 2 := hT1idx
    obtain ⟨t, htT, htT₁⟩ : ∃ t ∈ (T : Subgroup G), t ∉ T₁ := by
      by_contra h
      push Not at h
      rw [relIndex_eq_one.mpr h] at hT1idx'
      norm_num at hT1idx'
    obtain ⟨-, hKt⟩ := hflip t htT htT₁
    have hUT₁ : U₁ ≤ T₁ := le_inf ((hUS _).trans hST) ((hUS _).trans (hSK _))
    set A := CFSG.conjugate U₁ x₀ with hA
    set D₀ := closure ((T₁ : Set G) ∪ {y | y ∈ normalizer (T₁ : Set G) ∧ Odd (orderOf y)})
      with hD₀
    set X := D₀ ⊔ K₁ with hX
    obtain ⟨⟨-, hXV⟩, hUV, hVQ, hQP, hPX, -, hnot, -, -, -, ⟨hAP, hPA⟩, hAC, -, -, hXc⟩ :=
      SteinbergBN.A3_reversal_diagonal_characteristic_two_overgroup hev T (P := T₁) (K := K₁)
        (U := U₁) (Q := T₁ ⊓ centralizer (U₁ : Set G)) (D₀ := D₀) (V := conjJoin D₀ U₁) (X := X)
        (A := A) (E := ⁅U₁, A⁆) inf_le_left hT1idx' (hK _) (h3 _) inf_le_right rfl hUT₁ htT htT₁
        hKt hx₀N hx₀ rfl hD₀ rfl hX hA rfl
    have hV1 : conjJoin D₀ U₁ ≠ ⊥ := fun h => hU1 (le_bot_iff.mp (h ▸ hUV))
    have hV2 : IsPGroup 2 (conjJoin D₀ U₁) :=
      T.isPGroup'.to_le ((hVQ.trans hQP).trans inf_le_left)
    have h3X : ∀ E : Subgroup G, E ≤ X → CFSG.IsElementaryAbelian 3 E → Nat.card E ≤ 9 :=
      fun E hEX hE => card_le_nine_of_le_normalizer he2 hV1 hV2 (hEX.trans hXV) hE
    have hAU : ⁅A, U₁⁆ ≠ ⊥ := by
      rw [commutator_comm]
      exact hx₀
    obtain ⟨-, hNU⟩ := actual_A3_Sylow_normalizer_preserves_short_core hXc hPX le_sup_right
      (hK _) (h3 _) inf_le_right hAP hPA rfl hAU hAC h3X rfl
    exact hnot fun y hy => mem_inf.mpr ⟨(mem_inf.mp hy).1,
      hNU (mem_inf.mpr ⟨(mem_inf.mp hy).2, (mem_inf.mp hy).1⟩)⟩
  have hpair : ∀ a ∈ M, ∀ b ∈ M, ⁅CFSG.conjugate U₁ a, CFSG.conjugate U₁ b⁆ = ⊥ := by
    intro a ha b hb
    have h1 : CFSG.conjugate ⁅U₁, CFSG.conjugate U₁ (b * a⁻¹)⁆ a = CFSG.conjugate ⊥ a := by
      rw [hcommU (b * a⁻¹) (mul_mem hb (inv_mem ha))]
    rw [SteinbergBN.conjugate_commutator', SteinbergBN.conjugate_conjugate',
      inv_mul_cancel_right] at h1
    rw [h1]
    exact Subgroup.map_bot _
  set R₀ := conjJoin M U₁ with hR₀
  have hgen : ∀ s t : ↥M, U₁.map (MulAut.conj (s : G)).toMonoidHom ≤
      centralizer ((U₁.map (MulAut.conj (t : G)).toMonoidHom : Subgroup G) : Set G) := by
    intro s t
    have h := hpair (s : G)⁻¹ (inv_mem s.2) (t : G)⁻¹ (inv_mem t.2)
    simp only [CFSG.conjugate, inv_inv] at h
    exact commutator_eq_bot_iff_le_centralizer.mp h
  have hRcent : R₀ ≤ centralizer (R₀ : Set G) := by
    refine iSup_le fun s => ?_
    rw [le_centralizer_iff]
    exact iSup_le fun t => hgen t s
  have hRexp : ∀ x ∈ R₀, x ^ 2 = 1 := by
    intro x hx
    refine Subgroup.iSup_induction' (fun s : ↥M => U₁.map (MulAut.conj (s : G)).toMonoidHom)
      (C := fun x _ => x ^ 2 = 1) ?_ ?_ ?_ hx
    · rintro s _ ⟨u, hu, rfl⟩
      change ((s : G) * u * (s : G)⁻¹) ^ 2 = 1
      rw [sq, show (s : G) * u * (s : G)⁻¹ * ((s : G) * u * (s : G)⁻¹) =
        (s : G) * (u * u) * (s : G)⁻¹ by group, hUexp u hu, mul_one, mul_inv_cancel]
    · exact one_pow 2
    · intro y z hy hz hy2 hz2
      have hyz : Commute y z := (mem_centralizer_iff.mp (hRcent hy) z hz).symm
      rw [hyz.mul_pow, hy2, hz2, one_mul]
  have hUR : U₁ ≤ R₀ := by
    rw [hR₀]
    refine le_iSup_of_le (1 : ↥M) ?_
    rw [OneMemClass.coe_one, LieType.Steinberg.map_conj_one]
  have hRS : R₀ ≤ S := by
    refine iSup_le fun s => ?_
    rintro _ ⟨u, hu, rfl⟩
    exact (mem_normalizer_iff.mp (hSM s.2) u).mp (hUS _ hu)
  have hMR : M ≤ normalizer (R₀ : Set G) := by
    intro x hx
    rw [LieType.Steinberg.mem_normalizer_iff_map_conj, hR₀, conjJoin, Subgroup.map_iSup]
    have h1 : ∀ s : ↥M, (U₁.map (MulAut.conj (s : G)).toMonoidHom).map
        (MulAut.conj x).toMonoidHom =
          U₁.map (MulAut.conj (((⟨x, hx⟩ : ↥M) * s : ↥M) : G)).toMonoidHom := fun s => by
      rw [Subgroup.coe_mul, LieType.Steinberg.map_conj_mul]
    simp_rw [h1]
    exact (Equiv.mulLeft (⟨x, hx⟩ : ↥M)).iSup_comp
      (g := fun s : ↥M => U₁.map (MulAut.conj (s : G)).toMonoidHom)
  have hUiR : ∀ i, blockQ (Kf i) ≤ R₀ := by
    intro i
    obtain ⟨t, htT, hti⟩ := htrans ⟨0, hr⟩ i
    have h1 : blockQ (Kf i) = U₁.map (MulAut.conj t⁻¹).toMonoidHom := by
      rw [← hti]
      exact pCoreOf_map_equiv 2 (MulAut.conj t⁻¹) K₁
    rw [h1]
    exact le_iSup (fun s : ↥M => U₁.map (MulAut.conj (s : G)).toMonoidHom)
      ⟨t⁻¹, inv_mem (hTM htT)⟩
  have hKR : ∀ i, Kf i ≤ normalizer (R₀ : Set G) := by
    intro i
    obtain ⟨-, -, -, -, -, hQK, -, -, -⟩ := SteinbergBS.ReversalPair.block_structure (hK i) (h3 i)
      (hSK i) rfl (hUS i) rfl rfl
    have hRQ : R₀ ≤ S ⊓ centralizer (blockQ (Kf i) : Set G) :=
      le_inf hRS (le_centralizer_iff.mp ((hUiR i).trans hRcent))
    refine SteinbergBS.ReversalOvergroup.le_normalizer_of_conj_mem fun k hk x hx => ?_
    have h1 : ⁅x, k⁆ ∈ blockQ (Kf i) := hQK (commutator_mem_commutator (hRQ hx) hk)
    have h2 : k * x * k⁻¹ = ⁅x, k⁆⁻¹ * x := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact mul_mem (inv_mem (hUiR i h1)) hx
  refine ⟨hr2, hpair, fun h => hU1 (le_bot_iff.mp (h ▸ hUR)),
    ⟨le_centralizer_iff_isMulCommutative.mp hRcent, hRexp⟩, hRS,
    sup_le hMR (sup_le (hTM.trans hMR) (iSup_le hKR))⟩

end CFSG.Quasithin.H13.NQCore
