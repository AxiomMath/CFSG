module

public import CFSG.RankThree.PartOne.S12.PhanAssembly
public import CFSG.RankThree.PartOne.S12.InputsKF3
public import CFSG.RankThree.PartOne.S12.ModelTransport
public import CFSG.RankThree.PartOne.S12.InputsKF2

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Sec138141

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem torusInvariant_self (E : Subgroup G) : torusInvariant E ⊤ E := by
  intro w hw b hb
  exact (Subgroup.mem_normalizer_iff.1 hw.2 b).1 hb

omit [Finite G] in
theorem faithful_self (E : Subgroup G) :
    ∀ g ∈ torusWeyl E, (∀ b : E, (b : G) ∈ E → g b = b) → g = 1 :=
  fun _ _ h => MulEquiv.ext fun b => h b b.2

theorem exists_ne_two {n : ℕ} (hn : 2 ≤ n) (a b : Fin (n + 1)) :
    ∃ m : Fin (n + 1), m ≠ a ∧ m ≠ b := by
  have hcard : ({a, b} : Finset (Fin (n + 1))).card <
      (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt Finset.card_le_two (by omega)
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
  exact ⟨m, hm.1, hm.2⟩

omit [Finite G] in
theorem exists_fixed_self {p n : ℕ} (hn : 2 ≤ n) {E L : Subgroup G} (W : WeylIso p n E L)
    {s : MulAut E} (hs : s ∈ reflectionSet p E) :
    ∃ m, W.ψ ⟨s, Subgroup.subset_closure hs⟩ m = m ∧ W.ψ ⟨s, Subgroup.subset_closure hs⟩ m = m := by
  obtain ⟨a, b, -, hsab⟩ := W.isSwap s hs
  obtain ⟨m, hma, hmb⟩ := exists_ne_two hn a b
  refine ⟨m, ?_, ?_⟩ <;> rw [hsab] <;> exact Equiv.swap_apply_of_ne_of_ne hma hmb

theorem fixed_of_order_three : ∀ a b c d : Fin (3 + 1), a ≠ b → c ≠ d →
    (Equiv.swap a b * Equiv.swap c d) ^ 3 = 1 → Equiv.swap a b * Equiv.swap c d ≠ 1 →
    ∃ m, Equiv.swap a b m = m ∧ Equiv.swap c d m = m := by
  decide

omit [Finite G] in
theorem exists_common_fixed_three {p : ℕ} {E L : Subgroup G} (W : WeylIso p 3 E L)
    {s t : MulAut E} (hs : s ∈ reflectionSet p E) (ht : t ∈ reflectionSet p E)
    (h3 : orderOf (s * t) = 3) :
    ∃ m, W.ψ ⟨s, Subgroup.subset_closure hs⟩ m = m ∧
      W.ψ ⟨t, Subgroup.subset_closure ht⟩ m = m := by
  obtain ⟨a, b, hab, hsab⟩ := W.isSwap s hs
  obtain ⟨c, d, hcd, htcd⟩ := W.isSwap t ht
  have h3' : orderOf (W.ψ ⟨s, Subgroup.subset_closure hs⟩ *
      W.ψ ⟨t, Subgroup.subset_closure ht⟩) = 3 := by
    rw [← PhanAssembly.orderOf_mul_eq W hs ht]
    exact h3
  rw [hsab, htcd] at h3'
  have hpow : (Equiv.swap a b * Equiv.swap c d) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (Equiv.swap a b * Equiv.swap c d)
    rwa [h3'] at this
  have hne1 : Equiv.swap a b * Equiv.swap c d ≠ 1 := by
    intro h
    rw [h, orderOf_one] at h3'
    omega
  obtain ⟨m, hm1, hm2⟩ := fixed_of_order_three a b c d hab hcd hpow hne1
  refine ⟨m, ?_, ?_⟩
  · rw [hsab]
    exact hm1
  · rw [htcd]
    exact hm2

end Sec138141

@[expose] def Node138Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E ≠ A →
      RowModel p L 9 ∧ RowWeylIso E (torusImage E L) 9 ∧ Nat.card E = p ^ 4 ∧
        Nonempty (WeylIso p 4 E L)

@[expose] def Node141Struct : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A →
    (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
      RowModel p L 1 ∧ RowWeylIso E (torusImage E L) 1 ∧ Nonempty (WeylIso p 3 E L)

theorem node138_of_struct (hS : Node138Struct) (hKFU4 : KF126U4) (hPhan : ExtPhan)
    (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) : Node138 := by
  intro G _ _ p A c L E h hT hEA
  have hF12 := Sec12Facts.of_nodes h122 h122b h123 h124 h125 h
  have hF13 := Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126
    h127 h128 h129 h hT
  obtain ⟨hrow, hweyl, hcard, ⟨W⟩⟩ := hS G p A c L E h hF12 hF13 hT hEA
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  obtain ⟨f, hf1, hpf, hmodel⟩ := hrow
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have h3 := Nat.le_of_dvd (by norm_num) hpf
    norm_num at h3
    omega
  have hEel : IsElementaryAbelian p E := h.E_elem
  have hL : Nonempty (torusImage E L ≃* Equiv.Perm (Fin 4)) := hweyl
  have hL24 : Nat.card (torusImage E L) = (4 : ℕ).factorial := by
    obtain ⟨e⟩ := hL
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  obtain ⟨hKat, hKpair⟩ := hKFU4 G p A c L E f h hF12 hf1 hpf hmodel hcard
  have hKall : ∀ t ∈ reflectionSet p E, KFAt p E f t := by
    intro t ht
    obtain ⟨w, hw, hwt, -⟩ := W.exists_conj_into_L hL24 ht ht
      (W.exists_common_fixed (by norm_num) ht ht)
    exact KFAt.of_conj hw (hKat _ (conj_mem_reflectionSet hp ht hw) hwt)
  have hPall : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t →
      KFPair p E f s t := by
    intro s hs t ht hst
    obtain ⟨w, hw, hws, hwt⟩ := W.exists_conj_into_L hL24 hs ht
      (W.exists_common_fixed (by norm_num) hs ht)
    have hne' : conjAut E w hw * s * (conjAut E w hw)⁻¹ ≠
        conjAut E w hw * t * (conjAut E w hw)⁻¹ := fun h' =>
      hst (mul_left_cancel (mul_right_cancel h'))
    exact KFPair.of_conj hw (hKpair _ (conj_mem_reflectionSet hp hs hw) hws _
      (conj_mem_reflectionSet hp ht hw) hwt hne')
  have hP := PhanAssembly.phan_conclusion W hPhan (by norm_num) hp hp5 hEel hf2 hpf le_rfl
    (Sec138141.torusInvariant_self E) hF13.irreducible (Sec138141.faithful_self E) hKall hPall
  obtain ⟨tt, htt⟩ := PhanAssembly.exists_chain W
  exact ⟨f, hf1, hpf, projSU_of_statedClassicalModel hP, ⟨W.ψ⟩, hcard, hEA,
    PhanAssembly.even_card_lieGenerated hKall (htt 0).1⟩

theorem node141_of_struct (hS : Node141Struct) (hKF : KF141) (hCT : ExtCurtisTitsA)
    (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h11 : Sec11One)
    (h122 : Node122) (h122b : Node122b) (h123 : Node123) (h124 : Node124) (h125 : Node125)
    (h126 : Node126) (h127 : Node127) (h128 : Node128) (h129 : Node129) : Node141 := by
  intro G _ _ p A c L E h hT hEA hall
  have hF12 := Sec12Facts.of_nodes h122 h122b h123 h124 h125 h
  have hF13 := Sec13Facts.of_nodes hSchreier hTwoAction h106 h11 h122 h122b h123 h124 h125 h126
    h127 h128 h129 h hT
  obtain ⟨hrow, hweyl, ⟨W⟩⟩ := hS G p A c L E h hF12 hF13 hT hEA hall
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  obtain ⟨f, hf1, hpf, hmodel⟩ := hrow
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have h1 := Nat.le_of_dvd (by norm_num) hpf
    norm_num at h1
    omega
  have hEel : IsElementaryAbelian p E := h.E_elem
  have hL : Nonempty (torusImage E L ≃* Equiv.Perm (Fin 3)) := hweyl
  have hL6 : Nat.card (torusImage E L) = (3 : ℕ).factorial := by
    obtain ⟨e⟩ := hL
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
  obtain ⟨hK1, hK2, hK3⟩ := hKF G p A c L E f h hF12 hF13 hT hf1 hpf hmodel hEA hall
  have hKall : ∀ t ∈ reflectionSet p E, KFAt p E f t := by
    intro t ht
    obtain ⟨w, hw, hwt, -⟩ := W.exists_conj_into_L hL6 ht ht
      (Sec138141.exists_fixed_self (by norm_num) W ht)
    exact KFAt.of_conj hw (hK1 _ (conj_mem_reflectionSet hp ht hw) hwt)
  have hPall : ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t →
      KFPairL p E f s t := by
    intro s hs t ht hst
    refine ⟨fun hcomm => hK3 s hs t ht hst hcomm, fun h3 => ?_⟩
    obtain ⟨w, hw, hws, hwt⟩ := W.exists_conj_into_L hL6 hs ht
      (Sec138141.exists_common_fixed_three W hs ht h3)
    have hne' : conjAut E w hw * s * (conjAut E w hw)⁻¹ ≠
        conjAut E w hw * t * (conjAut E w hw)⁻¹ := fun h' =>
      hst (mul_left_cancel (mul_right_cancel h'))
    exact (KFPairL.of_conj hw (hK2 _ (conj_mem_reflectionSet hp hs hw) hws _
      (conj_mem_reflectionSet hp ht hw) hwt hne')).2 h3
  have hct := PhanAssembly.ctA_conclusion W hCT (by norm_num) hp hp5 hEel hf2 hpf le_rfl
    (Sec138141.torusInvariant_self E) hF13.irreducible (Sec138141.faithful_self E) hKall hPall
  have hcop : Nat.Coprime (3 + 1) (2 ^ f - 1) := by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hpos : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    have hodd : Odd (2 ^ (g + 1) - 1) := ⟨2 ^ g - 1, by rw [pow_succ]; omega⟩
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hodd)
  obtain ⟨tt, htt⟩ := PhanAssembly.exists_chain W
  exact ⟨f, hf1, hpf, projSL_of_statedClassicalModel (hct.2 hcop), ⟨W.ψ⟩, hEA,
    PhanAssembly.even_card_lieGenerated hKall (htt 0).1⟩

end CFSG.RankThree.PartOne
