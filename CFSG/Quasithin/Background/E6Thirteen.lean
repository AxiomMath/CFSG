module

public import CFSG.Quasithin.Background.E6Gamma
public import CFSG.Quasithin.Vol2.Ch3Sec1Defs
public import CFSG.Quasithin.Background.E1Amb

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Thirteen

variable {G : Type} [Group G] [Finite G] {T M V W : Subgroup G}

omit [Finite G] in
theorem exists_pow_mem_of_mem_sup {C P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.normalizer (C : Set G)) {x : G} (hx : x ∈ C ⊔ P) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ C := by
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left C P hPC] at hx
  obtain ⟨c, hc, t, ht, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hP ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have key : ∀ m : ℕ, ∃ c' ∈ C, (c * t) ^ m = c' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, C.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨c', hc', hm⟩ := ih
      refine ⟨c' * (t ^ m * c * (t ^ m)⁻¹), ?_, ?_⟩
      · refine C.mul_mem hc' ?_
        have htm : t ^ m ∈ Subgroup.normalizer (C : Set G) :=
          Subgroup.pow_mem _ (hPC ht) m
        exact (Subgroup.mem_normalizer_iff.1 htm c).1 hc
      · rw [pow_succ (c * t) m, hm, pow_succ t m]
        group
  obtain ⟨c', hc', hm⟩ := key (2 ^ k)
  exact ⟨k, by rw [hm, hk', mul_one]; exact hc'⟩

theorem e6_13 (h311 : Theorem311Stmt) (h : HypE61 T M V) (hWV : W ≤ V) (hW1 : W ≠ ⊥)
    (hres : twoPrimeResidual (M ⊓ Subgroup.centralizer (W : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G))
    (hWT : T ≤ Subgroup.normalizer (W : Set G)) : Subgroup.centralizer (W : Set G) ≤ M := by
  by_contra hHM
  have hWΓ : W ∈ gammaE64 V M := ⟨hWV, hW1, hHM, hres⟩
  set H : Subgroup G := Subgroup.centralizer (W : Set G) with hH
  set Q : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hQH : IsSylowIn 2 Q H := e6_5_one h hWΓ
  have hW2 : IsPGroup 2 W := h.isPGroup_V.to_le hWV
  have hTM : T ≤ M := h.inM.2
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hWH : W ≤ H := fun w hw => Subgroup.mem_centralizer_iff.2 fun w' hw' =>
    B2F.isElemAbelian_comm h.isElemAbelian (hWV hw') (hWV hw)
  have hTH : T ≤ Subgroup.normalizer (H : Set G) := by
    intro t ht
    rw [← conjSubgroup_eq_iff_mem_normalizer, hH, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.2 (hWT ht)]
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    intro t ht
    rw [← conjSubgroup_eq_iff_mem_normalizer, hQ, E3.conjSubgroup_inf, E3.conjSubgroup_centralizer,
      conjSubgroup_eq_iff_mem_normalizer.2 (h.normal ht),
      conjSubgroup_eq_iff_mem_normalizer.2 (Subgroup.le_normalizer ht)]
  set HT : Subgroup G := H ⊔ T with hHT
  have hHTW : HT ≤ Subgroup.normalizer (W : Set G) :=
    sup_le (Subgroup.centralizer_le_normalizer _) hWT
  have hWpc : W ≤ pCoreOf 2 HT :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hWH.trans le_sup_left) hHTW hW2
  have hHTin : InH T HT := ⟨le_sup_right, fun h0 => hW1 (le_bot_iff.1 (h0 ▸ hWpc))⟩
  have hHTM : ¬ HT ≤ M := fun hle => hHM (le_sup_left.trans hle)
  obtain ⟨H₁, ⟨hH₁in, hH₁le, hH₁M⟩, hmin⟩ :=
    (Set.toFinite {Y : Subgroup G | InH T Y ∧ Y ≤ HT ∧ ¬ Y ≤ M}).exists_minimal
      ⟨HT, hHTin, le_rfl, hHTM⟩
  have hstar : IsHStar T M H₁ := ⟨hH₁in, hH₁M, fun Y hYin hYH₁ hYM =>
    le_antisymm hYH₁ (hmin ⟨hYin, hYH₁.trans hH₁le, hYM⟩ hYH₁)⟩
  let Tsyl : Sylow 2 G := h.sylow.1.toSylow h.sylow.2
  have hunique : ∃ N : Subgroup G, IsUniqueMaxOver H₁ T N :=
    ⟨H₁ ⊓ M, IsHStar.isUniqueMaxOver Tsyl hstar hTM⟩
  have hO2H : oTwoUpper H₁ ≤ H := by
    refine (Subgroup.closure_le H).2 fun x hx => ?_
    obtain ⟨hxH₁, hxodd⟩ := hx
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hT2 hTH (hH₁le hxH₁)
    have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hxodd)
    exact E1.mem_of_pow_mem_of_coprime hcop hk (by rw [pow_orderOf_eq_one]; exact H.one_mem)
  have hRsyl : IsSylowTwoOf Q (oTwoUpper H₁ ⊔ Q) :=
    isSylowIn_of_le hQH le_sup_right (sup_le hO2H hQH.le)
  have hQpc : Q ≤ pCoreOf 2 (Subgroup.normalizer (Q : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl h.isPGroup_Q
  have hNQin : InH T (Subgroup.normalizer (Q : Set G)) :=
    ⟨hTQ, fun h0 => h.Q_ne_bot (le_bot_iff.1 (h0 ▸ hQpc))⟩
  obtain ⟨R₀, hR₀1, hR₀Q, hR₀N⟩ := h311 G T h.simple h.nonabelian h.qtke h.sylow
    (Subgroup.normalizer (Q : Set G)) H₁ Q hNQin hH₁in hunique h.Q_ne_bot inf_le_left hRsyl le_rfl
  have hR₀2 : IsPGroup 2 R₀ := h.isPGroup_Q.to_le hR₀Q
  have hloc : IsTwoLocal (Subgroup.normalizer (R₀ : Set G)) := ⟨R₀, hR₀1, hR₀2, rfl⟩
  obtain ⟨M', hM', hle'⟩ := exists_maxTwoLocal_ge hloc
  have hNQM' : Subgroup.normalizer (Q : Set G) ≤ M' := le_sup_left.trans (hR₀N.trans hle')
  have hM'M : M' = M := h.isUniqueM_normalizer_Q.2 M' ⟨hM', hNQM'⟩
  exact hH₁M (by rw [← hM'M]; exact le_sup_right.trans (hR₀N.trans hle'))

theorem e6_13_not_mem (h311 : Theorem311Stmt) (h : HypE61 T M V) (hWV : W ≤ V) (hW1 : W ≠ ⊥)
    (hres : twoPrimeResidual (M ⊓ Subgroup.centralizer (W : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G))
    (hWT : T ≤ Subgroup.normalizer (W : Set G)) : W ∉ gammaE64 V M :=
  fun hW => hW.2.2.1 (e6_13 h311 h hWV hW1 hres hWT)

end Thirteen

end E6

end CFSG.Quasithin
