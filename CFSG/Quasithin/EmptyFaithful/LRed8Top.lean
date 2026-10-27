module

public import CFSG.Quasithin.EmptyFaithful.LRed8A7
public import CFSG.Quasithin.EmptyFaithful.LRed8Alt6
public import CFSG.Quasithin.EmptyFaithful.LRed8G2
public import CFSG.Quasithin.EmptyFaithful.LRed6ModLemma

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank EmptyFaithfulMultiple.FFL
open scoped commutatorElement

namespace LRed8

section Fix

theorem eq_of_card_le_two {S : Type*} [Group S] [Finite S] (h : Nat.card S ≤ 2) {a b : S}
    (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  have hinj : Function.Injective (![1, a, b] : Fin 3 → S) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij.symm ha
        | exact absurd hij ha
        | exact absurd hij.symm hb
        | exact absurd hij hb
        | exact absurd hij hab
        | exact absurd hij.symm hab
  have h3 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h3
  omega

variable {V : Type*} [CommGroup V]

theorem fixV_le_fixV_of_card_le_two [Finite V] {H L : Subgroup (MulAut V)}
    (hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V))) (h : Nat.card ↥(fixV L) ≤ 2) :
    fixV L ≤ fixV H := by
  intro v hv x hx
  have hxv : x v ∈ fixV L := by
    intro l hl
    have hconj : x⁻¹ * l * x ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hx)) l).mp hl
      simpa using h1
    have h2 := hv _ hconj
    calc l (x v) = x ((x⁻¹ * l * x) v) := by simp [MulAut.mul_apply]
      _ = x v := by rw [h2]
  by_cases hv1 : v = 1
  · rw [hv1, map_one]
  · have hxv1 : x v ≠ 1 := fun h' => hv1 (by simpa using h')
    have := eq_of_card_le_two h (a := ⟨x v, hxv⟩) (b := ⟨v, hv⟩)
      (fun e => hxv1 (congrArg Subtype.val e)) (fun e => hv1 (congrArg Subtype.val e))
    exact congrArg Subtype.val this

end Fix

theorem irrFixShape_of_b56
    (h56 : AsB56) : IrrFixShape := by
  intro V _ _ hV H hcomm hB hI hne
  classical
  set L : Subgroup (MulAut V) := CFSG.Open.quasithinGenFitting H with hLdef
  have hLH : L ≤ H := quasithinGenFitting_le H
  have hHN : H ≤ Subgroup.normalizer (L : Set (MulAut V)) := le_normalizer_quasithinGenFitting H
  have hNn : (L.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHN
  have hH1 : H ≠ ⊥ := by
    intro h
    exact hne (le_antisymm hLH (by rw [h]; exact bot_le))
  have hS3 : ¬ Nonempty (↥H ≃* Equiv.Perm (Fin 3)) := by
    rintro ⟨e⟩
    have hmem := (LRed4.inspList_facts hI).1
    rw [Nat.card_congr e.toEquiv, LRed4.card_perm_fin] at hmem
    simp [LRed4.inspOrders, Nat.factorial] at hmem
  have h1 : B56Case1 H := by
    rcases h56 V hV H hH1 hB with h1 | h2 | h3 | h4 | h5
    · exact h1
    · exact (hS3 h2.1).elim
    · exact (LRed4.not_case3 hI h3).elim
    · exact (LRed4.not_case4 hI h4).elim
    · exact (LRed4.not_case5 hI h5).elim
  obtain ⟨hqL, ⟨⟨-, hcases⟩, hP2, -, -, -, -⟩, hQL⟩ := h1
  have hL3 : ¬ Nonempty (↥H ≃* ↥(CFSG.Open.StatedSL 3 (ZMod 2))) := by
    rintro ⟨e⟩
    have hs : IsSimpleGroup ↥(CFSG.Open.StatedSL 3 (ZMod 2)) :=
      S153E58.isSimpleGroup_statedSL_three_two
    have hsH : IsSimpleGroup ↥H := e.isSimpleGroup
    have hsq : IsSimpleGroup (↥L ⧸ Subgroup.center ↥L) := hqL.2.1
    have hnt : Nontrivial ↥L :=
      Function.Surjective.nontrivial (f := QuotientGroup.mk' (Subgroup.center ↥L))
        (QuotientGroup.mk'_surjective _)
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥L)
    rcases hsH.eq_bot_or_eq_top_of_normal (L.subgroupOf H) with h | h
    · apply hx1
      have hmem : (⟨x.1, hLH x.2⟩ : ↥H) ∈ L.subgroupOf H := x.2
      rw [h, Subgroup.mem_bot] at hmem
      have h' := congrArg Subtype.val hmem
      exact Subtype.ext h'
    · apply hne
      refine le_antisymm hLH fun y hy => ?_
      have hmem : (⟨y, hy⟩ : ↥H) ∈ L.subgroupOf H := by
        rw [h]
        exact Subgroup.mem_top _
      exact hmem
  have hi : B51Case1i H L := by
    rcases hcases with hi | hii | ⟨n, hiii⟩ | hiv
    · exact hi
    · exact (hL3 (LRed4.case1ii_conclusion hI hii)).elim
    · exact (LRed4.case1iii_false hI hiii).elim
    · exact (LRed4.case1iv_false hI hiv).elim
  obtain ⟨hirr, hB42, hsyl⟩ := hi
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf H
  rcases hsyl T hT with hHL | ⟨hHT, -⟩
  · exact absurd hHL.symm hne
  have hTL : T ≤ Subgroup.normalizer (L : Set (MulAut V)) := hT.1.trans hHN
  have hj : ∃ j : ℕ, Nat.card ↥H = 2 ^ j * Nat.card ↥L :=
    LRed6.pow_index_of_sup_two hLH hT.2.1 hTL hHT
  have hLtop : commV L = ⊤ := by
    have hc' : commV (L ⊔ T) = ⊤ := by
      rw [← hHT]
      exact hcomm
    exact LRed4.commV_eq_top_of_sup_two hV hT.2.1 hTL hc'
  have hInS : LRed6.InS (Nat.card ↥L) := LRed6.inS_of_inspList hI hL3 hLH hNn hqL hj
  rw [hLtop] at hB42
  have h1080 : Nat.card ↥L = 1080 → False := by
    intro hc
    obtain ⟨j, hj'⟩ := hj
    have hmem := (LRed4.inspList_facts hI).1
    rw [hj', hc] at hmem
    simp only [LRed4.inspOrders, Finset.mem_insert, Finset.mem_singleton] at hmem
    have hj0 : j = 0 := by
      rcases Nat.lt_or_ge j 4 with hj4 | hj4
      · interval_cases j <;> omega
      · have : 16 ≤ 2 ^ j := by
          calc 16 = 2 ^ 4 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj4
        omega
    subst hj0
    apply hne
    refine Subgroup.eq_of_le_of_card_ge hLH ?_
    rw [hj', hc]
    omega
  have hbot2520 : Nat.card ↥L = 2520 → fixV L = ⊥ := by
    intro hc
    have hdirect : IsIntDirect (commV L) (fixV L) ⊤ := by
      by_contra hnd
      have h2 := (hP2.2 hnd).2
      rw [hLtop] at h2
      exact not_naturalList2_of_card_2520 hc h2
    have h3 := hdirect.2
    rw [hLtop, top_inf_eq] at h3
    exact h3
  have hfix : Nat.card ↥(fixV L) ≤ 2 ∨ fixV L = ⊥ := by
    rcases LRed6.modelShape_of_card hInS hB42 with hA6 | hA7 | hA7F | hHat | hG2'
    · left
      exact card_fixV_alt6 hV hLtop hA6
    · right
      obtain ⟨π, hπ⟩ := hA7
      have hc : Nat.card ↥L = 2520 := by
        rw [LRed6.card_eq_of_faithful (FFC.altDn_faithful (by norm_num)) hπ]
        show Nat.card ↥(alternatingGroup (Fin 7)) = 2520
        rw [card_alternatingGroup1527d 7 (by norm_num)]
        norm_num [Nat.factorial]
      exact hbot2520 hc
    · right
      obtain ⟨α, π, hπ⟩ := hA7F
      have hc : Nat.card ↥L = 2520 := by
        rw [LRed6.card_eq_of_faithful (FFC.a7Four_faithful α) hπ]
        show Nat.card ↥(alternatingGroup (Fin 7)) = 2520
        rw [card_alternatingGroup1527d 7 (by norm_num)]
        norm_num [Nat.factorial]
      exact hbot2520 hc
    · exfalso
      obtain ⟨K, hK, hKf, Γ₀, hK4, hdet, hhat, hsc, π, hπ⟩ := hHat
      have hc : Nat.card ↥L = 1080 := by
        have h1 := LRed6.card_eq_of_faithful (FFModel.nat_faithful _) hπ
        rw [h1]
        have : Finite ↥Γ₀ := inferInstance
        show Nat.card ↥Γ₀ = 1080
        exact card_of_isHat1527d hhat (by
          rw [card_alternatingGroup1527d 6 (by norm_num)]
          norm_num [Nat.factorial])
      exact h1080 hc
    · left
      exact card_fixV_g2 hV hLtop hG2'
  refine le_antisymm ?_ (fun v hv x hx => hv x (hLH hx))
  rcases hfix with h | h
  · exact fixV_le_fixV_of_card_le_two hHN h
  · rw [h]
    exact bot_le

end LRed8

end CFSG.Quasithin
