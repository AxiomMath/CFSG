module

import CFSG.Monster.GMS.NotConj
public import CFSG.Monster.GMS.S35
public import CFSG.Monster.GMS.TwoAGraph

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S57

section Combinatorics

open Classical in
theorem ncard_eq_card_filter {G : Type*} [Fintype G] (S : Set G) :
    S.ncard = (Finset.univ.filter (· ∈ S)).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext
  simp

theorem card_mul_eq_card_mul_ncard {G : Type*} [Finite G] {A K : Set G} (R : G → G → Prop)
    {m n : ℕ} (hm : ∀ c ∈ A, {x | x ∈ K ∧ R c x}.ncard = m)
    (hn : ∀ x ∈ K, {c | c ∈ A ∧ R c x}.ncard = n) :
    A.ncard * m = K.ncard * n := by
  classical
  have := Fintype.ofFinite G
  have h := Finset.card_mul_eq_card_mul R (s := Finset.univ.filter (· ∈ A))
    (t := Finset.univ.filter (· ∈ K)) (m := m) (n := n) ?_ ?_
  · rw [ncard_eq_card_filter A, ncard_eq_card_filter K]
    exact h
  · intro c hc
    rw [← hm c (by simpa using hc), ncard_eq_card_filter]
    simp only [Finset.bipartiteAbove, Finset.filter_filter, Set.mem_ofPred_eq]
  · intro x hx
    rw [← hn x (by simpa using hx), ncard_eq_card_filter]
    simp only [Finset.bipartiteBelow, Finset.filter_filter, Set.mem_ofPred_eq]

end Combinatorics

section TwoANbr

variable {G : Type*} [Group G]

theorem isConj_mul_swap (x c : G) : IsConj (x * c) (c * x) :=
  isConj_iff.mpr ⟨x⁻¹, by group⟩

theorem mem_twoANbr_comm {a x c : G} (hx : IsConj a x) (hc : IsConj a c) :
    c ∈ twoANbr a x ↔ x ∈ twoANbr a c :=
  ⟨fun h => ⟨hx, h.2.trans (isConj_mul_swap x c)⟩, fun h => ⟨hc, h.2.trans (isConj_mul_swap c x)⟩⟩

theorem mem_tableVISet_of_mul_ne {a b c y : G} (hbb : b * b = 1) (hy : y ∈ twoANbr a c)
    (h1 : b * y ≠ 1) (h2 : b * y ≠ c) : y ∈ tableVISet a b c := by
  refine ⟨hy, fun e => h1 (by rw [e, hbb]), fun e => h2 ?_⟩
  rw [e, ← mul_assoc, hbb, one_mul]

end TwoANbr

section Fibres

variable {G : Type*} [Group G]

theorem fibre_twoB_eq {a z₀ b c : G} (ha : orderOf a = 2) (hz : orderOf z₀ = 2)
    (hnc : ¬ IsConj a z₀) (hb : IsConj a b) (hc : c ∈ twoANbr a b) :
    {x | x ∈ twoBNbr a z₀ b ∧ c ∈ twoANbr a x} = tableVIOrbit a z₀ b c .two_B := by
  have hbb : b * b = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hb).symm.trans ha)
  ext x
  constructor
  · rintro ⟨⟨hxA, hbx⟩, hcx⟩
    refine ⟨mem_tableVISet_of_mul_ne hbb ((mem_twoANbr_comm hxA hc.1).mp hcx) ?_ ?_, hbx⟩
    · intro h
      rw [h] at hbx
      have h1 := isConj_one_left.mp hbx
      rw [h1, orderOf_one] at hz
      omega
    · intro h
      rw [h] at hbx
      exact hnc (hc.1.trans hbx.symm)
  · rintro ⟨hxO, hbx⟩
    exact ⟨⟨hxO.1.1, hbx⟩, (mem_twoANbr_comm hxO.1.1 hc.1).mpr hxO.1⟩

theorem fibre_fourA_eq {a z₀ b c : G} (ha : orderOf a = 2) (hb : IsConj a b)
    (hc : c ∈ twoANbr a b) :
    {x | x ∈ fourANbr a z₀ b ∧ c ∈ twoANbr a x} = tableVIOrbit a z₀ b c .four_A := by
  have hbb : b * b = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hb).symm.trans ha)
  have hc2 : orderOf c = 2 := (orderOf_eq_of_isConj hc.1).symm.trans ha
  ext x
  constructor
  · rintro ⟨⟨hxA, hbx4, hbxz⟩, hcx⟩
    refine ⟨mem_tableVISet_of_mul_ne hbb ((mem_twoANbr_comm hxA hc.1).mp hcx) ?_ ?_,
      hbx4, hbxz⟩
    · intro h
      rw [h, orderOf_one] at hbx4
      omega
    · intro h
      rw [h, hc2] at hbx4
      omega
  · rintro ⟨hxO, hbx4, hbxz⟩
    exact ⟨⟨hxO.1.1, hbx4, hbxz⟩, (mem_twoANbr_comm hxO.1.1 hc.1).mpr hxO.1⟩

end Fibres

section Conjugation

variable {G : Type*} [Group G]

theorem conj_mem_inter {a b g x c : G} (hg : g ∈ Subgroup.centralizer ({b} : Set G))
    (hc : c ∈ twoANbr a b ∩ twoANbr a x) :
    g * c * g⁻¹ ∈ twoANbr a b ∩ twoANbr a (g * x * g⁻¹) := by
  refine ⟨⟨hc.1.1.trans (isConj_conj_self g c), ?_⟩, ⟨hc.2.1.trans (isConj_conj_self g c), ?_⟩⟩
  · rw [← conj_mul_of_mem_centralizer hg c]
    exact hc.1.2.trans (isConj_conj_self g _)
  · rw [← conj_mul_conj g x c]
    exact hc.2.2.trans (isConj_conj_self g _)

variable [Finite G]

theorem ncard_inter_le {a b g x y : G} (hg : g ∈ Subgroup.centralizer ({b} : Set G))
    (hy : g * x * g⁻¹ = y) :
    (twoANbr a b ∩ twoANbr a x).ncard ≤ (twoANbr a b ∩ twoANbr a y).ncard := by
  subst hy
  exact Set.ncard_le_ncard_of_injOn (fun c => g * c * g⁻¹)
    (fun c hc => conj_mem_inter hg hc) (fun c _ c' _ h => mul_left_cancel (mul_right_cancel h))
    (Set.toFinite _)

theorem ncard_inter_conj {a b g x y : G} (hg : g ∈ Subgroup.centralizer ({b} : Set G))
    (hy : g * x * g⁻¹ = y) :
    (twoANbr a b ∩ twoANbr a x).ncard = (twoANbr a b ∩ twoANbr a y).ncard :=
  le_antisymm (ncard_inter_le hg hy)
    (ncard_inter_le (Subgroup.inv_mem _ hg) (by rw [← hy]; group))

end Conjugation

section Graph

variable {G : Type*} [Group G]

theorem adj_iff_mem_twoANbr {a : G} (ha : orderOf a = 2) (v c : ConjVert a) :
    (twoAGraph a).Adj v c ↔ (c : G) ∈ twoANbr a (v : G) := by
  refine ⟨fun h => ⟨c.2, h.2⟩, fun h => ⟨fun hvc => ?_, h.2⟩⟩
  have hv2 : orderOf (v : G) = 2 := (orderOf_eq_of_isConj v.2).symm.trans ha
  have h1 : IsConj a ((v : G) * c) := h.2
  rw [← hvc, mul_self_eq_one_of_orderOf hv2, isConj_comm, isConj_one_right] at h1
  rw [h1, orderOf_one] at ha
  exact absurd ha (by norm_num)

theorem ncard_commonNbr_vertex {a : G} (ha : orderOf a = 2) (v w : ConjVert a) :
    {c : ConjVert a | (twoAGraph a).Adj v c ∧ (twoAGraph a).Adj w c}.ncard =
      (twoANbr a (v : G) ∩ twoANbr a (w : G)).ncard := by
  refine (Set.ncard_image_of_injective _ Subtype.val_injective).symm.trans ?_
  congr 1
  ext c
  constructor
  · rintro ⟨c', ⟨h1, h2⟩, rfl⟩
    exact ⟨(adj_iff_mem_twoANbr ha v c').mp h1, (adj_iff_mem_twoANbr ha w c').mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨c, h1.1⟩, ⟨(adj_iff_mem_twoANbr ha v ⟨c, h1.1⟩).mpr h1,
      (adj_iff_mem_twoANbr ha w ⟨c, h1.1⟩).mpr h2⟩, rfl⟩

end Graph

section Table

variable {G : Type} [Group G] {d₀ : B}

theorem mem_tableVISet_of_mem_inter {a b c x : G} (ha : orderOf a = 2) (hb : IsConj a b)
    (hc : c ∈ twoANbr a b) (hcx : c ∈ twoANbr a x) (hxA : IsConj a x) (hxb : x ≠ b)
    (hodd : Odd (orderOf (b * x))) : x ∈ tableVISet a b c := by
  refine ⟨(mem_twoANbr_comm hxA hc.1).mp hcx, hxb, fun e => ?_⟩
  have hbb : b * b = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hb).symm.trans ha)
  have hc2 : orderOf c = 2 := (orderOf_eq_of_isConj hc.1).symm.trans ha
  rw [e, ← mul_assoc, hbb, one_mul, hc2] at hodd
  exact (Nat.not_odd_iff_even.mpr even_two) hodd

variable [Finite G]

theorem exists_class_of_mem_inter
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {b c x : G} (hb : IsConj a b) (hc : c ∈ twoANbr a b)
    (hcx : c ∈ twoANbr a x) (hxA : IsConj a x) (hxb : x ≠ b) (hodd : Odd (orderOf (b * x))) :
    ∃ K : TableVIClass, x ∈ tableVIOrbit a z₀ b c K ∧ orderOf (b * x) = tableVIOrder K := by
  have hxO := mem_tableVISet_of_mem_inter hG.1.1 hb hc hcx hxA hxb hodd
  obtain ⟨b₀, z, u, φ, C⟩ := exists_tableVICtx hSLS hTV hL hT3 hT4 hG hb hc
  obtain ⟨K, hK⟩ := C.exists_cond hxO
  exact ⟨K, ⟨hxO, hK⟩, C.orderOf_of_cond hxO hK⟩

theorem ncard_commonNbr_of_orbit
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {b x : G} (hb : IsConj a b) {K : TableVIIClass}
    {K' : TableVIClass}
    (hfib : ∀ c ∈ twoANbr a b,
      {y | y ∈ tableVIISet a z₀ b K ∧ c ∈ twoANbr a y} = tableVIOrbit a z₀ b c K')
    (hx : x ∈ tableVIISet a z₀ b K) :
    tableVIISize .two_A * tableVISize K' =
      tableVIISize K * (twoANbr a b ∩ twoANbr a x).ncard := by
  have hA : (twoANbr a b).ncard = tableVIISize .two_A :=
    table7_ncard hSLS hTV hL hT3 hT4 hDC hLP hG hb .two_A
  have hK : (tableVIISet a z₀ b K).ncard = tableVIISize K :=
    table7_ncard hSLS hTV hL hT3 hT4 hDC hLP hG hb K
  have hm : ∀ c ∈ twoANbr a b,
      {y | y ∈ tableVIISet a z₀ b K ∧ c ∈ twoANbr a y}.ncard = tableVISize K' := by
    intro c hc
    rw [hfib c hc]
    exact s341_ncard hSLS hTV hL hT3 hT4 hG hb hc K'
  have hn : ∀ y ∈ tableVIISet a z₀ b K,
      {c | c ∈ twoANbr a b ∧ c ∈ twoANbr a y}.ncard = (twoANbr a b ∩ twoANbr a x).ncard := by
    intro y hy
    obtain ⟨g, hg, hgxy⟩ := table7_transitive hSLS hTV hL hT3 hT4 hDC hLP hG hb hx hy
    exact (ncard_inter_conj hg hgxy).symm
  have h := card_mul_eq_card_mul_ncard (A := twoANbr a b) (K := tableVIISet a z₀ b K)
    (fun c y => c ∈ twoANbr a y) hm hn
  rwa [hA, hK] at h

end Table

end S57

section Counting

variable {G : Type} [Group G] [Finite G] {d₀ : B}

theorem ncard_commonNbr_twoB
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {b x : G} (hb : IsConj a b) (hx : x ∈ twoBNbr a z₀ b) :
    (twoANbr a b ∩ twoANbr a x).ncard = 9200 := by
  have h := S57.ncard_commonNbr_of_orbit hSLS hTV hL hT3 hT4 hDC hLP hG hb (K := .two_B)
    (K' := .two_B) (fun c hc => S57.fibre_twoB_eq hG.1.1 hG.2.1 hG.not_isConj hb hc) hx
  simp only [tableVIISize, tableVISize] at h
  omega

theorem ncard_commonNbr_fourA
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {b x : G} (hb : IsConj a b) (hx : x ∈ fourANbr a z₀ b) :
    (twoANbr a b ∩ twoANbr a x).ncard = 550 := by
  have h := S57.ncard_commonNbr_of_orbit hSLS hTV hL hT3 hT4 hDC hLP hG hb (K := .four_A)
    (K' := .four_A) (fun c hc => S57.fibre_fourA_eq hG.1.1 hb hc) hx
  simp only [tableVIISize, tableVISize] at h
  omega

theorem ncard_commonNbr_fourB
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {b x : G} (hb : IsConj a b) (hx : x ∈ fourBNbr a b) :
    (twoANbr a b ∩ twoANbr a x).ncard = 1 := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hw, hxO⟩ := h.mem_tableVIOrbit_four_B hb hx
  rw [s342_one hSLS hTV hL hT3 hT4 hG hb hw hxO.1 (Or.inl hxO.2), Set.ncard_singleton]

theorem ncard_commonNbr_sixA
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {b x : G} (hb : IsConj a b) (hx : x ∈ sixANbr a b) :
    (twoANbr a b ∩ twoANbr a x).ncard = 1 := by
  obtain ⟨b₀, z, u, h⟩ := exists_twoClasses hSLS hTV hL hG
  obtain ⟨hw, hxO⟩ := h.mem_tableVIOrbit_six_A hb hx
  rw [s342_one hSLS hTV hL hT3 hT4 hG hb hw hxO.1 (Or.inr hxO.2), Set.ncard_singleton]

theorem commonNbr_fiveA_eq_empty
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {b x : G} (hb : IsConj a b) (hx : x ∈ typeSet a z₀ b .fiveA) :
    twoANbr a b ∩ twoANbr a x = ∅ := by
  obtain ⟨⟨hxA, hxb, hodd, w, hw, hwB⟩, hty⟩ := hx
  have h5 : orderOf (b * x) = 5 := (s348_card hty hw hwB).1
  refine Set.eq_empty_of_forall_notMem fun c hc => ?_
  obtain ⟨K, -, hK⟩ :=
    S57.exists_class_of_mem_inter hSLS hTV hL hT3 hT4 hG hb hc.1 hc.2 hxA hxb hodd
  have hK' : tableVIOrder K = 5 := hK.symm.trans h5
  cases K <;> exact absurd hK' (by decide)

theorem commonNbr_threeC_eq_empty
    (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) (hT3 : BabyTableIII) (hT4 : BabyTableIV)
    (hDC : DoubleCoverThreeSwapIn G) (hLP : LeechPairStatement)
    (hLO : LeechOddPairStatement) (hT4' : TableIVIn G) {a z₀ : G}
    (hG : GMSF1Type d₀ a z₀) {b x : G} (hb : IsConj a b) (hx : x ∈ typeSet a z₀ b .threeC) :
    twoANbr a b ∩ twoANbr a x = ∅ := by
  obtain ⟨⟨hxA, hxb, hodd, w, hw, hwB⟩, hty⟩ := hx
  have hty' : LeechOddType w b x 1 := hty w hw hwB
  have h3 : orderOf (b * x) = 3 := hty'.orderOf_mul
  have h15 := s347_factorization_three_C hSLS hTV hL hLO hT4' hG hwB
    (IsOddPair.of_mem_inf hb hxA hxb.symm hodd hw) hty'
  refine Set.eq_empty_of_forall_notMem fun c hc => ?_
  obtain ⟨K, hxK, hK⟩ :=
    S57.exists_class_of_mem_inter hSLS hTV hL hT3 hT4 hG hb hc.1 hc.2 hxA hxb hodd
  have hK' : tableVIOrder K = 3 := hK.symm.trans h3
  have hK3 : K = .three_A := by
    cases K <;> first | rfl | exact absurd hK' (by decide)
  subst hK3
  have hcard := s341_card hSLS hTV hL hT3 hT4 hDC hLP hG hb hc.1 hxK
  have hdvd : Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({c} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) ∣
        Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Subgroup.card_dvd_of_le fun g hg => Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp
      (Subgroup.mem_inf.mp hg).1).1, (Subgroup.mem_inf.mp hg).2⟩
  have h18 : 2 ^ 18 ∣ Nat.card ↥(Subgroup.centralizer ({b} : Set G) ⊓
      Subgroup.centralizer ({c} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) := by
    rw [hcard]
    exact ⟨3 ^ 9 * 5 ^ 2 * 7 * 11 * 13, by norm_num [tableVIStab]⟩
  have h := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp
    (h18.trans hdvd)
  omega

end Counting

end CFSG.Monster.GMS
