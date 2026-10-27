module

public import CFSG.Monster.Tri.ASegFactsLocal
public import CFSG.Monster.Tri.ASegFactsTransfer

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic

section Fusion

variable {G : Type} [Group G] [Finite G] {a : G}

omit [Finite G] in
theorem relIndex_eq_of_card {J I : Subgroup G} {N M r : ℕ} (hJ : Nat.card J = N)
    (hI : Nat.card ↥(J ⊓ I) = M) (h : r * M = N) (hM : 0 < M) : I.relIndex J = r := by
  have h1 := Subgroup.relIndex_mul_card (H := I) (K := J)
  rw [inf_comm I J, hI, hJ] at h1
  exact Nat.eq_of_mul_eq_mul_right hM (h1.trans h.symm)

theorem exists_fixed_commonNbr {x y i b : G} (hi2 : orderOf i = 2) (hix : i * x = x * i)
    (hiy : i * y = y * i) (hb : b ∈ twoANbr a x ∩ twoANbr a y)
    (hidx : ¬ 4 ∣ (Subgroup.centralizer ({b} : Set G)).relIndex
      (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}))
    (hperf : 2 ∣ (Subgroup.centralizer ({b} : Set G)).relIndex
        (Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) →
      ⁅Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y},
        Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}⁆ =
          Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y}) :
    ∃ v ∈ twoANbr a x ∩ twoANbr a y, i * v = v * i := by
  have hiJ : i ∈ Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer {y} :=
    Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hix,
      Subgroup.mem_centralizer_singleton_iff.2 hiy⟩
  obtain ⟨g, hgJ, hg⟩ := exists_conj_mem_of_relIndex hidx hperf hiJ hi2
  refine ⟨g⁻¹ * b * g, ?_, ?_⟩
  · simpa using conj_mem_twoANbr_inter (a := a) (Subgroup.inv_mem _ hgJ) hb
  · have h := Subgroup.mem_centralizer_singleton_iff.1 hg
    calc i * (g⁻¹ * b * g) = g⁻¹ * (g * i * g⁻¹ * b) * g := by group
      _ = g⁻¹ * (b * (g * i * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * b * g * i := by group

end Fusion

section Eight10

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem aseg_hinv_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∀ g : G, g ≠ 1 → g * g = 1 → IsConj a g ∨ g ∈ {w : G | IsConj z₀ w} := fun _ hg1 hgg =>
  s31_five I.sls I.tableV I.leech hG I.leechInv (orderOf_eq_two_of_mul_self hgg hg1)

theorem aseg_h810_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (F : ASegFacts a z₀) :
    ∀ i : G, i * i = 1 → i ≠ 1 → ∀ x y : ConjVert a, i * x = x * i → i * y = y * i →
      (twoAGraph a).dist x y = 2 → (x : G) * y ≠ y * x →
        ∃ v : ConjVert a, i * v = v * i ∧ (twoAGraph a).Adj v x ∧ (twoAGraph a).Adj v y := by
  intro i hii hi1 x y hix hiy hd hxy
  have ha : orderOf a = 2 := hG.1.1
  have hi2 : orderOf i = 2 := orderOf_eq_two_of_mul_self hii hi1
  have hxx := mul_self_of_vertex ha x
  have hyy := mul_self_of_vertex ha y
  obtain ⟨-, -, w, hxw, hwy⟩ := dist_eq_two_iff.1 hd
  have hb : (w : G) ∈ twoANbr a x ∩ twoANbr a y := mem_inter_of_adj ha hxw hwy
  have key : ∀ v : G, v ∈ twoANbr a x ∩ twoANbr a y → i * v = v * i →
      ∃ v : ConjVert a, i * v = v * i ∧ (twoAGraph a).Adj v x ∧ (twoAGraph a).Adj v y := by
    intro v hv hiv
    exact ⟨⟨v, hv.1.1⟩, hiv, ((S57.adj_iff_mem_twoANbr ha x ⟨v, hv.1.1⟩).2 hv.1).symm,
      ((S57.adj_iff_mem_twoANbr ha y ⟨v, hv.1.1⟩).2 hv.2).symm⟩
  have hcomm : Commute i ((x : G) * y) := Commute.mul_right hix hiy
  rcases dist_two_cases I hG F.gammaCover hd with h | h | h | h | h
  ·
    exfalso
    have hz2 : orderOf ((x : G) * y) = 2 := (orderOf_eq_of_isConj h.2).symm.trans hG.2.1
    exact hxy (commute_of_mul_self hxx hyy (mul_self_eq_one_of_orderOf hz2))
  ·
    have hJ := card_centralizer_inf_of_mem_fourANbr I.sls I.tableV I.leech I.leechPair hG x.2 h
    have hS := (s342_two I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap I.leechPair
      hG x.2 y.2 ⟨h.2.1, h.2.2⟩).2 w hb
    have hr := relIndex_eq_of_card (I := Subgroup.centralizer ({(w : G)} : Set G)) (r := 550) hJ hS
      (by norm_num) (by norm_num)
    obtain ⟨v, hv, hiv⟩ := exists_fixed_commonNbr (a := a) hi2 hix hiy hb
      (by rw [hr]; norm_num) (fun _ => F.fourAPerfect x y x.2 h)
    exact key v hv hiv
  ·
    have hK : orderOf ((x : G) * y) = 3 :=
      S36Lines.orderOf_mul_of_mem_typeSet ha hG.2.1 (K := .threeA) h
    have hJ := F.oddTypeOrders x y 0 x.2 h.1 h.2
    have hS := (s342_three I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG x.2 y.2 hK).2 w hb
    have hr := relIndex_eq_of_card (I := Subgroup.centralizer ({(w : G)} : Set G)) (r := 31671)
      hJ hS (by norm_num [oddTypeStab]) (by norm_num)
    obtain ⟨v, hv, hiv⟩ := exists_fixed_commonNbr (a := a) hi2 hix hiy hb
      (by rw [hr]; norm_num) (fun h2 => absurd (hr ▸ h2) (by norm_num))
    exact key v hv hiv
  ·
    obtain ⟨h₁, h₂⟩ := fourB_center_adj ha (y := x) (u := y) h
    exact ⟨_, (hcomm.pow_right 2).eq, h₁.symm, h₂.symm⟩
  ·
    obtain ⟨h₁, h₂⟩ := sixA_center_adj ha (y := x) (u := y) h
    exact ⟨_, (hcomm.pow_right 3).eq, h₁.symm, h₂.symm⟩

end Eight10

section Eight13

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

theorem fin3_cases (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  fin_cases k <;> simp

theorem aseg_h813_1_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (F : ASegFacts a z₀) :
    ∀ z : G, z * z = 1 → z ≠ 1 → IsConj z₀ z → ∀ x y : ConjVert a, z * x = x * z →
      z * y = y * z →
      (∃ b : ConjVert a, z * b = b * z ∧ (x : G) * b = b * x ∧ (y : G) * b = b * y) ∨
        orderOf ((x : G) * y) = 3 := by
  intro z hzz hz1 hz x y hzx hzy
  have ha : orderOf a = 2 := hG.1.1
  have hz2 : orderOf z = 2 := orderOf_eq_two_of_mul_self hzz hz1
  by_cases hc : (x : G) * y = y * x
  · exact Or.inl ⟨x, hzx, rfl, hc.symm⟩
  rcases Nat.even_or_odd (orderOf ((x : G) * y)) with hev | hodd
  · left
    rcases dist_le_two_of_even I hG hev with hxy | hadj | ⟨w, hxw, hwy⟩
    · exact absurd (by rw [hxy]) hc
    · exact absurd (commute_of_adj' ha hadj) hc
    · have hd : (twoAGraph a).dist x y = 2 := dist_eq_two_iff.2
        ⟨fun e => hc (by rw [e]), fun h => hc (commute_of_adj' ha h), w, hxw, hwy⟩
      obtain ⟨v, hzv, hvx, hvy⟩ := aseg_h810_of I hG F z hzz hz1 x y hzx hzy hd hc
      exact ⟨v, hzv, (commute_of_adj' ha hvx).symm, (commute_of_adj' ha hvy).symm⟩
  · have hyx : (y : G) ≠ x := fun e => hc (by rw [e])
    have hzJ : z ∈ Subgroup.centralizer ({(x : G)} : Set G) ⊓ Subgroup.centralizer {(y : G)} :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hzx,
        Subgroup.mem_centralizer_singleton_iff.2 hzy⟩
    have hy : (y : G) ∈ oddNbr a z₀ x := ⟨y.2, hyx, hodd, z, hzJ, hz⟩
    obtain ⟨k, hk, -⟩ := s348_type I.sls I.tableV I.leech I.leechOddPair I.tableIV hG x.2 hy
    rcases fin3_cases k with rfl | rfl | rfl
    · exact Or.inr (S36Lines.orderOf_mul_of_mem_typeSet ha hG.2.1 (K := .threeA) ⟨hy, hk⟩)
    · exact Or.inr (S36Lines.orderOf_mul_of_mem_typeSet ha hG.2.1 (K := .threeC) ⟨hy, hk⟩)
    · left
      obtain ⟨hfus, t, ht, t', ht', htt', hta, ht'z, -⟩ := F.fiveA x y x.2 ⟨hy, hk⟩
      have ht'2 : orderOf t' = 2 := (orderOf_eq_of_isConj ht'z).symm.trans hG.2.1
      obtain ⟨g, hgJ, hg⟩ := hfus t' ht' z hzJ ht'2 hz2 (Or.inr ⟨ht'z, hz⟩)
      obtain ⟨hgx, hgy⟩ := Subgroup.mem_inf.1 hgJ
      obtain ⟨htx, hty⟩ := Subgroup.mem_inf.1 ht
      have hxg : Commute (x : G) g := (Subgroup.mem_centralizer_singleton_iff.1 hgx).symm
      have hyg : Commute (y : G) g := (Subgroup.mem_centralizer_singleton_iff.1 hgy).symm
      have hxt : Commute (x : G) t := (Subgroup.mem_centralizer_singleton_iff.1 htx).symm
      have hyt : Commute (y : G) t := (Subgroup.mem_centralizer_singleton_iff.1 hty).symm
      refine ⟨⟨g * t * g⁻¹, hta.trans (isConj_conj_self g t)⟩, ?_, ?_, ?_⟩
      · calc z * (g * t * g⁻¹) = (g * t' * g⁻¹) * (g * t * g⁻¹) := by rw [hg]
          _ = g * (t' * t) * g⁻¹ := by group
          _ = g * (t * t') * g⁻¹ := by rw [htt']
          _ = (g * t * g⁻¹) * (g * t' * g⁻¹) := by group
          _ = (g * t * g⁻¹) * z := by rw [hg]
      · exact ((hxg.mul_right hxt).mul_right hxg.inv_right).eq
      · exact ((hyg.mul_right hyt).mul_right hyg.inv_right).eq

end Eight13

end CFSG.Monster.Tri
