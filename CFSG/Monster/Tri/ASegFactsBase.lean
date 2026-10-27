module

public import CFSG.Monster.GMS.S36LinesA12
public import CFSG.Monster.GMS.Facts.Section4Coh
public import CFSG.Monster.GMS.Facts.Interfaces
public import CFSG.Monster.GMS.Facts.Section37
public import CFSG.Monster.GMS.S36LinesBasic
public import CFSG.Monster.GMS.S4Defs
public import CFSG.Monster.GMS.S57
public import CFSG.Monster.Tri.ASegBase

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic
open scoped commutatorElement

section Basic

variable {G : Type*} [Group G] {a : G}

theorem commute_of_adj' (ha : orderOf a = 2) {x y : ConjVert a} (h : (twoAGraph a).Adj x y) :
    (x : G) * y = y * x :=
  S36Lines.mul_comm_of_isConj_mul ha x.2 y.2 h.2

theorem mul_self_of_vertex (ha : orderOf a = 2) (x : ConjVert a) : (x : G) * x = 1 :=
  S36Lines.sq_eq_one_of_isConj ha x.2

theorem exists_pow_conj_of_odd {x u : G} (hx : x * x = 1) (hu : u * u = 1)
    (hodd : Odd (orderOf (x * u))) : ∃ k : ℕ, (u * x) ^ k * u * ((u * x) ^ k)⁻¹ = x := by
  obtain ⟨k, hk⟩ := hodd
  refine ⟨k, ?_⟩
  have hinv : (x * u)⁻¹ = u * x := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hu]
  have hpow : (u * x) ^ (2 * k + 1) = 1 := by
    rw [← hinv, inv_pow, ← hk, pow_orderOf_eq_one, inv_one]
  have h2 : (u * x) ^ (2 * k) = x * u := by
    have h3 : (u * x) ^ (2 * k) * (u * x) = 1 := by rw [← pow_succ]; exact hpow
    have h4 := eq_inv_of_mul_eq_one_left h3
    rw [h4, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hu]
  rw [(conj_pow_mul_self hu hx k).1, h2, mul_assoc, hu, mul_one]

end Basic

section Facts

variable {G : Type*} [Group G]

structure ASegFacts (a z₀ : G) : Prop where
  gammaCover : GammaCover a z₀
  linesHaveInvolutions : LinesHaveInvolutions a
  commonNbrTwoB : CommonNbrTwoB a z₀
  oddTypeOrders : OddTypeOrders a z₀
  eightLines : EightGroupLines a z₀
  a12 : A12FusionAt a z₀
  fiveA : FiveAInvolutions a z₀
  fourAPerfect : FourAPerfect a z₀

end Facts

section Defs

variable {G : Type*} [Group G]

structure LeechGraphFacts (a z₀ : G) : Prop where
  diam : ∀ z : G, IsConj z₀ z → ∀ x y : ConjVert a, (x : G) ∈ leechQ z → (y : G) ∈ leechQ z →
    x = y ∨ (twoAGraph a).Adj x y ∨
      ∃ w : ConjVert a, (w : G) ∈ leechQ z ∧ (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w y
  mu : ∀ z : G, IsConj z₀ z → ∀ x y : ConjVert a, (x : G) ∈ leechQ z → (y : G) ∈ leechQ z →
    (twoAGraph a).dist x y = 2 → z ∈ Subgroup.zpowers ((x : G) * y) →
      ((twoAGraph a).induce ((twoAGraph a).commonNeighbors x y)).Preconnected

@[expose] def ThreeACommonNbrs (a z₀ : G) : Prop :=
  ∀ x y : ConjVert a, (y : G) ∈ typeSet a z₀ x .threeA →
    2 ≤ ((twoAGraph a).commonNeighbors x y).ncard ∧
      ((twoAGraph a).induce ((twoAGraph a).commonNeighbors x y)).Preconnected

@[expose] def MuConnected (a : G) : Prop :=
  ∀ x y : ConjVert a, (twoAGraph a).dist x y = 2 →
    ((twoAGraph a).induce ((twoAGraph a).commonNeighbors x y)).Preconnected

end Defs

section Local

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem mem_inter_of_adj (ha : orderOf a = 2) {x y w : ConjVert a} (h₁ : (twoAGraph a).Adj x w)
    (h₂ : (twoAGraph a).Adj w y) : (w : G) ∈ twoANbr a x ∩ twoANbr a y :=
  ⟨(S57.adj_iff_mem_twoANbr ha x w).1 h₁, (S57.adj_iff_mem_twoANbr ha y w).1 h₂.symm⟩

theorem dist_two_cases
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hGC : GammaCover a z₀) {x y : ConjVert a} (h : (twoAGraph a).dist x y = 2) :
    (y : G) ∈ twoBNbr a z₀ x ∨ (y : G) ∈ fourANbr a z₀ x ∨ (y : G) ∈ typeSet a z₀ x .threeA ∨
      (y : G) ∈ fourBNbr a x ∨ (y : G) ∈ sixANbr a x := by
  obtain ⟨hne, hna, w, h₁, h₂⟩ := dist_eq_two_iff.1 h
  have ha : orderOf a = 2 := hG.1.1
  have hcn := mem_inter_of_adj ha h₁ h₂
  rcases hGC x y x.2 y.2 with h | h
  · exact absurd (Subtype.ext h).symm hne
  · obtain ⟨K, hK⟩ := Set.mem_iUnion.1 h
    cases K with
    | twoA => exact absurd ((S57.adj_iff_mem_twoANbr ha x y).2 hK) hna
    | twoB => exact Or.inl hK
    | fourA => exact Or.inr (Or.inl hK)
    | threeA => exact Or.inr (Or.inr (Or.inl hK))
    | fourB => exact Or.inr (Or.inr (Or.inr (Or.inl hK)))
    | sixA => exact Or.inr (Or.inr (Or.inr (Or.inr hK)))
    | threeC =>
      have := commonNbr_threeC_eq_empty I.sls I.tableV I.leech I.tableIII I.tableIVBaby
        I.threeSwap I.leechPair I.leechOddPair I.tableIV hG x.2 hK
      rw [this] at hcn
      exact absurd hcn (Set.notMem_empty _)
    | fiveA =>
      have := commonNbr_fiveA_eq_empty I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG x.2 hK
      rw [this] at hcn
      exact absurd hcn (Set.notMem_empty _)

theorem dist_le_two_of_even
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    {x u : ConjVert a} (hev : Even (orderOf ((x : G) * u))) :
    x = u ∨ (twoAGraph a).Adj x u ∨ ∃ w : ConjVert a, (twoAGraph a).Adj x w ∧
      (twoAGraph a).Adj w u := by
  by_cases hxu : x = u
  · exact Or.inl hxu
  right
  have ha : orderOf a = 2 := hG.1.1
  have key : (twoANbr a x ∩ twoANbr a u).Nonempty →
      (twoAGraph a).Adj x u ∨ ∃ w : ConjVert a, (twoAGraph a).Adj x w ∧ (twoAGraph a).Adj w u := by
    rintro ⟨w, hw₁, hw₂⟩
    refine Or.inr ⟨⟨w, hw₁.1⟩, (S57.adj_iff_mem_twoANbr ha x ⟨w, hw₁.1⟩).2 hw₁, ?_⟩
    exact ((S57.adj_iff_mem_twoANbr ha u ⟨w, hw₁.1⟩).2 hw₂).symm
  rcases table7_cases I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG x.2 u.2 hev with
    h | h | h | h | h
  · exact Or.inl ((S57.adj_iff_mem_twoANbr ha x u).2 h)
  · refine key (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_commonNbr_twoB I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG x.2 h]
    norm_num
  · refine key (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_commonNbr_fourA I.sls I.tableV I.leech I.tableIII I.tableIVBaby I.threeSwap
      I.leechPair hG x.2 h]
    norm_num
  · refine key (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_commonNbr_fourB I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG x.2 h]
    norm_num
  · refine key (Set.nonempty_of_ncard_ne_zero ?_)
    rw [ncard_commonNbr_sixA I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG x.2 h]
    norm_num

omit [Finite G] in
theorem aseg_h83_2_of (hG : GMSF1Type d₀ a z₀) (F : ASegFacts a z₀) :
    ∀ x y v : ConjVert a, (twoAGraph a).dist x y = 2 → (twoAGraph a).Adj y v →
      ∃ i : G, i * i = 1 ∧ i ≠ 1 ∧ i * x = x * i ∧ i * y = y * i ∧ i * v = v * i := by
  intro x y v _ hyv
  have ha : orderOf a = 2 := hG.1.1
  obtain ⟨t, ht, ht2⟩ := F.linesHaveInvolutions x y v x.2 y.2
    ((S57.adj_iff_mem_twoANbr ha y v).1 hyv)
  obtain ⟨⟨htx, hty⟩, htv⟩ := Subgroup.mem_inf.1 ht
  exact ⟨t, mul_self_eq_one_of_orderOf ht2, ne_one_of_orderOf ht2,
    Subgroup.mem_centralizer_singleton_iff.1 htx, Subgroup.mem_centralizer_singleton_iff.1 hty,
    Subgroup.mem_centralizer_singleton_iff.1 htv⟩

theorem aseg_h814_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) :
    ∀ x u : ConjVert a, (∃ y : ConjVert a, (y = u ∨ (twoAGraph a).Adj y u) ∧
        (x : G) * y = y * x) →
      x = u ∨ (twoAGraph a).Adj x u ∨ ∃ w : ConjVert a, (twoAGraph a).Adj x w ∧
        (twoAGraph a).Adj w u := by
  rintro x u ⟨y, hy, hxy⟩
  have ha : orderOf a = 2 := hG.1.1
  rcases Nat.even_or_odd (orderOf ((x : G) * u)) with hev | hodd
  · exact dist_le_two_of_even I hG hev
  by_cases hxu : x = u
  · exact Or.inl hxu
  right
  have hxx := mul_self_of_vertex ha x
  have huu := mul_self_of_vertex ha u
  obtain hyu | hyu := hy
  ·
    subst hyu
    exfalso
    apply hxu
    have h2 : ((x : G) * y) * ((x : G) * y) = 1 := by
      calc (x : G) * y * ((x : G) * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hxx, huu, mul_one]
    have hd : orderOf ((x : G) * y) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    have h1 : orderOf ((x : G) * y) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    have h3 : (x : G) * y = 1 := orderOf_eq_one_iff.1 h1
    exact Subtype.ext (mul_eq_one_iff_eq_inv.1 h3 |>.trans (inv_eq_of_mul_eq_one_right huu))
  ·
    obtain ⟨k, hk⟩ := exists_pow_conj_of_odd hxx huu hodd
    have hyu' : (y : G) * u = u * y := commute_of_adj' ha hyu
    have hgy : ((u : G) * x) ^ k * y = y * ((u : G) * x) ^ k := by
      have hc : Commute ((u : G) * x) y :=
        Commute.mul_left (show Commute (u : G) y from hyu'.symm) (show Commute (x : G) y from hxy)
      exact (hc.pow_left k).eq
    by_cases hyx : y = x
    · exact Or.inl (hyx ▸ hyu)
    · refine Or.inr ⟨y, ⟨fun h => hyx h.symm, ?_⟩, hyu⟩
      have h1 : IsConj a (((u : G) * x) ^ k * ((y : G) * u) * (((u : G) * x) ^ k)⁻¹) :=
        isConj_conj hyu.2 _
      have e : ((u : G) * x) ^ k * ((y : G) * u) * (((u : G) * x) ^ k)⁻¹ = (x : G) * y := by
        calc ((u : G) * x) ^ k * ((y : G) * u) * (((u : G) * x) ^ k)⁻¹
            = (((u : G) * x) ^ k * y) * u * (((u : G) * x) ^ k)⁻¹ := by group
          _ = (y * ((u : G) * x) ^ k) * u * (((u : G) * x) ^ k)⁻¹ := by rw [hgy]
          _ = y * (((u : G) * x) ^ k * u * (((u : G) * x) ^ k)⁻¹) := by group
          _ = y * x := by rw [hk]
          _ = x * y := hxy.symm
      rwa [e] at h1

theorem aseg_h87_3_of (hG : GMSF1Type d₀ a z₀) :
    ∀ z : G, z * z = 1 → z ≠ 1 → IsConj z₀ z → ∀ x y v : ConjVert a, (x : G) ∈ leechQ z →
      (y : G) ∈ leechQ z → (v : G) ∈ leechQ z → (twoAGraph a).Adj x y →
        (v : G) * x = x * v ∨ (v : G) * y = y * v ∨ (v : G) * (x * y) = x * y * v := by
  intro z _ _ hz x y v hx hy hv _
  have hE := (hG.2.of_isConj hz).extraspecialData
  have hxy := hE.commutatorElement_mul_left hx hy hv
  have e : ∀ g h : G, ⁅g, h⁆ = 1 → h * g = g * h := fun g h hgh =>
    (commutatorElement_eq_one_iff_mul_comm.1 hgh).symm
  rcases hE.comm x hx v hv with h1 | h1
  · exact Or.inl (e _ _ h1)
  rcases hE.comm y hy v hv with h2 | h2
  · exact Or.inr (Or.inl (e _ _ h2))
  · refine Or.inr (Or.inr (e _ _ ?_))
    rw [hxy, h1, h2]
    exact hE.mul_self

end Local

end CFSG.Monster.Tri
