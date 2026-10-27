module

public import CFSG.Monster.Tri.ASegFactsBase

public section

namespace CFSG.Monster.Tri

open SimpleGraph CFSG.Monster.GMS CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog
  CFSG.YGroups

section Algebra

variable {G : Type*} [Group G]

theorem inv_eq_self_of_mul_self' {y : G} (hy : y * y = 1) : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy

theorem sq_expand (y u : G) : (y * u) ^ 2 = y * u * y * u := by
  rw [pow_two]; simp only [mul_assoc]

theorem cube_expand (y u : G) : (y * u) ^ 3 = y * u * y * u * y * u := by
  rw [pow_succ, pow_two]; simp only [mul_assoc]

theorem fourB_algebra {y u : G} (hy : y * y = 1) (hu : u * u = 1) (h4 : (y * u) ^ 4 = 1) :
    (y * u) ^ 2 * (y * u) ^ 2 = 1 ∧ y * (y * u) ^ 2 = u * y * u ∧
      u * (y * u) ^ 2 = y * u * y ∧ (y * u) ^ 2 * y = y * (y * u) ^ 2 ∧
      (y * u) ^ 2 * u = u * (y * u) ^ 2 := by
  have hyi := inv_eq_self_of_mul_self' hy
  have hui := inv_eq_self_of_mul_self' hu
  have hs : (y * u) ^ 2 * (y * u) ^ 2 = 1 := by
    rw [← pow_add]; exact h4
  have hsi : y * u * y * u = u * y * u * y := by
    have h := eq_inv_of_mul_eq_one_left hs
    rw [sq_expand] at h
    rw [h]
    simp [mul_inv_rev, hyi, hui, mul_assoc]
  have h1 : y * (y * u * y * u) = u * y * u := by
    calc y * (y * u * y * u) = (y * y) * u * y * u := by group
      _ = u * y * u := by rw [hy, one_mul]
  have h2 : u * (y * u * y * u) = y * u * y := by
    rw [hsi]
    calc u * (u * y * u * y) = (u * u) * y * u * y := by group
      _ = y * u * y := by rw [hu, one_mul]
  rw [sq_expand] at hs ⊢
  refine ⟨hs, h1, h2, ?_, ?_⟩
  · rw [h1]
    calc y * u * y * u * y = y * (u * y * u * y) := by group
      _ = u * y * u := by rw [← hsi]; exact h1
  · rw [h2]
    calc y * u * y * u * u = y * u * y * (u * u) := by group
      _ = y * u * y := by rw [hu, mul_one]

theorem sixA_algebra {y u : G} (hy : y * y = 1) (hu : u * u = 1) (h6 : (y * u) ^ 6 = 1) :
    (y * u) ^ 3 * y = y * (y * u) ^ 3 ∧ (y * u) ^ 3 * u = u * (y * u) ^ 3 ∧
      y * (y * u) ^ 3 = u * y * u * y * u ∧ u * (y * u) ^ 3 = y * u * y * u * y ∧
      u = (y * u) ^ 3 * (y * u * y * u * y) := by
  have hyi := inv_eq_self_of_mul_self' hy
  have hui := inv_eq_self_of_mul_self' hu
  have hs : (y * u) ^ 3 * (y * u) ^ 3 = 1 := by
    rw [← pow_add]; exact h6
  rw [cube_expand] at hs
  have hsi : y * u * y * u * y * u = u * y * u * y * u * y := by
    have h := eq_inv_of_mul_eq_one_left hs
    rw [h]
    simp [mul_inv_rev, hyi, hui, mul_assoc]
  have h1 : y * (y * u * y * u * y * u) = u * y * u * y * u := by
    calc y * (y * u * y * u * y * u) = (y * y) * u * y * u * y * u := by group
      _ = u * y * u * y * u := by rw [hy, one_mul]
  have hc1 : y * u * y * u * y * u * y = y * (y * u * y * u * y * u) := by
    rw [h1]
    calc y * u * y * u * y * u * y = y * (u * y * u * y * u * y) := by group
      _ = y * (y * u * y * u * y * u) := by rw [hsi]
      _ = u * y * u * y * u := h1
  have h2 : y * u * y * u * y * u * u = y * u * y * u * y := by
    calc y * u * y * u * y * u * u = y * u * y * u * y * (u * u) := by group
      _ = y * u * y * u * y := by rw [hu, mul_one]
  have hc2 : u * (y * u * y * u * y * u) = y * u * y * u * y * u * u := by
    rw [h2]
    calc u * (y * u * y * u * y * u) = (u * y * u * y * u * y) * u := by group
      _ = (y * u * y * u * y * u) * u := by rw [hsi]
      _ = y * u * y * u * y := h2
  have hfin : u = y * u * y * u * y * u * (y * u * y * u * y) := by
    have h12 : (y * u * y * u * y * u) * (y * u * y * u * y * u) = 1 := hs
    calc u = (y * u * y * u * y * u) * (y * u * y * u * y * u) * u := by rw [h12, one_mul]
      _ = y * u * y * u * y * u * (y * u * y * u * y * u * u) := by group
      _ = y * u * y * u * y * u * (y * u * y * u * y) := by rw [h2]
  rw [cube_expand]
  exact ⟨hc1, hc2.symm, h1, by rw [hc2, h2], hfin⟩

end Algebra

section Graph

variable {V : Type*}

theorem preconnected_induce_of_ncard_le_one [Finite V] (Γ : SimpleGraph V) {S : Set V}
    (h : S.ncard ≤ 1) : (Γ.induce S).Preconnected := by
  have hsub : ∀ p q : S, p = q := fun p q =>
    Subtype.ext ((Set.ncard_le_one_iff (Set.toFinite S)).1 h p.2 q.2)
  intro p q
  rw [hsub p q]

end Graph

section Vertices

variable {G : Type*} [Group G] {a : G}

theorem adj_of_conj {p q : ConjVert a} (hne : (p : G) ≠ q) (h : IsConj a ((p : G) * q)) :
    (twoAGraph a).Adj p q :=
  ⟨fun e => hne (congrArg Subtype.val e), h⟩

end Vertices

section Mu

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem ncard_commonNeighbors_eq (ha : orderOf a = 2) (x y : ConjVert a) :
    ((twoAGraph a).commonNeighbors x y).ncard = (twoANbr a (x : G) ∩ twoANbr a (y : G)).ncard := by
  rw [← S57.ncard_commonNbr_vertex ha x y]
  congr 1

theorem aseg_hmu_of
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (F : ASegFacts a z₀)
    (hL : LeechGraphFacts a z₀) (h3A : ThreeACommonNbrs a z₀) : MuConnected a := by
  intro x y hd
  have ha : orderOf a = 2 := hG.1.1
  have hxx := mul_self_of_vertex ha x
  have hyy := mul_self_of_vertex ha y
  rcases dist_two_cases I hG F.gammaCover hd with h | h | h | h | h
  ·
    have hz : IsConj z₀ ((x : G) * y) := h.2
    have hz2 : orderOf ((x : G) * y) = 2 := (orderOf_eq_of_isConj hz).symm.trans hG.2.1
    have hc : (x : G) * y = y * x :=
      commute_of_mul_self hxx hyy (mul_self_eq_one_of_orderOf hz2)
    have hxQ : (x : G) ∈ leechQ ((x : G) * y) := by
      refine mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG x.2 hz ?_ ?_
      · calc (x : G) * (x * y) = y := by rw [← mul_assoc, hxx, one_mul]
          _ = (x * y) * x := by rw [hc, mul_assoc, hxx, mul_one]
      · rw [← mul_assoc, hxx, one_mul]
        exact y.2
    have hyQ : (y : G) ∈ leechQ ((x : G) * y) := by
      refine mem_leechQ_of_isConj_mul I.sls I.tableV I.leech hG y.2 hz ?_ ?_
      · calc (y : G) * (x * y) = x := by rw [hc, ← mul_assoc, hyy, one_mul]
          _ = (x * y) * y := by rw [mul_assoc, hyy, mul_one]
      · rw [hc, ← mul_assoc, hyy, one_mul]
        exact x.2
    exact hL.mu _ hz x y hxQ hyQ hd (Subgroup.mem_zpowers _)
  ·
    obtain ⟨b, z, u, hT⟩ := exists_twoClasses I.sls I.tableV I.leech hG
    obtain ⟨hxQ, hyQ⟩ := TwoClasses.fourANbr_data hT x.2 h
    exact hL.mu _ h.2.2 x y hxQ hyQ hd (Subgroup.mem_zpowers_iff.2 ⟨2, by simp⟩)
  · exact (h3A x y h).2
  · refine preconnected_induce_of_ncard_le_one _ ?_
    rw [ncard_commonNeighbors_eq ha,
      ncard_commonNbr_fourB I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG x.2 h]
  · refine preconnected_induce_of_ncard_le_one _ ?_
    rw [ncard_commonNeighbors_eq ha,
      ncard_commonNbr_sixA I.sls I.tableV I.leech I.tableIII I.tableIVBaby hG x.2 h]

omit [Finite G] in
theorem aseg_h88_of (hμ : MuConnected a) :
    ∀ (u : ConjVert a) (c : (twoAGraph a).Walk u u), c.length ≤ 4 → Homotopic c .nil :=
  fun _ c hc => homotopic_nil_of_length_le_four_of_mu (fun x y h => hμ x y h) c hc

end Mu

section Centre

theorem not_commute_of_orderOf_eq {G : Type*} [Group G] {y u : G} (hyy : y * y = 1)
    (huu : u * u = 1) {n : ℕ} (hn : 2 < n) (hord : orderOf (y * u) = n) : y * u ≠ u * y := by
  intro hcm
  have h2' : y * u * (y * u) = 1 := by
    calc y * u * (y * u) = y * (u * y) * u := by group
      _ = y * (y * u) * u := by rw [hcm]
      _ = (y * y) * (u * u) := by group
      _ = 1 := by rw [hyy, huu, mul_one]
  have hd : orderOf (y * u) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2')
  rw [hord] at hd
  have := Nat.le_of_dvd (by norm_num) hd
  omega

variable {G : Type} [Group G] {a : G}

theorem fourB_center_adj (ha : orderOf a = 2) {y u : ConjVert a}
    (h : (u : G) ∈ fourBNbr a (y : G)) :
    (twoAGraph a).Adj y ⟨((y : G) * u) ^ 2, h.2.2⟩ ∧
      (twoAGraph a).Adj u ⟨((y : G) * u) ^ 2, h.2.2⟩ := by
  have hyy := mul_self_of_vertex ha y
  have huu := mul_self_of_vertex ha u
  have hr4 : ((y : G) * u) ^ 4 = 1 := by rw [← h.2.1]; exact pow_orderOf_eq_one _
  obtain ⟨-, h1, h2, hc1, hc2⟩ := fourB_algebra hyy huu hr4
  have hnc := not_commute_of_orderOf_eq hyy huu (by norm_num : 2 < 4) h.2.1
  refine ⟨adj_of_conj (fun e => hnc (by rw [e]; exact hc2)) ?_,
    adj_of_conj (fun e => hnc (by rw [e]; exact hc1.symm)) ?_⟩
  · show IsConj a ((y : G) * ((y : G) * u) ^ 2)
    have := isConj_conj y.2 (u : G)
    rw [inv_eq_self_of_mul_self' huu] at this
    rwa [h1]
  · show IsConj a ((u : G) * ((y : G) * u) ^ 2)
    have := isConj_conj u.2 (y : G)
    rw [inv_eq_self_of_mul_self' hyy] at this
    rwa [h2]

theorem sixA_center_adj (ha : orderOf a = 2) {y u : ConjVert a}
    (h : (u : G) ∈ sixANbr a (y : G)) :
    (twoAGraph a).Adj y ⟨((y : G) * u) ^ 3, h.2.2⟩ ∧
      (twoAGraph a).Adj u ⟨((y : G) * u) ^ 3, h.2.2⟩ := by
  have hyy := mul_self_of_vertex ha y
  have huu := mul_self_of_vertex ha u
  have hyi := inv_eq_self_of_mul_self' hyy
  have hui := inv_eq_self_of_mul_self' huu
  have hr6 : ((y : G) * u) ^ 6 = 1 := by rw [← h.2.1]; exact pow_orderOf_eq_one _
  obtain ⟨hc1, hc2, h1, h2, -⟩ := sixA_algebra hyy huu hr6
  have hnc := not_commute_of_orderOf_eq hyy huu (by norm_num : 2 < 6) h.2.1
  refine ⟨adj_of_conj (fun e => hnc (by rw [e]; exact hc2)) ?_,
    adj_of_conj (fun e => hnc (by rw [e]; exact hc1.symm)) ?_⟩
  · show IsConj a ((y : G) * ((y : G) * u) ^ 3)
    have := isConj_conj u.2 ((u : G) * y)
    rw [mul_inv_rev, hyi, hui] at this
    rw [h1]
    simpa [mul_assoc] using this
  · show IsConj a ((u : G) * ((y : G) * u) ^ 3)
    have := isConj_conj y.2 ((y : G) * u)
    rw [mul_inv_rev, hyi, hui] at this
    rw [h2]
    simpa [mul_assoc] using this

end Centre

end CFSG.Monster.Tri
