module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.Index
public import CFSG.Quasithin.EmptyFaithful.SzF53B3O1Alg
public import CFSG.Quasithin.EmptyFaithful.SzF53BasD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7

namespace F53.Stellmacher.S42B1

open CosetGeom F53

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure Tri (β a b c : Geo H M) : Prop where
  ha : a ∈ nbrs β
  hb : b ∈ nbrs β
  hc : c ∈ nbrs β
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c
  all : ∀ w ∈ nbrs β, w = a ∨ w = b ∨ w = c

section Tri

variable {β a b c : Geo H M}

omit [Finite G] in
theorem Tri.swap₁₂ (T : Tri β a b c) : Tri β b a c :=
  ⟨T.hb, T.ha, T.hc, T.hab.symm, T.hbc, T.hac, fun w hw => by
    rcases T.all w hw with h | h | h <;> simp [h]⟩

omit [Finite G] in
theorem Tri.swap₂₃ (T : Tri β a b c) : Tri β a c b :=
  ⟨T.ha, T.hc, T.hb, T.hac, T.hab, T.hbc.symm, fun w hw => by
    rcases T.all w hw with h | h | h <;> simp [h]⟩

theorem exists_tri (hA : F53Amalgam H M S) (hv : vtype β = true) (ha : a ∈ nbrs β) :
    ∃ b c : Geo H M, Tri β a b c := by
  have hcard : (nbrs β).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]; exact card_nbrs_true hA hv
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Set.ncard_eq_three.mp hcard
  rw [hs] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨y, z, by rw [hs]; simp, by rw [hs]; simp, by rw [hs]; simp, hxy, hxz, hyz,
      fun w hw => by rw [hs] at hw; simpa using hw⟩
  · exact ⟨x, z, by rw [hs]; simp, by rw [hs]; simp, by rw [hs]; simp, hxy.symm, hyz, hxz,
      fun w hw => by rw [hs] at hw; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
                     tauto⟩
  · exact ⟨x, y, by rw [hs]; simp, by rw [hs]; simp, by rw [hs]; simp, hxz.symm, hyz.symm, hxy,
      fun w hw => by rw [hs] at hw; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
                     tauto⟩

omit [Finite G] in
theorem smul_mem_nbrs_of_mem_stab {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab β) {μ : Geo H M}
    (hμ : μ ∈ nbrs β) : g • μ ∈ nbrs β := by
  have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj β μ from hμ)
  rwa [smul_eq_of_mem_stab hg] at this

theorem Tri.mem_Qv_of_fix (hA : F53Amalgam H M S) (T : Tri β a b c) {g : ↥(H ⊔ M)}
    (hg : (g : G) ∈ stab β) (ha : g • a = a) (hb : g • b = b) : (g : G) ∈ Qv β := by
  have hc : g • c = c := by
    have hmem := smul_mem_nbrs_of_mem_stab hg T.hc
    rcases T.all _ hmem with h | h | h
    · exact absurd (MulAction.injective g (h.trans ha.symm)) T.hac.symm
    · exact absurd (MulAction.injective g (h.trans hb.symm)) T.hbc.symm
    · exact h
  rw [Qv_eq_iInf hA]
  refine Subgroup.mem_iInf.mpr fun μ => Subgroup.mem_iInf.mpr fun hμ => ?_
  refine ⟨hg, ?_⟩
  rcases T.all μ hμ with rfl | rfl | rfl
  · exact mem_stab_of_smul_eq ha
  · exact mem_stab_of_smul_eq hb
  · exact mem_stab_of_smul_eq hc

theorem Tri.swap (hA : F53Amalgam H M S) (T : Tri β a b c) {g : ↥(H ⊔ M)}
    (hg : (g : G) ∈ stab β) (ha : g • a = a) (hgQ : (g : G) ∉ Qv β) :
    g • b = c ∧ g • c = b := by
  have h1 := smul_mem_nbrs_of_mem_stab hg T.hb
  have h2 := smul_mem_nbrs_of_mem_stab hg T.hc
  have hb : g • b = c := by
    rcases T.all _ h1 with h | h | h
    · exact absurd (MulAction.injective g (h.trans ha.symm)) T.hab.symm
    · exact absurd (T.mem_Qv_of_fix hA hg ha h) hgQ
    · exact h
  refine ⟨hb, ?_⟩
  rcases T.all _ h2 with h | h | h
  · exact absurd (MulAction.injective g (h.trans ha.symm)) T.hac.symm
  · exact h
  · exact absurd (MulAction.injective g (h.trans hb.symm)) T.hbc.symm

theorem exists_stab_elem (hA : F53Amalgam H M S) (hv : vtype β = true) (ha : a ∈ nbrs β) :
    ∃ g : ↥(H ⊔ M), (g : G) ∈ stab β ∧ g • a = a ∧ (g : G) ∉ Qv β := by
  by_contra hcon
  push Not at hcon
  have h1 : (Qv β).relIndex (stab β ⊓ stab a) = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro x hx
    by_contra hxQ
    exact hxQ (hcon ⟨x, stab_le β hx.1⟩ hx.1 (smul_eq_of_mem_stab hx.2))
  have := relIndex_Qv_inf_true hA ha hv
  omega

omit [Finite G] in
theorem conjSub_Qv_of_mem_stab {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab β) :
    conjSub (g : G) (Qv β) = Qv β := by
  rw [← Qv_smul, smul_eq_of_mem_stab hg]

omit [Finite G] in
theorem conjSub_Aq {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab β) (μ : Geo H M) :
    conjSub (g : G) (Zv μ ⊓ Qv β) = Zv (g • μ) ⊓ Qv β := by
  rw [conjSub_inf, ← Zv_smul, conjSub_Qv_of_mem_stab hg]

omit [Finite G] in
theorem not_Zv_le_Qv_of_nbr {a μ : Geo H M} (ha : a ∈ nbrs β) (hμ : μ ∈ nbrs β)
    (h : ¬ Zv a ≤ Qv β) : ¬ Zv μ ≤ Qv β := by
  obtain ⟨g, hg, hga⟩ := stab_transitive_on_nbrs ha hμ
  intro hle
  apply h
  have h1 : conjSub (g : G) (Zv a) ≤ conjSub (g : G) (Qv β) := by
    rw [← Zv_smul, hga, conjSub_Qv_of_mem_stab hg]; exact hle
  have h2 := (conjSub_le_iff (g : G)).mp h1
  rwa [conjSub_conjSub_inv] at h2

omit [Finite G] in
theorem nbrs_symm {a : Geo H M} (h : a ∈ nbrs β) : β ∈ nbrs a :=
  (show (graph (H ⊔ M) H M).Adj β a from h).symm

omit [Finite G] in
theorem vtype_false_of_nbr {a : Geo H M} (hβ : vtype β = true) (h : a ∈ nbrs β) :
    vtype a = false := by
  have := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj β a from h)
  rw [hβ] at this
  cases hv : vtype a
  · rfl
  · exact absurd hv.symm this

theorem Zv_le_edge (hA : F53Amalgam H M S) {a : Geo H M} (h : a ∈ nbrs β) :
    Zv a ≤ stab β ⊓ stab a := by
  have := Qv_le_inf hA (nbrs_symm h)
  rw [inf_comm] at this
  exact (Zv_le_Qv hA a).trans this

theorem edge_eq_mul (hA : F53Amalgam H M S) (hv : vtype β = true) {a : Geo H M}
    (ha : a ∈ nbrs β) (hn : ¬ Zv a ≤ Qv β) :
    ∀ s ∈ stab β ⊓ stab a, ∃ q ∈ Qv β, ∃ z ∈ Zv a, s = q * z := by
  intro s hs
  obtain ⟨z₀, hz₀, hz₀Q⟩ := Set.not_subset.mp hn
  by_cases hsQ : s ∈ Qv β
  · exact ⟨s, hsQ, 1, Subgroup.one_mem _, (mul_one s).symm⟩
  · have h2 := relIndex_Qv_inf_true hA ha hv
    refine ⟨s * z₀⁻¹, F53B3.O1.mul_inv_mem_of_relIndex_two h2 hs (Zv_le_edge hA ha hz₀) hsQ hz₀Q,
      z₀, hz₀, by group⟩

theorem three_dvd_card_stab (hA : F53Amalgam H M S) (hv : vtype β = true) :
    3 ∣ Nat.card (stab β) := by
  obtain ⟨φ⟩ := quot_stab_three hA hv
  have h6 : (Qv β).relIndex (stab β) = 6 := by
    rw [relIndex_Qv_stab, Nat.card_congr φ.toEquiv, Nat.card_perm]
    simp [Nat.factorial]
  have h := Subgroup.index_dvd_card ((Qv β).subgroupOf (stab β))
  have h6' : ((Qv β).subgroupOf (stab β)).index = 6 := h6
  rw [h6'] at h
  exact (show 3 ∣ 6 by norm_num).trans h

end Tri

end F53.Stellmacher.S42B1

end CFSG.Quasithin
