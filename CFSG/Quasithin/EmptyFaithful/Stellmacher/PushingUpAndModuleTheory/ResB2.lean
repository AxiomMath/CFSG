module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA16

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

section Nbrs

variable {μ : Geo H M}

omit [Finite G] in
theorem smul_mem_nbrs {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab μ) {x : Geo H M} (hx : x ∈ nbrs μ) :
    g • x ∈ nbrs μ := by
  have := (smul_adj g).mpr (show (graph (H ⊔ M) H M).Adj μ x from hx)
  rwa [smul_eq_of_mem_stab (g := g) hg] at this

omit [Finite G] in
theorem smul_ne_smul {g : ↥(H ⊔ M)} {x y : Geo H M} (h : x ≠ y) : g • x ≠ g • y :=
  fun hxy => h (smul_left_cancel g hxy)

theorem nbrs_three (hA : F53Amalgam H M S) (hv : vtype μ = true) {δ : Geo H M}
    (hδ : δ ∈ nbrs μ) :
    ∃ n n' : Geo H M, n ∈ nbrs μ ∧ n' ∈ nbrs μ ∧ n ≠ δ ∧ n' ≠ δ ∧ n ≠ n' ∧
      ∀ x ∈ nbrs μ, x = δ ∨ x = n ∨ x = n' := by
  have h3 := card_nbrs_true hA hv
  rw [Nat.card_coe_set_eq] at h3
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Set.ncard_eq_three.mp h3
  have hδ' : δ ∈ ({x, y, z} : Set (Geo H M)) := hs ▸ hδ
  have hall : ∀ w ∈ nbrs μ, w = x ∨ w = y ∨ w = z := fun w hw => by
    have : w ∈ ({x, y, z} : Set (Geo H M)) := hs ▸ hw
    simpa using this
  have hx : x ∈ nbrs μ := by rw [hs]; simp
  have hy : y ∈ nbrs μ := by rw [hs]; simp
  have hz : z ∈ nbrs μ := by rw [hs]; simp
  rcases (by simpa using hδ' : δ = x ∨ δ = y ∨ δ = z) with rfl | rfl | rfl
  · exact ⟨y, z, hy, hz, hxy.symm, hxz.symm, hyz, hall⟩
  · refine ⟨x, z, hx, hz, hxy, hyz.symm, hxz, fun w hw => ?_⟩
    rcases hall w hw with h | h | h <;> simp [h]
  · refine ⟨x, y, hx, hy, hxz, hyz, hxy, fun w hw => ?_⟩
    rcases hall w hw with h | h | h <;> simp [h]

theorem mem_Qv_of_fix (hA : F53Amalgam H M S) {g : ↥(H ⊔ M)} (hg : (g : G) ∈ stab μ)
    (hfix : ∀ x ∈ nbrs μ, g • x = x) : (g : G) ∈ Qv μ := by
  rw [← Qv_eq_ballStab_one hA μ, mem_ballStab]
  intro d hd
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hd with h0 | h1
  · have : d = μ := (dist_eq_zero_iff (hA.amalgam.gen)).mp h0 |>.symm
    subst this
    exact hg
  · have hadj : (graph (H ⊔ M) H M).Adj μ d := dist_eq_one_iff_adj.mp h1
    exact mem_stab_of_smul_eq (hfix d hadj)

theorem nbrs_eq_of_three (hA : F53Amalgam H M S) (hv : vtype μ = true) {a b c : Geo H M}
    (ha : a ∈ nbrs μ) (hb : b ∈ nbrs μ) (hc : c ∈ nbrs μ) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : nbrs μ = {a, b, c} := by
  have h3 := card_nbrs_true hA hv
  rw [Nat.card_coe_set_eq] at h3
  have hs : ({a, b, c} : Set (Geo H M)).ncard = 3 := Set.ncard_eq_three.mpr ⟨a, b, c, hab, hac, hbc, rfl⟩
  have hsub : ({a, b, c} : Set (Geo H M)) ⊆ nbrs μ := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    exacts [ha, hb, hc]
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm

theorem cube_mem_Qv (hA : F53Amalgam H M S) (hv : vtype μ = true) {g : ↥(H ⊔ M)}
    (hg : (g : G) ∈ stab μ) {a : Geo H M} (ha : a ∈ nbrs μ) (h1 : g • a ≠ a)
    (h2 : g • g • a ≠ a) : ((g ^ 3 : ↥(H ⊔ M)) : G) ∈ Qv μ := by
  have hb : g • a ∈ nbrs μ := smul_mem_nbrs hg ha
  have hc : g • g • a ∈ nbrs μ := smul_mem_nbrs hg hb
  have hbc : g • a ≠ g • g • a := smul_ne_smul (g := g) h1.symm
  have hset := nbrs_eq_of_three hA hv ha hb hc h1.symm h2.symm hbc
  have hd : g • g • g • a ∈ nbrs μ := smul_mem_nbrs hg hc
  have hda : g • g • g • a = a := by
    have hd' : g • g • g • a ∈ ({a, g • a, g • g • a} : Set (Geo H M)) := hset ▸ hd
    rcases hd' with h | h | h
    · exact h
    · exact absurd (smul_left_cancel g h) h2
    · exact absurd (smul_left_cancel g h) (fun e => hbc e.symm)
  apply mem_Qv_of_fix hA (by simpa using (stab μ).pow_mem hg 3)
  intro x hx
  have hx' : x ∈ ({a, g • a, g • g • a} : Set (Geo H M)) := hset ▸ hx
  have e3 : ∀ y : Geo H M, (g ^ 3) • y = g • g • g • y := fun y => by
    simp [pow_succ, mul_smul]
  rw [e3]
  rcases hx' with rfl | rfl | rfl
  · exact hda
  · rw [hda]
  · rw [hda]

end Nbrs

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem exists_swap_here (hA : F53Amalgam H M S) (h : ConfR δ μ U) {n n' : Geo H M}
    (hn : n ∈ nbrs μ) (hn' : n' ∈ nbrs μ) (hnδ : n ≠ δ) (hn'δ : n' ≠ δ) (hnn' : n ≠ n')
    (hall : ∀ x ∈ nbrs μ, x = δ ∨ x = n ∨ x = n') :
    ∃ s : ↥(H ⊔ M), (s : G) ∈ stab δ ∧ (s : G) ∈ stab μ ∧ s • n = n' := by
  obtain ⟨s0, hs0, hs0P⟩ := h.exists_edge_not_Qv hA
  set s : ↥(H ⊔ M) := toGeoElt μ hs0.2 with hs
  have hsδ : s • δ = δ := smul_eq_of_mem_stab (g := s) hs0.1
  have hsμ : (s : G) ∈ stab μ := hs0.2
  have hδμ : δ ∈ nbrs μ := h.sig.adj.symm
  have hne : ∀ x, x ≠ δ → s • x ≠ δ := fun x hx e => hx (smul_left_cancel s (e.trans hsδ.symm))
  have hn1 : s • n = n ∨ s • n = n' := by
    rcases hall _ (smul_mem_nbrs hsμ hn) with e | e | e
    · exact absurd e (hne n hnδ)
    · exact Or.inl e
    · exact Or.inr e
  rcases hn1 with e | e
  · exfalso
    have e' : s • n' = n' := by
      rcases hall _ (smul_mem_nbrs hsμ hn') with e2 | e2 | e2
      · exact absurd e2 (hne n' hn'δ)
      · exact absurd (smul_left_cancel s (e2.trans e.symm)) (Ne.symm hnn')
      · exact e2
    exact hs0P (mem_Qv_of_fix hA hsμ fun x hx => by
      rcases hall x hx with rfl | rfl | rfl
      exacts [hsδ, e, e'])
  · exact ⟨s, hs0.1, hsμ, e⟩

theorem exists_swap (hA : F53Amalgam H M S) (h : ConfR δ μ U) {v n n' : Geo H M}
    (hv : v ∈ nbrs μ) (hn : n ∈ nbrs μ) (hn' : n' ∈ nbrs μ) (hnv : n ≠ v) (hn'v : n' ≠ v)
    (hnn' : n ≠ n') (hall : ∀ x ∈ nbrs μ, x = v ∨ x = n ∨ x = n') :
    ∃ s : ↥(H ⊔ M), (s : G) ∈ stab v ∧ (s : G) ∈ stab μ ∧ s • n = n' := by
  obtain ⟨g, hg, hgv⟩ := stab_transitive_on_nbrs (h.sig.adj.symm : δ ∈ nbrs μ) hv
  have h' := h.smul_stab (g := (g : G)) hg
  have e : toGeoElt μ hg = g := rfl
  rw [e, hgv] at h'
  exact h'.exists_swap_here hA hn hn' hnv hn'v hnn' hall

theorem two_transitive (hA : F53Amalgam H M S) (h : ConfR δ μ U) {a b a' b' : Geo H M}
    (ha : a ∈ nbrs μ) (hb : b ∈ nbrs μ) (ha' : a' ∈ nbrs μ) (hb' : b' ∈ nbrs μ)
    (hab : a ≠ b) (hab' : a' ≠ b') :
    ∃ g : ↥(H ⊔ M), (g : G) ∈ stab μ ∧ g • a = a' ∧ g • b = b' := by
  have hv := h.vtype_mu hA
  obtain ⟨g1, hg1, hg1a⟩ := stab_transitive_on_nbrs ha ha'
  have hgb : g1 • b ∈ nbrs μ := smul_mem_nbrs hg1 hb
  have hne : g1 • b ≠ a' := fun e => hab (smul_left_cancel g1 (e.trans hg1a.symm)).symm
  by_cases hbb : g1 • b = b'
  · exact ⟨g1, hg1, hg1a, hbb⟩
  · have hset := nbrs_eq_of_three hA hv ha' hb' hgb hab' (Ne.symm hne)
      (Ne.symm hbb)
    obtain ⟨s, hsa', hsμ, hs⟩ := h.exists_swap hA ha' hgb hb' hne (Ne.symm hab') hbb
      (fun x hx => by
        have : x ∈ ({a', b', g1 • b} : Set (Geo H M)) := hset ▸ hx
        rcases this with e | e | e
        · exact Or.inl e
        · exact Or.inr (Or.inr e)
        · exact Or.inr (Or.inl e))
    refine ⟨s * g1, (stab μ).mul_mem hsμ hg1, ?_, ?_⟩
    · rw [mul_smul, hg1a]; exact smul_eq_of_mem_stab (g := s) hsa'
    · rw [mul_smul]; exact hs

end ConfR

end CFSG.Quasithin.F53
