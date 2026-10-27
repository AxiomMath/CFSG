module

public import CFSG.Quasithin.Recognition.St84.Sec7Setup
public import CFSG.Quasithin.Recognition.St84.WeissB
public import CFSG.Quasithin.Recognition.St84.Sec7Nat
public import CFSG.Quasithin.Recognition.SzR1MNUNorm
public import CFSG.GroupTheory.ElemAbelianClosure

import CFSG.Quasithin.Recognition.St84.Gen.Sec6LeafGen

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.Quasithin.F6.GoldAmL3T
  CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise

section Even

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

theorem not_trans_of_even (hs : IsSingularity Γ G s) (hev : Even s) (m : ℤ) :
    ¬ X.LeftTransAt m (m + (s : ℤ)) ∧ ¬ X.RightTransAt m (m + (s : ℤ)) := by
  have hnt := even_nontransitive X.hyp hs hev s le_rfl (X.line.arc m s)
  constructor
  · intro hL
    exact hnt.1 ((X.leftTransitive_arc_iff m s).mpr hL)
  · intro hR
    exact hnt.2 ((X.rightTransitive_arc_iff m hs.1).mpr hR)

theorem arcStab_eq_extend (hs : IsSingularity Γ G s) (hev : Even s) (m : ℤ) :
    X.arcStab m (m + (s : ℤ)) = X.arcStab (m - 1) (m + (s : ℤ) + 1) := by
  classical
  have hms : m < m + (s : ℤ) := by
    have := hs.1
    omega
  refine le_antisymm ?_ (X.arcStab_anti (by omega) (by omega))
  have hKA : X.K ≤ X.arcStab m (m + (s : ℤ)) :=
    X.K_le_GT.trans (X.GT_le_arcStab m (m + (s : ℤ)))
  have hAGi : X.arcStab m (m + (s : ℤ)) ≤ X.Gi m ⊓ X.Gi (m + 1) :=
    le_inf (X.arcStab_le_Gi_left hms) (X.arcStab_le_Gi_left_succ hms)
  obtain ⟨-, hKsup⟩ := X.pCoreOf_eq_inf_edgeSylow m hKA hAGi
  rw [← hKsup]
  refine sup_le ?_ ?_
  · exact X.K_le_GT.trans (X.GT_le_arcStab (m - 1) (m + (s : ℤ) + 1))
  · intro p hp
    have hpA : p ∈ X.arcStab m (m + (s : ℤ)) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hp
    have hleft := X.pCoreOf_arcStab_fixes_left m (m + (s : ℤ)) hms
      (X.not_trans_of_even hs hev m).1
    have hright := X.pCoreOf_arcStab_fixes_right m (m + (s : ℤ)) hms
      (X.not_trans_of_even hs hev m).2
    have hleft_adj : Γ.Adj (X.vert m) (X.vert (m - 1)) := by
      have h := (X.adj (m - 1)).symm
      rwa [show m - 1 + 1 = m by ring] at h
    unfold Setup.arcStab
    rw [Fan86.mem_fixSet]
    rintro _ ⟨i, hi, rfl⟩
    rw [Set.mem_Icc] at hi
    by_cases h1 : i = m - 1
    · rw [h1]
      exact hleft (X.vert (m - 1)) hleft_adj p hp
    · by_cases h2 : i = m + (s : ℤ) + 1
      · rw [h2]
        exact hright (X.vert (m + (s : ℤ) + 1)) (X.adj (m + (s : ℤ))) p hp
      · exact MulAction.mem_stabilizer_iff.mp
          (X.arcStab_le_Gi_of_between (by omega) (by omega) hpA)

theorem arcStab_eq_GT (hs : IsSingularity Γ G s) (hev : Even s) (m : ℤ) :
    X.arcStab m (m + (s : ℤ)) = X.GT := by
  classical
  refine le_antisymm ?_ (X.GT_le_arcStab m (m + (s : ℤ)))
  have hL : ∀ j : ℕ, X.arcStab m (m + (s : ℤ)) ≤
      X.arcStab (m - (j : ℤ)) (m - (j : ℤ) + (s : ℤ)) := by
    intro j
    induction j with
    | zero => simpa using le_refl (X.arcStab m (m + (s : ℤ)))
    | succ j ih =>
      have heq := X.arcStab_eq_extend hs hev (m - (j : ℤ))
      refine ih.trans ?_
      rw [heq]
      exact X.arcStab_anti (by push_cast; omega) (by push_cast; omega)
  have hR : ∀ j : ℕ, X.arcStab m (m + (s : ℤ)) ≤
      X.arcStab (m + (j : ℤ)) (m + (j : ℤ) + (s : ℤ)) := by
    intro j
    induction j with
    | zero => simpa using le_refl (X.arcStab m (m + (s : ℤ)))
    | succ j ih =>
      have heq := X.arcStab_eq_extend hs hev (m + (j : ℤ))
      refine ih.trans ?_
      rw [heq]
      exact X.arcStab_anti (by push_cast; omega) (by push_cast; omega)
  intro g hg
  unfold Setup.GT
  rw [Fan86.mem_fixSet]
  rintro _ ⟨i, rfl⟩
  by_cases hi : i ≤ m
  · have hj : (((m - i).toNat : ℕ) : ℤ) = m - i := Int.toNat_of_nonneg (by omega)
    have hmem := hL ((m - i).toNat) hg
    exact MulAction.mem_stabilizer_iff.mp
      (X.arcStab_le_Gi_of_between (by omega) (by omega) hmem)
  · by_cases hi2 : i ≤ m + (s : ℤ)
    · exact MulAction.mem_stabilizer_iff.mp
        (X.arcStab_le_Gi_of_between (by omega) hi2 hg)
    · have hj : (((i - (m + (s : ℤ))).toNat : ℕ) : ℤ) = i - (m + (s : ℤ)) :=
        Int.toNat_of_nonneg (by omega)
      have hmem := hR ((i - (m + (s : ℤ))).toNat) hg
      exact MulAction.mem_stabilizer_iff.mp
        (X.arcStab_le_Gi_of_between (by omega) (by omega) hmem)

theorem pCoreOf_GT_fixes (hs : IsSingularity Γ G s) (hev : Even s) (i : ℤ) {a : V}
    (ha : Γ.Adj (X.vert i) a) : ∀ g ∈ pCoreOf 2 X.GT, g • a = a := by
  have hms : i < i + (s : ℤ) := by
    have := hs.1
    omega
  have hGT : X.arcStab i (i + (s : ℤ)) = X.GT := X.arcStab_eq_GT hs hev i
  intro g hg
  have hg' : g ∈ pCoreOf 2 (X.arcStab i (i + (s : ℤ))) := by rwa [hGT]
  exact X.pCoreOf_arcStab_fixes_left i (i + (s : ℤ)) hms
    (X.not_trans_of_even hs hev i).1 a ha g hg'

theorem arcStab_le_normalizer_pCoreOf_GT_right (hs : IsSingularity Γ G s) (hev : Even s)
    (m : ℤ) :
    X.arcStab m (m + (s : ℤ) - 1) ≤ Subgroup.normalizer (pCoreOf 2 X.GT : Set G) := by
  classical
  have hs2 : 2 ≤ s := by
    have h1 : 1 ≤ s := hs.1
    obtain ⟨t, ht⟩ := hev
    omega
  have hms : m < m + (s : ℤ) - 1 := by omega
  have hB : X.K ≤ X.arcStab m (m + (s : ℤ) - 1) :=
    X.K_le_GT.trans (X.GT_le_arcStab m (m + (s : ℤ) - 1))
  have hBGi : X.arcStab m (m + (s : ℤ) - 1) ≤ X.Gi m ⊓ X.Gi (m + 1) :=
    le_inf (X.arcStab_le_Gi_left hms) (X.arcStab_le_Gi_left_succ hms)
  obtain ⟨hPB, hBeq⟩ := X.pCoreOf_eq_inf_edgeSylow m hB hBGi
  obtain ⟨hPGT, -⟩ := X.pCoreOf_eq_inf_edgeSylow m X.K_le_GT
    (le_inf (X.GT_le_Gi m) (X.GT_le_Gi (m + 1)))
  rw [← hBeq]
  refine sup_le ?_ ?_
  · exact X.K_le_GT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X.GT)
  · intro p hp
    have hconj : ∀ g ∈ pCoreOf 2 (X.arcStab m (m + (s : ℤ) - 1)),
        ∀ y ∈ pCoreOf 2 X.GT, g * y * g⁻¹ ∈ pCoreOf 2 X.GT := by
      intro g hg y hy
      have hgB : g ∈ X.arcStab m (m + (s : ℤ) - 1) :=
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hg
      have hg1B : g⁻¹ ∈ X.arcStab m (m + (s : ℤ) - 1) := Subgroup.inv_mem _ hgB
      have hgS : g ∈ X.edgeSylow m := (Subgroup.mem_inf.mp (hPB ▸ hg)).2
      have hyGT : y ∈ X.GT := (CFSG.LieType.BorelTits.pCoreOf_le 2 X.GT) hy
      have hyS : y ∈ X.edgeSylow m := (Subgroup.mem_inf.mp (hPGT ▸ hy)).2
      have hg1fix : g⁻¹ • X.vert (m + (s : ℤ) - 1) = X.vert (m + (s : ℤ) - 1) :=
        MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_right hms hg1B)
      have hadj : Γ.Adj (X.vert (m + (s : ℤ) - 1)) (g⁻¹ • X.vert (m + (s : ℤ))) := by
        have h := (X.hyp.adj_smul g⁻¹ (X.vert (m + (s : ℤ) - 1))
          (X.vert (m + (s : ℤ)))).2 (by
            have h' := X.adj (m + (s : ℤ) - 1)
            rwa [show m + (s : ℤ) - 1 + 1 = m + (s : ℤ) by ring] at h')
        rwa [hg1fix] at h
      have hyfix : y • (g⁻¹ • X.vert (m + (s : ℤ))) = g⁻¹ • X.vert (m + (s : ℤ)) :=
        X.pCoreOf_GT_fixes hs hev (m + (s : ℤ) - 1) hadj y hy
      have hfixmem : g * y * g⁻¹ ∈ X.arcStab m (m + (s : ℤ)) := by
        unfold Setup.arcStab
        rw [Fan86.mem_fixSet]
        rintro _ ⟨i, hi, rfl⟩
        rw [Set.mem_Icc] at hi
        by_cases hmid : i ≤ m + (s : ℤ) - 1
        · have h1 : g • X.vert i = X.vert i :=
            MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_of_between hi.1 hmid hgB)
          have h2 : y • X.vert i = X.vert i :=
            MulAction.mem_stabilizer_iff.mp (X.GT_le_Gi i hyGT)
          have h3 : g⁻¹ • X.vert i = X.vert i :=
            MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_of_between hi.1 hmid hg1B)
          calc (g * y * g⁻¹) • X.vert i = g • (y • (g⁻¹ • X.vert i)) := by simp [mul_smul]
            _ = g • (y • X.vert i) := by rw [h3]
            _ = g • X.vert i := by rw [h2]
            _ = X.vert i := h1
        · have hieq : i = m + (s : ℤ) := by omega
          rw [hieq]
          calc (g * y * g⁻¹) • X.vert (m + (s : ℤ))
              = g • (y • (g⁻¹ • X.vert (m + (s : ℤ)))) := by simp [mul_smul]
            _ = g • (g⁻¹ • X.vert (m + (s : ℤ))) := by rw [hyfix]
            _ = X.vert (m + (s : ℤ)) := by simp
      have hGTmem : g * y * g⁻¹ ∈ X.GT := by
        have h := X.arcStab_eq_GT hs hev m
        rwa [h] at hfixmem
      have hSylowmem : g * y * g⁻¹ ∈ X.edgeSylow m :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgS hyS) (Subgroup.inv_mem _ hgS)
      rw [hPGT]
      exact Subgroup.mem_inf.mpr ⟨hGTmem, hSylowmem⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj p hp x hx
    · intro hx
      have h := hconj p⁻¹ (Subgroup.inv_mem _ hp) (p * x * p⁻¹) hx
      have heq : p⁻¹ * (p * x * p⁻¹) * (p⁻¹)⁻¹ = x := by group
      rwa [heq] at h

theorem arcStab_le_normalizer_pCoreOf_GT_left (hs : IsSingularity Γ G s) (hev : Even s)
    (m : ℤ) :
    X.arcStab (m - (s : ℤ) + 1) m ≤ Subgroup.normalizer (pCoreOf 2 X.GT : Set G) := by
  classical
  have hs2 : 2 ≤ s := by
    have h1 : 1 ≤ s := hs.1
    obtain ⟨t, ht⟩ := hev
    omega
  have hms : m - (s : ℤ) + 1 < m := by omega
  have hB : X.K ≤ X.arcStab (m - (s : ℤ) + 1) m :=
    X.K_le_GT.trans (X.GT_le_arcStab (m - (s : ℤ) + 1) m)
  have hBGi : X.arcStab (m - (s : ℤ) + 1) m ≤ X.Gi (m - 1) ⊓ X.Gi m :=
    le_inf (X.arcStab_le_Gi_of_between (by omega) (by omega))
      (X.arcStab_le_Gi_right hms)
  obtain ⟨hPB, hBeq⟩ := X.pCoreOf_eq_inf_edgeSylow (m - 1) hB
    (by simpa [show m - 1 + 1 = m by ring] using hBGi)
  obtain ⟨hPGT, -⟩ := X.pCoreOf_eq_inf_edgeSylow (m - 1) X.K_le_GT
    (le_inf (X.GT_le_Gi (m - 1)) (by simpa [show m - 1 + 1 = m by ring] using X.GT_le_Gi m))
  rw [← hBeq]
  refine sup_le ?_ ?_
  · exact X.K_le_GT.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X.GT)
  · intro p hp
    have hconj : ∀ g ∈ pCoreOf 2 (X.arcStab (m - (s : ℤ) + 1) m),
        ∀ y ∈ pCoreOf 2 X.GT, g * y * g⁻¹ ∈ pCoreOf 2 X.GT := by
      intro g hg y hy
      have hgB : g ∈ X.arcStab (m - (s : ℤ) + 1) m :=
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hg
      have hg1B : g⁻¹ ∈ X.arcStab (m - (s : ℤ) + 1) m := Subgroup.inv_mem _ hgB
      have hgS : g ∈ X.edgeSylow (m - 1) := (Subgroup.mem_inf.mp (hPB ▸ hg)).2
      have hyGT : y ∈ X.GT := (CFSG.LieType.BorelTits.pCoreOf_le 2 X.GT) hy
      have hyS : y ∈ X.edgeSylow (m - 1) := (Subgroup.mem_inf.mp (hPGT ▸ hy)).2
      have hg1fix : g⁻¹ • X.vert m = X.vert m :=
        MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_right hms hg1B)
      have hadj : Γ.Adj (X.vert m) (g⁻¹ • X.vert (m + 1)) := by
        have h := (X.hyp.adj_smul g⁻¹ (X.vert m) (X.vert (m + 1))).2
          (by simpa using X.adj m)
        rwa [hg1fix] at h
      have hyfix : y • (g⁻¹ • X.vert (m + 1)) = g⁻¹ • X.vert (m + 1) :=
        X.pCoreOf_GT_fixes hs hev m hadj y hy
      have hfixmem : g * y * g⁻¹ ∈ X.arcStab (m - (s : ℤ) + 1) (m + 1) := by
        unfold Setup.arcStab
        rw [Fan86.mem_fixSet]
        rintro _ ⟨i, hi, rfl⟩
        rw [Set.mem_Icc] at hi
        by_cases hmid : i ≤ m
        · have h1 : g • X.vert i = X.vert i :=
            MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_of_between hi.1 hmid hgB)
          have h2 : y • X.vert i = X.vert i :=
            MulAction.mem_stabilizer_iff.mp (X.GT_le_Gi i hyGT)
          have h3 : g⁻¹ • X.vert i = X.vert i :=
            MulAction.mem_stabilizer_iff.mp (X.arcStab_le_Gi_of_between hi.1 hmid hg1B)
          calc (g * y * g⁻¹) • X.vert i = g • (y • (g⁻¹ • X.vert i)) := by simp [mul_smul]
            _ = g • (y • X.vert i) := by rw [h3]
            _ = g • X.vert i := by rw [h2]
            _ = X.vert i := h1
        · have hieq : i = m + 1 := by omega
          rw [hieq]
          calc (g * y * g⁻¹) • X.vert (m + 1)
              = g • (y • (g⁻¹ • X.vert (m + 1))) := by simp [mul_smul]
            _ = g • (g⁻¹ • X.vert (m + 1)) := by rw [hyfix]
            _ = X.vert (m + 1) := by simp
      have hGTmem : g * y * g⁻¹ ∈ X.GT := by
        have h := X.arcStab_eq_GT hs hev (m - (s : ℤ) + 1)
        have harc : m - (s : ℤ) + 1 + (s : ℤ) = m + 1 := by ring
        rw [harc] at h
        rwa [h] at hfixmem
      have hSylowmem : g * y * g⁻¹ ∈ X.edgeSylow (m - 1) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hgS hyS) (Subgroup.inv_mem _ hgS)
      rw [hPGT]
      exact Subgroup.mem_inf.mpr ⟨hGTmem, hSylowmem⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj p hp x hx
    · intro hx
      have h := hconj p⁻¹ (Subgroup.inv_mem _ hp) (p * x * p⁻¹) hx
      have heq : p⁻¹ * (p * x * p⁻¹) * (p⁻¹)⁻¹ = x := by group
      rwa [heq] at h

end Setup

theorem trans_of_cotrans (h : Hyp30 Γ G) {v u w : V} {N : Subgroup G} (huw : u ≠ w)
    (h1 : ∀ a b, Γ.Adj v a → a ≠ u → Γ.Adj v b → b ≠ u → ∃ g ∈ N, g • a = b)
    (h2 : ∀ a b, Γ.Adj v a → a ≠ w → Γ.Adj v b → b ≠ w → ∃ g ∈ N, g • a = b) :
    ∀ a b, Γ.Adj v a → Γ.Adj v b → ∃ g ∈ N, g • a = b := by
  intro a b ha hb
  by_cases hau : a = u
  · subst a
    by_cases hbw : b = w
    · subst b
      obtain ⟨c, hc, hcu, hcw⟩ := exists_adj_ne_ne (v := v) (a := u) (b := w)
        (h.three_le_card v)
      obtain ⟨g2, hg2, hg2c⟩ := h2 u c ha huw hc hcw
      obtain ⟨g1, hg1, hg1w⟩ := h1 c w hc hcu hb huw.symm
      exact ⟨g1 * g2, N.mul_mem hg1 hg2, by rw [mul_smul, hg2c, hg1w]⟩
    · exact h2 u b ha huw hb hbw
  · by_cases haw : a = w
    · subst a
      by_cases hbu : b = u
      · subst b
        obtain ⟨c, hc, hcw, hcu⟩ := exists_adj_ne_ne (v := v) (a := w) (b := u)
          (h.three_le_card v)
        obtain ⟨g1, hg1, hg1c⟩ := h1 w c ha huw.symm hc hcu
        obtain ⟨g2, hg2, hg2u⟩ := h2 c u hc hcw hb huw
        exact ⟨g2 * g1, N.mul_mem hg2 hg1, by rw [mul_smul, hg1c, hg2u]⟩
      · exact h1 w b ha huw.symm hb hbu
    · by_cases hbu : b = u
      · subst b
        exact h2 a u ha haw hb huw
      · exact h1 a b ha hau hb hbu

namespace Setup

variable (X : Setup Γ G)

theorem pCoreOf_GT_eq_bot (hs : IsSingularity Γ G s) (hev : Even s) :
    pCoreOf 2 X.GT = ⊥ := by
  classical
  have hs2 : 2 ≤ s := by
    have h1 : 1 ≤ s := hs.1
    obtain ⟨t, ht⟩ := hev
    omega
  have hcast : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := Nat.cast_sub (by omega : 1 ≤ s)
  have hX : pCoreOf 2 X.GT ≤
      MulAction.stabilizer G (X.vert 0) ⊓ MulAction.stabilizer G (X.vert 1) :=
    le_inf ((CFSG.LieType.BorelTits.pCoreOf_le 2 X.GT).trans (X.GT_le_Gi 0))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X.GT).trans (X.GT_le_Gi 1))
  refine eq_bot_of_normalizer_trans X.hyp (X.adj 0) hX ?_ ?_
  ·
    have hreg1 : X.LeftTransAt 0 ((0 : ℤ) + (s : ℤ) - 1) := by
      have h := (X.trans_of_lt hs 0 (k := s - 1) (by omega) (by omega)).1
      rwa [show (0 : ℤ) + ((s - 1 : ℕ) : ℤ) = (0 : ℤ) + (s : ℤ) - 1 by
        rw [hcast]; ring] at h
    have hreg2 : X.RightTransAt (1 - (s : ℤ)) 0 := by
      have h := (X.trans_of_lt hs (1 - (s : ℤ)) (k := s - 1) (by omega) (by omega)).2
      rwa [show (1 : ℤ) - (s : ℤ) + ((s - 1 : ℕ) : ℤ) = 0 by rw [hcast]; ring] at h
    have huw : X.vert 1 ≠ X.vert (-1) := by
      intro h
      have := X.vert_injective h
      omega
    have htrans := trans_of_cotrans X.hyp
      (N := Subgroup.normalizer (pCoreOf 2 X.GT : Set G) ⊓
        MulAction.stabilizer G (X.vert 0))
      (u := X.vert 1) (w := X.vert (-1)) huw
      (by
        intro a b ha ha1 hb hb1
        obtain ⟨g, hg, hgab⟩ := hreg1 a b ha ha1 hb hb1
        refine ⟨g, Subgroup.mem_inf.mpr ⟨?_, X.arcStab_le_Gi_of_between (by omega) (by omega) hg⟩, hgab⟩
        exact X.arcStab_le_normalizer_pCoreOf_GT_right hs hev 0 hg)
      (by
        intro a b ha ha1 hb hb1
        obtain ⟨g, hg, hgab⟩ := hreg2 a b ha ha1 hb hb1
        refine ⟨g, Subgroup.mem_inf.mpr ⟨?_, X.arcStab_le_Gi_of_between (by omega) le_rfl hg⟩, hgab⟩
        have hg' : g ∈ X.arcStab ((0 : ℤ) - (s : ℤ) + 1) 0 := by
          rwa [show (0 : ℤ) - (s : ℤ) + 1 = (1 : ℤ) - (s : ℤ) by ring]
        exact X.arcStab_le_normalizer_pCoreOf_GT_left hs hev 0 hg')
    exact htrans
  ·
    have hreg1 : X.LeftTransAt 1 (s : ℤ) := by
      have h := (X.trans_of_lt hs 1 (k := s - 1) (by omega) (by omega)).1
      rwa [show (1 : ℤ) + ((s - 1 : ℕ) : ℤ) = (s : ℤ) by rw [hcast]; ring] at h
    have hreg2 : X.RightTransAt (2 - (s : ℤ)) 1 := by
      have h := (X.trans_of_lt hs (2 - (s : ℤ)) (k := s - 1) (by omega) (by omega)).2
      rwa [show (2 : ℤ) - (s : ℤ) + ((s - 1 : ℕ) : ℤ) = 1 by rw [hcast]; ring] at h
    have huw : X.vert 0 ≠ X.vert 2 := by
      intro h
      have := X.vert_injective h
      omega
    have htrans := trans_of_cotrans X.hyp
      (N := Subgroup.normalizer (pCoreOf 2 X.GT : Set G) ⊓
        MulAction.stabilizer G (X.vert 1))
      (u := X.vert 0) (w := X.vert 2) huw
      (by
        intro a b ha ha1 hb hb1
        obtain ⟨g, hg, hgab⟩ := hreg2 a b ha ha1 hb hb1
        refine ⟨g, Subgroup.mem_inf.mpr ⟨?_, X.arcStab_le_Gi_of_between (by omega) (by omega) hg⟩, hgab⟩
        have hg' : g ∈ X.arcStab ((1 : ℤ) - (s : ℤ) + 1) 1 := by
          rwa [show (1 : ℤ) - (s : ℤ) + 1 = (2 : ℤ) - (s : ℤ) by ring]
        exact X.arcStab_le_normalizer_pCoreOf_GT_left hs hev 1 hg')
      (by
        intro a b ha ha1 hb hb1
        obtain ⟨g, hg, hgab⟩ := hreg1 a b ha ha1 hb hb1
        refine ⟨g, Subgroup.mem_inf.mpr ⟨?_, X.arcStab_le_Gi_of_between (by omega) (by omega) hg⟩, hgab⟩
        have hg' : g ∈ X.arcStab 1 ((1 : ℤ) + (s : ℤ) - 1) := by
          rwa [show (1 : ℤ) + (s : ℤ) - 1 = (s : ℤ) by ring]
        exact X.arcStab_le_normalizer_pCoreOf_GT_right hs hev 1 hg')
    exact htrans

theorem GT_eq_K (hs : IsSingularity Γ G s) (hev : Even s) : X.GT = X.K := by
  obtain ⟨-, hKsup⟩ := X.pCoreOf_eq_inf_edgeSylow 0 X.K_le_GT
    (le_inf (X.GT_le_Gi 0) (X.GT_le_Gi 1))
  rw [X.pCoreOf_GT_eq_bot hs hev] at hKsup
  simpa using hKsup.symm

theorem arcStab_eq_K (hs : IsSingularity Γ G s) (hev : Even s) (m : ℤ) :
    X.arcStab m (m + (s : ℤ)) = X.K :=
  (X.arcStab_eq_GT hs hev m).trans (X.GT_eq_K hs hev)

theorem n_zero_eq_n_one_of_even (hs : IsSingularity Γ G s) (hev : Even s) :
    X.n 0 = X.n 1 := by
  classical
  have hs2 : 2 ≤ s := by
    have h1 : 1 ≤ s := hs.1
    obtain ⟨t, ht⟩ := hev
    omega
  have hcast : ((s - 1 : ℕ) : ℤ) = (s : ℤ) - 1 := Nat.cast_sub (by omega : 1 ≤ s)
  have h0lt : (0 : ℤ) < ((s - 1 : ℕ) : ℤ) := by rw [hcast]; omega
  have htrans := X.trans_of_lt hs 0 (k := s - 1) (by omega) (by omega)
  have hR : X.RightTransAt 0 ((s - 1 : ℕ) : ℤ) := by simpa using htrans.2
  have hL : X.LeftTransAt 0 ((s - 1 : ℕ) : ℤ) := by simpa using htrans.1
  have hsucc := X.relIndex_arcStab_succ 0 ((s - 1 : ℕ) : ℤ) h0lt hR
  have hpred := X.relIndex_arcStab_pred 0 ((s - 1 : ℕ) : ℤ) h0lt hL
  rw [show (0 : ℤ) - 1 = -1 by norm_num] at hpred
  have hA0 : X.arcStab 0 (0 + (s : ℤ)) = X.GT := X.arcStab_eq_GT hs hev 0
  have hAm1 : X.arcStab (-1) ((-1) + (s : ℤ)) = X.GT := X.arcStab_eq_GT hs hev (-1)
  have hsucc' : X.GT.relIndex (X.arcStab 0 ((s - 1 : ℕ) : ℤ)) =
      2 ^ X.n ((s - 1 : ℕ) : ℤ) := by
    rw [← hA0]
    rw [show (0 : ℤ) + (s : ℤ) = ((s - 1 : ℕ) : ℤ) + 1 by rw [hcast]; ring]
    exact hsucc
  have hpred' : X.GT.relIndex (X.arcStab 0 ((s - 1 : ℕ) : ℤ)) = 2 ^ X.n 0 := by
    rw [← hAm1]
    rw [show (-1 : ℤ) + (s : ℤ) = ((s - 1 : ℕ) : ℤ) by rw [hcast]; ring]
    exact hpred
  have hpow : 2 ^ X.n ((s - 1 : ℕ) : ℤ) = 2 ^ X.n 0 := by
    rw [← hsucc', hpred']
  have hnmid : X.n ((s - 1 : ℕ) : ℤ) = X.n 0 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  have hnodd : X.n ((s - 1 : ℕ) : ℤ) = X.n 1 := by
    obtain ⟨t, ht⟩ := hev
    have hform : (s : ℤ) - 1 = 1 + 2 * ((t : ℤ) - 1) := by
      rw [ht]; push_cast; ring
    rw [hcast, hform, X.n_add]
  exact hnmid.symm.trans hnodd

theorem not_even_of_n_ne (hs : IsSingularity Γ G s) (hne : X.n 0 ≠ X.n 1) :
    ¬ Even s :=
  fun hev => hne (X.n_zero_eq_n_one_of_even hs hev)

end Setup

theorem Hyp30.le_G1_of_isPGroup_fixes_two (h : Hyp30 Γ G) : ∀ (v : V) (P : Subgroup G),
    IsPGroup 2 P → P ≤ MulAction.stabilizer G v → ∀ a b : V, Γ.Adj v a → Γ.Adj v b → a ≠ b →
    (∀ g ∈ P, g • a = a) → (∀ g ∈ P, g • b = b) → P ≤ G1 (Γ := Γ) (G := G) v := by
  intro v P hP hPv a b ha hb hab hPa hPb
  have hPcore : P ≤ pCoreOf 2 (MulAction.stabilizer G v) :=
    le_pCoreOf_of_isPGroup_fixes_two h hP hPv ha hb hab hPa hPb
  intro g hg
  rw [mem_G1]
  exact ⟨hPv hg, fun y hy => Hyp30.pCoreOf_fixes_adj h hy g (hPcore hg)⟩

theorem Setup.singularity_le_four (X : Setup Γ G) (hs : IsSingularity Γ G s) (hev : Even s)
    (hn : ∀ v, nOf Γ v = 2) : s ≤ 4 :=
  singularity_le_four_of_even X.hyp hn hs hev X.toKTrack
    (by
      intro i a b ha hb ha1 ha2 hb1 hb2
      obtain ⟨k, hk, hkb⟩ := X.Ki_transitive_gen i ha hb ha1 ha2 hb1 hb2
      exact ⟨k, hk.1, hkb⟩)
    X.hyp.le_G1_of_isPGroup_fixes_two

theorem Setup.singularity_eq_four (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (hev : Even s) (hn : ∀ v, nOf Γ v = 2) : s = 4 := by
  have hle := X.singularity_le_four hs hev hn
  have h3 := three_le_of_isSingularity X.hyp hc hs
  obtain ⟨t, ht⟩ := hev
  omega

namespace Setup

variable (X : Setup Γ G)

theorem card_S_of_four (hs : IsSingularity Γ G 4) (hn0 : X.n 0 = 2) (hn1 : X.n 1 = 2) :
    Nat.card X.S = 2 ^ 6 := by
  classical
  have hev4 : Even 4 := ⟨2, by norm_num⟩
  have hK : Nat.card ↥X.K * Nat.card ↥X.S = Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) :=
    card_mul_pCoreOf_edgeStab X.hyp (X.adj 0) X.K_le_inf X.K_inf X.K_sup
  have hreg1 : X.RightTransAt 0 1 := by
    have h := (X.trans_of_lt hs 0 (k := 1) (by norm_num) (by norm_num)).2
    simpa using h
  have hreg2 : X.RightTransAt 0 2 := by
    have h := (X.trans_of_lt hs 0 (k := 2) (by norm_num) (by norm_num)).2
    simpa using h
  have hreg3 : X.RightTransAt 0 3 := by
    have h := (X.trans_of_lt hs 0 (k := 3) (by norm_num) (by norm_num)).2
    simpa using h
  have h43 : (X.arcStab 0 4).relIndex (X.arcStab 0 3) = 2 ^ X.n 3 :=
    X.relIndex_arcStab_succ 0 3 (by norm_num) hreg3
  have h32 : (X.arcStab 0 3).relIndex (X.arcStab 0 2) = 2 ^ X.n 2 :=
    X.relIndex_arcStab_succ 0 2 (by norm_num) hreg2
  have h21 : (X.arcStab 0 2).relIndex (X.arcStab 0 1) = 2 ^ X.n 1 :=
    X.relIndex_arcStab_succ 0 1 (by norm_num) hreg1
  have hle43 : X.arcStab 0 4 ≤ X.arcStab 0 3 :=
    X.arcStab_anti (by norm_num) (by norm_num)
  have hle32 : X.arcStab 0 3 ≤ X.arcStab 0 2 :=
    X.arcStab_anti (by norm_num) (by norm_num)
  have hle21 : X.arcStab 0 2 ≤ X.arcStab 0 1 :=
    X.arcStab_anti (by norm_num) (by norm_num)
  have hle41 : X.arcStab 0 4 ≤ X.arcStab 0 1 := hle43.trans (hle32.trans hle21)
  have hA42 : (X.arcStab 0 4).relIndex (X.arcStab 0 2) =
      2 ^ X.n 3 * 2 ^ X.n 2 := by
    rw [← Subgroup.relIndex_mul_relIndex (H := X.arcStab 0 4) (K := X.arcStab 0 3)
      (L := X.arcStab 0 2) hle43 hle32, h43, h32]
  have hA41 : (X.arcStab 0 4).relIndex (X.arcStab 0 1) =
      2 ^ X.n 3 * 2 ^ X.n 2 * 2 ^ X.n 1 := by
    rw [← Subgroup.relIndex_mul_relIndex (H := X.arcStab 0 4) (K := X.arcStab 0 2)
      (L := X.arcStab 0 1) (hle43.trans hle32) hle21, hA42, h21]
  have hA4K : X.arcStab 0 4 = X.K := by
    have h := X.arcStab_eq_K hs hev4 0
    simpa using h
  have hA1Gi : X.arcStab 0 1 = X.Gi 0 ⊓ X.Gi 1 := X.arcStab_eq_inf (by norm_num)
  have hcardA1 : Nat.card ↥(X.Gi 0 ⊓ X.Gi 1) =
      2 ^ X.n 3 * 2 ^ X.n 2 * 2 ^ X.n 1 * Nat.card ↥X.K := by
    rw [← hA1Gi, ← hA4K]
    have h := Subgroup.relIndex_mul_card (H := X.arcStab 0 4) (K := X.arcStab 0 1)
    rw [inf_eq_left.mpr hle41, hA41] at h
    exact h.symm
  have hn2 : X.n 2 = 2 := X.n_two.trans hn0
  have hn3 : X.n 3 = 2 := X.n_three.trans hn1
  have hcastn : 2 ^ X.n 3 * 2 ^ X.n 2 * 2 ^ X.n 1 = 2 ^ 6 := by
    rw [hn1, hn2, hn3]
    norm_num
  rw [hcastn] at hcardA1
  rw [hcardA1] at hK
  haveI : Finite ↥X.K := finite_of_le_stabilizer X.hyp (H := X.K) (X.K_le_Gi 0)
  haveI : Nonempty ↥X.K := ⟨⟨1, X.K.one_mem⟩⟩
  have hKpos : 0 < Nat.card ↥X.K := Nat.card_pos
  rw [mul_comm (2 ^ 6) (Nat.card ↥X.K)] at hK
  exact Nat.eq_of_mul_eq_mul_left hKpos hK

theorem card_Q_of_four (hs : IsSingularity Γ G 4) (hn0 : X.n 0 = 2) (hn1 : X.n 1 = 2)
    {i : ℤ} (hi : i = 0 ∨ i = 1) : Nat.card (X.Q i) = 2 ^ 4 := by
  classical
  have hS : Nat.card X.S = 2 ^ 6 := X.card_S_of_four hs hn0 hn1
  rcases hi with rfl | rfl
  · have hle : X.Q 0 ≤ X.edgeSylow 0 := X.Q_le_edgeSylow_left 0
    have hrel : (X.Q 0).relIndex (X.edgeSylow 0) = 4 := by
      rw [X.relIndex_Q_edgeSylow 0, hn0]
      norm_num
    have h := Subgroup.relIndex_mul_card (H := X.Q 0) (K := X.edgeSylow 0)
    rw [inf_eq_left.mpr hle, hrel, X.edgeSylow_zero, hS] at h
    norm_num at h
    have h16 : Nat.card (X.Q 0) = 16 := by
      have h' : 4 * Nat.card (X.Q 0) = 4 * 16 := by
        rw [show (4 : ℕ) * 16 = 64 by norm_num]
        exact h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) h'
    rw [h16]
    norm_num
  · have hle : X.Q 1 ≤ X.edgeSylow 0 := by simpa using X.Q_le_edgeSylow 0
    have hrel : (X.Q 1).relIndex (X.edgeSylow 0) = 4 := by
      have h := X.relIndex_Q_succ_edgeSylow 0
      have h2 : X.n (0 + 1) = 2 := by simpa using hn1
      rw [h2] at h
      simpa using h
    have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := X.edgeSylow 0)
    rw [inf_eq_left.mpr hle, hrel, X.edgeSylow_zero, hS] at h
    norm_num at h
    have h16 : Nat.card (X.Q 1) = 16 := by
      have h' : 4 * Nat.card (X.Q 1) = 4 * 16 := by
        rw [show (4 : ℕ) * 16 = 64 by norm_num]
        exact h
      exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) h'
    rw [h16]
    norm_num

theorem card_Q_inf_of_four (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G 4)
    (hn0 : X.n 0 = 2) (hn1 : X.n 1 = 2) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ 2 := by
  classical
  have hcard0 : Nat.card (X.Q 0) = 2 ^ 4 := X.card_Q_of_four hs hn0 hn1 (Or.inl rfl)
  have hcard1 : Nat.card (X.Q 1) = 2 ^ 4 := X.card_Q_of_four hs hn0 hn1 (Or.inr rfl)
  have hS : Nat.card X.S = 2 ^ 6 := X.card_S_of_four hs hn0 hn1
  have hQS1 : X.Q 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow 0
  have hsup : X.Q 0 ⊔ X.Q 1 = X.S := by
    simpa [X.edgeSylow_zero] using X.sup_Q_eq_edgeSylow hc 0
  have hnorm : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.Q_le_Gi_adj 0 |>.trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hleft : (X.Q 1).relIndex X.S = 4 := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := X.S)
    rw [inf_eq_left.mpr hQS1, hcard1, hS] at h
    norm_num at h
    have h' : (X.Q 1).relIndex X.S * 16 = 4 * 16 := by
      rw [show (4 : ℕ) * 16 = 64 by norm_num]
      exact h
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 16) h'
  have hsecond := CFSG.Quasithin.SzR1.MNU.Norm.relIndex_sup_eq_of_le_normalizer
    (D := X.Q 1) (T := X.Q 0) hnorm
  rw [hsup] at hsecond
  have hrel1 : (X.Q 1).relIndex (X.Q 0) = 4 := by
    rw [← hsecond, hleft]
  have hinfrel : (X.Q 1 ⊓ X.Q 0).relIndex (X.Q 0) = 4 := by
    rw [Subgroup.inf_relIndex_right, hrel1]
  have hmul := Subgroup.relIndex_mul_card (H := X.Q 1 ⊓ X.Q 0) (K := X.Q 0)
  rw [inf_eq_left.mpr (inf_le_right : X.Q 1 ⊓ X.Q 0 ≤ X.Q 0), hinfrel, hcard0] at hmul
  norm_num at hmul
  have hmain : Nat.card ↥(X.Q 1 ⊓ X.Q 0) = 4 := by
    have h' : 4 * Nat.card ↥(X.Q 1 ⊓ X.Q 0) = 4 * 4 := by
      rw [show (4 : ℕ) * 4 = 16 by norm_num]
      exact hmul
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 4) h'
  rw [show (2 : ℕ) ^ 2 = 4 by norm_num, inf_comm]
  exact hmain

theorem four_le_card_Q_inf_centralizer (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G 4) (hn0 : X.n 0 = 2) (hn1 : X.n 1 = 2) {i : ℤ}
    (hi : i = 0 ∨ i = 1) :
    4 ≤ Nat.card ↥(X.Q i ⊓ Subgroup.centralizer (X.S : Set G)) := by
  classical
  have hcard0 : Nat.card (X.Q 0) = 2 ^ 4 := X.card_Q_of_four hs hn0 hn1 (Or.inl rfl)
  have hcard1 : Nat.card (X.Q 1) = 2 ^ 4 := X.card_Q_of_four hs hn0 hn1 (Or.inr rfl)
  have helem0 : IsElemAbelian 2 (X.Q 0) := X.isElemAbelian_Q_of_card hc 0 hn0 hcard0
  have helem1 : IsElemAbelian 2 (X.Q 1) := X.isElemAbelian_Q_of_card hc 1 hn1 hcard1
  have hsup : X.Q 0 ⊔ X.Q 1 = X.S := by
    simpa [X.edgeSylow_zero] using X.sup_Q_eq_edgeSylow hc 0
  have hcent0 : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.centralizer (X.Q 0 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact IsElemAbelian.comm helem0 hx hy.1
  have hcent1 : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.centralizer (X.Q 1 : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact IsElemAbelian.comm helem1 hx hy.2
  have hsupcent : X.Q 0 ⊔ X.Q 1 ≤ Subgroup.centralizer (X.Q 0 ⊓ X.Q 1 : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mpr hcent0) (Subgroup.le_centralizer_iff.mpr hcent1)
  have hcent : X.Q 0 ⊓ X.Q 1 ≤ Subgroup.centralizer (X.S : Set G) := by
    rw [← hsup]
    exact Subgroup.le_centralizer_iff.mpr hsupcent
  have hcard : Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ 2 := X.card_Q_inf_of_four hc hs hn0 hn1
  have h4 : Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 4 := by rw [hcard]; norm_num
  rcases hi with rfl | rfl
  · haveI : Finite ↥(X.Q 0 ⊓ Subgroup.centralizer (X.S : Set G)) :=
      finite_of_le_stabilizer X.hyp (H := X.Q 0 ⊓ Subgroup.centralizer (X.S : Set G))
        (inf_le_left.trans (X.Q_le_Gi 0))
    have hle : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0 ⊓ Subgroup.centralizer (X.S : Set G) :=
      le_inf inf_le_left hcent
    have h := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    rw [h4] at h
    exact h
  · haveI : Finite ↥(X.Q 1 ⊓ Subgroup.centralizer (X.S : Set G)) :=
      finite_of_le_stabilizer X.hyp (H := X.Q 1 ⊓ Subgroup.centralizer (X.S : Set G))
        (inf_le_left.trans (X.Q_le_Gi 1))
    have hle : X.Q 1 ⊓ X.Q 0 ≤ X.Q 1 ⊓ Subgroup.centralizer (X.S : Set G) :=
      le_inf inf_le_left (by simpa [inf_comm] using hcent)
    have hcard' : Nat.card ↥(X.Q 1 ⊓ X.Q 0) = 4 := by
      rw [inf_comm, h4]
    have h := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    rw [hcard'] at h
    exact h

end Setup

end Even

section TypeZero

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

structure TreeL34Data (X : Setup Γ G) : Prop where
  card_S : Nat.card X.S = 2 ^ 6
  elem_left : IsElemAbelian 2 (pCoreOf 2 (X.L 0))
  card_left : Nat.card (pCoreOf 2 (X.L 0)) = 2 ^ 4
  nat_left : NatSec (X.L 0) ⊥ (pCoreOf 2 (X.L 0))
  elem_right : IsElemAbelian 2 (pCoreOf 2 (X.L 1))
  card_right : Nat.card (pCoreOf 2 (X.L 1)) = 2 ^ 4
  nat_right : NatSec (X.L 1) ⊥ (pCoreOf 2 (X.L 1))
  card_inf : Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)) = 2 ^ 2

theorem even_singularity_A5A5 (X : Setup Γ G)
    (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) (hev : Even s)
    (hn : ∀ v, nOf Γ v = 2) : s = 4 ∧ X.TreeL34Data := by
  classical
  have h4 : s = 4 := X.singularity_eq_four hc hs hev hn
  subst h4
  have hn0 : X.n 0 = 2 := hn (X.vert 0)
  have hn1 : X.n 1 = 2 := hn (X.vert 1)
  have hcardS : Nat.card X.S = 2 ^ 6 := X.card_S_of_four hs hn0 hn1
  have hcard0 : Nat.card (X.Q 0) = 2 ^ 4 := X.card_Q_of_four hs hn0 hn1 (Or.inl rfl)
  have hcard1 : Nat.card (X.Q 1) = 2 ^ 4 := X.card_Q_of_four hs hn0 hn1 (Or.inr rfl)
  have hL0 : IsLocL2 Γ G (X.vert 0) (X.n 0) (X.L 0) := X.hyp.isLocL2_oTwoPrime (X.vert 0)
  have hL1 : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) := X.hyp.isLocL2_oTwoPrime (X.vert 1)
  have helem0 : IsElemAbelian 2 (pCoreOf 2 (X.L 0)) := by
    rw [hL0.pCoreOf_eq]
    exact X.isElemAbelian_Q_of_card hc 0 hn0 hcard0
  have helem1 : IsElemAbelian 2 (pCoreOf 2 (X.L 1)) := by
    rw [hL1.pCoreOf_eq]
    exact X.isElemAbelian_Q_of_card hc 1 hn1 hcard1
  have hcardL0 : Nat.card (pCoreOf 2 (X.L 0)) = 2 ^ 4 := by
    rw [hL0.pCoreOf_eq]
    exact hcard0
  have hcardL1 : Nat.card (pCoreOf 2 (X.L 1)) = 2 ^ 4 := by
    rw [hL1.pCoreOf_eq]
    exact hcard1
  have hT0 : IsSylowTwoOf X.S (X.L 0) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L 0
  have hT1 : IsSylowTwoOf X.S (X.L 1) := by
    rw [← X.edgeSylow_zero]
    exact X.isSylowTwoOf_edgeSylow_L_succ 0
  have hnat0 : NatSec (X.L 0) ⊥ (pCoreOf 2 (X.L 0)) :=
    X.natSec_Q_of_card hc 0 hn0 hcard0 hT0
      (X.four_le_card_Q_inf_centralizer hc hs hn0 hn1 (Or.inl rfl))
  have hnat1 : NatSec (X.L 1) ⊥ (pCoreOf 2 (X.L 1)) :=
    X.natSec_Q_of_card hc 1 hn1 hcard1 hT1
      (X.four_le_card_Q_inf_centralizer hc hs hn0 hn1 (Or.inr rfl))
  have hcardInf : Nat.card ↥(pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)) = 2 ^ 2 := by
    rw [hL0.pCoreOf_eq, hL1.pCoreOf_eq]
    exact X.card_Q_inf_of_four hc hs hn0 hn1
  exact ⟨rfl, hcardS, helem0, hcardL0, hnat0, helem1, hcardL1, hnat1, hcardInf⟩

end Setup

end TypeZero

end CFSG.Quasithin.St84
