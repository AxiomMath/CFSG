module

public import CFSG.LocalAnalysis.StandardType.GGQTwoInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoTransport
public import CFSG.LocalAnalysis.StandardType.GGQTwoS1Transport
public import CFSG.LocalAnalysis.StandardType.GGQTwoACore
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCore
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerSym
public import CFSG.LocalAnalysis.StandardType.GGQTwoAInnerE7
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInnerPhi
public import CFSG.LocalAnalysis.StandardType.GGQTwoDInnerE8
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflOrth
public import CFSG.LocalAnalysis.StandardType.GGQTwoInvForm
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCNorm
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoord
public import CFSG.LocalAnalysis.StandardType.GGQTwoThmA
public import CFSG.LocalAnalysis.StandardType.GGQTwoBridgeHL
public import CFSG.LocalAnalysis.StandardType.GGQTwoDWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2xF1_cartan_symm (D : GGQ2Lin 3) {m : ℕ} (e : Fin m ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e) :
    ∀ i j, D.cartan i j = D.cartan j i :=
  ggQ2xQ_cartan_symm_of_reindex (ggCoxeterMatrixD m)
    (by intro a b; rw [ggCoxeterMatrixD_apply]; split_ifs <;> omega) D e hD

private lemma ggQ2xF1_dsimple_chain {m : ℕ} (i : Fin m) (hlt : (i : ℕ) + 1 < m) :
    ggDSimple 3 m i = (Pi.single i (1 : ZMod 3) : GGBCV m) -
        (Pi.single ⟨(i : ℕ) + 1, hlt⟩ (1 : ZMod 3) : GGBCV m) := by
  funext l
  simp only [ggDSimple, hlt, if_true, Pi.sub_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> simp_all

private lemma ggQ2xF1_dsimple_fork {m : ℕ} (hm : 2 ≤ m) :
    ggDSimple 3 m ⟨m - 1, by omega⟩ =
      (Pi.single ⟨m - 2, by omega⟩ (1 : ZMod 3) : GGBCV m) +
        (Pi.single ⟨m - 1, by omega⟩ (1 : ZMod 3) : GGBCV m) := by
  funext l
  rw [ggDSimple, if_neg (show ¬ (m - 1) + 1 < m by omega), Pi.add_apply]
  by_cases h2 : (l : ℕ) + 2 = m
  · have hl : l = ⟨m - 2, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
    rw [if_pos (Or.inl h2), hl, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3)
        (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)]
    simp
  · by_cases h1 : (l : ℕ) + 1 = m
    · have hl : l = ⟨m - 1, by omega⟩ := Fin.ext (by simp only [Fin.val_mk]; omega)
      rw [if_pos (Or.inr h1), hl,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3)
          (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega),
        Pi.single_eq_same]
      simp
    · rw [if_neg (by rintro (h | h); exact h2 h; exact h1 h)]
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3)
          (by intro h; exact h2 (by
            have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)),
        Pi.single_eq_of_ne (M := fun _ => ZMod 3)
          (by intro h; exact h1 (by
            have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)),
        add_zero]

private lemma ggQ2xF1_dsimple_mem_D {m : ℕ} (hm : 4 ≤ m) (i : Fin m) :
    ggDSimple 3 m i ∈ ggDRoots m := by
  rcases lt_or_ge ((i : ℕ) + 1) m with hlt | hge
  · rw [ggDRoots, ggQ2xF1_dsimple_chain i hlt]
    exact ggQ2_DW_Wt_sub_single i ⟨(i : ℕ) + 1, hlt⟩
      (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)
  · have hltm : m - 1 < m := by omega
    have hi : i = ⟨m - 1, hltm⟩ := Fin.ext (by
      simp only [Fin.val_mk]
      have := i.isLt
      omega)
    subst hi
    rw [ggDRoots, ggQ2xF1_dsimple_fork (m := m) (by omega)]
    exact ggQ2_DW_Wt_add_single ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩
      (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega)

private theorem ggQ2xF1_weyl_coord (D : GGQ2Lin 3) {m : ℕ} (hm : 4 ≤ m) (e : Fin m ≃ D.ι)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j) :
    (D.weyl).map (ggLinConj τ).toMonoidHom = ggBCReflGp (ggDRoots m) := by
  rw [ggQ2_DW_linWeylMap D hm e τ hcor hroot]
  apply le_antisymm
  · rw [ggQ2_DW_Wc, Subgroup.closure_le]
    rintro t ⟨i, rfl⟩
    rw [ggQ2_DW_r_eq_bc hm i]
    exact Subgroup.subset_closure
      ⟨ggDSimple 3 m i, ggQ2xF1_dsimple_mem_D hm i,
        (by rw [ggQ2_DW_simple_norm hm i]; decide), rfl⟩
  · rw [ggBCReflGp, Subgroup.closure_le]
    rintro t ⟨c, hc, hcc, rfl⟩
    exact ggQ2_DW_Droot_refl_mem_Wc m hm hc hcc

private lemma ggQ2xF1_dsimple_zero {m : ℕ} [NeZero m] (hm : 4 ≤ m) {i : Fin m}
    (hi : (i : ℕ) ≠ 0) :
    ggDSimple 3 m i 0 = 0 := by
  by_cases hlt : (i : ℕ) + 1 < m
  · rw [ggQ2xF1_dsimple_chain i hlt]
    have h0i : (0 : Fin m) ≠ i := by
      intro h
      have hv : (i : ℕ) = 0 := by
        have := congrArg Fin.val h
        simpa using this.symm
      exact hi hv
    have h0i1 : (0 : Fin m) ≠ ⟨(i : ℕ) + 1, hlt⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk, Fin.val_zero] at this
      omega
    rw [Pi.sub_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) h0i,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) h0i1, sub_self]
  · have hlastm : m - 1 < m := by omega
    have hlast : i = ⟨m - 1, hlastm⟩ := Fin.ext (by
      simp only [Fin.val_mk]
      have := i.isLt
      omega)
    subst hlast
    rw [ggQ2xF1_dsimple_fork (m := m) (by omega)]
    have h0a : (0 : Fin m) ≠ ⟨m - 2, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk, Fin.val_zero] at this
      omega
    have h0b : (0 : Fin m) ≠ ⟨m - 1, hlastm⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk, Fin.val_zero] at this
      omega
    rw [Pi.add_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) h0a,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) h0b, zero_add]

private noncomputable def ggQ2xF1_parabT {m : ℕ} (hm : 4 ≤ m) :
    Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m) :=
  Subgroup.closure (Set.range (fun i : {i : Fin m // (i : ℕ) ≠ 0} =>
    ggQ2_DW_r 3 m hm i.1))

private lemma ggQ2xF1_parabT_adj {m : ℕ} (hm : 4 ≤ m) (c : Fin m)
    (hc0 : (c : ℕ) ≠ 0) (hcn : (c : ℕ) + 1 < m) :
    ggQ2_DW_Q 3 m (Equiv.swap c ⟨(c : ℕ) + 1, hcn⟩) ∈ ggQ2xF1_parabT hm := by
  rw [← ggQ2_DW_r_eq_swap 3 m hm c hcn]
  exact Subgroup.subset_closure ⟨⟨c, hc0⟩, rfl⟩

private lemma ggQ2xF1_parabT_swap {m : ℕ} (hm : 4 ≤ m) (i j : Fin m)
    (hi : (i : ℕ) ≠ 0) (hj : (j : ℕ) ≠ 0) :
    ggQ2_DW_Q 3 m (Equiv.swap i j) ∈ ggQ2xF1_parabT hm := by
  have key : ∀ k : ℕ, ∀ a b : Fin m, a.val ≤ b.val → max a.val b.val = k →
      (a : ℕ) ≠ 0 → (b : ℕ) ≠ 0 →
      ggQ2_DW_Q 3 m (Equiv.swap a b) ∈ ggQ2xF1_parabT hm := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro a b hle hk ha hb
      rcases lt_or_eq_of_le hle with hlt | heq
      · let c : Fin m := ⟨b.val - 1, by omega⟩
        have hcv : c.val = b.val - 1 := rfl
        have hc0 : (c : ℕ) ≠ 0 := by simp only [c, Fin.val_mk] at *; omega
        have hcn : (c : ℕ) + 1 < m := by simp only [c, Fin.val_mk] at *; omega
        have hcs : (⟨(c : ℕ) + 1, hcn⟩ : Fin m) = b := by
          apply Fin.ext; simp only [c, Fin.val_mk]; omega
        have hgen : ggQ2_DW_Q 3 m (Equiv.swap c (⟨(c : ℕ) + 1, hcn⟩ : Fin m)) ∈
            ggQ2xF1_parabT hm := ggQ2xF1_parabT_adj hm c hc0 hcn
        rw [hcs] at hgen
        by_cases hac : a.val = c.val
        · have hac' : a = c := Fin.ext hac
          rw [hac']; exact hgen
        · have haltc : a.val < c.val := by simp only [c, Fin.val_mk] at *; omega
          have ih_ac : ggQ2_DW_Q 3 m (Equiv.swap a c) ∈ ggQ2xF1_parabT hm :=
            ih (max a.val c.val) (by simp only [c, Fin.val_mk] at *; omega)
              a c (by omega) rfl ha hc0
          have hne_ac : a ≠ c := by intro hh; exact hac (congrArg Fin.val hh)
          have hne_ab : a ≠ b := by intro hh; have := congrArg Fin.val hh; omega
          have hswap : Equiv.swap a b = Equiv.swap c b * Equiv.swap a c * Equiv.swap c b := by
            rw [Equiv.swap_comm a b, ← Equiv.swap_mul_swap_mul_swap hne_ac hne_ab]
          rw [hswap, map_mul, map_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hgen ih_ac) hgen
      · have hab : a = b := Fin.ext heq
        rw [hab, Equiv.swap_self]
        show ggQ2_DW_Q 3 m (1 : Equiv.Perm (Fin m)) ∈ ggQ2xF1_parabT hm
        rw [map_one]
        exact Subgroup.one_mem _
  rcases le_total i.val j.val with hle | hle
  · exact key (max i.val j.val) i j hle rfl hi hj
  · have h := key (max j.val i.val) j i hle rfl hj hi
    rwa [← Equiv.swap_comm i j] at h

private lemma ggQ2xF1_parabT_conj_add {m : ℕ} (hm : 4 ≤ m) (i j : Fin m) (hij : i ≠ j)
    (hci : (i : ℕ) ≠ 0) (hcj : (j : ℕ) ≠ 0) :
    ∃ τ : Equiv.Perm (Fin m), ggQ2_DW_Q 3 m τ ∈ ggQ2xF1_parabT hm ∧
      ggQ2_DW_Q 3 m τ
        ((Pi.single ⟨m - 2, by omega⟩ (1 : ZMod 3) : GGBCV m) +
          Pi.single ⟨m - 1, by omega⟩ 1) =
        (Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1 := by
  have hab : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
  have h2 : (m - 2 : ℕ) ≠ 0 := by omega
  have h1 : (m - 1 : ℕ) ≠ 0 := by omega
  by_cases hja : j = ⟨m - 2, by omega⟩
  · refine ⟨Equiv.swap ⟨m - 1, by omega⟩ i, ggQ2xF1_parabT_swap hm _ _ h1 hci, ?_⟩
    have hia : i ≠ ⟨m - 2, by omega⟩ := by
      intro h; exact hij (h.trans hja.symm)
    have hτa : Equiv.swap ⟨m - 1, by omega⟩ i (⟨m - 2, by omega⟩ : Fin m) =
        ⟨m - 2, by omega⟩ := by
      rw [Equiv.swap_apply_def, if_neg hab, if_neg (fun h => hia h.symm)]
    have hτb : Equiv.swap ⟨m - 1, by omega⟩ i (⟨m - 1, by omega⟩ : Fin m) = i :=
      Equiv.swap_apply_left _ _
    change ggQ2_DW_Q 3 m (Equiv.swap ⟨m - 1, by omega⟩ i)
      (ggQ2_DW_fvec 3 m ⟨m - 2, by omega⟩ + ggQ2_DW_fvec 3 m ⟨m - 1, by omega⟩) = _
    rw [ggQ2_DW_Q_add_fvec, hτa, hτb, hja]
    exact add_comm _ _
  · refine ⟨Equiv.swap ⟨m - 2, by omega⟩ i * Equiv.swap ⟨m - 1, by omega⟩ j, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (ggQ2xF1_parabT_swap hm _ _ h2 hci)
        (ggQ2xF1_parabT_swap hm _ _ h1 hcj)
    · have hτa : (Equiv.swap ⟨m - 2, by omega⟩ i * Equiv.swap ⟨m - 1, by omega⟩ j)
          (⟨m - 2, by omega⟩ : Fin m) = i := by
        rw [Equiv.Perm.mul_apply]
        have h1' : (Equiv.swap ⟨m - 1, by omega⟩ j) (⟨m - 2, by omega⟩ : Fin m) =
            ⟨m - 2, by omega⟩ := by
          rw [Equiv.swap_apply_def, if_neg hab, if_neg (fun h => hja h.symm)]
        rw [h1', Equiv.swap_apply_left]
      have hτb : (Equiv.swap ⟨m - 2, by omega⟩ i * Equiv.swap ⟨m - 1, by omega⟩ j)
          (⟨m - 1, by omega⟩ : Fin m) = j := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_def,
          if_neg hja, if_neg (fun h => hij h.symm)]
      change ggQ2_DW_Q 3 m (Equiv.swap ⟨m - 2, by omega⟩ i * Equiv.swap ⟨m - 1, by omega⟩ j)
        (ggQ2_DW_fvec 3 m ⟨m - 2, by omega⟩ + ggQ2_DW_fvec 3 m ⟨m - 1, by omega⟩) = _
      rw [ggQ2_DW_Q_add_fvec, hτa, hτb]
      rfl

private lemma ggQ2xF1_add_refl_mem_parabT {m : ℕ} (hm : 4 ≤ m) (i j : Fin m) (hij : i ≠ j)
    (hci : (i : ℕ) ≠ 0) (hcj : (j : ℕ) ≠ 0)
    (hc : ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ≠ 0) :
    ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) hc ∈
      ggQ2xF1_parabT hm := by
  obtain ⟨τ, hτmem, hτ⟩ := ggQ2xF1_parabT_conj_add hm i j hij hci hcj
  let a : Fin m := ⟨m - 2, by omega⟩
  let b : Fin m := ⟨m - 1, by omega⟩
  have hab : a ≠ b := by
    intro h; have := congrArg Fin.val h; simp only [a, b, Fin.val_mk] at this; omega
  have hcA : ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ⬝ᵥ
      ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ≠ 0 := by
    rw [ggQ2_DW_add_norm a b hab]; decide
  have hrb : ggQ2_DW_r 3 m hm b =
      ggBCRefl ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) hcA := by
    rw [ggQ2_DW_r_eq_bc hm b]
    refine ggQ2_DW_refl_congr ?_ _ _
    funext k
    have hb' : ¬ ((b : ℕ) + 1 < m) := by simp only [b, Fin.val_mk]; omega
    simp only [ggDSimple, hb', if_false, Pi.add_apply, Pi.single_apply]
    by_cases hka : k = a
    · subst hka
      rw [if_pos (Or.inl (by simp only [a, Fin.val_mk]; omega)), if_pos rfl,
        if_neg (fun h => hab h), add_zero]
    · by_cases hkb : k = b
      · subst hkb
        rw [if_pos (Or.inr (by simp only [b, Fin.val_mk]; omega)),
          if_neg (fun h => hab h.symm), if_pos rfl, zero_add]
      · have h1' : ¬ (k : ℕ) + 2 = m := by
          intro h; exact hka (Fin.ext (by simp only [a, Fin.val_mk]; omega))
        have h2' : ¬ (k : ℕ) + 1 = m := by
          intro h; exact hkb (Fin.ext (by simp only [b, Fin.val_mk]; omega))
        rw [if_neg (by rintro (h | h); exact h1' h; exact h2' h), if_neg hka, if_neg hkb,
          add_zero]
  have hconj := ggQ2_DW_bc_conj (ggQ2_DW_Q 3 m τ) (ggQ2_DW_Q_isom 3 m τ)
    ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) hcA
  have heq : ggBCRefl (ggQ2_DW_Q 3 m τ
      ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1))
        (by
          change ggQ2_DW_dotLin 3 m
            (ggQ2_DW_Q 3 m τ ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1))
            (ggQ2_DW_Q 3 m τ ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1)) ≠ 0
          rw [ggQ2_DW_Q_isom 3 m τ
            ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1)
            ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1)]
          exact hcA) =
      ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) hc :=
    ggQ2_DW_refl_congr hτ _ hc
  rw [← heq, ← hconj, ← hrb]
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ hτmem
      (Subgroup.subset_closure ⟨⟨b, by simp only [b, Fin.val_mk]; omega⟩, rfl⟩))
    (Subgroup.inv_mem _ hτmem)

private lemma ggQ2xF1_DrootLam_refl_mem_parabT {m : ℕ} [NeZero m] (hm : 4 ≤ m) {z : GGBCV m}
    (hz : z ∈ ggDRootsLam1 m) (hz0 : z ⬝ᵥ z ≠ 0) :
    ggBCRefl z hz0 ∈ ggQ2xF1_parabT hm := by
  obtain ⟨i, j, l, k, hij, hl, hk, hz_eq⟩ :=
    ggQ2_DW_weight_two (m := m) (by exact hz.1)
  have hi0 : (i : ℕ) ≠ 0 := by
    intro h
    have hzi : z i = l := by
      rw [hz_eq]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij,
        mul_zero, add_zero, mul_one]
    have h0 : z (0 : Fin m) = l := by
      rw [show (0 : Fin m) = i from (Fin.ext h).symm]
      exact hzi
    rw [hz.2] at h0
    exact hl h0.symm
  have hj0 : (j : ℕ) ≠ 0 := by
    intro h
    have hzj : z j = k := by
      rw [hz_eq]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), Pi.single_eq_same,
        mul_zero, zero_add, mul_one]
    have h0 : z (0 : Fin m) = k := by
      rw [show (0 : Fin m) = j from (Fin.ext h).symm]
      exact hzj
    rw [hz.2] at h0
    exact hk h0.symm
  rcases ggQ2_DW_eq_one_or_neg_one l hl with rfl | rfl <;>
    rcases ggQ2_DW_eq_one_or_neg_one k hk with rfl | rfl
  · have hz' : z = (Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1 := by
      rw [hz_eq]; ext t
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul]
    rw [ggQ2_DW_refl_congr hz' hz0 (by rw [ggQ2_DW_add_norm i j hij]; decide)]
    exact ggQ2xF1_add_refl_mem_parabT hm i j hij hi0 hj0
      (by rw [ggQ2_DW_add_norm i j hij]; decide)
  · have hz' : z = (Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1 := by
      rw [hz_eq]; ext t
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact ggQ2_DW_scalar_f _ _
    rw [ggQ2_DW_refl_congr hz' hz0 (by rw [ggQ2_DW_sub_norm i j hij]; decide),
      ggQ2_DW_sub_refl_eq_swap i j hij (by rw [ggQ2_DW_sub_norm i j hij]; decide)]
    exact ggQ2xF1_parabT_swap hm i j hi0 hj0
  · have hz' : z = -((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) := by
      rw [hz_eq]; ext t
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact ggQ2_DW_scalar_g _ _
    have hcsub : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
        ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ≠ 0 := by
      rw [ggQ2_DW_sub_norm i j hij]; decide
    have hcneg : (-((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)) ⬝ᵥ
        (-((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)) ≠ 0 := by
      rw [ggQ2_DW_neg_dot_self, ggQ2_DW_sub_norm i j hij]; decide
    rw [ggQ2_DW_refl_congr hz' hz0 hcneg]
    rw [show ggBCRefl (-((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)) hcneg =
        ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) hcsub from
      ggQ2_DW_refl_neg ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) hcsub hcneg]
    rw [ggQ2_DW_sub_refl_eq_swap i j hij hcsub]
    exact ggQ2xF1_parabT_swap hm i j hi0 hj0
  · have hz' : z = -((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) := by
      rw [hz_eq]; ext t
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, one_mul]
      exact ggQ2_DW_scalar_h _ _
    have hcadd : ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ
        ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ≠ 0 := by
      rw [ggQ2_DW_add_norm i j hij]; decide
    have hcneg : (-((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)) ⬝ᵥ
        (-((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)) ≠ 0 := by
      rw [ggQ2_DW_neg_dot_self, ggQ2_DW_add_norm i j hij]; decide
    rw [ggQ2_DW_refl_congr hz' hz0 hcneg]
    rw [show ggBCRefl (-((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)) hcneg =
        ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) hcadd from
      ggQ2_DW_refl_neg ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) hcadd hcneg]
    exact ggQ2xF1_add_refl_mem_parabT hm i j hij hi0 hj0 hcadd

private lemma ggQ2xF1_parabT_eq {m : ℕ} [NeZero m] (hm : 4 ≤ m) :
    ggQ2xF1_parabT hm = ggBCReflGp (ggDRootsLam1 m) := by
  apply le_antisymm
  · rw [ggQ2xF1_parabT, Subgroup.closure_le]
    rintro t ⟨⟨i, hi⟩, rfl⟩
    change ggQ2_DW_r 3 m hm i ∈ ggBCReflGp (ggDRootsLam1 m)
    rw [ggQ2_DW_r_eq_bc hm i]
    exact Subgroup.subset_closure
      ⟨ggDSimple 3 m i, ⟨ggQ2xF1_dsimple_mem_D hm i, ggQ2xF1_dsimple_zero hm hi⟩,
        (by rw [ggQ2_DW_simple_norm hm i]; decide), rfl⟩
  · rw [ggBCReflGp, Subgroup.closure_le]
    rintro t ⟨c, hc, hcc, rfl⟩
    exact ggQ2xF1_DrootLam_refl_mem_parabT hm hc hcc

private theorem ggQ2xF1_parab_lam1 (D : GGQ2Lin 3) {m : ℕ} [NeZero m] (hm : 4 ≤ m)
    (e : Fin m ≃ D.ι) (ha : D.a = e ⟨0, by omega⟩) (τ : D.V ≃ₗ[ZMod 3] GGBCV m)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j) :
    (D.parab {k | k ≠ D.a}).map (ggLinConj τ).toMonoidHom =
      ggBCReflGp (ggDRootsLam1 m) := by
  have hm4 : 4 ≤ m := hm
  have hmap : (D.parab {k | k ≠ D.a}).map (ggLinConj τ).toMonoidHom =
      ggQ2xF1_parabT hm4 := by
    rw [GGQ2Lin.parab, MonoidHom.map_closure]
    congr 1
    ext t
    constructor
    · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective k
      have hi : (i : ℕ) ≠ 0 := by
        intro h
        exact hk (by rw [ha]; exact congrArg e (Fin.ext h))
      exact ⟨⟨i, hi⟩, (ggQ2_DW_linConj_simpleRefl D hm e τ hcor hroot i).symm⟩
    · rintro ⟨⟨i, hi⟩, rfl⟩
      refine ⟨D.simpleRefl (e i), ⟨e i, ?_, rfl⟩,
        ggQ2_DW_linConj_simpleRefl D hm e τ hcor hroot i⟩
      rw [ha]
      intro h
      exact hi (by have := congrArg Fin.val (e.injective h); simpa using this)
  rw [hmap, ggQ2xF1_parabT_eq hm4]

private theorem ggQ2xF1_fixed_lam1 {m : ℕ} [NeZero m] (hm : 5 ≤ m) (v : GGBCV m) :
    (∀ g ∈ ggBCReflGp (ggDRootsLam1 m), g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)} := by
  constructor
  · intro hv
    have hdot_zero : ∀ (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0),
        ggBCRefl c hc ∈ ggBCReflGp (ggDRootsLam1 m) → c ⬝ᵥ v = 0 := by
      intro c hc hcG
      have hfix := hv (ggBCRefl c hc) hcG
      rw [ggQ2x_ggBCRefl_apply c hc v] at hfix
      have hX : ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c = 0 := by
        apply add_left_cancel (a := v)
        rw [hfix, add_zero]
      have hcne : c ≠ 0 := by
        intro h0; exact hc (by rw [h0]; simp)
      rcases smul_eq_zero.mp hX with h | h
      · exact (mul_eq_zero.mp h).resolve_right hc
      · exact absurd h hcne
    have hzero : ∀ j : Fin m, j ≠ 0 → v j = 0 := by
      intro j hj
      have hk : ∃ k : Fin m, k ≠ 0 ∧ k ≠ j := by
        by_contra h
        push Not at h
        have hsub : (Finset.univ : Finset (Fin m)) ⊆ ({0, j} : Finset (Fin m)) := by
          intro k _
          by_cases hk0 : k = 0
          · rw [hk0]; simp
          · have hkj : k = j := h k hk0
            rw [hkj]; simp
        have hle : Fintype.card (Fin m) ≤ 2 := by
          calc Fintype.card (Fin m) = (Finset.univ : Finset (Fin m)).card := rfl
            _ ≤ ({0, j} : Finset (Fin m)).card := Finset.card_le_card hsub
            _ ≤ 2 := le_of_eq (Finset.card_pair (Ne.symm hj))
        rw [Fintype.card_fin] at hle
        omega
      obtain ⟨k, hk0, hkj⟩ := hk
      have hjk : j ≠ k := Ne.symm hkj
      have hc1mem : (Pi.single j 1 - Pi.single k 1 : GGBCV m) ∈ ggDRootsLam1 m := by
        refine ⟨ggQ2x_wt_sub_single j k hjk, ?_⟩
        simp [Pi.sub_apply, Pi.single_eq_of_ne, hj, hk0]
      have hc1n : (Pi.single j 1 - Pi.single k 1 : GGBCV m) ⬝ᵥ
          (Pi.single j 1 - Pi.single k 1 : GGBCV m) ≠ 0 := by
        rw [ggQ2x_sub_single_norm j k hjk]; decide
      have hd1 : (Pi.single j 1 - Pi.single k 1 : GGBCV m) ⬝ᵥ v = 0 :=
        hdot_zero _ hc1n (Subgroup.subset_closure ⟨_, hc1mem, hc1n, rfl⟩)
      rw [ggQ2x_sub_single_dot] at hd1
      have hc2mem : (Pi.single j 1 + Pi.single k 1 : GGBCV m) ∈ ggDRootsLam1 m := by
        refine ⟨ggQ2x_wt_single_add_single j k hjk 1 1 one_ne_zero one_ne_zero, ?_⟩
        simp [Pi.add_apply, Pi.single_eq_of_ne, hj, hk0]
      have hc2n : (Pi.single j 1 + Pi.single k 1 : GGBCV m) ⬝ᵥ
          (Pi.single j 1 + Pi.single k 1 : GGBCV m) ≠ 0 := by
        rw [ggQ2x_dot_self_eq_wt,
          ggQ2x_wt_single_add_single j k hjk 1 1 one_ne_zero one_ne_zero]
        decide
      have hd2 : (Pi.single j 1 + Pi.single k 1 : GGBCV m) ⬝ᵥ v = 0 :=
        hdot_zero _ hc2n (Subgroup.subset_closure ⟨_, hc2mem, hc2n, rfl⟩)
      rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct] at hd2
      have h1 : v j = v k := sub_eq_zero.mp hd1
      have h2 : v j = -v k := eq_neg_of_add_eq_zero_left hd2
      have hk0v : v k = 0 := by
        have h2' : v k = -v k := by nth_rewrite 1 [← h1]; exact h2
        have hsum : v k + v k = 0 := by
          nth_rewrite 2 [h2']
          exact add_neg_cancel (v k)
        have h2k : (2 : ZMod 3) * v k = 0 := by rw [two_mul]; exact hsum
        exact (mul_eq_zero.mp h2k).resolve_left (by decide)
      rw [h1, hk0v]
    rw [Submodule.mem_span_singleton]
    refine ⟨v 0, ?_⟩
    funext i
    by_cases hi : i = 0
    · subst hi; simp
    · rw [hzero i hi]
      simp [Pi.single_eq_of_ne hi]
  · rintro hvsp
    rw [Submodule.mem_span_singleton] at hvsp
    obtain ⟨a, rfl⟩ := hvsp
    have hbase : ∀ t ∈ ggBCReflSet (ggDRootsLam1 m),
        t (a • (Pi.single 0 1 : GGBCV m)) = a • Pi.single 0 1 := by
      rintro t ⟨c, hc, hcc, rfl⟩
      rw [ggQ2x_ggBCRefl_apply c hcc]
      have hc0 : c 0 = 0 := hc.2
      have hdot : c ⬝ᵥ (a • (Pi.single 0 1 : GGBCV m)) = 0 := by
        rw [dotProduct_smul, dotProduct_single, hc0, zero_mul, smul_zero]
      rw [hdot, zero_mul, zero_smul, add_zero]
    have hfix : ∀ g ∈ ggBCReflGp (ggDRootsLam1 m),
        g (a • (Pi.single 0 1 : GGBCV m)) = a • Pi.single 0 1 := by
      intro g hg
      refine Subgroup.closure_induction (fun x hx => hbase x hx) ?_ ?_ ?_ hg
      · rfl
      · intro x y hx hy ihx ihy
        rw [LinearEquiv.mul_apply, ihy, ihx]
      · intro x hx ihx
        change x.symm (a • (Pi.single 0 1 : GGBCV m)) = a • Pi.single 0 1
        have h := congrArg (fun w => x.symm w) ihx
        rw [LinearEquiv.symm_apply_apply] at h
        exact h.symm
    exact hfix

private def ggQ2xF1_prod {m : ℕ} (v : GGBCV m) : ZMod 3 := ∏ i, v i

private def ggQ2xF1_flipS {m : ℕ} (S : Finset (Fin m)) (v : GGBCV m) : GGBCV m :=
  fun k => if k ∈ S then -v k else v k

private lemma ggQ2xF1_scalar_a (x y : ZMod 3) : y + (x + y) * 2 = -x := by revert x y; decide
private lemma ggQ2xF1_scalar_b (x y : ZMod 3) : x + (x + y) * 2 = -y := by revert x y; decide

private lemma ggQ2xF1_flipS_union {m : ℕ} (S T : Finset (Fin m)) (h : Disjoint S T)
    (v : GGBCV m) :
    ggQ2xF1_flipS (S ∪ T) v = ggQ2xF1_flipS S (ggQ2xF1_flipS T v) := by
  funext k
  rw [ggQ2xF1_flipS, ggQ2xF1_flipS, ggQ2xF1_flipS]
  by_cases hkS : k ∈ S
  · have hkT : k ∉ T := fun hkT => (Finset.disjoint_left.mp h) hkS hkT
    simp [Finset.mem_union, hkS, hkT]
  · by_cases hkT : k ∈ T
    · simp [Finset.mem_union, hkS, hkT]
    · simp [Finset.mem_union, hkS, hkT]

private lemma ggQ2xF1_Wt_eq_one {m : ℕ} {v : GGBCV m} (h : ggBCWt v = 1) :
    ∃ a : Fin m, ∃ c : ZMod 3, c ≠ 0 ∧ v = c • Pi.single a 1 := by
  unfold ggBCWt at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  refine ⟨a, v a, ?_, ?_⟩
  · have hm : a ∈ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp
    simpa using hm
  · funext i
    by_cases hia : i = a
    · subst hia; simp
    · have hm : i ∉ Finset.univ.filter (fun i => v i ≠ 0) := by rw [ha]; simp [hia]
      have hvi : v i = 0 := by simpa using hm
      simp [Pi.single_eq_of_ne hia, hvi]

private lemma ggQ2xF1_prod_flipS_single {m : ℕ} (a : Fin m) (v : GGBCV m) :
    ggQ2xF1_prod (ggQ2xF1_flipS {a} v) = -ggQ2xF1_prod v := by
  classical
  rw [ggQ2xF1_prod, ggQ2xF1_prod,
    ← Finset.prod_erase_mul (Finset.univ : Finset (Fin m))
      (fun i => ggQ2xF1_flipS {a} v i) (Finset.mem_univ a),
    ← Finset.prod_erase_mul (Finset.univ : Finset (Fin m)) v (Finset.mem_univ a)]
  have hprod : Finset.prod ((Finset.univ : Finset (Fin m)).erase a)
      (fun i => ggQ2xF1_flipS {a} v i) =
      Finset.prod ((Finset.univ : Finset (Fin m)).erase a) (fun i => v i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_erase] at hi
    simp only [ggQ2xF1_flipS, Finset.mem_singleton]
    rw [if_neg hi.1]
  have ha : ggQ2xF1_flipS {a} v a = -v a := by simp [ggQ2xF1_flipS]
  rw [hprod, ha, mul_neg]

private lemma ggQ2xF1_prod_flipS_pair {m : ℕ} (a b : Fin m) (hab : a ≠ b) (v : GGBCV m) :
    ggQ2xF1_prod (ggQ2xF1_flipS ({a, b} : Finset (Fin m)) v) = ggQ2xF1_prod v := by
  have hdisj : Disjoint ({a} : Finset (Fin m)) {b} := by
    rw [Finset.disjoint_singleton_left]
    simpa using hab
  have hunion : ({a, b} : Finset (Fin m)) = {a} ∪ {b} := by
    ext i; simp [Finset.mem_union]
  rw [hunion, ggQ2xF1_flipS_union _ _ hdisj,
    ggQ2xF1_prod_flipS_single, ggQ2xF1_prod_flipS_single, neg_neg]

private lemma ggQ2xF1_prod_Q {m : ℕ} (σ : Equiv.Perm (Fin m)) (v : GGBCV m) :
    ggQ2xF1_prod (ggQ2_DW_Q 3 m σ v) = ggQ2xF1_prod v := by
  rw [ggQ2xF1_prod, ggQ2xF1_prod]
  simp only [ggQ2_DW_Q_apply]
  exact Equiv.prod_comp σ.symm (fun i => v i)

private lemma ggQ2xF1_add_refl_apply {m : ℕ} (a b : Fin m) (hab : a ≠ b)
    (hc : ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ⬝ᵥ
      ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ≠ 0) (v : GGBCV m) :
    ggBCRefl ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) hc v =
      ggQ2xF1_flipS ({a, b} : Finset (Fin m))
        (ggQ2_DW_Q 3 m (Equiv.swap a b) v) := by
  funext k
  rw [ggQ2_DW_bc_apply', ggQ2xF1_flipS, ggQ2_DW_Q_apply, ggQ2_DW_add_norm a b hab]
  have hdot : ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ⬝ᵥ v = v a + v b := by
    rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct]
  rw [hdot]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hka : k = a
  · rw [hka, if_pos (by simp : (a : Fin m) ∈ ({a, b} : Finset (Fin m))),
      Pi.single_eq_same, Pi.single_eq_of_ne hab, add_zero, mul_one,
      Equiv.symm_swap, Equiv.swap_apply_left]
    exact ggQ2xF1_scalar_b (v a) (v b)
  · by_cases hkb : k = b
    · rw [hkb, if_pos (by simp : (b : Fin m) ∈ ({a, b} : Finset (Fin m))),
        Pi.single_eq_of_ne (Ne.symm hab), Pi.single_eq_same, zero_add, mul_one,
        Equiv.symm_swap, Equiv.swap_apply_right]
      exact ggQ2xF1_scalar_a (v a) (v b)
    · rw [if_neg (by simp [hka, hkb]), Pi.single_eq_of_ne hka, Pi.single_eq_of_ne hkb,
        add_zero, mul_zero, add_zero, Equiv.symm_swap,
        Equiv.swap_apply_of_ne_of_ne hka hkb]

private lemma ggQ2xF1_add_refl_prod {m : ℕ} (a b : Fin m) (hab : a ≠ b)
    (hc : ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ⬝ᵥ
      ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) ≠ 0) (v : GGBCV m) :
    ggQ2xF1_prod (ggBCRefl ((Pi.single a (1 : ZMod 3) : GGBCV m) + Pi.single b 1) hc v) =
      ggQ2xF1_prod v := by
  rw [ggQ2xF1_add_refl_apply a b hab hc v, ggQ2xF1_prod_flipS_pair a b hab]
  exact ggQ2xF1_prod_Q (Equiv.swap a b) v

private lemma ggQ2xF1_r_prod {m : ℕ} (hm : 4 ≤ m) (i : Fin m) (v : GGBCV m) :
    ggQ2xF1_prod (ggQ2_DW_r 3 m hm i v) = ggQ2xF1_prod v := by
  by_cases hlt : (i : ℕ) + 1 < m
  · rw [ggQ2_DW_r_eq_swap 3 m hm i hlt]
    exact ggQ2xF1_prod_Q (Equiv.swap i ⟨(i : ℕ) + 1, hlt⟩) v
  · have hltm : m - 1 < m := by omega
    have hi : i = ⟨m - 1, hltm⟩ := Fin.ext (by
      simp only [Fin.val_mk]
      have := i.isLt
      omega)
    subst hi
    have hbc := ggQ2_DW_r_eq_bc (m := m) hm ⟨m - 1, hltm⟩
    have hab : (⟨m - 2, by omega⟩ : Fin m) ≠ ⟨m - 1, hltm⟩ := by
      intro h; have := congrArg Fin.val h; simp only [Fin.val_mk] at this; omega
    have hvec : ggDSimple 3 m ⟨m - 1, hltm⟩ =
        (Pi.single ⟨m - 2, by omega⟩ (1 : ZMod 3) : GGBCV m) +
          Pi.single ⟨m - 1, hltm⟩ 1 := ggQ2xF1_dsimple_fork (m := m) (by omega)
    have hc' : ((Pi.single ⟨m - 2, by omega⟩ (1 : ZMod 3) : GGBCV m) +
        Pi.single ⟨m - 1, hltm⟩ 1) ⬝ᵥ
        ((Pi.single ⟨m - 2, by omega⟩ (1 : ZMod 3) : GGBCV m) +
          Pi.single ⟨m - 1, hltm⟩ 1) ≠ 0 := by
      rw [ggQ2_DW_add_norm _ _ hab]
      decide
    rw [hbc]
    rw [show ggBCRefl (ggDSimple 3 m ⟨m - 1, hltm⟩) _ =
        ggBCRefl ((Pi.single ⟨m - 2, by omega⟩ (1 : ZMod 3) : GGBCV m) +
          Pi.single ⟨m - 1, hltm⟩ 1) hc' from
      ggQ2_DW_refl_congr hvec _ hc']
    exact ggQ2xF1_add_refl_prod ⟨m - 2, by omega⟩ ⟨m - 1, hltm⟩ hab hc' v

private lemma ggQ2xF1_Dgp_eq_Wc {m : ℕ} (hm : 4 ≤ m) :
    ggBCReflGp (ggDRoots m) = ggQ2_DW_Wc 3 m hm := by
  apply le_antisymm
  · rw [ggBCReflGp, Subgroup.closure_le]
    rintro t ⟨c, hc, hcc, rfl⟩
    exact ggQ2_DW_Droot_refl_mem_Wc m hm hc hcc
  · rw [ggQ2_DW_Wc, Subgroup.closure_le]
    rintro t ⟨i, rfl⟩
    rw [ggQ2_DW_r_eq_bc hm i]
    exact Subgroup.subset_closure
      ⟨ggDSimple 3 m i, ggQ2xF1_dsimple_mem_D hm i,
        (by rw [ggQ2_DW_simple_norm hm i]; decide), rfl⟩

private lemma ggQ2xF1_Wc_prod {m : ℕ} (hm : 4 ≤ m)
    (g : GGBCV m ≃ₗ[ZMod 3] GGBCV m) (hg : g ∈ ggQ2_DW_Wc 3 m hm) :
    ∀ v, ggQ2xF1_prod (g v) = ggQ2xF1_prod v := by
  rw [ggQ2_DW_Wc] at hg
  refine Subgroup.closure_induction (fun x hx => ?_) ?_ ?_ ?_ hg
  · obtain ⟨i, rfl⟩ := hx
    intro v
    exact ggQ2xF1_r_prod hm i v
  · intro v; simp
  · intro x y hx hy ihx ihy v
    rw [LinearEquiv.mul_apply, ihx, ihy]
  · intro x hx ihx v
    have h := ihx (x.symm v)
    rw [LinearEquiv.apply_symm_apply x v] at h
    exact h.symm

private lemma ggQ2xF1_Lam1_prod {m : ℕ} [NeZero m] (hm : 5 ≤ m)
    (g : GGBCV m ≃ₗ[ZMod 3] GGBCV m) (hg : g ∈ ggBCReflGp (ggDRootsLam1 m)) :
    ∀ v, ggQ2xF1_prod (g v) = ggQ2xF1_prod v := by
  have hm4 : 4 ≤ m := by omega
  have hsub : ggBCReflGp (ggDRootsLam1 m) ≤ ggBCReflGp (ggDRoots m) :=
    Subgroup.closure_mono (fun t ht => by
      obtain ⟨c, hc, hcc, rfl⟩ := ht
      exact ⟨c, hc.1, hcc, rfl⟩)
  rw [ggQ2xF1_Dgp_eq_Wc hm4] at hsub
  exact ggQ2xF1_Wc_prod hm4 g (hsub hg)

private lemma ggQ2xF1_wt_one_flip {m : ℕ} [NeZero m] {c : GGBCV m}
    (hw : ggBCWt c = 1) (hc : c ⬝ᵥ c ≠ 0) :
    ∃ v : GGBCV m, ggQ2xF1_prod (ggBCRefl c hc v) ≠ ggQ2xF1_prod v := by
  obtain ⟨a, μ, hμ, rfl⟩ := ggQ2xF1_Wt_eq_one hw
  refine ⟨fun _ => (1 : ZMod 3), ?_⟩
  have himg : ggBCRefl (μ • Pi.single a 1) hc (fun _ => (1 : ZMod 3)) =
      ggQ2xF1_flipS {a} (fun _ => (1 : ZMod 3)) := by
    funext k
    rw [ggQ2x_ggBCRefl_apply, ggQ2xF1_flipS]
    have hcc : (μ • Pi.single a 1 : GGBCV m) ⬝ᵥ (μ • Pi.single a 1 : GGBCV m) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, single_one_dotProduct, Pi.single_eq_same,
        smul_eq_mul, smul_eq_mul, mul_one]
      exact ggQ2_DW_sq μ hμ
    have hcv : (μ • Pi.single a 1 : GGBCV m) ⬝ᵥ (fun _ => (1 : ZMod 3)) = μ := by
      rw [smul_dotProduct, single_one_dotProduct]
      simp
    rw [hcc, hcv]
    by_cases hka : k = a
    · rw [hka]
      rw [if_pos (by simp : (a : Fin m) ∈ ({a} : Finset (Fin m)))]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one]
      rw [ggQ2_DW_sq μ hμ]
      decide
    · rw [if_neg (by simpa [Finset.mem_singleton] using hka)]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hka]
      rw [mul_zero, mul_zero, add_zero]
  rw [himg, ggQ2xF1_prod_flipS_single a, ggQ2xF1_prod]
  have hone : ∏ i : Fin m, (fun _ => (1 : ZMod 3)) i = (1 : ZMod 3) := by simp
  rw [hone]
  decide

private theorem ggQ2xF1_Lam1_refl_D (m : ℕ) [NeZero m] (hm : 5 ≤ m)
    (t : GGBCV m ≃ₗ[ZMod 3] GGBCV m)
    (ht : t ∈ ggBCReflGp (ggDRootsLam1 m)) (hr : IsReflLin t) :
    t ∈ ggBCReflSet (ggDRootsLam1 m) := by
  have hsub : ggBCReflGp (ggDRootsLam1 m) ≤ ggBCReflGp (ggBCRootsLam1 m) :=
    Subgroup.closure_mono (fun t ht => by
      obtain ⟨c, hc, hcc, rfl⟩ := ht
      exact ⟨c, ⟨⟨by have := hc.1; omega, by have := hc.1; omega⟩, hc.2⟩, hcc, rfl⟩)
  obtain ⟨c, hc, hcc, hteq⟩ := ggQ2_bc_Lam1_refl m hm t (hsub ht) hr
  by_cases hw : ggBCWt c = 2
  · exact ⟨c, ⟨hw, hc.2⟩, hcc, hteq⟩
  · exfalso
    have hw1 : ggBCWt c = 1 := by
      have h1 := hc.1.1
      have h2 := hc.1.2
      omega
    obtain ⟨v, hv⟩ := ggQ2xF1_wt_one_flip (m := m) hw1 hcc
    have hpres := ggQ2xF1_Lam1_prod (m := m) hm t ht v
    rw [hteq] at hpres
    exact hv hpres

private def ggQ2xF1_Z {m : ℕ} (A' : Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m)) :
    Set (GGBCV m) :=
  {z | ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A'}

private theorem ggQ2xF1_Z0 {m : ℕ} (A' : Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m)) :
    ∀ z ∈ ggQ2xF1_Z A', z ⬝ᵥ z ≠ 0 := by
  rintro z ⟨hz, -⟩
  exact hz

private theorem ggQ2xF1_Zroots {m : ℕ} (A' : Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m))
    (hW' : ggBCReflGp (ggDRoots m) ≤ A') :
    ggDRoots m ⊆ ggQ2xF1_Z A' := by
  intro z hz
  have hz0 : z ⬝ᵥ z ≠ 0 := by
    rw [ggQ2x_dot_self_eq_wt, hz]
    decide
  exact ⟨hz0, hW' (Subgroup.subset_closure ⟨z, hz, hz0, rfl⟩)⟩

private lemma ggQ2xF1_conj_reflection {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (a : V ≃ₗ[ZMod 3] V) {ψ : Module.Dual (ZMod 3) V} {c : V} (h : ψ c = 2) :
    a * Module.reflection h * a.symm =
      Module.reflection (show (ψ.comp (a.symm : V →ₗ[ZMod 3] V)) (a c) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h) := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    Module.reflection_apply (a.symm w) h, Module.reflection_apply w]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2xF1_refl_eq_bc {m : ℕ} {c : GGBCV m}
    {φ : Module.Dual (ZMod 3) (GGBCV m)} (hφ : φ c = 2) (ε : ZMod 3)
    (hφv : ∀ v, φ v = ε * (c ⬝ᵥ v)) :
    ∃ hc : c ⬝ᵥ c ≠ 0, Module.reflection hφ = ggBCRefl c hc := by
  have hc : c ⬝ᵥ c ≠ 0 := by
    intro h0
    have h := hφv c
    rw [hφ, h0, mul_zero] at h
    exact two_ne_zero_of_charP_three h
  refine ⟨hc, ?_⟩
  have he : ε = 2 / (c ⬝ᵥ c) := by
    have h : ε * (c ⬝ᵥ c) = 2 := by rw [← hφv c, hφ]
    field_simp
    exact h
  let ψ : Module.Dual (ZMod 3) (GGBCV m) := (2 / (c ⬝ᵥ c)) • ggBCDot c
  have hf : φ = ψ := by
    apply LinearMap.ext
    intro v
    rw [hφv v, LinearMap.smul_apply, ggQ2x_ggBCDot_apply, he, smul_eq_mul]
  subst φ
  rfl

private theorem ggQ2xF1_Zcl {m : ℕ} (A' : Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m))
    (hS1 : ∀ (c : GGBCV m) (φ : Module.Dual (ZMod 3) (GGBCV m)) (h : φ c = 2),
      Module.reflection h ∈ A' → ∃ ε : ZMod 3,
        (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v)) :
    ∀ z ∈ ggQ2xF1_Z A', ∀ w ∈ ggQ2xF1_Z A', ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xF1_Z A' := by
  intro z hzZ w hwZ hz
  obtain ⟨hw0, hwA⟩ := hwZ
  have hzA : ggBCRefl z hz ∈ A' := by
    obtain ⟨hz0, hzA'⟩ := hzZ
    rw [show ggBCRefl z hz = ggBCRefl z hz0 from
      congrArg (fun h => ggBCRefl z h) (Subsingleton.elim hz hz0)]
    exact hzA'
  let e : GGBCV m ≃ₗ[ZMod 3] GGBCV m := ggBCRefl z hz
  let ψ : Module.Dual (ZMod 3) (GGBCV m) := (2 / (w ⬝ᵥ w)) • ggBCDot w
  have hψ : ψ w = 2 := by
    change (2 / (w ⬝ᵥ w)) * (ggBCDot w w) = 2
    rw [ggQ2x_ggBCDot_apply]
    field_simp
  let φ : Module.Dual (ZMod 3) (GGBCV m) := ψ.comp (e.symm : GGBCV m →ₗ[ZMod 3] GGBCV m)
  have hφ : φ (e w) = 2 := by
    change ψ (e.symm (e w)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hψ
  have hconj : e * Module.reflection hψ * e.symm = Module.reflection hφ :=
    ggQ2xF1_conj_reflection e hψ
  have htA : e * Module.reflection hψ * e.symm ∈ A' := by
    change ggBCRefl z hz * ggBCRefl w hw0 * (ggBCRefl z hz)⁻¹ ∈ A'
    exact A'.mul_mem (A'.mul_mem hzA hwA) (A'.inv_mem hzA)
  have hreflA : Module.reflection hφ ∈ A' := by
    rw [← hconj]
    exact htA
  obtain ⟨ε, hε, hφv⟩ := hS1 (e w) φ hφ hreflA
  obtain ⟨hc, heq⟩ := ggQ2xF1_refl_eq_bc hφ ε hφv
  refine ⟨hc, ?_⟩
  change ggBCRefl (e w) hc ∈ A'
  rw [← heq]
  exact hreflA

private lemma ggQ2xF1_bc_apply_self {m : ℕ} (c : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hc c = -c := by
  rw [ggQ2x_ggBCRefl_apply]
  have hsq : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := by
    have h : ∀ a : ZMod 3, a ≠ 0 → a * a = 1 := by decide
    exact h _ hc
  rw [hsq, one_smul, ← two_smul (ZMod 3) c]
  rw [show (2 : ZMod 3) = -1 by decide]
  exact neg_one_smul (ZMod 3) c

private lemma ggQ2xF1_bc_eq_span {m : ℕ} (c d : GGBCV m) (hc : c ⬝ᵥ c ≠ 0) (hd : d ⬝ᵥ d ≠ 0)
    (heq : ggBCRefl c hc = ggBCRefl d hd) :
    c ∈ Submodule.span (ZMod 3) {d} := by
  refine Submodule.mem_span_singleton.mpr ⟨(d ⬝ᵥ c) * (d ⬝ᵥ d), ?_⟩
  have h := congrArg (fun e : GGBCV m ≃ₗ[ZMod 3] GGBCV m => e c) heq
  rw [ggQ2xF1_bc_apply_self c hc, ggQ2x_ggBCRefl_apply d hd c] at h
  change ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = c
  have h1 : (2 : ZMod 3) • c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = 0 := by
    rw [two_smul]
    calc c + c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d
        = c + (c + ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d) := by rw [add_assoc]
      _ = c + (-c) := by rw [← h]
      _ = 0 := add_neg_cancel c
  have h2 : ((d ⬝ᵥ c) * (d ⬝ᵥ d)) • d = -((2 : ZMod 3) • c) :=
    eq_neg_of_add_eq_zero_right h1
  have h2c : (2 : ZMod 3) • c = -c := by
    rw [show (2 : ZMod 3) = -1 by decide]
    exact neg_one_smul (ZMod 3) c
  rw [h2c] at h2
  rw [h2]
  exact neg_neg c

private lemma ggQ2xF1_wt_smul {m : ℕ} (v : GGBCV m) (μ : ZMod 3) (hμ : μ ≠ 0) :
    ggBCWt (μ • v) = ggBCWt v := by
  rw [ggBCWt, ggBCWt]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [Pi.smul_apply, smul_eq_mul, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨hμ, h⟩⟩

private lemma ggQ2xF1_lam1_smul {m : ℕ} [NeZero m] {v : GGBCV m} (hv : v ∈ ggDRootsLam1 m)
    (μ : ZMod 3) (hμ : μ ≠ 0) : μ • v ∈ ggDRootsLam1 m := by
  simp only [ggDRootsLam1, Set.mem_setOf_eq] at hv ⊢
  refine ⟨?_, ?_⟩
  · rw [ggQ2xF1_wt_smul v μ hμ, hv.1]
  · rw [Pi.smul_apply, smul_eq_mul, hv.2, mul_zero]

private lemma ggQ2xF1_root_ne_zero {m : ℕ} {v : GGBCV m} (hv : v ∈ ggDRoots m) : v ≠ 0 := by
  intro h0
  have h2 : v ⬝ᵥ v = (2 : ZMod 3) := by
    have hv' : ggBCWt v = 2 := hv
    rw [ggQ2x_dot_self_eq_wt, hv']
    rfl
  rw [h0] at h2
  have hzero : (0 : GGBCV m) ⬝ᵥ (0 : GGBCV m) = 0 := by simp [dotProduct]
  rw [hzero] at h2
  exact (by decide : (0 : ZMod 3) ≠ 2) h2

private theorem ggQ2xF1_ZHL {m : ℕ} [NeZero m] (hm : 5 ≤ m)
    (A' : Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m))
    (hW' : ggBCReflGp (ggDRoots m) ≤ A')
    (hS1 : ∀ (c : GGBCV m) (φ : Module.Dual (ZMod 3) (GGBCV m)) (h : φ c = 2),
      Module.reflection h ∈ A' → ∃ ε : ZMod 3,
        (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hHL' : ∀ φ ∈ A', φ (Pi.single 0 1) ∈
        Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)} →
      φ ∈ Subgroup.normalizer (ggBCReflGp (ggDRootsLam1 m) :
        Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) :
    ∀ z ∈ ggQ2xF1_Z A', z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 m := by
  intro z hzZ hz0 ρ hρ hz
  have hzA : ggBCRefl z hz ∈ A' := by
    obtain ⟨hz', hzA'⟩ := hzZ
    rw [show ggBCRefl z hz = ggBCRefl z hz' from
      congrArg (fun h => ggBCRefl z h) (Subsingleton.elim hz hz')]
    exact hzA'
  have hfix : ggBCRefl z hz (Pi.single 0 1) ∈
      Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)} := by
    rw [ggQ2x_ggBCRefl_apply]
    have hdot : z ⬝ᵥ (Pi.single 0 1 : GGBCV m) = 0 := by
      rw [dotProduct_single, hz0, mul_one]
    rw [hdot, zero_mul, zero_smul, add_zero]
    exact Submodule.mem_span_singleton_self _
  have hnorm := hHL' (ggBCRefl z hz) hzA hfix
  have hρ0 : ρ ⬝ᵥ ρ ≠ 0 := by
    rw [ggQ2x_dot_self_eq_wt, hρ.1]; decide
  let e : GGBCV m ≃ₗ[ZMod 3] GGBCV m := ggBCRefl z hz
  let ψ : Module.Dual (ZMod 3) (GGBCV m) := (2 / (ρ ⬝ᵥ ρ)) • ggBCDot ρ
  have hψ : ψ ρ = 2 := by
    change (2 / (ρ ⬝ᵥ ρ)) * (ggBCDot ρ ρ) = 2
    rw [ggQ2x_ggBCDot_apply]; field_simp
  let φ : Module.Dual (ZMod 3) (GGBCV m) := ψ.comp (e.symm : GGBCV m →ₗ[ZMod 3] GGBCV m)
  have hφ : φ (e ρ) = 2 := by
    change ψ (e.symm (e ρ)) = 2
    rw [LinearEquiv.symm_apply_apply]; exact hψ
  have hconj : e * Module.reflection hψ * e.symm = Module.reflection hφ :=
    ggQ2xF1_conj_reflection e hψ
  have hρA : ggBCRefl ρ hρ0 ∈ A' :=
    hW' (Subgroup.subset_closure (show ggBCRefl ρ hρ0 ∈ ggBCReflSet (ggDRoots m) from
      ⟨ρ, hρ.1, hρ0, rfl⟩))
  have htA : e * Module.reflection hψ * e.symm ∈ A' := by
    change ggBCRefl z hz * ggBCRefl ρ hρ0 * (ggBCRefl z hz)⁻¹ ∈ A'
    exact A'.mul_mem (A'.mul_mem hzA hρA) (A'.inv_mem hzA)
  have hconjΛ : Module.reflection hφ ∈ ggBCReflGp (ggDRootsLam1 m) := by
    rw [← hconj]
    change ggBCRefl z hz * ggBCRefl ρ hρ0 * (ggBCRefl z hz)⁻¹ ∈ ggBCReflGp (ggDRootsLam1 m)
    exact (Subgroup.mem_normalizer_iff.mp hnorm (ggBCRefl ρ hρ0)).mp
      (Subgroup.subset_closure (show ggBCRefl ρ hρ0 ∈ ggBCReflSet (ggDRootsLam1 m) from
        ⟨ρ, hρ, hρ0, rfl⟩))
  have htRefl : IsReflLin (Module.reflection hφ) := ⟨e ρ, φ, hφ, rfl⟩
  obtain ⟨lam, hlam, hlam0, heqLam⟩ :=
    ggQ2xF1_Lam1_refl_D m hm (Module.reflection hφ) hconjΛ htRefl
  have hreflA : Module.reflection hφ ∈ A' := by
    rw [← hconj]
    exact htA
  obtain ⟨ε, hε, hφv⟩ := hS1 (e ρ) φ hφ hreflA
  obtain ⟨hc, heqρ⟩ := ggQ2xF1_refl_eq_bc hφ ε hφv
  have heq : ggBCRefl (e ρ) hc = ggBCRefl lam hlam0 := by rw [← heqρ, heqLam]
  have hspan : e ρ ∈ Submodule.span (ZMod 3) {lam} :=
    ggQ2xF1_bc_eq_span (e ρ) lam hc hlam0 heq
  obtain ⟨μ, hμ⟩ := Submodule.mem_span_singleton.mp hspan
  have heρ_ne : e ρ ≠ 0 := by
    intro h0
    have he0 : e 0 = 0 := by
      change ggBCRefl z hz 0 = 0
      rw [ggQ2x_ggBCRefl_apply]; simp
    have hρzero : ρ = 0 := by
      apply e.injective
      rw [h0, he0]
    exact ggQ2xF1_root_ne_zero hρ.1 hρzero
  have hμne : μ ≠ 0 := by
    intro h0
    apply heρ_ne
    rw [← hμ, h0, zero_smul]
  have hres := ggQ2xF1_lam1_smul hlam μ hμne
  rw [hμ] at hres
  exact hres

private theorem ggQ2xF1_Z_hyps {m : ℕ} [NeZero m] (hm : 6 ≤ m)
    (A' : Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m))
    (hW' : ggBCReflGp (ggDRoots m) ≤ A')
    (hS1 : ∀ (c : GGBCV m) (φ : Module.Dual (ZMod 3) (GGBCV m)) (h : φ c = 2),
      Module.reflection h ∈ A' → ∃ ε : ZMod 3,
        (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v))
    (hHL' : ∀ φ ∈ A', φ (Pi.single 0 1) ∈
        Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)} →
      φ ∈ Subgroup.normalizer (ggBCReflGp (ggDRootsLam1 m) :
        Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) :
    (∀ z ∈ ggQ2xF1_Z A', z ⬝ᵥ z ≠ 0) ∧
    (ggDRoots m ⊆ ggQ2xF1_Z A') ∧
    (∀ z ∈ ggQ2xF1_Z A', ∀ w ∈ ggQ2xF1_Z A', ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz w ∈ ggQ2xF1_Z A') ∧
    (∀ z ∈ ggQ2xF1_Z A', z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 m) :=
  ⟨ggQ2xF1_Z0 A', ggQ2xF1_Zroots A' hW', ggQ2xF1_Zcl A' hS1,
    ggQ2xF1_ZHL (m := m) (by omega) A' hW' hS1 hHL'⟩

private def ggQ2xF1_dotForm (m : ℕ) :
    LinearMap.BilinForm (ZMod 3) (GGBCV m) :=
  LinearMap.mk₂ (ZMod 3) (fun u v => ∑ i, u i * v i)
    (by intro u₁ u₂ v
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [add_mul]))
    (by intro a u v
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_assoc]))
    (by intro u v₁ v₂
        simp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_add]))
    (by intro a u v
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by rw [mul_left_comm]))

private lemma ggQ2xF1_dotForm_apply (m : ℕ) (u v : GGBCV m) :
    ggQ2xF1_dotForm m u v = ∑ i, u i * v i := by
  rw [ggQ2xF1_dotForm, LinearMap.mk₂_apply]

private theorem ggQ2xF1_S1 (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m)
    (hcor : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j) :
    ∀ (c : GGBCV m) (φ : Module.Dual (ZMod 3) (GGBCV m)) (h : φ c = 2),
      Module.reflection h ∈ A.map (ggLinConj τ).toMonoidHom →
      ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v) := by
  intro c φ h ht
  have h4 : 4 ≤ Fintype.card D.ι := by
    rw [← Fintype.card_congr e, Fintype.card_fin]; omega
  have hsym : ∀ i j, D.cartan i j = D.cartan j i := ggQ2xF1_cartan_symm D e hD
  have hB' : ∀ i j : D.ι,
      ggQ2xF1_dotForm m (τ (D.coroot i)) (τ (D.coroot j)) = (D.cartan i j : ZMod 3) := by
    intro i j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    rw [ggQ2xF1_dotForm_apply, hcor a, hcor b]
    have h1 := hroot a (D.coroot (e b))
    rw [D.pairing] at h1
    rw [hcor b] at h1
    exact h1.symm
  obtain ⟨ε, hε, hφ⟩ :=
    ggQ2_S1_transport D hbas h4 hsym τ (ggQ2xF1_dotForm m) hB' A hW hTF h ht
  refine ⟨ε, hε, fun v => ?_⟩
  have hdot : ggQ2xF1_dotForm m c v = c ⬝ᵥ v := by
    rw [ggQ2xF1_dotForm_apply]
    rfl
  exact (hφ v).trans (congrArg (fun x => ε * x) hdot)

private lemma ggQ2xF1_flipS_empty {m : ℕ} (v : GGBCV m) : ggQ2xF1_flipS ∅ v = v := by
  funext k; simp [ggQ2xF1_flipS]

private lemma ggQ2xF1_flipS_pair_apply {m : ℕ} (a b k : Fin m) (hab : a ≠ b) (v : GGBCV m) :
    ggQ2xF1_flipS ({a, b} : Finset (Fin m)) v k
      = if k = a then -v a else if k = b then -v b else v k := by
  simp only [ggQ2xF1_flipS, Finset.mem_insert, Finset.mem_singleton]
  by_cases hka : k = a
  · subst hka; simp
  · by_cases hkb : k = b
    · subst hkb; simp [hka]
    · simp [hka, hkb]

private lemma ggQ2xF1_mem_pair {m : ℕ} {Z : Set (GGBCV m)}
    (hZroots : ggDRoots m ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {v : GGBCV m} (hv : v ∈ Z) {a b : Fin m} (hab : a ≠ b) :
    ggQ2xF1_flipS {a, b} v ∈ Z := by
  have hc1 : (Pi.single a 1 - Pi.single b 1 : GGBCV m) ⬝ᵥ
      (Pi.single a 1 - Pi.single b 1) = 2 := ggQ2x_sub_single_norm a b hab
  have hc1ne : (Pi.single a 1 - Pi.single b 1 : GGBCV m) ⬝ᵥ
      (Pi.single a 1 - Pi.single b 1) ≠ 0 := by rw [hc1]; decide
  have hroot1 : (Pi.single a 1 - Pi.single b 1 : GGBCV m) ∈ ggDRoots m := by
    rw [ggDRoots]; exact ggQ2x_wt_sub_single a b hab
  have hc2 : (Pi.single a 1 + Pi.single b 1 : GGBCV m) ⬝ᵥ
      (Pi.single a 1 + Pi.single b 1) = 2 := by
    rw [ggQ2x_dot_self_eq_wt,
      ggQ2x_wt_single_add_single a b hab 1 1 one_ne_zero one_ne_zero]
    decide
  have hc2ne : (Pi.single a 1 + Pi.single b 1 : GGBCV m) ⬝ᵥ
      (Pi.single a 1 + Pi.single b 1) ≠ 0 := by rw [hc2]; decide
  have hroot2 : (Pi.single a 1 + Pi.single b 1 : GGBCV m) ∈ ggDRoots m := by
    rw [ggDRoots]
    exact ggQ2x_wt_single_add_single a b hab 1 1 one_ne_zero one_ne_zero
  have h1mem : ggBCRefl (Pi.single a 1 - Pi.single b 1) hc1ne v ∈ Z :=
    hZcl _ (hZroots hroot1) v hv hc1ne
  have h1eq : ggBCRefl (Pi.single a 1 - Pi.single b 1) hc1ne v =
      fun k => v (Equiv.swap a b k) := ggQ2x_refl_sub_single a b hab v hc1ne
  have h2mem : ggBCRefl (Pi.single a 1 + Pi.single b 1) hc2ne
      (ggBCRefl (Pi.single a 1 - Pi.single b 1) hc1ne v) ∈ Z :=
    hZcl _ (hZroots hroot2) _ h1mem hc2ne
  have hcomp : ggBCRefl (Pi.single a 1 + Pi.single b 1) hc2ne
      (ggBCRefl (Pi.single a 1 - Pi.single b 1) hc1ne v)
      = ggQ2xF1_flipS {a, b} v := by
    rw [h1eq]
    have hD : (Pi.single a 1 + Pi.single b 1 : GGBCV m) ⬝ᵥ
        (fun k => v (Equiv.swap a b k)) = v a + v b := by
      rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct]
      simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
      ring
    funext k
    rw [ggQ2x_ggBCRefl_apply, hD, hc2]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hka : k = a
    · rw [hka, ggQ2xF1_flipS_pair_apply a b a hab v, if_pos rfl, Equiv.swap_apply_left]
      simp only [Pi.add_apply, Pi.single_apply]
      rw [if_pos trivial, if_neg hab, add_zero, mul_one]
      exact ggQ2xF1_scalar_a (v a) (v b)
    · rw [ggQ2xF1_flipS_pair_apply a b k hab v, if_neg hka]
      by_cases hkb : k = b
      · rw [hkb, if_pos rfl, Equiv.swap_apply_right]
        simp only [Pi.add_apply, Pi.single_apply]
        rw [if_neg (Ne.symm hab), if_pos trivial, zero_add, mul_one]
        exact ggQ2xF1_scalar_b (v a) (v b)
      · rw [if_neg hkb, Equiv.swap_apply_of_ne_of_ne hka hkb]
        simp only [Pi.add_apply, Pi.single_apply]
        rw [if_neg hkb, if_neg hka, add_zero, mul_zero, add_zero]
  rw [hcomp] at h2mem
  exact h2mem

private lemma ggQ2xF1_mem_flipS {m : ℕ} {Z : Set (GGBCV m)}
    (hZroots : ggDRoots m ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z) :
    ∀ (S : Finset (Fin m)), Even S.card → ∀ {v : GGBCV m}, v ∈ Z →
      ggQ2xF1_flipS S v ∈ Z := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS v hv
    by_cases h0 : S.card = 0
    · rw [Finset.card_eq_zero.mp h0, ggQ2xF1_flipS_empty]
      exact hv
    · have h2 : 1 < S.card := by
        obtain ⟨k, hk⟩ := hS
        omega
      obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
      have hbU : b ∈ S.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
      have haU : a ∉ (S.erase a).erase b := by
        rw [Finset.mem_erase]
        push Not
        intro _; exact Finset.notMem_erase a S
      have hbU2 : b ∉ (S.erase a).erase b := Finset.notMem_erase b (S.erase a)
      have hUsub : (S.erase a).erase b ⊂ S :=
        (Finset.erase_ssubset hbU).trans (Finset.erase_ssubset ha)
      have hUeven : Even ((S.erase a).erase b).card := by
        have h1 : (S.erase a).card = S.card - 1 := Finset.card_erase_of_mem ha
        have h2' : ((S.erase a).erase b).card = (S.erase a).card - 1 :=
          Finset.card_erase_of_mem hbU
        rw [h2', h1]
        obtain ⟨k, hk⟩ := hS
        refine ⟨k - 1, ?_⟩
        omega
      have hseq : insert a (insert b ((S.erase a).erase b)) = S := by
        rw [Finset.insert_erase hbU, Finset.insert_erase ha]
      rw [← hseq]
      have hdisj : Disjoint ({a, b} : Finset (Fin m)) ((S.erase a).erase b) := by
        rw [Finset.disjoint_left]
        intro x hx hxU
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact haU hxU
        · exact hbU2 hxU
      have hins : insert a (insert b ((S.erase a).erase b)) =
          ({a, b} : Finset (Fin m)) ∪ ((S.erase a).erase b) := by
        ext x; simp [Finset.mem_union]
      rw [hins, ggQ2xF1_flipS_union _ _ hdisj]
      exact ggQ2xF1_mem_pair hZroots hZcl
        (ih ((S.erase a).erase b) hUsub hUeven hv) hab

private lemma ggQ2xF1_eq_neg_of_ne {a b : ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0) (h : a ≠ b) :
    b = -a := by
  rcases ggQ2_DW_eq_one_or_neg_one a ha with rfl | rfl <;>
    rcases ggQ2_DW_eq_one_or_neg_one b hb with rfl | rfl <;>
    simp_all

private lemma ggQ2xF1_neg_one_pow_or (k : ℕ) :
    (-1 : ZMod 3) ^ k = 1 ∨ (-1 : ZMod 3) ^ k = -1 := by
  induction k with
  | zero => left; simp
  | succ k ih =>
    rw [pow_succ]
    rcases ih with h | h
    · right; rw [h, one_mul]
    · left; rw [h]; norm_num

private lemma ggQ2xF1_prod_eq_neg_one_pow_card {m : ℕ} (v : GGBCV m) (hv : ∀ i, v i ≠ 0) :
    ggQ2xF1_prod v = (-1 : ZMod 3) ^ (Finset.univ.filter (fun i => v i = -1)).card := by
  rw [ggQ2xF1_prod]
  rw [show (∏ i, v i) = ∏ i, (if v i = -1 then (-1 : ZMod 3) else 1) from
    Finset.prod_congr rfl (fun i _ => by
      rcases ggQ2_DW_eq_one_or_neg_one (v i) (hv i) with h | h
      · rw [h]; simp
      · rw [h]; simp)]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp

private lemma ggQ2xF1_prod_congr_of_even {m : ℕ} {v w : GGBCV m}
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0)
    (h : Even (Finset.univ.filter (fun i => v i = -1)).card ↔
      Even (Finset.univ.filter (fun i => w i = -1)).card) :
    ggQ2xF1_prod v = ggQ2xF1_prod w := by
  rw [ggQ2xF1_prod_eq_neg_one_pow_card v hv, ggQ2xF1_prod_eq_neg_one_pow_card w hw]
  by_cases hk : Even (Finset.univ.filter (fun i => v i = -1)).card
  · rw [(neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mpr hk,
      (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mpr (h.mp hk)]
  · have hk1 : (-1 : ZMod 3) ^ (Finset.univ.filter (fun i => v i = -1)).card ≠ 1 :=
      fun hh => hk ((neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hh)
    have hk2 : (-1 : ZMod 3) ^ (Finset.univ.filter (fun i => w i = -1)).card ≠ 1 :=
      fun hh => hk (h.mpr ((neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hh))
    rcases ggQ2xF1_neg_one_pow_or (Finset.univ.filter (fun i => v i = -1)).card with h' | h'
    · exact absurd h' hk1
    · rcases ggQ2xF1_neg_one_pow_or (Finset.univ.filter (fun i => w i = -1)).card with h'' | h''
      · exact absurd h'' hk2
      · rw [h', h'']

private lemma ggQ2xF1_nonzero_of_wt {m : ℕ} {v : GGBCV m} (h : ggBCWt v = m) :
    ∀ i, v i ≠ 0 := by
  intro i hi
  have hcard : (Finset.univ.filter (fun j => v j ≠ 0)).card = Fintype.card (Fin m) := by
    rw [← ggBCWt, h, Fintype.card_fin]
  have hfilt := Finset.eq_univ_of_card (Finset.univ.filter (fun j => v j ≠ 0)) hcard
  have : i ∈ Finset.univ.filter (fun j => v j ≠ 0) := by rw [hfilt]; simp
  have hvi : v i ≠ 0 := by simpa using this
  exact hvi hi

private lemma ggQ2xF1_flipS_single_apply {m : ℕ} (a : Fin m) (v : GGBCV m) (i : Fin m) :
    ggQ2xF1_flipS ({a} : Finset (Fin m)) v i = if i = a then -v i else v i := by
  rw [ggQ2xF1_flipS]
  by_cases h : i = a
  · simp [h]
  · simp [h, Finset.mem_singleton]

private lemma ggQ2xF1_wt_flipS_single {m : ℕ} (a : Fin m) (v : GGBCV m) :
    ggBCWt (ggQ2xF1_flipS ({a} : Finset (Fin m)) v) = ggBCWt v := by
  rw [ggBCWt, ggBCWt]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i _
  rw [ggQ2xF1_flipS_single_apply]
  by_cases h : i = a
  · rw [if_pos h]; simp [neg_ne_zero]
  · rw [if_neg h]

private lemma ggQ2xF1_smul_single_refl {m : ℕ} (a : Fin m) (μ : ZMod 3) (hμ : μ ≠ 0)
    (hc : (μ • Pi.single a 1 : GGBCV m) ⬝ᵥ (μ • Pi.single a 1 : GGBCV m) ≠ 0)
    (v : GGBCV m) :
    ggBCRefl (μ • Pi.single a 1) hc v = ggQ2xF1_flipS ({a} : Finset (Fin m)) v := by
  have hsq : μ * μ = 1 := ggQ2_DW_sq μ hμ
  have hcc : (μ • Pi.single a 1 : GGBCV m) ⬝ᵥ (μ • Pi.single a 1 : GGBCV m) = 1 := by
    rw [smul_dotProduct, dotProduct_smul, single_one_dotProduct, Pi.single_eq_same,
      smul_eq_mul, smul_eq_mul, mul_one]
    exact hsq
  have hcv : (μ • Pi.single a 1 : GGBCV m) ⬝ᵥ v = μ * v a := by
    rw [smul_dotProduct, single_one_dotProduct, smul_eq_mul]
  funext i
  rw [ggQ2x_ggBCRefl_apply, hcc, hcv, ggQ2xF1_flipS_single_apply]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hia : i = a
  · rw [hia, if_pos rfl, Pi.single_eq_same]
    have e : v a + (μ * v a) * 1 * (μ * 1) = v a + v a := by
      rw [mul_one, mul_one, mul_assoc, mul_comm (v a) μ, ← mul_assoc, hsq, one_mul]
    have h2 : v a + v a = -v a := by
      have h21 : (2 : ZMod 3) = -1 := by decide
      rw [← two_mul, h21, neg_one_mul]
    rw [e, h2]
  · rw [if_neg (by simpa [Finset.mem_singleton] using hia),
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hia]
    rw [mul_zero, mul_zero, add_zero]

private lemma ggQ2xF1_even_not_of_prod_neg {m : ℕ} {v w : GGBCV m}
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0) (h : ggQ2xF1_prod v = -ggQ2xF1_prod w) :
    ¬ (Even (Finset.univ.filter (fun i => v i = -1)).card ↔
      Even (Finset.univ.filter (fun i => w i = -1)).card) := by
  intro hiff
  have hp : ggQ2xF1_prod v = ggQ2xF1_prod w :=
    ggQ2xF1_prod_congr_of_even (v := v) (w := w) hv hw hiff
  rw [hp] at h
  have hw0 : ggQ2xF1_prod w ≠ 0 := by
    rw [ggQ2xF1_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hw i)
  have h2 : (2 : ZMod 3) * ggQ2xF1_prod w = 0 := by
    have hh : ggQ2xF1_prod w + ggQ2xF1_prod w = 0 := by
      nth_rewrite 1 [h]
      rw [neg_add_cancel]
    rwa [two_mul]
  exact hw0 ((mul_eq_zero.mp h2).resolve_left (by decide))

private lemma ggQ2xF1_wt_cases {m : ℕ} [NeZero m] (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0)
    (hwt : ∀ z ∈ Z, ggBCWt z ≤ 2 ∨ (m = 8 ∧ ggBCWt z = 8)) :
    ∀ z ∈ Z, ggBCWt z = 1 ∨ ggBCWt z = 2 ∨ (m = 8 ∧ ggBCWt z = 8) := by
  intro z hzZ
  have hne : ggBCWt z ≠ 0 := by
    intro h
    exact hZ0 z hzZ (by rw [ggQ2x_dot_self_eq_wt, h]; rfl)
  rcases hwt z hzZ with h | h
  · omega
  · exact Or.inr (Or.inr h)

private lemma ggQ2xF1_wt2_iff {m : ℕ} {Z : Set (GGBCV m)} (hZroots : ggDRoots m ⊆ Z)
    {z : GGBCV m} : (z ∈ Z ∧ ggBCWt z = 2) ↔ z ∈ ggDRoots m :=
  ⟨fun h => h.2, fun h => ⟨hZroots h, h⟩⟩

private lemma ggQ2xF1_wt1_all {m : ℕ} [NeZero m] {Z : Set (GGBCV m)}
    (hZroots : ggDRoots m ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {u : GGBCV m} (huZ : u ∈ Z) (hu1 : ggBCWt u = 1) :
    ∀ w : GGBCV m, ggBCWt w = 1 → w ∈ Z := by
  obtain ⟨i, c, hc, rfl⟩ := ggQ2xF1_Wt_eq_one hu1
  have hcj : ∀ j, c • (Pi.single j 1 : GGBCV m) ∈ Z := by
    intro j
    by_cases hji : j = i
    · subst hji; exact huZ
    · have hroot : (Pi.single i 1 - Pi.single j 1 : GGBCV m) ∈ ggDRoots m := by
        rw [ggDRoots]; exact ggQ2x_wt_sub_single i j (Ne.symm hji)
      have hcroot : (Pi.single i 1 - Pi.single j 1 : GGBCV m) ⬝ᵥ
          (Pi.single i 1 - Pi.single j 1) ≠ 0 := by
        rw [ggQ2x_sub_single_norm i j (Ne.symm hji)]; decide
      have hmem := hZcl _ (hZroots hroot) (c • Pi.single i 1) huZ hcroot
      rw [ggQ2_DW_sub_refl_eq_swap i j (Ne.symm hji) hcroot] at hmem
      have heq : ggQ2_DW_Q 3 m (Equiv.swap i j) (c • Pi.single i 1) =
          c • (Pi.single j 1 : GGBCV m) := by
        change ggQ2_DW_Q 3 m (Equiv.swap i j) (c • ggQ2_DW_fvec 3 m i) =
          c • ggQ2_DW_fvec 3 m j
        rw [map_smul, ggQ2_DW_Q_fvec, Equiv.swap_apply_left]
      rwa [heq] at hmem
  have hnegj : ∀ j, -(c • (Pi.single j 1 : GGBCV m)) ∈ Z := by
    intro j
    have hcj0 : (c • Pi.single j 1 : GGBCV m) ⬝ᵥ (c • Pi.single j 1 : GGBCV m) ≠ 0 := by
      rw [smul_dotProduct, dotProduct_smul, single_one_dotProduct, Pi.single_eq_same,
        smul_eq_mul, smul_eq_mul, mul_one, ggQ2_DW_sq c hc]
      decide
    have h := hZcl _ (hcj j) _ (hcj j) hcj0
    rwa [ggQ2xF1_bc_apply_self (c • Pi.single j 1) hcj0] at h
  intro w hw1
  obtain ⟨j, d, hd, rfl⟩ := ggQ2xF1_Wt_eq_one hw1
  have hdc : d * c⁻¹ = 1 ∨ d * c⁻¹ = -1 :=
    ggQ2_DW_eq_one_or_neg_one _ (mul_ne_zero hd (inv_ne_zero hc))
  have hw_eq : d • (Pi.single j 1 : GGBCV m) =
      (d * c⁻¹) • (c • (Pi.single j 1 : GGBCV m)) := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  rw [hw_eq]
  rcases hdc with h | h
  · rw [h, one_smul]; exact hcj j
  · rw [h, neg_one_smul]; exact hnegj j

private lemma ggQ2xF1_prod_flipS {m : ℕ} (S : Finset (Fin m)) (v : GGBCV m) :
    ggQ2xF1_prod (ggQ2xF1_flipS S v) = (-1 : ZMod 3) ^ S.card * ggQ2xF1_prod v := by
  induction S using Finset.induction_on with
  | empty => rw [ggQ2xF1_flipS_empty, Finset.card_empty, pow_zero, one_mul]
  | insert a S ha ih =>
    rw [show ggQ2xF1_flipS (insert a S) v = ggQ2xF1_flipS {a} (ggQ2xF1_flipS S v) from
        ggQ2xF1_flipS_union {a} S (by simp [ha]) v,
      ggQ2xF1_prod_flipS_single, ih, Finset.card_insert_of_notMem ha, pow_succ]
    ring

private lemma ggQ2xF1_full_class {m : ℕ} {Z : Set (GGBCV m)}
    (hZroots : ggDRoots m ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {z : GGBCV m} (hzZ : z ∈ Z) (hznz : ∀ i, z i ≠ 0) :
    ∀ w : GGBCV m, (∀ i, w i ≠ 0) →
      (Even (Finset.univ.filter (fun i => z i = -1)).card ↔
        Even (Finset.univ.filter (fun i => w i = -1)).card) → w ∈ Z := by
  intro w hwnz hpar
  let S : Finset (Fin m) := Finset.univ.filter (fun i => z i ≠ w i)
  have hflip : ggQ2xF1_flipS S z = w := by
    funext i
    rw [ggQ2xF1_flipS]
    by_cases hi : i ∈ S
    · rw [if_pos hi]
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact (ggQ2xF1_eq_neg_of_ne (hznz i) (hwnz i) hi).symm
    · rw [if_neg hi]
      by_contra hne
      exact hi (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact hne)
  have hSe : Even S.card := by
    have hprod : (-1 : ZMod 3) ^ S.card * ggQ2xF1_prod z = ggQ2xF1_prod z := by
      rw [← ggQ2xF1_prod_flipS S z, hflip]
      exact (ggQ2xF1_prod_congr_of_even (v := z) (w := w) hznz hwnz hpar).symm
    have hz0 : ggQ2xF1_prod z ≠ 0 := by
      rw [ggQ2xF1_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun i _ => hznz i)
    have h1 : (-1 : ZMod 3) ^ S.card = 1 := by
      apply mul_right_cancel₀ hz0
      rw [hprod, one_mul]
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp h1
  rw [← hflip]
  exact ggQ2xF1_mem_flipS hZroots hZcl S hSe hzZ

private lemma ggQ2xF1_wt1_not_full {m : ℕ} [NeZero m] {Z : Set (GGBCV m)}
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    {u z : GGBCV m} (huZ : u ∈ Z) (hu1 : ggBCWt u = 1) (hzZ : z ∈ Z)
    (hzm : ggBCWt z = m)
    (hpar : ∀ z ∈ Z, ∀ w ∈ Z, ggBCWt z = m → ggBCWt w = m →
      (Even (Finset.univ.filter (fun i => z i = -1)).card ↔
        Even (Finset.univ.filter (fun i => w i = -1)).card)) : False := by
  obtain ⟨a, c, hc, rfl⟩ := ggQ2xF1_Wt_eq_one hu1
  have hz00 : (c • Pi.single a 1 : GGBCV m) ⬝ᵥ (c • Pi.single a 1 : GGBCV m) ≠ 0 := by
    rw [smul_dotProduct, dotProduct_smul, single_one_dotProduct, Pi.single_eq_same,
      smul_eq_mul, smul_eq_mul, mul_one, ggQ2_DW_sq c hc]
    decide
  have hreflZ : ggBCRefl (c • Pi.single a 1) hz00 z ∈ Z := hZcl _ huZ z hzZ hz00
  have hflip := ggQ2xF1_smul_single_refl a c hc hz00 z
  have hznz : ∀ i, z i ≠ 0 := ggQ2xF1_nonzero_of_wt hzm
  have hrznz : ∀ i, ggBCRefl (c • Pi.single a 1) hz00 z i ≠ 0 := by
    intro i
    rw [hflip, ggQ2xF1_flipS_single_apply]
    by_cases h : i = a
    · rw [if_pos h]; simpa [neg_ne_zero] using hznz i
    · rw [if_neg h]; exact hznz i
  have hwt' : ggBCWt (ggBCRefl (c • Pi.single a 1) hz00 z) = m := by
    rw [hflip, ggQ2xF1_wt_flipS_single]
    exact hzm
  have hprodneg : ggQ2xF1_prod (ggBCRefl (c • Pi.single a 1) hz00 z) = -ggQ2xF1_prod z := by
    rw [hflip, ggQ2xF1_prod_flipS_single]
  exact ggQ2xF1_even_not_of_prod_neg hrznz hznz hprodneg
    (hpar _ hreflZ _ hzZ hwt' hzm)

private lemma ggQ2xF1_even_iff_of_prod_eq {m : ℕ} {v w : GGBCV m}
    (hv : ∀ i, v i ≠ 0) (hw : ∀ i, w i ≠ 0) (h : ggQ2xF1_prod v = ggQ2xF1_prod w) :
    (Even (Finset.univ.filter (fun i => v i = -1)).card ↔
      Even (Finset.univ.filter (fun i => w i = -1)).card) := by
  have h' : (-1 : ZMod 3) ^ (Finset.univ.filter (fun i => v i = -1)).card =
      (-1 : ZMod 3) ^ (Finset.univ.filter (fun i => w i = -1)).card := by
    rw [← ggQ2xF1_prod_eq_neg_one_pow_card v hv,
      ← ggQ2xF1_prod_eq_neg_one_pow_card w hw]
    exact h
  rw [← neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1),
    ← neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1), h']

private theorem ggQ2xF1_Z_cases {m : ℕ} [NeZero m] (hm : 6 ≤ m) (Z : Set (GGBCV m))
    (hZ0 : ∀ z ∈ Z, z ⬝ᵥ z ≠ 0) (hZroots : ggDRoots m ⊆ Z)
    (hZcl : ∀ z ∈ Z, ∀ w ∈ Z, ∀ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz w ∈ Z)
    (hHL : ∀ z ∈ Z, z 0 = 0 → ∀ ρ ∈ ggDRootsLam1 m, ∀ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ρ ∈ ggDRootsLam1 m) :
    Z = ggDRoots m ∨
    Z = ggDRoots m ∪ {z | ggBCWt z = 1} ∨
    (m = 8 ∧ ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
      Z = ggDRoots m ∪ {z | ggDHalfSpin ε z}) := by
  obtain ⟨hwt, hpar⟩ := ggQ2_D_Z_a1 m hm Z hZ0 hZroots hZcl hHL
  have hcases := ggQ2xF1_wt_cases Z hZ0 hwt
  by_cases h1 : ∃ u ∈ Z, ggBCWt u = 1
  · right; left
    obtain ⟨u, huZ, hu1⟩ := h1
    have hall1 := ggQ2xF1_wt1_all hZroots hZcl huZ hu1
    have hnov : ∀ v ∈ Z, ggBCWt v ≠ m := by
      intro v hvZ hvm
      exact ggQ2xF1_wt1_not_full hZcl huZ hu1 hvZ hvm hpar
    have hsub : Z ⊆ ggDRoots m ∪ {z | ggBCWt z = 1} := by
      intro z hzZ
      rcases hcases z hzZ with h | h | h
      · exact Or.inr h
      · exact Or.inl h
      · exact absurd (h.2.trans h.1.symm) (hnov z hzZ)
    have hsup : ggDRoots m ∪ {z | ggBCWt z = 1} ⊆ Z := by
      intro z hz
      rcases hz with hz | hz
      · exact hZroots hz
      · exact hall1 z hz
    exact le_antisymm hsub hsup
  · push Not at h1
    by_cases h8 : ∃ z ∈ Z, ggBCWt z = 8
    · right; right
      obtain ⟨z0, hz0Z, hz08⟩ := h8
      have hm8 : m = 8 := by
        rcases hwt z0 hz0Z with h | ⟨h, -⟩
        · exfalso; omega
        · exact h
      have hz0m : ggBCWt z0 = m := by rw [hz08, hm8]
      have hz0nz : ∀ i, z0 i ≠ 0 := ggQ2xF1_nonzero_of_wt hz0m
      refine ⟨hm8, ggQ2xF1_prod z0, ?_, ?_⟩
      · rw [ggQ2xF1_prod_eq_neg_one_pow_card z0 hz0nz]
        exact ggQ2xF1_neg_one_pow_or _
      · apply le_antisymm
        · intro z hzZ
          rcases hcases z hzZ with h | h | h
          · exact absurd h (h1 z hzZ)
          · exact Or.inl h
          · right
            have hzm : ggBCWt z = m := h.2.trans h.1.symm
            have hznz : ∀ i, z i ≠ 0 := ggQ2xF1_nonzero_of_wt hzm
            refine ⟨hznz, ?_⟩
            exact ggQ2xF1_prod_congr_of_even (v := z) (w := z0) hznz hz0nz
              (hpar z hzZ z0 hz0Z hzm hz0m)
        · intro z hz
          rcases hz with hz | hz
          · exact hZroots hz
          · obtain ⟨hznz, hzprod⟩ := hz
            exact ggQ2xF1_full_class hZroots hZcl hz0Z hz0nz z hznz
              (ggQ2xF1_even_iff_of_prod_eq (v := z) (w := z0) hznz hz0nz hzprod).symm
    · left
      apply le_antisymm
      · intro z hzZ
        rcases hcases z hzZ with h | h | h
        · exact absurd h (h1 z hzZ)
        · exact h
        · exact absurd ⟨z, hzZ, h.2⟩ h8
      · exact hZroots

private lemma ggQ2xF1_tau_x (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} [NeZero m] (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (ha : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x}) :
    Submodule.span (ZMod 3) {τ x} =
      Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)} := by
  have hparab := ggQ2xF1_parab_lam1 D (show 4 ≤ m by omega) e ha τ hτ hroot
  have hsub : Submodule.span (ZMod 3) {τ x} ≤
      Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)} := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    change τ x ∈ Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)}
    rw [← (ggQ2xF1_fixed_lam1 hm (τ x))]
    intro g hg
    have hg' : g ∈ Subgroup.map (ggLinConj τ).toMonoidHom (D.parab {k | k ≠ D.a}) := by
      rw [hparab]; exact hg
    obtain ⟨g', hg'P, rfl⟩ := Subgroup.mem_map.mp hg'
    have hfix : g' x = x := ((hx x).mpr (Submodule.mem_span_singleton_self x)) g' hg'P
    change (ggLinConj τ g') (τ x) = τ x
    rw [ggLinConj_apply, LinearEquiv.symm_apply_apply, hfix]
  refine le_antisymm hsub ?_
  rw [Submodule.span_le, Set.singleton_subset_iff]
  have hfix : ∀ t ∈ ggBCReflGp (ggDRootsLam1 m),
      t (Pi.single 0 1 : GGBCV m) = Pi.single 0 1 :=
    (ggQ2xF1_fixed_lam1 hm (Pi.single 0 1)).mpr (Submodule.mem_span_singleton_self _)
  have hpre : τ.symm (Pi.single 0 1 : GGBCV m) ∈ Submodule.span (ZMod 3) {x} := by
    rw [← hx]
    intro g hg
    have hg' : ggLinConj τ g ∈ ggBCReflGp (ggDRootsLam1 m) := by
      rw [← hparab]; exact ⟨g, hg, rfl⟩
    have hthis := hfix (ggLinConj τ g) hg'
    rw [ggLinConj_apply] at hthis
    apply τ.injective
    rw [hthis, LinearEquiv.apply_symm_apply]
  obtain ⟨a, ha'⟩ := Submodule.mem_span_singleton.mp hpre
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  have : a • τ x = τ (a • x) := by rw [map_smul]
  rw [this, ha', LinearEquiv.apply_symm_apply]

private lemma ggQ2xF1_HL (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} [NeZero m] (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (ha : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V))
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ A.map (ggLinConj τ).toMonoidHom,
      φ (Pi.single 0 1 : GGBCV m) ∈
        Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)} →
      φ ∈ Subgroup.normalizer
        (ggBCReflGp (ggDRootsLam1 m) : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m)) := by
  have hspan := ggQ2xF1_tau_x D hbas hm e hD τ hτ hroot ha x hx
  have hparab := ggQ2xF1_parab_lam1 D (show 4 ≤ m by omega) e ha τ hτ hroot
  intro φ hφ hφone
  have hτx : τ x ∈ Submodule.span (ZMod 3) {(Pi.single 0 1 : GGBCV m)} := by
    rw [← hspan]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hτx
  have hφτ : φ (τ x) ∈ Submodule.span (ZMod 3) {τ x} := by
    rw [hspan, ← hc, map_smul]
    exact Submodule.smul_mem _ c hφone
  have hmem := (ggLinConj_HL τ A (D.parab {k | k ≠ D.a}) x).mpr hHL φ hφ hφτ
  rwa [hparab] at hmem

private lemma ggQ2xF1_alg (a : ZMod 3) (ha : a * a = 1) : 2 * a + a * (a * a) = 0 := by
  have h3 : (3 : ZMod 3) = 0 := by decide
  linear_combination a * ha + a * h3

private lemma ggQ2xF1_isometry {n : ℕ} (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0) (u v : GGBCV n) :
    (ggBCRefl z hz).toFun u ⬝ᵥ (ggBCRefl z hz).toFun v = u ⬝ᵥ v := by
  rw [ggQ2_DW_bc_apply, ggQ2_DW_bc_apply]
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm u z]
  have h0 : z ⬝ᵥ u * (z ⬝ᵥ z) * (z ⬝ᵥ v)
      + z ⬝ᵥ v * (z ⬝ᵥ z) * (z ⬝ᵥ u + z ⬝ᵥ u * (z ⬝ᵥ z) * (z ⬝ᵥ z)) = 0 := by
    linear_combination (z ⬝ᵥ u * (z ⬝ᵥ v)) *
      ggQ2xF1_alg (z ⬝ᵥ z) (ggQ2_DW_sq (z ⬝ᵥ z) hz)
  rw [add_assoc, h0, add_zero]

private lemma ggQ2xF1_wt_single_of_ne_zero {n : ℕ} (i : Fin n) (s : ZMod 3) (hs : s ≠ 0) :
    ggBCWt (Pi.single i s : GGBCV n) = 1 := by
  unfold ggBCWt
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hne
    exact hj (Pi.single_eq_of_ne (M := fun _ => ZMod 3) hne s)
  · rintro rfl
    rw [Pi.single_eq_same]
    exact hs

private lemma ggQ2xF1_wt_eq_one_iff {n : ℕ} {v : GGBCV n} :
    ggBCWt v = 1 ↔ ∃ i s, s ≠ 0 ∧ v = Pi.single i s := by
  constructor
  · intro hv
    unfold ggBCWt at hv
    obtain ⟨i, h⟩ := Finset.card_eq_one.mp hv
    refine ⟨i, v i, ?_, ?_⟩
    · have : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by
        rw [h]; exact Finset.mem_singleton_self i
      simpa using this
    · ext k
      by_cases hk : k = i
      · subst hk; rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
        have : k ∉ Finset.univ.filter (fun l => v l ≠ 0) := by
          rw [h]; simp [hk]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using this
  · rintro ⟨i, s, hs, rfl⟩
    exact ggQ2xF1_wt_single_of_ne_zero i s hs

private lemma ggQ2xF1_refl_conj_isom {n : ℕ} (a : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (z : GGBCV n) (hz : z ⬝ᵥ z ≠ 0)
    (ha : ∀ u v, (a u) ⬝ᵥ (a v) = u ⬝ᵥ v) :
    ∃ hz' : (a z) ⬝ᵥ (a z) ≠ 0, a * ggBCRefl z hz * a.symm = ggBCRefl (a z) hz' := by
  have haz : (a z) ⬝ᵥ (a z) ≠ 0 := by rw [ha z z]; exact hz
  refine ⟨haz, ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2_DW_bc_apply', ggQ2_DW_bc_apply',
    map_add, LinearEquiv.apply_symm_apply, map_smul]
  have h1 : (a z) ⬝ᵥ v = z ⬝ᵥ a.symm v := by
    calc (a z) ⬝ᵥ v = (a z) ⬝ᵥ a (a.symm v) := by rw [LinearEquiv.apply_symm_apply]
      _ = z ⬝ᵥ a.symm v := ha z (a.symm v)
  have h2 : (a z) ⬝ᵥ (a z) = z ⬝ᵥ z := ha z z
  rw [h1, h2]

private lemma ggQ2xF1_dotLin_add_left (p m : ℕ) (u w v : Fin m → ZMod p) :
    ggQ2_DW_dotLin p m (u + w) v = ggQ2_DW_dotLin p m u v + ggQ2_DW_dotLin p m w v := by
  simp only [ggQ2_DW_dotLin_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => by simp only [Pi.add_apply]; ring)

private lemma ggQ2xF1_dotLin_fvec_fvec (p m : ℕ) (a b : Fin m) :
    ggQ2_DW_dotLin p m (ggQ2_DW_fvec p m a) (ggQ2_DW_fvec p m b) =
      if a = b then (1:ZMod p) else 0 := by
  rw [ggQ2_DW_dotLin_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · simp [ggQ2_DW_fvec]
    · intro c _ hc; rw [ggQ2_DW_fvec, Pi.single_eq_of_ne hc]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh
  · rw [if_neg h, Finset.sum_eq_single a]
    · rw [ggQ2_DW_fvec, ggQ2_DW_fvec, Pi.single_eq_same, Pi.single_eq_of_ne h]
      ring
    · intro c _ hc; rw [ggQ2_DW_fvec, Pi.single_eq_of_ne hc]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh

private lemma ggQ2xF1_refl_smul {n : ℕ} (l : ZMod 3) (hl : l ≠ 0) (c : GGBCV n)
    (hc : c ⬝ᵥ c ≠ 0) (hlc : (l • c) ⬝ᵥ (l • c) ≠ 0) :
    ggBCRefl (l • c) hlc = ggBCRefl c hc := by
  rcases ggQ2_DW_eq_one_or_neg_one l hl with rfl | rfl
  · exact ggQ2_DW_refl_congr (one_smul (ZMod 3) c) hlc hc
  · exact (ggQ2_DW_refl_congr (neg_one_smul (ZMod 3) c) hlc
      (by rw [ggQ2_DW_neg_dot_self]; exact hc)).trans (ggQ2_DW_refl_neg c hc _)

private lemma ggQ2xF1_bc_refl_invol {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0)
    (v : GGBCV n) : ggBCRefl c hc (ggBCRefl c hc v) = v := by
  have hψ : ((2 / (c ⬝ᵥ c)) • ggBCDot c : Module.Dual (ZMod 3) (GGBCV n)) c = 2 := by
    rw [LinearMap.smul_apply, ggQ2_DW_dot_apply, smul_eq_mul]
    exact div_mul_cancel₀ 2 hc
  have h1 : ggBCRefl c hc = Module.reflection hψ := by
    unfold ggBCRefl
    congr 1
  simpa [h1] using Module.involutive_reflection hψ v

private lemma ggQ2xF1_bc_refl_mul_self {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hc * ggBCRefl c hc = 1 := by
  apply LinearEquiv.ext
  intro v
  rw [LinearEquiv.mul_apply]
  change ggBCRefl c hc (ggBCRefl c hc v) = v
  exact ggQ2xF1_bc_refl_invol c hc v

private lemma ggQ2xF1_single_dot_left {m : ℕ} (i : Fin m) (v : GGBCV m) :
    (Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ v = v i := by
  change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i) v = v i
  exact ggQ2_DW_dotLin_fvec_left 3 m i v

private lemma ggQ2xF1_single_dot_self {m : ℕ} (i : Fin m) :
    (Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ Pi.single i 1 = 1 := by
  change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i) (ggQ2_DW_fvec 3 m i) = 1
  rw [ggQ2xF1_dotLin_fvec_fvec]; simp

private lemma ggQ2xF1_short_ne {m : ℕ} (i : Fin m) :
    (Pi.single i (1 : ZMod 3) : GGBCV m) ⬝ᵥ Pi.single i 1 ≠ 0 := by
  rw [ggQ2xF1_single_dot_self]; decide

private noncomputable def ggQ2xF1_short {m : ℕ} (i : Fin m) :
    GGBCV m ≃ₗ[ZMod 3] GGBCV m :=
  ggBCRefl (Pi.single i (1 : ZMod 3)) (ggQ2xF1_short_ne i)

private lemma ggQ2xF1_short_apply {m : ℕ} (i : Fin m) (v : GGBCV m) :
    ggQ2xF1_short i v = v + (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) := by
  rw [ggQ2xF1_short, ggQ2_DW_bc_apply', ggQ2xF1_single_dot_left, ggQ2xF1_single_dot_self, mul_one]

private noncomputable def ggQ2xF1_sub_refl {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    GGBCV m ≃ₗ[ZMod 3] GGBCV m :=
  ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)
    (by rw [ggQ2_DW_sub_norm i j hij]; decide)

private noncomputable def ggQ2xF1_add_refl {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    GGBCV m ≃ₗ[ZMod 3] GGBCV m :=
  ggBCRefl ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)
    (by rw [ggQ2_DW_add_norm i j hij]; decide)

private lemma ggQ2xF1_single_sub_dot {m : ℕ} (i j : Fin m) (v : GGBCV m) :
    ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ v = v i - v j := by
  change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j) v = v i - v j
  rw [ggQ2_DW_dotLin_sub_left, ggQ2_DW_dotLin_fvec_left, ggQ2_DW_dotLin_fvec_left]

private lemma ggQ2xF1_single_add_dot {m : ℕ} (i j : Fin m) (v : GGBCV m) :
    ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ v = v i + v j := by
  change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j) v = v i + v j
  rw [ggQ2xF1_dotLin_add_left, ggQ2_DW_dotLin_fvec_left, ggQ2_DW_dotLin_fvec_left]

private lemma ggQ2xF1_sub_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (v : GGBCV m) :
    ggQ2xF1_sub_refl i j hij v =
      v + ((((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ v) * 2) •
        ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) := by
  unfold ggQ2xF1_sub_refl
  rw [ggQ2_DW_bc_apply', ggQ2_DW_sub_norm i j hij]

private lemma ggQ2xF1_add_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (v : GGBCV m) :
    ggQ2xF1_add_refl i j hij v =
      v + ((((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) ⬝ᵥ v) * 2) •
        ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) := by
  unfold ggQ2xF1_add_refl
  rw [ggQ2_DW_bc_apply', ggQ2_DW_add_norm i j hij]

private lemma ggQ2xF1_short_mul_short_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (v : GGBCV m) :
    (ggQ2xF1_short i * ggQ2xF1_short j) v =
      v + (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
        (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
  rw [LinearEquiv.mul_apply, ggQ2xF1_short_apply, ggQ2xF1_short_apply]
  have hc : (v + (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m)) i = v i := by
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij, mul_zero, add_zero]
  rw [hc]
  abel

private lemma ggQ2xF1_sub_mul_add_apply {m : ℕ} (i j : Fin m) (hij : i ≠ j) (v : GGBCV m) :
    (ggQ2xF1_sub_refl i j hij * ggQ2xF1_add_refl i j hij) v =
      v + (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
        (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
  rw [LinearEquiv.mul_apply, ggQ2xF1_add_apply i j hij, ggQ2xF1_single_add_dot i j v,
    ggQ2xF1_sub_apply i j hij]
  have h0 : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) = 0 := by
    change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j)
      (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j) = 0
    rw [map_add, ggQ2_DW_dotLin_sub_left, ggQ2_DW_dotLin_sub_left,
      ggQ2xF1_dotLin_fvec_fvec, ggQ2xF1_dotLin_fvec_fvec,
      ggQ2xF1_dotLin_fvec_fvec, ggQ2xF1_dotLin_fvec_fvec]
    simp [hij, Ne.symm hij]
  have hdot : ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) ⬝ᵥ
      (v + ((v i + v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1)) =
      v i - v j := by
    change ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j)
      (v + ((v i + v j) * 2) • (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j)) = v i - v j
    rw [map_add, map_smul, ggQ2_DW_dotLin_sub_left, ggQ2_DW_dotLin_fvec_left,
      ggQ2_DW_dotLin_fvec_left,
      show ggQ2_DW_dotLin 3 m (ggQ2_DW_fvec 3 m i - ggQ2_DW_fvec 3 m j)
        (ggQ2_DW_fvec 3 m i + ggQ2_DW_fvec 3 m j) = 0 from h0,
      smul_zero, add_zero]
  rw [hdot]
  have hsum : ((v i + v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) +
        ((v i - v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1) =
      (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
        (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
    calc ((v i + v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1) +
          ((v i - v j) * 2) • ((Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1)
        = (((v i + v j) * 2) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
            ((v i - v j) * 2) • (Pi.single i (1 : ZMod 3) : GGBCV m)) +
          (((v i + v j) * 2) • (Pi.single j (1 : ZMod 3) : GGBCV m) -
            ((v i - v j) * 2) • (Pi.single j (1 : ZMod 3) : GGBCV m)) := by
          rw [smul_add, smul_sub]; abel
      _ = (((v i + v j) * 2) + ((v i - v j) * 2)) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
          (((v i + v j) * 2) - ((v i - v j) * 2)) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
          rw [add_smul, sub_smul]
      _ = (v i) • (Pi.single i (1 : ZMod 3) : GGBCV m) +
          (v j) • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
          rw [show ((v i + v j) * 2) + ((v i - v j) * 2) = v i from
                (by decide : ∀ x y : ZMod 3, (x + y) * 2 + (x - y) * 2 = x) (v i) (v j),
              show ((v i + v j) * 2) - ((v i - v j) * 2) = v j from
                (by decide : ∀ x y : ZMod 3, (x + y) * 2 - (x - y) * 2 = y) (v i) (v j)]
  rw [add_assoc, hsum]
  abel

private lemma ggQ2xF1_short_mul_short_eq {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ggQ2xF1_short i * ggQ2xF1_short j = ggQ2xF1_sub_refl i j hij * ggQ2xF1_add_refl i j hij := by
  apply LinearEquiv.ext
  intro v
  rw [ggQ2xF1_short_mul_short_apply i j hij, ggQ2xF1_sub_mul_add_apply i j hij]

private lemma ggQ2xF1_wt_short {m : ℕ} (i : Fin m) (v : GGBCV m) :
    ggBCWt (ggQ2xF1_short i v) = ggBCWt v := by
  unfold ggBCWt
  congr 1
  apply Finset.filter_congr
  intro k _
  rw [ggQ2xF1_short_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hk : k = i
  · subst hk
    rw [Pi.single_eq_same, mul_one]
    exact (by decide : ∀ x : ZMod 3, x + x ≠ 0 ↔ x ≠ 0) (v k)
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, mul_zero, add_zero]

private lemma ggQ2xF1_short_mul_short_mem_DR {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ggQ2xF1_short i * ggQ2xF1_short j ∈ ggBCReflGp (ggDRoots m) := by
  rw [ggQ2xF1_short_mul_short_eq i j hij]
  apply (ggBCReflGp (ggDRoots m)).mul_mem
  · unfold ggQ2xF1_sub_refl
    exact Subgroup.subset_closure
      ⟨(Pi.single i (1 : ZMod 3) : GGBCV m) - Pi.single j 1,
        ggQ2_DW_Wt_sub_single i j hij, _, rfl⟩
  · unfold ggQ2xF1_add_refl
    exact Subgroup.subset_closure
      ⟨(Pi.single i (1 : ZMod 3) : GGBCV m) + Pi.single j 1,
        ggQ2_DW_Wt_add_single i j hij, _, rfl⟩

private lemma ggQ2xF1_short_inv {m : ℕ} (i : Fin m) :
    (ggQ2xF1_short i)⁻¹ = ggQ2xF1_short i :=
  inv_eq_of_mul_eq_one_right (ggQ2xF1_bc_refl_mul_self _ (ggQ2xF1_short_ne i))

private lemma ggQ2xF1_short_normalizes_DR {m : ℕ} (i : Fin m) :
    ∀ g ∈ ggBCReflGp (ggDRoots m),
      ggQ2xF1_short i * g * (ggQ2xF1_short i)⁻¹ ∈ ggBCReflGp (ggDRoots m) := by
  have hle : Subgroup.map (MulAut.conj (ggQ2xF1_short i)) (ggBCReflGp (ggDRoots m)) ≤
      ggBCReflGp (ggDRoots m) := by
    rw [ggBCReflGp, MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro t ⟨u, ⟨c, hcroot, hc, rfl⟩, rfl⟩
    obtain ⟨hc', heq⟩ :=
      ggQ2xF1_refl_conj_isom (ggQ2xF1_short i) c hc
        (ggQ2xF1_isometry (Pi.single i (1 : ZMod 3)) (ggQ2xF1_short_ne i))
    refine ⟨ggQ2xF1_short i c, ?_, hc', ?_⟩
    · rw [ggDRoots]
      change ggBCWt (ggQ2xF1_short i c) = 2
      rw [ggQ2xF1_wt_short, hcroot]
    · change ggQ2xF1_short i * ggBCRefl c hc * (ggQ2xF1_short i).symm =
        ggBCRefl (ggQ2xF1_short i c) hc'
      exact heq
  intro g hg
  exact hle (Subgroup.mem_map_of_mem _ hg)

private lemma ggQ2xF1_short_mul_i0_mem_DR {m : ℕ} (j i₀ : Fin m) :
    ggQ2xF1_short j * ggQ2xF1_short i₀ ∈ ggBCReflGp (ggDRoots m) := by
  by_cases h : j = i₀
  · rw [h, show ggQ2xF1_short i₀ * ggQ2xF1_short i₀ = 1 from
      ggQ2xF1_bc_refl_mul_self _ (ggQ2xF1_short_ne i₀)]
    exact Subgroup.one_mem _
  · exact ggQ2xF1_short_mul_short_mem_DR j i₀ h

private lemma ggQ2xF1_Wc_le_R_union_Rs {m : ℕ} (i₀ : Fin m) :
    ∀ g ∈ ggBCW m,
      g ∈ ggBCReflGp (ggDRoots m) ∨
        ∃ r ∈ ggBCReflGp (ggDRoots m), g = r * ggQ2xF1_short i₀ := by
  have hs2 : ggQ2xF1_short i₀ * ggQ2xF1_short i₀ = 1 :=
    ggQ2xF1_bc_refl_mul_self _ (ggQ2xF1_short_ne i₀)
  have hgen : ∀ t ∈ ggBCReflSet (ggBCRoots m),
      t ∈ ggBCReflGp (ggDRoots m) ∨
        ∃ r ∈ ggBCReflGp (ggDRoots m), t = r * ggQ2xF1_short i₀ := by
    rintro t ⟨c, hcroot, hc, rfl⟩
    rcases (by have h1 := hcroot.1; have h2 := hcroot.2; omega : ggBCWt c = 1 ∨ ggBCWt c = 2)
      with h1 | h2
    · right
      obtain ⟨j, s, hs, rfl⟩ := ggQ2xF1_wt_eq_one_iff.mp h1
      have hsj : (Pi.single j s : GGBCV m) = s • (Pi.single j (1 : ZMod 3) : GGBCV m) := by
        ext k
        by_cases hk : k = j
        · subst hk; simp [Pi.smul_apply, smul_eq_mul]
        · simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, Pi.smul_apply]
      have hs' : (s • (Pi.single j (1 : ZMod 3) : GGBCV m)) ⬝ᵥ
          (s • (Pi.single j (1 : ZMod 3) : GGBCV m)) ≠ 0 := by
        rw [← hsj]; exact hc
      refine ⟨ggQ2xF1_short j * ggQ2xF1_short i₀, ggQ2xF1_short_mul_i0_mem_DR j i₀, ?_⟩
      rw [mul_assoc, hs2, mul_one]
      rw [show ggBCRefl (Pi.single j s) hc =
          ggBCRefl (s • (Pi.single j (1 : ZMod 3) : GGBCV m)) hs' from
        ggQ2_DW_refl_congr hsj hc hs']
      rw [ggQ2xF1_refl_smul s hs (Pi.single j (1 : ZMod 3)) (ggQ2xF1_short_ne j) hs']
      rfl
    · left
      exact Subgroup.subset_closure ⟨c, h2, hc, rfl⟩
  intro g hg
  rw [ggBCW] at hg
  refine Subgroup.closure_induction (fun t ht => hgen t ht) ?_ ?_ ?_ hg
  · exact Or.inl (Subgroup.one_mem _)
  · intro x y hxmem hymem hx hy
    rcases hx with hx | ⟨rx, hrx, rfl⟩
    · rcases hy with hy | ⟨ry, hry, rfl⟩
      · exact Or.inl (mul_mem hx hy)
      · exact Or.inr ⟨x * ry, mul_mem hx hry, by rw [mul_assoc]⟩
    · rcases hy with hy | ⟨ry, hry, rfl⟩
      · refine Or.inr ⟨rx * (ggQ2xF1_short i₀ * y * ggQ2xF1_short i₀),
          mul_mem hrx (by
            have h := ggQ2xF1_short_normalizes_DR i₀ y hy
            rwa [ggQ2xF1_short_inv i₀] at h), ?_⟩
        rw [mul_assoc rx (ggQ2xF1_short i₀ * y * ggQ2xF1_short i₀) (ggQ2xF1_short i₀),
          show ggQ2xF1_short i₀ * y * ggQ2xF1_short i₀ * ggQ2xF1_short i₀ =
            ggQ2xF1_short i₀ * y from by
            rw [show ggQ2xF1_short i₀ * y * ggQ2xF1_short i₀ * ggQ2xF1_short i₀ =
              ggQ2xF1_short i₀ * y * (ggQ2xF1_short i₀ * ggQ2xF1_short i₀) from by group,
              hs2, mul_one],
          mul_assoc]
      · have h := ggQ2xF1_short_normalizes_DR i₀ ry hry
        rw [ggQ2xF1_short_inv i₀] at h
        refine Or.inl ?_
        convert mul_mem hrx h using 1
        group
  · intro x hxmem hx
    rcases hx with hx | ⟨rx, hrx, rfl⟩
    · exact Or.inl (inv_mem hx)
    · refine Or.inr ⟨ggQ2xF1_short i₀ * rx⁻¹ * ggQ2xF1_short i₀, ?_, ?_⟩
      · have h := ggQ2xF1_short_normalizes_DR i₀ rx⁻¹ (inv_mem hrx)
        rwa [ggQ2xF1_short_inv i₀] at h
      · rw [mul_inv_rev, ggQ2xF1_short_inv i₀]
        calc ggQ2xF1_short i₀ * rx⁻¹
            = ggQ2xF1_short i₀ * rx⁻¹ * 1 := by rw [mul_one]
          _ = ggQ2xF1_short i₀ * rx⁻¹ * (ggQ2xF1_short i₀ * ggQ2xF1_short i₀) := by rw [hs2]
          _ = (ggQ2xF1_short i₀ * rx⁻¹ * ggQ2xF1_short i₀) * ggQ2xF1_short i₀ := by group

private lemma ggQ2xF1_short_apply_self {m : ℕ} (i : Fin m) :
    ggQ2xF1_short i (Pi.single i (1 : ZMod 3) : GGBCV m) = -Pi.single i 1 := by
  rw [ggQ2xF1_short_apply, Pi.single_eq_same, one_smul]
  ext k
  by_cases hk : k = i
  · rw [hk]
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul, one_mul,
      Pi.neg_apply]
    exact (by decide : ∀ x : ZMod 3, x + x = -x) 1
  · simp only [Pi.add_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, Pi.smul_apply,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, mul_zero, add_zero, Pi.neg_apply,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk, neg_zero]

private lemma ggQ2xF1_short_apply_of_ne {m : ℕ} (i j : Fin m) (hij : j ≠ i) :
    ggQ2xF1_short i (Pi.single j (1 : ZMod 3) : GGBCV m) = Pi.single j 1 := by
  rw [ggQ2xF1_short_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), zero_smul,
    add_zero]

private lemma ggQ2xF1_neg_one_smul {m : ℕ} (x : GGBCV m) :
    (-1 : ZMod 3) • x = -x := by
  ext i
  rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact (by decide : ∀ a : ZMod 3, (-1) * a = -a) (x i)

private lemma ggQ2xF1_neg_one_smul_neg {m : ℕ} (x : GGBCV m) :
    (-1 : ZMod 3) • (-x) = x := by
  ext i
  rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact (by decide : ∀ a : ZMod 3, (-1) * (-a) = a) (x i)

private lemma ggQ2xF1_diag_mem_W_aux {m : ℕ} (k : ℕ) :
    ∀ (S : Finset (Fin m)) (b : GGBCV m ≃ₗ[ZMod 3] GGBCV m),
      S.card ≤ k →
      (∀ j, b (Pi.single j (1 : ZMod 3)) =
        (if j ∈ S then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3)) →
      b ∈ ggBCW m := by
  induction k with
  | zero =>
    intro S b hk hb
    have hScard : S.card = 0 := Nat.eq_zero_of_le_zero hk
    have hS : S = ∅ := Finset.card_eq_zero.mp hScard
    subst hS
    have hb1 : b = 1 := by
      apply (Pi.basisFun (ZMod 3) (Fin m)).ext'
      intro j
      rw [Pi.basisFun_apply, hb j]
      simp
    rw [hb1]; exact (ggBCW m).one_mem
  | succ k ih =>
    intro S b hk hb
    by_cases hle : S.card ≤ k
    · exact ih S b hle hb
    · have hpos : 0 < S.card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      have hcard : (S.erase i).card ≤ k := by
        rw [Finset.card_erase_of_mem hi]; omega
      have hb' : ∀ j, (ggQ2xF1_short i * b) (Pi.single j (1 : ZMod 3)) =
          (if j ∈ S.erase i then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3) := by
        intro j
        rw [LinearEquiv.mul_apply, hb j, map_smul]
        by_cases hji : j = i
        · subst hji
          rw [if_pos hi, ggQ2xF1_short_apply_self, if_neg (by simp)]
          calc (-1 : ZMod 3) • (-Pi.single j (1 : ZMod 3)) = Pi.single j 1 :=
                ggQ2xF1_neg_one_smul_neg _
            _ = (1 : ZMod 3) • Pi.single j (1 : ZMod 3) := (one_smul _ _).symm
        · rw [ggQ2xF1_short_apply_of_ne i j hji]
          by_cases hjS : j ∈ S
          · rw [if_pos hjS, if_pos (by rw [Finset.mem_erase]; exact ⟨hji, hjS⟩)]
          · rw [if_neg hjS, if_neg (by rw [Finset.mem_erase]; exact fun h => hjS h.2)]
      have hmem : ggQ2xF1_short i * b ∈ ggBCW m := ih (S.erase i) (ggQ2xF1_short i * b) hcard hb'
      have hshort : ggQ2xF1_short i ∈ ggBCW m := by
        rw [ggQ2xF1_short]
        exact Subgroup.subset_closure
          ⟨_, (by
            rw [ggBCRoots]
            simp only [Set.mem_setOf_eq]
            rw [ggQ2xF1_wt_single_of_ne_zero i 1 one_ne_zero]
            decide), ggQ2xF1_short_ne i, rfl⟩
      have hb_eq : b = (ggQ2xF1_short i)⁻¹ * (ggQ2xF1_short i * b) := by group
      rw [hb_eq]
      exact mul_mem (inv_mem hshort) hmem

private lemma ggQ2xF1_diag_mem_W {m : ℕ} (S : Finset (Fin m))
    (b : GGBCV m ≃ₗ[ZMod 3] GGBCV m)
    (hb : ∀ j, b (Pi.single j (1 : ZMod 3)) =
      (if j ∈ S then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3)) :
    b ∈ ggBCW m :=
  ggQ2xF1_diag_mem_W_aux S.card S b le_rfl hb

private lemma ggQ2xF1_neg_one_mem_Wc {m : ℕ} :
    (LinearEquiv.neg (ZMod 3) : GGBCV m ≃ₗ[ZMod 3] GGBCV m) ∈ ggBCW m := by
  refine ggQ2xF1_diag_mem_W Finset.univ (LinearEquiv.neg (ZMod 3)) ?_
  intro j
  rw [LinearEquiv.neg_apply, if_pos (Finset.mem_univ j),
    show -Pi.single j (1 : ZMod 3) = (-1 : ZMod 3) • Pi.single j (1 : ZMod 3) from
      (ggQ2xF1_neg_one_smul _).symm]

private lemma ggQ2xF1_isReflLin_bc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    IsReflLin (ggBCRefl c hc) := by
  refine ⟨c, (2 / (c ⬝ᵥ c)) • (ggBCDot c : ggQ2_DW_Dualc n), ?_, ?_⟩
  · change (2 / (c ⬝ᵥ c)) * ((ggBCDot c : ggQ2_DW_Dualc n) c) = 2
    rw [ggQ2_DW_dot_apply_c]
    field_simp
  · rfl

private lemma ggQ2xF1_reflSet_eq (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A) :
    ggReflSet (A.map (ggLinConj τ).toMonoidHom) =
      ggBCReflSet {z : GGBCV m |
        ∃ hz : z ⬝ᵥ z ≠ 0, ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} := by
  ext t
  constructor
  · rintro ⟨htA, c, φ, hφ, rfl⟩
    obtain ⟨ε, hε, hφv⟩ := ggQ2xF1_S1 D hbas hm e hD A hW hTF τ hτ hroot c φ hφ htA
    obtain ⟨hc, heq⟩ := ggQ2xF1_refl_eq_bc hφ ε hφv
    exact ⟨c, ⟨hc, heq ▸ htA⟩, hc, heq⟩
  · rintro ⟨c, ⟨hc, hcA⟩, hc', rfl⟩
    refine ⟨?_, ggQ2xF1_isReflLin_bc c hc'⟩
    rw [show ggBCRefl c hc' = ggBCRefl c hc from ggQ2_DW_refl_congr rfl hc' hc]
    exact hcA

private lemma ggQ2xF1_reflGp_eq_DR (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hZ : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    reflGp (A.map (ggLinConj τ).toMonoidHom) = ggBCReflGp (ggDRoots m) := by
  have hZroots : ggDRoots m ⊆ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} :=
    ggQ2xF1_Zroots _ (ggQ2_DW_Droots_le_map D hbas hm e hD τ hτ hroot A hW)
  have hrefl := ggQ2xF1_reflSet_eq D hbas hm e hD τ hτ hroot A hW hTF
  have hZeq : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} = ggDRoots m :=
    le_antisymm hZ hZroots
  rw [reflGp]
  change Subgroup.closure (ggReflSet (A.map (ggLinConj τ).toMonoidHom)) =
    ggBCReflGp (ggDRoots m)
  rw [hrefl, hZeq]
  rfl

private lemma ggQ2xF1_inner_Phi (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    GGQ2QuandleInner (ggReflSet A)
      (ggLinConj τ.symm '' (ggBCW m : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))) := by
  have hZroots : ggDRoots m ⊆ {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} :=
    ggQ2xF1_Zroots _ (ggQ2_DW_Droots_le_map D hbas hm e hD τ hτ hroot A hW)
  have hZeq : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
      ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} = ggDRoots m :=
    le_antisymm hZPhi hZroots
  have hrefl := ggQ2xF1_reflSet_eq D hbas hm e hD τ hτ hroot A hW hTF
  have hcirc : ggLinConj τ.symm '' ggReflSet (A.map (ggLinConj τ).toMonoidHom) = ggReflSet A := by
    rw [show ggReflSet (A.map (ggLinConj τ).toMonoidHom) = (ggLinConj τ) '' ggReflSet A from
      ggLinConj_reflSet τ A]
    ext g
    constructor
    · rintro ⟨h, ⟨a, ha, rfl⟩, rfl⟩
      simpa [show ggLinConj τ.symm (ggLinConj τ a) = a from
        (ggLinConj τ).symm_apply_apply a] using ha
    · intro hg
      exact ⟨ggLinConj τ g, ⟨g, hg, rfl⟩, (ggLinConj τ).symm_apply_apply g⟩
  have hcoord : GGQ2QuandleInner (ggBCReflSet (ggDRoots m)) (ggBCW m) := ggQ2_D_inner_phi m hm
  have hmap := ggQ2_inner_map (ggLinConj τ.symm) hcoord
  rw [← hZeq, ← hrefl, hcirc] at hmap
  exact hmap

private lemma ggQ2xF1_A_le_pm_Gamma (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ a ∈ A, ∃ g ∈ (ggLinConj τ.symm '' (ggBCW m : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m))),
      (∀ v, a v = g v) ∨ (∀ v, a v = -(g v)) := by
  have h4 : 4 ≤ Fintype.card D.ι := by rw [← Fintype.card_congr e, Fintype.card_fin]; omega
  have hinner := ggQ2xF1_inner_Phi D hbas hm e hD τ hτ hroot A hW hTF hZPhi
  exact ggQ2_transfer (p := 3) (by decide) D hbas h4 A hW _ hinner

private lemma ggQ2xF1_short_not_mem_of_Phi (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ}
    (hm : 5 ≤ m) (e : Fin m ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (i₀ : Fin m)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ggQ2xF1_short i₀ ∉ A.map (ggLinConj τ).toMonoidHom := by
  intro hs
  have hmem : (Pi.single i₀ (1 : ZMod 3) : GGBCV m) ∈
      {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} :=
    ⟨ggQ2xF1_short_ne i₀, by
      change ggBCRefl (Pi.single i₀ (1 : ZMod 3)) (ggQ2xF1_short_ne i₀) ∈
        A.map (ggLinConj τ).toMonoidHom
      exact hs⟩
  have h2 : ggBCWt (Pi.single i₀ (1 : ZMod 3) : GGBCV m) = 2 := hZPhi hmem
  rw [ggQ2xF1_wt_single_of_ne_zero i₀ 1 one_ne_zero] at h2
  norm_num at h2

private lemma ggQ2xF1_coord_pm_Wc (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ a' ∈ A.map (ggLinConj τ).toMonoidHom,
      ∃ w ∈ ggBCW m, (∀ v, a' v = w v) ∨ (∀ v, a' v = -(w v)) := by
  intro a' ha'
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨g, hg, hgpm⟩ := ggQ2xF1_A_le_pm_Gamma D hbas hm e hD τ hτ hroot A hW hTF hZPhi a ha
  obtain ⟨w, hw, rfl⟩ := hg
  refine ⟨w, hw, ?_⟩
  rcases hgpm with h | h
  · left
    intro v
    change ggLinConj τ a v = w v
    rw [ggLinConj_apply, h (τ.symm v), ggLinConj_apply]
    simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]
  · right
    intro v
    change ggLinConj τ a v = -(w v)
    rw [ggLinConj_apply, h (τ.symm v), map_neg, ggLinConj_apply]
    simp only [LinearEquiv.symm_symm, LinearEquiv.apply_symm_apply]

private lemma ggQ2xF1_pm_R_of_Wc (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (i₀ : Fin m)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ w ∈ ggBCW m, ∀ a' ∈ A.map (ggLinConj τ).toMonoidHom,
      ((∀ v, a' v = w v) ∨ (∀ v, a' v = -(w v))) →
      ∃ r ∈ ggBCReflGp (ggDRoots m),
        (∀ v, a' v = r v) ∨ (∀ v, a' v = -(r v)) := by
  have hDle := ggQ2_DW_Droots_le_map D hbas hm e hD τ hτ hroot A hW
  have hs2 : ggQ2xF1_short i₀ * ggQ2xF1_short i₀ = 1 :=
    ggQ2xF1_bc_refl_mul_self _ (ggQ2xF1_short_ne i₀)
  have hsinv : (ggQ2xF1_short i₀)⁻¹ = ggQ2xF1_short i₀ := ggQ2xF1_short_inv i₀
  intro w hw a' ha' hwpm
  rcases ggQ2xF1_Wc_le_R_union_Rs i₀ w hw with hwR | ⟨r0, hr0, rfl⟩
  · rcases hwpm with h | h
    · exact ⟨w, hwR, Or.inl h⟩
    · exact ⟨w, hwR, Or.inr h⟩
  · rcases hwpm with h | h
    · exfalso
      have haeq : a' = r0 * ggQ2xF1_short i₀ := LinearEquiv.ext h
      have hmul : a' * ggQ2xF1_short i₀ = r0 := by rw [haeq, mul_assoc, hs2, mul_one]
      have hsA : ggQ2xF1_short i₀ ∈ A.map (ggLinConj τ).toMonoidHom := by
        have hmem : a'⁻¹ * r0 ∈ A.map (ggLinConj τ).toMonoidHom :=
          mul_mem (inv_mem ha') (hDle hr0)
        have heq : ggQ2xF1_short i₀ = a'⁻¹ * r0 := by rw [← hmul]; group
        rwa [heq]
      exact ggQ2xF1_short_not_mem_of_Phi D hbas hm e hD τ hτ hroot A hW hTF i₀ hZPhi hsA
    · by_cases hneg : (LinearEquiv.neg (ZMod 3) : GGBCV m ≃ₗ[ZMod 3] GGBCV m) ∈
          ggBCReflGp (ggDRoots m)
      · exfalso
        have haeq : a' = LinearEquiv.neg (ZMod 3) * r0 * ggQ2xF1_short i₀ := by
          ext v
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.neg_apply, h v,
            LinearEquiv.mul_apply]
        have hmul : a' * ggQ2xF1_short i₀ = LinearEquiv.neg (ZMod 3) * r0 := by
          rw [haeq,
            show (LinearEquiv.neg (ZMod 3) * r0 * ggQ2xF1_short i₀) * ggQ2xF1_short i₀ =
              (LinearEquiv.neg (ZMod 3) * r0) * (ggQ2xF1_short i₀ * ggQ2xF1_short i₀) from by
              group,
            hs2, mul_one]
        have hsA : ggQ2xF1_short i₀ ∈ A.map (ggLinConj τ).toMonoidHom := by
          have hmem : a'⁻¹ * (LinearEquiv.neg (ZMod 3) * r0) ∈
              A.map (ggLinConj τ).toMonoidHom :=
            mul_mem (inv_mem ha') (mul_mem (hDle hneg) (hDle hr0))
          have heq : ggQ2xF1_short i₀ = a'⁻¹ * (LinearEquiv.neg (ZMod 3) * r0) := by
            rw [← hmul]; group
          rwa [heq]
        exact ggQ2xF1_short_not_mem_of_Phi D hbas hm e hD τ hτ hroot A hW hTF i₀ hZPhi hsA
      · rcases ggQ2xF1_Wc_le_R_union_Rs i₀ (LinearEquiv.neg (ZMod 3))
            (ggQ2xF1_neg_one_mem_Wc) with hnegR | ⟨r0', hr0', hnegeq⟩
        · exact absurd hnegR hneg
        · have haeq : a' = r0' * (ggQ2xF1_short i₀ * r0 * ggQ2xF1_short i₀) := by
            have haeq0 : a' = LinearEquiv.neg (ZMod 3) * r0 * ggQ2xF1_short i₀ := by
              ext v
              rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.neg_apply, h v,
                LinearEquiv.mul_apply]
            rw [haeq0, hnegeq]
            group
          refine ⟨r0' * (ggQ2xF1_short i₀ * r0 * ggQ2xF1_short i₀), ?_, Or.inl ?_⟩
          · refine mul_mem hr0' ?_
            have h := ggQ2xF1_short_normalizes_DR i₀ r0 hr0
            rwa [hsinv] at h
          · intro v
            rw [haeq]

private lemma ggQ2xF1_coord_pm_R_of_Phi (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 5 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (τ : D.V ≃ₗ[ZMod 3] GGBCV m) (hτ : ∀ i, τ (D.coroot (e i)) = ggDSimple 3 m i)
    (hroot : ∀ i v, D.root (e i) v = ∑ j, ggDSimple 3 m i j * τ v j)
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (i₀ : Fin m)
    (hZPhi : {z : GGBCV m | ∃ hz : z ⬝ᵥ z ≠ 0,
        ggBCRefl z hz ∈ A.map (ggLinConj τ).toMonoidHom} ⊆ ggDRoots m) :
    ∀ a' ∈ A.map (ggLinConj τ).toMonoidHom,
      ∃ r ∈ ggBCReflGp (ggDRoots m),
        (∀ v, a' v = r v) ∨ (∀ v, a' v = -(r v)) := by
  intro a' ha'
  obtain ⟨w, hw, hwpm⟩ :=
    ggQ2xF1_coord_pm_Wc D hbas hm e hD τ hτ hroot A hW hTF hZPhi a' ha'
  exact ggQ2xF1_pm_R_of_Wc D hbas hm e hD τ hτ hroot A hW hTF i₀ hZPhi w hw a' ha' hwpm

private theorem ggQ2xF1_pm (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 6 ≤ m)
    (e : Fin m ≃ D.ι) (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e)
    (ha : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ a ∈ A, ∃ r ∈ reflGp A, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨τ, hτ, hroot⟩ :=
    ggQ2_D_coordinates (p := 3) (by decide) D hbas (by omega) e hD
  let A' : Subgroup (GGBCV m ≃ₗ[ZMod 3] GGBCV m) := A.map (ggLinConj τ).toMonoidHom
  have hA' : A' = A.map (ggLinConj τ).toMonoidHom := rfl
  have hW' : ggBCReflGp (ggDRoots m) ≤ A' :=
    ggQ2_DW_Droots_le_map D hbas (by omega) e hD τ hτ hroot A hW
  have hS1 : ∀ (c : GGBCV m) (φ : Module.Dual (ZMod 3) (GGBCV m)) (h : φ c = 2),
      Module.reflection h ∈ A' → ∃ ε : ZMod 3,
        (ε = 1 ∨ ε = -1) ∧ ∀ v, φ v = ε * (c ⬝ᵥ v) :=
    ggQ2xF1_S1 D hbas (by omega) e hD A hW hTF τ hτ hroot
  have hHL' := ggQ2xF1_HL D hbas (by omega) e hD τ hτ hroot ha x hx A hHL
  obtain ⟨hZ0, hZroots, hZcl, hZHL⟩ :=
    ggQ2xF1_Z_hyps (m := m) hm A' hW' hS1 hHL'
  have hZrefl : ggReflSet A' = ggBCReflSet (ggQ2xF1_Z A') :=
    ggQ2xF1_reflSet_eq D hbas (by omega) e hD τ hτ hroot A hW hTF
  have transport : (∀ a' ∈ A', ∃ r' ∈ reflGp A',
        (∀ v, a' v = r' v) ∨ (∀ v, a' v = -(r' v))) →
      ∀ a ∈ A, ∃ r ∈ reflGp A, (∀ v, a v = r v) ∨ (∀ v, a v = -(r v)) := by
    intro hpm a ha
    have ha' : ggLinConj τ a ∈ A' := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨r', hr', hpm'⟩ := hpm _ ha'
    rw [hA'] at hr'
    rw [ggLinConj_reflGp] at hr'
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hr'
    refine ⟨r, hr, ?_⟩
    rcases hpm' with h | h
    · left
      intro w
      have h2 := congrArg (fun y => τ.symm y) (h (τ w))
      simpa [ggLinConj_apply] using h2
    · right
      intro w
      have h2 := congrArg (fun y => τ.symm y) (h (τ w))
      simpa [ggLinConj_apply] using h2
  rcases ggQ2xF1_Z_cases (m := m) hm (ggQ2xF1_Z A') hZ0 hZroots hZcl hZHL with
    hZ | hZ | ⟨hm8, ε, hε, hZ⟩
  ·
    have hZPhi : ggQ2xF1_Z A' ⊆ ggDRoots m := by rw [hZ]
    have hgp : reflGp A' = ggBCReflGp (ggDRoots m) := by
      rw [hA']
      exact ggQ2xF1_reflGp_eq_DR D hbas (by omega) e hD τ hτ hroot A hW hTF hZPhi
    refine transport (fun a' ha' => ?_)
    obtain ⟨r, hr, hpm⟩ :=
      ggQ2xF1_coord_pm_R_of_Phi D hbas (by omega) e hD τ hτ hroot A hW hTF
        ⟨0, by omega⟩ hZPhi a' ha'
    exact ⟨r, by rw [hgp]; exact hr, hpm⟩
  ·
    have hZroots' : ggQ2xF1_Z A' = ggBCRoots m := by
      rw [hZ]
      ext z
      simp only [Set.mem_union, Set.mem_setOf_eq, ggBCRoots, ggDRoots]
      constructor
      · rintro (h | h)
        · exact ⟨by omega, by omega⟩
        · exact ⟨by omega, by omega⟩
      · rintro ⟨h1, h2⟩
        have hc : ggBCWt z = 1 ∨ ggBCWt z = 2 := by omega
        rcases hc with h | h
        · exact Or.inr h
        · exact Or.inl h
    have hrefl2 : ggReflSet A' = ggBCReflSet (ggBCRoots m) := by rw [hZrefl, hZroots']
    have hgp : reflGp A' = ggBCW m := by
      rw [reflGp]
      change Subgroup.closure (ggReflSet A') = ggBCW m
      rw [hrefl2]
      rfl
    have hWB : ggBCW m ≤ A' := by
      rw [ggBCW, Subgroup.closure_le]
      intro t ht
      rw [← hrefl2] at ht
      exact ht.1
    have hconjW_gen : ∀ a' ∈ A', ∀ g ∈ ggBCW m, a' * g * a'⁻¹ ∈ ggBCW m := by
      intro a' ha' g hg
      have hconj_gen : ∀ t ∈ ggBCReflSet (ggBCRoots m),
          a' * t * a'⁻¹ ∈ ggBCReflSet (ggBCRoots m) := by
        intro t ht
        rw [← hrefl2] at ht
        have htA' : t ∈ A' := ht.1
        have htR : IsReflLin t := ht.2
        have hconj : a' * t * a'⁻¹ ∈ ggReflSet A' :=
          ⟨A'.mul_mem (A'.mul_mem ha' htA') (A'.inv_mem ha'), ggQ2_isReflLin_conj a' t htR⟩
        rw [hrefl2] at hconj
        exact hconj
      have hle : Subgroup.map (MulAut.conj a') (ggBCW m) ≤ ggBCW m := by
        rw [ggBCW, MonoidHom.map_closure]
        apply Subgroup.closure_mono
        rintro t ⟨u, hu, rfl⟩
        exact hconj_gen u hu
      have hmem : (MulAut.conj a') g ∈ Subgroup.map (MulAut.conj a') (ggBCW m) :=
        Subgroup.mem_map_of_mem _ hg
      exact hle hmem
    have hle : A' ≤ ggBCW m := by
      intro a' ha'
      have hnorm : a' ∈ Subgroup.normalizer
          (ggBCW m : Set (GGBCV m ≃ₗ[ZMod 3] GGBCV m)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · intro hy; exact hconjW_gen a' ha' y hy
        · intro hy
          have hmem := hconjW_gen a'⁻¹ (A'.inv_mem ha') (a' * y * a'⁻¹) hy
          simpa [mul_assoc] using hmem
      exact ggQ2_bc_normalizer m (by omega) a' hnorm
    refine transport (fun a' ha' => ?_)
    exact ⟨a', by rw [hgp]; exact hle ha', Or.inl (fun v => rfl)⟩
  ·
    subst m
    have hZrefl8 : ggReflSet A' =
        ggBCReflSet (ggDRoots 8 ∪ {z | ggDHalfSpin ε z}) := by rw [hZrefl, hZ]
    have hgp : reflGp A' = ggBCReflGp (ggDRoots 8 ∪ {z | ggDHalfSpin ε z}) := by
      rw [reflGp]
      change Subgroup.closure (ggReflSet A') = ggBCReflGp (ggDRoots 8 ∪ {z | ggDHalfSpin ε z})
      rw [hZrefl8]
      rfl
    have hinnerE8 : GGQ2QuandleInner (ggReflSet A') (reflGp A') := by
      rw [hgp, hZrefl8]
      exact ggQ2_D_inner_E8 ε hε
    have hTc : ∀ s ∈ ggReflSet A, ∀ t ∈ ggReflSet A, s * t * s⁻¹ ∈ ggReflSet A := by
      rintro s ⟨hsA, -⟩ t ⟨htA, htR⟩
      exact ⟨A.mul_mem (A.mul_mem hsA htA) (A.inv_mem hsA), ggQ2_isReflLin_conj s t htR⟩
    have himg : (ggLinConj τ) '' (ggReflSet A) = ggReflSet A' :=
      (ggLinConj_reflSet τ A).symm
    have hinnerE8' : GGQ2QuandleInner ((ggLinConj τ) '' ggReflSet A) (reflGp A') := by
      rw [himg]; exact hinnerE8
    have hΓ : (reflGp A' : Set (GGBCV 8 ≃ₗ[ZMod 3] GGBCV 8)) ⊆
        (ggLinConj τ) '' (reflGp A : Set (D.V ≃ₗ[ZMod 3] D.V)) := by
      rw [hA', ggLinConj_reflGp]
      intro x hx
      exact hx
    have hinnerD : GGQ2QuandleInner (ggReflSet A) (reflGp A) :=
      ggQ2_inner_of_hom (f := (ggLinConj τ).toMonoidHom) (hf := (ggLinConj τ).injective)
        (T := ggReflSet A) (Γ := reflGp A) (Γ' := reflGp A') hTc hinnerE8' hΓ
    have h4 : 4 ≤ Fintype.card D.ι := by
      rw [← Fintype.card_congr e, Fintype.card_fin]; omega
    exact ggQ2_transfer (p := 3) (by decide) D hbas h4 A hW _ hinnerD

theorem ggQ2_thmB_D_a1 (D : GGQ2Lin 3) (hbas : D.Basis) {m : ℕ} (hm : 6 ≤ m) (e : Fin m ≃ D.ι)
    (hD : D.coxeter = (ggCoxeterMatrixD m).reindex e) (ha : D.a = e ⟨0, by omega⟩) (x : D.V)
    (hx : ∀ v, (∀ g ∈ D.parab {k | k ≠ D.a}, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {x})
    (A : Subgroup (D.V ≃ₗ[ZMod 3] D.V)) (hW : D.weyl ≤ A) (hTF : TransvectionFree A)
    (hHL : ∀ φ ∈ A, φ x ∈ Submodule.span (ZMod 3) {x} →
      φ ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∀ φ ∈ A, ∃ r ∈ reflGp A,
      Submodule.span (ZMod 3) {φ x} = Submodule.span (ZMod 3) {r x} := by
  exact ggQ2_P3_of_pm A x (ggQ2xF1_pm D hbas hm e hD ha x hx A hW hTF hHL)

end CFSG.StandardType

end
