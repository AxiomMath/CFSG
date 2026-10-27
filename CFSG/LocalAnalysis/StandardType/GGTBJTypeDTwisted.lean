module

public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDDatum
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeDParabolicLE3
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameChange
public import CFSG.Permutation.SupportedAdjacent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord
open CFSG.StandardType.TypeBDatum
open Multiplicative

namespace TypeDDatum

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma tbD3_diagAut_mul_self {m p : ℕ} (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1) :
    (diagAut s hs : MulAut (Fin m → Multiplicative (ZMod p))) * diagAut s hs = 1 := by
  refine MulEquiv.ext fun f => funext fun i => ?_
  rw [MulAut.mul_apply, diagAut_apply, diagAut_apply, MulAut.one_apply, toAdd_ofAdd,
    ← mul_assoc, hs i, one_mul, ofAdd_toAdd]

private lemma tbD3_conj_diagAut_permAut_apply {m p : ℕ} {s : Fin m → ZMod p}
    (hs : ∀ i, s i * s i = 1) (σ : Equiv.Perm (Fin m))
    (f : Fin m → Multiplicative (ZMod p)) (j : Fin m) :
    (MulAut.conj (diagAut s hs) (permAut (p := p) σ)) f j =
      ofAdd (s j * (s (σ⁻¹ j) * toAdd (f (σ⁻¹ j)))) := by
  have hD2 : (diagAut s hs : MulAut (Fin m → Multiplicative (ZMod p))) * diagAut s hs = 1 :=
    tbD3_diagAut_mul_self s hs
  have hDinv : (diagAut s hs)⁻¹ = diagAut s hs := inv_eq_of_mul_eq_one_right hD2
  simp only [MulAut.conj_apply, hDinv, MulAut.mul_apply, permAut_apply, Function.comp_apply,
    diagAut_apply, toAdd_ofAdd]

private lemma tbD3_conj_diagAut_sgnAut_apply {m p : ℕ} {s : Fin m → ZMod p}
    (hs : ∀ i, s i * s i = 1) (i : Fin m)
    (f : Fin m → Multiplicative (ZMod p)) (j : Fin m) :
    (MulAut.conj (diagAut s hs) (sgnAut (p := p) i)) f j =
      if j = i then (f j)⁻¹ else f j := by
  have hD2 : (diagAut s hs : MulAut (Fin m → Multiplicative (ZMod p))) * diagAut s hs = 1 :=
    tbD3_diagAut_mul_self s hs
  have hDinv : (diagAut s hs)⁻¹ = diagAut s hs := inv_eq_of_mul_eq_one_right hD2
  rw [MulAut.conj_apply, hDinv, MulAut.mul_apply, MulAut.mul_apply, diagAut_apply, sgnAut_apply,
    Function.update_apply]
  by_cases hji : j = i
  · rw [if_pos hji, diagAut_apply, toAdd_inv, toAdd_ofAdd, if_pos hji, hji]
    rw [show s i * -(s i * toAdd (f i)) = -toAdd (f i) from by
      rw [mul_neg, ← mul_assoc, hs i, one_mul]]
    rw [ofAdd_neg, ofAdd_toAdd]
  · rw [if_neg hji, diagAut_apply, toAdd_ofAdd, if_neg hji]
    rw [show s j * (s j * toAdd (f j)) = toAdd (f j) from by rw [← mul_assoc, hs j, one_mul]]
    rw [ofAdd_toAdd]

private lemma tbD3_conj_diagAut_sgnAut {m p : ℕ} {s : Fin m → ZMod p}
    (hs : ∀ i, s i * s i = 1) (i : Fin m) :
    MulAut.conj (diagAut s hs) (sgnAut (p := p) i) = sgnAut (p := p) i := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [tbD3_conj_diagAut_sgnAut_apply (s := s) hs i f j, sgnAut_apply, Function.update_apply]
  by_cases hji : j = i
  · rw [if_pos hji, if_pos hji, hji]
  · rw [if_neg hji, if_neg hji]

private lemma tbD3_conj_diagAut_involutive {m p : ℕ} {s : Fin m → ZMod p}
    (hs : ∀ i, s i * s i = 1) (x : MulAut (Fin m → Multiplicative (ZMod p))) :
    MulAut.conj (diagAut s hs) (MulAut.conj (diagAut s hs) x) = x := by
  rw [conj_apply_comp, tbD3_diagAut_mul_self s hs, MulAut.conj_apply]
  simp

private lemma tbD3_conj_diagAut_swap_of_mul_eq_one {m p : ℕ} {s : Fin m → ZMod p}
    (hs : ∀ i, s i * s i = 1) {a b : Fin m} (hab : a ≠ b) (hc : s a * s b = 1) :
    MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap a b)) =
      permAut (p := p) (Equiv.swap a b) := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [tbD3_conj_diagAut_permAut_apply (s := s) hs (Equiv.swap a b) f j, permAut_apply,
    Function.comp_apply, Equiv.swap_inv]
  by_cases hja : j = a
  · rw [hja, Equiv.swap_apply_left]
    rw [show s a * (s b * toAdd (f b)) = toAdd (f b) from by
      rw [← mul_assoc, hc, one_mul]]
    rw [ofAdd_toAdd]
  · by_cases hjb : j = b
    · rw [hjb, Equiv.swap_apply_right]
      rw [show s b * (s a * toAdd (f a)) = toAdd (f a) from by
        rw [← mul_assoc, mul_comm (s b) (s a), hc, one_mul]]
      rw [ofAdd_toAdd]
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
      rw [show s j * (s j * toAdd (f j)) = toAdd (f j) from by rw [← mul_assoc, hs j, one_mul]]
      rw [ofAdd_toAdd]

private lemma tbD3_sgnAut_mul_sgnAut_apply {m p : ℕ} {a b : Fin m} (hab : a ≠ b)
    (f : Fin m → Multiplicative (ZMod p)) (j : Fin m) :
    (sgnAut (p := p) a * sgnAut (p := p) b) f j =
      if j = a then (f a)⁻¹ else if j = b then (f b)⁻¹ else f j := by
  rw [MulAut.mul_apply, sgnAut_apply, sgnAut_apply, Function.update_apply, Function.update_apply]
  by_cases hja : j = a
  · subst hja; simp [hab]
  · by_cases hjb : j = b
    · subst hjb; simp [hja]
    · simp [hja, hjb]

private lemma tbD3_conj_diagAut_swap_of_mul_eq_neg_one {m p : ℕ} {s : Fin m → ZMod p}
    (hs : ∀ i, s i * s i = 1) {a b : Fin m} (hab : a ≠ b) (hc : s a * s b = -1) :
    MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap a b)) =
      permAut (p := p) (Equiv.swap a b) * (sgnAut (p := p) a * sgnAut (p := p) b) := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [tbD3_conj_diagAut_permAut_apply (s := s) hs (Equiv.swap a b) f j]
  rw [MulAut.mul_apply, permAut_apply, Function.comp_apply, Equiv.swap_inv,
    tbD3_sgnAut_mul_sgnAut_apply hab f]
  by_cases hja : j = a
  · rw [hja, Equiv.swap_apply_left, if_neg (Ne.symm hab), if_pos rfl]
    rw [show s a * (s b * toAdd (f b)) = -toAdd (f b) from by
      rw [← mul_assoc, hc, neg_one_mul]]
    rw [ofAdd_neg, ofAdd_toAdd]
  · by_cases hjb : j = b
    · rw [hjb, Equiv.swap_apply_right, if_pos rfl]
      rw [show s b * (s a * toAdd (f a)) = -toAdd (f a) from by
        rw [← mul_assoc, mul_comm (s b) (s a), hc, neg_one_mul]]
      rw [ofAdd_neg, ofAdd_toAdd]
    · rw [Equiv.swap_apply_of_ne_of_ne hja hjb, if_neg hja, if_neg hjb]
      rw [show s j * (s j * toAdd (f j)) = toAdd (f j) from by rw [← mul_assoc, hs j, one_mul]]
      rw [ofAdd_toAdd]

private lemma tbD3_conj_diagAut_swap_mem {m p : ℕ} [Fact p.Prime] {s : Fin m → ZMod p}
    (hs : ∀ i, s i * s i = 1) {a b : Fin m} (hab : a ≠ b) :
    MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap a b)) ∈ evenSignedAut m p := by
  have hcc : (s a * s b) * (s a * s b) = 1 := by
    have h : (s a * s b) * (s a * s b) = (s a * s a) * (s b * s b) := by ring
    rw [h, hs a, hs b, one_mul]
  rcases sign_of_sq_one hcc with hc | hc
  · rw [tbD3_conj_diagAut_swap_of_mul_eq_one (s := s) hs hab hc]
    exact Subgroup.subset_closure (Or.inl ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩)
  · rw [tbD3_conj_diagAut_swap_of_mul_eq_neg_one (s := s) hs hab hc]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (Or.inl ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩))
      (Subgroup.subset_closure (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩))

private theorem tbD3_evenSignedAut_map_conj_diag {m p : ℕ} [Fact p.Prime]
    (s : Fin m → ZMod p) (hs : ∀ i, s i * s i = 1) :
    (evenSignedAut m p).map (MulAut.conj (diagAut s hs)).toMonoidHom = evenSignedAut m p := by
  apply le_antisymm
  · rw [evenSignedAut, evenSignedSupportedAut, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg | hg, rfl⟩
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hg
      exact tbD3_conj_diagAut_swap_mem (s := s) hs hab
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hg
      rw [map_mul]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [tbD3_conj_diagAut_sgnAut (s := s) hs a, tbD3_conj_diagAut_sgnAut (s := s) hs b]
      exact Subgroup.subset_closure
        (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩)
  · rw [evenSignedAut, evenSignedSupportedAut, Subgroup.closure_le]
    rintro g (hg | hg)
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hg
      refine Subgroup.mem_map.mpr ⟨MulAut.conj (diagAut s hs) (permAut (p := p) (Equiv.swap a b)),
        tbD3_conj_diagAut_swap_mem (s := s) hs hab, ?_⟩
      exact tbD3_conj_diagAut_involutive (s := s) hs _
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hg
      refine Subgroup.mem_map.mpr ⟨sgnAut (p := p) a * sgnAut (p := p) b,
        Subgroup.subset_closure
          (Or.inr ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab, rfl⟩), ?_⟩
      rw [map_mul]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [tbD3_conj_diagAut_sgnAut (s := s) hs a, tbD3_conj_diagAut_sgnAut (s := s) hs b]

private lemma tbD3_conj_permAut_sgnAut_apply {m p : ℕ} (τ : Equiv.Perm (Fin m)) (i : Fin m)
    (f : Fin m → Multiplicative (ZMod p)) (j : Fin m) :
    (MulAut.conj (permAut (p := p) τ) (sgnAut (p := p) i)) f j =
      if j = τ i then (f j)⁻¹ else f j := by
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply, permAut_inv_apply, permAut_apply,
    Function.comp_apply, sgnAut_apply, Function.update_apply]
  by_cases h : τ⁻¹ j = i
  · have hj : j = τ i := by
      rw [← h]; exact (Equiv.apply_symm_apply τ j).symm
    rw [if_pos h, if_pos hj, Function.comp_apply, hj]
  · have hj : j ≠ τ i := by
      intro hh; exact h (by rw [hh]; exact Equiv.symm_apply_apply τ i)
    rw [if_neg h, if_neg hj, Function.comp_apply]
    exact congrArg f (Equiv.apply_symm_apply τ j)

private lemma tbD3_conj_permAut_sgnAut {m p : ℕ} (τ : Equiv.Perm (Fin m)) (i : Fin m) :
    MulAut.conj (permAut (p := p) τ) (sgnAut (p := p) i) = sgnAut (p := p) (τ i) := by
  refine MulEquiv.ext fun f => funext fun j => ?_
  rw [tbD3_conj_permAut_sgnAut_apply τ i f j, sgnAut_apply, Function.update_apply]
  by_cases h : j = τ i
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h]

private lemma tbD3_conj_permAut_permAut_swap {m p : ℕ} (τ : Equiv.Perm (Fin m)) (a b : Fin m) :
    MulAut.conj (permAut (p := p) τ) (permAut (p := p) (Equiv.swap a b)) =
      permAut (p := p) (Equiv.swap (τ a) (τ b)) := by
  rw [MulAut.conj_apply]
  exact permAut_mul_swap τ a b

private theorem tbD3_evenSignedAut_map_conj_perm {m p : ℕ} (τ : Equiv.Perm (Fin m)) :
    (evenSignedAut m p).map (MulAut.conj (permAut (p := p) τ)).toMonoidHom = evenSignedAut m p := by
  apply le_antisymm
  · rw [evenSignedAut, evenSignedSupportedAut, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg | hg, rfl⟩
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hg
      simp only [MulEquiv.coe_toMonoidHom]
      rw [tbD3_conj_permAut_permAut_swap]
      exact Subgroup.subset_closure (Or.inl ⟨τ a, Finset.mem_univ _, τ b, Finset.mem_univ _,
        fun h => hab (τ.injective h), rfl⟩)
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hg
      rw [map_mul]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [tbD3_conj_permAut_sgnAut τ a, tbD3_conj_permAut_sgnAut τ b]
      exact Subgroup.subset_closure (Or.inr ⟨τ a, Finset.mem_univ _, τ b, Finset.mem_univ _,
        fun h => hab (τ.injective h), rfl⟩)
  · rw [evenSignedAut, evenSignedSupportedAut, Subgroup.closure_le]
    rintro g (hg | hg)
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hg
      refine Subgroup.mem_map.mpr ⟨permAut (p := p) (Equiv.swap (τ⁻¹ a) (τ⁻¹ b)), ?_, ?_⟩
      · exact Subgroup.subset_closure (Or.inl ⟨τ⁻¹ a, Finset.mem_univ _, τ⁻¹ b, Finset.mem_univ _,
          fun h => hab (by simpa using congrArg τ h), rfl⟩)
      · simp only [MulEquiv.coe_toMonoidHom]
        rw [tbD3_conj_permAut_permAut_swap]
        simp
    · obtain ⟨a, -, b, -, hab, rfl⟩ := hg
      refine Subgroup.mem_map.mpr
        ⟨sgnAut (p := p) (τ⁻¹ a) * sgnAut (p := p) (τ⁻¹ b),
          Subgroup.subset_closure (Or.inr ⟨τ⁻¹ a, Finset.mem_univ _, τ⁻¹ b, Finset.mem_univ _,
            fun h => hab (by simpa using congrArg τ h), rfl⟩), ?_⟩
      rw [map_mul]
      simp only [MulEquiv.coe_toMonoidHom]
      rw [tbD3_conj_permAut_sgnAut τ (τ⁻¹ a), tbD3_conj_permAut_sgnAut τ (τ⁻¹ b)]
      simp

private theorem tbD3_permSupportedAut_last_eq_adjacent {m p b : ℕ} (hb : 2 ≤ b) (hbm : b ≤ m) :
    permSupportedAut m p (Finset.univ.filter (fun i : Fin m => m - b ≤ i.val)) =
      Subgroup.closure (Set.range fun j : {j : Fin m // m - b ≤ j.val ∧ j.val + 1 < m} =>
        permAut (p := p) (Equiv.swap j ⟨j.val + 1, j.2.2⟩)) := by
  classical
  let Tl : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => m - b ≤ i.val)
  change permSupportedAut m p Tl = _
  let e : Fin b ≃ Tl :=
    { toFun := fun i => ⟨⟨m - b + i.val, by have := i.isLt; omega⟩, by
        simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩
      invFun := fun x => ⟨x.1.val - (m - b), by
        have hx := x.2
        simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        omega⟩
      left_inv := fun i => by
        ext
        show (m - b + i.val) - (m - b) = i.val
        omega
      right_inv := fun x => by
        ext
        show m - b + (x.1.val - (m - b)) = x.1.val
        have hx := x.2
        simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        omega }
  let e' : Fin (b - 1 + 1) ≃ Tl := (finCongr (by omega : b - 1 + 1 = b)).trans e
  have hfix :=
    CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_compl_eq_closure_adjacent Tl e'
  have hmapfix : permSupportedAut m p Tl =
      (fixingSubgroup (Equiv.Perm (Fin m)) ((Tl : Set (Fin m))ᶜ)).map (permAutHom m p) := by
    apply le_antisymm
    · rw [permSupportedAut, Subgroup.closure_le]
      rintro σ ⟨a, ha, b', hb', hab, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Equiv.swap a b', by
        rw [mem_fixingSubgroup_iff]
        intro x hx
        exact Equiv.swap_apply_of_ne_of_ne (fun h => hx (h ▸ ha)) (fun h => hx (h ▸ hb')), rfl⟩
    · rw [hfix, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨j, rfl⟩, rfl⟩
      refine Subgroup.subset_closure ⟨(e' j.castSucc : Fin m), (e' j.castSucc).2,
        (e' j.succ : Fin m), (e' j.succ).2, ?_, rfl⟩
      intro h
      have hv := congrArg Fin.val h
      simp [e', e, finCongr] at hv
  rw [hmapfix, hfix, MonoidHom.map_closure, ← Set.range_comp]
  change Subgroup.closure (Set.range fun j : Fin (b - 1) =>
    permAut (p := p) (Equiv.swap (e' j.castSucc : Fin m) (e' j.succ : Fin m))) = _
  let eJ : {j : Fin m // m - b ≤ j.val ∧ j.val + 1 < m} ≃ Fin (b - 1) :=
    { toFun := fun j => ⟨j.1.val - (m - b), by have := j.2.1; have := j.2.2; omega⟩
      invFun := fun i =>
        ⟨⟨m - b + i.val, by have := i.isLt; omega⟩, by
          refine ⟨?_, ?_⟩
          · show m - b ≤ m - b + i.val; omega
          · show m - b + i.val + 1 < m; have := i.isLt; omega⟩
      left_inv := fun j => by
        ext
        show m - b + (j.1.val - (m - b)) = j.1.val
        have := j.2.1; omega
      right_inv := fun i => by
        ext
        show (m - b + i.val) - (m - b) = i.val
        omega }
  have hf : ∀ j : {j : Fin m // m - b ≤ j.val ∧ j.val + 1 < m},
      permAut (p := p) (Equiv.swap (e' (eJ j).castSucc : Fin m) (e' (eJ j).succ : Fin m)) =
        permAut (p := p) (Equiv.swap j ⟨j.val + 1, j.2.2⟩) := by
    intro j
    have h1 : (e' (eJ j).castSucc : Fin m) = j.1 := by
      apply Fin.ext
      show m - b + (j.1.val - (m - b)) = j.1.val
      have := j.2.1; omega
    have h2 : (e' (eJ j).succ : Fin m) = ⟨j.val + 1, j.2.2⟩ := by
      apply Fin.ext
      show m - b + ((j.1.val - (m - b)) + 1) = j.1.val + 1
      have := j.2.1; omega
    rw [h1, h2]
  have hrange : Set.range (fun j : Fin (b - 1) =>
        permAut (p := p) (Equiv.swap (e' j.castSucc : Fin m) (e' j.succ : Fin m))) =
      Set.range (fun j : {j : Fin m // m - b ≤ j.val ∧ j.val + 1 < m} =>
        permAut (p := p) (Equiv.swap j ⟨j.val + 1, j.2.2⟩)) := by
    ext x; constructor
    · rintro ⟨i, rfl⟩
      refine ⟨eJ.symm i, ?_⟩
      dsimp only
      rw [(hf (eJ.symm i)).symm, Equiv.apply_symm_apply eJ i]
    · rintro ⟨j, rfl⟩
      exact ⟨eJ j, hf j⟩
  rw [hrange]

theorem ggTBJTypeD_sideDatum_twistedPerm {G : Type} [Group G] [Finite G] {p m : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hm : 4 ≤ m) {Bs X J : Subgroup G} (hBs : IsElemAbelian p Bs)
    {W₀ : Type} [Group W₀] (Θ : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs)
    (hX : ggAutomizer X Bs = (evenSignedAut m p).map (liftBs Θ))
    {S : Finset (Fin m)} (hS : 2 ≤ S.card) (hc3 : m + 1 - S.card ≤ 3)
    {s : Fin m → ZMod p} (hs : ∀ i, s i * s i = 1)
    (hJ : ggAutomizer J Bs = (twistedPermAut m p S s hs).map (liftBs Θ)) :
    (m + 1 - S.card = 1 → GGResSideDatum p Bs X J) ∧
      (2 ≤ m + 1 - S.card → GGResLeviSideDatumLE3 p Bs X J) := by
  classical
  set b : ℕ := S.card with hb
  have hb2 : 2 ≤ b := by rw [hb]; exact hS
  have hbm : b ≤ m := by rw [hb]; simpa using Finset.card_le_univ S
  let Tl : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => m - b ≤ i.val)
  have hcardS : Nat.card S = b := by rw [hb, Nat.card_eq_finsetCard]
  let eS : Fin b ≃ S := (Finite.equivFinOfCardEq hcardS).symm
  let last : Fin b ↪ Fin m :=
    ⟨fun i => ⟨m - b + i.val, by have := i.isLt; omega⟩, fun i j h => by
      have := congrArg Fin.val h; simp only [Fin.mk.injEq] at this; omega⟩
  let enumerated : Fin b ↪ Fin m := eS.toEmbedding.trans (Function.Embedding.subtype (· ∈ S))
  obtain ⟨τ, hτ⟩ := Equiv.Perm.exists_smul_eq_embedding last enumerated
  have hτi : ∀ i : Fin b, τ (last i) = (eS i : Fin m) := by
    intro i
    have hh := congrArg (fun e : Fin b ↪ Fin m => e i) hτ
    simpa only [Function.Embedding.smul_apply, Equiv.Perm.smul_def, enumerated,
      Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Function.Embedding.coe_subtype,
      last] using hh
  have hTl_eq : Tl = Finset.univ.image last := by
    ext x; constructor
    · intro hx
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      refine Finset.mem_image.mpr ⟨⟨x.val - (m - b), by omega⟩, Finset.mem_univ _, ?_⟩
      apply Fin.ext
      show m - b + (x.val - (m - b)) = x.val
      omega
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
      simp only [Tl, Finset.mem_filter, Finset.mem_univ, true_and]
      show m - b ≤ m - b + i.val
      omega
  have hTlτ : Tl.image τ = S := by
    rw [hTl_eq]
    ext x; constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨i, -, rfl⟩
      change τ (last i) ∈ S
      rw [hτi i]
      exact (eS i).2
    · intro hx
      refine Finset.mem_image.mpr ⟨last (eS.symm ⟨x, hx⟩), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨eS.symm ⟨x, hx⟩, Finset.mem_univ _, rfl⟩
      · change τ (last (eS.symm ⟨x, hx⟩)) = x
        rw [hτi (eS.symm ⟨x, hx⟩)]; simp
  let D : MulAut (Fin m → Multiplicative (ZMod p)) := diagAut s hs
  let N : MulAut (Fin m → Multiplicative (ZMod p)) := permAut (p := p) τ
  let P : MulAut (Fin m → Multiplicative (ZMod p)) := D * N
  let Θ' : ((Fin m → Multiplicative (ZMod p)) × W₀) ≃* ↥Bs :=
    (MulEquiv.prodCongr P (MulEquiv.refl W₀)).trans Θ
  have hlift : liftBs (Bs := Bs) Θ' =
      (liftBs (Bs := Bs) Θ).comp (MulAut.conj P).toMonoidHom :=
    liftBs_prodCongr Θ P
  have hD_eq : (evenSignedAut m p).map (MulAut.conj D).toMonoidHom = evenSignedAut m p :=
    tbD3_evenSignedAut_map_conj_diag s hs
  have hN_eq : (evenSignedAut m p).map (MulAut.conj N).toMonoidHom = evenSignedAut m p :=
    tbD3_evenSignedAut_map_conj_perm τ
  have hP_eq : (evenSignedAut m p).map (MulAut.conj P).toMonoidHom = evenSignedAut m p := by
    have hPN : (MulAut.conj P).toMonoidHom =
        (MulAut.conj D).toMonoidHom.comp (MulAut.conj N).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [show MulAut.conj D (MulAut.conj N x) = MulAut.conj (D * N) x from
        conj_apply_comp D N x]
    rw [hPN, ← Subgroup.map_map, hN_eq, hD_eq]
  have hX' : ggAutomizer X Bs = (evenSignedAut m p).map (liftBs Θ') := by
    rw [hX, hlift, ← Subgroup.map_map, hP_eq]
  obtain ⟨V, instV, instMod, ι, φ, h, α, hlin, hrefl, hpair, ⟨f, hf⟩, hclos, hφexplicit⟩ :=
    exists_typeD_datum_of_evenSignedAut (G := G) (p := p) (m := m) hp2 hm hBs Θ' hX'
  letI : AddCommGroup V := instV
  letI : Module (ZMod p) V := instMod
  have hSN : permSupportedAut m p S =
      (permSupportedAut m p Tl).map (MulAut.conj N).toMonoidHom := by
    rw [← hTlτ]
    exact (permSupportedAut_map_conj τ Tl).symm
  have hJ'_orig : ggAutomizer J Bs = (permSupportedAut m p Tl).map (liftBs Θ') := by
    rw [hJ, hlift]
    calc (twistedPermAut m p S s hs).map (liftBs Θ)
        = ((permSupportedAut m p S).map (MulAut.conj D).toMonoidHom).map (liftBs Θ) := by
            rw [show twistedPermAut m p S s hs =
              (permSupportedAut m p S).map (MulAut.conj D).toMonoidHom from rfl]
      _ = (permSupportedAut m p S).map ((liftBs Θ).comp (MulAut.conj D).toMonoidHom) := by
            rw [Subgroup.map_map]
      _ = ((permSupportedAut m p Tl).map (MulAut.conj N).toMonoidHom).map
              ((liftBs Θ).comp (MulAut.conj D).toMonoidHom) := by rw [hSN]
      _ = (permSupportedAut m p Tl).map
              (((liftBs Θ).comp (MulAut.conj D).toMonoidHom).comp
                (MulAut.conj N).toMonoidHom) := by rw [Subgroup.map_map]
      _ = (permSupportedAut m p Tl).map
              ((liftBs Θ).comp (MulAut.conj P).toMonoidHom) := by
            have hhom : ((liftBs Θ).comp (MulAut.conj D).toMonoidHom).comp
                (MulAut.conj N).toMonoidHom =
                (liftBs Θ).comp (MulAut.conj P).toMonoidHom := by
              ext x
              simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
              rw [conj_apply_comp D N x]
            rw [hhom]
  have hJ_fin : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Fin m // m - b ≤ j.val ∧ j.val + 1 < m} => φ j) := by
    rw [hJ'_orig, tbD3_permSupportedAut_last_eq_adjacent hb2 hbm, MonoidHom.map_closure,
      ← Set.range_comp]
    apply congrArg Subgroup.closure
    ext x; constructor
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      change φ j.1 = (liftBs Θ') (permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, j.2.2⟩))
      rw [hφexplicit j.1]
      refine congrArg (liftBs Θ') ?_
      unfold typeDSimple
      rw [dif_pos j.2.2]
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      change (liftBs Θ') (permAut (p := p) (Equiv.swap j.1 ⟨j.1.val + 1, j.2.2⟩)) = φ j.1
      rw [hφexplicit j.1]
      refine congrArg (liftBs Θ') ?_
      unfold typeDSimple
      rw [dif_pos j.2.2]
  have hres := ggTBJTypeDParabolicLE3_endA (G := G) (p := p) (Bs := Bs) (X := X) (J := J)
    (n := m) (m := b) hp2 hb2 hbm (by omega) hm
    (M := ggCoxeterMatrixD m) (C := CartanMatrix.D m) rfl rfl
    (V := V) (ι := ι) (φ := φ) (h := h) (α := α) hlin hrefl hpair (f := f) hf hclos hJ_fin
  constructor
  · intro hc1
    exact hres.1 (by omega)
  · intro hc2
    exact hres.2 (by omega)

end TypeDDatum

end CFSG.StandardType

end
