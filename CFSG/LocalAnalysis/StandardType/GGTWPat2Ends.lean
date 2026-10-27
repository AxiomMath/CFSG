module

public import CFSG.LocalAnalysis.StandardType.GGTWPat2Base
public import CFSG.LocalAnalysis.StandardType.GGTwoDepSmallS0
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGResLeaf

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
theorem ggTWPat2_ends {N : ℕ} (hN : 5 ≤ N)
    {Λa : Type} [Fintype Λa] [DecidableEq Λa] (hΛa : Nat.card Λa = 2)
    {MK : CoxeterMatrix ({c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} ⊕ Λa)}
    {CK : Matrix ({c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} ⊕ Λa)
      ({c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} ⊕ Λa) ℤ}
    (hCK : GGIntCartan MK CK)
    (hA : ∃ e : Fin (N - 1) ≃ ({c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val} ⊕ Λa),
      MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hJ : ∀ i j : {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val},
      CK (Sum.inl i) (Sum.inl j) = CartanMatrix.A (N - 1) i.1 j.1) :
    ∃ (a₁ a₂ : Λa) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))), a₁ ≠ a₂ ∧
      GGTWPat2 N GGTWPos.ends c.val (c₂.map Fin.val) ∧
      (∀ j : {c : Fin (N - 1) // ggTWInJ N GGTWPos.ends c.val},
        CK (Sum.inr a₁) (Sum.inl j) = (if j.1 = c then -1 else 0) ∧
          CK (Sum.inl j) (Sum.inr a₁) = (if j.1 = c then -1 else 0) ∧
          CK (Sum.inr a₂) (Sum.inl j) = (if some j.1 = c₂ then -1 else 0) ∧
          CK (Sum.inl j) (Sum.inr a₂) = (if some j.1 = c₂ then -1 else 0)) ∧
      CK (Sum.inr a₁) (Sum.inr a₂) = (if c₂ = none then -1 else 0) ∧
      CK (Sum.inr a₂) (Sum.inr a₁) = (if c₂ = none then -1 else 0) ∧
      CK (Sum.inr a₁) (Sum.inr a₁) = 2 ∧ CK (Sum.inr a₂) (Sum.inr a₂) = 2 := by
  obtain ⟨e, he⟩ := hA
  let p : Λa → Fin (N - 1) := fun a => e.symm (Sum.inr a)
  have hp_inj : Function.Injective p := by
    intro a b hab
    exact Sum.inr.inj (e.symm.injective hab)
  have hpe : ∀ a (m : Fin (N - 3)), p a ≠ e.symm (Sum.inl (ggTWPat2_xiE N m)) := by
    intro a m h
    exact Sum.inr_ne_inl (e.symm.injective h)
  let g : Fin (N - 3) → Fin (N - 1) := fun k => e.symm (Sum.inl (ggTWPat2_xiE N k))
  have hg_inj : Function.Injective g := by
    intro a b hab
    have h1 : Sum.inl (ggTWPat2_xiE N a) = Sum.inl (ggTWPat2_xiE N b) := e.symm.injective hab
    have h2 : ggTWPat2_xiE N a = ggTWPat2_xiE N b := Sum.inl.inj h1
    exact (ggTWPat2_xiE N).injective h2
  have hpath := ggTWPat2_path hCK e he hJ (ggTWPat2_xiE N) 1 (fun k => rfl) g (fun k => rfl)
  have hL : 2 ≤ N - 3 := by omega
  rcases ggTWPat2_path_embed hL g hg_inj hpath with ⟨c0, hc0⟩ | ⟨c1, hc1⟩
  · have hc0le : c0 ≤ 2 := by
      have h := hc0 ⟨N - 4, by omega⟩
      simp only [Fin.val_mk] at h
      have hlt := (g ⟨N - 4, by omega⟩).isLt
      omega
    rcases (by omega : c0 = 0 ∨ c0 = 1 ∨ c0 = 2) with rfl | rfl | rfl
    ·
      have hb : ∀ k : Fin (N - 3), (g k).val = k.val := by
        intro k; have := hc0 k; omega
      let u : Fin (N - 1) := ⟨N - 3, by omega⟩
      let v : Fin (N - 1) := ⟨N - 2, by omega⟩
      have huv : u ≠ v := by
        intro h; have := congrArg Fin.val h; simp only [u, v, Fin.val_mk] at this; omega
      have hp_mem : ∀ a : Λa, p a = u ∨ p a = v := by
        intro a
        have hlt : (p a).val < N - 1 := (p a).isLt
        have hnot : ¬ ((p a).val ≤ N - 4) := by
          intro hle
          have hk : (p a).val < N - 3 := by omega
          have hg : g ⟨(p a).val, hk⟩ = p a := by
            apply Fin.ext; rw [hb]
          exact hpe a ⟨(p a).val, hk⟩ hg.symm
        have hv : (p a).val = N - 3 ∨ (p a).val = N - 2 := by omega
        rcases hv with h | h
        · left; apply Fin.ext; simpa [u] using h
        · right; apply Fin.ext; simpa [v] using h
      obtain ⟨a₁, a₂, hne, ha₁, ha₂⟩ := ggTWPat2_two_preimages hΛa p hp_inj huv hp_mem
      have hpa₁ : (p a₁).val = N - 3 := by rw [ha₁]
      have hpa₂ : (p a₂).val = N - 2 := by rw [ha₂]
      let k : Fin (N - 3) := ⟨N - 4, by omega⟩
      let c : Fin (N - 1) := (ggTWPat2_xiE N k).val
      have hc : c = (ggTWPat2_xiE N k).val := rfl
      have hadj₁ : ∀ m : Fin (N - 3),
          ((e.symm (Sum.inr a₁)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
           (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₁)).val) ↔ m = k := by
        intro m
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₁' : (e.symm (Sum.inr a₁)).val = N - 3 := hpa₁
        rw [hgm, hb m]
        constructor
        · intro h; apply Fin.ext; dsimp [k]; omega
        · intro h; rw [h]; right; dsimp [k]; omega
      have hno₂ : ∀ m : Fin (N - 3),
          ¬ ((e.symm (Sum.inr a₂)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
             (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₂)).val) := by
        intro m h
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₂' : (e.symm (Sum.inr a₂)).val = N - 2 := hpa₂
        rw [hgm, hb m] at h
        omega
      have hpat : GGTWPat2 N GGTWPos.ends c.val ((none : Option (Fin (N - 1))).map Fin.val) := by
        have hcv : c.val = N - 3 := by dsimp [c, k, ggTWPat2_xiE]; omega
        simp only [GGTWPat2, ggTWInJ, ggTWPlace, Option.map_none]
        exact ⟨⟨by omega, by omega⟩, Or.inr (by omega), trivial⟩
      have hp₁ := ggTWPat2_cross hCK e he (ggTWPat2_xiE N) a₁ k c hc hadj₁
      have hp₂ := ggTWPat2_cross_zero hCK e he (ggTWPat2_xiE N) a₂ hno₂
      have hpair := ggTWPat2_inr_adj hCK e he a₁ a₂ hne (by
        show (p a₁).val + 1 = (p a₂).val ∨ (p a₂).val + 1 = (p a₁).val
        left; rw [hpa₁, hpa₂]; omega)
      refine ⟨a₁, a₂, c, none, hne, hpat, ?_, hpair.1, hpair.2,
        hCK.1 (Sum.inr a₁), hCK.1 (Sum.inr a₂)⟩
      intro j
      refine ⟨(hp₁ j).1, (hp₁ j).2, ?_, ?_⟩
      · rw [show (if some j.1 = (none : Option (Fin (N - 1))) then -1 else 0) = 0 by simp]
        exact (hp₂ j).1
      · rw [show (if some j.1 = (none : Option (Fin (N - 1))) then -1 else 0) = 0 by simp]
        exact (hp₂ j).2
    ·
      have hb : ∀ k : Fin (N - 3), (g k).val = 1 + k.val := by
        intro k; have := hc0 k; omega
      let u : Fin (N - 1) := ⟨0, by omega⟩
      let v : Fin (N - 1) := ⟨N - 2, by omega⟩
      have huv : u ≠ v := by
        intro h; have := congrArg Fin.val h; simp only [u, v, Fin.val_mk] at this; omega
      have hp_mem : ∀ a : Λa, p a = u ∨ p a = v := by
        intro a
        have hlt : (p a).val < N - 1 := (p a).isLt
        have hnot : ¬ (1 ≤ (p a).val ∧ (p a).val ≤ N - 3) := by
          intro hmem
          have hk : (p a).val - 1 < N - 3 := by omega
          have hg : g ⟨(p a).val - 1, hk⟩ = p a := by
            apply Fin.ext; rw [hb]; dsimp only; omega
          exact hpe a ⟨(p a).val - 1, hk⟩ hg.symm
        have hv : (p a).val = 0 ∨ (p a).val = N - 2 := by omega
        rcases hv with h | h
        · left; apply Fin.ext; simpa [u] using h
        · right; apply Fin.ext; simpa [v] using h
      obtain ⟨a₁, a₂, hne, ha₁, ha₂⟩ := ggTWPat2_two_preimages hΛa p hp_inj huv hp_mem
      have hpa₁ : (p a₁).val = 0 := by rw [ha₁]
      have hpa₂ : (p a₂).val = N - 2 := by rw [ha₂]
      let k₁ : Fin (N - 3) := ⟨0, by omega⟩
      let c : Fin (N - 1) := (ggTWPat2_xiE N k₁).val
      have hc : c = (ggTWPat2_xiE N k₁).val := rfl
      have hadj₁ : ∀ m : Fin (N - 3),
          ((e.symm (Sum.inr a₁)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
           (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₁)).val) ↔ m = k₁ := by
        intro m
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₁' : (e.symm (Sum.inr a₁)).val = 0 := hpa₁
        rw [hgm, hb m]
        constructor
        · intro h; apply Fin.ext; dsimp [k₁]; omega
        · intro h; rw [h]; left; dsimp [k₁]; omega
      let k₂ : Fin (N - 3) := ⟨N - 4, by omega⟩
      let c₂ : Option (Fin (N - 1)) := some (ggTWPat2_xiE N k₂).val
      have hc₂ : c₂ = some (ggTWPat2_xiE N k₂).val := rfl
      have hadj₂ : ∀ m : Fin (N - 3),
          ((e.symm (Sum.inr a₂)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
           (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₂)).val) ↔ m = k₂ := by
        intro m
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₂' : (e.symm (Sum.inr a₂)).val = N - 2 := hpa₂
        rw [hgm, hb m]
        constructor
        · intro h; apply Fin.ext; dsimp [k₂]; omega
        · intro h; rw [h]; right; dsimp [k₂]; omega
      have hpat : GGTWPat2 N GGTWPos.ends c.val (c₂.map Fin.val) := by
        have hcv : c.val = 1 := by dsimp [c, k₁, ggTWPat2_xiE]
        have hc₂v : ((ggTWPat2_xiE N k₂).val).val = N - 3 := by dsimp [k₂, ggTWPat2_xiE]; omega
        simp only [GGTWPat2, ggTWInJ, ggTWPlace, Option.map_some]
        refine ⟨⟨by omega, by omega⟩, Or.inl (by omega),
          ⟨⟨by omega, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩⟩
      have hp₁ := ggTWPat2_cross hCK e he (ggTWPat2_xiE N) a₁ k₁ c hc hadj₁
      have hp₂ := ggTWPat2_cross hCK e he (ggTWPat2_xiE N) a₂ k₂ (ggTWPat2_xiE N k₂).val rfl hadj₂
      have hpair := ggTWPat2_inr_nonadj hCK e he a₁ a₂ hne (by
        show ¬ ((p a₁).val + 1 = (p a₂).val ∨ (p a₂).val + 1 = (p a₁).val)
        rw [hpa₁, hpa₂]; omega)
      refine ⟨a₁, a₂, c, c₂, hne, hpat, ?_, hpair.1, hpair.2,
        hCK.1 (Sum.inr a₁), hCK.1 (Sum.inr a₂)⟩
      intro j
      refine ⟨(hp₁ j).1, (hp₁ j).2, ?_, ?_⟩
      · rw [show (if some j.1 = c₂ then -1 else 0) =
            (if j.1 = (ggTWPat2_xiE N k₂).val then -1 else 0) by simp [c₂]]
        exact (hp₂ j).1
      · rw [show (if some j.1 = c₂ then -1 else 0) =
            (if j.1 = (ggTWPat2_xiE N k₂).val then -1 else 0) by simp [c₂]]
        exact (hp₂ j).2
    ·
      have hb : ∀ k : Fin (N - 3), (g k).val = 2 + k.val := by
        intro k; have := hc0 k; omega
      let u : Fin (N - 1) := ⟨1, by omega⟩
      let v : Fin (N - 1) := ⟨0, by omega⟩
      have huv : u ≠ v := by
        intro h; have := congrArg Fin.val h; simp only [u, v, Fin.val_mk] at this; omega
      have hp_mem : ∀ a : Λa, p a = u ∨ p a = v := by
        intro a
        have hlt : (p a).val < N - 1 := (p a).isLt
        have hnot : ¬ (2 ≤ (p a).val) := by
          intro hle
          have hk : (p a).val - 2 < N - 3 := by omega
          have hg : g ⟨(p a).val - 2, hk⟩ = p a := by
            apply Fin.ext; rw [hb]; dsimp only; omega
          exact hpe a ⟨(p a).val - 2, hk⟩ hg.symm
        have hv : (p a).val = 0 ∨ (p a).val = 1 := by omega
        rcases hv with h | h
        · right; apply Fin.ext; simpa [v] using h
        · left; apply Fin.ext; simpa [u] using h
      obtain ⟨a₁, a₂, hne, ha₁, ha₂⟩ := ggTWPat2_two_preimages hΛa p hp_inj huv hp_mem
      have hpa₁ : (p a₁).val = 1 := by rw [ha₁]
      have hpa₂ : (p a₂).val = 0 := by rw [ha₂]
      let k : Fin (N - 3) := ⟨0, by omega⟩
      let c : Fin (N - 1) := (ggTWPat2_xiE N k).val
      have hc : c = (ggTWPat2_xiE N k).val := rfl
      have hadj₁ : ∀ m : Fin (N - 3),
          ((e.symm (Sum.inr a₁)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
           (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₁)).val) ↔ m = k := by
        intro m
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₁' : (e.symm (Sum.inr a₁)).val = 1 := hpa₁
        rw [hgm, hb m]
        constructor
        · intro h; apply Fin.ext; dsimp [k]; omega
        · intro h; rw [h]; left; dsimp [k]; omega
      have hno₂ : ∀ m : Fin (N - 3),
          ¬ ((e.symm (Sum.inr a₂)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
             (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₂)).val) := by
        intro m h
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₂' : (e.symm (Sum.inr a₂)).val = 0 := hpa₂
        rw [hgm, hb m] at h
        omega
      have hpat : GGTWPat2 N GGTWPos.ends c.val ((none : Option (Fin (N - 1))).map Fin.val) := by
        have hcv : c.val = 1 := by dsimp [c, k, ggTWPat2_xiE]
        simp only [GGTWPat2, ggTWInJ, ggTWPlace, Option.map_none]
        exact ⟨⟨by omega, by omega⟩, Or.inl (by omega), trivial⟩
      have hp₁ := ggTWPat2_cross hCK e he (ggTWPat2_xiE N) a₁ k c hc hadj₁
      have hp₂ := ggTWPat2_cross_zero hCK e he (ggTWPat2_xiE N) a₂ hno₂
      have hpair := ggTWPat2_inr_adj hCK e he a₁ a₂ hne (by
        show (p a₁).val + 1 = (p a₂).val ∨ (p a₂).val + 1 = (p a₁).val
        right; rw [hpa₁, hpa₂])
      refine ⟨a₁, a₂, c, none, hne, hpat, ?_, hpair.1, hpair.2,
        hCK.1 (Sum.inr a₁), hCK.1 (Sum.inr a₂)⟩
      intro j
      refine ⟨(hp₁ j).1, (hp₁ j).2, ?_, ?_⟩
      · rw [show (if some j.1 = (none : Option (Fin (N - 1))) then -1 else 0) = 0 by simp]
        exact (hp₂ j).1
      · rw [show (if some j.1 = (none : Option (Fin (N - 1))) then -1 else 0) = 0 by simp]
        exact (hp₂ j).2
  · have hc1le : c1 ≤ N - 2 := by
      have h := hc1 ⟨0, by omega⟩
      simp only [Fin.val_mk] at h
      have hlt := (g ⟨0, by omega⟩).isLt
      omega
    have hc1ge : N - 4 ≤ c1 := by
      have h := hc1 ⟨N - 4, by omega⟩
      simp only [Fin.val_mk] at h
      omega
    rcases (by omega : c1 = N - 4 ∨ c1 = N - 3 ∨ c1 = N - 2) with rfl | rfl | rfl
    ·
      have hb : ∀ k : Fin (N - 3), (g k).val = N - 4 - k.val := by
        intro k; have := hc1 k; omega
      let u : Fin (N - 1) := ⟨N - 3, by omega⟩
      let v : Fin (N - 1) := ⟨N - 2, by omega⟩
      have huv : u ≠ v := by
        intro h; have := congrArg Fin.val h; simp only [u, v, Fin.val_mk] at this; omega
      have hp_mem : ∀ a : Λa, p a = u ∨ p a = v := by
        intro a
        have hlt : (p a).val < N - 1 := (p a).isLt
        have hnot : ¬ ((p a).val ≤ N - 4) := by
          intro hle
          have hk : N - 4 - (p a).val < N - 3 := by omega
          have hg : g ⟨N - 4 - (p a).val, hk⟩ = p a := by
            apply Fin.ext; rw [hb]; dsimp only; omega
          exact hpe a ⟨N - 4 - (p a).val, hk⟩ hg.symm
        have hv : (p a).val = N - 3 ∨ (p a).val = N - 2 := by omega
        rcases hv with h | h
        · left; apply Fin.ext; simpa [u] using h
        · right; apply Fin.ext; simpa [v] using h
      obtain ⟨a₁, a₂, hne, ha₁, ha₂⟩ := ggTWPat2_two_preimages hΛa p hp_inj huv hp_mem
      have hpa₁ : (p a₁).val = N - 3 := by rw [ha₁]
      have hpa₂ : (p a₂).val = N - 2 := by rw [ha₂]
      let k : Fin (N - 3) := ⟨0, by omega⟩
      let c : Fin (N - 1) := (ggTWPat2_xiE N k).val
      have hc : c = (ggTWPat2_xiE N k).val := rfl
      have hadj₁ : ∀ m : Fin (N - 3),
          ((e.symm (Sum.inr a₁)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
           (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₁)).val) ↔ m = k := by
        intro m
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₁' : (e.symm (Sum.inr a₁)).val = N - 3 := hpa₁
        rw [hgm, hb m]
        constructor
        · intro h; apply Fin.ext; dsimp [k]; omega
        · intro h; rw [h]; right; dsimp [k]; omega
      have hno₂ : ∀ m : Fin (N - 3),
          ¬ ((e.symm (Sum.inr a₂)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
             (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₂)).val) := by
        intro m h
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₂' : (e.symm (Sum.inr a₂)).val = N - 2 := hpa₂
        rw [hgm, hb m] at h
        omega
      have hpat : GGTWPat2 N GGTWPos.ends c.val ((none : Option (Fin (N - 1))).map Fin.val) := by
        have hcv : c.val = 1 := by dsimp [c, k, ggTWPat2_xiE]
        simp only [GGTWPat2, ggTWInJ, ggTWPlace, Option.map_none]
        exact ⟨⟨by omega, by omega⟩, Or.inl (by omega), trivial⟩
      have hp₁ := ggTWPat2_cross hCK e he (ggTWPat2_xiE N) a₁ k c hc hadj₁
      have hp₂ := ggTWPat2_cross_zero hCK e he (ggTWPat2_xiE N) a₂ hno₂
      have hpair := ggTWPat2_inr_adj hCK e he a₁ a₂ hne (by
        show (p a₁).val + 1 = (p a₂).val ∨ (p a₂).val + 1 = (p a₁).val
        left; rw [hpa₁, hpa₂]; omega)
      refine ⟨a₁, a₂, c, none, hne, hpat, ?_, hpair.1, hpair.2,
        hCK.1 (Sum.inr a₁), hCK.1 (Sum.inr a₂)⟩
      intro j
      refine ⟨(hp₁ j).1, (hp₁ j).2, ?_, ?_⟩
      · rw [show (if some j.1 = (none : Option (Fin (N - 1))) then -1 else 0) = 0 by simp]
        exact (hp₂ j).1
      · rw [show (if some j.1 = (none : Option (Fin (N - 1))) then -1 else 0) = 0 by simp]
        exact (hp₂ j).2
    ·
      have hb : ∀ k : Fin (N - 3), (g k).val = N - 3 - k.val := by
        intro k; have := hc1 k; omega
      let u : Fin (N - 1) := ⟨0, by omega⟩
      let v : Fin (N - 1) := ⟨N - 2, by omega⟩
      have huv : u ≠ v := by
        intro h; have := congrArg Fin.val h; simp only [u, v, Fin.val_mk] at this; omega
      have hp_mem : ∀ a : Λa, p a = u ∨ p a = v := by
        intro a
        have hlt : (p a).val < N - 1 := (p a).isLt
        have hnot : ¬ (1 ≤ (p a).val ∧ (p a).val ≤ N - 3) := by
          intro hmem
          have hk : N - 3 - (p a).val < N - 3 := by omega
          have hg : g ⟨N - 3 - (p a).val, hk⟩ = p a := by
            apply Fin.ext; rw [hb]; dsimp only; omega
          exact hpe a ⟨N - 3 - (p a).val, hk⟩ hg.symm
        have hv : (p a).val = 0 ∨ (p a).val = N - 2 := by omega
        rcases hv with h | h
        · left; apply Fin.ext; simpa [u] using h
        · right; apply Fin.ext; simpa [v] using h
      obtain ⟨a₁, a₂, hne, ha₁, ha₂⟩ := ggTWPat2_two_preimages hΛa p hp_inj huv hp_mem
      have hpa₁ : (p a₁).val = 0 := by rw [ha₁]
      have hpa₂ : (p a₂).val = N - 2 := by rw [ha₂]
      let k₁ : Fin (N - 3) := ⟨N - 4, by omega⟩
      let c : Fin (N - 1) := (ggTWPat2_xiE N k₁).val
      have hc : c = (ggTWPat2_xiE N k₁).val := rfl
      have hadj₁ : ∀ m : Fin (N - 3),
          ((e.symm (Sum.inr a₁)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
           (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₁)).val) ↔ m = k₁ := by
        intro m
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₁' : (e.symm (Sum.inr a₁)).val = 0 := hpa₁
        rw [hgm, hb m]
        constructor
        · intro h; apply Fin.ext; dsimp [k₁]; omega
        · intro h; rw [h]; left; dsimp [k₁]; omega
      let k₂ : Fin (N - 3) := ⟨0, by omega⟩
      let c₂ : Option (Fin (N - 1)) := some (ggTWPat2_xiE N k₂).val
      have hc₂ : c₂ = some (ggTWPat2_xiE N k₂).val := rfl
      have hadj₂ : ∀ m : Fin (N - 3),
          ((e.symm (Sum.inr a₂)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
           (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₂)).val) ↔ m = k₂ := by
        intro m
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₂' : (e.symm (Sum.inr a₂)).val = N - 2 := hpa₂
        rw [hgm, hb m]
        constructor
        · intro h; apply Fin.ext; dsimp [k₂]; omega
        · intro h; rw [h]; right; dsimp [k₂]; omega
      have hpat : GGTWPat2 N GGTWPos.ends c.val (c₂.map Fin.val) := by
        have hcv : c.val = N - 3 := by dsimp [c, k₁, ggTWPat2_xiE]; omega
        have hc₂v : ((ggTWPat2_xiE N k₂).val).val = 1 := by dsimp [k₂, ggTWPat2_xiE]
        simp only [GGTWPat2, ggTWInJ, ggTWPlace, Option.map_some]
        refine ⟨⟨by omega, by omega⟩, Or.inr (by omega),
          ⟨⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega⟩⟩⟩
      have hp₁ := ggTWPat2_cross hCK e he (ggTWPat2_xiE N) a₁ k₁ c hc hadj₁
      have hp₂ := ggTWPat2_cross hCK e he (ggTWPat2_xiE N) a₂ k₂ (ggTWPat2_xiE N k₂).val rfl hadj₂
      have hpair := ggTWPat2_inr_nonadj hCK e he a₁ a₂ hne (by
        show ¬ ((p a₁).val + 1 = (p a₂).val ∨ (p a₂).val + 1 = (p a₁).val)
        rw [hpa₁, hpa₂]; omega)
      refine ⟨a₁, a₂, c, c₂, hne, hpat, ?_, hpair.1, hpair.2,
        hCK.1 (Sum.inr a₁), hCK.1 (Sum.inr a₂)⟩
      intro j
      refine ⟨(hp₁ j).1, (hp₁ j).2, ?_, ?_⟩
      · rw [show (if some j.1 = c₂ then -1 else 0) =
            (if j.1 = (ggTWPat2_xiE N k₂).val then -1 else 0) by simp [c₂]]
        exact (hp₂ j).1
      · rw [show (if some j.1 = c₂ then -1 else 0) =
            (if j.1 = (ggTWPat2_xiE N k₂).val then -1 else 0) by simp [c₂]]
        exact (hp₂ j).2
    ·
      have hb : ∀ k : Fin (N - 3), (g k).val = N - 2 - k.val := by
        intro k; have := hc1 k; omega
      let u : Fin (N - 1) := ⟨1, by omega⟩
      let v : Fin (N - 1) := ⟨0, by omega⟩
      have huv : u ≠ v := by
        intro h; have := congrArg Fin.val h; simp only [u, v, Fin.val_mk] at this; omega
      have hp_mem : ∀ a : Λa, p a = u ∨ p a = v := by
        intro a
        have hlt : (p a).val < N - 1 := (p a).isLt
        have hnot : ¬ (2 ≤ (p a).val ∧ (p a).val ≤ N - 2) := by
          intro hmem
          have hk : N - 2 - (p a).val < N - 3 := by omega
          have hg : g ⟨N - 2 - (p a).val, hk⟩ = p a := by
            apply Fin.ext; rw [hb]; dsimp only; omega
          exact hpe a ⟨N - 2 - (p a).val, hk⟩ hg.symm
        have hv : (p a).val = 0 ∨ (p a).val = 1 := by omega
        rcases hv with h | h
        · right; apply Fin.ext; simpa [v] using h
        · left; apply Fin.ext; simpa [u] using h
      obtain ⟨a₁, a₂, hne, ha₁, ha₂⟩ := ggTWPat2_two_preimages hΛa p hp_inj huv hp_mem
      have hpa₁ : (p a₁).val = 1 := by rw [ha₁]
      have hpa₂ : (p a₂).val = 0 := by rw [ha₂]
      let k : Fin (N - 3) := ⟨N - 4, by omega⟩
      let c : Fin (N - 1) := (ggTWPat2_xiE N k).val
      have hc : c = (ggTWPat2_xiE N k).val := rfl
      have hadj₁ : ∀ m : Fin (N - 3),
          ((e.symm (Sum.inr a₁)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
           (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₁)).val) ↔ m = k := by
        intro m
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₁' : (e.symm (Sum.inr a₁)).val = 1 := hpa₁
        rw [hgm, hb m]
        constructor
        · intro h; apply Fin.ext; dsimp [k]; omega
        · intro h; rw [h]; left; dsimp [k]; omega
      have hno₂ : ∀ m : Fin (N - 3),
          ¬ ((e.symm (Sum.inr a₂)).val + 1 = (e.symm (Sum.inl (ggTWPat2_xiE N m))).val ∨
             (e.symm (Sum.inl (ggTWPat2_xiE N m))).val + 1 = (e.symm (Sum.inr a₂)).val) := by
        intro m h
        have hgm : (e.symm (Sum.inl (ggTWPat2_xiE N m))).val = (g m).val := rfl
        have hpa₂' : (e.symm (Sum.inr a₂)).val = 0 := hpa₂
        rw [hgm, hb m] at h
        omega
      have hpat : GGTWPat2 N GGTWPos.ends c.val ((none : Option (Fin (N - 1))).map Fin.val) := by
        have hcv : c.val = N - 3 := by dsimp [c, k, ggTWPat2_xiE]; omega
        simp only [GGTWPat2, ggTWInJ, ggTWPlace, Option.map_none]
        exact ⟨⟨by omega, by omega⟩, Or.inr (by omega), trivial⟩
      have hp₁ := ggTWPat2_cross hCK e he (ggTWPat2_xiE N) a₁ k c hc hadj₁
      have hp₂ := ggTWPat2_cross_zero hCK e he (ggTWPat2_xiE N) a₂ hno₂
      have hpair := ggTWPat2_inr_adj hCK e he a₁ a₂ hne (by
        show (p a₁).val + 1 = (p a₂).val ∨ (p a₂).val + 1 = (p a₁).val
        right; rw [hpa₁, hpa₂])
      refine ⟨a₁, a₂, c, none, hne, hpat, ?_, hpair.1, hpair.2,
        hCK.1 (Sum.inr a₁), hCK.1 (Sum.inr a₂)⟩
      intro j
      refine ⟨(hp₁ j).1, (hp₁ j).2, ?_, ?_⟩
      · rw [show (if some j.1 = (none : Option (Fin (N - 1))) then -1 else 0) = 0 by simp]
        exact (hp₂ j).1
      · rw [show (if some j.1 = (none : Option (Fin (N - 1))) then -1 else 0) = 0 by simp]
        exact (hp₂ j).2

end CFSG.StandardType
