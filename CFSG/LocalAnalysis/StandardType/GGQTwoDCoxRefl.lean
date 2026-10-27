module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
public import CFSG.LocalAnalysis.StandardType.GGQTwoDPatterns

public section

namespace CFSG.StandardType.QTwo

theorem qtwoParabRefl_conj {m : ℕ} {u r : (ggCoxeterMatrixD m).Group}
    (hu : u ∈ Subgroup.closure
      ((ggCoxeterMatrixD m).simple '' {j : Fin m | (j : ℕ) ≠ 0}))
    (hr : r ∈ qtwoParabRefl m) : u * r * u⁻¹ ∈ qtwoParabRefl m := by
  obtain ⟨i, hi, v, hv, rfl⟩ := hr
  exact ⟨i, hi, u * v, Subgroup.mul_mem _ hu hv, by group⟩

@[expose] noncomputable def dPermW {m : ℕ} (e : (ggCoxeterMatrixD m).Group ≃* dEven m)
    (π : Equiv.Perm (Fin m)) : (ggCoxeterMatrixD m).Group :=
  e.symm ⟨dPerm m π, dPerm_mem_dEven m π⟩

private theorem plh_e_dPermW {m : ℕ} (e : (ggCoxeterMatrixD m).Group ≃* dEven m)
    (π : Equiv.Perm (Fin m)) :
    ((e (dPermW e π) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dPerm m π := by
  rw [dPermW, MulEquiv.apply_symm_apply]

private theorem plh_e_simple_of_lt {m : ℕ} {e : (ggCoxeterMatrixD m).Group ≃* dEven m}
    (he : IsDEquiv m e) {j : Fin m} (hj : j.val + 1 < m) :
    ((e ((ggCoxeterMatrixD m).simple j) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      dTau m false j ⟨j.val + 1, hj⟩ := by
  have hdec : decide (j.val + 1 = m) = false := by
    have hne : j.val + 1 ≠ m := by omega
    simp [hne]
  have hlo : OrthTorus.simpleLo j = j := Fin.ext (OrthTorus.simpleLo_of_lt hj)
  have hhi : OrthTorus.simpleHi j = ⟨j.val + 1, hj⟩ :=
    Fin.ext (OrthTorus.simpleHi_of_lt hj)
  rw [he j, hdec, hlo, hhi]

private theorem plh_e_simple_last {m : ℕ} (hm : 4 ≤ m)
    {e : (ggCoxeterMatrixD m).Group ≃* dEven m} (he : IsDEquiv m e)
    {t : Fin m} (ht : t.val + 1 = m) :
    ((e ((ggCoxeterMatrixD m).simple t) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      dTau m true ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩ := by
  have hdec : decide (t.val + 1 = m) = true := by
    rw [ht]
    simp
  have hlo : OrthTorus.simpleLo t = ⟨m - 2, by omega⟩ :=
    Fin.ext (OrthTorus.simpleLo_of_last ht)
  have hhi : OrthTorus.simpleHi t = ⟨m - 1, by omega⟩ :=
    Fin.ext (OrthTorus.simpleHi_of_last ht)
  rw [he t, hdec, hlo, hhi]

private theorem plh_conj_step {m : ℕ} {e : (ggCoxeterMatrixD m).Group ≃* dEven m}
    (he : IsDEquiv m e) {ε : Bool} {a b j : Fin m}
    (hj1 : 1 ≤ j.val) (hj2 : j.val + 1 < m)
    {r : (ggCoxeterMatrixD m).Group} (hr : r ∈ qtwoParabRefl m)
    (her : ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dTau m ε a b) :
    ∃ r' ∈ qtwoParabRefl m,
      ((e r' : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
        dTau m ε (Equiv.swap j ⟨j.val + 1, hj2⟩ a)
          (Equiv.swap j ⟨j.val + 1, hj2⟩ b) := by
  let j' : Fin m := ⟨j.val + 1, hj2⟩
  have hmem : (ggCoxeterMatrixD m).simple j ∈ Subgroup.closure
      ((ggCoxeterMatrixD m).simple '' {k : Fin m | (k : ℕ) ≠ 0}) := by
    refine Subgroup.subset_closure ⟨j, ?_, rfl⟩
    simp only [Set.mem_setOf_eq]
    omega
  let r' : (ggCoxeterMatrixD m).Group :=
    (ggCoxeterMatrixD m).simple j * r * ((ggCoxeterMatrixD m).simple j)⁻¹
  have hr' : r' ∈ qtwoParabRefl m := qtwoParabRefl_conj hmem hr
  refine ⟨r', hr', ?_⟩
  have hsimple : ((e ((ggCoxeterMatrixD m).simple j) : dEven m) :
      DVec m ≃ₗ[ZMod 3] DVec m) = dPerm m (Equiv.swap j j') := by
    rw [plh_e_simple_of_lt he hj2]
    simp [dTau, j']
  calc
    ((e r' : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m)
        = ((e ((ggCoxeterMatrixD m).simple j * r *
            ((ggCoxeterMatrixD m).simple j)⁻¹) : dEven m) :
              DVec m ≃ₗ[ZMod 3] DVec m) := rfl
    _ = ((e ((ggCoxeterMatrixD m).simple j) * e r *
          (e ((ggCoxeterMatrixD m).simple j))⁻¹ : dEven m) :
            DVec m ≃ₗ[ZMod 3] DVec m) := by rw [map_mul, map_mul, map_inv]
    _ = ((e ((ggCoxeterMatrixD m).simple j) : dEven m) :
          DVec m ≃ₗ[ZMod 3] DVec m) * ((e r : dEven m) :
            DVec m ≃ₗ[ZMod 3] DVec m) *
          (((e ((ggCoxeterMatrixD m).simple j) : dEven m) :
            DVec m ≃ₗ[ZMod 3] DVec m))⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    _ = dPerm m (Equiv.swap j j') * dTau m ε a b *
          (dPerm m (Equiv.swap j j'))⁻¹ := by rw [hsimple, her]
    _ = dTau m ε (Equiv.swap j j' a) (Equiv.swap j j' b) :=
          dPerm_conj_dTau m (Equiv.swap j j') ε a b

private theorem plh_exists_false {m : ℕ} (hm : 4 ≤ m)
    {e : (ggCoxeterMatrixD m).Group ≃* dEven m} (he : IsDEquiv m e) :
    ∀ {a b : Fin m}, 1 ≤ a.val → a.val < b.val →
      ∃ r ∈ qtwoParabRefl m,
        ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dTau m false a b := by
  intro a b ha hab
  have key : ∀ d : ℕ, ∀ a b : Fin m, 1 ≤ a.val → b.val = a.val + 1 + d →
      ∃ r ∈ qtwoParabRefl m,
        ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dTau m false a b := by
    intro d
    induction d with
    | zero =>
        intro a b ha hb
        have hbval : b.val = a.val + 1 := by omega
        have hj : a.val + 1 < m := by omega
        have hb_eq : b = ⟨a.val + 1, hj⟩ := Fin.ext (by simp [hbval])
        refine ⟨(ggCoxeterMatrixD m).simple a, ?_, ?_⟩
        · exact simple_mem_qtwoParabRefl (by omega)
        · rw [plh_e_simple_of_lt he hj, hb_eq]
    | succ d ih =>
        intro a b ha hb
        have hbval : b.val = a.val + 2 + d := by omega
        let b' : Fin m := ⟨b.val - 1, by omega⟩
        have hb'val : b'.val = a.val + 1 + d := by simp [b']; omega
        obtain ⟨r, hr, her⟩ := ih a b' ha hb'val
        have hb'1 : 1 ≤ b'.val := by omega
        have hb'lt : b'.val + 1 < m := by simp [b']; omega
        let j' : Fin m := ⟨b'.val + 1, hb'lt⟩
        have hj'eq : j' = b := Fin.ext (by simp [j', b']; omega)
        obtain ⟨r', hr', her'⟩ := plh_conj_step (e := e) he hb'1 hb'lt hr her
        refine ⟨r', hr', ?_⟩
        have ha_ne_b' : a ≠ b' := by
          intro h
          have := congrArg Fin.val h
          omega
        have ha_ne_b : a ≠ b := by
          intro h
          have := congrArg Fin.val h
          omega
        have h1 : Equiv.swap b' j' a = a := by
          rw [hj'eq]
          exact Equiv.swap_apply_of_ne_of_ne ha_ne_b' ha_ne_b
        have h2 : Equiv.swap b' j' b' = b := by
          rw [hj'eq]
          exact Equiv.swap_apply_left b' b
        rw [her', h1, h2]
  have hb' : b.val = a.val + 1 + (b.val - 1 - a.val) := by omega
  exact key (b.val - 1 - a.val) a b ha hb'

private theorem plh_exists_true_last {m : ℕ} (hm : 4 ≤ m)
    {e : (ggCoxeterMatrixD m).Group ≃* dEven m} (he : IsDEquiv m e)
    {c : Fin m} (hc1 : 1 ≤ c.val) (hc2 : c.val + 1 ≤ m - 1) :
    ∃ r ∈ qtwoParabRefl m,
      ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
        dTau m true c ⟨m - 1, by omega⟩ := by
  have key : ∀ k : ℕ, ∀ c : Fin m, c.val = m - 2 - k → 1 ≤ c.val →
      ∃ r ∈ qtwoParabRefl m,
        ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
          dTau m true c ⟨m - 1, by omega⟩ := by
    intro k
    induction k with
    | zero =>
        intro c hc hc1
        have hcval : c.val = m - 2 := by omega
        have hc_eq : c = ⟨m - 2, by omega⟩ := Fin.ext hcval
        have hlt : m - 1 < m := by omega
        let last : Fin m := ⟨m - 1, hlt⟩
        have hlast_ht : last.val + 1 = m := by dsimp [last]; omega
        have hlast0 : (last : ℕ) ≠ 0 := by dsimp [last]; omega
        refine ⟨(ggCoxeterMatrixD m).simple last, ?_, ?_⟩
        · exact simple_mem_qtwoParabRefl hlast0
        · rw [plh_e_simple_last hm he (t := last) hlast_ht, hc_eq]
    | succ k ih =>
        intro c hc hc1
        have hcval : c.val + 1 = m - 2 - k := by omega
        let c' : Fin m := ⟨c.val + 1, by omega⟩
        have hc'val : c'.val = m - 2 - k := by simp [c']; omega
        have hc'1 : 1 ≤ c'.val := by simp [c']
        obtain ⟨r, hr, her⟩ := ih c' hc'val hc'1
        have hc_lt : c.val + 1 < m := by omega
        obtain ⟨r', hr', her'⟩ := plh_conj_step (e := e) he hc1 hc_lt hr her
        refine ⟨r', hr', ?_⟩
        have hlast_ne_c : (⟨m - 1, by omega⟩ : Fin m) ≠ c := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        have hlast_ne_c' : (⟨m - 1, by omega⟩ : Fin m) ≠ c' := by
          intro h
          have := congrArg Fin.val h
          simp [c'] at this
          omega
        have h1 : Equiv.swap c c' c' = c := Equiv.swap_apply_right c c'
        have h2 : Equiv.swap c c' (⟨m - 1, by omega⟩ : Fin m) =
            ⟨m - 1, by omega⟩ :=
          Equiv.swap_apply_of_ne_of_ne hlast_ne_c hlast_ne_c'
        rw [her', h1, h2]
  have hc_le : c.val ≤ m - 2 := by omega
  have hk : c.val = m - 2 - (m - 2 - c.val) := by omega
  exact key (m - 2 - c.val) c hk hc1

private theorem plh_exists_true {m : ℕ} (hm : 4 ≤ m)
    {e : (ggCoxeterMatrixD m).Group ≃* dEven m} (he : IsDEquiv m e) :
    ∀ {c d : Fin m}, 1 ≤ c.val → c.val < d.val →
      ∃ r ∈ qtwoParabRefl m,
        ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dTau m true c d := by
  intro c d hc hcd
  have key : ∀ k : ℕ, ∀ c d : Fin m, 1 ≤ c.val → c.val < d.val →
      d.val = m - 1 - k →
      ∃ r ∈ qtwoParabRefl m,
        ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dTau m true c d := by
    intro k
    induction k with
    | zero =>
        intro c d hc hcd hd
        have hdval : d.val = m - 1 := by omega
        have hd_eq : d = ⟨m - 1, by omega⟩ := Fin.ext hdval
        have hc2 : c.val + 1 ≤ m - 1 := by omega
        obtain ⟨r, hr, her⟩ := plh_exists_true_last hm he hc hc2
        refine ⟨r, hr, ?_⟩
        rw [her, hd_eq]
    | succ k ih =>
        intro c d hc hcd hd
        have hd_lt : d.val + 1 < m := by omega
        let d' : Fin m := ⟨d.val + 1, hd_lt⟩
        have hd'val : d'.val = m - 1 - k := by simp [d']; omega
        have hc_lt_d' : c.val < d'.val := by simp [d']; omega
        obtain ⟨r, hr, her⟩ := ih c d' hc hc_lt_d' hd'val
        have hd1 : 1 ≤ d.val := by omega
        obtain ⟨r', hr', her'⟩ := plh_conj_step (e := e) he hd1 hd_lt hr her
        refine ⟨r', hr', ?_⟩
        have hcd_ne : c ≠ d := by
          intro h
          have := congrArg Fin.val h
          omega
        have hcd'_ne : c ≠ d' := by
          intro h
          have := congrArg Fin.val h
          simp [d'] at this
          omega
        have h1 : Equiv.swap d d' c = c :=
          Equiv.swap_apply_of_ne_of_ne hcd_ne hcd'_ne
        have h2 : Equiv.swap d d' d' = d := Equiv.swap_apply_right d d'
        rw [her', h1, h2]
  have hk : d.val = m - 1 - (m - 1 - d.val) := by omega
  exact key (m - 1 - d.val) c d hc hcd hk

theorem dTau_mem_qtwoParabRefl {m : ℕ} (hm : 4 ≤ m) {e : (ggCoxeterMatrixD m).Group ≃* dEven m}
    (he : IsDEquiv m e) (ε : Bool) {a b : Fin m} (ha : 1 ≤ a.val) (hab : a.val < b.val) :
    ∃ r ∈ qtwoParabRefl m,
      ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) = dTau m ε a b := by
  cases ε with
  | false => exact plh_exists_false hm he ha hab
  | true => exact plh_exists_true hm he ha hab

theorem dPermW_conj_simple_mem {m : ℕ} (hm : 4 ≤ m) {e : (ggCoxeterMatrixD m).Group ≃* dEven m}
    (he : IsDEquiv m e) (π : Equiv.Perm (Fin m)) (t : Fin m)
    (h1 : ((π (OrthTorus.simpleLo t) : Fin m) : ℕ) ≠ 0)
    (h2 : ((π (OrthTorus.simpleHi t) : Fin m) : ℕ) ≠ 0) :
    dPermW e π * (ggCoxeterMatrixD m).simple t * (dPermW e π)⁻¹ ∈ qtwoParabRefl m := by
  let lo : Fin m := OrthTorus.simpleLo t
  let hi : Fin m := OrthTorus.simpleHi t
  let ε : Bool := decide (t.val + 1 = m)
  let g : (ggCoxeterMatrixD m).Group :=
    dPermW e π * (ggCoxeterMatrixD m).simple t * (dPermW e π)⁻¹
  change g ∈ qtwoParabRefl m
  have hne : lo ≠ hi := OrthTorus.simpleLo_ne_simpleHi (by omega) t
  have hπne : π lo ≠ π hi := fun h => hne (π.injective h)
  have h1' : (π lo).val ≠ 0 := h1
  have h2' : (π hi).val ≠ 0 := h2
  have hg : ((e g : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
      dTau m ε (π lo) (π hi) := by
    have hd : ((e (dPermW e π) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
        dPerm m π := plh_e_dPermW e π
    have hst : ((e ((ggCoxeterMatrixD m).simple t) : dEven m) :
        DVec m ≃ₗ[ZMod 3] DVec m) = dTau m ε (OrthTorus.simpleLo t)
          (OrthTorus.simpleHi t) := he t
    calc
      ((e g : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m)
          = ((e (dPermW e π * (ggCoxeterMatrixD m).simple t *
              (dPermW e π)⁻¹) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) := rfl
      _ = ((e (dPermW e π) * e ((ggCoxeterMatrixD m).simple t) *
            (e (dPermW e π))⁻¹ : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) := by
            rw [map_mul, map_mul, map_inv]
      _ = ((e (dPermW e π) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) *
            ((e ((ggCoxeterMatrixD m).simple t) : dEven m) :
              DVec m ≃ₗ[ZMod 3] DVec m) *
            (((e (dPermW e π) : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m))⁻¹ := by
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      _ = dPerm m π * dTau m ε (OrthTorus.simpleLo t) (OrthTorus.simpleHi t) *
            (dPerm m π)⁻¹ := by rw [hd, hst]
      _ = dTau m ε (π (OrthTorus.simpleLo t)) (π (OrthTorus.simpleHi t)) :=
            dPerm_conj_dTau m π ε _ _
  rcases lt_or_gt_of_ne hπne with hlt | hgt
  · obtain ⟨r, hr, her⟩ := dTau_mem_qtwoParabRefl (e := e) hm he ε
      (a := π lo) (b := π hi) (by omega) hlt
    have hrg : r = g := e.injective (by
      apply Subtype.ext
      rw [her, hg])
    rwa [hrg] at hr
  · obtain ⟨r, hr, her⟩ := dTau_mem_qtwoParabRefl (e := e) hm he ε
      (a := π hi) (b := π lo) (by omega) hgt
    have her' : ((e r : dEven m) : DVec m ≃ₗ[ZMod 3] DVec m) =
        dTau m ε (π lo) (π hi) := by rw [her, dTau_symm]
    have hrg : r = g := e.injective (by
      apply Subtype.ext
      rw [her', hg])
    rwa [hrg] at hr

end CFSG.StandardType.QTwo

end
