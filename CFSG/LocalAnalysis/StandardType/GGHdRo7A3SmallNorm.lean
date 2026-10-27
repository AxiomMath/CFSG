module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3SmallDefs

public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def hdRo7A9NormAux_class : Fin 10 → A9Class
  | ⟨0, _⟩ => .cz
  | ⟨1, _⟩ => .ep
  | ⟨2, _⟩ => .em
  | ⟨3, _⟩ => .bpm
  | ⟨4, _⟩ => .bmp
  | ⟨5, _⟩ => .cp
  | ⟨6, _⟩ => .cm
  | ⟨7, _⟩ => .d
  | ⟨8, _⟩ => .e
  | ⟨9, _⟩ => .f
  | ⟨_, _⟩ => .cz

private def hdRo7A9NormAux_nX : Fin 10 → ZMod 3 → ℕ :=
  ![fun a => if a = 0 then 9 else 0,
    fun a => if a = 0 then 6 else if a = 1 then 3 else 0,
    fun a => if a = 0 then 6 else if a = 2 then 3 else 0,
    fun a => if a = 0 then 6 else if a = 1 then 3 else 0,
    fun a => if a = 0 then 6 else if a = 2 then 3 else 0,
    fun _ => 3,
    fun _ => 3,
    fun a => if a = 0 then 7 else 1,
    fun a => if a = 0 then 1 else 4,
    fun a => if a = 0 then 5 else 2]

private def hdRo7A9NormAux_fX : Fin 10 → ZMod 3 → ZMod 3 :=
  ![fun _ => 0,
    fun a => if a = 0 then 0 else 1,
    fun a => if a = 0 then 0 else 2,
    fun a => if a = 0 then 0 else 2,
    fun a => if a = 0 then 0 else 1,
    fun a => a,
    fun a => -a,
    fun a => -a,
    fun a => -a,
    fun a => a]

private def hdRo7A9NormAux_dX : Fin 10 → ZMod 3 :=
  ![2, 2, 2, 2, 2, 2, 2, 1, 1, 1]

private theorem hdRo7A9NormAux_nX_eq (k : Fin 10) (a : ZMod 3) :
    hdRo7A9NormAux_nX k a =
      (Finset.univ.filter fun i : Fin 9 => a9H (hdRo7A9NormAux_class k) i = a).card := by
  decide +kernel +revert

private theorem hdRo7A9NormAux_fX_eq (k : Fin 10) (i : Fin 9) :
    a9F (hdRo7A9NormAux_class k) i =
      hdRo7A9NormAux_fX k (a9H (hdRo7A9NormAux_class k) i) := by
  decide +kernel +revert

private theorem hdRo7A9NormAux_dX_eq (k : Fin 10) :
    a9D (hdRo7A9NormAux_class k) = hdRo7A9NormAux_dX k := by
  decide +kernel +revert

private theorem hdRo7A9NormAux_finite (cnt : ZMod 3 → Fin 10) (g : ZMod 3 → ZMod 3)
    (d : ZMod 3)
    (h9 : ∑ a : ZMod 3, (cnt a : ℕ) = 9)
    (hsum : ∑ a : ZMod 3, ((cnt a : ℕ) : ZMod 3) * a = 0)
    (hsumf : ∑ a : ZMod 3, ((cnt a : ℕ) : ZMod 3) * g a = 0)
    (hprodf : ∑ a : ZMod 3, ((cnt a : ℕ) : ZMod 3) * (g a * a) + d = 2)
    (hd : d ≠ 0)
    (hinj : ∀ a b : ZMod 3, (cnt a : ℕ) ≠ 0 → (cnt b : ℕ) ≠ 0 →
      g a = g b → a = b) :
    ∃ (c κ : ZMod 3) (k : Fin 10),
      (∀ a : ZMod 3, (cnt (a - c) : ℕ) = hdRo7A9NormAux_nX k a) ∧
      (∀ a : ZMod 3, (cnt (a - c) : ℕ) ≠ 0 →
        g (a - c) = hdRo7A9NormAux_fX k a + κ) ∧
      d = hdRo7A9NormAux_dX k := by
  decide +kernel +revert

private def hdRo7A9NormAux_cnt (hh : Fin 9 → ZMod 3) : ZMod 3 → ℕ :=
  fun a => (Finset.univ.filter fun i => hh i = a).card

private def hdRo7A9NormAux_cntF (hh : Fin 9 → ZMod 3) : ZMod 3 → Fin 10 :=
  fun a => ⟨hdRo7A9NormAux_cnt hh a,
    Nat.lt_succ_of_le (by
      have h := Finset.card_le_card
        (Finset.filter_subset (fun i : Fin 9 => hh i = a) Finset.univ)
      simpa [hdRo7A9NormAux_cnt] using h)⟩

private theorem hdRo7A9NormAux_sum_zmod3 {M : Type*} [AddCommMonoid M] (F : ZMod 3 → M) :
    ∑ a : ZMod 3, F a = F 0 + F 1 + F 2 := by
  have hmem : ∀ x : ZMod 3, x ∈ ({0, 1, 2} : Finset (ZMod 3)) := by decide
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} :=
    (Finset.eq_univ_of_forall hmem).symm
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  simp only [Finset.sum_singleton]
  abel

private theorem hdRo7A9NormAux_fiber (hh : Fin 9 → ZMod 3) (G : ZMod 3 → ZMod 3) :
    ∑ i, G (hh i) =
      ∑ a : ZMod 3, ((hdRo7A9NormAux_cnt hh a : ℕ) : ZMod 3) * G a := by
  have h := Finset.sum_fiberwise' (Finset.univ : Finset (Fin 9)) hh G
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  simp [hdRo7A9NormAux_cnt]

private theorem hdRo7A9NormAux_card_fiber (hh : Fin 9 → ZMod 3) :
    hdRo7A9NormAux_cnt hh 0 + hdRo7A9NormAux_cnt hh 1 + hdRo7A9NormAux_cnt hh 2 = 9 := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin 9))) (f := hh)
    (t := (Finset.univ : Finset (ZMod 3))) (fun i _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [hdRo7A9NormAux_sum_zmod3 (fun a => (Finset.univ.filter fun i => hh i = a).card)] at h
  simpa [hdRo7A9NormAux_cnt] using h.symm

private theorem hdRo7A9NormAux_exists_g {hh f : Fin 9 → ZMod 3}
    (hiff : ∀ i j, f i = f j ↔ hh i = hh j) :
    ∃ g : ZMod 3 → ZMod 3, ∀ i, f i = g (hh i) := by
  classical
  refine ⟨fun a => if h : ∃ i, hh i = a then f (Classical.choose h) else 0, fun i => ?_⟩
  have hex : ∃ j, hh j = hh i := ⟨i, rfl⟩
  have hch : hh (Classical.choose hex) = hh i := Classical.choose_spec hex
  have h1 : (if h : ∃ j, hh j = hh i then f (Classical.choose h) else 0) =
      f (Classical.choose hex) := by
    rw [dite_eq_left hex]
  show f i = (if h : ∃ j, hh j = hh i then f (Classical.choose h) else 0)
  rw [h1]
  exact (hiff i (Classical.choose hex)).mpr hch.symm

private theorem hdRo7A9NormAux_filter_add (hh : Fin 9 → ZMod 3) (c a : ZMod 3) :
    (Finset.univ.filter fun i => hh i + c = a).card =
      (Finset.univ.filter fun i => hh i = a - c).card := by
  have h : (Finset.univ.filter fun i => hh i + c = a) =
      (Finset.univ.filter fun i => hh i = a - c) := by
    refine Finset.filter_congr ?_
    intro i _
    constructor <;> intro hh'
    · rw [← hh']; abel
    · rw [hh']; abel
  rw [h]

theorem a9_norm_holds : A9NormLeaf := by
  intro hh f d hhU hf hprod hd hiff
  obtain ⟨g, hg⟩ := hdRo7A9NormAux_exists_g hiff
  have hsumh : ∑ i, hh i = 0 := hhU
  have h9 : ∑ a : ZMod 3, (hdRo7A9NormAux_cntF hh a : ℕ) = 9 := by
    rw [hdRo7A9NormAux_sum_zmod3 (fun a => (hdRo7A9NormAux_cntF hh a : ℕ))]
    simpa [hdRo7A9NormAux_cntF] using hdRo7A9NormAux_card_fiber hh
  have hsum : ∑ a : ZMod 3,
      ((hdRo7A9NormAux_cnt hh a : ℕ) : ZMod 3) * a = 0 := by
    rw [← hdRo7A9NormAux_fiber hh (fun a => a)]
    exact hsumh
  have hsumf : ∑ a : ZMod 3,
      ((hdRo7A9NormAux_cnt hh a : ℕ) : ZMod 3) * g a = 0 := by
    rw [← hdRo7A9NormAux_fiber hh g, ← hf]
    exact Finset.sum_congr rfl fun i _ => (hg i).symm
  have hprodf : ∑ a : ZMod 3,
      ((hdRo7A9NormAux_cnt hh a : ℕ) : ZMod 3) * (g a * a) + d = 2 := by
    rw [← hdRo7A9NormAux_fiber hh (fun a => g a * a), ← hprod]
    exact congrArg (· + d) (Finset.sum_congr rfl fun i _ => by rw [hg i])
  have hinj : ∀ a b : ZMod 3, hdRo7A9NormAux_cnt hh a ≠ 0 →
      hdRo7A9NormAux_cnt hh b ≠ 0 → g a = g b → a = b := by
    intro a b ha hb hab
    rw [hdRo7A9NormAux_cnt] at ha hb
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero ha)
    obtain ⟨j, hj⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hb)
    rw [Finset.mem_filter] at hi hj
    have hfij : f i = f j := by rw [hg i, hg j, hi.2, hj.2, hab]
    have hlev := (hiff i j).mp hfij
    rw [hi.2, hj.2] at hlev
    exact hlev
  obtain ⟨c, κ, k, hcntX, hgX, hdX⟩ :=
    hdRo7A9NormAux_finite (hdRo7A9NormAux_cntF hh) g d h9 hsum hsumf hprodf hd hinj
  have hcntX' : ∀ a : ZMod 3, hdRo7A9NormAux_cnt hh (a - c) = hdRo7A9NormAux_nX k a :=
    fun a => hcntX a
  have hcard : ∀ a : ZMod 3, Fintype.card {i : Fin 9 // hh i + c = a} =
      Fintype.card {i : Fin 9 // a9H (hdRo7A9NormAux_class k) i = a} := by
    intro a
    rw [Fintype.card_subtype, Fintype.card_subtype, hdRo7A9NormAux_filter_add]
    rw [← hdRo7A9NormAux_nX_eq k a]
    exact hcntX' a
  let e : ∀ a : ZMod 3,
      {i : Fin 9 // hh i + c = a} ≃ {i : Fin 9 // a9H (hdRo7A9NormAux_class k) i = a} :=
    fun a => Fintype.equivOfCardEq (hcard a)
  let σ : Equiv.Perm (Fin 9) := Equiv.ofFiberEquiv e
  have hσ : ∀ i : Fin 9, a9H (hdRo7A9NormAux_class k) (σ i) = hh i + c :=
    fun i => Equiv.ofFiberEquiv_map e i
  have hκ : ∀ j : Fin 9, f (σ.symm j) - a9F (hdRo7A9NormAux_class k) j = κ := by
    intro j
    have hj : a9H (hdRo7A9NormAux_class k) j = hh (σ.symm j) + c := by
      have h := hσ (σ.symm j)
      rwa [Equiv.apply_symm_apply] at h
    have hpos : 0 < (Finset.univ.filter fun i : Fin 9 =>
        a9H (hdRo7A9NormAux_class k) i = a9H (hdRo7A9NormAux_class k) j).card :=
      Finset.card_pos.mpr ⟨j, by simp⟩
    have hnX : hdRo7A9NormAux_nX k (a9H (hdRo7A9NormAux_class k) j) ≠ 0 := by
      rw [hdRo7A9NormAux_nX_eq]
      exact ne_of_gt hpos
    have hne : hdRo7A9NormAux_cnt hh (a9H (hdRo7A9NormAux_class k) j - c) ≠ 0 := by
      rw [hcntX']
      exact hnX
    have hval := hgX (a9H (hdRo7A9NormAux_class k) j) hne
    have harg : hh (σ.symm j) = a9H (hdRo7A9NormAux_class k) j - c := by
      rw [hj]; abel
    calc f (σ.symm j) - a9F (hdRo7A9NormAux_class k) j
        = g (a9H (hdRo7A9NormAux_class k) j - c) -
            a9F (hdRo7A9NormAux_class k) j := by rw [hg, harg]
      _ = (hdRo7A9NormAux_fX k (a9H (hdRo7A9NormAux_class k) j) + κ) -
            a9F (hdRo7A9NormAux_class k) j := by rw [hval]
      _ = κ := by
          rw [hdRo7A9NormAux_fX_eq]
          abel
  refine ⟨σ, hdRo7A9NormAux_class k, ?_, ?_, ?_⟩
  · intro i
    have hi : a9H (hdRo7A9NormAux_class k) i = hh (σ.symm i) + c := by
      have h := hσ (σ.symm i)
      rwa [Equiv.apply_symm_apply] at h
    have h0 : a9H (hdRo7A9NormAux_class k) 0 = hh (σ.symm 0) + c := by
      have h := hσ (σ.symm 0)
      rwa [Equiv.apply_symm_apply] at h
    show hh (σ.symm i) - a9H (hdRo7A9NormAux_class k) i =
      hh (σ.symm 0) - a9H (hdRo7A9NormAux_class k) 0
    rw [hi, h0]
    abel
  · intro i
    show f (σ.symm i) - a9F (hdRo7A9NormAux_class k) i =
      f (σ.symm 0) - a9F (hdRo7A9NormAux_class k) 0
    rw [hκ i, hκ 0]
  · exact hdX.trans (hdRo7A9NormAux_dX_eq k).symm

end CFSG.StandardType.HdRo7A3.Small
