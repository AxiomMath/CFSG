module

public import CFSG.Quasithin.Background.HSL
public import CFSG.Quasithin.Background.B4L3FactA
public import CFSG.Quasithin.Background.FFC5T7

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank Matrix

section Schur

variable {V : Type} [CommGroup V]

theorem schur_nilp (hV : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ x ∈ L, ∀ w ∈ W, x w ∈ W) (hcomm : commSub W L = W)
    (hirr : ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → fixV L ⊓ W ≤ J → J ≤ W →
      J = fixV L ⊓ W ∨ J = W)
    {q : MulAut V} (hq : ∀ x ∈ L, q * x = x * q) (hqW : ∀ w ∈ W, q w ∈ W)
    (hq2 : ∀ w ∈ W, q (q w) = w) : ∀ w ∈ W, q w = w := by
  have hqx : ∀ x ∈ L, ∀ v : V, q (x v) = x (q v) := fun x hx v => by
    have := congrArg (fun g : MulAut V => g v) (hq x hx)
    simpa [MulAut.mul_apply] using this
  let fh : V →* V := MonoidHom.mk' (fun v => q v * v⁻¹) (fun a b => by
    rw [map_mul, mul_inv]
    simp [mul_comm, mul_left_comm, mul_assoc])
  have hfh : ∀ v, fh v = q v * v⁻¹ := fun v => rfl
  have hfhL : ∀ x ∈ L, ∀ v, fh (x v) = x (fh v) := fun x hx v => by
    rw [hfh, hfh, hqx x hx, map_mul, map_inv]
  have hfhfh : ∀ w ∈ W, fh (fh w) = 1 := by
    intro w hw
    rw [hfh, hfh, map_mul, map_inv, hq2 w hw]
    have h1 := hV w
    have h2 := hV (q w)
    have e : w * (q w)⁻¹ * (q w * w⁻¹)⁻¹ = w ^ 2 * ((q w) ^ 2)⁻¹ := by
      simp [sq, mul_comm, mul_left_comm, mul_assoc]
    rw [e, h1, h2]
    simp
  set C : Subgroup V := fixV L ⊓ W with hC
  have hCfix : ∀ c ∈ C, ∀ x ∈ L, x c = c := fun c hc x hx => hc.1 x hx
  have hfhW : ∀ w ∈ W, fh w ∈ W := fun w hw => W.mul_mem (hqW w hw) (W.inv_mem hw)
  have hfhC : ∀ c ∈ C, fh c ∈ C := by
    intro c hc
    refine ⟨fun x hx => ?_, hfhW c hc.2⟩
    rw [← hfhL x hx c, hCfix c hc x hx]
  let Y : Subgroup V := W ⊓ C.comap fh
  have hYinv : ∀ x ∈ L, ∀ w ∈ Y, x w ∈ Y := by
    intro x hx w hw
    refine ⟨hLW x hx w hw.1, ?_⟩
    show fh (x w) ∈ C
    have hc : fh w ∈ C := hw.2
    rw [hfhL x hx w, hCfix _ hc x hx]
    exact hc
  have hCY : C ≤ Y := fun c hc => ⟨hc.2, hfhC c hc⟩
  have hall : ∀ w ∈ W, fh w ∈ C := by
    rcases hirr Y hYinv hCY inf_le_left with hY | hY
    · intro w hw
      have : fh w ∈ Y := by
        refine ⟨hfhW w hw, ?_⟩
        show fh (fh w) ∈ C
        rw [hfhfh w hw]
        exact C.one_mem
      rw [hY] at this
      exact this
    · intro w hw
      have : w ∈ Y := by rw [hY]; exact hw
      exact this.2
  have hker : commSub W L ≤ fh.ker := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨x, hx, w, hw, rfl⟩
    show fh (x w * w⁻¹) = 1
    rw [map_mul, map_inv, hfhL x hx w, hCfix _ (hall w hw) x hx]
    simp
  intro w hw
  have h1 : w ∈ commSub W L := by rw [hcomm]; exact hw
  have h2 := MonoidHom.mem_ker.1 (hker h1)
  rw [hfh, mul_inv_eq_one] at h2
  exact h2

theorem commSub_commV_perfect {X : Subgroup (MulAut V)} (hX : ⁅X, X⁆ = X) :
    commSub (commV X) X = commV X :=
  le_antisymm (commSub_le_of_invariant (CFSG.Quasithin.commV_invariant X))
    (commV_le_commSub_of_perfect hX fun g hg v => Subgroup.subset_closure ⟨g, hg, v, rfl⟩)

end Schur

section Natural

variable {V : Type} [CommGroup V]

@[expose] noncomputable def tGLn {d : ℕ} {K : Type} [Field K] (i j : Fin d) (h : i ≠ j) (c : K) :
    GL (Fin d) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
    (by rw [Matrix.det_transvection_of_ne i j h c]; exact one_ne_zero)

theorem tGLn_mem {d : ℕ} {K : Type} [Field K] {i j : Fin d} (h : i ≠ j) (c : K) :
    tGLn i j h c ∈ StatedSL d K :=
  Subgroup.subset_closure (Matrix.det_transvection_of_ne i j h c)

theorem irr_of_binaryNatural {L : Subgroup (MulAut V)} {U Z : Subgroup V} {d n : ℕ} (hd : 2 ≤ d)
    (h : BinaryNaturalSL L U Z d n) :
    ∀ J : Subgroup V, (∀ x ∈ L, ∀ w ∈ J, x w ∈ J) → Z ≤ J → J ≤ U → J = Z ∨ J = U := by
  obtain ⟨K, hK, hfin, hc, π, hπ⟩ := h
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap hπ
  intro J hJ hZJ hJU
  let J' : AddSubgroup (Fin d → K) :=
    { carrier := {v | ∃ u : ↥U, (u : V) ∈ J ∧ f u = Multiplicative.ofAdd v}
      add_mem' := by
        rintro a b ⟨u, hu, hfu⟩ ⟨u', hu', hfu'⟩
        refine ⟨u * u', J.mul_mem hu hu', ?_⟩
        rw [map_mul, hfu, hfu']
        rfl
      zero_mem' := ⟨1, J.one_mem, by simp⟩
      neg_mem' := by
        rintro a ⟨u, hu, hfu⟩
        refine ⟨u⁻¹, J.inv_mem hu, ?_⟩
        rw [map_inv, hfu]
        rfl }
  have hU' : ∀ i j : Fin d, i ≠ j → ∀ c : K, ∀ u ∈ J', Matrix.transvection i j c *ᵥ u ∈ J' := by
    rintro i j hij c v ⟨u, hu, hfu⟩
    set γ : ↥(StatedSL d K) := ⟨tGLn i j hij c, tGLn_mem hij c⟩ with hγ
    have hgu : ((π γ : ↥L) : MulAut V) (u : V) ∈ U := hπ.2.2.2.1 (π γ) u u.2
    refine ⟨⟨_, hgu⟩, hJ (π γ).1 (π γ).2 u hu, ?_⟩
    refine (hfe γ u hgu).trans ?_
    rw [hfu]
    rfl
  rcases H.eq_bot_or_eq_top_of_transvection_inv hd J' hU' with h0 | h0
  · left
    refine le_antisymm (fun u hu => ?_) hZJ
    have hmem : f ⟨u, hJU hu⟩ = 1 := by
      have : Multiplicative.toAdd (f ⟨u, hJU hu⟩) ∈ J' := ⟨⟨u, hJU hu⟩, hu, by simp⟩
      rw [h0, AddSubgroup.mem_bot] at this
      exact Multiplicative.toAdd.injective this
    exact (hfk _).1 hmem
  · right
    refine le_antisymm hJU (fun u hu => ?_)
    have hv : Multiplicative.toAdd (f ⟨u, hu⟩) ∈ J' := by rw [h0]; trivial
    obtain ⟨u', hu', hfu'⟩ := hv
    have h1 : f (⟨u, hu⟩ * u'⁻¹) = 1 := by
      rw [map_mul, map_inv, hfu', ofAdd_toAdd]
      exact mul_inv_cancel _
    have h2 : u * (u' : V)⁻¹ ∈ Z := (hfk _).1 h1
    have h3 : u = (u * (u' : V)⁻¹) * (u' : V) := by simp
    rw [h3]
    exact J.mul_mem (hZJ h2) hu'

end Natural

end FFC

end CFSG.Quasithin
