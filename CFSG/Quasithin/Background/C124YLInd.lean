module

public import CFSG.Quasithin.Background.C124YLTrans
public import CFSG.Quasithin.Background.A1aFStar

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open

variable {W : Type*} [CommGroup W] {Q : Type*} [CommGroup Q] {U Z : Subgroup W} {c : ↥U →* Q}

section Ind

variable (hc : IsCoord U Z c) (N : Subgroup (MulAut W)) (hU : ∀ x ∈ N, ∀ u, u ∈ U ↔ x u ∈ U)
  (hZ : ∀ x ∈ N, ∀ z, z ∈ Z ↔ x z ∈ Z)

@[expose] def resU (x : ↥N) : ↥U →* ↥U :=
  MonoidHom.codRestrict ((x : MulAut W).toMonoidHom.comp U.subtype) U
    (fun u => (hU x x.2 u).1 u.2)

include hc hZ in
theorem exists_ind (x : ↥N) : ∃ ρ : Q →* Q, ∀ u : ↥U, ρ (c u) = c (resU N hU x u) := by
  have hker : c.ker ≤ (c.comp (resU N hU x)).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    have h1 := (hc.ker u).1 hu
    exact (hc.ker (resU N hU x u)).2 ((hZ x x.2 u).1 h1)
  refine ⟨c.liftOfRightInverse (Function.surjInv hc.surj) (Function.rightInverse_surjInv hc.surj)
    ⟨c.comp (resU N hU x), hker⟩, fun u => ?_⟩
  exact c.liftOfRightInverse_comp_apply _ _ _ u

@[expose] noncomputable def indHom : ↥N →* Monoid.End Q where
  toFun x := (exists_ind hc N hU hZ x).choose
  map_one' := by
    refine MonoidHom.ext fun q => ?_
    obtain ⟨u, rfl⟩ := hc.surj q
    rw [(exists_ind hc N hU hZ 1).choose_spec u]
    have : resU N hU (1 : ↥N) u = u := Subtype.ext rfl
    rw [this]
    rfl
  map_mul' x y := by
    refine MonoidHom.ext fun q => ?_
    obtain ⟨u, rfl⟩ := hc.surj q
    show (exists_ind hc N hU hZ (x * y)).choose (c u) =
      (exists_ind hc N hU hZ x).choose ((exists_ind hc N hU hZ y).choose (c u))
    rw [(exists_ind hc N hU hZ (x * y)).choose_spec u, (exists_ind hc N hU hZ y).choose_spec u,
      (exists_ind hc N hU hZ x).choose_spec (resU N hU y u)]
    rfl

theorem indHom_apply (x : ↥N) (u : ↥U) : indHom hc N hU hZ x (c u) = c (resU N hU x u) :=
  (exists_ind hc N hU hZ x).choose_spec u

end Ind

section Faithful

variable [Finite W] (hc : IsCoord U Z c)

theorem faithful_of_fstar {Xs Ls : Subgroup (MulAut W)} (hLX : Ls ≤ Xs)
    (hnorm : ∀ x ∈ Xs, x ∈ Subgroup.normalizer (Ls : Set (MulAut W)))
    (hF : quasithinGenFitting Xs = Ls)
    (hU : ∀ x ∈ Xs, ∀ u, u ∈ U ↔ x u ∈ U) (hZ : ∀ x ∈ Xs, ∀ z, z ∈ Z ↔ x z ∈ Z)
    (hLfaith : ∀ l : ↥Ls, indHom hc Xs hU hZ ⟨l, hLX l.2⟩ = 1 → l = 1)
    (x : ↥Xs) (hx : indHom hc Xs hU hZ x = 1) : x = 1 := by
  have hx' : indHom hc Xs hU hZ x⁻¹ = 1 := by
    have := (indHom hc Xs hU hZ).map_mul x⁻¹ x
    rw [inv_mul_cancel, map_one, hx, mul_one] at this
    exact this.symm
  have hcomm : ∀ l : ↥Ls, (x : MulAut W) * l = l * x := by
    intro l
    let l' : ↥Xs := ⟨l, hLX l.2⟩
    let y : MulAut W := x * l * (x : MulAut W)⁻¹ * (l : MulAut W)⁻¹
    have hyL : y ∈ Ls := by
      have h1 : (x : MulAut W) * l * (x : MulAut W)⁻¹ ∈ Ls :=
        (Subgroup.mem_normalizer_iff.1 (hnorm x x.2) l).1 l.2
      exact Ls.mul_mem h1 (Ls.inv_mem l.2)
    have hy1 : indHom hc Xs hU hZ ⟨y, hLX hyL⟩ = 1 := by
      have : (⟨y, hLX hyL⟩ : ↥Xs) = x * l' * x⁻¹ * l'⁻¹ := rfl
      rw [this, map_mul, map_mul, map_mul, hx, hx', one_mul, mul_one, ← map_mul, mul_inv_cancel,
        map_one]
    have h1 : y = 1 := congrArg Subtype.val (hLfaith ⟨y, hyL⟩ hy1)
    have h2 : (x : MulAut W) * l = l * x := by
      have := congrArg (· * ((l : MulAut W) * (x : MulAut W))) h1
      simp only [y, one_mul] at this
      calc (x : MulAut W) * l = x * l * (x : MulAut W)⁻¹ * (l : MulAut W)⁻¹ *
            ((l : MulAut W) * x) := by group
        _ = l * x := this.trans (by simp)
    exact h2
  have hmem : (x : MulAut W) ∈ quasithinGenFitting Xs := by
    refine centralizer_quasithinGenFitting_le Xs ⟨x.2, ?_⟩
    rw [hF]
    refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    exact (hcomm ⟨l, hl⟩).symm
  rw [hF] at hmem
  have h3 : ((⟨x, hmem⟩ : ↥Ls) : MulAut W) = 1 := congrArg Subtype.val (hLfaith ⟨x, hmem⟩ hx)
  exact Subtype.ext h3

end Faithful

section FixInd

variable (hc : IsCoord U Z c) (N : Subgroup (MulAut W)) (hU : ∀ x ∈ N, ∀ u, u ∈ U ↔ x u ∈ U)
  (hZ : ∀ x ∈ N, ∀ z, z ∈ Z ↔ x z ∈ Z)

theorem mem_fixImg_iff_ind {B : Subgroup (MulAut W)} (hB : B ≤ N) (q : Q) :
    q ∈ fixImg U Z c B ↔ ∀ x : ↥N, (x : MulAut W) ∈ B → indHom hc N hU hZ x q = q := by
  have key : ∀ (x : ↥N) (u : ↥U), (x : MulAut W) (u : W) * (u : W)⁻¹ ∈ Z ↔
      indHom hc N hU hZ x (c u) = c u := by
    intro x u
    rw [indHom_apply hc N hU hZ x u]
    have h1 := hc.ker (resU N hU x u * u⁻¹)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1.symm
  rw [mem_fixImg]
  constructor
  · rintro ⟨u, rfl, hu⟩ x hx
    exact (key x u).1 (hu _ hx)
  · intro h
    obtain ⟨u, rfl⟩ := hc.surj q
    refine ⟨u, rfl, fun b hb => ?_⟩
    exact (key ⟨b, hB hb⟩ u).2 (h ⟨b, hB hb⟩ hb)

end FixInd

end CFSG.Quasithin.C124.YL
