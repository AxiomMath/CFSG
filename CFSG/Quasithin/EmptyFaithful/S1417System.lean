module

public import CFSG.Quasithin.EmptyFaithful.S1417NaturalMore
public import CFSG.Assembly.Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Blocks

public section

namespace CFSG.Quasithin

namespace S1417

section System

variable {W : Type*} [CommGroup W]

structure BlockSystem (X Y : Subgroup (MulAut W)) (I : Finset (Subgroup (MulAut W))) : Prop where
  Y_eq : Y = ⨆ L ∈ I, L
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  indep : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥
  nat : ∀ L ∈ I, ActsAsNaturalL2 L (commV L)
  sup : fixV Y ⊔ ⨆ L ∈ I, commV L = ⊤
  inf : fixV Y ⊓ ⨆ L ∈ I, commV L = ⊥
  indepV : ∀ L ∈ I, commV L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), commV L' = ⊥
  perm : ∀ g ∈ X, ∀ L ∈ I, B1.conjAut g L ∈ I ∧
    (commV L).map g.toMonoidHom = commV (B1.conjAut g L)

variable {X Y : Subgroup (MulAut W)} {I : Finset (Subgroup (MulAut W))}

theorem BlockSystem.le_Y (hS : BlockSystem X Y I) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    L ≤ Y := by
  rw [hS.Y_eq]
  exact le_iSup₂ (f := fun (L : Subgroup (MulAut W)) (_ : L ∈ I) => L) L hL

theorem commV_le_iSup {L : Subgroup (MulAut W)} (hL : L ∈ I) : commV L ≤ ⨆ L ∈ I, commV L :=
  le_iSup₂ (f := fun (L : Subgroup (MulAut W)) (_ : L ∈ I) => commV L) L hL

theorem inv_apply_eq_of_apply_eq {g : MulAut W} {u : W} (h : g u = u) : g⁻¹ u = u := by
  have h1 : g⁻¹ (g u) = u := by simp
  rw [h] at h1
  exact h1

theorem BlockSystem.apply_mem (hS : BlockSystem X Y I) {g : MulAut W} (hg : g ∈ X) {u : W}
    (hu : u ∈ ⨆ L ∈ I, commV L) : g u ∈ ⨆ L ∈ I, commV L := by
  have h : (⨆ L ∈ I, commV L) ≤ (⨆ L ∈ I, commV L).comap g.toMonoidHom := by
    refine iSup₂_le fun L hL => ?_
    intro u hu
    have h1 : g u ∈ (commV L).map g.toMonoidHom := ⟨u, hu, rfl⟩
    rw [(hS.perm g hg L hL).2] at h1
    exact commV_le_iSup (hS.perm g hg L hL).1 h1
  exact h hu

theorem apply_mem_fixV_of_conj {g : MulAut W} (hg : B1.conjAut g Y = Y) {w : W}
    (hw : w ∈ fixV Y) : g w ∈ fixV Y := by
  intro y hy
  have h1 : y ∈ B1.conjAut g Y := by rw [hg]; exact hy
  rw [B1.mem_conjAut] at h1
  have h2 : (g⁻¹ * y * g) w = w := hw _ h1
  have h3 : y (g w) = g w := by
    have := congrArg g h2
    simpa using this
  exact h3

theorem BlockSystem.commute_of_trivial (hS : BlockSystem X Y I) (hYX : Y ≤ X)
    (hXY : ∀ g ∈ X, B1.conjAut g Y = Y) {c : MulAut W} (hcX : c ∈ X)
    (hc : ∀ u ∈ ⨆ L ∈ I, commV L, c u = u) : ∀ y ∈ Y, c * y = y * c := by
  intro y hy
  have hcy : c * y * c⁻¹ ∈ Y := by
    have h : y ∈ B1.conjAut c⁻¹ Y := by rw [hXY c⁻¹ (X.inv_mem hcX)]; exact hy
    rw [B1.mem_conjAut] at h
    simpa using h
  have hcinv : ∀ u ∈ ⨆ L ∈ I, commV L, c⁻¹ u = u := by
    intro u hu
    exact inv_apply_eq_of_apply_eq (hc u hu)
  set D : MulAut W := y⁻¹ * (c * y * c⁻¹) with hD
  have hfix : fixV Y ≤ MonoidHom.eqLocus D.toMonoidHom (MonoidHom.id W) := by
    intro w hw
    have h1 : (c * y * c⁻¹) w = w := hw _ hcy
    have h2 : y⁻¹ w = w := inv_apply_eq_of_apply_eq (hw y hy)
    show D w = w
    rw [hD]
    show y⁻¹ ((c * y * c⁻¹) w) = w
    rw [h1, h2]
  have hU : (⨆ L ∈ I, commV L) ≤ MonoidHom.eqLocus D.toMonoidHom (MonoidHom.id W) := by
    intro u hu
    have h1 : (c * y * c⁻¹) u = y u := by
      show c (y (c⁻¹ u)) = y u
      rw [hcinv u hu]
      exact hc _ (hS.apply_mem (hYX hy) hu)
    show D u = u
    rw [hD]
    show y⁻¹ ((c * y * c⁻¹) u) = u
    rw [h1]
    simp
  have hall : ∀ w : W, D w = w := by
    intro w
    have hw : w ∈ fixV Y ⊔ ⨆ L ∈ I, commV L := by rw [hS.sup]; exact Subgroup.mem_top w
    exact (sup_le hfix hU) hw
  have hD1 : D = 1 := MulEquiv.ext fun w => hall w
  have : c * y * c⁻¹ = y := by
    have h : y⁻¹ * (c * y * c⁻¹) = 1 := hD1
    exact (inv_mul_eq_one.mp h).symm
  calc c * y = (c * y * c⁻¹) * c := by group
    _ = y * c := by rw [this]

theorem BlockSystem.apply_eq_of_commute (hS : BlockSystem X Y I) {c : MulAut W} (hcX : c ∈ X)
    (hc : ∀ y ∈ Y, c * y = y * c) : ∀ u ∈ ⨆ L ∈ I, commV L, c u = u := by
  have hall : ∀ L ∈ I, commV L ≤ MonoidHom.eqLocus c.toMonoidHom (MonoidHom.id W) := by
    intro L hL u hu
    have hcL : ∀ l ∈ L, c * l = l * c := fun l hl => hc l (hS.le_Y hL hl)
    have hconj : B1.conjAut c L = L := conjAut_eq_of_commute (fun b hb => hcL b hb)
    have hmap := (hS.perm c hcX L hL).2
    rw [hconj] at hmap
    have hstab : c ∈ stabSub (commV L) := mem_stabSub_of_map_eq hmap
    exact S1417.apply_eq_of_commute (hS.nat L hL) (fun l hl u hu => commV_stable L hl hu) hstab hcL u hu
  intro u hu
  exact (iSup₂_le hall) hu

end System

end S1417

end CFSG.Quasithin
