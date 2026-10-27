module

public import CFSG.Quasithin.Vol2.Ch10SecQ34ML
public import CFSG.Quasithin.Vol2.Ch10SecB3Facts
public import CFSG.Quasithin.Vol2.Ch10SecQ34MA
public import CFSG.Quasithin.Vol2.Ch10SecQ34MK

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

theorem factCommOrth_holds : FactCommOrth := by
  classical
  intro V _ _ H A Z a p hD hp hp2 hpH hA hcomm hZ x hx v
  obtain ⟨K, _, _, _, hK, π, hπ⟩ := hD
  have ha : 1 ≤ a := by
    by_contra h
    have h0 : a = 0 := by omega
    rw [h0, mul_zero, pow_zero] at hK
    exact absurd hK (Finite.one_lt_card (α := K)).ne'
  obtain ⟨B, hBs, hBk, hBe⟩ := C10P34.exists_herm_hom a hπ
  obtain ⟨Y, hY⟩ := C10P34.exists_induced B hBs x.toMonoidHom
    (fun w hw => (hBk _).mpr (hZ x hx w ((hBk w).mp hw)))
  have hY' : ∀ w, Y (B w) = B (x w) := hY
  have hxπ : ∀ (γ : ↥(StatedSL 2 K)) (w : V),
      x (((π γ : ↥H) : MulAut V) w) = ((π γ : ↥H) : MulAut V) (x w) := by
    intro γ w
    have := congrArg (fun g : MulAut V => g w) (hcomm x hx _ (π γ).2)
    simpa [MulAut.mul_apply] using this
  have hYc : ∀ (γ : ↥(StatedSL 2 K)) (m : ↥(hermSub a (Fin 2) K)),
      ((Y ⟨twistAct a (StatedSL 2 K) γ m, C10P34.isHerm_tw a hK _ m.2⟩ :
        ↥(hermSub a (Fin 2) K)) : Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
        twistAct a (StatedSL 2 K) γ (Y m) := by
    intro γ m
    obtain ⟨w, rfl⟩ := hBs m
    have e1 : (⟨twistAct a (StatedSL 2 K) γ (B w), C10P34.isHerm_tw a hK _ (B w).2⟩ :
        ↥(hermSub a (Fin 2) K)) = B (((π γ : ↥H) : MulAut V) w) := Subtype.ext (hBe γ w).symm
    rw [e1, hY', hxπ, hY']
    exact hBe γ (x w)
  set f : Matrix (Fin 2) (Fin 2) K → Matrix (Fin 2) (Fin 2) K := fun X =>
    if h : C10P34.IsHerm a X then
      Multiplicative.toAdd ((Y ⟨Multiplicative.ofAdd X, h⟩ : ↥(hermSub a (Fin 2) K)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) K))
    else 0 with hf
  have hfX : ∀ X (hX : C10P34.IsHerm a X), f X =
      Multiplicative.toAdd ((Y ⟨Multiplicative.ofAdd X, hX⟩ : ↥(hermSub a (Fin 2) K)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) K)) := fun X hX => by
    rw [hf]
    exact dite_eq_left_of_eq_true (eq_true hX)
  have hherm : ∀ X, C10P34.IsHerm a X → C10P34.IsHerm a (f X) := fun X hX => by
    rw [hfX X hX]
    exact (Y _).2
  have hadd : ∀ X X', C10P34.IsHerm a X → C10P34.IsHerm a X' → f (X + X') = f X + f X' := by
    intro X X' hX hX'
    rw [hfX _ (C10P34.isHerm_add a hX hX'), hfX X hX, hfX X' hX']
    have e : (⟨Multiplicative.ofAdd (X + X'), C10P34.isHerm_add a hX hX'⟩ :
        ↥(hermSub a (Fin 2) K)) = ⟨Multiplicative.ofAdd X, hX⟩ * ⟨Multiplicative.ofAdd X', hX'⟩ :=
      Subtype.ext rfl
    rw [e, map_mul]
    rfl
  have hU : ∀ t X, C10P34.IsHerm a X →
      f (C10P34.tw a (C10P34.um t) X) = C10P34.tw a (C10P34.um t) (f X) := by
    intro t X hX
    rw [hfX _ (C10P34.isHerm_tw a hK _ hX), hfX X hX]
    exact congrArg Multiplicative.toAdd (hYc (C10P34.uSL t) ⟨Multiplicative.ofAdd X, hX⟩)
  have hW : ∀ X, C10P34.IsHerm a X →
      f (C10P34.tw a C10P34.wm X) = C10P34.tw a C10P34.wm (f X) := by
    intro X hX
    rw [hfX _ (C10P34.isHerm_tw a hK _ hX), hfX X hX]
    exact congrArg Multiplicative.toAdd (hYc C10P34.wSL ⟨Multiplicative.ofAdd X, hX⟩)
  obtain ⟨μ, hμq, hμ⟩ := C10P34.eq_smul_of_comm_twist a ha hK f hherm hadd hU hW
  have hYμ : ∀ m : ↥(hermSub a (Fin 2) K),
      Multiplicative.toAdd ((Y m : ↥(hermSub a (Fin 2) K)) :
        Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
        μ • Multiplicative.toAdd (m : Multiplicative (Matrix (Fin 2) (Fin 2) K)) := by
    intro m
    have h := hμ _ m.2
    rw [hfX _ m.2] at h
    exact h
  exact C10P34.factCommOrth_aux a hp hp2 hpH hA hx hBs hBk hBe hY' hμq hYμ v

end CFSG.Quasithin.Vol2.Ch10.SecB
