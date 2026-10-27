module

public import CFSG.Quasithin.Background.B5Part3

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10P34

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem eq_zero_or_eq_one_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (c : K) : c = 0 ∨ c = 1 := by
  have := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have h := FiniteField.pow_card c
  rw [hq, pow_two] at h
  have h0 : c * (c - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr (sub_eq_zero.mp h1)

theorem eq_of_comm_trv {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    (Y : Multiplicative (Fin n → K) →* Multiplicative (Fin n → K)) (hY : Function.Injective Y)
    (hc : ∀ (i j : Fin n) (hij : i ≠ j) (x : Multiplicative (Fin n → K)),
      Y (natAct (StatedSL n K) (B5.trvSL i j hij 1) x) =
        natAct (StatedSL n K) (B5.trvSL i j hij 1) (Y x))
    (x : Multiplicative (Fin n → K)) : Y x = x := by
  have hbasis : ∀ i : Fin n, Y (Multiplicative.ofAdd (Pi.single i 1)) =
      Multiplicative.ofAdd (Pi.single i 1) := by
    intro i
    obtain ⟨j, hij⟩ : ∃ j : Fin n, i ≠ j := by
      by_cases hi0 : i = ⟨0, by omega⟩
      · exact ⟨⟨1, by omega⟩, by rw [hi0]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, by omega⟩, hi0⟩
    have h := hc i j hij (Multiplicative.ofAdd (Pi.single j 1))
    rw [B5.natAct_trvSL, B5.natAct_trvSL] at h
    have h' := congrArg Multiplicative.toAdd h
    simp only [toAdd_ofAdd, Pi.single_eq_same, one_mul] at h'
    rw [ofAdd_add, map_mul, toAdd_mul] at h'
    have hb := add_left_cancel h'
    set c := Multiplicative.toAdd (Y (Multiplicative.ofAdd (Pi.single j 1))) j with hcdef
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, Pi.single_zero] at hb
      have h1 : Y (Multiplicative.ofAdd (Pi.single i 1)) = Y 1 := by
        rw [map_one]
        exact hb
      have h2 := congrFun (congrArg Multiplicative.toAdd (hY h1)) i
      rw [toAdd_ofAdd, Pi.single_eq_same] at h2
      exact one_ne_zero h2
    have hc1 : c = 1 := (eq_zero_or_eq_one_of_card_two hK c).resolve_left hc0
    rw [hc1] at hb
    exact congrArg Multiplicative.ofAdd hb
  have hv : ∀ v : Fin n → K, Y (Multiplicative.ofAdd v) = Multiplicative.ofAdd v := by
    intro v
    rw [← Finset.univ_sum_single v, ofAdd_sum, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases eq_zero_or_eq_one_of_card_two hK (v i) with h | h
    · rw [h, Pi.single_zero, ofAdd_zero, map_one]
    · rw [h]
      exact hbasis i
  exact hv (Multiplicative.toAdd x)

theorem fix_of_comm_nat {V : Type} [CommGroup V] {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) {L : Subgroup (MulAut V)} {I : Subgroup V}
    {π : ↥(StatedSL n K) →* ↥L} (hD : (FFModel.nat (StatedSL n K)).RealizesVia L I ⊥ π)
    {x : MulAut V} (hxI : ∀ u ∈ I, x u ∈ I) (hxc : ∀ l ∈ L, x * l = l * x) :
    ∀ u ∈ I, x u = u := by
  obtain ⟨e, he⟩ := B5.exists_linModel hD
  set y : ↥I →* ↥I :=
    { toFun := fun u => ⟨x (u : V), hxI u u.2⟩
      map_one' := Subtype.ext (map_one x)
      map_mul' := fun a b => Subtype.ext (map_mul x (a : V) (b : V)) } with hy
  set Y : Multiplicative (Fin n → K) →* Multiplicative (Fin n → K) :=
    e.toMonoidHom.comp (y.comp e.symm.toMonoidHom) with hYdef
  have hYinj : Function.Injective Y := by
    intro a b hab
    have h1 := e.injective hab
    have h2 : x (e.symm a : V) = x (e.symm b : V) := congrArg Subtype.val h1
    exact e.symm.injective (Subtype.ext (x.injective h2))
  have hYc : ∀ (i j : Fin n) (hij : i ≠ j) (X : Multiplicative (Fin n → K)),
      Y (natAct (StatedSL n K) (B5.trvSL i j hij 1) X) =
        natAct (StatedSL n K) (B5.trvSL i j hij 1) (Y X) := by
    intro i j hij X
    set γ := B5.trvSL i j hij (1 : K)
    set u := e.symm X with hu
    have hγu : ((π γ : ↥L) : MulAut V) (u : V) ∈ I := hD.2.2.2.1 (π γ) _ u.2
    have h1 : natAct (StatedSL n K) γ X = e ⟨((π γ : ↥L) : MulAut V) (u : V), hγu⟩ := by
      rw [he γ u hγu, hu, MulEquiv.apply_symm_apply]
    have hcomm : x (((π γ : ↥L) : MulAut V) (u : V)) = ((π γ : ↥L) : MulAut V) (x u) := by
      have := congrArg (fun g : MulAut V => g (u : V)) (hxc _ (π γ).2)
      simpa [MulAut.mul_apply] using this
    have hγx : ((π γ : ↥L) : MulAut V) (x u) ∈ I := hD.2.2.2.1 (π γ) _ (hxI _ u.2)
    have h2 := he γ ⟨x u, hxI _ u.2⟩ hγx
    rw [h1]
    simp only [hYdef, hy, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [← h2]
    congr 1
    exact Subtype.ext hcomm
  intro u hu
  have h := eq_of_comm_trv hn hK Y hYinj hYc (e ⟨u, hu⟩)
  simp only [hYdef, hy, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.symm_apply_apply, MonoidHom.coe_mk, OneHom.coe_mk] at h
  exact congrArg Subtype.val (e.injective h)

end CFSG.Quasithin.Vol2.Ch10.SecB.C10P34
