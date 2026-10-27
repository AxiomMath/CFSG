module

public import CFSG.Sporadic.Fi23.Fischer
public import CFSG.Fischer.Uniq.F23Uniq
public import CFSG.Fischer.Uniq.LocalOfComp
public import CFSG.Fischer.Uniq.Parity

public section

namespace CFSG.Sporadic.Fi23

open CFSG.Blueprint.Fischer CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem d_mem_D23 : d ∈ D23 := IsConj.refl d

theorem localPoints_D23
    (hPF : PolarFacts) :
    ∀ f ∈ D23, Nonempty (LocalPoints (pairModel Fi22.pair_D) D23 f) :=
  fun _ hf => Fi22.F23.nonempty_localPoints_fi22 hPF f23_J hf

theorem F23.exists_commute
    (hPF : PolarFacts) {Z : Type} [Group Z] {C : Set Z} (hC : F23 Z C) :
    ∃ e f, e ∈ C ∧ f ∈ C ∧ e ≠ f ∧ e * f = f * e := by
  obtain ⟨e₀, he₀⟩ := hC.1.2.1
  have hd : e₀ ∈ C := by rw [he₀]; exact IsConj.refl e₀
  obtain ⟨L⟩ := Fi22.F23.nonempty_localPoints_fi22 hPF hC hd
  set f := L.χ.symm ⟨Fi22.a, Fi22.a_mem_D⟩
  exact ⟨e₀, f, hd, f.2.1, f.2.2.1.symm, f.2.2.2.symm⟩

theorem connected_D23
    (hPF : PolarFacts) : (commGraph D23).Connected :=
  Pair.connected_of_simple pair_J isSimpleGroup_commutator_J (F23.exists_commute hPF f23_J)

theorem hasFixedPointProperty_D23 : HasFixedPointProperty pair_J :=
  hasFixedPointProperty_of_odd pair_J (by
    have h : Nat.card ↥D23 = 31671 := card_class_d
    rw [h]; decide)

theorem F24.nonempty_localPoints_fi23
    (hPF : PolarFacts) (hHF : HyperovalFacts)
    (hFF : Fi22Facts) {X : Type} [Group X] {E : Set X} (hE : F24 X E) {e : X} (he : e ∈ E) :
    Nonempty (LocalPoints (pairModel pair_J) E e) := by
  have hQ := F24_local hE he
  have hconn := connected_D23 hPF
  have huD : compSet D23 d = Set.univ :=
    compSet_eq_univ fun c hc hcd => Pair.muSet_nonempty pair_J hconn d_mem_D23 hc hcd
  have hY : ∀ e x : J, e ∈ D23 → x ∈ D23 → e * x ≠ x * e → ySet D23 e x ⊆ {e, x, e * x * e} :=
    fun _ _ he hx hex => Pair.ySet_subset_of_fi22 hPF hHF hFF pair_J (localPoints_D23 hPF) he hx
      hex (Pair.muSet_nonempty pair_J hconn he hx fun h => hex h.symm)
  refine nonempty_localPoints_of_compIso pair_J hasFixedPointProperty_D23 hE.1 hQ.1
    (F23.exists_commute hPF hQ) fun q hq => ?_
  obtain ⟨ι₀⟩ := F23.nonempty_compGraphIso hPF hHF hFF hQ f23_J hq d_mem_D23
  exact ⟨ι₀.trans (compGraphIsoTop huD), fun a b =>
    Pair.tau_of_compGraphIso hQ.1 pair_J hq d_mem_D23 ι₀ hY a b⟩

end CFSG.Sporadic.Fi23
