module

public import CFSG.RankThree.PartOne.CTP.Su4Coord
public import CFSG.RankThree.PartOne.CTP.Su4Plane

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {p : ℕ} [NeZero p] {ζ : K}

theorem movU_eq_hermOrth_eigU_one (hσ : ∀ c, σ (σ c) = c) (hζ : IsPrimitiveRoot ζ p)
    {g : SUid σ 4} (hg : g ^ p = 1) : movU g = hermOrth σ (eigU g 1) := by
  refine Submodule.eq_of_le_of_finrank_eq (movU_le_hermOrth_eigU_one g) ?_
  have h1 := finrank_hermOrth_add σ hσ (eigU g 1)
  have h2 := finrank_eigU_one_add_movU hζ hg
  omega

theorem exists_witt_of_long (hσ : IsUnitaryInvolution σ) (hζ : IsPrimitiveRoot ζ p)
    {g : SUid σ 4} (hg : g ^ p = 1) (hdim : Module.finrank K (eigU g 1) = 2) :
    ∃ b : Fin 4 → (Fin 4 → K),
      (∀ i j, herm σ (b i) (b j) = if j = Fin.rev i then 1 else 0) ∧
        b 0 ∈ movU g ∧ b 3 ∈ movU g := by
  have hmovdim : Module.finrank K (movU g) = 2 := by
    have := finrank_eigU_one_add_movU hζ hg
    omega
  obtain ⟨x, hx, y, hy, hxx, hyy, hxy⟩ := exists_hyperbolic_pair_of_nondeg_plane hσ hdim
    (fun w hw h => eigU_one_nondeg hσ.invol hζ hg hw h)
  obtain ⟨x', hx', y', hy', hx'x', hy'y', hx'y'⟩ :=
    exists_hyperbolic_pair_of_nondeg_plane hσ hmovdim
      (fun w hw h => movU_nondeg hσ.invol hζ hg hw h)
  have horth : ∀ u ∈ movU g, ∀ v ∈ eigU g 1, herm σ u v = 0 := fun u hu v hv =>
    herm_eq_zero_comm σ hσ.invol ((mem_hermOrth σ).mp (movU_le_hermOrth_eigU_one g hu) v hv)
  have horth' : ∀ u ∈ movU g, ∀ v ∈ eigU g 1, herm σ v u = 0 := fun u hu v hv =>
    (mem_hermOrth σ).mp (movU_le_hermOrth_eigU_one g hu) v hv
  have hyx : herm σ y x = 1 := by rw [herm_conj σ hσ.invol, hxy, map_one]
  have hy'x' : herm σ y' x' = 1 := by rw [herm_conj σ hσ.invol, hx'y', map_one]
  have e1 := horth x' hx' x hx
  have e2 := horth x' hx' y hy
  have e3 := horth' x' hx' x hx
  have e4 := horth' x' hx' y hy
  have e5 := horth y' hy' x hx
  have e6 := horth y' hy' y hy
  have e7 := horth' y' hy' x hx
  have e8 := horth' y' hy' y hy
  refine ⟨![x', x, y, y'], ?_, hx', hy'⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.rev, hxx, hyy, hxy, hyx, hx'x', hy'y', hx'y', hy'x', e1, e2, e3, e4, e5, e6, e7, e8]

theorem card_le_of_long [Finite K] (hσ : IsUnitaryInvolution σ) (hζ : IsPrimitiveRoot ζ p)
    {g : SUid σ 4} (hg : g ^ p = 1) (hdim : Module.finrank K (eigU g 1) = 2)
    {A : Subgroup (SUid σ 4)} (hfix : ∀ a ∈ A, ∀ v ∈ movU g, a • v = v) :
    Nat.card A ≤ Nat.card (SU σ 2) := by
  obtain ⟨b, hb, hb0, hb3⟩ := exists_witt_of_long hσ hζ hg hdim
  obtain ⟨Q, hQ, hQb⟩ := exists_wittConj b hb
  have hle := le_map_lbEmb_of_fix hQ (A := A)
    (fun a ha => by rw [hQb]; exact hfix a ha _ hb0)
    (fun a ha => by rw [hQb]; exact hfix a ha _ hb3)
  calc Nat.card A ≤ Nat.card ((lbEmb σ).range.map (conjEquiv Q hQ).toMonoidHom) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card (SU σ 2) := by
        rw [Subgroup.card_map_of_injective (conjEquiv Q hQ).injective, natCard_range_lbEmb]

end CFSG.RankThree.PartOne.CTP
