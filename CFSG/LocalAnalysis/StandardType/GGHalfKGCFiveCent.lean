module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCFiveSplit
public import CFSG.LocalAnalysis.StandardType.GGHalfKGCANum
public import CFSG.GroupTheory.OrderBelowSixtySolvable

public section

namespace CFSG.StandardType

private lemma ggKGCFiveCent_symm_comm {V : Type} [AddCommGroup V] [Module GGKGCF V]
    {y g : V ≃ₗ[GGKGCF] V} (hgy : g * y = y * g) : g.symm * y = y * g.symm :=
  Commute.inv_left hgy

private lemma ggKGCFiveCent_coe_pow {V : Type} [AddCommGroup V] [Module GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) (n : ℕ) :
    ((y ^ n : V ≃ₗ[GGKGCF] V) : V →ₗ[GGKGCF] V) = (y : V →ₗ[GGKGCF] V) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, LinearEquiv.coe_toLinearMap_one, Module.End.one_eq_id]
  | succ n ih => rw [pow_succ, pow_succ, LinearEquiv.coe_toLinearMap_mul, ih]

private lemma ggKGCFiveCent_map_fix {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    {y g : V ≃ₗ[GGKGCF] V} (hgy : g * y = y * g) :
    Submodule.map (g : V →ₗ[GGKGCF] V) (ggKGCAFix y) = ggKGCAFix y := by
  have hg := (ggKGCFive_stable hgy).1
  have hgs := (ggKGCFive_stable (ggKGCFiveCent_symm_comm hgy)).1
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    exact hg
  · intro x hx
    exact Submodule.mem_map.mpr ⟨g.symm x, hgs x hx, by simp⟩

private noncomputable def ggKGCFiveCent_restrict {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) (g : V ≃ₗ[GGKGCF] V) (hgy : g * y = y * g) :
    ggKGCAFix y ≃ₗ[GGKGCF] ggKGCAFix y :=
  LinearEquiv.ofSubmodules g (ggKGCAFix y) (ggKGCAFix y) (ggKGCFiveCent_map_fix hgy)

private noncomputable def ggKGCFiveCent_res {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) :
    ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[GGKGCF] V))) →*
      (ggKGCAFix y ≃ₗ[GGKGCF] ggKGCAFix y) where
  toFun g := ggKGCFiveCent_restrict y g.1 (Subgroup.mem_centralizer_singleton_iff.mp g.2)
  map_one' := by
    ext x
    simp [ggKGCFiveCent_restrict, LinearEquiv.ofSubmodules_apply]
  map_mul' := by
    intro a b
    ext x
    simp [ggKGCFiveCent_restrict, LinearEquiv.ofSubmodules_apply]

private lemma ggKGCFiveCent_ker_fix {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V)
    {g : ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[GGKGCF] V)))}
    (hg : g ∈ (ggKGCFiveCent_res y).ker) :
    ∀ w ∈ ggKGCAFix y, (g : V ≃ₗ[GGKGCF] V) w = w := by
  intro w hw
  have h := MonoidHom.mem_ker.mp hg
  have h2 := congrArg
    (fun e : ggKGCAFix y ≃ₗ[GGKGCF] ggKGCAFix y => ((e ⟨w, hw⟩ : ggKGCAFix y) : V)) h
  simpa [ggKGCFiveCent_res, ggKGCFiveCent_restrict, LinearEquiv.ofSubmodules_apply] using h2

private lemma ggKGCFiveCent_ker_comm {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V]
    (y : V ≃ₗ[GGKGCF] V) (hy : y ^ 5 = 1)
    (hU : Module.finrank GGKGCF (ggKGCFiveU y) = 4)
    (hcompl : IsCompl (ggKGCAFix y) (ggKGCFiveU y))
    (a b : ↥((ggKGCFiveCent_res y).ker)) : a * b = b * a := by
  have hay : (a.1.1 : V ≃ₗ[GGKGCF] V) * y = y * (a.1.1 : V ≃ₗ[GGKGCF] V) :=
    Subgroup.mem_centralizer_singleton_iff.mp a.1.2
  have hby : (b.1.1 : V ≃ₗ[GGKGCF] V) * y = y * (b.1.1 : V ≃ₗ[GGKGCF] V) :=
    Subgroup.mem_centralizer_singleton_iff.mp b.1.2
  have hafix : ∀ w ∈ ggKGCAFix y, (a.1.1 : V ≃ₗ[GGKGCF] V) w = w :=
    ggKGCFiveCent_ker_fix y a.2
  have hbfix : ∀ w ∈ ggKGCAFix y, (b.1.1 : V ≃ₗ[GGKGCF] V) w = w :=
    ggKGCFiveCent_ker_fix y b.2
  obtain ⟨c, hc⟩ := ggKGCFive_commutant y hy hU hay
  obtain ⟨d, hd⟩ := ggKGCFive_commutant y hy hU hby
  let Pa : V →ₗ[GGKGCF] V := ∑ i : Fin 4, c i • (y : V →ₗ[GGKGCF] V) ^ (i : ℕ)
  let Pb : V →ₗ[GGKGCF] V := ∑ i : Fin 4, d i • (y : V →ₗ[GGKGCF] V) ^ (i : ℕ)
  have hPa : ∀ u ∈ ggKGCFiveU y, (a.1.1 : V ≃ₗ[GGKGCF] V) u = Pa u := by
    intro u hu
    rw [hc u hu]
    simp only [Pa, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [← ggKGCFiveCent_coe_pow (y := y) (i : ℕ)]
    rfl
  have hPb : ∀ u ∈ ggKGCFiveU y, (b.1.1 : V ≃ₗ[GGKGCF] V) u = Pb u := by
    intro u hu
    rw [hd u hu]
    simp only [Pb, LinearMap.sum_apply, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [← ggKGCFiveCent_coe_pow (y := y) (i : ℕ)]
    rfl
  have hPa_mem : Pa ∈ Algebra.adjoin GGKGCF ({(y : V →ₗ[GGKGCF] V)} : Set (V →ₗ[GGKGCF] V)) := by
    dsimp only [Pa]
    apply Subalgebra.sum_mem
    intro i _
    apply Subalgebra.smul_mem
    exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton GGKGCF (y : V →ₗ[GGKGCF] V)) i
  have hPb_mem : Pb ∈ Algebra.adjoin GGKGCF ({(y : V →ₗ[GGKGCF] V)} : Set (V →ₗ[GGKGCF] V)) := by
    dsimp only [Pb]
    apply Subalgebra.sum_mem
    intro i _
    apply Subalgebra.smul_mem
    exact Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton GGKGCF (y : V →ₗ[GGKGCF] V)) i
  have hcomm : Pa * Pb = Pb * Pa := by
    haveI : IsMulCommutative
        (Algebra.adjoin GGKGCF ({(y : V →ₗ[GGKGCF] V)} : Set (V →ₗ[GGKGCF] V))) :=
      Algebra.isMulCommutative_adjoin_singleton GGKGCF (y : V →ₗ[GGKGCF] V)
    have h := mul_comm
      (⟨Pa, hPa_mem⟩ : Algebra.adjoin GGKGCF ({(y : V →ₗ[GGKGCF] V)} : Set (V →ₗ[GGKGCF] V)))
      ⟨Pb, hPb_mem⟩
    simpa using h
  have hWeq : Set.EqOn ((a.1.1 : V →ₗ[GGKGCF] V) * (b.1.1 : V →ₗ[GGKGCF] V))
      ((b.1.1 : V →ₗ[GGKGCF] V) * (a.1.1 : V →ₗ[GGKGCF] V)) (ggKGCAFix y) := by
    intro w hw
    have hbw : b.1.1 w ∈ ggKGCAFix y := (ggKGCFive_stable hby).1 w hw
    have haw : a.1.1 w ∈ ggKGCAFix y := (ggKGCFive_stable hay).1 w hw
    calc ((a.1.1 : V →ₗ[GGKGCF] V) * (b.1.1 : V →ₗ[GGKGCF] V)) w
        = a.1.1 (b.1.1 w) := rfl
      _ = b.1.1 w := hafix (b.1.1 w) hbw
      _ = b.1.1 (a.1.1 w) := by rw [hafix w hw]
      _ = ((b.1.1 : V →ₗ[GGKGCF] V) * (a.1.1 : V →ₗ[GGKGCF] V)) w := rfl
  have hUeq : Set.EqOn ((a.1.1 : V →ₗ[GGKGCF] V) * (b.1.1 : V →ₗ[GGKGCF] V))
      ((b.1.1 : V →ₗ[GGKGCF] V) * (a.1.1 : V →ₗ[GGKGCF] V)) (ggKGCFiveU y) := by
    intro u hu
    have hbu : b.1.1 u ∈ ggKGCFiveU y := (ggKGCFive_stable hby).2 u hu
    have hau : a.1.1 u ∈ ggKGCFiveU y := (ggKGCFive_stable hay).2 u hu
    calc ((a.1.1 : V →ₗ[GGKGCF] V) * (b.1.1 : V →ₗ[GGKGCF] V)) u
        = a.1.1 (b.1.1 u) := rfl
      _ = Pa (b.1.1 u) := hPa (b.1.1 u) hbu
      _ = Pa (Pb u) := by rw [hPb u hu]
      _ = (Pa * Pb) u := rfl
      _ = (Pb * Pa) u := by rw [hcomm]
      _ = Pb (Pa u) := rfl
      _ = Pb (a.1.1 u) := by rw [hPa u hu]
      _ = b.1.1 (a.1.1 u) := (hPb (a.1.1 u) hau).symm
      _ = ((b.1.1 : V →ₗ[GGKGCF] V) * (a.1.1 : V →ₗ[GGKGCF] V)) u := rfl
  have hEmaps : ((a.1.1 : V →ₗ[GGKGCF] V) * (b.1.1 : V →ₗ[GGKGCF] V)) =
      ((b.1.1 : V →ₗ[GGKGCF] V) * (a.1.1 : V →ₗ[GGKGCF] V)) :=
    LinearMap.ext_on_codisjoint hcompl.codisjoint hWeq hUeq
  have hab : a.1.1 * b.1.1 = b.1.1 * a.1.1 := by
    apply LinearEquiv.toLinearMap_injective
    simpa using hEmaps
  exact Subtype.ext (Subtype.ext hab)

theorem ggKGCFive_cent_solvable {V : Type} [AddCommGroup V] [Module GGKGCF V]
    [FiniteDimensional GGKGCF V] (hV : Module.finrank GGKGCF V = 6) (y : V ≃ₗ[GGKGCF] V)
    (hy : y ^ 5 = 1) (hy1 : y ≠ 1) :
    Group.IsSolvable ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[GGKGCF] V))) := by
  let W := ggKGCAFix y
  let U := ggKGCFiveU y
  have hcompl : IsCompl W U := ggKGCFive_isCompl y hy
  have hU4 : Module.finrank GGKGCF U = 4 := ggKGCFive_finrank_U y hy hy1 hV
  have hW2 : Module.finrank GGKGCF W = 2 := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hU4, hV] at h
    omega
  haveI : FiniteDimensional GGKGCF W := FiniteDimensional.finiteDimensional_submodule W
  have hcardW : Nat.card (W ≃ₗ[GGKGCF] W) = 6 := ggKGCANum_card_aut_two hW2
  haveI : Finite (W ≃ₗ[GGKGCF] W) :=
    Nat.finite_of_card_ne_zero (by rw [hcardW]; norm_num)
  haveI : Group.IsSolvable (W ≃ₗ[GGKGCF] W) :=
    CFSG.GroupTheory.groups_order_below_sixty_solvable (by rw [hcardW]; norm_num)
  let C := ↥(Subgroup.centralizer ({y} : Set (V ≃ₗ[GGKGCF] V)))
  change Group.IsSolvable C
  let res : C →* (W ≃ₗ[GGKGCF] W) := ggKGCFiveCent_res y
  haveI hker : Group.IsSolvable res.ker := by
    apply Group.isSolvable_of_comm
    intro a b
    exact ggKGCFiveCent_ker_comm y hy hU4 hcompl a b
  haveI hquot : Group.IsSolvable (C ⧸ res.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective res)
  exact Group.isSolvable_of_subgroup_quotient res.ker

end CFSG.StandardType

end
