module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalRk2L4
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal
open CFSG.RankThree.PartOne.KCOrthogonal


namespace OrthRestOdd

open Module Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2

theorem largeEvenLayer_centralizer_eq_of_commSpace_two
    {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 8 ≤ finrank K V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    {t : orthDerived Q} (ht1 : t ≠ 1) (htp : t ^ p = 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2) :
    LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q))) =
      (supportedFixedDerived Q (t : V ≃ₗ[K] V)).subgroupOf (orthDerived Q) := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set x : V ≃ₗ[K] V := ↑t with hxdef
  have hxp : x ^ p = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, htp]
    rfl
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup t.2
  have hx : OddOrderIsometry Q p x := ⟨hxO, hxp, hpK, fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hxp
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hW6 : 6 ≤ finrank K (fixedSpace x) := by rw [fixedSpace_eq_lit]; omega
  obtain ⟨hq, hcenter, hodd⟩ := orthDerived_facts (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate hW6
  set D₀ := supportedFixedDerived Q x with hD₀
  have hD₀Ω : D₀ ≤ orthDerived Q := hx.supportedFixedDerived_le_orthDerived
  set D : Subgroup (orthDerived Q) := D₀.subgroupOf (orthDerived Q) with hD
  have hmemC : ∀ y : orthDerived Q,
      y ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)) ↔
        (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, isometryCentralizer, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup y.2,
        congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hDH : D ≤ Subgroup.centralizer ({t} : Set (orthDerived Q)) := by
    intro y hy
    rw [hmemC]
    exact supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.mp hy)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)),
      ∀ h ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)), g * h * g⁻¹ * h⁻¹ ∈ D := by
    intro g hg h hh
    rw [hD, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact commutator_mem_supportedFixedDerived hx hK1 ht2 ((hmemC g).mp hg) ((hmemC h).mp hh)
  have hDq : CFSG.IsQuasisimple D := by
    have e1 : D ≃* D₀ := Subgroup.subgroupOfEquivOfLe hD₀Ω
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e1.trans (supportedFixedDerivedEquiv hx)).symm hq
  exact (TableBSymp.largeEvenLayer_eq_of_commutator_mem hDH hcomm hDq).1

end OrthRestOdd

private def tbkls12_planeLM (i : Fin 3) :
    (ZMod 2 × ZMod 2) →ₗ[ZMod 2] ModelSpace (ZMod 2) where
  toFun p := planeVec i p
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · funext k
      simp [planeVec, Pi.single_add]
    · simp [planeVec]
  map_smul' c p := by
    refine Prod.ext ?_ ?_
    · funext k
      simp [planeVec, Pi.single_smul]
    · simp [planeVec]

private lemma tbkls12_planeLM_injective (i : Fin 3) :
    Function.Injective (tbkls12_planeLM i) := by
  intro p q h
  have h' := congrArg (fun x : ModelSpace (ZMod 2) => x.1 i) h
  simpa [tbkls12_planeLM, planeVec, Pi.single_apply] using h'

private lemma tbkls12_rotPow_one_eq : rotPow (ZMod 2) 1 = rotLE (ZMod 2) := by
  simp only [rotPow, ZMod.val_one, pow_one]

private lemma tbkls12_rotPow_two_eq : rotPow (ZMod 2) 2 = rotLE (ZMod 2) ^ 2 := by
  rw [rotPow, ZMod.val_two_eq_two_mod, show (2 : ℕ) % 3 = 2 by norm_num]

private lemma tbkls12_rotLE_sub_self_aux :
    ∀ p : ZMod 2 × ZMod 2, rotLE (ZMod 2) (rotLE (ZMod 2) p) - rotLE (ZMod 2) p = p := by
  decide

private lemma tbkls12_rotLE_sq_sub_self_aux :
    ∀ p : ZMod 2 × ZMod 2,
      (rotLE (ZMod 2) ^ 2) ((rotLE (ZMod 2) ^ 2) p) - (rotLE (ZMod 2) ^ 2) p = p := by
  simp only [pow_two, LinearEquiv.mul_apply]
  decide

private lemma tbkls12_rotPow_one_sub_self (p : ZMod 2 × ZMod 2) :
    rotPow (ZMod 2) 1 (rotPow (ZMod 2) 1 p) - rotPow (ZMod 2) 1 p = p := by
  rw [tbkls12_rotPow_one_eq]
  exact tbkls12_rotLE_sub_self_aux p

private lemma tbkls12_rotPow_two_sub_self (p : ZMod 2 × ZMod 2) :
    rotPow (ZMod 2) 2 (rotPow (ZMod 2) 2 p) - rotPow (ZMod 2) 2 p = p := by
  rw [tbkls12_rotPow_two_eq]
  exact tbkls12_rotLE_sq_sub_self_aux p

private lemma tbkls12_rotPow_sub_surjective {a : ZMod 3} (ha : a ≠ 0) :
    ∀ p : ZMod 2 × ZMod 2, ∃ q, rotPow (ZMod 2) a q - q = p := by
  have ha' : a = 1 ∨ a = 2 := by
    have h : ∀ b : ZMod 3, b ≠ 0 → b = 1 ∨ b = 2 := by decide
    exact h a ha
  rcases ha' with rfl | rfl
  · intro p
    exact ⟨rotPow (ZMod 2) 1 p, tbkls12_rotPow_one_sub_self p⟩
  · intro p
    exact ⟨rotPow (ZMod 2) 2 p, tbkls12_rotPow_two_sub_self p⟩

private lemma tbkls12_weight_one (u : Fin 3 → ZMod 3) (hu : Two.weight u = 1) :
    ∃ i : Fin 3, u i ≠ 0 ∧ ∀ j, j ≠ i → u j = 0 := by
  have hs : (Finset.univ.filter (fun i => u i ≠ 0)).card = 1 := by
    simpa only [Two.weight] using hu
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hs
  refine ⟨i, ?_, ?_⟩
  · have hmem : i ∈ Finset.univ.filter (fun j => u j ≠ 0) := by
      rw [hi]; exact Finset.mem_singleton_self i
    simpa using hmem
  · intro j hj
    by_contra h
    have hmem : j ∈ Finset.univ.filter (fun k => u k ≠ 0) := by
      simp [h]
    rw [hi] at hmem
    exact hj (Finset.mem_singleton.mp hmem)

private lemma tbkls12_tor_sub_eq (u : Fin 3 → ZMod 3) (i : Fin 3)
    (huj : ∀ j, j ≠ i → u j = 0) (y : ModelSpace (ZMod 2)) :
    Two.tor u y - y = tbkls12_planeLM i (rotPow (ZMod 2) (u i) (y.1 i) - y.1 i) := by
  rw [show Two.tor u = cmEquiv (ZMod 2) u from rfl, cmEquiv_apply]
  change (fun j => rotPow (ZMod 2) (u j) (y.1 j), y.2) - (y.1, y.2)
      = (Pi.single i (rotPow (ZMod 2) (u i) (y.1 i) - y.1 i), 0)
  refine Prod.ext ?_ ?_
  · funext j
    by_cases hji : j = i
    · subst hji; simp
    · have h0 : u j = 0 := huj j hji
      simp [h0, rotPow_zero, Pi.single_apply, hji]
  · simp

private lemma tbkls12_tor_planeVec (u : Fin 3 → ZMod 3) (i : Fin 3) (q : ZMod 2 × ZMod 2) :
    Two.tor u (tbkls12_planeLM i q) - tbkls12_planeLM i q
      = tbkls12_planeLM i (rotPow (ZMod 2) (u i) q - q) := by
  rw [show tbkls12_planeLM i q = planeVec i q from rfl]
  rw [show Two.tor u = cmEquiv (ZMod 2) u from rfl, cmEquiv_apply_planeVec]
  change tbkls12_planeLM i (rotPow (ZMod 2) (u i) q) - tbkls12_planeLM i q
      = tbkls12_planeLM i (rotPow (ZMod 2) (u i) q - q)
  rw [map_sub]

private lemma tbkls12_commSpace_tor_eq_range (u : Fin 3 → ZMod 3) (i : Fin 3)
    (hui : u i ≠ 0) (huj : ∀ j, j ≠ i → u j = 0) :
    CFSG.RankThree.PartOne.LIT.commSpace (Two.tor u) = LinearMap.range (tbkls12_planeLM i) := by
  apply le_antisymm
  · intro w hw
    obtain ⟨y, hy⟩ := CFSG.RankThree.PartOne.LIT.mem_commSpace.mp hw
    refine LinearMap.mem_range.mpr ⟨rotPow (ZMod 2) (u i) (y.1 i) - y.1 i, ?_⟩
    rw [← tbkls12_tor_sub_eq u i huj y]
    exact hy
  · rintro w ⟨p, rfl⟩
    rw [CFSG.RankThree.PartOne.LIT.mem_commSpace]
    obtain ⟨q, hq⟩ := tbkls12_rotPow_sub_surjective hui p
    refine ⟨tbkls12_planeLM i q, ?_⟩
    rw [tbkls12_tor_planeVec u i q, hq]

theorem finrank_commSpace_twoTor_of_weight_eq_one {u : Fin 3 → ZMod 3}
    (hu : Two.weight u = 1) :
    Module.finrank (ZMod 2) (CFSG.RankThree.PartOne.LIT.commSpace (Two.tor u)) = 2 := by
  obtain ⟨i, hui, huj⟩ := tbkls12_weight_one u hu
  rw [tbkls12_commSpace_tor_eq_range u i hui huj]
  rw [LinearMap.finrank_range_of_inj (tbkls12_planeLM_injective i)]
  rw [Module.finrank_prod]
  norm_num

end CFSG.StandardType

end
