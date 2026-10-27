module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7CentGen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCSub
public import CFSG.RankThree.OrthogonalInvolutions.Dickson
import CFSG.RankThree.Literature.FSmithOrthogonal
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.LieType.SeitzGeneration.OrthNonsplitTools
import CFSG.GroupTheory.CommutingProductFixedSubgroup
import CFSG.LieType.SeitzGeneration.HyperLinear
import CFSG.LieType.SeitzGeneration.OrthCubeBlocks
import CFSG.LieType.SeitzGeneration.OrthExLift
import CFSG.RankThree.PartOne.CTP.SeitzLinear
import CFSG.RankThree.PartOne.CTP.SeitzOrthModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Module QuadraticMap CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
  CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.Classical2 (orthDerived)
open scoped commutatorElement

theorem commutatorElement_mul_mul_of_commute {H : Type*} [Group H] {c c' a a' : H}
    (h1 : Commute c a) (h2 : Commute c a') (h3 : Commute c' a) (h4 : Commute c' a')
    (h5 : Commute c c') : ⁅c * a, c' * a'⁆ = ⁅a, a'⁆ := by
  have hw : Commute (c * c') ⁅a, a'⁆ := by
    rw [commutatorElement_def]
    exact ((((h1.mul_left h3).mul_right (h2.mul_left h4)).mul_right
      (h1.mul_left h3).inv_right).mul_right (h2.mul_left h4).inv_right)
  calc ⁅c * a, c' * a'⁆ = c * (a * c') * a' * a⁻¹ * c⁻¹ * a'⁻¹ * c'⁻¹ := by
        rw [commutatorElement_def]; group
    _ = c * (c' * a) * a' * a⁻¹ * c⁻¹ * a'⁻¹ * c'⁻¹ := by rw [h3.eq]
    _ = c * c' * (a * a' * a⁻¹) * (c⁻¹ * a'⁻¹) * c'⁻¹ := by group
    _ = c * c' * (a * a' * a⁻¹) * (a'⁻¹ * c⁻¹) * c'⁻¹ := by
        rw [(h2.inv_left.inv_right).eq]
    _ = (c * c') * ⁅a, a'⁆ * (c' * c)⁻¹ := by rw [commutatorElement_def]; group
    _ = ⁅a, a'⁆ * (c * c') * (c * c')⁻¹ := by rw [hw.eq, h5.eq]
    _ = ⁅a, a'⁆ := by group

theorem centralizer_mul_inf_centralizer_inv_mul {H : Type*} [Group H] {a b : H} (ha : a ^ 3 = 1) :
    Subgroup.centralizer ({a * b} : Set H) ⊓ Subgroup.centralizer ({a⁻¹ * b} : Set H) =
      Subgroup.centralizer ({a} : Set H) ⊓ Subgroup.centralizer ({b} : Set H) := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    have c1 : Commute x (a * b) := h1
    have c2 : Commute x (a⁻¹ * b) := h2
    have c3 : Commute x (a ^ 2) := by
      rw [show a ^ 2 = a * b * (a⁻¹ * b)⁻¹ by rw [pow_two]; group]
      exact c1.mul_right c2.inv_right
    have c4 : Commute x a := by
      rw [show a = (a ^ 2) ^ 2 by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, ha, one_mul]]
      exact c3.pow_right 2
    have c5 : Commute x b := by
      rw [show b = a⁻¹ * (a * b) by group]
      exact c4.inv_right.mul_right c1
    exact ⟨c4.eq, c5.eq⟩
  · rintro ⟨h1, h2⟩
    have c1 : Commute x a := h1
    have c2 : Commute x b := h2
    exact ⟨(c1.mul_right c2).eq, (c1.inv_right.mul_right c2).eq⟩

section Model

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {U : Submodule (ZMod 2) V}

omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_extG (hU : IsCompl U (perpOf Q U))
    (φ : TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (perpOf Q U))) :
    commSpace (extG hU φ) =
      (commSpace (φ : perpOf Q U ≃ₗ[ZMod 2] perpOf Q U)).map (perpOf Q U).subtype := by
  ext v
  simp only [commSpace, LinearMap.mem_range, Submodule.mem_map]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨u, hu, w, hw, rfl⟩ :=
      Submodule.mem_sup.mp (hU.sup_eq_top ▸ Submodule.mem_top (x := z))
    refine ⟨(φ : perpOf Q U ≃ₗ[ZMod 2] perpOf Q U) ⟨w, hw⟩ - ⟨w, hw⟩, ⟨⟨w, hw⟩, rfl⟩, ?_⟩
    have h1 := extHom_apply_of_mem_W hU φ hu
    have h2 := extHom_apply_of_mem_U hU φ hw
    change _ = ((extHom hU φ).1 : V ≃ₗ[ZMod 2] V) (u + w) - (u + w)
    rw [map_add, h1, h2]
    simp only [Submodule.subtype_apply, Submodule.coe_sub]
    abel
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w : V), ?_⟩
    have h2 := extHom_apply_of_mem_U hU φ w.2
    change ((extHom hU φ).1 : V ≃ₗ[ZMod 2] V) w - w = _
    rw [h2]
    rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem commutator_fixW_eq_map (hU : IsCompl U (perpOf Q U)) :
    ⁅fixW Q U, fixW Q U⁆ =
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (perpOf Q U)))).map
        (extG hU) := by
  rw [← range_extG hU, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]

theorem mem_commutator_fixW_of_mem_orthDerived (hQ : (polarBilin Q).Nondegenerate)
    (hU : IsCompl U (perpOf Q U)) (hP : (polarBilin (Q.restrict (perpOf Q U))).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) (perpOf Q U)) {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ fixW Q U)
    (hgΩ : g ∈ orthDerived Q) : g ∈ ⁅fixW Q U, fixW Q U⁆ := by
  rw [← range_extG hU] at hg
  obtain ⟨φ, rfl⟩ := hg
  have h6V : 6 ≤ finrank (ZMod 2) V := h6.trans (Submodule.finrank_le _)
  have hev : Even (finrank (ZMod 2) (commSpace (extG hU φ))) := by
    have h : extG hU φ ∈ omegaGroup Q hQ := by
      rw [← CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hQ h6V]
      exact hgΩ
    exact h.2
  have hφΩ : (φ : perpOf Q U ≃ₗ[ZMod 2] perpOf Q U) ∈
      omegaGroup (Q.restrict (perpOf Q U)) hP := by
    refine ⟨φ.2, ?_⟩
    rw [commSpace_extG hU φ, Submodule.finrank_map_subtype_eq] at hev
    exact hev
  rw [← CFSG.RankThree.Literature.FSmith.commutator_orthogonalGroup_eq_omegaGroup hP h6] at hφΩ
  have h2 : ⁅TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (perpOf Q U)),
      TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (perpOf Q U))⁆ =
      (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (perpOf Q U)))).map
        (TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (perpOf Q U))).subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [h2] at hφΩ
  obtain ⟨ψ, hψ, hψφ⟩ := hφΩ
  have hψ' : ψ = φ := Subtype.ext hψφ
  rw [commutator_fixW_eq_map hU]
  exact ⟨ψ, hψ, by rw [hψ']⟩

omit [FiniteDimensional (ZMod 2) V] in
theorem commute_of_mem_fixW (hU : IsCompl U (perpOf Q U)) {x g : V ≃ₗ[ZMod 2] V}
    (hxU : ∀ u ∈ U, x u ∈ U) (hxP : ∀ w ∈ perpOf Q U, x w = w) (hg : g ∈ fixW Q U) :
    g * x = x * g := by
  ext v
  obtain ⟨u, hu, w, hw, rfl⟩ :=
    Submodule.mem_sup.mp (hU.sup_eq_top ▸ Submodule.mem_top (x := v))
  simp only [LinearEquiv.mul_apply, map_add]
  rw [hg.2 _ (hxU u hu), hxP w hw, hg.2 u hu, hxP _ (map_mem_perpOf hg hw)]

theorem commutator_commutator_fixW (hU : IsCompl U (perpOf Q U))
    (hP : (polarBilin (Q.restrict (perpOf Q U))).Nondegenerate)
    (hT : ∃ T : Submodule (ZMod 2) (perpOf Q U), finrank (ZMod 2) T = 3 ∧
      ∀ u ∈ T, (Q.restrict (perpOf Q U)) u = 0) :
    ⁅⁅fixW Q U, fixW Q U⁆, ⁅fixW Q U, fixW Q U⁆⁆ = ⁅fixW Q U, fixW Q U⁆ := by
  set O' := TauCeti.QuadraticMap.orthogonalGroup (Q.restrict (perpOf Q U)) with hO'
  have hq := CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hP hT
  have hperf : Group.IsPerfect ↥(orthDerived (Q.restrict (perpOf Q U))) := hq.1
  have h2 : orthDerived (Q.restrict (perpOf Q U)) = (commutator ↥O').map O'.subtype := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  let e : ↥(commutator ↥O') ≃* ↥(orthDerived (Q.restrict (perpOf Q U))) :=
    (Subgroup.equivMapOfInjective _ O'.subtype O'.subtype_injective).trans
      (MulEquiv.subgroupCongr h2.symm)
  have : Group.IsPerfect ↥(commutator ↥O') :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hA : Group.IsPerfect ↥((commutator ↥O').map (extG hU)) := Group.IsPerfect.map _
  rw [← commutator_fixW_eq_map hU] at hA
  exact Subgroup.isPerfect_iff.mp hA

theorem exists_pow_inv_mul_mem_fixW (hU : IsCompl U (perpOf Q U))
    (hU2 : finrank (ZMod 2) U = 2) {x : V ≃ₗ[ZMod 2] V}
    (hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hx3 : x ^ 3 = 1)
    (hxU : ∀ u ∈ U, x u ∈ U) (hxfix : ∀ v, x v = v ↔ v ∈ perpOf Q U) {g : V ≃ₗ[ZMod 2] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgx : g * x = x * g) :
    ∃ i : ℕ, (x ^ i)⁻¹ * g ∈ fixW Q U := by
  have hgx' : ∀ v, g (x v) = x (g v) := fun v => by
    have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f v) hgx
    simpa [LinearEquiv.mul_apply] using this
  have hsub : ∀ v, x v - v ∈ U := by
    intro v
    obtain ⟨u, hu, w, hw, rfl⟩ :=
      Submodule.mem_sup.mp (hU.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add, (hxfix w).mpr hw]
    have : x u + w - (u + w) = x u - u := by abel
    rw [this]
    exact U.sub_mem (hxU u hu) hu
  have hdis : ∀ u ∈ U, x u = u → u = 0 := fun u hu hxu =>
    (Submodule.disjoint_def.mp hU.disjoint) u hu ((hxfix u).mp hxu)
  have hsurj : ∀ u ∈ U, ∃ a ∈ U, x a - a = u := by
    let f : U →ₗ[ZMod 2] U := ((x : V →ₗ[ZMod 2] V) - 1).restrict
      (fun a ha => by simpa using hsub a)
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      have h0 : x a - a = 0 := by
        have := congrArg Subtype.val ha
        simpa [f, LinearMap.restrict_apply] using this
      exact Subtype.ext (hdis a a.2 (sub_eq_zero.mp h0))
    have hfs : Function.Surjective f := LinearMap.injective_iff_surjective.mp hf
    intro u hu
    obtain ⟨a, ha⟩ := hfs ⟨u, hu⟩
    refine ⟨a, a.2, ?_⟩
    have := congrArg Subtype.val ha
    simpa [f, LinearMap.restrict_apply] using this
  have hgU : ∀ u ∈ U, g u ∈ U := by
    intro u hu
    obtain ⟨a, -, rfl⟩ := hsurj u hu
    rw [map_sub, hgx']
    exact hsub _
  have hUne : U ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hU2
    exact absurd hU2 (by norm_num)
  obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hxu₀ : x u₀ ∈ U := hxU u₀ hu₀
  have hne : x u₀ ≠ u₀ := fun h => hu₀0 (hdis u₀ hu₀ h)
  have hx0 : x u₀ ≠ 0 := fun h => hu₀0 (by simpa using congrArg x.symm h)
  have hli : LinearIndependent (ZMod 2) ![u₀, x u₀] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h01 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
    rcases h01 s with rfl | rfl <;> rcases h01 t with rfl | rfl
    · exact ⟨rfl, rfl⟩
    · exfalso
      rw [zero_smul, zero_add, one_smul] at hst
      exact hx0 hst
    · exfalso
      rw [one_smul, zero_smul, add_zero] at hst
      exact hu₀0 hst
    · exfalso
      rw [one_smul, one_smul] at hst
      exact hne (by
        rw [← sub_eq_zero, sub_eq_add_neg, ZModModule.neg_eq_self, add_comm]
        exact hst)
  have hspan : Submodule.span (ZMod 2) (Set.range ![u₀, x u₀]) = U := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · exact hu₀
      · exact hxu₀
    · rw [finrank_span_eq_card hli, Fintype.card_fin, hU2]
  have hmemU : ∀ u ∈ U, ∃ c d : ZMod 2, c • u₀ + d • x u₀ = u := by
    intro u hu
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun] at hu
    obtain ⟨c, hc⟩ := hu
    exact ⟨c 0, c 1, by simpa [Fin.sum_univ_two] using hc⟩
  have hx2 : x (x u₀) = u₀ + x u₀ := by
    have hmem : x (x u₀) + x u₀ + u₀ ∈ U := U.add_mem (U.add_mem (hxU _ hxu₀) hxu₀) hu₀
    have hfix : x (x (x u₀) + x u₀ + u₀) = x (x u₀) + x u₀ + u₀ := by
      have h3 : x (x (x u₀)) = u₀ := by
        have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f u₀) hx3
        simpa [pow_succ, LinearEquiv.mul_apply] using this
      rw [map_add, map_add, h3]
      abel
    have h0 := hdis _ hmem hfix
    have h0' : x (x u₀) = -(x u₀ + u₀) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact h0
    rw [h0', ZModModule.neg_eq_self, add_comm]
  obtain ⟨a, b, hab⟩ := hmemU _ (hgU u₀ hu₀)
  obtain ⟨i, hi⟩ : ∃ i : ℕ, g u₀ = (x ^ i) u₀ := by
    have h01 : ∀ r : ZMod 2, r = 0 ∨ r = 1 := by decide
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl
    · exfalso
      rw [zero_smul, zero_smul, add_zero] at hab
      exact hu₀0 (g.injective (by rw [← hab, map_zero]))
    · refine ⟨1, ?_⟩
      rw [zero_smul, zero_add, one_smul] at hab
      rw [← hab, pow_one]
    · refine ⟨0, ?_⟩
      rw [one_smul, zero_smul, add_zero] at hab
      rw [← hab, pow_zero]
      rfl
    · refine ⟨2, ?_⟩
      rw [one_smul, one_smul] at hab
      rw [← hab, pow_two, LinearEquiv.mul_apply, hx2]
  have hgUi : ∀ u ∈ U, g u = (x ^ i) u := by
    intro u hu
    obtain ⟨c, d, rfl⟩ := hmemU u hu
    have hcomm : (x ^ i) (x u₀) = x ((x ^ i) u₀) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← pow_succ, ← pow_succ']
    rw [map_add, map_smul, map_smul, hgx', hi, map_add, map_smul, map_smul, hcomm]
  refine ⟨i, ⟨mul_mem (inv_mem (pow_mem hxO i)) hgO, fun u hu => ?_⟩⟩
  rw [LinearEquiv.mul_apply, hgUi u hu]
  exact (x ^ i).symm_apply_apply u

theorem commutator_le_commutator_fixW (hQ : (polarBilin Q).Nondegenerate)
    (hU : IsCompl U (perpOf Q U)) (hU2 : finrank (ZMod 2) U = 2)
    (hP : (polarBilin (Q.restrict (perpOf Q U))).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) (perpOf Q U)) {x : V ≃ₗ[ZMod 2] V} (hxΩ : x ∈ orthDerived Q)
    (hx3 : x ^ 3 = 1) (hxU : ∀ u ∈ U, x u ∈ U) (hxfix : ∀ v, x v = v ↔ v ∈ perpOf Q U)
    {H : Subgroup (V ≃ₗ[ZMod 2] V)}
    (hH : H ≤ orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))) :
    ⁅H, H⁆ ≤ ⁅fixW Q U, fixW Q U⁆ := by
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _ hxΩ
  have hxP : ∀ w ∈ perpOf Q U, x w = w := fun w hw => (hxfix w).mpr hw
  have hAfix : ⁅fixW Q U, fixW Q U⁆ ≤ fixW Q U := Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hcomm : ∀ a ∈ ⁅fixW Q U, fixW Q U⁆, ∀ i : ℕ, Commute (x ^ i) a := fun a ha i =>
    (show Commute a x from commute_of_mem_fixW hU hxU hxP (hAfix ha)).symm.pow_left i
  have hdec : ∀ g ∈ H, ∃ i : ℕ, (x ^ i)⁻¹ * g ∈ ⁅fixW Q U, fixW Q U⁆ := by
    intro g hg
    obtain ⟨hgΩ, hgx⟩ := Subgroup.mem_inf.mp (hH hg)
    obtain ⟨i, hi⟩ := exists_pow_inv_mul_mem_fixW hU hU2 hxO hx3 hxU hxfix
      (Subgroup.commutator_le_self _ hgΩ) (Subgroup.mem_centralizer_singleton_iff.mp hgx)
    exact ⟨i, mem_commutator_fixW_of_mem_orthDerived hQ hU hP h6 hi
      (mul_mem (inv_mem (pow_mem hxΩ i)) hgΩ)⟩
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  obtain ⟨i, hi⟩ := hdec g hg
  obtain ⟨i', hi'⟩ := hdec g' hg'
  have key := commutatorElement_mul_mul_of_commute (c := x ^ i) (c' := x ^ i')
    (a := (x ^ i)⁻¹ * g) (a' := (x ^ i')⁻¹ * g') (hcomm _ hi i) (hcomm _ hi' i) (hcomm _ hi i')
    (hcomm _ hi' i') ((Commute.refl x).pow_pow i i')
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at key
  rw [key, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hi hi') (inv_mem hi)) (inv_mem hi')

theorem centralizer_decomp_of_plane (hQ : (polarBilin Q).Nondegenerate)
    (hU : IsCompl U (perpOf Q U)) (hU2 : finrank (ZMod 2) U = 2)
    (hP : (polarBilin (Q.restrict (perpOf Q U))).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) (perpOf Q U))
    (hT : ∃ T : Submodule (ZMod 2) (perpOf Q U), finrank (ZMod 2) T = 3 ∧
      ∀ u ∈ T, (Q.restrict (perpOf Q U)) u = 0)
    {x : V ≃ₗ[ZMod 2] V} (hxΩ : x ∈ orthDerived Q) (hx3 : x ^ 3 = 1)
    (hxU : ∀ u ∈ U, x u ∈ U) (hxfix : ∀ v, x v = v ↔ v ∈ perpOf Q U) :
    orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) ≤ Subgroup.zpowers x ⊔
        ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆ ∧
      ⁅⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆,
        ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆⁆ =
        ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆ ∧
      Disjoint (Subgroup.zpowers x)
        ⁅orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)),
          orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V))⁆ := by
  classical
  set C := orthDerived Q ⊓ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) with hC
  set A := ⁅fixW Q U, fixW Q U⁆ with hA
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := Subgroup.commutator_le_self _ hxΩ
  have hxP : ∀ w ∈ perpOf Q U, x w = w := fun w hw => (hxfix w).mpr hw
  have hfixC : fixW Q U ≤ Subgroup.centralizer ({x} : Set (V ≃ₗ[ZMod 2] V)) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mpr (commute_of_mem_fixW hU hxU hxP hg)
  have hAfix : A ≤ fixW Q U := Subgroup.commutator_le.mpr fun g hg h hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hAC : A ≤ C :=
    le_inf (Subgroup.commutator_mono fixW_le_orthogonalGroup fixW_le_orthogonalGroup)
      (hAfix.trans hfixC)
  have hAA : ⁅A, A⁆ = A := commutator_commutator_fixW hU hP hT
  have hdec : ∀ g ∈ C, ∃ i : ℕ, (x ^ i)⁻¹ * g ∈ A := by
    intro g hg
    obtain ⟨hgΩ, hgx⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨i, hi⟩ := exists_pow_inv_mul_mem_fixW hU hU2 hxO hx3 hxU hxfix
      (Subgroup.commutator_le_self _ hgΩ) (Subgroup.mem_centralizer_singleton_iff.mp hgx)
    exact ⟨i, mem_commutator_fixW_of_mem_orthDerived hQ hU hP h6 hi
      (mul_mem (inv_mem (pow_mem hxΩ i)) hgΩ)⟩
  have hCC : ⁅C, C⁆ = A :=
    le_antisymm (commutator_le_commutator_fixW hQ hU hU2 hP h6 hxΩ hx3 hxU hxfix le_rfl)
      (calc A = ⁅A, A⁆ := hAA.symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hAC hAC)
  have hdisj : Disjoint (Subgroup.zpowers x) A := by
    rw [Subgroup.disjoint_def]
    intro y hyx hyA
    have hfix := (hAfix hyA).2
    have hUne : U ≠ ⊥ := fun h => by
      rw [h, finrank_bot] at hU2
      exact absurd hU2 (by norm_num)
    obtain ⟨u₀, hu₀, hu₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
    have hdis : ∀ u ∈ U, x u = u → u = 0 := fun u hu hxu =>
      (Submodule.disjoint_def.mp hU.disjoint) u hu ((hxfix u).mp hxu)
    have hord : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    obtain ⟨n, hn, rfl⟩ := (mem_zpowers_iff_mem_range_orderOf (y := y)).mp hyx |>
      Finset.mem_image.mp
    have hn3 : n < 3 := lt_of_lt_of_le (Finset.mem_range.mp hn) (Nat.le_of_dvd (by norm_num) hord)
    have hfu := hfix u₀ hu₀
    interval_cases n
    · rfl
    · exact absurd (hdis u₀ hu₀ (by simpa using hfu)) hu₀0
    · exfalso
      have h3 : x (x (x u₀)) = u₀ := by
        have := congrArg (fun f : V ≃ₗ[ZMod 2] V => f u₀) hx3
        simpa [pow_succ, LinearEquiv.mul_apply] using this
      have h2 : x (x u₀) = u₀ := by simpa [pow_two, LinearEquiv.mul_apply] using hfu
      have : x u₀ = u₀ := by
        have := congrArg x h2
        rw [h3] at this
        exact this.symm
      exact hu₀0 (hdis u₀ hu₀ this)
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, hi⟩ := hdec g hg
    rw [← mul_inv_cancel_left (x ^ i) g]
    exact Subgroup.mul_mem_sup (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) i) (hCC ▸ hi)
  · rw [hCC, hAA]
  · rw [hCC]
    exact hdisj

end Model

section Transport

theorem le_zpowers_sup_commutator_of_map {G H : Type*} [Group G] [Group H] {K C : Subgroup G}
    (hCK : C ≤ K) (ι : ↥K →* H) (hι : Function.Injective ι) {C' : Subgroup H}
    (hC' : (C.subgroupOf K).map ι = C') {b : G} (hb : b ∈ K) {y : H} (hy : ι ⟨b, hb⟩ = y)
    (h1 : C' ≤ Subgroup.zpowers y ⊔ ⁅C', C'⁆) (h2 : ⁅⁅C', C'⁆, ⁅C', C'⁆⁆ = ⁅C', C'⁆)
    (h3 : Disjoint (Subgroup.zpowers y) ⁅C', C'⁆) :
    C ≤ Subgroup.zpowers b ⊔ ⁅C, C⁆ ∧ ⁅⁅C, C⁆, ⁅C, C⁆⁆ = ⁅C, C⁆ ∧
      Disjoint (Subgroup.zpowers b) ⁅C, C⁆ := by
  set D := C.subgroupOf K with hD
  set b' : ↥K := ⟨b, hb⟩ with hb'
  have hDmap : D.map K.subtype = C := by
    rw [hD, Subgroup.subgroupOf_map_subtype, inf_of_le_left hCK]
  have hDD : (⁅D, D⁆).map K.subtype = ⁅C, C⁆ := by
    rw [Subgroup.map_commutator, hDmap]
  have hz : (Subgroup.zpowers b').map K.subtype = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]; rfl
  have hzι : (Subgroup.zpowers b').map ι = Subgroup.zpowers y := by
    rw [MonoidHom.map_zpowers, hy]
  have hDι : (⁅D, D⁆).map ι = ⁅C', C'⁆ := by rw [Subgroup.map_commutator, hC']
  refine ⟨?_, ?_, ?_⟩
  · have hle : D ≤ Subgroup.zpowers b' ⊔ ⁅D, D⁆ := by
      rw [← Subgroup.map_le_map_iff_of_injective hι, Subgroup.map_sup, hzι, hDι, hC']
      exact h1
    have := Subgroup.map_mono (f := K.subtype) hle
    rwa [hDmap, Subgroup.map_sup, hz, hDD] at this
  · have hDD2 : ⁅⁅D, D⁆, ⁅D, D⁆⁆ = ⁅D, D⁆ := by
      apply Subgroup.map_injective hι
      rw [Subgroup.map_commutator, hDι, h2]
    rw [← hDD, ← Subgroup.map_commutator, hDD2]
  · have hbot : Subgroup.zpowers b' ⊓ ⁅D, D⁆ = ⊥ := by
      apply Subgroup.map_injective hι
      rw [Subgroup.map_inf_eq _ _ ι hι, hzι, hDι, Subgroup.map_bot]
      exact disjoint_iff.mp h3
    rw [disjoint_iff, ← hz, ← hDD, ← Subgroup.map_inf_eq _ _ K.subtype K.subtype_injective, hbot,
      Subgroup.map_bot]

end Transport

section TwD7

open CFSG.Open CFSG.Assembly CFSG.ClassicalGroups.Orthogonal CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.OrthBlk CFSG.LieType.Universal.Spin

theorem centralizer_inf_eq_zpowers_sup_commutator_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) :
    Subgroup.centralizer ({B.b 1} : Set G) ⊓ K = Subgroup.zpowers (B.b 1) ⊔
        ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K, Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ∧
      Group.IsPerfect ↥⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ∧
      Disjoint (Subgroup.zpowers (B.b 1))
        ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
          Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ := by
  classical
  obtain ⟨_hsimple, hHyp, hCanon⟩ := id hstd
  obtain ⟨hrow, hdisjEK, hsup, hmax, hcard, -⟩ := hCanon
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, hKn, hcenter, -, -, -, -⟩ := hA
  have hrec' : RecOutTwD7 B b₀ := hrec
  obtain ⟨-, ⟨φ⟩⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hrow hcenter
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hcenter
  have hQ : (polarBilin (quadMinus 7 (ZMod 2) 1 1)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 7 (ZMod 2)
      (by decide : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0)
  have h14 : finrank (ZMod 2) (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) = 14 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
  obtain ⟨B', F, hB', heven, hU2, hφB'⟩ := exists_basis_frame_of_model hQ
    exists_totallySingular_three_quadMinus_seven (n := 7) (by norm_num) φ hb₀ hKC hdisj hsup
    hmax hcard
  have hR : B.realized K ⊆ evenFix0 7 := fun M hM =>
    realized_centralizer_subset_evenFix0_of_recOutTwD7 hB hKC hKn hdisjEK hrec'
      (realized_mono B hKC hM)
  obtain ⟨j, hj⟩ := exists_eq_or_eq_inv_of_realized_evenFix0 (n := 7) (by norm_num) hdisj hB hB'
    hR heven 0
  have hbj : B'.b j.succ ∈ K := hB'.2.2 _ (Fin.succ_ne_zero j)
  obtain ⟨U, hUdef⟩ : ∃ U, U = F.U j := ⟨_, rfl⟩
  obtain ⟨x, hxdef⟩ : ∃ x : (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
      (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2), x = F.ι (Multiplicative.ofAdd (Pi.single j 1)) :=
    ⟨_, rfl⟩
  have hφx : ((φ ⟨B'.b j.succ, hbj⟩ : ↥(orthDerived (quadMinus 7 (ZMod 2) 1 1))) :
      (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) = x := by
    rw [hxdef]
    exact hφB' j hbj
  have hnd : PolarNondegOn (quadMinus 7 (ZMod 2) 1 1) U := by
    rw [hUdef]
    exact fun u hu huv => F.nondeg j u hu fun v hv => by
      rw [polar_comm]
      exact huv v hv
  have hUc : IsCompl U (perpOf (quadMinus 7 (ZMod 2) 1 1) U) := isCompl_perp hnd
  have hPnd : PolarNondegOn (quadMinus 7 (ZMod 2) 1 1) (perp (quadMinus 7 (ZMod 2) 1 1) U) :=
    polarNondegOn_perp hQ hnd
  have hP : (polarBilin ((quadMinus 7 (ZMod 2) 1 1).restrict
      (perpOf (quadMinus 7 (ZMod 2) 1 1) U))).Nondegenerate := by
    have hrefl : (polarBilin ((quadMinus 7 (ZMod 2) 1 1).restrict
        (perpOf (quadMinus 7 (ZMod 2) 1 1) U))).IsRefl :=
      (QuadraticMap.isSymm_polarBilin _).isRefl
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mpr ?_
    intro m hm
    refine Submodule.coe_eq_zero.mp (hPnd m m.2 fun y hy => ?_)
    have h := hm ⟨y, hy⟩
    rw [polarBilin_apply_apply] at h
    simpa [QuadraticMap.polar, QuadraticMap.restrict_apply] using h
  have hU2' : finrank (ZMod 2) U = 2 := by rw [hUdef]; exact hU2 j
  have hfin : finrank (ZMod 2) U + finrank (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U) =
      14 := by
    rw [Submodule.finrank_add_eq_of_isCompl hUc, h14]
  have h12 : finrank (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U) = 12 := by
    rw [hU2'] at hfin
    omega
  have hT : ∃ T : Submodule (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U),
      finrank (ZMod 2) T = 3 ∧
        ∀ u ∈ T,
          ((quadMinus 7 (ZMod 2) 1 1).restrict (perpOf (quadMinus 7 (ZMod 2) 1 1) U)) u = 0 :=
    OrthNS.exists_ts_three_comp hPnd (by
      change 8 ≤ finrank (ZMod 2) (perpOf (quadMinus 7 (ZMod 2) 1 1) U)
      rw [h12]
      norm_num)
  have hxΩ : x ∈ orthDerived (quadMinus 7 (ZMod 2) 1 1) := hφx ▸ (φ ⟨B'.b j.succ, hbj⟩).2
  have hx3 : x ^ 3 = 1 := by
    have h3 : (⟨B'.b j.succ, hbj⟩ : ↥K) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← B'.ord j.succ, OneMemClass.coe_one]
      exact pow_orderOf_eq_one _
    rw [← hφx, ← Subgroup.coe_pow, ← map_pow, h3, map_one, OneMemClass.coe_one]
  have hxU : ∀ u ∈ U, x u ∈ U := fun u hu => by
    rw [hUdef] at hu ⊢
    rw [hxdef]
    exact F.mapsTo _ j u hu
  have hxfix : ∀ v, x v = v ↔ v ∈ perpOf (quadMinus 7 (ZMod 2) 1 1) U := fun v => by
    rw [hxdef, F.fix, hUdef]
    constructor
    · intro h
      exact mem_perp.mpr (h j (by simp))
    · intro h i hi u hu
      have hij : i = j := by
        by_contra hne
        exact hi (by simp [hne])
      subst hij
      exact mem_perp.mp h u hu
  obtain ⟨h1, h2, h3⟩ := centralizer_decomp_of_plane hQ hUc hU2' hP (by rw [h12]; norm_num)
    hT hxΩ hx3 hxU hxfix
  let ι : ↥K →* ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) :=
    (orthDerived (quadMinus 7 (ZMod 2) 1 1)).subtype.comp φ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp φ.injective
  have hιb : ι ⟨B'.b j.succ, hbj⟩ = x := hφx
  have hιφ : ∀ k : ↥K, ι k = ((φ k : ↥(orthDerived (quadMinus 7 (ZMod 2) 1 1))) :
      (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2)) :=
    fun _ => rfl
  have hC' : ((Subgroup.centralizer ({B'.b j.succ} : Set G) ⊓ K).subgroupOf K).map ι =
      orthDerived (quadMinus 7 (ZMod 2) 1 1) ⊓ Subgroup.centralizer ({x} : Set
        ((Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2] (Fin 6 ⊕ Fin 6 ⊕ Fin 2 → ZMod 2))) := by
    ext g
    constructor
    · intro hg
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
      rw [Subgroup.mem_subgroupOf] at hk
      refine Subgroup.mem_inf.mpr ⟨(φ k).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hkb : k * ⟨B'.b j.succ, hbj⟩ = ⟨B'.b j.succ, hbj⟩ * k :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hk).1)
      have h := congrArg ι hkb
      rw [map_mul, map_mul, hιb] at h
      exact h
    · intro hg
      obtain ⟨hgΩ, hgx⟩ := Subgroup.mem_inf.mp hg
      have hg' : ι (φ.symm ⟨g, hgΩ⟩) = g := by rw [hιφ, MulEquiv.apply_symm_apply]
      refine Subgroup.mem_map.mpr ⟨φ.symm ⟨g, hgΩ⟩, ?_, hg'⟩
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨?_, (φ.symm ⟨g, hgΩ⟩).2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hk : φ.symm ⟨g, hgΩ⟩ * ⟨B'.b j.succ, hbj⟩ =
          ⟨B'.b j.succ, hbj⟩ * φ.symm ⟨g, hgΩ⟩ := by
        apply hι
        rw [map_mul, map_mul, hιb, hg']
        exact Subgroup.mem_centralizer_singleton_iff.mp hgx
      exact congrArg Subtype.val hk
  obtain ⟨k1, k2, k3⟩ := le_zpowers_sup_commutator_of_map inf_le_right ι hι hC' hbj hιb h1 h2 h3
  have hcent : Subgroup.centralizer ({B'.b j.succ} : Set G) =
      Subgroup.centralizer ({B.b 1} : Set G) := by
    rcases hj with h | h
    · rw [show B.b 1 = B.b (0 : Fin 7).succ from rfl, h]
    · ext g
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
        show B.b 1 = B.b (0 : Fin 7).succ from rfl, h]
      exact Commute.inv_right_iff.symm
  have hzp : Subgroup.zpowers (B'.b j.succ) = Subgroup.zpowers (B.b 1) := by
    rcases hj with h | h
    · rw [show B.b 1 = B.b (0 : Fin 7).succ from rfl, h]
    · rw [show B.b 1 = B.b (0 : Fin 7).succ from rfl, h, Subgroup.zpowers_inv]
  rw [hcent] at k1 k2 k3
  rw [hzp] at k1 k3
  refine ⟨le_antisymm k1 (sup_le ?_ (Subgroup.commutator_le_self _)),
    Subgroup.isPerfect_iff.mpr k2, k3⟩
  rw [Subgroup.zpowers_le]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hB.2.2 1 (by decide)⟩

theorem le_sup_normalizer_of_frame {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E J : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    {ι : Type*} (U : ι → Subgroup G) (g : G) (hJU : J ≤ ⨆ k, U k)
    (hβU : b₀ * B.b 1 ∈ ⨆ k, U k)
    (hUk : ∀ k, U k ≤ J ∨ U k ≤ J.map (MulAut.conj g).toMonoidHom)
    (hEJ : E ≤ Subgroup.zpowers (b₀ * B.b 1) ⊔ J)
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J)
    (hJgen : J ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hg : g ∈ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G)) :
    E ≤ ⨆ k, U k ∧ Subgroup.centralizer ({B.b 1} : Set G) ⊓ K ≤ ⨆ k, U k ∧
      ⨆ k, U k ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G) := by
  have hEY : E ≤ ⨆ k, U k := hEJ.trans (sup_le (Subgroup.zpowers_le.mpr hβU) hJU)
  refine ⟨hEY, ?_, iSup_le fun k => ?_⟩
  · rw [(centralizer_inf_eq_zpowers_sup_commutator_twD7 hstd hB hrec).1]
    refine sup_le ?_ (hMJ.trans hJU)
    rw [Subgroup.zpowers_le]
    exact hEY (hB.1 ▸ B.b_mem_span 1)
  · rcases hUk k with h | h
    · exact h.trans hJgen
    · refine h.trans fun y hy => ?_
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem hg (hJgen hj)) (inv_mem hg)

theorem centralizer_inf_centralizer_eq_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    {R : Subgroup G} (hRK : R ≤ Subgroup.centralizer (K : Set G))
    (hC : Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K)) :
    Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer ({B.b 1} : Set G) =
      R ⊔ (Subgroup.zpowers b₀ ⊔ (Subgroup.zpowers (B.b 1) ⊔
        ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
          Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆)) := by
  obtain ⟨-, hHyp, -⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, -, -, -, -, -⟩ := hA
  rw [← (centralizer_inf_eq_zpowers_sup_commutator_twD7 hstd hB hrec).1]
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hRC : R ≤ Subgroup.centralizer ({b₀} : Set G) := hC ▸ le_sup_left
  have hRb₁ : R ≤ Subgroup.centralizer ({B.b 1} : Set G) := fun r hr =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp (hRK hr) _ hb₁K).symm
  have hb₀b₁ : b₀ ∈ Subgroup.centralizer ({B.b 1} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hKC hb₁K)).symm
  refine le_antisymm (fun x hx => ?_) (sup_le (le_inf hRC hRb₁) (sup_le ?_ ?_))
  · obtain ⟨hx0, hx1⟩ := Subgroup.mem_inf.mp hx
    have hZK : Subgroup.zpowers b₀ ⊔ K ≤ Subgroup.centralizer (R : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.le_centralizer_iff.mp hRK)
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      exact Subgroup.mem_centralizer_singleton_iff.mp (hRC hr)
    have hcommR : ∀ r ∈ R, ∀ s ∈ Subgroup.zpowers b₀ ⊔ K, r * s = s * r := fun r hr s hs =>
      Subgroup.mem_centralizer_iff.mp (hZK hs) r hr
    obtain ⟨r, hr, s, hs, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommR (hC ▸ hx0)
    have hZcK : Subgroup.zpowers b₀ ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun k hk =>
        Subgroup.mem_centralizer_singleton_iff.mp (hKC hk))
    have hcommK : ∀ z ∈ Subgroup.zpowers b₀, ∀ k ∈ K, z * k = k * z := fun z hz k hk =>
      (Subgroup.mem_centralizer_iff.mp (hZcK hz) k hk).symm
    obtain ⟨z, hz, k, hk, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommK hs
    have hzb₁ : z ∈ Subgroup.centralizer ({B.b 1} : Set G) := (Subgroup.zpowers_le.mpr hb₀b₁) hz
    have hk1 : k ∈ Subgroup.centralizer ({B.b 1} : Set G) := by
      rw [show k = z⁻¹ * r⁻¹ * (r * (z * k)) by group]
      exact mul_mem (mul_mem (inv_mem hzb₁) (inv_mem (hRb₁ hr))) hx1
    exact mul_mem (Subgroup.mem_sup_left hr) (Subgroup.mem_sup_right
      (mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hk1, hk⟩))))
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hb₀b₁⟩)
  · exact fun y hy => Subgroup.mem_inf.mpr ⟨hKC (Subgroup.mem_inf.mp hy).2, (Subgroup.mem_inf.mp hy).1⟩

theorem mem_sup_of_conj_mem_zpowers_twD7 {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    {R J : Subgroup G} (hRK : R ≤ Subgroup.centralizer (K : Set G))
    (hC : Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K))
    (hJC : J ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G)) (hβ₁J : b₀⁻¹ * B.b 1 ∈ J)
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J)
    (hinv : ∃ t ∈ J, t * (b₀⁻¹ * B.b 1) * t⁻¹ = (b₀⁻¹ * B.b 1)⁻¹) {x : G}
    (hx : x ∈ Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (hxβ₁ : x * (b₀⁻¹ * B.b 1) * x⁻¹ ∈ Subgroup.zpowers (b₀⁻¹ * B.b 1)) :
    x ∈ R ⊔ (Subgroup.zpowers (b₀ * B.b 1) ⊔ J) := by
  obtain ⟨-, hHyp, -⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, -, hcenter, -, -, -, -⟩ := hA
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hb₁3 : B.b 1 ^ 3 = 1 := by rw [← B.ord 1]; exact pow_orderOf_eq_one _
  have hcb : Commute b₀ (B.b 1) := (Subgroup.mem_centralizer_singleton_iff.mp (hKC hb₁K)).symm
  have hβ₁3 : (b₀⁻¹ * B.b 1) ^ 3 = 1 := by
    rw [hcb.inv_left.mul_pow, inv_pow, hb₀3, hb₁3, inv_one, one_mul]
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := disjoint_zpowers_of_center hKC hcenter
  have hβ₁1 : b₀⁻¹ * B.b 1 ≠ 1 := by
    intro h
    have h' : b₀ = B.b 1 := inv_mul_eq_one.mp h
    have h1 : b₀ = 1 :=
      Subgroup.disjoint_def.mp hdisj (Subgroup.mem_zpowers b₀) (by rw [h']; exact hb₁K)
    rw [h1, orderOf_one] at hb₀
    exact absurd hb₀ (by decide)
  have hβ₁o : orderOf (b₀⁻¹ * B.b 1) = 3 := orderOf_eq_prime hβ₁3 hβ₁1
  have hb₀mem : b₀ ∈ Subgroup.zpowers (b₀ * B.b 1) ⊔ J := by
    have key : ((b₀ * B.b 1) * (b₀⁻¹ * B.b 1)⁻¹) ^ 2 = b₀ := by
      rw [show (b₀ * B.b 1) * (b₀⁻¹ * B.b 1)⁻¹ = b₀ ^ 2 by rw [pow_two]; group, ← pow_mul,
        show 2 * 2 = 3 + 1 from rfl, pow_succ, hb₀3, one_mul]
    have h2 : ((b₀ * B.b 1) * (b₀⁻¹ * B.b 1)⁻¹) ^ 2 ∈ Subgroup.zpowers (b₀ * B.b 1) ⊔ J :=
      pow_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (inv_mem hβ₁J))) 2
    rwa [key] at h2
  have hb₁mem : B.b 1 ∈ Subgroup.zpowers (b₀ * B.b 1) ⊔ J := by
    have h2 : b₀⁻¹ * (b₀ * B.b 1) ∈ Subgroup.zpowers (b₀ * B.b 1) ⊔ J :=
      mul_mem (inv_mem hb₀mem) (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    rwa [inv_mul_cancel_left] at h2
  have hle : R ⊔ (Subgroup.zpowers b₀ ⊔ (Subgroup.zpowers (B.b 1) ⊔
      ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K, Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆)) ≤
      R ⊔ (Subgroup.zpowers (b₀ * B.b 1) ⊔ J) :=
    sup_le_sup_left (sup_le (Subgroup.zpowers_le.mpr hb₀mem)
      (sup_le (Subgroup.zpowers_le.mpr hb₁mem) (hMJ.trans le_sup_right))) R
  have hmain : ∀ y ∈ Subgroup.centralizer ({b₀ * B.b 1} : Set G),
      y ∈ Subgroup.centralizer ({b₀⁻¹ * B.b 1} : Set G) →
        y ∈ R ⊔ (Subgroup.zpowers (b₀ * B.b 1) ⊔ J) := by
    intro y hy hy'
    have hy2 : y ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer ({B.b 1} : Set G) := by
      rw [← centralizer_mul_inf_centralizer_inv_mul hb₀3]
      exact Subgroup.mem_inf.mpr ⟨hy, hy'⟩
    rw [centralizer_inf_centralizer_eq_twD7 hstd hB hrec hRK hC] at hy2
    exact hle hy2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxβ₁
  rw [← zpow_mod_orderOf, hβ₁o] at hk
  push_cast at hk
  have hk3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk3 with h0 | h1 | h2
  · rw [h0, zpow_zero] at hk
    exact absurd (conj_eq_one_iff.mp hk.symm) hβ₁1
  · rw [h1, zpow_one] at hk
    refine hmain x hx (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    calc x * (b₀⁻¹ * B.b 1) = x * (b₀⁻¹ * B.b 1) * x⁻¹ * x := by group
      _ = (b₀⁻¹ * B.b 1) * x := by rw [← hk]
  · rw [h2] at hk
    obtain ⟨t, htJ, ht⟩ := hinv
    have hβinv : (b₀⁻¹ * B.b 1) ^ (2 : ℤ) = (b₀⁻¹ * B.b 1)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num,
        zpow_natCast, hβ₁3]
    have e1 : x * (b₀⁻¹ * B.b 1) * x⁻¹ = (b₀⁻¹ * B.b 1)⁻¹ := by rw [← hk, hβinv]
    have e2 : t * (b₀⁻¹ * B.b 1)⁻¹ * t⁻¹ = b₀⁻¹ * B.b 1 := by
      calc t * (b₀⁻¹ * B.b 1)⁻¹ * t⁻¹ = (t * (b₀⁻¹ * B.b 1) * t⁻¹)⁻¹ := by group
        _ = b₀⁻¹ * B.b 1 := by rw [ht, inv_inv]
    have htx : t * x ∈ Subgroup.centralizer ({b₀⁻¹ * B.b 1} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc t * x * (b₀⁻¹ * B.b 1) = t * (x * (b₀⁻¹ * B.b 1) * x⁻¹) * t⁻¹ * (t * x) := by group
        _ = t * (b₀⁻¹ * B.b 1)⁻¹ * t⁻¹ * (t * x) := by rw [e1]
        _ = (b₀⁻¹ * B.b 1) * (t * x) := by rw [e2]
    have h := hmain _ (mul_mem (hJC htJ) hx) htx
    rw [show x = t⁻¹ * (t * x) by group]
    exact mul_mem (Subgroup.mem_sup_right (Subgroup.mem_sup_right (inv_mem htJ))) h

end TwD7

end CFSG.StandardType.FrameRoute.FS81
