module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L34FixedPoints
public import CFSG.LargeExtraspecial.DWInsBW
public import CFSG.RankThree.PartTwo.KFacts.L34Sylow
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeRank
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.LargeExtraspecial.DW.Insp
open Module
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.StandardType.TwoThree
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] noncomputable def triEnd {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (f : Module.End (ZMod 2) V) : Module.End (ZMod 2) V :=
  1 + f + f ^ 2

theorem range_triEnd {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {f : Module.End (ZMod 2) V} (hf : f ^ 3 = 1) :
    LinearMap.range (triEnd f) = LinearMap.ker (f - 1) := range_tri hf

theorem bw2_end {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (f g : Module.End (ZMod 2) V) (hcomm : f * g = g * f)
    (hf : f ^ 3 = 1) (hg : g ^ 3 = 1) :
    rk (triEnd f) + rk (triEnd g) + rk (triEnd (f * g)) + rk (triEnd (f * g ^ 2)) =
      finrank (ZMod 2) V + 3 * rk (triEnd f * triEnd g) := by
  let S : Set (Module.End (ZMod 2) V) := {f, g}
  have hcommS : S.Pairwise Commute := by
    intro x hx y hy _
    simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hcomm
    · exact hcomm.symm
    · exact Commute.refl _
  have hmc := Algebra.isMulCommutative_adjoin (ZMod 2) hcommS
  let : CommRing (Algebra.adjoin (ZMod 2) S) :=
    { (inferInstance : Ring (Algebra.adjoin (ZMod 2) S)) with
      mul_comm := fun x y => hmc.is_comm.comm x y }
  let φ : Algebra.adjoin (ZMod 2) S →+* Module.End (ZMod 2) V :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  have hinj : Function.Injective φ := Subtype.val_injective
  have h2 : (2 : Algebra.adjoin (ZMod 2) S) = 0 := by
    apply hinj
    rw [map_ofNat, map_zero,
      show (2 : Module.End (ZMod 2) V) = 1 + 1 from one_add_one_eq_two.symm]
    ext v
    rw [LinearMap.add_apply, Module.End.one_apply, add_self_vec']
    rfl
  let A : Algebra.adjoin (ZMod 2) S := ⟨f, Algebra.subset_adjoin (by simp [S])⟩
  let B : Algebra.adjoin (ZMod 2) S := ⟨g, Algebra.subset_adjoin (by simp [S])⟩
  have hA : A ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    change f ^ 3 = 1
    exact hf)
  have hB : B ^ 3 = 1 := hinj (by
    rw [map_pow, map_one]
    change g ^ 3 = 1
    exact hg)
  have h := bw2_one φ h2 hA hB
  have h1 : φ (tri A) = triEnd f := rfl
  have h2' : φ (tri B) = triEnd g := rfl
  have h3 : φ (tri (A * B)) = triEnd (f * g) := rfl
  have h4 : φ (tri (A * B ^ 2)) = triEnd (f * g ^ 2) := rfl
  have h5 : φ (tri A * tri B) = triEnd f * triEnd g := by
    rw [map_mul, h1, h2']
  rw [h1, h2', h3, h4, h5] at h
  exact h

theorem exists_eq_conj_aP_of_mem_eZero {k : Type*} [Field k] [Finite k]
    (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) {x : projectiveSL 3 k}
    (hx : x ∈ eZero k) (hx1 : x ≠ 1) :
    ∃ g : projectiveSL 3 k, x = g * aP u * g⁻¹ := by
  obtain ⟨i, j, hi, hj, rfl⟩ := exists_eq_aP_pow_mul_bP_pow hk hu hx
  have ha3 : aP u ^ 3 = 1 := pow_three_of_mem_eZero hk aP_mem_eZero
  have hb3 : (bP : projectiveSL 3 k) ^ 3 = 1 := pow_three_of_mem_eZero hk bP_mem_eZero
  have hab : Commute (aP u) bP := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  set A : projectiveSL 3 k := aP u with haeq
  set B : projectiveSL 3 k := bP with hbeq
  set F : projectiveSL 3 k := fP hk hu with hfeq
  set J : projectiveSL 3 k := jP hk hu with hjeq
  have hFA : MulAut.conj F A = B := by
    rw [MulAut.conj_apply, haeq, hbeq, hfeq]; exact fP_conj_aP hk hu
  have hFB : MulAut.conj F B = A⁻¹ := by
    rw [MulAut.conj_apply, haeq, hbeq, hfeq]; exact fP_conj_bP hk hu
  have hJA : MulAut.conj J A = B * A⁻¹ := by
    rw [MulAut.conj_apply, haeq, hbeq, hjeq]; exact jP_conj_aP hk hu
  have hAinv : A⁻¹ = A ^ 2 := (sq_eq_inv_of_pow_three ha3).symm
  have hBinv : B⁻¹ = B ^ 2 := (sq_eq_inv_of_pow_three hb3).symm
  have hA4 : A ^ 4 = A := by
    rw [show 4 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
  have hA22 : (A ^ 2) ^ 2 = A := by
    rw [← pow_mul, show 2 * 2 = 4 by norm_num, hA4]
  have hF2A : MulAut.conj (F ^ 2) A = A⁻¹ := by
    rw [map_pow, pow_two, MulAut.mul_apply, hFA, hFB]
  have hF2B : MulAut.conj (F ^ 2) B = B⁻¹ := by
    rw [map_pow, pow_two, MulAut.mul_apply, hFB, map_inv, hFA]
  have hF3A : MulAut.conj (F ^ 3) A = B⁻¹ := by
    rw [show F ^ 3 = F * F ^ 2 by group, map_mul, MulAut.mul_apply, hF2A, map_inv, hFA]
  have hF3B : MulAut.conj (F ^ 3) B = A := by
    rw [show F ^ 3 = F * F ^ 2 by group, map_mul, MulAut.mul_apply, hF2B, map_inv, hFB,
      inv_inv]
  have hFJA : MulAut.conj (F * J) A = A ^ 2 * B ^ 2 := by
    rw [map_mul, MulAut.mul_apply, hJA]
    simp only [map_mul, map_inv]
    rw [hFB, hFA, hAinv, hBinv]
  have hF2JA : MulAut.conj (F ^ 2 * J) A = A * B ^ 2 := by
    rw [map_mul, MulAut.mul_apply, hJA]
    simp only [map_mul, map_inv]
    rw [hF2B, hF2A, inv_inv, hBinv]
    exact (hab.pow_right 2).eq.symm
  have hF3JA : MulAut.conj (F ^ 3 * J) A = A * B := by
    rw [map_mul, MulAut.mul_apply, hJA]
    simp only [map_mul, map_inv]
    rw [hF3B, hF3A, inv_inv]
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi' with rfl | rfl | rfl <;> rcases hj' with rfl | rfl | rfl
  · exfalso; exact hx1 (by simp)
  · refine ⟨F, ?_⟩
    simpa only [pow_zero, pow_one, one_mul, mul_one, MulAut.conj_apply] using hFA.symm
  · refine ⟨F ^ 3, ?_⟩
    simpa only [pow_zero, one_mul, mul_one, MulAut.conj_apply, hBinv] using hF3A.symm
  · refine ⟨1, ?_⟩
    group
  · refine ⟨F ^ 3 * J, ?_⟩
    simpa only [pow_one, MulAut.conj_apply] using hF3JA.symm
  · refine ⟨F ^ 2 * J, ?_⟩
    simpa only [pow_one, MulAut.conj_apply] using hF2JA.symm
  · refine ⟨F ^ 2, ?_⟩
    simpa only [pow_zero, one_mul, mul_one, MulAut.conj_apply, hAinv] using hF2A.symm
  · refine ⟨J, ?_⟩
    simpa only [pow_one, one_mul, mul_one, MulAut.conj_apply, hAinv, (hab.pow_left 2).eq]
      using hJA.symm
  · refine ⟨F * J, ?_⟩
    simpa only [MulAut.conj_apply] using hFJA.symm

theorem exists_eq_conj_aP_of_orderOf_three {k : Type*} [Field k] [Finite k]
    (hk : Nat.card k = 4) {u : kˣ} (hu : u ≠ 1) {x : projectiveSL 3 k}
    (hx : orderOf x = 3) :
    ∃ g : projectiveSL 3 k, x = g * aP u * g⁻¹ := by
  have hx3 : x ^ 3 = 1 := by simpa [hx] using pow_orderOf_eq_one x
  have hxz : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨S, hxS⟩ := hxz.exists_le_sylow
  have hS9 : Nat.card (S : Subgroup (projectiveSL 3 k)) = 9 := by
    rw [Sylow.card_eq_multiplicity, factorization_card hk]
    norm_num
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hk hS9
  have hxM : x ∈ (eZero k).map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact hxS (Subgroup.mem_zpowers_iff.mpr ⟨1, pow_one x⟩)
  obtain ⟨z, hzE, hzx⟩ := Subgroup.mem_map.mp hxM
  have hord : orderOf z = 3 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g) z
    rw [show (MulAut.conj g) z = x from hzx, hx] at h
    exact h.symm
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hord
    exact absurd hord (by norm_num)
  obtain ⟨c, hc⟩ := exists_eq_conj_aP_of_mem_eZero hk hu hzE hz1
  refine ⟨g * c, ?_⟩
  rw [← MulAut.conj_apply] at hc ⊢
  rw [map_mul, MulAut.mul_apply, ← hc, ← hzx]
  rfl

theorem exists_eq_conj_of_orderOf_three {X : Type} [Group X] [Finite X] (hX : IsL3 X 2)
    {a x : X} (ha : orderOf a = 3) (hx : orderOf x = 3) :
    ∃ g : X, x = g * a * g⁻¹ := by
  obtain ⟨k, hfield, hfin, hk, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (n := 3) (p := 2) (f := 2) hX
  let : Field k := hfield
  let : Finite k := hfin
  have hk4 : Nat.card k = 4 := by rw [hk]; norm_num
  have ha' : orderOf (e a) = 3 := by rw [MulEquiv.orderOf_eq e a, ha]
  have hx' : orderOf (e x) = 3 := by rw [MulEquiv.orderOf_eq e x, hx]
  obtain ⟨u, hu⟩ := exists_units_ne_one hk4
  obtain ⟨g1, hg1⟩ := exists_eq_conj_aP_of_orderOf_three hk4 hu ha'
  obtain ⟨g2, hg2⟩ := exists_eq_conj_aP_of_orderOf_three hk4 hu hx'
  refine ⟨e.symm (g2 * g1⁻¹), ?_⟩
  have key : e x = (g2 * g1⁻¹) * (e a) * (g2 * g1⁻¹)⁻¹ := by
    rw [hg2, hg1]
    group
  calc x = e.symm (e x) := (MulEquiv.symm_apply_apply e x).symm
    _ = e.symm ((g2 * g1⁻¹) * (e a) * (g2 * g1⁻¹)⁻¹) := by rw [key]
    _ = e.symm (g2 * g1⁻¹) * a * (e.symm (g2 * g1⁻¹))⁻¹ := by
        rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]

theorem exists_commuting_orderOf_three {X : Type} [Group X] [Finite X] (hX : IsL3 X 2)
    {a : X} (ha : orderOf a = 3) :
    ∃ b : X, orderOf b = 3 ∧ a * b = b * a ∧ b ∉ Subgroup.zpowers a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hfield, hfin, hk, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.LinearCover.exists_mulEquiv_projectiveSL_of_lieModel
      (n := 3) (p := 2) (f := 2) hX
  let : Field k := hfield
  let : Finite k := hfin
  have hk4 : Nat.card k = 4 := by rw [hk]; norm_num
  have ha' : orderOf (e a) = 3 := by rw [MulEquiv.orderOf_eq e a, ha]
  have hzp : IsPGroup 3 (Subgroup.zpowers (e a)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha', pow_one])
  obtain ⟨S, ha'S⟩ := hzp.exists_le_sylow
  have hS9 : Nat.card (S : Subgroup (projectiveSL 3 k)) = 9 := by
    rw [Sylow.card_eq_multiplicity, factorization_card hk4]
    norm_num
  have hS : IsElementaryAbelian 3 (S : Subgroup (projectiveSL 3 k)) :=
    isElementaryAbelian_of_card_eq_nine hk4 hS9
  have hnotle : ¬ (S : Subgroup (projectiveSL 3 k)) ≤ Subgroup.zpowers (e a) := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [hS9, Nat.card_zpowers, ha'] at hc
    norm_num at hc
  obtain ⟨b', hb'S, hb'notin⟩ := Set.not_subset.mp hnotle
  have hb'1 : b' ≠ 1 := by
    intro h
    exact hb'notin (h ▸ Subgroup.one_mem _)
  have hb'3 : (b' : projectiveSL 3 k) ^ 3 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (A := (S : Subgroup (projectiveSL 3 k))) b' hb'S
  have hb'order : orderOf b' = 3 := orderOf_eq_prime hb'3 hb'1
  have hcomm' : e a * b' = b' * e a := by
    have h := (show IsMulCommutative (S : Subgroup (projectiveSL 3 k)) from inferInstance).is_comm
      |>.comm (⟨e a, ha'S (Subgroup.mem_zpowers_iff.mpr ⟨1, pow_one (e a)⟩)⟩ :
        (S : Subgroup (projectiveSL 3 k)))
      (⟨b', hb'S⟩ : (S : Subgroup (projectiveSL 3 k)))
    exact congrArg Subtype.val h
  refine ⟨e.symm b', ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq e.symm b', hb'order]
  · apply e.injective
    show e (a * e.symm b') = e (e.symm b' * a)
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hcomm'
  · intro hb
    apply hb'notin
    have h := MonoidHom.map_zpowers e.toMonoidHom a
    rw [show e.toMonoidHom a = (e a) from rfl] at h
    rw [← h]
    simpa using Subgroup.mem_map_of_mem e.toMonoidHom hb



theorem rk_triEnd_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (f : Module.End (ZMod 2) V) :
    rk (triEnd f) ≤ finrank (ZMod 2) V := by
  rw [rk]
  exact (Submodule.finrank_mono (le_top : LinearMap.range (triEnd f) ≤ ⊤)).trans_eq
    (finrank_top (ZMod 2) V)

theorem rk_triEnd_sq {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (x : Module.End (ZMod 2) V) (hx : x ^ 3 = 1) :
    rk (triEnd (x ^ 2)) = rk (triEnd x) := by
  have hx2 : (x ^ 2) ^ 3 = 1 := pow_three_pow hx 2
  have hker : LinearMap.ker (x ^ 2 - 1) = LinearMap.ker (x - 1) := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    constructor
    · intro h
      have hpow : x ((x ^ 2) v) = (x ^ 3) v := by
        rw [pow_two, pow_three]
        simp only [Module.End.mul_apply]
      have h' := congrArg (fun w => x w) h
      rw [hpow] at h'
      rw [hx, Module.End.one_apply] at h'
      exact h'.symm
    · intro h
      rw [pow_two, Module.End.mul_apply, h, h]
  rw [rk, rk, range_triEnd hx2, range_triEnd hx, hker]

lemma rk_triEnd_conj {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (y z y' : Module.End (ZMod 2) W)
    (hyy' : y * y' = 1) (hy'y : y' * y = 1) :
    rk (triEnd (y * z * y')) = rk (triEnd z) := by
  have htri : triEnd (y * z * y') = y * triEnd z * y' := by
    have hsq : (y * z * y') ^ 2 = y * z ^ 2 * y' := by
      calc (y * z * y') ^ 2 = (y * z * y') * (y * z * y') := by rw [pow_two]
        _ = y * z * (y' * y) * z * y' := by noncomm_ring
        _ = y * z * 1 * z * y' := by rw [hy'y]
        _ = y * z * z * y' := by noncomm_ring
        _ = y * (z * z) * y' := by noncomm_ring
        _ = y * z ^ 2 * y' := by rw [pow_two]
    rw [triEnd, hsq]
    calc 1 + y * z * y' + y * z ^ 2 * y' =
        y * 1 * y' + y * z * y' + y * z ^ 2 * y' := by rw [mul_one, hyy']
      _ = y * triEnd z * y' := by rw [triEnd]; noncomm_ring
  rw [htri, rk, rk]
  have hy_inj : Function.Injective y := by
    intro u v huv
    have h := congrArg y' huv
    simpa only [← Module.End.mul_apply, hy'y, Module.End.one_apply] using h
  have hy'_surj : Function.Surjective y' := by
    intro v
    exact ⟨y v, by rw [← Module.End.mul_apply, hy'y, Module.End.one_apply]⟩
  have hrange : LinearMap.range (y * triEnd z * y') = (LinearMap.range (triEnd z)).map y := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hy'_surj, Submodule.map_top, LinearMap.range_comp]
  rw [hrange]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective y hy_inj
    (LinearMap.range (triEnd z)))).symm

lemma conj_fixed_dims {X : Type} [Group X] [Finite X] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (hX : IsL3 X 2)
    (ρ : Representation (ZMod 2) X V) (β : Module.End (ZMod 2) V)
    (hβcomm : ∀ x : X, ρ x ∘ₗ β = β ∘ₗ ρ x) (a : X) (ha : orderOf a = 3) :
    (∀ x : X, orderOf x = 3 → rk (triEnd (ρ x)) = rk (triEnd (ρ a))) ∧
    (∀ x : X, orderOf x = 3 → rk (triEnd (ρ x * β)) = rk (triEnd (ρ a * β))) := by
  have hcomm : ∀ g : X, ρ g * β = β * ρ g := by
    intro g
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact hβcomm g
  constructor
  · intro x hx
    obtain ⟨g, hg⟩ := exists_eq_conj_of_orderOf_three hX ha hx
    have hρ : ρ x = ρ g * ρ a * ρ g⁻¹ := by rw [hg, map_mul, map_mul]
    rw [hρ]
    exact rk_triEnd_conj (ρ g) (ρ a) (ρ g⁻¹)
      (by rw [← map_mul, mul_inv_cancel, map_one])
      (by rw [← map_mul, inv_mul_cancel, map_one])
  · intro x hx
    obtain ⟨g, hg⟩ := exists_eq_conj_of_orderOf_three hX ha hx
    have hρ : ρ x = ρ g * ρ a * ρ g⁻¹ := by rw [hg, map_mul, map_mul]
    have hsplit : (ρ g * ρ a * ρ g⁻¹) * β = ρ g * (ρ a * β) * ρ g⁻¹ := by
      calc (ρ g * ρ a * ρ g⁻¹) * β = ρ g * ρ a * (ρ g⁻¹ * β) := by noncomm_ring
        _ = ρ g * ρ a * (β * ρ g⁻¹) := by rw [hcomm (g⁻¹)]
        _ = ρ g * (ρ a * β) * ρ g⁻¹ := by noncomm_ring
    rw [hρ, hsplit]
    exact rk_triEnd_conj (ρ g) (ρ a * β) (ρ g⁻¹)
      (by rw [← map_mul, mul_inv_cancel, map_one])
      (by rw [← map_mul, inv_mul_cancel, map_one])

lemma even_finrank_sub_rk_triEnd {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (A : Module.End (ZMod 2) W) (hA : A ^ 3 = 1) :
    Even (finrank (ZMod 2) W - rk (triEnd A)) := by
  have hfp : ∀ u ∈ LinearMap.range (A - 1), A u = u → u = 0 := by
    intro u hu hfix
    obtain ⟨w, rfl⟩ := hu
    have h2 : (A - 1) ((A - 1) w) = 0 := by
      rw [LinearMap.sub_apply, Module.End.one_apply, hfix, sub_self]
    have h3 : A (A w) + w = 0 := by
      have hh := h2
      rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.sub_apply,
        Module.End.one_apply, LinearMap.map_sub] at hh
      have hcalc : A (A w) - A w - (A w - w) = A (A w) + w := by
        calc A (A w) - A w - (A w - w) = A (A w) - (A w + A w) + w := by abel
          _ = A (A w) - 0 + w := by rw [add_self_vec' (A w)]
          _ = A (A w) + w := by abel
      rwa [hcalc] at hh
    have h2' : (A * A) w + w = 0 := by
      rw [Module.End.mul_apply]
      exact h3
    have h3' : A ((A * A) w + w) = 0 := by rw [h2', map_zero]
    rw [map_add] at h3'
    have h4 : A ((A * A) w) = (A ^ 3) w := by
      rw [pow_three]
      simp only [Module.End.mul_apply]
    rw [h4, hA, Module.End.one_apply] at h3'
    have hAw : A w = w := by
      have h3'' : A w + w = 0 := by rw [add_comm]; exact h3'
      have hww : w + w = 0 := add_self_vec' w
      calc A w = A w + 0 := by rw [add_zero]
        _ = A w + (w + w) := by rw [hww]
        _ = (A w + w) + w := by abel
        _ = 0 + w := by rw [h3'']
        _ = w := by rw [zero_add]
    rw [LinearMap.sub_apply, Module.End.one_apply, hAw, sub_self]
  have heven := even_finrank_of_fpf (K := ZMod 2) (V := W) (by norm_num : Nat.card
    (ZMod 2) = 2) hA (x := A) (U := LinearMap.range (A - 1))
    (fun u hu => by
      obtain ⟨w, rfl⟩ := hu
      exact ⟨A w, by
        rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.sub_apply,
          Module.End.one_apply, LinearMap.map_sub]⟩) hfp
  have hsplit := LinearMap.finrank_range_add_finrank_ker (A - 1)
  have hker : finrank (ZMod 2) (LinearMap.ker (A - 1)) = rk (triEnd A) := by
    rw [rk, range_triEnd hA]
  rw [hker] at hsplit
  have hsub : finrank (ZMod 2) W - rk (triEnd A) =
      finrank (ZMod 2) (LinearMap.range (A - 1)) := by omega
  rw [hsub]
  exact heven

lemma arith_one_fixed_point {t n c : ℕ} (hI : 4 * t = n + 3 * c) (hct : c ≤ t) (hn : 1 ≤ n)
    (hpar : Even (n - t)) : (t = 1 ∧ n = 1) ∨ 2 ≤ t := by
  rcases Nat.lt_or_ge t 2 with hlt | hge
  · left
    have ht1 : t = 1 := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · exfalso; omega
      · omega
    have hc01 : c = 0 ∨ c = 1 := by omega
    rcases hc01 with hc0 | hc1
    · exfalso
      have hn4 : n = 4 := by omega
      obtain ⟨q, hq⟩ := hpar
      omega
    · refine ⟨ht1, ?_⟩
      omega
  · right
    exact hge

private lemma fpf_branch {X : Type} [Group X] [Finite X] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Nontrivial V] [IsSimpleGroup X]
    (ρ : Representation (ZMod 2) X V) (β : Module.End (ZMod 2) V) (a b : X)
    (hβ3 : β ^ 3 = 1) (ha : orderOf a = 3) (hb3 : orderOf b = 3)
    (hcomm : ∀ x : X, ρ x * β = β * ρ x) (hρab : ρ a * ρ b = ρ b * ρ a)
    (hra3 : ρ a ^ 3 = 1) (hrb3 : ρ b ^ 3 = 1) (hA3 : (ρ a * β) ^ 3 = 1)
    (hab3 : orderOf (a * b) = 3) (hab23 : orderOf (a * b ^ 2) = 3)
    (t s u n cL : ℕ) (ht : t = rk (triEnd (ρ a))) (hs : s = rk (triEnd (ρ a * β)))
    (hu : u = rk (triEnd β)) (hn : n = finrank (ZMod 2) V)
    (hcL : cL = rk (triEnd (ρ a * β) * triEnd (ρ b)))
    (hphi_rho : ∀ x : X, orderOf x = 3 → rk (triEnd (ρ x)) = t)
    (hphi_beta : ∀ x : X, orderOf x = 3 → rk (triEnd (ρ x * β)) = s)
    (hc_le : ∀ x y : Module.End (ZMod 2) V, rk (triEnd x * triEnd y) ≤ rk (triEnd x))
    (hnontriv : ∃ x v, ρ x v ≠ v) (hu0 : u = 0) : 2 ≤ s := by
  have ha3 : a ^ 3 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  have hb3' : b ^ 3 = 1 := by simpa [hb3] using pow_orderOf_eq_one b
  have ha2 : orderOf (a ^ 2) = 3 := by
    rw [sq_eq_inv_of_pow_three ha3, orderOf_inv, ha]
  have hABcomm : (ρ a * β) * ρ b = ρ b * (ρ a * β) := by
    calc (ρ a * β) * ρ b = ρ a * (β * ρ b) := by noncomm_ring
      _ = ρ a * (ρ b * β) := by rw [← hcomm b]
      _ = (ρ a * ρ b) * β := by noncomm_ring
      _ = (ρ b * ρ a) * β := by rw [hρab]
      _ = ρ b * (ρ a * β) := by noncomm_ring
  have hbw := bw2_end (ρ a * β) (ρ b) hABcomm hA3 hrb3
  have h_AB : rk (triEnd ((ρ a * β) * ρ b)) = s := by
    rw [show (ρ a * β) * ρ b = ρ (a * b) * β from by
      calc (ρ a * β) * ρ b = ρ a * (β * ρ b) := by noncomm_ring
        _ = ρ a * (ρ b * β) := by rw [← hcomm b]
        _ = (ρ a * ρ b) * β := by noncomm_ring
        _ = ρ (a * b) * β := by rw [← map_mul]]
    exact hphi_beta (a * b) hab3
  have h_AB2 : rk (triEnd ((ρ a * β) * ρ b ^ 2)) = s := by
    have hb2 : β * ρ b ^ 2 = ρ b ^ 2 * β := by
      have h := hcomm (b ^ 2)
      rw [map_pow] at h
      exact h.symm
    rw [show (ρ a * β) * ρ b ^ 2 = ρ (a * b ^ 2) * β from by
      calc (ρ a * β) * ρ b ^ 2 = ρ a * (β * ρ b ^ 2) := by noncomm_ring
        _ = ρ a * (ρ b ^ 2 * β) := by rw [hb2]
        _ = (ρ a * ρ b ^ 2) * β := by noncomm_ring
        _ = ρ (a * b ^ 2) * β := by rw [← map_pow, ← map_mul]]
    exact hphi_beta (a * b ^ 2) hab23
  have hII : 3 * s + t = n + 3 * cL := by
    have h := hbw
    rw [← hn, ← hs, hphi_rho b hb3, h_AB, h_AB2, ← hcL] at h
    omega
  have h_Ab2 : rk (triEnd (ρ a * β ^ 2)) = s := by
    have hra4 : ρ a ^ 4 = ρ a := by
      rw [show 4 = 3 + 1 by norm_num, pow_add, hra3, one_mul, pow_one]
    have hβa2 : β * ρ a ^ 2 = ρ a ^ 2 * β := by
      have h := hcomm (a ^ 2)
      rw [map_pow] at h
      exact h.symm
    have hsq : (ρ a ^ 2 * β) ^ 2 = ρ a * β ^ 2 := by
      rw [pow_two]
      calc (ρ a ^ 2 * β) * (ρ a ^ 2 * β)
          = ρ a ^ 2 * (β * ρ a ^ 2) * β := by noncomm_ring
        _ = ρ a ^ 2 * (ρ a ^ 2 * β) * β := by rw [hβa2]
        _ = ρ a ^ 4 * β ^ 2 := by rw [pow_two, pow_two]; noncomm_ring
        _ = ρ a * β ^ 2 := by rw [hra4]
    have hc : (ρ a ^ 2 * β) ^ 3 = 1 := by
      have hcomm2 : Commute (ρ a ^ 2) β := by
        have h := hcomm (a ^ 2)
        rwa [map_pow] at h
      rw [Commute.mul_pow hcomm2, pow_three_pow hra3 2, hβ3, one_mul]
    rw [← hsq]
    rw [rk_triEnd_sq (ρ a ^ 2 * β) hc, ← map_pow]
    exact hphi_beta (a ^ 2) ha2
  set cB : ℕ := rk (triEnd (ρ a) * triEnd β) with hcB
  have hIIb : t + 2 * s = n + 3 * cB := by
    have h := bw2_end (ρ a) β (hcomm a) hra3 hβ3
    rw [← hn, ← ht, ← hu, hu0, ← hs, ← hcB, h_Ab2] at h
    omega
  have ht_le : t ≤ n := by
    rw [ht, hn]
    exact rk_triEnd_le (ρ a)
  have hsne0 : s ≠ 0 := by
    intro hs0
    have ht_eq : t = n := by
      have hc0 : cL = 0 := by
        have hle := hc_le (ρ a * β) (ρ b)
        omega
      omega
    have hrn : rk (triEnd (ρ a)) = n := by rw [← ht]; exact ht_eq
    have hρa1 : ρ a = 1 := by
      ext v
      have hrange : LinearMap.range (triEnd (ρ a)) = ⊤ := by
        refine Submodule.eq_top_of_finrank_eq ?_
        rw [show finrank (ZMod 2) (LinearMap.range (triEnd (ρ a))) = rk (triEnd (ρ a))
          from rfl, hrn, ← hn]
      have hv : v ∈ LinearMap.range (triEnd (ρ a)) := by rw [hrange]; exact Submodule.mem_top
      have hv' : v ∈ LinearMap.ker (ρ a - 1) := by rwa [range_triEnd hra3] at hv
      simpa only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        sub_eq_zero] using hv'
    have ha_ne1 : a ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at ha
      omega
    have hker : a ∈ MonoidHom.ker ρ.asGroupHom := by
      rw [MonoidHom.mem_ker]
      apply Units.ext
      rw [Representation.asGroupHom_apply]
      exact hρa1
    have hN : MonoidHom.ker ρ.asGroupHom = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ.asGroupHom) with h | h
      · exfalso
        have : a ∈ (⊥ : Subgroup X) := by rw [← h]; exact hker
        exact ha_ne1 (Subgroup.mem_bot.mp this)
      · exact h
    have hρtriv : ∀ x : X, ρ x = 1 := by
      intro x
      have hx : x ∈ MonoidHom.ker ρ.asGroupHom := by rw [hN]; trivial
      rw [MonoidHom.mem_ker] at hx
      have hcoe := congrArg (fun u : (Module.End (ZMod 2) V)ˣ => (u : Module.End (ZMod 2) V)) hx
      rw [Representation.asGroupHom_apply] at hcoe
      simpa using hcoe
    obtain ⟨x, v, hv⟩ := hnontriv
    rw [hρtriv x] at hv
    exact hv rfl
  have hsne1 : s ≠ 1 := by
    intro hs1
    omega
  omega

private lemma one_branch {X : Type} [Group X] [Finite X] {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] [Nontrivial V]
    (ρ : Representation (ZMod 2) X V) (β : Module.End (ZMod 2) V) (a b : X)
    (hnontriv : ∃ x v, ρ x v ≠ v) (hβ1 : β = 1)
    (t s n cL : ℕ) (hst : s = t)
    (htriv_one : n = 1 → ∀ x : X, ρ x = 1)
    (hI : 4 * t = n + 3 * cL) (hpar : Even (n - t))
    (hn1pos : 1 ≤ n) (hc_le_t : cL ≤ t) : 2 ≤ s := by
  rw [hst]
  rcases arith_one_fixed_point hI hc_le_t hn1pos hpar with ⟨ht1, hn1⟩ | ht2
  · have htriv := htriv_one hn1
    obtain ⟨x, v, hv⟩ := hnontriv
    rw [htriv x] at hv
    exact absurd rfl hv
  · exact ht2

theorem k_L34Fix_holds : K_L34Fix := by
  classical
  intro X _ _ hX V _ _ _ ρ β hβcomm hβ3 hirr hnontriv a ha
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hX
  obtain ⟨x₀, v₀, hv₀⟩ := hnontriv
  have hnontriv' : ∃ x v, ρ x v ≠ v := ⟨x₀, v₀, hv₀⟩
  have hv₀0 : v₀ ≠ 0 := by
    rintro rfl
    exact hv₀ (map_zero _)
  have : Nontrivial V := ⟨v₀, 0, hv₀0⟩
  obtain ⟨b, hb3, hcomm_ab, hbnot⟩ := exists_commuting_orderOf_three hX ha
  have hcomm_end : ∀ x : X, ρ x * β = β * ρ x := by
    intro x
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    exact hβcomm x
  have ha3 : a ^ 3 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  have hb3' : b ^ 3 = 1 := by simpa [hb3] using pow_orderOf_eq_one b
  have hra3 : ρ a ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hrb3 : ρ b ^ 3 = 1 := by rw [← map_pow, hb3', map_one]
  have hA3 : (ρ a * β) ^ 3 = 1 := by
    rw [Commute.mul_pow (hcomm_end a), hra3, hβ3, one_mul]
  have hab3 : orderOf (a * b) = 3 := by
    apply orderOf_eq_prime
    · rw [Commute.mul_pow hcomm_ab, ha3, hb3', one_mul]
    · rintro h
      have hb_eq : b = a⁻¹ := by
        calc b = a⁻¹ * (a * b) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
          _ = a⁻¹ := by rw [h, mul_one]
      exact hbnot (by rw [hb_eq]; exact Subgroup.mem_zpowers_iff.mpr ⟨-1, by simp⟩)
  have hab23 : orderOf (a * b ^ 2) = 3 := by
    apply orderOf_eq_prime
    · rw [Commute.mul_pow ((show Commute a b from hcomm_ab).pow_right 2), ha3, one_mul,
        ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hb3', one_pow]
    · rintro h
      have hb2_eq : b ^ 2 = a⁻¹ := by
        calc b ^ 2 = a⁻¹ * (a * b ^ 2) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
          _ = a⁻¹ := by rw [h, mul_one]
      have hb4 : b ^ 4 = b := by
        rw [show 4 = 3 + 1 by norm_num, pow_add, hb3', one_mul, pow_one]
      have hb_eq : b = (a⁻¹) ^ 2 := by
        calc b = b ^ 4 := hb4.symm
          _ = (b ^ 2) ^ 2 := by rw [← pow_mul]
          _ = (a⁻¹) ^ 2 := by rw [hb2_eq]
      exact hbnot (by rw [hb_eq]; exact Subgroup.mem_zpowers_iff.mpr ⟨-2, by simp⟩)
  set n : ℕ := finrank (ZMod 2) V with hn
  set t : ℕ := rk (triEnd (ρ a)) with ht
  set s : ℕ := rk (triEnd (ρ a * β)) with hs
  set u : ℕ := rk (triEnd β) with hu
  have hconj := conj_fixed_dims hX ρ β hβcomm a ha
  have hphi_rho : ∀ x : X, orderOf x = 3 → rk (triEnd (ρ x)) = t := by
    intro x hx
    rw [hconj.1 x hx, ← ht]
  have hphi_beta : ∀ x : X, orderOf x = 3 → rk (triEnd (ρ x * β)) = s := by
    intro x hx
    rw [hconj.2 x hx, ← hs]
  set W : Submodule (ZMod 2) V := LinearMap.ker (β - 1) with hWdef
  have hXW : ∀ x : X, W.map (ρ x) ≤ W := by
    intro x
    rintro _ ⟨w, hw, rfl⟩
    have hw' : β w = w := by
      have h1 : (β - 1) w = 0 := hw
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    show (β - 1) (ρ x w) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    have h := congrArg (fun f : Module.End (ZMod 2) V => f w) (hcomm_end x)
    simp only [Module.End.mul_apply] at h
    rw [← h, hw']
  have hβW : W.map β ≤ W := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : β w = w := by
      have h1 : (β - 1) w = 0 := hw
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
    show (β - 1) (β w) = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    rw [hw', hw']
  have hu_eq : u = finrank (ZMod 2) W := by
    rw [hu, rk, range_triEnd hβ3]
  have hβ_dich : u = 0 ∨ u = n := by
    rcases hirr W hXW hβW with hWbot | hWtop
    · left
      rw [hu_eq, hWbot, finrank_bot]
    · right
      rw [hu_eq, hWtop, finrank_top]
  have hβ_one_of_u : u = n → β = 1 := by
    intro hun
    have hWtop : W = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [← hu_eq, hun]
    ext v
    have hv : v ∈ W := by rw [hWtop]; exact Submodule.mem_top
    simpa [W, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hv
  have hρab : ρ a * ρ b = ρ b * ρ a := by rw [← map_mul, ← map_mul, hcomm_ab]
  have hc_le : ∀ (x : Module.End (ZMod 2) V) (y : Module.End (ZMod 2) V),
      rk (triEnd x * triEnd y) ≤ rk (triEnd x) := by
    intro x y
    rw [rk, rk, Module.End.mul_eq_comp]
    exact Submodule.finrank_mono (LinearMap.range_comp_le_range (triEnd y) (triEnd x))
  have h_rab : rk (triEnd (ρ a * ρ b)) = t := by
    rw [show ρ a * ρ b = ρ (a * b) from by rw [← map_mul]]
    exact hphi_rho (a * b) hab3
  have h_rab2 : rk (triEnd (ρ a * ρ b ^ 2)) = t := by
    rw [show ρ a * ρ b ^ 2 = ρ (a * b ^ 2) from by rw [← map_pow, ← map_mul]]
    exact hphi_rho (a * b ^ 2) hab23
  set cL : ℕ := rk (triEnd (ρ a * β) * triEnd (ρ b)) with hcL
  have htriv_one : n = 1 → ∀ x : X, ρ x = 1 := by
    intro hn1 x
    ext w
    have hspan : Submodule.span (ZMod 2) ({v₀} : Set V) = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      rw [finrank_span_singleton hv₀0, ← hn, hn1]
    have hw : w ∈ Submodule.span (ZMod 2) ({v₀} : Set V) := by
      rw [hspan]; exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    have hvimage : ρ x v₀ ∈ Submodule.span (ZMod 2) ({v₀} : Set V) := by
      rw [hspan]; exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hvimage
    obtain ⟨d, hd⟩ := hvimage
    have hd1 : d = 1 := by
      have hinj : Function.Injective (ρ x) := (ρ.apply_bijective x).1
      have hd0 : d ≠ 0 := by
        intro hdzero
        have hz : ρ x v₀ = 0 := by rw [← hd, hdzero, zero_smul]
        have hzero : ρ x v₀ = ρ x 0 := by rw [hz, map_zero]
        exact hv₀0 (hinj hzero)
      fin_cases d
      · exact absurd rfl hd0
      · rfl
    rw [map_smul, Module.End.one_apply]
    have hdv : ρ x v₀ = d • v₀ := hd.symm
    rw [hdv, hd1, one_smul]
  have hs2 : 2 ≤ s := by
    rcases hβ_dich with hu0 | hun
    · exact fpf_branch ρ β a b hβ3 ha hb3 hcomm_end hρab hra3 hrb3 hA3 hab3 hab23
        t s u n cL ht hs hu hn hcL hphi_rho hphi_beta hc_le hnontriv' hu0
    · have hβ1 : β = 1 := hβ_one_of_u hun
      have hst : s = t := by rw [hs, ht, hβ1, mul_one]
      have hbw := bw2_end (ρ a) (ρ b) hρab hra3 hrb3
      have hcL' : cL = rk (triEnd (ρ a) * triEnd (ρ b)) := by
        rw [hcL, hβ1, mul_one]
      have hI : 4 * t = n + 3 * cL := by
        have h := hbw
        rw [← hn, ← ht, hphi_rho b hb3, h_rab, h_rab2, ← hcL'] at h
        omega
      have hc_le_t : cL ≤ t := by
        rw [hcL', ht]
        exact hc_le (ρ a) (ρ b)
      have hpar : Even (n - t) := by
        have h := even_finrank_sub_rk_triEnd (ρ a) hra3
        rwa [← hn, ← ht] at h
      have hn1pos : 1 ≤ n := by
        rw [hn]
        exact finrank_pos
      exact one_branch ρ β a b hnontriv' hβ1 t s n cL hst htriv_one hI hpar hn1pos hc_le_t
  have hker : LinearMap.ker (ρ a ∘ₗ β - 1) = LinearMap.range (triEnd (ρ a * β)) := by
    rw [show ρ a ∘ₗ β = ρ a * β from (Module.End.mul_eq_comp _ _).symm]
    rw [range_triEnd hA3]
  rw [hker]
  have hcard : Nat.card (LinearMap.range (triEnd (ρ a * β))) = 2 ^ s := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := LinearMap.range (triEnd (ρ a * β)))
    rw [h, show Nat.card (ZMod 2) = 2 by norm_num]
    rfl
  rw [hcard]
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4]
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mpr hs2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
