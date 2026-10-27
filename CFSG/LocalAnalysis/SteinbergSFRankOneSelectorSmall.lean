module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRoot
public import CFSG.Sporadic.J1
public import CFSG.GH74.GLS.C3.Layer1.BkP89J2M12
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalOuter
public import CFSG.LocalAnalysis.SteinbergCDOddThreeElementaryBound
public import CFSG.GH74.Orders.LieType
public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer
public import CFSG.LocalAnalysis.SteinbergSFSingleCommPrincipalLayersModels
public import CFSG.Assembly.OrderReductions.LinearOrders
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace RankOneSelector

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.EvenBN.GMSK
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem card_le_of_not_dvd {D : Type*} [Group D] [Finite D] {k : ℕ}
    (hN : ¬ 2 ^ (k + 1) ∣ Nat.card D) {P : Subgroup D} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 2 ^ k := by
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card P ∣ Nat.card D := Subgroup.card_subgroup_dvd_card P
  rw [hm] at hdvd ⊢
  by_contra hlt
  have hkm : k + 1 ≤ m := by
    by_contra h
    exact hlt (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact hN ((pow_dvd_pow 2 hkm).trans hdvd)

theorem card_le_of_equiv {D X : Type*} [Group D] [Group X] [Finite X] (e : D ≃* X) {k : ℕ}
    (hN : ¬ 2 ^ (k + 1) ∣ Nat.card X) {P : Subgroup D} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 2 ^ k := by
  have : Finite D := Finite.of_equiv _ e.symm.toEquiv
  refine card_le_of_not_dvd ?_ hP
  rwa [Nat.card_congr e.toEquiv]

theorem card_le_of_J1 {D : Type} [Group D]
    (hD : NativeSporadic.IsSporadic D .J1) {P : Subgroup D} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 8 := by
  obtain ⟨e⟩ := hD
  change D ≃* NativeSporadic.J1 at e
  have : Finite NativeSporadic.J1 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.J1.card_J1]; norm_num)
  have h := card_le_of_equiv (k := 3) e (by
    change ¬ 2 ^ 4 ∣ Nat.card NativeSporadic.J1
    rw [CFSG.Sporadic.J1.card_J1]
    decide) hP
  simpa using h

theorem card_le_of_M12 {D : Type} [Group D]
    (hD : NativeSporadic.IsSporadic D .M12) {P : Subgroup D} (hP : IsPGroup 2 P) :
    Nat.card P ≤ 64 := by
  obtain ⟨e⟩ := hD
  change D ≃* NativeSporadic.M12 at e
  have : Finite NativeSporadic.M12 :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num)
  have h := card_le_of_equiv (k := 6) e (by
    change ¬ 2 ^ 7 ∣ Nat.card NativeSporadic.M12
    rw [CFSG.Sporadic.Mathieu.card_M12]
    decide) hP
  simpa using h

theorem card_le_of_A7 {D : Type} [Group D] (hD : Nonempty (D ≃* alternatingGroup (Fin 7)))
    {P : Subgroup D} (hP : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  obtain ⟨e⟩ := hD
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    have h := two_mul_card_alternatingGroup (α := Fin 7)
    rw [Fintype.card_perm, Fintype.card_fin] at h
    rw [Nat.card_eq_fintype_card]
    have : Nat.factorial 7 = 5040 := by decide
    omega
  have h := card_le_of_equiv (k := 3) e (by rw [hA]; decide) hP
  simpa using h

theorem card_le_of_psl_two_twentyfive {D : Type} [Group D]
    (hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel D .PSL 2 5 2) {P : Subgroup D}
    (hP : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hD
  have hc : Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) = 7800 := by
    rw [Nat.card_congr (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      2 K).symm.toEquiv, CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2
      (by norm_num), hK]
    decide
  have : Finite (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K)) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have h := card_le_of_equiv (k := 3) e (by rw [hc]; decide) hP
  simpa using h

open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open PrincipalLayers (statedProjEquivProjectiveSL)

theorem isElementaryAbelian_of {D : Type*} [Group D] {E : Subgroup D}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hs : ∀ x ∈ E, x * x = 1) :
    CFSG.IsElementaryAbelian 2 E := CFSG.IsElementaryAbelian.two_of_forall_mul_self hc hs

theorem psl_three_five_bounds {D : Type} [Group D]
    (hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel D .PSL 3 5 1) :
    (∀ P : Subgroup D, IsPGroup 2 P → Nat.card P ≤ 32) ∧
      ∀ E : Subgroup D, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 4 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hD
  have hK5 : Nat.card K = 5 := by simpa using hK
  let η := e.trans (statedProjEquivProjectiveSL 3 K)
  have hb :=
    CFSG.LocalAnalysis.SteinbergCD.odd_degree_three_projective_groups_elementary_two_bound.{0, 0}
  refine ⟨fun P hP => ?_, fun E hc hs => ?_⟩
  · have h := (hb.2.2.2.1 K hK5).2 (P.map η.toMonoidHom) (hP.map _)
    rwa [Subgroup.card_map_of_injective η.injective] at h
  · have h := hb.1 K (by rw [hK5]; decide) (E.map η.toMonoidHom)
      (isElementaryAbelian_of (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul, hc x hx y hy]) (by
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_mul, hs x hx, map_one]))
    rwa [Subgroup.card_map_of_injective η.injective] at h

theorem psu_three_five_bounds {D : Type} [Group D]
    (hD : CFSG.Assembly.LowTwoRank.StatedClassicalModel D .PSU 3 5 1) :
    (∀ P : Subgroup D, IsPGroup 2 P → Nat.card P ≤ 16) ∧
      ∀ E : Subgroup D, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
        Nat.card E ≤ 4 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hD
  have hu : UnitaryFieldData 5 1 K := ⟨by norm_num, le_rfl, by rw [hK]; norm_num⟩
  let η := e.trans (unitaryPSUEquiv hu (n := 3) (by norm_num)).symm
  have hb :=
    CFSG.LocalAnalysis.SteinbergCD.odd_degree_three_projective_groups_elementary_two_bound.{0, 0}
  refine ⟨fun P hP => ?_, fun E hc hs => ?_⟩
  · have h := (hb.2.2.2.2 K hu).2 (P.map η.toMonoidHom) (hP.map _)
    rwa [Subgroup.card_map_of_injective η.injective] at h
  · have h := hb.2.1 5 1 K hu (by norm_num) (E.map η.toMonoidHom)
      (isElementaryAbelian_of (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [← map_mul, ← map_mul, hc x hx y hy]) (by
        rintro _ ⟨x, hx, rfl⟩
        rw [← map_mul, hs x hx, map_one]))
    rwa [Subgroup.card_map_of_injective η.injective] at h

@[expose] def rotSL (k : Type) [Field k] : Matrix.SpecialLinearGroup (Fin 2) k :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem orderOf_rotSL {k : Type} [Field k] (h2 : (2 : k) ≠ 0) : orderOf (rotSL k) = 4 := by
  have hW2 : ((rotSL k ^ 2 : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      !![-1, 0; 0, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_pow, rotSL]
    simp [sq]
  have hne : rotSL k ^ 2 ≠ 1 := by
    intro h
    have h1 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) k =>
      (A : Matrix (Fin 2) (Fin 2) k) 0 0) h
    simp only [hW2, Matrix.SpecialLinearGroup.coe_one] at h1
    simp at h1
    apply h2
    linear_combination -h1
  have h4 : rotSL k ^ 2 ^ (1 + 1) = 1 := by
    apply Subtype.ext
    rw [show (2 : ℕ) ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, Matrix.SpecialLinearGroup.coe_pow, hW2,
      Matrix.SpecialLinearGroup.coe_one]
    simp [sq, Matrix.one_fin_two]
  have h4' : orderOf (rotSL k) = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by rwa [pow_one]) h4
  rw [h4']
  norm_num

section G2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem G2_three_card {D : Type} [Group D] (hD : LieModel D .G2 0 3 1) :
    Nat.card D = 4245696 := by
  rw [CFSG.GH74.card_of_lieModel_G2 (by norm_num) hD]
  decide

theorem exists_orderOf_four_of_G2_three {D : Type} [Group D] (hD : LieModel D .G2 0 3 1) :
    ∃ x : D, orderOf x = 4 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.chevalleyExceptionalModel_of_lieModel (by decide) hD
  have hK3 : Nat.card K = 3 := by simpa using hK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : CharP K 3 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card, hK3])
  have hch : ringChar K ≠ 2 := by
    rw [ringChar.eq K 3]
    norm_num
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hch
  let i : Fin Tag.G2.rank := ⟨0, by decide⟩
  set y : adjointGroup .G2 K :=
    ⟨simpleRootSL2 .G2 K i (rotSL K), simpleRootSL2_mem_adjointGroup i (rotSL K)⟩
  have hy : orderOf y = 4 := by
    rw [← orderOf_injective (adjointGroup .G2 K).subtype (adjointGroup .G2 K).subtype_injective,
      Subgroup.coe_subtype]
    change orderOf (simpleRootSL2 .G2 K i (rotSL K)) = 4
    rw [orderOf_injective _ (simpleRootSL2_injective hch i), orderOf_rotSL h2]
  have hcen := center_adjointGroup_eq_bot_field .G2 K
  have hinj : Function.Injective (QuotientGroup.mk' (Subgroup.center (adjointGroup .G2 K))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hcen]
  refine ⟨e.symm (QuotientGroup.mk' _ y), ?_⟩
  rw [MulEquiv.orderOf_eq, orderOf_injective _ hinj, hy]

end G2

section M12

open CFSG.ComponentClassification.M12Cover CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a)) b).symm

theorem commutator_self_of_simple {D : Type*} [Group D] {S : Subgroup D} [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : ⁅S, S⁆ = S := by
  have h1 : commutator S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hc : ⁅a, b⁆ ∈ commutator S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hab hc
    · exact h
  calc ⁅S, S⁆ = (⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ : Subgroup S).map S.subtype := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = S := by
        rw [← _root_.commutator_def, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem false_of_m12_outer
    {D : Type} [Group D] (hD : NativeSporadic.IsSporadic D .M12) {α : MulAut D}
    (hα : orderOf α = 2) (hout : α ∉ (MulAut.conj : D →* MulAut D).range) {S : Subgroup D}
    (hSα : S ≤ fixedSubgroup α) (hSp : ⁅S, S⁆ = S) (hS60 : Nat.card S = 60)
    (hr : FixedRootRankOne α S) : False := by
  obtain ⟨e⟩ := hD
  change D ≃* NativeSporadic.M12 at e
  set α' : MulAut NativeSporadic.M12 := (e.symm.trans α).trans e with hα'
  have hα'x : ∀ x : D, α' (e x) = e (α x) := fun x => by
    change e (α (e.symm (e x))) = e (α x)
    rw [MulEquiv.symm_apply_apply]
  have hα'2 : orderOf α' = 2 := by
    rw [show α' = MulAut.congr e α from rfl, MulEquiv.orderOf_eq, hα]
  have hα'out : α' ∉ inner NativeSporadic.M12 := by
    rintro ⟨m, hm⟩
    apply hout
    refine ⟨e.symm m, MulEquiv.ext fun x => e.injective ?_⟩
    have h1 := congrArg (fun β : MulAut NativeSporadic.M12 => β (e x)) hm
    simp only [MulAut.conj_apply] at h1
    rw [← hα'x, ← h1, MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := exists_conj_beta_of_outer hα'2 hα'out
  set S' := S.map e.toMonoidHom with hS'
  have hS'fix : S' ≤ CFSG.Sporadic.Schreier.fixSub α' := by
    rintro _ ⟨s, hs, rfl⟩
    change α' (e s) = e s
    rw [hα'x]
    exact congrArg e (hSα hs)
  have hS'le : S' ≤ fixedD.map (MulAut.conj g).toMonoidHom := by
    have h1 : ⁅S', S'⁆ = S' := by rw [hS', ← Subgroup.map_commutator, hSp]
    rw [← h1, ← commutator_fixSub_conj_beta g, ← hg]
    exact Subgroup.commutator_mono hS'fix hS'fix
  have hS'eq : S' = fixedD.map (MulAut.conj g).toMonoidHom := by
    refine Subgroup.eq_of_le_of_card_ge hS'le ?_
    rw [card_fixedD_map_conj, hS', Subgroup.card_map_of_injective e.injective, hS60]
  set z : NativeSporadic.M12 := g * elemZ * g⁻¹ with hz
  have hzfix : α' z = z := by
    rw [hg, hz]
    exact conj_beta_apply_conj g elemZ elemZ_mem_fixSub
  have hzcomm : ∀ s ∈ S', z * s = s * z := by
    intro s hs
    rw [hS'eq] at hs
    obtain ⟨d, hd, rfl⟩ := hs
    change g * elemZ * g⁻¹ * (g * d * g⁻¹) = g * d * g⁻¹ * (g * elemZ * g⁻¹)
    have := elemZ_comm_fixedD d hd
    calc g * elemZ * g⁻¹ * (g * d * g⁻¹) = g * (elemZ * d) * g⁻¹ := by group
      _ = g * (d * elemZ) * g⁻¹ := by rw [this]
      _ = g * d * g⁻¹ * (g * elemZ * g⁻¹) := by group
  have hzord : orderOf z = 2 := by
    rw [hz, ← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_elemZ]
  set z₀ : D := e.symm z with hz₀
  have hz₀fix : z₀ ∈ fixedSubgroup α := by
    change α z₀ = z₀
    apply e.injective
    rw [← hα'x, hz₀, MulEquiv.apply_symm_apply, hzfix]
  have hz₀cen : z₀ ∈ centralizer (S : Set D) := by
    rw [mem_centralizer_iff]
    intro s hs
    apply e.injective
    rw [map_mul, map_mul, hz₀, MulEquiv.apply_symm_apply]
    exact (hzcomm (e s) ⟨s, hs, rfl⟩).symm
  have hz₀ord : orderOf z₀ = 2 := by rw [hz₀, MulEquiv.orderOf_eq, hzord]
  have hP : IsPGroup 2 (zpowers z₀) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz₀ord, pow_one])
  have hPle : zpowers z₀ ≤ fixedSubgroup α ⊓ centralizer (S : Set D) :=
    (zpowers_le).2 (mem_inf.2 ⟨hz₀fix, hz₀cen⟩)
  have hbot := (hr _ hPle hP).2 hout
  have h1 : z₀ = 1 := by
    have := mem_zpowers z₀
    rw [hbot] at this
    exact (mem_bot).1 this
  rw [h1, orderOf_one] at hz₀ord
  exact absurd hz₀ord (by norm_num)

theorem card_le_of_m12_inner {D : Type} [Group D] [Finite D]
    (hD : NativeSporadic.IsSporadic D .M12) (hnab : ∃ a b : D, a * b ≠ b * a) [IsSimpleGroup D]
    {α : MulAut D} (hα : orderOf α = 2) (hin : α ∈ (MulAut.conj : D →* MulAut D).range)
    {S : Subgroup D} (hSα : S ≤ fixedSubgroup α) (hSc : Subgroup.center S = ⊥)
    {V : Subgroup D} (hV : IsPGroup 2 V) (hαV : V.map α.toMonoidHom ≤ V)
    (hCV : V ⊓ fixedSubgroup α ≤ S) : Nat.card V ≤ 32 := by
  obtain ⟨x, rfl⟩ := hin
  have hcen := center_eq_bot_of_simple hnab
  have hx2 : x ^ 2 = 1 := by
    have h1 : MulAut.conj (x ^ 2) = 1 := by rw [map_pow, ← hα, pow_orderOf_eq_one]
    have h2 : x ^ 2 ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h3 := congrArg (fun β : MulAut D => β g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc g * x ^ 2 = x ^ 2 * g * (x ^ 2)⁻¹ * x ^ 2 := by rw [h3]
        _ = x ^ 2 * g := by group
    rw [hcen] at h2
    exact (mem_bot).1 h2
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hα
    exact absurd hα (by norm_num)
  have hxV : ∀ v ∈ V, x * v * x⁻¹ ∈ V := fun v hv =>
    hαV ⟨v, hv, by rfl⟩
  have hxN : x ∈ normalizer (V : Set D) := by
    rw [mem_normalizer_iff]
    intro v
    constructor
    · exact hxV v
    · intro hv
      have h1 := hxV _ hv
      have hxx : x * x = 1 := by rw [← sq, hx2]
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
      rw [hxinv] at h1
      have h2 : x * (x * v * x) * x = v := by
        calc x * (x * v * x) * x = (x * x) * v * (x * x) := by simp only [mul_assoc]
          _ = v := by rw [hxx, one_mul, mul_one]
      rwa [h2] at h1
  have hxS : x ∉ V := by
    intro hxV'
    have hxfix : x ∈ fixedSubgroup (MulAut.conj x) := by
      change MulAut.conj x x = x
      rw [MulAut.conj_apply, mul_inv_cancel_right]
    have hxSm : x ∈ S := hCV (mem_inf.2 ⟨hxV', hxfix⟩)
    have hxc : (⟨x, hxSm⟩ : S) ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      have h1 : MulAut.conj x (s : D) = s := hSα s.2
      rw [MulAut.conj_apply] at h1
      change (s : D) * x = x * s
      calc (s : D) * x = x * s * x⁻¹ * x := by rw [h1]
        _ = x * s := by group
    rw [hSc] at hxc
    exact hx1 (congrArg Subtype.val ((mem_bot).1 hxc))
  have hx2' : IsPGroup 2 (zpowers x) := by
    have hord : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hzN : zpowers x ≤ normalizer (V : Set D) := (zpowers_le).2 hxN
  have hQ := IsPGroup.to_sup_of_normal_left' hV hx2' hzN
  have hlt : V < V ⊔ zpowers x :=
    lt_of_le_of_ne le_sup_left fun h => hxS (h ▸ (le_sup_right (a := V)) (mem_zpowers x))
  have h64 := card_le_of_M12 hD hQ
  have hdvd : Nat.card V ∣ Nat.card (V ⊔ zpowers x : Subgroup D) :=
    Subgroup.card_dvd_of_le le_sup_left
  have hlt' := Subgroup.card_lt_of_lt hlt
  obtain ⟨c, hc⟩ := hdvd
  have hc2 : 2 ≤ c := by
    by_contra hlt2
    have h1 : Nat.card V * c ≤ Nat.card V * 1 := Nat.mul_le_mul_left _ (by omega)
    omega
  have h2 : Nat.card V * 2 ≤ Nat.card (V ⊔ zpowers x : Subgroup D) := by
    rw [hc]
    exact Nat.mul_le_mul_left _ hc2
  omega

end M12

theorem false_of_small_survivor
    {D : Type} [Group D] [Finite D] [IsSimpleGroup D] (hnab : ∃ a b : D, a * b ≠ b * a)
    {n : ℕ} (hn : 2 ≤ n) {α : MulAut D} (hα : orderOf α = 2) {S : Subgroup D}
    (hSα : S ≤ fixedSubgroup α) [IsSimpleGroup S] (hSnab : ∃ a b : S, a * b ≠ b * a)
    (hScard : Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1)) (hr : FixedRootRankOne α S)
    {V : Subgroup D} (hV : IsPGroup 2 V) (hαV : V.map α.toMonoidHom ≤ V)
    (hCV : V ⊓ fixedSubgroup α ≤ S)
    (hsmall : (n = 2 ∧ (NativeSporadic.IsSporadic D .J1 ∨ NativeSporadic.IsSporadic D .M12 ∨
      Nonempty (D ≃* alternatingGroup (Fin 7)) ∨ LieModel D .PSL 2 5 2 ∨
      LieModel D .PSL 3 5 1 ∨ LieModel D .PSU 3 5 1)) ∨ (n = 3 ∧ LieModel D .G2 0 3 1))
    (hbig : (2 ^ n) ^ 3 ≤ Nat.card V ∨ ((∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧
      (∀ x ∈ V, x * x = 1) ∧ Nat.card V = (2 ^ n) ^ 2)) : False := by
  have hclass : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {d p f : ℕ}, d ≠ 0 →
      LieModel D t d p f → CFSG.Assembly.LowTwoRank.StatedClassicalModel D t d p f := by
    intro t d p f hd h
    rcases h with ⟨-, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 hd
  rcases hsmall with ⟨rfl, h⟩ | ⟨rfl, h⟩
  ·
    have hbig' : 64 ≤ Nat.card V ∨ ((∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧
        (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 16) := by
      simpa using hbig
    have h16 : 16 ≤ Nat.card V := by
      rcases hbig' with h' | ⟨-, -, h'⟩ <;> omega
    rcases h with h | h | h | h | h | h
    · have := card_le_of_J1 h hV
      omega
    · rcases hbig' with h64 | ⟨hc, hs, h16'⟩
      · by_cases hin : α ∈ (MulAut.conj : D →* MulAut D).range
        · have := card_le_of_m12_inner h hnab hα hin hSα (center_eq_bot_of_simple hSnab) hV hαV
            hCV
          omega
        · exact false_of_m12_outer h hα hin hSα (commutator_self_of_simple hSnab)
            (by rw [hScard]; norm_num) hr
      · have h8 := CFSG.GH74.GLS.C3.Layer1.Bk.M12.m12_rank_le_three h V
          (fun a ha => ⟨hs a ha, fun b hb => hc a ha b hb⟩)
        omega
    · have := card_le_of_A7 h hV
      omega
    · have := card_le_of_psl_two_twentyfive (hclass (by norm_num) h) hV
      omega
    · obtain ⟨h32, h4⟩ := psl_three_five_bounds (hclass (by norm_num) h)
      rcases hbig' with h64 | ⟨hc, hs, h16'⟩
      · have := h32 V hV
        omega
      · have := h4 V hc hs
        omega
    · obtain ⟨h16b, h4⟩ := psu_three_five_bounds (hclass (by norm_num) h)
      rcases hbig' with h64 | ⟨hc, hs, h16'⟩
      · have := h16b V hV
        omega
      · have := h4 V hc hs
        omega
  ·
    have hcard := G2_three_card h
    have h64 : ∀ P : Subgroup D, IsPGroup 2 P → Nat.card P ≤ 64 := fun P hP => by
      have := card_le_of_not_dvd (k := 6) (by rw [hcard]; decide) hP
      simpa using this
    have hbig' : 512 ≤ Nat.card V ∨ ((∀ x ∈ V, ∀ y ∈ V, x * y = y * x) ∧
        (∀ x ∈ V, x * x = 1) ∧ Nat.card V = 64) := by
      simpa using hbig
    rcases hbig' with h512 | ⟨-, hs, h64'⟩
    · have := h64 V hV
      omega
    ·
      obtain ⟨x, hx⟩ := exists_orderOf_four_of_G2_three h
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hxP : IsPGroup 2 (zpowers x) :=
        IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx]; norm_num)
      obtain ⟨P, hP⟩ := hxP.exists_le_sylow
      obtain ⟨Q, hQ⟩ := hV.exists_le_sylow
      have hQV : V = (Q : Subgroup D) :=
        Subgroup.eq_of_le_of_card_ge hQ (by rw [h64']; exact h64 _ Q.isPGroup')
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D Q P
      have h1 : x ∈ (P : Subgroup D) := hP (mem_zpowers x)
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← hQV]
        at h1
      have h1' : g⁻¹ * x * g ∈ V := by
        simpa [MulAut.smul_def, MulAut.conj_apply] using h1
      have h2 := hs _ h1'
      have h3 : x ^ 2 = 1 := by
        have : g * (g⁻¹ * x * g * (g⁻¹ * x * g)) * g⁻¹ = 1 := by rw [h2]; group
        rw [sq]
        simpa [mul_assoc] using this
      have := orderOf_dvd_of_pow_eq_one h3
      rw [hx] at this
      exact absurd this (by norm_num)

end RankOneSelector

end CFSG.LocalAnalysis.SymplecticFourStandard
