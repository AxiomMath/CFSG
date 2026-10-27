module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

/-!
# Higman Lemma 3
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped IsMulCommutative commutatorElement

universe u

private theorem lemma3_squares_C_mem_A
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P)
    {A C : Subgroup P}
    (hfrattini : (frattini C).map C.subtype = (frattini A).map A.subtype)
    (u : C) : (u : P) ^ 2 ∈ A := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Finite C := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 C) :=
    ⟨(isPGroup_of_isSuzukiTwoGroup hP).to_subgroup C⟩
  have huPhi : u ^ 2 ∈ frattini C :=
    pth_power_mem_frattini_of_isPGroup (R := C) (p := 2) u
  have huMap : (u : P) ^ 2 ∈ (frattini C).map C.subtype :=
    Subgroup.mem_map.mpr ⟨u ^ 2, huPhi, by simp⟩
  rw [hfrattini] at huMap
  rcases Subgroup.mem_map.mp huMap with ⟨a, _, ha⟩
  rw [← ha]
  exact a.property

private theorem lemma3_commutator_mem_frattiniA
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P)
    {A C : Subgroup P} (hAC : A ≤ C)
    (hfrattini : (frattini C).map C.subtype = (frattini A).map A.subtype)
    (u : C) (a : A) :
    ⁅(u : P), (a : P)⁆ ∈ (frattini A).map A.subtype := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Finite C := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 C) :=
    ⟨(isPGroup_of_isSuzukiTwoGroup hP).to_subgroup C⟩
  let aC : C := ⟨a, hAC a.property⟩
  have hcomm : ⁅u, aC⁆ ∈ _root_.commutator C :=
    Subgroup.commutator_mem_commutator
      (H₁ := (⊤ : Subgroup C)) (H₂ := (⊤ : Subgroup C)) trivial trivial
  have hPhi : ⁅u, aC⁆ ∈ frattini C :=
    commutator_le_frattini_of_isPGroup (R := C) (p := 2) hcomm
  rw [← hfrattini]
  exact Subgroup.mem_map.mpr ⟨⁅u, aC⁆, hPhi, rfl⟩
private theorem lemma3_frattini_eq_square_range_map
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P)
    {A : Subgroup P} (hA_abelian : IsMulCommutative A) :
    (frattini A).map A.subtype =
      (powMonoidHom 2 : A →* A).range.map A.subtype := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Finite A := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 A) :=
    ⟨(isPGroup_of_isSuzukiTwoGroup hP).to_subgroup A⟩
  letI : IsMulCommutative A := hA_abelian
  have hPhi : frattini A = (powMonoidHom 2 : A →* A).range := by
    classical
    have hcomm : _root_.commutator A = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top]
      apply eq_top_iff.mpr
      intro x _hx
      exact Subgroup.mem_center_iff.mpr
        (fun y => ((IsMulCommutative.is_comm (M := A)).comm x y).symm)
    rw [frattini_eq_closure_commutator_union_powers (R := A) (p := 2)]
    refine le_antisymm ?_ ?_
    · refine (Subgroup.closure_le (K := (powMonoidHom 2 : A →* A).range)).2 ?_
      intro x hx
      rcases hx with hxcomm | hxpow
      · have hxbot : x ∈ (⊥ : Subgroup A) := by
          simpa [hcomm] using hxcomm
        have hx1 : x = 1 := by
          simpa using hxbot
        subst x
        exact ⟨1, by simp⟩
      · simpa [powMonoidHom] using hxpow
    · intro x hx
      exact Subgroup.subset_closure (Or.inr (by simpa [powMonoidHom] using hx))
  exact congrArg (fun K : Subgroup A => K.map A.subtype) hPhi

private def lemma3_conjDefect
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A) (u : P) : A →* A := by
  letI : IsMulCommutative A := hA_abelian
  letI : A.Normal := hA_normal
  exact (MulAut.conjNormal (H := A) u).toMonoidHom * (MonoidHom.id A)⁻¹

private theorem lemma3_conjDefect_val
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A) (u : P) (a : A) :
    ((lemma3_conjDefect hA_normal hA_abelian u a : A) : P) = ⁅u, (a : P)⁆ := by
  letI : IsMulCommutative A := hA_abelian
  simp [lemma3_conjDefect, commutatorElement_def, MulAut.conjNormal_apply, mul_assoc]

private theorem lemma3_conj_defect_lift_square
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A C : Subgroup P} (hA_normal : A.Normal)
    (hA_abelian : IsMulCommutative A) (hA_X : IsXInvariantSubgroup X A)
    (hAC : A ≤ C)
    (hfrattini : (frattini C).map C.subtype = (frattini A).map A.subtype)
    (u : C) :
    ∃ eta : A →* A,
      ∀ a, lemma3_conjDefect hA_normal hA_abelian (u : P) a = (eta a) ^ 2 := by
  letI : IsMulCommutative A := hA_abelian
  obtain ⟨e, r, ⟨hA⟩, _⟩ :=
    lemma1_abelian_invariant_homocyclic hP hXtrans hA_abelian hA_X
  apply lemma2_endomorphism_power_root_of_homocyclic hA 2
  intro a
  have hcomm := lemma3_commutator_mem_frattiniA hP hAC hfrattini u a
  rw [lemma3_frattini_eq_square_range_map hP hA_abelian] at hcomm
  rcases Subgroup.mem_map.mp hcomm with ⟨y, hy, hyval⟩
  rcases MonoidHom.mem_range.mp hy with ⟨b, rfl⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  exact hyval.trans (lemma3_conjDefect_val hA_normal hA_abelian (u : P) a).symm
private theorem lemma3_four_torsion_is_square_of_homocyclic
    {A : Type*} [Group A] {e r : ℕ} (he : 3 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    {x : A} (hx : x ^ 4 = 1) :
    ∃ y : A, y ^ 2 = x := by
  obtain ⟨z, hz⟩ :=
    lemma1_exists_power_root_of_homocyclic (e := e) (f := 2) (by omega) hA
      (by simpa using hx)
  refine ⟨z ^ (2 ^ (e - 3)), ?_⟩
  calc
    (z ^ (2 ^ (e - 3))) ^ 2 = z ^ (2 ^ (e - 3) * 2) :=
      (pow_mul z (2 ^ (e - 3)) 2).symm
    _ = z ^ (2 ^ (e - 2)) := by
      rw [show e - 2 = (e - 3) + 1 by omega, pow_succ]
    _ = x := hz

private theorem lemma3_eta_four_torsion
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A)
    (u : P) (hu_sq : u ^ 2 ∈ A) (eta : A →* A)
    (hdef : ∀ a, lemma3_conjDefect hA_normal hA_abelian u a = (eta a) ^ 2) :
    ∀ a, (eta a * eta (eta a)) ^ 4 = 1 := by
  letI : IsMulCommutative A := hA_abelian
  letI : A.Normal := hA_normal
  let c : MulAut A := MulAut.conjNormal (H := A) u
  have hca (a : A) : c a = a * (eta a) ^ 2 := by
    have hd : c a * a⁻¹ = (eta a) ^ 2 := by
      simpa [c, lemma3_conjDefect] using hdef a
    calc
      c a = (c a * a⁻¹) * a := by simp
      _ = (eta a) ^ 2 * a := by rw [hd]
      _ = a * (eta a) ^ 2 := mul_comm _ _
  have hcc (a : A) : c (c a) = a := by
    apply Subtype.ext
    change u * (u * (a : P) * u⁻¹) * u⁻¹ = (a : P)
    let u2A : A := ⟨u ^ 2, hu_sq⟩
    have hu2_comm := congrArg A.subtype (mul_comm u2A a)
    change u ^ 2 * (a : P) = (a : P) * u ^ 2 at hu2_comm
    calc
      u * (u * (a : P) * u⁻¹) * u⁻¹ = u ^ 2 * (a : P) * (u ^ 2)⁻¹ := by
        rw [pow_two]
        group
      _ = (a : P) * u ^ 2 * (u ^ 2)⁻¹ := by rw [hu2_comm]
      _ = (a : P) := by group
  have hcalc (a : A) :
      c (c a) = a * (eta a * eta (eta a)) ^ 4 := by
    calc
      c (c a) = c (a * (eta a) ^ 2) := by rw [hca a]
      _ = c a * (c (eta a)) ^ 2 := by rw [map_mul, map_pow]
      _ = (a * (eta a) ^ 2) *
          (eta a * (eta (eta a)) ^ 2) ^ 2 := by
        rw [hca a, hca (eta a)]
      _ = a * (eta a * eta (eta a)) ^ 4 := by
        rw [show (eta a * eta (eta a)) ^ 4 =
          ((eta a * eta (eta a)) ^ 2) ^ 2 by
            exact pow_mul (eta a * eta (eta a)) 2 2]
        simp only [pow_two]
        ac_rfl
  intro a
  have hax : a * (eta a * eta (eta a)) ^ 4 = a :=
    (hcalc a).symm.trans (hcc a)
  have hcancel := congrArg (fun z : A => a⁻¹ * z) hax
  simpa [mul_assoc] using hcancel

public abbrev lemma3_squareRange (A : Type*) [CommGroup A] : Subgroup A :=
  (powMonoidHom 2 : A →* A).range

private theorem lemma3_frattini_eq_squareRange
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P)
    {A : Subgroup P} (hA_abelian : IsMulCommutative A) :
    letI : IsMulCommutative A := hA_abelian
    frattini A = lemma3_squareRange A := by
  letI : IsMulCommutative A := hA_abelian
  apply Subgroup.map_injective A.subtype_injective
  exact lemma3_frattini_eq_square_range_map hP hA_abelian

private theorem lemma3_squareQuotient_nontrivial
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P)
    {A : Subgroup P} (hA_abelian : IsMulCommutative A) (hA_ne : A ≠ ⊥) :
    letI : IsMulCommutative A := hA_abelian
    ∃ q : A ⧸ lemma3_squareRange A, q ≠ 1 := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Finite A := inferInstance
  letI : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA_ne
  letI : IsMulCommutative A := hA_abelian
  have hsq_ne_top : lemma3_squareRange A ≠ ⊤ := by
    intro hsq
    have hphi : frattini A = ⊤ := by
      rw [lemma3_frattini_eq_squareRange hP hA_abelian, hsq]
    have hbot : (⊥ : Subgroup A) = ⊤ := by
      apply frattini_nongenerating
      simp [hphi]
    exact (bot_ne_top : (⊥ : Subgroup A) ≠ ⊤) hbot
  obtain ⟨a, -, ha⟩ :=
    SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hsq_ne_top)
  refine ⟨(a : A ⧸ lemma3_squareRange A), ?_⟩
  intro hq
  rw [QuotientGroup.eq_one_iff] at hq
  exact ha hq
private theorem lemma3_powerClosure_eq_range_map
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_abelian : IsMulCommutative A) (n : ℕ) :
    Subgroup.closure {x : P | ∃ a : A, (a : P) ^ n = x} =
      (powMonoidHom n : A →* A).range.map A.subtype := by
  letI : IsMulCommutative A := hA_abelian
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨a, rfl⟩
    exact Subgroup.mem_map.mpr
      ⟨a ^ n, MonoidHom.mem_range.mpr ⟨a, rfl⟩, rfl⟩
  · rintro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
    exact Subgroup.subset_closure ⟨a, rfl⟩
/-- The subgroup of squares is invariant under a group action by automorphisms. -/
public theorem lemma3_squareRange_isInvariant
    {X A : Type*} [Group X] [CommGroup A] [MulDistribMulAction X A] :
    IsInvariant X A (lemma3_squareRange A) := by
  constructor
  intro x a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨x • b, by simp [powMonoidHom]⟩
  · rintro ⟨b, hb⟩
    refine ⟨x⁻¹ • b, ?_⟩
    have h := congrArg (fun z : A => x⁻¹ • z) hb
    simpa [powMonoidHom, smul_smul] using h
private theorem lemma3_eta_mod_square_idempotent
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A)
    {e r : ℕ} (he : 3 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (u : P) (hu_sq : u ^ 2 ∈ A) (eta : A →* A)
    (hdef : ∀ a, lemma3_conjDefect hA_normal hA_abelian u a = (eta a) ^ 2) :
    ∀ a, eta (eta a) / eta a ∈ lemma3_squareRange A := by
  letI : IsMulCommutative A := hA_abelian
  intro a
  have hx := lemma3_eta_four_torsion hA_normal hA_abelian u hu_sq eta hdef a
  obtain ⟨y, hy⟩ := lemma3_four_torsion_is_square_of_homocyclic he hA hx
  refine MonoidHom.mem_range.mpr ⟨y * (eta a)⁻¹, ?_⟩
  rw [powMonoidHom_apply, div_eq_mul_inv]
  calc
    (y * (eta a)⁻¹) ^ 2 = y ^ 2 * ((eta a)⁻¹) ^ 2 := mul_pow _ _ _
    _ = (eta a * eta (eta a)) * ((eta a)⁻¹) ^ 2 := by rw [hy]
    _ = eta (eta a) * (eta a * (eta a)⁻¹) * (eta a)⁻¹ := by
      rw [pow_two]
      ac_rfl
    _ = eta (eta a) * (eta a)⁻¹ := by simp

private def lemma3_etaBar
    {A : Type*} [CommGroup A] (eta : A →* A) :
    A ⧸ lemma3_squareRange A →* A ⧸ lemma3_squareRange A :=
  QuotientGroup.map (lemma3_squareRange A) (lemma3_squareRange A) eta (by
    rintro _ ⟨a, rfl⟩
    exact ⟨eta a, by simp [powMonoidHom]⟩)

private theorem lemma3_etaBar_idempotent
    {A : Type*} [CommGroup A] (eta : A →* A)
    (hidem : ∀ a, eta (eta a) / eta a ∈ lemma3_squareRange A) :
    (lemma3_etaBar eta).comp (lemma3_etaBar eta) = lemma3_etaBar eta := by
  apply MonoidHom.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  simp only [MonoidHom.comp_apply, lemma3_etaBar]
  apply (QuotientGroup.eq_iff_div_mem (N := lemma3_squareRange A)).2
  simpa using hidem a
private theorem lemma3_conj_defect_mul_formula
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A)
    (u v : P) (a : A) :
    lemma3_conjDefect hA_normal hA_abelian (u * v) a =
      lemma3_conjDefect hA_normal hA_abelian u a *
        lemma3_conjDefect hA_normal hA_abelian v a *
          lemma3_conjDefect hA_normal hA_abelian u
            (lemma3_conjDefect hA_normal hA_abelian v a) := by
  letI : IsMulCommutative A := hA_abelian
  letI : A.Normal := hA_normal
  let d (w : P) : A →* A := lemma3_conjDefect hA_normal hA_abelian w
  let c (w : P) : MulAut A := MulAut.conjNormal (H := A) w
  change d (u * v) a = d u a * d v a * d u (d v a)
  have hd (w : P) (x : A) : d w x = c w x * x⁻¹ := by
    simp [d, c, lemma3_conjDefect]
  have hca (w : P) (x : A) : c w x = x * d w x := by
    calc
      c w x = (c w x * x⁻¹) * x := by simp
      _ = d w x * x := by rw [← hd w x]
      _ = x * d w x := mul_comm _ _
  have hcmul (x : A) : c (u * v) x = c u (c v x) := by
    apply Subtype.ext
    change (u * v) * (x : P) * (u * v)⁻¹ =
      u * (v * (x : P) * v⁻¹) * u⁻¹
    group
  calc
    d (u * v) a = c (u * v) a * a⁻¹ := hd (u * v) a
    _ = c u (c v a) * a⁻¹ := by rw [hcmul]
    _ = c u (a * d v a) * a⁻¹ := by rw [hca v a]
    _ = (c u a * c u (d v a)) * a⁻¹ := by rw [map_mul]
    _ = ((a * d u a) * (d v a * d u (d v a))) * a⁻¹ := by
      rw [hca u a, hca u (d v a)]
    _ = (a * a⁻¹) * (d u a * d v a * d u (d v a)) := by
      ac_rfl
    _ = d u a * d v a * d u (d v a) := by simp
private theorem lemma3_square_roots_eq_mod_square
    {A : Type*} [CommGroup A] {e r : ℕ} (he : 3 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    {x y : A} (hxy : x ^ 2 = y ^ 2) :
    x / y ∈ lemma3_squareRange A := by
  have hq2 : (x / y) ^ 2 = 1 := by
    rw [div_pow, hxy]
    simp
  have hq4 : (x / y) ^ 4 = 1 := by
    rw [show (x / y) ^ 4 = ((x / y) ^ 2) ^ 2 by
      exact pow_mul (x / y) 2 2, hq2, one_pow]
  obtain ⟨z, hz⟩ := lemma3_four_torsion_is_square_of_homocyclic he hA hq4
  exact MonoidHom.mem_range.mpr ⟨z, by simpa [powMonoidHom] using hz⟩
private theorem lemma3_etaBar_mul
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A)
    {e r : ℕ} (he : 3 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (u v : P) (etaU etaV etaUV : A →* A)
    (hU : ∀ a, lemma3_conjDefect hA_normal hA_abelian u a = (etaU a) ^ 2)
    (hV : ∀ a, lemma3_conjDefect hA_normal hA_abelian v a = (etaV a) ^ 2)
    (hUV : ∀ a,
      lemma3_conjDefect hA_normal hA_abelian (u * v) a = (etaUV a) ^ 2) :
    lemma3_etaBar etaUV = lemma3_etaBar etaU * lemma3_etaBar etaV := by
  letI : IsMulCommutative A := hA_abelian
  apply MonoidHom.ext
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  simp only [lemma3_etaBar]
  apply (QuotientGroup.eq_iff_div_mem (N := lemma3_squareRange A)).2
  let dU := lemma3_conjDefect hA_normal hA_abelian u
  let dV := lemma3_conjDefect hA_normal hA_abelian v
  let cand : A := etaU a * etaV a * (etaU (etaV a)) ^ 2
  have hsq : (etaUV a) ^ 2 = cand ^ 2 := by
    calc
      (etaUV a) ^ 2 =
          lemma3_conjDefect hA_normal hA_abelian (u * v) a := (hUV a).symm
      _ = dU a * dV a * dU (dV a) := by
        exact lemma3_conj_defect_mul_formula hA_normal hA_abelian u v a
      _ = cand ^ 2 := by
        simp only [dU, dV, hU, hV, map_pow, cand, mul_pow]
  have hroot : etaUV a / cand ∈ lemma3_squareRange A :=
    lemma3_square_roots_eq_mod_square he hA hsq
  have hcand : cand / (etaU a * etaV a) ∈ lemma3_squareRange A := by
    refine MonoidHom.mem_range.mpr ⟨etaU (etaV a), ?_⟩
    rw [powMonoidHom_apply, div_eq_mul_inv]
    dsimp [cand]
    calc
      (etaU (etaV a)) ^ 2 =
          ((etaU a * etaV a) * (etaU a * etaV a)⁻¹) *
            (etaU (etaV a)) ^ 2 := by simp
      _ = (etaU a * etaV a * (etaU (etaV a)) ^ 2) *
          (etaU a * etaV a)⁻¹ := by ac_rfl
  rw [show etaUV a / (etaU a * etaV a) =
    (etaUV a / cand) * (cand / (etaU a * etaV a)) by
      calc
        etaUV a / (etaU a * etaV a) =
            etaUV a * (etaU a * etaV a)⁻¹ := by rw [div_eq_mul_inv]
        _ = etaUV a * (cand⁻¹ * cand) * (etaU a * etaV a)⁻¹ := by simp
        _ = (etaUV a * cand⁻¹) * (cand * (etaU a * etaV a)⁻¹) := by
          ac_rfl
        _ = (etaUV a / cand) * (cand / (etaU a * etaV a)) := by
          simp only [div_eq_mul_inv]]
  exact (lemma3_squareRange A).mul_mem hroot hcand
private theorem lemma3_squareQuotient_pow_two
    {A : Type*} [CommGroup A] (q : A ⧸ lemma3_squareRange A) :
    q ^ 2 = 1 := by
  refine Quotient.inductionOn' q ?_
  intro a
  change ((a ^ 2 : A) : A ⧸ lemma3_squareRange A) = 1
  rw [QuotientGroup.eq_one_iff]
  exact MonoidHom.mem_range.mpr ⟨a, by simp [powMonoidHom]⟩

private theorem lemma3_commute_of_mul_idempotent
    {Q : Type*} [CommGroup Q] (hQ2 : ∀ q : Q, q ^ 2 = 1)
    (f g : Q →* Q)
    (hf : f.comp f = f) (hg : g.comp g = g)
    (hfg : (f * g).comp (f * g) = f * g) :
    f.comp g = g.comp f := by
  apply MonoidHom.ext
  intro q
  have hfq : f (f q) = f q := DFunLike.congr_fun hf q
  have hgq : g (g q) = g q := DFunLike.congr_fun hg q
  have hfgq := DFunLike.congr_fun hfg q
  change f (f q * g q) * g (f q * g q) = f q * g q at hfgq
  rw [map_mul, map_mul, hfq, hgq] at hfgq
  have hbase :
      (f q * g q) * (f (g q) * g (f q)) = f q * g q := by
    calc
      (f q * g q) * (f (g q) * g (f q)) =
          f q * f (g q) * (g (f q) * g q) := by ac_rfl
      _ = f q * g q := hfgq
  have hcross : f (g q) * g (f q) = 1 := by
    apply mul_left_cancel (a := f q * g q)
    simpa [mul_assoc] using hbase
  have hself : f (g q) * f (g q) = 1 := by
    simpa [pow_two] using hQ2 (f (g q))
  have hsame : f (g q) * g (f q) = f (g q) * f (g q) :=
    hcross.trans hself.symm
  exact (mul_left_cancel hsame).symm

private theorem lemma3_eta_mod_square_commute
    {A : Type*} [CommGroup A] (etaU etaV etaUV : A →* A)
    (hUidem : (lemma3_etaBar etaU).comp (lemma3_etaBar etaU) = lemma3_etaBar etaU)
    (hVidem : (lemma3_etaBar etaV).comp (lemma3_etaBar etaV) = lemma3_etaBar etaV)
    (hUVidem : (lemma3_etaBar etaUV).comp (lemma3_etaBar etaUV) = lemma3_etaBar etaUV)
    (hmul : lemma3_etaBar etaUV = lemma3_etaBar etaU * lemma3_etaBar etaV) :
    (lemma3_etaBar etaU).comp (lemma3_etaBar etaV) =
      (lemma3_etaBar etaV).comp (lemma3_etaBar etaU) := by
  apply lemma3_commute_of_mul_idempotent lemma3_squareQuotient_pow_two
  · exact hUidem
  · exact hVidem
  · rw [← hmul]
    exact hUVidem
private theorem lemma3_exists_common_eigenvector
    {ι Q : Type*} [Fintype ι] [Monoid Q]
    (hne : ∃ q : Q, q ≠ 1) (f : ι → Q →* Q)
    (hidem : ∀ i, (f i).comp (f i) = f i)
    (hcomm : ∀ i j, (f i).comp (f j) = (f j).comp (f i)) :
    ∃ q : Q, q ≠ 1 ∧ ∀ i, f i q = 1 ∨ f i q = q := by
  classical
  have aux : ∀ s : Finset ι,
      ∃ q : Q, q ≠ 1 ∧ ∀ i ∈ s, f i q = 1 ∨ f i q = q := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        obtain ⟨q, hq⟩ := hne
        exact ⟨q, hq, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨q, hq, hqEig⟩ := ih
        by_cases hiq : f i q = 1
        · refine ⟨q, hq, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Or.inl hiq
          · exact hqEig j hj
        · refine ⟨f i q, hiq, ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact Or.inr (DFunLike.congr_fun (hidem j) q)
          · rcases hqEig j hj with hjq | hjq
            · left
              rw [← MonoidHom.comp_apply, hcomm j i, MonoidHom.comp_apply, hjq,
                map_one]
            · right
              rw [← MonoidHom.comp_apply, hcomm j i, MonoidHom.comp_apply, hjq]
  obtain ⟨q, hq, hqEig⟩ := aux Finset.univ
  exact ⟨q, hq, fun i => hqEig i (Finset.mem_univ i)⟩
private theorem lemma3_conjDefect_smul
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    {A : Subgroup P} (hA_normal : A.Normal)
    (hA_abelian : IsMulCommutative A) (hA_X : IsXInvariantSubgroup X A)
    (x : X) (u : P) (a : A) :
    letI : IsInvariant X P A := ⟨hA_X⟩
    lemma3_conjDefect hA_normal hA_abelian (x • u) (x • a) =
      x • lemma3_conjDefect hA_normal hA_abelian u a := by
  letI : IsInvariant X P A := ⟨hA_X⟩
  apply Subtype.ext
  calc
    ((lemma3_conjDefect hA_normal hA_abelian (x • u) (x • a) : A) : P) =
        ⁅x • u, x • (a : P)⁆ :=
      lemma3_conjDefect_val hA_normal hA_abelian (x • u) (x • a)
    _ = x • ⁅u, (a : P)⁆ := by
      simp [commutatorElement_def, smul_mul']
    _ = x • ((lemma3_conjDefect hA_normal hA_abelian u a : A) : P) := by
      rw [lemma3_conjDefect_val]
    _ = ((x • lemma3_conjDefect hA_normal hA_abelian u a : A) : P) := rfl
private theorem lemma3_etaBar_smul
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    {A : Subgroup P} (hA_normal : A.Normal)
    (hA_abelian : IsMulCommutative A) (hA_X : IsXInvariantSubgroup X A)
    {e r : ℕ} (he : 3 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (x : X) (u : P) (etaU etaXU : A →* A)
    (hU : ∀ a, lemma3_conjDefect hA_normal hA_abelian u a = (etaU a) ^ 2)
    (hXU : ∀ a,
      lemma3_conjDefect hA_normal hA_abelian (x • u) a = (etaXU a) ^ 2) :
    letI : IsMulCommutative A := hA_abelian
    letI : IsInvariant X P A := ⟨hA_X⟩
    letI : IsInvariant X A (lemma3_squareRange A) :=
      lemma3_squareRange_isInvariant
    letI : MulAction.QuotientAction X (lemma3_squareRange A) :=
      quotientAction_of_isInvariant (A := X) (G := A) _ (by infer_instance)
    letI : MulDistribMulAction X (A ⧸ lemma3_squareRange A) :=
      quotientMulDistribMulAction (A := X) (G := A) _ (by infer_instance)
    ∀ q : A ⧸ lemma3_squareRange A,
      lemma3_etaBar etaXU (x • q) = x • lemma3_etaBar etaU q := by
  letI : IsMulCommutative A := hA_abelian
  letI : IsInvariant X P A := ⟨hA_X⟩
  letI : IsInvariant X A (lemma3_squareRange A) :=
    lemma3_squareRange_isInvariant
  letI : MulAction.QuotientAction X (lemma3_squareRange A) :=
    quotientAction_of_isInvariant (A := X) (G := A) _ (by infer_instance)
  letI : MulDistribMulAction X (A ⧸ lemma3_squareRange A) :=
    quotientMulDistribMulAction (A := X) (G := A) _ (by infer_instance)
  intro q
  refine Quotient.inductionOn' q ?_
  intro a
  simp only [lemma3_etaBar, MulAction.Quotient.smul_coe]
  apply (QuotientGroup.eq_iff_div_mem (N := lemma3_squareRange A)).2
  apply lemma3_square_roots_eq_mod_square he hA
  calc
    (etaXU (x • a)) ^ 2 =
        lemma3_conjDefect hA_normal hA_abelian (x • u) (x • a) :=
      (hXU (x • a)).symm
    _ = x • lemma3_conjDefect hA_normal hA_abelian u a :=
      lemma3_conjDefect_smul hA_normal hA_abelian hA_X x u a
    _ = x • (etaU a) ^ 2 := by rw [hU]
    _ = (x • etaU a) ^ 2 := by rw [smul_pow']
private theorem lemma3_squareQuotient_mk_transitive
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (hA_abelian : IsMulCommutative A)
    (hA_X : IsXInvariantSubgroup X A)
    {e r : ℕ} (he : 1 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    letI : IsInvariant X P A := ⟨hA_X⟩
    ∀ a b : A,
      (a : A ⧸ lemma3_squareRange A) ≠ 1 →
      (b : A ⧸ lemma3_squareRange A) ≠ 1 →
      ∃ x : X,
        (b : A ⧸ lemma3_squareRange A) =
          ((x • a : A) : A ⧸ lemma3_squareRange A) := by
  letI : IsInvariant X P A := ⟨hA_X⟩
  intro a b ha hb
  have hpow_ne (c : A)
      (hc : (c : A ⧸ lemma3_squareRange A) ≠ 1) :
      c ^ (2 ^ (e - 1)) ≠ 1 := by
    intro hkill
    obtain ⟨y, hy⟩ :=
      lemma1_exists_power_root_of_homocyclic
        (e := e) (f := e - 1) (Nat.sub_le e 1) hA hkill
    apply hc
    rw [QuotientGroup.eq_one_iff]
    refine MonoidHom.mem_range.mpr ⟨y, ?_⟩
    simpa [powMonoidHom, show e - (e - 1) = 1 by omega] using hy
  have hexp : 2 ^ (e - 1) * 2 = 2 ^ e := by
    rw [← pow_succ]
    congr 1
    omega
  have hpow_sq (c : A) : (c ^ (2 ^ (e - 1))) ^ 2 = 1 := by
    calc
      (c ^ (2 ^ (e - 1))) ^ 2 = c ^ (2 ^ (e - 1) * 2) := by
        rw [pow_mul]
      _ = c ^ (2 ^ e) := by rw [hexp]
      _ = 1 := lemma1_pow_eq_one_of_homocyclic hA c
  have haInv : (a : P) ^ (2 ^ (e - 1)) ∈ involutions P := by
    refine ⟨?_, ?_⟩
    · intro ha1
      apply hpow_ne a ha
      apply Subtype.ext
      simpa using ha1
    · simpa using congrArg A.subtype (hpow_sq a)
  have hbInv : (b : P) ^ (2 ^ (e - 1)) ∈ involutions P := by
    refine ⟨?_, ?_⟩
    · intro hb1
      apply hpow_ne b hb
      apply Subtype.ext
      simpa using hb1
    · simpa using congrArg A.subtype (hpow_sq b)
  obtain ⟨x, hx⟩ := hXtrans _ haInv _ hbInv
  let xa : A := x • a
  have hpows : b ^ (2 ^ (e - 1)) = xa ^ (2 ^ (e - 1)) := by
    apply Subtype.ext
    change (b : P) ^ (2 ^ (e - 1)) = (x • (a : P)) ^ (2 ^ (e - 1))
    simpa using hx
  have hkill : (b / xa) ^ (2 ^ (e - 1)) = 1 := by
    calc
      (b / xa) ^ (2 ^ (e - 1)) =
          b ^ (2 ^ (e - 1)) / xa ^ (2 ^ (e - 1)) := div_pow b xa _
      _ = 1 := by simp [hpows]
  obtain ⟨y, hy⟩ :=
    lemma1_exists_power_root_of_homocyclic
      (e := e) (f := e - 1) (Nat.sub_le e 1) hA hkill
  refine ⟨x, (QuotientGroup.eq_iff_div_mem (N := lemma3_squareRange A)).2 ?_⟩
  refine MonoidHom.mem_range.mpr ⟨y, ?_⟩
  simpa [xa, powMonoidHom, show e - (e - 1) = 1 by omega] using hy
private theorem lemma3_scalar_of_common_eigenvector
    {X Q ι : Type*} [Group X] [Group Q]
    [MulDistribMulAction X Q] [MulAction X ι]
    (f : ι → Q →* Q)
    (htrans : ∀ q : Q, q ≠ 1 → ∀ r : Q, r ≠ 1 → ∃ x : X, r = x • q)
    (hequiv : ∀ (x : X) (i : ι) (q : Q), f (x • i) (x • q) = x • f i q)
    {q0 : Q} (hq0 : q0 ≠ 1)
    (hcommon : ∀ i, f i q0 = 1 ∨ f i q0 = q0) :
    ∀ i, f i = 1 ∨ f i = MonoidHom.id Q := by
  have hpoint (i : ι) (q : Q) : f i q = 1 ∨ f i q = q := by
    by_cases hq : q = 1
    · subst q
      exact Or.inl (map_one (f i))
    · obtain ⟨x, hx⟩ := htrans q0 hq0 q hq
      rcases hcommon (x⁻¹ • i) with hzero | hfix
      · left
        rw [hx]
        have he := hequiv x (x⁻¹ • i) q0
        simpa [smul_smul, hzero] using he
      · right
        rw [hx]
        have he := hequiv x (x⁻¹ • i) q0
        simpa [smul_smul, hfix] using he
  intro i
  by_cases hker : ∃ q : Q, q ≠ 1 ∧ f i q = 1
  · left
    obtain ⟨q, hq, hfq⟩ := hker
    apply MonoidHom.ext
    intro r
    simp only [MonoidHom.one_apply]
    rcases hpoint i r with hrzero | hrfix
    · exact hrzero
    · have hprod : f i (q * r) = r := by
        rw [map_mul, hfq, hrfix, one_mul]
      rcases hpoint i (q * r) with hprodzero | hprodfix
      · exact hrfix.trans (hprod.symm.trans hprodzero)
      · have hqone : q = 1 := by
          apply mul_right_cancel (b := r)
          simpa using hprodfix.symm.trans hprod
        exact (hq hqone).elim
  · right
    apply MonoidHom.ext
    intro r
    simp only [MonoidHom.id_apply]
    rcases hpoint i r with hrzero | hrfix
    · by_cases hr : r = 1
      · exact hrzero.trans hr.symm
      · exact (hker ⟨r, hr, hrzero⟩).elim
    · exact hrfix
private theorem lemma3_squares_C_mem_square_closure
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P)
    {A C : Subgroup P}
    (hA_abelian : IsMulCommutative A)
    (hfrattini : (frattini C).map C.subtype = (frattini A).map A.subtype)
    (u : C) :
    (u : P) ^ 2 ∈
      Subgroup.closure {x : P | ∃ a : A, (a : P) ^ 2 = x} := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Finite C := inferInstance
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 C) :=
    ⟨(isPGroup_of_isSuzukiTwoGroup hP).to_subgroup C⟩
  have huPhi : u ^ 2 ∈ frattini C :=
    pth_power_mem_frattini_of_isPGroup (R := C) (p := 2) u
  have huMap : (u : P) ^ 2 ∈ (frattini C).map C.subtype :=
    Subgroup.mem_map.mpr ⟨u ^ 2, huPhi, by simp⟩
  rw [hfrattini, lemma3_frattini_eq_square_range_map hP hA_abelian] at huMap
  rcases Subgroup.mem_map.mp huMap with ⟨y, hy, hyval⟩
  rcases MonoidHom.mem_range.mp hy with ⟨a, rfl⟩
  exact Subgroup.subset_closure ⟨a, by simpa using hyval⟩

private theorem lemma3_etaBar_eq_one_iff_mem
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A C : Subgroup P} (hA_normal : A.Normal)
    (hA_abelian : IsMulCommutative A) (hA_X : IsXInvariantSubgroup X A)
    (hfrattini : (frattini C).map C.subtype = (frattini A).map A.subtype)
    (hA_ne : A ≠ ⊥) {e r : ℕ} (he : 3 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (u : C) (eta : A →* A)
    (hdef : ∀ a,
      lemma3_conjDefect hA_normal hA_abelian (u : P) a = (eta a) ^ 2) :
    letI : IsMulCommutative A := hA_abelian
    lemma3_etaBar eta = 1 ↔ (u : P) ∈ A := by
  letI : IsMulCommutative A := hA_abelian
  constructor
  · intro heta
    by_contra hu
    apply (lemma2_no_external_square_commutator_exception
      hP hXtrans hA_normal hA_abelian hA_X hA_ne (u : P) hu)
    refine ⟨lemma3_squares_C_mem_square_closure
      hP hA_abelian hfrattini u, ?_⟩
    rw [Subgroup.closure_le]
    rintro _ ⟨a, rfl⟩
    have heta_q : lemma3_etaBar eta
        (a : A ⧸ lemma3_squareRange A) = 1 := by
      rw [heta]
      rfl
    simp only [lemma3_etaBar] at heta_q
    change ((eta a : A) : A ⧸ lemma3_squareRange A) = 1 at heta_q
    rw [QuotientGroup.eq_one_iff] at heta_q
    rcases MonoidHom.mem_range.mp heta_q with ⟨b, hb⟩
    change b ^ 2 = eta a at hb
    refine Subgroup.subset_closure ⟨b, ?_⟩
    have hb4 : b ^ 4 = (eta a) ^ 2 := by
      rw [show b ^ 4 = (b ^ 2) ^ 2 by exact pow_mul b 2 2, hb]
    calc
      (b : P) ^ 4 = ((b ^ 4 : A) : P) := by simp
      _ = (((eta a) ^ 2 : A) : P) := congrArg Subtype.val hb4
      _ = ((lemma3_conjDefect hA_normal hA_abelian (u : P) a : A) : P) := by
        rw [hdef]
      _ = ⁅(u : P), (a : P)⁆ :=
        lemma3_conjDefect_val hA_normal hA_abelian (u : P) a
  · intro hu
    apply MonoidHom.ext
    intro q
    refine Quotient.inductionOn' q ?_
    intro a
    simp only [lemma3_etaBar, MonoidHom.one_apply]
    change ((eta a : A) : A ⧸ lemma3_squareRange A) = 1
    rw [QuotientGroup.eq_one_iff]
    have heta2 : (eta a) ^ 2 = 1 := by
      calc
        (eta a) ^ 2 =
            lemma3_conjDefect hA_normal hA_abelian (u : P) a := (hdef a).symm
        _ = 1 := by
          apply Subtype.ext
          rw [lemma3_conjDefect_val]
          let uA : A := ⟨u, hu⟩
          have hcomm := congrArg A.subtype (mul_comm uA a)
          change (u : P) * (a : P) = (a : P) * (u : P) at hcomm
          simp only [commutatorElement_def]
          rw [hcomm]
          group
          simp
    have heta4 : (eta a) ^ 4 = 1 := by
      rw [show (eta a) ^ 4 = ((eta a) ^ 2) ^ 2 by
        exact pow_mul (eta a) 2 2, heta2, one_pow]
    obtain ⟨b, hb⟩ :=
      lemma3_four_torsion_is_square_of_homocyclic he hA heta4
    exact MonoidHom.mem_range.mpr ⟨b, by simpa [powMonoidHom] using hb⟩
private theorem lemma3_homocyclic_rank_two_le
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A : Subgroup P} (hA_X : IsXInvariantSubgroup X A) (hA_ne : A ≠ ⊥)
    {e r : ℕ} (he : 0 < e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    2 ≤ r := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Finite A := inferInstance
  obtain ⟨x, y, hx, hy, hxy⟩ := hP.2.2.1
  have hxA_mem :=
    lemma1_involutions_mem_of_nontrivial_invariant
      hP hXtrans hA_X hA_ne x hx
  have hyA_mem :=
    lemma1_involutions_mem_of_nontrivial_invariant
      hP hXtrans hA_X hA_ne y hy
  let xA : A := ⟨x, hxA_mem⟩
  let yA : A := ⟨y, hyA_mem⟩
  have hxA_sq : xA ^ 2 = 1 := by
    apply Subtype.ext
    simpa [xA] using hx.sq_eq_one
  have hyA_sq : yA ^ 2 = 1 := by
    apply Subtype.ext
    simpa [yA] using hy.sq_eq_one
  let T := {z : A // z ^ 2 = 1}
  let oneT : T := ⟨1, by simp⟩
  let xT : T := ⟨xA, hxA_sq⟩
  let yT : T := ⟨yA, hyA_sq⟩
  have hxT : xT ≠ oneT := by
    intro h
    apply hx.ne_one
    exact congrArg (fun z : T => ((z.1 : A) : P)) h
  have hyT : yT ≠ oneT := by
    intro h
    apply hy.ne_one
    exact congrArg (fun z : T => ((z.1 : A) : P)) h
  have hxyT : xT ≠ yT := by
    intro h
    apply hxy
    exact congrArg (fun z : T => ((z.1 : A) : P)) h
  letI : Fintype T := Fintype.ofFinite T
  have hthree : ({oneT, xT, yT} : Finset T).card = 3 := by
    have hone : oneT ∉ ({xT, yT} : Finset T) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro h
      rcases h with h | h
      · exact hxT h.symm
      · exact hyT h.symm
    rw [Finset.card_insert_of_notMem hone]
    have hxnot : xT ∉ ({yT} : Finset T) := by
      simp [hxyT]
    rw [Finset.card_insert_of_notMem hxnot]
    simp
  have hle : 3 ≤ Nat.card T := by
    rw [Nat.card_eq_fintype_card, ← hthree]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hcard : Nat.card T = 2 ^ r := by
    exact lemma1_twoTorsion_card_of_homocyclic he hA
  rw [hcard] at hle
  by_contra hr
  have hrle : r ≤ 1 := by omega
  interval_cases r <;> norm_num at hle
private theorem lemma3_outside_mul_inv_mem
    {P : Type u} [Group P] {A C : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A)
    {e r : ℕ} (he : 3 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e)))
    (eta : C → (A →* A))
    (hdef : ∀ (u : C) (a : A),
      lemma3_conjDefect hA_normal hA_abelian (u : P) a = (eta u a) ^ 2)
    (hscalar : ∀ u : C, lemma3_etaBar (eta u) = 1 ∨
      lemma3_etaBar (eta u) = MonoidHom.id _)
    (hzero : ∀ u : C, lemma3_etaBar (eta u) = 1 ↔ (u : P) ∈ A)
    (u v : C) (hu : (u : P) ∉ A) (hv : (v : P) ∉ A) :
    (v : P) * (u : P)⁻¹ ∈ A := by
  letI : IsMulCommutative A := hA_abelian
  have huinv : ((u⁻¹ : C) : P) ∉ A := by
    intro hui
    apply hu
    simpa using A.inv_mem hui
  have huinv_id :
      lemma3_etaBar (eta u⁻¹) = MonoidHom.id _ :=
    (hscalar u⁻¹).resolve_left (fun h => huinv ((hzero u⁻¹).mp h))
  have hv_id :
      lemma3_etaBar (eta v) = MonoidHom.id _ :=
    (hscalar v).resolve_left (fun h => hv ((hzero v).mp h))
  have hmul := lemma3_etaBar_mul
    hA_normal hA_abelian he hA (v : P) ((u⁻¹ : C) : P)
      (eta v) (eta u⁻¹) (eta (v * u⁻¹)) (hdef v) (hdef u⁻¹) (by
        intro a
        simpa using hdef (v * u⁻¹) a)
  have hid_mul :
      (MonoidHom.id (A ⧸ lemma3_squareRange A)) *
          MonoidHom.id (A ⧸ lemma3_squareRange A) = 1 := by
    apply MonoidHom.ext
    intro q
    simpa only [MonoidHom.mul_apply, MonoidHom.id_apply, MonoidHom.one_apply, pow_two]
      using lemma3_squareQuotient_pow_two q
  apply (hzero (v * u⁻¹)).mp
  rw [hmul, hv_id, huinv_id, hid_mul]
private theorem lemma3_conjDefect_eq_of_mul_inv_mem
    {P : Type u} [Group P] {A : Subgroup P}
    (hA_normal : A.Normal) (hA_abelian : IsMulCommutative A)
    (u v : P) (hvu : v * u⁻¹ ∈ A) :
    lemma3_conjDefect hA_normal hA_abelian v =
      lemma3_conjDefect hA_normal hA_abelian u := by
  letI : IsMulCommutative A := hA_abelian
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  rw [lemma3_conjDefect_val hA_normal hA_abelian v a,
    lemma3_conjDefect_val hA_normal hA_abelian u a]
  let d : A := ⟨v * u⁻¹, hvu⟩
  have hv : v = (d : P) * u := by
    dsimp [d]
    group
  have hua_mem : u * (a : P) * u⁻¹ ∈ A :=
    hA_normal.conj_mem (a : P) a.property u
  let ua : A := ⟨u * (a : P) * u⁻¹, hua_mem⟩
  have hcomm := congrArg A.subtype (mul_comm d ua)
  change (d : P) * (u * (a : P) * u⁻¹) =
    (u * (a : P) * u⁻¹) * (d : P) at hcomm
  rw [hv]
  simp only [commutatorElement_def]
  calc
    ((d : P) * u) * (a : P) * ((d : P) * u)⁻¹ * (a : P)⁻¹ =
        (d : P) * (u * (a : P) * u⁻¹) * (d : P)⁻¹ * (a : P)⁻¹ := by
      group
    _ = (u * (a : P) * u⁻¹) * (d : P) * (d : P)⁻¹ * (a : P)⁻¹ := by
      rw [hcomm]
    _ = u * (a : P) * u⁻¹ * (a : P)⁻¹ := by group
private theorem lemma3_power_subgroups_not_cyclic_over
    {A : Type*} [CommGroup A] [Finite A]
    {r d m : ℕ} (hr : 2 ≤ r) (hm : 2 ≤ m)
    (D B : Subgroup A)
    (hcardD : Nat.card D = d)
    (hcardB : Nat.card B = d * m ^ r)
    (z : A) (hzpow : z ^ m ∈ D)
    (hB : B = D ⊔ Subgroup.zpowers z) :
    False := by
  classical
  have hDB : D ≤ B := by
    rw [hB]
    exact le_sup_left
  have hmul :=
    Subgroup.relIndex_mul_relIndex (⊥ : Subgroup A) D B bot_le hDB
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    hcardD, hcardB] at hmul
  have hdpos : 0 < d := by
    rw [← hcardD]
    exact Nat.card_pos
  have hindex_eq : D.relIndex B = m ^ r :=
    Nat.eq_of_mul_eq_mul_left hdpos hmul
  have hindex_order :
      D.relIndex B = orderOf (QuotientGroup.mk' D z) := by
    calc
      D.relIndex B = (QuotientGroup.mk' D).ker.relIndex B := by
        rw [QuotientGroup.ker_mk']
      _ = Nat.card (B.map (QuotientGroup.mk' D)) :=
        Subgroup.relIndex_ker B (QuotientGroup.mk' D)
      _ = Nat.card ((D ⊔ Subgroup.zpowers z).map
          (QuotientGroup.mk' D)) := by rw [← hB]
      _ = Nat.card ↥(D.map (QuotientGroup.mk' D) ⊔
          (Subgroup.zpowers z).map (QuotientGroup.mk' D)) := by
        rw [Subgroup.map_sup]
      _ = Nat.card ↥((⊥ : Subgroup (A ⧸ D)) ⊔
          Subgroup.zpowers (QuotientGroup.mk' D z)) := by
        rw [(Subgroup.map_eq_bot_iff D).mpr (by rw [QuotientGroup.ker_mk']),
          MonoidHom.map_zpowers]
      _ = orderOf (QuotientGroup.mk' D z) := by simp
  have hzq : (QuotientGroup.mk' D z) ^ m = 1 := by
    rw [← map_pow]
    change ((z ^ m : A) : A ⧸ D) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hzpow
  have hindex_le : D.relIndex B ≤ m := by
    rw [hindex_order]
    exact orderOf_le_of_pow_eq_one (by omega) hzq
  have hlt : m < m ^ r := by
    simpa using Nat.pow_lt_pow_right (by omega : 1 < m) (by omega : 1 < r)
  rw [hindex_eq] at hindex_le
  omega

private theorem lemma3_eta_mod_square_scalar
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (hP : IsSuzukiTwoGroup P)
    (hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A C : Subgroup P} (hA_normal : A.Normal)
    (hA_abelian : IsMulCommutative A) (hA_X : IsXInvariantSubgroup X A)
    (hC_X : IsXInvariantSubgroup X C) (hAC : A ≤ C)
    (hfrattini : (frattini C).map C.subtype = (frattini A).map A.subtype)
    (hA_ne : A ≠ ⊥) {e r : ℕ} (he : 3 ≤ e)
    (hA : A ≃* Multiplicative (Fin r → ZMod (2 ^ e))) :
    letI : IsMulCommutative A := hA_abelian
    ∃ eta : C → (A →* A),
      (∀ (u : C) (a : A),
        lemma3_conjDefect hA_normal hA_abelian (u : P) a = (eta u a) ^ 2) ∧
      ∀ u : C, lemma3_etaBar (eta u) = 1 ∨
        lemma3_etaBar (eta u) = MonoidHom.id _ := by
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : Finite C := inferInstance
  letI : Fintype C := Fintype.ofFinite C
  letI : IsMulCommutative A := hA_abelian
  choose eta hdef using fun u : C =>
    lemma3_conj_defect_lift_square
      hP hXtrans hA_normal hA_abelian hA_X hAC hfrattini u
  refine ⟨eta, hdef, ?_⟩
  have hidem (u : C) :
      (lemma3_etaBar (eta u)).comp (lemma3_etaBar (eta u)) =
        lemma3_etaBar (eta u) := by
    apply lemma3_etaBar_idempotent
    apply lemma3_eta_mod_square_idempotent
      hA_normal hA_abelian he hA (u : P)
      (lemma3_squares_C_mem_A hP hfrattini u) (eta u) (hdef u)
  have hcomm (u v : C) :
      (lemma3_etaBar (eta u)).comp (lemma3_etaBar (eta v)) =
        (lemma3_etaBar (eta v)).comp (lemma3_etaBar (eta u)) := by
    apply lemma3_eta_mod_square_commute
      (eta u) (eta v) (eta (u * v)) (hidem u) (hidem v) (hidem (u * v))
    apply lemma3_etaBar_mul hA_normal hA_abelian he hA
      (u : P) (v : P) (eta u) (eta v) (eta (u * v)) (hdef u) (hdef v)
    intro a
    simpa using hdef (u * v) a
  obtain ⟨q0, hq0, hcommon⟩ :=
    lemma3_exists_common_eigenvector
      (lemma3_squareQuotient_nontrivial hP hA_abelian hA_ne)
      (fun u : C => lemma3_etaBar (eta u)) hidem hcomm
  letI : IsInvariant X P A := ⟨hA_X⟩
  letI : IsInvariant X P C := ⟨hC_X⟩
  letI : IsInvariant X A (lemma3_squareRange A) :=
    lemma3_squareRange_isInvariant
  letI : MulAction.QuotientAction X (lemma3_squareRange A) :=
    quotientAction_of_isInvariant (A := X) (G := A) _ (by infer_instance)
  letI : MulDistribMulAction X (A ⧸ lemma3_squareRange A) :=
    quotientMulDistribMulAction (A := X) (G := A) _ (by infer_instance)
  apply lemma3_scalar_of_common_eigenvector (X := X)
    (Q := A ⧸ lemma3_squareRange A) (ι := C)
    (fun u : C => lemma3_etaBar (eta u)) ?_ ?_ hq0 hcommon
  · intro q
    refine Quotient.inductionOn' q ?_
    intro a ha q'
    refine Quotient.inductionOn' q' ?_
    intro b hb
    obtain ⟨x, hx⟩ :=
      lemma3_squareQuotient_mk_transitive
        hXtrans hA_abelian hA_X (by omega : 1 ≤ e) hA a b ha hb
    refine ⟨x, ?_⟩
    simpa only [MulAction.Quotient.smul_coe] using hx
  · intro x u q
    exact lemma3_etaBar_smul
      hA_normal hA_abelian hA_X he hA x (u : P)
        (eta u) (eta (x • u)) (hdef u) (by
          intro a
          have hxu : ((x • u : C) : P) = x • (u : P) := rfl
          rw [← hxu]
          exact hdef (x • u) a) q
/-- Higman Lemma 3: in the deferred covering case, the covered abelian subgroup
has exponent at most four. -/
public theorem lemma3_covering_phi_case_exponent_le_four
    {X P : Type u} [Group X] [Group P] [MulDistribMulAction X P]
    (_hP : IsSuzukiTwoGroup P)
    (_hXtrans : ∀ x : P, x ∈ involutions P →
      ∀ y : P, y ∈ involutions P → ∃ k : X, y = k • x)
    {A C : Subgroup P} (_hA_normal : A.Normal)
    (_hA_abelian : IsMulCommutative A) (_hA_X : IsXInvariantSubgroup X A)
    (_hC_normal : C.Normal) (_hC_X : IsXInvariantSubgroup X C)
    (_hAC : A < C)
    (_hcover : ∀ B : Subgroup P, B.Normal → IsXInvariantSubgroup X B →
      A < B → B < C → False)
    (_hfrattini : (frattini C).map C.subtype = (frattini A).map A.subtype) :
    ∀ x : A, x ^ 4 = 1 := by
  intro x
  by_cases hA_ne : A ≠ ⊥
  · obtain ⟨e, r, ⟨hA⟩, hpower⟩ :=
      lemma1_abelian_invariant_homocyclic
        _hP _hXtrans _hA_abelian _hA_X
    by_cases he : 3 ≤ e
    · letI : Finite P := finite_of_isSuzukiTwoGroup _hP
      letI : Finite A := inferInstance
      letI : IsMulCommutative A := _hA_abelian
      letI : IsInvariant X P A := ⟨_hA_X⟩
      letI : IsInvariant X P C := ⟨_hC_X⟩
      have hr : 2 ≤ r :=
        lemma3_homocyclic_rank_two_le _hP _hXtrans _hA_X hA_ne (by omega) hA
      obtain ⟨eta, hdef, hscalar⟩ :=
        lemma3_eta_mod_square_scalar
          _hP _hXtrans _hA_normal _hA_abelian _hA_X _hC_X
            _hAC.le _hfrattini hA_ne he hA
      have hzero (w : C) :
          lemma3_etaBar (eta w) = 1 ↔ (w : P) ∈ A :=
        lemma3_etaBar_eq_one_iff_mem
          _hP _hXtrans _hA_normal _hA_abelian _hA_X
            _hfrattini hA_ne he hA w (eta w) (hdef w)
      obtain ⟨u0, huC, huA⟩ := SetLike.exists_of_lt _hAC
      let u : C := ⟨u0, huC⟩
      have hu : (u : P) ∉ A := huA
      have hu2_mem : (u : P) ^ 2 ∈ A :=
        lemma3_squares_C_mem_A _hP _hfrattini u
      let z : A := ⟨(u : P) ^ 2, hu2_mem⟩
      let theta : A →* A :=
        (powMonoidHom 2 : A →* A) *
          lemma3_conjDefect _hA_normal _hA_abelian (u : P)
      have htheta (a : A) :
          theta a = a ^ 2 *
            lemma3_conjDefect _hA_normal _hA_abelian (u : P) a := by
        rfl
      have hsquare (a : A) :
          ((u : P) * (a : P)) ^ 2 = (z : P) * (theta a : P) := by
        let d : A :=
          lemma3_conjDefect _hA_normal _hA_abelian (u : P) a
        have hd :
            (d : P) = ⁅(u : P), (a : P)⁆ :=
          lemma3_conjDefect_val _hA_normal _hA_abelian (u : P) a
        have hconj :
            (u : P) * (a : P) * (u : P)⁻¹ = (d : P) * (a : P) := by
          rw [hd]
          simp only [commutatorElement_def]
          group
        calc
          ((u : P) * (a : P)) ^ 2 =
              ((u : P) * (a : P) * (u : P)⁻¹) *
                (u : P) ^ 2 * (a : P) := by
            rw [pow_two]
            group
          _ = (d : P) * (a : P) * (z : P) * (a : P) := by
            rw [hconj]
          _ = ((z * (a ^ 2 * d) : A) : P) := by
            have hAeq : d * a * z * a = z * (a ^ 2 * d) := by
              rw [pow_two]
              ac_rfl
            exact congrArg A.subtype hAeq
          _ = (z : P) * (theta a : P) := by
            rw [htheta]
            rfl
      have htheta_smul (k : X) (a : A) :
          theta (k • a) = k • theta a := by
        let ku : C := k • u
        have hku_not : (ku : P) ∉ A := by
          intro hku
          exact hu ((_hA_X k (u : P)).mpr hku)
        have hcoset : (ku : P) * (u : P)⁻¹ ∈ A :=
          lemma3_outside_mul_inv_mem
            _hA_normal _hA_abelian he hA eta hdef hscalar hzero
              u ku hu hku_not
        have hdefect :=
          lemma3_conjDefect_eq_of_mul_inv_mem
            _hA_normal _hA_abelian (u : P) (ku : P) hcoset
        rw [htheta]
        change (k • a) ^ 2 *
            lemma3_conjDefect _hA_normal _hA_abelian (u : P) (k • a) =
          k • (a ^ 2 *
            lemma3_conjDefect _hA_normal _hA_abelian (u : P) a)
        nth_rw 1 [← hdefect]
        rw [show
          lemma3_conjDefect _hA_normal _hA_abelian (ku : P) (k • a) =
            k • lemma3_conjDefect _hA_normal _hA_abelian (u : P) a by
          change lemma3_conjDefect _hA_normal _hA_abelian (k • (u : P)) (k • a) =
            k • lemma3_conjDefect _hA_normal _hA_abelian (u : P) a
          exact lemma3_conjDefect_smul
            _hA_normal _hA_abelian _hA_X k (u : P) a]
        simp [smul_mul']
      let D : Subgroup A := theta.range
      have hD_forward (k : X) {a : A} (ha : a ∈ D) : k • a ∈ D := by
        rcases MonoidHom.mem_range.mp ha with ⟨b, rfl⟩
        exact MonoidHom.mem_range.mpr ⟨k • b, htheta_smul k b⟩
      have hD_internal : ∀ k : X, ∀ a : A, a ∈ D ↔ k • a ∈ D := by
        intro k a
        constructor
        · exact hD_forward k
        · intro hka
          have h := hD_forward k⁻¹ hka
          simpa [smul_smul] using h
      let Dp : Subgroup P := D.map A.subtype
      have hDp_X : IsXInvariantSubgroup X Dp := by
        intro k p
        constructor
        · intro hp
          rcases Subgroup.mem_map.mp hp with ⟨a, ha, rfl⟩
          exact Subgroup.mem_map.mpr
            ⟨k • a, (hD_internal k a).mp ha, rfl⟩
        · intro hp
          rcases Subgroup.mem_map.mp hp with ⟨a, ha, hval⟩
          have ha' : k⁻¹ • a ∈ D := (hD_internal k⁻¹ a).mp ha
          refine Subgroup.mem_map.mpr ⟨k⁻¹ • a, ha', ?_⟩
          have := congrArg (fun q : P => k⁻¹ • q) hval
          change k⁻¹ • (a : P) = p
          simpa [smul_smul] using this
      by_cases hzD : z ∈ D
      · rcases MonoidHom.mem_range.mp hzD with ⟨a, ha⟩
        let b : A := a⁻¹
        have hthetab : theta b = z⁻¹ := by
          dsimp [b]
          rw [map_inv, ha]
        have hinv_sq : ((u : P) * (b : P)) ^ 2 = 1 := by
          rw [hsquare, hthetab]
          simp
        have hinv_ne : (u : P) * (b : P) ≠ 1 := by
          intro hub
          apply hu
          have hu_eq : (u : P) = (b : P)⁻¹ := by
            calc
              (u : P) = (u : P) * (b : P) * (b : P)⁻¹ := by
                simp
              _ = (b : P)⁻¹ := by rw [hub, one_mul]
          rw [hu_eq]
          exact A.inv_mem b.property
        have hinv_mem : (u : P) * (b : P) ∈ involutions P :=
          ⟨hinv_ne, hinv_sq⟩
        have hinside :=
          lemma1_involutions_mem_of_nontrivial_invariant
            _hP _hXtrans _hA_X hA_ne ((u : P) * (b : P)) hinv_mem
        exfalso
        apply hu
        have hb_inv : (b : P)⁻¹ ∈ A := A.inv_mem b.property
        have := A.mul_mem hinside hb_inv
        simpa using this
      · let B : Subgroup A := D ⊔ Subgroup.zpowers z
        have hzB : z ∈ B := by
          exact (le_sup_right : Subgroup.zpowers z ≤ B)
            (Subgroup.mem_zpowers z)
        have hxzB (k : X) : k • z ∈ B := by
          let ku : C := k • u
          have hku_not : (ku : P) ∉ A := by
            intro hku
            exact hu ((_hA_X k (u : P)).mpr hku)
          have hcoset : (ku : P) * (u : P)⁻¹ ∈ A :=
            lemma3_outside_mul_inv_mem
              _hA_normal _hA_abelian he hA eta hdef hscalar hzero
                u ku hu hku_not
          let d : A := ⟨(ku : P) * (u : P)⁻¹, hcoset⟩
          have hd_mem : (u : P)⁻¹ * (d : P) * (u : P) ∈ A := by
            simpa using
              _hA_normal.conj_mem (d : P) d.property (u : P)⁻¹
          let a : A := ⟨(u : P)⁻¹ * (d : P) * (u : P), by
            simpa using hd_mem⟩
          have hku_eq : (ku : P) = (u : P) * (a : P) := by
            dsimp [a, d]
            group
          have hkz : k • z = z * theta a := by
            apply Subtype.ext
            change k • (u : P) ^ 2 = (z : P) * (theta a : P)
            calc
              k • (u : P) ^ 2 = (k • (u : P)) ^ 2 := by
                simp only [pow_two, smul_mul']
              _ = (ku : P) ^ 2 := rfl
              _ = ((u : P) * (a : P)) ^ 2 := by rw [hku_eq]
              _ = (z : P) * (theta a : P) := hsquare a
          rw [hkz]
          exact B.mul_mem
            ((le_sup_right : Subgroup.zpowers z ≤ B)
              (Subgroup.mem_zpowers z))
            ((le_sup_left : D ≤ B) (MonoidHom.mem_range.mpr ⟨a, rfl⟩))
        have hB_forward (k : X) {a : A} (ha : a ∈ B) : k • a ∈ B := by
          let f : A →* A := MulDistribMulAction.toMonoidHom A k
          have hmap : B.map f ≤ B := by
            dsimp [B]
            rw [Subgroup.map_sup, MonoidHom.map_zpowers]
            refine sup_le ?_ ?_
            · intro y hy
              rcases Subgroup.mem_map.mp hy with ⟨d, hd, rfl⟩
              exact (le_sup_left : D ≤ B) (hD_forward k hd)
            · exact (Subgroup.zpowers_le).mpr (hxzB k)
          exact hmap (Subgroup.mem_map_of_mem f ha)
        have hB_internal : ∀ k : X, ∀ a : A, a ∈ B ↔ k • a ∈ B := by
          intro k a
          constructor
          · exact hB_forward k
          · intro hka
            have h := hB_forward k⁻¹ hka
            simpa [smul_smul] using h
        let Bp : Subgroup P := B.map A.subtype
        have hBp_X : IsXInvariantSubgroup X Bp := by
          intro k p
          constructor
          · intro hp
            rcases Subgroup.mem_map.mp hp with ⟨a, ha, rfl⟩
            exact Subgroup.mem_map.mpr
              ⟨k • a, (hB_internal k a).mp ha, rfl⟩
          · intro hp
            rcases Subgroup.mem_map.mp hp with ⟨a, ha, hval⟩
            have ha' : k⁻¹ • a ∈ B := (hB_internal k⁻¹ a).mp ha
            refine Subgroup.mem_map.mpr ⟨k⁻¹ • a, ha', ?_⟩
            have := congrArg (fun q : P => k⁻¹ • q) hval
            change k⁻¹ • (a : P) = p
            simpa [smul_smul] using this
        have hDpA : Dp ≤ A := by
          rintro p ⟨a, -, rfl⟩
          exact a.property
        have hBpA : Bp ≤ A := by
          rintro p ⟨a, -, rfl⟩
          exact a.property
        obtain ⟨sD, hsD, hDp_pow⟩ := hpower Dp hDpA hDp_X
        obtain ⟨sB, hsB, hBp_pow⟩ := hpower Bp hBpA hBp_X
        have hDpow :
            D = (powMonoidHom (2 ^ sD) : A →* A).range := by
          apply Subgroup.map_injective A.subtype_injective
          exact hDp_pow.trans
            (lemma3_powerClosure_eq_range_map _hA_abelian (2 ^ sD))
        have hBpow :
            B = (powMonoidHom (2 ^ sB) : A →* A).range := by
          apply Subgroup.map_injective A.subtype_injective
          exact hBp_pow.trans
            (lemma3_powerClosure_eq_range_map _hA_abelian (2 ^ sB))
        have hDB : D < B := by
          apply lt_of_le_of_ne le_sup_left
          intro hEq
          apply hzD
          rw [hEq]
          exact hzB
        have hsBD : sB < sD := by
          by_contra hnot
          have hsDB : sD ≤ sB := by omega
          apply (not_le_of_gt hDB)
          rw [hBpow, hDpow]
          rintro y ⟨a, rfl⟩
          refine MonoidHom.mem_range.mpr ⟨a ^ (2 ^ (sB - sD)), ?_⟩
          change (a ^ (2 ^ (sB - sD))) ^ (2 ^ sD) = a ^ (2 ^ sB)
          rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hsDB]
        have hzpow : z ^ (2 ^ (sD - sB)) ∈ D := by
          have hzB' := hzB
          rw [hBpow] at hzB'
          rcases MonoidHom.mem_range.mp hzB' with ⟨a, ha⟩
          rw [hDpow]
          refine MonoidHom.mem_range.mpr ⟨a, ?_⟩
          rw [← ha]
          change a ^ (2 ^ sD) =
            (a ^ (2 ^ sB)) ^ (2 ^ (sD - sB))
          rw [← pow_mul, ← pow_add, Nat.add_sub_of_le hsBD.le]
        have hDcard :
            Nat.card D = (2 ^ (e - sD)) ^ r := by
          calc
            Nat.card D = Nat.card Dp :=
              (Subgroup.card_map_of_injective A.subtype_injective).symm
            _ = Nat.card (Subgroup.closure
                {y : P | ∃ a : A, (a : P) ^ (2 ^ sD) = y}) :=
              by rw [hDp_pow]
            _ = (2 ^ (e - sD)) ^ r := by
              simpa [Nat.sub_sub_self hsD] using
                lemma1_power_closure_card _hA_abelian
                  (f := e - sD) (Nat.sub_le e sD) hA
        have hBcard :
            Nat.card B = (2 ^ (e - sB)) ^ r := by
          calc
            Nat.card B = Nat.card Bp :=
              (Subgroup.card_map_of_injective A.subtype_injective).symm
            _ = Nat.card (Subgroup.closure
                {y : P | ∃ a : A, (a : P) ^ (2 ^ sB) = y}) :=
              by rw [hBp_pow]
            _ = (2 ^ (e - sB)) ^ r := by
              simpa [Nat.sub_sub_self hsB] using
                lemma1_power_closure_card _hA_abelian
                  (f := e - sB) (Nat.sub_le e sB) hA
        let d := (2 ^ (e - sD)) ^ r
        let m := 2 ^ (sD - sB)
        have hm : 2 ≤ m := by
          dsimp [m]
          have : 0 < sD - sB := Nat.sub_pos_of_lt hsBD
          have hm1 : 1 < 2 ^ (sD - sB) := Nat.one_lt_two_pow (Nat.ne_of_gt this)
          omega
        have hbase : 2 ^ (e - sB) = 2 ^ (e - sD) * m := by
          dsimp [m]
          rw [← pow_add]
          congr 1
          omega
        have hBcard' : Nat.card B = d * m ^ r := by
          rw [hBcard, hbase, mul_pow]
        exact (lemma3_power_subgroups_not_cyclic_over
          (r := r) hr (m := m) hm D B (d := d)
            (by simpa [d] using hDcard) hBcard' z
            (by simpa [m] using hzpow) rfl).elim
    · have he2 : e ≤ 2 := by omega
      have hxexp := lemma1_pow_eq_one_of_homocyclic hA x
      have hfour : 4 = 2 ^ e * 2 ^ (2 - e) := by
        interval_cases e <;> norm_num
      rw [hfour, pow_mul, hxexp, one_pow]
  · have hAbot : A = ⊥ := not_ne_iff.mp hA_ne
    have hx1 : (x : P) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hAbot]
      exact x.property
    apply Subtype.ext
    simp [hx1]
end Higman
end External
end CFSG.BenderSuzuki













































