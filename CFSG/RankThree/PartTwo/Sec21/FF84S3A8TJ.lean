module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3Model
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG.RankThree.PartTwo.Sec21.FF79 (IsElemAb Nor)
open CFSG.ComponentClassification.GHarris (isSimpleGroup_GL32_gh card_GL32_gh)
open Matrix
open scoped Pointwise

abbrev V3 : Type := Fin 3 → ZMod 2

@[expose] def ptVec : Fin 8 → V3 :=
  ![![1, 0, 0], ![0, 1, 0], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ![1, 1, 1], ![0, 0, 0], ![0, 0, 1]]

@[expose] def vecIdx (v : V3) : Fin 8 :=
  let c : ℕ := (v 0).val + 2 * (v 1).val + 4 * (v 2).val
  ![6, 0, 1, 2, 7, 3, 4, 5] ⟨c % 8, Nat.mod_lt _ (by norm_num)⟩

theorem vecIdx_ptVec (x : Fin 8) : vecIdx (ptVec x) = x := by
  revert x; decide

theorem ptVec_vecIdx (v : V3) : ptVec (vecIdx v) = v := by
  have key : ∀ a b c : ZMod 2, ptVec (vecIdx ![a, b, c]) = ![a, b, c] := by decide
  have hv : v = ![v 0, v 1, v 2] := by
    ext i; fin_cases i <;> rfl
  calc ptVec (vecIdx v) = ptVec (vecIdx ![v 0, v 1, v 2]) := by rw [← hv]
    _ = ![v 0, v 1, v 2] := key _ _ _
    _ = v := hv.symm

@[expose] def ptEquiv : Fin 8 ≃ V3 where
  toFun := ptVec
  invFun := vecIdx
  left_inv := vecIdx_ptVec
  right_inv := ptVec_vecIdx

theorem ptVec_six : ptVec 6 = 0 := by
  ext i; fin_cases i <;> rfl

@[expose] def Amat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 1, 0; 0, 0, 1]

@[expose] def Ainv : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def Smat : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

@[expose] def Aunit : GL (Fin 3) (ZMod 2) := ⟨Amat, Ainv, by decide, by decide⟩

@[expose] def Sunit : GL (Fin 3) (ZMod 2) := ⟨Smat, Smat, by decide, by decide⟩

@[expose] def linAct : GL (Fin 3) (ZMod 2) →* Equiv.Perm V3 where
  toFun g :=
    { toFun := fun v => (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v
      invFun := fun v => ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ v
      left_inv := fun v => by simp [Matrix.mulVec_mulVec]
      right_inv := fun v => by simp [Matrix.mulVec_mulVec] }
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp [Matrix.mulVec_mulVec]

@[expose] def tr8 : Equiv.Perm V3 →* Equiv.Perm (Fin 8) where
  toFun p := ptEquiv.symm.permCongr p
  map_one' := by ext x; simp
  map_mul' p q := by ext x; simp [Equiv.permCongr_apply]

@[expose] def rho : GL (Fin 3) (ZMod 2) →* Equiv.Perm (Fin 8) := tr8.comp linAct

@[expose] def transPerm : Multiplicative V3 →* Equiv.Perm V3 where
  toFun v := Equiv.addRight (Multiplicative.toAdd v)
  map_one' := by ext x; simp
  map_mul' v w := by ext x; simp; abel

@[expose] def trans8 : Multiplicative V3 →* Equiv.Perm (Fin 8) := tr8.comp transPerm

@[expose] def Tsub : Subgroup (Equiv.Perm (Fin 8)) := (⊤ : Subgroup (Multiplicative V3)).map trans8

@[expose] def Jsub : Subgroup (Equiv.Perm (Fin 8)) := (rho).range

theorem m₁_eq : m₁ = Equiv.swap 0 1 * Equiv.swap 1 2 * (Equiv.swap 3 4 * Equiv.swap 4 5) := by
  simp [m₁, List.formPerm_cons_cons, mul_assoc]

theorem rho_Aunit : rho Aunit = m₁ := by
  rw [m₁_eq]
  exact Equiv.ext (by intro x; revert x; decide)

theorem m1_ne_one : m₁ ≠ 1 := by intro h; revert h; decide

theorem Aunit_cube : Aunit ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, pow_three]; decide)

theorem Aunit_ne_one : Aunit ≠ 1 := fun h => by
  have := congrArg Units.val h
  exact absurd this (by decide)

theorem Sunit_mul_self : Sunit * Sunit = 1 := Units.ext (by simp only [Units.val_mul, Units.val_one]; decide)

theorem Sunit_inv : Sunit⁻¹ = Sunit := inv_eq_of_mul_eq_one_right Sunit_mul_self

theorem Sunit_conj_Aunit : Sunit * Aunit * Sunit = Aunit * Aunit :=
  Units.ext (by simp only [Units.val_mul]; decide)

theorem Aunit_not_comm_Sunit : Aunit * Sunit ≠ Sunit * Aunit := fun h => by
  have := congrArg Units.val h
  simp only [Units.val_mul] at this
  revert this; decide

theorem trans_sign (v : V3) : Equiv.Perm.sign (trans8 (Multiplicative.ofAdd v)) = 1 := by
  have key : ∀ a b c : ZMod 2,
      Equiv.Perm.sign (trans8 (Multiplicative.ofAdd ![a, b, c])) = 1 := by decide
  have hv : v = ![v 0, v 1, v 2] := by
    ext i; fin_cases i <;> rfl
  rw [hv]
  exact key _ _ _

theorem factorization_168 : (168 : ℕ).factorization 3 = 1 := by
  rw [show (168 : ℕ) = 3 ^ 1 * 56 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  simp

theorem rho_injective : Function.Injective rho := by
  have hs := isSimpleGroup_GL32_gh
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hs.eq_bot_or_eq_top_of_normal rho.ker with h | h
  · exact h
  · exfalso
    have hmem : Aunit ∈ rho.ker := h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, rho_Aunit] at hmem
    exact m1_ne_one hmem

theorem rho_sign (g : GL (Fin 3) (ZMod 2)) : Equiv.Perm.sign (rho g) = 1 := by
  have hs := isSimpleGroup_GL32_gh
  let f : GL (Fin 3) (ZMod 2) →* ℤˣ := Equiv.Perm.sign.comp rho
  rcases hs.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exfalso
    have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 h
    have hcomm : Aunit * Sunit = Sunit * Aunit := hinj (by
      simp only [f, MonoidHom.comp_apply, map_mul]
      exact mul_comm _ _)
    exact Aunit_not_comm_Sunit hcomm
  · have hmem : g ∈ f.ker := h ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hmem
    exact hmem

theorem rho_mem_A8 (g : GL (Fin 3) (ZMod 2)) : rho g ∈ A8s :=
  Equiv.Perm.mem_alternatingGroup.2 (rho_sign g)

theorem Jsub_le_A8 : Jsub ≤ A8s := by
  rintro _ ⟨g, rfl⟩
  exact rho_mem_A8 g

theorem lin_conj (g : GL (Fin 3) (ZMod 2)) (a : Multiplicative V3) :
    (linAct g) * transPerm a * (linAct g)⁻¹ =
      transPerm (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd a)) := by
  have hinv : (linAct g)⁻¹ = linAct g⁻¹ := (map_inv linAct g).symm
  rw [hinv]
  ext x
  simp [linAct, transPerm, Matrix.mulVec_add, Matrix.mulVec_mulVec]

theorem rho_conj_trans (g : GL (Fin 3) (ZMod 2)) (a : Multiplicative V3) :
    rho g * trans8 a * (rho g)⁻¹ =
      trans8 (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd a)) := by
  have := congrArg tr8 (lin_conj g a)
  simpa [rho, trans8, map_mul, map_inv] using this

theorem trans8_apply6 (a : Multiplicative V3) : ptVec (trans8 a 6) = Multiplicative.toAdd a := by
  show ptVec (vecIdx (ptVec 6 + Multiplicative.toAdd a)) = Multiplicative.toAdd a
  rw [ptVec_six, zero_add, ptVec_vecIdx]

theorem trans8_injective : Function.Injective trans8 := by
  intro a b h
  have h6 : Multiplicative.toAdd a = Multiplicative.toAdd b := by
    rw [← trans8_apply6 a, ← trans8_apply6 b, h]
  exact Multiplicative.toAdd.injective h6

theorem Jsub_le_Nor : Jsub ≤ Nor (Tsub) := by
  have fwd : ∀ g : GL (Fin 3) (ZMod 2), ∀ x ∈ Tsub, rho g * x * (rho g)⁻¹ ∈ Tsub := by
    intro g x hx
    obtain ⟨a, _, rfl⟩ := Subgroup.mem_map.1 hx
    rw [rho_conj_trans]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_top _)
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fwd g x
  · intro hx
    have h2 := fwd g⁻¹ _ hx
    rw [map_inv] at h2
    have e : (rho g)⁻¹ * (rho g * x * (rho g)⁻¹) * (rho g)⁻¹⁻¹ = x := by group
    rwa [e] at h2

theorem isElemAb_Tsub : IsElemAb 2 3 Tsub := by
  refine ⟨?_, ?_⟩
  · have hsq : ∀ a : Multiplicative V3, a ^ 2 = 1 := by
      intro a
      apply Multiplicative.toAdd.injective
      have hu : ∀ u : V3, u + u = 0 := by decide
      rw [toAdd_pow, two_nsmul, toAdd_one]
      exact hu _
    haveI : CFSG.IsElementaryAbelian 2 ↥(⊤ : Subgroup (Multiplicative V3)) :=
      { toIsMulCommutative := inferInstance
        exponent_dvd_p := by
          refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
          intro x
          exact Subtype.ext (by simpa using hsq x.1) }
    exact CFSG.IsElementaryAbelian.map trans8
  · rw [Tsub, Subgroup.card_map_of_injective trans8_injective, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl

theorem Tsub_le_A8 : Tsub ≤ A8s := by
  intro x hx
  obtain ⟨a, _, rfl⟩ := Subgroup.mem_map.1 hx
  have := trans_sign (Multiplicative.toAdd a)
  exact Equiv.Perm.mem_alternatingGroup.2 (by simpa using this)

theorem card_Jsub : Nat.card Jsub = 168 :=
  (Nat.card_congr (MonoidHom.ofInjective rho_injective).symm.toEquiv).trans card_GL32_gh

theorem Jsub_simple : IsSimpleGroup Jsub := by
  haveI := isSimpleGroup_GL32_gh
  exact (MonoidHom.ofInjective rho_injective).symm.isSimpleGroup

theorem m1_mem : m₁ ∈ Jsub := ⟨Aunit, rho_Aunit⟩

theorem gl3_conj_order3 (g : GL (Fin 3) (ZMod 2)) (hg : orderOf g = 3) :
    ∃ h : GL (Fin 3) (ZMod 2), h * Aunit * h⁻¹ = g := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (GL (Fin 3) (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [card_GL32_gh]; norm_num)
  have hfac : (Nat.card (GL (Fin 3) (ZMod 2))).factorization 3 = 1 := by
    rw [card_GL32_gh]; exact factorization_168
  have hA : orderOf Aunit = 3 := orderOf_eq_prime Aunit_cube Aunit_ne_one
  let PA : Sylow 3 (GL (Fin 3) (ZMod 2)) :=
    Sylow.ofCard (Subgroup.zpowers Aunit) (by rw [Nat.card_zpowers, hA, hfac]; norm_num)
  let PG : Sylow 3 (GL (Fin 3) (ZMod 2)) :=
    Sylow.ofCard (Subgroup.zpowers g) (by rw [Nat.card_zpowers, hg, hfac]; norm_num)
  have hmem : PG ∈ MulAction.orbit (GL (Fin 3) (ZMod 2)) PA := by
    rw [Sylow.orbit_eq_top]; exact Set.mem_univ _
  obtain ⟨h, hh⟩ := hmem
  have hcoe : MulAut.conj h • (Subgroup.zpowers Aunit) = Subgroup.zpowers g := by
    have := congrArg (fun P : Sylow 3 (GL (Fin 3) (ZMod 2)) => (P : Subgroup (GL (Fin 3) (ZMod 2)))) hh
    simpa [Sylow.coe_subgroup_smul, PA, PG] using this
  have hmemg : g ∈ MulAut.conj h • (Subgroup.zpowers Aunit) := by
    rw [hcoe]; exact Subgroup.mem_zpowers g
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.1 hmemg
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  simp only [MulAut.smul_def, MulAut.conj_apply] at hkg
  have hr : Aunit ^ m = Aunit ^ (m % 3) := by
    have := zpow_mod_orderOf Aunit m
    rw [hA] at this
    push_cast at this
    exact this.symm
  have hr3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr3 with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hr
    rw [hr, mul_one, mul_inv_cancel] at hkg
    subst hkg
    simp at hg
  · refine ⟨h, ?_⟩
    rw [hr, h1, zpow_one] at hkg
    exact hkg
  · refine ⟨h * Sunit, ?_⟩
    rw [hr, h2, zpow_two] at hkg
    rw [← hkg, ← Sunit_conj_Aunit, _root_.mul_inv_rev, Sunit_inv]
    group

theorem m1_conj : ∀ y ∈ Jsub, orderOf y = 3 → ∃ j ∈ Jsub, j * m₁ * j⁻¹ = y := by
  rintro _ ⟨g, rfl⟩ hy3
  have hg3 : orderOf g = 3 := (orderOf_injective rho rho_injective g).symm.trans hy3
  obtain ⟨h, hh⟩ := gl3_conj_order3 g hg3
  refine ⟨rho h, ⟨h, rfl⟩, ?_⟩
  rw [← rho_Aunit, ← map_inv, ← map_mul, ← map_mul, hh]

theorem A8_TJ :
    ∃ T J : Subgroup P8, T ≤ A8s ∧ J ≤ A8s ∧ IsElemAb 2 3 T ∧ J ≤ Nor T ∧ IsSimpleGroup J ∧
      Nat.card J = 168 ∧ m₁ ∈ J ∧
      ∀ y ∈ J, orderOf y = 3 → ∃ j ∈ J, j * m₁ * j⁻¹ = y :=
  ⟨Tsub, Jsub, Tsub_le_A8, Jsub_le_A8, isElemAb_Tsub, Jsub_le_Nor, Jsub_simple, card_Jsub,
    m1_mem, m1_conj⟩

end CFSG.RankThree.PartTwo.Sec21.FF84.S3
