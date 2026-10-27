module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis

open Subgroup

variable {D : Type*} [Group D]

@[expose] def gmsRootConjugates (W R : Subgroup D) : Set (Subgroup D) :=
  {S | ∃ g : D, S = R.map (MulAut.conj g⁻¹).toMonoidHom ∧ S ≤ W}

theorem map_conj_mem_gmsRootConjugates {W R S : Subgroup D} (hS : S ∈ gmsRootConjugates W R)
    {n : D} (hn : n ∈ normalizer (W : Set D)) :
    S.map (MulAut.conj n).toMonoidHom ∈ gmsRootConjugates W R := by
  obtain ⟨g, rfl, hle⟩ := hS
  refine ⟨g * n⁻¹, ?_, ?_⟩
  · rw [Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]
  · rintro _ ⟨s, hs, rfl⟩
    exact (mem_normalizer_iff.mp hn s).mp (hle hs)

instance gmsRootConjugatesMulAction (W R : Subgroup D) :
    MulAction (normalizer (W : Set D)) (gmsRootConjugates W R) where
  smul n S := ⟨S.1.map (MulAut.conj (n : D)).toMonoidHom,
    map_conj_mem_gmsRootConjugates S.2 n.2⟩
  one_smul S := Subtype.ext (by
    change S.1.map (MulAut.conj (1 : D)).toMonoidHom = S.1
    rw [map_one]
    exact Subgroup.map_id _)
  mul_smul n m S := Subtype.ext (by
    change S.1.map (MulAut.conj ((n : D) * m)).toMonoidHom =
      (S.1.map (MulAut.conj (m : D)).toMonoidHom).map (MulAut.conj (n : D)).toMonoidHom
    rw [Subgroup.map_map, map_mul]
    rfl)

@[expose] def gmsRootConjugateAction (W R : Subgroup D) :
    normalizer (W : Set D) →* Equiv.Perm (gmsRootConjugates W R) :=
  MulAction.toPermHom _ _

instance gmsCentralizer_normal (X U : Subgroup D) :
    ((X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D))).Normal where
  conj_mem c hc n := by
    rw [mem_subgroupOf] at hc ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hnX : (n : D) ∈ X := (Subgroup.mem_inf.mp n.2).1
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem hnX (Subgroup.mem_inf.mp hc).1) (inv_mem hnX),
      mem_centralizer_iff.mpr fun u hu => ?_⟩
    have hn : (n : D)⁻¹ ∈ normalizer (U : Set D) := inv_mem (Subgroup.mem_inf.mp n.2).2
    have hu' : (n : D)⁻¹ * u * (n : D)⁻¹⁻¹ ∈ U := (mem_normalizer_iff.mp hn u).mp hu
    rw [inv_inv] at hu'
    have hc' := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _ hu'
    calc u * ((n : D) * c * (n : D)⁻¹) = n * (((n : D)⁻¹ * u * n) * c) * (n : D)⁻¹ := by group
      _ = n * (c * ((n : D)⁻¹ * u * n)) * (n : D)⁻¹ := by rw [hc']
      _ = ((n : D) * c * (n : D)⁻¹) * u := by group

@[expose] def gmsConjAct (X U : Subgroup D) :
    (X ⊓ normalizer (U : Set D) : Subgroup D) →* MulAut U where
  toFun n :=
    { toFun := fun u => ⟨n * u * (n : D)⁻¹,
        (mem_normalizer_iff.mp (Subgroup.mem_inf.mp n.2).2 u).mp u.2⟩
      invFun := fun u => ⟨(n : D)⁻¹ * u * (n : D)⁻¹⁻¹,
        (mem_normalizer_iff.mp (inv_mem (Subgroup.mem_inf.mp n.2).2) u).mp u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext u
    simp
  map_mul' n m := by
    ext u
    simp [mul_assoc]

theorem gmsConjAct_ker_le (X U : Subgroup D) :
    (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D)) ≤
      (gmsConjAct X U).ker := by
  intro c hc
  rw [mem_subgroupOf] at hc
  rw [MonoidHom.mem_ker]
  ext u
  have h := mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 u u.2
  simp only [gmsConjAct, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    MulAut.one_apply]
  rw [← h, mul_inv_cancel_right]

@[expose] def gmsQuotConjAct (X U : Subgroup D) :
    (X ⊓ normalizer (U : Set D) : Subgroup D) ⧸
        (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D)) →*
      MulAut U :=
  QuotientGroup.lift _ (gmsConjAct X U) (gmsConjAct_ker_le X U)


abbrev GMSNormalizerQuotient (X U : Subgroup D) : Type _ :=
  (X ⊓ normalizer (U : Set D) : Subgroup D) ⧸
    (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D))

@[expose] def GMSNormalRootData (J R X U P : Subgroup D) (n : ℕ) : Prop :=
  3 ≤ n ∧
    (Even (Nat.card J) ∧ ∀ g : D, g ∉ normalizer (J : Set D) →
      Odd (Nat.card (J ⊓ J.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup D))) ∧
    (IsElementaryAbelian 2 R ∧ R ≤ J ∧ ∃ T : Sylow 2 J, (T : Subgroup J) = R.subgroupOf J) ∧
    (X ≤ normalizer (R : Set D) ∧ (X.subgroupOf (normalizer (R : Set D))).Normal ∧
      X ≤ centralizer (R : Set D)) ∧
    (IsElementaryAbelian 2 U ∧ U ≤ X ∧ (∃ T : Sylow 2 X, (T : Subgroup X) = U.subgroupOf X) ∧
      Nat.card U = 2 ^ n) ∧
    (IsCyclic (GMSNormalizerQuotient X U) ∧ Nat.card (GMSNormalizerQuotient X U) = 2 ^ n - 1 ∧
      ∀ u v : U, u ≠ 1 → v ≠ 1 → ∃! c : GMSNormalizerQuotient X U, gmsQuotConjAct X U c u = v) ∧
    (P ≤ normalizer (R : Set D) ∧
      (∃ T : Sylow 2 (normalizer (R : Set D)),
        (T : Subgroup (normalizer (R : Set D))) = P.subgroupOf (normalizer (R : Set D))) ∧
      U ≤ P ∧ R ≤ P ∧ P ≤ normalizer (U : Set D) ∧ U ⊓ R = ⊥ ∧
      P ⊓ centralizer (U : Set D) = U ⊔ R ∧ ((U ⊔ R).subgroupOf P).Normal)

theorem GMSNormalRootData.ne_bot [Finite D] {J R X U P : Subgroup D} {n : ℕ}
    (h : GMSNormalRootData J R X U P n) : R ≠ ⊥ := by
  obtain ⟨-, ⟨hJ, -⟩, ⟨-, hRJ, T, hT⟩, -⟩ := h
  rintro rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := Sylow.card_eq_multiplicity T
  have hT1 : Nat.card T = 1 := by
    rw [show Nat.card T = Nat.card ((⊥ : Subgroup D).subgroupOf J) from by rw [← hT]]
    simp
  rw [hT1] at hcard
  have h0 : (Nat.card J).factorization 2 = 0 := by
    have := (Nat.pow_eq_one.mp hcard.symm)
    omega
  have hJ0 : Nat.card J ≠ 0 := Nat.card_pos.ne'
  have := Nat.Prime.factorization_pos_of_dvd Nat.prime_two hJ0 (even_iff_two_dvd.mp hJ)
  omega

end CFSG.LocalAnalysis
