module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TDih
public import CFSG.Quasithin.Vol2.Ch8Sec2L828TCtx

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative commutatorElement

section SixB1

variable {G : Type} [Group G] [Finite G]

theorem s828_V_not_le_P {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) (m : ℕ) (hm : 1 < m)
    (eI : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup m) :
    ¬ fsuV T I ≤ pCoreOf 2 (ch82I (fsuV T I) h) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := fsuV T I with hVdef
  set J := ch82I V h with hJdef
  set P := pCoreOf 2 J with hPdef
  have hkerI : kerIn (fsuM T L ⊓ J) J = P := by
    obtain ⟨-, -, -, -, -, -, -, hkerI, -⟩ := id c.hC
    exact hkerI
  have hkerJ : ∀ x : ↥J, QuotientGroup.mk' ((kerIn (fsuM T L ⊓ J) J).subgroupOf J) x = 1 ↔
      (x : G) ∈ P := by
    intro x
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hkerI]
  intro hVle
  have hhP : h ∈ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ c.hhI
  have hJle : J ≤ P := by
    refine sup_le hVle fun x hx => ?_
    rw [B6.mem_conjSub] at hx
    have := (Subgroup.mem_normalizer_iff.mp hhP _).mp (hVle hx)
    simpa [mul_assoc] using this
  have htriv : ∀ q : E2.StarQuot (fsuM T L ⊓ J) J, q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn (fsuM T L ⊓ J) J).subgroupOf J) q
    exact (hkerJ x).mpr (hJle x.2)
  have hc1 : Nat.card (E2.StarQuot (fsuM T L ⊓ J) J) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (htriv a).trans (htriv b).symm⟩, ⟨1⟩⟩
  have hc2 := Nat.card_congr eI.toEquiv
  rw [DihedralGroup.nat_card, hc1] at hc2
  omega

theorem s828_P_norm_V {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k) :
    pCoreOf 2 (ch82I (fsuV T I) h) ≤ Subgroup.normalizer (fsuV T I : Set G) := by
  have hkerI : kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) =
      pCoreOf 2 (ch82I (fsuV T I) h) := by
    obtain ⟨-, -, -, -, -, -, -, hkerI, -⟩ := id c.hC
    exact hkerI
  have hP := s828_pair c.hV c.hVT c.hTV c.hC
  have hVPB := s828_commutator_V_le_B hP hkerI
  have hfwd : ∀ p ∈ pCoreOf 2 (ch82I (fsuV T I) h), ∀ v ∈ fsuV T I,
      p * v * p⁻¹ ∈ fsuV T I := by
    intro p hp v hv
    have h1 : ⁅v, p⁆ ∈ ch82B (fsuV T I) h := (Subgroup.commutator_le.mp hVPB) v hv p hp
    have e : p * v * p⁻¹ = (⁅v, p⁆)⁻¹ * v := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (fsuV T I).mul_mem ((fsuV T I).inv_mem ((inf_le_left : ch82B (fsuV T I) h ≤ _) h1)) hv
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => hfwd p hp v hv, fun hv => ?_⟩
  have := hfwd p⁻¹ ((pCoreOf 2 (ch82I (fsuV T I) h)).inv_mem hp) _ hv
  simpa [mul_assoc] using this

theorem s828_T_norm_I {T L I H : Subgroup G} {h : G} {k : ℕ} [IsMulCommutative ↥(fsuV T I)]
    (c : S828Ctx T L I H h k)
    (eI : E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 5)
    (hTX : T ≤ Subgroup.normalizer (oTwoUpper (ch82I (fsuV T I) h) : Set G)) :
    T ≤ Subgroup.normalizer (ch82I (fsuV T I) h : Set G) ∧
      T ≤ Subgroup.normalizer (pCoreOf 2 (ch82I (fsuV T I) h) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V := fsuV T I with hVdef
  set J := ch82I V h with hJdef
  set P := pCoreOf 2 J with hPdef
  have hkerI : kerIn (fsuM T L ⊓ J) J = P := by
    obtain ⟨-, -, -, -, -, -, -, hkerI, -⟩ := id c.hC
    exact hkerI
  have hJ2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hPJ : P ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hJP : J ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  haveI hNP : (P.subgroupOf J).Normal := by
    rw [← hkerI]
    infer_instance
  let e' : ↥J ⧸ P.subgroupOf J ≃* DihedralGroup 5 :=
    (QuotientGroup.quotientMulEquivOfEq (by rw [hkerI])).trans eI
  obtain ⟨y, hy5, j, hj, hye⟩ := L828Dih.exists_five_elt hJ2 e'
  have hVP := s828_V_not_le_P c 5 (by norm_num) eI
  obtain ⟨v, hvV, hvP⟩ := Set.not_subset.mp hVP
  have hvJ : v ∈ J := (le_sup_left : V ≤ J) hvV
  have hv2 : v ^ 2 = 1 := c.hV.2 _ hvV
  set X := oTwoUpper J with hXdef
  have hyX : (y : G) ∈ X := by
    refine mem_oTwoUpper_of_odd y.2 ?_
    have h1 : orderOf (y : G) ∣ 5 := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hy5
      simpa using this
    exact Odd.of_dvd_nat (by decide) h1
  have hXJ : X ≤ J := oTwoUpper_le J
  have hJX : J ≤ Subgroup.normalizer (X : Set G) := le_normalizer_oTwoUpper J
  have hPV := s828_P_norm_V c
  have hPY : P ≤ Subgroup.normalizer ((X ⊔ V : Subgroup G) : Set G) := by
    intro p hp
    have h1 := hJX (hPJ hp)
    have h2 := hPV hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    show (X ⊔ V).map _ = X ⊔ V
    rw [Subgroup.map_sup, h1, h2]
  have hsup : (X ⊔ P) ⊔ V = J := by
    refine L828Dih.sup_eq_of_dihedral (I := J) (P := P) (X := X ⊔ P) (V := V) e'
      (sup_le hXJ hPJ) (le_sup_left : V ≤ J) (le_sup_right.trans le_sup_left) (y := y) (j := j) hj
      hye
      (Subgroup.mem_sup_left hyX) (v := ⟨v, hvJ⟩) hvV hvP hv2
  have hJY : J ≤ Subgroup.normalizer ((X ⊔ V : Subgroup G) : Set G) := by
    rw [← hsup]
    refine sup_le (sup_le ?_ hPY) ?_
    · exact le_sup_left.trans Subgroup.le_normalizer
    · exact le_sup_right.trans Subgroup.le_normalizer
  have hJle : J ≤ X ⊔ V := by
    refine sup_le le_sup_right fun x hx => ?_
    rw [B6.mem_conjSub] at hx
    have hw : h⁻¹ * x * h ∈ X ⊔ V := Subgroup.mem_sup_right hx
    have := (Subgroup.mem_normalizer_iff.mp (hJY c.hhI) _).mp hw
    simpa [mul_assoc] using this
  have hJeq : X ⊔ V = J := le_antisymm (sup_le hXJ (le_sup_left : V ≤ J)) hJle
  have hTI : T ≤ Subgroup.normalizer (J : Set G) := by
    rw [← hJeq]
    intro t ht
    have h1 := hTX ht
    have h2 := c.hTV ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
    show (X ⊔ V).map _ = X ⊔ V
    rw [Subgroup.map_sup, h1, h2]
  exact ⟨hTI, hTI.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)⟩

end SixB1

end CFSG.Quasithin.H13
