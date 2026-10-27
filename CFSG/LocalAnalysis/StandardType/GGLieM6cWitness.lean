module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeModel

public section

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three
  CFSG.StandardType.TableBExc.Three

abbrev SylowModelE6 := Model piE7 piE7_pow_three

local instance instDecidableEqM6 : DecidableEq SylowModelE6 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    ⟨fun h => SemidirectProduct.ext h.1 h.2,
     fun h => ⟨congrArg SemidirectProduct.left h, congrArg SemidirectProduct.right h⟩⟩

local instance instFintypeM6 : Fintype SylowModelE6 :=
  Fintype.ofEquiv _ SemidirectProduct.equivProd.symm

local instance instFiniteM6 : Finite SylowModelE6 := Finite.of_fintype SylowModelE6

local instance instFiniteSub (H : Subgroup SylowModelE6) : Finite ↥H :=
  Finite.of_injective (Subtype.val : ↥H → SylowModelE6) Subtype.coe_injective

private def m6c_mkE (v0 v1 v2 m : ZMod 3) : SylowModelE6 :=
  ⟨Multiplicative.ofAdd ![v0, v1, v2], Multiplicative.ofAdd m⟩

private def m6c_pairSub (s t : SylowModelE6) : Finset SylowModelE6 :=
  Finset.univ.image fun p : Fin 3 × Fin 3 => s ^ (p.1 : ℕ) * t ^ (p.2 : ℕ)

private def m6c_wordOf (y : SylowModelE6) : List (Fin Tag.E6.rank) :=
  nfWordE6 ((y.left.toAdd 0).val) ((y.left.toAdd 1).val) ((y.left.toAdd 2).val) ++
    (List.replicate ((y.right.toAdd).val) wordE6C).flatten

private def m6c_adjVec (x : Fin Tag.E6.rank → ZMod 3) : Fin Tag.E6.rank → ℤ :=
  Tag.E6.cartan.adjugate.mulVec fun i => (((x i).val : ℕ) : ℤ)

private structure goodEntry where
  H : Finset SylowModelE6
  sg : SylowModelE6
  tg : SylowModelE6
  a : SylowModelE6
  x : Fin Tag.E6.rank → ZMod 3

private def goodTable : List goodEntry :=
  [ ⟨m6c_pairSub (m6c_mkE 0 0 0 1) (m6c_mkE 0 0 0 1), m6c_mkE 0 0 0 1, m6c_mkE 0 0 0 1,
      m6c_mkE 0 0 0 1, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 1 0) (m6c_mkE 0 1 1 0), m6c_mkE 0 1 1 0, m6c_mkE 0 1 1 0,
      m6c_mkE 0 1 1 0, ![0,1,0,0,2,2]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 2 0) (m6c_mkE 0 1 2 0), m6c_mkE 0 1 2 0, m6c_mkE 0 1 2 0,
      m6c_mkE 0 1 2 0, ![0,1,0,0,1,1]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 2 1) (m6c_mkE 0 1 2 1), m6c_mkE 0 1 2 1, m6c_mkE 0 1 2 1,
      m6c_mkE 0 1 2 1, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 2 2) (m6c_mkE 0 1 2 2), m6c_mkE 0 1 2 2, m6c_mkE 0 1 2 2,
      m6c_mkE 0 1 2 2, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 2 1 1) (m6c_mkE 0 2 1 1), m6c_mkE 0 2 1 1, m6c_mkE 0 2 1 1,
      m6c_mkE 0 2 1 1, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 2 1 2) (m6c_mkE 0 2 1 2), m6c_mkE 0 2 1 2, m6c_mkE 0 2 1 2,
      m6c_mkE 0 2 1 2, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 0 1 0) (m6c_mkE 1 0 1 0), m6c_mkE 1 0 1 0, m6c_mkE 1 0 1 0,
      m6c_mkE 1 0 1 0, ![1,2,1,0,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 0 2 0) (m6c_mkE 1 0 2 0), m6c_mkE 1 0 2 0, m6c_mkE 1 0 2 0,
      m6c_mkE 1 0 2 0, ![1,1,1,0,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 0 2 2) (m6c_mkE 1 0 2 2), m6c_mkE 1 0 2 2, m6c_mkE 1 0 2 2,
      m6c_mkE 1 0 2 2, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 1 0 0) (m6c_mkE 1 1 0 0), m6c_mkE 1 1 0 0, m6c_mkE 1 1 0 0,
      m6c_mkE 1 1 0 0, ![1,0,1,0,2,2]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 1 1 0) (m6c_mkE 1 1 1 0), m6c_mkE 1 1 1 0, m6c_mkE 1 1 1 0,
      m6c_mkE 1 1 1 0, ![0,1,0,0,2,2]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 1 1 1) (m6c_mkE 1 1 1 1), m6c_mkE 1 1 1 1, m6c_mkE 1 1 1 1,
      m6c_mkE 1 1 1 1, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 1 1 2) (m6c_mkE 1 1 1 2), m6c_mkE 1 1 1 2, m6c_mkE 1 1 1 2,
      m6c_mkE 1 1 1 2, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 1 2 0) (m6c_mkE 1 1 2 0), m6c_mkE 1 1 2 0, m6c_mkE 1 1 2 0,
      m6c_mkE 1 1 2 0, ![0,1,0,0,1,1]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 2 0 0) (m6c_mkE 1 2 0 0), m6c_mkE 1 2 0 0, m6c_mkE 1 2 0 0,
      m6c_mkE 1 2 0 0, ![1,0,1,0,1,1]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 2 1 0) (m6c_mkE 1 2 1 0), m6c_mkE 1 2 1 0, m6c_mkE 1 2 1 0,
      m6c_mkE 1 2 1 0, ![0,1,0,0,1,1]⟩,
    ⟨m6c_pairSub (m6c_mkE 1 2 2 0) (m6c_mkE 1 2 2 0), m6c_mkE 1 2 2 0, m6c_mkE 1 2 2 0,
      m6c_mkE 1 2 2 0, ![0,1,0,0,2,2]⟩,
    ⟨m6c_pairSub (m6c_mkE 2 0 1 2) (m6c_mkE 2 0 1 2), m6c_mkE 2 0 1 2, m6c_mkE 2 0 1 2,
      m6c_mkE 2 0 1 2, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 0 0 1) (m6c_mkE 1 1 1 0), m6c_mkE 0 0 0 1, m6c_mkE 1 1 1 0,
      m6c_mkE 0 0 0 1, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 1 0) (m6c_mkE 1 0 1 0), m6c_mkE 0 1 1 0, m6c_mkE 1 0 1 0,
      m6c_mkE 0 1 1 0, ![1,2,1,0,1,1]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 1 0) (m6c_mkE 1 0 2 0), m6c_mkE 0 1 1 0, m6c_mkE 1 0 2 0,
      m6c_mkE 0 1 1 0, ![1,1,1,0,2,2]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 2 0) (m6c_mkE 1 0 1 0), m6c_mkE 0 1 2 0, m6c_mkE 1 0 1 0,
      m6c_mkE 0 1 2 0, ![1,2,1,0,2,2]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 2 0) (m6c_mkE 1 0 2 0), m6c_mkE 0 1 2 0, m6c_mkE 1 0 2 0,
      m6c_mkE 0 1 2 0, ![1,1,1,0,1,1]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 2 1) (m6c_mkE 0 2 1 2), m6c_mkE 0 1 2 1, m6c_mkE 0 2 1 2,
      m6c_mkE 0 1 2 1, ![0,0,0,1,0,0]⟩,
    ⟨m6c_pairSub (m6c_mkE 0 1 2 2) (m6c_mkE 0 2 1 1), m6c_mkE 0 1 2 2, m6c_mkE 0 2 1 1,
      m6c_mkE 0 1 2 2, ![0,0,0,1,0,0]⟩ ]

private abbrev validEntry (e : goodEntry) : Prop :=
  e.a ∈ e.H ∧
    adWord Tag.E6 3 (m6c_wordOf e.sg) e.x = e.x ∧
    adWord Tag.E6 3 (m6c_wordOf e.tg) e.x = e.x ∧
    ∃ l : Fin Tag.E6.rank,
      ¬ (9 : ℤ) ∣ wordAct Tag.E6 (m6c_wordOf e.a) (m6c_adjVec e.x) l - m6c_adjVec e.x l

private def hasEntry (H : Finset SylowModelE6) : Bool := goodTable.any fun e => decide (e.H = H)

private theorem m6c_allValid : goodTable.all (fun e => decide (validEntry e)) = true := by
  decide +kernel

private theorem m6c_classification :
    ∀ s t : SylowModelE6, s ^ 3 = 1 → t ^ 3 = 1 → s * t = t * s → s ≠ 1 →
      (∀ i : Fin 3,
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i 1)) ∉ m6c_pairSub s t) →
      hasEntry (m6c_pairSub s t) = true := by
  decide +kernel

private theorem goodTable_H :
    goodTable.all (fun e => decide (e.H = m6c_pairSub e.sg e.tg)) = true := by
  decide +kernel

private theorem hasEntry_sound {H : Finset SylowModelE6} (h : hasEntry H = true) :
    ∃ e ∈ goodTable, e.H = H := by
  rw [hasEntry, List.any_eq_true] at h
  obtain ⟨e, he, hh⟩ := h
  exact ⟨e, he, of_decide_eq_true hh⟩

private theorem allValid_sound : ∀ e ∈ goodTable, validEntry e := by
  have h := m6c_allValid
  rw [List.all_eq_true] at h
  intro e he
  exact of_decide_eq_true (h e he)

private theorem goodTable_H_sound : ∀ e ∈ goodTable, e.H = m6c_pairSub e.sg e.tg := by
  have h := goodTable_H
  rw [List.all_eq_true] at h
  intro e he
  exact of_decide_eq_true (h e he)

private theorem pairSub_subset_closure (s t : SylowModelE6) :
    (↑(m6c_pairSub s t) : Set SylowModelE6) ⊆ ↑(Subgroup.closure ({s, t} : Set SylowModelE6)) := by
  intro x hx
  rw [m6c_pairSub, Finset.mem_coe, Finset.mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
    (pow_mem (Subgroup.subset_closure (by simp)) _)

private theorem modelHomE6_wordOf (y : SylowModelE6) :
    modelHomE6 y = (coxeterSystem .E6).wordProd (m6c_wordOf y) := by
  change modelHom isModel_E6 y = (coxeterSystem .E6).wordProd (m6c_wordOf y)
  rw [modelHom_apply isModel_E6 y]
  change modelN isModel_E6 y.left * cE6 ^ (y.right.toAdd).val =
    (coxeterSystem .E6).wordProd (m6c_wordOf y)
  rw [show modelN isModel_E6 y.left = modelHomE6 (SemidirectProduct.inl y.left) from
      (modelHom_inl isModel_E6 y.left).symm, modelHomE6_inl, m6c_wordOf,
    CoxeterSystem.wordProd_append, wordProd_replicate, cE6]

private theorem modelHomE6_smul_wordOf (y : SylowModelE6) (v : Fin Tag.E6.rank → ℤ) :
    modelHomE6 y • v = wordAct Tag.E6 (m6c_wordOf y) v := by
  rw [modelHomE6_wordOf, CFSG.StandardType.TableBExc.wordProd_smul]

private theorem adAct_modelHomE6_wordOf (y : SylowModelE6) (x : Fin Tag.E6.rank → ZMod 3) :
    adAct Tag.E6 3 (modelHomE6 y) x = adWord Tag.E6 3 (m6c_wordOf y) x := by
  rw [modelHomE6_wordOf, adWord_eq_adAct]

private theorem m6c_modelHomE6_single (i : Fin 3) :
    modelHomE6 (SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i 1))) = gE6 i := by
  rw [gE6, modelHomE6, modelHom_inl, modelN_single, ZMod.val_one, pow_one]
  fin_cases i <;> rfl

private def modelStab (x : Fin Tag.E6.rank → ZMod 3) : Subgroup SylowModelE6 where
  carrier := {y | adAct Tag.E6 3 (modelHomE6 y) x = x}
  one_mem' := by
    show adAct Tag.E6 3 (modelHomE6 1) x = x
    rw [map_one, adAct_one]
  mul_mem' := by
    intro y z hy hz
    change adAct Tag.E6 3 (modelHomE6 y) x = x at hy
    change adAct Tag.E6 3 (modelHomE6 z) x = x at hz
    show adAct Tag.E6 3 (modelHomE6 (y * z)) x = x
    rw [map_mul, adAct_mul, hz, hy]
  inv_mem' := by
    intro y hy
    change adAct Tag.E6 3 (modelHomE6 y) x = x at hy
    show adAct Tag.E6 3 (modelHomE6 y⁻¹) x = x
    have h : adAct Tag.E6 3 (modelHomE6 y⁻¹) (adAct Tag.E6 3 (modelHomE6 y) x) = x := by
      rw [← adAct_mul, ← map_mul, inv_mul_cancel, map_one, adAct_one]
    rw [hy] at h
    exact h

private theorem eq_nine_of_dvd_81 {n : ℕ} (h : n ∣ 3 ^ 4) (hgt : 3 < n) (hle : n ≤ 9) : n = 9 := by
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h
  rw [hk'] at hgt hle ⊢
  interval_cases k
  · norm_num at hgt
  · norm_num at hgt
  · norm_num
  · norm_num at hle
  · norm_num at hle

private theorem m6c_card_le_nine (A' : Subgroup SylowModelE6) (hA' : IsElemAbelian 3 A')
    (hA'1 : A' ≠ ⊥)
    (hgood : ∀ i : Fin 3,
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i 1)) ∉ A') :
    Nat.card A' ≤ 9 := by
  have hcardN : Nat.card (SemidirectProduct.inl :
      Multiplicative (Fin 3 → ZMod 3) →* SylowModelE6).range = 3 ^ 3 := card_range_inl
  by_cases hN : A' ≤ (SemidirectProduct.inl :
      Multiplicative (Fin 3 → ZMod 3) →* SylowModelE6).range
  · have hdvd3 : Nat.card A' ∣ 3 ^ 3 := by
      rw [← hcardN]
      exact Subgroup.card_dvd_of_le hN
    have hle27 : Nat.card A' ≤ 3 ^ 3 := by
      calc Nat.card A' ≤ Nat.card (SemidirectProduct.inl :
              Multiplicative (Fin 3 → ZMod 3) →* SylowModelE6).range := Subgroup.card_le_of_le hN
        _ = 3 ^ 3 := hcardN
    have hne : Nat.card A' ≠ 3 ^ 3 := by
      intro h
      have heq : A' = (SemidirectProduct.inl :
          Multiplicative (Fin 3 → ZMod 3) →* SylowModelE6).range :=
        Subgroup.eq_of_le_of_card_ge hN (by rw [hcardN, h])
      exact hgood 0 (by rw [heq]; exact ⟨Multiplicative.ofAdd (Pi.single 0 1), rfl⟩)
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd3
    rw [hk'] at hne hle27 ⊢
    interval_cases k
    · norm_num
    · norm_num
    · norm_num
    · norm_num at hne
  · have hex : ∃ y ∈ A', y ∉ (SemidirectProduct.inl :
        Multiplicative (Fin 3 → ZMod 3) →* SylowModelE6).range := by
      by_contra h
      apply hN
      intro x hx
      by_contra hxN
      exact h ⟨x, hx, hxN⟩
    obtain ⟨y, hyA, hyN⟩ := hex
    have hyr : y.right ≠ 1 := by
      intro h
      apply hyN
      rw [SemidirectProduct.range_inl_eq_ker_rightHom, MonoidHom.mem_ker,
        SemidirectProduct.rightHom_eq_right]
      exact h
    obtain ⟨y₁, hy₁A, hy₁r⟩ := exists_right_eq_ofAdd_one hyA hyr
    have hAc : ∀ y ∈ A', ∀ z ∈ A', y * z = z * y :=
      fun y hy z hz => TableB.IsElemAbelian.comm hA' hy hz
    have h := card_le_of_right_eq (π := piE7) (hπ := piE7_pow_three) hAc hy₁A hy₁r
      (K₁ := 3) card_fixShift_E7
    omega

private theorem eq_closure_of_indep (A' : Subgroup SylowModelE6) {s t : SylowModelE6} (hsA : s ∈ A')
    (htA : t ∈ A')
    (hs3 : s ^ 3 = 1) (hs1 : s ≠ 1) (htnotin : t ∉ Subgroup.zpowers s)
    (hcard : Nat.card A' ≤ 9) :
    A' = Subgroup.closure ({s, t} : Set SylowModelE6) := by
  have hcl_le : Subgroup.closure ({s, t} : Set SylowModelE6) ≤ A' :=
    (Subgroup.closure_le _).mpr (by
      intro x hx
      rcases hx with rfl | rfl
      · exact hsA
      · exact htA)
  have hcardM6 : Nat.card SylowModelE6 = 81 := by rw [card_model]; norm_num
  have hcardzp : Nat.card (Subgroup.zpowers s) = 3 := by
    have hdvd : Nat.card (Subgroup.zpowers s) ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_iff_pow_eq_one.mpr hs3
    have hne1 : Nat.card (Subgroup.zpowers s) ≠ 1 := by
      rw [Nat.card_zpowers]
      exact fun h => hs1 (orderOf_eq_one_iff.mp h)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hle : Subgroup.zpowers s ≤ Subgroup.closure ({s, t} : Set SylowModelE6) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hne : Subgroup.zpowers s ≠ Subgroup.closure ({s, t} : Set SylowModelE6) := by
    intro h
    apply htnotin
    rw [h]
    exact Subgroup.subset_closure (by simp)
  have hcardcl_dvd : Nat.card (Subgroup.closure ({s, t} : Set SylowModelE6)) ∣ 3 ^ 4 := by
    calc Nat.card (Subgroup.closure ({s, t} : Set SylowModelE6)) ∣ Nat.card SylowModelE6 :=
          Subgroup.card_subgroup_dvd_card _
      _ = 3 ^ 4 := by rw [hcardM6]; norm_num
  have hcardcl_le9 : Nat.card (Subgroup.closure ({s, t} : Set SylowModelE6)) ≤ 9 :=
    le_trans (Subgroup.card_le_of_le hcl_le) hcard
  have hgt : 3 < Nat.card (Subgroup.closure ({s, t} : Set SylowModelE6)) := by
    have hlt : Nat.card (Subgroup.zpowers s) <
        Nat.card (Subgroup.closure ({s, t} : Set SylowModelE6)) :=
      lt_of_le_of_ne (Subgroup.card_le_of_le hle) (fun h =>
        hne (Subgroup.eq_of_le_of_card_ge hle h.ge))
    rwa [hcardzp] at hlt
  have hcard9 := eq_nine_of_dvd_81 hcardcl_dvd hgt hcardcl_le9
  exact (Subgroup.eq_of_le_of_card_ge hcl_le (by rw [hcard9]; exact hcard)).symm

theorem exists_pairing_witness
    (A : Subgroup (WeylGroup Tag.E6)) (hAS : A ≤ modelHomE6.range) (hA : IsElemAbelian 3 A)
    (hA1 : A ≠ ⊥) (hg : ∀ i, gE6 i ∉ A) :
    ∃ a ∈ A, ∃ x : Fin Tag.E6.rank → ZMod 3, (∀ a' ∈ A, adAct Tag.E6 3 a' x = x) ∧
      ∃ l, ¬ ((9 : ℤ) ∣
        (a • (Tag.E6.cartan.adjugate.mulVec fun i => (((x i).val : ℕ) : ℤ))) l -
          (Tag.E6.cartan.adjugate.mulVec fun i => (((x i).val : ℕ) : ℤ)) l) := by
  classical
  let A' : Subgroup SylowModelE6 := A.comap modelHomE6
  have hmap : A'.map modelHomE6 = A := Subgroup.map_comap_eq_self hAS
  have hA' : IsElemAbelian 3 A' := by
    refine ⟨⟨⟨fun a b => Subtype.ext (modelHomE6_injective ?_)⟩⟩,
      fun x hx => modelHomE6_injective ?_⟩
    · simpa only [Subgroup.coe_mul, map_mul] using TableB.IsElemAbelian.comm hA a.2 b.2
    · simpa only [map_pow, map_one] using hA.2 (modelHomE6 x) hx
  have hA'1 : A' ≠ ⊥ := by
    intro h
    exact hA1 (by rw [← hmap, h, Subgroup.map_bot])
  have hgood' : ∀ i : Fin 3,
      SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i 1)) ∉ A' := by
    intro i hmem
    exact hg i (by
      rw [← hmap, ← m6c_modelHomE6_single i]
      exact Subgroup.mem_map_of_mem _ hmem)
  obtain ⟨⟨s, hsA⟩, hs1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA'1
  have hs1 : s ≠ 1 := fun h => hs1' (Subtype.ext h)
  have hs3 : s ^ 3 = 1 := hA'.2 s hsA
  have finish : ∀ t : SylowModelE6, t ∈ A' → A' = Subgroup.closure ({s, t} : Set SylowModelE6) →
      ∃ a ∈ A, ∃ x : Fin Tag.E6.rank → ZMod 3, (∀ a' ∈ A, adAct Tag.E6 3 a' x = x) ∧
        ∃ l, ¬ ((9 : ℤ) ∣
          (a • (Tag.E6.cartan.adjugate.mulVec fun i => (((x i).val : ℕ) : ℤ))) l -
            (Tag.E6.cartan.adjugate.mulVec fun i => (((x i).val : ℕ) : ℤ)) l) := by
    intro t htA hA'eq
    have ht3 : t ^ 3 = 1 := hA'.2 t htA
    have hcomm : s * t = t * s := TableB.IsElemAbelian.comm hA' hsA htA
    have hgood'' : ∀ i : Fin 3,
        SemidirectProduct.inl (Multiplicative.ofAdd (Pi.single i 1)) ∉ m6c_pairSub s t := by
      intro i hmem
      exact hgood' i (by rw [hA'eq]; exact pairSub_subset_closure s t hmem)
    have hcl := m6c_classification s t hs3 ht3 hcomm hs1 hgood''
    obtain ⟨e, heT, heH⟩ := hasEntry_sound hcl
    have hv := allValid_sound e heT
    have hH := goodTable_H_sound e heT
    set x : Fin Tag.E6.rank → ZMod 3 := e.x with hx
    have hfix_sg : adAct Tag.E6 3 (modelHomE6 e.sg) x = x := by
      rw [adAct_modelHomE6_wordOf]; exact hv.2.1
    have hfix_tg : adAct Tag.E6 3 (modelHomE6 e.tg) x = x := by
      rw [adAct_modelHomE6_wordOf]; exact hv.2.2.1
    have hstab_gen : Subgroup.closure ({e.sg, e.tg} : Set SylowModelE6) ≤ modelStab x :=
      (Subgroup.closure_le _).mpr (by
        intro y hy
        rcases hy with rfl | rfl
        · exact hfix_sg
        · exact hfix_tg)
    have hs_pair : s ∈ m6c_pairSub s t := by
      rw [m6c_pairSub, Finset.mem_image]
      exact ⟨(1, 0), Finset.mem_univ _, by simp⟩
    have ht_pair : t ∈ m6c_pairSub s t := by
      rw [m6c_pairSub, Finset.mem_image]
      exact ⟨(0, 1), Finset.mem_univ _, by simp⟩
    have hs_mem : s ∈ modelStab x :=
      hstab_gen (pairSub_subset_closure e.sg e.tg (by rw [← hH, heH]; exact hs_pair))
    have ht_mem : t ∈ modelStab x :=
      hstab_gen (pairSub_subset_closure e.sg e.tg (by rw [← hH, heH]; exact ht_pair))
    have hA'le : A' ≤ modelStab x := by
      rw [hA'eq]
      exact (Subgroup.closure_le _).mpr (by
        intro y hy
        rcases hy with rfl | rfl
        · exact hs_mem
        · exact ht_mem)
    have hv1 : e.a ∈ e.H := hv.1
    have hea : e.a ∈ A' := by
      rw [hA'eq]
      exact pairSub_subset_closure s t (by rw [heH] at hv1; exact hv1)
    refine ⟨modelHomE6 e.a, ?_, x, ?_, ?_⟩
    · rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hea
    · intro a' ha'
      rw [← hmap] at ha'
      obtain ⟨y, hyA, rfl⟩ := ha'
      have hh := hA'le hyA
      change adAct Tag.E6 3 (modelHomE6 y) x = x at hh
      exact hh
    · obtain ⟨l, hl⟩ := hv.2.2.2
      refine ⟨l, ?_⟩
      change ¬ (9 : ℤ) ∣ (modelHomE6 e.a • m6c_adjVec x) l - m6c_adjVec x l
      rw [modelHomE6_smul_wordOf e.a (m6c_adjVec x)]
      exact hl
  by_cases hle : A' ≤ Subgroup.zpowers s
  · have hA'eq : A' = Subgroup.closure ({s, s} : Set SylowModelE6) := by
      rw [show ({s, s} : Set SylowModelE6) = {s} from by ext y; simp]
      refine le_antisymm ?_ ((Subgroup.closure_le _).mpr ?_)
      · exact le_trans hle (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
      · intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hsA
    exact finish s hsA hA'eq
  · have hex : ∃ t ∈ A', t ∉ Subgroup.zpowers s := by
      by_contra h
      apply hle
      intro y hy
      by_contra hy'
      exact h ⟨y, hy, hy'⟩
    obtain ⟨t, htA, htnotin⟩ := hex
    have hA'eq : A' = Subgroup.closure ({s, t} : Set SylowModelE6) :=
      eq_closure_of_indep A' hsA htA hs3 hs1 htnotin (m6c_card_le_nine A' hA' hA'1 hgood')
    exact finish t htA hA'eq

end CFSG.StandardType.LieCore.M6c
