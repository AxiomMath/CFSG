module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34DCTransport
public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtend
import CFSG.Quasithin.Recognition.St84.Gen.U4qModel
import CFSG.Quasithin.Recognition.St84.Gen.L3qAmalExtend
import CFSG.Quasithin.Recognition.St84.Gen.SL2Semilinear
import CFSG.Quasithin.Recognition.St84.Gen.U4qVFact

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.H13.U4Par
open CFSG.GH74.QTGen4.DSGen4.L34
open CFSG.Quasithin.H13.Sec53F.Unit (fieldAut)

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

private theorem preserves_symm_u4 {Γ : Type*} [Group Γ] (τ : MulAut Γ) {P : Γ → Prop}
    (hτ : ∀ b, P b ↔ P (τ b)) (b : Γ) : P b ↔ P (τ.symm b) := by
  have e := hτ (τ.symm b)
  rw [MulEquiv.apply_symm_apply] at e
  exact e.symm

private theorem iff_of_map_eq_u4 {Γ : Type*} [Group Γ] (τ : MulAut Γ) {S : Subgroup Γ}
    (hS : S.map τ.toMonoidHom = S) (b : Γ) : b ∈ S ↔ τ b ∈ S := by
  constructor
  · intro hb
    rw [← hS]
    exact Subgroup.mem_map_of_mem _ hb
  · intro hb
    rw [← hS] at hb
    obtain ⟨b', hb', he⟩ := Subgroup.mem_map.mp hb
    simp only [MulEquiv.coe_toMonoidHom] at he
    rw [← τ.injective he]
    exact hb'

private theorem exists_addEquiv_u4 {Γ : Type*} [Group Γ] {A : Type*} [AddGroup A] [Finite A]
    (f : A → Γ) (hf_add : ∀ a b, f (a + b) = f a * f b) (hf_inj : Function.Injective f)
    (τ : MulAut Γ) (hτ : ∀ a, ∃ b, τ (f a) = f b) : ∃ l : A ≃+ A, ∀ a, τ (f a) = f (l a) := by
  choose l hl using hτ
  have hadd : ∀ a b, l (a + b) = l a + l b := by
    intro a b
    apply hf_inj
    have e1 : f (l (a + b)) = f (l a) * f (l b) := by
      rw [← hl, ← hl, ← hl, hf_add, map_mul]
    rw [e1, hf_add]
  have hinj : Function.Injective l := by
    intro a b hab
    apply hf_inj
    apply τ.injective
    rw [hl, hl, hab]
  exact ⟨AddEquiv.ofBijective (AddMonoidHom.mk' l hadd)
    ⟨hinj, Finite.injective_iff_surjective.mp hinj⟩, hl⟩

private noncomputable abbrev bU (h : UnitaryFieldData 2 m K) : Subgroup ↥(parP h ⊓ parP2 h) :=
  (hypUnitriangular h 2 0).subgroupOf (parP h ⊓ parP2 h)

private noncomputable abbrev bT (h : UnitaryFieldData 2 m K) : Subgroup ↥(parP h ⊓ parP2 h) :=
  (hypTorus h 2 0).subgroupOf (parP h ⊓ parP2 h)

private theorem inf_le_normalizer_u4 :
    parP h ⊓ parP2 h ≤ Subgroup.normalizer (hypUnitriangular h 2 0 : Set (hypSU h 2 0)) := by
  intro b hb
  rw [parP_inf_parP2_eq_u4 h] at hb
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · exact CFSG.RankThree.CentralLiftU.conj_mem_hypUnitriangular_of_mem_hypBorel (by norm_num) hb
  · intro hu
    have := CFSG.RankThree.CentralLiftU.conj_mem_hypUnitriangular_of_mem_hypBorel (by norm_num)
      ((hypBorel h 2 0).inv_mem hb) hu
    simpa [mul_assoc] using this

private theorem bU_normal : (bU h).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (hypUnitriangular_le_inf_u4 h)).mpr
    (inf_le_normalizer_u4 h)

private theorem bU_isPGroup : IsPGroup 2 (bU h) :=
  (isSylowTwoOf_hypUnitriangular h).2.1.of_equiv
    (Subgroup.subgroupOfEquivOfLe (hypUnitriangular_le_inf_u4 h)).symm

private theorem bU_disjoint : Disjoint (bU h) (bT h) := by
  rw [Subgroup.disjoint_def]
  intro x hxU hxH
  apply Subtype.ext
  have hx : (x : hypSU h 2 0) ∈ hypUnitriangular h 2 0 ⊓ hypTorus h 2 0 :=
    ⟨Subgroup.mem_subgroupOf.mp hxU, Subgroup.mem_subgroupOf.mp hxH⟩
  rw [CFSG.RankThree.CentralLiftU.hypUnitriangular_inf_hypTorus] at hx
  exact Subgroup.mem_bot.mp hx

private theorem bU_sup_bT : bU h ⊔ bT h = ⊤ := by
  have hBsup : parP h ⊓ parP2 h = hypUnitriangular h 2 0 ⊔ hypTorus h 2 0 := by
    refine le_antisymm ?_ (sup_le (hypUnitriangular_le_inf_u4 h) (hypTorus_le_inf_u4 h))
    rw [parP_inf_parP2_eq_u4 h]
    exact CFSG.RankThree.CentralLiftU.hypBorel_le_sup (by norm_num) (by norm_num)
  rw [← Subgroup.subgroupOf_sup (hypUnitriangular_le_inf_u4 h) (hypTorus_le_inf_u4 h), ← hBsup,
    Subgroup.subgroupOf_self]

private theorem bU_isComplement' : (bU h).IsComplement' (bT h) := by
  haveI := bU_normal h
  exact Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (bU_disjoint h) (by
    rw [← Subgroup.normal_mul, bU_sup_bT h]
    simp)

private theorem odd_card_hypTorus_u4 : Odd (Nat.card (hypTorus h 2 0)) := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have := h.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  obtain ⟨q, hq⟩ := exists_diag_of_mem_hypTorus_u4 h x.2
  have hx2 : (x : hypSU h 2 0) * x = 1 := by
    have e := pow_orderOf_eq_one x
    rw [hx, pow_two] at e
    exact congrArg Subtype.val e
  have hq1 : ∀ i, q i = 1 := by
    intro i
    have e := congrFun (congrFun
      (congrArg (fun z : hypSU h 2 0 => ((z : GL Ix K) : Matrix Ix Ix K)) hx2) i) i
    simp only [coe_mul_hypSU, hq, diagonal_mul_diagonal, diagonal_apply_eq] at e
    have e' : q i ^ 2 = 1 ^ 2 := by
      rw [sq, e, one_pow]
      simp
    exact CharTwo.sq_inj.mp e'
  have hx1 : x = 1 := by
    apply Subtype.ext
    apply hypSU_ext h
    rw [hq, show q = fun _ => 1 from funext hq1, diagonal_one]
    rfl
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

private theorem odd_card_bT : Odd (Nat.card (bT h)) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hypTorus_le_inf_u4 h)).toEquiv]
  exact odd_card_hypTorus_u4 h

private theorem preserves_hypUnitriangular_u4 (σ : MulAut ↥(parP h ⊓ parP2 h))
    (b : ↥(parP h ⊓ parP2 h)) :
    (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0 ↔
      ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypUnitriangular h 2 0 := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hn : (bU h).Normal := bU_normal h
  have hidx : ¬ 2 ∣ (bU h).index := by
    rw [(bU_isComplement' h).symm.index_eq_card]
    exact (odd_card_bT h).not_two_dvd_nat
  let S : Sylow 2 ↥(parP h ⊓ parP2 h) := (bU_isPGroup h).toSylow hidx
  have hS : (S : Subgroup ↥(parP h ⊓ parP2 h)) = bU h := rfl
  have key : ∀ τ : MulAut ↥(parP h ⊓ parP2 h), (bU h).map τ.toMonoidHom ≤ bU h := by
    intro τ
    haveI : ((bU h).map τ.toMonoidHom).Normal := hn.map τ.toMonoidHom τ.surjective
    have hp : IsPGroup 2 ((bU h).map τ.toMonoidHom) := (bU_isPGroup h).map τ.toMonoidHom
    rw [← hS]
    exact hp.le_sylow_of_normal S
  constructor
  · intro hb
    exact Subgroup.mem_subgroupOf.mp (key σ ⟨b, Subgroup.mem_subgroupOf.mpr hb, rfl⟩)
  · intro hb
    have e := key σ.symm (x := b) ⟨σ b, Subgroup.mem_subgroupOf.mpr hb, by simp⟩
    exact Subgroup.mem_subgroupOf.mp e

private theorem exists_conj_torus_u4 (σ : MulAut ↥(parP h ⊓ parP2 h)) :
    ∃ e : ↥(parP h ⊓ parP2 h), (e : hypSU h 2 0) ∈ hypUnitriangular h 2 0 ∧
      ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ hypTorus h 2 0 ↔
        (((MulAut.conj e * σ) b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypTorus h 2 0 := by
  haveI := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  haveI : (bU h).Normal := bU_normal h
  have hσU : (bU h).map σ.toMonoidHom = bU h := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        ((preserves_hypUnitriangular_u4 h σ y).mp (Subgroup.mem_subgroupOf.mp hy))
    · intro hx
      refine ⟨σ.symm x, ?_, by simp⟩
      exact Subgroup.mem_subgroupOf.mpr ((preserves_symm_u4 σ
        (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0)
        (preserves_hypUnitriangular_u4 h σ) x).mp (Subgroup.mem_subgroupOf.mp hx))
  let Y : Subgroup ↥(parP h ⊓ parP2 h) := (bT h).map σ.toMonoidHom
  have hEY : Disjoint (bU h) Y := by
    have e := congrArg (fun S : Subgroup ↥(parP h ⊓ parP2 h) => S.map σ.toMonoidHom)
      (disjoint_iff.mp (bU_disjoint h))
    rw [Subgroup.map_inf _ _ _ σ.injective, hσU, Subgroup.map_bot] at e
    exact disjoint_iff.mpr e
  have htop2 : bU h ⊔ Y = ⊤ := by
    have htopσ : (⊤ : Subgroup ↥(parP h ⊓ parP2 h)).map σ.toMonoidHom = ⊤ := by
      rw [Subgroup.map_top, MonoidHom.range_eq_top]
      exact σ.surjective
    have e := congrArg (fun S : Subgroup ↥(parP h ⊓ parP2 h) => S.map σ.toMonoidHom)
      (bU_sup_bT h)
    rw [Subgroup.map_sup, hσU, htopσ] at e
    exact e
  have hcompY : (bU h).IsComplement' Y :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hEY (by
      rw [← Subgroup.normal_mul, htop2]
      simp)
  have hBsolv : Group.IsSolvable ↥(parP h ⊓ parP2 h) :=
    CFSG.Quasithin.F112R.isSolvable_parP_inf_parP2 h
  let π : Set Nat.Primes := {p | p.val ≠ 2}
  have hoddY : Odd (Nat.card Y) := by
    rw [Subgroup.card_map_of_injective σ.injective]
    exact odd_card_bT h
  have hUp := bU_isPGroup h
  have hHall : ∀ W : Subgroup ↥(parP h ⊓ parP2 h), Odd (Nat.card W) →
      (bU h).IsComplement' W → CFSG.IsHallSubgroup π W := by
    intro W hW hcW
    refine CFSG.isHallSubgroup_of π W ?_ ?_
    · intro p hp
      have hpodd : Odd p.val := hW.of_dvd_nat hp
      intro h2
      rw [h2] at hpodd
      exact (by decide : ¬ Odd 2) hpodd
    · intro p hp hpdvd
      rw [hcW.index_eq_card] at hpdvd
      obtain ⟨k, hk⟩ := hUp.exists_card_eq
      rw [hk] at hpdvd
      exact hp ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow p.property hpdvd))
  obtain ⟨g, hg⟩ := CFSG.exists_conj_eq_of_isHallSubgroup_of_solvable hBsolv
    (hHall Y hoddY hcompY) (hHall (bT h) (odd_card_bT h) (bU_isComplement' h))
  obtain ⟨⟨uE, yE⟩, huy⟩ := hcompY.2 g
  have huy' : (uE : ↥(parP h ⊓ parP2 h)) * (yE : ↥(parP h ⊓ parP2 h)) = g := by simpa using huy
  have hmap : Y.map (MulAut.conj g).toMonoidHom =
      Y.map (MulAut.conj (uE : ↥(parP h ⊓ parP2 h))).toMonoidHom := by
    have hc : (MulAut.conj g).toMonoidHom =
        (MulAut.conj (uE : ↥(parP h ⊓ parP2 h))).toMonoidHom.comp
          (MulAut.conj (yE : ↥(parP h ⊓ parP2 h))).toMonoidHom := by
      ext x
      simp [← huy', MulAut.conj_apply, mul_assoc]
    have hyY : Y.map (MulAut.conj (yE : ↥(parP h ⊓ parP2 h))).toMonoidHom = Y :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer yE.2)
    rw [hc, ← Subgroup.map_map, hyY]
  have hτ : (bT h).map (MulAut.conj (uE : ↥(parP h ⊓ parP2 h)) * σ).toMonoidHom = bT h := by
    have hcomp : (MulAut.conj (uE : ↥(parP h ⊓ parP2 h)) * σ).toMonoidHom =
        (MulAut.conj (uE : ↥(parP h ⊓ parP2 h))).toMonoidHom.comp σ.toMonoidHom := by
      ext x
      rfl
    rw [hcomp, ← Subgroup.map_map, ← hmap]
    exact hg.symm
  refine ⟨uE, Subgroup.mem_subgroupOf.mp uE.2, fun b => ?_⟩
  exact iff_of_map_eq_u4 _ hτ b

private theorem exists_fixed_ne_u4 (hm : 2 ≤ m) : ∃ l : K, h.bar l = l ∧ l ≠ 0 ∧ l ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have := h.finite
  have hsurj : Function.Surjective
      (fun b : Bool => (if b then 1 else 0 : h.fixedField)) := by
    rintro ⟨l, hl⟩
    by_cases h0 : l = 0
    · exact ⟨false, Subtype.ext (by simp [h0])⟩
    · exact ⟨true, Subtype.ext (by simp [hcon l ((h.mem_fixedField).mp hl) h0])⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, h.card_fixedField] at hle
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

include h in
private theorem ne_inv_u4 {l : K} (hl0 : l ≠ 0) (hl1 : l ≠ 1) : l ≠ l⁻¹ := by
  have := h.charP
  intro e
  apply hl1
  have e2 : l ^ 2 = 1 ^ 2 := by
    rw [sq, one_pow]
    nth_rewrite 2 [e]
    exact mul_inv_cancel₀ hl0
  exact CharTwo.sq_inj.mp e2

private theorem comm_symm_u4 (τ : MulAut ↥(parP h ⊓ parP2 h)) (a b : ↥(parP h ⊓ parP2 h))
    (hc : ((τ a : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * (b : hypSU h 2 0) =
      (b : hypSU h 2 0) * ((τ a : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0)) :
    (a : hypSU h 2 0) * ((τ.symm b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) =
      ((τ.symm b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * (a : hypSU h 2 0) := by
  have hcB : τ a * b = b * τ a := Subtype.ext hc
  have e := congrArg τ.symm hcB
  rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at e
  exact congrArg Subtype.val e

private theorem comm_map_u4 (τ : MulAut ↥(parP h ⊓ parP2 h)) (a b : ↥(parP h ⊓ parP2 h))
    (hc : (a : hypSU h 2 0) * (b : hypSU h 2 0) = (b : hypSU h 2 0) * (a : hypSU h 2 0)) :
    ((τ a : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) =
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) *
        ((τ a : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) := by
  have hcB : a * b = b * a := Subtype.ext hc
  have e := congrArg τ hcB
  rw [map_mul, map_mul] at e
  exact congrArg Subtype.val e

private theorem isolate_u4RootB (hm : 2 ≤ m) (τ : MulAut ↥(parP h ⊓ parP2 h))
    (hU : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0 ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypUnitriangular h 2 0)
    (hQ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h)
    (hH : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ hypTorus h 2 0 ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypTorus h 2 0)
    (b : ↥(parP h ⊓ parP2 h)) (hb : (b : hypSU h 2 0) ∈ u4RootB h) :
    ((τ.symm b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ u4RootB h := by
  obtain ⟨l, hlb, hl0, hl1⟩ := exists_fixed_ne_u4 h hm
  obtain ⟨d, hdT, q, hq, e1, e2, e3, e4⟩ :=
    exists_mem_hypTorus_u4 h hl0 one_ne_zero (by rw [mul_one, hlb])
  rw [hlb] at e3
  rw [map_one, inv_one] at e4
  let dB : ↥(parP h ⊓ parP2 h) := ⟨d, hypTorus_le_inf_u4 h hdT⟩
  have hkT := (hH dB).mp hdT
  obtain ⟨qk, hqk⟩ := exists_diag_of_mem_hypTorus_u4 h hkT
  have hk24 : qk ie2 = qk if2 := by
    by_contra hne
    let xB : ↥(parP h ⊓ parP2 h) :=
      ⟨u4xbElt h (map_one h.bar), u4RootB_le_inf h (u4xbElt_mem_u4RootB h (map_one h.bar))⟩
    have hc : (dB : hypSU h 2 0) * (xB : hypSU h 2 0) = (xB : hypSU h 2 0) * (dB : hypSU h 2 0) :=
      comm_of_mem_u4RootB h hq (by rw [e2, e4]) (u4xbElt_mem_u4RootB h (map_one h.bar))
    have hc' := comm_map_u4 h τ dB xB hc
    have hτxU := (hU xB).mp (u4xbElt_mem_hypUnitriangular h (map_one h.bar))
    have hxQ := (hQ xB).mpr (mem_radQ_of_comm_diag h hqk hne hτxU hc')
    obtain ⟨x, y, c, -, hxm⟩ := hxQ
    have e := congrFun (congrFun hxm ie2) if2
    change u4xbMat 1 ie2 if2 = sMat h x y c ie2 if2 at e
    simp [u4xbMat_apply, sMat_apply, one_apply] at e
  have hcb := comm_symm_u4 h τ dB b (comm_of_mem_u4RootB h hqk hk24 hb)
  have hU' := (preserves_symm_u4 τ
    (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0) hU b).mp
    (u4RootB_le_hypUnitriangular h hb)
  refine mem_u4RootB_of_comm_diag h hq ?_ ?_ ?_ hU' hcb
  · rw [e1, e2]
    exact hl1
  · rw [e1, e4]
    exact hl1
  · rw [e1, e3]
    exact ne_inv_u4 h hl0 hl1

private theorem preserves_inf_comm_u4 (τ : MulAut ↥(parP h ⊓ parP2 h))
    {S T : Subgroup (hypSU h 2 0)} (hTB : T ≤ parP h ⊓ parP2 h)
    (hS : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ S ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ S)
    (hT : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ T ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ T)
    (b : ↥(parP h ⊓ parP2 h))
    (hb : (b : hypSU h 2 0) ∈ S ∧ ∀ x ∈ T, (b : hypSU h 2 0) * x = x * b) :
    ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ S ∧
      ∀ x ∈ T, ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * x =
        x * ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) := by
  refine ⟨(hS b).mp hb.1, fun x hx => ?_⟩
  let xB : ↥(parP h ⊓ parP2 h) := ⟨x, hTB hx⟩
  have hx' := (preserves_symm_u4 τ
    (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ T) hT xB).mp hx
  have hc := comm_map_u4 h τ b (τ.symm xB) (hb.2 _ hx')
  rw [MulEquiv.apply_symm_apply] at hc
  exact hc

private theorem preserves_inf_comm_iff_u4 (τ : MulAut ↥(parP h ⊓ parP2 h))
    {S T : Subgroup (hypSU h 2 0)} (hTB : T ≤ parP h ⊓ parP2 h)
    (hS : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ S ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ S)
    (hT : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ T ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ T)
    (b : ↥(parP h ⊓ parP2 h)) :
    ((b : hypSU h 2 0) ∈ S ∧ ∀ x ∈ T, (b : hypSU h 2 0) * x = x * b) ↔
      (((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ S ∧
        ∀ x ∈ T, ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * x =
          x * ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0)) := by
  constructor
  · exact preserves_inf_comm_u4 h τ hTB hS hT b
  · intro hb
    have e := preserves_inf_comm_u4 h τ.symm hTB
      (preserves_symm_u4 τ (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ S) hS)
      (preserves_symm_u4 τ (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ T) hT)
      (τ b) hb
    rwa [MulEquiv.symm_apply_apply] at e

private theorem isolate_u4RootA (hm : 2 ≤ m) (τ : MulAut ↥(parP h ⊓ parP2 h))
    (hQ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h)
    (hQQ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h)
    (hH : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ hypTorus h 2 0 ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypTorus h 2 0)
    (b : ↥(parP h ⊓ parP2 h)) (hb : (b : hypSU h 2 0) ∈ u4RootA h) :
    ((τ.symm b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ u4RootA h := by
  obtain ⟨l, hlb, hl0, hl1⟩ := exists_fixed_ne_u4 h hm
  obtain ⟨d, hdT, q, hq, e1, e2, e3, e4⟩ :=
    exists_mem_hypTorus_u4 h hl0 hl0 (by rw [map_mul, hlb])
  rw [hlb] at e3 e4
  let dB : ↥(parP h ⊓ parP2 h) := ⟨d, hypTorus_le_inf_u4 h hdT⟩
  have hkT := (hH dB).mp hdT
  obtain ⟨qk, hqk⟩ := exists_diag_of_mem_hypTorus_u4 h hkT
  have hk43 : qk if2 = qk if1 := by
    by_contra hne
    let xB : ↥(parP h ⊓ parP2 h) :=
      ⟨syElt h 1, u4RootA_le_inf h (syElt_mem_u4RootA h 1)⟩
    have hc : (dB : hypSU h 2 0) * (xB : hypSU h 2 0) = (xB : hypSU h 2 0) * (dB : hypSU h 2 0) :=
      comm_of_mem_u4RootA h hq (by rw [e3, e4]) (syElt_mem_u4RootA h 1)
    have hc' := comm_map_u4 h τ dB xB hc
    have hτxQ := (hQ xB).mp (syElt_mem 1)
    have hxQQ := (hQQ xB).mpr (mem_radQ_inf_radQ2_of_comm_diag h hqk hne hτxQ hc')
    obtain ⟨x, c, -, hxm⟩ := (mem_radQ_inf_radQ2_iff h).mp hxQQ
    change sMat h 0 1 0 = sMat h x 0 c at hxm
    exact one_ne_zero (sMat_injective h hxm).2.1
  have hcb := comm_symm_u4 h τ dB b (comm_of_mem_u4RootA h hqk hk43 hb)
  have hQ' := (preserves_symm_u4 τ
    (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ radQ h) hQ b).mp (by
      obtain ⟨y, hy⟩ := hb
      exact ⟨0, y, 0, sAdm_zero_y h y, hy⟩)
  refine mem_u4RootA_of_comm_diag h hq ?_ ?_ hQ' hcb
  · rw [e2, e3]
    exact ne_inv_u4 h hl0 hl1
  · rw [e1, e3]
    exact ne_inv_u4 h hl0 hl1

private noncomputable def fA_u4 (y : K) : ↥(parP h ⊓ parP2 h) :=
  ⟨syElt h y, u4RootA_le_inf h (syElt_mem_u4RootA h y)⟩

private noncomputable def fB_u4 (t : h.fixedField) : ↥(parP h ⊓ parP2 h) :=
  ⟨u4xbElt h ((h.mem_fixedField).mp t.2), u4RootB_le_inf h (u4xbElt_mem_u4RootB h _)⟩

private theorem fA_u4_add (y y' : K) : fA_u4 h (y + y') = fA_u4 h y * fA_u4 h y' :=
  Subtype.ext (syElt_add_u4 h y y')

private theorem fA_u4_injective : Function.Injective (fA_u4 h) := by
  intro y y' e
  have e' := congrArg (fun z : ↥(parP h ⊓ parP2 h) =>
    (((z : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)) e
  exact (sMat_injective h e').2.1

private theorem fB_u4_add (t t' : h.fixedField) : fB_u4 h (t + t') = fB_u4 h t * fB_u4 h t' :=
  Subtype.ext (u4xbElt_add h ((h.mem_fixedField).mp t.2) ((h.mem_fixedField).mp t'.2)
    ((h.mem_fixedField).mp (t + t').2))

private theorem fB_u4_injective : Function.Injective (fB_u4 h) := by
  intro t t' e
  have e' := congrFun (congrFun (congrArg (fun z : ↥(parP h ⊓ parP2 h) =>
    (((z : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)) e) ie2) if2
  change u4xbMat (t : K) ie2 if2 = u4xbMat (t' : K) ie2 if2 at e'
  simpa [u4xbMat_apply, one_apply] using e'

private theorem root_torus_u4 (τ : MulAut ↥(parP h ⊓ parP2 h)) (l : K ≃+ K)
    (hl : ∀ y, τ (fA_u4 h y) = fA_u4 h (l y)) (k : ↥(parP h ⊓ parP2 h)) {q qk : Ix → K}
    (hq : (((k : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) = diagonal q)
    (hqk : ((((τ k : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) =
      diagonal qk) (y : K) :
    l (q if2 * (q if1)⁻¹ * y) = qk if2 * (qk if1)⁻¹ * l y := by
  have e1 : k * fA_u4 h y * k⁻¹ = fA_u4 h (q if2 * (q if1)⁻¹ * y) := by
    apply Subtype.ext
    apply hypSU_ext h
    exact coe_conj_syElt_of_diag h hq y
  have e2 := congrArg τ e1
  rw [map_mul, map_mul, map_inv, hl, hl] at e2
  have e3 := coe_conj_syElt_of_diag h hqk (l y)
  have e4 : ((τ k : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * syElt h (l y) *
      ((τ k : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0)⁻¹ =
        syElt h (l (q if2 * (q if1)⁻¹ * y)) := congrArg Subtype.val e2
  rw [e4, coe_syElt] at e3
  exact (sMat_injective h e3).2.1

include h in
private theorem exists_sq_u4 (x : K) : ∃ r : K, r * r = x := by
  have := h.finite
  have := h.charP
  obtain ⟨r, hr⟩ := isSquare_of_charTwo' x
  exact ⟨r, hr.symm⟩

private theorem exists_torus_alpha_u4 {x : K} (hx : x ≠ 0) :
    ∃ k ∈ hypTorus h 2 0, ∃ q : Ix → K,
      ((k : GL Ix K) : Matrix Ix Ix K) = diagonal q ∧ q if2 * (q if1)⁻¹ = x := by
  obtain ⟨r, hr⟩ := exists_sq_u4 h x
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hx (by rw [← hr, zero_mul])
  have hw0 : h.bar r ≠ 0 := (map_ne_zero h.bar).mpr hr0
  obtain ⟨k, hk, q, hq, -, -, e3, e4⟩ := exists_mem_hypTorus_u4 h hw0 (inv_ne_zero hw0)
    (by rw [mul_inv_cancel₀ hw0, map_one])
  refine ⟨k, hk, q, hq, ?_⟩
  rw [e3, e4, map_inv₀, inv_inv, h.bar_bar, hr]

private theorem exists_torus_alpha_beta_u4 {s t : K} (hs : s ≠ 0) (ht0 : t ≠ 0)
    (ht : h.bar t = t) :
    ∃ k ∈ hypTorus h 2 0, ∃ q : Ix → K,
      ((k : GL Ix K) : Matrix Ix Ix K) = diagonal q ∧ q if2 * (q if1)⁻¹ = s ∧
        q ie2 * (q if2)⁻¹ = t := by
  have := h.charP
  obtain ⟨r, hr⟩ := exists_sq_u4 h s
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hs (by rw [← hr, zero_mul])
  have hw0 : h.bar r ≠ 0 := (map_ne_zero h.bar).mpr hr0
  obtain ⟨a, ha⟩ := exists_sq_u4 h (t * (h.bar r * r))
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at ha
    exact mul_ne_zero ht0 (mul_ne_zero hw0 hr0) ha.symm
  have hab : h.bar a = a := by
    have e : h.bar a ^ 2 = a ^ 2 := by
      rw [sq, sq, ← map_mul, ha, map_mul, map_mul, ht, h.bar_bar, mul_comm r]
    exact CharTwo.sq_inj.mp e
  obtain ⟨k, hk, q, hq, -, e2, e3, e4⟩ := exists_mem_hypTorus_u4 h (a0 := h.bar r * a)
    (a1 := a * (h.bar r)⁻¹) (mul_ne_zero hw0 ha0) (mul_ne_zero ha0 (inv_ne_zero hw0)) (by
      rw [show h.bar r * a * (a * (h.bar r)⁻¹) = a * a by field_simp, map_mul, hab])
  refine ⟨k, hk, q, hq, ?_, ?_⟩
  · rw [e3, e4, map_mul, map_mul, map_inv₀, hab, h.bar_bar, inv_inv]
    rw [← hr]
    field_simp
  · rw [e2, e4, inv_inv, map_mul, map_inv₀, hab, h.bar_bar]
    field_simp
    linear_combination ha

private theorem root_rel_u4 (τ : MulAut ↥(parP h ⊓ parP2 h))
    (hZ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ zRad h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ zRad h)
    (l : K ≃+ K) (hl : ∀ y, τ (fA_u4 h y) = fA_u4 h (l y))
    (μ : h.fixedField ≃+ h.fixedField) (hμ : ∀ t, τ (fB_u4 h t) = fB_u4 h (μ t))
    (t : h.fixedField) : (μ t : K) * l 1 = (μ 1 : K) * l t := by
  have := h.charP
  have ht : h.bar (t : K) = t := (h.mem_fixedField).mp t.2
  have hz2 : h.bar ((t : K) + t * t) = t + t * t := by rw [map_add, map_mul, ht]
  let z : ↥(parP h ⊓ parP2 h) :=
    ⟨sElt h ((sAdm_zero_zero_iff h).mpr hz2), radQ_le_inf_u4 h (sElt_mem_radQ h _)⟩
  have hzZ : (z : hypSU h 2 0) ∈ zRad h := ⟨_, hz2, rfl⟩
  have hw : fB_u4 h t * fA_u4 h 1 * fB_u4 h t * fA_u4 h 1 =
      fB_u4 h 1 * fA_u4 h (t : K) * fB_u4 h 1 * fA_u4 h (t : K) * z := by
    apply Subtype.ext
    apply hypSU_ext h
    change u4xbMat (t : K) * sMat h 0 1 0 * u4xbMat (t : K) * sMat h 0 1 0 =
      u4xbMat ((1 : h.fixedField) : K) * sMat h 0 t 0 * u4xbMat ((1 : h.fixedField) : K) *
        sMat h 0 t 0 * sMat h 0 0 (t + t * t)
    rw [u4xbMat_comm_sMat h ht, OneMemClass.coe_one, u4xbMat_comm_sMat h (map_one h.bar),
      sMat_mul, ht]
    congr 1
    · ring
    · simp
    · simp only [map_one, mul_one, one_mul, map_zero, mul_zero, zero_mul, add_zero]
      grind
  have e := congrArg (fun w : ↥(parP h ⊓ parP2 h) =>
    ((((τ w : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K) ie2 if1) hw
  simp only [map_mul, hl, hμ] at e
  obtain ⟨c, -, hzm⟩ := (hZ z).mp hzZ
  have hμt : h.bar ((μ t : h.fixedField) : K) = μ t := (h.mem_fixedField).mp (μ t).2
  have hμ1 : h.bar ((μ 1 : h.fixedField) : K) = μ 1 := (h.mem_fixedField).mp (μ 1).2
  change (u4xbMat ((μ t : h.fixedField) : K) * sMat h 0 (l 1) 0 *
      u4xbMat ((μ t : h.fixedField) : K) * sMat h 0 (l 1) 0) ie2 if1 =
    (u4xbMat ((μ 1 : h.fixedField) : K) * sMat h 0 (l t) 0 *
      u4xbMat ((μ 1 : h.fixedField) : K) * sMat h 0 (l t) 0 *
      ((((τ z : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)) ie2 if1 at e
  rw [u4xbMat_comm_sMat h hμt, u4xbMat_comm_sMat h hμ1, hzm, sMat_mul, sMat_ie2_if1,
    sMat_ie2_if1, add_zero] at e
  exact e

theorem exists_stdAut_eq_of_preserves_radQ_u4 (hm : 2 ≤ m)
    (σ : MulAut ↥(parP h ⊓ parP2 h))
    (hσ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h ↔
      ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h) :
    ∃ (e : ↥(parP h ⊓ parP2 h)) (d : hypSU h 2 0) (ρ : K ≃+* K), d ∈ hypTorus h 2 0 ∧
      ∀ b : ↥(parP h ⊓ parP2 h),
        ((MulAut.conj (e : hypSU h 2 0)⁻¹ * u4StdAut h d ρ) b : hypSU h 2 0) =
          ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) := by
  have := h.charP
  haveI := h.finite
  obtain ⟨e, -, hτH⟩ := exists_conj_torus_u4 h σ
  set τ : MulAut ↥(parP h ⊓ parP2 h) := MulAut.conj e * σ
  have hτapp : ∀ b : ↥(parP h ⊓ parP2 h), ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) =
      (e : hypSU h 2 0) * ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * (e : hypSU h 2 0)⁻¹ :=
    fun b => rfl
  have heB : (e : hypSU h 2 0) ∈ parP h ⊓ parP2 h := e.2
  have hconj : ∀ {N : Subgroup (hypSU h 2 0)},
      (e : hypSU h 2 0) ∈ Subgroup.normalizer (N : Set (hypSU h 2 0)) →
      (∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ N ↔
        ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ N) →
      ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ N ↔
        ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ N := by
    intro N hN hσN b
    rw [hτapp, ← Subgroup.mem_normalizer_iff.mp hN]
    exact hσN b
  have hτU := hconj (inf_le_normalizer_u4 h heB) (preserves_hypUnitriangular_u4 h σ)
  have hτQ := hconj (parP_le_normalizer_radQ h heB.1) hσ
  have hτXb : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ u4RootB h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ u4RootB h := by
    intro b
    constructor
    · intro hb
      have e' := isolate_u4RootB h hm τ.symm
        (preserves_symm_u4 τ
          (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0) hτU)
        (preserves_symm_u4 τ (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ radQ h)
          hτQ)
        (preserves_symm_u4 τ
          (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ hypTorus h 2 0) hτH) b hb
      rwa [MulEquiv.symm_symm] at e'
    · intro hb
      have e' := isolate_u4RootB h hm τ hτU hτQ hτH (τ b) hb
      rwa [MulEquiv.symm_apply_apply] at e'
  have hτQQ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h := by
    intro b
    rw [mem_radQ_inf_radQ2_iff_comm, mem_radQ_inf_radQ2_iff_comm]
    exact preserves_inf_comm_iff_u4 h τ (u4RootB_le_inf h) hτQ hτXb b
  have hτZ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ zRad h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ zRad h := by
    intro b
    rw [mem_zRad_iff_comm, mem_zRad_iff_comm]
    exact preserves_inf_comm_iff_u4 h τ (radQ_le_inf_u4 h) hτQ hτQ b
  have hτXa : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ u4RootA h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ u4RootA h := by
    intro b
    constructor
    · intro hb
      have e' := isolate_u4RootA h hm τ.symm
        (preserves_symm_u4 τ (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ radQ h)
          hτQ)
        (preserves_symm_u4 τ
          (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h) hτQQ)
        (preserves_symm_u4 τ
          (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ hypTorus h 2 0) hτH) b hb
      rwa [MulEquiv.symm_symm] at e'
    · intro hb
      have e' := isolate_u4RootA h hm τ hτQ hτQQ hτH (τ b) hb
      rwa [MulEquiv.symm_apply_apply] at e'
  obtain ⟨l, hl⟩ := exists_addEquiv_u4 (fA_u4 h) (fA_u4_add h) (fA_u4_injective h) τ (by
    intro y
    obtain ⟨y', hy'⟩ := (hτXa (fA_u4 h y)).mp (syElt_mem_u4RootA h y)
    exact ⟨y', Subtype.ext (hypSU_ext h hy')⟩)
  obtain ⟨μ, hμ⟩ := exists_addEquiv_u4 (fB_u4 h) (fB_u4_add h) (fB_u4_injective h) τ (by
    intro t
    obtain ⟨t', ht', ht'm⟩ :=
      (hτXb (fB_u4 h t)).mp (u4xbElt_mem_u4RootB h ((h.mem_fixedField).mp t.2))
    exact ⟨⟨t', (h.mem_fixedField).mpr ht'⟩, Subtype.ext (hypSU_ext h ht'm)⟩)
  have hl0 : l 1 ≠ 0 := by
    intro e0
    exact one_ne_zero (l.injective (by rw [e0, map_zero]))
  have hmul : ∀ x y : K, l (x * y) * l 1 = l x * l y := by
    intro x y
    by_cases hx : x = 0
    · rw [hx, zero_mul, map_zero, zero_mul, zero_mul]
    obtain ⟨k, hk, q, hq, hqx⟩ := exists_torus_alpha_u4 h hx
    let kB : ↥(parP h ⊓ parP2 h) := ⟨k, hypTorus_le_inf_u4 h hk⟩
    obtain ⟨qk, hqk⟩ := exists_diag_of_mem_hypTorus_u4 h ((hτH kB).mp hk)
    have e1 := root_torus_u4 h τ l hl kB hq hqk y
    have e2 := root_torus_u4 h τ l hl kB hq hqk 1
    rw [hqx] at e1 e2
    rw [mul_one] at e2
    rw [e1, e2]
    ring
  obtain ⟨ρ, hρ, -, -⟩ := exists_ringEquiv_of_map_mul l.toAddMonoidHom l.toAddMonoidHom
    ((AddMonoidHom.mulLeft (l 1)⁻¹).comp l.toAddMonoidHom) l.bijective (by
      intro y t
      change l (y * t) = l y * ((l 1)⁻¹ * l t)
      field_simp
      exact hmul y t)
  have hρ' : ∀ x : K, l x = l 1 * ρ x := hρ
  have hμρ : ∀ t : h.fixedField, (μ t : K) = (μ 1 : K) * ρ t := by
    intro t
    have e1 := root_rel_u4 h τ hτZ l hl μ hμ t
    rw [hρ' (t : K)] at e1
    have e2 : ((μ t : K) - (μ 1 : K) * ρ t) * l 1 = 0 := by linear_combination e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hl0)
  have hμ10 : (μ 1 : K) ≠ 0 := by
    intro e0
    have e1 : μ 1 = 0 := Subtype.ext e0
    exact one_ne_zero (μ.injective (by rw [e1, map_zero]))
  obtain ⟨d, hdT, q, hq, hqα, hqβ⟩ := exists_torus_alpha_beta_u4 h hl0 hμ10
    ((h.mem_fixedField).mp (μ 1).2)
  have hdB : d ∈ parP h ⊓ parP2 h := hypTorus_le_inf_u4 h hdT
  let Φ : MulAut (hypSU h 2 0) := u4StdAut h d ρ
  have hagree : ∀ b : ↥(parP h ⊓ parP2 h),
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) = Φ b := by
    refine eq_of_agree_u4Roots h (fun g => (stdAut_mem_hypUnitriangular_iff_u4 h
      (hypTorus_le_hypBorel h hdT) ρ g).symm) (fun g hg => stdAut_mem_hypTorus_u4 h hdT ρ hg)
      (fun b hb => (hτH b).mp hb) ?_ ?_
    · intro b hb
      obtain ⟨y, hy⟩ := hb
      have hb' : b = fA_u4 h y := Subtype.ext (hypSU_ext h hy)
      rw [hb', hl]
      apply hypSU_ext h
      change sMat h 0 (l y) 0 =
        (((u4StdAut h d ρ (syElt h y) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)
      rw [coe_stdAut_syElt_u4 h hq ρ y, hqα, hρ' y]
    · intro b hb
      obtain ⟨t, ht, htm⟩ := hb
      have hb' : b = fB_u4 h ⟨t, (h.mem_fixedField).mpr ht⟩ := Subtype.ext (hypSU_ext h htm)
      rw [hb', hμ]
      apply hypSU_ext h
      change u4xbMat ((μ ⟨t, (h.mem_fixedField).mpr ht⟩ : h.fixedField) : K) =
        (((u4StdAut h d ρ (u4xbElt h ht) : hypSU h 2 0) : GL Ix K) : Matrix Ix Ix K)
      rw [coe_stdAut_u4xbElt h hq ρ ht, hqβ, hμρ]
  refine ⟨e, d, ρ, hdT, fun b => ?_⟩
  rw [MulAut.mul_apply, MulAut.conj_apply, inv_inv, ← hagree b, hτapp]
  group

private theorem exists_extend_of_preserves_radQ_u4 (hm : 2 ≤ m)
    (σ : MulAut ↥(parP h ⊓ parP2 h))
    (hσ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h ↔
      ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h) :
    ∃ Ψ : MulAut (hypSU h 2 0), (∀ g, g ∈ parP h ↔ Ψ g ∈ parP h) ∧
      (∀ g, g ∈ parP2 h ↔ Ψ g ∈ parP2 h) ∧
      ∀ b : ↥(parP h ⊓ parP2 h),
        (Ψ b : hypSU h 2 0) = ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) := by
  obtain ⟨e, d, ρ, hdT, hagree⟩ := exists_stdAut_eq_of_preserves_radQ_u4 h hm σ hσ
  have heB : (e : hypSU h 2 0) ∈ parP h ⊓ parP2 h := e.2
  have hdB : d ∈ parP h ⊓ parP2 h := hypTorus_le_inf_u4 h hdT
  refine ⟨MulAut.conj (e : hypSU h 2 0)⁻¹ * u4StdAut h d ρ, ?_, ?_, hagree⟩
  · intro g
    rw [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
    rw [Subgroup.mul_mem_cancel_right _ heB.1, Subgroup.mul_mem_cancel_left _
      ((parP h).inv_mem heB.1)]
    exact (stdAut_mem_parP_iff_u4 h hdB.1 ρ g).symm
  · intro g
    rw [MulAut.mul_apply, MulAut.conj_apply, inv_inv]
    rw [Subgroup.mul_mem_cancel_right _ heB.2, Subgroup.mul_mem_cancel_left _
      ((parP2 h).inv_mem heB.2)]
    exact (stdAut_mem_parP2_iff_u4 h hdB.2 ρ g).symm

private theorem map_subgroupOf_eq_of_iff_u4 (τ : MulAut ↥(parP h ⊓ parP2 h))
    {S : Subgroup (hypSU h 2 0)}
    (hS : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ S ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ S) :
    (S.subgroupOf (parP h ⊓ parP2 h)).map τ.toMonoidHom = S.subgroupOf (parP h ⊓ parP2 h) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hS y).mp hy
  · intro hx
    exact ⟨τ.symm x, (preserves_symm_u4 τ
      (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ S) hS x).mp hx, by simp⟩

private theorem preserves_commutator_u4 (τ : MulAut ↥(parP h ⊓ parP2 h))
    (hQ2 : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ2 h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ2 h)
    (hXa : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ u4RootA h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ u4RootA h)
    (b : ↥(parP h ⊓ parP2 h)) :
    (b : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h := by
  let R := (radQ2 h).subgroupOf (parP h ⊓ parP2 h)
  let A := (u4RootA h).subgroupOf (parP h ⊓ parP2 h)
  have hC : (⁅R, A⁆).map (parP h ⊓ parP2 h).subtype = radQ h ⊓ radQ2 h := by
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le (radQ2_le_inf_u4 h),
      Subgroup.map_subgroupOf_eq_of_le (u4RootA_le_inf h), commutator_radQ2_u4RootA]
  have hτC : (⁅R, A⁆).map τ.toMonoidHom = ⁅R, A⁆ := by
    rw [Subgroup.map_commutator, map_subgroupOf_eq_of_iff_u4 h τ hQ2,
      map_subgroupOf_eq_of_iff_u4 h τ hXa]
  have hmem : ∀ x : ↥(parP h ⊓ parP2 h), (x : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h ↔ x ∈ ⁅R, A⁆ := by
    intro x
    rw [← hC]
    exact Subgroup.mem_map_iff_mem (parP h ⊓ parP2 h).subtype_injective
  rw [hmem, hmem]
  exact iff_of_map_eq_u4 τ hτC b

private theorem isolate_u4RootA_of_radQ2 (hm : 2 ≤ m) (τ : MulAut ↥(parP h ⊓ parP2 h))
    (hU : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0 ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypUnitriangular h 2 0)
    (hQ2 : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ2 h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ2 h)
    (hH : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ hypTorus h 2 0 ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ hypTorus h 2 0)
    (b : ↥(parP h ⊓ parP2 h)) (hb : (b : hypSU h 2 0) ∈ u4RootA h) :
    ((τ.symm b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ u4RootA h := by
  obtain ⟨l, hlb, hl0, hl1⟩ := exists_fixed_ne_u4 h hm
  obtain ⟨d, hdT, q, hq, e1, e2, e3, e4⟩ :=
    exists_mem_hypTorus_u4 h hl0 hl0 (by rw [map_mul, hlb])
  rw [hlb] at e3 e4
  let dB : ↥(parP h ⊓ parP2 h) := ⟨d, hypTorus_le_inf_u4 h hdT⟩
  have hkT := (hH dB).mp hdT
  obtain ⟨qk, hqk⟩ := exists_diag_of_mem_hypTorus_u4 h hkT
  have hk43 : qk if2 = qk if1 := by
    by_contra hne
    let xB : ↥(parP h ⊓ parP2 h) :=
      ⟨syElt h 1, u4RootA_le_inf h (syElt_mem_u4RootA h 1)⟩
    have hc : (dB : hypSU h 2 0) * (xB : hypSU h 2 0) = (xB : hypSU h 2 0) * (dB : hypSU h 2 0) :=
      comm_of_mem_u4RootA h hq (by rw [e3, e4]) (syElt_mem_u4RootA h 1)
    have hc' := comm_map_u4 h τ dB xB hc
    have hτxU := (hU xB).mp (radQ_le_hypUnitriangular_u4 h (syElt_mem 1))
    have hxQ2 := (hQ2 xB).mpr (mem_radQ2_of_comm_diag h hqk hne hτxU hc')
    have e := hxQ2.2.1
    change sMat h 0 1 0 ie1 ie2 = 0 at e
    simp [sMat_apply, one_apply] at e
  have hcb := comm_symm_u4 h τ dB b (comm_of_mem_u4RootA h hqk hk43 hb)
  have hU' := (preserves_symm_u4 τ
    (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0) hU b).mp
    (radQ_le_hypUnitriangular_u4 h (u4RootA_le_radQ h hb))
  have hQ' := mem_radQ_of_comm_diag h hq (by rw [e2, e4]; exact ne_inv_u4 h hl0 hl1) hU' hcb
  refine mem_u4RootA_of_comm_diag h hq ?_ ?_ hQ' hcb
  · rw [e2, e3]
    exact ne_inv_u4 h hl0 hl1
  · rw [e1, e3]
    exact ne_inv_u4 h hl0 hl1

private theorem preserves_radQ_of_radQ2_u4 (hm : 2 ≤ m) (σ : MulAut ↥(parP h ⊓ parP2 h))
    (hσ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ2 h ↔
      ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ2 h)
    (b : ↥(parP h ⊓ parP2 h)) :
    (b : hypSU h 2 0) ∈ radQ h ↔ ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h := by
  obtain ⟨e, -, hτH⟩ := exists_conj_torus_u4 h σ
  set τ : MulAut ↥(parP h ⊓ parP2 h) := MulAut.conj e * σ
  have hτapp : ∀ b : ↥(parP h ⊓ parP2 h), ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) =
      (e : hypSU h 2 0) * ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) * (e : hypSU h 2 0)⁻¹ :=
    fun b => rfl
  have heB : (e : hypSU h 2 0) ∈ parP h ⊓ parP2 h := e.2
  have hconj : ∀ {N : Subgroup (hypSU h 2 0)},
      (e : hypSU h 2 0) ∈ Subgroup.normalizer (N : Set (hypSU h 2 0)) →
      (∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ N ↔
        ((σ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ N) →
      ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ N ↔
        ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ N := by
    intro N hN hσN b
    rw [hτapp, ← Subgroup.mem_normalizer_iff.mp hN]
    exact hσN b
  have hτU := hconj (inf_le_normalizer_u4 h heB) (preserves_hypUnitriangular_u4 h σ)
  have hτQ2 := hconj (parP2_le_normalizer_radQ2 h heB.2) hσ
  have hτXa : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ u4RootA h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ u4RootA h := by
    intro b
    constructor
    · intro hb
      have e' := isolate_u4RootA_of_radQ2 h hm τ.symm
        (preserves_symm_u4 τ
          (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ hypUnitriangular h 2 0) hτU)
        (preserves_symm_u4 τ (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ radQ2 h)
          hτQ2)
        (preserves_symm_u4 τ
          (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ hypTorus h 2 0) hτH) b hb
      rwa [MulEquiv.symm_symm] at e'
    · intro hb
      have e' := isolate_u4RootA_of_radQ2 h hm τ hτU hτQ2 hτH (τ b) hb
      rwa [MulEquiv.symm_apply_apply] at e'
  have hτQQ := preserves_commutator_u4 h τ hτQ2 hτXa
  have key : ∀ ψ : MulAut ↥(parP h ⊓ parP2 h),
      (∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ u4RootA h ↔
        ((ψ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ u4RootA h) →
      (∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h ↔
        ((ψ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h) →
      ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h →
        ((ψ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h := by
    intro ψ hψA hψQQ b hb
    obtain ⟨a, ha, r, hr, hbar⟩ := (mem_radQ_iff_u4 h).mp hb
    let aB : ↥(parP h ⊓ parP2 h) := ⟨a, u4RootA_le_inf h ha⟩
    let rB : ↥(parP h ⊓ parP2 h) := ⟨r, radQ2_le_inf_u4 h hr.2⟩
    have hb' : b = aB * rB := Subtype.ext hbar
    rw [hb', map_mul]
    exact (mem_radQ_iff_u4 h).mpr ⟨_, (hψA aB).mp ha, _, (hψQQ rB).mp hr, rfl⟩
  have hτQ : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ h ↔
      ((τ b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ h := by
    intro b
    constructor
    · exact key τ hτXa hτQQ b
    · intro hb
      have e' := key τ.symm
        (preserves_symm_u4 τ (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ u4RootA h)
          hτXa)
        (preserves_symm_u4 τ
          (P := fun b : ↥(parP h ⊓ parP2 h) => (b : hypSU h 2 0) ∈ radQ h ⊓ radQ2 h) hτQQ)
        (τ b) hb
      rwa [MulEquiv.symm_apply_apply] at e'
  rw [hτQ b, hτapp, ← Subgroup.mem_normalizer_iff.mp (parP_le_normalizer_radQ h heB.1)]

theorem dcProp_parP2_parP {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)
    (hm : 2 ≤ m) : DCProp (parP2 h) (parP h) := by
  refine dcProp_of_forall_exists_extend fun σ hσ => ?_
  rw [U4qModel.pCoreOf_parP2_eq h hm] at hσ
  let E : ↥(parP2 h ⊓ parP h) ≃* ↥(parP h ⊓ parP2 h) :=
    MulEquiv.subgroupCongr (inf_comm (parP2 h) (parP h))
  have hE : ∀ x : ↥(parP2 h ⊓ parP h), ((E x : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) = x :=
    MulEquiv.subgroupCongr_apply _
  have hEs : ∀ x : ↥(parP h ⊓ parP2 h),
      ((E.symm x : ↥(parP2 h ⊓ parP h)) : hypSU h 2 0) = x :=
    MulEquiv.subgroupCongr_symm_apply _
  let σ' : MulAut ↥(parP h ⊓ parP2 h) := (E.symm.trans σ).trans E
  have hσ' : ∀ x : ↥(parP h ⊓ parP2 h), ((σ' x : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) =
      ((σ (E.symm x) : ↥(parP2 h ⊓ parP h)) : hypSU h 2 0) := by
    intro x
    rw [← hE (σ (E.symm x))]
    rfl
  have hσ'Q2 : ∀ b : ↥(parP h ⊓ parP2 h), (b : hypSU h 2 0) ∈ radQ2 h ↔
      ((σ' b : ↥(parP h ⊓ parP2 h)) : hypSU h 2 0) ∈ radQ2 h := by
    intro b
    rw [hσ' b, ← hEs b]
    exact hσ (E.symm b)
  obtain ⟨Ψ, hP, hP2, hΨ⟩ := exists_extend_of_preserves_radQ_u4 h hm σ'
    (preserves_radQ_of_radQ2_u4 h hm σ' hσ'Q2)
  refine ⟨Ψ, hP2, hP, fun b => ?_⟩
  have e := hΨ (E b)
  rw [hσ' (E b), MulEquiv.symm_apply_apply, hE] at e
  exact e

end CFSG.Quasithin.F112R.St84

end
