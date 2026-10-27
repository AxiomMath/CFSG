module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4HjPerf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M24
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Def
public import CFSG.Quasithin.EmptyFaithful.T1515M11
public import CFSG.Quasithin.EmptyFaithful.SBc11List
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Perf

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc CFSG.Quasithin.A312M24
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven

theorem isPGroup_of_isE2 {n : ℕ} {V : Type} [Group V] (h : IsE2 n V) : IsPGroup 2 V := by
  obtain ⟨e⟩ := h
  refine IsPGroup.of_card (n := n) ?_
  rw [Nat.card_congr e.toEquiv]
  simp

theorem isPGroup_of_isExtraspecial2 {m : ℕ} {V : Type} [Group V] (h : IsExtraspecial2 m V) :
    IsPGroup 2 V :=
  IsPGroup.of_card (n := 1 + 2 * m) h.2

theorem exists_modO2_equiv_of_ext {B C : Type} [Group B] [Finite B] [Group C] (g : B →* C)
    (hg : IsPGroup 2 g.ker) {PV PY : ∀ (V : Type) [Group V], Prop}
    (hV : ∀ (V : Type) [Group V], PV V → IsPGroup 2 V)
    (hY : ∀ (S : Type) [Group S] [Finite S], PY S → CFSG.pCore 2 S = ⊥)
    (h : IsExt ↥g.range PV PY) :
    ∃ (S : Type) (_ : Group S), PY S ∧ Nonempty ((B ⧸ CFSG.pCore 2 B) ≃* S) := by
  obtain ⟨V, hVn, hPV, hPY⟩ := h
  have : Finite ↥g.range := Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective g)
  let ψ : B →* (↥g.range ⧸ V) := (QuotientGroup.mk' V).comp g.rangeRestrict
  have hψ : Function.Surjective ψ :=
    (QuotientGroup.mk'_surjective V).comp (MonoidHom.rangeRestrict_surjective g)
  have hker : IsPGroup 2 ψ.ker := by
    refine isPGroup_ker_comp g.rangeRestrict (QuotientGroup.mk' V) ?_ ?_
    · rw [MonoidHom.ker_rangeRestrict]
      exact hg
    · rw [QuotientGroup.ker_mk']
      exact hV _ hPV
  exact ⟨_, inferInstance, hPY, nonempty_modO2_equiv ψ hψ hker (hY _ hPY)⟩

theorem pCore_eq_bot_of_isPSL42 {S : Type} [Group S] [Finite S] (h : IsPSL 4 2 1 S) :
    CFSG.pCore 2 S = ⊥ := by
  have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity S 4 2 1 h).2
  have hc : Nat.card S = 20160 := by
    rw [CFSG.Quasithin.card_of_isPSL_two1522 4 h]
    decide
  refine pCore_eq_bot_of_simple (nonabelian_of_card_not_prime (S := S) ?_)
  rw [hc]
  norm_num

theorem pCore_eq_bot_of_isPSL32 {S : Type} [Group S] [Finite S] (h : IsPSL 3 2 1 S) :
    CFSG.pCore 2 S = ⊥ := by
  have hs := (CFSG.LieType.Simplicity.fam_PSL_simplicity S 3 2 1 h).2
  have hc : Nat.card S = 168 := CFSG.Quasithin.SBc11.card_of_isPSL_three_two h
  exact pCore_eq_bot_of_simple (nonabelian_of_card168 hc)

theorem J4Shape_of_c14 {B C : Type} [Group B] [Finite B] [Group C] (g : B →* C)
    (hg : IsPGroup 2 g.ker)
    (h : IsExt ↥g.range (fun V _ => IsE2 4 V) (fun Y _ => IsPSL 4 2 1 Y) ∨
      IsExt ↥g.range (fun V _ => IsE2 6 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
      IsExt ↥g.range (fun V _ => IsExtraspecial2 3 V) (fun Y _ => IsPSL 3 2 1 Y) ∨
      IsExt ↥g.range (fun V _ => IsE2 6 V) (fun Y _ => IsHat Y (alternatingGroup (Fin 6)))) :
    J4Shape B := by
  rcases h with h | h | h | h
  · obtain ⟨S, _, hS, ⟨e⟩⟩ := exists_modO2_equiv_of_ext g hg (fun _ _ => isPGroup_of_isE2)
      (fun S _ _ hS => pCore_eq_bot_of_isPSL42 hS) h
    exact J4Shape.of_psl42 e hS
  · obtain ⟨S, _, hS, ⟨e⟩⟩ := exists_modO2_equiv_of_ext g hg (fun _ _ => isPGroup_of_isE2)
      (fun S _ _ hS => pCore_eq_bot_of_isPSL32 hS) h
    exact J4Shape.of_psl32 e hS
  · obtain ⟨S, _, hS, ⟨e⟩⟩ := exists_modO2_equiv_of_ext g hg
      (fun _ _ => isPGroup_of_isExtraspecial2)
      (fun S _ _ hS => pCore_eq_bot_of_isPSL32 hS) h
    exact J4Shape.of_psl32 e hS
  · obtain ⟨S, _, hS, ⟨e⟩⟩ := exists_modO2_equiv_of_ext g hg (fun _ _ => isPGroup_of_isE2)
      (fun S _ _ hS => pCore_eq_bot_of_isHat hS.1 hS.2.1) h
    exact J4Shape.of_hat6 e hS

section Case


theorem isQuasisimple_G24 : CFSG.IsQuasisimple G24 := by
  have hs : IsSimpleGroup G24 := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hna : ∃ a b : G24, a * b ≠ b * a := by
    refine nonabelian_of_card_not_prime (S := G24) ?_
    rw [show Nat.card G24 = 244823040 from CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hna).1

theorem J4Shape_Hj : J4Shape ↥Hj := by
  have hM := j4Facts.mat
  refine Or.inr (Or.inl ⟨(Eg uJ 11).subgroupOf Hj, inferInstance, ?_, isSporadic_Hj_quotient⟩)
  have hE' : IsE2 11 ↥(Eg uJ 11) :=
    isE2_of_elementary (Eg uJ 11) (fun a ha b hb => Eg_comm (elem_uJ hM) ha hb)
      (fun a ha => Eg_sq (elem_uJ hM) ha) (card_Eg_uJ hM)
  have e : ↥(Eg uJ 11) ≃* ↥((Eg uJ 11).subgroupOf Hj) :=
    (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).symm
  exact IsE2.of_mulEquiv (X := ↥(Eg uJ 11)) (Y := ↥((Eg uJ 11).subgroupOf Hj)) e hE'

theorem hj_case [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] : J4Case Hj := by
  intro B hB hBH
  have hM := j4Facts.mat
  have hBle : B ≤ Hj := le_sup_left.trans hBH
  have hP0H : P0 ≤ Hj := P0_le_Hj
  have hB' : B.subgroupOf Hj ∈ lFamily (P0.subgroupOf Hj) := by
    have h1 := A312.mem_cComp_subgroupOf hBH (show B ∈ cComp (B ⊔ P0) from hB)
    rw [Subgroup.subgroupOf_sup hBle hP0H] at h1
    exact h1
  have hT' : IsSylowTwoOf (P0.subgroupOf Hj) ⊤ := isSylowTwoOf_subgroupOf_of_le isSylowTwoOf_P0 hP0H
  have hkernil : Group.IsNilpotent ↥fHj.ker := isPGroup_ker_fHj.isNilpotent
  have hkersolv : Group.IsSolvable ↥fHj.ker := inferInstance
  have hkersolv' : Group.IsSolvable ↥(fHj.ker ⊓ (B.subgroupOf Hj ⊔ P0.subgroupOf Hj)) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective _)
  have hBb : (B.subgroupOf Hj).map fHj ∈ lFamily ((P0.subgroupOf Hj).map fHj) := by
    have h2 := A312.map_mem_cComp fHj hkersolv'
      (show B.subgroupOf Hj ∈ cComp (B.subgroupOf Hj ⊔ P0.subgroupOf Hj) from hB')
    rwa [Subgroup.map_sup] at h2
  have hTf : IsSylowTwoOf ((P0.subgroupOf Hj).map fHj) ⊤ :=
    A312.isSylowTwoOf_top_map fHj fHj_surjective hT'
  by_cases htop : (B.subgroupOf Hj).map fHj = ⊤
  ·
    have hsup : B.subgroupOf Hj ⊔ fHj.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, htop, Subgroup.comap_top]
    have hEle : fHj.ker ≤ B.subgroupOf Hj ⊔ P0.subgroupOf Hj := by
      rw [ker_fHj]
      intro x hx
      exact Subgroup.mem_sup_right
        (Subgroup.mem_subgroupOf.2 (Eg_le_P0 (Subgroup.mem_subgroupOf.1 hx)))
    have hnorm : B.subgroupOf Hj ≤ Subgroup.normalizer (fHj.ker : Set ↥Hj) := by
      rw [Subgroup.normalizer_eq_top_iff.2 inferInstance]
      exact le_top
    have h3 := cComp_commutator_perfectCore (show B.subgroupOf Hj ∈ cComp
      (B.subgroupOf Hj ⊔ P0.subgroupOf Hj) from hB') hEle hkersolv hnorm
    have hperf : ⁅(⊤ : Subgroup ↥Hj), ⊤⁆ = ⊤ := Group.isPerfect_def.1 isPerfect_Hj
    rw [hsup, perfectCore_eq_self_of_perfect hperf] at h3
    have hBtop : B.subgroupOf Hj = ⊤ := h3.2.symm
    have hHB : Hj ≤ B := Subgroup.subgroupOf_eq_top.1 hBtop
    have hBeq : B = Hj := le_antisymm hBle hHB
    rw [hBeq]
    exact J4Shape_Hj
  ·
    have h14 := a312C14_of_lFamily isQuasisimple_G24 hTf hBb htop
    let g : ↥B →* G24 := fHj.comp (Subgroup.inclusion hBle)
    have hrange : g.range = (B.subgroupOf Hj).map fHj := by
      show (fHj.comp (Subgroup.inclusion hBle)).range = _
      rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    have hgker : IsPGroup 2 g.ker := by
      intro x
      have hx : fHj (Subgroup.inclusion hBle x.1) = 1 := x.2
      have hxk : Subgroup.inclusion hBle x.1 ∈ fHj.ker := hx
      obtain ⟨k, hk⟩ := isPGroup_ker_fHj (⟨_, hxk⟩ : fHj.ker)
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg (fun y : fHj.ker => ((y : ↥Hj) : J)) hk
      simpa using this
    have h14' := h14.1
    rw [← hrange] at h14'
    exact J4Shape_of_c14 g hgker h14'

end Case

end CFSG.Quasithin.J4Fam
