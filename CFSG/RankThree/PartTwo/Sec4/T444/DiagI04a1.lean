module

public import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.KFacts.KS18OuterZ3

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.KS18 CFSG.RankThree.PartTwo.KFacts.L34
open scoped commutatorElement

theorem I04a1_exists_mul {Y : Type} [Group Y] {A' L' : Subgroup Y}
    (hAL : A' ≤ Subgroup.normalizer (L' : Set Y)) {x : Y} (hx : x ∈ A' ⊔ L') :
    ∃ a ∈ A', ∃ l ∈ L', a * l = x := by
  have hx' : x ∈ ((A' ⊔ L' : Subgroup Y) : Set Y) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A' L' hAL] at hx'
  obtain ⟨a, ha, l, hl, hal⟩ := hx'
  exact ⟨a, ha, l, hl, hal⟩

theorem I04a1_conj_mem {Y : Type} [Group Y] {A' L' : Subgroup Y}
    (hAL : A' ≤ Subgroup.normalizer (L' : Set Y)) {a : Y} (ha : a ∈ A') {n : Y} (hn : n ∈ L') :
    a * n * a⁻¹ ∈ L' :=
  (Subgroup.mem_normalizer_iff.mp (hAL ha) n).mp hn

theorem I04a1_conj_inv_mem {Y : Type} [Group Y] {A' L' : Subgroup Y}
    (hAL : A' ≤ Subgroup.normalizer (L' : Set Y)) {a : Y} (ha : a ∈ A') {n : Y} (hn : n ∈ L') :
    a⁻¹ * n * a ∈ L' := by
  have h := I04a1_conj_mem hAL (A'.inv_mem ha) hn
  rwa [inv_inv] at h

theorem I04a1_comm {Y : Type} [Group Y] {A' : Subgroup Y}
    (hA : CFSG.Assembly.IsElemAbelian 3 A') {a : Y} (ha : a ∈ A') {a' : Y} (ha' : a' ∈ A') :
    a * a' = a' * a := by
  have key : (⟨a, ha⟩ : A') * ⟨a', ha'⟩ = ⟨a', ha'⟩ * ⟨a, ha⟩ := hA.1.is_comm.comm _ _
  have h := congrArg Subtype.val key
  simpa using h

theorem I04a1_commutator_mem {Y : Type} [Group Y] {A' L' : Subgroup Y}
    (hAL : A' ≤ Subgroup.normalizer (L' : Set Y)) (hAc : ∀ a ∈ A', ∀ a' ∈ A', a * a' = a' * a)
    {a l a' l' : Y} (ha : a ∈ A') (hl : l ∈ L') (ha' : a' ∈ A') (hl' : l' ∈ L') :
    ⁅a * l, a' * l'⁆ ∈ L' := by
  have hcomm := hAc a ha a' ha'
  have hxy : a * l * (a' * l') = (a * a') * ((a'⁻¹ * l * a') * l') := by group
  have hyx : a' * l' * (a * l) = (a * a') * ((a⁻¹ * l' * a) * l) := by
    calc a' * l' * (a * l) = (a' * a) * ((a⁻¹ * l' * a) * l) := by group
      _ = (a * a') * ((a⁻¹ * l' * a) * l) := by rw [hcomm]
  have hcomm_eq : ⁅a * l, a' * l'⁆ = (a * l * (a' * l')) * (a' * l' * (a * l))⁻¹ := by
    rw [commutatorElement_def]; group
  have hc : a * a' ∈ A' := A'.mul_mem ha ha'
  have hn1 : (a'⁻¹ * l * a') * l' ∈ L' := L'.mul_mem (I04a1_conj_inv_mem hAL ha' hl) hl'
  have hn2 : (a⁻¹ * l' * a) * l ∈ L' := L'.mul_mem (I04a1_conj_inv_mem hAL ha hl') hl
  have hdecomp : ⁅a * l, a' * l'⁆ = (a * a') * (((a'⁻¹ * l * a') * l') *
      ((a⁻¹ * l' * a) * l)⁻¹) * (a * a')⁻¹ := by
    rw [hcomm_eq, hxy, hyx]; group
  rw [hdecomp]
  exact I04a1_conj_mem hAL hc (L'.mul_mem hn1 (L'.inv_mem hn2))

theorem I04a1_commutator_self {Y : Type} [Group Y] {L : Subgroup Y} (hLp : Group.IsPerfect L) :
    ⁅L, L⁆ = L := by
  have hmap : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hc : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤ := by
    rw [← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  calc ⁅L, L⁆ = ⁅(⊤ : Subgroup L).map L.subtype, (⊤ : Subgroup L).map L.subtype⁆ := by
        rw [hmap]
    _ = (⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆).map L.subtype := by
        rw [Subgroup.map_commutator]
    _ = (⊤ : Subgroup L).map L.subtype := by rw [hc]
    _ = L := hmap

theorem I04a1_commutator_le {Y : Type} [Group Y] {A' L' S : Subgroup Y}
    (hAL : A' ≤ Subgroup.normalizer (L' : Set Y)) (hAc : ∀ a ∈ A', ∀ a' ∈ A', a * a' = a' * a)
    (hS : S ≤ A' ⊔ L') : ⁅S, S⁆ ≤ L' := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨a, ha, l, hl, rfl⟩ := I04a1_exists_mul hAL (hS hx)
  obtain ⟨a', ha', l', hl', rfl⟩ := I04a1_exists_mul hAL (hS hy)
  exact I04a1_commutator_mem hAL hAc ha hl ha' hl'

theorem I04a1_card_projectiveSL :
    Nat.card (projectiveSL 3 (GaloisField 2 2)) = 20160 := by
  rw [← Nat.card_congr (projSLEquivProjectiveSL 3 (GaloisField 2 2)).toEquiv]
  exact card_projSL

theorem I04a1_three_le_card_ker {G : Type} [Group G] (hG : Nat.card G = 27)
    (f : G →* projectiveSL 3 (GaloisField 2 2)) : 3 ≤ Nat.card f.ker := by
  have h1 : Nat.card f.ker * Nat.card f.range = 27 := by
    rw [Subgroup.card_ker_mul_card_range f, hG]
  have hdvd : Nat.card f.range ∣ 20160 := by
    rw [← I04a1_card_projectiveSL]
    exact Subgroup.card_subgroup_dvd_card f.range
  have h27 : Nat.card f.range ∣ 27 := Dvd.intro_left _ h1
  have hg9 : Nat.gcd 27 20160 = 9 := by norm_num
  have hm9 : Nat.card f.range ≤ 9 := by
    have hg : Nat.card f.range ∣ 9 := by
      rw [← hg9]
      exact Nat.dvd_gcd h27 hdvd
    exact Nat.le_of_dvd (by norm_num) hg
  by_contra hlt
  push Not at hlt
  have hle : Nat.card f.ker * Nat.card f.range ≤ 2 * 9 :=
    Nat.mul_le_mul (by omega) hm9
  linarith

theorem I04a1_L_eq_range {Y : Type} [Group Y] {A' L' S : Subgroup Y}
    (hAL : A' ≤ Subgroup.normalizer (L' : Set Y)) (hLp : Group.IsPerfect L')
    (hAc : ∀ a ∈ A', ∀ a' ∈ A', a * a' = a' * a) (hL'S : L' ≤ S) (hS : S ≤ A' ⊔ L')
    (e : S ≃* Multiplicative (ZMod 3) × projectiveSL 3 (GaloisField 2 2)) :
    L' = (inrY e).range := by
  apply le_antisymm
  · rw [← commutator_eq_range e]
    calc L' = ⁅L', L'⁆ := (I04a1_commutator_self hLp).symm
      _ ≤ ⁅S, S⁆ := Subgroup.commutator_mono hL'S hL'S
  · rw [← commutator_eq_range e]
    exact I04a1_commutator_le hAL hAc hS

theorem I04a1_range_inlY_le_A {Y : Type} [Group Y] {A' S : Subgroup Y}
    (hA27 : Nat.card A' = 27) (hA'S : A' ≤ S)
    (e : S ≃* Multiplicative (ZMod 3) × projectiveSL 3 (GaloisField 2 2)) :
    (inlY e).range ≤ A' := by
  haveI : Finite (inlY e).range :=
    Nat.finite_of_card_ne_zero (by rw [card_range_inlY e]; norm_num)
  let prj : S →* projectiveSL 3 (GaloisField 2 2) := (MonoidHom.snd _ _).comp e.toMonoidHom
  let phi : A' →* projectiveSL 3 (GaloisField 2 2) := prj.comp (Subgroup.inclusion hA'S)
  have hn3 : 3 ≤ Nat.card phi.ker := I04a1_three_le_card_ker hA27 phi
  have hcrux : ∀ y ∈ phi.ker, (y : Y) ∈ (inlY e).range := by
    intro y hy
    have hyS : (y : Y) ∈ S := hA'S y.2
    have h1 : (e ⟨(y : Y), hyS⟩).2 = 1 := MonoidHom.mem_ker.mp hy
    have h2 := eq_inrY_mul_inlY e ⟨(y : Y), hyS⟩
    rw [h1, map_one, one_mul] at h2
    exact ⟨(e ⟨(y : Y), hyS⟩).1, h2.symm⟩
  have hKc : Nat.card (phi.ker.map A'.subtype) = Nat.card phi.ker :=
    Subgroup.card_map_of_injective A'.subtype_injective
  have hKle : phi.ker.map A'.subtype ≤ (inlY e).range := by
    rintro x ⟨y, hy, rfl⟩
    exact hcrux y hy
  have hKeq : phi.ker.map A'.subtype = (inlY e).range :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [card_range_inlY e, hKc]; exact hn3)
  rw [← hKeq]
  rintro x ⟨y, _, rfl⟩
  exact y.2

theorem ys03_I04a1_Z3L34_structure {Y : Type} [Group Y] {A' L' S : Subgroup Y}
    (hAL : A' ≤ Subgroup.normalizer (L' : Set Y)) (hLp : Group.IsPerfect L')
    (hA : CFSG.Assembly.IsElemAbelian 3 A') (hA27 : Nat.card A' = 27) (hA'S : A' ≤ S)
    (hL'S : L' ≤ S) (hS : S ≤ A' ⊔ L')
    (hX : Nonempty (↥S ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2))) :
    Nat.card (A' ⊓ Subgroup.centralizer (L' : Set Y) : Subgroup Y) ≤ 3 ∧
      ∀ a ∈ A', ∃ c ∈ A' ⊓ Subgroup.centralizer (L' : Set Y), ∃ b ∈ L', a = c * b := by
  obtain ⟨e0⟩ := hX
  let e : S ≃* Multiplicative (ZMod 3) × projectiveSL 3 (GaloisField 2 2) :=
    e0.trans (MulEquiv.prodCongr (MulEquiv.refl (Multiplicative (ZMod 3)))
      (projSLEquivProjectiveSL 3 (GaloisField 2 2)))
  have hk : Nat.card (GaloisField 2 2) = 4 := card_galoisField_two_two
  have hAc : ∀ a ∈ A', ∀ a' ∈ A', a * a' = a' * a := fun a ha a' ha' => I04a1_comm hA ha ha'
  have hLeq : L' = (inrY e).range := I04a1_L_eq_range hAL hLp hAc hL'S hS e
  have hZA : (inlY e).range ≤ A' := I04a1_range_inlY_le_A hA27 hA'S e
  haveI : Finite (inlY e).range :=
    Nat.finite_of_card_ne_zero (by rw [card_range_inlY e]; norm_num)
  have hAC : A' ⊓ Subgroup.centralizer (L' : Set Y) = (inlY e).range := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
      have hxC' : x ∈ Subgroup.centralizer ((inrY e).range : Set Y) := by
        rw [← hLeq]; exact hxC
      exact mem_range_inlY_of_mem_centralizer e hk (hA'S hxA) hxC'
    · rintro x ⟨z, rfl⟩
      have hzr : inlY e z ∈ (inlY e).range := ⟨z, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨hZA hzr, ?_⟩
      rw [hLeq]; exact inlY_mem_centralizer e z
  refine ⟨le_of_eq (by rw [hAC, card_range_inlY e]), ?_⟩
  intro a ha
  obtain ⟨p, z, hpz⟩ := exists_eq_inrY_mul_inlY e (hA'S ha)
  have hc : inlY e z ∈ A' ⊓ Subgroup.centralizer (L' : Set Y) := by
    rw [hAC]; exact ⟨z, rfl⟩
  have hb : inrY e p ∈ L' := by
    rw [hLeq]; exact ⟨p, rfl⟩
  exact ⟨inlY e z, hc, inrY e p, hb, hpz.trans (inrY_mul_inlY e p z)⟩

end CFSG.RankThree.PartTwo.Sec4

end
