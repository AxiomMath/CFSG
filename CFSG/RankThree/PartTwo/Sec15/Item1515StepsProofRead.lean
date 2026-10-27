module

import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.RankThree.PartTwo.Sec15.Item157

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1515

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Quasisimple

variable {Q : Type*} [Group Q]

theorem isEmpty_mulEquiv_prod_of_isQuasisimple (hq : IsQuasisimple Q) {H₁ H₂ : Type*}
    [Group H₁] [Group H₂] [Nontrivial H₁] [Nontrivial H₂] : IsEmpty (Q ≃* H₁ × H₂) := by
  refine ⟨fun e => ?_⟩
  set U := ((MonoidHom.snd H₁ H₂).comp e.toMonoidHom).ker with hU
  set V := ((MonoidHom.fst H₁ H₂).comp e.toMonoidHom).ker with hV
  have hUm : ∀ x, x ∈ U ↔ (e x).2 = 1 := fun x => by rw [hU, MonoidHom.mem_ker]; rfl
  have hVm : ∀ x, x ∈ V ↔ (e x).1 = 1 := fun x => by rw [hV, MonoidHom.mem_ker]; rfl
  have hsup : U ⊔ V = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    have hx : x = e.symm ((e x).1, 1) * e.symm (1, (e x).2) := by
      apply e.injective
      rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, Prod.mk_mul_mk,
        mul_one, one_mul]
    rw [hx]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · rw [hUm, MulEquiv.apply_symm_apply]
    · rw [hVm, MulEquiv.apply_symm_apply]
  have hinf : U ⊓ V = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have h1 : (e x).2 = 1 := (hUm x).mp hx.1
    have h2 : (e x).1 = 1 := (hVm x).mp hx.2
    have : e x = 1 := Prod.ext h2 h1
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [this, map_one])
  rcases eq_bot_or_eq_bot_of_isQuasisimple hq (MonoidHom.normal_ker _) (MonoidHom.normal_ker _)
      hsup hinf with h | h
  · obtain ⟨a, ha⟩ := exists_ne (1 : H₁)
    have hmem : e.symm (a, 1) ∈ U := by rw [hUm, MulEquiv.apply_symm_apply]
    have h' : U = ⊥ := h
    rw [h', Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at hmem
    exact ha (congrArg Prod.fst hmem)
  · obtain ⟨b, hb⟩ := exists_ne (1 : H₂)
    have hmem : e.symm (1, b) ∈ V := by rw [hVm, MulEquiv.apply_symm_apply]
    have h' : V = ⊥ := h
    rw [h', Subgroup.mem_bot, MulEquiv.symm_apply_eq, map_one] at hmem
    exact hb (congrArg Prod.snd hmem)

theorem not_isMulCommutative_of_isTripleCover {X Y : Type*} [Group X] [Group Y]
    (h : Sec4.IsTripleCover X Y) (hY : ∃ a b : Y, a * b ≠ b * a) : ∃ a b : X, a * b ≠ b * a := by
  obtain ⟨-, ⟨φ⟩⟩ := h
  obtain ⟨a, b, hab⟩ := hY
  obtain ⟨a, rfl⟩ := φ.surjective a
  obtain ⟨b, rfl⟩ := φ.surjective b
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← map_mul, ← map_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem not_isA6CoverTimesA5_of_isQuasisimple (hq : IsQuasisimple Q) :
    ¬ IsA6CoverTimesA5 Q := by
  rintro ⟨U, V, hU, hV, hUV, hsup, ⟨hU3, -⟩, ⟨eV⟩⟩
  rcases eq_bot_or_eq_bot_of_isQuasisimple hq hU hV hsup hUV with h | h
  · subst h
    have hle : Nat.card (Subgroup.center (⊥ : Subgroup Q)) ≤ 1 := by
      rw [← Nat.card_unique (α := (⊥ : Subgroup Q))]
      exact Subgroup.card_le_card_group _
    omega
  · subst h
    have : Nontrivial (alternatingGroup (Fin 5)) := by
      have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := card_alternatingGroup_five
      rw [← Finite.one_lt_card_iff_nontrivial]
      omega
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) eV.symm.injective.nontrivial

theorem not_isCentralProductA6Covers_of_isQuasisimple (hq : IsQuasisimple Q) :
    ¬ IsCentralProductA6Covers Q := by
  rintro ⟨U, V, hU, hV, hsup, hcomm, -, hU6, hV6⟩
  have hA6 : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
      fun h => ?_⟩
    have := congrArg Subtype.val h
    revert this
    decide
  have hab : ∀ W : Subgroup Q, Sec4.IsTripleCover ↥W (alternatingGroup (Fin 6)) →
      W ≤ Subgroup.center Q → False := by
    intro W hW hWc
    obtain ⟨a, b, hab⟩ := not_isMulCommutative_of_isTripleCover hW hA6
    exact hab (Subtype.ext (Subgroup.mem_center_iff.mp (hWc a.2) b).symm)
  have hUV : U ≤ Subgroup.centralizer (V : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hU with hUt | hUc
  · refine hab V hV6 fun v hv => Subgroup.mem_center_iff.mpr fun g => ?_
    have hg : g ∈ U := hUt ▸ Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.mp (hUV hg) v hv).symm
  · exact hab U hU6 hUc

end Quasisimple

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_of_mem_scriptY4 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY4 A LB) : 3 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  have hO2 : CFSG.pCore 2 ↥Y ≠ ⊤ := by
    intro h2
    obtain ⟨-, -, -, -, hs, -⟩ := hY
    have hnt := hs.toNontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    apply hx
    rw [(QuotientGroup.eq_one_iff y).mpr (h2 ▸ Subgroup.mem_top y)]
    rfl
  exact three_dvd_card_quotient_of_eq_oPrimeResidualOf hY.2.1 (CFSG.pCore 2 ↥Y) hO2

theorem pPrimeCore_ne_top_of_mem_scriptY4 {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY4 A LB) : CFSG.pPrimeCore 3 ↥Y ≠ ⊤ := by
  intro htop
  have hc := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y)
  rw [htop, Subgroup.card_top] at hc
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc
    ((three_dvd_card_of_mem_scriptY4 hY).trans (Subgroup.card_quotient_dvd_card _))

theorem isQuasisimple_quot_pPrimeCore {A Y : Subgroup G} {LB : Subgroup G → Subgroup G}
    (hY : Y ∈ scriptY4 A LB) : IsQuasisimple (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
  have hq : IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.2.2.2
  have hO2 : CFSG.pCore 2 ↥Y ≤ CFSG.pPrimeCore 3 ↥Y := pCore_two_le_pPrimeCore_three
  set f := QuotientGroup.map (CFSG.pCore 2 ↥Y) (CFSG.pPrimeCore 3 ↥Y) (MonoidHom.id _)
    (by simpa using hO2) with hf
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨y, rfl⟩
  have hker : f.ker ≤ Subgroup.center _ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq f.normal_ker with ht | hc
    · exfalso
      apply pPrimeCore_ne_top_of_mem_scriptY4 hY
      refine eq_top_iff.mpr fun y _ => ?_
      have hy : (y : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ f.ker := ht ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hf, QuotientGroup.map_mk, MonoidHom.id_apply,
        QuotientGroup.eq_one_iff] at hy
      exact hy
    · exact hc
  exact CFSG.LocalCores.isQuasisimple_of_surjective hq f hsurj hker

theorem isoLThreePi_congr {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {p f : ℕ}
    [Fact p.Prime] (h : Sec4.IsoLThreePi X p f) : Sec4.IsoLThreePi X' p f := by
  rcases h with ⟨h1, ⟨φ⟩⟩ | ⟨h2, ⟨φ⟩⟩
  · exact Or.inl ⟨h1, ⟨e.symm.trans φ⟩⟩
  · exact Or.inr ⟨h2, ⟨e.symm.trans φ⟩⟩

theorem isTripleCover_congr {X X' S : Type*} [Group X] [Group X'] [Group S] (e : X ≃* X')
    (h : Sec4.IsTripleCover X S) : Sec4.IsTripleCover X' S := by
  obtain ⟨hcard, ⟨φ⟩⟩ := h
  have hc : (Subgroup.center X).map e.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e
  refine ⟨?_, ⟨(QuotientGroup.congr _ _ e hc).symm.trans φ⟩⟩
  rw [← hc, Subgroup.card_map_of_injective e.injective, hcard]

theorem nontrivial_alternatingGroup_five : Nontrivial (alternatingGroup (Fin 5)) := by
  rw [← Finite.one_lt_card_iff_nontrivial, card_alternatingGroup_five]
  norm_num

theorem nontrivial_J2 : Nontrivial CFSG.Blueprint.NativeSporadic.J2 := by
  rw [← Finite.one_lt_card_iff_nontrivial, KFacts.KS14.card_nativeJ2]
  norm_num

section Case148


theorem cases148_of_mem_scriptY4 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h148 : Item148 A LB) (hAab : IsMulCommutative A) {Y : Subgroup G}
    (hY : Y ∈ scriptY4 A LB) (hYΔ : Y = deltaZero A LB Y) :
    (∃ c' : G, Subgroup.zpowers c' ∈ omegaA A ∧
      Y = pPrimeCoreOf 3 Y ⊔
        deltaZero A LB (Y ⊓ Subgroup.normalizer (Subgroup.zpowers c' : Set G)) ∧
      ∃ L' ∈ lA A c',
        Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* ↥L' ⧸ aschbacherSolvableCore 3 ↥L') ∨
        ((Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
              CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 5 2))) ∨
            (∃ _ : Fact (Nat.Prime 5), Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
              CFSG.Assembly.RankThreeEven.projSU 3 5 1))) ∧
          Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7))) ∨
        (∃ (p f e : ℕ) (_ : Fact p.Prime), 1 ≤ f ∧ 1 ≤ e ∧
          Sec4.IsoLThreePi (↥L' ⧸ aschbacherSolvableCore 3 ↥L') p (f * e) ∧
          IsLThreeEpsAt (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) p f) ∨
        (Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
          (Sec4.IsTripleCover (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) (alternatingGroup (Fin 6)) ∨
            Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 5))))) ∨
    (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      (Sec4.IsTripleCover (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) CFSG.Blueprint.NativeSporadic.ON ∨
        Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 7)) ∨
        (∃ _ : Fact (Nat.Prime 7), Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))))) ∨
    (Nonempty (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y ≃* alternatingGroup (Fin 10)) ∧
      (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
        Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* alternatingGroup (Fin 7))) ∧
      WStarS4 A) ∨
    (∃ (c' : G) (L' : Subgroup G) (n m : ℕ), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      1 ≤ n ∧ 1 ≤ m ∧ Sec4.IsoLThreePi (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) 2 (3 * n) ∧
      IsLThreeEpsAt (↥L' ⧸ aschbacherSolvableCore 3 ↥L') 2 (n * m)) := by
  let := ker148_normal hY.1.2
  have hq := isQuasisimple_quot_pPrimeCore hY
  have hne := pPrimeCore_ne_top_of_mem_scriptY4 hY
  obtain ⟨e0⟩ : Nonempty (↥(img148 A Y (deltaZero A LB Y)) ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
    rw [← hYΔ]
    exact nonempty_img148_equiv hY.1.2
  have hqX : IsQuasisimple ↥(img148 A Y (deltaZero A LB Y)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq e0.symm.toMonoidHom e0.symm.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e0.symm.injective]; exact bot_le)
  have := nontrivial_alternatingGroup_five
  have := nontrivial_J2
  rcases (h148 Y hY.1).2 with h1 | h2 | h3 | h4 | h5 | h6 | h7
  ·
    exfalso
    apply hne
    rw [← hYΔ] at h1
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz, hzy⟩ := h1 y.2
    rwa [show z = y from Subtype.ext hzy] at hz
  ·
    obtain ⟨c', hc', hdec, L', hL', hcases⟩ := h2
    rw [← hYΔ] at hdec
    refine Or.inl ⟨c', hc', hdec, L', hL', ?_⟩
    rcases hcases with hφ | ⟨hL, hφ⟩ | ⟨p, f, e, hp, hf, he, hiso, hε⟩ | ⟨hJ, h6 | hφ⟩
    · obtain ⟨φ⟩ := hφ
      exact Or.inl ⟨e0.symm.trans φ⟩
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inl ⟨hL, ⟨e0.symm.trans φ⟩⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨p, f, e, hp, hf, he, hiso, IsLThreeEpsAt.of_mulEquiv e0 hε⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hJ, Or.inl (isTripleCover_congr e0 h6)⟩))
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inr (Or.inr ⟨hJ, Or.inr ⟨e0.symm.trans φ⟩⟩))
  ·
    obtain ⟨c', d, L', hc', hL', hJ, -, -, -, -, h⟩ := h3
    rcases h with hON | hCP | hA6A5 | hφ | hφ | ⟨h7, hφ⟩
    · exact Or.inr (Or.inl ⟨c', L', hc', hL', hJ,
        Or.inl (isTripleCover_congr e0 hON)⟩)
    · exact (not_isCentralProductA6Covers_of_isQuasisimple hqX hCP).elim
    · exact (not_isA6CoverTimesA5_of_isQuasisimple hqX hA6A5).elim
    · obtain ⟨φ⟩ := hφ
      exact ((isEmpty_mulEquiv_prod_of_isQuasisimple hqX).false φ).elim
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inl ⟨c', L', hc', hL', hJ, Or.inr (Or.inl ⟨e0.symm.trans φ⟩)⟩)
    · obtain ⟨φ⟩ := hφ
      exact Or.inr (Or.inl ⟨c', L', hc', hL', hJ, Or.inr (Or.inr ⟨h7, ⟨e0.symm.trans φ⟩⟩)⟩)
  ·
    obtain ⟨hφ, hL7, hW⟩ := h4
    obtain ⟨φ⟩ := hφ
    exact Or.inr (Or.inr (Or.inl ⟨⟨e0.symm.trans φ⟩, hL7, hW⟩))
  ·
    obtain ⟨c', -, L', n, m, hc', hL', hn, hm, hiso, -, -, -, hε, -⟩ := h5
    exact Or.inr (Or.inr (Or.inr ⟨c', L', n, m, hc', hL', hn, hm, isoLThreePi_congr e0 hiso,
      hε⟩))
  ·
    obtain ⟨hφ, -⟩ := h6
    obtain ⟨φ⟩ := hφ
    exact ((isEmpty_mulEquiv_prod_of_isQuasisimple hqX).false φ).elim
  ·
    exfalso
    obtain ⟨-, -, L₁, L₂, J₁, J₂, p₁, f₁, -, p₂, f₂, -, -, -, -, -, -, -, hJ₁, hJ₂, hsup, hinf,
      hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    set X := img148 A Y (deltaZero A LB Y) with hX
    have hJ₁le : img148 A Y J₁ ≤ X := hsup ▸ le_sup_left
    have hJ₂le : img148 A Y J₂ ≤ X := hsup ▸ le_sup_right
    have hC₁ : img148 A Y J₂ ≤ Subgroup.centralizer (img148 A Y J₁ : Set _) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hcomm
    have hC₂ : img148 A Y J₁ ≤ Subgroup.centralizer (img148 A Y J₂ : Set _) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hN₁ : ((img148 A Y J₁).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁le).mpr ?_
      rw [← hsup]
      exact sup_le Subgroup.le_normalizer (hC₁.trans (Subgroup.centralizer_le_normalizer _))
    have hN₂ : ((img148 A Y J₂).subgroupOf X).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂le).mpr ?_
      rw [← hsup]
      exact sup_le (hC₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    have hsup' : (img148 A Y J₁).subgroupOf X ⊔ (img148 A Y J₂).subgroupOf X = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hJ₁le hJ₂le, hsup, Subgroup.subgroupOf_self]
    have hinf' : (img148 A Y J₁).subgroupOf X ⊓ (img148 A Y J₂).subgroupOf X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (x : ↥(Y ⊔ A) ⧸ ker148 A Y) ∈ img148 A Y J₁ ⊓ img148 A Y J₂ := ⟨hx.1, hx.2⟩
      rw [hinf] at h1
      exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
    have hbot : img148 A Y J₁ = ⊥ ∨ img148 A Y J₂ = ⊥ := by
      rcases eq_bot_or_eq_bot_of_isQuasisimple hqX hN₁ hN₂ hsup' hinf' with h | h
      · left
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₁le)
      · right
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.mp (h.mono_right hJ₂le)
    have hAle : A ≤ Y ⊔ A := le_sup_right
    have key : ∀ J : Subgroup G, J ≤ Y → img148 A Y J = ⊥ →
        ∀ p f : ℕ, IsZ3PGLThreeAt ↥(img148 A Y (J ⊔ A)) p f → False := by
      intro J hJY hJ p f hZ
      rw [img148_sup (hJY.trans le_sup_left) hAle, hJ, bot_sup_eq] at hZ
      obtain ⟨a, b, hab⟩ := KFacts.KS14.ks15Z3PGLNonabelian _ p f hZ
      exact hab (img148_comm hAab a b)
    rcases hbot with h | h
    · exact key J₁ (hJ₁.trans inf_le_right) h p₁ f₁ hZ₁
    · exact key J₂ (hJ₂.trans inf_le_right) h p₂ f₂ hZ₂

end Case148

end CFSG.RankThree.PartTwo.Sec15.Proof1515
