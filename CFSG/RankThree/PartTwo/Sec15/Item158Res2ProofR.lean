module

public import CFSG.RankThree.PartTwo.Sec15.Item158StepsProof
import CFSG.RankThree.PartTwo.Sec13.Item138NMod9
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree
import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofTypeC
import CFSG.RankThree.PartTwo.Sec15.Item157Proof
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.PartTwo.KFacts.K72SLPiIdent
import CFSG.RankThree.PartTwo.Sec19.Step1917EqProofArith

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree)

namespace Proof158R

theorem eq_of_order_eq {π π' : Bool} {x y : ℕ} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (h : x ^ 3 * (x ^ 2 - 1) * cond π (x ^ 3 - 1) (x ^ 3 + 1) =
      y ^ 3 * (y ^ 2 - 1) * cond π' (y ^ 3 - 1) (y ^ 3 + 1)) : π = π' ∧ x = y := by
  cases π <;> cases π' <;> simp only [Bool.cond_true, Bool.cond_false] at h
  · refine ⟨rfl, ?_⟩
    rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
    · exact absurd h (KFacts.su3Order_lt (by omega) hxy).ne
    · exact hxy
    · exact absurd h.symm (KFacts.su3Order_lt (by omega) hxy).ne
  · exact absurd h.symm (Sec19.Step1917EqProof.sl3Order_ne_su3Order hy hx)
  · exact absurd h (Sec19.Step1917EqProof.sl3Order_ne_su3Order hx hy)
  · refine ⟨rfl, ?_⟩
    rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
    · exact absurd h (KFacts.sl3Order_lt (by omega) hxy).ne
    · exact hxy
    · exact absurd h.symm (KFacts.sl3Order_lt (by omega) hxy).ne

theorem factorization_twentySeven_mul {m : ℕ} (hm : ¬ 3 ∣ m) : (27 * m).factorization 3 = 3 := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero, show (27 : ℕ) = 3 ^ 3 by norm_num,
    Nat.Prime.factorization_pow Nat.prime_three]
  simp

theorem factorization_card_slPi {K : Type} [Field K] {π : Bool} {p f : ℕ}
    (hK : PiField π p f K) (hq : ModThree π (p ^ f)) (h9 : ¬ (p ^ f % 9 = 1 ∨ p ^ f % 9 = 8)) :
    (Nat.card (slPi π 3 (p ^ f) K)).factorization 3 = 3 := by
  rw [card_slPi_three hK]
  cases π
  · change p ^ f % 3 = 2 at hq
    obtain ⟨m, hm3, hm⟩ := Item138Proof.su3Order_eq_of_not_modNine hq (by omega)
    simp only [Bool.cond_false]
    rw [hm]
    exact factorization_twentySeven_mul hm3
  · change p ^ f % 3 = 1 at hq
    obtain ⟨m, hm3, hm⟩ := Item138Proof.sl3Order_eq_of_not_modNine hq (by omega)
    simp only [Bool.cond_true]
    rw [hm]
    exact factorization_twentySeven_mul hm3

theorem factorization_three_le_of_le {Q : Type*} [Group Q] [Finite Q] {X Y : Subgroup Q}
    (h : X ≤ Y) : (Nat.card X).factorization 3 ≤ (Nat.card Y).factorization 3 :=
  (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (Subgroup.card_dvd_of_le h) 3

theorem le_factorization_three_of_dvd {Q : Type*} [Group Q] [Finite Q] {X : Subgroup Q} {k : ℕ}
    (h : 3 ^ k ∣ Nat.card X) : k ≤ (Nat.card X).factorization 3 :=
  (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h

theorem factorization_three_card_map_mk {Q : Type*} [Group Q] [Finite Q] (N : Subgroup Q)
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) (X : Subgroup Q) :
    (Nat.card (X.map (QuotientGroup.mk' N))).factorization 3 = (Nat.card X).factorization 3 := by
  set f : X →* Q ⧸ N := (QuotientGroup.mk' N).comp X.subtype with hf
  have hrange : f.range = X.map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card X := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    intro h3
    apply hN
    refine h3.trans ?_
    have hle : f.ker.map X.subtype ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : QuotientGroup.mk' N (x : Q) = 1 := hx
      exact (QuotientGroup.eq_one_iff _).mp hx'
    rw [← Subgroup.card_map_of_injective X.subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  rw [← hrange, ← hcard, mul_comm,
    Proof157.factorization_three_mul Nat.card_pos.ne' Nat.card_pos.ne' hker]

variable {G : Type} [Group G] [Finite G]

theorem factorization_three_card_lBarA {c : G} {L X : Subgroup G}
    (hle : L ⊔ X ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    (Nat.card (lBarA c L X)).factorization 3 = (Nat.card (L ⊔ X : Subgroup G)).factorization 3 := by
  have hθ := (solvable_prime_complement_core_characterization
    (H := Subgroup.normalizer (Subgroup.zpowers c : Set G)) Nat.prime_three).2.2.1
  rw [lBarA, factorization_three_card_map_mk _ hθ,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem isZ3PGLThreeAt_and_factorization {A L E : Subgroup G} {c : G} (hD : Sec13Data G A c L)
    (hcE : c ∈ E) (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hEN : E ≤ Subgroup.normalizer (L : Set G)) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L E))
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    (h9 : ¬ (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8)) :
    Sec14.IsZ3PGLThreeAt ↥(lBarA c L E) p e ∧ (Nat.card (lBarA c L E)).factorization 3 = 4 := by
  have hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEH : E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := fun x hx =>
    centralizer_le_normalizer_zpowers c
      (Subgroup.mem_centralizer_singleton_iff.mpr (hEc x hx c hcE))
  obtain ⟨π, p', f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
  have hπ : π = false → CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p' f K :=
    fun h => by subst h; exact hK.unitary
  set Λ := (Sec12.lBar c L).subgroupOf (lBarA c L E) with hΛ
  have hcomm := commutator_lBarA_eq hD hEN hEH hEc
  have hΛp : Group.IsPerfect Λ := by
    have := isPerfect_lBar hD
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).symm.surjective
  have hq2 : 2 < p' ^ f := by
    by_contra hle
    have h2 : p' ^ f = 2 := by
      have : 2 ≤ p' ^ f :=
        le_trans hK.prime.two_le (Nat.le_self_pow (by have := hK.one_le; omega) _)
      omega
    cases π
    · have hs := isSolvable_projImage_glPi_two hK h2
      have : Group.IsSolvable (lBarA c L E) :=
        Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
      have hΛs : Group.IsSolvable Λ := inferInstance
      have : Nontrivial (Sec12.lBar c L) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr (lBar_ne_bot hD)
      have : Nontrivial Λ :=
        (Subgroup.subgroupOfEquivOfLe
          (lBar_le_lBarA (c := c) (L := L) (A := E))).surjective.nontrivial
      exact Group.IsPerfect.not_isSolvable Λ hΛs
    · change p' ^ f % 3 = 1 at hq
      omega
  have hmap : Λ.map φ.toMonoidHom = (⊥ : Subgroup (Multiplicative (ZMod 3))).prod
      ((projImage (slPi π 3 (p' ^ f) K)).subgroupOf (projImage (glPi π 3 (p' ^ f) K))) := by
    rw [hΛ, ← hcomm, ← commutator_projImage_glPi hK hq2, ← commutator_zthree_prod, commutator_def,
      Subgroup.map_commutator, Subgroup.map_top_of_surjective _ φ.surjective, commutator_def]
  have hSG : projImage (slPi π 3 (p' ^ f) K) ≤ projImage (glPi π 3 (p' ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hcardΛ : Nat.card Λ = Nat.card (projImage (slPi π 3 (p' ^ f) K)) := by
    rw [← Subgroup.card_map_of_injective (f := φ.toMonoidHom) φ.injective, hmap,
      Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, Subgroup.card_bot, one_mul]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG).toEquiv
  have hcardL : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = Nat.card Λ := by
    obtain ⟨η, -⟩ := exists_lBarEquiv hD.mem_thetaComponentsAt
    rw [Nat.card_congr η.toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe lBar_le_lBarA).toEquiv.symm
  obtain ⟨π₀, K₀, _, hK₀, hq₀, ⟨φ₀⟩⟩ := exists_projImage_model he hL3
  have h1 := card_projImage_slPi_mul_three hK₀ hq₀
  have h2 := card_projImage_slPi_mul_three hK hq
  rw [← Nat.card_congr φ₀.toEquiv, hcardL, hcardΛ, h2] at h1
  have hpe2 : 2 ≤ p ^ e :=
    le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow (by omega) _)
  obtain ⟨-, hqq⟩ := eq_of_order_eq (by omega) hpe2 h1
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by have := hK.one_le; omega⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  obtain ⟨rfl, rfl⟩ := Nat.Prime.pow_inj hK.prime (Fact.out : p.Prime) hqq
  refine ⟨⟨π, K, inferInstance, hK, hq, ⟨φ⟩⟩, ?_⟩
  have := hK.finite
  have hcard : Nat.card (lBarA c L E) = 3 * Nat.card (slPi π 3 (p' ^ (f' + 1)) K) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Sec16.ProofKSL3Two.card_projImage_glPi hK,
      Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)), Nat.card_zmod]
  rw [hcard, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    factorization_card_slPi hK hq h9, Nat.Prime.factorization_self Nat.prime_three]

theorem sup_eq_of_factorization_three_le {P E L : Subgroup G} (hP : IsPGroup 3 P) (hEP : E ≤ P)
    (hPN : P ≤ Subgroup.normalizer (L : Set G))
    (hv : (Nat.card (P ⊔ L : Subgroup G)).factorization 3 ≤
      (Nat.card (E ⊔ L : Subgroup G)).factorization 3) :
    P ⊔ L = E ⊔ L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : E ⊔ L ≤ P ⊔ L := sup_le_sup_right hEP L
  have hnd := Proof157.not_dvd_relIndex_of_factorization_three_eq hle
    (le_antisymm hv (factorization_three_le_of_le hle))
  have h1 := Sec6.card_sup_mul_card_inf hPN
  have h2 := Subgroup.relIndex_mul_card L (P ⊔ L)
  rw [inf_of_le_left le_sup_right] at h2
  have h3 : L.relIndex (P ⊔ L) * Nat.card (P ⊓ L : Subgroup G) = Nat.card P := by
    have hL0 : 0 < Nat.card L := Nat.card_pos
    have h4 : L.relIndex (P ⊔ L) * Nat.card (P ⊓ L : Subgroup G) * Nat.card L =
        Nat.card P * Nat.card L := by
      rw [← h1, ← h2]
      ring
    exact Nat.eq_of_mul_eq_mul_right hL0 h4
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : (E ⊔ L).relIndex (P ⊔ L) ∣ 3 ^ k := by
    rw [← hk]
    exact (Subgroup.relIndex_dvd_of_le_left (P ⊔ L) le_sup_right).trans (Dvd.intro _ h3)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hj0 : j = 0 := by
    by_contra hj0
    exact hnd (hj ▸ dvd_pow_self 3 hj0)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_antisymm hj hle

theorem isSylowOf_zpowers_sup {F L : Subgroup G} {c : G} (hcF : c ∈ F) (hc3 : orderOf c = 3)
    (hcL : c ∉ L) (hFc : F ≤ Subgroup.centralizer ({c} : Set G))
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hF27 : Nat.card F = 27)
    (hF9 : Nat.card (F ⊓ L : Subgroup G) = 9) (hL9 : (Nat.card L).factorization 3 = 2) :
    CFSG.ABGLocalTools.IsSylowOf 3 F (Subgroup.zpowers c ⊔ L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLbot := Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc3 hcL
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer ((F ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hFc hx.1))
  have h1 := Sec6.card_sup_mul_card_inf hcN
  have hbot : Subgroup.zpowers c ⊓ (F ⊓ L) = ⊥ := by
    rw [eq_bot_iff, ← hLbot]
    exact fun x hx => ⟨hx.2.2, hx.1⟩
  rw [hbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3, hF9] at h1
  have hle : Subgroup.zpowers c ⊔ (F ⊓ L) ≤ F := sup_le (Subgroup.zpowers_le.mpr hcF) inf_le_left
  have heq : Subgroup.zpowers c ⊔ (F ⊓ L) = F := Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hFle : F ≤ Subgroup.zpowers c ⊔ L := by
    rw [← heq]
    exact sup_le_sup_left inf_le_right _
  have hcLN : Subgroup.zpowers c ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hx))
  have h2 := Sec6.card_sup_mul_card_inf hcLN
  rw [inf_comm, hLbot, Subgroup.card_bot, mul_one, Nat.card_zpowers, hc3] at h2
  have hv : (Nat.card (Subgroup.zpowers c ⊔ L : Subgroup G)).factorization 3 = 3 := by
    rw [h2, Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply, hL9,
      Nat.Prime.factorization_self Nat.prime_three]
  exact CFSG.ABGLocalTools.isSylowOf_of_card hFle (by rw [hv, hF27]; norm_num)

theorem nontrivial_of_isQuasisimple {X : Type*} [Group X] (hq : IsQuasisimple X) :
    Nontrivial X := by
  obtain ⟨x, y, hxy⟩ := hq.2.2
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply hxy
  have : Subsingleton (X ⧸ Subgroup.center X) := QuotientGroup.mk_surjective.subsingleton
  exact Subsingleton.elim _ _

end Proof158R

open Proof158R Proof158Steps

theorem step158R : Step158R := by
  intro G _ _ A c L h p e _ he hL3 Y hY _ P _ hP _ E F hC hPGL h9 hSyl
  have hD := h.toSec13Data
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLH : L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hD.le_centralizer.trans (centralizer_le_normalizer_zpowers c)
  have hEL : E ⊔ L ≤ Subgroup.centralizer ({c} : Set G) :=
    sup_le (le_centralizer_of_mem hC.elem.1 hC.mem_c) hD.le_centralizer
  have hELH : E ⊔ L ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    hEL.trans (centralizer_le_normalizer_zpowers c)
  have hθL : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hL9 : (Nat.card L).factorization 3 = 2 := by
    rw [Proof157.factorization_three_card_quotient _ hθL]
    exact Item138Proof.factorization_card_three_eq_two he hL3 h9
  have hHL : Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    Sec16.normalizer_zpowers_le_normalizer_L h (Nat.dvd_of_factorization_pos (by omega))
  obtain ⟨hAt, hEL4⟩ := isZ3PGLThreeAt_and_factorization hD hC.mem_c hC.elem hC.le_normalizer
    hPGL he hL3 h9
  have hEL4' : (Nat.card (E ⊔ L : Subgroup G)).factorization 3 = 4 := by
    have := factorization_three_card_lBarA (sup_le hLH (hELH.trans' le_sup_left) :
      L ⊔ E ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    rw [hEL4, sup_comm] at this
    exact this.symm
  have hFEL : F ≤ E ⊔ L := hC.isF.1.1
  have hEFEL : E ⊔ F ≤ E ⊔ L := sup_le le_sup_left hFEL
  have hcardEF := hSyl.card_eq
  have hH4 : (Nat.card (Subgroup.normalizer (Subgroup.zpowers c : Set G))).factorization 3 = 4 := by
    apply le_antisymm
    · rw [← hEL4']
      apply le_factorization_three_of_dvd
      rw [← hcardEF]
      exact Subgroup.card_dvd_of_le hEFEL
    · rw [← hEL4']
      exact factorization_three_le_of_le hELH
  have hPH : P ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := hP.le.trans inf_le_left
  have hPL : P ⊔ L = E ⊔ L := by
    refine sup_eq_of_factorization_three_le hP.isPGroup hC.le_p (hPH.trans hHL) ?_
    rw [hEL4', ← hH4]
    exact factorization_three_le_of_le (sup_le hPH hLH)
  have hRP : omegaOneThree P ≤ P := (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hER : E ≤ omegaOneThree P := fun x hx =>
    Subgroup.subset_closure ⟨hC.le_p hx, hC.elem.2 x hx⟩
  have hRL : omegaOneThree P ⊔ L = E ⊔ L :=
    le_antisymm (sup_le ((hRP.trans le_sup_left).trans hPL.le) le_sup_right)
      (sup_le_sup_right hER L)
  have hbar : lBarA c L (omegaOneThree P) = lBarA c L E := by
    simp only [lBarA, show L ⊔ omegaOneThree P = L ⊔ E by rw [sup_comm, hRL, sup_comm]]
  refine ⟨hbar ▸ hAt, by rw [hRL]; exact hEL4', ?_, ?_⟩
  ·
    rw [hRL]
    apply le_antisymm
    · rw [← hEL4']
      exact factorization_three_le_of_le inf_le_left
    · have hEFY : E ⊔ F ≤ (E ⊔ L) ⊓ Subgroup.normalizer (Y : Set G) :=
        le_inf hEFEL (sup_le (hC.le_p.trans (hP.le.trans inf_le_right)) hC.le_normalizer_Y)
      rw [← hH4]
      apply le_factorization_three_of_dvd
      rw [← hcardEF]
      exact Subgroup.card_dvd_of_le hEFY
  ·
    have hFE : partTwoF G = partTwoE G :=
      (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
    have hFE' : F ∈ partTwoE G := mem_partTwoE_of_le_normalizer hY.2 hC.isF.1.2.1
      hC.isF.1.2.2.1 hC.le_normalizer_Y
    have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hD.mem_A
    have hcF : c ∈ F := mem_of_mem_partTwoF (hFE ▸ hFE') hc3 (hFEL.trans hEL)
    have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt
    have := nontrivial_of_isQuasisimple hq
    have hcL : c ∉ L := not_mem_of_center_eq_bot hD
      (Sec14.center_eq_bot_of_isLThreePi ⟨p, e, inferInstance, he, hL3⟩ hq.1)
    exact isSylowOf_zpowers_sup hcF hD.orderOf_eq hcL (hFEL.trans hEL) hD.le_centralizer
      hC.isF.1.2.2.1 hC.isF.2 hL9

end CFSG.RankThree.PartTwo.Sec15
