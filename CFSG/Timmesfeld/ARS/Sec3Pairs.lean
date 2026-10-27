module

public import CFSG.Timmesfeld.ARS.Sec3Lines

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Matrix
open CFSG.Timmesfeld.RankOne NaturalModule

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec3

section Natural

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C : Subgroup G}
  (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B) (hAC : C ∈ lambdaSet R A)
  (hBC : C ∈ psiSet R B)
include hR hiso hA hB hAB hAC hBC

theorem exists_commutatorElement_eq {n : G} (hn : n ∈ C ⊔ ⁅B, C⁆) (hnC : n ∉ C) {c : G}
    (hc : c ∈ C) : ∃ a ∈ A, ⁅a, n⁆ = c := by
  obtain ⟨k, -, -, φ, hφA, -⟩ := hAB.exists_mulEquiv_SL2' hR hA
  obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hAC.1.1
  obtain ⟨θ, hθ, hrange, -⟩ :=
    exists_isNaturalModule hR hiso hA hB hAB hAC hBC φ hφA hw hw1
  have hAX : A ≤ A ⊔ B := le_sup_left
  have hmem : ∀ y ∈ C ⊔ ⁅B, C⁆, ∃ v, θ v = y := fun y hy => by
    rw [← SetLike.mem_coe, ← hrange] at hy
    exact hy
  obtain ⟨v, rfl⟩ := hmem n hn
  have hcN : c ∈ C ⊔ ⁅B, C⁆ := Subgroup.mem_sup_left hc
  obtain ⟨s, hs⟩ := (hθ.mem_fixed_upper_iff hφA hAX).1
    ⟨by rw [hrange]; exact hcN, fun a ha => hAC.1.2.2 a ha c hc⟩
  have hv1 : v 1 ≠ 0 := by
    intro h0
    apply hnC
    refine mem_of_forall_commute_of_mem_sup hR hiso hA hB hAB hAC hBC hn ?_
    exact (hθ.forall_commute_upper_iff hφA hAX v).2 h0
  set t := s / v 1 with ht
  set a : ↥(A ⊔ B) := φ.symm (upperElt (GaloisField 2 k) t) with ha
  have haA : (a : G) ∈ A := (coe_mem_iff hφA a).2 (by
    rw [ha, MulEquiv.apply_symm_apply]
    exact (mem_upperUnipotent_iff _).2 ⟨t, rfl⟩)
  refine ⟨a, haA, ?_⟩
  rw [hθ.commutatorElement_eq, ha, MulEquiv.apply_symm_apply, upperElt_mulVec_sub, ← hs]
  congr 3
  rw [ht, div_mul_cancel₀ _ hv1]

end Natural

theorem commute_of_conjSub_eq (hR : IsRootClass R) (hiso : NoIsolated R) {E P : Subgroup G}
    (hE : E ∈ R) (hP : P ∈ R) {x : G} (hx : x ∈ E) (hxP : conjSub P x = P) :
    ∀ p ∈ P, Commute x p := by
  by_cases hx1 : x = 1
  · intro p _
    rw [hx1]
    exact Commute.one_left p
  by_cases hEP : E = P
  · subst hEP
    exact fun p hp => hR.commute hE hx hp
  rcases hR.rel E hE P hP hEP with hc | hop | hsp
  · exact fun p hp => hc x hx p hp
  · exact absurd (hop.eq_one_of_conjSub_eq hx hxP) hx1
  · intro p hp
    have hne : P ≠ ⁅E, P⁆ := by
      have := hsp.symm.ne_commutator hR
      rwa [Subgroup.commutator_comm] at this
    have h1 : ⁅x, p⁆ ∈ P ⊓ ⁅E, P⁆ := by
      refine ⟨?_, Subgroup.commutator_mem_commutator hx hp⟩
      rw [commutatorElement_def]
      refine P.mul_mem ?_ (P.inv_mem hp)
      rw [← hxP]
      exact conj_mem_conjSub x hp
    rw [inf_eq_bot hR hiso hP hsp.1 hne, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

section Pairs

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C D B₀ : Subgroup G}
  (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (hAB : Opposite A B) (hAC : Opposite A C)
  (hDA : D ∈ psiSet R A) (hBC : B ∈ lambdaSet R C) (hBD : B ∈ lambdaSet R D)
  (hCD : C ∈ lambdaSet R D) (hB₀ : B₀ ≤ B ⊔ C) (hB₀A : B₀ ∈ psiSet R A)

omit [Finite G] in
include hDA hBD hCD in
theorem mem_lambdaSet_of_pairs : D ∈ lambdaSet R B ∧ D ∈ lambdaSet R C :=
  ⟨mem_lambdaSet_comm hDA.1 hBD, mem_lambdaSet_comm hDA.1 hCD⟩

include hR hiso hA hB hC hAB hBC hB₀ hB₀A in

theorem mem_lambdaSet_and_sup_eq_of_pairs : B₀ ∈ lambdaSet R B ∧ B ⊔ B₀ = B ⊔ C := by
  have hB₀R : B₀ ∈ R := hB₀A.1
  have hne : B ≠ B₀ := fun e => Special.not_opposite hR hA hB₀A.2 (e ▸ hAB)
  have hcomm : Commuting (B ⊔ C) (B ⊔ C) :=
    Commuting.sup_left (Commuting.sup_right (hR.commuting_self hB) hBC.1.2.2.symm)
      (Commuting.sup_right hBC.1.2.2 (hR.commuting_self hC))
  have hsup : B ⊔ B₀ = B ⊔ C := sup_eq_of_le_of_commuting hR hiso hB hC hB hB₀R
    hBC.1.2.2.symm le_sup_left hB₀ hne
  refine ⟨⟨⟨hB₀R, hne.symm, hcomm.mono le_sup_left hB₀⟩, ?_⟩, hsup⟩
  rw [hsup, sup_comm]
  exact hBC.2

include hR hiso hA hB hC hAB hAC hDA hBC hBD hCD in
theorem commutatorElement_mem_of_pairs {x n : G} (hx : x ∈ B ⊔ C)
    (hn : n ∈ D ⊔ ⁅A, D⁆) : ⁅x, n⁆ ∈ D := by
  obtain ⟨hDB, hDC⟩ := mem_lambdaSet_of_pairs hDA hBD hCD
  have hle : C ≤ Subgroup.normalizer (B : Set G) :=
    (commuting_iff_le_centralizer.1 hBC.1.2.2.symm).trans (Subgroup.centralizer_le_normalizer _)
  have hx' : x ∈ ((B ⊔ C : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left B C hle] at hx'
  obtain ⟨b, hb, c, hc, rfl⟩ := hx'
  dsimp only
  have hbn := commutatorElement_mem_of_mem_sup hR hiso hB hA hAB.symm hDB hDA hb hn
  have hcn := commutatorElement_mem_of_mem_sup hR hiso hC hA hAC.symm hDC hDA hc hn
  have e : ⁅b * c, n⁆ = b * ⁅c, n⁆ * b⁻¹ * ⁅b, n⁆ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  rw [e, (hBD.1.2.2 _ hcn b hb).symm.eq, mul_inv_cancel_right]
  exact D.mul_mem hcn hbn

include hR hiso hA hB hC hAB hAC hDA hBC hBD hCD in
theorem exists_mul_mem_centralizer_of_pairs {b : G} (hb : b ∈ B) :
    ∃ c ∈ C, ∀ n ∈ D ⊔ ⁅A, D⁆, Commute (b * c) n := by
  obtain ⟨hDB, hDC⟩ := mem_lambdaSet_of_pairs hDA hBD hCD
  have hDR : D ∈ R := hDA.1
  have hER : ⁅A, D⁆ ∈ R := hDA.2.1
  by_cases hb1 : b = 1
  · exact ⟨1, C.one_mem, fun n _ => by rw [hb1, mul_one]; exact Commute.one_left n⟩
  have hDE : D ≠ ⁅A, D⁆ := by
    have := hDA.2.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm] at this
  obtain ⟨n₀, hn₀E, hn₀1⟩ := hR.exists_ne_one hER
  have hn₀ : n₀ ∈ D ⊔ ⁅A, D⁆ := Subgroup.mem_sup_right hn₀E
  have hn₀D : n₀ ∉ D := fun h => hn₀1 (by
    have : n₀ ∈ D ⊓ ⁅A, D⁆ := ⟨h, hn₀E⟩
    rwa [inf_eq_bot hR hiso hDR hER hDE, Subgroup.mem_bot] at this)
  have hbn := commutatorElement_mem_of_mem_sup hR hiso hB hA hAB.symm hDB hDA hb hn₀
  obtain ⟨c, hc, hcn⟩ := exists_commutatorElement_eq hR hiso hC hA hAC.symm hDC hDA hn₀ hn₀D
    (D.inv_mem hbn)
  refine ⟨c, hc, ?_⟩
  set x := b * c with hx
  have hxBC : x ∈ B ⊔ C :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hc)
  have hxn₀ : Commute x n₀ := by
    have e : ⁅b * c, n₀⁆ = b * ⁅c, n₀⁆ * b⁻¹ * ⁅b, n₀⁆ := by
      rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
      group
    have hcD : ⁅c, n₀⁆ ∈ D := by rw [hcn]; exact D.inv_mem hbn
    rw [Commute, SemiconjBy, ← commutatorElement_eq_one_iff_mul_comm, hx, e,
      (hBD.1.2.2 _ hcD b hb).symm.eq, mul_inv_cancel_right, hcn, inv_mul_cancel]
  have hx1 : x ≠ 1 := by
    intro h1
    apply hb1
    have hbC : b ∈ C := by rw [eq_inv_of_mul_eq_one_left h1]; exact C.inv_mem hc
    have : b ∈ B ⊓ C := ⟨hb, hbC⟩
    rwa [inf_eq_bot hR hiso hB hC hBC.1.2.1, Subgroup.mem_bot] at this
  obtain ⟨E, hE, -, hxE⟩ := hBC.2 x (sup_comm B C ▸ hxBC) hx1
  obtain ⟨P, hP, hPN, hn₀P⟩ :=
    coveredBy_sup_commutator hR hiso hB hA hAB.symm hDB hDA n₀ hn₀ hn₀1
  have hxn₀' : x * n₀ * x⁻¹ = n₀ := by rw [hxn₀.eq, mul_inv_cancel_right]
  have hPx : conjSub P x = P := eq_of_mem_of_mem hR hiso (hR.conjSub_mem hP x) hP
    (hxn₀' ▸ conj_mem_conjSub x hn₀P) hn₀P hn₀1
  have hxP := commute_of_conjSub_eq hR hiso hE hP hxE hPx
  have hxD : ∀ d ∈ D, Commute x d := fun d hd =>
    ((hBD.1.2.2 d hd b hb).symm).mul_left ((hCD.1.2.2 d hd c hc).symm)
  have hDP : D ≠ P := fun e => hn₀D (e ▸ hn₀P)
  have hsup : D ⊔ P = D ⊔ ⁅A, D⁆ := sup_eq_of_le_of_commuting hR hiso hDR hER hDR hP
    hDA.2.2.2.symm le_sup_left hPN hDP
  have hcent : D ⊔ P ≤ Subgroup.centralizer ({x} : Set G) := sup_le
    (fun d hd => Subgroup.mem_centralizer_singleton_iff.2 (hxD d hd).eq.symm)
    (fun p hp => Subgroup.mem_centralizer_singleton_iff.2 (hxP p hp).eq.symm)
  intro n hn
  rw [← hsup] at hn
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hcent hn)).symm

include hR hiso hA hB hC hAB hAC hDA hBC hBD hCD hB₀ hB₀A in
theorem mem_of_forall_commute_of_pairs {k : G} (hk : k ∈ B ⊔ C)
    (hkN : ∀ n ∈ D ⊔ ⁅A, D⁆, Commute k n) : k ∈ B₀ := by
  obtain ⟨hDB, hDC⟩ := mem_lambdaSet_of_pairs hDA hBD hCD
  have hDR : D ∈ R := hDA.1
  have hER : ⁅A, D⁆ ∈ R := hDA.2.1
  have hB₀R : B₀ ∈ R := hB₀A.1
  by_cases hk1 : k = 1
  · rw [hk1]
    exact B₀.one_mem
  obtain ⟨E, hE, hEle, hkE⟩ := hBC.2 k (sup_comm B C ▸ hk) hk1
  have hEle' : E ≤ B ⊔ C := sup_comm C B ▸ hEle
  by_contra hkB₀
  have hEB₀ : E ≠ B₀ := fun e => hkB₀ (e ▸ hkE)
  have hcommBC : Commuting (B ⊔ C) (B ⊔ C) :=
    Commuting.sup_left (Commuting.sup_right (hR.commuting_self hB) hBC.1.2.2.symm)
      (Commuting.sup_right hBC.1.2.2 (hR.commuting_self hC))
  have hEA : Opposite A E := by
    have hne : A ≠ E := by
      intro e
      apply hAB.not_commuting (hR.ne_bot A hA)
      exact hcommBC.mono (e ▸ hEle') le_sup_left
    have hnc : ¬ Commuting A E := by
      by_cases hEB : E = B
      · rw [hEB]
        exact hAB.not_commuting (hR.ne_bot A hA)
      · have hEl : E ∈ lambdaSet R B := by
          refine ⟨⟨hE, hEB, hcommBC.mono le_sup_left hEle'⟩, ?_⟩
          rw [sup_eq_of_le_of_commuting hR hiso hB hC hB hE hBC.1.2.2.symm le_sup_left hEle'
            (Ne.symm hEB), sup_comm]
          exact hBC.2
        exact not_commuting_of_opposite_of_mem_lambdaSet hR hA hAB hEl
    have hns : ¬ Special R A E := by
      intro hs
      obtain ⟨D', -, huniq⟩ :=
        existsUnique_mem_psiSet_of_le hR hiso hB hA hAB.symm (mem_lambdaSet_comm hC hBC)
      exact hEB₀ ((huniq E ⟨hE, hEle', hE, hs⟩).trans (huniq B₀ ⟨hB₀R, hB₀, hB₀A⟩).symm)
    rcases hR.rel A hA E hE hne with h | h | h
    · exact absurd h hnc
    · exact h
    · exact absurd h hns
  obtain ⟨a, ha, -, hak⟩ := hEA.2.2 k hkE hk1
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hA
  obtain ⟨n, hn, hn1⟩ := hR.exists_ne_one hDR
  have hnN : n ∈ D ⊔ ⁅A, D⁆ := Subgroup.mem_sup_left hn
  have hxn : ⁅x, n⁆ ≠ 1 := fun h1 => hn1 (eq_one_of_commute_of_special hR hiso hA hDR hDA.2 hx
    hx1 hn (commutatorElement_eq_one_iff_mul_comm.1 h1))
  have h1 : ⁅x, n⁆ ∈ ⁅A, D⁆ := Subgroup.commutator_mem_commutator hx hn
  have hNA : ∀ y ∈ A, ∀ m ∈ D ⊔ ⁅A, D⁆, y * m * y⁻¹ ∈ D ⊔ ⁅A, D⁆ := fun y hy m hm => by
    rw [← conjSub_sup_commutator_eq hR hiso hB hA hAB.symm hDB hDA (Subgroup.mem_sup_right hy)]
    exact conj_mem_conjSub y hm
  have hkx : ⁅k * x * k⁻¹, n⁆ = ⁅x, n⁆ := by
    have hm := hNA x hx n hnN
    have hkn := hkN n hnN
    have hkm := hkN _ hm
    rw [commutatorElement_def, commutatorElement_def]
    calc k * x * k⁻¹ * n * (k * x * k⁻¹)⁻¹ * n⁻¹ = k * x * (k⁻¹ * n * k) * x⁻¹ * k⁻¹ * n⁻¹ := by
          group
      _ = k * (x * n * x⁻¹) * k⁻¹ * n⁻¹ := by
          rw [show k⁻¹ * n * k = n by rw [mul_assoc, ← hkn.eq, inv_mul_cancel_left]]
          group
      _ = x * n * x⁻¹ * n⁻¹ := by rw [hkm.eq, mul_inv_cancel_right]
  have hxk : k * x * k⁻¹ ∈ conjSub E a := by rw [hak]; exact conj_mem_conjSub k hx
  obtain ⟨e, he, hee⟩ := hxk
  have hee' : a * e * a⁻¹ = k * x * k⁻¹ := hee
  have h2 : ⁅x, n⁆ ∈ conjSub D a := by
    rw [← hkx, ← hee']
    have hm : a⁻¹ * n * a ∈ D ⊔ ⁅A, D⁆ := by
      have := hNA a⁻¹ (A.inv_mem ha) n hnN
      rwa [inv_inv] at this
    have hed := commutatorElement_mem_of_pairs hR hiso hA hB hC hAB hAC hDA hBC hBD hCD
      (hEle' he) hm
    have e1 : ⁅a * e * a⁻¹, n⁆ = a * ⁅e, a⁻¹ * n * a⁆ * a⁻¹ := by
      rw [commutatorElement_def, commutatorElement_def]
      group
    rw [e1]
    exact conj_mem_conjSub a hed
  have hEq := eq_of_mem_of_mem hR hiso hER (hR.conjSub_mem hDR a) h1 h2 hxn
  have hDE : D = ⁅A, D⁆ := by
    have h3 : conjSub ⁅A, D⁆ a⁻¹ = ⁅A, D⁆ :=
      conjSub_of_forall_commute fun y hy => (hDA.2.2.1 y hy a⁻¹ (A.inv_mem ha)).symm
    rw [← h3, hEq, ← conjSub_mul, inv_mul_cancel, conjSub_one]
  have := hDA.2.symm.ne_commutator hR
  rw [Subgroup.commutator_comm] at this
  exact this hDE

include hR hiso hA hB hC hAB hAC hDA hBC hBD hCD hB₀ hB₀A in
theorem commuting_of_pairs : Commuting B₀ (D ⊔ ⁅A, D⁆) := by
  set K₀ := (B ⊔ C) ⊓ Subgroup.centralizer ((D ⊔ ⁅A, D⁆ : Subgroup G) : Set G) with hK₀
  have hK₀B₀ : K₀ ≤ B₀ := fun k hk => mem_of_forall_commute_of_pairs hR hiso hA hB hC hAB hAC
    hDA hBC hBD hCD hB₀ hB₀A hk.1 fun n hn => (Subgroup.mem_centralizer_iff.1 hk.2 n hn).symm
  choose c hc hcN using fun b : B =>
    exists_mul_mem_centralizer_of_pairs hR hiso hA hB hC hAB hAC hDA hBC hBD hCD b.2
  let f : B → K₀ := fun b => ⟨b * c b, Subgroup.mul_mem _ (Subgroup.mem_sup_left b.2)
    (Subgroup.mem_sup_right (hc b)),
    Subgroup.mem_centralizer_iff.2 fun n hn => (hcN b n hn).eq.symm⟩
  have hf : Function.Injective f := by
    intro b b' h
    have h1 : (b : G) * c b = b' * c b' := congrArg Subtype.val h
    have h2 : (b' : G)⁻¹ * b = c b' * (c b)⁻¹ := by
      calc (b' : G)⁻¹ * b = (b' : G)⁻¹ * (b * c b) * (c b)⁻¹ := by group
        _ = (b' : G)⁻¹ * (b' * c b') * (c b)⁻¹ := by rw [h1]
        _ = c b' * (c b)⁻¹ := by group
    have h3 : (b' : G)⁻¹ * b ∈ B ⊓ C :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ b'.2) b.2, h2 ▸ Subgroup.mul_mem _ (hc b')
        (Subgroup.inv_mem _ (hc b))⟩
    rw [inf_eq_bot hR hiso hB hC hBC.1.2.1, Subgroup.mem_bot, inv_mul_eq_one] at h3
    exact Subtype.ext h3.symm
  have hcard : Nat.card B₀ ≤ Nat.card K₀ := by
    rw [hR.card_eq hB₀A.1 hB]
    exact Nat.card_le_card_of_injective f hf
  have heq : K₀ = B₀ := Subgroup.eq_of_le_of_card_ge hK₀B₀ hcard
  intro k hk n hn
  rw [← heq] at hk
  exact (Subgroup.mem_centralizer_iff.1 hk.2 n hn).symm

end Pairs

end Sec3

open Sec3

theorem natural_modules_of_opposite_opposite [Finite G] (hR : IsRootClass R)
    (hiso : NoIsolated R) {A B C D B₀ : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R)
    (hAB : Opposite A B) (hAC : Opposite A C) (hDA : D ∈ psiSet R A) (hBC : B ∈ lambdaSet R C)
    (hBD : B ∈ lambdaSet R D) (hCD : C ∈ lambdaSet R D) (hB₀ : B₀ ≤ B ⊔ C)
    (hB₀A : B₀ ∈ psiSet R A) :
    D ∈ lambdaSet R B ∧ B₀ ∈ lambdaSet R B ∧
      Commuting (D ⊔ ⁅A, D⁆) (B₀ ⊔ ⁅A, B₀⁆) ∧
      A ⊔ B ⊔ C ⊔ D = (D ⊔ ⁅A, D⁆) ⊔ (B₀ ⊔ ⁅A, B₀⁆) ⊔ (A ⊔ B) ∧
      ((D ⊔ ⁅A, D⁆) ⊔ (B₀ ⊔ ⁅A, B₀⁆)) ⊓ (A ⊔ B) = ⊥ := by
  obtain ⟨hDB, -⟩ := mem_lambdaSet_of_pairs hDA hBD hCD
  obtain ⟨hB₀B, hsupB₀⟩ := mem_lambdaSet_and_sup_eq_of_pairs hR hiso hA hB hC hAB hBC hB₀ hB₀A
  have hB₀N₁ := commuting_of_pairs hR hiso hA hB hC hAB hAC hDA hBC hBD hCD hB₀ hB₀A
  have hN₁N₂ : Commuting (D ⊔ ⁅A, D⁆) (B₀ ⊔ ⁅A, B₀⁆) := by
    rw [sup_commutator_eq_iSup hR hiso hB hA hAB.symm hB₀B hB₀A, commuting_iff_le_centralizer]
    refine iSup₂_le fun x hx => commuting_iff_le_centralizer.1 ?_
    have h1 := hB₀N₁.conjSub x
    rw [conjSub_sup_commutator_eq hR hiso hB hA hAB.symm hDB hDA hx] at h1
    exact h1.symm
  refine ⟨hDB, hB₀B, hN₁N₂, le_antisymm ?_ ?_, ?_⟩
  · refine sup_le (sup_le (sup_le (le_sup_left.trans le_sup_right) (le_sup_right.trans
      le_sup_right)) ?_) (le_sup_left.trans (le_sup_left.trans le_sup_left))
    calc C ≤ B ⊔ C := le_sup_right
      _ = B ⊔ B₀ := hsupB₀.symm
      _ ≤ (D ⊔ ⁅A, D⁆) ⊔ (B₀ ⊔ ⁅A, B₀⁆) ⊔ (A ⊔ B) :=
        sup_le (le_sup_right.trans le_sup_right)
          (le_sup_left.trans (le_sup_right.trans le_sup_left))
  · have hX : A ⊔ B ≤ A ⊔ B ⊔ C ⊔ D := le_sup_left.trans le_sup_left
    have hBA : ∀ x ∈ B ⊔ A, x ∈ A ⊔ B ⊔ C ⊔ D := fun x hx => hX (sup_comm B A ▸ hx)
    refine sup_le (sup_le ?_ ?_) hX
    · rw [sup_commutator_eq_iSup hR hiso hB hA hAB.symm hDB hDA]
      exact iSup₂_le fun x hx => conjSub_le le_sup_right (hBA x hx)
    · rw [sup_commutator_eq_iSup hR hiso hB hA hAB.symm hB₀B hB₀A]
      refine iSup₂_le fun x hx => conjSub_le ?_ (hBA x hx)
      exact hB₀.trans (sup_le (le_sup_right.trans (le_sup_left.trans le_sup_left))
        (le_sup_right.trans le_sup_left))
  · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    have hN₁ := commuting_sup_commutator hR hDB hDA
    have hN₂ := commuting_sup_commutator hR hB₀B hB₀A
    have hN : Commuting ((D ⊔ ⁅A, D⁆) ⊔ (B₀ ⊔ ⁅A, B₀⁆)) ((D ⊔ ⁅A, D⁆) ⊔ (B₀ ⊔ ⁅A, B₀⁆)) :=
      Commuting.sup_left (Commuting.sup_right hN₁ hN₁N₂)
        (Commuting.sup_right hN₁N₂.symm hN₂)
    exact eq_one_of_forall_commute_of_mem_sup_left hR hiso hB hA hAB.symm hDB hDA
      (sup_comm A B ▸ hx.2) fun n hn => hN x hx.1 n (Subgroup.mem_sup_left hn)

theorem natural_modules_of_opposite_special [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B C D : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hAB : Opposite A B)
    (hCA : C ∈ psiSet R A) (hDA : D ∈ psiSet R A) (hBC : B ∈ lambdaSet R C)
    (hBD : B ∈ lambdaSet R D)
    (hC' : ∃ C' ∈ R, C' ≤ B ⊔ C ∧ C' ≠ B ∧ C' ≠ C ∧ C' ∈ lambdaSet R D) :
    D ∈ lambdaSet R B ∧ C ∈ lambdaSet R B ∧
      Commuting (D ⊔ ⁅A, D⁆) (C ⊔ ⁅A, C⁆) ∧
      A ⊔ B ⊔ C ⊔ D = (D ⊔ ⁅A, D⁆) ⊔ (C ⊔ ⁅A, C⁆) ⊔ (A ⊔ B) ∧
      ((D ⊔ ⁅A, D⁆) ⊔ (C ⊔ ⁅A, C⁆)) ⊓ (A ⊔ B) = ⊥ := by
  obtain ⟨C', hC'R, hC'le, hC'B, hC'C, hC'D⟩ := hC'
  have hCR : C ∈ R := hCA.1
  have hcommBC : Commuting (B ⊔ C) (B ⊔ C) :=
    Commuting.sup_left (Commuting.sup_right (hR.commuting_self hB) hBC.1.2.2.symm)
      (Commuting.sup_right hBC.1.2.2 (hR.commuting_self hCR))
  have hsup : B ⊔ C' = B ⊔ C := sup_eq_of_le_of_commuting hR hiso hB hCR hB hC'R
    hBC.1.2.2.symm le_sup_left hC'le (Ne.symm hC'B)
  have hC'Bl : C' ∈ lambdaSet R B := by
    refine ⟨⟨hC'R, hC'B, hcommBC.mono le_sup_left hC'le⟩, ?_⟩
    rw [hsup, sup_comm]
    exact hBC.2
  have hBC' : B ∈ lambdaSet R C' := mem_lambdaSet_comm hB hC'Bl
  have hAC' : Opposite A C' := by
    have hne : A ≠ C' := by
      intro e
      apply hAB.not_commuting (hR.ne_bot A hA)
      exact hcommBC.mono (e ▸ hC'le) le_sup_left
    have hnc : ¬ Commuting A C' := not_commuting_of_opposite_of_mem_lambdaSet hR hA hAB hC'Bl
    have hns : ¬ Special R A C' := by
      intro hs
      obtain ⟨D', -, huniq⟩ :=
        existsUnique_mem_psiSet_of_le hR hiso hB hA hAB.symm (mem_lambdaSet_comm hCR hBC)
      exact hC'C ((huniq C' ⟨hC'R, hC'le, hC'R, hs⟩).trans
        (huniq C ⟨hCR, le_sup_right, hCA⟩).symm)
    rcases hR.rel A hA C' hC'R hne with h | h | h
    · exact absurd h hnc
    · exact h
    · exact absurd h hns
  obtain ⟨hDB, hCB, hN, hRe, hinf⟩ := natural_modules_of_opposite_opposite hR hiso hA hB hC'R hAB
    hAC' hDA hBC' hBD hC'D (hsup ▸ le_sup_right) hCA
  refine ⟨hDB, hCB, hN, ?_, hinf⟩
  rw [← hRe, sup_assoc A B C, ← hsup, ← sup_assoc]

end CFSG.Timmesfeld.ARS
