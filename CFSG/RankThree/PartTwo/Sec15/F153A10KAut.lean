module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153A10K

open Equiv
open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V]

private theorem a10kMapFix {X : Subgroup (MulAut V)} {x : MulAut V} (hx : x ∈ X) :
    (fixV X).map (MulEquiv.toMonoidHom (x : V ≃* V)) = fixV X := by
  ext v
  constructor
  · intro h
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp h
    have hxc : x c = c := mem_fixV.mp hc x hx
    show x c ∈ fixV X
    rw [hxc]
    exact hc
  · intro hv
    exact Subgroup.mem_map.mpr ⟨v, hv, mem_fixV.mp hv x hx⟩

private noncomputable def a10kAct (X : Subgroup (MulAut V)) : X →* MulAut (V ⧸ fixV X) where
  toFun x := QuotientGroup.congr (fixV X) (fixV X) (x : MulAut V) (a10kMapFix x.2)
  map_one' := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H v => simp
  map_mul' g h := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H v => rfl

private theorem a10kPTwoOfSq {G : Type*} [Group G] (h : ∀ g : G, g ^ 2 = 1) : IsPGroup 2 G :=
  fun g => ⟨1, by simpa using h g⟩

private theorem a10kMemStab {X : Subgroup (MulAut V)} {g : X} (hg : a10kAct X g = 1) :
    (g : MulAut V) ∈ CFSG.CGT.PushingUpLit.CGT6.stabGrp (fixV X) := by
  rw [CFSG.CGT.PushingUpLit.CGT6.mem_stabGrp]
  refine ⟨fun w hw => mem_fixV.mp hw (g : MulAut V) g.2, fun v => ?_⟩
  have h1 : (QuotientGroup.mk ((g : MulAut V) v) : V ⧸ fixV X) = QuotientGroup.mk v := by
    have h := congrArg (fun φ : MulAut (V ⧸ fixV X) => φ (QuotientGroup.mk v)) hg
    exact h
  rw [QuotientGroup.eq] at h1
  have h2 := (fixV X).inv_mem h1
  rwa [mul_inv, inv_inv] at h2

private theorem a10kSqKer {X : Subgroup (MulAut V)} (hV : ∀ v : V, v ^ 2 = 1)
    (g : (a10kAct X).ker) : g ^ 2 = 1 := by
  have hg : a10kAct X (g : X) = 1 := MonoidHom.mem_ker.mp g.2
  have hsq := CFSG.CGT.PushingUpLit.CGT6.sq_eq_one_of_mem_stabGrp hV (a10kMemStab hg)
  apply Subtype.ext
  apply Subtype.ext
  simpa using hsq

private theorem a10kSqQuot (hV : ∀ v : V, v ^ 2 = 1) (X : Subgroup (MulAut V))
    (q : V ⧸ fixV X) : q ^ 2 = 1 := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_pow, hV v, QuotientGroup.mk_one]

theorem dvd_card_mulAut_quotient (hV : ∀ v : V, v ^ 2 = 1) (X : Subgroup (MulAut V)) {m : ℕ}
    (hm : Odd m) (hmX : m ∣ Nat.card X) : m ∣ Nat.card (MulAut (V ⧸ fixV X)) := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (a10kPTwoOfSq (a10kSqKer (X := X) hV))
  have hquot : Nat.card (↥X ⧸ (a10kAct X).ker) = Nat.card ↥(a10kAct X).range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (a10kAct X)).toEquiv
  have hsplit : Nat.card X = Nat.card ↥(a10kAct X).ker * Nat.card ↥(a10kAct X).range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (a10kAct X).ker, hquot, mul_comm]
  have hcop : Nat.Coprime m (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hm)
  have hmR : m ∣ Nat.card ↥(a10kAct X).range := by
    rw [hsplit, ha] at hmX
    exact Nat.Coprime.dvd_of_dvd_mul_left hcop hmX
  exact hmR.trans (Subgroup.card_subgroup_dvd_card _)

theorem not_dvd_card_of_index_le (hV : ∀ v : V, v ^ 2 = 1) (X : Subgroup (MulAut V)) {d m : ℕ}
    (hm : Odd m) (hd : (fixV X).index ≤ 2 ^ d)
    (hGL : ∀ e ≤ d, ¬ m ∣ ∏ i : Fin e, (2 ^ e - 2 ^ (i : ℕ))) : ¬ m ∣ Nat.card X := by
  intro hmX
  have h1 := dvd_card_mulAut_quotient hV X hm hmX
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (a10kPTwoOfSq (a10kSqQuot hV X))
  have hd' : 2 ^ e ≤ 2 ^ d := by
    rw [← he]
    exact hd
  have hed : e ≤ d := (Nat.pow_le_pow_iff_right (by norm_num)).1 hd'
  have hcard : Nat.card (MulAut (V ⧸ fixV X)) = ∏ i : Fin e, (2 ^ e - 2 ^ (i : ℕ)) := by
    obtain ⟨φ⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
      (fun a b : V ⧸ fixV X => mul_comm a b) (a10kSqQuot hV X) he
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL φ, CFSG.SectionRank.Ccomm.card_GL_zmod]
  rw [hcard] at h1
  exact hGL e hed h1

theorem not_twentyfive_dvd_card (hV : ∀ v : V, v ^ 2 = 1) (X : Subgroup (MulAut V))
    (hd : (fixV X).index ≤ 2 ^ 6) : ¬ 25 ∣ Nat.card X := by
  refine not_dvd_card_of_index_le hV X (d := 6) (m := 25) ⟨12, by norm_num⟩ hd ?_
  intro e he
  interval_cases e <;> norm_num [Fin.prod_univ_succ] <;> decide

theorem not_five_dvd_card (hV : ∀ v : V, v ^ 2 = 1) (X : Subgroup (MulAut V))
    (hd : (fixV X).index ≤ 2 ^ 3) : ¬ 5 ∣ Nat.card X := by
  refine not_dvd_card_of_index_le hV X (d := 3) (m := 5) ⟨2, by norm_num⟩ hd ?_
  intro e he
  interval_cases e <;> norm_num [Fin.prod_univ_succ] <;> decide

end CFSG.RankThree.PartTwo.Sec15.F153A10K
