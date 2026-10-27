module

public import CFSG.Quasithin.Background.C41PfT
public import CFSG.Quasithin.Background.C124BlkQuot
public import CFSG.RankThree.S4Free.Stellmacher25
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.Quasithin.Background.D2Tools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_e3_a5_fixed_le :
    ∀ γ : ↥(alternatingGroup (Fin 5)), γ ≠ 1 →
      (Finset.univ.filter (fun v : Fin 5 → ZMod 2 =>
        (∑ i, v i = 0) ∧ (∀ i, v ((γ : Equiv.Perm (Fin 5)) i) = v i))).card ≤ 4 := by
  decide +kernel

theorem s16h_e3_fix_le_four {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {J : Subgroup W} (hJ : AlternatingNatural L J ⊥ 5)
    {x : MulAut W} (hxL : x ∈ L) (hx1 : x ≠ 1) :
    Nat.card ↥(J ⊓ fixV (Subgroup.zpowers x)) ≤ 4 := by
  classical
  obtain ⟨π, hsurj, -, -, hJinv, -, hsecinv, -, β, -, hβker, hβeq⟩ := hJ
  let e : (↥(G6.coreMod 5) ⧸ ((FFModel.altDn 5).ker.subgroupOf (FFModel.altDn 5).sec)) ≃*
      Multiplicative (AltHeart 5) := CFSG.Quasithin.C124.altQuotEquiv 5 (by norm_num)
  let β' : ↥J →* Multiplicative (AltHeart 5) := e.toMonoidHom.comp β
  have hβinj : Function.Injective β' := by
    intro a b hab
    have hab' : β a = β b := e.injective hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab', mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥J) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  obtain ⟨γ, hγ⟩ := hsurj ⟨x, hxL⟩
  let γ' : ↥(alternatingGroup (Fin 5)) := γ
  have hγ' : (π γ' : ↥L) = ⟨x, hxL⟩ := hγ
  have hγ1 : γ' ≠ 1 := by
    intro h
    have h2 : (γ' : (FFModel.altDn 5).Gam) = (1 : (FFModel.altDn 5).Gam) :=
      congrArg (fun z : ↥(alternatingGroup (Fin 5)) =>
        (z : (FFModel.altDn 5).Gam)) h
    have h1 : (π γ' : ↥L) = 1 := by rw [h2, map_one]
    exact hx1 (by simpa [hγ'] using congrArg Subtype.val h1)
  have hβe' : ∀ (γ : ↥(alternatingGroup (Fin 5))) (u : ↥J)
      (hu : ((π γ : ↥L) : MulAut W) (u : W) ∈ J),
      β' ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩ =
        Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ : Equiv.Perm (Fin 5))
          (Multiplicative.toAdd (β' u))) := by
    intro γ u hu
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hmu : β u = QuotientGroup.mk m := hm.symm
    have hsec : (FFModel.altDn 5).act γ (m : (FFModel.altDn 5).Amb) ∈
        (FFModel.altDn 5).sec := hsecinv γ m m.2
    have h1 := hβeq γ u m hu hsec hmu
    change e (β ⟨((π γ : ↥L) : MulAut W) (u : W), hu⟩) =
      Multiplicative.ofAdd (CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ : Equiv.Perm (Fin 5))
        (Multiplicative.toAdd (e (β u))))
    rw [h1, hmu]
    rfl
  have hfix_of_mem : ∀ (w : ↥(J ⊓ fixV (Subgroup.zpowers x))),
      CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ' : Equiv.Perm (Fin 5))
        (Multiplicative.toAdd (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J))) =
      Multiplicative.toAdd (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J)) := by
    intro w
    have hwfix : x (w : W) = w := (mem_fixV_zpowers x (w : W)).1 (Subgroup.mem_inf.1 w.2).2
    have hmem : ((π γ' : ↥L) : MulAut W) (w : W) ∈ J := by
      rw [hγ']
      exact hwfix.symm ▸ (Subgroup.mem_inf.1 w.2).1
    have h := hβe' γ' ⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ hmem
    have h2 : β' (⟨((π γ' : ↥L) : MulAut W) (w : W), hmem⟩ : ↥J) =
        β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J) := by
      apply congrArg β'
      apply Subtype.ext
      exact (show ((π γ' : ↥L) : MulAut W) (w : W) = w by rw [hγ']; exact hwfix)
    rw [h2] at h
    exact (congrArg Multiplicative.toAdd h).symm
  let P : (Fin 5 → ZMod 2) → Prop := fun v =>
    (∑ i, v i = 0) ∧ (∀ i, v ((γ' : Equiv.Perm (Fin 5)) i) = v i)
  have hcheck : (Finset.univ.filter P).card ≤ 4 := s16h_e3_a5_fixed_le γ' hγ1
  have hP_of_mem : ∀ (w : ↥(J ⊓ fixV (Subgroup.zpowers x))),
      P (((Quotient.out (Multiplicative.toAdd
        (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J)))) :
          ↥(CFSG.QuasithinUnique.evenWeight 5)) : Fin 5 → ZMod 2) := by
    intro w
    set a : AltHeart 5 := Multiplicative.toAdd (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J))
    have hfixa : CFSG.Quasithin.C41Pf.AltN.hAct 5 (γ' : Equiv.Perm (Fin 5)) a = a :=
      hfix_of_mem w
    have hq : (QuotientAddGroup.mk (Quotient.out a) : AltHeart 5) = a := Quotient.out_eq a
    have hq' : (QuotientAddGroup.mk (CFSG.Quasithin.permWeight 5 (γ' : Equiv.Perm (Fin 5))
        (Quotient.out a)) : AltHeart 5) = a := by
      rw [← CFSG.Quasithin.C41Pf.AltN.hAct_mk, hq, hfixa]
    have hdiff : CFSG.Quasithin.permWeight 5 (γ' : Equiv.Perm (Fin 5)) (Quotient.out a) -
        Quotient.out a ∈ CFSG.Quasithin.constWeight 5 := by
      have h := QuotientAddGroup.eq.mp (hq.trans hq'.symm)
      simpa [sub_eq_add_neg, add_comm] using h
    have heq : CFSG.Quasithin.permWeight 5 (γ' : Equiv.Perm (Fin 5)) (Quotient.out a) =
        Quotient.out a := by
      have h1 : CFSG.Quasithin.permWeight 5 (γ' : Equiv.Perm (Fin 5)) (Quotient.out a) -
          Quotient.out a ∈ (⊥ : AddSubgroup ↥(CFSG.QuasithinUnique.evenWeight 5)) := by
        rw [← CFSG.Quasithin.constWeight_eq_bot_of_odd (by decide : Odd 5)]
        exact hdiff
      exact sub_eq_zero.1 (AddSubgroup.mem_bot.mp h1)
    constructor
    · exact (Quotient.out a).2
    · intro i
      have h1 := congrArg (fun v : ↥(CFSG.QuasithinUnique.evenWeight 5) => (v : Fin 5 → ZMod 2)) heq
      have h2 := congrFun h1 ((γ' : Equiv.Perm (Fin 5)) i)
      rw [CFSG.Quasithin.C41Pf.AltN.permWeight_apply] at h2
      have hs : ((γ' : Equiv.Perm (Fin 5))⁻¹) ((γ' : Equiv.Perm (Fin 5)) i) = i := by simp
      rw [hs] at h2
      exact h2.symm
  have hinj : Function.Injective (fun w : ↥(J ⊓ fixV (Subgroup.zpowers x)) =>
      (⟨(((Quotient.out (Multiplicative.toAdd
        (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J)))) :
          ↥(CFSG.QuasithinUnique.evenWeight 5)) : Fin 5 → ZMod 2),
        hP_of_mem w⟩ : {v : Fin 5 → ZMod 2 // P v})) := by
    intro w w' hww'
    have hval : (((Quotient.out (Multiplicative.toAdd
        (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J)))) :
          ↥(CFSG.QuasithinUnique.evenWeight 5)) : Fin 5 → ZMod 2) =
        (((Quotient.out (Multiplicative.toAdd
        (β' (⟨(w' : W), (Subgroup.mem_inf.1 w'.2).1⟩ : ↥J)))) :
          ↥(CFSG.QuasithinUnique.evenWeight 5)) : Fin 5 → ZMod 2) :=
      congrArg (fun x : {v : Fin 5 → ZMod 2 // P v} => (x : Fin 5 → ZMod 2)) hww'
    have h1 : Quotient.out (Multiplicative.toAdd
        (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J))) =
        Quotient.out (Multiplicative.toAdd
        (β' (⟨(w' : W), (Subgroup.mem_inf.1 w'.2).1⟩ : ↥J))) :=
      Subtype.ext hval
    have h2 : Multiplicative.toAdd (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J)) =
        Multiplicative.toAdd (β' (⟨(w' : W), (Subgroup.mem_inf.1 w'.2).1⟩ : ↥J)) := by
      rw [← Quotient.out_eq (Multiplicative.toAdd
            (β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J))),
        ← Quotient.out_eq (Multiplicative.toAdd
            (β' (⟨(w' : W), (Subgroup.mem_inf.1 w'.2).1⟩ : ↥J))),
        h1]
    have h3 : β' (⟨(w : W), (Subgroup.mem_inf.1 w.2).1⟩ : ↥J) =
        β' (⟨(w' : W), (Subgroup.mem_inf.1 w'.2).1⟩ : ↥J) := Multiplicative.toAdd.injective h2
    have h4 := hβinj h3
    exact Subtype.ext (by
      have := congrArg (fun z : ↥J => (z : W)) h4
      simpa using this)
  have hfin : Nat.card {v : Fin 5 → ZMod 2 // P v} ≤ 4 := by
    haveI : Fintype {v : Fin 5 → ZMod 2 // P v} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hcheck
  exact (Nat.card_le_card_of_injective _ hinj).trans hfin

section Rank

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_e3_card_isAlt_five {X : Type} [Group X] (h : IsAlt X 5) : Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

theorem s16h_e3_isSimpleGroup_of_isAlt {X : Type} [Group X] (h : IsAlt X 5) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  exact e.isSimpleGroup

theorem s16h_e3_card_commSub_mul {A : Subgroup W} {x : MulAut W} (hx : x ∈ stabSub A) :
    Nat.card ↥(commSub A (Subgroup.zpowers x)) *
      Nat.card ↥(A ⊓ fixV (Subgroup.zpowers x)) = Nat.card ↥A := by
  rw [CFSG.RankThree.S4Free.Stell.commSub_zpowers_eq_map_commMulHom hx]
  exact CFSG.RankThree.S4Free.Stell.card_map_commMulHom_mul x A

theorem s16h_e3_card_sup_of_inf_eq_bot {A B : Subgroup W} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have hc := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B
    (fun a _ b _ => mul_comm a b)).1
  simpa [h] using hc

theorem s16h_e3_commSub_sup {A B : Subgroup W} {X : Subgroup (MulAut W)} :
    commSub (A ⊔ B) X = commSub A X ⊔ commSub B X :=
  commSub_sup_left A B X

theorem s16h_e3_commSub_zpowers_le_of_stab {A : Subgroup W} {g : MulAut W}
    (hg : g ∈ stabSub A) : commSub A (Subgroup.zpowers g) ≤ A := by
  apply commSub_le_of_invariant
  intro y hy a ha
  exact ((mem_stabSub.mp (Subgroup.zpowers_le.mpr hg hy)) a).mpr ha

theorem s16h_e3_commSub_zpowers_mul_le {A : Subgroup W} {a b : MulAut W}
    (ha : a ∈ stabSub A) (hb : b ∈ stabSub A) :
    commSub A (Subgroup.zpowers (a * b)) ≤
      commSub A (Subgroup.zpowers a) ⊔ commSub A (Subgroup.zpowers b) := by
  have hab : a * b ∈ stabSub A := (stabSub A).mul_mem ha hb
  rw [CFSG.RankThree.S4Free.Stell.commSub_zpowers_eq_map_commMulHom hab,
    CFSG.RankThree.S4Free.Stell.commSub_zpowers_eq_map_commMulHom ha,
    CFSG.RankThree.S4Free.Stell.commSub_zpowers_eq_map_commMulHom hb]
  rintro _ ⟨w, hw, rfl⟩
  have h : CFSG.RankThree.S4Free.Stell.commMulHom (a * b) w =
      CFSG.RankThree.S4Free.Stell.commMulHom a (b w) *
        CFSG.RankThree.S4Free.Stell.commMulHom b w := by
    rw [CFSG.RankThree.S4Free.Stell.commMulHom_apply,
      CFSG.RankThree.S4Free.Stell.commMulHom_apply,
      CFSG.RankThree.S4Free.Stell.commMulHom_apply]
    show a (b w) * w⁻¹ = (a (b w) * (b w)⁻¹) * (b w * w⁻¹)
    group
  rw [h]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left
      (Subgroup.mem_map_of_mem (CFSG.RankThree.S4Free.Stell.commMulHom a)
        (((mem_stabSub.mp hb) w).2 hw)))
    (Subgroup.mem_sup_right
      (Subgroup.mem_map_of_mem (CFSG.RankThree.S4Free.Stell.commMulHom b) hw))

theorem s16h_e3_four_le_card_commSub_natural {L : Subgroup (MulAut W)} {J : Subgroup W}
    (hJ : AlternatingNatural L J ⊥ 5) {x : MulAut W} (hxL : x ∈ L) (hx1 : x ≠ 1) :
    4 ≤ Nat.card ↥(commSub J (Subgroup.zpowers x)) := by
  have hJ0 := hJ
  obtain ⟨π, hπ⟩ := hJ
  have hLstab : L ≤ stabSub J :=
    CFSG.RankThree.S4Free.Stell.le_stabSub_of_forall_apply_mem
      (fun y hy u hu => hπ.2.2.2.1 ⟨y, hy⟩ u hu)
  have hcard := s16h_e3_card_commSub_mul (A := J) (hLstab hxL)
  have hJcard : Nat.card ↥J = 16 := by
    have h := s16c1610_card_alternatingNatural_odd (H := L) (U := J) (n := 5)
      (by decide : Odd 5) hJ0
    norm_num at h
    exact h
  have hfix : Nat.card ↥(J ⊓ fixV (Subgroup.zpowers x)) ≤ 4 :=
    s16h_e3_fix_le_four hJ0 hxL hx1
  have hfpos : 0 < Nat.card ↥(J ⊓ fixV (Subgroup.zpowers x)) := Nat.card_pos
  have hkey : 4 * Nat.card ↥(J ⊓ fixV (Subgroup.zpowers x)) ≤
      Nat.card ↥(commSub J (Subgroup.zpowers x)) *
        Nat.card ↥(J ⊓ fixV (Subgroup.zpowers x)) := by
    rw [hcard, hJcard]
    calc 4 * Nat.card ↥(J ⊓ fixV (Subgroup.zpowers x)) ≤ 4 * 4 :=
          Nat.mul_le_mul_left 4 hfix
      _ = 16 := by norm_num
  exact Nat.le_of_mul_le_mul_right hkey hfpos

theorem s16h_e3_iSup_fin_three_eq (I : Fin 3 → Subgroup W) :
    (⨆ i, I i) = I 0 ⊔ I 1 ⊔ I 2 := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (sup_le ?_ ?_) ?_)
  · fin_cases i
    · exact le_trans le_sup_left le_sup_left
    · exact le_trans le_sup_right le_sup_left
    · exact le_sup_right
  · exact le_iSup I 0
  · exact le_iSup I 1
  · exact le_iSup I 2

theorem s16h_e3_indep_pair {I : Fin 3 → Subgroup W}
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ ⊥)
    {i j : Fin 3} (hij : i ≠ j) : I i ⊓ I j = ⊥ := by
  refine le_bot_iff.mp ?_
  calc I i ⊓ I j ≤ I i ⊓ (⊥ ⊔ ⨆ (k : Fin 3) (_ : k ≠ i), I k) :=
        inf_le_inf_left _ (le_sup_of_le_right (le_iSup₂_of_le j (Ne.symm hij) le_rfl))
    _ ≤ ⊥ := hind i

theorem s16h_e3_iSup_ne_zero (I : Fin 3 → Subgroup W) :
    (⨆ (j : Fin 3) (_ : j ≠ 0), I j) = I 1 ⊔ I 2 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_)
    (sup_le (le_iSup₂_of_le 1 (by decide) le_rfl)
      (le_iSup₂_of_le 2 (by decide) le_rfl))
  fin_cases j
  · exact absurd rfl hj
  · exact le_sup_left
  · exact le_sup_right

theorem s16h_e3_iSup_ne_one (I : Fin 3 → Subgroup W) :
    (⨆ (j : Fin 3) (_ : j ≠ 1), I j) = I 0 ⊔ I 2 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_)
    (sup_le (le_iSup₂_of_le 0 (by decide) le_rfl)
      (le_iSup₂_of_le 2 (by decide) le_rfl))
  fin_cases j
  · exact le_sup_left
  · exact absurd rfl hj
  · exact le_sup_right

theorem s16h_e3_iSup_ne_two (I : Fin 3 → Subgroup W) :
    (⨆ (j : Fin 3) (_ : j ≠ 2), I j) = I 0 ⊔ I 1 := by
  refine le_antisymm (iSup₂_le fun j hj => ?_)
    (sup_le (le_iSup₂_of_le 0 (by decide) le_rfl)
      (le_iSup₂_of_le 1 (by decide) le_rfl))
  fin_cases j
  · exact le_sup_left
  · exact le_sup_right
  · exact absurd rfl hj

theorem s16h_e3_indep_three {I : Fin 3 → Subgroup W}
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ ⊥) :
    I 0 ⊓ (I 1 ⊔ I 2) = ⊥ ∧ I 1 ⊓ (I 0 ⊔ I 2) = ⊥ ∧ I 2 ⊓ (I 0 ⊔ I 1) = ⊥ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    refine le_bot_iff.mp ?_
  · have h := hind 0
    rwa [s16h_e3_iSup_ne_zero I, bot_sup_eq] at h
  · have h := hind 1
    rwa [s16h_e3_iSup_ne_one I, bot_sup_eq] at h
  · have h := hind 2
    rwa [s16h_e3_iSup_ne_two I, bot_sup_eq] at h

theorem s16h_e3_commSub_sum_three_ge {L : Subgroup (MulAut W)} {U : Subgroup W}
    {I : Fin 3 → Subgroup W}
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 3) (_ : j ≠ i), I j) ≤ ⊥)
    (hnat : ∀ i, AlternatingNatural L (I i) ⊥ 5)
    (hU : (⊥ ⊔ ⨆ i, I i) = U) {x : MulAut W} (hxL : x ∈ L) (hx1 : x ≠ 1) :
    64 ≤ Nat.card ↥(commSub U (Subgroup.zpowers x)) := by
  have hU' : U = I 0 ⊔ I 1 ⊔ I 2 := by
    rw [← hU, bot_sup_eq, s16h_e3_iSup_fin_three_eq]
  have hinv : ∀ i, ∀ l ∈ L, ∀ a ∈ I i, l a ∈ I i := by
    intro i l hl a ha
    obtain ⟨π, hπ⟩ := hnat i
    exact hπ.2.2.2.1 ⟨l, hl⟩ a ha
  have hle : ∀ i, commSub (I i) (Subgroup.zpowers x) ≤ I i := by
    intro i
    exact s16h_e3_commSub_zpowers_le_of_stab
      ((CFSG.RankThree.S4Free.Stell.le_stabSub_of_forall_apply_mem
        (fun y hy u hu => hinv i y hy u hu)) hxL)
  have h2 : ∀ (i j : Fin 3), i ≠ j →
      commSub (I i) (Subgroup.zpowers x) ⊓ commSub (I j) (Subgroup.zpowers x) = ⊥ := by
    intro i j hij
    refine le_bot_iff.mp (le_trans (inf_le_inf (hle i) (hle j)) ?_)
    exact le_of_eq (s16h_e3_indep_pair hind hij)
  have h01 := h2 0 1 (by decide)
  have h02 := h2 0 2 (by decide)
  have h12 := h2 1 2 (by decide)
  have hC012 : (commSub (I 0) (Subgroup.zpowers x) ⊔ commSub (I 1) (Subgroup.zpowers x)) ⊓
      commSub (I 2) (Subgroup.zpowers x) = ⊥ := by
    have hI : (I 0 ⊔ I 1) ⊓ I 2 = ⊥ := by
      have h := (s16h_e3_indep_three hind).2.2
      rwa [inf_comm] at h
    exact le_bot_iff.mp (le_trans (inf_le_inf (sup_le_sup (hle 0) (hle 1)) (hle 2))
      (le_of_eq hI))
  have hcomm : commSub U (Subgroup.zpowers x) =
      commSub (I 0) (Subgroup.zpowers x) ⊔ commSub (I 1) (Subgroup.zpowers x) ⊔
        commSub (I 2) (Subgroup.zpowers x) := by
    rw [hU', s16h_e3_commSub_sup, s16h_e3_commSub_sup]
  have hcard : Nat.card ↥(commSub U (Subgroup.zpowers x)) =
      Nat.card ↥(commSub (I 0) (Subgroup.zpowers x)) *
        Nat.card ↥(commSub (I 1) (Subgroup.zpowers x)) *
          Nat.card ↥(commSub (I 2) (Subgroup.zpowers x)) := by
    rw [hcomm, s16h_e3_card_sup_of_inf_eq_bot hC012, s16h_e3_card_sup_of_inf_eq_bot h01,
      mul_assoc]
  rw [hcard]
  have h0 := s16h_e3_four_le_card_commSub_natural (hnat 0) hxL hx1
  have h1 := s16h_e3_four_le_card_commSub_natural (hnat 1) hxL hx1
  have h2' := s16h_e3_four_le_card_commSub_natural (hnat 2) hxL hx1
  have : (4 * 4) * 4 ≤ Nat.card ↥(commSub (I 0) (Subgroup.zpowers x)) *
      Nat.card ↥(commSub (I 1) (Subgroup.zpowers x)) *
        Nat.card ↥(commSub (I 2) (Subgroup.zpowers x)) :=
    Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2'
  norm_num at this ⊢
  exact this

theorem s16h_e3_invariant_ge_eight {L : Subgroup (MulAut W)} {U S : Subgroup W}
    (hL : IsAlt ↥L 5) (hW : ∀ w : W, w ^ 2 = 1) (hUL : U ⊓ fixV L = ⊥) (hSU : S ≤ U)
    (hSne : S ≠ ⊥) (hSinv : ∀ l ∈ L, ∀ s ∈ S, l s ∈ S) : 8 ≤ Nat.card ↥S := by
  by_contra h
  have hSlt : Nat.card ↥S < 8 := lt_of_not_ge h
  have hpow : Nat.card ↥S = 2 ^ rk ↥S := card_eq_two_pow hW S
  have hrkle : rk ↥S ≤ 2 := by
    by_contra hge
    have hge3 : 3 ≤ rk ↥S := by
      have hge2 : 2 < rk ↥S := not_le.1 hge
      omega
    have h1 : 2 ^ 3 ≤ 2 ^ rk ↥S := Nat.pow_le_pow_right (by norm_num) hge3
    rw [← hpow] at h1
    norm_num at h1
    omega
  have hSle4 : Nat.card ↥S ≤ 4 := by
    rw [hpow]
    calc 2 ^ rk ↥S ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hrkle
      _ = 4 := by norm_num
  let act : ↥L → ↥S → ↥S :=
    fun l s => ⟨(l : MulAut W) s, hSinv (l : MulAut W) l.2 s s.2⟩
  have hact_one : ∀ s : ↥S, act 1 s = s := fun s => Subtype.ext (by simp [act])
  have hact_mul : ∀ (l m : ↥L) (s : ↥S), act (l * m) s = act l (act m s) :=
    fun l m s => Subtype.ext (by simp [act, map_mul])
  letI : MulAction ↥L ↥S :=
    { smul := act
      one_smul := hact_one
      mul_smul := hact_mul }
  let ψ : ↥L →* Equiv.Perm ↥S := MulAction.toPermHom ↥L ↥S
  haveI : IsSimpleGroup ↥L := s16h_e3_isSimpleGroup_of_isAlt hL
  have hker : ψ.ker = ⊥ ∨ ψ.ker = ⊤ := IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker
  rcases hker with hk | hk
  · have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hk
    have hLcard : Nat.card ↥L = 60 := s16h_e3_card_isAlt_five hL
    have hMA : Nat.card (Equiv.Perm ↥S) ≤ 24 := by
      rw [Nat.card_perm]
      calc Nat.factorial (Nat.card ↥S) ≤ Nat.factorial 4 := Nat.factorial_le hSle4
        _ = 24 := by norm_num
    have hle : Nat.card ↥L ≤ Nat.card (Equiv.Perm ↥S) := Nat.card_le_card_of_injective ψ hinj
    omega
  · have hfix : S ≤ fixV L := by
      intro s hs
      rw [mem_fixV]
      intro l hl
      have hmem : (⟨l, hl⟩ : ↥L) ∈ ψ.ker := by rw [hk]; exact Subgroup.mem_top _
      have h1 : ψ ⟨l, hl⟩ = 1 := MonoidHom.mem_ker.mp hmem
      have h2 := congrArg (fun f : Equiv.Perm ↥S => f ⟨s, hs⟩) h1
      exact congrArg Subtype.val h2
    have hcontra : S ≤ (⊥ : Subgroup W) := by
      rw [← hUL]
      exact le_inf hSU hfix
    exact hSne (le_bot_iff.mp hcontra)

end Rank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
