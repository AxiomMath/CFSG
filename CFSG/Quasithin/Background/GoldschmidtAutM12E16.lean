module

public import CFSG.Quasithin.Background.GoldschmidtAutM12Tab

public section

namespace CFSG.Quasithin.F6

open CFSG.Assembly CFSG.Quasithin

namespace AutM12Recog

namespace Tab

@[expose] def posWord {G : Type} [Group G] (x : ℕ → G) : List ℕ → G
  | [] => 1
  | i :: w => x i * posWord x w

@[expose] def lwordD {D : Type} (mulD : D → D → D) (oneD : D) (xl : List D) : List ℕ → D
  | [] => oneD
  | i :: w => mulD (xl.getD i oneD) (lwordD mulD oneD xl w)

theorem rel_posWord {G D : Type} [Group G] (R : Rep G D) (x : ℕ → G) (xl : List D)
    (hx : ∀ i, i < xl.length → R.rel (x i) (xl.getD i R.oneD)) (w : List ℕ)
    (hw : ∀ i ∈ w, i < xl.length) :
    R.rel (posWord x w) (lwordD R.mulD R.oneD xl w) := by
  induction w with
  | nil => exact R.rel_one
  | cons i w ih =>
    have h1 := hx i (hw i List.mem_cons_self)
    have h2 := ih fun j hj => hw j (List.mem_cons_of_mem _ hj)
    exact R.rel_mul _ _ _ _ h1 h2

structure E16Data (D : Type) where
  gd : List D
  hEls : List D
  hPar : List ℕ
  hLab : List ℕ
  hRm : List (List ℕ)
  e1Els : List D
  e1Par : List ℕ
  e1Lab : List ℕ
  e1Rm : List (List ℕ)
  e2Els : List D
  e2Par : List ℕ
  e2Lab : List ℕ
  e2Rm : List (List ℕ)

namespace E16Data

variable {D : Type} [DecidableEq D]

@[expose] def Ok (mulD : D → D → D) (oneD : D) (d : E16Data D) : Prop :=
  d.gd.length = 6 ∧ d.hEls.length = 64 ∧ d.e1Els.length = 16 ∧ d.e2Els.length = 16 ∧
    ValidD mulD oneD d.gd d.hEls d.hPar d.hLab d.hRm ∧
    ValidD mulD oneD (d.gd.take 4) d.e1Els d.e1Par d.e1Lab d.e1Rm ∧
    ValidD mulD oneD (d.gd.take 2 ++ d.gd.drop 4) d.e2Els d.e2Par d.e2Lab d.e2Rm ∧
    (∀ i, i < 16 → ∀ j, j < 16 → mulD (d.e1Els.getD i oneD) (d.e1Els.getD j oneD) =
      mulD (d.e1Els.getD j oneD) (d.e1Els.getD i oneD)) ∧
    (∀ i, i < 16 → mulD (d.e1Els.getD i oneD) (d.e1Els.getD i oneD) = oneD) ∧
    (∀ i, i < 16 → ∀ j, j < 16 → mulD (d.e2Els.getD i oneD) (d.e2Els.getD j oneD) =
      mulD (d.e2Els.getD j oneD) (d.e2Els.getD i oneD)) ∧
    (∀ i, i < 16 → mulD (d.e2Els.getD i oneD) (d.e2Els.getD i oneD) = oneD) ∧
    d.gd.getD 4 oneD ∉ d.e1Els

instance (mulD : D → D → D) (oneD : D) (d : E16Data D) : Decidable (d.Ok mulD oneD) := by
  unfold Ok
  infer_instance

end E16Data

theorem hasTwoE16_of_rep {G D : Type} [Group G] [Finite G] [DecidableEq D] (R : Rep G D)
    (d : E16Data D) (hok : d.Ok R.mulD R.oneD) (gens : ℕ → G)
    (hgd : ∀ a, a < 6 → R.rel (gens a) (d.gd.getD a R.oneD)) (Q : Sylow 2 G) :
    HasTwoE16 ↥(Q : Subgroup G) := by
  obtain ⟨hgl, hHl, hE1l, hE2l, hH, hE1, hE2, hc1, hs1, hc2, hs2, hne⟩ := hok
  set H := Subgroup.closure (gens '' {a | a < 6}) with hHdef
  set E1 := Subgroup.closure (gens '' {a | a < 4}) with hE1def
  set E2 := Subgroup.closure ((fun a => gens ([0, 1, 4, 5].getD a 0)) '' {a | a < 4}) with hE2def
  have hgd1 : ∀ a, a < 4 → R.rel (gens a) ((d.gd.take 4).getD a R.oneD) := by
    intro a ha
    have h1 := hgd a (by omega)
    have h2 : (d.gd.take 4).getD a R.oneD = d.gd.getD a R.oneD := by
      rw [List.getD_eq_getElem _ _ (by simp [hgl]; omega), List.getD_eq_getElem _ _ (by omega),
        List.getElem_take]
    rw [h2]
    exact h1
  have hgd2 : ∀ a, a < 4 → R.rel (gens ([0, 1, 4, 5].getD a 0))
      ((d.gd.take 2 ++ d.gd.drop 4).getD a R.oneD) := by
    intro a ha
    interval_cases a
    · simpa [List.getD_eq_getElem?_getD, hgl] using hgd 0 (by omega)
    · simpa [List.getD_eq_getElem?_getD, hgl] using hgd 1 (by omega)
    · simpa [List.getD_eq_getElem?_getD, hgl] using hgd 4 (by omega)
    · simpa [List.getD_eq_getElem?_getD, hgl] using hgd 5 (by omega)
  have hlen1 : (d.gd.take 4).length = 4 := by simp [hgl]
  have hlen2 : (d.gd.take 2 ++ d.gd.drop 4).length = 4 := by simp [hgl]
  obtain ⟨hHmem, -, hHcard⟩ := Tab.card_closure_of_valid (R := R) gens 6 hgl hgd hH
  obtain ⟨hE1mem, -, hE1card⟩ := Tab.card_closure_of_valid (R := R) gens 4 hlen1 hgd1 hE1
  obtain ⟨hE2mem, -, hE2card⟩ := Tab.card_closure_of_valid (R := R)
    (fun a => gens ([0, 1, 4, 5].getD a 0)) 4 hlen2 hgd2 hE2
  have hE1a : IsElemAbelian 2 E1 :=
    Tab.isElemAbelian_of_valid (R := R) gens 4 hlen1 hgd1 hE1
      (by rw [hE1l]; exact hc1) (by rw [hE1l]; exact hs1)
  have hE2a : IsElemAbelian 2 E2 :=
    Tab.isElemAbelian_of_valid (R := R) (fun a => gens ([0, 1, 4, 5].getD a 0)) 4 hlen2 hgd2 hE2
      (by rw [hE2l]; exact hc2) (by rw [hE2l]; exact hs2)
  have hgenH : ∀ a, a < 6 → gens a ∈ H := fun a ha => Subgroup.subset_closure ⟨a, ha, rfl⟩
  have hE1H : E1 ≤ H := by
    rw [hE1def, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a < 4 := ha
    exact hgenH a (by omega)
  have hE2H : E2 ≤ H := by
    rw [hE2def, Subgroup.closure_le]
    rintro _ ⟨a, ha, rfl⟩
    have ha' : a < 4 := ha
    refine hgenH _ ?_
    interval_cases a <;> simp
  have hHp : IsPGroup 2 H := IsPGroup.of_card (n := 6) (by rw [hHcard, hHl]; norm_num)
  have hne12 : E1 ≠ E2 := by
    intro h
    have hg4 : gens 4 ∈ E2 := Subgroup.subset_closure ⟨2, show (2 : ℕ) < 4 by norm_num, by simp⟩
    rw [← h] at hg4
    obtain ⟨j, hj, hjr⟩ := hE1mem _ hg4
    apply hne
    rw [R.rel_uniq _ _ _ (hgd 4 (by omega)) hjr]
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  exact hasTwoE16_sylow hHp hE1H hE2H hE1a hE2a (hE1card.trans hE1l) (hE2card.trans hE2l) hne12 Q

end Tab

end AutM12Recog

end CFSG.Quasithin.F6
