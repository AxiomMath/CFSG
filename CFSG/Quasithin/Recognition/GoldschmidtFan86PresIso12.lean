module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresIsoLink
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresBound
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresIsoBase

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin CFSG.CosetTable

variable {A C B : Type*} [Group A] [Group C] [Group B]

section Generation

variable {x w za c : A} {y z : Fin 5 → A} {xb t w1 w2 ub cb : B} {zm ym za' : Fin 3 → B}

theorem closure_genC1 (hg : Subgroup.closure (({x, w, za, c} : Set A) ∪ Set.range y ∪
    Set.range z) = ⊤) : Subgroup.closure (Set.range (PresP1.genC x w za c y z)) = ⊤ := by
  refine eq_top_iff.2 (hg ▸ Subgroup.closure_mono ?_)
  rintro g (((rfl | rfl | rfl | rfl) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact ⟨Fin.castSucc PresP1.gx, by rw [PresP1.genC_castSucc, PresP1.gen_x]⟩
  · exact ⟨Fin.castSucc PresP1.gw, by rw [PresP1.genC_castSucc, PresP1.gen_w]⟩
  · exact ⟨Fin.castSucc PresP1.gza, by rw [PresP1.genC_castSucc, PresP1.gen_za]⟩
  · exact ⟨PresP1.gc, PresP1.genC_gc⟩
  · exact ⟨Fin.castSucc (PresP1.gy j), by rw [PresP1.genC_castSucc, PresP1.gen_y]⟩
  · exact ⟨Fin.castSucc (PresP1.gz j), by rw [PresP1.genC_castSucc, PresP1.gen_z]⟩

theorem closure_genC2 (hg : Subgroup.closure (({xb, t, w1, w2, ub, cb} : Set B) ∪ Set.range zm ∪
    Set.range ym ∪ Set.range za') = ⊤) :
    Subgroup.closure (Set.range (PresP2.genC xb t w1 w2 ub cb zm ym za')) = ⊤ := by
  refine eq_top_iff.2 (hg ▸ Subgroup.closure_mono ?_)
  rintro g ((((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact ⟨Fin.castSucc PresP2.gxb, by rw [PresP2.genC_castSucc, PresP2.gen_xb]⟩
  · exact ⟨Fin.castSucc PresP2.gt, by rw [PresP2.genC_castSucc, PresP2.gen_t]⟩
  · exact ⟨Fin.castSucc PresP2.gw1, by rw [PresP2.genC_castSucc, PresP2.gen_w1]⟩
  · exact ⟨Fin.castSucc PresP2.gw2, by rw [PresP2.genC_castSucc, PresP2.gen_w2]⟩
  · exact ⟨Fin.castSucc PresP2.gub, by rw [PresP2.genC_castSucc, PresP2.gen_ub]⟩
  · exact ⟨PresP2.gc, PresP2.genC_gc⟩
  · exact ⟨Fin.castSucc (PresP2.gzm i), by rw [PresP2.genC_castSucc, PresP2.gen_zm]⟩
  · exact ⟨Fin.castSucc (PresP2.gym i), by rw [PresP2.genC_castSucc, PresP2.gen_ym]⟩
  · exact ⟨Fin.castSucc (PresP2.gza i), by rw [PresP2.genC_castSucc, PresP2.gen_za]⟩

theorem closure_linkBc {X : GoldAmalgam A C B} {a : Fin 13 ⊕ Unit → A}
    (hl : ∀ i, AmalgamLink X (a i) (linkBc t w1 w2 ub cb zm ym za' i))
    (hg : Subgroup.closure (({t, w1, w2, ub, cb} : Set B) ∪ Set.range zm ∪ Set.range ym ∪
      Set.range za') = X.edgeB) :
    Subgroup.closure (Set.range (linkBc t w1 w2 ub cb zm ym za')) = X.edgeB := by
  refine closure_range_eq_edgeB _ (fun i => ⟨a i, hl i⟩) hg ?_
  rintro g ((((rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact ⟨Sum.inl 0, rfl⟩
  · exact ⟨Sum.inl 1, rfl⟩
  · exact ⟨Sum.inl 2, rfl⟩
  · exact ⟨Sum.inl 3, rfl⟩
  · exact ⟨Sum.inr (), rfl⟩
  · fin_cases i
    · exact ⟨Sum.inl 4, rfl⟩
    · exact ⟨Sum.inl 5, rfl⟩
    · exact ⟨Sum.inl 6, rfl⟩
  · fin_cases i
    · exact ⟨Sum.inl 7, rfl⟩
    · exact ⟨Sum.inl 8, rfl⟩
    · exact ⟨Sum.inl 9, rfl⟩
  · fin_cases i
    · exact ⟨Sum.inl 10, rfl⟩
    · exact ⟨Sum.inl 11, rfl⟩
    · exact ⟨Sum.inl 12, rfl⟩

end Generation

theorem exists_presEquiv12
    {X : GoldAmalgam A C B} (h : AdmitsPres12 X) (hA : Nat.card A = 5 * 2 ^ 12)
    (hB : Nat.card B = 3 * 2 ^ 12) :
    ∃ (φA : PG 14 p1cWords ≃* A) (φB : PG 15 p2cWords ≃* B),
      (∀ i, AmalgamLink X (φA (presLinkAc i)) (φB (presLinkBc i))) ∧
        Subgroup.closure (Set.range fun i => φB (presLinkBc i)) = X.edgeB := by
  obtain ⟨x, w, za, c, y, z, xb, t, w1, w2, ub, cb, zm, ym, za', h1, hc1, hwc, h2, hc2, h3, hc3,
    hgA, hgB, hgE, hl, hcl⟩ := h
  obtain ⟨φA, hφA⟩ : ∃ φ : PG 14 p1cWords ≃* A,
      ∀ i, φ (PresentedGroup.of i) = PresP1.genC x w za c y z i :=
    exists_mulEquiv_presented
      (lift_eq_one_of_words (PresP1.genC x w za c y z) (PresP1.lift_relsC h1 hc1 hwc))
      (closure_genC1 hgA) card_p1c_le.1 card_p1c_le.2 hA
  obtain ⟨φB, hφB⟩ : ∃ φ : PG 15 p2cWords ≃* B,
      ∀ i, φ (PresentedGroup.of i) = PresP2.genC xb t w1 w2 ub cb zm ym za' i :=
    exists_mulEquiv_presented
      (lift_eq_one_of_words (PresP2.genC xb t w1 w2 ub cb zm ym za')
        (PresP2.lift_relsC h2 h3 hc2 hc3))
      (closure_genC2 hgB) card_p2c_le.1 card_p2c_le.2 hB
  have eA : ∀ i, φA (presLinkAc i) = linkAc w za c y z i := by
    rintro (i | ⟨⟩)
    · have := map_linkA φA.toMonoidHom (PresentedGroup.of (Fin.castSucc PresP1.gw))
        (PresentedGroup.of (Fin.castSucc PresP1.gza))
        (fun j => PresentedGroup.of (Fin.castSucc (PresP1.gy j)))
        (fun j => PresentedGroup.of (Fin.castSucc (PresP1.gz j))) i
      simp only [MulEquiv.coe_toMonoidHom, hφA, PresP1.genC_castSucc, PresP1.gen_w,
        PresP1.gen_za, PresP1.gen_y, PresP1.gen_z] at this
      exact this
    · exact (hφA _).trans PresP1.genC_gc
  have eB : ∀ i, φB (presLinkBc i) = linkBc t w1 w2 ub cb zm ym za' i := by
    rintro (i | ⟨⟩)
    · have := map_linkB φB.toMonoidHom (PresentedGroup.of (Fin.castSucc PresP2.gt))
        (PresentedGroup.of (Fin.castSucc PresP2.gw1))
        (PresentedGroup.of (Fin.castSucc PresP2.gw2))
        (PresentedGroup.of (Fin.castSucc PresP2.gub))
        (fun i => PresentedGroup.of (Fin.castSucc (PresP2.gzm i)))
        (fun i => PresentedGroup.of (Fin.castSucc (PresP2.gym i)))
        (fun i => PresentedGroup.of (Fin.castSucc (PresP2.gza i))) i
      simp only [MulEquiv.coe_toMonoidHom, hφB, PresP2.genC_castSucc, PresP2.gen_t,
        PresP2.gen_w1, PresP2.gen_w2, PresP2.gen_ub, PresP2.gen_zm, PresP2.gen_ym,
        PresP2.gen_za] at this
      exact this
    · exact (hφB _).trans PresP2.genC_gc
  have hl0 : ∀ i, AmalgamLink X (linkAc w za c y z i) (linkBc t w1 w2 ub cb zm ym za' i) := by
    rintro (i | ⟨⟩)
    · exact hl.link i
    · exact hcl
  refine ⟨φA, φB, fun i => by rw [eA, eB]; exact hl0 i, ?_⟩
  have : (fun i => φB (presLinkBc i)) = linkBc t w1 w2 ub cb zm ym za' := funext eB
  rw [this]
  exact closure_linkBc hl0 hgE

end CFSG.Quasithin.Fan86
