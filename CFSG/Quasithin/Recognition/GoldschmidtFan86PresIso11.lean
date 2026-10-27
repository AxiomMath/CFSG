module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresIsoLink
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresBound
public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresIsoBase

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin CFSG.CosetTable

variable {A C B : Type*} [Group A] [Group C] [Group B]

section Generation

variable {x w za : A} {y z : Fin 5 → A} {xb t w1 w2 ub : B} {zm ym za' : Fin 3 → B}

theorem closure_gen1
    (hg : Subgroup.closure (({x, w, za} : Set A) ∪ Set.range y ∪ Set.range z) = ⊤) :
    Subgroup.closure (Set.range (PresP1.gen x w za y z)) = ⊤ := by
  refine eq_top_iff.2 (hg ▸ Subgroup.closure_mono ?_)
  rintro g (((rfl | rfl | rfl) | ⟨j, rfl⟩) | ⟨j, rfl⟩)
  · exact ⟨PresP1.gx, PresP1.gen_x⟩
  · exact ⟨PresP1.gw, PresP1.gen_w⟩
  · exact ⟨PresP1.gza, PresP1.gen_za⟩
  · exact ⟨PresP1.gy j, PresP1.gen_y j⟩
  · exact ⟨PresP1.gz j, PresP1.gen_z j⟩

theorem closure_gen2 (hg : Subgroup.closure (({xb, t, w1, w2, ub} : Set B) ∪ Set.range zm ∪
    Set.range ym ∪ Set.range za') = ⊤) :
    Subgroup.closure (Set.range (PresP2.gen xb t w1 w2 ub zm ym za')) = ⊤ := by
  refine eq_top_iff.2 (hg ▸ Subgroup.closure_mono ?_)
  rintro g ((((rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact ⟨PresP2.gxb, PresP2.gen_xb⟩
  · exact ⟨PresP2.gt, PresP2.gen_t⟩
  · exact ⟨PresP2.gw1, PresP2.gen_w1⟩
  · exact ⟨PresP2.gw2, PresP2.gen_w2⟩
  · exact ⟨PresP2.gub, PresP2.gen_ub⟩
  · exact ⟨PresP2.gzm i, PresP2.gen_zm i⟩
  · exact ⟨PresP2.gym i, PresP2.gen_ym i⟩
  · exact ⟨PresP2.gza i, PresP2.gen_za i⟩

theorem closure_linkB {X : GoldAmalgam A C B} {a : Fin 13 → A}
    (hl : ∀ i, AmalgamLink X (a i) (linkB t w1 w2 ub zm ym za' i))
    (hg : Subgroup.closure (({t, w1, w2, ub} : Set B) ∪ Set.range zm ∪ Set.range ym ∪
      Set.range za') = X.edgeB) :
    Subgroup.closure (Set.range (linkB t w1 w2 ub zm ym za')) = X.edgeB := by
  refine closure_range_eq_edgeB _ (fun i => ⟨a i, hl i⟩) hg ?_
  rintro g ((((rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · fin_cases i
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
  · fin_cases i
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
  · fin_cases i
    · exact ⟨10, rfl⟩
    · exact ⟨11, rfl⟩
    · exact ⟨12, rfl⟩

end Generation

theorem exists_presEquiv11
    {X : GoldAmalgam A C B} (h : AdmitsPres11 X) (hA : Nat.card A = 5 * 2 ^ 11)
    (hB : Nat.card B = 3 * 2 ^ 11) :
    ∃ (φA : PG 13 p1Words ≃* A) (φB : PG 14 p2Words ≃* B),
      (∀ i, AmalgamLink X (φA (presLinkA i)) (φB (presLinkB i))) ∧
        Subgroup.closure (Set.range fun i => φB (presLinkB i)) = X.edgeB := by
  obtain ⟨x, w, za, y, z, xb, t, w1, w2, ub, zm, ym, za', h1, h2, h3, hgA, hgB, hgE, hl⟩ := h
  obtain ⟨φA, hφA⟩ : ∃ φ : PG 13 p1Words ≃* A,
      ∀ i, φ (PresentedGroup.of i) = PresP1.gen x w za y z i :=
    exists_mulEquiv_presented
      (lift_eq_one_of_words (PresP1.gen x w za y z) (PresP1.lift_rels h1)) (closure_gen1 hgA)
      card_p1_le.1 card_p1_le.2 hA
  obtain ⟨φB, hφB⟩ : ∃ φ : PG 14 p2Words ≃* B,
      ∀ i, φ (PresentedGroup.of i) = PresP2.gen xb t w1 w2 ub zm ym za' i :=
    exists_mulEquiv_presented
      (lift_eq_one_of_words (PresP2.gen xb t w1 w2 ub zm ym za') (PresP2.lift_rels h2 h3))
      (closure_gen2 hgB) card_p2_le.1 card_p2_le.2 hB
  have eA : ∀ i, φA (presLinkA i) = linkA w za y z i := by
    intro i
    have := map_linkA φA.toMonoidHom (PresentedGroup.of PresP1.gw) (PresentedGroup.of PresP1.gza)
      (fun j => PresentedGroup.of (PresP1.gy j)) (fun j => PresentedGroup.of (PresP1.gz j)) i
    simp only [MulEquiv.coe_toMonoidHom, hφA, PresP1.gen_w, PresP1.gen_za, PresP1.gen_y,
      PresP1.gen_z] at this
    exact this
  have eB : ∀ i, φB (presLinkB i) = linkB t w1 w2 ub zm ym za' i := by
    intro i
    have := map_linkB φB.toMonoidHom (PresentedGroup.of PresP2.gt) (PresentedGroup.of PresP2.gw1)
      (PresentedGroup.of PresP2.gw2) (PresentedGroup.of PresP2.gub)
      (fun i => PresentedGroup.of (PresP2.gzm i)) (fun i => PresentedGroup.of (PresP2.gym i))
      (fun i => PresentedGroup.of (PresP2.gza i)) i
    simp only [MulEquiv.coe_toMonoidHom, hφB, PresP2.gen_t, PresP2.gen_w1, PresP2.gen_w2,
      PresP2.gen_ub, PresP2.gen_zm, PresP2.gen_ym, PresP2.gen_za] at this
    exact this
  refine ⟨φA, φB, fun i => by rw [eA, eB]; exact hl.link i, ?_⟩
  have : (fun i => φB (presLinkB i)) = linkB t w1 w2 ub zm ym za' := funext eB
  rw [this]
  exact closure_linkB (a := linkA w za y z) (fun i => hl.link i) hgE

end CFSG.Quasithin.Fan86
