module

public import CFSG.Sporadic.Fi24.PtGraph
public import CFSG.Sporadic.Fi24.ExtClass

public section

namespace CFSG.Sporadic.Fi24

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem seedGrp_eq_J : seedGrp = J := by
  unfold seedGrp J
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem mem_seedGrp_iff (g : GL (Fin 781) (ZMod 3)) :
    g ∈ seedGrp ↔ g ∈ J := by rw [seedGrp_eq_J]

theorem subImg_mat (g : J) (S : Sub781) :
    subImg (g : GL (Fin 781) (ZMod 3)) S.sp = (g • S).sp := rfl

theorem isPt_iff_pt (V : Submodule (ZMod 3) (Fin 781 → ZMod 3)) :
    IsPt V ↔ ∃ k : Fin 306936, (pt k.val).sp = V := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_seedGrp_iff] at hg
    refine ⟨(⟨g, hg⟩ : J) • root, ?_⟩
    rw [pt_smul]
    rfl
  · rintro ⟨k, rfl⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J root k
    refine ⟨g, (mem_seedGrp_iff _).2 g.2, ?_⟩
    rw [← hg, pt_smul]
    rfl

theorem pt_sp_inj {k l : Fin 306936}
    (h : (pt k.val).sp = (pt l.val).sp) : k = l :=
  eq_of_pt_eq (Sub781.ext' h)

theorem mem_ptFix_iff (w : J) (k : Fin 306936) :
    (pt k.val).sp ∈ ptFix (w : GL (Fin 781) (ZMod 3)) ↔ w • k = k := by
  constructor
  · rintro ⟨-, h⟩
    apply pt_sp_inj
    rw [pt_smul]
    exact h
  · intro h
    refine ⟨(isPt_iff_pt _).2 ⟨k, rfl⟩, ?_⟩
    rw [subImg_mat, ← pt_smul, h]

theorem pt_p1 :
    (pt p1.val).sp = (pt 0).sp.map (Matrix.mulVecLin mA) := by
  rw [pt_smul]
  rfl

theorem ptAdj_pt_iff
    (k l : Fin 306936) :
    PtAdj (pt k.val).sp (pt l.val).sp ↔ k ≠ l ∧ cls k * cls l = cls l * cls k := by
  constructor
  · rintro ⟨g, hg, h1, h2⟩
    rw [mem_seedGrp_iff] at hg
    set gJ : J := ⟨g, hg⟩
    have hk : gJ • root = k := pt_sp_inj (by rw [pt_smul]; exact h1)
    have hl : gJ • p1 = l := pt_sp_inj (by
      rw [pt_smul]
      change subImg g (pt p1.val).sp = _
      rw [pt_p1]
      exact h2)
    refine ⟨fun e => p1_ne_root (MulAction.injective gJ (hl.trans (e.symm.trans hk.symm))), ?_⟩
    rw [← hk, ← hl, cls_smul, cls_smul, cls_root]
    have hc : tR * cls p1 = cls p1 * tR := (tPerm_eq_self_iff_commute p1).1 tPerm_p1
    calc jR gJ * tR * (jR gJ)⁻¹ * (jR gJ * cls p1 * (jR gJ)⁻¹) =
          jR gJ * (tR * cls p1) * (jR gJ)⁻¹ := by group
      _ = jR gJ * (cls p1 * tR) * (jR gJ)⁻¹ := by rw [hc]
      _ = jR gJ * cls p1 * (jR gJ)⁻¹ * (jR gJ * tR * (jR gJ)⁻¹) := by group
  · rintro ⟨hne, hc⟩
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq J root k
    set m := g⁻¹ • l
    have hcm : tR * cls m = cls m * tR := by
      have e1 : cls k = jR g * tR * (jR g)⁻¹ := by rw [← hg, cls_smul_root]
      have e2 : cls m = (jR g)⁻¹ * cls l * jR g := by
        rw [cls_smul, map_inv, inv_inv]
      rw [e2]
      have : (jR g)⁻¹ * cls k * jR g = tR := by rw [e1]; group
      rw [← this]
      calc (jR g)⁻¹ * cls k * jR g * ((jR g)⁻¹ * cls l * jR g) =
            (jR g)⁻¹ * (cls k * cls l) * jR g := by group
        _ = (jR g)⁻¹ * (cls l * cls k) * jR g := by rw [hc]
        _ = (jR g)⁻¹ * cls l * jR g * ((jR g)⁻¹ * cls k * jR g) := by group
    rcases (tPerm_eq_self_iff m).1 ((tPerm_eq_self_iff_commute m).2 hcm) with h0 | h2
    · exact absurd (by rw [← hg, ← h0]; simp [m]) hne
    · obtain ⟨h, hh, hhm⟩ := subLab_orb p1 m (subLab_p1.trans h2.symm)
      have hroot : h • root = root := mem_stabilizer_of_lvl hh
      refine ⟨((g * h : J) : GL (Fin 781) (ZMod 3)), (mem_seedGrp_iff _).2 (g * h).2, ?_, ?_⟩
      · rw [subImg_mat]
        change ((g * h) • pt root.val).sp = _
        rw [← pt_smul, mul_smul, hroot, hg]
      · rw [← pt_p1, subImg_mat, ← pt_smul, mul_smul, hhm]
        simp [m]

theorem smul_eq_iff_comm_cls
    (g : J) (k : Fin 306936) : g • k = k ↔ jR g * cls k = cls k * jR g := by
  constructor
  · intro h
    have e := cls_smul g k
    rw [h] at e
    calc jR g * cls k = jR g * cls k * (jR g)⁻¹ * jR g := by group
      _ = cls k * jR g := by rw [← e]
  · intro h
    apply cls_injective
    rw [cls_smul, h, mul_inv_cancel_right]

theorem mem_ptFix_iff_comm
    (w : J) (k : Fin 306936) :
    (pt k.val).sp ∈ ptFix (w : GL (Fin 781) (ZMod 3)) ↔ cls k * jR w = jR w * cls k := by
  rw [mem_ptFix_iff, smul_eq_iff_comm_cls]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem exists_pt_of_mem_ptFix {w : GL (Fin 781) (ZMod 3)}
    {V : Submodule (ZMod 3) (Fin 781 → ZMod 3)} (hV : V ∈ ptFix w) :
    ∃ k : Fin 306936, (pt k.val).sp = V :=
  (isPt_iff_pt V).1 hV.1

theorem card_ptFix_eq (w : J) :
    Nat.card {k : Fin 306936 // w • k = k} = Nat.card (ptFix (w : GL (Fin 781) (ZMod 3))) := by
  refine Nat.card_congr
    { toFun := fun k => ⟨(pt k.1.val).sp, (mem_ptFix_iff w k.1).2 k.2⟩
      invFun := fun V => ⟨(exists_pt_of_mem_ptFix V.2).choose, (mem_ptFix_iff w _).1 (by
        rw [(exists_pt_of_mem_ptFix V.2).choose_spec]
        exact V.2)⟩
      left_inv := fun k => Subtype.ext (pt_sp_inj (exists_pt_of_mem_ptFix
        ((mem_ptFix_iff w k.1).2 k.2)).choose_spec)
      right_inv := fun V => Subtype.ext (exists_pt_of_mem_ptFix V.2).choose_spec }

theorem graph_D24
    (w : J)
    (h : (ptFix (w : GL (Fin 781) (ZMod 3))).Nonempty ∧
      (∀ V ∈ ptFix (w : GL (Fin 781) (ZMod 3)), ∃ W ∈ ptFix (w : GL (Fin 781) (ZMod 3)),
        W ≠ V ∧ PtAdj V W) ∧
      (∀ V ∈ ptFix (w : GL (Fin 781) (ZMod 3)), ∀ W ∈ ptFix (w : GL (Fin 781) (ZMod 3)),
        V ≠ W → ¬ PtAdj V W → ∃ Z ∈ ptFix (w : GL (Fin 781) (ZMod 3)), PtAdj Z V ∧ PtAdj Z W)) :
    (∃ e ∈ D24, e * jR w = jR w * e) ∧
    (∀ x ∈ D24, x * jR w = jR w * x → ∃ y ∈ D24, y * jR w = jR w * y ∧ y ≠ x ∧ x * y = y * x) ∧
    (∀ x ∈ D24, x * jR w = jR w * x → ∀ y ∈ D24, y * jR w = jR w * y → x * y ≠ y * x →
      ∃ z ∈ D24, z * jR w = jR w * z ∧ z * x = x * z ∧ z * y = y * z) := by
  obtain ⟨⟨V, hV⟩, h1, h2⟩ := h
  refine ⟨?_, fun x hx hxw => ?_, fun x hx hxw y hy hyw hxy => ?_⟩
  · obtain ⟨k, rfl⟩ := exists_pt_of_mem_ptFix hV
    exact ⟨cls k, cls_mem k, (mem_ptFix_iff_comm w k).1 hV⟩
  · obtain ⟨k, rfl⟩ := exists_cls hx
    obtain ⟨W, hW, -, hadj⟩ := h1 _ ((mem_ptFix_iff_comm w k).2 hxw)
    obtain ⟨l, rfl⟩ := exists_pt_of_mem_ptFix hW
    obtain ⟨hkl, hc⟩ := (ptAdj_pt_iff k l).1 hadj
    exact ⟨cls l, cls_mem l, (mem_ptFix_iff_comm w l).1 hW,
      fun e => hkl (cls_injective e).symm, hc⟩
  · obtain ⟨k, rfl⟩ := exists_cls hx
    obtain ⟨l, rfl⟩ := exists_cls hy
    have hkl : (pt k.val).sp ≠ (pt l.val).sp := fun e => hxy (by rw [pt_sp_inj e])
    have hna : ¬ PtAdj (pt k.val).sp (pt l.val).sp := fun h => hxy ((ptAdj_pt_iff k l).1 h).2
    obtain ⟨Z, hZ, hZk, hZl⟩ := h2 _ ((mem_ptFix_iff_comm w k).2 hxw) _
      ((mem_ptFix_iff_comm w l).2 hyw) hkl hna
    obtain ⟨m, rfl⟩ := exists_pt_of_mem_ptFix hZ
    exact ⟨cls m, cls_mem m, (mem_ptFix_iff_comm w m).1 hZ, ((ptAdj_pt_iff m k).1 hZk).2,
      ((ptAdj_pt_iff m l).1 hZl).2⟩

theorem chain_D24
    (w : J) {n : ℕ}
    (P : Fin n → Submodule (ZMod 3) (Fin 781 → ZMod 3))
    (hP : ∀ i, P i ∈ ptFix (w : GL (Fin 781) (ZMod 3)))
    (h1 : ∀ i j : Fin n, i.val + 1 = j.val → P i ≠ P j ∧ ¬ PtAdj (P i) (P j))
    (h2 : ∀ i j : Fin n, i.val + 2 ≤ j.val → PtAdj (P i) (P j)) :
    ∃ s : Fin n → R, (∀ i, s i ∈ D24 ∧ s i * jR w = jR w * s i) ∧
      (∀ i j : Fin n, i.val + 1 = j.val → s i ≠ s j ∧ s i * s j ≠ s j * s i) ∧
      (∀ i j : Fin n, i.val + 2 ≤ j.val → s i * s j = s j * s i) := by
  choose k hk using fun i => exists_pt_of_mem_ptFix (hP i)
  refine ⟨fun i => cls (k i), fun i => ⟨cls_mem _, (mem_ptFix_iff_comm w _).1 (by
    rw [hk]; exact hP i)⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · obtain ⟨hne, hna⟩ := h1 i j hij
    refine ⟨fun e => hne (by rw [← hk i, ← hk j, cls_injective e]), fun hc => hna ?_⟩
    rw [← hk i, ← hk j]
    exact (ptAdj_pt_iff _ _).2 ⟨fun e => hne (by rw [← hk i, ← hk j, e]), hc⟩
  · have := h2 i j hij
    rw [← hk i, ← hk j] at this
    exact ((ptAdj_pt_iff _ _).1 this).2

end CFSG.Sporadic.Fi24

end
