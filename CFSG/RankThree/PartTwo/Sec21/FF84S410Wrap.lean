module

public import CFSG.RankThree.PartTwo.Sec21.FF84S410Hyp
public import CFSG.RankThree.PartTwo.Sec21.FF84S48Final
public import CFSG.RankThree.PartTwo.Sec21.FF84S49Orb

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

namespace S48Ctx

variable (c : S48Ctx b L B K b₁ b₂) {U : Subgroup G} (hU : U ∈ PiStar (Cen b) B 2)

include c hU

theorem cen_iff_comm :
    (∀ x ∈ Op 2 (Nor U), (x ∈ Cen b ↔
      x ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆ ⊔ ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆)) ∧
    (∀ x ∈ Op 2 (Nor U), (x ∈ Cen b₁ ↔
      x ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ ⊔ ⁅Op 2 (Nor U), Subgroup.zpowers b₂⁆)) ∧
    (∀ x ∈ Op 2 (Nor U), (x ∈ Cen b₂ ↔
      x ∈ ⁅Op 2 (Nor U), Subgroup.zpowers b⁆ ⊔ ⁅Op 2 (Nor U), Subgroup.zpowers b₁⁆)) := by
  obtain ⟨-, -, -, -, f0, f1, f2⟩ := c.S_iso hU
  obtain ⟨-, -, hC⟩ := c.S48_b2 hU
  have hSEA := c.S_ea2 hU
  have hgen : B = Subgroup.closure {b, b₁, b₂} := c.sec.mono.2.1
  have hbB := mem_b c.sec
  have hb1B := mem_b₁ c.sec
  have hb2B := mem_b₂ c.sec
  have hBS := c.B_le_nor_S hU
  have hfix : ∀ y ∈ Op 2 (Nor U), Commute b y → Commute b₁ y → Commute b₂ y → y = 1 := by
    intro y hy h0 h1 h2
    refine IsoAux.fix_of_B hC hgen hy ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have hcen : ∀ (W : Subgroup G) (u v w : G), W ≤ CenS (Subgroup.closure {u, v}) → w ∈ W →
      Commute u w ∧ Commute v w := by
    intro W u v w hW hw
    have hm := Subgroup.mem_centralizer_iff.1 (hW hw)
    exact ⟨hm u (Subgroup.subset_closure (by simp)), hm v (Subgroup.subset_closure (by simp))⟩
  have hcb : ∀ {x u : G}, Commute u x → x ∈ Cen u := fun h =>
    Subgroup.mem_centralizer_singleton_iff.2 h.symm
  have hbc : ∀ {x u : G}, x ∈ Cen u → Commute u x := fun h =>
    (Subgroup.mem_centralizer_singleton_iff.1 h).symm
  have hcomm : ∀ x y : G, x ∈ B → y ∈ B → Commute x y := fun x y hx hy => c.hBcomm x hx y hy
  have hn : ∀ z ∈ B, z ∈ Nor (Op 2 (Nor U)) := fun z hz => hBS hz
  have jm : ∀ u v w : G, u ∈ B → v ∈ B → w ∈ B →
      (∀ y ∈ Op 2 (Nor U), Commute u y → Commute v y → Commute w y → y = 1) →
      ∀ z ∈ Op 2 (Nor U), Commute w z →
        z ∈ ⁅Op 2 (Nor U), Subgroup.zpowers u⁆ ⊔ ⁅Op 2 (Nor U), Subgroup.zpowers v⁆ :=
    fun u v w hu hv hw hf =>
      IsoAux.join_mem hSEA.1 hSEA.2 (hn u hu) (hn v hv) (c.hB3 u hu) (c.hB3 v hv)
        (hcomm u v hu hv) (hcomm w v hw hv) (hcomm w u hw hu)
        (fun y hy h1 h2 h3 => hf y hy h1 h3 h2)
  refine ⟨fun x hx => ⟨fun hxc => ?_, fun hxm => ?_⟩, fun x hx => ⟨fun hxc => ?_, fun hxm => ?_⟩,
    fun x hx => ⟨fun hxc => ?_, fun hxm => ?_⟩⟩
  · exact jm b₁ b₂ b hb1B hb2B hbB
      (fun y hy h1 h2 h3 => hfix y hy h3 h1 h2) x hx (hbc hxc)
  · exact (sup_le (fun w hw => hcb ((hcen _ b b₂ w f1 hw).1))
      (fun w hw => hcb ((hcen _ b b₁ w f2 hw).1)) : _ ≤ Cen b) hxm
  · exact jm b b₂ b₁ hbB hb2B hb1B
      (fun y hy h1 h2 h3 => hfix y hy h1 h3 h2) x hx (hbc hxc)
  · exact (sup_le (fun w hw => hcb ((hcen _ b₁ b₂ w f0 hw).1))
      (fun w hw => hcb ((hcen _ b b₁ w f2 hw).2)) : _ ≤ Cen b₁) hxm
  · exact jm b b₁ b₂ hbB hb1B hb2B hfix x hx (hbc hxc)
  · exact (sup_le (fun w hw => hcb ((hcen _ b₁ b₂ w f0 hw).2))
      (fun w hw => hcb ((hcen _ b b₂ w f1 hw).2)) : _ ≤ Cen b₂) hxm

open scoped _root_.Classical in
theorem ncomp_eq_NcompC {x : G} (hx : x ∈ Op 2 (Nor U)) :
    ncomp (Op 2 (Nor U)) b b₁ b₂ x = NcompC b b₁ b₂ x := by
  obtain ⟨e0, e1, e2⟩ := c.cen_iff_comm hU
  unfold ncomp NcompC
  classical
  rw [if_congr (e0 x hx).symm rfl rfl, if_congr (e1 x hx).symm rfl rfl,
    if_congr (e2 x hx).symm rfl rfl]

end S48Ctx

theorem S48Ctx_of (h41 : FF84_4_1) (h47 : S47TransportItem)
    (hpost : FF84Post b L B K b₁ b₂) : S48Ctx b L B K b₁ b₂ :=
  ⟨hpost, h47 G b L B K b₁ b₂ hpost, S45_D_normalizes h41 hpost.sec hpost.o3'⟩

theorem hypS48CSb_of (h41 : FF84_4_1) (h47 : S47TransportItem) : HypS48CSb := by
  intro G _ _ b L B K b₁ b₂ hpost U hU
  exact (S48Ctx_of h41 h47 hpost).S48_CSb hU

theorem hypS48b2_of (h41 : FF84_4_1) (h47 : S47TransportItem) : HypS48b2 := by
  intro G _ _ b L B K b₁ b₂ hpost U hU
  exact (S48Ctx_of h41 h47 hpost).S48_b2 hU

section S49


theorem hypS49S6_of (h41 : FF84_4_1) (h47 : S47TransportItem) (hodd : A_cent_A5_odd_stmt) :
    HypS49S6 := by
  intro G _ _ b L B K b₁ b₂ hpost U hU s₀ hs hs1
  exact (S48Ctx_of h41 h47 hpost).S49_S6 hU (a8Model_of_hyp hpost.sec.hyp) hodd hs hs1

theorem hypS49orbits_of (h41 : FF84_4_1) (h47 : S47TransportItem) (hP : A_PiStar_stmt)
    (hT : A_transv_stmt) (hodd : A_cent_A5_odd_stmt) : HypS49orbits := by
  intro G _ _ b L B K b₁ b₂ hpost U hU
  have c := S48Ctx_of h41 h47 hpost
  obtain ⟨Δ₁, Δ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    c.S49_orbits hU (a8Model_of_hyp hpost.sec.hyp) hP hT hodd
  refine ⟨Δ₁, Δ₂, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun x hx hx1 => ?_⟩
  rw [c.ncomp_eq_NcompC hU hx]
  exact h10 x hx hx1

end S49

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

end
