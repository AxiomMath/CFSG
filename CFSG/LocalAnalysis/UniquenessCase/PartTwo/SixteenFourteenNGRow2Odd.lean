module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGRow2Min
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyIrrThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s1614_ro_irr_inf_or_le {W : Type*} [CommGroup W] {A : Subgroup (MulAut W)}
    {I X : Subgroup W} (hI : IsIrrOn A I ⊥) (hX : StableUnder A X) :
    I ⊓ X = ⊥ ∨ I ≤ X := by
  have hstable : StableUnder A (I ⊓ X) := fun a ha u hu =>
    ⟨hI.2.1 a ha u hu.1, hX a ha u hu.2⟩
  rcases hI.2.2.2 (I ⊓ X) hstable bot_le inf_le_left with h | h
  · exact Or.inl h
  · exact Or.inr (le_of_inf_eq h)

private theorem s1614_ro_perm_fin_three_cube_fpf :
    ∀ g : Equiv.Perm (Fin 3), g ^ 3 = 1 → g ≠ 1 → ∀ i, g i ≠ i := by
  decide

theorem s1614_row2_oddBar (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) (hS : Case168_2Small D ⊥ V hV L)
    {J₀ : Subgroup (Vtil ⊥ V hV)} (hJ₀ : J₀ ∈ irrSet (lBar ⊥ V hV L)) :
    ∃ y : MulAut (Vtil ⊥ V hV), y ∈ Mbar D.M ⊥ V hV ∧ y ∈ oddBar D.M ⊥ V hV ∧ y ≠ 1 ∧
      y * y * y = 1 ∧ (∀ l ∈ lBar ⊥ V hV L, y * l = l * y) ∧ (∀ x, y x = x → x = 1) ∧
      J₀ ⊓ J₀.map y.toMonoidHom = ⊥ := by
  classical
  obtain ⟨F, π, hFinj, hrange, hact, hπ2, htrans⟩ := s16c167_irr_three D hC hS
  have h2 : Case168_2 D ⊥ V hV L := hS.case168_2
  have hfix : fixV (lBar ⊥ V hV L) = ⊥ := s16c167_cfg2_fix D h2
  have hodd := s16c167_oddBar_case2 D h2
  have hJ : J₀ ∈ irrBar L ⊥ V hV := hJ₀
  rw [hrange] at hJ
  obtain ⟨a, ha⟩ := hJ
  obtain ⟨yM, hyodd, hπy⟩ := htrans a (a + 1)
  have hyM3 : (yM : MulAut (Vtil ⊥ V hV)) ^ 3 = 1 := by
    have hy0cube : (⟨(yM : MulAut (Vtil ⊥ V hV)), hyodd⟩ :
        ↥(oddBar D.M ⊥ V hV)) ^ 3 = 1 := by
      have h := pow_card_eq_one' (x := (⟨(yM : MulAut (Vtil ⊥ V hV)), hyodd⟩ :
        ↥(oddBar D.M ⊥ V hV))) (G := ↥(oddBar D.M ⊥ V hV))
      rwa [hodd.2] at h
    have h := congrArg (fun z : ↥(oddBar D.M ⊥ V hV) =>
      (z : MulAut (Vtil ⊥ V hV))) hy0cube
    simpa using h
  have hy3mul : (yM : MulAut (Vtil ⊥ V hV)) * (yM : MulAut (Vtil ⊥ V hV)) *
      (yM : MulAut (Vtil ⊥ V hV)) = 1 := by
    have heq : (yM : MulAut (Vtil ⊥ V hV)) ^ 3 =
        (yM : MulAut (Vtil ⊥ V hV)) * (yM : MulAut (Vtil ⊥ V hV)) *
          (yM : MulAut (Vtil ⊥ V hV)) := by
      rw [pow_succ, pow_two]
    rwa [heq] at hyM3
  have hyM3sub : yM ^ 3 = 1 := Subtype.ext hyM3
  have hg3 : (π yM) ^ 3 = 1 := by rw [← map_pow, hyM3sub, map_one]
  have hane : ∀ a : Fin 3, a + 1 ≠ a := by decide
  have hgne : π yM ≠ 1 := by
    intro h
    have : a + 1 = a := by rw [← hπy, h, Equiv.Perm.one_apply]
    exact hane a this
  have hmoved : ∀ i : Fin 3, π yM i ≠ i :=
    s1614_ro_perm_fin_three_cube_fpf (π yM) hg3 hgne
  have hyne : (yM : MulAut (Vtil ⊥ V hV)) ≠ 1 := by
    intro h
    apply hgne
    have hyM1 : yM = 1 := Subtype.ext h
    rw [hyM1, map_one]
  have hycommL : ∀ l ∈ lBar ⊥ V hV L, (yM : MulAut (Vtil ⊥ V hV)) * l =
      l * (yM : MulAut (Vtil ⊥ V hV)) := by
    intro l hl
    have hyk : (yM : MulAut (Vtil ⊥ V hV)) ∈ kBar D.M ⊥ V hV L := hodd.1 hyodd
    have hcent : (yM : MulAut (Vtil ⊥ V hV)) ∈
        Subgroup.centralizer ((lBar ⊥ V hV L : Subgroup _) : Set _) :=
      (Subgroup.mem_inf.1 hyk).2
    exact (Subgroup.mem_centralizer_iff.1 hcent l hl).symm
  have hirr : ∀ i : Fin 3, IsIrrOn (lBar ⊥ V hV L) (F i) ⊥ := by
    intro i
    have hi : F i ∈ irrSet (lBar ⊥ V hV L) := by
      have h : F i ∈ irrBar L ⊥ V hV := by
        rw [hrange]
        exact Set.mem_range_self i
      exact h
    have h2i := hi.2
    rwa [hfix, inf_bot_eq] at h2i
  have hmeet : ∀ i j, i ≠ j → F i ⊓ F j = ⊥ := by
    intro i j hij
    rcases s1614_ro_irr_inf_or_le (hirr i) (hirr j).2.1 with h | h
    · exact h
    · exfalso
      rcases (hirr j).2.2.2 (F i) (hirr i).2.1 bot_le h with hbot | htop
      · exact absurd hbot.symm (ne_of_lt (hirr i).1)
      · exact hij (hFinj htop)
  have hJdisj : J₀ ⊓ J₀.map (yM : MulAut (Vtil ⊥ V hV)).toMonoidHom = ⊥ := by
    rw [← ha]
    have hmap : (F a).map (yM : MulAut (Vtil ⊥ V hV)).toMonoidHom = F (a + 1) := by
      have h := hact yM a
      rw [hπy] at h
      exact h
    rw [hmap, hmeet a (a + 1) (fun h => hane a h.symm)]
  have hfixpt : ∀ x, (yM : MulAut (Vtil ⊥ V hV)) x = x → x = 1 := by
    intro x₀ hx₀
    by_contra hxne
    have hxU : x₀ ∈ fixV (Subgroup.zpowers (yM : MulAut (Vtil ⊥ V hV))) :=
      mem_fixV_zpowers_iff_apply.2 hx₀
    have hUne : fixV (Subgroup.zpowers (yM : MulAut (Vtil ⊥ V hV))) ≠ ⊥ := by
      intro h
      have hxbot : x₀ ∈ (⊥ : Subgroup (Vtil ⊥ V hV)) := by
        rw [← h]
        exact hxU
      exact hxne (Subgroup.mem_bot.1 hxbot)
    have hUstable : StableUnder (lBar ⊥ V hV L)
        (fixV (Subgroup.zpowers (yM : MulAut (Vtil ⊥ V hV)))) := by
      intro l hl u hu
      rw [mem_fixV_zpowers_iff_apply] at hu ⊢
      have hcomm := hycommL l hl
      calc (yM : MulAut (Vtil ⊥ V hV)) (l u)
          = ((yM : MulAut (Vtil ⊥ V hV)) * l) u := rfl
        _ = (l * (yM : MulAut (Vtil ⊥ V hV))) u := by rw [hcomm]
        _ = l ((yM : MulAut (Vtil ⊥ V hV)) u) := rfl
        _ = l u := by rw [hu]
    obtain ⟨I, hI, hIU⟩ := s1614_exists_irr_le hfix hUstable hUne
    have hIr : I ∈ irrBar L ⊥ V hV := hI
    rw [hrange] at hIr
    obtain ⟨i, hi⟩ := hIr
    have hFIU : F i ≤ fixV (Subgroup.zpowers (yM : MulAut (Vtil ⊥ V hV))) := by
      rw [hi]
      exact hIU
    have hFixI : ∀ u ∈ F i, (yM : MulAut (Vtil ⊥ V hV)) u = u := by
      intro u hu
      exact (mem_fixV_zpowers_iff_apply (g := (yM : MulAut (Vtil ⊥ V hV)))).1 (hFIU hu)
    have hmapI : (F i).map (yM : MulAut (Vtil ⊥ V hV)).toMonoidHom = F i := by
      apply Subgroup.ext
      intro v
      constructor
      · intro hv
        rw [Subgroup.mem_map] at hv
        obtain ⟨u, hu, rfl⟩ := hv
        change (yM : MulAut (Vtil ⊥ V hV)) u ∈ F i
        rw [hFixI u hu]
        exact hu
      · intro hv
        exact Subgroup.mem_map.2 ⟨v, hv, hFixI v hv⟩
    have hmapI2 : (F i).map (yM : MulAut (Vtil ⊥ V hV)).toMonoidHom = F (π yM i) :=
      hact yM i
    have hπfix : π yM i = i := hFinj (hmapI2.symm.trans hmapI)
    exact hmoved i hπfix
  exact ⟨(yM : MulAut (Vtil ⊥ V hV)), yM.2, hyodd, hyne, hy3mul, hycommL, hfixpt, hJdisj⟩

theorem s1614_row2_stab (D : Data G) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hC : Counterex16 D ⊥ V L hV) (hS : Case168_2Small D ⊥ V hV L)
    {J₀ : Subgroup (Vtil ⊥ V hV)} (hJ₀ : J₀ ∈ irrSet (lBar ⊥ V hV L))
    {x : MulAut (Vtil ⊥ V hV)} (hxM : x ∈ Mbar D.M ⊥ V hV) (hx2 : x * x = 1)
    (hxc : ∀ y ∈ oddBar D.M ⊥ V hV, x * y = y * x) : J₀.map x.toMonoidHom = J₀ := by
  obtain ⟨F, π, hFinj, hrange, hact, hπ2, htrans⟩ := s16c167_irr_three D hC hS
  have hJ : J₀ ∈ irrBar L ⊥ V hV := hJ₀
  rw [hrange] at hJ
  obtain ⟨a, ha⟩ := hJ
  let xM : ↥(Mbar D.M ⊥ V hV) := ⟨x, hxM⟩
  have hxM2 : xM ^ 2 = 1 := by
    apply Subtype.ext
    simpa [xM, pow_two] using hx2
  have hxpow : ∃ k : ℕ, xM ^ (2 ^ k) = 1 := ⟨1, by simpa using hxM2⟩
  have hπx : π xM = 1 := (hπ2 xM hxpow).1 hxc
  have hmap : (F a).map x.toMonoidHom = F (π xM a) := hact xM a
  rw [hπx, Equiv.Perm.one_apply] at hmap
  rw [← ha]
  exact hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
