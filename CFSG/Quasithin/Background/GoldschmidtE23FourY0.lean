module

public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourSylow

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace E2

variable {G : Type} [Group G]

theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have h1 := B6.conjSub_eq_self hA
  have h2 := B6.conjSub_eq_self hB
  refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
  have h3 : B6.conjSub g (A ⊔ B) = B6.conjSub g A ⊔ B6.conjSub g B := OrderIso.map_sup _ _ _
  rw [h1, h2] at h3
  exact h3

theorem normalizer_le_of_characteristic {S C : Subgroup G} (hCS : C ≤ S)
    (hchar : (C.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have h := normalizer_le_normalizer_map_of_characteristic (C.subgroupOf S)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCS] at h

theorem isBlock2_of_normal {Y X L : Subgroup G} (hYX : Y ≤ X)
    (hn : X ≤ Subgroup.normalizer (Y : Set G)) (hL : IsBlock2 Y L) : IsBlock2 X L := by
  have hLY : L ≤ Y := hL.2.1
  have hYsub : IsSubnormal Y X :=
    A4.subnormal_of_normal hYX (Subgroup.normal_subgroupOf_of_le_normalizer hn)
  have hsub : IsSubnormal L X := A4.subnormal_trans (IsBlock2.isSubnormal hL) hYsub
  exact ⟨hL.1, hLY.trans hYX, (isSubnormal_iff_subgroupOf (hLY.trans hYX)).mp hsub⟩

variable [Finite G]

theorem exists_chi0Block_of_sylow_baum (h129 : ASC129Statement G) {H T M : Subgroup G}
    (hmin : MinParabolic H T M) (hsq : SQTKGroup ↥H) (hF : CharTwo H)
    (hPU : ∀ C : Subgroup G, C ≤ baum T → C ≠ ⊥ → (C.subgroupOf (baum T)).Characteristic →
      ¬ H ≤ Subgroup.normalizer (C : Set G))
    (hSyl : IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T)) :
    ∃ L : Subgroup G, IsChi0Block H L ∧ H = L ⊔ T ∧ (¬ IsAltType L 3 → L ∈ cComp H) := by
  classical
  have hT := hmin.isSylow
  have hTH : T ≤ H := hT.1
  have hST : baum T ≤ T := inf_le_left
  have hKH : twoResidual H ≤ H := twoResidual_le H
  have hKN : H ≤ Subgroup.normalizer (twoResidual H : Set G) := le_normalizer_twoResidual H
  have hTS : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hYH : twoResidual H ⊔ baum T ≤ H := sup_le hKH (hST.trans hTH)
  have hHeq : T ⊔ twoResidual H = H := sup_twoResidual_eq hT
  have hYN : H ≤ Subgroup.normalizer ((twoResidual H ⊔ baum T : Subgroup G) : Set G) :=
    hHeq.symm.le.trans (sup_le (fun t ht => mem_normalizer_sup (hKN (hTH ht)) (hTS ht))
      (le_sup_left.trans Subgroup.le_normalizer))
  have hSK : baum T ≤ Subgroup.normalizer (twoResidual H : Set G) := hST.trans (hTH.trans hKN)
  have hFK : CharTwo (twoResidual H) := A4.charTwo_of_normal hKH hKN hF
  have hFY : CharTwo (twoResidual H ⊔ baum T) :=
    A4.charTwo_sup hFK hSK (hT.2.1.to_le hST)
  have hcgs : cgsIn (twoResidual H ⊔ baum T) (baum T) ≤ M ⊓ (twoResidual H ⊔ baum T) := by
    refine le_inf ?_ (cgsIn_le _ _)
    refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC0 => iSup_le fun hchar => ?_
    have hTN : T ≤ Subgroup.normalizer (C : Set G) :=
      hTS.trans (normalizer_le_of_characteristic hCS hchar)
    have hlt : H ⊓ Subgroup.normalizer (C : Set G) < H := lt_of_le_of_ne inf_le_left
      fun he => hPU C hCS hC0 hchar (he ▸ inf_le_right)
    exact (inf_le_inf_right _ hYH).trans (hmin.le_of_lt (le_inf hTH hTN) hlt)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := h129 (twoResidual H ⊔ baum T) (baum T)
    (M ⊓ (twoResidual H ⊔ baum T)) (IsSQTKIn.mono hsq hYH) hFY hSyl hcgs inf_le_right
  have hYM : ¬ twoResidual H ⊔ baum T ≤ M := fun hle => by
    have hHM : H ≤ M := hHeq.symm.le.trans (sup_le hmin.le (le_sup_left.trans hle))
    exact lt_irrefl H (lt_of_le_of_lt hHM hmin.maximal.1)
  obtain ⟨i, hi⟩ : ∃ i, ¬ Lb i ≤ M := by
    by_contra hall
    push Not at hall
    refine hYM fun y hy => ?_
    obtain ⟨m, hm, x, hx, rfl⟩ := hprod y hy
    refine M.mul_mem hm.1 (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
    exact hall j (hx j)
  obtain ⟨hchi, -, -⟩ := hLb i
  have hLY : Lb i ≤ twoResidual H ⊔ baum T := hchi.1.2.1
  have hblock : IsBlock2 H (Lb i) := isBlock2_of_normal hYH hYN hchi.1
  have hLH : Lb i ≤ H := hLY.trans hYH
  refine ⟨Lb i, ⟨hblock, hchi.2⟩, ?_, fun h3 => ?_⟩
  · exact (hmin.eq_of_not_le le_sup_right (sup_le hLH hTH) fun h => hi (le_sup_left.trans h)).symm
  · refine L238.mem_cComp_of_isChi0Block_nonsolvable hblock ?_
    rcases hchi.2 with h | h | h
    · exact Or.inl h
    · exact absurd h h3
    · exact Or.inr h

end E2

end CFSG.Quasithin
