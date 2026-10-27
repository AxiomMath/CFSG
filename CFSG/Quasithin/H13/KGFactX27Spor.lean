module

public import CFSG.Quasithin.H13.KGFactX27J4
public import CFSG.Quasithin.H13.NQCoreP134X27Cfg
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverFinal

public section

namespace CFSG.Quasithin.H13.KGX27

open CFSG.Quasithin.H13.NQCore CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.QuasithinUnique.Ch1 (false_of_odd_cover_trivial)

theorem noX27Simple_of_noIndex {F : ∀ (X : Type) [Group X], Prop}
    (h : NoIndexOvergroup 27 F) : NoX27Simple F := by
  intro A _ _ L P T hcfg h27 hL
  obtain ⟨H, S, hS2, hSi, hSH, hH⟩ := hcfg.exists_model_sylow_x27 h27 (MulEquiv.refl ↥L)
  exact h ↥L hL H S hS2 hSi hSH hH

theorem noE9Cfg_of_noIndex {F : ∀ (X : Type) [Group X], Prop}
    (h : NoIndexOvergroup 9 F) : NoE9Cfg F := by
  intro A _ _ L P T hL hcfg
  obtain ⟨H, S, hS2, hSi, hSH, hH⟩ := hcfg.exists_model_sylow (MulEquiv.refl ↥L)
  exact h ↥L hL H S hS2 hSi hSH hH

theorem isoInvariant_nonempty_equiv (C : Type) [Group C] :
    IsoInvariant fun (X : Type) [Group X] => Nonempty (X ≃* C) :=
  fun _ _ _ _ e ⟨f⟩ => ⟨e.symm.trans f⟩

theorem not_dvd_of_equiv {C : Type} [Group C] {N : ℕ} (hC : Nat.card C = N) (hN : ¬ 27 ∣ N) :
    ∀ (X : Type) [Group X], Nonempty (X ≃* C) → ¬ 27 ∣ Nat.card X := by
  intro X _ ⟨e⟩
  rw [Nat.card_congr e.toEquiv, hC]
  exact hN

theorem noX27ConfigQ_m11 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M11) := by
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_not_dvd (not_dvd_of_equiv (C := NativeSporadic.Carrier .M11)
      CFSG.Sporadic.Mathieu.card_M11 (by norm_num))) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.QuasithinUnique.Ch1.M11_perfect_odd_cover_trivial π hπ hC hodd

theorem noX27ConfigQ_m12 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M12) := by
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_noIndex (noIndexOvergroup_m12 (Or.inr rfl))) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.SectionRank.M12_perfect_odd_cover_trivial π hπ hC hodd

theorem noX27ConfigQ_m22 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22) :=
  noX27ConfigQ_of_noE9Cfg (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_not_dvd (not_dvd_of_equiv (C := NativeSporadic.Carrier .M22)
      CFSG.Sporadic.Mathieu.card_M22 (by norm_num)))
    (noE9Cfg_of_noIndex noIndexOvergroup_m22)

theorem noX27ConfigQ_m23 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23) := by
  have hc : Nat.card NativeSporadic.M23 = 10200960 := by
    rw [CFSG.Sporadic.Mathieu.nativeM23_eq, Nat.card_eq_fintype_card]
    exact CFSG.M23.M23Group.card_M23
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_not_dvd (not_dvd_of_equiv (C := NativeSporadic.Carrier .M23) hc
      (by norm_num))) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.QuasithinUnique.Ch1.M23_perfect_odd_cover_trivial π hπ hC hodd

theorem noX27ConfigQ_m24 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24) := by
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_noIndex noIndexOvergroup_m24) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.SectionRank.M24_perfect_odd_cover_trivial π hπ hC hodd

theorem noX27ConfigQ_j1 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J1) :=
  noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_not_dvd (not_dvd_of_equiv (C := NativeSporadic.Carrier .J1)
      CFSG.Sporadic.J1.card_J1 (by norm_num))) fun _ _ _ hX h3 ⟨e⟩ =>
      CFSG.QuasithinUnique.Vol2Native.false_of_a134TypesCentral hX h3 (Or.inr (Or.inr (Or.inl ⟨e⟩)))

theorem noX27ConfigQ_j2 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2) := by
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_noIndex noIndexOvergroup_j2) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.SectionRank.J2_perfect_odd_cover_trivial π hπ hC hodd

theorem noX27ConfigQ_j4 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4) := by
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_noIndex noIndexOvergroup_j4) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.SectionRank.J4_perfect_odd_cover_trivial CFSG.SectionRank.j4OrderHyp π hπ hC hodd

theorem noX27ConfigQ_hs :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS) := by
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_not_dvd (not_dvd_of_equiv (C := NativeSporadic.Carrier .HS)
      CFSG.Sporadic.HS.card_HS (by norm_num))) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.SectionRank.HS_perfect_odd_cover_trivial π hπ hC hodd

theorem noX27ConfigQ_he :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .He) := by
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_noIndex noIndexOvergroup_he) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.SectionRank.He_perfect_odd_cover_trivial π hπ hC hodd

theorem noX27ConfigQ_ru :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru) := by
  refine noX27ConfigQ_of_noCover (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_noIndex (noIndexOvergroup_ru (Or.inr rfl))) fun X _ _ hX h3 ⟨e⟩ => ?_
  have : Group.IsPerfect X := hX.1
  exact false_of_odd_cover_trivial h3 e fun π hπ hC hodd =>
    CFSG.SectionRank.Ru_perfect_odd_cover_trivial π hπ hC hodd

theorem noX27ConfigQ_alt6 :
    NoX27ConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 6)) := by
  have hc : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    simp [Nat.factorial]
  refine noX27ConfigQ_of_noE9Cfg (isoInvariant_nonempty_equiv _)
    (noX27Simple_of_not_dvd (not_dvd_of_equiv hc (by norm_num)))
    (noE9Cfg_of_noIndex (noIndexOvergroup_card_360 fun X _ _ ⟨e⟩ => ?_))
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact ⟨e.isSimpleGroup, (Nat.card_congr e.toEquiv).trans hc⟩

theorem noX27ConfigQ_psu3_three :
    NoX27ConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 3 1 :=
  noX27ConfigQ_of_noE9Cfg
    (fun _ _ _ _ e h => CFSG.SectionRank.statedClassicalModel_of_mulEquiv e.symm h)
    (noX27Simple_of_noIndex (noIndexOvergroup_psu3_three (Or.inr rfl)))
    (noE9Cfg_of_noIndex (noIndexOvergroup_psu3_three (Or.inl rfl)))

end CFSG.Quasithin.H13.KGX27
