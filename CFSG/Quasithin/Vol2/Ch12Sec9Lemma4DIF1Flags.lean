module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Tits
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Index

public section

namespace CFSG.Quasithin.H13.C1294

open Module MulAction

section Flags

theorem Wc_le {k k' : ℕ} (hkk' : k ≤ k') : Wc k ≤ Wc k' := by
  intro x hx
  show ∀ i : Fin (3 + 1), k' < i.val → x i = 0
  intro i hi
  exact hx i (lt_of_le_of_lt hkk' hi)

theorem map_trans_eq {M N P : Type} [AddCommGroup M] [Module (ZMod 2) M] [AddCommGroup N]
    [Module (ZMod 2) N] [AddCommGroup P] [Module (ZMod 2) P] (f : M ≃ₗ[ZMod 2] N)
    (g : N ≃ₗ[ZMod 2] P) (X : Submodule (ZMod 2) M) :
    X.map ((f.trans g : M ≃ₗ[ZMod 2] P) : M →ₗ[ZMod 2] P) =
      (X.map (f : M →ₗ[ZMod 2] N)).map (g : N →ₗ[ZMod 2] P) := by
  rw [← Submodule.map_comp]
  rfl

theorem flagI_trans {I : Type} [AddCommGroup I] [Module (ZMod 2) I]
    (e0 : V4 ≃ₗ[ZMod 2] I) (g : I ≃ₗ[ZMod 2] I) (k : ℕ) :
    flagI (e0.trans g) k = (flagI e0 k).map (g : I →ₗ[ZMod 2] I) := by
  unfold flagI
  rw [← Submodule.map_comp]
  rfl

variable {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [Finite I]

theorem exists_basis_flag [FiniteDimensional (ZMod 2) I] (hI : finrank (ZMod 2) I = 4)
    {p ℓ Pl : Submodule (ZMod 2) I} (hp : finrank (ZMod 2) p = 1)
    (hℓ : finrank (ZMod 2) ℓ = 2) (hPl : finrank (ZMod 2) Pl = 3)
    (hpℓ : p ≤ ℓ) (hℓPl : ℓ ≤ Pl) :
    ∃ e : V4 ≃ₗ[ZMod 2] I, flagI e 0 = p ∧ flagI e 1 = ℓ ∧ flagI e 2 = Pl := by
  have hV : finrank (ZMod 2) V4 = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  let e0 : V4 ≃ₗ[ZMod 2] I := LinearEquiv.ofFinrankEq V4 I (by rw [hV, hI])
  have hfin : ∀ k, k ≤ 2 → finrank (ZMod 2) (flagI e0 k) = k + 1 := fun k hk =>
    finrank_flagI e0 k hk
  have hmono : ∀ k k' : ℕ, k ≤ k' → flagI e0 k ≤ flagI e0 k' := fun k k' h =>
    Submodule.map_mono (Wc_le h)
  obtain ⟨g1, hg1⟩ := CFSG.Monster.B.TwoA.exists_linearEquiv_map_eq
    (S := flagI e0 0) (T := p) (by rw [hfin 0 (by norm_num), hp])
  have hpU1 : p ≤ (flagI e0 1).map (g1 : I →ₗ[ZMod 2] I) := by
    rw [← hg1]
    exact Submodule.map_mono (hmono 0 1 (by norm_num))
  have hfinU1 : finrank (ZMod 2) ((flagI e0 1).map (g1 : I →ₗ[ZMod 2] I)) =
      finrank (ZMod 2) ℓ := by
    rw [LinearEquiv.finrank_map_eq, hfin 1 (by norm_num), hℓ]
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl p
  obtain ⟨g2, hg2, -, hmap2⟩ := exists_stabS_fix_map_super hC hpU1 hpℓ hfinU1
  set g12 : I ≃ₗ[ZMod 2] I := g1.trans g2 with hg12
  have hF0 : (flagI e0 0).map (g12 : I →ₗ[ZMod 2] I) = p := by
    rw [hg12, map_trans_eq, hg1, map_eq_of_mem_stabS hg2]
  have hF1 : (flagI e0 1).map (g12 : I →ₗ[ZMod 2] I) = ℓ := by
    rw [hg12, map_trans_eq, hmap2]
  have hℓU2 : ℓ ≤ (flagI e0 2).map (g12 : I →ₗ[ZMod 2] I) := by
    rw [← hF1]
    exact Submodule.map_mono (hmono 1 2 (by norm_num))
  have hfinU2 : finrank (ZMod 2) ((flagI e0 2).map (g12 : I →ₗ[ZMod 2] I)) =
      finrank (ZMod 2) Pl := by
    rw [LinearEquiv.finrank_map_eq, hfin 2 (by norm_num), hPl]
  obtain ⟨g3, hg3, hmap3⟩ := exists_K1_map_super hpℓ hℓU2 hℓPl hfinU2
  set g : I ≃ₗ[ZMod 2] I := g12.trans g3 with hg
  have hg0 : (flagI e0 0).map (g : I →ₗ[ZMod 2] I) = p := by
    rw [hg, map_trans_eq, hF0]
    exact map_eq_of_mem_stabS (Subgroup.mem_inf.1 hg3).1
  have hg1' : (flagI e0 1).map (g : I →ₗ[ZMod 2] I) = ℓ := by
    rw [hg, map_trans_eq, hF1]
    exact map_eq_of_mem_stabS (Subgroup.mem_inf.1 hg3).2
  have hg2' : (flagI e0 2).map (g : I →ₗ[ZMod 2] I) = Pl := by
    rw [hg, map_trans_eq, hmap3]
  refine ⟨e0.trans g, ?_, ?_, ?_⟩
  · rw [flagI_trans]
    exact hg0
  · rw [flagI_trans]
    exact hg1'
  · rw [flagI_trans]
    exact hg2'

@[expose] def flagSet (p ℓ Pl : Submodule (ZMod 2) I) : Set (Subgroup (I ≃ₗ[ZMod 2] I)) :=
  {⊤, stabS p, stabS ℓ, stabS Pl, stabS p ⊓ stabS ℓ, stabS p ⊓ stabS Pl, stabS ℓ ⊓ stabS Pl,
    stabS p ⊓ stabS ℓ ⊓ stabS Pl}

theorem ne_of_index_ne {G : Type} [Group G] {X Y : Subgroup G} (h : X.index ≠ Y.index) : X ≠ Y :=
  fun e => h (congrArg Subgroup.index e)

theorem stabS_ne_of_flag (hI : finrank (ZMod 2) I = 4) {p Pl : Submodule (ZMod 2) I}
    (hp : finrank (ZMod 2) p = 1) (hPl : finrank (ZMod 2) Pl = 3) (hpPl : p ≤ Pl) :
    stabS p ≠ stabS Pl := by
  intro h
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl p
  have hCd : finrank (ZMod 2) C = 3 := by
    have h' := Submodule.finrank_add_eq_of_isCompl hC
    omega
  have hcard : Nat.card (SuperOf p 3) = 7 := by
    rw [card_superOf p C hC 3 (by omega) (by omega), hCd, hp]
    rfl
  have hnot : ∃ U : SuperOf p 3, U.1 ≠ Pl := by
    by_contra hcon
    push_neg at hcon
    have hsub : Subsingleton (SuperOf p 3) :=
      ⟨fun a b => Subtype.ext ((hcon a).trans (hcon b).symm)⟩
    have h1 := (Finite.card_le_one_iff_subsingleton (α := SuperOf p 3)).2 hsub
    omega
  obtain ⟨U, hU⟩ := hnot
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (stabS p) (⟨Pl, hpPl, hPl⟩ : SuperOf p 3) U
  have hgPl : (g : I ≃ₗ[ZMod 2] I) ∈ stabS Pl := by
    rw [← h]
    exact g.2
  have hPl' : Pl.map ((g : stabS p).1 : I →ₗ[ZMod 2] I) = Pl := map_eq_of_mem_stabS hgPl
  have hval := congrArg Subtype.val hg
  exact hU (hval.symm.trans hPl')

theorem flagSet_ncard [FiniteDimensional (ZMod 2) I] (hI : finrank (ZMod 2) I = 4)
    {p ℓ Pl : Submodule (ZMod 2) I} (hp : finrank (ZMod 2) p = 1)
    (hℓ : finrank (ZMod 2) ℓ = 2) (hPl : finrank (ZMod 2) Pl = 3)
    (hpℓ : p ≤ ℓ) (hℓPl : ℓ ≤ Pl) :
    (flagSet p ℓ Pl).ncard = 8 := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := index_flag_values hI hp hℓ hPl hpℓ hℓPl
  have hpPl : p ≤ Pl := hpℓ.trans hℓPl
  have d1 : stabS p ≠ stabS Pl := stabS_ne_of_flag hI hp hPl hpPl
  have d2 : stabS p ⊓ stabS ℓ ≠ stabS p ⊓ stabS Pl := fun h =>
    not_le_stabS_of_flag hI hℓ hPl hpℓ hℓPl (by rw [h]; exact inf_le_right)
  have d3 : stabS p ⊓ stabS ℓ ≠ stabS ℓ ⊓ stabS Pl := fun h =>
    not_le_stabS_of_flag hI hℓ hPl hpℓ hℓPl (by rw [h]; exact inf_le_right)
  have d4 : stabS p ⊓ stabS Pl ≠ stabS ℓ ⊓ stabS Pl := fun h => by
    have hle : stabS ℓ ⊓ stabS Pl ≤ stabS p ⊓ stabS ℓ :=
      le_inf (by rw [← h]; exact inf_le_left) inf_le_left
    have hidx := Subgroup.relIndex_mul_index hle
    rw [i4, i6] at hidx
    have hrel : (stabS ℓ ⊓ stabS Pl).relIndex (stabS p ⊓ stabS ℓ) = 1 := by omega
    have hK1 : stabS p ⊓ stabS ℓ ≤ stabS ℓ ⊓ stabS Pl := Subgroup.relIndex_eq_one.1 hrel
    exact not_le_stabS_of_flag hI hℓ hPl hpℓ hℓPl (hK1.trans inf_le_right)
  unfold flagSet
  have n01 : (⊤ : Subgroup (I ≃ₗ[ZMod 2] I)) ≠ stabS p := ne_of_index_ne (by rw [Subgroup.index_top, i1]; norm_num)
  have n02 : (⊤ : Subgroup (I ≃ₗ[ZMod 2] I)) ≠ stabS ℓ := ne_of_index_ne (by rw [Subgroup.index_top, i2]; norm_num)
  have n03 : (⊤ : Subgroup (I ≃ₗ[ZMod 2] I)) ≠ stabS Pl := ne_of_index_ne (by rw [Subgroup.index_top, i3]; norm_num)
  have n04 : (⊤ : Subgroup (I ≃ₗ[ZMod 2] I)) ≠ stabS p ⊓ stabS ℓ := ne_of_index_ne (by rw [Subgroup.index_top, i4]; norm_num)
  have n05 : (⊤ : Subgroup (I ≃ₗ[ZMod 2] I)) ≠ stabS p ⊓ stabS Pl := ne_of_index_ne (by rw [Subgroup.index_top, i5]; norm_num)
  have n06 : (⊤ : Subgroup (I ≃ₗ[ZMod 2] I)) ≠ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [Subgroup.index_top, i6]; norm_num)
  have n07 : (⊤ : Subgroup (I ≃ₗ[ZMod 2] I)) ≠ stabS p ⊓ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [Subgroup.index_top, i7]; norm_num)
  have n12 : stabS p ≠ stabS ℓ := ne_of_index_ne (by rw [i1, i2]; norm_num)
  have n13 : stabS p ≠ stabS Pl := d1
  have n14 : stabS p ≠ stabS p ⊓ stabS ℓ := ne_of_index_ne (by rw [i1, i4]; norm_num)
  have n15 : stabS p ≠ stabS p ⊓ stabS Pl := ne_of_index_ne (by rw [i1, i5]; norm_num)
  have n16 : stabS p ≠ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i1, i6]; norm_num)
  have n17 : stabS p ≠ stabS p ⊓ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i1, i7]; norm_num)
  have n23 : stabS ℓ ≠ stabS Pl := ne_of_index_ne (by rw [i2, i3]; norm_num)
  have n24 : stabS ℓ ≠ stabS p ⊓ stabS ℓ := ne_of_index_ne (by rw [i2, i4]; norm_num)
  have n25 : stabS ℓ ≠ stabS p ⊓ stabS Pl := ne_of_index_ne (by rw [i2, i5]; norm_num)
  have n26 : stabS ℓ ≠ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i2, i6]; norm_num)
  have n27 : stabS ℓ ≠ stabS p ⊓ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i2, i7]; norm_num)
  have n34 : stabS Pl ≠ stabS p ⊓ stabS ℓ := ne_of_index_ne (by rw [i3, i4]; norm_num)
  have n35 : stabS Pl ≠ stabS p ⊓ stabS Pl := ne_of_index_ne (by rw [i3, i5]; norm_num)
  have n36 : stabS Pl ≠ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i3, i6]; norm_num)
  have n37 : stabS Pl ≠ stabS p ⊓ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i3, i7]; norm_num)
  have n45 : stabS p ⊓ stabS ℓ ≠ stabS p ⊓ stabS Pl := d2
  have n46 : stabS p ⊓ stabS ℓ ≠ stabS ℓ ⊓ stabS Pl := d3
  have n47 : stabS p ⊓ stabS ℓ ≠ stabS p ⊓ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i4, i7]; norm_num)
  have n56 : stabS p ⊓ stabS Pl ≠ stabS ℓ ⊓ stabS Pl := d4
  have n57 : stabS p ⊓ stabS Pl ≠ stabS p ⊓ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i5, i7]; norm_num)
  have n67 : stabS ℓ ⊓ stabS Pl ≠ stabS p ⊓ stabS ℓ ⊓ stabS Pl := ne_of_index_ne (by rw [i6, i7]; norm_num)
  rw [Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_singleton]
  all_goals first
    | rfl
    | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
       repeat' constructor
       all_goals assumption)

theorem overgroups_flag_eq [FiniteDimensional (ZMod 2) I] (hI : finrank (ZMod 2) I = 4)
    {p ℓ Pl : Submodule (ZMod 2) I} (hp : finrank (ZMod 2) p = 1)
    (hℓ : finrank (ZMod 2) ℓ = 2) (hPl : finrank (ZMod 2) Pl = 3)
    (hpℓ : p ≤ ℓ) (hℓPl : ℓ ≤ Pl) :
    {X : Subgroup (I ≃ₗ[ZMod 2] I) | stabS p ⊓ stabS ℓ ⊓ stabS Pl ≤ X} = flagSet p ℓ Pl := by
  obtain ⟨e, he0, he1, he2⟩ := exists_basis_flag hI hp hℓ hPl hpℓ hℓPl
  have hB : Bstd e = stabS p ⊓ stabS ℓ ⊓ stabS Pl := by
    unfold Bstd
    rw [he0, he1, he2]
  have hsub : flagSet p ℓ Pl ⊆ {X : Subgroup (I ≃ₗ[ZMod 2] I) | stabS p ⊓ stabS ℓ ⊓ stabS Pl ≤ X} := by
    intro X hX
    simp only [flagSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    show stabS p ⊓ stabS ℓ ⊓ stabS Pl ≤ X
    rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact le_top
    · exact inf_le_left.trans inf_le_left
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
    · exact inf_le_left
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · exact le_rfl
  have hcard := flagSet_ncard hI hp hℓ hPl hpℓ hℓPl
  have hov := Bstd_overgroups_ncard_le e
  rw [hB] at hov
  haveI : Finite (I ≃ₗ[ZMod 2] I) :=
    Finite.of_injective (fun f : I ≃ₗ[ZMod 2] I => (f : I → I)) DFunLike.coe_injective
  haveI : Finite (Subgroup (I ≃ₗ[ZMod 2] I)) := inferInstance
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; exact hov)).symm

end Flags

end CFSG.Quasithin.H13.C1294
