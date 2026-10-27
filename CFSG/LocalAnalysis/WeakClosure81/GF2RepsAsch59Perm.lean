module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch59Blocks
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch59Solv
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch59Gen
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch59Cent
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.GF2Type.Smith1979W3.CaseD.Jordan
import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneCount2
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch59

open Equiv

theorem odd_card_of_involution {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {σ : Perm Ω}
    (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x y, σ x = x → σ y = y → x = y) {ω : Ω}
    (hω : σ ω = ω) : Odd (Fintype.card Ω) := by
  let f : Function.End Ω := fun x => σ x
  have hf : f ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq]
    funext x
    exact hσ x
  have hfp : Fintype.card (Function.fixedPoints f) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨ω, hω⟩, ?_⟩
    rintro ⟨x, hx⟩
    exact Subtype.ext (hfix x ω hx hω)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := Ω) (f := f)
    (p := 2) (n := 1) hf
  rw [hfp] at hmod
  rw [Nat.odd_iff]
  unfold Nat.ModEq at hmod
  omega

theorem image_sdiff_univ_eq_self {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (g : Perm Ω)
    {U : Finset Ω} (hU : ∀ x ∈ U, g x ∈ U) :
    (Finset.univ \ U).image g = Finset.univ \ U := by
  have hUimage : U.map g.toEmbedding = U := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro x hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hU y hy
    · rw [Finset.card_map]
  have himage : (Finset.univ \ U).image g =
      Finset.map g.toEmbedding (Finset.univ \ U) :=
    (Finset.map_eq_image g.toEmbedding (Finset.univ \ U)).symm
  rw [himage, Finset.map_sdiff, hUimage, Finset.univ_map_equiv_to_embedding]

theorem exists_isThreeCycle_mul_ne_mul {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h3 : 3 ≤ Fintype.card Ω) {σ : Perm Ω} (hσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x y, σ x = x → σ y = y → x = y) :
    ∃ g : Perm Ω, g.IsThreeCycle ∧ g * σ ≠ σ * g := by
  have hne : ∃ a, σ a ≠ a := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card Ω)
    exact hab (hfix a b (h a) (h b))
  obtain ⟨a, ha⟩ := hne
  let b := σ a
  have hab : a ≠ b := fun h => ha h.symm
  have hcard : 1 < (Finset.univ.erase a).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
    omega
  obtain ⟨c, hc, hcb⟩ := Finset.exists_mem_ne hcard b
  have hca : c ≠ a := (Finset.mem_erase.mp hc).1
  let g : Perm Ω := Equiv.swap a b * Equiv.swap a c
  have hg3 : g.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab (Ne.symm hca) (Ne.symm hcb)
  have hga : g a = c := by
    dsimp only [g]
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hca hcb
  have hgb : g b = a := by
    dsimp only [g]
    rw [Equiv.Perm.mul_apply]
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) (Ne.symm hcb)]
    exact Equiv.swap_apply_right a b
  refine ⟨g, hg3, ?_⟩
  intro heq
  have h1 : (g * σ) b = c := by
    rw [Equiv.Perm.mul_apply, show σ b = a from hσ a]
    exact hga
  have h2 : (σ * g) b = b := by
    rw [Equiv.Perm.mul_apply, hgb]
  have h := congrArg (fun p : Perm Ω => p b) heq
  rw [h1, h2] at h
  exact hcb h

theorem exists_isThreeCycle_support_subset_of_card_four {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {B : Finset Ω} (hB : B.card = 4) :
    ∃ c : Perm Ω, c.IsThreeCycle ∧ c.support ⊆ B := by
  have h0 : 0 < B.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h0
  have h1 : 1 < (B.erase a).card := by
    rw [Finset.card_erase_of_mem ha, hB]
    norm_num
  obtain ⟨b, hb, hba⟩ := Finset.exists_mem_ne h1 a
  have hbB : b ∈ B := Finset.mem_of_mem_erase hb
  have h2 : 1 < ((B.erase a).erase b).card := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha, hB]
    norm_num
  obtain ⟨c, hc, hca⟩ := Finset.exists_mem_ne h2 a
  have hcB : c ∈ B := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hc)
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  refine ⟨Equiv.swap a b * Equiv.swap a c,
    Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hba) (Ne.symm hca) (Ne.symm hcb), ?_⟩
  refine (Equiv.Perm.support_mul_le _ _).trans ?_
  rw [Equiv.Perm.support_swap (Ne.symm hba), Equiv.Perm.support_swap (Ne.symm hca),
    Finset.sup_eq_union]
  intro x hx
  rw [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_insert,
    Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl) | (rfl | rfl) <;> assumption

theorem card_sdiff_biUnion_eq_mod {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    {ℬ : Finset (Finset Ω)} (hdisj : (ℬ : Set (Finset Ω)).PairwiseDisjoint id)
    (hcard : ℬ.card = Fintype.card Ω / 4) (h4 : ∀ B ∈ ℬ, B.card = 4) :
    (Finset.univ \ ℬ.biUnion id).card = Fintype.card Ω % 4 := by
  have hUcard : (ℬ.biUnion id).card = 4 * ℬ.card := by
    rw [Finset.card_biUnion hdisj]
    calc ∑ B ∈ ℬ, (id B).card = ∑ _B ∈ ℬ, 4 :=
          Finset.sum_congr rfl (fun B hB => h4 B hB)
      _ = ℬ.card • 4 := Finset.sum_const 4
      _ = 4 * ℬ.card := by rw [smul_eq_mul, mul_comm]
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), hUcard, hcard,
    Finset.card_univ, ← Nat.mod_eq_sub_mul_div]

theorem exists_sup_eq_of_card {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h6 : 6 ≤ Fintype.card Ω) (h11 : Fintype.card Ω ≤ 11) (h9 : Fintype.card Ω ≠ 9)
    {G T : Subgroup (Perm Ω)} (hAG : alternatingGroup Ω ≤ G) (hTG : T ≤ G) (hT : IsPGroup 2 T) :
    ∃ Y X : Subgroup (Perm Ω), T ≤ Y ∧ Y < G ∧ T ≤ X ∧ X < G ∧ Y ⊔ X = G ∧
      Group.IsSolvable ↥Y ∧ ∃ φ : ↥X →* Perm (Fin 5), IsPGroup 2 φ.ker := by
  classical
  obtain ⟨σ, ℬ, hσ, hfix, hTσ, hBcard, hBdisj, hB4, hTB⟩ := exists_blocks_four hT
  have h4B : ∀ B ∈ ℬ, B.card = 4 := fun B hB => (hB4 B hB).1
  let R : Finset Ω := Finset.univ \ ℬ.biUnion id
  let parts : Finset (Finset Ω) := insert R ℬ
  let S : Set (Perm Ω) := {g : Perm Ω | g.IsThreeCycle ∧ ∃ P ∈ parts, g.support ⊆ P}
  let Y : Subgroup (Perm Ω) := Subgroup.closure S ⊔ T
  let X : Subgroup (Perm Ω) := Subgroup.centralizer {σ} ⊓ G
  have hRmod : R.card = Fintype.card Ω % 4 := by
    dsimp only [R]
    exact card_sdiff_biUnion_eq_mod hBdisj hBcard h4B
  have hRle : R.card ≤ 3 := by
    rw [hRmod]
    have h := Nat.mod_lt (Fintype.card Ω) (by norm_num : 0 < 4)
    omega
  have hpartsdisj : (parts : Set (Finset Ω)).PairwiseDisjoint id := by
    have hRdisj : ∀ B ∈ ℬ, Disjoint R B := by
      intro B hB
      rw [Finset.disjoint_left]
      intro x hxR hxB
      exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_biUnion.mpr ⟨B, hB, hxB⟩)
    intro P hP Q hQ hne
    change Disjoint P Q
    dsimp only [parts] at hP hQ
    change P ∈ insert R ℬ at hP
    change Q ∈ insert R ℬ at hQ
    rw [Finset.mem_insert] at hP hQ
    rcases hP with rfl | hP <;> rcases hQ with rfl | hQ
    · exact absurd rfl hne
    · exact hRdisj Q hQ
    · exact (hRdisj P hP).symm
    · exact hBdisj hP hQ hne
  have hparts4 : ∀ P ∈ parts, P.card ≤ 4 := by
    intro P hP
    dsimp only [parts] at hP
    change P ∈ insert R ℬ at hP
    rw [Finset.mem_insert] at hP
    rcases hP with rfl | hP
    · exact hRle.trans (by norm_num)
    · rw [h4B P hP]
  have hTn : Group.IsNilpotent ↥T :=
    IsPGroup.isNilpotent (p := 2) (hp := ⟨Nat.prime_two⟩) hT
  have hTsolv : Group.IsSolvable ↥T := IsNilpotent.to_isSolvable (h := hTn)
  have hTparts : ∀ g ∈ T, ∀ P ∈ parts, P.image g ∈ parts := by
    intro g hg P hP
    dsimp only [parts] at hP ⊢
    change P ∈ insert R ℬ at hP
    rw [Finset.mem_insert] at hP ⊢
    rcases hP with rfl | hP
    · have hUim : ∀ x ∈ ℬ.biUnion id, g x ∈ ℬ.biUnion id := by
        intro x hx
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨B, hB, hxB⟩ := hx
        exact ⟨B.image g, hTB g hg B hB, Finset.mem_image.mpr ⟨x, hxB, rfl⟩⟩
      have hRim : R.image g = R := by
        dsimp only [R]
        exact image_sdiff_univ_eq_self g hUim
      exact Or.inl hRim
    · exact Or.inr (hTB g hg P hP)
  have hYsolv : Group.IsSolvable ↥Y := by
    dsimp only [Y, S]
    exact isSolvable_closure_threeCycles_sup hpartsdisj hparts4 hTsolv hTparts
  have hclosure_le : Subgroup.closure S ≤ G :=
    (Subgroup.closure_le G).mpr fun g hg => hAG hg.1.mem_alternatingGroup
  have hYG : Y ≤ G := by
    dsimp only [Y]
    exact sup_le hclosure_le hTG
  have hGns : ¬ Group.IsSolvable ↥G := by
    intro hsol
    have hAsolv : Group.IsSolvable ↥(alternatingGroup Ω) :=
      @Group.isSolvable_of_isSolvable_injective ↥(alternatingGroup Ω) ↥G _
        _ (Subgroup.inclusion hAG) (Subgroup.inclusion_injective hAG) hsol
    exact CFSG.OddStandard.Solomon75.not_isSolvable_alternatingGroup' (by omega) hAsolv
  have hYlt : Y < G := by
    refine lt_of_le_of_ne hYG ?_
    intro hYG'
    exact hGns (hYG' ▸ hYsolv)
  have hBnonempty : ℬ.Nonempty := by
    have hpos : 0 < ℬ.card := by
      rw [hBcard]
      exact Nat.div_pos (by omega) (by norm_num)
    exact Finset.card_pos.mp hpos
  obtain ⟨B0, hB0⟩ := hBnonempty
  have hB0card : B0.card = 4 := h4B B0 hB0
  have hB0σ : ∀ x ∈ B0, σ x ∈ B0 := (hB4 B0 hB0).2
  have hSY : ∀ g : Perm Ω, g.IsThreeCycle → g.support ⊆ B0 → g ∈ Y := by
    intro g hg3 hgsupp
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hg3, ⟨B0, by
      dsimp only [parts]
      exact Finset.mem_insert_of_mem hB0, hgsupp⟩⟩)
  have hRY : ∀ ω, σ ω = ω → ∃ R' : Finset Ω, ω ∈ R' ∧ R'.card = 3 ∧
      ∀ g : Perm Ω, g.IsThreeCycle → g.support ⊆ R' → g ∈ Y := by
    intro ω hω
    have hodd := odd_card_of_involution hσ hfix hω
    have hRcard3 : R.card = 3 := by
      obtain ⟨k, hk⟩ := hodd
      have hn : Fintype.card Ω = 7 ∨ Fintype.card Ω = 11 := by omega
      rcases hn with h7 | h11'
      · rw [hRmod, h7]
      · rw [hRmod, h11']
    have hUinv : ∀ x ∈ ℬ.biUnion id, σ x ∈ ℬ.biUnion id := by
      intro x hx
      rw [Finset.mem_biUnion] at hx ⊢
      obtain ⟨B, hB, hxB⟩ := hx
      exact ⟨B, hB, (hB4 B hB).2 x hxB⟩
    have hRinv : ∀ x ∈ R, σ x ∈ R := by
      intro x hx
      dsimp only [R] at hx ⊢
      rw [Finset.mem_sdiff] at hx ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hxU
      exact hx.2 (by
        have := hUinv (σ x) hxU
        rwa [hσ x] at this)
    have hRfix : ω ∈ R := by
      obtain ⟨x, hxR, hxσ⟩ :=
        exists_fixed_of_odd_card_of_involution (by ext z; exact hσ z) hRinv
          (by rw [hRcard3]; norm_num)
      exact (hfix x ω hxσ hω) ▸ hxR
    refine ⟨R, hRfix, hRcard3, ?_⟩
    intro g hg3 hgsupp
    exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hg3, ⟨R, by
      dsimp only [parts]
      exact Finset.mem_insert_self R ℬ, hgsupp⟩⟩)
  have hgen : Y ⊔ X = G :=
    sup_centralizer_eq_of_threeCycles h6 hσ hfix hAG hYG hB0card hB0σ hSY hRY
  have hTY : T ≤ Y := by
    dsimp only [Y]
    exact le_sup_right
  have hTX : T ≤ X := by
    dsimp only [X]
    exact le_inf hTσ hTG
  have hXle : X ≤ G := by
    dsimp only [X]
    exact inf_le_right
  have hXlt : X < G := by
    refine lt_of_le_of_ne hXle ?_
    intro hXeq
    obtain ⟨g, hg3, hgnc⟩ :=
      exists_isThreeCycle_mul_ne_mul (by omega : 3 ≤ Fintype.card Ω) hσ hfix
    have hgG : g ∈ G := hAG hg3.mem_alternatingGroup
    have hgX : g ∉ X := by
      intro hgXmem
      have hgcent : g ∈ Subgroup.centralizer {σ} := (Subgroup.mem_inf.mp hgXmem).1
      exact hgnc (Subgroup.mem_centralizer_singleton_iff.mp hgcent)
    exact hgX (hXeq.symm ▸ hgG)
  refine ⟨Y, X, hTY, hYlt, hTX, hXlt, hgen, hYsolv, ?_⟩
  exact exists_hom_perm_five_isPGroup_ker h11 hσ hfix (by
    dsimp only [X]
    exact inf_le_left)

theorem exists_isSolvable_two_le_pRank_three {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (h8 : 8 ≤ Fintype.card Ω) {G T : Subgroup (Perm Ω)} (hAG : alternatingGroup Ω ≤ G)
    (hTG : T ≤ G) (hT : IsPGroup 2 T) :
    ∃ H : Subgroup (Perm Ω), T ≤ H ∧ H < G ∧ Group.IsSolvable ↥H ∧
      2 ≤ CFSG.Open.pRank 3 H := by
  classical
  obtain ⟨σ, ℬ, hσ, hfix, hTσ, hBcard, hBdisj, hB4, hTB⟩ := exists_blocks_four hT
  have h4B : ∀ B ∈ ℬ, B.card = 4 := fun B hB => (hB4 B hB).1
  let R : Finset Ω := Finset.univ \ ℬ.biUnion id
  let parts : Finset (Finset Ω) := insert R ℬ
  let S : Set (Perm Ω) := {g : Perm Ω | g.IsThreeCycle ∧ ∃ P ∈ parts, g.support ⊆ P}
  let Y : Subgroup (Perm Ω) := Subgroup.closure S ⊔ T
  have hRmod : R.card = Fintype.card Ω % 4 := by
    dsimp only [R]
    exact card_sdiff_biUnion_eq_mod hBdisj hBcard h4B
  have hRle : R.card ≤ 3 := by
    rw [hRmod]
    have h := Nat.mod_lt (Fintype.card Ω) (by norm_num : 0 < 4)
    omega
  have hpartsdisj : (parts : Set (Finset Ω)).PairwiseDisjoint id := by
    have hRdisj : ∀ B ∈ ℬ, Disjoint R B := by
      intro B hB
      rw [Finset.disjoint_left]
      intro x hxR hxB
      exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_biUnion.mpr ⟨B, hB, hxB⟩)
    intro P hP Q hQ hne
    change Disjoint P Q
    dsimp only [parts] at hP hQ
    change P ∈ insert R ℬ at hP
    change Q ∈ insert R ℬ at hQ
    rw [Finset.mem_insert] at hP hQ
    rcases hP with rfl | hP <;> rcases hQ with rfl | hQ
    · exact absurd rfl hne
    · exact hRdisj Q hQ
    · exact (hRdisj P hP).symm
    · exact hBdisj hP hQ hne
  have hparts4 : ∀ P ∈ parts, P.card ≤ 4 := by
    intro P hP
    dsimp only [parts] at hP
    change P ∈ insert R ℬ at hP
    rw [Finset.mem_insert] at hP
    rcases hP with rfl | hP
    · exact hRle.trans (by norm_num)
    · rw [h4B P hP]
  have hTn : Group.IsNilpotent ↥T :=
    IsPGroup.isNilpotent (p := 2) (hp := ⟨Nat.prime_two⟩) hT
  have hTsolv : Group.IsSolvable ↥T := IsNilpotent.to_isSolvable (h := hTn)
  have hTparts : ∀ g ∈ T, ∀ P ∈ parts, P.image g ∈ parts := by
    intro g hg P hP
    dsimp only [parts] at hP ⊢
    change P ∈ insert R ℬ at hP
    rw [Finset.mem_insert] at hP ⊢
    rcases hP with rfl | hP
    · have hUim : ∀ x ∈ ℬ.biUnion id, g x ∈ ℬ.biUnion id := by
        intro x hx
        rw [Finset.mem_biUnion] at hx ⊢
        obtain ⟨B, hB, hxB⟩ := hx
        exact ⟨B.image g, hTB g hg B hB, Finset.mem_image.mpr ⟨x, hxB, rfl⟩⟩
      have hRim : R.image g = R := by
        dsimp only [R]
        exact image_sdiff_univ_eq_self g hUim
      exact Or.inl hRim
    · exact Or.inr (hTB g hg P hP)
  have hYsolv : Group.IsSolvable ↥Y := by
    dsimp only [Y, S]
    exact isSolvable_closure_threeCycles_sup hpartsdisj hparts4 hTsolv hTparts
  have hclosure_le : Subgroup.closure S ≤ G :=
    (Subgroup.closure_le G).mpr fun g hg => hAG hg.1.mem_alternatingGroup
  have hYG : Y ≤ G := by
    dsimp only [Y]
    exact sup_le hclosure_le hTG
  have hGns : ¬ Group.IsSolvable ↥G := by
    intro hsol
    have hAsolv : Group.IsSolvable ↥(alternatingGroup Ω) :=
      @Group.isSolvable_of_isSolvable_injective ↥(alternatingGroup Ω) ↥G _
        _ (Subgroup.inclusion hAG) (Subgroup.inclusion_injective hAG) hsol
    exact CFSG.OddStandard.Solomon75.not_isSolvable_alternatingGroup' (by omega) hAsolv
  have hYlt : Y < G := by
    refine lt_of_le_of_ne hYG ?_
    intro hYG'
    exact hGns (hYG' ▸ hYsolv)
  have hBtwo : 1 < ℬ.card := by
    rw [hBcard]
    have hdecomp : Fintype.card Ω = 4 * (Fintype.card Ω / 4) + Fintype.card Ω % 4 := by
      have := Nat.div_add_mod (Fintype.card Ω) 4
      omega
    have hr := Nat.mod_lt (Fintype.card Ω) (by norm_num : 0 < 4)
    omega
  obtain ⟨B₁, hB₁, B₂, hB₂, hBne⟩ := Finset.one_lt_card.mp hBtwo
  obtain ⟨c₁, hc₁3, hc₁supp⟩ :=
    exists_isThreeCycle_support_subset_of_card_four (h4B B₁ hB₁)
  obtain ⟨c₂, hc₂3, hc₂supp⟩ :=
    exists_isThreeCycle_support_subset_of_card_four (h4B B₂ hB₂)
  have hdisjB : Disjoint B₁ B₂ := hBdisj hB₁ hB₂ hBne
  have hdisjSupp : Disjoint c₁.support c₂.support :=
    Finset.disjoint_of_subset_left hc₁supp
      (Finset.disjoint_of_subset_right hc₂supp hdisjB)
  have hdisjPerm : c₁.Disjoint c₂ :=
    Equiv.Perm.disjoint_iff_disjoint_support.mpr hdisjSupp
  have hc₁Y : c₁ ∈ Y :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hc₁3, ⟨B₁, by
      dsimp only [parts]
      exact Finset.mem_insert_of_mem hB₁, hc₁supp⟩⟩)
  have hc₂Y : c₂ ∈ Y :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨hc₂3, ⟨B₂, by
      dsimp only [parts]
      exact Finset.mem_insert_of_mem hB₂, hc₂supp⟩⟩)
  let E : Subgroup (Perm Ω) := Subgroup.closure ({c₁, c₂} : Set (Perm Ω))
  have hEY : E ≤ Y := by
    dsimp only [E]
    refine (Subgroup.closure_le Y).mpr ?_
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hc₁Y
    · exact hc₂Y
  have hEel : CFSG.Open.IsElemAbelian 3 E := by
    dsimp only [E]
    refine CFSG.Open.IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · rfl
      · exact hdisjPerm.commute.eq
      · exact hdisjPerm.commute.eq.symm
      · rfl
    · intro a ha
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with h | h
      · rw [h, ← hc₁3.orderOf]
        exact pow_orderOf_eq_one c₁
      · rw [h, ← hc₂3.orderOf]
        exact pow_orderOf_eq_one c₂
  have hEcard : Nat.card E = 3 ^ 2 := by
    dsimp only [E]
    rw [CFSG.GF2Type.Smith1979W3.CaseD.card_closure_threeCycles hc₁3 hc₂3 hdisjPerm]
    norm_num
  have hrank : 2 ≤ CFSG.Open.pRank 3 Y :=
    CFSG.LocalAnalysis.RankThreeTheoremC.pRank_ge_of_elemAbelian_card (p := 3) (k := 2)
      (by norm_num : 1 < 3) hEY hEel hEcard
  have hTY : T ≤ Y := by
    dsimp only [Y]
    exact le_sup_right
  exact ⟨Y, hTY, hYlt, hYsolv, hrank⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch59
