module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12c3
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KO4PlusSwap.Holds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
import CFSG.Quasithin.Background.FFC5Two

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

section Conj

variable {A : Type*} [Group A]

private theorem map_conj_one (K : Subgroup A) : K.map (MulAut.conj (1 : A)).toMonoidHom = K := by
  ext x
  simp

private theorem map_conj_of_mem {K : Subgroup A} {s : A} (hs : s ∈ K) :
    K.map (MulAut.conj s).toMonoidHom = K := by
  refine le_antisymm ?_ fun x hx => ⟨s⁻¹ * x * s, K.mul_mem (K.mul_mem (K.inv_mem hs) hx) hs, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩
    simpa [MulAut.conj_apply] using K.mul_mem (K.mul_mem hs hk) (K.inv_mem hs)
  · simp [MulAut.conj_apply, mul_assoc]

private theorem mem_normalizer_of_map_conj_eq {K : Subgroup A} {s : A}
    (h : K.map (MulAut.conj s).toMonoidHom = K) : s ∈ normalizer (K : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hmem : s * x * s⁻¹ ∈ K.map (MulAut.conj s).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [h] at hmem
  · intro hx
    rw [← h] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    have hkx' : s * k * s⁻¹ = s * x * s⁻¹ := by simpa [MulAut.conj_apply] using hkx
    rw [mul_left_inj, mul_right_inj] at hkx'
    exact hkx' ▸ hk

private theorem map_conj_map_conj (K : Subgroup A) (x y : A) :
    (K.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      K.map (MulAut.conj (x * y)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, mul_assoc]

private theorem le_of_mem_conjSet {K N X : Subgroup A} (hKN : K ≤ N) (hX : X ∈ conjSet K N) :
    X ≤ N := by
  obtain ⟨n, hn, rfl⟩ := hX
  rintro _ ⟨k, hk, rfl⟩
  simpa [MulAut.conj_apply] using N.mul_mem (N.mul_mem hn (hKN hk)) (N.inv_mem hn)

private theorem map_conj_mem_conjSet {K N X : Subgroup A} (hX : X ∈ conjSet K N) {x : A}
    (hx : x ∈ N) : X.map (MulAut.conj x).toMonoidHom ∈ conjSet K N := by
  obtain ⟨n, hn, rfl⟩ := hX
  exact ⟨x * n, N.mul_mem hx hn, map_conj_map_conj K x n⟩

end Conj

section Module

variable {W : Type} [CommGroup W]

private theorem mem_commV_map_conj {X : Subgroup (MulAut W)} (y : MulAut W) {u : W}
    (hu : u ∈ commV X) : y u ∈ commV (X.map (MulAut.conj y).toMonoidHom) := by
  have hle : commV X ≤ (commV (X.map (MulAut.conj y).toMonoidHom)).comap y.toMonoidHom := by
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨x, hx, v, rfl⟩
    refine Subgroup.subset_closure ⟨y * x * y⁻¹, ⟨x, hx, by simp [MulAut.conj_apply]⟩, y v, ?_⟩
    simp
  exact hle hu

private theorem disjoint_commV {Y R : Subgroup (MulAut W)}
    (hind : iSupIndep fun X : conjSet R Y => commV (X : Subgroup (MulAut W)))
    {X X' : Subgroup (MulAut W)} (hX : X ∈ conjSet R Y) (hX' : X' ∈ conjSet R Y) (hne : X ≠ X') :
    Disjoint (commV X) (commV X') :=
  hind.pairwiseDisjoint (i := ⟨X, hX⟩) (j := ⟨X', hX'⟩) fun h => hne (congrArg Subtype.val h)

private theorem disjoint_commV_sup {Y R : Subgroup (MulAut W)}
    (hind : iSupIndep fun X : conjSet R Y => commV (X : Subgroup (MulAut W)))
    {Z X X' : Subgroup (MulAut W)} (hZ : Z ∈ conjSet R Y) (hX : X ∈ conjSet R Y)
    (hX' : X' ∈ conjSet R Y) (hZX : Z ≠ X) (hZX' : Z ≠ X') :
    Disjoint (commV Z) (commV X ⊔ commV X') := by
  refine (iSupIndep_def.mp hind ⟨Z, hZ⟩).mono_right (sup_le ?_ ?_)
  · exact le_iSup_of_le (⟨X, hX⟩ : conjSet R Y)
      (le_iSup_of_le (fun h => hZX (congrArg Subtype.val h).symm) le_rfl)
  · exact le_iSup_of_le (⟨X', hX'⟩ : conjSet R Y)
      (le_iSup_of_le (fun h => hZX' (congrArg Subtype.val h).symm) le_rfl)

theorem apply_eq_of_mem_commV {Y R : Subgroup (MulAut W)} (hRY : R ≤ Y)
    (hind : iSupIndep fun X : conjSet R Y => commV (X : Subgroup (MulAut W)))
    {X X' : Subgroup (MulAut W)} (hX : X ∈ conjSet R Y) (hX' : X' ∈ conjSet R Y) (hne : X ≠ X')
    {x : MulAut W} (hx : x ∈ X') {u : W} (hu : u ∈ commV X) : x u = u := by
  have hxY : x ∈ Y := le_of_mem_conjSet hRY hX' hx
  have hZ := map_conj_mem_conjSet hX hxY
  have hv : x u ∈ commV (X.map (MulAut.conj x).toMonoidHom) := mem_commV_map_conj x hu
  have hw : x u * u⁻¹ ∈ commV X' := Subgroup.subset_closure ⟨x, hx, u, rfl⟩
  have hXX' : Disjoint (commV X) (commV X') := disjoint_commV hind hX hX' hne
  by_cases hZX : X.map (MulAut.conj x).toMonoidHom = X
  · rw [hZX] at hv
    exact mul_inv_eq_one.mp
      (Subgroup.disjoint_def.mp hXX' ((commV X).mul_mem hv ((commV X).inv_mem hu)) hw)
  by_cases hZX' : X.map (MulAut.conj x).toMonoidHom = X'
  · rw [hZX'] at hv
    have hu' : u ∈ commV X' := by
      simpa using (commV X').mul_mem ((commV X').inv_mem hw) hv
    rw [Subgroup.disjoint_def.mp hXX' hu hu', map_one]
  · have hvs : x u ∈ commV X ⊔ commV X' := by
      simpa using Subgroup.mul_mem_sup hu hw
    have h1 : x u = 1 :=
      Subgroup.disjoint_def.mp (disjoint_commV_sup hind hZ hX hX' hZX hZX') hv hvs
    have hu1 : u = 1 := by simpa using congrArg x.symm h1
    rw [h1, hu1]

private theorem eq_one_of_mem_conjSet {Y R : Subgroup (MulAut W)}
    (hfaith : ∀ g ∈ R, (∀ u ∈ commV R, g u = u) → g = 1)
    {X : Subgroup (MulAut W)} (hX : X ∈ conjSet R Y) {g : MulAut W} (hg : g ∈ X)
    (hgu : ∀ u ∈ commV X, g u = u) : g = 1 := by
  obtain ⟨y, -, rfl⟩ := hX
  obtain ⟨r, hr, rfl⟩ := hg
  have hr1 : r = 1 := hfaith r hr fun u hu => by
    simpa [MulAut.conj_apply] using hgu (y u) (mem_commV_map_conj y hu)
  rw [hr1, map_one]

end Module

theorem conjSet_eq_singleton_of_o4Plus
    {W : Type} [CommGroup W] [Finite W] {Y L T R : Subgroup (MulAut W)} {e : ℕ}
    (hL : IsComponentOf L Y) (hT : IsSylowIn 2 T Y)
    (hfix : fixV (⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) = ⊥)
    (hncard : (conjSet L T).ncard ≤ 2)
    (hRY : R ≤ Y) (hsum : IsDirSumOver (conjSet R Y) commV)
    (hLR : CFSG.Open.IsSubnormal L R) (hnat : IsNaturalO4Plus R e) :
    conjSet R Y = {R} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLR' : L ≤ R := hLR.le
  have hL1 : L ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot L).mp (MinDegLow.nontrivial_of_isQuasisimple hL.2.2)
  have hconjL : ∀ y : MulAut W, L.map (MulAut.conj y).toMonoidHom ≠ ⊥ := fun y h =>
    hL1 ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj y).injective).mp h)
  have hfaith : ∀ g ∈ R, (∀ u ∈ commV R, g u = u) → g = 1 := by
    obtain ⟨K, _, _, -, π, hπ⟩ := hnat
    exact FFC.faithful_on_of_realizes (FFModel.nat_faithful _) hπ
  have hind := hsum.1
  have hRmem : R ∈ conjSet R Y := ⟨1, Y.one_mem, (map_conj_one R).symm⟩
  have hmeet : ∀ {X X' : Subgroup (MulAut W)}, X ∈ conjSet R Y → X' ∈ conjSet R Y → X ≠ X' →
      ∀ {B : Subgroup (MulAut W)}, B ≤ X → B ≤ X' → B = ⊥ := by
    intro X X' hX hX' hne B hBX hBX'
    refine eq_bot_iff.mpr fun b hb => Subgroup.mem_bot.mpr ?_
    exact eq_one_of_mem_conjSet hfaith hX (hBX hb) fun u hu =>
      apply_eq_of_mem_commV hRY hind hX hX' hne (hBX' hb) hu
  have hcommR : commV R ≠ ⊥ := by
    intro h
    refine hL1 (eq_bot_iff.mpr fun l hl => Subgroup.mem_bot.mpr ?_)
    refine hfaith l (hLR' hl) fun u hu => ?_
    rw [h, Subgroup.mem_bot] at hu
    rw [hu, map_one]
  have hnormR : ∀ X ∈ conjSet R Y, X ≤ normalizer (R : Set (MulAut W)) := by
    intro X hX x hx
    by_cases hXR : X = R
    · subst hXR
      exact Subgroup.le_normalizer hx
    refine mem_normalizer_of_map_conj_eq ?_
    by_contra hZR
    have hZ := map_conj_mem_conjSet hRmem (le_of_mem_conjSet hRY hX hx)
    refine hcommR (eq_bot_iff.mpr fun u hu => ?_)
    have hxu : x u = u := apply_eq_of_mem_commV hRY hind hRmem hX (Ne.symm hXR) hx hu
    have hv := mem_commV_map_conj x hu
    rw [hxu] at hv
    exact Subgroup.disjoint_def.mp (disjoint_commV hind hZ hRmem hZR) hv hu
  have hRsub : CFSG.Open.IsSubnormal R Y := by
    set M := ⨆ X ∈ conjSet R Y, X
    have hMY : M ≤ Y := iSup₂_le fun X hX => le_of_mem_conjSet hRY hX
    have hRM : R ≤ M := le_iSup₂_of_le (f := fun X (_ : X ∈ conjSet R Y) => X) R hRmem le_rfl
    have hMn : (M.subgroupOf Y).Normal := by
      refine (iSup_map_conj_eq_self_iff hMY).mp (le_antisymm (iSup₂_le fun g hg => ?_) ?_)
      · refine Subgroup.map_le_iff_le_comap.mpr (iSup₂_le fun X hX => ?_)
        exact Subgroup.map_le_iff_le_comap.mp (le_iSup₂_of_le
          (f := fun X (_ : X ∈ conjSet R Y) => X) _ (map_conj_mem_conjSet hX hg) le_rfl)
      · exact le_iSup₂_of_le (f := fun g (_ : g ∈ Y) => M.map (MulAut.conj g).toMonoidHom) 1
          Y.one_mem (map_conj_one M).ge
    have hRn : (R.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr (iSup₂_le hnormR)
    exact CFSG.Open.IsSubnormal.step hRM hRn
      (CFSG.Open.IsSubnormal.step hMY hMn (CFSG.Open.IsSubnormal.refl Y))
  have hTR : ∀ t ∈ T, R.map (MulAut.conj t).toMonoidHom = R := by
    intro t ht
    by_contra hRt
    have hRtmem := map_conj_mem_conjSet hRmem (hT.1 ht)
    have hLt : L.map (MulAut.conj t).toMonoidHom ≠ L := fun h =>
      hL1 (hmeet hRmem hRtmem (Ne.symm hRt) hLR' (h ▸ Subgroup.map_mono hLR'))
    have hfin : (conjSet L T).Finite :=
      ((T : Set (MulAut W)).toFinite.image fun n => L.map (MulAut.conj n).toMonoidHom).subset
        fun X ⟨n, hn, hX⟩ => ⟨n, hn, hX.symm⟩
    have hL0 : L ∈ conjSet L T := ⟨1, T.one_mem, (map_conj_one L).symm⟩
    have hLT : ∀ s ∈ T, L.map (MulAut.conj s).toMonoidHom = L ∨
        L.map (MulAut.conj s).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
      intro s hs
      by_contra hcon
      rw [not_or] at hcon
      have h3 : 2 < (conjSet L T).ncard := (Set.two_lt_ncard hfin).mpr
        ⟨L, hL0, _, ⟨t, ht, rfl⟩, _, ⟨s, hs, rfl⟩, Ne.symm hLt, Ne.symm hcon.1, Ne.symm hcon.2⟩
      omega
    have hSN : T ⊓ R ≤ normalizer (L : Set (MulAut W)) := by
      intro s hs
      refine mem_normalizer_of_map_conj_eq ((hLT s hs.1).resolve_right fun h => ?_)
      have hle : L.map (MulAut.conj t).toMonoidHom ≤ R :=
        h ▸ (Subgroup.map_mono hLR').trans (map_conj_of_mem hs.2).le
      exact hconjL t (hmeet hRmem hRtmem (Ne.symm hRt) hle (Subgroup.map_mono hLR'))
    exact kO4PlusSwap_holds W R L (T ⊓ R) e hnat hL.2.2 hLR
      (F6.isSylowIn_inf_of_isSubnormal hRsub hT) hSN
  have hLTR : (⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) ≤ R :=
    iSup₂_le fun t ht => (Subgroup.map_mono hLR').trans (hTR t ht).le
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨hRmem, fun X hX => ?_⟩
  by_contra hXR
  have hXbot : commV X = ⊥ := by
    rw [eq_bot_iff, ← hfix]
    intro u hu
    exact mem_fixV.mpr fun g hg => apply_eq_of_mem_commV hRY hind hX hRmem hXR (hLTR hg) hu
  obtain ⟨y, hy, rfl⟩ := hX
  refine hconjL y (eq_bot_iff.mpr fun g hg => Subgroup.mem_bot.mpr ?_)
  refine eq_one_of_mem_conjSet hfaith ⟨y, hy, rfl⟩ (Subgroup.map_mono hLR' hg) fun u hu => ?_
  rw [hXbot, Subgroup.mem_bot] at hu
  rw [hu, map_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
