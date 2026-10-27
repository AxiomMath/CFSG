module

public import CFSG.Quasithin.Vol2.Ch7Lem741Odd
public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsD
public import CFSG.Quasithin.Background.HL3NineM
public import CFSG.Quasithin.Vol2.Ch8Sec2D1Inputs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def HL3NineHyp : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (L M : Subgroup (MulAut V)), Mathieu.IsOver L M →
    ∀ n : ℕ, 1 ≤ n → BinaryNineTensor L ⊤ ⊥ n → ∀ A ∈ aSet (2 * n + 1) M, 3 * n < rk ↥A →
      rkIdx (gammaCheck (3 * n) A) ≤ n

variable {G : Type} [Group G] [Finite G]

theorem gammaCheck_le_normalizer {V : Subgroup G} (hV : IsElemAbelian 2 V) {g : G} {k : ℕ}
    (hk : ((mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) + k :
      ℕ) : ℕ∞) < rParam V) :
    gammaCheck k (autI hV (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G))) ≤
      (V ⊓ Subgroup.normalizer (conjSubgroup V g : Set G)).comap (E3.valHom hV) := by
  set A := conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) with hAdef
  have hAN : A ≤ Subgroup.normalizer (V : Set G) := inf_le_right
  refine iSup_le fun X => iSup_le fun hX => iSup_le fun hXm => ?_
  intro v hv
  have hBA : preI hV A hAN X ≤ A := preI_le hV
  have hmB : mQuot A (preI hV A hAN X) = mQuot (autI hV A) X := (mQuot_autI_preI hV hAN hX).symm
  have hadd := mQuot_add (V := conjSubgroup V g) hBA inf_le_left
  have hC : V ⊓ Subgroup.centralizer (preI hV A hAN X : Set G) ≤
      Subgroup.normalizer (conjSubgroup V g : Set G) := by
    by_contra hC
    have h1 := e3_4_one hBA hC
    have h2 : mQuot (conjSubgroup V g) (preI hV A hAN X) ≤ mQuot (conjSubgroup V g) A + k := by
      omega
    exact absurd (h1.trans (Nat.cast_le.2 h2)) (not_le.2 hk)
  exact ⟨v.val_mem, hC ⟨v.val_mem, (mem_fixV_iff_preI hV hAN hX v).1 hv⟩⟩

omit [Finite G] in
theorem fixV_autI_eq_comap {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set G)) :
    fixV (autI hV A) = (V ⊓ Subgroup.centralizer (A : Set G)).comap (E3.valHom hV) := by
  ext v
  rw [mem_fixV_autI hV hA v]
  exact ⟨fun h => ⟨v.val_mem, h⟩, fun h => h.2⟩

variable {T L I : Subgroup G}

theorem stmt7_5_6_two_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hmod : StmtFSUModule) (h325 : Stmt3_2_5) (hin : Input8_1_2) (h711n : Stmt7_1_1_normal)
    (htab : HTab82) (hL9 : HL3Nine82) (hHyp : HL3NineHyp) : Stmt7_5_6_two := by
  intro G _ _ T L I hyp h731 hab n hrow
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM h37 h38 h39 hyp.fsu hV hN
  have hT := hypE322_of_fsu hyp.fsu hV hN
  have h24 := hypE324_of_hyp702 hyp hV hNM
  have hTL : T ≤ Subgroup.normalizer (L : Set G) :=
    h711n G T L I hyp hab (Or.inr (Or.inr (Or.inl ⟨n, hrow⟩)))
  have hML := fsuM_le_normalizer_of_le_normalizer hTL
  obtain ⟨hn, hnat⟩ := hrow
  have hL : BinaryNineTensor (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ n := hnat
  have hOver : Mathieu.IsOver (autI hV (fsuL0 T L)) (autI hV ⊤) :=
    ⟨autI_fsuL0_le hV, autI_top_le_normalizer hV hNM⟩
  obtain ⟨hT9, -, -⟩ := htab (IntMod (fsuV T I) hV) _ _ hOver
  obtain ⟨hm2, hβ, hα1, hα⟩ := hT9 n hn hL
  obtain ⟨-, hL93, -⟩ := hL9 (IntMod (fsuV T I) hV) _ _ hOver n hn hL
  have hr : ((4 * n : ℕ) : ℕ∞) ≤ rParam (fsuV T I) := by
    refine le_trans (le_min ?_ hβ) (stmt7_4_1_of h37 h38 h39 hmod h325 hin G T L I hyp h731 hML hV)
    rcases Nat.lt_or_ge 1 n with h1 | h1
    · rw [hα h1]
      exact le_top
    · obtain rfl : n = 1 := le_antisymm h1 hn
      exact le_trans (by norm_num) (hα1 rfl)
  have hm : 3 * n ≤ mParam (autI hV ⊤) :=
    H42_L3Nine_mParam hn hL (autI_fsuL0_le hV) (autI_top_le_normalizer hV hNM)
  have hs : 3 * n ≤ sParam hV := by
    unfold sParam
    have h1 : ((3 * n : ℕ) : ℕ∞) ≤ min (rParam (fsuV T I)) ((mParam (autI hV ⊤) : ℕ) : ℕ∞) :=
      le_min (le_trans (Nat.cast_le.2 (by omega)) hr) (Nat.cast_le.2 hm)
    have h2 : min (rParam (fsuV T I)) ((mParam (autI hV ⊤) : ℕ) : ℕ∞) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENat.natCast_ne_top _) (min_le_right _ _)
    simpa [ENat.toNat_natCast] using ENat.toNat_le_toNat h1 h2
  by_contra hw
  rw [not_le] at hw
  obtain ⟨g, hg⟩ := exists_isWOffenderAt hV hT (ne_top_of_lt hw)
  set Vg := conjSubgroup (fsuV T I) g with hVg
  set A := Vg ⊓ Subgroup.normalizer (fsuV T I : Set G) with hAdef
  set b := mQuot Vg A with hbdef
  have hwb : wParam T (fsuV T I) = (b : ℕ∞) := hg.2
  have hbn : b < n := by
    rw [hwb] at hw
    exact_mod_cast hw
  have hAN : A ≤ Subgroup.normalizer (fsuV T I : Set G) := inf_le_right
  have hAel : IsElemAbelian 2 A :=
    B2F.isElemAbelian_mono inf_le_left (isElemAbelian_conjSubgroup hV g)
  have hAe2 : IsElemAbelian2 (autI hV A) := isElemAbelian2_autI hV hAel hAN
  have hbs : b < sParam hV := by omega
  have hA2' : autI hV A ∈ aSet (sParam hV - b) (autI hV ⊤) := e3_10_two hV hbs hg.1
  have hA2 : autI hV A ∈ aSet (2 * n + 1) (autI hV ⊤) := aSet_anti (by omega) _ hA2'
  have hrA : 3 * n < rk ↥(autI hV A) := by
    have h1 : rParam (fsuV T I) - wParam T (fsuV T I) ≤ ((rk ↥(autI hV A) : ℕ) : ℕ∞) :=
      e3_28_three hV hT h24 hg
    rw [hwb] at h1
    have h2 := (tsub_le_tsub_right hr (b : ℕ∞)).trans h1
    rw [← ENat.natCast_sub] at h2
    have h3 : 4 * n - b ≤ rk ↥(autI hV A) := by exact_mod_cast h2
    omega
  set D := fsuV T I ⊓ Subgroup.normalizer (Vg : Set G) with hDdef
  have hbk : b + 3 * n < 4 * n := by omega
  have hWD : gammaCheck (3 * n) (autI hV A) ≤ D.comap (E3.valHom hV) :=
    gammaCheck_le_normalizer hV (g := g) (k := 3 * n) (lt_of_lt_of_le (Nat.cast_lt.2 hbk) hr)
  have hDn : mQuot (fsuV T I) D ≤ n := by
    rw [mQuot_eq_rkIdx_comap hV (U := D) inf_le_left]
    exact (rkIdx_anti hWD).trans (hHyp _ _ _ hOver n hn hL _ hA2 hrA)
  have h1010 : fsuV T I ⊓ Subgroup.centralizer (A : Set G) =
      fsuV T I ⊓ Subgroup.centralizer (Vg : Set G) := e3_10_one hV hbs
  have hCV : 5 * n ≤ mQuot (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (Vg : Set G)) := by
    rw [← h1010, mQuot_eq_rkIdx_comap hV inf_le_left, ← fixV_autI_eq_comap hV hAN]
    exact hL93 _ (autI_mono hV le_top) hAe2 (Or.inl hrA.le)
  have hCD : fsuV T I ⊓ Subgroup.centralizer (Vg : Set G) ≤ D :=
    inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have haddD := mQuot_add hCD (inf_le_left : D ≤ fsuV T I)
  set Ds := conjSubgroup D g⁻¹ with hDs
  have hDsN : Ds ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    have h1 : Ds ≤ conjSubgroup (Subgroup.normalizer (Vg : Set G)) g⁻¹ :=
      conjSubgroup_mono_left _ inf_le_right
    rwa [conjSubgroup_normalizer, hVg, conjSubgroup_conj_inv] at h1
  have hDsel : IsElemAbelian 2 Ds :=
    B2F.isElemAbelian_mono (conjSubgroup_mono_left _ inf_le_left)
      (isElemAbelian_conjSubgroup hV g⁻¹)
  have hDsC : Ds ⊓ Subgroup.centralizer (fsuV T I : Set G) =
      conjSubgroup (fsuV T I ⊓ Subgroup.centralizer (Vg : Set G)) g⁻¹ := by
    have h1 : D ⊓ Subgroup.centralizer (Vg : Set G) =
        fsuV T I ⊓ Subgroup.centralizer (Vg : Set G) :=
      inf_normalizer_inf_centralizer (fsuV T I) Vg
    rw [← h1, conjSubgroup_inf, conjSubgroup_centralizer, hVg, conjSubgroup_conj_inv]
  have hrDs : 3 * n ≤ rk ↥(autI hV Ds) := by
    rw [rk_autI_eq_mQuot hV hDsN, hDsC, hDs, mQuot_conjSubgroup]
    omega
  have hCDs : 5 * n ≤ mQuot (fsuV T I) (fsuV T I ⊓ Subgroup.centralizer (Ds : Set G)) := by
    rw [mQuot_eq_rkIdx_comap hV inf_le_left, ← fixV_autI_eq_comap hV hDsN]
    exact hL93 _ (autI_mono hV le_top) (isElemAbelian2_autI hV hDsel hDsN) (Or.inl hrDs)
  have hconj : conjSubgroup (fsuV T I ⊓ Subgroup.centralizer (Ds : Set G)) g =
      Vg ⊓ Subgroup.centralizer (D : Set G) := by
    rw [conjSubgroup_inf, conjSubgroup_centralizer, hDs, conjSubgroup_inv_conj]
  have hCVgD : 5 * n ≤ mQuot Vg (Vg ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [← hconj, hVg, mQuot_conjSubgroup]
    exact hCDs
  have hle : Vg ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
      Vg ⊓ Subgroup.centralizer (D : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (inf_le_left : D ≤ fsuV T I))
  have h1 := mQuot_mono (V := Vg) hle
  have h2 : mQuot Vg (Vg ⊓ Subgroup.centralizer (fsuV T I : Set G)) = b + rk ↥(autI hV A) := by
    have h := mQuot_conj_inf_centralizer hV g
    rwa [inf_normalizer_inf_centralizer] at h
  have h3 : rk ↥(autI hV A) ≤ 4 * n := (rk_autI_le_pRank hV (g := g)).trans hm2
  omega

end CFSG.Quasithin.H13
