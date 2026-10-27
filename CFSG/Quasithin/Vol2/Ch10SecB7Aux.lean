module

public import CFSG.Quasithin.Vol2.Ch10SecB7Bridge
public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.Background.E6Hyp

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem autI_top_eq {V M : Subgroup G} (hV : IsElemAbelian 2 V)
    (hNM : Subgroup.normalizer (V : Set G) ≤ M) : autI hV ⊤ = autI hV M := by
  refine le_antisymm (fun φ hφ => ?_) (autI_mono hV le_top)
  obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hφ
  exact (mem_autI hV).2 ⟨g, hNM g.2, rfl⟩

theorem preI_inf_fixingSubgroup {V A U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hAN : A ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V) :
    preI hV A hAN (autI hV A ⊓ fixingSubgroup (MulAut (IntMod V hV))
      (modSub hV U : Set (IntMod V hV))) = A ⊓ Subgroup.centralizer (U : Set G) := by
  ext g
  rw [mem_preI, Subgroup.mem_inf]
  constructor
  · rintro ⟨hg, -, hfix⟩
    refine ⟨hg, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    have h1 := (mem_fixingSubgroup_iff _).mp hfix (IntMod.mk hV ⟨u, hUV hu⟩) hu
    rw [MulAut.smul_def, convHom_apply] at h1
    have h2 := congrArg IntMod.val h1
    rw [convI_apply_val] at h2
    have h3 : g * u * g⁻¹ = u := h2
    calc u * g = g * u * g⁻¹ * g := by rw [h3]
      _ = g * u := by group
  · rintro ⟨hg, hgC⟩
    refine ⟨hg, Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [convHom_apply]
      exact convI_mem_autI hV hg (hAN hg)
    · rw [mem_fixingSubgroup_iff]
      intro w hw
      rw [MulAut.smul_def, convHom_apply]
      exact convI_fix hV hgC hw

theorem le_of_modSub_le {V U U' : Subgroup G} (hV : IsElemAbelian 2 V) (hU : U ≤ V)
    (h : modSub hV U ≤ modSub hV U') : U ≤ U' :=
  fun v hv => h (show IntMod.mk hV ⟨v, hU hv⟩ ∈ modSub hV U from hv)

variable [Finite G]

open E3 in
theorem exists_isWOffenderAt {T V : Subgroup G} (hV : IsElemAbelian 2 V) (hT : HypE322 T V)
    {k : ℕ} (hk : wParam T V = k) : ∃ g : G, IsWOffenderAt T V g := by
  have hk1 : ¬ wClos V k T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    intro hle
    have : ((k + 1 : ℕ) : ℕ∞) ≤ wParam T V := by
      refine le_iInf₂ fun j hj => ?_
      have h1 : (k : ℕ∞) ≤ j := hk ▸ iInf₂_le j hj
      have h2 : j ≠ k := fun hjk => hj (hjk ▸ hle)
      have h1' : k ≤ j := Nat.cast_le.mp h1
      exact Nat.cast_le.mpr (by omega)
    rw [hk] at this
    exact absurd (Nat.cast_le.mp this) (by omega)
  obtain ⟨A, hA, hAC⟩ : ∃ A ∈ gammaSet V k T, ¬ A ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    exact hk1 (iSup₂_le fun A hA => le_inf hA.1 (not_not.mp fun h => hcon ⟨A, hA, h⟩))
  obtain ⟨hAT, g, hAg, hAk⟩ := hA
  have hAB : A ≤ conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf hAg (hAT.trans hT.normal)
  have hBk : mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) ≤ k :=
    hAk ▸ mQuot_mono hAB
  have hBk' :
      mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) = k := by
    by_contra hne
    have hlt := lt_of_le_of_ne hBk hne
    apply hAC
    refine hAB.trans ?_
    have hTN : IsSylowIn 2 T (Subgroup.normalizer (V : Set G)) :=
      B6.isSylowTwoOf_mono hT.sylow hT.normal le_top
    have hB2 : IsPGroup 2 ↥(conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) :=
      (isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) g).to_le inf_le_left
    obtain ⟨n, hn, hle⟩ := exists_le_conj_of_isSylowIn hTN inf_le_right hB2
    have h1 : conjSubgroup (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ≤ T := by
      have := conjSubgroup_mono_left n⁻¹ hle
      rwa [conjSubgroup_conj_inv] at this
    have hmem : conjSubgroup (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ∈
        gammaSet V (mQuot (conjSubgroup V g) (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)))
          T := by
      refine ⟨h1, g * n⁻¹, ?_, ?_⟩
      · rw [← conjSubgroup_conjSubgroup]
        exact conjSubgroup_mono_left n⁻¹ inf_le_left
      · rw [← conjSubgroup_conjSubgroup, mQuot_conjSubgroup]
    have h2 : conjSubgroup (conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G)) n⁻¹ ≤
        Subgroup.centralizer (V : Set G) :=
      ((le_wClos hmem).trans (wClos_le_of_lt_wParam (by rw [hk]; exact_mod_cast hlt))).trans
        inf_le_right
    have hnV : conjSubgroup V n = V := conjSubgroup_eq_iff_mem_normalizer.2 hn
    have h3 := conjSubgroup_mono_left n h2
    rwa [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one, conjSubgroup_centralizer,
      hnV] at h3
  refine ⟨g, fun hbot => hAC (hAg.trans ?_), by rw [hk, hBk']⟩
  exact le_centralizer_iff_comm.mp (commutator_eq_bot_iff_le_centralizer'.mp hbot)

variable {T L I : Subgroup G}

theorem hypE61_of (h331 : Stmt3_3_1) (h1012 : Stmt10_1_2) (hyp : Hyp10 G T L I)
    (h6 : Case10_1_1Six T L I) : E6.HypE61 T (fsuM T L) (fsuVM T L I) where
  simple := hyp.fsu.simple
  nonabelian := hyp.fsu.nonabelian
  qtke := hyp.fsu.qtke
  sylow := hyp.fsu.sylow
  inM := ⟨fsuM_isMaxTwoLocal h331 hyp, le_fsuM T L⟩
  ne_bot := SecA.fsuVM_ne_bot hyp.fsu
  isElemAbelian := SecA.isElemAbelian_fsuVM hyp
  le := SecA.fsuVM_le_T hyp
  normal := SecA.le_normalizer_fsuVM T L I
  tiSet := ⟨SecA.fsuVM_le_fsuM hyp.fsu, fun _ hg hgn =>
    absurd (SecA.fsuM_le_normalizer_fsuVM T L I hg) hgn⟩
  unique := by
    have hU := isUniqueM_L0T h331 hyp
    have hle : fsuL0 T L ⊔ T ≤ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) : Subgroup G) : Set G) ⊓
          (fsuM T L ⊓ Subgroup.normalizer (fsuVM T L I : Set G)) :=
      le_inf ((h1012 G T L I hyp).2.2.2.1 h6)
        (le_inf hU.1.2 (hU.1.2.trans (SecA.fsuM_le_normalizer_fsuVM T L I)))
    exact ⟨⟨hU.1.1, inf_le_right.trans inf_le_left⟩, fun M' hM' => hU.2 M' ⟨hM'.1, hle.trans hM'.2⟩⟩

end CFSG.Quasithin.Vol2.Ch10.SecB
