module

public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.Vol2.Ch1Unique
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuV_ne_bot (hfsu : FSU G T L I) : fsuV T I ≠ ⊥ := by
  intro h
  apply hfsu.irrPlus.2.1
  rw [eq_bot_iff, ← h]
  intro x hx
  refine Subgroup.subset_closure ⟨1, T.one_mem, x, hx, by group⟩

omit [Finite G] in
theorem le_fsuV (I T : Subgroup G) : I ≤ fsuV T I := fun x hx =>
  Subgroup.subset_closure ⟨1, T.one_mem, x, hx, by group⟩

omit [Finite G] in
theorem le_fsuL0 (T L : Subgroup G) : L ≤ fsuL0 T L := fun x hx =>
  Subgroup.subset_closure ⟨1, T.one_mem, x, hx, by group⟩

omit [Finite G] in
theorem isPGroup_of_isElemAbelian_two {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    IsPGroup 2 V := CFSG.Open.IsElemAbelian.isPGroup hV

theorem isSylowIn_top_of_fsu (hfsu : FSU G T L I) : IsSylowIn 2 T ⊤ :=
  ⟨le_top, hfsu.sylow.1, by rw [Subgroup.relIndex_top_right]; exact hfsu.sylow.2⟩

theorem fsuV_le_T (hfsu : FSU G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) : fsuV T I ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_right.trans hN
  have hp : IsPGroup 2 ↥(fsuV T I ⊔ T) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_of_isElemAbelian_two hV) hfsu.sylow.1 hTN
  let S : Sylow 2 G := hfsu.sylow.1.toSylow hfsu.sylow.2
  have hS : (S : Subgroup G) = T := rfl
  have h2 : (S : Subgroup G) ≤ fsuV T I ⊔ T := by
    rw [hS]
    exact le_sup_right
  have h3 := S.is_maximal' hp h2
  calc fsuV T I ≤ fsuV T I ⊔ T := le_sup_left
    _ = S := h3
    _ = T := hS

theorem normalizer_fsuV_le_fsuM (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hfsu : FSU G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L := by
  have hU := lemma_1_2_7_three hfsu.qtke hfsu.simple hfsu.nonabelian h37 h38 h39 hfsu.sylow
    hfsu.maximal
  have hO2 : pCoreOf 2 (Subgroup.normalizer (fsuV T I : Set G)) ≠ ⊥ := by
    intro h
    have : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (fsuV T I : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
        (isPGroup_of_isElemAbelian_two hV)
    exact fsuV_ne_bot hfsu (le_bot_iff.mp (h ▸ this))
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hO2
  have hLT : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) :=
    sup_le ((le_fsuL0 T L).trans (le_sup_left.trans hN)) (le_sup_right.trans hN)
  have : M' = fsuM T L := hU.2 M' ⟨hM'.1, hLT.trans hM'.2⟩
  rw [← this]
  exact hM'.2

omit [Finite G] in
theorem autI_fsuM_eq_top (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    autI hV (fsuM T L) = autI hV ⊤ := by
  apply le_antisymm (autI_mono hV le_top)
  intro φ hφ
  obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hφ
  exact convI_mem_autI hV (hNM g.2) g.2

omit [Finite G] in
theorem autI_fsuL0_le (hV : IsElemAbelian 2 (fsuV T I)) :
    autI hV (fsuL0 T L) ≤ autI hV ⊤ :=
  autI_mono hV le_top

omit [Finite G] in
theorem autI_top_le_normalizer (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    autI hV ⊤ ≤
      Subgroup.normalizer (autI hV (fsuL0 T L) : Set (MulAut (IntMod (fsuV T I) hV))) := by
  intro φ hφ
  obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hφ
  rw [Subgroup.mem_normalizer_iff]
  intro ψ
  have hgM : (g : G) ∈ fsuM T L := hNM g.2
  constructor
  · intro hψ
    obtain ⟨h, hh, rfl⟩ := (mem_autI hV).1 hψ
    refine (mem_autI hV).2 ⟨g * h * g⁻¹, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp hgM h).mp hh
      exact this
    · rw [map_mul, map_mul, map_inv]
  · intro hψ
    obtain ⟨h, hh, hgh⟩ := (mem_autI hV).1 hψ
    refine (mem_autI hV).2 ⟨g⁻¹ * h * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgM) h).mp hh
      simpa using this
    · rw [map_mul, map_mul, map_inv, hgh]
      group

section WOffender

variable {V : Subgroup G}

omit [Finite G] in
theorem wParam_eq_sInf (hw : E3.wParam T V ≠ ⊤) :
    ∃ j : ℕ, E3.wParam T V = j ∧ ¬ E3.wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
  set S := {j : ℕ | ¬ E3.wClos V j T ≤ T ⊓ Subgroup.centralizer (V : Set G)} with hS
  have hSne : S.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hw
    unfold E3.wParam
    rw [← hS, h]
    simp
  refine ⟨sInf S, ?_, Nat.sInf_mem hSne⟩
  unfold E3.wParam
  rw [← hS]
  exact (ENat.natCast_sInf hSne).symm

theorem exists_isWOffenderAt (hV : IsElemAbelian 2 V) (hT : E3.HypE322 T V)
    (hw : E3.wParam T V ≠ ⊤) : ∃ g : G, E3.IsWOffenderAt T V g := by
  obtain ⟨j, hwj, hjS⟩ := wParam_eq_sInf hw
  obtain ⟨A, hA, hAc⟩ : ∃ A ∈ E3.gammaSet V j T,
      ¬ A ≤ T ⊓ Subgroup.centralizer (V : Set G) := by
    by_contra h
    push Not at h
    exact hjS (iSup₂_le h)
  obtain ⟨hAT, g, hAg, hAm⟩ := hA
  have hAnc : ¬ A ≤ Subgroup.centralizer (V : Set G) := fun h => hAc (le_inf hAT h)
  refine ⟨g, ?_, ?_⟩
  · intro h
    apply hAnc
    refine hAg.trans ?_
    exact Subgroup.le_centralizer_iff.mp (E3.commutator_eq_bot_iff_le_centralizer'.mp h)
  · rw [hwj]
    set B := conjSubgroup V g ⊓ Subgroup.normalizer (V : Set G) with hB
    have hAB : A ≤ B := le_inf hAg (hAT.trans hT.normal)
    have hk1 : E3.mQuot (conjSubgroup V g) B ≤ j := hAm ▸ E3.mQuot_mono hAB
    have hk2 : j ≤ E3.mQuot (conjSubgroup V g) B := by
      by_contra hlt
      push Not at hlt
      have hBp : IsPGroup 2 B :=
        (((isPGroup_of_isElemAbelian_two hV).map (MulAut.conj g⁻¹).toMonoidHom :
          IsPGroup 2 (conjSubgroup V g))).to_le inf_le_left
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      let S : Sylow 2 G := hT.sylow.isPGroup.toSylow (by
        have := hT.sylow.not_dvd_relIndex
        rwa [Subgroup.relIndex_top_right] at this)
      have hTN : IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) :=
        isSylowTwoOf_of_sylow S hT.normal
      obtain ⟨h, hhN, hhB⟩ := exists_conj_le_of_isSylowTwoOf hTN inf_le_right hBp
      have hmem : cjSub h B ∈ E3.gammaSet V (E3.mQuot (conjSubgroup V g) B) T := by
        refine ⟨hhB, g * h⁻¹, ?_, ?_⟩
        · have : cjSub h B = conjSubgroup B h⁻¹ := by
            ext x
            rw [mem_cjSub, E3.mem_conjSubgroup_inv_iff]
          rw [this, ← conjSubgroup_conjSubgroup]
          exact E3.conjSubgroup_mono_left _ inf_le_left
        · have : cjSub h B = conjSubgroup B h⁻¹ := by
            ext x
            rw [mem_cjSub, E3.mem_conjSubgroup_inv_iff]
          rw [this, ← conjSubgroup_conjSubgroup, E3.mQuot_conjSubgroup]
      have hW := E3.wClos_le_of_lt_wParam (T := T) (V := V)
        (i := E3.mQuot (conjSubgroup V g) B) (by rw [hwj]; exact_mod_cast hlt)
      have hle : cjSub h B ≤ Subgroup.centralizer (V : Set G) :=
        (le_iSup₂_of_le (cjSub h B) hmem le_rfl).trans (hW.trans inf_le_right)
      apply hAnc
      intro a ha
      have hb : h * a * h⁻¹ ∈ cjSub h B := by
        rw [mem_cjSub]
        simpa [mul_assoc] using hAB ha
      have h1 := hle hb
      rw [Subgroup.mem_centralizer_iff] at h1 ⊢
      intro v hv
      have hv' : h * v * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hhN v).mp hv
      have h2 := h1 _ hv'
      have h3 : h * (v * a) * h⁻¹ = h * (a * v) * h⁻¹ := by
        calc h * (v * a) * h⁻¹ = (h * v * h⁻¹) * (h * a * h⁻¹) := by group
          _ = (h * a * h⁻¹) * (h * v * h⁻¹) := h2
          _ = h * (a * v) * h⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h3)
    exact_mod_cast le_antisymm hk2 hk1

end WOffender

theorem hypE322_of_fsu (hfsu : FSU G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G)) :
    E3.HypE322 T (fsuV T I) :=
  ⟨isSylowIn_top_of_fsu hfsu, fsuV_le_T hfsu hV hN, le_sup_right.trans hN⟩

theorem not_isFFModule_of_hyp702 (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    ¬ IsFFModule (autI hV ⊤) := by
  intro hFF
  have hle := autI_top_le_normalizer (T := T) (L := L) (I := I) hV hNM
  have hFF' : IsFFModule (Subgroup.normalizer (autI hV (fsuL0 T L) :
      Set (MulAut (IntMod (fsuV T I) hV)))) := by
    obtain ⟨A, hA, hA1, hA2, hcard⟩ := hFF
    exact ⟨A, hA.trans hle, hA1, hA2, hcard⟩
  have hsq : ∀ v : IntMod (fsuV T I) hV, v ^ 2 = 1 := IntMod.sq_eq_one
  obtain ⟨A, hA⟩ := ((B1_4_5 hsq _).out 1 2).mp hFF'
  exact hyp.notFF hV.1 ⟨A, hA⟩

theorem hypE324_of_hyp702 (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    E3.HypE324 T (fsuV T I) hV :=
  Or.inr (not_isFFModule_of_hyp702 hyp hV hNM)

theorem hypBang_autI (hfsu : FSU G T L I) (hV : IsElemAbelian 2 (fsuV T I)) :
    H.HypBang (autI hV ⊤) := by
  have hO2 : pCoreOf 2 (Subgroup.normalizer (fsuV T I : Set G)) ≠ ⊥ := by
    intro h
    have : fsuV T I ≤ pCoreOf 2 (Subgroup.normalizer (fsuV T I : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
        (isPGroup_of_isElemAbelian_two hV)
    exact fsuV_ne_bot hfsu (le_bot_iff.mp (h ▸ this))
  have hsq := sqtkGroup_of_pCoreOf_ne_bot hfsu.qtke hfsu.simple hfsu.nonabelian hO2
  refine ⟨↥(Subgroup.normalizer (fsuV T I : Set G)), inferInstance, inferInstance, hsq,
    (convI hV).codRestrict (autI hV ⊤)
      (fun g => convI_mem_autI hV (Subgroup.mem_top g.1) g.2), ?_⟩
  rintro ⟨φ, hφ⟩
  obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hφ
  exact ⟨g, rfl⟩

theorem lemma_7_5_1 (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hNM : Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L) :
    E3.rParam (fsuV T I) ≤
      ((CFSG.Open.pRank 2 (autI hV ⊤) : ℕ) : ℕ∞) + E3.wParam T (fsuV T I) := by
  by_cases hw : E3.wParam T (fsuV T I) = ⊤
  · rw [hw, add_top]
    exact le_top
  · have hT := hypE322_of_fsu hyp.fsu hV hN
    obtain ⟨g, hg⟩ := exists_isWOffenderAt hV hT hw
    exact E3.e3_29 hV hT (hypE324_of_hyp702 hyp hV hNM) hg

theorem lemma_7_3_3 (hyp : Hyp7_0_2 G T L I) (hV : IsElemAbelian 2 (fsuV T I))
    (hN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G))
    (h732 : (E3.mParam (autI hV ⊤) : ℕ∞) ≤ E3.rParam (fsuV T I))
    (ham : E3.aParam (autI hV ⊤) < E3.mParam (autI hV ⊤)) :
    ((E3.mParam (autI hV ⊤) - E3.aParam (autI hV ⊤) : ℕ) : ℕ∞) ≤ E3.wParam T (fsuV T I) := by
  have hT := hypE322_of_fsu hyp.fsu hV hN
  have hs : E3.sParam hV = E3.mParam (autI hV ⊤) := by
    unfold E3.sParam
    rw [min_eq_right h732, ENat.toNat_natCast]
  have := (E3.e3_34_one hV hT (by rw [hs]; exact ham)).1
  rwa [hs] at this

end CFSG.Quasithin.H13
