module

public import CFSG.Quasithin.Background.B6Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSL
import CFSG.Quasithin.Background.B6Basic
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Quasithin.Background.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open Matrix (SpecialLinearGroup)

section General

variable {G : Type} [Group G]

theorem pCoreOf_top_eq_pCore_two : pCoreOf 2 (⊤ : Subgroup G) = CFSG.pCore 2 G := by
  unfold pCoreOf
  rw [← CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (Subgroup.topEquiv (G := G)).symm, Subgroup.map_map]
  have : (Subgroup.subtype ⊤).comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom = MonoidHom.id G := by
    ext x
    rfl
  rw [this, Subgroup.map_id]

theorem normal_omegaOneCenterOf (X : Subgroup G) [X.Normal] : (omegaOneCenterOf X).Normal := by
  refine ⟨fun n hn g => ?_⟩
  change n ∈ Subgroup.closure {x | x ∈ centerOf X ∧ x ^ 2 = 1} at hn
  change g * n * g⁻¹ ∈ Subgroup.closure {x | x ∈ centerOf X ∧ x ^ 2 = 1}
  have hg : g ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  induction hn using Subgroup.closure_induction with
  | mem x hx =>
    refine Subgroup.subset_closure ⟨⟨‹X.Normal›.conj_mem x hx.1.1 g,
      B6.conj_mem_centralizer_of_mem_normalizer hg hx.1.2⟩, ?_⟩
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]
  | one => simpa using Subgroup.one_mem _
  | mul x y _ _ ihx ihy => simpa [mul_assoc] using Subgroup.mul_mem _ ihx ihy
  | inv x _ ih => simpa [mul_assoc] using Subgroup.inv_mem _ ih

theorem normal_VZ_top (T : Subgroup G) : (VZ T ⊤).Normal :=
  Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_conjClosure _ ⊤))

theorem omegaOneCenter_le_centralizer (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1.2

theorem omegaOneCenter_le_omegaOneCenterOf_thompsonJ [Finite G] (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro z ⟨⟨hzT, hzC⟩, hz2⟩
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers z, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_right (Subgroup.mem_centralizer_iff.mp hzC a (hA.1 ha)) n).eq
  have hB : IsElemAbelian 2 (A ⊔ Subgroup.zpowers z) :=
    IsElemAbelian.sup_of_commute hA.2.1 (isElemAbelian_zpowers hz2) hcomm
  have hBT : A ⊔ Subgroup.zpowers z ≤ T := sup_le hA.1 (Subgroup.zpowers_le.mpr hzT)
  have hAB : A = A ⊔ Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (hA.2.2 _ hBT hB)
  have hzJ : z ∈ thompsonJ T :=
    B6.le_thompsonJ hA (hAB ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  exact Subgroup.subset_closure
    ⟨⟨hzJ, Subgroup.centralizer_le (B6.thompsonJ_le T) hzC⟩, hz2⟩

end General

structure SeedSetting {G : Type} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2]
    (T : Subgroup G) (π : G →* SpecialLinearGroup (Fin 2) k) : Prop where
  surj : Function.Surjective π
  sylow : IsSylowTwoOf T ⊤
  charTwo : CharTwo (⊤ : Subgroup G)
  supp : ∀ Y : Subgroup G, Y ≠ ⊤ → Y ⊔ π.ker = ⊤ → ¬ CFSG.pCore 2 G ≤ Y

namespace SeedSetting

variable {G : Type} [Group G] [Finite G] {k : Type} [Field k] [Finite k] [CharP k 2]
  {T : Subgroup G} {π : G →* SpecialLinearGroup (Fin 2) k}

theorem exists_sylow (h : SeedSetting T π) : ∃ P : Sylow 2 G, (P : Subgroup G) = T := by
  refine ⟨h.sylow.2.1.toSylow ?_, rfl⟩
  rw [← Subgroup.relIndex_top_right]
  exact h.sylow.2.2

theorem exists_sylow_map (h : SeedSetting T π) :
    ∃ P : Sylow 2 (SpecialLinearGroup (Fin 2) k),
      (P : Subgroup (SpecialLinearGroup (Fin 2) k)) = T.map π := by
  obtain ⟨P, hP⟩ := h.exists_sylow
  exact ⟨P.mapSurjective h.surj, by rw [Sylow.coe_mapSurjective, hP]⟩

theorem eq_top_of_sup_ker (h : SeedSetting T π) {Y : Subgroup G} (hO : CFSG.pCore 2 G ≤ Y)
    (hY : Y ⊔ π.ker = ⊤) : Y = ⊤ := by
  by_contra hne
  exact h.supp Y hne hY hO

theorem ker_le_of_maximal (h : SeedSetting T π) {N : Subgroup G} (hne : N ≠ ⊤)
    (hmax : ∀ L : Subgroup G, N < L → L = ⊤) (hO : CFSG.pCore 2 G ≤ N) : π.ker ≤ N := by
  by_contra hK
  have hlt : N < N ⊔ π.ker := lt_of_le_of_ne le_sup_left fun he => hK (by rw [he]; exact le_sup_right)
  exact hne (h.eq_top_of_sup_ker hO (hmax _ hlt))

theorem isSylowTwoOf_inf_ker (h : SeedSetting T π) : IsSylowTwoOf (T ⊓ π.ker) π.ker :=
  B6.isSylowTwoOf_inf_normal h.sylow le_top (Subgroup.normalizer_eq_top (H := π.ker)).ge

theorem map_ne_bot (h : SeedSetting T π) : T.map π ≠ ⊥ := by
  obtain ⟨P, hP⟩ := h.exists_sylow_map
  rw [← hP]
  exact sl2_sylow_ne_bot (MulEquiv.refl _) P

theorem isPGroup_map (h : SeedSetting T π) : IsPGroup 2 (T.map π) :=
  h.sylow.2.1.map π

theorem pCore_le (h : SeedSetting T π) : CFSG.pCore 2 G ≤ T := by
  obtain ⟨P, hP⟩ := h.exists_sylow
  rw [← hP]
  exact CFSG.pCore_isPGroup.le_sylow_of_normal P

theorem pCore_le_ker (h : SeedSetting T π) : CFSG.pCore 2 G ≤ π.ker := by
  have hn : ((CFSG.pCore 2 G).map π).Normal := Subgroup.Normal.map inferInstance π h.surj
  exact (Subgroup.map_eq_bot_iff _).mp
    (sl2_normal_isPGroup_eq_bot (MulEquiv.refl _) _ (CFSG.pCore_isPGroup.map π))

theorem not_le_ker (h : SeedSetting T π) : ¬ T ≤ π.ker :=
  fun hle => h.map_ne_bot ((Subgroup.map_eq_bot_iff _).mpr hle)

theorem ker_inf_eq (h : SeedSetting T π) : π.ker ⊓ T = CFSG.pCore 2 G := by
  refine le_antisymm ?_ (le_inf h.pCore_le_ker h.pCore_le)
  have hSyl : IsSylowTwoOf (T ⊓ π.ker) π.ker := h.isSylowTwoOf_inf_ker
  have hfr := B6.frattini_two (H := ⊤) (N := π.ker) (S := T ⊓ π.ker) le_top
    (Subgroup.normalizer_eq_top (H := π.ker)).ge hSyl
  have hY : Subgroup.normalizer ((T ⊓ π.ker : Subgroup G) : Set G) ⊔ π.ker = ⊤ := by
    rw [top_inf_eq, sup_comm] at hfr
    exact top_le_iff.mp hfr
  have hOS : CFSG.pCore 2 G ≤ T ⊓ π.ker := le_inf h.pCore_le h.pCore_le_ker
  have htop := h.eq_top_of_sup_ker (hOS.trans Subgroup.le_normalizer) hY
  have hnorm : (T ⊓ π.ker).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rw [inf_comm]
  exact CFSG.LieType.BorelTits.le_pCore 2 hnorm hSyl.2.1

theorem sup_eq_top (h : SeedSetting T π) {C : Subgroup G} [C.Normal] (hO : CFSG.pCore 2 G ≤ C)
    (hC : ¬ C ≤ π.ker) : C ⊔ T = ⊤ := by
  obtain ⟨P, hP⟩ := h.exists_sylow_map
  have hne : C.map π ≠ ⊥ := fun h0 => hC ((Subgroup.map_eq_bot_iff _).mp h0)
  have hn : (C.map π).Normal := Subgroup.Normal.map inferInstance π h.surj
  have h1 := sl2_normal_sup_sylow_eq_top (MulEquiv.refl _) P (C.map π) hne
  rw [hP, ← Subgroup.map_sup] at h1
  have h2 : (C ⊔ T) ⊔ π.ker = ⊤ := by
    have := Subgroup.comap_map_eq π (C ⊔ T)
    rwa [h1, Subgroup.comap_top, eq_comm] at this
  exact h.eq_top_of_sup_ker (hO.trans le_sup_left) h2

theorem mem_of_pow_mem (h : SeedSetting T π) {C : Subgroup G} [C.Normal] (hO : CFSG.pCore 2 G ≤ C)
    (hCK : C ≤ π.ker) {x : G} (hx : x ∈ π.ker) {a : ℕ} (hxa : x ^ 2 ^ a ∈ C) : x ∈ C := by
  have hS := h.isSylowTwoOf_inf_ker
  have hTK : T ⊓ π.ker ≤ C := by
    rw [inf_comm, h.ker_inf_eq]
    exact hO
  have hodd : ¬ 2 ∣ C.relIndex π.ker := fun hd =>
    hS.2.2 (hd.trans (Subgroup.relIndex_dvd_of_le_left π.ker hTK))
  set q : π.ker ⧸ C.subgroupOf π.ker := QuotientGroup.mk ⟨x, hx⟩ with hq
  have hq1 : q ^ 2 ^ a = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hxa
  have hd1 : orderOf q ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one hq1
  have hd2 : orderOf q ∣ C.relIndex π.ker := by
    have := orderOf_dvd_natCard q
    rwa [← Subgroup.index_eq_card] at this
  have hcop : Nat.Coprime (2 ^ a) (C.relIndex π.ker) :=
    Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  have hq2 : q = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  rw [hq, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq2
  exact hq2

theorem ker_map_le_frattini (h : SeedSetting T π) :
    π.ker.map (QuotientGroup.mk' (CFSG.pCore 2 G)) ≤ frattini (G ⧸ CFSG.pCore 2 G) := by
  unfold frattini Order.radical
  refine le_iInf₂ fun M hM => ?_
  have hM' : IsCoatom (M.comap (QuotientGroup.mk' (CFSG.pCore 2 G))) :=
    Subgroup.isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective _) hM
  have hOM : CFSG.pCore 2 G ≤ M.comap (QuotientGroup.mk' (CFSG.pCore 2 G)) := fun x hx => by
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact M.one_mem
  exact Subgroup.map_le_iff_le_comap.mpr (h.ker_le_of_maximal hM'.1 hM'.2 hOM)

theorem exists_minParabolic (h : SeedSetting T π) : ∃ M : Subgroup G, MinParabolic (⊤ : Subgroup G) T M := by
  obtain ⟨P, hP⟩ := h.exists_sylow_map
  set NT : Subgroup (SpecialLinearGroup (Fin 2) k) :=
    Subgroup.normalizer ((T.map π : Subgroup (SpecialLinearGroup (Fin 2) k)) : Set _) with hNT
  have hF2 : ∀ Y : Subgroup (SpecialLinearGroup (Fin 2) k), T.map π ≤ Y → Y ≠ ⊤ → Y ≤ NT := by
    intro Y hY hne
    have := sl2_le_normalizer_of_sylow_le (MulEquiv.refl _) P (Y := Y) (hP ▸ hY) hne
    rwa [hP] at this
  have hNTtop : NT ≠ ⊤ := by
    intro htop
    haveI : (T.map π).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    exact h.map_ne_bot (sl2_normal_isPGroup_eq_bot (MulEquiv.refl _) _ h.isPGroup_map)
  have hMtop : NT.comap π ≠ ⊤ := fun h0 =>
    hNTtop (Subgroup.comap_injective h.surj (h0.trans (Subgroup.comap_top π).symm))
  have hTM : T ≤ NT.comap π := fun t ht => Subgroup.le_normalizer (Subgroup.mem_map_of_mem π ht)
  have hA : ∀ N : Subgroup G, T ≤ N → π.ker ≤ N → N ≠ ⊤ → N ≤ NT.comap π := by
    intro N hTN hKN hNtop g hg
    have hmap : N.map π ≠ ⊤ := by
      intro h0
      apply hNtop
      have := Subgroup.comap_map_eq π N
      rwa [h0, Subgroup.comap_top, sup_eq_left.mpr hKN, eq_comm] at this
    exact hF2 (N.map π) (Subgroup.map_mono hTN) hmap (Subgroup.mem_map_of_mem π hg)
  have hB : ∀ N : Subgroup G, IsMaxSubgroupIn ⊤ N → T ≤ N → N ≤ NT.comap π := by
    intro N hN hTN
    have hK : π.ker ≤ N :=
      h.ker_le_of_maximal hN.1.ne (fun L hL => hN.2 L hL le_top) (h.pCore_le.trans hTN)
    exact hA N hTN hK hN.1.ne
  refine ⟨NT.comap π, h.sylow, ?_, ?_⟩
  · intro hle
    have hnorm : T.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hle)
    have : (T.map π).Normal := Subgroup.Normal.map hnorm π h.surj
    exact h.map_ne_bot (sl2_normal_isPGroup_eq_bot (MulEquiv.refl _) _ h.isPGroup_map)
  · ext N
    refine ⟨fun hN => ?_, fun hN => ?_⟩
    · have hle := hB N hN.1 hN.2
      rcases hle.lt_or_eq with hlt | heq
      · exact absurd (hN.1.2 _ hlt le_top) hMtop
      · exact heq
    · have hN : N = NT.comap π := hN
      subst hN
      refine ⟨⟨lt_top_iff_ne_top.mpr hMtop, fun L hML _ => ?_⟩, hTM⟩
      by_contra hLtop
      obtain ⟨N', hN', hLN'⟩ := exists_isMaxSubgroupIn (lt_top_iff_ne_top.mpr hLtop)
      exact absurd (hML.trans_le (hLN'.trans (hB N' hN' (hTM.trans (hML.le.trans hLN'))))) (lt_irrefl _)

theorem VZ_le_center_pCore (h : SeedSetting T π) :
    VZ T ⊤ ≤ centerOf (pCoreOf 2 (⊤ : Subgroup G)) :=
  (conjClosure_le_centerOf_pCoreOf_of_sylowIn le_top h.sylow.2.1 h.sylow.2.2 h.charTwo le_rfl).1

theorem isElemAbelian_VZ (h : SeedSetting T π) : IsElemAbelian 2 (VZ T ⊤) :=
  (conjClosure_le_centerOf_pCoreOf_of_sylowIn le_top h.sylow.2.1 h.sylow.2.2 h.charTwo le_rfl).2

theorem isTwoReducedIn_VZ (h : SeedSetting T π) : IsTwoReducedIn (⊤ : Subgroup G) (VZ T ⊤) :=
  isTwoReducedIn_conjClosure_of_sylowIn le_top h.sylow.2.1 h.sylow.2.2 h.charTwo le_rfl

theorem pCore_le_centralizer_VZ (h : SeedSetting T π) :
    CFSG.pCore 2 G ≤ Subgroup.centralizer (VZ T ⊤ : Set G) := by
  rw [Subgroup.le_centralizer_iff]
  intro v hv
  have h1 := (h.VZ_le_center_pCore hv).2
  rwa [pCoreOf_top_eq_pCore_two] at h1

theorem centralizer_VZ_le_ker (h : SeedSetting T π)
    (hnc : ⁅(⊤ : Subgroup G), quasithinOmegaOneCenter T⁆ ≠ ⊥) :
    Subgroup.centralizer (VZ T ⊤ : Set G) ≤ π.ker := by
  by_contra hC
  haveI := normal_VZ_top (G := G) T
  have hsup := h.sup_eq_top h.pCore_le_centralizer_VZ hC
  apply hnc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hsup.symm.trans_le (sup_le (Subgroup.centralizer_le (le_conjClosure _ _))
    (Subgroup.le_centralizer_iff.mpr (omegaOneCenter_le_centralizer T)))

theorem not_thompsonJ_le_pCore (h : SeedSetting T π)
    (hnc : ⁅(⊤ : Subgroup G), quasithinOmegaOneCenter T⁆ ≠ ⊥)
    (hJ : omegaOneCenterOf (thompsonJ T) ≤ Subgroup.centralizer (T : Set G)) :
    ¬ thompsonJ T ≤ CFSG.pCore 2 G := by
  intro hJO
  have h1 : thompsonJ (⊤ : Subgroup G) ≤ CFSG.pCore 2 G :=
    B6.thompsonJ_le_of_sylow_of_le h.sylow hJO (Subgroup.normalizer_eq_top (H := CFSG.pCore 2 G)).ge
  have h2 : thompsonJ T = thompsonJ (⊤ : Subgroup G) :=
    B6.thompsonJ_eq_of_le (h1.trans h.pCore_le) le_top
  haveI hJn : (thompsonJ T).Normal := by
    rw [h2]
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (B6.le_normalizer_thompsonJ ⊤))
  haveI hEn : (omegaOneCenterOf (thompsonJ T)).Normal := normal_omegaOneCenterOf _
  have hTC : T ≤ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
    Subgroup.le_centralizer_iff.mp hJ
  have hsup := h.sup_eq_top (C := Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G))
    (h.pCore_le.trans hTC) (fun hle => h.not_le_ker (hTC.trans hle))
  rw [sup_eq_left.mpr hTC] at hsup
  apply hnc
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact hsup.symm.trans_le (Subgroup.centralizer_le (omegaOneCenter_le_omegaOneCenterOf_thompsonJ T))

theorem not_thompsonJ_le_centralizer_VZ (h : SeedSetting T π)
    (hnc : ⁅(⊤ : Subgroup G), quasithinOmegaOneCenter T⁆ ≠ ⊥)
    (hJ : omegaOneCenterOf (thompsonJ T) ≤ Subgroup.centralizer (T : Set G)) :
    ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T ⊤ : Set G) := by
  intro hle
  apply h.not_thompsonJ_le_pCore hnc hJ
  have h1 : thompsonJ T ≤ π.ker ⊓ T :=
    le_inf (hle.trans (h.centralizer_VZ_le_ker hnc)) (B6.thompsonJ_le T)
  rwa [h.ker_inf_eq] at h1

theorem thompsonJ_sup_centralizer_sup_eq_top (h : SeedSetting T π)
    (hnc : ⁅(⊤ : Subgroup G), quasithinOmegaOneCenter T⁆ ≠ ⊥)
    (hJ : omegaOneCenterOf (thompsonJ T) ≤ Subgroup.centralizer (T : Set G)) :
    thompsonJ (⊤ : Subgroup G) ⊔ Subgroup.centralizer (VZ T ⊤ : Set G) ⊔ T = ⊤ := by
  haveI : (VZ T ⊤).Normal := normal_VZ_top T
  haveI : (thompsonJ (⊤ : Subgroup G)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (B6.le_normalizer_thompsonJ ⊤))
  refine h.sup_eq_top (C := thompsonJ (⊤ : Subgroup G) ⊔ Subgroup.centralizer (VZ T ⊤ : Set G))
    (h.pCore_le_centralizer_VZ.trans le_sup_right) fun hle => ?_
  apply h.not_thompsonJ_le_pCore hnc hJ
  have h1 : thompsonJ T ≤ π.ker ⊓ T :=
    le_inf ((B6.thompsonJ_le_of_sylow h.sylow).trans (le_sup_left.trans hle)) (B6.thompsonJ_le T)
  rwa [h.ker_inf_eq] at h1

end SeedSetting

end CFSG.LocalAnalysis.UniquenessCase.UC22
