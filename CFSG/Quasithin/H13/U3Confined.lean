module

public import CFSG.Quasithin.H13.U3SixAction
public import CFSG.Quasithin.H13.U3GlobalTI
public import CFSG.Quasithin.H13.A7HyperplaneConfine
public import CFSG.Quasithin.SteinbergBSSmallRankEscape
public import CFSG.Quasithin.SteinbergCBConjugateHull

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.SteinbergCB
open scoped Pointwise

@[expose] def UniqueThreeCaseModelReduction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), UniqueSetting G T M →
    fusionIsBenderGroup G ∨ UniqueSmallModel G

@[expose] def UniqueModelsExcludeU3Sections : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T E L : Subgroup G) (R : Subgroup L) [R.Normal],
    IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → quasithinIsSylowTwo T → T ≤ E →
    pCoreOf 2 E ≠ ⊥ → L ≤ E → IsPGroup 2 R → LieModel (↥L ⧸ R) .PSU 3 3 1 →
    ¬ fusionIsBenderGroup G ∧ ¬ UniqueSmallModel G

variable {G : Type} [Group G]

theorem conjugate_one' (V : Subgroup G) : CFSG.conjugate V 1 = V := by
  ext x
  rw [mem_conjugate_iff', one_mul, inv_one, mul_one]

theorem conjugate_eq_smul (V : Subgroup G) (g : G) :
    CFSG.conjugate V g = MulAut.conj g⁻¹ • V := by
  ext x
  rw [mem_conjugate_iff', mem_conj_inv_smul_iff]

theorem iSup_conjugate_eq (V T : Subgroup G) :
    (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g) =
      ⨆ g : {g : G // MulAut.conj g⁻¹ • V ≤ T}, MulAut.conj (g : G)⁻¹ • V := by
  simp only [conjugate_eq_smul]
  rw [iSup_subtype']

theorem isSylowTwoOf_top_of_quasithin {T : Subgroup G} (hT : quasithinIsSylowTwo T) :
    IsSylowTwoOf T ⊤ := by
  refine ⟨le_top, hT.1, ?_⟩
  have h : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
  rw [h]
  exact hT.2

theorem isSylowTwoOf_of_le {T H : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) :
    IsSylowTwoOf T H := by
  refine ⟨hTH, hT.1, fun h2 => hT.2 ?_⟩
  rw [← Subgroup.relIndex_mul_index hTH]
  exact Dvd.dvd.mul_right h2 _

theorem u3_confined_centralizer_overgroup
    (h1332 : Stmt13_3_2)
    (h3 : UniqueThreeCaseModelReduction) (hex : UniqueModelsExcludeU3Sections) :
    U3ConfinedCentralizerOvergroup := by
  intro G _ _ T L V z hH hU3 hF hz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTL, hVT, hVe, hV64, hVO, hVC, hLV, hTV, hirr, hnt, hTC, hVz, hz2⟩ := id hF
  have : IsElementaryAbelian 2 V := hVe
  have : IsSimpleGroup G := hH.simple
  set M := normalizer (L : Set G) with hM
  obtain ⟨hMtop, hVM, hTIM, -, hCMv⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  obtain ⟨-, -, -, hU, -⟩ := u3_original_local_maximality_and_unique_normalizer_of_1332 h1332 hH
  obtain ⟨htrans, b, -, -, -, hprof⟩ := u3_six_action_profile_producer h1332 G T L V z hH hU3 hF
  have hLM : L ≤ M := le_normalizer
  have hzV : z ∈ V := by
    have h : z ∈ V ⊓ centralizer (T : Set G) := by
      rw [hVz]
      exact mem_zpowers z
    exact h.1
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hV1 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hV64
    norm_num at hV64
  have hCv : ∀ v ∈ V, v ≠ 1 → centralizer ({v} : Set G) ≤ normalizer (V : Set G) := by
    intro v hv hv1
    obtain ⟨l, hl, hlv⟩ := htrans z hzV hz1 v hv hv1
    have hCM : centralizer ({v} : Set G) ≤ M := by
      intro c hc
      have hc' : c * v = v * c := ((mem_centralizer_iff.1 hc) v rfl).symm
      have h1 : l * c * l⁻¹ ∈ centralizer ({z} : Set G) := by
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        have hz' : z = l * v * l⁻¹ := by rw [← hlv]; group
        rw [hz']
        calc l * v * l⁻¹ * (l * c * l⁻¹) = l * (v * c) * l⁻¹ := by group
          _ = l * (c * v) * l⁻¹ := by rw [hc']
          _ = l * c * l⁻¹ * (l * v * l⁻¹) := by group
      have h2 := M.mul_mem (M.mul_mem (M.inv_mem (hLM hl)) (hz h1)) (hLM hl)
      have h3 : l⁻¹ * (l * c * l⁻¹) * l = c := by group
      rwa [h3] at h2
    intro c hc
    exact hCMv v hv hv1 ⟨hCM hc, hc⟩
  have hTIG : ∀ x : G, V ⊓ CFSG.conjugate V x = ⊥ ∨ CFSG.conjugate V x = V := by
    intro x
    by_cases hb : V ⊓ CFSG.conjugate V x = ⊥
    · exact Or.inl hb
    · right
      obtain ⟨⟨u, huV, hux⟩, hu1⟩ := ne_bot_iff_exists_ne_one.1 hb
      have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
      have hv : x * u * x⁻¹ ∈ V := mem_conjugate_iff'.1 hux
      have hv1 : x * u * x⁻¹ ≠ 1 := by
        intro h
        apply hu1'
        calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
          _ = 1 := by rw [h]; group
      obtain ⟨l, hl, hlu⟩ := htrans _ hv hv1 u huV hu1'
      have hxl : x * l⁻¹ ∈ centralizer ({x * u * x⁻¹} : Set G) := by
        rw [mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff.1 hy]
        calc x * u * x⁻¹ * (x * l⁻¹) = x * u * l⁻¹ := by group
          _ = x * (l⁻¹ * (x * u * x⁻¹) * l) * l⁻¹ := by rw [hlu]
          _ = x * l⁻¹ * (x * u * x⁻¹) := by group
      have hxM : x ∈ M := by
        have h1 := hVM (hCv _ hv hv1 hxl)
        have h2 := M.mul_mem h1 (hLM hl)
        simpa using h2
      rcases hTIM x hxM with h | h
      · exact h
      · exact absurd h hb
  obtain ⟨hcomm0, hcommT⟩ :=
    binary_six_global_TI_conjugates_with_mutual_normalizer_commute hV64 hTIG b hprof
  have hcomm : ∀ g : G, (CFSG.conjugate V g ⊓ normalizer (V : Set G) ≠ ⊥ ∨
      V ⊓ normalizer (CFSG.conjugate V g : Set G) ≠ ⊥) → ⁅V, CFSG.conjugate V g⁆ = ⊥ :=
    fun g hg => hcomm0 g hg.symm
  obtain ⟨-, hWT⟩ := hcommT T hTV
  set W := (⨆ (g : G) (_ : CFSG.conjugate V g ≤ T), CFSG.conjugate V g : Subgroup G) with hW
  have hVW : V ≤ W := by
    have h : CFSG.conjugate V 1 ≤ W := le_iSup₂_of_le (f := fun g (_ : CFSG.conjugate V g ≤ T) =>
      CFSG.conjugate V g) 1 (by rw [conjugate_one']; exact hVT) le_rfl
    rwa [conjugate_one'] at h
  have hWQ : W ≤ pCoreOf 2 (L ⊔ T) := hTC ▸ hWT
  have hQT : pCoreOf 2 (L ⊔ T) ≤ T := hTC ▸ (inf_le_left : T ⊓ centralizer (V : Set G) ≤ T)
  have hhull := linear_conjugate_hull_normalizer_containment (V := V) (T := T) hVT
  have hNQW : normalizer (pCoreOf 2 (L ⊔ T) : Set G) ≤ normalizer (W : Set G) := by
    rw [hW, iSup_conjugate_eq]
    exact (hhull _ (by rw [← iSup_conjugate_eq, ← hW]; exact hWQ) hQT).1
  have hNTW : normalizer (T : Set G) ≤ normalizer (W : Set G) := by
    rw [hW, iSup_conjugate_eq]
    exact (hhull _ (by rw [← iSup_conjugate_eq, ← hW]; exact hWT.trans inf_le_left) le_rfl).1
  have hW1 : W ≠ ⊥ := fun h => hV1 (le_bot_iff.1 (h ▸ hVW))
  have hW2 : IsPGroup 2 W := by
    have hT2 : IsPGroup 2 T := hH.sylow.1
    exact hT2.to_le (hWT.trans inf_le_left)
  have hLTW : L ⊔ T ≤ normalizer (W : Set G) :=
    (LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)).trans hNQW
  have hNWM : normalizer (W : Set G) ≤ M :=
    normalizer_le_of_uniqueMaxTwoLocal hU.2.2 hW1 hW2 hLTW
  have hNTM : normalizer (T : Set G) ≤ M := hNTW.trans hNWM
  have hzZ : z ∈ quasithinOmegaOneCenter T := by
    refine Subgroup.subset_closure ⟨⟨hVT hzV, ?_⟩, ?_⟩
    · have h : z ∈ V ⊓ centralizer (T : Set G) := by
        rw [hVz]
        exact mem_zpowers z
      exact h.2
    · rw [← hz2, pow_orderOf_eq_one]
  have hZM : centralizer (quasithinOmegaOneCenter T : Set G) ≤ M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 hzZ)).trans hz
  have hCVM : centralizer (V : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer (V : Set G)).trans hVM
  have hhyp : ∀ (g : G) (B : Subgroup G), B ≤ CFSG.conjugate V g ⊓ T →
      B.relIndex (CFSG.conjugate V g) ≤ 2 → ⁅V, CFSG.conjugate V g⁆ = ⊥ := by
    intro g B hB hidx
    refine hcomm g (Or.inl ?_)
    intro hbot
    have hB1 : B = ⊥ := le_bot_iff.1 (hbot ▸ le_inf (hB.trans inf_le_left)
      ((hB.trans inf_le_right).trans hTV))
    have h1 := card_mul_relIndex (hB.trans inf_le_left)
    rw [hB1, card_bot, one_mul, card_conjugate] at h1
    rw [hB1] at hidx
    rw [← h1] at hV64
    omega
  let TS : Sylow 2 G := hH.sylow.1.toSylow hH.sylow.2
  have hsolv : ∀ A : Subgroup G, T ≤ A → Group.IsSolvable A → A ≤ M :=
    A7.A7_hyperplane_conjugates_confine_solvable_Sylow_overgroups TS hV1 hVT hVe hNWM hCVM hhyp
  have hMmax : quasithinIsMaxTwoLocal M := hU.1
  have hTM : T ≤ M := le_sup_right.trans hU.2.1
  have hesc : ∃ A : Subgroup G, T ≤ A ∧ pCoreOf 2 A ≠ ⊥ ∧ ¬ A ≤ M := by
    by_contra hno
    push Not at hno
    have huniq : ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → T ≤ M' → M' = M := by
      intro M' hM' hTM'
      have hO : pCoreOf 2 M' ≠ ⊥ := by
        obtain ⟨P, hP1, hP2, hPM⟩ := hM'.1
        intro hb
        apply hP1
        rw [eq_bot_iff, ← hb, hPM]
        exact LieType.BorelTits.le_pCoreOf_normalizer 2 P hP2
      exact (hM'.2 M hMmax.1 (hno M' hTM' hO)).symm
    have hset : UniqueSetting G T M :=
      { simple := hH.simple
        nonabelian := hH.nonabelian
        qtke := qtkeCore_of_cat hH.nonabelian hH.qtke
        sylow := isSylowTwoOf_top_of_quasithin hH.sylow
        maxLocal := hMmax
        le := hTM
        unique := huniq }
    have hO2E : pCoreOf 2 (L ⊔ T) ≠ ⊥ := hH.faithful.1.2.2.2
    have hR2 : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
    obtain ⟨hnb, hns⟩ := hex G T (L ⊔ T) L (CFSG.pCore 2 ↥L) hH.simple hH.nonabelian hH.sylow
      le_sup_right hO2E le_sup_left hR2 hU3
    rcases h3 G T M hset with h | h
    · exact hnb h
    · exact hns h
  classical
  have hexn : ∃ n, ∃ A : Subgroup G, (T ≤ A ∧ pCoreOf 2 A ≠ ⊥ ∧ ¬ A ≤ M) ∧ Nat.card A = n :=
    ⟨_, hesc.choose, hesc.choose_spec, rfl⟩
  obtain ⟨H₀, hH₀, hH₀n⟩ := Nat.find_spec hexn
  have hleast₀ : ∀ A : Subgroup G, T ≤ A → pCoreOf 2 A ≠ ⊥ → ¬ A ≤ M →
      Nat.card H₀ ≤ Nat.card A := fun A h1 h2 h3 => by
    rw [hH₀n]
    exact Nat.find_min' hexn ⟨A, ⟨h1, h2, h3⟩, rfl⟩
  refine ⟨hCv, hVM, hTIG, hcomm, ⟨hV1, hVW, hWQ, hNWM⟩, hNTM, hZM, hsolv, ⟨H₀, hH₀, hleast₀⟩, ?_⟩
  intro H hTH hR hHM hleast
  have hT2 : IsPGroup 2 T := hH.sylow.1
  have hHtop : H < ⊤ := lt_top_iff_ne_top.2 (ne_top_of_pCoreOf_ne_bot_of_simple hH.nonabelian hR)
  have hsqtk : SectionRank.IsSQTKCat H := (qtkeCore_of_cat hH.nonabelian hH.qtke).1 H hR
  have hchar : CharTwo H :=
    charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hH.qtke.2.1
      (isSylowTwoOf_top_of_quasithin hH.sylow) hTH hR
  have hTn : ¬ (T.subgroupOf H).Normal := by
    intro hn
    exact hHM (((normal_subgroupOf_iff_le_normalizer hTH).1 hn).trans hNTM)
  have huniqH : IsUniqueMaxOvergroup T M H := by
    refine ⟨inf_lt_left.2 hHM, le_inf hTH hTM, fun A hTA hAH => le_inf hAH.le ?_⟩
    by_contra hAM
    have hRA : pCoreOf 2 H ≤ pCoreOf 2 A := by
      have hRT : pCoreOf 2 H ≤ T :=
        QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hH.sylow hTH)
      refine LieType.BorelTits.le_pCoreOf 2 (hRT.trans hTA) ?_
        (LieType.BorelTits.pCoreOf_isPGroup 2 H)
      exact (normal_subgroupOf_iff_le_normalizer (hRT.trans hTA)).2
        (hAH.le.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    have hA2 : pCoreOf 2 A ≠ ⊥ := fun h => hR (le_bot_iff.1 (h ▸ hRA))
    have h1 := hleast A hTA hA2 hAM
    have h2 : Nat.card A < Nat.card H := by
      by_contra hge
      push Not at hge
      exact hAH.ne (Subgroup.eq_of_le_of_card_ge hAH.le hge)
    omega
  have hns : ¬ Group.IsSolvable H := fun hs => hHM (hsolv H hTH hs)
  refine ⟨hHtop, hns, hchar, hsqtk, hTn, huniqH, ?_⟩
  by_contra hlt
  push Not at hlt
  have hV2 : Nat.card V = 2 ^ 6 := by rw [hV64]; norm_num
  exact SteinbergBS.ti_conjugate_commutation_excludes_small_rank_minimal_sylow_escape TS hV2 hTV
    hNWM hCVM (fun g hg => hcomm g (Or.inl hg))
    ⟨H, hTH, hHM, ⟨le_inf hTH hTM, inf_lt_left.2 hHM, huniqH.2.2⟩, hlt⟩

end CFSG.Quasithin.H13.U3
