module

public import CFSG.Quasithin.H13.U3S1349L

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem s134_solvable_Gz_data (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h56 : AsB56) (h1347 : Stmt13_4_7L2) (h1348 : Stmt13_4_8)
    {T L V : Subgroup G} (S : A6.Setting134 G T L V) {z : G}
    (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
    (hCz : ¬ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (hsol : Group.IsSolvable ↥(centralizer ({z} : Set G))) :
    ∃ H₁ : Subgroup G,
      IsHStar T (normalizer (L : Set G)) H₁ ∧ H₁ ≤ centralizer ({z} : Set G) ∧
      (∀ X, IsHStar T (normalizer (L : Set G)) X → X ≤ centralizer ({z} : Set G) → X = H₁) ∧
      quasithinO2QuotientIso H₁ (Perm (Fin 3)) ∧
      (∀ X : Subgroup G, T ≤ X → X ≤ centralizer ({z} : Set G) →
        X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = H₁ ∨ X = centralizer ({z} : Set G)) ∧
      ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ H₁ ∧ ¬ H₁ ≤ L₁Of L (fsuV1 T V) ⊔ T ∧
      cZ T H₁ = zpowers z ∧
      InH T (H₁ ⊔ (l2Of S ⊔ T)) ∧ ¬ H₁ ⊔ (l2Of S ⊔ T) ≤ normalizer (L : Set G) ∧
      Concl1347ii T H₁ (l2Of S ⊔ T) ∧
      ∀ X : Subgroup G, InH (H₁ ⊔ (l2Of S ⊔ T)) X → X = H₁ ⊔ (l2Of S ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalizer (L : Set G) with hM
  set Gz := centralizer ({z} : Set G) with hGzdef
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set Z := quasithinOmegaOneCenter T with hZdef
  have hTsylG : quasithinIsSylowTwo T := S.h13.sylow
  have hT2 : IsPGroup 2 T := hTsylG.1
  have hTM : T ≤ M := S.T_le_NL
  have hTGz : T ≤ Gz := s134_T_le_Gz hz
  have hL1TGz : L₁ ⊔ T ≤ Gz := s134_L1T_le_Gz S hz
  have hL1L : L₁ ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1TM : L₁ ⊔ T ≤ M := sup_le (hL1L.trans le_normalizer) hTM
  have hL2TM : l2Of S ⊔ T ≤ M := sup_le ((s134_L2_le_L S).trans le_normalizer) hTM
  obtain ⟨h1T, h2T, h12, h21⟩ := s134_parabolics S
  have hTZ : T ≤ centralizer (Z : Set G) := fun t ht => mem_centralizer_iff.2 fun x hx =>
    (mem_centralizer_iff.1 (mem_quasithinOmegaOneCenter_iff.1 hx).2.1 t ht).symm
  have hCzV : centralizer ({S.zV} : Set G) = M := S.centralizer_zV h1222
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem _)
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 hz.2).2.2
  have hO2Gz : pCoreOf 2 Gz ≠ ⊥ := by
    intro hbot
    have hzmem : z ∈ Gz := mem_centralizer_singleton_iff.mpr rfl
    have hle : zpowers z ≤ pCoreOf 2 Gz := by
      refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
        (zpowers_le.mpr hzmem) ?_ ?_
      · refine (normal_subgroupOf_iff_le_normalizer (zpowers_le.mpr hzmem)).2 fun y hy => ?_
        refine Subgroup.centralizer_le_normalizer _ ?_
        rw [mem_centralizer_iff]
        intro w hw
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
        exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp hy).symm k).symm).eq.symm
      · exact IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, pow_one]
          exact orderOf_eq_prime hz2 hz1)
    rw [hbot, le_bot_iff, zpowers_eq_bot] at hle
    exact hz1 hle
  have hInHGz : InH T Gz := ⟨hTGz, hO2Gz⟩
  have hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ M := ⟨Gz, hInHGz, hCz⟩
  have hsylGz : IsSylowTwoOf T Gz := A5.isSylowTwoOf_of_le hTsylG hTGz
  have hred : IsTwoReducedIn Gz (VZ T Gz) :=
    C1GN.isTwoReducedIn_VZ (s134_charTwo_of_inH S hInHGz) hsylGz
  have hZVH : V ⊓ centralizer (L : Set G) ≤ VZ T Gz := by
    intro x hx
    rcases S.mem_ZV_iff.1 hx with rfl | rfl
    · exact one_mem _
    · exact le_conjClosure _ _ (s134_zV_mem_Z S)
  obtain ⟨hA6, hIq, hW, hGzeq, hGzq, hstar, hstaru⟩ :=
    h1348 G T L V S z hz hzL hCz Gz (VZ T Gz) ⟨⟨hL1TGz, hO2Gz⟩, le_rfl, hCz⟩ hsol hred hZVH
  set I := conjClosure (thompsonJ (r1Of T L V)) Gz with hIdef
  have hGzSL : quasithinO2QuotientIso Gz A6.SL22.K := by
    obtain ⟨φ, hφ, hker⟩ := hGzq
    let e : A6.SL22.K ≃* Perm (Fin 3) × Perm (Fin 3) :=
      MulEquiv.prodCongr CFSG.QuasithinUnique.Setup.Lift.sl2F2EquivPerm3
        CFSG.QuasithinUnique.Setup.Lift.sl2F2EquivPerm3
    refine ⟨e.symm.toMonoidHom.comp φ, e.symm.surjective.comp hφ, ?_⟩
    rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h => by simpa using congrArg e h, fun h => by rw [h, map_one]⟩
  obtain ⟨P₀, X₁, X₂, hP, hP', hc, hX₁, hX₂, hX₁₂, hX₂₁⟩ := A6.modelData_SL22.exists_data
  obtain ⟨A₁, A₂, -, -, -, -, hA₁₂, hA₂₁, -, -, hclsGz⟩ :=
    A6.overgroups_transport hGzSL hsylGz hP hP' hc hX₁ hX₂ hX₁₂ hX₂₁
  have hMGz : M ⊓ Gz = L₁ ⊔ T :=
    (eq_of_overgroups hclsGz hA₁₂ hA₂₁ le_sup_right (le_inf hL1TM hL1TGz) inf_le_right h1T
      fun h => hCz (h.symm.le.trans inf_le_left)).symm
  have hMLT : M = L ⊔ T := by
    refine le_antisymm ((s134_normalizer_le_sup h1222 S hz hzL).trans (sup_le le_sup_left ?_))
      (sup_le le_normalizer hTM)
    rw [hMGz]
    exact sup_le (hL1L.trans le_sup_left) le_sup_right
  have hp : IsPGroup 2 ↥(M ⊓ centralizer (V : Set G)) := s134_isPGroup_CMV S hA6 hMLT
  have hCT : M ⊓ centralizer (V : Set G) ≤ T := s134_CMV_le_T S hp h1222
  have hMsup : (L₁ ⊔ T) ⊔ (l2Of S ⊔ T) = M := s134_sup_parabolics h1222 S hp
  have hclsM : ∀ Y : Subgroup G, T ≤ Y → Y ≤ M →
      Y = T ∨ Y = L₁ ⊔ T ∨ Y = l2Of S ⊔ T ∨ Y = M := s134_overgroups_M h1222 S hp
  have hIGz : I ≤ Gz := (le_sup_right.trans le_sup_left).trans hGzeq.symm.le
  have hGzI : Gz ≤ normalizer (I : Set G) := le_normalizer_conjClosure _ _
  have hTI : T ≤ normalizer (I : Set G) := hTGz.trans hGzI
  have hsylIT : IsSylowTwoOf T (I ⊔ T) := A5.isSylowTwoOf_of_le hTsylG le_sup_right
  obtain ⟨hITq, -⟩ := quot_S3_sup hTI hsylIT hIq
  have hITM : ¬ I ⊔ T ≤ M := hstar.2.1
  have hITGz : I ⊔ T ≤ Gz := sup_le hIGz hTGz
  have hITT : I ⊔ T ≠ T := fun h => hITM (h.le.trans hTM)
  have hIM : ¬ I ≤ M := fun h => hITM (sup_le h hTM)
  have hZcard := s134_card_Z h1332 hC58 h317 h56 S hHM
  have hindex₁ : Nat.card ↥Z = 2 * Nat.card ↥(cZ T (I ⊔ T)) := by
    rw [cZ_sup_eq T I]
    have hVab : ∀ a ∈ VZ T Gz, ∀ b ∈ VZ T Gz, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hred.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hV2 : ∀ v ∈ VZ T Gz, v * v = 1 := fun v hv => by
      rw [← pow_two]
      exact hred.2.2.1.2 v hv
    have hOI : pCoreOf 2 I ≤ centralizer (VZ T Gz : Set G) := by
      refine (pCoreOf_le_pCoreOf hIGz hGzI).trans ?_
      refine hred.2.2.2 _ (LieType.BorelTits.pCoreOf_le 2 Gz)
        (LieType.BorelTits.le_normalizer_pCoreOf 2 Gz) fun d hd => ?_
      obtain ⟨k, hk⟩ := LieType.BorelTits.pCoreOf_isPGroup 2 Gz ⟨d, hd⟩
      refine ⟨k, ?_⟩
      have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      rw [this]
      exact one_mem _
    have hsylI : IsSylowTwoOf (I ⊓ T) I := by
      have := A4.isSylowTwoOf_inf_normal hsylIT le_sup_left (sup_le le_normalizer hTI)
      rwa [inf_comm] at this
    have hle := card_le_two_mul_inf_centralizer hVab hV2 (le_conjClosure _ _)
      (hIGz.trans hred.2.1) hIq hOI hsylI hTZ hW
    have hne : Z ⊓ centralizer (I : Set G) ≠ Z := by
      intro h
      apply hIM
      intro i hi
      have hmem : S.zV ∈ Z ⊓ centralizer (I : Set G) := by
        rw [h]
        exact s134_zV_mem_Z S
      rw [← hCzV, mem_centralizer_singleton_iff]
      exact mem_centralizer_iff.1 (mem_inf.1 hmem).2 i hi
    obtain ⟨k, hk⟩ := card_dvd_of_le (inf_le_left : Z ⊓ centralizer (I : Set G) ≤ Z)
    have hpos : 0 < Nat.card ↥(Z ⊓ centralizer (I : Set G)) := Nat.card_pos
    have hk1 : k ≠ 1 := by
      intro h
      rw [h, mul_one] at hk
      exact hne (eq_of_le_of_card_ge inf_le_left hk.le)
    have hk0 : k ≠ 0 := by
      intro h
      rw [h, mul_zero] at hk
      exact (Nat.card_pos (α := ↥Z)).ne' hk
    have hk2 : k ≤ 2 := by
      rw [hk, mul_comm 2] at hle
      exact Nat.le_of_mul_le_mul_left hle hpos
    have hk' : k = 2 := by omega
    rw [hk, hk', mul_comm]
  have hindex₂ : Nat.card ↥Z = 2 * Nat.card ↥(cZ T (l2Of S ⊔ T)) := by
    rw [s134_cZ_L2T S hZcard]
    exact hZcard
  have hVL2T : V ≤ pCoreOf 2 (l2Of S ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((s134_V_le_L2 S).trans le_sup_left)
      (sup_le ((s134_L2_le_L S).trans S.frame.L_le) S.frame.T_le) S.isPGroup_V
  have hInH₂ : InH T (l2Of S ⊔ T) :=
    ⟨le_sup_right, fun h => S.irr.2.1 (le_bot_iff.1 (h ▸ hVL2T))⟩
  have hK2 : oTwoRes (l2Of S ⊔ T) = l2Of S := s134_oTwoRes_L2T S
  have hcent : InH T ((I ⊔ T) ⊔ (l2Of S ⊔ T)) →
      (((I ⊔ T) ⊔ (l2Of S ⊔ T)) ⊓ centralizer (cZ T (oTwoRes (I ⊔ T)) : Set G) ≤
          normalizer (oTwoRes (I ⊔ T) : Set G) ∧
        ((I ⊔ T) ⊔ (l2Of S ⊔ T)) ⊓ centralizer (cZ T (oTwoRes (l2Of S ⊔ T)) : Set G) ≤
          normalizer (oTwoRes (l2Of S ⊔ T) : Set G)) ∧
      (oTwoRes (I ⊔ T) = oThreePrimeResidual (((I ⊔ T) ⊔ (l2Of S ⊔ T)) ⊓
          centralizer (cZ T (oTwoRes (I ⊔ T)) : Set G)) ∨
        oTwoRes (l2Of S ⊔ T) = oThreePrimeResidual (((I ⊔ T) ⊔ (l2Of S ⊔ T)) ⊓
          centralizer (cZ T (oTwoRes (l2Of S ⊔ T)) : Set G))) := by
    intro hInH0
    set H₀ := (I ⊔ T) ⊔ (l2Of S ⊔ T) with hH₀
    have hMH0 : ¬ M ≤ H₀ := fun h =>
      hITM (le_sup_left.trans (s134_le_of_normalizer_le S hInH0.2 h))
    have hMH0eq : M ⊓ H₀ = l2Of S ⊔ T :=
      (eq_of_overgroups hclsM h12 h21 le_sup_right (le_inf hL2TM le_sup_right) inf_le_left h2T
        fun h => hMH0 (h.symm.le.trans inf_le_right)).symm
    have hGzH0 : Gz ⊓ H₀ = I ⊔ T := by
      refine (eq_of_overgroups hclsGz hA₁₂ hA₂₁ le_sup_right (le_inf hITGz le_sup_left)
        inf_le_left hITT fun h => hMH0 ?_).symm
      rw [← hMsup]
      exact sup_le (hL1TGz.trans (h.symm.le.trans inf_le_right)) le_sup_right
    have hzK1 : z ∈ cZ T (oTwoRes (I ⊔ T)) :=
      mem_inf.2 ⟨hz.2, mem_centralizer_of_le_centralizer ((oTwoRes_le _).trans hITGz)⟩
    have hzVK2 : S.zV ∈ cZ T (oTwoRes (l2Of S ⊔ T)) := by
      rw [hK2]
      refine mem_inf.2 ⟨s134_zV_mem_Z S, ?_⟩
      have hzVL : S.zV ∈ centralizer (L : Set G) := (S.mem_ZV_iff.2 (Or.inr rfl)).2
      exact centralizer_le (SetLike.coe_subset_coe.2 (s134_L2_le_L S)) hzVL
    have hC1 : centralizer (cZ T (oTwoRes (I ⊔ T)) : Set G) ≤ Gz :=
      centralizer_le (Set.singleton_subset_iff.2 hzK1)
    have hC2 : centralizer (cZ T (oTwoRes (l2Of S ⊔ T)) : Set G) ≤ M := by
      rw [← hCzV]
      exact centralizer_le (Set.singleton_subset_iff.2 hzVK2)
    have hH0C2 : H₀ ⊓ centralizer (cZ T (oTwoRes (l2Of S ⊔ T)) : Set G) = l2Of S ⊔ T := by
      apply le_antisymm
      · intro x hx
        have : x ∈ M ⊓ H₀ := mem_inf.2 ⟨hC2 (mem_inf.1 hx).2, (mem_inf.1 hx).1⟩
        rw [hMH0eq] at this
        exact this
      · refine le_inf le_sup_right ?_
        rw [hK2]
        refine sup_le (fun l hl => ?_) (fun t ht => ?_)
        · rw [mem_centralizer_iff]
          intro x hx
          exact (mem_centralizer_iff.1 (mem_inf.1 hx).2 l hl).symm
        · rw [mem_centralizer_iff]
          intro x hx
          exact (mem_centralizer_iff.1 (mem_quasithinOmegaOneCenter_iff.1
            (mem_inf.1 hx).1).2.1 t ht).symm
    refine ⟨⟨fun x hx => ?_, ?_⟩, Or.inr ?_⟩
    · have : x ∈ Gz ⊓ H₀ := mem_inf.2 ⟨hC1 (mem_inf.1 hx).2, (mem_inf.1 hx).1⟩
      rw [hGzH0] at this
      exact le_normalizer_oTwoRes _ this
    · rw [hH0C2, hK2]
      exact sup_le le_normalizer (s134_T_le_normalizer_L2 S)
    · rw [hH0C2, s134_oThree_L2T S hA6, hK2]
  have hyp : Hyp1347 T (I ⊔ T) (l2Of S ⊔ T) :=
    { inH₁ := hstar.1
      inH₂ := hInH₂
      ne := fun h => hITM (h.le.trans hL2TM)
      s3₁ := hITq
      s3₂ := s134_L2T_quot S hCT
      chief := Or.inr (by rw [hK2]; exact s134_chief_L2 S)
      index₁ := hindex₁
      index₂ := hindex₂
      cent := hcent }
  obtain ⟨⟨hInH0, hH0M, -, -, -, hc₁, -, hcases⟩, h2', h3', hniv, hii2⟩ :=
    h1347 G T L V S _ _ hyp hK2
  set H₀ := (I ⊔ T) ⊔ (l2Of S ⊔ T) with hH₀
  have hii : Concl1347ii T (I ⊔ T) (l2Of S ⊔ T) := by
    rcases hcases with hi | hii | hiii | hiv
    · exfalso
      have hcomm := hi.2.1
      rw [hK2] at hcomm
      have hL2N : l2Of S ≤ normalizer (oTwoRes (I ⊔ T) : Set G) := by
        refine le_normalizer_of_conj_mem' fun l hl k hk => ?_
        have hlk : ⁅l, k⁆ ∈ ⁅oTwoRes (I ⊔ T), l2Of S⁆ := by
          rw [commutator_comm]
          exact commutator_mem_commutator hl hk
        have hc : ⁅l, k⁆ ∈ pCoreOf 2 (oTwoRes (I ⊔ T)) := (mem_inf.1 (hcomm hlk)).1
        have e : l * k * l⁻¹ = ⁅l, k⁆ * k := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact mul_mem (LieType.BorelTits.pCoreOf_le 2 _ hc) hk
      have hL1N : L₁ ≤ normalizer (oTwoRes (I ⊔ T) : Set G) := by
        rw [oTwoRes_sup_eq hT2 hTI]
        exact (le_sup_left.trans hL1TGz).trans (hGzI.trans (normalizer_le_normalizer_oTwoRes I))
      have hKV := s134_le_centralizer_V S hz hzL ((oTwoRes_le _).trans hITGz) hL1N hL2N
      have hCVM : centralizer (V : Set G) ≤ M := fun x hx =>
        A6.Setting134.normalizer_V_le S (Subgroup.centralizer_le_normalizer _ hx)
      exact hITM ((le_oTwoRes_sup_of_isSylowTwoOf hsylIT).trans (sup_le (hKV.trans hCVM) hTM))
    · exact hii
    · exact absurd hiii h3'
    · exact absurd hiv hniv
  have hL1Gz : L₁ ⊔ T ≠ Gz := fun h => hCz (h.symm.le.trans hL1TM)
  have hITne : I ⊔ T ≠ Gz := by
    intro h
    obtain ⟨e₁⟩ := (quasithinO2QuotientIso_iff _ _).1 hITq
    obtain ⟨e₂⟩ := (quasithinO2QuotientIso_iff _ _).1 hGzq
    have h6 := Nat.card_congr e₁.toEquiv
    have h36 := Nat.card_congr e₂.toEquiv
    rw [h] at h6
    rw [h6, Nat.card_perm, Nat.card_prod, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin] at h36
    norm_num [Nat.factorial] at h36
  have hL1A : L₁ ⊔ T = A₁ ∨ L₁ ⊔ T = A₂ := by
    rcases hclsGz _ le_sup_right hL1TGz with h | h | h | h
    · exact absurd h h1T
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hL1Gz
  have hITA : I ⊔ T = A₁ ∨ I ⊔ T = A₂ := by
    rcases hclsGz _ le_sup_right hITGz with h | h | h | h
    · exact absurd h hITT
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd h hITne
  have hL1IT : L₁ ⊔ T ≠ I ⊔ T := fun h => hITM (h ▸ hL1TM)
  have hcls : ∀ X : Subgroup G, T ≤ X → X ≤ Gz →
      X = T ∨ X = L₁ ⊔ T ∨ X = I ⊔ T ∨ X = Gz := by
    intro X hTX hXGz
    rcases hclsGz X hTX hXGz with h | h | h | h
    · exact Or.inl h
    · rcases hL1A with h' | h'
      · exact Or.inr (Or.inl (h.trans h'.symm))
      · rcases hITA with h'' | h''
        · exact Or.inr (Or.inr (Or.inl (h.trans h''.symm)))
        · exact absurd (h'.trans h''.symm) hL1IT
    · rcases hL1A with h' | h'
      · rcases hITA with h'' | h''
        · exact absurd (h'.trans h''.symm) hL1IT
        · exact Or.inr (Or.inr (Or.inl (h.trans h''.symm)))
      · exact Or.inr (Or.inl (h.trans h'.symm))
    · exact Or.inr (Or.inr (Or.inr h))
  have hL1nle : ¬ L₁ ⊔ T ≤ I ⊔ T := by
    intro hle
    rcases hL1A with h' | h'
    · rcases hITA with h'' | h''
      · exact hL1IT (h'.trans h''.symm)
      · exact hA₁₂ (h' ▸ h'' ▸ hle)
    · rcases hITA with h'' | h''
      · exact hA₂₁ (h' ▸ h'' ▸ hle)
      · exact hL1IT (h'.trans h''.symm)
  have hITnle : ¬ I ⊔ T ≤ L₁ ⊔ T := fun hle => hITM (hle.trans hL1TM)
  have hzcZ : z ∈ cZ T (I ⊔ T) :=
    mem_inf.2 ⟨hz.2, mem_centralizer_of_le_centralizer hITGz⟩
  have hcZ : cZ T (I ⊔ T) = zpowers z := by
    refine (eq_of_le_of_card_ge (zpowers_le.mpr hzcZ) ?_).symm
    rw [hc₁, Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
  have hCZ : centralizer (Z : Set G) ≤ L₁ ⊔ T := by
    rw [← hMGz]
    refine le_inf ?_ ?_
    · rw [← hCzV]
      exact centralizer_le (Set.singleton_subset_iff.2 (s134_zV_mem_Z S))
    · exact centralizer_le (Set.singleton_subset_iff.2 hz.2)
  have hL1M : L₁ ⊔ T ≠ M := fun h => h21 (hL2TM.trans h.symm.le)
  have hHX : ∀ X : Subgroup G, InH H₀ X → X = H₀ := by
    intro X hX
    have hXL1 : X ⊓ (L₁ ⊔ T) = T := by
      by_contra hne
      have hTX : T ≤ X := (le_sup_right.trans le_sup_left).trans hX.1
      have heq := eq_of_overgroups hclsM h12 h21 (le_inf hTX le_sup_right) inf_le_right hL1TM
        hne hL1M
      have hMX : M ≤ X := by
        rw [← hMsup]
        exact sup_le (heq.symm.le.trans inf_le_left) (le_sup_right.trans hX.1)
      exact hH0M (hX.1.trans (s134_le_of_normalizer_le S hX.2 hMX))
    have hXCZ : X ⊓ centralizer (Z : Set G) = T := by
      refine le_antisymm ?_ (le_inf ((le_sup_right.trans le_sup_left).trans hX.1) hTZ)
      calc X ⊓ centralizer (Z : Set G) ≤ X ⊓ (L₁ ⊔ T) := inf_le_inf_left _ hCZ
        _ = T := hXL1
    exact h2' hii X hX hXCZ
  exact ⟨I ⊔ T, hstar, hITGz, fun X hX hXGz => hstaru X hX hXGz, hITq, hcls, hL1nle, hITnle,
    hcZ, hInH0, hH0M, hii, hHX⟩

end CFSG.Quasithin.H13.U3
