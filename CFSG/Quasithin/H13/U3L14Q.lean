module

public import CFSG.Quasithin.H13.U3L14J
public import CFSG.Quasithin.H13.NQBlockEscapingComponent
public import CFSG.Quasithin.H13.NQTermAmbientQuotient
public import CFSG.Quasithin.H13.U3L14E

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem commutator_le_of_le_normalizer {Γ : Type*} [Group Γ] {K X : Subgroup Γ}
    (h : X ≤ normalizer (K : Set Γ)) : ⁅K, X⁆ ≤ K := by
  rw [commutator_le]
  intro k hk x hx
  have hx' : x * k⁻¹ * x⁻¹ ∈ K := (mem_normalizer_iff.mp (h hx) k⁻¹).mp (inv_mem hk)
  rw [commutatorElement_def, mul_assoc, mul_assoc]
  exact mul_mem hk (by simpa [mul_assoc] using hx')

theorem commutator_eq_of_isComponent {Γ : Type} [Group Γ] [Finite Γ] {K X A : Subgroup Γ}
    (hK : K ∈ cComp (⊤ : Subgroup Γ))
    (hc : CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.pCore 2 Γ))))
    (hXK : X ≤ normalizer (K : Set Γ)) (hAX : A ≤ X) (hKA : ¬ ⁅K, A⁆ ≤ CFSG.pCore 2 Γ) :
    ⁅K, X⁆ = K := by
  rcases cComp_commutator_dichotomy hK X with ⟨-, hsolv⟩ | h
  · exfalso
    set π := QuotientGroup.mk' (CFSG.pCore 2 Γ) with hπ
    set Kb := K.map π with hKb
    set Xb := X.map π with hXb
    have hq : CFSG.IsQuasisimple ↥Kb := hc.1
    have hKX : ⁅Kb, Xb⁆ = (⁅K, X⁆).map π := (map_commutator _ _ _).symm
    have hsb : Group.IsSolvable ↥⁅Kb, Xb⁆ := by
      rw [hKX]
      exact Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
    have hXbK : Xb ≤ normalizer (Kb : Set (Γ ⧸ CFSG.pCore 2 Γ)) :=
      (map_mono hXK).trans (le_normalizer_map _)
    have hle : ⁅Kb, Xb⁆ ≤ Kb := commutator_le_of_le_normalizer hXbK
    have hn : (⁅Kb, Xb⁆.subgroupOf Kb).Normal :=
      (normal_subgroupOf_iff_le_normalizer hle).2 (A3.le_normalizer_commutator_left Kb Xb)
    have hbot : ⁅Kb, Xb⁆ = ⊥ := by
      rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with htop | hcen
      · exfalso
        have hKle : Kb ≤ ⁅Kb, Xb⁆ := by
          intro k hk
          have : (⟨k, hk⟩ : ↥Kb) ∈ ⁅Kb, Xb⁆.subgroupOf Kb := htop ▸ mem_top _
          exact this
        have hKs : Group.IsSolvable ↥Kb :=
          Group.isSolvable_of_isSolvable_injective (inclusion_injective hKle)
        obtain ⟨hperf, -, a, b, hab⟩ := hq
        obtain ⟨n, hn⟩ := hKs.solvable
        have htop' : ∀ m, derivedSeries ↥Kb m = ⊤ := by
          intro m
          induction m with
          | zero => rfl
          | succ m ih =>
            rw [derivedSeries_succ, ih]
            exact hperf.commutator_eq_top
        rw [htop'] at hn
        have h1 : ∀ x : ↥Kb, x = 1 := fun x => by
          have hx : x ∈ (⊥ : Subgroup ↥Kb) := hn ▸ mem_top x
          exact mem_bot.mp hx
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b => exact hab (by rw [h1 a, h1 b])
      · refine CFSG.LocalCores.perfect_double_commutator hq.1 ?_
        rw [commutator_eq_bot_iff_le_centralizer]
        intro c hc'
        rw [mem_centralizer_iff]
        intro k hk
        have hcz : (⟨c, hle hc'⟩ : ↥Kb) ∈ center ↥Kb := hcen hc'
        exact congrArg Subtype.val ((mem_center_iff.mp hcz) ⟨k, hk⟩)
    apply hKA
    have h1 : (⁅K, X⁆).map π = ⊥ := hKX ▸ hbot
    have h2 : ⁅K, X⁆ ≤ CFSG.pCore 2 Γ := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 Γ)]
      exact (Subgroup.map_eq_bot_iff _).mp h1
    exact (commutator_mono le_rfl hAX).trans h2
  · rw [h]
    exact le_antisymm (conjClosure_le fun _ hs x hx => (mem_normalizer_iff.mp (hXK hs) x).mp hx)
      (le_conjClosure K X)

variable {G : Type} [Group G] [Finite G]

theorem isQuasisimple_quot_of_isComponent {H K : Subgroup G} (hK : K ∈ cComp H)
    (hc : CFSG.IsComponent ((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) :
    CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK'c : CFSG.IsCComponent (K.subgroupOf H) :=
    mem_cComp_top_iff_isCComponent.1 (subgroupOf_mem_cComp hK)
  have hKcap : (CFSG.pCore 2 ↥(K.subgroupOf H)).map (K.subgroupOf H).subtype =
      K.subgroupOf H ⊓ (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).ker := by
    rw [QuotientGroup.ker_mk']
    have h := CFSG.LocalCores.prime_set_core_subnormal_intersection
      {q : Nat.Primes | q.val = 2} hK'c.2.2.1
    rw [← CFSG.pCore_eq_piCore (K.subgroupOf H) 2, ← CFSG.pCore_eq_piCore ↥H 2] at h
    exact h
  obtain ⟨e⟩ := NQBlock.nonempty_quotient_mulEquiv (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) rfl
    (CFSG.pCore 2 ↥(K.subgroupOf H)) hKcap
  have hq' : CFSG.IsQuasisimple (↥(K.subgroupOf H) ⧸ CFSG.pCore 2 ↥(K.subgroupOf H)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hc.1
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (NQTerm.isQuasisimple_pCore_quotient_congr (subgroupOfEquivOfLe hKH)).1 hq'
  exact A3.isQuasisimple_iff_open.1 (CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (A3.pCore_eq_openCore 2 ↥K)) hq)

theorem commutator_eq_of_isComponent_of_le {H K X A : Subgroup G} (hK : K ∈ cComp H)
    (hc : CFSG.IsComponent ((K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))))
    (hXH : X ≤ H) (hXK : X ≤ normalizer (K : Set G)) (hAX : A ≤ X)
    (hKA : ¬ ⁅K, A⁆ ≤ pCoreOf 2 H) : ⁅K, X⁆ = K := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hXK' : X.subgroupOf H ≤ normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro k
    have h := (mem_normalizer_iff.mp (hXK (mem_subgroupOf.mp hx)) k)
    simpa [mem_subgroupOf] using h
  have hKA' : ¬ ⁅K.subgroupOf H, A.subgroupOf H⁆ ≤ CFSG.pCore 2 ↥H := by
    intro h
    apply hKA
    have h1 := map_mono (f := H.subtype) h
    rw [map_commutator, map_subgroupOf_eq_of_le hKH,
      map_subgroupOf_eq_of_le ((hAX.trans hXH))] at h1
    refine h1.trans ?_
    rintro _ ⟨y, hy, rfl⟩
    exact coe_mem_pCoreOf_iff.2 hy
  have h := commutator_eq_of_isComponent (subgroupOf_mem_cComp hK) hc hXK'
    (fun x hx => mem_subgroupOf.mpr (hAX (mem_subgroupOf.mp hx))) hKA'
  have h2 := congrArg (Subgroup.map H.subtype) h
  rwa [map_commutator, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hXH] at h2

structure KData14 (T L V V₂ Lp K : Subgroup G) : Prop where
  mem : K ∈ cComp (A6.g1 T V)
  comp : CFSG.IsComponent ((K.subgroupOf (A6.g1 T V)).map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V))))
  quasi : CFSG.Open.IsQuasisimple (↥K ⧸ CFSG.Open.pCore 2 ↥K)
  comm : ¬ ⁅K, pCoreOf 2 Lp⁆ ≤ pCoreOf 2 (A6.g1 T V)
  omega : ⁅omegaOneCenterOf (pCoreOf 2 (A6.g1 T V)), K⁆ ≠ ⊥
  faithful : quasithinIsFaithfulLocal T K
  T_K : T ≤ normalizer (K : Set G)
  G1_K : A6.g1 T V ≤ normalizer (K : Set G)
  L_K : ¬ L ≤ normalizer (K : Set G)
  K_M : ¬ K ≤ normalizer (L : Set G)
  L2_K : ¬ L₁Of L V₂ ≤ normalizer (K : Set G)
  Lp_K : Lp ≤ normalizer (K : Set G)
  eqLp : ⁅K, Lp⁆ = K

namespace Set14

variable {T L V V₂ V₃ Lp : Subgroup G} (S : Set14 G T L V V₂ V₃ Lp)
include S

theorem kData_of (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) {K : Subgroup G}
    (hK : K ∈ cComp (A6.g1 T V))
    (hc : CFSG.IsComponent ((K.subgroupOf (A6.g1 T V)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(A6.g1 T V)))))
    (hKA : ¬ ⁅K, pCoreOf 2 Lp⁆ ≤ pCoreOf 2 (A6.g1 T V)) : KData14 T L V V₂ Lp K := by
  obtain ⟨hΩ, hfK, hTK, hHK, hLK, hKM⟩ := S.stepE h1332 h1336 h37 h38 h39 hQ hK
  have hLpK : Lp ≤ normalizer (K : Set G) := S.Lp_G1.trans hHK
  exact
    { mem := hK
      comp := hc
      quasi := isQuasisimple_quot_of_isComponent hK hc
      comm := hKA
      omega := hΩ
      faithful := hfK
      T_K := hTK
      G1_K := hHK
      L_K := hLK
      K_M := hKM
      L2_K := S.stepF hHK hLK
      Lp_K := hLpK
      eqLp := commutator_eq_of_isComponent_of_le hK hc S.Lp_G1 hLpK
        (LieType.BorelTits.pCoreOf_le 2 Lp) hKA }

theorem exists_kData (h1332 : Stmt13_3_2) (h1336 : A6.Stmt13_3_6) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hQ : pCoreOf 2 (A6.g1 T V) ≤ centralizer (V₂ : Set G)) (hd : StepD T V Lp) :
    ∃ K : Subgroup G, KData14 T L V V₂ Lp K := by
  obtain ⟨K, hK, hc, hKA⟩ := S.exists_K hQ hd
  exact ⟨K, S.kData_of h1332 h1336 h37 h38 h39 hQ hK hc hKA⟩

theorem K_eq_comm_J (h1332 : Stmt13_3_2) (hC58 : TheoremC58) (h317 : AS317Sylow)
    {K : Subgroup G} (hD : KData14 T L V V₂ Lp K) : ⁅K, thompsonJ T⁆ = K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hKH : K ≤ A6.g1 T V := le_of_mem_cComp hD.mem
  refine commutator_eq_of_isComponent_of_le hD.mem hD.comp (hJT.trans S.T_G1)
    (hJT.trans hD.T_K) le_rfl fun hle => ?_
  apply (S.ff_K h1332 hC58 h317 hD.faithful hD.quasi hD.G1_K hD.L2_K).1
  rw [(S.reduced_K h1332 hD.faithful hD.quasi).2]
  have hcomm : ⁅K, thompsonJ T⁆ ≤ pCoreOf 2 K := by
    refine le_trans (le_inf (commutator_le_of_le_normalizer (hJT.trans hD.T_K)) hle) ?_
    refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ K
      inf_le_left ?_ ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_right)
    refine (normal_subgroupOf_iff_le_normalizer inf_le_left).2 fun k hk => ?_
    exact mem_normalizer_inf (le_normalizer hk)
      (LieType.BorelTits.le_normalizer_pCoreOf 2 _ (hKH hk))
  have hKT : (K.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).2 (sup_le le_normalizer hD.T_K)
  have hO2K : pCoreOf 2 K ≤ T :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K (K ⊔ T)
      le_sup_left hKT).trans (pCoreOf_two_le_of_isSylowTwoOf (S.syl le_sup_right))
  set P := pCoreOf 2 K ⊔ thompsonJ T with hP
  have hPT : P ≤ T := sup_le hO2K hJT
  have hkey : ∀ g ∈ K, P ≤ P.comap (MulAut.conj g).toMonoidHom := by
    intro g hg
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact le_sup_left (a := pCoreOf 2 K)
        ((mem_normalizer_iff.mp (LieType.BorelTits.le_normalizer_pCoreOf 2 K hg) a).mp ha)
    · show g * b * g⁻¹ ∈ P
      have h1 : g * b * g⁻¹ * b⁻¹ ∈ pCoreOf 2 K :=
        hcomm (commutator_mem_commutator hg hb)
      have : g * b * g⁻¹ = (g * b * g⁻¹ * b⁻¹) * b := by group
      rw [this]
      exact mul_mem (le_sup_left (a := pCoreOf 2 K) h1) (le_sup_right (b := thompsonJ T) hb)
  have hKP : K ≤ normalizer (P : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hkey g hg hx, fun hx => ?_⟩
    have := hkey g⁻¹ (inv_mem hg) hx
    simpa [mul_assoc] using this
  have hTP : T ≤ normalizer (P : Set G) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    have hsub : ∀ s ∈ T, P ≤ P.comap (MulAut.conj s).toMonoidHom := by
      intro s hs
      refine sup_le (fun a ha => ?_) (fun b hb => ?_)
      · exact le_sup_left (a := pCoreOf 2 K)
          ((mem_normalizer_iff.mp ((hD.T_K.trans
            (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) hs) a).mp ha)
      · exact le_sup_right (b := thompsonJ T)
          ((mem_normalizer_iff.mp (normalizer_le_normalizer_thompsonJ T (le_normalizer hs)) b).mp
            hb)
    refine ⟨fun hx => hsub t ht hx, fun hx => ?_⟩
    have := hsub t⁻¹ (inv_mem ht) hx
    simpa [mul_assoc] using this
  have hPn : (P.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (hPT.trans le_sup_right)).2 (sup_le hKP hTP)
  exact (le_sup_right (a := pCoreOf 2 K)).trans
    (CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 P (K ⊔ T)
      (hPT.trans le_sup_right) hPn (S.isP_T.to_le hPT))

end Set14

end CFSG.Quasithin.H13.U3
