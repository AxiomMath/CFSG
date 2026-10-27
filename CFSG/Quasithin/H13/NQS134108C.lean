module

public import CFSG.Quasithin.H13.NQS134108B
public import CFSG.Quasithin.H13.NQS13410Asm5
public import CFSG.Quasithin.H13.U3S1349L

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem exists_h2 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) :
    ∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ K ⊔ T ∧
      (∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ K ⊔ T → X = H₂) ∧
      quasithinO2QuotientIso H₂ (Perm (Fin 3)) ∧
      (∀ X : Subgroup G, T ≤ X → X ≤ K ⊔ T →
        X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = H₂ ∨ X = K ⊔ T) ∧
      ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ H₂ ∧ ¬ H₂ ≤ L₁Of L (fsuV1 T V) ⊔ T := by
  have hM : normalizer (L : Set G) = L ⊔ T := D.M4.resolve_right hnhat
  obtain ⟨-, hZW, hL1, -, htype⟩ := (D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he).2
  obtain ⟨-, -, -, -, -, -, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S D.exists_inH
  rcases htype with ⟨hK3, hnat⟩ | ⟨hK6, h6 | hc⟩
  · exact D.exists_h2_l32 hM hZV1 hL1Z hL1 hZW hK3 hnat
  · exact D.exists_h2_nat h1332 hM hZV1 hL1Z hL1 hZW hK6 h6.1
  · exact D.exists_h2_core h1332 hM hZV1 hL1Z hL1 hZW hK6 hc.2.2

theorem eight_setup (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h1222 : Stmt12_2_2) (h1347 : U3.Stmt13_4_7L2)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) {H₂ : Subgroup G} (hstar : IsHStar T (normalizer (L : Set G)) H₂)
    (hH₂H : H₂ ≤ H) :
    quasithinO2QuotientIso H₂ (Perm (Fin 3)) ∧
      (∀ X : Subgroup G, T ≤ X → X ≤ centralizer ({z} : Set G) →
        X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = H₂ ∨ X = centralizer ({z} : Set G)) ∧
      ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ H₂ ∧ ¬ H₂ ≤ L₁Of L (fsuV1 T V) ⊔ T ∧
      U3.cZ T H₂ = zpowers z ∧
      InH T (H₂ ⊔ (U3.l2Of S ⊔ T)) ∧ ¬ H₂ ⊔ (U3.l2Of S ⊔ T) ≤ normalizer (L : Set G) ∧
      normalizer (L : Set G) ⊓ (H₂ ⊔ (U3.l2Of S ⊔ T)) = U3.l2Of S ⊔ T ∧
      centralizer ({z} : Set G) ⊓ (H₂ ⊔ (U3.l2Of S ⊔ T)) = H₂ ∧
      (U3.Concl1347i T H₂ (U3.l2Of S ⊔ T) ∨
        (U3.Concl1347ii T H₂ (U3.l2Of S ⊔ T) ∧
          ∀ X : Subgroup G, InH (H₂ ⊔ (U3.l2Of S ⊔ T)) X → X = H₂ ⊔ (U3.l2Of S ⊔ T))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM : normalizer (L : Set G) = L ⊔ T := D.M4.resolve_right hnhat
  obtain ⟨-, -, -, -, -, hZ4, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  obtain ⟨-, hHKT, hHGz, -⟩ := D.seven hC137 h1332 h1228 hC58 h317 h56 he hnhat
  have hGzKT : centralizer ({z} : Set G) = K ⊔ T := hHGz.symm.trans hHKT
  obtain ⟨H₂', hstar', -, huniq, hq, hcls, hinc1, hinc2⟩ :=
    D.exists_h2 hC137 h1332 h1228 hC58 h317 h56 he hnhat
  obtain rfl : H₂ = H₂' := huniq H₂ hstar (hH₂H.trans hHKT.le)
  have hclsGz : ∀ X : Subgroup G, T ≤ X → X ≤ centralizer ({z} : Set G) →
      X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = H₂ ∨ X = centralizer ({z} : Set G) := by
    intro X hTX hXGz
    rw [hGzKT] at hXGz ⊢
    exact hcls X hTX hXGz
  have hA6 : quasithinO2QuotientIso L ↥(alternatingGroup (Fin 6)) :=
    (quasithinO2QuotientIso_iff L _).2 he
  have hp := U3.s134_isPGroup_CMV S hA6 hM
  have hCT := U3.s134_CMV_le_T S hp h1222
  have hclsM := U3.s134_overgroups_M h1222 S hp
  have hMsup := U3.s134_sup_parabolics h1222 S hp
  obtain ⟨-, h2T, h12, h21⟩ := U3.s134_parabolics S
  have hCzV : centralizer ({S.zV} : Set G) = normalizer (L : Set G) := S.centralizer_zV h1222
  have hTM : T ≤ normalizer (L : Set G) := S.T_le_NL
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := (oTwoRes_le _).trans inf_le_left
  have hL1TM : L₁Of L (fsuV1 T V) ⊔ T ≤ normalizer (L : Set G) :=
    sup_le (hL1L.trans le_normalizer) hTM
  have hL2TM : U3.l2Of S ⊔ T ≤ normalizer (L : Set G) :=
    sup_le ((U3.s134_L2_le_L S).trans le_normalizer) hTM
  have hL1TGz : L₁Of L (fsuV1 T V) ⊔ T ≤ centralizer ({z} : Set G) := D.L1TH.trans D.Hz
  have hH₂Gz : H₂ ≤ centralizer ({z} : Set G) := hH₂H.trans D.Hz
  have hH₂M : ¬ H₂ ≤ normalizer (L : Set G) := hstar.2.1
  have hTH₂ : T ≤ H₂ := hstar.1.1
  have hH₂T : H₂ ≠ T := fun h => hH₂M (h.le.trans hTM)
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    fun t ht => mem_centralizer_iff.2 fun x hx =>
      (mem_centralizer_iff.1 (mem_quasithinOmegaOneCenter_iff.1 hx).2.1 t ht).symm
  have hzZ : z ∈ quasithinOmegaOneCenter T := D.zV1.2
  have hcZ2 : U3.cZ T H₂ = zpowers z := by
    have hzc : z ∈ U3.cZ T H₂ :=
      mem_inf.2 ⟨hzZ, U3.mem_centralizer_of_le_centralizer hH₂Gz⟩
    have hle : zpowers z ≤ U3.cZ T H₂ := zpowers_le.mpr hzc
    have hne : U3.cZ T H₂ ≠ quasithinOmegaOneCenter T := by
      intro h
      apply hinc2
      intro x hx
      refine centralizer_Z_le_L1T S hM hZV1 (mem_centralizer_iff.2 fun y hy => ?_)
      have hy' : y ∈ U3.cZ T H₂ := h ▸ hy
      exact (mem_centralizer_iff.1 (mem_inf.1 hy').2 x hx).symm
    have hdvd : Nat.card ↥(U3.cZ T H₂) ∣ 4 := hZ4 ▸ card_dvd_of_le inf_le_left
    have h2 : 2 ≤ Nat.card ↥(U3.cZ T H₂) := D.card_zpowers_z ▸ card_le_of_le hle
    have h4 : Nat.card ↥(U3.cZ T H₂) ≠ 4 := fun h =>
      hne (eq_of_le_of_card_ge inf_le_left (by rw [h, hZ4]))
    obtain ⟨c, hc⟩ : ∃ c, Nat.card ↥(U3.cZ T H₂) = c := ⟨_, rfl⟩
    rw [hc] at hdvd h2 h4
    have hc4 : c ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hc2 : c = 2 := by interval_cases c <;> omega
    exact (eq_of_le_of_card_ge hle (by rw [hc, hc2, D.card_zpowers_z])).symm
  have hZcard := U3.s134_card_Z h1332 hC58 h317 h56 S D.exists_inH
  have hindex₁ : Nat.card ↥(quasithinOmegaOneCenter T) = 2 * Nat.card ↥(U3.cZ T H₂) := by
    rw [hcZ2, D.card_zpowers_z, hZ4]
  have hindex₂ : Nat.card ↥(quasithinOmegaOneCenter T) =
      2 * Nat.card ↥(U3.cZ T (U3.l2Of S ⊔ T)) := by
    rw [U3.s134_cZ_L2T S hZcard]
    exact hZcard
  have hVL2T : V ≤ pCoreOf 2 (U3.l2Of S ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((U3.s134_V_le_L2 S).trans le_sup_left)
      (sup_le ((U3.s134_L2_le_L S).trans S.frame.L_le) S.frame.T_le) S.isPGroup_V
  have hInH₂ : InH T (U3.l2Of S ⊔ T) :=
    ⟨le_sup_right, fun h => S.irr.2.1 (le_bot_iff.1 (h ▸ hVL2T))⟩
  have hK2 : oTwoRes (U3.l2Of S ⊔ T) = U3.l2Of S := U3.s134_oTwoRes_L2T S
  have hinter : InH T (H₂ ⊔ (U3.l2Of S ⊔ T)) →
      normalizer (L : Set G) ⊓ (H₂ ⊔ (U3.l2Of S ⊔ T)) = U3.l2Of S ⊔ T ∧
        centralizer ({z} : Set G) ⊓ (H₂ ⊔ (U3.l2Of S ⊔ T)) = H₂ := by
    intro hInH0
    have hMH0 : ¬ normalizer (L : Set G) ≤ H₂ ⊔ (U3.l2Of S ⊔ T) := fun h =>
      hH₂M (le_sup_left.trans (U3.s134_le_of_normalizer_le S hInH0.2 h))
    refine ⟨(U3.eq_of_overgroups hclsM h12 h21 le_sup_right (le_inf hL2TM le_sup_right)
      inf_le_left h2T fun h => hMH0 (h.symm.le.trans inf_le_right)).symm, ?_⟩
    refine (U3.eq_of_overgroups hclsGz hinc1 hinc2 hTH₂ (le_inf hH₂Gz le_sup_left) inf_le_left
      hH₂T fun h => hMH0 ?_).symm
    rw [← hMsup]
    exact sup_le (hL1TGz.trans (h.symm.le.trans inf_le_right)) le_sup_right
  have hcent : InH T (H₂ ⊔ (U3.l2Of S ⊔ T)) →
      ((H₂ ⊔ (U3.l2Of S ⊔ T)) ⊓ centralizer (U3.cZ T (oTwoRes H₂) : Set G) ≤
          normalizer (oTwoRes H₂ : Set G) ∧
        (H₂ ⊔ (U3.l2Of S ⊔ T)) ⊓ centralizer (U3.cZ T (oTwoRes (U3.l2Of S ⊔ T)) : Set G) ≤
          normalizer (oTwoRes (U3.l2Of S ⊔ T) : Set G)) ∧
      (oTwoRes H₂ = oThreePrimeResidual ((H₂ ⊔ (U3.l2Of S ⊔ T)) ⊓
          centralizer (U3.cZ T (oTwoRes H₂) : Set G)) ∨
        oTwoRes (U3.l2Of S ⊔ T) = oThreePrimeResidual ((H₂ ⊔ (U3.l2Of S ⊔ T)) ⊓
          centralizer (U3.cZ T (oTwoRes (U3.l2Of S ⊔ T)) : Set G))) := by
    intro hInH0
    obtain ⟨hMH0eq, hGzH0⟩ := hinter hInH0
    have hzK1 : z ∈ U3.cZ T (oTwoRes H₂) :=
      mem_inf.2 ⟨hzZ, U3.mem_centralizer_of_le_centralizer ((oTwoRes_le _).trans hH₂Gz)⟩
    have hzVK2 : S.zV ∈ U3.cZ T (oTwoRes (U3.l2Of S ⊔ T)) := by
      rw [hK2]
      refine mem_inf.2 ⟨U3.s134_zV_mem_Z S, ?_⟩
      have hzVL : S.zV ∈ centralizer (L : Set G) := (S.mem_ZV_iff.2 (Or.inr rfl)).2
      exact centralizer_le (SetLike.coe_subset_coe.2 (U3.s134_L2_le_L S)) hzVL
    have hC1 : centralizer (U3.cZ T (oTwoRes H₂) : Set G) ≤ centralizer ({z} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.2 hzK1)
    have hC2 : centralizer (U3.cZ T (oTwoRes (U3.l2Of S ⊔ T)) : Set G) ≤
        normalizer (L : Set G) := by
      rw [← hCzV]
      exact centralizer_le (Set.singleton_subset_iff.2 hzVK2)
    have hH0C2 : (H₂ ⊔ (U3.l2Of S ⊔ T)) ⊓
        centralizer (U3.cZ T (oTwoRes (U3.l2Of S ⊔ T)) : Set G) = U3.l2Of S ⊔ T := by
      apply le_antisymm
      · intro x hx
        have : x ∈ normalizer (L : Set G) ⊓ (H₂ ⊔ (U3.l2Of S ⊔ T)) :=
          mem_inf.2 ⟨hC2 (mem_inf.1 hx).2, (mem_inf.1 hx).1⟩
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
    · have : x ∈ centralizer ({z} : Set G) ⊓ (H₂ ⊔ (U3.l2Of S ⊔ T)) :=
        mem_inf.2 ⟨hC1 (mem_inf.1 hx).2, (mem_inf.1 hx).1⟩
      rw [hGzH0] at this
      exact le_normalizer_oTwoRes _ this
    · rw [hH0C2, hK2]
      exact sup_le le_normalizer (U3.s134_T_le_normalizer_L2 S)
    · rw [hH0C2, U3.s134_oThree_L2T S hA6, hK2]
  have hyp : U3.Hyp1347 T H₂ (U3.l2Of S ⊔ T) :=
    { inH₁ := hstar.1
      inH₂ := hInH₂
      ne := fun h => hH₂M (h.le.trans hL2TM)
      s3₁ := hq
      s3₂ := U3.s134_L2T_quot S hCT
      chief := Or.inr (by rw [hK2]; exact U3.s134_chief_L2 S)
      index₁ := hindex₁
      index₂ := hindex₂
      cent := hcent }
  obtain ⟨⟨hInH0, hH0M, -, -, -, -, -, hcases⟩, h2', h3', hniv, hii2⟩ :=
    h1347 G T L V S _ _ hyp hK2
  obtain ⟨hMH0eq, hGzH0⟩ := hinter hInH0
  refine ⟨hq, hclsGz, hinc1, hinc2, hcZ2, hInH0, hH0M, hMH0eq, hGzH0, ?_⟩
  rcases hcases with hi | hii | hiii | hiv
  · exact Or.inl hi
  · refine Or.inr ⟨hii, fun X hX => h2' hii X hX ?_⟩
    have hL2X : U3.l2Of S ⊔ T ≤ X := le_sup_right.trans hX.1
    have hH₂X : H₂ ≤ X := le_sup_left.trans hX.1
    have hMX : ¬ normalizer (L : Set G) ≤ X := fun h =>
      hH0M (hX.1.trans (U3.s134_le_of_normalizer_le S hX.2 h))
    have hXM : X ⊓ normalizer (L : Set G) = U3.l2Of S ⊔ T := by
      have hle : U3.l2Of S ⊔ T ≤ X ⊓ normalizer (L : Set G) := le_inf hL2X hL2TM
      rcases hclsM _ (le_inf (le_sup_right.trans hL2X) hTM) inf_le_right with h | h | h | h
      · exact absurd (le_antisymm (h ▸ hle) le_sup_right) h2T
      · exact absurd (h ▸ hle) h21
      · exact h
      · exact absurd (h ▸ (inf_le_left : X ⊓ normalizer (L : Set G) ≤ X)) hMX
    have hXGz : X ⊓ centralizer ({z} : Set G) = H₂ := by
      have hle : H₂ ≤ X ⊓ centralizer ({z} : Set G) := le_inf hH₂X hH₂Gz
      rcases hclsGz _ (le_inf (hTH₂.trans hH₂X) (hTH₂.trans hH₂Gz)) inf_le_right with
        h | h | h | h
      · exact absurd (le_antisymm (h ▸ hle) hTH₂) hH₂T
      · exact absurd (h ▸ hle) hinc2
      · exact h
      · apply absurd ?_ hMX
        rw [← hMsup]
        refine sup_le (hL1TGz.trans ?_) hL2X
        rw [← h]
        exact inf_le_left
    have hH₂MT : normalizer (L : Set G) ⊓ H₂ = T := by
      rcases hclsGz _ (le_inf hTM hTH₂) (inf_le_right.trans hH₂Gz) with h | h | h | h
      · exact h
      · exact absurd (h ▸ (inf_le_right : normalizer (L : Set G) ⊓ H₂ ≤ H₂)) hinc1
      · exact absurd (h ▸ (inf_le_left : normalizer (L : Set G) ⊓ H₂ ≤ normalizer (L : Set G)))
          hH₂M
      · exact absurd (h ▸ (inf_le_right : normalizer (L : Set G) ⊓ H₂ ≤ H₂))
          fun h' => hinc1 (hL1TGz.trans h')
    refine le_antisymm ?_ (le_inf (le_sup_right.trans hL2X) hTZ)
    intro x hx
    obtain ⟨hxX, hxZ⟩ := mem_inf.1 hx
    have hxM : x ∈ normalizer (L : Set G) := hL1TM (centralizer_Z_le_L1T S hM hZV1 hxZ)
    have hxGz : x ∈ centralizer ({z} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.2 hzZ) hxZ
    have h2 : x ∈ H₂ := hXGz ▸ mem_inf.2 ⟨hxX, hxGz⟩
    exact hH₂MT ▸ mem_inf.2 ⟨hxM, h2⟩
  · exact absurd hiii h3'
  · exact absurd hiv hniv

end Data13410

end CFSG.Quasithin.H13.NQS134
