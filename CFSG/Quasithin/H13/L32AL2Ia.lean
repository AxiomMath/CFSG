module

public import CFSG.Quasithin.H13.L32A705a

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

abbrev vY (T V : Subgroup G) (z' : G) : Subgroup G := fsuV1 T V ⊔ Subgroup.zpowers z'

abbrev iI (T L V : Subgroup G) (z z' : G) : Subgroup G := l1 T L V ⊔ T ⊔ a114Y z z'

abbrev vI (T L V : Subgroup G) (z z' : G) : Subgroup G :=
  conjClosure (fsuV1 T V) (iI T L V z z')

structure IData (T L V TY : Subgroup G) (z z' : G) : Prop where
  S : Setting147 G T L V (A6.g1 T V)
  hz : Subgroup.zpowers z = fsuV1 T V
  hA : A114Hyp (vY T V z') z z'
  hTY : TY ≤ T
  hLTY : l1 T L V ⊔ T ≤ Subgroup.normalizer (TY : Set G)
  hTYV : TY ≤ Subgroup.normalizer (vY T V z' : Set G)
  hO2Y0 : pCoreOf 2 (a114Y z z') ≤ TY
  hO2G1 : pCoreOf 2 (A6.g1 T V) ≤ TY
  hSyl : IsSylowTwoOf TY (a114Y z z' ⊔ TY)
  hO2Y : pCoreOf 2 (a114Y z z' ⊔ TY) =
    (a114Y z z' ⊔ TY) ⊓ Subgroup.centralizer (vY T V z' : Set G)
  hW0 : a114Y z z' ⊔ TY ≤ Subgroup.normalizer (E3.wClos V 0 TY : Set G)
  hVTY : V ≤ TY
  hL1 : ¬ pCoreOf 2 (l1 T L V) ≤ Subgroup.normalizer (vY T V z' : Set G)
  hx3 : ∃ x ∈ l1 T L V, orderOf x = 3 ∧ x ∈ Subgroup.centralizer (vY T V z' : Set G)
  hVcl : V ≤ Subgroup.closure {w | ∃ l ∈ pCoreOf 2 (l1 T L V), w = l * z' * l⁻¹} ⊔ fsuV1 T V
  hCT : T ⊓ Subgroup.centralizer (V : Set G) ⊓ Subgroup.centralizer (vY T V z' : Set G) ≤ TY

namespace IData

variable {T L V TY : Subgroup G} {z z' : G} (D : IData T L V TY z z')
include D

omit D [Finite G] in
theorem T_le_iI : T ≤ iI T L V z z' := le_sup_right.trans le_sup_left

omit D [Finite G] in
theorem l1_le_iI : l1 T L V ≤ iI T L V z z' := le_sup_left.trans le_sup_left

omit D [Finite G] in
theorem a114Y_le_iI : a114Y z z' ≤ iI T L V z z' := le_sup_right

theorem TY_le_iI : TY ≤ iI T L V z z' := D.hTY.trans T_le_iI

theorem isPGroup_T : IsPGroup 2 T := D.S.hyp.fsu.sylow.1

theorem iI_le_normalizer_W0 :
    iI T L V z z' ≤ Subgroup.normalizer (E3.wClos V 0 TY : Set G) :=
  sup_le (D.hLTY.trans (E3.normalizer_le_normalizer_wClos TY))
    (le_sup_left.trans D.hW0)

theorem W0_le_iI : E3.wClos V 0 TY ≤ iI T L V z z' := (E3.wClos_le 0 TY).trans D.TY_le_iI

theorem V_spec (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    IsElemAbelian 2 V ∧ Nat.card V = 8 := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V D.S.hyp.hyp D.S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 D.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 D.S.hyp h1222 h1332 h1334 hV2
  exact ⟨⟨inferInstance, fun v hv => S14.sq_V hv⟩, S14.card_V⟩

theorem W0_ne_bot (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    E3.wClos V 0 TY ≠ ⊥ := by
  obtain ⟨hVe, hV8⟩ := D.V_spec h1222 h1332 h1334
  refine E3.wClos_ne_bot hVe D.hVTY ?_
  have : rk ↥V = 3 := by
    rw [rk, hV8, show (8 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  omega

theorem pCoreOf_iI_ne_bot (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    pCoreOf 2 (iI T L V z z') ≠ ⊥ := by
  have hW := LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 D.W0_le_iI D.iI_le_normalizer_W0
    (D.isPGroup_T.to_le ((E3.wClos_le 0 TY).trans D.hTY))
  intro hb
  exact D.W0_ne_bot h1222 h1332 h1334 (le_bot_iff.mp (hb ▸ hW))

theorem isSylowTwoOf_T : IsSylowTwoOf T (iI T L V z z') :=
  isSylowTwoOf_of_quasithinIsSylowTwo D.S.hyp.fsu.sylow T_le_iI

theorem charTwo_iI (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    CharTwo (iI T L V z z') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT := D.S.hyp.fsu.sylow
  refine charTwo_of_inH D.S.hyp.fsu.qtke.2.1 (hT.1.toSylow hT.2)
    ⟨?_, D.pCoreOf_iI_ne_bot h1222 h1332 h1334⟩
  rw [IsPGroup.toSylow_coe]
  exact T_le_iI

theorem sqtk_iI (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    SQTKGroup ↥(iI T L V z z') :=
  sqtkGroup_of_pCoreOf_ne_bot D.S.hyp.fsu.qtke D.S.hyp.fsu.simple D.S.hyp.fsu.nonabelian
    (D.pCoreOf_iI_ne_bot h1222 h1332 h1334)

theorem vI_spec (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    vI T L V z z' ≤ pCoreOf 2 (iI T L V z z') ⊓
        Subgroup.centralizer (pCoreOf 2 (iI T L V z z') : Set G) ∧
      IsElemAbelian 2 (vI T L V z z') ∧ IsTwoReducedIn (iI T L V z z') (vI T L V z z') :=
  conjClosure_isTwoReducedIn_of_charTwo D.isSylowTwoOf_T (D.charTwo_iI h1222 h1332 h1334)
    inf_le_right

omit D [Finite G] in
theorem V1_le_vI : fsuV1 T V ≤ vI T L V z z' := le_conjClosure _ _

theorem z_mem_vI : z ∈ vI T L V z z' := V1_le_vI (D.hz ▸ Subgroup.mem_zpowers z)

theorem z'_mem_vI : z' ∈ vI T L V z z' := by
  obtain ⟨-, a₂, -, ha₂, -, h₂⟩ := D.hA.exists_gens
  have hzz : z * z' ∈ vI T L V z z' := by
    rw [← h₂]
    exact mem_conjClosure (a114Y_le_iI (Subgroup.mem_sup_right ha₂)) (D.hz ▸ Subgroup.mem_zpowers z)
  have := Subgroup.mul_mem _ (Subgroup.inv_mem _ D.z_mem_vI) hzz
  rwa [inv_mul_cancel_left] at this

theorem vY_le_vI : vY T V z' ≤ vI T L V z z' :=
  sup_le V1_le_vI (Subgroup.zpowers_le.mpr D.z'_mem_vI)

theorem V_le_vI : V ≤ vI T L V z z' := by
  refine D.hVcl.trans (sup_le ?_ V1_le_vI)
  rw [Subgroup.closure_le]
  rintro w ⟨l, hl, rfl⟩
  have hlI : l ∈ iI T L V z z' := l1_le_iI (pCoreOf_le 2 _ hl)
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure _ _ hlI) z').mp D.z'_mem_vI

theorem centralizer_vI_le :
    Subgroup.centralizer (vI T L V z z' : Set G) ≤
      Subgroup.centralizer (V : Set G) ⊓ Subgroup.centralizer (vY T V z' : Set G) :=
  le_inf (Subgroup.centralizer_le D.V_le_vI) (Subgroup.centralizer_le D.vY_le_vI)

theorem not_le_normalizer_l1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : ¬ iI T L V z z' ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  intro hN
  obtain ⟨-, -, hred⟩ := D.vI_spec h1222 h1332 h1334
  have hD : pCoreOf 2 (l1 T L V) ≤ Subgroup.centralizer (vI T L V z z' : Set G) := by
    refine hred.2.2.2 _ ((pCoreOf_le 2 _).trans l1_le_iI)
      (hN.trans (normalizer_le_normalizer_pCoreOf 2 _)) fun d hd => ?_
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (l1 T L V) ⟨d, hd⟩
    refine ⟨k, ?_⟩
    have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    rw [this]
    exact Subgroup.one_mem _
  exact D.hL1 ((hD.trans (D.centralizer_vI_le.trans inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _))

theorem a114Y_not_le_normalizer_l1 (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) : ¬ a114Y z z' ≤ Subgroup.normalizer (l1 T L V : Set G) := by
  intro hY
  refine D.not_le_normalizer_l1 h1222 h1332 h1334 (sup_le (sup_le ?_ ?_) hY)
  · exact Subgroup.le_normalizer
  · exact Setting147.T_le_N_l1 D.S h1332

end IData

end CFSG.Quasithin.H13.L32A.L2
