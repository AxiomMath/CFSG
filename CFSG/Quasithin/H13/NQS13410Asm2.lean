module

public import CFSG.Quasithin.H13.NQS13410Asm1
public import CFSG.Quasithin.H13.NQS13410B
public import CFSG.Quasithin.H13.NQS134Defs2
public import CFSG.Quasithin.H13.NQS13410A
public import CFSG.Quasithin.H13.NQS13410HX

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem le_normalizer_conjClosure_of {A K X : Subgroup G} (hXK : X ≤ normalizer (K : Set G))
    (hXA : ∀ x ∈ X, ∀ a ∈ A, x * a * x⁻¹ = a) :
    X ≤ normalizer (conjClosure A K : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun x hx n hn => ?_
  induction hn using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, a, ha, rfl⟩ := hy
    have hxk : x * k * x⁻¹ ∈ K := (mem_normalizer_iff.mp (hXK hx) k).mp hk
    have e : x * (k * a * k⁻¹) * x⁻¹ = (x * k * x⁻¹) * (x * a * x⁻¹) * (x * k * x⁻¹)⁻¹ := by
      group
    rw [e, hXA x hx a ha]
    exact mem_conjClosure hxk ha
  | one => simp
  | mul a b _ _ ha hb =>
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact mul_mem ha hb
  | inv a _ ha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ha

omit [Finite G] in
theorem card_quot_of_type (K : Subgroup G) :
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) →
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60) ∧
    (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 → Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 168) ∧
    (Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) →
      Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 360) ∧
    (A6.IsHatA6 K → Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 1080) := by
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  refine ⟨fun he => ?_, fun h3 => ?_, fun he => ?_, fun hh => ?_⟩
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, h60]
  · exact card_of_statedClassicalModel_psl32 (statedClassicalModel_of_lieModel_psl32 h3)
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, h360]
  · obtain ⟨-, hz, ⟨e⟩⟩ := hh
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center (↥K ⧸ CFSG.pCore 2 ↥K))
    rw [Nat.card_congr e.toEquiv, h360, hz] at h1
    rw [h1]

theorem l32_of_case1ii {K W : Subgroup G} [IsMulCommutative ↥W]
    (hKW : K ≤ normalizer (W : Set G)) (hO : pCoreOf 2 K ≤ centralizer (W : Set G))
    {J : Subgroup (MulAut ↥W)} (hii : B51Case1ii J (autOn K W))
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K) :
    LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 := by
  obtain ⟨-, n', F, _, _, hF, I', π, -, -, hreal, -, -⟩ := hii
  have hinj := B5.realizesVia_injective (FFModel.nat_faithful _) (hreal 0)
  have hcard := Nat.card_congr (Equiv.ofBijective π ⟨hinj, (hreal 0).1⟩)
  rw [← Nat.card_congr (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).toEquiv,
    Vol2.Ch11.SecC.B51.card_SL3_eq_pow hF] at hcard
  have hdvd := A6.card_autOn_dvd_quot hKW hO
  rw [← hcard] at hdvd
  have h7 : 7 ∣ 2 ^ (3 * n') - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ 3) 1 n'
    rw [one_pow, ← pow_mul] at this
    norm_num at this
    exact this
  have h7' : 7 ∣ Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) :=
    (Dvd.dvd.mul_left (Dvd.dvd.mul_right h7 _) _).trans hdvd
  obtain ⟨c5, -, c6, cH⟩ := card_quot_of_type K
  rcases hK with h | h | h | h
  · rw [c5 h] at h7'
    omega
  · exact h
  · rw [c6 h] at h7'
    omega
  · rw [cH h] at h7'
    omega

omit [Finite G] in
theorem nat_of_l32 {K W : Subgroup G} [IsMulCommutative ↥W] (hKW : K ≤ normalizer (W : Set G))
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    (hmod : (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
      (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
      (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
        FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥) ∨
      (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
        BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1 ∧ W ⊓ centralizer (K : Set G) = ⊥)) :
    BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1 := by
  have h168 := (card_autOn_of_type hKW ho2Z).2.1 hK3
  obtain ⟨m5, m6, mc, -⟩ := card_autOn_of_module (K := K) (W := W)
  rcases hmod with ⟨h5, -⟩ | ⟨h6, -⟩ | ⟨-, -, hc⟩ | ⟨-, hn, -⟩
  · have := m5 h5
    omega
  · have := m6 h6
    omega
  · have := mc hc
    omega
  · exact hn

structure Data13410 (S : A6.Setting134 G T L V) (z : G) (H K W : Subgroup G)
    [IsMulCommutative ↥W] : Prop where
  zV1 : z ∈ fsuV1 T V
  zL : z ∉ centralizer (L : Set G)
  L1TH : L₁Of L (fsuV1 T V) ⊔ T ≤ H
  O2H : pCoreOf 2 H ≠ ⊥
  Hz : H ≤ centralizer ({z} : Set G)
  HM : ¬ H ≤ normalizer (L : Set G)
  KH : K ≤ H
  HK : H ≤ normalizer (K : Set G)
  Kf : quasithinIsFaithfulLocal T K
  KM : ¬ K ≤ normalizer (L : Set G)
  KZV : ¬ K ≤ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G)
  Kz : K ≤ centralizer ({z} : Set G)
  GzK : centralizer ({z} : Set G) ≤ normalizer (K : Set G)
  KJ : ⁅K, thompsonJ T⁆ = K
  Ktype : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
    LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K
  M4 : normalizer (L : Set G) = L ⊔ T ∨ A6.IsHatA6 L
  Wirr : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W
  TW : T ≤ normalizer (W : Set G)
  fsu : FSU G T K W
  Wcl : W = conjClosure (quasithinOmegaOneCenter T ⊓ W) K
  mod : (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
    (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
    (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
      FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥) ∨
    (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
      BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1 ∧ W ⊓ centralizer (K : Set G) = ⊥)
  o2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)

theorem exists_data13410 (h1345 : Stmt13_4_5) (h1346 : Stmt13_4_6) (S : A6.Setting134 G T L V)
    {z : G} {H : Subgroup G} (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
    (hHz : U3.InHz T L V z H) (hns : ¬ Group.IsSolvable ↥H) {K : Subgroup G}
    (hK : K ∈ cComp H) :
    ∃ (W : Subgroup G) (_ : IsMulCommutative ↥W), Data13410 S z H K W := by
  obtain ⟨-, h6, hM4⟩ := h1346 G T L V S z H hz hzL hHz hns
  obtain ⟨⟨-, hKf⟩, hHK, hKM, -, hKZV, hKz, hGzK, hKJ⟩ := h6 K hK
  have hInH : InH T H := ⟨le_sup_right.trans hHz.1.1, hHz.1.2⟩
  obtain ⟨-, h5⟩ := h1345 G T L V S H hInH hHz.2.2 hns
  obtain ⟨-, -, hKtype, -, -, -, -, ⟨W, hW⟩, hall⟩ := h5 K hK
  obtain ⟨hTW, hfsu, hWcl, ⟨hab, hmod⟩, ho2Z, -⟩ := hall W hW
  have hM : normalizer (L : Set G) = L ⊔ T ∨ A6.IsHatA6 L := by
    rcases hM4 with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  exact ⟨W, hab, hz, hzL, hHz.1.1, hHz.1.2, hHz.2.1, hHz.2.2, le_of_mem_cComp hK, hHK, hKf, hKM,
    hKZV, hKz, hGzK, hKJ, hKtype, hM, hW, hTW, hfsu, hWcl, hmod, ho2Z⟩

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem T_le_K : T ≤ normalizer (K : Set G) := (le_sup_right.trans D.L1TH).trans D.HK

theorem isSylowTwoOf : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, D.Kf.1.1, D.Kf.1.2.2.1⟩

theorem charTwo : CharTwo (K ⊔ T) := U3.s134_charTwo_of_inH S ⟨le_sup_right, D.Kf.1.2.2.2⟩

theorem L1_le_K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G) :=
  (le_sup_left.trans D.L1TH).trans D.HK

theorem exists_inH : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G) :=
  ⟨H, ⟨le_sup_right.trans D.L1TH, D.O2H⟩, D.HM⟩

theorem W_le_T : W ≤ T :=
  (D.Wirr.1.trans (R2_le_pCoreOf (K ⊔ T))).trans
    (EscapingLocal.pCoreOf_le_of_isSylowTwoOf D.isSylowTwoOf)

theorem isSylowTwoOf_inf : IsSylowTwoOf (T ⊓ K) K :=
  A4.isSylowTwoOf_inf_normal D.isSylowTwoOf le_sup_left (sup_le le_normalizer D.T_le_K)

theorem sq_eq_one {w : G} (hw : w ∈ W) : w ^ 2 = 1 :=
  (twoReduced_R2 (K ⊔ T)).2.2.1.2 w (D.Wirr.1 hw)

theorem L1_le_W (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G)) :
    L₁Of L (fsuV1 T V) ≤ normalizer (W : Set G) := by
  rw [D.Wcl]
  refine le_normalizer_conjClosure_of D.L1_le_K fun x hx a ha => ?_
  rw [← mem_centralizer_iff.mp (hL1Z hx) a (mem_inf.1 ha).1, mul_inv_cancel_right]

theorem normalizer_W_le (h1332 : Stmt13_3_2) :
    normalizer (W : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨-, ⟨-, -, -, huniqK⟩, -, -⟩ := h1332 G T L S.h13 K D.Kf
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
    (⟨W, D.Wirr.2.1, S.h13.sylow.1.to_le D.W_le_T, rfl⟩ : IsTwoLocal (normalizer (W : Set G)))
  have := huniqK M' hM' ((sup_le D.Wirr.2.2.1 D.TW).trans hle)
  exact this ▸ hle

theorem not_le_centralizer_R2 :
    ¬ K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) := by
  intro h
  apply D.KZV
  have hZV : V ⊓ centralizer (L : Set G) ≤ reducedAggregate (K ⊔ T) :=
    ((S.ZV_le_ZL.trans inf_le_left).trans (le_conjClosure _ K)).trans
      (vH_le_R2 D.isSylowTwoOf D.charTwo D.T_le_K)
  exact h.trans (centralizer_le (SetLike.coe_subset_coe.mpr hZV))

theorem pCoreOf_le_R2 : pCoreOf 2 K ≤ centralizer (reducedAggregate (K ⊔ T) : Set G) :=
  (LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
    ((sup_le le_normalizer D.T_le_K).trans
      (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
    (LieType.BorelTits.pCoreOf_isPGroup 2 K)).trans (pCoreOf_le_centralizer_R2 (K ⊔ T))

theorem card_autOn_R2_le : Nat.card ↥(autOn K (reducedAggregate (K ⊔ T))) ≤ 1080 := by
  have hdvd := A6.card_autOn_dvd_quot (le_sup_left.trans (twoReduced_R2 (K ⊔ T)).2.1)
    D.pCoreOf_le_R2
  obtain ⟨c5, c3, c6, cH⟩ := card_quot_of_type K
  have hle : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) ≤ 1080 := by
    rcases D.Ktype with h | h | h | h
    · rw [c5 h]
      norm_num
    · rw [c3 h]
      norm_num
    · rw [c6 h]
      norm_num
    · rw [cH h]
  exact (Nat.le_of_dvd Nat.card_pos hdvd).trans hle

theorem vK_ne_bot : ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ≠ ⊥ := by
  intro h
  apply D.KZV
  have h1 : K ≤ centralizer (conjClosure (quasithinOmegaOneCenter T) K : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp h)
  exact h1.trans (centralizer_le (SetLike.coe_subset_coe.mpr
    ((S.ZV_le_ZL.trans inf_le_left).trans (le_conjClosure _ K))))

theorem Z_le_vK :
    quasithinOmegaOneCenter T ≤
      ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ ⊔ U3.cZ T K := by
  rw [← vH_eq_sup D.isSylowTwoOf D.charTwo D.T_le_K]
  exact le_conjClosure _ K

theorem split (h56 : AsB56) :
    ∃ _ : IsMulCommutative ↥(reducedAggregate (K ⊔ T)),
      commV (autOn K (reducedAggregate (K ⊔ T))) ∈
          IrrPlus (autOn K (reducedAggregate (K ⊔ T))) ⊤ ∨
        B51Case1ii (ffJ (autOn (K ⊔ T) (reducedAggregate (K ⊔ T))))
          (autOn K (reducedAggregate (K ⊔ T))) := by
  obtain ⟨hab, -, hcases⟩ := b51Part1_K h56 S D.Kf D.T_le_K D.fsu.quasisimple
    D.not_le_centralizer_R2 D.KJ
  refine ⟨hab, ?_⟩
  have h6048 : Nat.card ↥(autOn K (reducedAggregate (K ⊔ T))) ≤ 6048 :=
    D.card_autOn_R2_le.trans (by norm_num)
  rcases hcases with h | h | h | h
  · exact Or.inl h.1
  · exact Or.inr h
  · exact absurd h (U3.not_case1iii_iv h6048).1
  · exact absurd h (U3.not_case1iii_iv h6048).2

theorem comm_eq_of_irr [IsMulCommutative ↥(reducedAggregate (K ⊔ T))]
    (hi : commV (autOn K (reducedAggregate (K ⊔ T))) ∈
      IrrPlus (autOn K (reducedAggregate (K ⊔ T))) ⊤) :
    ⁅reducedAggregate (K ⊔ T), K⁆ = W ∧
      ⁅reducedAggregate (K ⊔ T), K⁆ = ⁅conjClosure (quasithinOmegaOneCenter T) K, K⁆ :=
  ⟨U3.eq_of_irrPlus (le_sup_left.trans (twoReduced_R2 (K ⊔ T)).2.1) hi D.Wirr.1 D.Wirr.2.2.1
      D.Wirr.2.2.2.1 D.Wirr.2.1,
    comm_R2_eq_vK D.isSylowTwoOf D.charTwo D.T_le_K D.Kf.1.2.1.2.1 hi D.vK_ne_bot⟩

theorem W_le_comm : W ≤ ⁅reducedAggregate (K ⊔ T), K⁆ := by
  have h := commutator_mono D.Wirr.1 (le_refl K)
  rwa [D.Wirr.2.2.2.1] at h

theorem Z_le_comm :
    quasithinOmegaOneCenter T ≤ ⁅reducedAggregate (K ⊔ T), K⁆ ⊔ U3.cZ T K :=
  D.Z_le_vK.trans (sup_le_sup_right (vK_le_comm D.isSylowTwoOf D.charTwo D.T_le_K) _)

theorem not_hat (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) : ¬ A6.IsHatA6 L := by
  intro hhat
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S D.exists_inH
  obtain ⟨hab2, hi | hii⟩ := D.split h56
  · obtain ⟨hWR, hVK⟩ := D.comm_eq_of_irr hi
    have hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K := by
      have h := D.Z_le_vK
      rwa [← hVK, hWR] at h
    exact not_isHatA6_of_irr hC137 h1332 h1228 S D.Kf D.KM D.L1_le_K hL1Z (D.L1_le_W hL1Z)
      D.Wirr D.TW hZW D.o2Z (match13410 D.Wirr.2.2.1 D.o2Z D.Ktype D.mod) hhat
  · have hK3 := l32_of_case1ii (le_sup_left.trans (twoReduced_R2 (K ⊔ T)).2.1)
      D.pCoreOf_le_R2 hii D.Ktype
    exact not_case1ii_of_hat h1332 h1228 S hhat D.Kf D.KM D.L1_le_K hK3
      (nat_of_l32 D.Wirr.2.2.1 D.o2Z hK3 D.mod) D.Wirr.2.2.1 D.TW D.W_le_comm D.o2Z hii
      D.Z_le_comm

end Data13410

end CFSG.Quasithin.H13.NQS134
