module

public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Background.B6Basic
public import CFSG.Quasithin.Background.C126NatDProd
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Background.E6Hyp
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.E6
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {T M V : Subgroup G}

theorem exists_central_of_normalized {T V : Subgroup G} (hT : IsPGroup 2 ↥T) (hVT : V ≤ T)
    (hV : V ≠ ⊥) (hTV : T ≤ Subgroup.normalizer (V : Set G)) :
    ∃ v ∈ V, v ≠ 1 ∧ ∀ t ∈ T, t * v = v * t := by
  classical
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  have hVn : (V.subgroupOf T).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hV1 : V.subgroupOf T ≠ ⊥ := by
    intro hb
    apply hV
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hVT hx⟩ : ↥T) ∈ V.subgroupOf T := hx
    rw [hb, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hV1
  obtain ⟨⟨⟨v, hvT⟩, hvmem⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  refine ⟨v, Subgroup.mem_subgroupOf.mp hvmem.1, fun h => hv1 (Subtype.ext (Subtype.ext h)),
    fun t ht => ?_⟩
  have := Subgroup.mem_center_iff.mp hvmem.2 ⟨t, ht⟩
  exact congrArg Subtype.val this

theorem mem_M_of_commute (h : HypE61 T M V)
    (hC : ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G))
    {v x : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hx : x * v = v * x) : x ∈ M := by
  have hU : Subgroup.zpowers v ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hv1
  have hxC : x ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    exact ((Commute.zpow_left (show Commute v x from hx.symm) n).eq)
  exact h.normalizer_le (hC _ (Subgroup.zpowers_le.2 hv) hU hxC)

theorem exists_central_mem_V (h : HypE61 T M V) :
    ∃ v ∈ V, v ≠ 1 ∧ v ∈ quasithinOmegaOneCenter T := by
  obtain ⟨v, hv, hv1, hvc⟩ := exists_central_of_normalized (T := T) (V := V)
    (h.sylow.1) h.le h.ne_bot h.normal
  refine ⟨v, hv, hv1, Subgroup.subset_closure ⟨⟨h.le hv, ?_⟩, ?_⟩⟩
  · refine Subgroup.mem_centralizer_iff.2 fun t ht => hvc t ht
  · have := h.isElemAbelian.2 v hv
    exact this

theorem centralizer_le_M_of_omegaOneCenter_le (h : HypE61 T M V)
    (hC : ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G))
    {U : Subgroup G} (hZU : quasithinOmegaOneCenter T ≤ U) :
    Subgroup.centralizer (U : Set G) ≤ M := by
  obtain ⟨v, hv, hv1, hvZ⟩ := exists_central_mem_V h
  intro x hx
  exact mem_M_of_commute h hC hv hv1 (Subgroup.mem_centralizer_iff.1 hx v (hZU hvZ)).symm

theorem exists_isHStar_of_inM (h : HypE61 T M V) {M' : Subgroup G} (hM' : InM T M')
    (hne : M' ≠ M) : ∃ H : Subgroup G, IsHStar T M H := by
  have hM'M : ¬ M' ≤ M := fun hle => hne (hM'.1.2 M h.inM.1.1 hle).symm
  obtain ⟨H, ⟨hH1, hH2⟩, hmin⟩ := WellFounded.has_min wellFounded_lt
    {H : Subgroup G | InH T H ∧ ¬ H ≤ M} ⟨M', inH_of_inM hM', hM'M⟩
  exact ⟨H, hH1, hH2, fun Y hY hYH hYM => by_contra fun hne' =>
    hmin Y ⟨hY, hYM⟩ (lt_of_le_of_ne hYH hne')⟩

omit [Finite G] in
theorem normalizer_le_of_char {Q C : Subgroup G} (hCQ : C ≤ Q)
    (hchar : (C.subgroupOf Q).Characteristic) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (C : Set G) := by
  have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (C.subgroupOf Q)
  rwa [Subgroup.map_subgroupOf_eq_of_le hCQ] at h

theorem le_of_isMaxElemAbelian (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) {A : Subgroup G}
    (hA : IsMaxElemAbelian T A) : V ≤ A := by
  have hAJ : A ≤ thompsonJ T := B6.le_thompsonJ hA
  have hcomm : ∀ v ∈ V, ∀ a ∈ A, v * a = a * v := fun v hv a ha =>
    (Subgroup.mem_centralizer_iff.1 (hJ (hAJ ha)).2 v hv)
  have hB := B2F.isElemAbelian_sup_of_commute h.isElemAbelian hA.2.1 hcomm
  have hBT : V ⊔ A ≤ T := sup_le h.le hA.1
  have hAB : A = V ⊔ A := Subgroup.eq_of_le_of_card_ge le_sup_right (hA.2.2 _ hBT hB)
  exact le_sup_left.trans hAB.symm.le

theorem le_thompsonJ_of_le (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) : V ≤ thompsonJ T := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  exact (le_of_isMaxElemAbelian h hJ hA).trans (B6.le_thompsonJ hA)

theorem le_omegaOneCenterOf_thompsonJ (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    V ≤ omegaOneCenterOf (thompsonJ T) := by
  intro v hv
  refine Subgroup.subset_closure ⟨⟨le_thompsonJ_of_le h hJ hv, ?_⟩, h.isElemAbelian.2 v hv⟩
  refine Subgroup.mem_centralizer_iff.2 fun j hj => ?_
  exact (Subgroup.mem_centralizer_iff.1 (hJ hj).2 v hv).symm

theorem baum_le_Q (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    baum T ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
  inf_le_inf_left T (Subgroup.centralizer_le (le_omegaOneCenterOf_thompsonJ h hJ))

theorem thompsonJ_Q (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    thompsonJ (T ⊓ Subgroup.centralizer (V : Set G)) = thompsonJ T :=
  B6.thompsonJ_eq_of_le hJ inf_le_left

theorem baum_Q (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    baum (T ⊓ Subgroup.centralizer (V : Set G)) = baum T :=
  (baum_eq_of_le (baum_le_Q h hJ) inf_le_left).symm

theorem normalizer_le_M_of_le (h : HypE61 T M V) {X : Subgroup G} (hX1 : X ≠ ⊥)
    (hX2 : IsPGroup 2 X)
    (hle : Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (X : Set G)) : Subgroup.normalizer (X : Set G) ≤ M :=
  (h.isUniqueM_of_le hX1 hX2 (inf_le_left.trans hle)).1.2

theorem normalizer_thompsonJ_le_M (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    Subgroup.normalizer (thompsonJ T : Set G) ≤ M := by
  refine normalizer_le_M_of_le h ?_ (h.sylow.1.to_le (B6.thompsonJ_le T)) ?_
  · intro hb
    exact h.ne_bot (le_bot_iff.1 (hb ▸ le_thompsonJ_of_le h hJ))
  · exact (normalizer_le_normalizer_thompsonJ _).trans (by rw [thompsonJ_Q hJ])

theorem normalizer_T_le_M (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    Subgroup.normalizer (T : Set G) ≤ M :=
  (normalizer_le_normalizer_thompsonJ T).trans (normalizer_thompsonJ_le_M h hJ)

theorem normalizer_baum_le_M (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    Subgroup.normalizer (baum T : Set G) ≤ M := by
  have hB1 : baum T ≠ ⊥ := fun hb =>
    h.ne_bot (le_bot_iff.1 (hb ▸ (le_thompsonJ_of_le h hJ).trans (B2F.thompsonJ_le_baum T)))
  refine normalizer_le_M_of_le h hB1 (h.sylow.1.to_le inf_le_left) ?_
  exact (normalizer_le_normalizer_baum _).trans (by rw [baum_Q h hJ])

theorem normalizer_char_le_M (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) {C : Subgroup G}
    (hCS : C ≤ baum T) (hC0 : C ≠ ⊥) (hchar : (C.subgroupOf (baum T)).Characteristic) :
    Subgroup.normalizer (C : Set G) ≤ M := by
  refine normalizer_le_M_of_le h hC0 (h.sylow.1.to_le (hCS.trans inf_le_left)) ?_
  exact (normalizer_le_normalizer_baum _).trans
    ((by rw [baum_Q h hJ]) : Subgroup.normalizer (baum (T ⊓ Subgroup.centralizer (V : Set G)) : Set G) ≤
      Subgroup.normalizer (baum T : Set G)) |>.trans (normalizer_le_of_char hCS hchar)

section HStar

variable {H : Subgroup G}

theorem isHStar_charTwo (h : HypE61 T M V) (hH : IsHStar T M H) : CharTwo H :=
  charTwo_of_inH' h.qtke h.sylow hH.1

theorem isHStar_sylow (h : HypE61 T M V) (hH : IsHStar T M H) : IsSylowTwoOf T H :=
  isSylowTwoOf_of_isSylowTwo h.sylow hH.1.1

theorem isHStar_sqtk (h : HypE61 T M V) (hH : IsHStar T M H) : IsSQTKSub H :=
  isSQTKSub_of_inH h.qtke h.simple h.nonabelian hH.1

theorem isHStar_uniqueMax (h : HypE61 T M V) (hH : IsHStar T M H) :
    IsUniqueMaxOver H T (H ⊓ M) := by
  obtain ⟨S, hS⟩ := exists_sylow_coe_eq h.sylow
  subst hS
  exact hH.isUniqueMaxOver S h.inM.2

theorem isHStar_minParabolic (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) (hH : IsHStar T M H) :
    MinParabolic H T (H ⊓ M) :=
  ⟨isHStar_sylow h hH, hH.not_le_normalizer (normalizer_T_le_M h hJ), isHStar_uniqueMax h hH⟩

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer' (U : Subgroup G) :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ Subgroup.normalizer (U : Set G), ∀ c ∈ Subgroup.centralizer (U : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro s hs
    have hs' : g⁻¹ * s * g ∈ U := (Subgroup.mem_normalizer_iff''.mp hg s).mp hs
    have h := hc _ hs'
    calc s * (g * c * g⁻¹) = g * ((g⁻¹ * s * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * s * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * s := by group
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ hc

theorem not_thompsonJ_le_centralizer_VZ (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G))
    (hC : ∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
      Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hH : IsHStar T M H) : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G) := by
  intro hJU
  have hF := isHStar_charTwo h hH
  have hsyl := isHStar_sylow h hH
  have hred : IsTwoReducedIn H (VZ T H) := C1GN.isTwoReducedIn_VZ hF hsyl
  have hUel : IsElemAbelian 2 (VZ T H) := hred.2.2.1
  have hUT : VZ T H ≤ T :=
    (MinParabolic.le_pCoreOf_of_isTwoReduced hred).trans (B6.pCoreOf_two_le_of_isSylowTwoOf hsyl)
  have hJ' : thompsonJ T ≤ T ⊓ Subgroup.centralizer (VZ T H : Set G) :=
    le_inf (B6.thompsonJ_le T) hJU
  have hbaum : baum T = baum (T ⊓ Subgroup.centralizer (VZ T H : Set G)) :=
    baum_eq_baum_centralizer hUel hUT hJ'
  have hHX : H ≤ Subgroup.normalizer ((H ⊓ Subgroup.centralizer (VZ T H : Set G) : Subgroup G) :
      Set G) := by
    intro g hg
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, ?_⟩
    exact normalizer_le_normalizer_centralizer' _ (hred.2.1 hg)
  have hSyl : IsSylowTwoOf (T ⊓ Subgroup.centralizer (VZ T H : Set G))
      (H ⊓ Subgroup.centralizer (VZ T H : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal hsyl (inf_le_left : H ⊓ Subgroup.centralizer (VZ T H : Set G) ≤ H) hHX
    rwa [← inf_assoc, inf_eq_left.2 hsyl.1] at this
  apply hH.2.1
  intro x hx
  obtain ⟨n, hn, m, hm, rfl⟩ := C126.Nat.exists_mul_normalizer_of_sylow hSyl (hHX hx)
  have hnM : n ∈ M := centralizer_le_M_of_omegaOneCenter_le h hC (le_conjClosure _ _) hn.2
  have hmM : m ∈ M := by
    have h1 : Subgroup.normalizer ((T ⊓ Subgroup.centralizer (VZ T H : Set G) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (baum T : Set G) := by
      rw [hbaum]
      exact normalizer_le_normalizer_baum _
    exact normalizer_baum_le_M h hJ (h1 hm)
  exact M.mul_mem hnM hmM

end HStar

theorem T_le_normalizer_Q (h : HypE61 T M V) :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro g hg
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
    normalizer_le_normalizer_centralizer' _ (h.normal hg)⟩

theorem isSylowTwoOf_sup_of_le {N S Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hSQ : S ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (N : Set G)) (hS : IsSylowTwoOf S (N ⊔ S)) :
    IsSylowTwoOf Q (N ⊔ Q) := by
  refine ⟨le_sup_right, hQ2, ?_⟩
  have h1 : (Q ⊓ N).relIndex N = Q.relIndex (Q ⊔ N) := B6.relIndex_inf_eq_relIndex_sup hQN
  have h2 : (S ⊓ N).relIndex N = S.relIndex (S ⊔ N) :=
    B6.relIndex_inf_eq_relIndex_sup (hSQ.trans hQN)
  have h3 := Subgroup.relIndex_mul_relIndex (S ⊓ N) (Q ⊓ N) N (inf_le_inf_right N hSQ) inf_le_right
  intro hd
  apply hS.2.2
  rw [sup_comm] at hd
  have hd' : 2 ∣ (Q ⊓ N).relIndex N := by rw [h1]; exact hd
  have : 2 ∣ S.relIndex (S ⊔ N) := by
    rw [← h2, ← h3]
    exact Dvd.dvd.mul_left hd' _
  rw [sup_comm]
  exact this

theorem false_of_sylow_baum (hC58 : TheoremC58) (h : HypE61 T M V)
    (hJ : thompsonJ T ≤ T ⊓ Subgroup.centralizer (V : Set G)) {H : Subgroup G}
    (hH : IsHStar T M H) (hS : IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T)) : False := by
  set Q : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G) with hQdef
  have hSQ : baum T ≤ Q := baum_le_Q h hJ
  have hQT : Q ≤ T := inf_le_left
  have hQ2 : IsPGroup 2 Q := h.sylow.1.to_le hQT
  have hQ1 : Q ≠ ⊥ := h.Q_ne_bot
  have hQN : Q ≤ Subgroup.normalizer (twoResidual H : Set G) :=
    hQT.trans ((hH.1.1).trans (le_normalizer_twoResidual H))
  have hQsyl : IsSylowTwoOf Q (oTwoUpper H ⊔ Q) := by
    rw [← F6.twoResidual_eq_oTwoUpper]
    exact isSylowTwoOf_sup_of_le hQ2 hSQ hQN hS
  have hTM0 : T ≤ Subgroup.normalizer (Q : Set G) := T_le_normalizer_Q h
  have hM₀ : InH T (Subgroup.normalizer (Q : Set G)) := by
    refine ⟨hTM0, fun hb => hQ1 (le_bot_iff.1 ?_)⟩
    rw [← hb]
    exact CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 Q hQ2
  obtain ⟨R₀, hR₀1, hR₀Q, hR₀N⟩ := theorem311_of_C58 hC58 h.simple h.nonabelian h.qtke h.sylow
    hM₀ hH.1 ⟨H ⊓ M, isHStar_uniqueMax h hH⟩ hQ1 hQT hQsyl le_rfl
  have hHN : H ≤ Subgroup.normalizer (R₀ : Set G) := le_sup_right.trans hR₀N
  have hN₀ : Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (R₀ : Set G) :=
    le_sup_left.trans hR₀N
  have hNM := normalizer_le_M_of_le h hR₀1 (hQ2.to_le hR₀Q) hN₀
  exact hH.2.1 (hHN.trans hNM)

end CFSG.Quasithin.RonanE628
