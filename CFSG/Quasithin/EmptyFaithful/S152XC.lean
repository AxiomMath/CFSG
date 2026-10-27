module

public import CFSG.Quasithin.EmptyFaithful.S152XB
public import CFSG.Quasithin.EmptyFaithful.S152He9R
public import CFSG.Quasithin.EmptyFaithful.SzN22Basic

public section

namespace CFSG.Quasithin.S152X

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.He9 (isQuasithinSub_of)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rcOf_le_M {Mc M : Subgroup G} : rcOf Mc M ≤ M := (pCoreOf_le 2 (Mc ⊓ M)).trans inf_le_right

structure S5Ctx (T Mc M H Y₁ : Subgroup G) (φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)) : Prop where
  hs : Setting152 T Mc M
  hH : IsHStar T M H
  c1515 : Lemma1515Concl T Mc M
  c1519 : Lemma1519Concl T Mc M
  hY : IsY1 T Mc M Y₁
  c15207 : Lemma15207Concl T Mc M Y₁

namespace S5Ctx

variable {T Mc M H Y₁ : Subgroup G} {φ : OTwoQuot H ≃* Equiv.Perm (Fin 5)} (c : S5Ctx T Mc M H Y₁ φ)

include c

theorem hT : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar c.hs c.hH

theorem inM : InM T M := c.hs.mf.1.1

theorem T_le_M : T ≤ M := c.inM.2

theorem T_pgroup : IsPGroup 2 T := (isSylowTwoOf_of_le151 c.hs.qtfe.sylow c.T_le_M).2.1

theorem T_le_H : T ≤ H := c.hH.1.1

theorem T_le_normalizer_K : T ≤ Subgroup.normalizer (kS5 H φ : Set G) :=
  c.T_le_H.trans (le_normalizer_kS5 H φ)

theorem H_le_Mc : H ≤ Mc :=
  (c.c1519.three H c.hH).1.trans (c.c1519.three H c.hH).2

theorem T_le_normalizer_rc : T ≤ Subgroup.normalizer (rcOf Mc M : Set G) :=
  (le_inf c.hs.qtfe.t_le_mc c.T_le_M).trans (le_normalizer_pCoreOf 2 (Mc ⊓ M))

theorem Y₁_le_M : Y₁ ≤ M := le_sup_left.trans c.hY.unique.1.2

theorem L₁_le_M : Y₁ ⊔ rcOf Mc M ≤ M := sup_le c.Y₁_le_M rcOf_le_M

theorem T_le_normalizer_L₁ : T ≤ Subgroup.normalizer ((Y₁ ⊔ rcOf Mc M : Subgroup G) : Set G) :=
  fun _ hx => Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨c.hY.normalized hx, c.T_le_normalizer_rc hx⟩

theorem sylow_L₁ : IsSylowTwoOf (T ⊓ (Y₁ ⊔ rcOf Mc M)) (Y₁ ⊔ rcOf Mc M) :=
  SzN22.isSylowTwoOf_inf_normalized (isSylowTwoOf_of_le151 c.hs.qtfe.sylow c.T_le_M) c.L₁_le_M
    c.T_le_normalizer_L₁

theorem T_le_normalizer_inf : T ≤ Subgroup.normalizer ((T ⊓ kS5 H φ : Subgroup G) : Set G) :=
  fun _ hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, c.T_le_normalizer_K hx⟩

theorem not_H_le_normalizer_inf :
    ¬ H ≤ Subgroup.normalizer ((T ⊓ kS5 H φ : Subgroup G) : Set G) := by
  intro hHN
  apply not_inf_le_pCoreOf φ c.hT
  rw [← pCoreOf_kS5 H φ]
  exact le_pCoreOf_of_le_normalizer 2 inf_le_right (fun k hk => hHN (kS5_le H φ hk))
    (c.T_pgroup.to_le inf_le_left)

theorem normalizer_inf_le_M :
    H ⊓ Subgroup.normalizer ((T ⊓ kS5 H φ : Subgroup G) : Set G) ≤ H ⊓ M := by
  have hmp := S152L08.minParabolic_of_hStar c.hs c.hH c.c1519.seven_normalizer
  by_contra hne
  have h := hmp.eq_of_not_le (X := H ⊓ Subgroup.normalizer ((T ⊓ kS5 H φ : Subgroup G) : Set G))
    (le_inf c.T_le_H c.T_le_normalizer_inf) inf_le_left hne
  exact c.not_H_le_normalizer_inf (h.symm.le.trans inf_le_right)

theorem borel_K_le_HM : borelOf (kS5 H φ) T ≤ H ⊓ M :=
  fun _ hx => c.normalizer_inf_le_M ⟨kS5_le H φ (Subgroup.mem_inf.1 hx).1, (Subgroup.mem_inf.1 hx).2⟩

theorem borel_K_le_M : borelOf (kS5 H φ) T ≤ M := borel_K_le_HM c |>.trans inf_le_right

theorem T_le_normalizer_borel_K : T ≤ Subgroup.normalizer ((borelOf (kS5 H φ) T : Subgroup G) : Set G) := by
  intro t ht
  refine Subgroup.inf_normalizer_le_normalizer_inf ⟨c.T_le_normalizer_K ht, ?_⟩
  exact Subgroup.le_normalizer (c.T_le_normalizer_inf ht)

theorem borel_K_le_normalizer_rc : borelOf (kS5 H φ) T ≤ Subgroup.normalizer (rcOf Mc M : Set G) := by
  intro x hx
  have hxHM := c.borel_K_le_HM hx
  exact le_normalizer_pCoreOf 2 (Mc ⊓ M) ⟨c.H_le_Mc hxHM.1, hxHM.2⟩

theorem borel_K_le_normalizer_Y₁ :
    borelOf (kS5 H φ) T ≤ Subgroup.normalizer (Y₁ : Set G) := by
  set B := borelOf (kS5 H φ) T with hB
  have hSB : T ⊓ kS5 H φ ≤ B := le_inf inf_le_right Subgroup.le_normalizer
  have hn : B ≤ Subgroup.normalizer ((T ⊓ kS5 H φ : Subgroup G) : Set G) := inf_le_right
  have hp : IsPGroup 2 (T ⊓ kS5 H φ : Subgroup G) := c.T_pgroup.to_le inf_le_left
  have h3 : (T ⊓ kS5 H φ).relIndex B = 3 := relIndex_borel_kS5 φ c.hT
  obtain ⟨hBX, hrel⟩ := oTwoUpper_borel hSB hn hp h3
  have hXMC : oTwoUpper B ≤ M ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :=
    le_inf ((oTwoUpper_le B).trans c.borel_K_le_M)
      ((oTwoUpper_mono c.borel_K_le_HM).trans (c.c1519.four H c.hH))
  have hXbot : oTwoUpper B ≠ ⊥ := by
    intro h
    rw [h] at hrel
    have := Subgroup.relIndex_eq_one.2 (bot_le : (⊥ : Subgroup G) ≤ pCoreOf 2 ⊥)
    omega
  have hXeq : oTwoUpper B = oTwoUpper (oTwoUpper B) := (A4.oTwoUpper_oTwoUpper B).symm
  have hTX : T ≤ Subgroup.normalizer ((oTwoUpper B : Subgroup G) : Set G) :=
    c.T_le_normalizer_borel_K.trans (normalizer_le_normalizer_oTwoUpper B)
  have hXY : oTwoUpper B ≤ Subgroup.normalizer (Y₁ : Set G) :=
    c.c15207.acts (oTwoUpper B) hXbot hXeq hXMC hTX hrel
  exact hBX.trans (sup_le hXY (inf_le_left.trans c.hY.normalized))

theorem borel_K_le_normalizer_L₁ :
    borelOf (kS5 H φ) T ≤ Subgroup.normalizer ((Y₁ ⊔ rcOf Mc M : Subgroup G) : Set G) :=
  fun _ hx => Subgroup.inf_normalizer_le_normalizer_sup _ _
    ⟨c.borel_K_le_normalizer_Y₁ hx, c.borel_K_le_normalizer_rc hx⟩

theorem charTwo_M : CharTwo M := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo c.hs.qtfe.sylow
  exact c.hs.qtfe.qtke.2.1 M c.inM.1.1 ⟨P, hP ▸ c.T_le_M⟩

theorem charTwo_H : CharTwo H := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo c.hs.qtfe.sylow
  subst hP
  exact CFSG.Quasithin.charTwo_of_inH c.hs.qtfe.qtke.2.1 P c.hH.1

theorem hO2 : pCoreOf 2 M ≤ Subgroup.centralizer (V154 T Mc M : Set G) := by
  refine c.c1515.reduced.2.2.2 (pCoreOf 2 M) (pCoreOf_le 2 M) (le_normalizer_pCoreOf 2 M)
    fun d hd => ?_
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 M) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

theorem O2M_le_rc : pCoreOf 2 M ≤ rcOf Mc M := by
  have hle : pCoreOf 2 M ≤ Mc ⊓ M := le_inf (c.hO2.trans c.c1515.centralizer_le) (pCoreOf_le 2 M)
  exact le_pCoreOf_of_le_normalizer 2 hle (inf_le_right.trans (le_normalizer_pCoreOf 2 M))
    (pCoreOf_isPGroup 2 M)

theorem charTwo_L₁TB : CharTwo ((Y₁ ⊔ rcOf Mc M) ⊔ T ⊔ borelOf (kS5 H φ) T) := by
  refine charTwo_of_pCore_centralizer_le c.charTwo_M ?_ ?_
  · exact sup_le (sup_le c.L₁_le_M c.T_le_M) c.borel_K_le_M
  · exact inf_le_left.trans (c.O2M_le_rc.trans (le_sup_right.trans (le_sup_left.trans le_sup_left)))

theorem o2_eq_bot : pCoreOf 2 ((Y₁ ⊔ rcOf Mc M) ⊔ kS5 H φ ⊔ T) = ⊥ := by
  by_contra hne
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hne
  have hYT : Y₁ ⊔ T ≤ (Y₁ ⊔ rcOf Mc M) ⊔ kS5 H φ ⊔ T :=
    sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right
  have hMM' : M' = M := c.hY.unique.2 M' ⟨hM'.1, hYT.trans hM'.2⟩
  have hHle : H ≤ M := by
    rw [← sup_kS5_eq φ c.hT, ← hMM']
    exact sup_le (le_sup_right.trans (le_sup_left.trans hM'.2)) (le_sup_right.trans hM'.2)
  exact c.hH.2.1 hHle

end S5Ctx

end CFSG.Quasithin.S152X
