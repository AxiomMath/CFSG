module

public import CFSG.Quasithin.H13.L32AL3c

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G} {t₀ : G}

namespace TopCtx

variable {X : TopCtx T L V K (fsuV1 T V) t₀} [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]

omit [IsMulCommutative ↥(conjClosure V (A6.g1 T V))] in
theorem comm_mem_pCore_l1 (S : Setting147 G T L V (A6.g1 T V)) (h1332 : Stmt13_3_2) {a b : G}
    (ha : a ∈ l1 T L V) (hb : b ∈ pCoreOf 2 (l1 T L V ⊔ T)) :
    a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 (l1 T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL := Setting147.T_le_N_l1 S h1332
  have hRT : pCoreOf 2 (l1 T L V ⊔ T) ≤ T := Setting147.R1_le_T S
  have hRN : l1 T L V ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hle : l1 T L V ⊓ pCoreOf 2 (l1 T L V ⊔ T) ≤ pCoreOf 2 (l1 T L V) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun l hl => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hl, (le_sup_left.trans hRN) hl⟩)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
  refine hle ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ l1 T L V :=
      (Subgroup.mem_normalizer_iff.mp (hTL (hRT hb)) _).mp ((l1 T L V).inv_mem ha)
    have := (l1 T L V).mul_mem ha h1
    simpa [mul_assoc] using this
  · have h1 : a * b * a⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hRN (Subgroup.mem_sup_left ha)) _).mp hb
    exact (pCoreOf 2 (l1 T L V ⊔ T)).mul_mem h1 ((pCoreOf 2 (l1 T L V ⊔ T)).inv_mem hb)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem l2Cfg (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6)
    (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14)
    (hF4 : Nat.card F = 4) (e : Hat V (A6.g1 T V) (fsuV1 T V) ≃* VM F)
    (he1 : (X.img (conjClosure K T)).map (MulAut.congr e).toMonoidHom = (rho (K := F)).range)
    (he2 : ∀ f ∈ X.img (A6.g1 T V), MulAut.congr e f ∈
      Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))))
    (he3 : (X.img T).map (MulAut.congr e).toMonoidHom ⊓ (rho (K := F)).range = sZero)
    {t : ↥(A6.g1 T V)} (htR : (t : G) ∈ pCoreOf 2 (l1 T L V ⊔ T)) (ht2 : t * t = 1)
    (ht1 : X.top.act t ≠ 1)
    (hidx : ((Subgroup.centralizer ({(t : G)} : Set G)).subgroupOf
      (conjClosure V (A6.g1 T V))).index ≤ 4)
    {D : Subgroup G} (hD : (D.subgroupOf (conjClosure V (A6.g1 T V))).index ≤ 2)
    {z : G} (hzU : z ∈ conjClosure V (A6.g1 T V))
    (hDt : ∀ d ∈ D, d ∈ conjClosure V (A6.g1 T V) →
      (t : G) * d * (t : G)⁻¹ * d⁻¹ = 1 ∨ (t : G) * d * (t : G)⁻¹ * d⁻¹ = z) :
    L2Cfg F ((X.img (A6.g1 T V)).map (MulAut.congr e).toMonoidHom)
      ((X.img T).map (MulAut.congr e).toMonoidHom)
      ((X.img (l1 T L V)).map (MulAut.congr e).toMonoidHom)
      ((X.img (pCoreOf 2 (l1 T L V ⊔ T))).map (MulAut.congr e).toMonoidHom)
      ((X.img (pCoreOf 2 (l1 T L V))).map (MulAut.congr e).toMonoidHom)
      ((vHat V (A6.g1 T V) (fsuV1 T V)).map e.toMonoidHom) (MulAut.congr e (X.top.act t))
      (e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V)))
        ⟨z, hzU⟩)) := by
  have S := X.R.S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hV8, hLTV, hV12, -⟩ :=
    stmtL32NModule_of_inputs h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hL1L : l1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hLV : l1 T L V ≤ Subgroup.normalizer (V : Set G) := (hL1L.trans le_sup_left).trans hLTV
  have hTH : T ≤ A6.g1 T V := Setting147.TH' S
  have hL1H : l1 T L V ≤ A6.g1 T V := Setting147.l1H' S
  have hRT : pCoreOf 2 (l1 T L V ⊔ T) ≤ T := Setting147.R1_le_T S
  have hQR : pCoreOf 2 (A6.g1 T V) ≤ pCoreOf 2 (l1 T L V ⊔ T) := Setting147.O2H_le_R1 S
  have hOR : pCoreOf 2 (l1 T L V) ≤ pCoreOf 2 (l1 T L V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 _)
        ((Setting147.T_le_N_l1 S h1332).trans (normalizer_le_normalizer_pCoreOf 2 _)))
      (pCoreOf_isPGroup 2 _)
  have hRN : l1 T L V ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 _
  have hΦi : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hR1T : (pCoreOf 2 (l1 T L V ⊔ T)).relIndex T = 2 := by
    have hMod := stmtL32NModule_of_inputs h1332 h1334
    have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
    obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
    have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
    have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
    exact hl1eq ▸ S14.index2_eq
  have hnorm : ∀ {A B : Subgroup G}, A ≤ Subgroup.normalizer (B : Set G) →
      (X.img A).map (MulAut.congr e).toMonoidHom ≤ Subgroup.normalizer
        (((X.img B).map (MulAut.congr e).toMonoidHom : Subgroup (MulAut (VM F))) :
          Set (MulAut (VM F))) := fun h =>
    (Subgroup.map_mono (map_subgroupOf_le_normalizer X.top.act h)).trans
      (Subgroup.le_normalizer_map _)
  have hstab : ∀ {A : Subgroup G}, A ≤ Subgroup.normalizer (V : Set G) →
      ∀ x ∈ (X.img A).map (MulAut.congr e).toMonoidHom,
        ∀ v ∈ (vHat V (A6.g1 T V) (fsuV1 T V)).map e.toMonoidHom,
          x v ∈ (vHat V (A6.g1 T V) (fsuV1 T V)).map e.toMonoidHom := by
    intro A hA x hx v hv
    obtain ⟨a, haA, rfl⟩ := (mem_map_img_iff e).mp hx
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨X.top.act a w, X.act_mem_vHat (hA haA) hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    exact (congr_apply_e e _ w).symm
  have hsN : MulAut.congr e (X.top.act t) ∈
      Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))) :=
    he2 _ (act_mem_img t t.2)
  have hs2 : MulAut.congr e (X.top.act t) * MulAut.congr e (X.top.act t) = 1 := by
    rw [← map_mul (MulAut.congr e), ← map_mul X.top.act, ht2, map_one, map_one]
  have hs1 : MulAut.congr e (X.top.act t) ≠ 1 := fun h =>
    ht1 ((MulAut.congr e).injective (by rw [map_one]; exact h))
  have hsc : Nat.card (commHom (MulAut.congr e (X.top.act t))).range ≤ 4 := by
    rw [card_range_commHom_congr]
    exact X.card_range_le_of_index hidx
  have hDe : (((D.subgroupOf (conjClosure V (A6.g1 T V))).map (InternalSec.secMk
      ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))))).map e.toMonoidHom).index ≤ 2 := by
    rw [Subgroup.index_map_of_bijective e.bijective]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd _ (InternalSec.secMk_surjective _))).trans hD
  obtain ⟨d, hd, hd1⟩ := exists_comm_ne_one hF4 hsN hs2 hs1 hsc hDe
  obtain ⟨_, ⟨u, hu, rfl⟩, rfl⟩ := hd
  rw [MulEquiv.coe_toMonoidHom, commHom_congr_apply, X.commHom_act_secMk] at hd1
  have ha : commHom (MulAut.congr e (X.top.act t)) (e (InternalSec.secMk
      ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) u)) =
      e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨z, hzU⟩) := by
    rw [commHom_congr_apply, X.commHom_act_secMk]
    rcases hDt u (Subgroup.mem_subgroupOf.mp hu) u.2 with h | h
    · exfalso
      apply hd1
      rw [show commHom (Setup.rho (conjClosure V (A6.g1 T V)) (A6.g1 T V)
          (le_normalizer_conjClosure V (A6.g1 T V)) t) u = 1 from
        Subtype.ext (by rw [coe_commHom_rho]; exact h), map_one, map_one]
    · congr 2
      exact Subtype.ext (by rw [coe_commHom_rho]; exact h)
  have hd1' : commHom (MulAut.congr e (X.top.act t)) (e (InternalSec.secMk
      ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) u)) ≠ 1 := by
    rw [commHom_congr_apply, X.commHom_act_secMk]
    exact hd1
  refine
    { card := hF4
      hN := by
        rintro _ ⟨f, hf, rfl⟩
        exact he2 f hf
      hTH := Subgroup.map_mono X.img_T_le
      hT2 := fun x hx => by
        have hP : IsPGroup 2 ((X.img T).map (MulAut.congr e).toMonoidHom) :=
          X.isSylowTwoOf_img_T.2.1.map _
        obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
        refine ⟨k, ?_⟩
        have := congrArg Subtype.val hk
        rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at this
      hS0 := he3
      hTV := hstab hTV
      hLK := by
        rw [← he1]
        exact Subgroup.map_mono (X.img_mono X.R.hl1)
      hLV := hstab hLV
      hLT := hnorm (Setting147.T_le_N_l1 S h1332)
      hL3 := ?_
      hOL := Subgroup.map_mono (X.img_mono (pCoreOf_le 2 _))
      hO2 := fun x hx => by
        obtain ⟨f, hf, rfl⟩ := hx
        obtain ⟨k, hk⟩ := exists_pow_of_mem_map X.top.act (pCoreOf_isPGroup 2 (l1 T L V)) hf
        exact ⟨k, by rw [← map_pow, hk, map_one]⟩
      hLR := by
        intro l hl r hr
        obtain ⟨a, haL, rfl⟩ := (mem_map_img_iff e).mp hl
        obtain ⟨b, hbR, rfl⟩ := (mem_map_img_iff e).mp hr
        refine (mem_map_img_iff e).mpr ⟨a * b * a⁻¹ * b⁻¹, ?_, by
          simp only [map_mul, map_inv]⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact comm_mem_pCore_l1 S h1332 haL hbR
      hNR := fun N hNL hLN hN2 =>
        (X.le_map_img_pCore e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hNL hLN hN2).trans
          (Subgroup.map_mono (X.img_mono hOR))
      hRT := Subgroup.map_mono (X.img_mono hRT)
      hRidx0 := ?_
      hRidx := ?_
      hRn := sup_le (hnorm (le_sup_left.trans hRN)) (hnorm (le_sup_right.trans hRN))
      hRV := by
        intro x hx v hv
        obtain ⟨a, haR, rfl⟩ := (mem_map_img_iff e).mp hx
        obtain ⟨w, hw, rfl⟩ := hv
        simp only [MulEquiv.coe_toMonoidHom]
        rw [congr_apply_e, X.act_fix_vHat (fun v hv =>
          comm_mem_of_mem_R1 S X.top.hF h1222 h1332 h1334 h13314 haR hv) hw]
      hVcard := by
        rw [← card_vHat S X.top.hF h1332 h1334]
        exact (Nat.card_congr ((vHat V (A6.g1 T V) (fsuV1 T V)).equivMapOfInjective
          e.toMonoidHom e.injective).toEquiv).symm
      ht := (mem_map_img_iff e).mpr ⟨t, htR, rfl⟩
      ht2 := hs2
      ht1 := hs1
      htc := hsc
      ha := ⟨_, ha⟩
      ha1 := by rw [← ha]; exact hd1' }
  ·
    obtain ⟨x, hxL, -, hfpf⟩ := exists_l1_fpf S.hyp (stmtL32NModule_of_inputs h1332 h1334)
      h1222 h1332 h1334
    have hl1 : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
    rw [hl1] at hxL
    have hV₁V : fsuV1 T V ≤ V := X.top.hF.toHypF91.V₁_le_V
    obtain ⟨v, hvV, hvV₁⟩ : ∃ v ∈ V, v ∉ fsuV1 T V := by
      by_contra hall
      push Not at hall
      have := Subgroup.card_le_of_le (show V ≤ fsuV1 T V from hall)
      rw [hV8, hV12] at this
      omega
    have hvU : v ∈ conjClosure V (A6.g1 T V) := le_conjClosure V _ hvV
    refine ⟨MulAut.congr e (X.top.act ⟨x, hL1H hxL⟩), (mem_map_img_iff e).mpr ⟨_, hxL, rfl⟩,
      e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨v, hvU⟩),
      ⟨_, ⟨⟨v, hvU⟩, Subgroup.mem_subgroupOf.mpr hvV, rfl⟩, rfl⟩,
      fun h => hvV₁ (hfpf v hvV ?_)⟩
    rw [congr_apply_e, e.apply_eq_iff_eq, X.top.act_mk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
      A6.A6Mod.secMk_eq_one_iff] at h
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  ·
    rw [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff _).mpr hΦi, sup_bot_eq, sup_bot_eq,
      X.relIndex_img hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hRT hTH hQR,
      hR1T]
    norm_num
  ·
    rw [Subgroup.relIndex_map_map, (MonoidHom.ker_eq_bot_iff _).mpr hΦi, sup_bot_eq, sup_bot_eq,
      X.relIndex_img hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hRT hTH hQR, hR1T]

end TopCtx

end CFSG.Quasithin.H13.L32A.L2
