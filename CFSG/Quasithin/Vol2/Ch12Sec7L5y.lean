module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5x
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Vol2.Ch10SecG31H

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.L715
open scoped IsMulCommutative

namespace S127.L716

variable {G : Type} [Group G] [Finite G]

abbrev Gt (z : G) : Type :=
  SecQuot (Subgroup.normalizer (Subgroup.zpowers z : Set G)) (Subgroup.zpowers z)

abbrev Ut (T L V : Subgroup G) (z : G) : Subgroup (Gt z) :=
  tildeOf (Subgroup.zpowers z) (U714 T L V z)

abbrev Ht (T L V : Subgroup G) (z : G) : Subgroup (Gt z) :=
  tildeOf (Subgroup.zpowers z) (H714 T L V z)

noncomputable abbrev Hs (T L V : Subgroup G) (z : G) : Subgroup (MulAut ↥(Ut T L V z)) :=
  autOn (Ht T L V z) (Ut T L V z)

abbrev X1 (T L V : Subgroup G) (z : G) : Subgroup ↥(Ut T L V z) :=
  (tildeOf (Subgroup.zpowers z) (V1 T L V)).subgroupOf (Ut T L V z)

omit [Finite G] in
theorem card_secImg {A B X : Subgroup G} [(B.subgroupOf A).Normal] (hBX : B ≤ X) (hXA : X ≤ A) :
    Nat.card ↥(secImg A B X) = B.relIndex X := by
  have hB : secImg A B B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨b, hb, rfl⟩ := mem_secImg.1 hy
    rw [Subgroup.mem_bot]
    exact secMk_eq_one_iff.2 hb
  have h := relIndex_secImg (A := A) (B := B) le_rfl hBX hXA
  rwa [hB, Subgroup.relIndex_bot_left] at h


end S127.L716

namespace S127.L715.Set714

open S127.L716

variable {G : Type} [Group G] [Finite G]
variable {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem elemAbelian_Ut
    (h1222 : Stmt12_2_2) : IsElemAbelian 2 (Ut T L V z) :=
  (s.isTwoReducedIn h1222).2.2.1

theorem Ht_le_normalizer
    (h1222 : Stmt12_2_2) : Ht T L V z ≤ Subgroup.normalizer (Ut T L V z : Set (Gt z)) :=
  (s.isTwoReducedIn h1222).2.1

theorem pCoreOf_Hs
    (h1222 : Stmt12_2_2) : pCoreOf 2 (Hs T L V z) = ⊥ :=
  CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot (s.isTwoReducedIn h1222)

theorem V1_le_N (h1222 : Stmt12_2_2) :
    V1 T L V ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
  ((inf_le_left : V1 T L V ≤ V).trans (s.V_le_Gz h1222)).trans
    (centralizer_le_normalizer_zpowers z)

theorem card_tilde_V1
    (h1222 : Stmt12_2_2) : Nat.card ↥(tildeOf (Subgroup.zpowers z) (V1 T L V)) = 2 := by
  have hV14 : Nat.card ↥(V1 T L V) = 4 := by
    have := (S127.card_eq_of_1222 h1222 s.setting.hyp).1
    exact (S127.Mod.lemma12_7_2_two h1222 s.setting.hyp).1.2
  have hz2 : Nat.card ↥(Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, s.orderOf_z]
  have hzV1 : Subgroup.zpowers z ≤ V1 T L V := Subgroup.zpowers_le_of_mem s.mem
  rw [tildeOf, card_secImg hzV1 (s.V1_le_N h1222)]
  have h := Subgroup.card_mul_index ((Subgroup.zpowers z).subgroupOf (V1 T L V))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzV1).toEquiv, hz2, hV14] at h
  rw [Subgroup.relIndex]
  omega

theorem comm_mem_V1
    (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {v u : G}
    (hv : v ∈ V) (hu : u ∈ U714 T L V z) : v * u * v⁻¹ * u⁻¹ ∈ V1 T L V := by
  have hUT := (s.U_le_T h1222).1
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    S127.Mod.T_le_normalizer h1222 s.setting.hyp (hUT hu)
  have ha : conjAct V ⟨u, huN⟩ ∈ autOn (R1 T L V) V := hU ▸ S127.Mod.conjAct_mem_autOn hu huN
  obtain ⟨r, hrN, hrR, hre⟩ := S127.Mod.mem_autOn'.1 ha
  have h1 : u * v * u⁻¹ = r * v * r⁻¹ := by
    have := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : G)) hre
    simp only [S127.Mod.conjAct_val] at this
    exact this.symm
  have h2 := s.R1_comm_mem h1222 hrR hv
  rw [← h1] at h2
  have e : v * u * v⁻¹ * u⁻¹ = (u * v * u⁻¹ * v⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ h2

theorem V_le_N (h1222 : Stmt12_2_2) : V ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
  (s.V_le_Gz h1222).trans (centralizer_le_normalizer_zpowers z)

theorem tmk_mem_Ht (h1222 : Stmt12_2_2) {v : G} (hv : v ∈ V) :
    tmk (Subgroup.zpowers z) ⟨v, s.V_le_N h1222 hv⟩ ∈ Ht T L V z :=
  secMk_mem_secImg (V_le_H714 T L V z hv)

noncomputable def phiV
    (h1222 : Stmt12_2_2) : ↥V →* MulAut ↥(Ut T L V z) :=
  (conjAct (Ut T L V z)).comp
    (((tmk (Subgroup.zpowers z)).comp (Subgroup.inclusion (s.V_le_N h1222))).codRestrict _
      fun v => s.Ht_le_normalizer h1222 (s.tmk_mem_Ht h1222 v.2))

theorem phiV_apply
    (h1222 : Stmt12_2_2) (v : ↥V) (w : ↥(Ut T L V z)) :
    ((s.phiV h1222 v w : ↥(Ut T L V z)) : Gt z) =
      tmk (Subgroup.zpowers z) ⟨v, s.V_le_N h1222 v.2⟩ * (w : Gt z) *
        (tmk (Subgroup.zpowers z) ⟨v, s.V_le_N h1222 v.2⟩)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ w

theorem phiV_mem_Hs
    (h1222 : Stmt12_2_2) (v : ↥V) : s.phiV h1222 v ∈ Hs T L V z :=
  ⟨⟨_, s.Ht_le_normalizer h1222 (s.tmk_mem_Ht h1222 v.2)⟩, s.tmk_mem_Ht h1222 v.2, rfl⟩

theorem phiV_transv
    (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) (v : ↥V)
    (w : ↥(Ut T L V z)) : s.phiV h1222 v w * w⁻¹ ∈ X1 T L V z := by
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, s.phiV_apply h1222]
  obtain ⟨u, hu, hwu⟩ := mem_secImg.1 w.2
  rw [← hwu]
  have hc := s.comm_mem_V1 h1222 hU v.2 hu
  have e : tmk (Subgroup.zpowers z) ⟨v, s.V_le_N h1222 v.2⟩ * secMk _ _ u *
      (tmk (Subgroup.zpowers z) ⟨v, s.V_le_N h1222 v.2⟩)⁻¹ * (secMk _ _ u)⁻¹ =
      tmk (Subgroup.zpowers z) (⟨v, s.V_le_N h1222 v.2⟩ * u * ⟨v, s.V_le_N h1222 v.2⟩⁻¹ * u⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e]
  exact secMk_mem_secImg hc

theorem mem_ker_phiV
    (h1222 : Stmt12_2_2) (v : ↥V) :
    s.phiV h1222 v = 1 ↔ (v : G) ∈ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) := by
  have hvN := s.V_le_N h1222 v.2
  constructor
  · intro h1
    refine ⟨V_le_H714 T L V z v.2, fun u hu => ?_⟩
    have huN : u ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
      (s.U_le_T h1222).1.trans (s.le_cent.trans (centralizer_le_normalizer_zpowers z)) hu
    have hw : secMk (Subgroup.normalizer (Subgroup.zpowers z : Set G)) (Subgroup.zpowers z)
        ⟨u, huN⟩ ∈ Ut T L V z := secMk_mem_secImg hu
    have h2 := congrArg (fun f : MulAut ↥(Ut T L V z) => ((f ⟨_, hw⟩ : ↥(Ut T L V z)) : Gt z)) h1
    simp only [s.phiV_apply h1222, MulAut.one_apply] at h2
    have h3 : tmk (Subgroup.zpowers z) (⟨v, hvN⟩ * ⟨u, huN⟩ * ⟨v, hvN⟩⁻¹ * ⟨u, huN⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [h2, mul_inv_cancel]
    exact secMk_eq_one_iff.1 h3
  · intro hc
    apply MulEquiv.ext
    intro w
    apply Subtype.ext
    rw [s.phiV_apply h1222, MulAut.one_apply]
    obtain ⟨u, hu, hwu⟩ := mem_secImg.1 w.2
    rw [← hwu]
    have h1 : tmk (Subgroup.zpowers z) (⟨v, hvN⟩ * u * ⟨v, hvN⟩⁻¹ * u⁻¹) = 1 :=
      secMk_eq_one_iff.2 (hc.2 _ hu)
    simp only [map_mul, map_inv] at h1
    rw [← mul_inv_eq_one]
    exact h1

theorem four_le_card_range_phiV
    (h1222 : Stmt12_2_2) : 4 ≤ Nat.card ↥(s.phiV h1222).range := by
  set W := V ⊓ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) with hW
  have hker : (s.phiV h1222).ker = W.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, s.mem_ker_phiV h1222, Subgroup.mem_subgroupOf]
    exact ⟨fun h => ⟨v.2, h⟩, fun h => h.2⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (s.phiV h1222).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (s.phiV h1222)).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : W ≤ V)).toEquiv] at h1
  have hWpos : 0 < Nat.card ↥W := Nat.card_pos
  rcases s.card_V_cTil h1222 with h2 | h2
  · rw [h2] at h1
    have := Nat.eq_of_mul_eq_mul_right hWpos h1
    omega
  · rw [h2] at h1
    have := Nat.eq_of_mul_eq_mul_right hWpos h1
    omega

theorem range_phiV_le_transvGroup
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    (s.phiV h1222).range ≤ ASInputs.transvGroup (Hs T L V z) (X1 T L V z) := by
  rintro _ ⟨v, rfl⟩
  exact G31.mem_transvGroup_iff.2 ⟨s.phiV_mem_Hs h1222 v, s.phiV_transv h1222 hU v⟩

theorem four_le_card_transvGroup
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    4 ≤ Nat.card ↥(ASInputs.transvGroup (Hs T L V z) (X1 T L V z)) :=
  (s.four_le_card_range_phiV h1222).trans
    (Subgroup.card_le_of_le (s.range_phiV_le_transvGroup h1222 hU))

theorem card_X1
    (h1222 : Stmt12_2_2) : Nat.card ↥(X1 T L V z) = 2 := by
  have hle : tildeOf (Subgroup.zpowers z) (V1 T L V) ≤ Ut T L V z :=
    secImg_mono (le_conjClosure _ _)
  rw [X1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, s.card_tilde_V1 h1222]

end S127.L715.Set714

end CFSG.Quasithin.H13
