module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5v
public import CFSG.Quasithin.Vol2.Ch12Sec7ModP
public import CFSG.Quasithin.Vol2.Ch12Sec7L5s

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127
open scoped IsMulCommutative

namespace S127.L715

variable {G : Type} [Group G] [Finite G]

structure Set714 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t z : G) : Prop where
  setting : Setting1273 G T L V t
  mem : z ∈ V1 T L V
  ne_one : z ≠ 1
  le_cent : T ≤ Subgroup.centralizer ({z} : Set G)
  not_le : ¬ V ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))

abbrev H714 (T L V : Subgroup G) (z : G) : Subgroup G := K714 V z ⊔ (L1 T L V ⊔ T)

omit [Finite G] in
theorem le_normalizer_conjClosure_of {Z H X : Subgroup G}
    (hZ : X ≤ Subgroup.normalizer (Z : Set G)) (hH : X ≤ Subgroup.normalizer (H : Set G)) :
    X ≤ Subgroup.normalizer (conjClosure Z H : Set G) := by
  refine le_normalizer_of_conj_mem fun x hx w hw => ?_
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨h, hh, v, hv, rfl⟩ := hy
    have e : x * (h * v * h⁻¹) * x⁻¹ = (x * h * x⁻¹) * (x * v * x⁻¹) * (x * h * x⁻¹)⁻¹ := by
      group
    rw [e]
    exact mem_conjClosure ((Subgroup.mem_normalizer_iff.mp (hH hx) h).mp hh)
      ((Subgroup.mem_normalizer_iff.mp (hZ hx) v).mp hv)
  | one => simp
  | mul a b _ _ ha hb =>
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact (conjClosure Z H).mul_mem ha hb
  | inv a _ ha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact (conjClosure Z H).inv_mem ha

omit [Finite G] in
theorem V_le_H714 (T L V : Subgroup G) (z : G) : V ≤ H714 T L V z :=
  (le_conjClosure V _).trans le_sup_left

omit [Finite G] in
theorem centralizer_le_normalizer_zpowers (z : G) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg w hw => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have hgz : g * z = z * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have e : g * z ^ k * g⁻¹ = z ^ k := by
    rw [← conj_zpow, hgz, mul_inv_cancel_right]
  rw [e]
  exact Subgroup.zpow_mem_zpowers z k

theorem T_le_normalizer_L1 {T L V : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hTV1 : T ≤ Subgroup.normalizer (V1 T L V : Set G)) :
    T ≤ Subgroup.normalizer (L1 T L V : Set G) := by
  refine le_trans ?_ (S127.Mod.normalizer_le_normalizer_oTwoUpper _)
  refine le_normalizer_of_conj_mem fun x hx w hw => ?_
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hTL hx) w).mp hw.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : x⁻¹ * v * x ∈ V1 T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (hTV1 (T.inv_mem hx)) v).mp hv
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hw.2 _ hv'
  calc v * (x * w * x⁻¹) = x * ((x⁻¹ * v * x) * w) * x⁻¹ := by group
    _ = x * (w * (x⁻¹ * v * x)) * x⁻¹ := by rw [hc]
    _ = x * w * x⁻¹ * v := by group

@[expose] def cTil {H U : Subgroup G} {z : G} (hHz : H ≤ Subgroup.centralizer ({z} : Set G))
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) : Subgroup G where
  carrier := {h | h ∈ H ∧ ∀ u ∈ U, h * u * h⁻¹ * u⁻¹ ∈ Subgroup.zpowers z}
  one_mem' := ⟨H.one_mem, fun u _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hau⟩ ⟨hb, hbu⟩
    refine ⟨H.mul_mem ha hb, fun u hu => ?_⟩
    have e : a * b * u * (a * b)⁻¹ * u⁻¹ =
        a * (b * u * b⁻¹ * u⁻¹) * a⁻¹ * (a * u * a⁻¹ * u⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp
      (centralizer_le_normalizer_zpowers z (hHz ha)) _).mp (hbu u hu)) (hau u hu)
  inv_mem' := by
    rintro a ⟨ha, hau⟩
    refine ⟨H.inv_mem ha, fun u hu => ?_⟩
    have hu' : a⁻¹ * u * a ∈ U := by
      have := (Subgroup.mem_normalizer_iff.mp (hHU (H.inv_mem ha)) u).mp hu
      simpa using this
    have e : a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ = (a * (a⁻¹ * u * a) * a⁻¹ * (a⁻¹ * u * a)⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ (hau _ hu')

omit [Finite G] in
theorem mem_cTil {H U : Subgroup G} {z : G} {hHz : H ≤ Subgroup.centralizer ({z} : Set G)}
    {hHU : H ≤ Subgroup.normalizer (U : Set G)} {h : G} :
    h ∈ cTil hHz hHU ↔ h ∈ H ∧ ∀ u ∈ U, h * u * h⁻¹ * u⁻¹ ∈ Subgroup.zpowers z := Iff.rfl

omit [Finite G] in
theorem le_normalizer_cTil {H U : Subgroup G} {z : G}
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) (hHU : H ≤ Subgroup.normalizer (U : Set G)) :
    H ≤ Subgroup.normalizer (cTil hHz hHU : Set G) := by
  refine le_normalizer_of_conj_mem fun g hg c hc => ?_
  obtain ⟨hcH, hcu⟩ := hc
  refine ⟨H.mul_mem (H.mul_mem hg hcH) (H.inv_mem hg), fun u hu => ?_⟩
  have hu' : g⁻¹ * u * g ∈ U := by
    have := (Subgroup.mem_normalizer_iff.mp (hHU (H.inv_mem hg)) u).mp hu
    simpa using this
  have e : g * c * g⁻¹ * u * (g * c * g⁻¹)⁻¹ * u⁻¹ =
      g * (c * (g⁻¹ * u * g) * c⁻¹ * (g⁻¹ * u * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (centralizer_le_normalizer_zpowers z (hHz hg)) _).mp
    (hcu _ hu')

omit [Finite G] in
theorem cTil_le_normalizer {H U W : Subgroup G} {z : G}
    (hHz : H ≤ Subgroup.centralizer ({z} : Set G)) (hHU : H ≤ Subgroup.normalizer (U : Set G))
    (hzW : z ∈ W) (hWU : W ≤ U) : cTil hHz hHU ≤ Subgroup.normalizer (W : Set G) := by
  refine le_normalizer_of_conj_mem fun c hc w hw => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc.2 w (hWU hw))
  have e : c * w * c⁻¹ = (c * w * c⁻¹ * w⁻¹) * w := by group
  rw [e, ← hk]
  exact W.mul_mem (W.zpow_mem hzW k) hw

namespace Set714

variable {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem z_mem_V : z ∈ V := (inf_le_left : V1 T L V ≤ V) s.mem

theorem V_le_Gz (h1222 : Stmt12_2_2) : V ≤ Subgroup.centralizer ({z} : Set G) := by
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 s.setting.hyp
  intro v hv
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (hcomm.is_comm.comm ⟨v, hv⟩ ⟨z, s.z_mem_V⟩)

theorem K_le_Gz (h1222 : Stmt12_2_2) : K714 V z ≤ Subgroup.centralizer ({z} : Set G) :=
  conjClosure_le fun _ hh _ hv => Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (s.V_le_Gz h1222 hv))
    (Subgroup.inv_mem _ hh)

theorem L1_le_Gz : L1 T L V ≤ Subgroup.centralizer ({z} : Set G) := by
  intro l hl
  have hl' := ((oTwoUpper_le _).trans inf_le_right) hl
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp hl' z s.mem).symm

theorem H_le_Gz (h1222 : Stmt12_2_2) : H714 T L V z ≤ Subgroup.centralizer ({z} : Set G) :=
  sup_le (s.K_le_Gz h1222) (sup_le s.L1_le_Gz s.le_cent)

omit [Finite G] s in
theorem Gz_le_normalizer_K :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K714 V z : Set G) :=
  le_normalizer_conjClosure V _

theorem T_le_normalizer_V1 (h1222 : Stmt12_2_2) :
    T ≤ Subgroup.normalizer (V1 T L V : Set G) :=
  S127.Mod.T_le_normalizer_V1 h1222 s.setting.hyp

theorem L1T_le_normalizer_V1 (h1222 : Stmt12_2_2) :
    L1 T L V ⊔ T ≤ Subgroup.normalizer (V1 T L V : Set G) := by
  refine sup_le (fun l hl => ?_) (s.T_le_normalizer_V1 h1222)
  have hl' := ((oTwoUpper_le _).trans inf_le_right) hl
  exact Subgroup.centralizer_le_normalizer _ hl'

theorem H_le_normalizer_U (h1222 : Stmt12_2_2) :
    H714 T L V z ≤ Subgroup.normalizer (U714 T L V z : Set G) :=
  sup_le (le_normalizer_conjClosure _ _)
    (le_normalizer_conjClosure_of (s.L1T_le_normalizer_V1 h1222)
      ((sup_le s.L1_le_Gz s.le_cent).trans Gz_le_normalizer_K))

theorem conjClosure_eq (h1222 : Stmt12_2_2) :
    conjClosure (V1 T L V) (H714 T L V z) = U714 T L V z := by
  refine le_antisymm (conjClosure_le fun h hh v hv => ?_) (conjClosure_mono le_rfl le_sup_left)
  exact (Subgroup.mem_normalizer_iff.mp (s.H_le_normalizer_U h1222 hh) v).mp
    (le_conjClosure _ _ hv)

theorem orderOf_z : orderOf z = 2 :=
  orderOf_eq_prime (S127.sq_eq_one_of_mem s.setting.hyp.hyp s.z_mem_V) s.ne_one


theorem zpowers_le_pCoreOf (h1222 : Stmt12_2_2) :
    Subgroup.zpowers z ≤ pCoreOf 2 (H714 T L V z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.zpowers_le_of_mem (V_le_H714 T L V z s.z_mem_V))
    ((s.H_le_Gz h1222).trans (centralizer_le_normalizer_zpowers z)) ?_
  exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, s.orderOf_z, pow_one])

theorem almostSpecialHyp
    (h1222 : Stmt12_2_2) :
    AlmostSpecialHyp (V1 T L V) (Subgroup.zpowers z) (L1 T L V) T (H714 T L V z) := by
  have h := s.setting.hyp
  have hy := h.hyp
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 h
  have hVT := S127.L713.V_le_T h1222 h
  have hV1V : V1 T L V ≤ V := inf_le_left
  obtain ⟨hpt, -⟩ := S127.Mod.lemma12_7_2_two h1222 h
  have hV14 : Nat.card ↥(V1 T L V) = 4 := hpt.2
  have hz2 : Nat.card ↥(Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, s.orderOf_z]
  have hzV1 : Subgroup.zpowers z ≤ V1 T L V := Subgroup.zpowers_le_of_mem s.mem
  have hTV1 := s.T_le_normalizer_V1 h1222
  have hTH : T ≤ H714 T L V z := le_sup_right.trans le_sup_right
  have hlL : lOne (L1 T L V) (Subgroup.zpowers z) ≤ L1 T L V :=
    (oTwoUpper_le _).trans inf_le_left
  have hL1N : L1 T L V ≤ Subgroup.normalizer (V1 T L V : Set G) :=
    le_sup_left.trans (s.L1T_le_normalizer_V1 h1222)
  have hL1z : L1 T L V ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    s.L1_le_Gz.trans (centralizer_le_normalizer_zpowers z)
  exact
    { elemAbelian := ⟨⟨⟨fun a b => Subtype.ext (show (a : G) * b = b * a from congrArg Subtype.val
          (hcomm.is_comm.comm ⟨a, hV1V a.2⟩ ⟨b, hV1V b.2⟩))⟩⟩,
        fun x hx => S127.sq_eq_one_of_mem hy (hV1V hx)⟩
      ne_bot := by
        intro hb
        rw [hb, Subgroup.card_bot] at hz2
        norm_num at hz2
      le_V := hzV1
      oTwo_eq := (S127.Mod.oTwoUpper_idem _).symm
      V_le_T := hV1V.trans hVT
      T_le_normV₁ := s.le_cent.trans (centralizer_le_normalizer_zpowers z)
      T_le_normV := hTV1
      T_le_normL := T_le_normalizer_L1 hy.normalizes hTV1
      sylow_LT := S127.L713.isSylowTwoOf_of_le hy.sylow le_sup_right
      H_le := (s.H_le_Gz h1222).trans (centralizer_le_normalizer_zpowers z)
      lOne_sup_le := sup_le (hlL.trans (le_sup_left.trans le_sup_right)) hTH
      sylow_H := S127.L713.isSylowTwoOf_of_le hy.sylow hTH
      charTwo := charTwo_of_inH hy.qtke.2.1 (hy.sylow.1.toSylow hy.sylow.2)
        ⟨hTH, fun hb => s.ne_one (by
          have := s.zpowers_le_pCoreOf h1222 (Subgroup.mem_zpowers z)
          rw [hb, Subgroup.mem_bot] at this
          exact this)⟩
      irred := by
        refine ⟨lt_of_le_of_ne hzV1 fun he => ?_, sup_le (hlL.trans hL1N) hTV1,
          sup_le (hlL.trans hL1z) (s.le_cent.trans (centralizer_le_normalizer_zpowers z)),
          fun W h1 h2 _ => ?_⟩
        · rw [he, hV14] at hz2
          norm_num at hz2
        · have hd : Nat.card ↥W ∣ 4 := hV14 ▸ Subgroup.card_dvd_of_le h2
          have hd2 : 2 ∣ Nat.card ↥W := hz2 ▸ Subgroup.card_dvd_of_le h1
          have hW : Nat.card ↥W = 2 ∨ Nat.card ↥W = 4 := by
            have hle : Nat.card ↥W ≤ 4 := Nat.le_of_dvd (by norm_num) hd
            interval_cases hc : Nat.card ↥W <;> simp_all
          rcases hW with hW | hW
          · exact Or.inl (Subgroup.eq_of_le_of_card_ge h1 (by rw [hW, hz2])).symm
          · exact Or.inr (Subgroup.eq_of_le_of_card_ge h2 (by rw [hW, hV14])) }

theorem frattiniOf_le
    (h1222 : Stmt12_2_2) : frattiniOf (U714 T L V z) ≤ Subgroup.zpowers z := by
  rw [← s.conjClosure_eq h1222]
  exact (s.almostSpecialHyp h1222).G22_two

theorem U_le_T
    (h1222 : Stmt12_2_2) : U714 T L V z ≤ T ∧ T ≤ Subgroup.normalizer (U714 T L V z : Set G) := by
  rw [← s.conjClosure_eq h1222]
  exact (s.almostSpecialHyp h1222).G22_three

theorem isTwoReducedIn
    (h1222 : Stmt12_2_2) :
    IsTwoReducedIn (tildeOf (Subgroup.zpowers z) (H714 T L V z))
      (tildeOf (Subgroup.zpowers z) (U714 T L V z)) := by
  rw [← s.conjClosure_eq h1222]
  exact (s.almostSpecialHyp h1222).G22_four

theorem not_le_pCoreOf_H (h1222 : Stmt12_2_2) : ¬ V ≤ pCoreOf 2 (H714 T L V z) := by
  intro hle
  apply s.not_le
  have hK : V ≤ pCoreOf 2 (K714 V z) :=
    (le_inf hle (le_conjClosure V _)).trans (C58.pCoreOf_inf_le le_sup_left)
  refine hK.trans ?_
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (s.K_le_Gz h1222))
    (Gz_le_normalizer_K.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem not_le_cTil
    (h1222 : Stmt12_2_2) : ¬ V ≤ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) := by
  intro hV
  apply s.not_le_pCoreOf_H h1222
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) with hC
  have hCN : C ≤ Subgroup.normalizer (V1 T L V : Set G) :=
    cTil_le_normalizer _ _ s.mem (le_conjClosure _ _)
  have h713 := (lemma12_7_13_of h1222 G T L V t s.setting).2
  have hVC : V ≤ pCoreOf 2 C := (le_inf h713 hV).trans (C58.pCoreOf_inf_le hCN)
  refine hVC.trans ?_
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 C).trans fun c hc => hc.1)
    ((le_normalizer_cTil _ _).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C)

end Set714

end S127.L715

end CFSG.Quasithin.H13
