module

public import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction

public section

namespace CFSG.RankThree.PartTwo.Sec12.Item125Diag

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

structure DiagHyp (c : G) (L E : Subgroup G) : Prop where
  mem_thetaComponentsAt : L ∈ thetaComponentsAt 3 c
  mem_L : c ∈ L
  ne_one : c ≠ 1
  isE27 : Late.IsE27 E
  le_lcBar : E ≤ lcBar c L
  mem_E : c ∈ E
  card_inf_C : Nat.card (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) = 3
  card_inf_L : Nat.card (E ⊓ L : Subgroup G) = 3
  exp : ∀ e ∈ E, ∃ l ∈ L, ∃ z ∈ Sec4.thetaQuotCentralizer L,
    e = l * z ∧ l ^ 3 = 1 ∧ l * z = z * l
  card_center : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3

theorem thetaBarAct_mul {L : Subgroup G} {l z : G} (hl : l ∈ L)
    (hz : z ∈ Sec4.thetaQuotCentralizer L) (h : l * z ∈ Subgroup.normalizer (L : Set G)) :
    thetaBarAct L ⟨l * z, h⟩ =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl⟩) := by
  have hzN := thetaQuotCentralizer_le_normalizer' L hz
  have h1 : (⟨l * z, h⟩ : Subgroup.normalizer (L : Set G)) =
      ⟨l, Subgroup.le_normalizer hl⟩ * ⟨z, hzN⟩ := rfl
  rw [h1, map_mul, thetaBarAct_of_mem hl, (mem_thetaQuotCentralizer_iff_thetaBarAct hzN).mp hz,
    mul_one]

theorem mul_inv_mem_center_of_commute {X : Type*} [Group X] {σ : MulAut X} {b : X}
    (h : σ * MulAut.conj b = MulAut.conj b * σ) : σ b * b⁻¹ ∈ Subgroup.center X := by
  have h1 : MulAut.conj (σ b) = MulAut.conj b := by
    ext y
    have h2 := congrArg (fun τ : MulAut X => τ (σ⁻¹ y)) h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.apply_inv_self, map_mul,
      map_inv] at h2
    rw [MulAut.conj_apply, MulAut.conj_apply, h2]
  refine mem_center_of_conj_eq_one ?_
  rw [map_mul, map_inv, h1, mul_inv_cancel]

@[expose] noncomputable def fixer (L : Subgroup G) (xb : L ⧸ aschbacherSolvableCore 3 L) :
    Subgroup G where
  carrier := {g | ∃ hg : g ∈ Subgroup.normalizer (L : Set G), thetaBarAct L ⟨g, hg⟩ xb = xb}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have e1 : (⟨a * b, mul_mem ha hb⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, ha⟩ * ⟨b, hb⟩ :=
      rfl
    rw [e1, map_mul, MulAut.mul_apply, hb', ha']
  one_mem' := by
    refine ⟨(Subgroup.normalizer (L : Set G)).one_mem, ?_⟩
    have e1 : (⟨1, (Subgroup.normalizer (L : Set G)).one_mem⟩ :
        Subgroup.normalizer (L : Set G)) = 1 := rfl
    rw [e1, map_one, MulAut.one_apply]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    have e1 : (⟨a⁻¹, inv_mem ha⟩ : Subgroup.normalizer (L : Set G)) = (⟨a, ha⟩)⁻¹ := rfl
    rw [e1, map_inv]
    conv_lhs => rw [← ha']
    exact MulAut.inv_apply_self _ _ _

theorem mem_fixer_iff {L : Subgroup G} {xb : L ⧸ aschbacherSolvableCore 3 L} {g : G} :
    g ∈ fixer L xb ↔
      ∃ hg : g ∈ Subgroup.normalizer (L : Set G), thetaBarAct L ⟨g, hg⟩ xb = xb :=
  Iff.rfl

theorem exists_lift_fixed_pow_three {L D : Subgroup G} (hD3 : IsPGroup 3 D)
    (hDN : D ≤ Subgroup.normalizer (L : Set G)) (xb : L ⧸ aschbacherSolvableCore 3 L)
    (hxb : orderOf xb = 3) (hfix : ∀ d (hd : d ∈ D), thetaBarAct L ⟨d, hDN hd⟩ xb = xb) :
    ∃ w : L, QuotientGroup.mk' (aschbacherSolvableCore 3 L) w = xb ∧ (w : G) ^ 3 = 1 ∧
      ∀ d ∈ D, d * (w : G) = w * d := by
  obtain ⟨y, hy, hyfix⟩ := exists_lift_fixed hD3 hDN xb hfix
  obtain ⟨m, hm, hym⟩ := exists_pow_orderOf_three (y := y) (by rw [hy]; exact hxb)
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm).symm (by norm_num : 1 < 3)
  have hx3 : xb ^ 3 = 1 := by
    have h := pow_orderOf_eq_one xb
    rwa [hxb] at h
  refine ⟨(y ^ m) ^ r, ?_, ?_, ?_⟩
  · rw [map_pow, map_pow, hy, ← pow_mul, pow_eq_pow_mod (m * r) hx3, hr, pow_one]
  · have h1 := pow_orderOf_eq_one (y ^ m)
    rw [hym] at h1
    have h2 : ((y ^ m) ^ r) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
    simpa using congrArg Subtype.val h2
  · intro d hd
    have h1 : d * (y : G) = y * d := by
      calc d * (y : G) = (d * y * d⁻¹) * d := by group
        _ = y * d := by rw [hyfix d hd]
    have hc : Commute d (y : G) := h1
    have := ((hc.pow_right m).pow_right r).eq
    simpa using this

theorem mk_commutator_eq {L : Subgroup G} (y : L) {e : G}
    (he : e ∈ Subgroup.normalizer (L : Set G)) (h : (y : G) * e * (y : G)⁻¹ * e⁻¹ ∈ L) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨_, h⟩ =
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) y *
        (thetaBarAct L ⟨e, he⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) y))⁻¹ := by
  rw [thetaBarAct_mk, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
  group

theorem card_le_of_isSylowOf {X : Type*} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    {S K Y : Subgroup X} (hS : IsSylowOf p S K) (hYK : Y ≤ K) (hY : IsPGroup p Y) :
    Nat.card Y ≤ Nat.card S := by
  rw [hS.card_eq]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
  rw [hk]
  refine Nat.pow_le_pow_right hp.out.pos ?_
  have hdvd : p ^ k ∣ Nat.card K := hk ▸ Subgroup.card_dvd_of_le hYK
  exact (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd

omit [Finite G] in
theorem pow_three_eq_one_of_mem_transvectionGroup {A : Subgroup G} {c : A} (hc3 : c ^ 3 = 1)
    {σ : MulAut A} (hσ : σ ∈ transvectionGroup A c) : σ ^ 3 = 1 := by
  refine MulEquiv.ext fun a => ?_
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hσ.2 a)
  have hσc : σ (c ^ n) = c ^ n := by rw [map_zpow, hσ.1]
  have h1 : σ a = c ^ n * a := by rw [hn, inv_mul_cancel_right]
  have h3 : (c ^ n) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc3, one_zpow]
  have e3 : σ ^ 3 = σ * σ * σ := by rw [pow_succ, pow_two]
  have h2 : σ (σ (σ a)) = c ^ n * (c ^ n * (c ^ n * a)) := by
    simp only [h1, map_mul, hσc]
  rw [e3, MulAut.mul_apply, MulAut.mul_apply, MulAut.one_apply, h2]
  calc c ^ n * (c ^ n * (c ^ n * a)) = (c ^ n) ^ 3 * a := by group
    _ = a := by rw [h3, one_mul]

namespace DiagHyp

variable {c : G} {L E : Subgroup G}

theorem pow_three (hD : DiagHyp c L E) {x : G} (hx : x ∈ E) : x ^ 3 = 1 := hD.isE27.1.2 x hx

theorem orderOf_c (hD : DiagHyp c L E) : orderOf c = 3 :=
  orderOf_eq_prime (hD.pow_three hD.mem_E) hD.ne_one

theorem comm (hD : DiagHyp c L E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x :=
  congrArg Subtype.val (hD.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem commute (hD : DiagHyp c L E) {x y : G} (hx : x ∈ E) (hy : y ∈ E) : Commute x y :=
  hD.comm hx hy

theorem isPGroup (hD : DiagHyp c L E) : IsPGroup 3 E :=
  fun x => ⟨1, Subtype.ext (by simpa using hD.pow_three x.2)⟩

theorem le_normalizer (hD : DiagHyp c L E) : E ≤ Subgroup.normalizer (L : Set G) :=
  hD.le_lcBar.trans (lcBar_le_normalizer hD.mem_thetaComponentsAt)

theorem le_centralizer (hD : DiagHyp c L E) : L ≤ Subgroup.centralizer ({c} : Set G) :=
  Sec6.le_centralizer_of_mem_thetaComponentsAt hD.mem_thetaComponentsAt

theorem c_mem_C (hD : DiagHyp c L E) : c ∈ Sec4.thetaQuotCentralizer L :=
  mem_thetaQuotCentralizer_of_central hD.mem_L hD.le_centralizer

theorem inf_L_eq (hD : DiagHyp c L E) : E ⊓ L = Subgroup.zpowers c :=
  (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hD.mem_E, hD.mem_L⟩))
    (by rw [hD.card_inf_L, Nat.card_zpowers, hD.orderOf_c])).symm

theorem inf_C_eq (hD : DiagHyp c L E) : E ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c :=
  (Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hD.mem_E, hD.c_mem_C⟩))
    (by rw [hD.card_inf_C, Nat.card_zpowers, hD.orderOf_c])).symm

theorem mem_zpowers_of_mem_L (hD : DiagHyp c L E) {e : G} (he : e ∈ E) (heL : e ∈ L) :
    e ∈ Subgroup.zpowers c := by
  rw [← hD.inf_L_eq]
  exact ⟨he, heL⟩

theorem mem_zpowers_of_thetaBarAct (hD : DiagHyp c L E) {e : G} (he : e ∈ E)
    (h1 : thetaBarAct L ⟨e, hD.le_normalizer he⟩ = 1) : e ∈ Subgroup.zpowers c := by
  rw [← hD.inf_C_eq]
  exact ⟨he, (mem_thetaQuotCentralizer_iff_thetaBarAct _).mpr h1⟩

theorem eq_one_of_mem_theta (hD : DiagHyp c L E) {x : G} (hxE : x ∈ E)
    (hx : x ∈ inSubgroup (aschbacherSolvableCore 3) L) : x = 1 := by
  have h := inf_inSubgroup_theta_eq_bot hD.isPGroup (L := L)
  have hx' : x ∈ E ⊓ inSubgroup (aschbacherSolvableCore 3) L := ⟨hxE, hx⟩
  rw [h] at hx'
  exact Subgroup.mem_bot.mp hx'

theorem exists_part (hD : DiagHyp c L E) {e : G} (he : e ∈ E) :
    ∃ l : L, (l : G) ^ 3 = 1 ∧
      thetaBarAct L ⟨e, hD.le_normalizer he⟩ =
        MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) l) ∧
      ∃ z ∈ Sec4.thetaQuotCentralizer L, e = l * z ∧ (l : G) * z = z * l := by
  obtain ⟨l, hl, z, hz, rfl, hl3, hlz⟩ := hD.exp e he
  exact ⟨⟨l, hl⟩, hl3, thetaBarAct_mul hl hz _, z, hz, rfl, hlz⟩

theorem thetaBarAct_comm (hD : DiagHyp c L E) {e f : G} (he : e ∈ E) (hf : f ∈ E) :
    thetaBarAct L ⟨e, hD.le_normalizer he⟩ * thetaBarAct L ⟨f, hD.le_normalizer hf⟩ =
      thetaBarAct L ⟨f, hD.le_normalizer hf⟩ * thetaBarAct L ⟨e, hD.le_normalizer he⟩ := by
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hD.comm he hf)

theorem thetaBarAct_mul_inv_mem_center (hD : DiagHyp c L E) {e f : G} (he : e ∈ E) (hf : f ∈ E)
    {b : L ⧸ aschbacherSolvableCore 3 L}
    (hb : thetaBarAct L ⟨f, hD.le_normalizer hf⟩ = MulAut.conj b) :
    thetaBarAct L ⟨e, hD.le_normalizer he⟩ b * b⁻¹ ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
  refine mul_inv_mem_center_of_commute ?_
  rw [← hb]
  exact hD.thetaBarAct_comm he hf

theorem mk_c_mem_center (hD : DiagHyp c L E) :
    QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hD.mem_L⟩ ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) :=
  mk_mem_center_of_mem_thetaQuotCentralizer hD.c_mem_C

theorem orderOf_mk_c (hD : DiagHyp c L E) :
    orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hD.mem_L⟩) = 3 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [← map_pow]
    have h3 : (⟨c, hD.mem_L⟩ : L) ^ 3 = 1 := Subtype.ext (by simpa using hD.pow_three hD.mem_E)
    rw [h3, map_one]
  · rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact hD.ne_one (hD.eq_one_of_mem_theta hD.mem_E ⟨_, h, rfl⟩)

theorem center_eq_zpowers (hD : DiagHyp c L E) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) =
      Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨c, hD.mem_L⟩) :=
  (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hD.mk_c_mem_center)
    (by rw [hD.card_center, Nat.card_zpowers, hD.orderOf_mk_c])).symm

theorem exists_zpow_mul_mem_theta (hD : DiagHyp c L E) {w : L}
    (hw : QuotientGroup.mk' (aschbacherSolvableCore 3 L) w ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ k : ℤ, (w : G) * c ^ (-k) ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  rw [hD.center_eq_zpowers] at hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
  refine ⟨k, ⟨w * (⟨c, hD.mem_L⟩ : L) ^ (-k), ?_, by simp⟩⟩
  have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L)
      (w * (⟨c, hD.mem_L⟩ : L) ^ (-k)) = 1 := by
    rw [map_mul, map_zpow, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem commutator_mem_zpowers (hD : DiagHyp c L E) {y : G} (hyL : y ∈ L)
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) {e : G} (he : e ∈ E) :
    y * e * y⁻¹ * e⁻¹ ∈ Subgroup.zpowers c := by
  apply hD.mem_zpowers_of_mem_L
  · exact E.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN e).mp he) (E.inv_mem he)
  · have h1 : e * y⁻¹ * e⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer he) _).mp (L.inv_mem hyL)
    have e1 : y * e * y⁻¹ * e⁻¹ = y * (e * y⁻¹ * e⁻¹) := by group
    rw [e1]
    exact L.mul_mem hyL h1

theorem exists_lift_normalizer (hD : DiagHyp c L E) (x : L)
    (hx : ∀ e (he : e ∈ E), thetaBarAct L ⟨e, hD.le_normalizer he⟩
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x) *
        (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x)⁻¹ ∈
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ y : L, QuotientGroup.mk' (aschbacherSolvableCore 3 L) y =
        QuotientGroup.mk' (aschbacherSolvableCore 3 L) x ∧
      (y : G) ∈ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set T : Subgroup G := inSubgroup (aschbacherSolvableCore 3) L with hT
  have hET : E ≤ Subgroup.normalizer (T : Set G) := fun e he =>
    Subgroup.mem_normalizer_fintype fun n hn =>
      conj_mem_inSubgroup_theta (hD.le_normalizer he) hn
  have hdisj : T ⊓ E = ⊥ := by
    rw [inf_comm]
    exact inf_inSubgroup_theta_eq_bot hD.isPGroup
  have hT3 : ¬ 3 ∣ Nat.card T := by
    rw [hT, show Nat.card (inSubgroup (aschbacherSolvableCore 3) L) =
      Nat.card (aschbacherSolvableCore 3 L) from
        Subgroup.card_map_of_injective L.subtype_injective]
    exact three_not_dvd_card_aschbacherSolvableCore
  have hfac : (Nat.card (T ⊔ E : Subgroup G)).factorization 3 = 3 := by
    rw [CentralCover.card_sup_eq_mul_of_le_normalizer hET hdisj, hD.isE27.2,
      show Nat.card T * 27 = 3 * (9 * Nat.card T) by ring]
    exact KFacts.factorization_three_mul_nine_mul hT3
  have hSylE : IsSylowOf 3 E (T ⊔ E) :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_sup_right (by rw [hD.isE27.2, hfac]; norm_num)
  have hxE : ∀ e ∈ E, (x : G) * e * (x : G)⁻¹ ∈ T ⊔ E := by
    intro e he
    have heN := hD.le_normalizer he
    have hw : (x : G) * e * (x : G)⁻¹ * e⁻¹ ∈ L := by
      have h1 : e * (x : G)⁻¹ * e⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp heN _).mp (L.inv_mem x.2)
      have e1 : (x : G) * e * (x : G)⁻¹ * e⁻¹ = x * (e * (x : G)⁻¹ * e⁻¹) := by group
      rw [e1]
      exact L.mul_mem x.2 h1
    have hwZ : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (⟨_, hw⟩ : L) ∈
        Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      have h3 : thetaBarAct L ⟨e, heN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x) =
          QuotientGroup.mk' (aschbacherSolvableCore 3 L) (L.normalizerMonoidHom ⟨e, heN⟩ x) :=
        thetaBarAct_mk _ _
      have h4 : (⟨_, hw⟩ : L) = x * (L.normalizerMonoidHom ⟨e, heN⟩ x)⁻¹ := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
        group
      rw [h4, map_mul, map_inv, ← h3]
      have h5 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) x *
          (thetaBarAct L ⟨e, heN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x))⁻¹ =
          (thetaBarAct L ⟨e, heN⟩ (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x) *
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L) x)⁻¹)⁻¹ := by group
      rw [h5]
      exact Subgroup.inv_mem _ (hx e he)
    obtain ⟨k, hk⟩ := hD.exists_zpow_mul_mem_theta hwZ
    have e2 : (x : G) * e * (x : G)⁻¹ =
        ((x : G) * e * (x : G)⁻¹ * e⁻¹ * c ^ (-k)) * (c ^ k * e) := by group
    rw [e2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
      (Subgroup.mem_sup_right (E.mul_mem (E.zpow_mem hD.mem_E k) he))
  set E' := E.map (MulAut.conj (x : G)).toMonoidHom with hE'
  have hE'X : E' ≤ T ⊔ E := by
    rintro _ ⟨e, he, rfl⟩
    exact hxE e he
  have hE'card : Nat.card E' = 27 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.conj (x : G)).injective, hD.isE27.2]
  have hSylE' : IsSylowOf 3 E' (T ⊔ E) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hE'X (by rw [hE'card, hfac]; norm_num)
  obtain ⟨k, hk, hkE⟩ := hSylE.exists_mem_conj hSylE'
  have hk' : k ∈ ((T ⊔ E : Subgroup G) : Set G) := hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left T E hET] at hk'
  obtain ⟨n, hn, e', he', rfl⟩ := hk'
  obtain ⟨n₀, hn₀, rfl⟩ := hn
  refine ⟨n₀⁻¹ * x, ?_, ?_⟩
  · have h0 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) n₀ = 1 :=
      (QuotientGroup.eq_one_iff n₀).mpr hn₀
    rw [map_mul, map_inv, h0, inv_one, one_mul]
  · refine Subgroup.mem_normalizer_fintype fun e he => ?_
    have h1 := (hkE _).mp ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
    have h2 : ((n₀⁻¹ * x : L) : G) * e * ((n₀⁻¹ * x : L) : G)⁻¹ =
        e' * ((L.subtype n₀ * e')⁻¹ * ((x : G) * e * (x : G)⁻¹) * (L.subtype n₀ * e')) *
          e'⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
      group
    rw [h2]
    exact E.mul_mem (E.mul_mem he' h1) (E.inv_mem he')

theorem card_sup_eq_nine (hD : DiagHyp c L E) {e₁ : G} (he₁ : e₁ ∈ E)
    (h₁ : e₁ ∉ Subgroup.zpowers c) :
    Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers e₁ : Subgroup G) = 9 := by
  have he₁3 : orderOf e₁ = 3 :=
    orderOf_eq_prime (hD.pow_three he₁) fun h => h₁ (h ▸ Subgroup.one_mem _)
  have hcen : e₁ ∈ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((Commute.zpow_left (hD.comm hD.mem_E he₁) k)).eq
  obtain ⟨h9, -, -⟩ := card_sup_zpowers_of_disjoint hcen inferInstance
    (fun w hw => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hD.pow_three hD.mem_E,
        one_zpow])
    he₁3 (inf_zpowers_eq_bot_of_not_mem he₁3 h₁)
  rwa [Nat.card_zpowers, hD.orderOf_c] at h9

theorem eq_sup_of_not_mem (hD : DiagHyp c L E) {e₁ e₂ : G} (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E)
    (h₁ : e₁ ∉ Subgroup.zpowers c) (h₂ : e₂ ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers e₁) :
    Subgroup.zpowers c ⊔ Subgroup.zpowers e₁ ⊔ Subgroup.zpowers e₂ = E :=
  eq_of_card_nine_lt hD.isE27.2
    (sup_le (sup_le (Subgroup.zpowers_le.mpr hD.mem_E) (Subgroup.zpowers_le.mpr he₁))
      (Subgroup.zpowers_le.mpr he₂))
    le_sup_left (hD.card_sup_eq_nine he₁ h₁) (Subgroup.mem_sup_right (Subgroup.mem_zpowers e₂)) h₂

theorem exists_basis (hD : DiagHyp c L E) :
    ∃ e₁ ∈ E, ∃ e₂ ∈ E, e₁ ∉ Subgroup.zpowers c ∧
      e₂ ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers e₁ := by
  obtain ⟨e₁, he₁, h₁⟩ : ∃ e₁ ∈ E, e₁ ∉ Subgroup.zpowers c := by
    by_contra hcon
    push Not at hcon
    have h := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers c from hcon)
    rw [hD.isE27.2, Nat.card_zpowers, hD.orderOf_c] at h
    omega
  obtain ⟨e₂, he₂, h₂⟩ : ∃ e₂ ∈ E, e₂ ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers e₁ := by
    by_contra hcon
    push Not at hcon
    have h := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers e₁ from hcon)
    rw [hD.isE27.2, hD.card_sup_eq_nine he₁ h₁] at h
    omega
  exact ⟨e₁, he₁, e₂, he₂, h₁, h₂⟩

theorem commutator_ne_one (hD : DiagHyp c L E) (hFE : partTwoF G = partTwoE G)
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hev : 2 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L))
    {e₁ e₂ : G} (he₁ : e₁ ∈ E) (he₂ : e₂ ∈ E) (h₁ : e₁ ∉ Subgroup.zpowers c)
    (h₂ : e₂ ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers e₁)
    {x₁ x₂ : L ⧸ aschbacherSolvableCore 3 L}
    (hx₁ : thetaBarAct L ⟨e₁, hD.le_normalizer he₁⟩ = MulAut.conj x₁)
    (hx₂ : thetaBarAct L ⟨e₂, hD.le_normalizer he₂⟩ = MulAut.conj x₂)
    (hx₁3 : x₁ ^ 3 = 1) (hx₂3 : x₂ ^ 3 = 1) : x₁ * x₂ ≠ x₂ * x₁ := by
  intro hcomm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEsup := hD.eq_sup_of_not_mem he₁ he₂ h₁ h₂
  have hc1 : thetaBarAct L ⟨c, hD.le_normalizer hD.mem_E⟩ = 1 :=
    (mem_thetaQuotCentralizer_iff_thetaBarAct _).mp hD.c_mem_C
  have hconj : ∀ a b : L ⧸ aschbacherSolvableCore 3 L, a * b = b * a → MulAut.conj a b = b :=
    fun a b hab => by rw [MulAut.conj_apply, hab, mul_inv_cancel_right]
  have hfixE : ∀ xb ∈ ({x₁, x₂} : Set (L ⧸ aschbacherSolvableCore 3 L)), E ≤ fixer L xb := by
    intro xb hxb
    have h1 : MulAut.conj x₁ xb = xb := by
      rcases hxb with rfl | rfl
      · exact hconj _ _ rfl
      · exact hconj _ _ hcomm
    have h2 : MulAut.conj x₂ xb = xb := by
      rcases hxb with rfl | rfl
      · exact hconj _ _ hcomm.symm
      · exact hconj _ _ rfl
    rw [← hEsup]
    refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
    · exact ⟨hD.le_normalizer hD.mem_E, by rw [hc1, MulAut.one_apply]⟩
    · exact ⟨hD.le_normalizer he₁, by rw [hx₁, h1]⟩
    · exact ⟨hD.le_normalizer he₂, by rw [hx₂, h2]⟩
  have hfix : ∀ xb ∈ ({x₁, x₂} : Set (L ⧸ aschbacherSolvableCore 3 L)), ∀ d (hd : d ∈ E),
      thetaBarAct L ⟨d, hD.le_normalizer hd⟩ xb = xb := by
    intro xb hxb d hd
    obtain ⟨_, h⟩ := mem_fixer_iff.mp (hfixE xb hxb hd)
    exact h
  have hx₁1 : x₁ ≠ 1 := by
    rintro rfl
    exact h₁ (hD.mem_zpowers_of_thetaBarAct he₁ (by rw [hx₁, map_one]))
  have hx₂1 : x₂ ≠ 1 := by
    rintro rfl
    exact h₂ (Subgroup.mem_sup_left (hD.mem_zpowers_of_thetaBarAct he₂ (by rw [hx₂, map_one])))
  have hx₁o : orderOf x₁ = 3 := orderOf_eq_prime hx₁3 hx₁1
  have hx₂o : orderOf x₂ = 3 := orderOf_eq_prime hx₂3 hx₂1
  obtain ⟨w₁, hw₁, hw₁3, hw₁E⟩ := exists_lift_fixed_pow_three hD.isPGroup hD.le_normalizer x₁
    hx₁o (hfix x₁ (Set.mem_insert _ _))
  have hw₁act : thetaBarAct L ⟨(w₁ : G), Subgroup.le_normalizer w₁.2⟩ = MulAut.conj x₁ := by
    rw [thetaBarAct_of_mem w₁.2, ← hw₁]
  have hw₁1 : (w₁ : G) ≠ 1 := by
    intro h
    have h' : w₁ = 1 := Subtype.ext h
    rw [h', map_one] at hw₁
    exact hx₁1 hw₁.symm
  have hw₁o : orderOf (w₁ : G) = 3 := orderOf_eq_prime hw₁3 hw₁1
  have hw₁notE : (w₁ : G) ∉ E := by
    intro h
    have hz := hD.mem_zpowers_of_mem_L h w₁.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hk' : w₁ = (⟨c, hD.mem_L⟩ : L) ^ k := Subtype.ext (by simp [hk])
    have hxZ : x₁ ∈ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) := by
      rw [← hw₁, hk', map_zpow]
      exact Subgroup.zpow_mem _ hD.mk_c_mem_center k
    apply h₁
    apply hD.mem_zpowers_of_thetaBarAct he₁
    rw [hx₁]
    exact conj_eq_one_of_mem_center hxZ
  have hw₁cen : (w₁ : G) ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact hw₁E h hh
  obtain ⟨-, hE₁c, hE₁e⟩ := card_sup_zpowers_of_disjoint hw₁cen hD.isE27.1.1 hD.isE27.1.2 hw₁o
    (inf_zpowers_eq_bot_of_not_mem hw₁o hw₁notE)
  set E₁ := E ⊔ Subgroup.zpowers (w₁ : G) with hE₁
  have hE₁3 : IsPGroup 3 E₁ := fun x => ⟨1, Subtype.ext (by simpa using hE₁e x x.2)⟩
  have hE₁N : E₁ ≤ Subgroup.normalizer (L : Set G) :=
    sup_le hD.le_normalizer (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer w₁.2))
  have hE₁fix : E₁ ≤ fixer L x₂ := by
    refine sup_le (hfixE x₂ (Set.mem_insert_of_mem _ rfl)) (Subgroup.zpowers_le.mpr ?_)
    exact ⟨Subgroup.le_normalizer w₁.2, by rw [hw₁act]; exact hconj _ _ hcomm⟩
  obtain ⟨w₂, hw₂, hw₂3, hw₂E⟩ := exists_lift_fixed_pow_three hE₁3 hE₁N x₂ hx₂o
    (fun d hd => by obtain ⟨_, h⟩ := mem_fixer_iff.mp (hE₁fix hd); exact h)
  have hw₂act : thetaBarAct L ⟨(w₂ : G), Subgroup.le_normalizer w₂.2⟩ = MulAut.conj x₂ := by
    rw [thetaBarAct_of_mem w₂.2, ← hw₂]
  have cE₁ : ∀ d ∈ E, Commute d (w₁ : G) := fun d hd => hw₁E d hd
  have cE₂ : ∀ d ∈ E, Commute d (w₂ : G) := fun d hd => hw₂E d (Subgroup.mem_sup_left hd)
  have c12 : Commute (w₁ : G) (w₂ : G) :=
    hw₂E _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  set u₁ := e₁ * (w₁ : G)⁻¹ with hu₁
  set u₂ := e₂ * (w₂ : G)⁻¹ with hu₂
  have huC : ∀ {e : G} (he : e ∈ E) (w : L) {xb : L ⧸ aschbacherSolvableCore 3 L},
      thetaBarAct L ⟨e, hD.le_normalizer he⟩ = MulAut.conj xb →
      thetaBarAct L ⟨(w : G), Subgroup.le_normalizer w.2⟩ = MulAut.conj xb →
      e * (w : G)⁻¹ ∈ Sec4.thetaQuotCentralizer L := by
    intro e he w xb h1 h2
    have hN : e * (w : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      mul_mem (hD.le_normalizer he) (inv_mem (Subgroup.le_normalizer w.2))
    rw [mem_thetaQuotCentralizer_iff_thetaBarAct hN]
    have e1 : (⟨e * (w : G)⁻¹, hN⟩ : Subgroup.normalizer (L : Set G)) =
        ⟨e, hD.le_normalizer he⟩ * (⟨(w : G), Subgroup.le_normalizer w.2⟩)⁻¹ := rfl
    rw [e1, map_mul, map_inv, h1, h2, mul_inv_cancel]
  have hu₁C : u₁ ∈ Sec4.thetaQuotCentralizer L := huC he₁ w₁ hx₁ hw₁act
  have hu₂C : u₂ ∈ Sec4.thetaQuotCentralizer L := huC he₂ w₂ hx₂ hw₂act
  have hu3 : ∀ {e : G} (he : e ∈ E) (w : L), Commute e (w : G) → (w : G) ^ 3 = 1 →
      (e * (w : G)⁻¹) ^ 3 = 1 := by
    intro e he w hc hw3
    rw [(hc.inv_right).mul_pow, hD.pow_three he, one_mul, inv_pow, hw3, inv_one]
  have hu₁c : u₁ ∉ Subgroup.zpowers c := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    have he₁' : e₁ = c ^ k * w₁ := by rw [hk, hu₁, inv_mul_cancel_right]
    apply h₁
    apply hD.mem_zpowers_of_mem_L he₁
    rw [he₁']
    exact L.mul_mem (L.zpow_mem hD.mem_L k) w₁.2
  have hu₁o : orderOf u₁ = 3 :=
    orderOf_eq_prime (hu3 he₁ w₁ (cE₁ e₁ he₁) hw₁3) fun h => hu₁c (h ▸ Subgroup.one_mem _)
  set T₁ := Subgroup.zpowers c ⊔ Subgroup.zpowers e₁ with hT₁
  set T₂ := Subgroup.zpowers (w₁ : G) ⊔ Subgroup.zpowers (w₂ : G) with hT₂
  have hT₁E : T₁ ≤ E :=
    sup_le (Subgroup.zpowers_le.mpr hD.mem_E) (Subgroup.zpowers_le.mpr he₁)
  have hT₂L : T₂ ≤ L := sup_le (Subgroup.zpowers_le.mpr w₁.2) (Subgroup.zpowers_le.mpr w₂.2)
  have hT₂N : T₂ ≤ Subgroup.normalizer (T₁ : Set G) := by
    have hcen' : ∀ w : G, (∀ d ∈ E, Commute d w) → w ∈ Subgroup.normalizer (T₁ : Set G) :=
      fun w hw => Subgroup.mem_normalizer_fintype fun d hd => by
        rw [(hw d (hT₁E hd)).eq.symm, mul_inv_cancel_right]
        exact hd
    exact sup_le (Subgroup.zpowers_le.mpr (hcen' _ cE₁)) (Subgroup.zpowers_le.mpr (hcen' _ cE₂))
  have hu₂B : u₂ ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers u₁ := by
    intro h
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers u₁ ≤ T₁ ⊔ T₂ := by
      refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)))) (Subgroup.zpowers_le.mpr ?_)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers e₁))) (Subgroup.inv_mem _ (Subgroup.mem_sup_right
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))))
    have he₂T : e₂ ∈ ((T₁ ⊔ T₂ : Subgroup G) : Set G) := by
      have : e₂ = u₂ * w₂ := by rw [hu₂, inv_mul_cancel_right]
      rw [this]
      exact Subgroup.mul_mem _ (hle h)
        (Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))
    rw [Subgroup.coe_mul_of_right_le_normalizer_left T₁ T₂ hT₂N] at he₂T
    obtain ⟨a, ha, b, hb, hab⟩ := he₂T
    have hbE : b ∈ E := by
      have : b = a⁻¹ * e₂ := by rw [← hab, inv_mul_cancel_left]
      rw [this]
      exact E.mul_mem (E.inv_mem (hT₁E ha)) he₂
    have hbc := hD.mem_zpowers_of_mem_L hbE (hT₂L hb)
    apply h₂
    rw [← hab]
    exact Subgroup.mul_mem _ ha (Subgroup.mem_sup_left hbc)
  have hu₂o : orderOf u₂ = 3 :=
    orderOf_eq_prime (hu3 he₂ w₂ (cE₂ e₂ he₂) hw₂3) fun h => hu₂B (h ▸ Subgroup.one_mem _)
  have cu : ∀ {e : G} (he : e ∈ E) (w : L), (∀ d ∈ E, Commute d (w : G)) →
      Commute c (e * (w : G)⁻¹) := fun he w hw =>
    (hD.commute hD.mem_E he).mul_right (hw c hD.mem_E).inv_right
  have hu₁cen : u₁ ∈ Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((cu he₁ w₁ cE₁).zpow_left k).eq
  obtain ⟨hB9, hBc, hBe⟩ := card_sup_zpowers_of_disjoint hu₁cen inferInstance
    (fun w hw => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hD.pow_three hD.mem_E,
        one_zpow])
    hu₁o (inf_zpowers_eq_bot_of_not_mem hu₁o hu₁c)
  have hu₂cen : u₂ ∈ Subgroup.centralizer
      ((Subgroup.zpowers c ⊔ Subgroup.zpowers u₁ : Subgroup G) : Set G) := by
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers u₁ ≤ Subgroup.centralizer {u₂} := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (cu he₂ w₂ cE₂).eq
      · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        have h1 : Commute e₁ u₂ := (hD.commute he₁ he₂).mul_right (cE₂ e₁ he₁).inv_right
        have h2 : Commute (w₁ : G)⁻¹ u₂ := ((cE₁ e₂ he₂).symm.mul_right
          c12.inv_right).inv_left
        exact (h1.mul_left h2).eq
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh))
  rw [Nat.card_zpowers, hD.orderOf_c] at hB9
  obtain ⟨hB27, hB'c, hB'e⟩ := card_sup_zpowers_of_disjoint hu₂cen hBc hBe hu₂o
    (inf_zpowers_eq_bot_of_not_mem hu₂o hu₂B)
  refine false_of_E27_le_thetaQuotCentralizer hFE hperf hD.card_center hev ⟨hB'c, hB'e⟩
    (by rw [hB27, hB9]) ?_
  refine sup_le (sup_le ?_ ?_) ?_ <;> rw [Subgroup.zpowers_le]
  · exact hD.c_mem_C
  · exact hu₁C
  · exact hu₂C

theorem conj_eq_self_iff (hD : DiagHyp c L E) (y : L)
    (hyN : (y : G) ∈ Subgroup.normalizer (E : Set G)) {e : G} (he : e ∈ E)
    {b : L ⧸ aschbacherSolvableCore 3 L}
    (hb : thetaBarAct L ⟨e, hD.le_normalizer he⟩ = MulAut.conj b) :
    (y : G) * e * (y : G)⁻¹ = e ↔
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) y * b =
        b * QuotientGroup.mk' (aschbacherSolvableCore 3 L) y := by
  have hw := hD.commutator_mem_zpowers y.2 hyN he
  have hcL : Subgroup.zpowers c ≤ L := Subgroup.zpowers_le.mpr hD.mem_L
  have hcE : Subgroup.zpowers c ≤ E := Subgroup.zpowers_le.mpr hD.mem_E
  have hwL : (y : G) * e * (y : G)⁻¹ * e⁻¹ ∈ L := hcL hw
  have hπw := mk_commutator_eq y (hD.le_normalizer he) hwL
  rw [hb, MulAut.conj_apply] at hπw
  constructor
  · intro h
    have h1 : (y : G) * e * (y : G)⁻¹ * e⁻¹ = 1 := by rw [h, mul_inv_cancel]
    have h2 : (⟨_, hwL⟩ : L) = 1 := Subtype.ext h1
    rw [h2, map_one] at hπw
    have h3 := mul_inv_eq_one.mp hπw.symm
    calc QuotientGroup.mk' (aschbacherSolvableCore 3 L) y * b =
        (b * QuotientGroup.mk' (aschbacherSolvableCore 3 L) y * b⁻¹) * b := by rw [← h3]
      _ = b * QuotientGroup.mk' (aschbacherSolvableCore 3 L) y := by group
  · intro h
    have h2 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) (⟨_, hwL⟩ : L) = 1 := by
      rw [hπw, mul_inv_eq_one, ← h]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 : (y : G) * e * (y : G)⁻¹ * e⁻¹ = 1 := hD.eq_one_of_mem_theta (hcE hw) ⟨_, h2, rfl⟩
    calc (y : G) * e * (y : G)⁻¹ = ((y : G) * e * (y : G)⁻¹ * e⁻¹) * e := by group
      _ = e := by rw [h3, one_mul]

theorem nine_le_card_autIn (hD : DiagHyp c L E) (hFE : partTwoF G = partTwoE G)
    (hperf : commutator (L ⧸ aschbacherSolvableCore 3 L) = ⊤)
    (hev : 2 ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L)) {P : Subgroup G}
    (hP : IsSylowOf 3 P (Subgroup.normalizer (E : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G))) :
    9 ≤ Nat.card (Sec4.autIn P E) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := Subgroup.normalizer (E : Set G) with hW
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  obtain ⟨e₁, he₁, e₂, he₂, h₁, h₂⟩ := hD.exists_basis
  obtain ⟨l₁, hl₁3, hl₁, -⟩ := hD.exists_part he₁
  obtain ⟨l₂, hl₂3, hl₂, -⟩ := hD.exists_part he₂
  have hcube : ∀ l : L, (l : G) ^ 3 = 1 →
      QuotientGroup.mk' (aschbacherSolvableCore 3 L) l ^ 3 = 1 := fun l hl => by
    rw [← map_pow]
    have hl' : l ^ 3 = 1 := Subtype.ext (by simpa using hl)
    rw [hl', map_one]
  have hnc := hD.commutator_ne_one hFE hperf hev he₁ he₂ h₁ h₂ hl₁ hl₂ (hcube l₁ hl₁3)
    (hcube l₂ hl₂3)
  obtain ⟨y₁, hy₁, hy₁N⟩ := hD.exists_lift_normalizer l₁ fun e he =>
    hD.thetaBarAct_mul_inv_mem_center he he₁ hl₁
  obtain ⟨y₂, hy₂, hy₂N⟩ := hD.exists_lift_normalizer l₂ fun e he =>
    hD.thetaBarAct_mul_inv_mem_center he he₂ hl₂
  set c' : E := ⟨c, hD.mem_E⟩ with hc'
  set τ₁ := E.normalizerMonoidHom ⟨(y₁ : G), hy₁N⟩ with hτ₁
  set τ₂ := E.normalizerMonoidHom ⟨(y₂ : G), hy₂N⟩ with hτ₂
  have hyH : ∀ y : L, (y : G) ∈ H := fun y =>
    Sec13.le_normalizer_zpowers_of_mem hD.mem_thetaComponentsAt y.2
  have hτK : ∀ (y : L) (hyN : (y : G) ∈ W),
      E.normalizerMonoidHom ⟨(y : G), hyN⟩ ∈ Sec4.autIn (W ⊓ H) E :=
    fun y hyN => Sec4.mem_autIn_iff.mpr ⟨y, hyN, ⟨hyN, hyH y⟩, rfl⟩
  have hτT : ∀ (y : L) (hyN : (y : G) ∈ W),
      E.normalizerMonoidHom ⟨(y : G), hyN⟩ ∈ transvectionGroup E c' := by
    intro y hyN
    refine ⟨Subtype.ext ?_, fun a => ?_⟩
    · rw [Sec4.normalizerMonoidHom_apply_coe]
      have hyc : (y : G) * c = c * y :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer y.2))
      rw [hyc, mul_inv_cancel_right]
    · rw [mem_zpowers_subtype_iff, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
        Subgroup.coe_inv]
      exact hD.commutator_mem_zpowers y.2 hyN a.2
  have hval : ∀ (y : L) (hyN : (y : G) ∈ W) {e : G} (he : e ∈ E),
      E.normalizerMonoidHom ⟨(y : G), hyN⟩ ⟨e, he⟩ = ⟨e, he⟩ ↔
        (y : G) * e * (y : G)⁻¹ = e := by
    intro y hyN e he
    constructor
    · intro h
      have h' := congrArg Subtype.val h
      rwa [Sec4.normalizerMonoidHom_apply_coe] at h'
    · intro h
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      exact h
  have h11 : τ₁ ⟨e₁, he₁⟩ = ⟨e₁, he₁⟩ :=
    (hval y₁ hy₁N he₁).mpr ((hD.conj_eq_self_iff y₁ hy₁N he₁ hl₁).mpr (by rw [hy₁]))
  have h12 : τ₁ ⟨e₂, he₂⟩ ≠ ⟨e₂, he₂⟩ := fun h =>
    hnc (hy₁ ▸ (hD.conj_eq_self_iff y₁ hy₁N he₂ hl₂).mp ((hval y₁ hy₁N he₂).mp h))
  have h21 : τ₂ ⟨e₁, he₁⟩ ≠ ⟨e₁, he₁⟩ := fun h =>
    hnc (hy₂ ▸ (hD.conj_eq_self_iff y₂ hy₂N he₁ hl₁).mp ((hval y₂ hy₂N he₁).mp h)).symm
  set Y := Subgroup.closure ({τ₁, τ₂} : Set (MulAut E)) with hY
  have hYK : Y ≤ Sec4.autIn (W ⊓ H) E := by
    rw [hY, Subgroup.closure_le]
    rintro σ (rfl | rfl)
    · exact hτK y₁ hy₁N
    · exact hτK y₂ hy₂N
  have hYT : Y ≤ transvectionGroup E c' := by
    rw [hY, Subgroup.closure_le]
    rintro σ (rfl | rfl)
    · exact hτT y₁ hy₁N
    · exact hτT y₂ hy₂N
  have hc'3 : c' ^ 3 = 1 := Subtype.ext (by simpa using hD.pow_three hD.mem_E)
  have hY3 : IsPGroup 3 Y := fun σ =>
    ⟨1, Subtype.ext (by simpa using pow_three_eq_one_of_mem_transvectionGroup hc'3 (hYT σ.2))⟩
  have hτ₁Y : τ₁ ∈ Y := Subgroup.subset_closure (Set.mem_insert _ _)
  have hτ₂Y : τ₂ ∈ Y := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hτ₁o : orderOf τ₁ = 3 :=
    orderOf_eq_prime (pow_three_eq_one_of_mem_transvectionGroup hc'3 (hτT y₁ hy₁N))
      fun h => h12 (by rw [h, MulAut.one_apply])
  have hτ₂n : τ₂ ∉ Subgroup.zpowers τ₁ := by
    intro h
    have hle : Subgroup.zpowers τ₁ ≤ MulAction.stabilizer (MulAut E) (⟨e₁, he₁⟩ : E) :=
      Subgroup.zpowers_le.mpr (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact h11)
    have h' := hle h
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h'
    exact h21 h'
  have h9Y : 9 ≤ Nat.card Y := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY3
    have hle : Subgroup.zpowers τ₁ ≤ Y := Subgroup.zpowers_le.mpr hτ₁Y
    rw [hk]
    by_contra hcon
    push Not at hcon
    have hk1 : k ≤ 1 := by
      by_contra hk2
      push Not at hk2
      have : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      omega
    have hYeq : Subgroup.zpowers τ₁ = Y := Subgroup.eq_of_le_of_card_ge hle (by
      rw [hk, Nat.card_zpowers, hτ₁o]
      calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
        _ = 3 := by norm_num)
    exact hτ₂n (hYeq ▸ hτ₂Y)
  have hPW : P ≤ W := hP.le.trans inf_le_left
  have hPW' : IsSylowOf 3 (P.subgroupOf W) ((W ⊓ H).subgroupOf W) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff W, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPW, inf_eq_left.mpr inf_le_left]
    exact hP
  have hS := IsSylowOf.map hPW' E.normalizerMonoidHom
  have e1 : Sec4.autIn P E = (P.subgroupOf W).map E.normalizerMonoidHom := by
    rw [Sec4.autIn, inf_eq_left.mpr hPW]
  have e2 : Sec4.autIn (W ⊓ H) E = ((W ⊓ H).subgroupOf W).map E.normalizerMonoidHom := by
    rw [Sec4.autIn, inf_eq_left.mpr (inf_le_left : W ⊓ H ≤ W)]
  rw [← e1, ← e2] at hS
  exact h9Y.trans (card_le_of_isSylowOf hS hYK hY3)

end DiagHyp

end CFSG.RankThree.PartTwo.Sec12.Item125Diag
