module

public import CFSG.RankThree.GF2n.Tim79aCitedInvol
public import CFSG.LargeExtraspecial.Timmesfeld.FStarBasic
public import CFSG.CGT.T75H.QuatZ
public import CFSG.CGT.T75H.Setup

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.CGT.T75H CFSG.RankThree.GF2n.Tim79a
  CFSG.LargeExtraspecial.Timmesfeld

open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

abbrev H (z : G) : Subgroup G :=
  Subgroup.centralizer ({z} : Set G)

abbrev Q (z : G) : Subgroup G :=
  Qa z

abbrev ZQ (z : G) : Subgroup G :=
  centerIn (Qa z)

class Setting (z : G) (E F : Subgroup G) : Prop where
  hyp : StrothHyp z E F
  normal_Q : ((Qa z).subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal

instance instNormalQH (z : G) : ((Q z).subgroupOf (H z)).Normal :=
  fStar_subgroupOf_normal (H z)

instance instNormalZQ (z : G) : ((ZQ z).subgroupOf (Q z)).Normal := by
  have hcenter : (ZQ z).subgroupOf (Q z) = Subgroup.center ↥(Q z) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hxc : (x : G) ∈ Subgroup.centralizer (Q z : Set G) := (Subgroup.mem_inf.mp hx).2
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (y : G) y.2)
    · intro hx
      rw [Subgroup.mem_subgroupOf]
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx (⟨y, hy⟩ : ↥(Q z)))
  rw [hcenter]
  infer_instance

theorem Setting.ofHyp (h : StrothHyp z E F) : Setting z E F :=
  ⟨h, fStar_subgroupOf_normal (H z)⟩

theorem z_mem_H (z : G) : z ∈ H z := by
  rw [H, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff.mp hy]

theorem Q_le_H (S : Setting z E F) : Q z ≤ H z :=
  fStar_le (H z)

theorem Q_eq_sup (S : Setting z E F) : Q z = E ⊔ F :=
  S.hyp.sup_eq.symm

theorem E_le_Q (S : Setting z E F) : E ≤ Q z := by
  rw [Q_eq_sup S]
  exact le_sup_left

theorem F_le_Q (S : Setting z E F) : F ≤ Q z := by
  rw [Q_eq_sup S]
  exact le_sup_right

theorem z_mem_Q (S : Setting z E F) : z ∈ Q z := by
  have hzF : z ∈ F := Subgroup.commutator_le_self F S.hyp.mem_derived
  exact F_le_Q S hzF

theorem F_deriv_eq_zpowers (S : Setting z E F) : ⁅F, F⁆ = Subgroup.zpowers z := by
  have hcard : Nat.card (⁅F, F⁆ : Subgroup G) = 2 := S.hyp.extraspecial.2.2
  have hcardz : Nat.card (Subgroup.zpowers z) = 2 := by
    rw [Nat.card_zpowers, S.hyp.orderOf_z]
  have hle : Subgroup.zpowers z ≤ ⁅F, F⁆ := Subgroup.zpowers_le.mpr S.hyp.mem_derived
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hcardz])).symm

theorem F_centerIn_eq (S : Setting z E F) : centerIn F = Subgroup.zpowers z := by
  rw [centerIn_eq_map_center, ← S.hyp.extraspecial.2.1, F_deriv_eq_zpowers S]

theorem Q_deriv_eq (S : Setting z E F) : ⁅Q z, Q z⁆ = Subgroup.zpowers z := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a :=
    fun a ha b hb => (S.hyp.commute a ha b hb).eq
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
    fun a ha b hb =>
      congrArg Subtype.val (S.hyp.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine le_antisymm ?_ ?_
  · rw [Q_eq_sup S]
    refine (Subgroup.commutator_le).mpr ?_
    intro x hx y hy
    obtain ⟨e1, he1, f1, hf1, rfl⟩ := exists_mul_of_mem_sup_of_comm hcomm hx
    obtain ⟨e2, he2, f2, hf2, rfl⟩ := exists_mul_of_mem_sup_of_comm hcomm hy
    have he1e2 : Commute e1 e2 := hEab e1 he1 e2 he2
    have hzero1 : ⁅e1, e2 * f2⁆ = 1 :=
      (he1e2.mul_right (S.hyp.commute e1 he1 f2 hf2)).commutator_eq
    have hzero2 : ⁅f1, e2⁆ = 1 :=
      (S.hyp.commute e2 he2 f1 hf1).symm.commutator_eq
    have he1_deriv : Commute e1 ⁅f1, f2⁆ := by
      have h1 : Commute e1 f1 := S.hyp.commute e1 he1 f1 hf1
      have h2 : Commute e1 f2 := S.hyp.commute e1 he1 f2 hf2
      rw [commutatorElement_def]
      exact ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
    have he2_deriv : Commute e2 ⁅f1, f2⁆ := by
      have h1 : Commute e2 f1 := S.hyp.commute e2 he2 f1 hf1
      have h2 : Commute e2 f2 := S.hyp.commute e2 he2 f2 hf2
      rw [commutatorElement_def]
      exact ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
    have step1 : ⁅e1 * f1, e2 * f2⁆ = e1 * ⁅f1, e2 * f2⁆ * e1⁻¹ := by
      rw [commutatorElement_mul_left_eq_conj_mul, hzero1, mul_one]
    have step2 : ⁅f1, e2 * f2⁆ = ⁅f1, f2⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj, hzero2, one_mul]
      rw [he2_deriv.eq, mul_assoc, mul_inv_cancel, mul_one]
    have hmain : ⁅e1 * f1, e2 * f2⁆ = ⁅f1, f2⁆ := by
      calc
        ⁅e1 * f1, e2 * f2⁆ = e1 * ⁅f1, e2 * f2⁆ * e1⁻¹ := step1
        _ = e1 * ⁅f1, f2⁆ * e1⁻¹ := by rw [step2]
        _ = ⁅f1, f2⁆ := by
          rw [he1_deriv.eq, mul_assoc, mul_inv_cancel, mul_one]
    rw [hmain, ← F_deriv_eq_zpowers S]
    exact Subgroup.commutator_mem_commutator hf1 hf2
  · rw [← F_deriv_eq_zpowers S]
    exact Subgroup.commutator_mono (F_le_Q S) (F_le_Q S)

theorem Q_isPGroup (S : Setting z E F) : IsPGroup 2 (Q z) := by
  have hE : IsPGroup 2 E := fun x =>
    ⟨1, Subtype.ext (by simpa using S.hyp.elemAbelian.2 (x : G) x.2)⟩
  have hF : IsPGroup 2 F := S.hyp.extraspecial.1
  have hFcent : F ≤ Subgroup.centralizer (E : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (S.hyp.commute e he f hf).eq
  have hEF : F ≤ Subgroup.normalizer (E : Set G) :=
    hFcent.trans (Subgroup.centralizer_le_normalizer (E : Set G))
  rw [Q_eq_sup S]
  exact IsPGroup.to_sup_of_normal_left' hE hF hEF

theorem z_mem_ZQ (S : Setting z E F) : z ∈ ZQ z := by
  have hzcenterF : z ∈ centerIn F := by
    rw [F_centerIn_eq S]
    exact Subgroup.mem_zpowers z
  have hzF : z ∈ F := (Subgroup.mem_inf.mp hzcenterF).1
  have hzFcent : z ∈ Subgroup.centralizer (F : Set G) := (Subgroup.mem_inf.mp hzcenterF).2
  refine Subgroup.mem_inf.mpr ⟨F_le_Q S hzF, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  change q ∈ Q z at hq
  rw [Q_eq_sup S] at hq
  obtain ⟨e, he, f, hf, rfl⟩ := exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hq
  have hzf' : f * z = z * f := Subgroup.mem_centralizer_iff.mp hzFcent f hf
  have hze : e * z = z * e := (S.hyp.commute e he z hzF).eq
  calc
    (e * f) * z = e * (f * z) := by group
    _ = e * (z * f) := by rw [hzf']
    _ = (e * z) * f := by group
    _ = (z * e) * f := by rw [hze]
    _ = z * (e * f) := by group

theorem E_le_ZQ (S : Setting z E F) : E ≤ ZQ z := by
  intro e0 he0
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
    fun a ha b hb =>
      congrArg Subtype.val (S.hyp.elemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  refine Subgroup.mem_inf.mpr ⟨E_le_Q S he0, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  change q ∈ Q z at hq
  rw [Q_eq_sup S] at hq
  obtain ⟨e, he, f, hf, rfl⟩ := exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hq
  calc
    (e * f) * e0 = e * (f * e0) := by group
    _ = e * (e0 * f) := by rw [← (S.hyp.commute e0 he0 f hf).eq]
    _ = (e * e0) * f := by group
    _ = (e0 * e) * f := by rw [← hEab e0 he0 e he]
    _ = e0 * (e * f) := by group

theorem ZQ_eq (S : Setting z E F) : ZQ z = E ⊔ Subgroup.zpowers z := by
  refine le_antisymm ?_ ?_
  · intro x hx
    change x ∈ Q z ⊓ Subgroup.centralizer (Q z : Set G) at hx
    obtain ⟨hxQ, hxcent⟩ := hx
    change x ∈ Q z at hxQ
    rw [Q_eq_sup S] at hxQ
    obtain ⟨e, he, f, hf, hxef⟩ := exists_mul_of_mem_sup_of_comm
      (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hxQ
    subst hxef
    have hfcenter : f ∈ centerIn F := by
      refine Subgroup.mem_inf.mpr ⟨hf, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyQ : y ∈ Q z := F_le_Q S hy
      have hxy : y * (e * f) = (e * f) * y :=
        Subgroup.mem_centralizer_iff.mp hxcent y hyQ
      have hfy : f * y = y * f := by
        calc
          f * y = e⁻¹ * ((e * f) * y) := by group
          _ = e⁻¹ * (y * (e * f)) := by rw [← hxy]
          _ = e⁻¹ * (y * e) * f := by group
          _ = e⁻¹ * (e * y) * f := by rw [← (S.hyp.commute e he y hy).eq]
          _ = y * f := by group
      exact hfy.symm
    have hfz : f ∈ Subgroup.zpowers z := by
      rw [← F_centerIn_eq S]
      exact hfcenter
    exact Subgroup.mul_mem_sup he hfz
  · exact sup_le (E_le_ZQ S) (Subgroup.zpowers_le.mpr (z_mem_ZQ S))

theorem card_sup_of_comm {A B : Subgroup G} (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hinf : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun p =>
    ⟨(p.1 : G) * (p.2 : G), Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint (disjoint_iff.mpr hinf)
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro s
    obtain ⟨a, ha, b, hb, hs⟩ := exists_mul_of_mem_sup_of_comm hcomm s.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hs.symm⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

theorem Q_card (S : Setting z E F) : Nat.card (Q z) = Nat.card E * Nat.card F := by
  rw [Q_eq_sup S]
  exact card_sup_of_comm (fun a ha b hb => (S.hyp.commute a ha b hb).eq) S.hyp.inf_eq_bot

theorem ZQ_card (S : Setting z E F) : Nat.card (ZQ z) = Nat.card E * 2 := by
  have hz2 : z ^ 2 = 1 := by
    simpa [S.hyp.orderOf_z] using pow_orderOf_eq_one z
  have hzF : z ∈ F := Subgroup.commutator_le_self F S.hyp.mem_derived
  have hz1 : z ≠ 1 := by
    intro h
    have hord := S.hyp.orderOf_z
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hzE : z ∉ E := by
    intro hzE
    have hmem : z ∈ E ⊓ F := ⟨hzE, hzF⟩
    rw [S.hyp.inf_eq_bot] at hmem
    exact hz1 (Subgroup.mem_bot.mp hmem)
  have hcomm : ∀ a ∈ E, ∀ w ∈ Subgroup.zpowers z, a * w = w * a := by
    intro a ha w hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    rw [← hk]
    exact ((S.hyp.commute a ha z hzF).zpow_right k).eq
  have hinf : E ⊓ Subgroup.zpowers z = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro w hw
    rw [Subgroup.mem_bot]
    obtain ⟨hwE, hwz⟩ := hw
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hwz
    rw [← hk]
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [zpow_mul]
      simp [hz2]
    · exfalso
      apply hzE
      rw [← hk, zpow_add, zpow_mul] at hwE
      simpa [hz2] using hwE
  calc
    Nat.card (ZQ z) = Nat.card (E ⊔ Subgroup.zpowers z : Subgroup G) := by rw [ZQ_eq S]
    _ = Nat.card E * Nat.card (Subgroup.zpowers z) := card_sup_of_comm hcomm hinf
    _ = Nat.card E * 2 := by rw [Nat.card_zpowers, S.hyp.orderOf_z]

theorem sq_mem_ZQ (S : Setting z E F) {x : G} (hx : x ∈ Q z) : x ^ 2 ∈ ZQ z := by
  have hz2 : z ^ 2 = 1 := by
    simpa [S.hyp.orderOf_z] using pow_orderOf_eq_one z
  rw [Q_eq_sup S] at hx
  obtain ⟨e, he, f, hf, hxef⟩ := exists_mul_of_mem_sup_of_comm
    (fun a ha b hb => (S.hyp.commute a ha b hb).eq) hx
  subst hxef
  have he2 : e ^ 2 = 1 := S.hyp.elemAbelian.2 e he
  have he2' : e * e = 1 := by simpa [pow_two] using he2
  have hef : e * f = f * e := (S.hyp.commute e he f hf).eq
  have hsq : (e * f) ^ 2 = f ^ 2 := by
    rw [pow_two, pow_two]
    calc
      (e * f) * (e * f) = e * (f * e) * f := by group
      _ = e * (e * f) * f := by rw [hef]
      _ = (e * e) * (f * f) := by group
      _ = f * f := by rw [he2', one_mul]
  have hf2_center : f ^ 2 ∈ centerIn F := by
    refine Subgroup.mem_inf.mpr ⟨pow_mem hf 2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hc_center : ⁅g, f⁆ ∈ centerIn F := by
      rw [F_centerIn_eq S, ← F_deriv_eq_zpowers S]
      exact Subgroup.commutator_mem_commutator hg hf
    have hc_comm_f : f * ⁅g, f⁆ = ⁅g, f⁆ * f :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc_center).2 f hf
    have hc_sq : ⁅g, f⁆ ^ 2 = 1 := by
      have hc_z : ⁅g, f⁆ ∈ Subgroup.zpowers z := by
        rw [← F_centerIn_eq S]
        exact hc_center
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc_z
      rw [← hk, sq, ← zpow_add, show k + k = 2 * k by ring, zpow_mul]
      simp [hz2]
    have hc_sq' : ⁅g, f⁆ * ⁅g, f⁆ = 1 := by simpa [pow_two] using hc_sq
    have hconj : g * f ^ 2 * g⁻¹ = f ^ 2 := by
      have hconj1 : g * f * g⁻¹ = ⁅g, f⁆ * f := by
        rw [commutatorElement_def]
        group
      calc
        g * f ^ 2 * g⁻¹ = (g * f * g⁻¹) ^ 2 := (conj_pow).symm
        _ = (⁅g, f⁆ * f) ^ 2 := by rw [hconj1]
        _ = f ^ 2 := by
          rw [pow_two]
          calc
            (⁅g, f⁆ * f) * (⁅g, f⁆ * f) = ⁅g, f⁆ * (f * ⁅g, f⁆) * f := by group
            _ = ⁅g, f⁆ * (⁅g, f⁆ * f) * f := by rw [hc_comm_f]
            _ = (⁅g, f⁆ * ⁅g, f⁆) * (f * f) := by group
            _ = f ^ 2 := by rw [hc_sq', one_mul, pow_two]
    calc
      g * f ^ 2 = (g * f ^ 2 * g⁻¹) * g := by group
      _ = f ^ 2 * g := by rw [hconj]
  have hf2_z : f ^ 2 ∈ Subgroup.zpowers z := by
    rw [← F_centerIn_eq S]
    exact hf2_center
  have hf2_ZQ : f ^ 2 ∈ ZQ z := by
    rw [ZQ_eq S]
    exact Subgroup.mem_sup_right hf2_z
  rw [hsq]
  exact hf2_ZQ

abbrev Qbar (z : G) : Type :=
  ↥(Q z) ⧸ (ZQ z).subgroupOf (Q z)

theorem Qbar_isMulCommutative (S : Setting z E F) : IsMulCommutative (Qbar z) := by
  have hcomm : _root_.commutator ↥(Q z) ≤ (ZQ z).subgroupOf (Q z) := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := Q z)]
    rw [Subgroup.map_subtype_commutator,
      Subgroup.map_subgroupOf_eq_of_le (show ZQ z ≤ Q z from inf_le_left)]
    rw [Q_deriv_eq S, ZQ_eq S]
    exact le_sup_right
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm

theorem Qbar_sq_eq_one (S : Setting z E F) (x : Qbar z) : x * x = 1 := by
  obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)) x
  rw [← map_mul]
  change (QuotientGroup.mk (x' * x') : Qbar z) = 1
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  simpa [sq] using sq_mem_ZQ S x'.2

abbrev QbarOf (S : Setting z E F) : Type := Qbar z

instance instCommGroupQbarOf (S : Setting z E F) : CommGroup (QbarOf S) :=
  letI : IsMulCommutative (Qbar z) := Qbar_isMulCommutative S
  IsMulCommutative.instCommGroup

instance instAddCommGroupQbarOf (S : Setting z E F) : AddCommGroup (Additive (QbarOf S)) :=
  inferInstance

noncomputable instance instModuleQbarOf (S : Setting z E F) :
    Module (ZMod 2) (Additive (QbarOf S)) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    simpa [two_nsmul] using Qbar_sq_eq_one S (Additive.toMul x))

end CFSG.RankThree.GF2n.Stroth78
