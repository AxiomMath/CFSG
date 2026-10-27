module

public import CFSG.RankThree.GF2n.Stroth80.Sec713O2XActs
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVSecCard
public import CFSG.RankThree.GF2n.Stroth80.Sec7FormOnRange
public import CFSG.RankThree.GF2n.Stroth80.Sec7SecModEmbed
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommFormFormula
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec711Step2
public import CFSG.RankThree.GF2n.Stroth80.Sec7CommForm
public import CFSG.RankThree.GF2n.Stroth80.Sec7NoInvariantFormProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_conj_section_data_of_comm (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {x : G} (hxM : x ∈ M)
    (hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hxR : ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ hc.CN t)
    (hx2 : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x ^ 2, w⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∃ (Md : Type) (_ : AddCommGroup Md) (_ : DistribMulAction ↥(Rt M (LB M Q B) t) Md)
      (κ : ↥(Wt Q (Vt M (LB M Q B) B Z t)) →* Multiplicative Md)
      (_ : IsSecMod (Rt M (LB M Q B) t) (Wt Q (Vt M (LB M Q B) B Z t))
        (Vt M (LB M Q B) B Z t) Md κ) (S : Md →+ Md),
      (∀ (r : ↥(Rt M (LB M Q B) t)) (a : Md), S (r • a) = r • S a) ∧ (∀ a : Md, S (S a) = a) ∧
      ∀ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)), ∃ w' : ↥(Wt Q (Vt M (LB M Q B) B Z t)),
        (w' : G) = x * w * x⁻¹ ∧ κ w' = Multiplicative.ofAdd (S (Multiplicative.toAdd (κ w))) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hWN := sec7_N_comm_W_le_V h52a hA hc hs
  set V := Vt M (LB M Q B) B Z t with hVdef
  set W := Wt Q V with hWdef
  set R := Rt M (LB M Q B) t with hRdef
  have hVW : V ≤ W := sec7_V_le_W h310chi hc hs
  have hWQ : W ≤ Q := inf_le_left
  have hZV : Z ≤ V := sec39_Z_le_Vt
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRM : R ≤ M := hc.Rt_le_M t
  have hxQn : x ∈ Subgroup.normalizer (Q : Set G) := hQM hxM
  have hnormW : ∀ l, l ∈ Subgroup.normalizer (Q : Set G) →
      l ∈ Subgroup.normalizer (V : Set G) → l ∈ Subgroup.normalizer (W : Set G) :=
    fun l hlQ hlV => Subgroup.mem_normalizer_fintype fun w hw => conj_mem_Wt hlQ hlV hw
  let R' : Subgroup G := Subgroup.normalizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G)
  have hsec : SecHyp R' W V :=
    ⟨hVW, fun a ha b hb => hZV (hc.hyp.toHyp79.comm_mem_V (hWQ ha) (hWQ hb)),
      fun a ha => hZV (hc.hyp.toHyp79.sq_mem_V (hWQ ha)),
      fun r hr a ha => (Subgroup.mem_normalizer_iff.mp hr.1 a).mp ha,
      fun r hr a ha => (Subgroup.mem_normalizer_iff.mp hr.2 a).mp ha⟩
  have hRR' : ∀ r ∈ R, r ∈ R' := fun r hr => by
    have hrV : r ∈ Subgroup.normalizer (V : Set G) := hc.Rt_normalizes_Vt ht hr
    exact ⟨hnormW r (hQM (hRM hr)) hrV, hrV⟩
  have hxR' : x ∈ R' := ⟨hnormW x hxQn hxVn, hxVn⟩
  obtain ⟨Md, iD, iA, κ, hκ⟩ := exists_sectionModule hsec
  let xR : ↥R' := ⟨x, hxR'⟩
  have hNtriv : ∀ k : ↥R', (k : G) ∈ hc.CN t → ∀ b : Md, k • b = b := by
    intro k hk b
    obtain ⟨w, rfl⟩ : ∃ w : ↥W, Multiplicative.toAdd (κ w) = b := by
      obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd b)
      exact ⟨w, by rw [hw]; rfl⟩
    have hkw : (k : G) * w * (k : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp k.2.1 w).mp w.2
    have h1 := hκ.act k w ⟨(k : G) * w * (k : G)⁻¹, hkw⟩ rfl
    have h2 : κ ⟨(k : G) * w * (k : G)⁻¹, hkw⟩ = κ w := by
      rw [hκ.eq_iff]
      have e : (k : G) * w * (k : G)⁻¹ * (w : G)⁻¹ = ⁅(k : G), (w : G)⁆ := by
        simp only [commutatorElement_def]
      show (k : G) * w * (k : G)⁻¹ * (w : G)⁻¹ ∈ V
      rw [e]
      exact hWN _ hk _ w.2
    rw [h2] at h1
    have h3 := congrArg Multiplicative.toAdd h1
    rw [toAdd_ofAdd] at h3
    exact h3.symm
  have hRle : R ≤ R' := fun r hr => hRR' r hr
  let S : Md →+ Md := DistribSMul.toAddMonoidHom Md xR
  have hSa : ∀ a, S a = xR • a := fun a => rfl
  have hS2 : ∀ a : Md, S (S a) = a := by
    intro a
    obtain ⟨w, rfl⟩ : ∃ w : ↥W, Multiplicative.toAdd (κ w) = a := by
      obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
      exact ⟨w, by rw [hw]; rfl⟩
    have hxw : x * w * x⁻¹ ∈ W := conj_mem_Wt hxQn hxVn w.2
    have hxw' : x * (x * w * x⁻¹) * x⁻¹ ∈ W := conj_mem_Wt hxQn hxVn hxw
    have h1 := hκ.act xR w ⟨x * w * x⁻¹, hxw⟩ rfl
    have h2 := hκ.act xR ⟨x * w * x⁻¹, hxw⟩ ⟨x * (x * w * x⁻¹) * x⁻¹, hxw'⟩ rfl
    have h3 : κ ⟨x * (x * w * x⁻¹) * x⁻¹, hxw'⟩ = κ w := by
      rw [hκ.eq_iff]
      show x * (x * w * x⁻¹) * x⁻¹ * (w : G)⁻¹ ∈ V
      have e : x * (x * (w : G) * x⁻¹) * x⁻¹ * (w : G)⁻¹ = ⁅x ^ 2, (w : G)⁆ := by
        simp only [commutatorElement_def]
        rw [pow_two]
        group
      rw [e]
      exact hx2 w w.2
    rw [hSa, hSa, ← toAdd_ofAdd (xR • Multiplicative.toAdd (κ w)), ← h1, ← toAdd_ofAdd (xR •
      Multiplicative.toAdd (κ ⟨x * w * x⁻¹, hxw⟩)), ← h2, h3]
  have hScomm : ∀ (r : G) (hr : r ∈ R) (a : Md),
      S ((⟨r, hRR' r hr⟩ : ↥R') • a) = (⟨r, hRR' r hr⟩ : ↥R') • S a := by
    intro r hr a
    have hcn : ⁅r, x⁆ ∈ hc.CN t := hxR r hr
    have hcR' : ⁅r, x⁆ ∈ R' := hRR' _ (Ctx.mem_CN.mp hcn).1
    have hrel : (⟨⁅r, x⁆, hcR'⟩ : ↥R') * (xR * ⟨r, hRR' r hr⟩) = ⟨r, hRR' r hr⟩ * xR := by
      apply Subtype.ext
      show ⁅r, x⁆ * (x * r) = r * x
      simp only [commutatorElement_def]
      group
    have h1 : (⟨r, hRR' r hr⟩ : ↥R') • xR • a = xR • (⟨r, hRR' r hr⟩ : ↥R') • a := by
      rw [← mul_smul, ← hrel, mul_smul, hNtriv _ hcn, mul_smul]
    rw [hSa, hSa]
    exact h1.symm
  have hSw : ∀ w : ↥W, ∃ w' : ↥W, (w' : G) = x * w * x⁻¹ ∧
      κ w' = Multiplicative.ofAdd (S (Multiplicative.toAdd (κ w))) := by
    intro w
    have hxw : x * w * x⁻¹ ∈ W := conj_mem_Wt hxQn hxVn w.2
    exact ⟨⟨x * w * x⁻¹, hxw⟩, rfl, hκ.act xR w ⟨x * w * x⁻¹, hxw⟩ rfl⟩
  refine ⟨Md, iD, DistribMulAction.compHom Md (Subgroup.inclusion hRle), κ,
    isSecMod_restrict hRle hκ, S, ?_, hS2, hSw⟩
  intro r a
  exact hScomm (r : G) r.2 a

theorem no_wild_plus6_ten_of (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement)
    (hc : Ctx M Q Z B) {t : G} (hs : Sec7Hyp hc 10 t) (hp : OmegaPlusNat hc t 3)
    {x : G} (hxM : x ∈ M) (hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G))
    (hxR : ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x⁆ ∈ hc.CN t) (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z)
    (hx2 : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x ^ 2, w⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  classical
  by_contra hex
  push Not at hex
  obtain ⟨Md, iD, iA, κ, hκ, S, hSA, hS2, hSw⟩ :=
    exists_conj_section_data_of_comm h52a hA h310chi hc hs hxM hxVn hxR hx2
  haveI : Finite Md := hκ.finite
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hWN := sec7_N_comm_W_le_V h52a hA hc hs
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := sec7_V_le_W h310chi hc hs
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hWn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      r * y * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun r hr y hy =>
    conj_mem_Wt (hQM (hRM hr)) (hc.Rt_normalizes_Vt ht hr) hy
  have hVn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      r * y * r⁻¹ ∈ Vt M (LB M Q B) B Z t := fun r hr y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr) y).mp hy
  have hRZ : ∀ r ∈ Rt M (LB M Q B) t, ∀ z ∈ Z, r * z * r⁻¹ = z := by
    intro r hr z hz
    have := Subgroup.mem_centralizer_iff.mp (hc.Rt_le_H0 t hr).2 z hz
    rw [← this]
    group
  have hxQ : ∀ y ∈ Q, x * y * x⁻¹ ∈ Q := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp (hQM hxM) y).mp hy
  have h52c : Stroth52cStatement := stroth_5_2c_of_chi h310chi
  obtain ⟨lam, hlam⟩ := n12Lam_holds G M Q Z B hc
  obtain ⟨hZQ, hZc, hcomm, hsq⟩ := n12Q_holds G M Q Z B hc
  have hnd := n12Lemma1_holds G M Q Z B hc lam hlam
  have hW2 := (n12Lemma2_of h34 h52c G M Q Z B hc 10 t hs).2 lam hlam
  have hrad := lamOrth_radical_le lam hZQ hZc hcomm hsq hnd hZV hVW hWQ hW2
  have hVW1 : ∀ v ∈ Vt M (LB M Q B) B Z t, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅v, w⁆ = 1 := by
    intro v hv w hw
    have := Subgroup.mem_centralizer_iff.mp hw.2 v hv
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact this
  obtain ⟨β, hβA, hβnd, hβκ⟩ :=
    exists_commForm_WV_formula lam hZQ hZc hcomm hZV hVW hWQ hVW1 hκ hRZ hWn hrad
  have hsurj : ∀ a : Md, ∃ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)),
      Multiplicative.toAdd (κ w) = a := by
    intro a
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    exact ⟨w, by rw [hw]; rfl⟩
  have hSβ : ∀ a b : Md, β (S a) (S b) = β a b := by
    intro a b
    obtain ⟨w, rfl⟩ := hsurj a
    obtain ⟨w', rfl⟩ := hsurj b
    obtain ⟨u, hu1, hu2⟩ := hSw w
    obtain ⟨u', hu1', hu2'⟩ := hSw w'
    have e1 : S (Multiplicative.toAdd (κ w)) = Multiplicative.toAdd (κ u) := by
      rw [hu2, toAdd_ofAdd]
    have e2 : S (Multiplicative.toAdd (κ w')) = Multiplicative.toAdd (κ u') := by
      rw [hu2', toAdd_ofAdd]
    rw [e1, e2, hβκ u u', hβκ w w']
    have hwQ : (w : G) ∈ Q := hWQ w.2
    have hwQ' : (w' : G) ∈ Q := hWQ w'.2
    have eU : (⟨(u : G), hWQ u.2⟩ : ↥Q) = ⟨x * (w : G) * x⁻¹, hxQ _ hwQ⟩ := Subtype.ext hu1
    have eU' : (⟨(u' : G), hWQ u'.2⟩ : ↥Q) = ⟨x * (w' : G) * x⁻¹, hxQ _ hwQ'⟩ :=
      Subtype.ext hu1'
    rw [eU, eU']
    exact comm2_conj_eq lam hcomm x hxQ hxZ ⟨(w : G), hwQ⟩ ⟨(w' : G), hwQ'⟩
  let T : Md →+ Md := S + AddMonoidHom.id Md
  have hTa : ∀ a, T a = S a + a := fun a => rfl
  have h2 : ∀ a : Md, a + a = 0 := hκ.two
  have hTT : ∀ a, T (T a) = 0 := by
    intro a
    rw [hTa, hTa, map_add, hS2]
    have e : a + S a + (S a + a) = (a + a) + (S a + S a) := by abel
    rw [e, h2, h2, add_zero]
  have hTA : ∀ (r : ↥(Rt M (LB M Q B) t)) (a : Md), r • T a = T (r • a) := by
    intro r a
    rw [hTa, hTa, hSA, smul_add]
  have hself : ∀ a b : Md, β (T a) b = β a (T b) := by
    intro a b
    rw [hTa, hTa, map_add β, AddMonoidHom.add_apply, map_add (β a)]
    have h1 := hSβ (S a) b
    rw [hS2] at h1
    rw [h1]
  have hTκ : ∀ w : ↥(Wt Q (Vt M (LB M Q B) B Z t)), ∃ c : ↥(Wt Q (Vt M (LB M Q B) B Z t)),
      (c : G) = ⁅x, (w : G)⁆ ∧
        κ c = Multiplicative.ofAdd (T (Multiplicative.toAdd (κ w))) := by
    intro w
    obtain ⟨u, hu1, hu2⟩ := hSw w
    refine ⟨u * w⁻¹, ?_, ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_inv, hu1]
      simp only [commutatorElement_def]
    · rw [map_mul, map_inv, hu2, hTa, ofAdd_add]
      have hneg : Multiplicative.ofAdd (Multiplicative.toAdd (κ w)) =
          (Multiplicative.ofAdd (Multiplicative.toAdd (κ w)))⁻¹ := by
        rw [← ofAdd_neg]
        congr 1
        exact (neg_eq_of_add_eq_zero_left (h2 _)).symm
      rw [ofAdd_toAdd] at hneg ⊢
      rw [← hneg]
  obtain ⟨P, hVP, hPW, hPsec⟩ := exists_secSub_eq hVW hκ T.range
  have hmemP : ∀ y : ↥(Wt Q (Vt M (LB M Q B) B Z t)), (y : G) ∈ P ↔
      Multiplicative.toAdd (κ y) ∈ T.range := fun y => by
    rw [← hPsec]
    exact (toAdd_mem_secSub_iff hκ hVP y).symm
  have hPn : ∀ r ∈ Rt M (LB M Q B) t, ∀ y ∈ P, r * y * r⁻¹ ∈ P := by
    intro r hr y hy
    have hyW : y ∈ Wt Q (Vt M (LB M Q B) B Z t) := hPW hy
    have hrW : r * y * r⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := hWn r hr y hyW
    obtain ⟨a, ha⟩ := (hmemP ⟨y, hyW⟩).mp hy
    have h1 := hκ.act ⟨r, hr⟩ ⟨y, hyW⟩ ⟨r * y * r⁻¹, hrW⟩ rfl
    refine (hmemP ⟨r * y * r⁻¹, hrW⟩).mpr ?_
    rw [h1, toAdd_ofAdd]
    refine ⟨(⟨r, hr⟩ : ↥(Rt M (LB M Q B) t)) • a, ?_⟩
    rw [← hTA, ha]
  have hPR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P := by
    intro r hr
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hy' : r⁻¹ * y * r ∈ P := mem_conjSubgroup.mp hy
      have := hPn r hr _ hy'
      simpa [mul_assoc] using this
    · rw [mem_conjSubgroup]
      have := hPn r⁻¹ ((Rt M (LB M Q B) t).inv_mem hr) y hy
      simpa using this
  have hVPlt : Vt M (LB M Q B) B Z t < P := by
    obtain ⟨w0, hw0, hw0V⟩ := hex
    refine lt_of_le_of_ne hVP fun h => hw0V ?_
    obtain ⟨c, hc1, hc2⟩ := hTκ ⟨w0, hw0⟩
    have : (c : G) ∈ P := (hmemP c).mpr (by
      rw [hc2, toAdd_ofAdd]
      exact ⟨_, rfl⟩)
    rw [h, ← hc1]
    exact this
  have hV3 := n12N_card_V hc t 3 (by norm_num) (Or.inl hp)
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hVpos : 0 < Nat.card ↥(Vt M (LB M Q B) B Z t) := Nat.card_pos
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Vt_le_Q t hv)))
  have hchi := card_mul_card_of_isChiIso
    (h52c G M Q Z B hc 10 t hs.toSec5 hs.omegaNat (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl) hWQ hZV
  have hWc : Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 8 :=
    sec713_card_W_eq hZpos hchi hs.toSec5.width hV3 (by norm_num)
  have hMd : Nat.card Md = Nat.card ↥Z ^ 8 := by
    have h1 := natCard_eq_of_isSecMod hVW hκ
    rw [hWc] at h1
    exact (Nat.eq_of_mul_eq_mul_left hVpos h1).symm
  have hTrk : T.range ≤ T.ker := by
    intro b hb
    obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hb
    exact AddMonoidHom.mem_ker.mpr (hTT a)
  have hrange : Nat.card ↥T.range ≤ Nat.card ↥Z ^ 4 := by
    have h1 : Nat.card ↥T.range * Nat.card ↥T.range ≤ Nat.card ↥Z ^ 4 * Nat.card ↥Z ^ 4 :=
      calc Nat.card ↥T.range * Nat.card ↥T.range ≤ Nat.card ↥T.ker * Nat.card ↥T.range :=
            Nat.mul_le_mul_right _ (AddSubgroup.card_le_of_le hTrk)
        _ = Nat.card Md := AddSubgroup.card_ker_mul_card_range T
        _ = Nat.card ↥Z ^ 4 * Nat.card ↥Z ^ 4 := by rw [hMd, ← pow_add]
    exact Nat.mul_self_le_mul_self_iff.mp h1
  have hPbound : Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 4 := by
    have h1 := natCard_secSub_mul hVW hκ hVP hPW
    rw [hPsec] at h1
    rw [← h1, mul_comm]
    exact Nat.mul_le_mul_left _ hrange
  obtain ⟨k, hk⟩ := ((sec7WVSecCard_of hA hPts h52a h52b) G M Q Z B hc 10 t hs P hVP hPW hPR 3
    (by norm_num)).2 hp (le_refl 3)
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hk4 : 2 ^ (3 - 1) * k ≤ 4 := by
    have h3 : Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 ^ (3 - 1) * k) ≤
        Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ 4 := hk ▸ hPbound
    have h4 := Nat.le_of_mul_le_mul_left h3 hVpos
    exact (Nat.pow_le_pow_iff_right hq).mp h4
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hcardle : Nat.card ↥P ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) := by
      rw [hk]
      simp
    exact (ne_of_lt hVPlt) (Subgroup.eq_of_le_of_card_ge hVPlt.le hcardle)
  have hk1 : k = 1 := by
    norm_num at hk4
    omega
  subst hk1
  obtain ⟨r₀, hr₀, hdP⟩ := oppDecomp_of_invariant_section hA hPts h52a h52b hc hs hVPlt.le hPW hPR
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r₀ B) = conjSubgroup r₀ (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr₀.mem)
  have hL2R : LB M Q (conjSubgroup r₀ B) ≤ Rt M (LB M Q B) t :=
    le_sup_right.trans hr₀.gen.ge
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc 10 t hs.toSec5 hs.omegaNat r₀ hr₀.mem hr₀.plane
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', hu0, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
  · have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat hZV hKZ
    have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    have hmm : m' = 3 := sec7_pin_dim hq (hcard.symm.trans hV3)
    subst hmm
    have hsecP : SecHyp (Rt M (LB M Q B) t) P (Vt M (LB M Q B) B Z t) :=
      SecHyp.of_isOppDecomp hdP hPn hVn
    obtain ⟨Y, iY, iYD, κ', hκ', hkerY⟩ :=
      exists_sectionModule_ker hker hsecP (fun k hk y hy => hWN k hk y (hPW hy))
    haveI : Finite Y := hκ'.finite
    have hdec := isCompl_fixedSub_of_isOppDecomp hPn hκ' hdP hLR hL2R
    have hPcard := natCard_eq_of_isSecMod hVPlt.le hκ'
    have hYcard : Nat.card Y = Nat.card K ^ 4 := by
      rw [hKZ]
      have e : Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 ^ (3 - 1) * 1) =
          Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Y := by
        rw [← hk, hPcard]
      have e' := Nat.eq_of_mul_eq_mul_left hVpos e
      norm_num at e'
      exact e'.symm
    obtain ⟨ι, hι_inj, hιA, -, hιrange⟩ := exists_secMod_embedding hκ hκ' hVP hPW hPn
    obtain ⟨γ, hγA, hγnd⟩ := exists_form_on_range β hβnd T hself hβA hTA ι hι_inj hιA
      (hιrange.trans hPsec)
    exact noInvariantForm_frame_hom (hKZ ▸ (by omega : 4 ≤ Nat.card Z)) φ hrange hu hu' hu0 huu'
      Y hκ'.two hkerY ((LB M Q B).subgroupOf (Rt M (LB M Q B) t))
      ((LB M Q (conjSubgroup r₀ B)).subgroupOf (Rt M (LB M Q B) t))
      (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
      (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu') hdec hYcard ⟨γ, hγA, hγnd⟩
  · have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
        (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat hZV hKZ
    have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    have hmm : m' = 3 := sec7_pin_dim hq (hcard.symm.trans hV3)
    have hMinusM : OmegaMinusNat hc t 3 := by
      rw [← hmm]
      exact ⟨K, hKf, hKfin, hKZ, b, c, hirr, hnat⟩
    exact omegaSignStatement_holds G M Q Z B hc t 3 (by norm_num) hp hMinusM

theorem step713XActsPlus6_of (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement) (hZt : Sec7ZtStatement)
    (hZcard : Sec7ZCardStatement) : Step713XActsPlus6Statement := by
  intro G _ _ M Q Z B _ hc t hs hp Z0 hZ0 x hx _ _
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨hD2, hDN, -⟩ := sec713_O2NormPre_facts hc ht hZ0
  have hxD : x ∈ O2NormPre M Q Z Z0 := mem_O2NormPre.mpr hx
  obtain ⟨a, ha⟩ := hD2 ⟨x, hxD⟩
  have hxa : x ^ 2 ^ a = 1 := by
    have h1 := congrArg Subtype.val ha
    simpa using h1
  by_contra hex
  push Not at hex
  have hPa : ∃ j : ℕ, ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅x ^ 2 ^ j, w⁆ ∈ Vt M (LB M Q B) B Z t :=
    ⟨a, fun w _ => by rw [hxa, commutatorElement_one_left]; exact one_mem _⟩
  have hj := Nat.find_spec hPa
  have hj0 : Nat.find hPa ≠ 0 := by
    intro h0
    obtain ⟨w, hw, hwV⟩ := hex
    have h1 := hj w hw
    rw [h0, pow_zero, pow_one] at h1
    exact hwV h1
  have hj1 := Nat.find_min hPa (show Nat.find hPa - 1 < Nat.find hPa by omega)
  push Not at hj1
  obtain ⟨w, hw, hwV⟩ := hj1
  have hy2 : (x ^ 2 ^ (Nat.find hPa - 1)) ^ 2 = x ^ 2 ^ Nat.find hPa := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
  have hyD : x ^ 2 ^ (Nat.find hPa - 1) ∈ O2NormPre M Q Z Z0 :=
    (O2NormPre M Q Z Z0).pow_mem hxD _
  have hyN := hDN hyD
  have hyZ : ∀ z ∈ Z, x ^ 2 ^ (Nat.find hPa - 1) * z * (x ^ 2 ^ (Nat.find hPa - 1))⁻¹ = z := by
    intro z hz
    have h1 := Subgroup.mem_centralizer_iff.mp hyN.1.2 z hz
    rw [← h1, mul_inv_cancel_right]
  have hyV : x ^ 2 ^ (Nat.find hPa - 1) ∈
      Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp (sec7_normalizes_of_zt hZt hZcard hc hs hZ0 hyN).2
  have hyR : ∀ r ∈ Rt M (LB M Q B) t, ⁅r, x ^ 2 ^ (Nat.find hPa - 1)⁆ ∈ hc.CN t := by
    intro r hr
    rw [← commutatorElement_inv]
    exact (hc.CN t).inv_mem (sec713_comm_Rt_of_O2 hZt hZcard hc hs hZ0 _ hyD r hr)
  have hy2W : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅(x ^ 2 ^ (Nat.find hPa - 1)) ^ 2, w⁆ ∈ Vt M (LB M Q B) B Z t := by
    rw [hy2]
    exact hj
  exact hwV (no_wild_plus6_ten_of h34 hA hPts h52a h52b h310chi hc hs hp hyN.1.1 hyV hyR hyZ
    hy2W w hw)

end CFSG.RankThree.GF2n.Stroth80
