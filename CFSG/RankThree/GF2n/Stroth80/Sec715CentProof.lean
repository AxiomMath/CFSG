module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Sec712
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsSchur
public import CFSG.RankThree.GF2n.Stroth80.Sec78CommW
public import CFSG.RankThree.GF2n.Stroth80.Sec8CommNorm
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

private theorem one_add_pow_two_pow_of_add_self {A : Type*} [Ring A] (h2 : ∀ x : A, x + x = 0)
    (f : A) (j : ℕ) : (1 + f) ^ 2 ^ j = 1 + f ^ 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, pow_mul, ih]
    have e : (1 + f ^ 2 ^ j) ^ 2 = 1 + (f ^ 2 ^ j + f ^ 2 ^ j) + f ^ 2 ^ j * f ^ 2 ^ j := by
      noncomm_ring
    rw [e, h2, add_zero, ← pow_two, ← pow_mul]

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem secSub_smul_mem {R P I : Subgroup G} {Md : Type} [AddCommGroup Md]
    [DistribMulAction ↥R Md] {κ : ↥P →* Multiplicative Md} (hκ : IsSecMod R P I Md κ)
    (hP : ∀ r ∈ R, ∀ x ∈ P, r * x * r⁻¹ ∈ P) {U : Subgroup G}
    (hU : ∀ r ∈ R, ∀ u ∈ U, r * u * r⁻¹ ∈ U) (z : ↥R) {a : Md} (ha : a ∈ secSub κ U) :
    z • a ∈ secSub κ U := by
  obtain ⟨x, hxU, hxa⟩ := mem_secSub.mp ha
  have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
  have hyP : (z : G) * x * (z : G)⁻¹ ∈ P := hP z z.2 x x.2
  refine mem_secSub.mpr ⟨⟨(z : G) * x * (z : G)⁻¹, hyP⟩, hU z z.2 x hxU, ?_⟩
  rw [hκ.act z x ⟨(z : G) * x * (z : G)⁻¹, hyP⟩ rfl, hxa']

theorem Ctx.comm_comm_mem_Z_of_comm (hc : Ctx M Q Z B) {R : Subgroup G} (hRM : R ≤ M) {w : G}
    (hwM : w ∈ M) (hwR : ∀ ρ ∈ R, ⁅ρ⁻¹, w⁆ ∈ Q) {s x : G} (hs : s ∈ R) (hx : x ∈ Q)
    (hsx : ⁅⁅s, x⁆, w⁆ ∈ Z) : ⁅s, ⁅x, w⁆⁆ ∈ Z := by
  classical
  have hSec := sec7ctr_secHyp hc hRM
  have hP := hSec.normP
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hSec
  obtain ⟨ε, hε, hεR⟩ := exists_comm_endo hc hRM hκ hwM hwR
  have hyQ : ⁅x, w⁆ ∈ Q := hc.comm_mem_Q hwM hx
  have hsxQ : s * x * s⁻¹ ∈ Q := hP s hs x hx
  have hcQ : ⁅s, x⁆ ∈ Q := by
    rw [commutatorElement_def]
    exact Q.mul_mem hsxQ (Q.inv_mem hx)
  have hsyQ : s * ⁅x, w⁆ * s⁻¹ ∈ Q := hP s hs _ hyQ
  have h1 := hκ.act ⟨s, hs⟩ ⟨⁅x, w⁆, hyQ⟩ ⟨s * ⁅x, w⁆ * s⁻¹, hsyQ⟩ rfl
  have h2 := hκ.act ⟨s, hs⟩ ⟨x, hx⟩ ⟨s * x * s⁻¹, hsxQ⟩ rfl
  have h3 : κ ⟨s * x * s⁻¹, hsxQ⟩ = κ ⟨⁅s, x⁆, hcQ⟩ * κ ⟨x, hx⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show s * x * s⁻¹ = ⁅s, x⁆ * x
    rw [commutatorElement_def]
    group
  have h4 : ε (Multiplicative.toAdd (κ ⟨⁅s, x⁆, hcQ⟩)) = 0 := by
    rw [hε]
    have h : κ ⟨⁅⁅s, x⁆, w⁆, hc.comm_mem_Q hwM hcQ⟩ = 1 := (hκ.ker _).mpr hsx
    rw [h]
    rfl
  have e2 : (⟨s, hs⟩ : ↥R) • Multiplicative.toAdd (κ ⟨x, hx⟩) =
      Multiplicative.toAdd (κ ⟨⁅s, x⁆, hcQ⟩) + Multiplicative.toAdd (κ ⟨x, hx⟩) := by
    rw [← toAdd_mul, ← h3, h2, toAdd_ofAdd]
  have h5 : Multiplicative.toAdd (κ ⟨s * ⁅x, w⁆ * s⁻¹, hsyQ⟩) =
      Multiplicative.toAdd (κ ⟨⁅x, w⁆, hyQ⟩) := by
    rw [h1, toAdd_ofAdd, ← hε ⟨x, hx⟩, ← hεR, e2, map_add, h4, zero_add]
  have h6 := (hκ.eq_iff _ _).mp (Multiplicative.toAdd.injective h5)
  have e : ⁅s, ⁅x, w⁆⁆ = s * ⁅x, w⁆ * s⁻¹ * ⁅x, w⁆⁻¹ := by
    rw [commutatorElement_def s]
  rw [e]
  exact h6

theorem sec715_comm_Rt_mem_Q [(Q.subgroupOf M).Normal] (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hZcard : Sec7ZCardStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hZN : IsCentrePre Z0 (hc.CN t) Q) {w : G}
    (hwM : w ∈ M) (hwN : ∀ x ∈ hc.CN t, ⁅w, x⁆ ∈ Q) :
    ∀ r ∈ Rt M (LB M Q B) t, ⁅w, r⁆ ∈ Q := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hwRn : conjSubgroup w (Rt M (LB M Q B) t) = Rt M (LB M Q B) t :=
    sec8_conj_R_of_comm hc htM hwM (hwN t (hZN.le htZ0))
  let wm : ↥M := ⟨w, hwM⟩
  have hcZ0 : ∀ r ∈ Rt M (LB M Q B) t, ⁅w, r⁆ ∈ Z0 := by
    intro r hr
    have hrM : r ∈ M := hRM hr
    have hcR : ⁅w, r⁆ ∈ Rt M (LB M Q B) t := by
      rw [commutatorElement_def]
      exact (Rt M (LB M Q B) t).mul_mem
        ((Subgroup.mem_normalizer_iff.mp (conjSubgroup_eq_self_iff.mp hwRn) r).mp hr)
        ((Rt M (LB M Q B) t).inv_mem hr)
    have hcN : ∀ x ∈ hc.CN t, ⁅⁅w, r⁆, x⁆ ∈ Q := by
      intro x hx
      have hxM : x ∈ M := hRM (Ctx.mem_CN.mp hx).1
      have hx' : r⁻¹ * x * r ∈ hc.CN t := by
        simpa using hc.CN_conj_mem ht ((Rt M (LB M Q B) t).inv_mem hr) hx
      let rm : ↥M := ⟨r, hrM⟩
      let xm : ↥M := ⟨x, hxM⟩
      have h1 : Commute (QuotientGroup.mk' (Q.subgroupOf M) wm)
          (QuotientGroup.mk' (Q.subgroupOf M) xm) := (mk_commute_iff wm xm).mpr (hwN x hx)
      have h2 : Commute (QuotientGroup.mk' (Q.subgroupOf M) wm)
          ((QuotientGroup.mk' (Q.subgroupOf M) rm)⁻¹ * QuotientGroup.mk' (Q.subgroupOf M) xm *
            QuotientGroup.mk' (Q.subgroupOf M) rm) := by
        have h := (mk_commute_iff wm (rm⁻¹ * xm * rm)).mpr (hwN _ hx')
        rwa [map_mul, map_mul, map_inv] at h
      have h3 : Commute (QuotientGroup.mk' (Q.subgroupOf M) rm *
          (QuotientGroup.mk' (Q.subgroupOf M) wm)⁻¹ * (QuotientGroup.mk' (Q.subgroupOf M) rm)⁻¹)
          (QuotientGroup.mk' (Q.subgroupOf M) xm) := by
        have h := h2.inv_left.conj (QuotientGroup.mk' (Q.subgroupOf M) rm)
        simpa [mul_assoc] using h
      have h4 : Commute ⁅QuotientGroup.mk' (Q.subgroupOf M) wm,
          QuotientGroup.mk' (Q.subgroupOf M) rm⁆ (QuotientGroup.mk' (Q.subgroupOf M) xm) := by
        have e : ⁅QuotientGroup.mk' (Q.subgroupOf M) wm, QuotientGroup.mk' (Q.subgroupOf M) rm⁆ =
            QuotientGroup.mk' (Q.subgroupOf M) wm * (QuotientGroup.mk' (Q.subgroupOf M) rm *
              (QuotientGroup.mk' (Q.subgroupOf M) wm)⁻¹ *
                (QuotientGroup.mk' (Q.subgroupOf M) rm)⁻¹) := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact h1.mul_left h3
      rw [← map_commutatorElement] at h4
      exact (mk_commute_iff ⁅wm, rm⁆ xm).mp h4
    exact hZN.mem_iff.mpr ⟨sec712_DR h51 hA hZcard hc hs hZ0 _ hcR hcN, hcN⟩
  have hR' := commutator_R_comm_of_comm hc hs hZ0 hwM hcZ0
  intro r hr
  obtain ⟨a, ha, x, hx, rfl⟩ := sec7_Rt_eq_comm_mul_CN hc hs r hr
  have haM : a ∈ M := hRM (Subgroup.commutator_le_self _ ha)
  have e : ⁅w, a * x⁆ = ⁅w, a⁆ * (a * ⁅w, x⁆ * a⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Q.mul_mem (hR' a ha)
    ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 haM) _).mp (hwN x hx))

theorem sec715_comm_Vt_mem_Z (hirr : Sec7VtIrredStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {w : G} (hwM : w ∈ M) (hw2 : ∃ e : ℕ, w ^ 2 ^ e ∈ Q)
    (hwR : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ⁻¹, w⁆ ∈ Q) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, w⁆ ∈ Z := by
  classical
  obtain ⟨e, he⟩ := hw2
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have htR : t ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht ht
  have hwt : ⁅w, t⁆ ∈ Q := by
    have h := hwR t⁻¹ ((Rt M (LB M Q B) t).inv_mem htR)
    rw [inv_inv] at h
    rw [← commutatorElement_inv]
    exact Q.inv_mem h
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hSec := sec7ctr_secHyp hc hRM
  have hP := hSec.normP
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hSec
  obtain ⟨ε, hε, hεR⟩ := exists_comm_endo hc hRM hκ hwM hwR
  have hwN : w ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    sec8_normV_of_comm hc hwM hwt
  have hQc : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hεV : ∀ a ∈ secSub κ (Vt M (LB M Q B) B Z t),
      ε a ∈ secSub κ (Vt M (LB M Q B) B Z t) := by
    intro a ha
    obtain ⟨x, hxV, hxa⟩ := mem_secSub.mp ha
    have hxa' : Multiplicative.toAdd (κ x) = a := by rw [hxa]; rfl
    rw [← hxa', hε x]
    refine (toAdd_mem_secSub_iff hκ hZV _).mpr ?_
    show ⁅(x : G), w⁆ ∈ Vt M (LB M Q B) B Z t
    have h1 : w * (x : G)⁻¹ * w⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp hwN _).mp ((Vt M (LB M Q B) B Z t).inv_mem hxV)
    rw [show ⁅(x : G), w⁆ = (x : G) * (w * (x : G)⁻¹ * w⁻¹) by
      rw [commutatorElement_def]; group]
    exact (Vt M (LB M Q B) B Z t).mul_mem hxV h1
  let f : AddMonoid.End Md := ε
  have hpow : ∀ j : ℕ, w ^ j ∈ M := fun j => M.pow_mem hwM j
  have hone : ∀ y : ↥Q, (1 - f) (Multiplicative.toAdd (κ y)) =
      Multiplicative.toAdd (κ ⟨w * y * w⁻¹, hQc w hwM y y.2⟩) := by
    intro y
    have hyQ : ⁅(y : G), w⁆ ∈ Q := hc.comm_mem_Q hwM y.2
    have h1 : κ ⟨w * y * w⁻¹, hQc w hwM y y.2⟩ = (κ ⟨⁅(y : G), w⁆, hyQ⟩)⁻¹ * κ y := by
      rw [← map_inv, ← map_mul]
      congr 1
      apply Subtype.ext
      show w * (y : G) * w⁻¹ = ⁅(y : G), w⁆⁻¹ * y
      rw [commutatorElement_def]
      group
    rw [h1, toAdd_mul, toAdd_inv, ← hε y]
    show Multiplicative.toAdd (κ y) - ε (Multiplicative.toAdd (κ y)) = _
    abel
  have hiter : ∀ (j : ℕ) (y : ↥Q), (⇑(1 - f))^[j] (Multiplicative.toAdd (κ y)) =
      Multiplicative.toAdd (κ ⟨w ^ j * y * (w ^ j)⁻¹, hQc _ (hpow j) y y.2⟩) := by
    intro j
    induction j with
    | zero =>
      intro y
      show Multiplicative.toAdd (κ y) = _
      congr 2
      apply Subtype.ext
      simp
    | succ j ih =>
      intro y
      rw [Function.iterate_succ_apply', ih y, hone]
      congr 2
      apply Subtype.ext
      show w * (w ^ j * y * (w ^ j)⁻¹) * w⁻¹ = w ^ (j + 1) * y * (w ^ (j + 1))⁻¹
      rw [pow_succ']
      group
  have hfpow : (1 - f) ^ 2 ^ e = 1 := by
    refine DFunLike.ext _ _ fun a => ?_
    obtain ⟨y, hy⟩ := hκ.surj (Multiplicative.ofAdd a)
    have hya : Multiplicative.toAdd (κ y) = a := by rw [hy]; rfl
    rw [AddMonoid.End.coe_pow, ← hya, hiter]
    show _ = Multiplicative.toAdd (κ y)
    congr 1
    refine (hκ.eq_iff _ _).mpr ?_
    exact hc.hyp.toHyp79.comm_mem_V he y.2
  have h2f : ∀ g : AddMonoid.End Md, g + g = 0 := fun g =>
    DFunLike.ext _ _ fun a => hκ.two (g a)
  have hneg : 1 - f = 1 + f := by
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (h2f f)]
  have hnil : f ^ 2 ^ e = 0 := by
    have h := hfpow
    rw [hneg, one_add_pow_two_pow_of_add_self h2f f e] at h
    simpa using h
  have hnil' : ∀ a : Md, (⇑ε)^[2 ^ e] a = 0 := fun a => by
    show (⇑f)^[2 ^ e] a = 0
    rw [← AddMonoid.End.coe_pow, hnil]
    rfl
  obtain ⟨d, hd4, hVcard⟩ := sec7ctr_card_Vt hc hs
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨v₀, hv₀V, hv₀Z⟩ : ∃ v ∈ Vt M (LB M Q B) B Z t, v ∉ Z := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card ↥(Vt M (LB M Q B) B Z t) ≤ Nat.card Z := Subgroup.card_le_of_le hcon
    rw [hVcard] at h1
    have h2 : 1 < Nat.card Z ^ d := Nat.one_lt_pow (by omega) (by omega)
    nlinarith
  have ha₀V : Multiplicative.toAdd (κ ⟨v₀, hVQ hv₀V⟩) ∈ secSub κ (Vt M (LB M Q B) B Z t) :=
    mem_secSub.mpr ⟨_, hv₀V, rfl⟩
  have ha₀ne : Multiplicative.toAdd (κ ⟨v₀, hVQ hv₀V⟩) ≠ 0 := fun h =>
    hv₀Z ((hκ.ker _).mp (Multiplicative.toAdd.injective (h.trans toAdd_one.symm)))
  have hiterV : ∀ (j : ℕ), ∀ a ∈ secSub κ (Vt M (LB M Q B) B Z t),
      (⇑ε)^[j] a ∈ secSub κ (Vt M (LB M Q B) B Z t) := by
    intro j
    induction j with
    | zero => exact fun a ha => ha
    | succ j ih =>
      intro a ha
      rw [Function.iterate_succ_apply']
      exact hεV _ (ih a ha)
  have hex : ∃ j, (⇑ε)^[j] (Multiplicative.toAdd (κ ⟨v₀, hVQ hv₀V⟩)) = 0 :=
    ⟨2 ^ e, hnil' _⟩
  obtain ⟨j₁, hj₁⟩ : ∃ j₁, Nat.find hex = j₁ + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h => ha₀ne ?_
    have h' := Nat.find_spec hex
    rw [h] at h'
    exact h'
  have hmin : (⇑ε)^[j₁] (Multiplicative.toAdd (κ ⟨v₀, hVQ hv₀V⟩)) ≠ 0 :=
    Nat.find_min hex (by omega)
  have hker : ε ((⇑ε)^[j₁] (Multiplicative.toAdd (κ ⟨v₀, hVQ hv₀V⟩))) = 0 := by
    rw [← Function.iterate_succ_apply' (⇑ε) j₁]
    have h' := Nat.find_spec hex
    rw [hj₁] at h'
    exact h'
  have hTinv : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ ε.ker ⊓ secSub κ (Vt M (LB M Q B) B Z t),
      z • a ∈ ε.ker ⊓ secSub κ (Vt M (LB M Q B) B Z t) := by
    intro z a ha
    obtain ⟨ha1, ha2⟩ := AddSubgroup.mem_inf.mp ha
    refine AddSubgroup.mem_inf.mpr ⟨?_, secSub_smul_mem hκ hP (fun r hr u hu =>
      (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hr) u).mp hu) z ha2⟩
    rw [AddMonoidHom.mem_ker] at ha1 ⊢
    rw [hεR, ha1, smul_zero]
  have hirr' : ∀ U : Subgroup G, Z ≤ U → U ≤ Vt M (LB M Q B) B Z t →
      (∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ U, r * u * r⁻¹ ∈ U) →
      U = Z ∨ U = Vt M (LB M Q B) B Z t := fun U h1 h2 h3 =>
    hirr G M Q Z B hc n t hs U h1 h2 h3
  have hVirr := secSub_irred_of_irred hκ hZV hVQ hP hirr'
  have hTV : ε.ker ⊓ secSub κ (Vt M (LB M Q B) B Z t) = secSub κ (Vt M (LB M Q B) B Z t) := by
    refine (hVirr _ inf_le_right hTinv).resolve_left fun hbot => hmin ?_
    have hmem : (⇑ε)^[j₁] (Multiplicative.toAdd (κ ⟨v₀, hVQ hv₀V⟩)) ∈
        ε.ker ⊓ secSub κ (Vt M (LB M Q B) B Z t) :=
      AddSubgroup.mem_inf.mpr ⟨AddMonoidHom.mem_ker.mpr hker, hiterV j₁ _ ha₀V⟩
    rw [hbot] at hmem
    exact AddSubgroup.mem_bot.mp hmem
  intro v hv
  have hmem : Multiplicative.toAdd (κ ⟨v, hVQ hv⟩) ∈ ε.ker ⊓ secSub κ (Vt M (LB M Q B) B Z t) := by
    rw [hTV]
    exact mem_secSub.mpr ⟨_, hv, rfl⟩
  have h1 := AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp hmem).1
  rw [hε] at h1
  exact (hκ.ker _).mp (Multiplicative.toAdd.injective (h1.trans toAdd_one.symm))

theorem sec715_comm_Wt_mem_Vt (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hCV : Sec7CVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {w : G}
    (hwM : w ∈ M) (hwR : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ⁻¹, w⁆ ∈ Q)
    (hwV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, w⁆ ∈ Z) :
    ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t := by
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨-, hNW⟩ := h52a G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl
  intro x hx
  have hxQ : x ∈ Q := hx.1
  refine (hCV G M Q Z B hc n t hs _ (hc.comm_mem_Q hwM hxQ)).mpr fun y hy => ?_
  obtain ⟨-, hyN⟩ := Subgroup.mem_inf.mp hy
  exact hc.comm_comm_mem_Z_of_comm (hc.Rt_le_M t) hwM hwR (Ctx.mem_CN.mp hyN).1 hxQ
    (hwV _ (hNW y hyN x hx))

theorem sec715_comm_Q_mem_Wt (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {w : G} (hwM : w ∈ M)
    (hwR : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ⁻¹, w⁆ ∈ Q)
    (hwV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, w⁆ ∈ Z) :
    ∀ x ∈ Q, ⁅x, w⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  obtain ⟨hVeq, hWeq⟩ := h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
  intro x hx
  rw [hWeq, hc.mem_Q1_iff htM]
  refine ⟨hc.comm_mem_Q hwM hx, hc.comm_comm_mem_Z_of_comm (hc.Rt_le_M t) hwM hwR
    (le_Rt (M := M) (LB M Q B) ht ht) hx (hwV _ ?_)⟩
  rw [hVeq, ← commutatorElement_inv]
  exact (Ut Q Z t).inv_mem (comm_mem_Ut hx)

theorem sec715_mem_H0 (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {w : G}
    (hwM : w ∈ M) (hwV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, w⁆ ∈ Z)
    (hwQ : ∀ x ∈ Q, ⁅x, w⁆ ∈ Wt Q (Vt M (LB M Q B) B Z t)) : w ∈ H0 M Z := by
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  obtain ⟨d, hd4, hVcard⟩ := sec7ctr_card_Vt hc hs
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨v, hvV, hvZ⟩ : ∃ v ∈ Vt M (LB M Q B) B Z t, v ∉ Z := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card ↥(Vt M (LB M Q B) B Z t) ≤ Nat.card Z := Subgroup.card_le_of_le hcon
    rw [hVcard] at h1
    have h2 : 1 < Nat.card Z ^ d := Nat.one_lt_pow (by omega) (by omega)
    nlinarith
  obtain ⟨K, _, _, _, γ, M₀, hgm⟩ := stroth_globalModelData hc.hyp
  have hcen : ∀ z ∈ Z, ∀ y ∈ Q, Commute z y := fun z hz y hy =>
    hc.hyp.toHyp79.V_central hz hy
  refine ⟨hwM, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
  obtain ⟨q, hq, hqz⟩ := Smith81.GM.exists_comm hgm (hVQ hvV) hvZ hz
  have hz1 : ⁅v, w⁆⁻¹ ∈ Z := Z.inv_mem (hwV v hvV)
  have hq1 : ⁅q, w⁆⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    (Wt Q (Vt M (LB M Q B) B Z t)).inv_mem (hwQ q hq)
  have hq1Q : ⁅q, w⁆⁻¹ ∈ Q := hq1.1
  have hvqZ : ⁅v, q⁆ ∈ Z := by rw [hqz]; exact hz
  have e1 : w * z * w⁻¹ = ⁅⁅v, w⁆⁻¹ * v, ⁅q, w⁆⁻¹ * q⁆ := by
    rw [← hqz]
    simp only [commutatorElement_def]
    group
  have hXQ : ⁅v, ⁅q, w⁆⁻¹ * q⁆ ∈ Q := by
    have hyQ : ⁅q, w⁆⁻¹ * q ∈ Q := Q.mul_mem hq1Q hq
    rw [commutatorElement_def]
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem (hVQ hvV) hyQ) (Q.inv_mem (hVQ hvV))) (Q.inv_mem hyQ)
  have hvq1 : Commute v ⁅q, w⁆⁻¹ := Subgroup.mem_centralizer_iff.mp hq1.2 v hvV
  have e2 : ⁅⁅v, w⁆⁻¹ * v, ⁅q, w⁆⁻¹ * q⁆ = ⁅v, q⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      (hcen _ hz1 _ (Q.mul_mem hq1Q hq)).commutator_eq, mul_one,
      (hcen _ hz1 _ hXQ).mul_inv_cancel, commutatorElement_mul_right_eq_mul_conj,
      hvq1.commutator_eq, one_mul, (hcen _ hvqZ _ hq1Q).symm.mul_inv_cancel]
  have e3 : w * z * w⁻¹ = z := by rw [e1, e2, hqz]
  calc z * w = w * z * w⁻¹ * w := by rw [e3]
    _ = w * z := by group

theorem sec715_comm_Wt_mem_Z (h34 : Stroth34Statement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hirr : Sec7VtIrredStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) {w : G} (hwM : w ∈ M)
    (hwR : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ⁻¹, w⁆ ∈ Q)
    (hwV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅v, w⁆ ∈ Z)
    (hwW : ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Vt M (LB M Q B) B Z t) :
    ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∈ Z := by
  classical
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have hrM : r ∈ M := hRM hr.mem
  have hZQ : Z ≤ Q := hc.Z_le_Q
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  obtain ⟨hWdec, -⟩ := h52a G M Q Z B hc n t h5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  have hLBR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLCR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := by
    rw [hr.gen]
    exact le_sup_right
  have h35B := (stroth_3_5 h34 hc h5.width h5.n_gt h5.noA2 h5.gen).2.1
  have h35C := (stroth_3_5 h34 hC h5.width h5.n_gt (hc.noA2_conj h5.noA2 hrM)
    (h5.gen.conj_of_mem hrM)).2.1
  have hCV : conjSubgroup r B ⊔ Z ≤ Vt M (LB M Q B) B Z t := hc.conj_Rt_le_Vt ht hr.mem
  have hBV : B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le (hc.B_le_Vt ht) hZV
  have hBpart : ∀ a ∈ Q ⊓ QB B, ⁅a, w⁆ ∈ B ⊔ Z := by
    intro a ha
    have hmem : ⁅a, w⁆ ∈ CQt Q Z (LB M Q B) := ⟨hc.comm_mem_Q hwM ha.1, fun l hl =>
      hc.comm_comm_mem_Z_of_comm hRM hwM hwR (hLBR hl) ha.1
        (hwV _ (hBV (by rw [sup_comm]; exact hc.comm_LB_inf_QB_mem_sup hl ha)))⟩
    rw [h35B] at hmem
    exact hmem
  have hCpart : ∀ a ∈ Q ⊓ QB (conjSubgroup r B), ⁅a, w⁆ ∈ conjSubgroup r B ⊔ Z := by
    intro a ha
    have hmem : ⁅a, w⁆ ∈ CQt Q Z (LB M Q (conjSubgroup r B)) := ⟨hc.comm_mem_Q hwM ha.1,
      fun l hl => hc.comm_comm_mem_Z_of_comm hRM hwM hwR (hLCR hl) ha.1
        (hwV _ (hCV (by rw [sup_comm]; exact hC.comm_LB_inf_QB_mem_sup hl ha)))⟩
    rw [h35C] at hmem
    exact hmem
  have hSec := sec7ctr_secHyp hc hRM
  have hP := hSec.normP
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hSec
  haveI : Finite Md := hκ.finite
  obtain ⟨ε, hε, hεR⟩ := exists_comm_endo hc hRM hκ hwM hwR
  set T : AddSubgroup Md := (secSub κ (Wt Q (Vt M (LB M Q B) B Z t))).map ε with hT
  have hTV : T ≤ secSub κ (Vt M (LB M Q B) B Z t) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hxW, hxb⟩ := mem_secSub.mp hb
    have hxb' : Multiplicative.toAdd (κ x) = b := by rw [hxb]; rfl
    rw [← hxb', hε x]
    exact (toAdd_mem_secSub_iff hκ hZV _).mpr (hwW x hxW)
  have hTinv : ∀ z : ↥(Rt M (LB M Q B) t), ∀ a ∈ T, z • a ∈ T := by
    rintro z _ ⟨b, hb, rfl⟩
    exact ⟨z • b, secSub_smul_mem hκ hP (fun ρ hρ x hx => sec7ctr_Wt_conj_mem hc ht hρ hx) z hb,
      hεR z b⟩
  have hBcard : Nat.card ↥B = Nat.card Z := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [hg, card_conjSubgroup]
  have hCcard : Nat.card ↥(conjSubgroup r B) = Nat.card Z := by
    rw [card_conjSubgroup, hBcard]
  have hsB : Nat.card ↥(secSub κ (B ⊔ Z)) ≤ Nat.card Z :=
    sec7ctr_card_secSub_sup_le hc hκ hc.le hBcard
  have hsC : Nat.card ↥(secSub κ (conjSubgroup r B ⊔ Z)) ≤ Nat.card Z :=
    sec7ctr_card_secSub_sup_le hc hκ hC.le hCcard
  have hTBC : T ≤ secSub κ (B ⊔ Z) ⊔ secSub κ (conjSubgroup r B ⊔ Z) := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hxW, hxb⟩ := mem_secSub.mp hb
    have hxb' : Multiplicative.toAdd (κ x) = b := by rw [hxb]; rfl
    obtain ⟨a₁, ha₁, b₁, hb₁, hxab⟩ := hWdec (x : G) hxW
    obtain ⟨ha₁B, ha₁W⟩ := Subgroup.mem_inf.mp ha₁
    obtain ⟨hb₁C, hb₁W⟩ := Subgroup.mem_inf.mp hb₁
    have ha₁Q : a₁ ∈ Q := hWQ ha₁W
    have hb₁Q : b₁ ∈ Q := hWQ hb₁W
    have hκx : κ x = κ ⟨a₁, ha₁Q⟩ * κ ⟨b₁, hb₁Q⟩ := by
      rw [← map_mul]
      congr 1
      exact Subtype.ext hxab
    rw [← hxb', hκx, toAdd_mul, map_add, hε ⟨a₁, ha₁Q⟩, hε ⟨b₁, hb₁Q⟩]
    exact AddSubgroup.add_mem_sup
      ((toAdd_mem_secSub_iff hκ (le_sup_right : Z ≤ B ⊔ Z) _).mpr (hBpart a₁ ⟨ha₁Q, ha₁B⟩))
      ((toAdd_mem_secSub_iff hκ (le_sup_right : Z ≤ conjSubgroup r B ⊔ Z) _).mpr
        (hCpart b₁ ⟨hb₁Q, hb₁C⟩))
  have hTcard : Nat.card ↥T ≤ Nat.card Z * Nat.card Z := by
    have h1 : Nat.card ↥T ≤ Nat.card ↥(secSub κ (B ⊔ Z) ⊔ secSub κ (conjSubgroup r B ⊔ Z)) :=
      Nat.card_mono (Set.toFinite _) hTBC
    have h2 := card_sup_mul_card_inf_addSubgroup (secSub κ (B ⊔ Z))
      (secSub κ (conjSubgroup r B ⊔ Z))
    have h3 : Nat.card ↥(secSub κ (B ⊔ Z) ⊔ secSub κ (conjSubgroup r B ⊔ Z)) ≤
        Nat.card ↥(secSub κ (B ⊔ Z) ⊔ secSub κ (conjSubgroup r B ⊔ Z)) *
          Nat.card ↥(secSub κ (B ⊔ Z) ⊓ secSub κ (conjSubgroup r B ⊔ Z)) :=
      Nat.le_mul_of_pos_right _ Nat.card_pos
    exact h1.trans (h3.trans (h2 ▸ Nat.mul_le_mul hsB hsC))
  have hirr' : ∀ U : Subgroup G, Z ≤ U → U ≤ Vt M (LB M Q B) B Z t →
      (∀ r ∈ Rt M (LB M Q B) t, ∀ u ∈ U, r * u * r⁻¹ ∈ U) →
      U = Z ∨ U = Vt M (LB M Q B) B Z t := fun U h1 h2 h3 =>
    hirr G M Q Z B hc n t hs U h1 h2 h3
  have hVirr := secSub_irred_of_irred hκ hZV hVQ hP hirr'
  obtain ⟨d, hd4, hVcard⟩ := sec7ctr_card_Vt hc hs
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hVsec : Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) = Nat.card Z ^ d := by
    have h1 := natCard_secSub_mul hZQ hκ hZV hVQ
    rw [hVcard] at h1
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have h2 : Nat.card ↥(secSub κ (Vt M (LB M Q B) B Z t)) * Nat.card Z =
        Nat.card Z ^ d * Nat.card Z := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  have hTne : T ≠ secSub κ (Vt M (LB M Q B) B Z t) := by
    intro h
    have h1 : Nat.card ↥T = Nat.card Z ^ d := by rw [h, hVsec]
    have h2 : Nat.card Z ^ 4 ≤ Nat.card Z ^ d := Nat.pow_le_pow_right (by omega) hd4
    have h3 : Nat.card Z * Nat.card Z < Nat.card Z ^ 4 := by
      have e : Nat.card Z ^ 4 = Nat.card Z * Nat.card Z * (Nat.card Z * Nat.card Z) := by ring
      rw [e]
      have hqq : 1 < Nat.card Z * Nat.card Z := by nlinarith
      exact (Nat.lt_mul_iff_one_lt_right (by omega)).mpr hqq
    omega
  have hTbot : T = ⊥ := (hVirr T hTV hTinv).resolve_right hTne
  intro x hx
  have hxQ : x ∈ Q := hWQ hx
  have h1 : ε (Multiplicative.toAdd (κ ⟨x, hxQ⟩)) ∈ T :=
    ⟨_, mem_secSub.mpr ⟨⟨x, hxQ⟩, hx, rfl⟩, rfl⟩
  rw [hTbot, AddSubgroup.mem_bot, hε ⟨x, hxQ⟩] at h1
  exact (hκ.ker _).mp (Multiplicative.toAdd.injective (h1.trans toAdd_one.symm))

theorem sec715Cent_of_parts (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h51 : Stroth51Statement) (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (hZcard : Sec7ZCardStatement) (hirr : Sec7VtIrredStatement) (hCV : Sec7CVStatement)
    (hSchur : Sec7SchurStatement) : Sec715CentStatement := by
  intro G _ _ M Q Z B _ hc n t hs _ Z0 hZ0 hZN k hk2 hkN
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) k
  have hwM : (w : G) ∈ M := w.2
  have hw2 : ∃ e : ℕ, (w : G) ^ 2 ^ e ∈ Q := by
    obtain ⟨e, he⟩ := hk2 ⟨QuotientGroup.mk' (Q.subgroupOf M) w, Subgroup.mem_zpowers _⟩
    refine ⟨e, ?_⟩
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) (w ^ 2 ^ e) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val he
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at h2
    exact h2
  have hwN : ∀ x ∈ hc.CN t, ⁅(w : G), x⁆ ∈ Q := by
    intro x hx
    have hxM : x ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hx).1
    exact (mk_commute_iff w ⟨x, hxM⟩).mp
      (hkN _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)))
  have hwR := sec715_comm_Rt_mem_Q h51 hA hZcard hc hs hZ0 hZN hwM hwN
  have hwR' : ∀ ρ ∈ Rt M (LB M Q B) t, ⁅ρ⁻¹, (w : G)⁆ ∈ Q := fun ρ hρ => by
    rw [← commutatorElement_inv]
    exact Q.inv_mem (hwR _ ((Rt M (LB M Q B) t).inv_mem hρ))
  have hwV := sec715_comm_Vt_mem_Z hirr hc hs hwM hw2 hwR'
  have hwWV := sec715_comm_Wt_mem_Vt h52a hA hCV hc hs hwM hwR' hwV
  have hwQ := sec715_comm_Q_mem_Wt h310chi hc hs hwM hwR' hwV
  have hwH := sec715_mem_H0 hc hs hwM hwV hwQ
  have hwW := sec715_comm_Wt_mem_Z h34 h52a hA hirr hc hs hwM hwR' hwV hwWV
  have hwZ0 := hSchur G M Q Z B hc n t hs Z0 hZ0 (w : G) hwH
    (fun a ha => hwR a (Subgroup.commutator_le_self _ ha)) (fun u hu => by
      rw [← commutatorElement_inv]
      exact Z.inv_mem (hwW u hu))
  exact Subgroup.mem_map.mpr ⟨w, Subgroup.mem_subgroupOf.mpr hwZ0, rfl⟩

end CFSG.RankThree.GF2n.Stroth80
