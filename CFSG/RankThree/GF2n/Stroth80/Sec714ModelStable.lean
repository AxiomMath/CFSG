module

public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelDelta
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmt
import CFSG.RankThree.GF2n.Stroth80.Sec52aProof
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec714ModelLin

public section

namespace CFSG.RankThree.GF2n.Stroth80.S714

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

omit [Finite G] in
theorem card_sup_mul_inf {X : Type} [Group X] {A C : Subgroup X}
    (h : A ≤ Subgroup.normalizer (C : Set X)) :
    Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) = Nat.card A * Nat.card C := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient A C h).toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf A)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf (A ⊔ C))
  have h3 : Nat.card (C.subgroupOf A) = Nat.card ↥(A ⊓ C) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have h4 : Nat.card (C.subgroupOf (A ⊔ C)) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h3] at h1
  rw [h4, ← e] at h2
  rw [h1, h2]
  ring

omit [Finite G] in
theorem card_mul_of_isOppDecomp {P I L₁ L₂ A₁ A₂ : Subgroup G}
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) : Nat.card P * Nat.card I = Nat.card A₁ * Nat.card A₂ := by
  obtain ⟨-, hA₁P, hIA₂, hA₂P, hsup, hinf, hcomm, -⟩ := hd
  have hnorm : A₁ ≤ Subgroup.normalizer (A₂ : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun a ha c hc => ?_
    have key : a * c * a⁻¹ = ⁅a, c⁆ * c := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact A₂.mul_mem (hIA₂ (hcomm a (hA₁P ha) c (hA₂P hc))) hc
  have h := card_sup_mul_inf hnorm
  rw [hsup, hinf] at h
  exact h

theorem commute_mk_of_mem_LB (hc : Ctx M Q Z B) (l l' : ↥M) (hl : (l : G) ∈ LB M Q B)
    (hl' : (l' : G) ∈ LB M Q B) :
    (QuotientGroup.mk l : Mbar M Q) * QuotientGroup.mk l' =
      QuotientGroup.mk l' * QuotientGroup.mk l := by
  have hsq : ∀ x : ↥M, (x : G) ∈ LB M Q B → (QuotientGroup.mk x : Mbar M Q) ^ 2 = 1 := by
    intro x hx
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hc.sq_mem_Q_of_mem_LB hx)
  have h1 := hsq l hl
  have h2 := hsq l' hl'
  have h3 := hsq (l * l') ((LB M Q B).mul_mem hl hl')
  rw [QuotientGroup.mk_mul] at h3
  set a : Mbar M Q := QuotientGroup.mk l
  set c : Mbar M Q := QuotientGroup.mk l'
  have ha : a⁻¹ = a := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, h1]
  have hc' : c⁻¹ = c := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
  have h4 : a * c = (a * c)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_two, h3]
  rw [h4, mul_inv_rev, ha, hc']

theorem conj_mem_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r x : G}
    (hr : r ∈ Rt M (LB M Q B) t) (hx : x ∈ hc.CN t) : r * x * r⁻¹ ∈ hc.CN t := by
  rw [Ctx.mem_CN] at hx ⊢
  refine ⟨(Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hr hx.1)
    ((Rt M (LB M Q B) t).inv_mem hr), fun v hv => ?_⟩
  have hv' : r⁻¹ * v * r ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp
      (hc.Rt_normalizes_Vt ht ((Rt M (LB M Q B) t).inv_mem hr)) v).mp hv
    simpa using this
  have e : ⁅r * x * r⁻¹, v⁆ = r * ⁅x, r⁻¹ * v * r⁆ * r⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (hc.Rt_le_M t hr)) _).mp
    (hx.2 _ hv')

theorem conj_Wt_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) :
    conjSubgroup r (Wt Q (Vt M (LB M Q B) B Z t)) = Wt Q (Vt M (LB M Q B) B Z t) := by
  have hle : ∀ s ∈ Rt M (LB M Q B) t,
      conjSubgroup s (Wt Q (Vt M (LB M Q B) B Z t)) ≤ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro s hs x hx
    have hx' : s⁻¹ * x * s ∈ Wt Q (Vt M (LB M Q B) B Z t) := mem_conjSubgroup.mp hx
    have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
    rw [e]
    exact conj_mem_Wt (hc.hyp.Q_normal.2 (hc.Rt_le_M t hs)) (hc.Rt_normalizes_Vt ht hs) hx'
  exact Subgroup.eq_of_le_of_card_ge (hle r hr) (by rw [card_conjSubgroup])

theorem conj_CN_eq (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {r : G}
    (hr : r ∈ Rt M (LB M Q B) t) : conjSubgroup r (hc.CN t) = hc.CN t := by
  refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (by rw [card_conjSubgroup])
  have hx' : r⁻¹ * x * r ∈ hc.CN t := mem_conjSubgroup.mp hx
  have e : x = r * (r⁻¹ * x * r) * r⁻¹ := by group
  rw [e]
  exact conj_mem_CN hc ht hr hx'

section Fix

variable (hS : IsTensorSetup hc n M₀ ρ b) (t : G) in
@[expose] def fixSub (L : Subgroup G) (hL : L ≤ Rt M (LB M Q B) t) : Submodule K M₀.E where
  carrier := {e | e ∈ wsub hS t ∧ ∀ l : ↥M, (l : G) ∈ L →
    dmap ρ (QuotientGroup.mk l) e ∈ hc.VtSub hS.model t}
  add_mem' := fun {e f} he hf => ⟨(wsub hS t).add_mem he.1 hf.1, fun l hl => by
    rw [dmap_add]
    exact (hc.VtSub hS.model t).add_mem (he.2 l hl) (hf.2 l hl)⟩
  zero_mem' := ⟨(wsub hS t).zero_mem, fun l _ => by
    rw [dmap_zero]
    exact (hc.VtSub hS.model t).zero_mem⟩
  smul_mem' := fun c e he => ⟨(wsub hS t).smul_mem c he.1, fun l hl => by
    rw [dmap_smul hS (mem_bar_H0_of_Rt hc (mk_mem_bar l (hL hl)))]
    exact (hc.VtSub hS.model t).smul_mem c (he.2 l hl)⟩

theorem mem_fixSub (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {L : Subgroup G}
    (hL : L ≤ Rt M (LB M Q B) t) {e : M₀.E} :
    e ∈ fixSub hS t L hL ↔ e ∈ wsub hS t ∧ ∀ l : ↥M, (l : G) ∈ L →
      dmap ρ (QuotientGroup.mk l) e ∈ hc.VtSub hS.model t := Iff.rfl

theorem pi_mem_fixSub_iff (hS : IsTensorSetup hc n M₀ ρ b) (t : G) {L : Subgroup G}
    (hL : L ≤ Rt M (LB M Q B) t) {x : G} (hx : x ∈ Wt Q (Vt M (LB M Q B) B Z t)) :
    M₀.π x ∈ fixSub hS t L hL ↔ ∀ l ∈ L, ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t := by
  have hxQ : x ∈ Q := hx.1
  have hcQ : ∀ m : ↥M, ⁅(m : G), x⁆ ∈ Q := fun m => by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 m.2) x).mp hxQ)
      (Q.inv_mem hxQ)
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  rw [mem_fixSub]
  constructor
  · rintro ⟨-, h⟩ l hl
    have hlM : l ∈ M := hc.Rt_le_M t (hL hl)
    have h1 := h ⟨l, hlM⟩ hl
    rw [dmap_pi hS ⟨l, hlM⟩ hxQ, hc.mem_VtSub hS.model t] at h1
    exact (M₀.mem_img_iff hZV (hcQ ⟨l, hlM⟩)).mp h1
  · intro h
    refine ⟨(mem_wsub hS t).mpr (M₀.pi_mem_img hx hxQ), fun l hl => ?_⟩
    rw [dmap_pi hS l hxQ, hc.mem_VtSub hS.model t]
    exact M₀.pi_mem_img (h l hl) (hcQ l)

end Fix

section Grp

@[expose] def deltaGrp (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hS : IsTensorSetup hc n M₀ ρ b) {t r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r)
    (P : Subgroup G) (hPN : P ≤ hc.CN t) : AddSubgroup (↥(wsub hS t) →ₗ[K] M₀.E) where
  carrier := {f | ∃ x : ↥M, ∃ hx : (x : G) ∈ P,
    f = delta hS t (QuotientGroup.mk x) (mem_bar_H0_of_CN (mk_mem_bar x (hPN hx)))}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x * y, P.mul_mem hx hy, ?_⟩
    rw [← delta_mul h310chi h52a hS hs hr (mk_mem_bar x (hPN hx)) (mk_mem_bar y (hPN hy))]
    exact delta_congr hS t (QuotientGroup.mk_mul (Q.subgroupOf M) x y).symm _ _
  zero_mem' := by
    refine ⟨1, P.one_mem, LinearMap.ext fun w => ?_⟩
    rw [delta_apply, LinearMap.zero_apply]
    exact (dmap_one (ρ := ρ) (w : M₀.E)).symm
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x⁻¹, P.inv_mem hx, ?_⟩
    have h := delta_mul h310chi h52a hS hs hr (mk_mem_bar x (hPN hx))
      (mk_mem_bar x⁻¹ (hPN (P.inv_mem hx)))
    have h1 : delta hS t ((QuotientGroup.mk x : Mbar M Q) * QuotientGroup.mk x⁻¹)
        (Subgroup.mul_mem _ (mem_bar_H0_of_CN (mk_mem_bar x (hPN hx)))
          (mem_bar_H0_of_CN (mk_mem_bar x⁻¹ (hPN (P.inv_mem hx))))) = 0 := by
      refine LinearMap.ext fun w => ?_
      rw [delta_apply, LinearMap.zero_apply, ← QuotientGroup.mk_mul, mul_inv_cancel]
      exact dmap_one (ρ := ρ) (w : M₀.E)
    rw [h1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm)

theorem card_deltaGrp_mul (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {t r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {P : Subgroup G} (hPN : P ≤ hc.CN t)
    (hZP : Z0 ≤ P) :
    Nat.card (deltaGrp h310chi h52a hS hs hr P hPN) * Nat.card Z0 = Nat.card P := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hPM : ∀ x ∈ P, x ∈ M := fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp (hPN hx)).1
  have hQZ0 : Q ≤ Z0 := fun x hx => (hZ0 x).mpr ⟨hc.Q_le_Rt ht hx, fun y hy => by
    have hyx : y * x⁻¹ * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp
      (hc.hyp.Q_normal.2 (hc.Rt_le_M t hy)) x⁻¹).mp (Q.inv_mem hx)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact Q.mul_mem hx hyx⟩
  let φ : ↥P →* Multiplicative (↥(wsub hS t) →ₗ[K] M₀.E) :=
    { toFun := fun x => Multiplicative.ofAdd (delta hS t (QuotientGroup.mk ⟨(x : G), hPM x x.2⟩)
        (mem_bar_H0_of_CN (mk_mem_bar (S := hc.CN t) ⟨(x : G), hPM x x.2⟩ (hPN x.2))))
      map_one' := by
        rw [← ofAdd_zero]
        congr 1
        refine LinearMap.ext fun w => ?_
        rw [delta_apply, LinearMap.zero_apply]
        exact dmap_one (ρ := ρ) (w : M₀.E)
      map_mul' := fun x y => by
        rw [← ofAdd_add]
        congr 1
        rw [← delta_mul h310chi h52a hS hs hr
          (mk_mem_bar (S := hc.CN t) ⟨(x : G), hPM x x.2⟩ (hPN x.2))
          (mk_mem_bar (S := hc.CN t) ⟨(y : G), hPM y y.2⟩ (hPN y.2))]
        exact delta_congr hS t (QuotientGroup.mk_mul (Q.subgroupOf M)
          (⟨(x : G), hPM x x.2⟩ : ↥M) ⟨(y : G), hPM y y.2⟩) _ _ }
  have hker : φ.ker = Z0.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have hxR : (QuotientGroup.mk ⟨(x : G), hPM x x.2⟩ : Mbar M Q) ∈
        bar M Q (Rt M (LB M Q B) t) :=
      mk_mem_bar ⟨(x : G), hPM x x.2⟩ (Ctx.mem_CN.mp (hPN x.2)).1
    have h := delta_eq_zero_iff hCRW hMp hS hs hZ0 hxR
    constructor
    · intro h1
      have h2 : delta hS t (QuotientGroup.mk ⟨(x : G), hPM x x.2⟩) (mem_bar_H0_of_Rt hc hxR) =
          0 := congrArg Multiplicative.toAdd h1
      exact (mk_mem_bar_iff_sec4 (M := M) hQZ0 ⟨(x : G), hPM x x.2⟩).mp (h.mp h2)
    · intro h1
      have h2 := h.mpr ((mk_mem_bar_iff_sec4 (M := M) hQZ0 ⟨(x : G), hPM x x.2⟩).mpr h1)
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
      exact congrArg Multiplicative.ofAdd h2
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv] at h1
  rw [h1]
  congr 1
  refine Nat.card_congr
    { toFun := fun f => ⟨Multiplicative.ofAdd (f : ↥(wsub hS t) →ₗ[K] M₀.E), by
        obtain ⟨x, hx, hfx⟩ := f.2
        exact ⟨⟨x, hx⟩, by rw [hfx]; rfl⟩⟩
      invFun := fun y => ⟨Multiplicative.toAdd (y : Multiplicative _), by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨⟨(x : G), hPM x x.2⟩, x.2, by rw [← hx]; rfl⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Grp

section Orders

theorem card_Wt_mul_Vt (h310chi : Stroth310ChiStatement) {t : G} (hs : Sec5Hyp hc n t)
    (hSpOm : SpNat hc t ∨ OmegaNat hc t) :
    Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)) * Nat.card ↥(Vt M (LB M Q B) B Z t) =
      Nat.card Q * Nat.card Z := by
  have ht : t ∈ LB M Q B := hs.mem
  obtain ⟨hVU, hWQ1⟩ := h310chi G M Q Z B hc n t hs hSpOm
  have hUt : Nat.card Q * Nat.card Z = Nat.card ↥(Q1 hc t) * Nat.card ↥(Ut Q Z t) := by
    haveI : (Z.subgroupOf (Ut Q Z t)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
        hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Ut_le_Q (hc.LB_le_M ht) hv)))
    exact card_mul_card_of_isChiIso (hc.isChiIso_Q1_Ut ht) (fun x hx => hx.1)
      (le_sup_right : Z ≤ Ut Q Z t)
  rw [← hWQ1, ← hVU] at hUt
  exact hUt.symm

theorem conj_fix_eq (hc : Ctx M Q Z B) {t r : G} (ht : t ∈ LB M Q B)
    (hr : r ∈ Rt M (LB M Q B) t) :
    conjSubgroup r ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) =
      (QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t := by
  rw [conjSubgroup_sup_eq_sup, conjSubgroup_inf, ← QB_conj, conj_Wt_eq hc ht hr,
    conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hr)]

theorem conj_LB_inf_CN (hc : Ctx M Q Z B) {t r : G} (ht : t ∈ LB M Q B)
    (hr : r ∈ Rt M (LB M Q B) t) :
    conjSubgroup r (LB M Q B ⊓ hc.CN t) = LB M Q (conjSubgroup r B) ⊓ hc.CN t := by
  rw [conjSubgroup_inf, ← hc.LB_conj (hc.Rt_le_M t hr), conj_CN_eq hc ht hr]

theorem card_fix_mul_Z0 (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    {t r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) :
    Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) * Nat.card Z0 =
      Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  obtain ⟨m, hm, hOm⟩ := hs.orth
  have hV := card_Vt_orthogonal hc hm hOm
  have hWV := card_Wt_mul_Vt h310chi hs.toSec5 (Or.inr hs.omegaNat)
  have hN := hNO G M Q Z B hc n t hs m hm hOm
  have hZ0c := hZc G M Q Z B hc n t hs Z0 hZ0
  obtain ⟨-, hLL', -, hdN⟩ := h51 G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat) r hr.mem
    hr.plane _ _ _ _ _ rfl rfl rfl rfl rfl
  have hdW := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane _ _ _ _ _ rfl rfl
    rfl rfl rfl
  have hprodN := card_mul_of_isOppDecomp hdN
  have hprodW := card_mul_of_isOppDecomp hdW
  rw [← conj_fix_eq hc ht hr.mem, card_conjSubgroup] at hprodW
  rw [← conj_LB_inf_CN hc ht hr.mem, card_conjSubgroup, hLL'] at hprodN
  set q := Nat.card Z
  set a := Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)
  set v := Nat.card ↥(Vt M (LB M Q B) B Z t)
  set l := Nat.card ↥(LB M Q B ⊓ hc.CN t)
  set z0 := Nat.card Z0
  have e1 : (a * z0) ^ 2 = (Nat.card Q * q) ^ 3 := by
    rw [mul_pow, sq a, ← hprodW, hWV, hZ0c]
    ring
  have e2 : (v * l) ^ 2 = (Nat.card Q * q) ^ 3 := by
    have h1 : v ^ 2 * Nat.card ↥(hc.CN t) = q ^ 2 * Nat.card Q ^ 2 := by
      rw [hV, ← hN]
      ring
    calc (v * l) ^ 2 = v ^ 2 * (l * l) := by ring
      _ = v ^ 2 * (Nat.card ↥(hc.CN t) * (Nat.card Q * q)) := by rw [hprodN]
      _ = (v ^ 2 * Nat.card ↥(hc.CN t)) * (Nat.card Q * q) := by ring
      _ = (Nat.card Q * q) ^ 3 := by rw [h1]; ring
  exact Nat.pow_left_injective two_ne_zero (e1.trans e2.symm)

end Orders

section Stable

theorem smul_mem_deltaGrp_LB (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {t r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) :
    ∀ f ∈ deltaGrp h310chi h52a hS hs hr (LB M Q B ⊓ hc.CN t) inf_le_right, ∀ k : K,
      k • f ∈ deltaGrp h310chi h52a hS hs hr (LB M Q B ⊓ hc.CN t) inf_le_right := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL'R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem hrM
  obtain ⟨Z0, hZ0⟩ := exists_isCentrePre (hc.Q_le_Rt ht)
  obtain ⟨hVU, hWQ1⟩ := h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
  set V := Vt M (LB M Q B) B Z t with hVdef
  set W := Wt Q V with hWdef
  have hdW := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane _ _ _ _ _ rfl rfl
    rfl rfl rfl
  obtain ⟨hVA₁, hA₁W, hVA₂, hA₂W, hsup, -, hcommW, -, hfA₁, hfA₂⟩ := hdW
  have hfix₁ : ∀ x ∈ W, M₀.π x ∈ fixSub hS t (LB M Q B) hLR ↔
      x ∈ (QB B ⊓ W) ⊔ V := fun x hx =>
    (pi_mem_fixSub_iff hS t hLR hx).trans (hfA₁ x hx).symm
  have hfix₂ : ∀ x ∈ W, M₀.π x ∈ fixSub hS t (LB M Q (conjSubgroup r B)) hL'R ↔
      x ∈ (QB (conjSubgroup r B) ⊓ W) ⊔ V := fun x hx =>
    (pi_mem_fixSub_iff hS t hL'R hx).trans (hfA₂ x hx).symm
  have hVW : V ≤ W := hVA₁.trans hA₁W
  have hcard33 : Nat.card ↥(Q ⊓ QB B) = Nat.card Z ^ (n + 1) :=
    (hc.card_of_3_3 hs.toSec5.width (by have := hs.toSec5.n_gt; omega) hs.toSec5.noA2
      (stroth_3_3 hc hs.toSec5.width (by have := hs.toSec5.n_gt; omega))).2
  have hcardC : Nat.card ↥(Q ⊓ QB (conjSubgroup r B)) = Nat.card Z ^ (n + 1) := by
    rw [QB_conj, ← hc.conj_Q_eq hrM, ← conjSubgroup_inf, card_conjSubgroup]
    exact hcard33
  obtain ⟨T, hT⟩ := hcC.exists_submodule_inf_QB hs.toSec5.width hcardC hS.model
  obtain ⟨b', -, -, hB', -, -⟩ := hc.dictB hS.model
  have hBimg : ∀ e ∈ Submodule.span K {b}, e ∈ M₀.img B := by
    intro e he
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp he
    obtain ⟨s₀, hs₀⟩ := (hB' b).mp hS.b_img
    exact (hB' _).mpr ⟨s * s₀, by rw [hs₀, smul_smul]⟩
  have hBT : Submodule.span K {b} ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    rintro e ⟨heB, heT⟩
    rw [Submodule.mem_bot]
    obtain ⟨y, hyB, hyQ, rfl⟩ := M₀.mem_img.mp (hBimg e heB)
    obtain ⟨x, hxQC, hxQ, hxy⟩ := M₀.mem_img.mp ((hT _).mp heT)
    have h1 : x⁻¹ * y ∈ Z := (Tim79.QuadModel.pi_eq_iff M₀ hxQ hyQ).mp hxy
    have hyQC : y ∈ QB (conjSubgroup r B) := by
      have e : y = x * (x⁻¹ * y) := by group
      rw [e]
      exact (QB (conjSubgroup r B)).mul_mem hxQC.2 (hcC.Z_le_QB.1 h1)
    have hy1 : y ∈ (⊥ : Subgroup G) := by
      rw [← sec52a_B_inf_QB_conj_eq_bot h34 hRoot hc hs.toSec5 hs.omegaNat hr.mem hr.plane]
      exact ⟨hyB, hyQC⟩
    rw [Subgroup.mem_bot] at hy1
    rw [hy1]
    exact Tim79.QuadModel.pi_one M₀
  let ι := {l : ↥M // (l : G) ∈ LB M Q B}
  have hιH : ∀ i : ι, (QuotientGroup.mk i.1 : Mbar M Q) ∈ bar M Q (H0 M Z) := fun i =>
    mem_bar_H0_of_Rt hc (mk_mem_bar i.1 (hLR i.2))
  let D : ι → M₀.E →ₗ[K] M₀.E := fun i => dlin hS (QuotientGroup.mk i.1) (hιH i)
  have hcQ : ∀ m : ↥M, ∀ x ∈ Q, ⁅(m : G), x⁆ ∈ Q := fun m x hx => by
    rw [commutatorElement_def]
    exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 m.2) x).mp hx)
      (Q.inv_mem hx)
  have hDW : ∀ i, ∀ w ∈ wsub hS t, D i w ∈ fixSub hS t (LB M Q B) hLR := by
    intro i w hw
    obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp hw)
    show dmap ρ (QuotientGroup.mk i.1) (M₀.π x) ∈ _
    rw [dmap_pi hS i.1 hxQ]
    have hcB : ⁅(i.1 : G), x⁆ ∈ QB B := comm_LB_Wt_mem_QB hc (hc.B_le_Vt ht) i.2 hxW
    have hcW : ⁅(i.1 : G), x⁆ ∈ W := by
      rw [commutatorElement_def]
      exact W.mul_mem (conj_mem_Wt (hc.hyp.Q_normal.2 i.1.2)
        (hc.Rt_normalizes_Vt ht (hLR i.2)) hxW) (W.inv_mem hxW)
    exact (hfix₁ _ hcW).mpr (Subgroup.mem_sup_left ⟨hcB, hcW⟩)
  have hfixB : ∀ v ∈ hc.VtSub hS.model t, (∀ i, D i v = 0) → v ∈ Submodule.span K {b} := by
    intro v _ hv
    refine (hS.fix v).mp fun ℓ hℓ => ?_
    obtain ⟨l, hl, rfl⟩ := exists_of_mem_bar hℓ
    have h1 : dmap ρ (QuotientGroup.mk l) v = 0 := hv ⟨l, hl⟩
    rw [act_eq_add_dmap, h1, add_zero]
  have hX : RestrHyp (wsub hS t) (fixSub hS t (LB M Q B) hLR)
      (fixSub hS t (LB M Q (conjSubgroup r B)) hL'R) (hc.VtSub hS.model t)
      (Submodule.span K {b}) T (fun _ he => he.1) D hDW
      (deltaGrp h310chi h52a hS hs hr (LB M Q B ⊓ hc.CN t) inf_le_right) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ w hwA
      obtain ⟨h1, -, -⟩ := dmap_CN_facts h310chi h52a hS hs hr (mk_mem_bar x hx.2)
      refine (hS.fix _).mp fun ℓ hℓ => ?_
      obtain ⟨l, hl, rfl⟩ := exists_of_mem_bar hℓ
      rw [act_eq_add_dmap, delta_apply,
        dmap_comm (commute_mk_of_mem_LB hc l x hl hx.1), h1 _ (hwA.2 l hl), add_zero]
    · rintro _ ⟨x, hx, rfl⟩ w hwV
      exact (dmap_CN_facts h310chi h52a hS hs hr (mk_mem_bar x hx.2)).1 _ hwV
    · rintro _ ⟨x, hx, rfl⟩ w hwC
      obtain ⟨y, hyW, hyQ, hyw⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp w.2)
      have hyA : y ∈ (QB (conjSubgroup r B) ⊓ W) ⊔ V := by
        rw [← hfix₂ y hyW, hyw]
        exact hwC
      have hnorm : QB (conjSubgroup r B) ⊓ W ≤ Subgroup.normalizer (V : Set G) := by
        intro a ha
        exact Subgroup.centralizer_le_normalizer (V : Set G) ha.2.2
      obtain ⟨a, ha, v, hv, rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hyA
      have haQ : a ∈ Q := ha.2.1
      have hvQ : v ∈ Q := hc.Vt_le_Q t hv
      obtain ⟨h1, -, -⟩ := dmap_CN_facts h310chi h52a hS hs hr (mk_mem_bar x hx.2)
      rw [delta_apply, ← hyw, M₀.π_mul _ haQ _ hvQ, dmap_add,
        h1 _ ((hc.mem_VtSub hS.model t).mpr (M₀.pi_mem_img hv hvQ)), add_zero,
        dmap_pi hS x haQ]
      have hnormQC := sec52a_QB_inf_normalizes_of_mem_CN hc hs.toSec5 hr.mem hx.2
      have hxa : (x : G) * a * (x : G)⁻¹ ∈ Q ⊓ QB (conjSubgroup r B) :=
        (Subgroup.mem_normalizer_iff.mp hnormQC a).mp ⟨haQ, ha.1⟩
      have hcomm : ⁅(x : G), a⁆ ∈ Q ⊓ QB (conjSubgroup r B) := by
        rw [commutatorElement_def]
        exact (Q ⊓ QB (conjSubgroup r B)).mul_mem hxa ((Q ⊓ QB (conjSubgroup r B)).inv_mem
          ⟨haQ, ha.1⟩)
      exact (hT _).mpr (M₀.pi_mem_img hcomm (hcQ x a haQ))
    · rintro _ ⟨x, hx, rfl⟩ w
      exact (dmap_CN_facts h310chi h52a hS hs hr (mk_mem_bar x hx.2)).2.1 _ w.2
    · rintro _ ⟨x, hx, rfl⟩ i w
      show dmap ρ (QuotientGroup.mk i.1) (dmap ρ (QuotientGroup.mk x) w) =
        dmap ρ (QuotientGroup.mk x) (dmap ρ (QuotientGroup.mk i.1) w)
      exact dmap_comm (commute_mk_of_mem_LB hc i.1 x i.2 hx.1) (w : M₀.E)
  have hZ0LN : Z0 ≤ LB M Q B ⊓ hc.CN t := by
    intro z hz
    obtain ⟨hzL, hzW⟩ := hMp G M Q Z B hc n t hs Z0 hZ0 z hz
    exact ⟨hzL, Ctx.mem_CN.mpr ⟨hZ0.le hz, fun v hv => hzW v (hVW hv)⟩⟩
  have hcardX := card_deltaGrp_mul h310chi h52a hCRW hMp hS hs hr hZ0 inf_le_right hZ0LN
  have hcardA := card_fix_mul_Z0 h310chi h51 h52b hNO hZc hs hr hZ0
  have hfixImg : Nat.card ↥(fixSub hS t (LB M Q B) hLR) =
      Nat.card ↥(M₀.img ((QB B ⊓ W) ⊔ V)) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun e => ?_)
    constructor
    · intro he
      obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp
        ((mem_fixSub hS t hLR).mp he).1)
      exact M₀.pi_mem_img ((hfix₁ x hxW).mp he) hxQ
    · intro he
      obtain ⟨x, hxA, hxQ, rfl⟩ := M₀.mem_img.mp he
      exact (hfix₁ x (sup_le inf_le_right hVW hxA)).mpr hxA
  have hZA : Z ≤ (QB B ⊓ W) ⊔ V := le_sup_of_le_right sec39_Z_le_Vt
  have hAQ : (QB B ⊓ W) ⊔ V ≤ Q := sup_le (inf_le_right.trans inf_le_left) (hc.Vt_le_Q t)
  have hcA := M₀.card_eq hAQ hZA
  have hcV := M₀.card_eq (hc.Vt_le_Q t) sec39_Z_le_Vt
  have hVle : hc.VtSub hS.model t ≤ fixSub hS t (LB M Q B) hLR := by
    intro v hv
    refine ⟨?_, fun l hl => ?_⟩
    · obtain ⟨x, hxV, hxQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hv)
      exact (mem_wsub hS t).mpr (M₀.pi_mem_img (hVW hxV) hxQ)
    · have h1 := hc.act_mem_VtSub hS ht (QuotientGroup.mk l) (mk_mem_bar l (hLR hl)) v hv
      simp only [dmap]
      exact (hc.VtSub hS.model t).sub_mem h1 hv
  refine smul_mem_of_card (A := fixSub hS t (LB M Q B) hLR)
    (C := fixSub hS t (LB M Q (conjSubgroup r B)) hL'R) (fun _ he => he.1) hVle
    (fun w hw => ?_) hBT (finrank_span_singleton hS.b_ne) hfixB hX ?_
  · obtain ⟨x, hxW, hxQ, rfl⟩ := M₀.mem_img.mp ((mem_wsub hS t).mp hw)
    rw [← hsup] at hxW
    have hnorm : (QB B ⊓ W) ⊔ V ≤ Subgroup.normalizer
        (((QB (conjSubgroup r B) ⊓ W) ⊔ V : Subgroup G) : Set G) := by
      refine Subgroup.le_normalizer_iff.mpr fun a ha c hc' => ?_
      have key : a * c * a⁻¹ = ⁅a, c⁆ * c := by
        rw [commutatorElement_def]
        group
      rw [key]
      exact Subgroup.mul_mem _ (hVA₂ (hcommW a (hA₁W ha) c (hA₂W hc'))) hc'
    obtain ⟨a, ha, c, hc', rfl⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hxW
    rw [M₀.π_mul _ (hAQ ha) _ (sup_le (inf_le_right.trans inf_le_left) (hc.Vt_le_Q t) hc')]
    exact Submodule.add_mem_sup ((hfix₁ a (hA₁W ha)).mpr ha) ((hfix₂ c (hA₂W hc')).mpr hc')
  ·
    haveI : Finite M₀.E := Module.finite_of_finite K
    have hfA := Module.natCard_eq_pow_finrank (K := K) (V := ↥(fixSub hS t (LB M Q B) hLR))
    have hfV := Module.natCard_eq_pow_finrank (K := K) (V := ↥(hc.VtSub hS.model t))
    have hle := Submodule.finrank_mono (R := K) hVle
    have hKZ : Nat.card K = Nat.card Z := hS.card
    have hpos : 0 < Nat.card Z := Nat.card_pos
    have hpos0 : 0 < Nat.card Z0 := Nat.card_pos
    have hsplit : Nat.card K ^ Module.finrank K ↥(fixSub hS t (LB M Q B) hLR) =
        Nat.card K ^ (Module.finrank K ↥(fixSub hS t (LB M Q B) hLR) -
          Module.finrank K ↥(hc.VtSub hS.model t)) *
        Nat.card K ^ Module.finrank K ↥(hc.VtSub hS.model t) := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    have hVimg : Nat.card ↥(hc.VtSub hS.model t) = Nat.card ↥(M₀.img V) := rfl
    have key : Nat.card K ^ (Module.finrank K ↥(fixSub hS t (LB M Q B) hLR) -
          Module.finrank K ↥(hc.VtSub hS.model t)) * (Nat.card ↥(hc.VtSub hS.model t) *
          (Nat.card Z * Nat.card Z0)) =
        Nat.card ↥(deltaGrp h310chi h52a hS hs hr (LB M Q B ⊓ hc.CN t) inf_le_right) *
          (Nat.card ↥(hc.VtSub hS.model t) * (Nat.card Z * Nat.card Z0)) := by
      have h1 : Nat.card K ^ (Module.finrank K ↥(fixSub hS t (LB M Q B) hLR) -
          Module.finrank K ↥(hc.VtSub hS.model t)) * Nat.card ↥(hc.VtSub hS.model t) =
          Nat.card ↥(fixSub hS t (LB M Q B) hLR) := by
        rw [hfA, hfV, hsplit]
      calc _ = (Nat.card K ^ (Module.finrank K ↥(fixSub hS t (LB M Q B) hLR) -
            Module.finrank K ↥(hc.VtSub hS.model t)) * Nat.card ↥(hc.VtSub hS.model t)) *
            Nat.card Z * Nat.card Z0 := by ring
        _ = Nat.card Z * Nat.card ↥(M₀.img ((QB B ⊓ W) ⊔ V)) * Nat.card Z0 := by
          rw [h1, hfixImg]
          ring
        _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
          rw [← hcA, hcardA]
        _ = Nat.card Z * Nat.card ↥(M₀.img V) *
            (Nat.card ↥(deltaGrp h310chi h52a hS hs hr (LB M Q B ⊓ hc.CN t) inf_le_right) *
              Nat.card Z0) := by rw [← hcV, hcardX]
        _ = _ := by rw [hVimg]; ring
    have hne : 0 < Nat.card ↥(hc.VtSub hS.model t) * (Nat.card Z * Nat.card Z0) := by
      have : 0 < Nat.card ↥(hc.VtSub hS.model t) := Nat.card_pos
      positivity
    exact (Nat.eq_of_mul_eq_mul_right hne key).le

theorem exists_delta_smul (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {t r : G} (hs : Sec7Hyp hc n t) (hr : Sec7A hc t r) {g : Mbar M Q}
    (hg : g ∈ bar M Q (hc.CN t)) (k : K) :
    ∃ (g' : Mbar M Q) (hg' : g' ∈ bar M Q (hc.CN t)),
      delta hS t g' (mem_bar_H0_of_CN hg') = k • delta hS t g (mem_bar_H0_of_CN hg) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hstab := smul_mem_deltaGrp_LB h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hS hs hr
  obtain ⟨x, hxN, rfl⟩ := exists_of_mem_bar hg
  obtain ⟨hprod, -, -, -⟩ := h51 G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat) r hr.mem
    hr.plane _ _ _ _ _ rfl rfl rfl rfl rfl
  obtain ⟨a, ha, c, hc', hac⟩ := hprod x hxN
  have hNM : ∀ y ∈ hc.CN t, y ∈ M := fun y hy => hc.Rt_le_M t (Ctx.mem_CN.mp hy).1
  have haM : a ∈ M := hNM a ha.2
  have hcM : c ∈ M := hNM c hc'.2
  have hc₀ : r⁻¹ * c * r ∈ LB M Q B ⊓ hc.CN t := by
    rw [← conj_LB_inf_CN hc ht hr.mem] at hc'
    have := mem_conjSubgroup.mp hc'
    exact this
  have hc₀M : r⁻¹ * c * r ∈ M := hNM _ hc₀.2
  obtain ⟨a', ha', hΔa⟩ := hstab _ ⟨⟨a, haM⟩, ha, rfl⟩ k
  obtain ⟨c', hc'', hΔc⟩ := hstab _ ⟨⟨r⁻¹ * c * r, hc₀M⟩, hc₀, rfl⟩ k
  let rb : Mbar M Q := QuotientGroup.mk (⟨r, hrM⟩ : ↥M)
  have hrb : rb ∈ bar M Q (Rt M (LB M Q B) t) := mk_mem_bar _ hr.mem
  have hc'N : r * (c' : G) * r⁻¹ ∈ hc.CN t := conj_mem_CN hc ht hr.mem hc''.2
  have hcbar : rb * QuotientGroup.mk c' * rb⁻¹ ∈ bar M Q (hc.CN t) := by
    have e : rb * QuotientGroup.mk c' * rb⁻¹ =
        QuotientGroup.mk (⟨r * (c' : G) * r⁻¹, hNM _ hc'N⟩ : ↥M) := by
      simp only [rb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
      rfl
    rw [e]
    exact mk_mem_bar _ hc'N
  have hg'N : (QuotientGroup.mk a' : Mbar M Q) * (rb * QuotientGroup.mk c' * rb⁻¹) ∈
      bar M Q (hc.CN t) := Subgroup.mul_mem _ (mk_mem_bar a' ha'.2) hcbar
  refine ⟨_, hg'N, LinearMap.ext fun w => ?_⟩
  show dmap ρ (QuotientGroup.mk a' * (rb * QuotientGroup.mk c' * rb⁻¹)) (w : M₀.E) =
    k • dmap ρ (QuotientGroup.mk x) (w : M₀.E)
  have hΔa' : ∀ w : ↥(wsub hS t), dmap ρ (QuotientGroup.mk a') w =
      k • dmap ρ (QuotientGroup.mk (⟨a, haM⟩ : ↥M)) w := fun w => by
    have := LinearMap.congr_fun hΔa w
    rw [LinearMap.smul_apply, delta_apply, delta_apply] at this
    exact this.symm
  have hΔc' : ∀ w : ↥(wsub hS t), dmap ρ (QuotientGroup.mk c') w =
      k • dmap ρ (QuotientGroup.mk (⟨r⁻¹ * c * r, hc₀M⟩ : ↥M)) w := fun w => by
    have := LinearMap.congr_fun hΔc w
    rw [LinearMap.smul_apply, delta_apply, delta_apply] at this
    exact this.symm
  have hcN' : (QuotientGroup.mk c' : Mbar M Q) ∈ bar M Q (hc.CN t) := mk_mem_bar c' hc''.2
  have hc₀N : (QuotientGroup.mk (⟨r⁻¹ * c * r, hc₀M⟩ : ↥M) : Mbar M Q) ∈ bar M Q (hc.CN t) :=
    mk_mem_bar _ hc₀.2
  have hconj := delta_conj hS ht hrb (mem_bar_H0_of_CN hcN') w
  have hconj₀ := delta_conj hS ht hrb (mem_bar_H0_of_CN hc₀N) w
  rw [delta_apply, delta_apply] at hconj hconj₀
  have hcEq : rb * QuotientGroup.mk (⟨r⁻¹ * c * r, hc₀M⟩ : ↥M) * rb⁻¹ =
      QuotientGroup.mk (⟨c, hcM⟩ : ↥M) := by
    simp only [rb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hxEq : (QuotientGroup.mk x : Mbar M Q) =
      QuotientGroup.mk (⟨a, haM⟩ : ↥M) * QuotientGroup.mk (⟨c, hcM⟩ : ↥M) := by
    rw [← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext hac
  have hA : dmap ρ (QuotientGroup.mk a' * (rb * QuotientGroup.mk c' * rb⁻¹)) (w : M₀.E) =
      dmap ρ (QuotientGroup.mk a') w + dmap ρ (rb * QuotientGroup.mk c' * rb⁻¹) w := by
    have := LinearMap.congr_fun (delta_mul h310chi h52a hS hs hr (mk_mem_bar a' ha'.2) hcbar) w
    simpa only [delta_apply, LinearMap.add_apply] using this
  have hX : dmap ρ (QuotientGroup.mk x) (w : M₀.E) =
      dmap ρ (QuotientGroup.mk (⟨a, haM⟩ : ↥M)) w +
        dmap ρ (QuotientGroup.mk (⟨c, hcM⟩ : ↥M)) w := by
    rw [hxEq]
    have := LinearMap.congr_fun (delta_mul h310chi h52a hS hs hr
      (mk_mem_bar (S := hc.CN t) ⟨a, haM⟩ ha.2) (mk_mem_bar (S := hc.CN t) ⟨c, hcM⟩ hc'.2)) w
    simpa only [delta_apply, LinearMap.add_apply] using this
  have hC : dmap ρ (rb * QuotientGroup.mk c' * rb⁻¹) (w : M₀.E) =
      k • dmap ρ (QuotientGroup.mk (⟨c, hcM⟩ : ↥M)) w := by
    rw [hconj, hΔc', hS.lin rb (mem_bar_H0_of_Rt hc hrb), ← hconj₀, hcEq]
  rw [hA, hX, hΔa', hC, smul_add]

end Stable

end CFSG.RankThree.GF2n.Stroth80.S714
