module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux
public import CFSG.RankThree.GF2n.Stroth80.Sec79Split
public import CFSG.RankThree.GF2n.Stroth80.OppDecompSplit
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem exists_comm_section_Wt (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement)
    (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q)
    (hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∈ Z)
    (hex : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x, w⁆ ∉ Vt M (LB M Q B) B Z t) :
    ∃ P : Subgroup G, Vt M (LB M Q B) B Z t < P ∧ P ≤ Wt Q (Vt M (LB M Q B) B Z t) ∧
      (∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) ∧
      (∀ y ∈ P, ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
        y * ⁅x, w⁆⁻¹ ∈ Vt M (LB M Q B) B Z t) := by
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
  have hxVn : x ∈ Subgroup.normalizer (V : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)
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
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hsec
  let xR : ↥R' := ⟨x, hxR'⟩
  let φ : Md →+ Md := AddMonoidHom.mk' (fun a => xR • a - a) (fun a b => by
    rw [smul_add]; abel)
  have hφ : ∀ a, φ a = xR • a - a := fun a => rfl
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
  have hφcomm : ∀ (r : G) (hr : r ∈ R) (a : Md),
      (⟨r, hRR' r hr⟩ : ↥R') • φ a = φ ((⟨r, hRR' r hr⟩ : ↥R') • a) := by
    intro r hr a
    have hcn : ⁅r, x⁆ ∈ hc.CN t := comm_mem_CN_of_vanish hc hs hxM hxt hxV hr
    have hcR' : ⁅r, x⁆ ∈ R' := hRR' _ (Ctx.mem_CN.mp hcn).1
    have hrel : (⟨⁅r, x⁆, hcR'⟩ : ↥R') * (xR * ⟨r, hRR' r hr⟩) = ⟨r, hRR' r hr⟩ * xR := by
      apply Subtype.ext
      show ⁅r, x⁆ * (x * r) = r * x
      simp only [commutatorElement_def]
      group
    have h1 : (⟨r, hRR' r hr⟩ : ↥R') • xR • a = xR • (⟨r, hRR' r hr⟩ : ↥R') • a := by
      rw [← mul_smul, ← hrel, mul_smul, hNtriv _ hcn, mul_smul]
    rw [hφ, hφ, smul_sub, h1]
  obtain ⟨P, hVP, hPW, hPsec⟩ := exists_secSub_eq hVW hκ φ.range
  have hmemP : ∀ y : ↥W, (y : G) ∈ P ↔ Multiplicative.toAdd (κ y) ∈ φ.range := fun y => by
    rw [← hPsec]
    exact (toAdd_mem_secSub_iff hκ hVP y).symm
  have hcommW : ∀ w : ↥W, ⁅x, (w : G)⁆ ∈ W := fun w => by
    have h1 : x * w * x⁻¹ ∈ W := conj_mem_Wt hxQn hxVn w.2
    rw [show ⁅x, (w : G)⁆ = x * w * x⁻¹ * (w : G)⁻¹ by simp only [commutatorElement_def]]
    exact W.mul_mem h1 (W.inv_mem w.2)
  have hκcomm : ∀ w : ↥W, κ ⟨⁅x, (w : G)⁆, hcommW w⟩ =
      Multiplicative.ofAdd (φ (Multiplicative.toAdd (κ w))) := by
    intro w
    have hxw : x * w * x⁻¹ ∈ W := conj_mem_Wt hxQn hxVn w.2
    have h1 := hκ.act xR w ⟨x * w * x⁻¹, hxw⟩ rfl
    have e : (⟨⁅x, (w : G)⁆, hcommW w⟩ : ↥W) = ⟨x * w * x⁻¹, hxw⟩ * w⁻¹ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, map_mul, map_inv, h1, hφ, sub_eq_add_neg, ofAdd_add, ofAdd_neg, ofAdd_toAdd]
  refine ⟨P, ?_, hPW, ?_, ?_⟩
  · obtain ⟨w0, hw0, hw0V⟩ := hex
    refine lt_of_le_of_ne hVP fun h => hw0V ?_
    have h1 : ⁅x, w0⁆ ∈ P := by
      have := (hmemP ⟨⁅x, w0⁆, hcommW ⟨w0, hw0⟩⟩).mpr (by
        rw [hκcomm ⟨w0, hw0⟩, toAdd_ofAdd]
        exact ⟨_, rfl⟩)
      exact this
    rw [h]
    exact h1
  · intro r hr
    have hle : ∀ r ∈ R, ∀ y ∈ P, r * y * r⁻¹ ∈ P := by
      intro r hr y hy
      have hyW : y ∈ W := hPW hy
      have hrW : r * y * r⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hRR' r hr).1 y).mp hyW
      obtain ⟨a, ha⟩ := (hmemP ⟨y, hyW⟩).mp hy
      have h1 := hκ.act ⟨r, hRR' r hr⟩ ⟨y, hyW⟩ ⟨r * y * r⁻¹, hrW⟩ rfl
      refine (hmemP ⟨r * y * r⁻¹, hrW⟩).mpr ?_
      rw [h1, toAdd_ofAdd]
      refine ⟨(⟨r, hRR' r hr⟩ : ↥R') • a, ?_⟩
      rw [← hφcomm r hr a, ha]
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hy' : r⁻¹ * y * r ∈ P := mem_conjSubgroup.mp hy
      have := hle r hr _ hy'
      simpa [mul_assoc] using this
    · rw [mem_conjSubgroup]
      have := hle r⁻¹ (R.inv_mem hr) y hy
      simpa using this
  · intro y hy
    have hyW : y ∈ W := hPW hy
    obtain ⟨a, ha⟩ := (hmemP ⟨y, hyW⟩).mp hy
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    refine ⟨w, w.2, ?_⟩
    have h1 : κ ⟨⁅x, (w : G)⁆, hcommW w⟩ = κ ⟨y, hyW⟩ := by
      rw [hκcomm w, hw, toAdd_ofAdd, ha, ofAdd_toAdd]
    exact (hκ.eq_iff ⟨y, hyW⟩ ⟨⁅x, (w : G)⁆, hcommW w⟩).mp h1.symm


theorem oppDecomp_of_invariant_section (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {P : Subgroup G} (hVP : Vt M (LB M Q B) B Z t ≤ P)
    (hPW : P ≤ Wt Q (Vt M (LB M Q B) B Z t))
    (hPR : ∀ r ∈ Rt M (LB M Q B) t, conjSubgroup r P = P) :
    ∃ r : G, Sec7A hc t r ∧
      IsOppDecomp P (Vt M (LB M Q B) B Z t) (LB M Q B) (LB M Q (conjSubgroup r B))
        (P ⊓ ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t))
        (P ⊓ ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
          Vt M (LB M Q B) B Z t)) := by
  classical
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  refine ⟨r, hr, ?_⟩
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hQM : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hVn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Vt M (LB M Q B) B Z t,
      x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun x hx y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hx) y).mp hy
  have hWN' : ∀ s ∈ hc.CN t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      ⁅s, y⁆ ∈ Vt M (LB M Q B) B Z t := sec7_N_comm_W_le_V h52a hA hc hs
  have hd := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  have hWn : ∀ x ∈ Rt M (LB M Q B) t, ∀ y ∈ Wt Q (Vt M (LB M Q B) B Z t),
      x * y * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun x hx y hy =>
    conj_mem_Wt (hQM (hRM hx)) (hc.Rt_normalizes_Vt ht hx) hy
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', -, -, huu', hrange, hker, hsec, hLu, hLu'⟩
  · have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hsplit := sec79_split_of_hom (ElemMatrixIso.plus hm')
      (nondegenerate_polarBilin_quadPlus m' K) (by rw [hι]; omega) φ hrange hker hWn hVn hWN'
      hd hLR hL2R hu hu' huu' (by rw [ElemMatrixIso.LomGL_plus hm']; exact hLu)
      (by rw [hLA, ElemMatrixIso.LomGL_plus hm']; exact hLu') hVP hPW hPR
    exact isOppDecomp_of_split hd hVP hPW hsplit
  · have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    have hsplit := sec79_split_of_hom (ElemMatrixIso.minus hm' hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m' K hirr) (by rw [hι]; omega) φ hrange hker
      hWn hVn hWN' hd hLR hL2R hu hu' huu'
      (by rw [ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu)
      (by rw [hLA, ElemMatrixIso.LomGL_minus hm' hirr]; exact hLu') hVP hPW hPR
    exact isOppDecomp_of_split hd hVP hPW hsplit


theorem step71TypeSec_of_inputs (h52a : Stroth52aStatement) (h52b : Stroth52bStatement)
    (hA : Sec7AExistsStatement) (h310chi : Stroth310ChiStatement)
    (hPts : Sec5NatPointsOmegaStatement) : Step71TypeSecStatement := by
  intro G _ _ M Q Z B hc n t hs hno x hx hxt hxV hex
  have hWN := sec7_N_comm_W_le_V h52a hA hc hs
  obtain ⟨P, hVP, hPW, hPR, hPchar⟩ := exists_comm_section_Wt h52a hA h310chi hc hs hx.1 hxt hxV hex
  refine ⟨P, hVP, hPW, hPR, fun k hk y hy => hWN k hk y (hPW hy), ?_, ?_⟩
  · obtain ⟨r, hr, hdec⟩ := oppDecomp_of_invariant_section hA hPts h52a h52b hc hs hVP.le hPW hPR
    exact ⟨r, hr, _, _, hdec⟩
  · intro m hm2 hmtype
    obtain ⟨g, hg, hcomm⟩ := comm_conjMod_mem_conj h310chi hc hs hx
    have hPle : P ≤ Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
      intro y hy
      obtain ⟨w, hw, hyw⟩ := hPchar y hy
      have e : y = (y * ⁅x, w⁆⁻¹) * ⁅x, w⁆ := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyw)
        (Subgroup.mem_sup_right (hcomm w hw.1))
    have hcardP : Nat.card ↥P ≤
        Nat.card ↥(Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)) :=
      Nat.card_mono (Set.toFinite _) hPle
    have h1 := card_sup_conj_mul_le hc sec39_Z_le_Vt (hc.Vt_le_Q t) hg
    have hV := card_Vt_orthogonal hc hm2 hmtype
    have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
    refine Nat.le_of_mul_le_mul_right ?_ hZpos
    calc Nat.card ↥P * Nat.card ↥Z ≤ Nat.card ↥(Vt M (LB M Q B) B Z t ⊔
          conjSubgroup g (Vt M (LB M Q B) B Z t)) * Nat.card ↥Z :=
        Nat.mul_le_mul_right _ hcardP
      _ ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥(Vt M (LB M Q B) B Z t) := h1
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * (Nat.card ↥Z * Nat.card ↥Z ^ (2 * m)) := by
        rw [← hV]
      _ = Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card ↥Z ^ (2 * m) * Nat.card ↥Z := by ring

end CFSG.RankThree.GF2n.Stroth80
