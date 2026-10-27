module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsAux
public import CFSG.RankThree.GF2n.Stroth80.Sec78HypFrame

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem card_arith_vanish (q n m a w i s v : ℕ) (hq : 4 ≤ q) (hv : v = q * q ^ (2 * m))
    (hw : w * v = q ^ (2 * n + 1) * q) (ha : a * a = w * v) (hi : 2 * q ≤ i)
    (hsi : s * i = v * v) (has : a ≤ s) : 2 * n ≤ 8 * m - 2 := by
  have hqpos : 0 < q := by omega
  have h1 : a * (2 * q) ≤ v * v := by
    calc a * (2 * q) ≤ a * i := Nat.mul_le_mul_left _ hi
      _ ≤ s * i := Nat.mul_le_mul_right _ has
      _ = v * v := hsi
  have h2 : (a * (2 * q)) * (a * (2 * q)) ≤ (v * v) * (v * v) := Nat.mul_le_mul h1 h1
  have h3 : 4 * q ^ (2 * n + 4) ≤ q ^ (8 * m + 4) := by
    have e1 : (a * (2 * q)) * (a * (2 * q)) = 4 * q ^ (2 * n + 4) := by
      calc (a * (2 * q)) * (a * (2 * q)) = (a * a) * (4 * q ^ 2) := by ring
        _ = (q ^ (2 * n + 1) * q) * (4 * q ^ 2) := by rw [ha, hw]
        _ = 4 * q ^ (2 * n + 4) := by ring
    have e2 : (v * v) * (v * v) = q ^ (8 * m + 4) := by
      rw [hv]
      ring
    rw [e1, e2] at h2
    exact h2
  by_contra hcon
  have hn : 8 * m ≤ 2 * n := by omega
  have h4 : q ^ (8 * m + 4) ≤ q ^ (2 * n + 4) :=
    Nat.pow_le_pow_right hqpos (by omega)
  have h5 : 0 < q ^ (8 * m + 4) := by positivity
  have h6 : 4 * q ^ (8 * m + 4) ≤ 4 * q ^ (2 * n + 4) := Nat.mul_le_mul_left _ h4
  omega

omit [Finite G] in
theorem conjSubgroup_eq_of_isOppDecomp {P I L₁ L₂ A₁ A₂ : Subgroup G}
    (hd : IsOppDecomp P I L₁ L₂ A₁ A₂) {x : G} (hxL : conjSubgroup x L₁ = L₂)
    (hxP : ∀ y ∈ P, x * y * x⁻¹ ∈ P) (hxP' : ∀ y ∈ P, x⁻¹ * y * x ∈ P)
    (hxI : ∀ y ∈ I, x * y * x⁻¹ ∈ I) (hxI' : ∀ y ∈ I, x⁻¹ * y * x ∈ I) :
    conjSubgroup x A₁ = A₂ := by
  unfold IsOppDecomp at hd
  obtain ⟨-, hA₁P, -, hA₂P, -, -, -, -, hA₁cl, hA₂cl⟩ := hd
  ext y
  rw [mem_conjSubgroup]
  constructor
  · intro hy
    have hPy : x⁻¹ * y * x ∈ P := hA₁P hy
    have hyP : y ∈ P := by
      have h := hxP _ hPy
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rwa [e] at h
    refine (hA₂cl y hyP).2 ?_
    intro l hl
    have hl2 : l ∈ conjSubgroup x L₁ := by
      rw [hxL]
      exact hl
    have hl' : x⁻¹ * l * x ∈ L₁ := mem_conjSubgroup.1 hl2
    have hm : ⁅x⁻¹ * l * x, x⁻¹ * y * x⁆ ∈ I := (hA₁cl _ hPy).1 hy _ hl'
    have heq : ⁅l, y⁆ = x * ⁅x⁻¹ * l * x, x⁻¹ * y * x⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact hxI _ hm
  · intro hy
    have hyP : y ∈ P := hA₂P hy
    have hPy : x⁻¹ * y * x ∈ P := hxP' y hyP
    refine (hA₁cl _ hPy).2 ?_
    intro l hl
    have hl2 : x * l * x⁻¹ ∈ L₂ := by
      rw [← hxL, mem_conjSubgroup]
      have e : x⁻¹ * (x * l * x⁻¹) * x = l := by group
      rw [e]
      exact hl
    have hm : ⁅x * l * x⁻¹, y⁆ ∈ I := (hA₂cl y hyP).1 hy _ hl2
    have heq : ⁅l, x⁻¹ * y * x⁆ = x⁻¹ * ⁅x * l * x⁻¹, y⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact hxI' _ hm

theorem exists_comm_section_card_ge (hc : Ctx M Q Z B) {x : G}
    {V W A₁ : Subgroup G} (hZV : Z ≤ V) (hWQ : W ≤ Q)
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxW : x ∈ Subgroup.normalizer (W : Set G))
    (hVA : V ≤ A₁) (hAW : A₁ ≤ W) (hint : A₁ ⊓ conjSubgroup x A₁ = V) :
    ∃ P : Subgroup G, V ≤ P ∧ P ≤ W ∧ (∀ y ∈ P, ∃ w ∈ W, y * ⁅x, w⁆⁻¹ ∈ V) ∧
      Nat.card ↥A₁ ≤ Nat.card ↥P := by
  have hVW : V ≤ W := hVA.trans hAW
  have hxw : ∀ w ∈ W, x * w * x⁻¹ ∈ W := fun w hw =>
    (Subgroup.mem_normalizer_iff.mp hxW w).mp hw
  let R' : Subgroup G := Subgroup.normalizer (W : Set G) ⊓ Subgroup.normalizer (V : Set G)
  have hsec : SecHyp R' W V :=
    ⟨hVW, fun a ha b hb => hZV (hc.hyp.toHyp79.comm_mem_V (hWQ ha) (hWQ hb)),
      fun a ha => hZV (hc.hyp.toHyp79.sq_mem_V (hWQ ha)),
      fun r hr a ha => (Subgroup.mem_normalizer_iff.mp hr.1 a).mp ha,
      fun r hr a ha => (Subgroup.mem_normalizer_iff.mp hr.2 a).mp ha⟩
  have hxR' : x ∈ R' := ⟨hxW, hxV⟩
  obtain ⟨Md, iA, iD, κ, hκ⟩ := exists_sectionModule hsec
  let xR : ↥R' := ⟨x, hxR'⟩
  let φ : Md →+ Md := AddMonoidHom.mk' (fun a => xR • a - a) (fun a b => by
    rw [smul_add]; abel)
  have hφ : ∀ a, φ a = xR • a - a := fun a => rfl
  obtain ⟨P, hVP, hPW, hPsec⟩ := exists_secSub_eq hVW hκ φ.range
  have hmemP : ∀ y : ↥W, (y : G) ∈ P ↔ Multiplicative.toAdd (κ y) ∈ φ.range := fun y => by
    rw [← hPsec]
    exact (toAdd_mem_secSub_iff hκ hVP y).symm
  have hcommW : ∀ w : ↥W, ⁅x, (w : G)⁆ ∈ W := fun w => by
    have h1 : x * (w : G) * x⁻¹ ∈ W := hxw _ w.2
    rw [show ⁅x, (w : G)⁆ = x * (w : G) * x⁻¹ * (w : G)⁻¹ by
      simp only [commutatorElement_def]]
    exact W.mul_mem h1 (W.inv_mem w.2)
  have hκcomm : ∀ w : ↥W, κ ⟨⁅x, (w : G)⁆, hcommW w⟩ =
      Multiplicative.ofAdd (φ (Multiplicative.toAdd (κ w))) := by
    intro w
    have hxw' : x * (w : G) * x⁻¹ ∈ W := hxw _ w.2
    have h1 := hκ.act xR w ⟨x * (w : G) * x⁻¹, hxw'⟩ rfl
    have e : (⟨⁅x, (w : G)⁆, hcommW w⟩ : ↥W) = ⟨x * (w : G) * x⁻¹, hxw'⟩ * w⁻¹ := by
      apply Subtype.ext
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e, map_mul, map_inv, h1, hφ, sub_eq_add_neg, ofAdd_add, ofAdd_neg, ofAdd_toAdd]
  have hkerS : ∀ a ∈ secSub κ A₁, φ a = 0 → a = 0 := by
    intro a ha hφa
    obtain ⟨c, hcA, hca⟩ := mem_secSub.mp ha
    have hκc : Multiplicative.toAdd (κ c) = a := by rw [hca, toAdd_ofAdd]
    have h1 := hκcomm c
    rw [hκc, hφa, ofAdd_zero] at h1
    have hxc : ⁅x, (c : G)⁆ ∈ V := (hκ.ker ⟨⁅x, (c : G)⁆, hcommW c⟩).mp h1
    have hxc' : x * (c : G) * x⁻¹ ∈ A₁ ⊓ conjSubgroup x A₁ := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have e : x * (c : G) * x⁻¹ = ⁅x, (c : G)⁆ * (c : G) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact A₁.mul_mem (hVA hxc) hcA
      · rw [mem_conjSubgroup]
        have e : x⁻¹ * (x * (c : G) * x⁻¹) * x = c := by group
        rw [e]
        exact hcA
    rw [hint] at hxc'
    have hcV : (c : G) ∈ V := (Subgroup.mem_normalizer_iff.mp hxV (c : G)).mpr hxc'
    have h2 : κ c = 1 := (hκ.ker c).mpr hcV
    rw [hca] at h2
    exact ofAdd_eq_one.mp h2
  have hinj : Function.Injective (fun a : ↥(secSub κ A₁) =>
      (⟨φ (a : Md), AddMonoidHom.mem_range.mpr ⟨(a : Md), rfl⟩⟩ : ↥φ.range)) := by
    intro a b hab
    have h1 : φ (a : Md) = φ (b : Md) := congrArg Subtype.val hab
    have h2 : φ ((a : Md) - (b : Md)) = 0 := by rw [map_sub, h1, sub_self]
    have h3 : (a : Md) - (b : Md) = 0 :=
      hkerS _ ((secSub κ A₁).sub_mem a.2 b.2) h2
    exact Subtype.ext (sub_eq_zero.mp h3)
  have hfin : Finite Md := hκ.finite
  have hcard1 : Nat.card ↥(secSub κ A₁) ≤ Nat.card ↥φ.range :=
    Nat.card_le_card_of_injective _ hinj
  have hA1 : Nat.card ↥(secSub κ A₁) * Nat.card ↥V = Nat.card ↥A₁ :=
    natCard_secSub_mul hVW hκ hVA hAW
  have hPc : Nat.card ↥φ.range * Nat.card ↥V = Nat.card ↥P := by
    rw [← hPsec]
    exact natCard_secSub_mul hVW hκ hVP hPW
  refine ⟨P, hVP, hPW, ?_, ?_⟩
  · intro y hy
    have hyW : y ∈ W := hPW hy
    obtain ⟨a, ha⟩ := (hmemP ⟨y, hyW⟩).mp hy
    obtain ⟨w, hw⟩ := hκ.surj (Multiplicative.ofAdd a)
    refine ⟨(w : G), w.2, ?_⟩
    have h1 : κ ⟨⁅x, (w : G)⁆, hcommW w⟩ = κ ⟨y, hyW⟩ := by
      rw [hκcomm w, hw, toAdd_ofAdd, ha, ofAdd_toAdd]
    exact (hκ.eq_iff ⟨y, hyW⟩ ⟨⁅x, (w : G)⁆, hcommW w⟩).mp h1.symm
  · calc Nat.card ↥A₁ = Nat.card ↥(secSub κ A₁) * Nat.card ↥V := hA1.symm
      _ ≤ Nat.card ↥φ.range * Nat.card ↥V := Nat.mul_le_mul_right _ hcard1
      _ = Nat.card ↥P := hPc

theorem step71VanishBound_core (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) {r : G}
    (hrR : r ∈ Rt M (LB M Q B) t) (hplane : HypPlane Q Z B (conjSubgroup r B) t)
    {x : G} (hx : ConjMod M Q t x) (hxt : ⁅x, t⁆ ∈ Q)
    (hmov : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z)
    (hpair : conjSubgroup x B ⊔ Z = conjSubgroup r B ⊔ Z)
    {m : ℕ} (hm2 : 2 ≤ m) (hmt : OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) :
    2 * n ≤ 8 * m - 2 := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hxM : x ∈ M := hx.1
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hrM : r ∈ M := hRM hrR
  obtain ⟨hVU, hWQ1⟩ := h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)
  have hZQ : Z ≤ Q := hc.hyp.Z_normal.1
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)
  have hxQn : x ∈ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2 hxM
  have hxWn : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), x * w * x⁻¹ ∈ Wt Q (Vt M (LB M Q B) B Z t) :=
    fun w hw => conj_mem_Wt hxQn hxVn hw
  have hxWn' : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t),
      x⁻¹ * w * x ∈ Wt Q (Vt M (LB M Q B) B Z t) := fun w hw => by
    have := conj_mem_Wt (Subgroup.inv_mem _ hxQn) (Subgroup.inv_mem _ hxVn) hw
    simpa using this
  have hxVc : ∀ y ∈ Vt M (LB M Q B) B Z t, x * y * x⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun y hy => (Subgroup.mem_normalizer_iff.mp hxVn y).mp hy
  have hxVc' : ∀ y ∈ Vt M (LB M Q B) B Z t, x⁻¹ * y * x ∈ Vt M (LB M Q B) B Z t :=
    fun y hy => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxVn) y).mp hy
      simpa using this
  have hd := h52b G M Q Z B hc n t hs.toSec5 hs.omegaNat r hrR hplane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  have hxL : conjSubgroup x (LB M Q B) = LB M Q (conjSubgroup r B) := by
    rw [hc.conj_LB_eq_of_conj_BZ hxM hrM hpair, hc.LB_conj hrM]
  have hsw := conjSubgroup_eq_of_isOppDecomp hd hxL hxWn hxWn' hxVc hxVc'
  have hAA := card_mul_card_isOppDecomp hd
  obtain ⟨hVA, hAW, -, -, -, hinfA, -⟩ := hd
  have hint : ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) ⊓
      conjSubgroup x ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) =
        Vt M (LB M Q B) B Z t := by
    rw [hsw]
    exact hinfA
  have hxWN : x ∈ Subgroup.normalizer (Wt Q (Vt M (LB M Q B) B Z t) : Set G) :=
    Subgroup.mem_normalizer_fintype fun w hw => hxWn w hw
  obtain ⟨P, hVP, hPW, hPchar, hAP⟩ := exists_comm_section_card_ge hc hZV hWQ hxVn hxWN hVA
    hAW hint
  obtain ⟨g, hg, hcomm⟩ := comm_conjMod_mem_conj h310chi hc hs hx
  have hPle : P ≤ Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    intro y hy
    obtain ⟨w, hw, hyw⟩ := hPchar y hy
    have e : y = (y * ⁅x, w⁆⁻¹) * ⁅x, w⁆ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hyw)
      (Subgroup.mem_sup_right (hcomm w hw.1))
  obtain ⟨v₀, hv₀, hxv₀⟩ := hmov
  have hZg : Z ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) := hc.Z_le_conjSubgroup hZV hg
  have hmemI : ⁅x, v₀⁆ ∈ Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    refine Subgroup.mem_inf.mpr ⟨?_, hcomm v₀ (hVQ hv₀)⟩
    rw [commutatorElement_def]
    exact (Vt M (LB M Q B) B Z t).mul_mem (hxVc v₀ hv₀) ((Vt M (LB M Q B) B Z t).inv_mem hv₀)
  have hZlt : Z < Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
    lt_of_le_of_ne (le_inf hZV hZg) (fun h => hxv₀ (by rw [h]; exact hmemI))
  have hdvd := Subgroup.card_dvd_of_le hZlt.le
  have hne : Nat.card ↥Z ≠ Nat.card ↥(Vt M (LB M Q B) B Z t ⊓
      conjSubgroup g (Vt M (LB M Q B) B Z t)) := fun h =>
    hZlt.ne (Subgroup.eq_of_le_of_card_ge hZlt.le h.symm.le)
  obtain ⟨k, hk⟩ := hdvd
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hk
      exact absurd hk (Nat.card_pos (α := ↥(Vt M (LB M Q B) B Z t ⊓
        conjSubgroup g (Vt M (LB M Q B) B Z t)))).ne'
    · simp at hk
      exact absurd hk.symm hne
    · omega
  have hi : 2 * Nat.card ↥Z ≤ Nat.card ↥(Vt M (LB M Q B) B Z t ⊓
      conjSubgroup g (Vt M (LB M Q B) B Z t)) := by
    rw [hk]
    nlinarith
  have hsi := card_sup_mul_card_inf_conj hc hZV hVQ hg
  have has : Nat.card ↥(( QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t) ≤
      Nat.card ↥(Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)) :=
    hAP.trans (Nat.card_mono (Set.toFinite _) hPle)
  have hA2 : Nat.card ↥(conjSubgroup x ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
      Vt M (LB M Q B) B Z t)) = Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔
        Vt M (LB M Q B) B Z t) := card_conjSubgroup x _
  rw [hsw] at hA2
  have hUt : Nat.card Q * Nat.card Z = Nat.card ↥(Q1 hc t) * Nat.card ↥(Ut Q Z t) := by
    haveI : (Z.subgroupOf (Ut Q Z t)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
        hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.Ut_le_Q (hc.LB_le_M ht) hv)))
    exact card_mul_card_of_isChiIso (hc.isChiIso_Q1_Ut ht) (fun x hx => hx.1)
      (le_sup_right : Z ≤ Ut Q Z t)
  rw [← hWQ1, ← hVU] at hUt
  have hq : 4 ≤ Nat.card ↥Z := hc.hyp.q4
  have hv := card_Vt_orthogonal hc hm2 hmt
  have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hs.toSec5.width
  rw [hQc] at hUt
  refine card_arith_vanish (Nat.card ↥Z) n m
    (Nat.card ↥((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t))
    (Nat.card ↥(Wt Q (Vt M (LB M Q B) B Z t)))
    (Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)))
    (Nat.card ↥(Vt M (LB M Q B) B Z t ⊔ conjSubgroup g (Vt M (LB M Q B) B Z t)))
    (Nat.card ↥(Vt M (LB M Q B) B Z t)) hq hv hUt.symm ?_ hi hsi has
  rw [hAA, hA2]

@[expose] def Step71VanishPairStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t →
    ∀ x : G, ConjMod M Q t x → ⁅x, t⁆ ∈ Q → (∃ v ∈ Vt M (LB M Q B) B Z t, ⁅x, v⁆ ∉ Z) →
    ∃ (h : G) (_ : h ∈ Rt M (LB M Q B) t) (r : G), r ∈ Rt M (LB M Q B) t ∧
      HypPlane Q Z (conjSubgroup h B) (conjSubgroup r (conjSubgroup h B)) t ∧
      conjSubgroup x (conjSubgroup h B) ⊔ Z = conjSubgroup r (conjSubgroup h B) ⊔ Z

theorem step71VanishBound_of_pair (hPair : Step71VanishPairStatement)
    (h52b : Stroth52bStatement) (h310chi : Stroth310ChiStatement) :
    Step71VanishBoundStatement := by
  intro G _ _ M Q Z B hc n t hs hno hex m hm2 hmt
  obtain ⟨x, hx, hxt, hmov⟩ := hex
  obtain ⟨h, hh, r, hrR, hplane, hpair⟩ := hPair G M Q Z B hc n t hs hno x hx hxt hmov
  have hhM : h ∈ M := hc.Rt_le_M t hh
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hsL : t ∈ LB M Q (conjSubgroup h B) := by
    rw [hc.LB_conj hhM, mem_conjSubgroup]
    have e : h⁻¹ * t * h = ⁅h⁻¹, t⁆ * t := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hq : ⁅h⁻¹, t⁆ ∈ Q := hc.Rt_comm_mem_Q ((Rt M (LB M Q B) t).inv_mem hh)
    exact (LB M Q B).mul_mem (Subgroup.mem_sup_left hq) ht
  have hs' : Sec7Hyp (hc.conj_of_mem hhM) n t :=
    sec7ctr_hyp_frame hc hs hhM hsL hs.toSec5.notQ rfl rfl
  have hV : Vt M (LB M Q (conjSubgroup h B)) (conjSubgroup h B) Z t =
      Vt M (LB M Q B) B Z t := by
    rw [hc.LB_conj hhM]
    exact sec7ctr_Vt_conj_frame hhM t
  have hmov' : ∃ v ∈ Vt M (LB M Q (conjSubgroup h B)) (conjSubgroup h B) Z t, ⁅x, v⁆ ∉ Z := by
    obtain ⟨v, hv, hxv⟩ := hmov
    exact ⟨v, by rw [hV]; exact hv, hxv⟩
  have hmt' : OmegaPlusNat (hc.conj_of_mem hhM) t m ∨ OmegaMinusNat (hc.conj_of_mem hhM) t m := by
    rcases hmt with h1 | h1
    · exact Or.inl ((sec7ctr_OmegaPlusNat_conj_frame hc hhM t m).mpr h1)
    · exact Or.inr ((sec7ctr_OmegaMinusNat_conj_frame hc hhM t m).mpr h1)
  have hrR' : r ∈ Rt M (LB M Q (conjSubgroup h B)) t := by
    rw [hc.LB_conj hhM, sec7ctr_Rt_conj_frame hhM t]
    exact hrR
  exact step71VanishBound_core h52b h310chi (hc.conj_of_mem hhM) hs' hrR' hplane hx
    hxt hmov' hpair hm2 hmt'

end CFSG.RankThree.GF2n.Stroth80
