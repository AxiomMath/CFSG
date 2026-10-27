module

public import CFSG.RankThree.PartOne.F106.NoQD32NADegWts
public import CFSG.RankThree.PartOne.Q1327T.R8Weights

public section

namespace CFSG.RankThree.PartOne.F106.NAD

open Matrix Module Subgroup CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.Q1327T.R8
open scoped commutatorElement

section Index

theorem exists_mem_ker_not_mem_center {G μ : Type*} [Group G] [Group μ] [Finite μ] {q : ℕ}
    (hq : 2 ≤ q) (hμ : Nat.card μ ≤ q) (f g : G →* μ)
    (h4 : q ^ 4 ≤ (Subgroup.center G).index) :
    ∃ y : G, y ∈ f.ker ∧ y ∈ g.ker ∧ y ∉ Subgroup.center G := by
  by_contra H
  push Not at H
  have hle : f.ker ⊓ g.ker ≤ Subgroup.center G := fun y hy => H y hy.1 hy.2
  have hker : ∀ f : G →* μ, f.ker.index ≠ 0 ∧ f.ker.index ≤ q := by
    intro f
    rw [Subgroup.index_ker]
    have : Finite ↥f.range := Subtype.finite
    exact ⟨Nat.card_pos.ne', (Nat.card_le_card_of_injective _ Subtype.val_injective).trans hμ⟩
  have h1 := Subgroup.index_dvd_of_le hle
  have h2 : (f.ker ⊓ g.ker).index ≤ q * q :=
    Subgroup.index_inf_le.trans (Nat.mul_le_mul (hker f).2 (hker g).2)
  have h3 := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Subgroup.index_inf_ne_zero (hker f).1 (hker g).1)) h1
  have h5 : q ^ 2 < q ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have h6 : q * q = q ^ 2 := (sq q).symm
  omega

end Index

section Pair

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (L : Type) [Field L]
  [Algebra K L] {q N : ℕ} {Y : Subgroup (GL ι K)}

theorem hcommF (e e' : Fz Y) : (e : GL ι K) * e' = e' * e :=
  mul_comm_of_mem_Fz e'.2 (Fz_le Y e.2)

theorem finrank_joint_le (w : Wts L (Fz Y)) :
    finrank L ↥(joint L (Fz Y) w.1) ≤ Fintype.card ι := by
  have := Submodule.finrank_le (joint L (Fz Y) w.1)
  rwa [Module.finrank_fintype_fun_eq_card] at this

structure ClassTwo (q N : ℕ) (Y : Subgroup (GL ι K)) : Prop where
  prime : q.Prime
  expF : ∀ e ∈ Fz Y, e ^ N = 1
  commq : ∀ a ∈ Y, ∀ b ∈ Y, ⁅a, b⁆ ^ q = 1
  cl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1

namespace ClassTwo

variable {L} (h : ClassTwo q N Y)

include h

theorem hexpF : ∀ e : Fz Y, (e : GL ι K) ^ N = 1 := fun e => h.expF e e.2

theorem comm_mul_left {x y a : GL ι K} (hx : x ∈ Y) (hy : y ∈ Y) (ha : a ∈ Y) :
    ⁅x * y, a⁆ = ⁅x, a⁆ * ⁅y, a⁆ := by
  have e1 : ⁅x * y, a⁆ = x * ⁅y, a⁆ * x⁻¹ * ⁅x, a⁆ := by
    simp only [commutatorElement_def]
    group
  have e2 : x * ⁅y, a⁆ * x⁻¹ = ⁅y, a⁆ := by
    rw [mul_comm_of_mem_Fz (comm_mem_Fz h.cl hy ha) hx]
    group
  have e3 : ⁅x, a⁆ * ⁅y, a⁆ = ⁅y, a⁆ * ⁅x, a⁆ :=
    mul_comm_of_mem_Fz (comm_mem_Fz h.cl hy ha) (Fz_le Y (comm_mem_Fz h.cl hx ha))
  rw [e1, e2, e3]

@[expose] noncomputable def pairHom (L : Type) [Field L] [Algebra K L] (w : Wts L (Fz Y))
    {a : GL ι K} (ha : a ∈ Y) : ↥Y →* rootsOfUnity q L :=
  MonoidHom.mk' (fun y => ⟨wtUnits L (Fz Y) w.2 ⟨⁅(y : GL ι K), a⁆, comm_mem_Fz h.cl y.2 ha⟩, by
      rw [mem_rootsOfUnity]
      exact Units.ext (by
        rw [Units.val_pow_eq_pow_val, wtUnits_apply]
        exact weight_pow_eq_one_elem L w.2 _ (h.commq _ y.2 _ ha))⟩)
    fun x y => by
      apply Subtype.ext
      change wtUnits L (Fz Y) w.2 ⟨⁅((x * y : ↥Y) : GL ι K), a⁆, _⟩ =
        wtUnits L (Fz Y) w.2 ⟨⁅(x : GL ι K), a⁆, _⟩ * wtUnits L (Fz Y) w.2 ⟨⁅(y : GL ι K), a⁆, _⟩
      rw [← map_mul]
      congr 1
      exact Subtype.ext (h.comm_mul_left x.2 y.2 ha)

theorem pairHom_eq_one_iff (w : Wts L (Fz Y)) {a : GL ι K} (ha : a ∈ Y) (y : ↥Y) :
    pairHom h L w ha y = 1 ↔ wv w.1 ⁅(y : GL ι K), a⁆ = 1 := by
  rw [wv_of_mem w.1 (comm_mem_Fz h.cl y.2 ha)]
  constructor
  · intro h1
    have := congrArg (fun z : rootsOfUnity q L => ((z : Lˣ) : L)) h1
    simpa [pairHom, wtUnits_apply] using this
  · intro h1
    apply Subtype.ext
    apply Units.ext
    simpa [pairHom, wtUnits_apply] using h1

theorem exists_orth (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) (w : Wts L (Fz Y))
    {a b : GL ι K} (ha : a ∈ Y) (hb : b ∈ Y) :
    ∃ c ∈ Y, c ∉ Fz Y ∧ wv w.1 ⁅c, a⁆ = 1 ∧ wv w.1 ⁅c, b⁆ = 1 := by
  have : NeZero q := ⟨h.prime.ne_zero⟩
  obtain ⟨y, hyf, hyg, hyc⟩ := exists_mem_ker_not_mem_center h.prime.two_le
    (card_rootsOfUnity L q) (pairHom h L w ha) (pairHom h L w hb) (by rwa [Subgroup.index_eq_card])
  refine ⟨(y : GL ι K), y.2, ?_, (pairHom_eq_one_iff h w ha y).1 hyf,
    (pairHom_eq_one_iff h w hb y).1 hyg⟩
  intro hF
  apply hyc
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (mul_comm_of_mem_Fz hF g.2)

theorem exists_noncomm (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) :
    ∃ a b : GL ι K, a ∈ Y ∧ b ∈ Y ∧ ⁅a, b⁆ ≠ 1 := by
  by_contra H
  push Not at H
  have hc : Subgroup.center ↥Y = ⊤ := by
    refine eq_top_iff.2 fun z _ => Subgroup.mem_center_iff.2 fun g => ?_
    exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.1 (H g z g.2 z.2))
  rw [hc, ← Subgroup.index_eq_card, Subgroup.index_top] at h4
  have := Nat.one_lt_pow (by norm_num : (4 : ℕ) ≠ 0) h.prime.one_lt
  omega

theorem comm_eq_one_of_forall [IsAlgClosed L] (hpL : (N : L) ≠ 0) {a b : GL ι K} (ha : a ∈ Y)
    (hb : b ∈ Y) (hall : ∀ w : Wts L (Fz Y), wv w.1 ⁅a, b⁆ = 1) : ⁅a, b⁆ = 1 := by
  have hab := comm_mem_Fz h.cl ha hb
  have := eq_of_forall_weight_eq L (Fz Y) hpL h.hexpF hcommF (a := ⟨⁅a, b⁆, hab⟩) (b := 1)
    fun χ hχ => by
      have h1 := hall ⟨χ, hχ⟩
      rw [wv_of_mem χ hab] at h1
      rw [h1, weight_one L (Fz Y) hχ]
  exact congrArg Subtype.val this

theorem exists_sig [IsAlgClosed L] (hpL : (N : L) ≠ 0) {a b : GL ι K} (ha : a ∈ Y) (hb : b ∈ Y)
    (hne : ⁅a, b⁆ ≠ 1) : ∃ w : Wts L (Fz Y), wv w.1 ⁅a, b⁆ ≠ 1 := by
  by_contra H
  push Not at H
  exact hne (h.comm_eq_one_of_forall hpL ha hb H)

theorem mul_card_le [IsAlgClosed L] (hpL : (N : L) ≠ 0) (s : Finset (Wts L (Fz Y)))
    (hs : ∀ w ∈ s, q ≤ finrank L ↥(joint L (Fz Y) w.1)) : q * s.card ≤ Fintype.card ι := by
  classical
  have hind : iSupIndep fun w : Wts L (Fz Y) => joint L (Fz Y) w.1 :=
    (iSupIndep_joint L (Fz Y) hcommF hpL h.hexpF).comp Subtype.val_injective
  have h1 := sum_finrank_le (L := L) (M := ι → L) (fun w : Wts L (Fz Y) => joint L (Fz Y) w.1)
    hind s
  rw [Module.finrank_fintype_fun_eq_card] at h1
  have h2 : s.card • q ≤ ∑ w ∈ s, finrank L ↥(joint L (Fz Y) w.1) :=
    Finset.card_nsmul_le_sum s _ q hs
  rw [smul_eq_mul, mul_comm] at h2
  exact h2.trans h1

theorem sq_le_finrank [IsAlgClosed L] (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y))
    {w : Wts L (Fz Y)} {a b : GL ι K} (ha : a ∈ Y) (hb : b ∈ Y) (hne : wv w.1 ⁅a, b⁆ ≠ 1)
    (hnd : ∀ y ∈ Y, (∀ y' ∈ Y, wv w.1 ⁅y, y'⁆ = 1) → y ∈ Fz Y) :
    q ^ 2 ≤ finrank L ↥(joint L (Fz Y) w.1) := by
  obtain ⟨c, hcY, hcF, hca, hcb⟩ := h.exists_orth h4 w ha hb
  have : ∃ y' ∈ Y, wv w.1 ⁅c, y'⁆ ≠ 1 := by
    by_contra H
    push Not at H
    exact hcF (hnd c hcY H)
  obtain ⟨y', hy', hy'ne⟩ := this
  exact sq_le_finrank_joint L h.prime h.commq h.cl w.2 hcY hy' ha hb hy'ne hne hca hcb

end ClassTwo

end Pair

end CFSG.RankThree.PartOne.F106.NAD

namespace CFSG.RankThree.PartOne.F106

open Matrix Module CFSG.RankThree.PartOne.N143X CFSG.RankThree.PartOne.Q1327T.R8
  CFSG.RankThree.PartOne.F106.NAD
open scoped commutatorElement

theorem na_deg_of_classTwo {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {q N : ℕ}
    {Y : Subgroup (GL ι K)} (hC : ClassTwo q N Y) (hNK : (N : K) ≠ 0)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : 2 * q ≤ Fintype.card ι := by
  classical
  have hq := hC.prime
  let L := AlgebraicClosure K
  have hpL : (N : L) ≠ 0 := by
    intro h0
    apply hNK
    apply (algebraMap K L).injective
    rw [map_natCast, map_zero]
    exact h0
  obtain ⟨a, b, ha, hb, hab⟩ := hC.exists_noncomm h4
  obtain ⟨w₀, hw₀⟩ := hC.exists_sig hpL ha hb hab
  have hd₀ : q ≤ finrank L ↥(joint L (Fz Y) w₀.1) :=
    q_le_finrank_joint L hq hC.commq hC.cl w₀.2 ha hb hw₀
  by_cases hex : ∃ w₁ : Wts L (Fz Y), w₁ ≠ w₀ ∧ ∃ a' ∈ Y, ∃ b' ∈ Y, wv w₁.1 ⁅a', b'⁆ ≠ 1
  · obtain ⟨w₁, hne, a', ha', b', hb', h'⟩ := hex
    have hd₁ : q ≤ finrank L ↥(joint L (Fz Y) w₁.1) :=
      q_le_finrank_joint L hq hC.commq hC.cl w₁.2 ha' hb' h'
    have := hC.mul_card_le hpL ({w₀, w₁} : Finset (Wts L (Fz Y))) (by
      intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hd₀
      · rw [Finset.mem_singleton.1 hw]
        exact hd₁)
    rw [Finset.card_pair hne.symm] at this
    omega
  · push Not at hex
    have hnd : ∀ y ∈ Y, (∀ y' ∈ Y, wv w₀.1 ⁅y, y'⁆ = 1) → y ∈ Fz Y := by
      intro y hy hy'
      refine mem_Fz.2 ⟨hy, fun g hg => ?_⟩
      have h1 : ⁅y, g⁆ = 1 := hC.comm_eq_one_of_forall hpL hy hg fun w => by
        by_cases hw : w = w₀
        · rw [hw]
          exact hy' g hg
        · exact hex w hw y hy g hg
      exact (commutatorElement_eq_one_iff_mul_comm.1 h1).symm
    have h2 := hC.sq_le_finrank h4 ha hb hw₀ hnd
    have h3 := finrank_joint_le L w₀
    have h5 : 2 * q ≤ q ^ 2 := by nlinarith [hq.two_le]
    omega

theorem na_deg {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {q : ℕ}
    (hq : q.Prime) (_hq2 : q ≠ 2) (hqK : (q : K) ≠ 0) (Y : Subgroup (GL ι K))
    (hexp : ∀ y ∈ Y, y ^ q = 1) (hcl : ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ⁅⁅a, b⁆, c⁆ = 1)
    (h4 : q ^ 4 ≤ Nat.card (↥Y ⧸ Subgroup.center ↥Y)) : 2 * q ≤ Fintype.card ι :=
  na_deg_of_classTwo ⟨hq, fun e he => hexp e (Fz_le Y he),
    fun _ ha _ hb => hexp _ (Fz_le Y (comm_mem_Fz hcl ha hb)), hcl⟩ hqK h4

end CFSG.RankThree.PartOne.F106
