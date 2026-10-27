module

public import CFSG.RankThree.PartOne.S12.Sec136
import CFSG.RankThree.PartOne.S12.Sec127
public import CFSG.RankThree.PartOne.S12.Sec136Inputs
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec138Trans

public section

namespace CFSG.RankThree.PartOne.DISTX

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

variable {G : Type} [Group G] [Finite G]

theorem pair_sym (hRefl : KF136Refl) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E ≠ A) (hrow : RowModel p L 10)
    (hG : Sec12TwoGeneric p c L E) (hcard : Nat.card E = p ^ 4)
    {u : MulAut E} (huΓ : u ∈ torusImage E L) (hu2 : u * u = 1)
    (hucomm : ∀ g ∈ torusImage E L, g * u = u * g)
    (hfix : autFixedInG E u = Subgroup.zpowers c) (hinv : ∀ b : E, (b : G) ∈ L → u b = b⁻¹)
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) (hwH : w ∉ cNormalizer c)
    (hcomm : (conjAut E w hw * u * (conjAut E w hw)⁻¹) * u =
      u * (conjAut E w hw * u * (conjAut E w hw)⁻¹)) :
    ∃ (z t : MulAut E),
      z ∈ reflectionSet p E ∧ t ∈ reflectionSet p E ∧ t ∈ torusImage E L ∧
      conjAut E w hw * z * (conjAut E w hw)⁻¹ = t ∧
      (∀ g ∈ torusImage E L, z * g = g * z) ∧ z * z = 1 ∧
      (∃ hc : c ∈ E, z ⟨c, hc⟩ = ⟨c, hc⟩⁻¹) ∧ (∀ b : E, (b : G) ∈ L → z b = b) := by
  classical
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => h.E_elem.is_comm.comm a b
  let _inst : CommGroup ↥E := commGroupOf hEc
  have hp := h.prime
  have hp2 : p ≠ 2 := by
    have := h.three_lt
    omega
  have hpow : ∀ x : ↥E, x ^ p = 1 := fun x =>
    Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h x.2)
  have R := h.restr_of_generic hG
  have hordc : orderOf (⟨c, hcE⟩ : ↥E) = p := by
    rw [← Subgroup.orderOf_coe]
    exact Sec12Three.orderOf_c h
  have hfixS : Invol.fixS u = Subgroup.zpowers (⟨c, hcE⟩ : ↥E) := by
    apply Subgroup.map_injective E.subtype_injective
    have h1 : (Invol.fixS u).map E.subtype = autFixedInG E u := rfl
    rw [h1, hfix, MonoidHom.map_zpowers]
    rfl
  have hUD : Invol.UData p (⟨c, hcE⟩ : ↥E) u := ⟨hp, hp2, hpow, hcard, hordc, hu2, hfixS⟩
  have hmoves : conjAut E w hw ⟨c, hcE⟩ ∉ Subgroup.zpowers (⟨c, hcE⟩ : ↥E) := by
    intro hmem
    apply hwH
    apply Sec127.mem_cNormalizer_of_conj_mem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have h1 := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow, Equivariance.coe_conjAut hw] at h1
    rw [← h1]
    exact Subgroup.zpow_mem_zpowers c k
  have hZ : Invol.ZPair p (⟨c, hcE⟩ : ↥E) u (conjAut E w hw) := ⟨hUD, hcomm, hmoves⟩
  have hBL : ∀ x : ↥E, x ∈ Invol.invS u ↔ (x : G) ∈ L := by
    intro x
    constructor
    · intro hx
      obtain ⟨f, hf, i, hfi⟩ := R.exists_mul_zpow x.2
      have hfL : f ∈ L := R.F_le_L hf
      have hfE : f ∈ E := R.F_le_E hf
      have hb₀ : (⟨f, hfE⟩ : ↥E) ∈ Invol.invS u := hinv ⟨f, hfE⟩ hfL
      have hx_eq : x = ⟨f, hfE⟩ * (⟨c, hcE⟩ : ↥E) ^ i := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_zpow]
        exact hfi
      have h1 : u x = x⁻¹ := hx
      rw [hx_eq, Invol.apply_mul_zpow, hUD.u_c, (hb₀ : u ⟨f, hfE⟩ = ⟨f, hfE⟩⁻¹), mul_inv,
        ← zpow_neg] at h1
      have h2 := hUD.eq_of_mul_zpow_eq ((Invol.invS u).inv_mem hb₀) ((Invol.invS u).inv_mem hb₀) h1
      have h3 := hUD.zpow_eq_one_of_eq_neg h2.2
      rw [hx_eq, h3, mul_one]
      exact hfL
    · intro hx
      exact hinv x hx
  obtain ⟨n, hn, hnu⟩ := Subgroup.mem_map.1 huΓ
  have hnL : (n : G) ∈ L := Subgroup.mem_subgroupOf.mp hn
  have hnN : (n : G) ∈ Subgroup.normalizer (E : Set G) := n.2
  have hnc : (n : G) * c * (n : G)⁻¹ = c := by
    rw [← Sec12Three.comm_c_L h (n : G) hnL, mul_inv_cancel_right]
  have hnH : (n : G) ∈ cNormalizer c :=
    Sec127.mem_cNormalizer_of_conj_mem (by rw [hnc]; exact Subgroup.mem_zpowers c)
  have hu_mem : u ∈ torusImage E (cNormalizer c) := by
    have := Sec138Trans.conjAut_mem_torusImage hnN hnH
    have heq : conjAut E (n : G) hnN = u := hnu
    rwa [heq] at this
  have hv_mem : Invol.vOf u (conjAut E w hw) ∈ torusImage E (cNormalizer c) := by
    have hxN : w * (n : G) * w⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      mul_mem (mul_mem hw hnN) (inv_mem hw)
    have hxeq : conjAut E (w * (n : G) * w⁻¹) hxN = Invol.vOf u (conjAut E w hw) := by
      show E.normalizerMonoidHom ⟨w * (n : G) * w⁻¹, hxN⟩ =
        conjAut E w hw * u * (conjAut E w hw)⁻¹
      have : (⟨w * (n : G) * w⁻¹, hxN⟩ : Subgroup.normalizer (E : Set G)) =
          ⟨w, hw⟩ * n * ⟨w, hw⟩⁻¹ := Subtype.ext rfl
      rw [this, map_mul, map_mul, map_inv, hnu]
      rfl
    have hxH : w * (n : G) * w⁻¹ ∈ cNormalizer c := by
      apply Sec127.mem_cNormalizer_of_conj_mem
      have h1 : ((conjAut E (w * (n : G) * w⁻¹) hxN ⟨c, hcE⟩ : ↥E) : G) =
          (w * (n : G) * w⁻¹) * c * (w * (n : G) * w⁻¹)⁻¹ := Equivariance.coe_conjAut hxN _
      rw [hxeq, hZ.v_c, Subgroup.coe_inv] at h1
      rw [← h1]
      exact (Subgroup.zpowers c).inv_mem (Subgroup.mem_zpowers c)
    have := Sec138Trans.conjAut_mem_torusImage hxN hxH
    rwa [hxeq] at this
  have hy_mem : Invol.yOf u (conjAut E w hw) ∈ torusImage E (cNormalizer c) :=
    mul_mem hv_mem hu_mem
  have hybar : Nat.card ↥(autFixedInG E (Invol.yOf u (conjAut E w hw)) ⊓ L) = p ^ 2 := by
    have h1 : autFixedInG E (Invol.yOf u (conjAut E w hw)) =
        (Invol.fixS (Invol.yOf u (conjAut E w hw))).map E.subtype := rfl
    have h2 : autFixedInG E (Invol.yOf u (conjAut E w hw)) ≤ L := by
      rw [h1]
      rintro _ ⟨x, hx, rfl⟩
      exact (hBL x).1 (hZ.fixS_y_le hx)
    rw [inf_eq_left.2 h2, h1, Subgroup.card_map_of_injective E.subtype_injective,
      hZ.card_fixS_y]
  obtain ⟨t, ht, htΓ, hty⟩ := hRefl G p A c L E h hF hF13 hT hEA hrow _ hy_mem hZ.y_sq
    ⟨hcE, hZ.y_c⟩ hybar
  have htc : t ⟨c, hcE⟩ = ⟨c, hcE⟩ := apply_c_of_mem_torusImage h hcE htΓ
  have ht2 : t * t = 1 := RefFacts.mul_self_eq_one ht.1
  have hty' : ∀ b ∈ Invol.invS u, t b = Invol.yOf u (conjAut E w hw) b := fun b hb =>
    (hty b ((hBL b).1 hb)).symm
  obtain ⟨z, hz⟩ : ∃ z : MulAut ↥E, z = Invol.yOf u (conjAut E w hw) * t := ⟨_, rfl⟩
  obtain ⟨hzc, hzb, hzsq, hzconj, hinvz⟩ := hZ.conj_eq ht2 htc hty' hz
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1] at hzc
    have h2 : (⟨c, hcE⟩ : ↥E) = (⟨c, hcE⟩ : ↥E)⁻¹ := hzc
    have h3 := hUD.eq_one_of_eq_inv h2
    exact h.c_ne_one (congrArg Subtype.val h3)
  have hzrefl : IsAutReflection p E z := by
    refine ⟨?_, ?_⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [pow_two]; exact hzsq) hz1
    · have h1 : autMoved E z = Invol.invS z := Invol.movedS_eq_invS hp hp2 hpow hzsq
      rw [h1, hinvz, Nat.card_zpowers, hordc]
  have hw' : w⁻¹ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer (E : Set G)).inv_mem hw
  have hzeq : z = conjAut E w⁻¹ hw' * t * (conjAut E w⁻¹ hw')⁻¹ := by
    rw [Equivariance.conjAut_inv hw, inv_inv]
    calc z = (conjAut E w hw)⁻¹ * (conjAut E w hw * z * (conjAut E w hw)⁻¹) * conjAut E w hw := by
          group
      _ = _ := by rw [hzconj]
  have hzD : z ∈ reflectionSet p E := by
    rw [hzeq]
    exact conj_mem_reflectionSet hp ht hw'
  refine ⟨z, t, hzD, ht, htΓ, hzconj, ?_, hzsq, ⟨hcE, hzc⟩, fun b hb => hzb b ((hBL b).2 hb)⟩
  intro g hg
  exact hUD.comm_of_fixes hzc hzb (apply_c_of_mem_torusImage h hcE hg) (hucomm g hg).symm

omit [Finite G] in
theorem pair_comm_inv {E : Subgroup G} (u a : MulAut E)
    (h : (a * u * a⁻¹) * u = u * (a * u * a⁻¹)) :
    (a⁻¹ * u * a⁻¹⁻¹) * u = u * (a⁻¹ * u * a⁻¹⁻¹) := by
  have h1 : Commute (a * u * a⁻¹) u := h
  have h2 := h1.map (MulAut.conj a⁻¹)
  simp only [MulAut.conj_apply, inv_inv] at h2
  have h3 : a⁻¹ * (a * u * a⁻¹) * a = u := by group
  rw [h3] at h2
  simpa only [inv_inv] using h2.symm.eq

omit [Finite G] in
theorem eq_of_inv_c_of_fix {c : G} {L E : Subgroup G}
    (R : Sec12Three.Restr c L E (E ⊓ L)) {hcE : c ∈ E} {z z' : MulAut E}
    (hz : z ⟨c, hcE⟩ = ⟨c, hcE⟩⁻¹) (hz' : z' ⟨c, hcE⟩ = ⟨c, hcE⟩⁻¹)
    (hF : ∀ b : E, (b : G) ∈ L → z b = b) (hF' : ∀ b : E, (b : G) ∈ L → z' b = b) : z = z' := by
  refine MulEquiv.ext fun e => ?_
  obtain ⟨f, hf, i, hfi⟩ := R.exists_mul_zpow e.2
  have he : e = (⟨f, hf.1⟩ : E) * (⟨c, hcE⟩ : E) ^ i := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hfi
  rw [he, map_mul, map_mul, map_zpow, map_zpow, hz, hz', hF _ hf.2, hF' _ hf.2]

theorem pair_both (hRefl : KF136Refl) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) (hEA : E ≠ A) (hrow : RowModel p L 10)
    (hG : Sec12TwoGeneric p c L E) (hcard : Nat.card E = p ^ 4)
    {u : MulAut E} (huΓ : u ∈ torusImage E L) (hu2 : u * u = 1)
    (hucomm : ∀ g ∈ torusImage E L, g * u = u * g)
    (hfix : autFixedInG E u = Subgroup.zpowers c) (hinv : ∀ b : E, (b : G) ∈ L → u b = b⁻¹)
    {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G)) (hwH : w ∉ cNormalizer c)
    (hcomm : (conjAut E w hw * u * (conjAut E w hw)⁻¹) * u =
      u * (conjAut E w hw * u * (conjAut E w hw)⁻¹)) :
    ∃ z : MulAut E, z ∈ reflectionSet p E ∧ (∃ hc : c ∈ E, z ⟨c, hc⟩ = ⟨c, hc⟩⁻¹) ∧
      (∀ g ∈ torusImage E L, z * g = g * z) ∧
      (conjAut E w hw * z * (conjAut E w hw)⁻¹ ∈ reflectionSet p E ∧
        conjAut E w hw * z * (conjAut E w hw)⁻¹ ∈ torusImage E L) ∧
      ((conjAut E w hw)⁻¹ * z * conjAut E w hw ∈ reflectionSet p E ∧
        (conjAut E w hw)⁻¹ * z * conjAut E w hw ∈ torusImage E L) := by
  have hw' : w⁻¹ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer (E : Set G)).inv_mem hw
  have hwH' : w⁻¹ ∉ cNormalizer c := fun hin => hwH (by simpa using (cNormalizer c).inv_mem hin)
  have hinvA : conjAut E w⁻¹ hw' = (conjAut E w hw)⁻¹ := Equivariance.conjAut_inv hw
  have hcomm' : (conjAut E w⁻¹ hw' * u * (conjAut E w⁻¹ hw')⁻¹) * u =
      u * (conjAut E w⁻¹ hw' * u * (conjAut E w⁻¹ hw')⁻¹) := by
    rw [hinvA]
    exact pair_comm_inv u _ hcomm
  obtain ⟨z, t, hzD, htD, htΓ, hzt, hzL, -, ⟨hcE, hzc⟩, hzB⟩ :=
    pair_sym hRefl h hF hF13 hT hEA hrow hG hcard huΓ hu2 hucomm hfix hinv hw hwH hcomm
  obtain ⟨z', t', hzD', htD', htΓ', hzt', -, -, ⟨hcE', hzc'⟩, hzB'⟩ :=
    pair_sym hRefl h hF hF13 hT hEA hrow hG hcard huΓ hu2 hucomm hfix hinv hw' hwH' hcomm'
  have R := h.restr_of_generic hG
  have hzz : z' = z := eq_of_inv_c_of_fix R hzc' hzc hzB' hzB
  subst hzz
  rw [hinvA] at hzt'
  exact ⟨z', hzD', ⟨hcE', hzc'⟩, hzL, ⟨hzt ▸ htD, hzt ▸ htΓ⟩, ⟨hzt' ▸ htD', hzt' ▸ htΓ'⟩⟩

end CFSG.RankThree.PartOne.DISTX
