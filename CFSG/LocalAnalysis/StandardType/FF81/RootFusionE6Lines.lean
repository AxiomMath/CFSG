module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.GroupTheory.IndexThreeCosets

public section

namespace CFSG.StandardType.FF81

open CFSG.StandardType.FrameRoute.FS81 (IsConjLine)

private theorem eq_one_of_pow_mem_of_hypA {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} (hA : HypA G n b L) {z : Fin 3 → ↥L} (hz : AfterProp2 b L z) {k : ℕ}
    (hk : b ^ k ∈ L) : b ^ k = 1 := by
  have hx : ∀ y : ↥L, (⟨b ^ k, hk⟩ : ↥L) * y = y * ⟨b ^ k, hk⟩ := by
    intro y
    apply Subtype.ext
    show b ^ k * (y : G) = (y : G) * b ^ k
    have hy : Commute (y : G) b := Subgroup.mem_centralizer_singleton_iff.mp (hA.le y.2)
    exact (hy.pow_right k).symm
  have h1 : (⟨b ^ k, hk⟩ : ↥L) = 1 := hz.model.eq_one_of_forall_comm hx
  exact congrArg Subtype.val h1

private theorem wt_eq_one_of_zpowers_vecElt_eq {H : Type} [Group H] {z : Fin 3 → H}
    (hp : ∀ i, z i ^ 3 = 1) (hc : ∀ i j, z i * z j = z j * z i)
    (hi : ∀ v, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v = 1 → v = 0)
    {v : Fin 3 → ZMod 3} {j : Fin 3}
    (hZ : Subgroup.zpowers (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v) = Subgroup.zpowers (z j)) : GGFF.wt v = 1 := by
  have hzj1 : z j ≠ 1 := by
    intro h1
    have h0 : Pi.single j 1 = 0 := hi _ (by
      rw [CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one, h1])
    have := congrFun h0 j
    simp at this
  have hw1 : CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v ≠ 1 := by
    intro h1
    have hbot : Subgroup.zpowers (z j) = ⊥ := by
      rw [← hZ, h1, Subgroup.zpowers_one_eq_bot]
    exact hzj1 (Subgroup.zpowers_eq_bot.mp hbot)
  have hmem : CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v ∈ Subgroup.zpowers (z j) := by
    rw [← hZ]
    exact Subgroup.mem_zpowers _
  have hwt1 : ∀ j : Fin 3, GGFF.wt (Pi.single j 1) = 1 := by decide
  have hwt2 : ∀ j : Fin 3, GGFF.wt (Pi.single j (2 : ZMod 3)) = 1 := by decide
  have hord : orderOf (z j) = 3 := orderOf_eq_prime (hp j) hzj1
  rcases CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hord hmem hw1 with
    h | h
  · have hv : v = Pi.single j 1 := (GGFF.vecElt_injective hp hc hi) (by
      rw [h, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single_one])
    rw [hv]
    exact hwt1 j
  · have hz2 : (z j)⁻¹ = z j ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ']
      exact hp j
    have h2 : v = Pi.single j (2 : ZMod 3) := (GGFF.vecElt_injective hp hc hi) (by
      rw [h, hz2, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt_single]
      rw [show (2 : ZMod 3).val = 2 from rfl])
    rw [h2]
    exact hwt2 j

private theorem exists_wt_one_of_isConjLine {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} (hA : HypA G n b L) {z : Fin 3 → ↥L} (hz : AfterProp2 b L z) {l : G}
    (hl : l ∈ L) (hl3 : orderOf l = 3) (hlb : IsConjLine b (Subgroup.zpowers l)) :
    ∃ (v : Fin 3 → ZMod 3) (g : ↥L), GGFF.wt v = 1 ∧
      (⟨l, hl⟩ : ↥L) = g * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v * g⁻¹ := by
  have hl_ne : l ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hl3
    omega
  have hlL_ne : (⟨l, hl⟩ : ↥L) ≠ 1 := fun h1 => hl_ne (congrArg Subtype.val h1)
  have hlL3 : (⟨l, hl⟩ : ↥L) ^ 3 = 1 := by
    apply Subtype.ext
    show l ^ 3 = 1
    rw [← hl3]
    exact pow_orderOf_eq_one l
  obtain ⟨g, v, hgv⟩ := hz.model.fus ⟨l, hl⟩ hlL3
  have hv : v ≠ 0 := by
    intro hv0
    apply hlL_ne
    rw [hgv, hv0, GGFF.vecElt_zero z]
    simp
  let w : ↥L := CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v
  have hwG : (w : G) = CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v := (GGFF.SettingCore.vecElt_zs z v).symm
  have hw3 : w ^ 3 = 1 := by
    change CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v ^ 3 = 1
    have hv3 : v + v + v = 0 := by
      ext i
      have h : ∀ x : ZMod 3, x + x + x = 0 := by decide
      exact h (v i)
    calc CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v ^ 3 = CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v ^ 2 * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v := by
          rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ]
      _ = (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v) * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v := by rw [pow_two]
      _ = CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z (v + v) * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v := by
          rw [GGFF.Model.vecElt_mul hz.model]
      _ = CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z (v + v + v) := by rw [GGFF.Model.vecElt_mul hz.model]
      _ = 1 := by rw [hv3, GGFF.vecElt_zero z]
  have hw_ne : w ≠ 1 := by
    intro h1
    exact hv (hz.model.inj v (by simpa [w] using h1))
  have hword : orderOf w = 3 := orderOf_eq_prime hw3 hw_ne
  have hwordG : orderOf (w : G) = 3 := by
    rw [Subgroup.orderOf_coe, hword]
  let Z : Subgroup G := Subgroup.zpowers (w : G)
  have hZdef : Z = Subgroup.zpowers (w : G) := rfl
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Nat.card_zpowers, hwordG]
  have hZle : Z ≤ GGFF.Bt b z := by
    rw [hZdef, Subgroup.zpowers_le]
    rw [hwG]
    exact GGFF.SettingCore.tor_le_Bt b z (GGFF.vecElt_mem_tor _ v)
  have hgvG : l = (g : G) * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v * (g : G)⁻¹ := by
    have h := congrArg Subtype.val hgv
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rwa [← GGFF.SettingCore.vecElt_zs] at h
  have hw_eq : (w : G) = (g : G)⁻¹ * l * (g : G) := by
    rw [hwG, hgvG]
    group
  have hZconj : IsConjLine b Z := by
    obtain ⟨g0, hg0⟩ := hlb
    refine ⟨(g : G)⁻¹ * g0, ?_⟩
    rw [show (g : G)⁻¹ * g0 * b * ((g : G)⁻¹ * g0)⁻¹ =
      (g : G)⁻¹ * (g0 * b * g0⁻¹) * (g : G) by group]
    rw [hZdef, hw_eq]
    simpa [MonoidHom.map_zpowers, MulAut.conj_apply] using
      congrArg (Subgroup.map (MulAut.conj (g : G)⁻¹).toMonoidHom) hg0
  have hZmem : Z ∈ coordLines b z ∨ Z ∈ weightFourLines b z := by
    have hout : PropTwoOut b L z := hz.out
    unfold PropTwoOut at hout
    rcases hout with ⟨-, hCL⟩ | ⟨-, -, hCL, -⟩
    · exact Or.inl ((hCL Z hZle hZcard).mp hZconj)
    · rcases (hCL Z hZle hZcard).mp hZconj with h | h
      · exact Or.inl h
      · exact Or.inr h
  have hzs_pow : ∀ i, GGFF.zs z i ^ 3 = 1 := fun i => by
    simpa [GGFF.zs] using congrArg Subtype.val (hz.model.pow_z i)
  have hzs_comm : ∀ i j, GGFF.zs z i * GGFF.zs z j = GGFF.zs z j * GGFF.zs z i := fun i j => by
    simpa [GGFF.zs] using congrArg Subtype.val (hz.model.comm_z i j)
  have hzs_inj : ∀ v, CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v = 1 → v = 0 := by
    intro v hv1
    apply hz.model.inj v
    apply Subtype.ext
    rw [← GGFF.SettingCore.vecElt_zs]
    exact hv1
  have hord : orderOf b = 3 := hA.ord
  have hb_ne : b ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    omega
  have hb_not_mem : b ∉ L := by
    intro hb
    have h1 : b ^ 1 ∈ L := by simpa using hb
    have h2 : b ^ 1 = 1 := eq_one_of_pow_mem_of_hypA hA hz h1
    exact hb_ne (by simpa using h2)
  have hwt : GGFF.wt v = 1 := by
    rcases hZmem with ⟨i, hiZ⟩ | ⟨ε, u, hε, hu, hZw⟩
    · have hZeqW : Subgroup.zpowers (w : G) = Subgroup.zpowers (xs b z i) := by
        rw [← hZdef]
        exact hiZ
      have hZeq : Subgroup.zpowers (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v) =
          Subgroup.zpowers (xs b z i) := by
        rw [← hwG]
        exact hZeqW
      have hw1 : CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v ≠ 1 := by
        intro h1
        apply hw_ne
        apply Subtype.ext
        rw [Subgroup.coe_one, hwG, h1]
      have hi_ne : i ≠ 0 := by
        intro hi0
        apply hb_not_mem
        have hZb : Subgroup.zpowers (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v) = Subgroup.zpowers b := by
          simpa [xs, hi0] using hZeq
        have hmem : CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v ∈ Subgroup.zpowers b := by
          rw [← hZb]
          exact Subgroup.mem_zpowers _
        rcases CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three hA.ord hmem
          hw1 with h | h
        · have hbL : b ∈ L := by
            rw [← h, ← hwG]
            exact w.2
          exact hbL
        · have hbL : b ∈ L := by
            have hbw : b = (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v)⁻¹ := by rw [h]; group
            rw [hbw, ← hwG]
            exact L.inv_mem w.2
          exact hbL
      fin_cases i
      · exact absurd rfl hi_ne
      · exact wt_eq_one_of_zpowers_vecElt_eq hzs_pow hzs_comm hzs_inj (by simpa [xs] using hZeq)
      · exact wt_eq_one_of_zpowers_vecElt_eq hzs_pow hzs_comm hzs_inj (by simpa [xs] using hZeq)
      · exact wt_eq_one_of_zpowers_vecElt_eq hzs_pow hzs_comm hzs_inj (by simpa [xs] using hZeq)
    · have hZeqW : Subgroup.zpowers (w : G) =
          Subgroup.zpowers (b ^ ε.val * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) u) := by
        rw [← hZdef]
        exact hZw
      have hZeq : Subgroup.zpowers (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v) =
          Subgroup.zpowers (b ^ ε.val * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) u) := by
        rw [← hwG]
        exact hZeqW
      have hy_mem : b ^ ε.val * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) u ∈ Z := by
        rw [hZdef, hZeqW]
        exact Subgroup.mem_zpowers _
      have hu_mem : CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) u ∈ L := by
        simpa only [GGFF.SettingCore.vecElt_zs] using (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z u).2
      have hbeps_mem : b ^ ε.val ∈ L := by
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy_mem
        have heq : b ^ ε.val =
            (w : G) ^ m * (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) u)⁻¹ := by
          rw [hm]
          group
        rw [heq]
        exact L.mul_mem (L.zpow_mem w.2 m) (L.inv_mem hu_mem)
      have hbeps_ne : b ^ ε.val ≠ 1 := by
        have hlt := ZMod.val_lt ε
        have hne : ε.val ≠ 0 := fun h0 => hε ((ZMod.val_eq_zero ε).mp h0)
        have hcases : ε.val = 1 ∨ ε.val = 2 := by omega
        rcases hcases with h | h
        · rw [h]
          simpa using hb_ne
        · rw [h]
          intro h1
          have hdvd : orderOf b ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
          rw [hord] at hdvd
          norm_num at hdvd
      exact absurd (eq_one_of_pow_mem_of_hypA hA hz hbeps_mem) hbeps_ne
  exact ⟨v, g, hwt, hgv⟩

theorem exists_conj_eq_of_isConjLine {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} (hA : HypA G n b L) {z : Fin 3 → ↥L} (hz : AfterProp2 b L z) {l l' : G}
    (hl : l ∈ L) (hl' : l' ∈ L) (hl3 : orderOf l = 3) (hl'3 : orderOf l' = 3)
    (hlb : IsConjLine b (Subgroup.zpowers l)) (hl'b : IsConjLine b (Subgroup.zpowers l')) :
    ∃ c ∈ L, c * l * c⁻¹ = l' := by
  obtain ⟨v, g, hv, hgv⟩ := exists_wt_one_of_isConjLine hA hz hl hl3 hlb
  obtain ⟨v', g', hv', hg'v⟩ := exists_wt_one_of_isConjLine hA hz hl' hl'3 hl'b
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0] at hv
    have hwt0 : GGFF.wt (0 : Fin 3 → ZMod 3) = 0 := by decide
    rw [hwt0] at hv
    exact zero_ne_one hv
  have hv0' : v' ≠ 0 := by
    intro h0
    rw [h0] at hv'
    have hwt0 : GGFF.wt (0 : Fin 3 → ZMod 3) = 0 := by decide
    rw [hwt0] at hv'
    exact zero_ne_one hv'
  have hconj : IsConj (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v) (CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt z v') :=
    (hz.model.conj_iff v v' hv0 hv0').mpr (by rw [hv, hv'])
  obtain ⟨d, hd⟩ := isConj_iff.mp hconj
  have hgvG : l = (g : G) * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v * (g : G)⁻¹ := by
    have h := congrArg Subtype.val hgv
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rwa [← GGFF.SettingCore.vecElt_zs] at h
  have hg'vG : l' = (g' : G) * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v' * (g' : G)⁻¹ := by
    have h := congrArg Subtype.val hg'v
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rwa [← GGFF.SettingCore.vecElt_zs] at h
  have hdG : (d : G) * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v * (d : G)⁻¹ =
      CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v' := by
    have h := congrArg Subtype.val hd
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h
    rwa [← GGFF.SettingCore.vecElt_zs] at h
  refine ⟨(g' : G) * (d : G) * (g : G)⁻¹, ?_, ?_⟩
  · exact L.mul_mem (L.mul_mem g'.2 d.2) (L.inv_mem g.2)
  · calc
      ((g' : G) * (d : G) * (g : G)⁻¹) * l * ((g' : G) * (d : G) * (g : G)⁻¹)⁻¹
          = (g' : G) * ((d : G) * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v * (d : G)⁻¹) *
              (g' : G)⁻¹ := by
            rw [hgvG]
            group
      _ = (g' : G) * CFSG.RankThree.PartTwo.Sec4.Item434Kit.vecElt (GGFF.zs z) v' * (g' : G)⁻¹ := by rw [hdG]
      _ = l' := hg'vG.symm

end CFSG.StandardType.FF81
