module

public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers
public import CFSG.Open.FusionDefs

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiModel

open CFSG.Blueprint CFSG.LieType.Ree
open scoped LinearAlgebra.Projectivization

variable {a : ℕ} {K : Type} [Field K]

@[expose] def suzukiDHom
    (a : ℕ) (K : Type) [Field K] : Kˣ →* suzukiGroup a K where
  toFun := suzukiDElt a K
  map_one' := suzukiDElt_one
  map_mul' l m := (suzukiDElt_mul l m).symm

theorem suzukiDHom_apply
    (l : Kˣ) : suzukiDHom a K l = suzukiDElt a K l :=
  rfl

theorem range_suzukiDHom : (suzukiDHom a K).range = suzukiT a K :=
  SetLike.coe_injective (by rw [MonoidHom.coe_range, coe_suzukiT]; rfl)

theorem isCyclic_suzukiT [Finite K] : IsCyclic (suzukiT a K) := by
  rw [← range_suzukiDHom]
  exact isCyclic_of_surjective _ (MonoidHom.rangeRestrict_surjective _)

variable [Finite K]

theorem suzukiSElt_smul_suzukiLine_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (u v : K) :
    suzukiSElt a K u v • suzukiLine a K 0 0 = suzukiLine a K u v := by
  rw [suzukiSElt_smul_suzukiLine hK, add_zero, add_zero, mul_zero, add_zero]

theorem suzukiDElt_smul_suzukiLine_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (l : Kˣ) :
    suzukiDElt a K l • suzukiLine a K 0 0 = suzukiLine a K 0 0 := by
  rw [(suzuki_ovoid_torus_action a hK l 0 0).2, mul_zero, mul_zero]

theorem suzukiT_le_stabilizer_suzukiLine
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiT a K ≤ MulAction.stabilizer (suzukiGroup a K) (suzukiLine a K 0 0) :=
  (Subgroup.closure_le _).2 (by
    rintro _ ⟨l, rfl⟩
    exact suzukiDElt_smul_suzukiLine_zero hK l)

theorem suzuki_two_point_stabilizer
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) ⊓
      MulAction.stabilizer (suzukiGroup a K) (suzukiLine a K 0 0) = suzukiT a K := by
  have hB := (suzuki_ovoid_stabilizer hK).1
  refine le_antisymm (fun g hg => ?_)
    (le_inf ((suzukiT_le_suzukiB a K).trans hB.ge) (suzukiT_le_stabilizer_suzukiLine hK))
  obtain ⟨hα, hβ⟩ := Subgroup.mem_inf.1 hg
  rw [hB] at hα
  obtain ⟨u, v, l, rfl⟩ := (mem_suzukiB_iff hK).1 hα
  rw [MulAction.mem_stabilizer_iff, mul_smul, suzukiDElt_smul_suzukiLine_zero hK,
    suzukiSElt_smul_suzukiLine_zero hK, suzukiLine_eq_iff] at hβ
  obtain ⟨rfl, rfl⟩ := hβ
  rw [suzukiSElt_zero_zero hK, one_mul]
  exact suzukiDElt_mem_suzukiT a K l

theorem index_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (suzukiU a K).index = (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have h := (suzukiU a K).index_mul_card
  rw [suzuki_order hK, (suzuki_unipotent_structure hK).2.1] at h
  refine Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (2 ^ (2 * a + 1)) ^ 2) ?_
  rw [h]
  ring

theorem odd_two_pow_sub_one (n : ℕ) (hn : n ≠ 0) : Odd (2 ^ n - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, hn⟩) odd_one

theorem exists_sylow_eq_suzukiU (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ P : Sylow 2 (suzukiGroup a K), (P : Subgroup (suzukiGroup a K)) = suzukiU a K := by
  have hp : IsPGroup 2 (suzukiU a K) := IsPGroup.of_card (n := 2 * (2 * a + 1)) (by
    rw [(suzuki_unipotent_structure hK).2.1]
    ring)
  have hidx : ¬2 ∣ (suzukiU a K).index := by
    rw [index_suzukiU hK, Nat.Prime.dvd_mul Nat.prime_two, not_or, ← even_iff_two_dvd,
      ← even_iff_two_dvd, Nat.not_even_iff_odd, Nat.not_even_iff_odd]
    exact ⟨odd_two_pow_sub_one _ (by omega),
      (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, two_ne_zero⟩).add_one⟩
  exact ⟨hp.toSylow hidx, IsPGroup.toSylow_coe hp hidx⟩

theorem suzukiSElt_zero_mul_self
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) :
    suzukiSElt a K 0 v * suzukiSElt a K 0 v = 1 := by
  obtain ⟨h2, -⟩ := suzuki_frob_data a hK
  rw [suzukiSElt_mul hK, ← suzukiSElt_zero_zero hK]
  congr 1
  · ring
  · linear_combination v * h2

theorem orderOf_suzukiSElt_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {v : K} (hv : v ≠ 0) :
    orderOf (suzukiSElt a K 0 v) = 2 := by
  refine orderOf_eq_prime (by rw [sq]; exact suzukiSElt_zero_mul_self hK v) ?_
  rw [← suzukiSElt_zero_zero hK, Ne, suzukiSElt_inj]
  exact fun h => hv h.2

theorem mem_suzukiB_and_orderOf_eq_two_iff
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {g : suzukiGroup a K} :
    g ∈ suzukiB a K ∧ orderOf g = 2 ↔ ∃ v : K, v ≠ 0 ∧ suzukiSElt a K 0 v = g := by
  refine ⟨fun ⟨hg, hord⟩ => ?_, ?_⟩
  · obtain ⟨h2, -⟩ := suzuki_frob_data a hK
    have hgg : g * g = 1 := by rw [← sq, ← hord, pow_orderOf_eq_one]
    obtain ⟨u, v, l, rfl⟩ := (mem_suzukiB_iff hK).1 hg
    have hsq : suzukiSElt a K u v * suzukiDElt a K l * (suzukiSElt a K u v * suzukiDElt a K l) =
        suzukiSElt a K u v * (suzukiDElt a K l * suzukiSElt a K u v * (suzukiDElt a K l)⁻¹) *
          suzukiDElt a K (l * l) := by
      rw [← suzukiDElt_mul]
      group
    rw [hsq, suzukiDElt_conj' hK, suzukiSElt_mul hK] at hgg
    obtain ⟨-, hv, hl⟩ := (suzuki_bruhat_normal_form hK 1).2.2.1 _ _ 0 0 _ 1 hgg.symm
      (by rw [suzukiSElt_zero_zero hK, suzukiDElt_one, one_mul])
    have hl1 : l = 1 := by
      have hlK : ((l : K) - 1) ^ 2 = 0 := by
        have := congrArg (fun x : Kˣ => (x : K)) hl
        simp only [Units.val_mul, Units.val_one] at this
        linear_combination this + (1 - (l : K)) * h2
      exact Units.ext (by simpa [sub_eq_zero] using hlK)
    subst hl1
    have hu : u = 0 := by
      have huθ : u ^ 2 ^ (a + 1) * u = 0 := by
        simp only [inv_one, Units.val_one, one_pow, one_mul] at hv
        linear_combination hv - v * h2
      rcases mul_eq_zero.1 huθ with h | h
      · exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.1 h
      · exact h
    subst hu
    refine ⟨v, fun hv0 => ?_, by rw [suzukiDElt_one, mul_one]⟩
    subst hv0
    rw [suzukiDElt_one, mul_one, suzukiSElt_zero_zero hK, orderOf_one] at hord
    exact absurd hord (by norm_num)
  · rintro ⟨v, hv, rfl⟩
    exact ⟨suzukiU_le_suzukiB a K (suzukiSElt_mem_suzukiU a K 0 v), orderOf_suzukiSElt_zero hK hv⟩

theorem suzukiSElt_zero_mem_center
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (v : K) :
    suzukiSElt a K 0 v ∈ (Subgroup.center (suzukiU a K)).map (suzukiU a K).subtype := by
  refine ⟨⟨_, suzukiSElt_mem_suzukiU a K 0 v⟩, Subgroup.mem_center_iff.2 fun h => ?_, rfl⟩
  obtain ⟨u, w, hw⟩ := (mem_suzukiU_iff hK).1 h.2
  refine Subtype.ext ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hw]
  exact (suzukiSElt_zero_commute hK v u w).symm

theorem ncard_involutions_suzukiB
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    {g | g ∈ suzukiB a K ∧ orderOf g = 2}.ncard = 2 ^ (2 * a + 1) - 1 := by
  have hset : {g | g ∈ suzukiB a K ∧ orderOf g = 2} =
      Set.range fun v : Kˣ => suzukiSElt a K 0 (v : K) := by
    ext g
    rw [Set.mem_ofPred_eq, mem_suzukiB_and_orderOf_eq_two_iff hK, Set.mem_range]
    exact ⟨fun ⟨v, hv, h⟩ => ⟨Units.mk0 v hv, h⟩, fun ⟨v, h⟩ => ⟨v, v.ne_zero, h⟩⟩
  rw [hset, ← Nat.card_coe_set_eq, Nat.card_range_of_injective
    (fun v w h => Units.ext (suzukiSElt_inj.1 h).2), Nat.card_units, hK]

theorem suzukiWElt_smul_suzukiInfty
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiWElt a K • suzukiInfty K = suzukiLine a K 0 0 :=
  (suzuki_ovoid_weyl_action a hK).1

theorem suzukiWElt_smul_suzukiLine_zero
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    suzukiWElt a K • suzukiLine a K 0 0 = suzukiInfty K :=
  (suzuki_ovoid_weyl_action a hK).2.1

theorem exists_eq_suzukiWElt_mul_of_swap
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {w : suzukiGroup a K} (h₁ : w • suzukiInfty K = suzukiLine a K 0 0)
    (h₂ : w • suzukiLine a K 0 0 = suzukiInfty K) :
    ∃ l : Kˣ, w = suzukiWElt a K * suzukiDElt a K l := by
  have hmem : suzukiWElt a K * w ∈ suzukiT a K := by
    rw [← suzuki_two_point_stabilizer hK]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩ <;> rw [MulAction.mem_stabilizer_iff, mul_smul]
    · rw [h₁, suzukiWElt_smul_suzukiLine_zero hK]
    · rw [h₂, suzukiWElt_smul_suzukiInfty hK]
  obtain ⟨l, hl⟩ := mem_suzukiT_iff.1 hmem
  exact ⟨l, by rw [hl, ← mul_assoc, suzukiWElt_mul_self, one_mul]⟩

theorem conj_eq_inv_of_swap
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {w : suzukiGroup a K}
    (h₁ : w • suzukiInfty K = suzukiLine a K 0 0) (h₂ : w • suzukiLine a K 0 0 = suzukiInfty K)
    {t : suzukiGroup a K} (ht : t ∈ suzukiT a K) : w * t * w⁻¹ = t⁻¹ := by
  obtain ⟨l, rfl⟩ := exists_eq_suzukiWElt_mul_of_swap hK h₁ h₂
  obtain ⟨m, rfl⟩ := mem_suzukiT_iff.1 ht
  have hlm : l * m * l⁻¹ = m := by rw [mul_right_comm, mul_inv_cancel, one_mul]
  rw [mul_inv_rev, suzukiWElt_inv, suzukiDElt_inv, suzukiDElt_inv,
    show suzukiWElt a K * suzukiDElt a K l * suzukiDElt a K m *
        (suzukiDElt a K l⁻¹ * suzukiWElt a K) =
      suzukiWElt a K * (suzukiDElt a K l * suzukiDElt a K m * suzukiDElt a K l⁻¹) *
        suzukiWElt a K by group,
    suzukiDElt_mul, suzukiDElt_mul, hlm, suzukiWElt_D_W hK]

theorem orderOf_eq_two_of_swap
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {w : suzukiGroup a K}
    (h₁ : w • suzukiInfty K = suzukiLine a K 0 0) (h₂ : w • suzukiLine a K 0 0 = suzukiInfty K) :
    orderOf w = 2 := by
  obtain ⟨l, rfl⟩ := exists_eq_suzukiWElt_mul_of_swap hK h₁ h₂
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [sq, show suzukiWElt a K * suzukiDElt a K l * (suzukiWElt a K * suzukiDElt a K l) =
        suzukiWElt a K * suzukiDElt a K l * suzukiWElt a K * suzukiDElt a K l by group,
      suzukiWElt_D_W hK, suzukiDElt_mul, inv_mul_cancel, suzukiDElt_one]
  · rw [h, one_smul] at h₁
    exact suzukiLine_ne_suzukiInfty 0 0 h₁.symm

theorem fusionStronglyEmbedded_suzukiB
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.Open.fusionStronglyEmbedded (suzukiB a K) := by
  have hB := (suzuki_ovoid_stabilizer hK).1
  refine ⟨fun htop => ?_, ?_, fun g hg => ?_⟩
  · have hW : suzukiWElt a K ∈ suzukiB a K := htop ▸ Subgroup.mem_top _
    rw [← hB, MulAction.mem_stabilizer_iff, suzukiWElt_smul_suzukiInfty hK] at hW
    exact suzukiLine_ne_suzukiInfty 0 0 hW
  · rw [(suzuki_borel_structure hK).2.2.2.2.2.2.2]
    exact (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by omega⟩, two_ne_zero⟩).mul_right _
  · rw [← hB, ← MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    have hγ : g⁻¹ • suzukiInfty K ∈ suzukiOmega a K \ {suzukiInfty K} := by
      refine ⟨suzuki_smul_mem_suzukiOmega hK _ (suzukiInfty_mem_suzukiOmega a K), fun h => hg ?_⟩
      rw [← hB, MulAction.mem_stabilizer_iff]
      exact (eq_inv_smul_iff.1 (Set.mem_singleton_iff.1 h).symm)
    obtain ⟨⟨u, hu⟩, hux, -⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _
      (mem_suzukiOmega_diff_iff.2 ⟨0, 0, rfl⟩) _ hγ
    have huα : u • suzukiInfty K = suzukiInfty K :=
      suzukiB_le_stabilizer hK (suzukiU_le_suzukiB a K hu)
    have hα : MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) =
        (MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K)).map
          (MulAut.conj u).toMonoidHom := by
      rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj, huα]
    have hinj : Function.Injective (MulAut.conj u).toMonoidHom := (MulAut.conj u).injective
    rw [← hux, MulAction.stabilizer_smul_eq_stabilizer_map_conj, hα,
      ← Subgroup.map_inf_eq _ _ _ hinj, suzuki_two_point_stabilizer hK,
      Subgroup.card_map_of_injective hinj,
      (suzuki_borel_structure hK).2.2.1]
    exact odd_two_pow_sub_one _ (by omega)

theorem isElemAbelian_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.Open.IsElemAbelian 2 (suzukiZ0 a K) := by
  obtain ⟨-, -, -, -, hZ0ab, -⟩ := suzuki_unipotent_structure hK
  refine ⟨⟨⟨fun x y => Subtype.ext (hZ0ab _ x.2 _ y.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hx
  rw [sq]
  exact suzukiSElt_zero_mul_self hK v

theorem card_suzukiZ0 (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Nat.card (suzukiZ0 a K) = 2 ^ (2 * a + 1) := by
  rw [← SetLike.coe_sort_coe, coe_suzukiZ0 hK,
    Nat.card_range_of_injective (fun v w h => (suzukiSElt_inj.1 h).2), hK]

theorem le_twoRank_suzukiGroup (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    2 * a + 1 ≤ CFSG.Open.twoRank (suzukiGroup a K) :=
  CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary _ _ (isElemAbelian_suzukiZ0 hK) _
    (card_suzukiZ0 hK)

theorem twoRank_suzukiGroup (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.Open.twoRank (suzukiGroup a K) = 2 * a + 1 := by
  refine le_antisymm ?_ (le_twoRank_suzukiGroup hK)
  unfold CFSG.Open.twoRank CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, hE, hcard⟩
  obtain ⟨P, hP⟩ := exists_sylow_eq_suzukiU hK
  obtain ⟨Q, hEQ⟩ := (IsPGroup.of_card hcard).exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (suzukiGroup a K) P Q
  have hsub : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ suzukiZ0 a K := by
    rintro _ ⟨x, hx, rfl⟩
    have hxU : g⁻¹ * x * g ∈ suzukiU a K := by
      have := hEQ hx
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, hP] at this
      exact this
    change g⁻¹ * x * g⁻¹⁻¹ ∈ suzukiZ0 a K
    rw [inv_inv]
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, inv_mul_cancel]
      exact one_mem _
    · have hord : orderOf (g⁻¹ * x * g) = 2 := by
        refine orderOf_eq_prime ?_ fun h => hx1 ?_
        · rw [show g⁻¹ * x * g = (MulAut.conj g⁻¹) x by rw [MulAut.conj_apply, inv_inv],
            ← map_pow, hE.2 x hx, map_one]
        · rw [show x = g * (g⁻¹ * x * g) * g⁻¹ by group, h, mul_one, mul_inv_cancel]
      obtain ⟨v, -, hv⟩ := (mem_suzukiB_and_orderOf_eq_two_iff hK).1
        ⟨suzukiU_le_suzukiB a K hxU, hord⟩
      exact (mem_suzukiZ0_iff hK).2 ⟨v, hv⟩
  have h := Subgroup.card_le_of_le hsub
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard, card_suzukiZ0 hK] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

end CFSG.ShultStronglyClosedTI.SuzukiModel
