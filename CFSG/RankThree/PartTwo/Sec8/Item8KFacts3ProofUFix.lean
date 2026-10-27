module

public import CFSG.RankThree.PartTwo.KFacts.K71PSU3
public import CFSG.RankThree.PartTwo.KFacts.KS6OuterIndexProof
import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofOmegaG2
import CFSG.RankThree.PartTwo.KFacts.K71Item119
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofArith
import CFSG.RankThree.PartTwo.Sec8.Item812Res8ProofGammaInner

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3U

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.GH74.GLS.IVK (fixedField)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)

theorem trichotomy_of_outThreeCyclic {M : Type*} [Group M] (hO : OutThreeCyclic M)
    (R : Subgroup (MulAut M)) (hRc : ∀ β ∈ R, ∀ γ ∈ R, β * γ = γ * β)
    (hR3 : ∀ β ∈ R, β ^ 3 = 1) {α : MulAut M} (hαR : α ∈ R) (hα : ¬ IsInnerAut α) :
    ∀ γ ∈ R, IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α) := by
  intro γ hγ
  have hαγ : α * γ = γ * α := hRc α hαR γ hγ
  obtain ⟨k, hk, hin⟩ := hO α γ hαγ (hR3 α hαR) (hR3 γ hγ) hα
  interval_cases k
  · left
    rwa [pow_zero, one_mul] at hin
  · right; right
    rwa [pow_one, hαγ] at hin
  · right; left
    have h2 : α ^ 2 = α⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, hR3 α hαR]
    have h3 : α⁻¹ * γ = γ * α⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hαγ, mul_assoc, mul_inv_cancel, mul_one]
    rwa [h2, h3] at hin

theorem fixed_of_trichotomy_conj' {M : Type*} [Group M] [Finite M] (R : Subgroup (MulAut M))
    (hRc : ∀ β ∈ R, ∀ γ ∈ R, β * γ = γ * β) (hR3 : ∀ β ∈ R, β ^ 3 = 1) (hR9 : Nat.card R ≤ 9)
    {α : MulAut M} (hαR : α ∈ R) (hα : ¬ IsInnerAut α)
    (htri : ∀ γ ∈ R, IsInnerAut γ ∨ IsInnerAut (γ * α⁻¹) ∨ IsInnerAut (γ * α))
    {w₀ : M} (hw₀R : MulAut.conj w₀ ∈ R) (hc1 : MulAut.conj w₀ ≠ 1) {v : M} (hαv : α v = v)
    (hvw : v * w₀ = w₀ * v) : ∀ γ ∈ R, γ v = v := by
  classical
  have : Finite (MulAut M) := Finite.of_injective (fun f : MulAut M => (f : M → M))
    (fun f g h => MulEquiv.ext (congrFun h))
  set S : Subgroup (MulAut M) := R ⊓ (MulAut.conj : M →* MulAut M).range
  have hS3 : Nat.card S ≤ 3 := Item812Res11.card_inf_inn_le_three R hRc hR3 hR9 hαR hα
  have hco : orderOf (MulAut.conj w₀) = 3 := orderOf_eq_prime (hR3 _ hw₀R) hc1
  have hSeq : S = Subgroup.zpowers (MulAut.conj w₀) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr ⟨hw₀R, ⟨w₀, rfl⟩⟩) ?_
    rw [Nat.card_zpowers, hco]
    exact hS3
  refine Item812Res11.fixed_of_fixed_inner R hαR htri hαv fun σ hσR hσ => ?_
  have hσS : σ ∈ S := ⟨hσR, hσ⟩
  rw [hSeq] at hσS
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hσS
  rw [← map_zpow, MulAut.conj_apply]
  have hc : Commute v (w₀ ^ k) := Commute.zpow_right hvw k
  rw [← hc.eq, mul_inv_cancel_right]

theorem exists_fixed_involution_of_projSL {M : Type} [Group M] [Finite M] {α : MulAut M}
    (hα3 : α ^ 3 = 1) {S : Subgroup M} (hSα : ∀ s ∈ S, α s ∈ S) {m : ℕ} (hm : 1 ≤ m)
    (ψ : S ≃* projSL 2 (GaloisField 2 (3 * m)))
    (hno : ∀ k ∈ S, k ^ 3 = 1 → α k = k → ¬ ∀ s ∈ S, α s = k * s * k⁻¹) :
    ∃ v ∈ S, v ≠ 1 ∧ v ^ 2 = 1 ∧ α v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hααα : ∀ y : M, α (α (α y)) = y := fun y => by
    have h1 := congrArg (fun φ : MulAut M => φ y) hα3
    simpa only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] using h1
  have hmap : S.map α.toMonoidHom = S := by
    refine le_antisymm ?_ fun s hs => ⟨α (α s), hSα _ (hSα s hs), hααα s⟩
    rintro _ ⟨s, hs, rfl⟩
    exact hSα s hs
  set β : MulAut S := (α.subgroupMap S).trans (MulEquiv.subgroupCongr hmap)
  have hβapply : ∀ s : S, ((β s : S) : M) = α s := fun s => rfl
  have hβ3 : β ^ 3 = 1 := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply, hβapply]
    exact hααα s
  by_cases hin : IsInnerAut β
  · exfalso
    obtain ⟨k, hk⟩ := hin
    have hconj : ∀ s : S, α s = (k : M) * s * (k : M)⁻¹ := by
      intro s
      rw [← hβapply, ← hk]
      rfl
    have hk3 : k ^ 3 = 1 := by
      apply Sec21.eq_one_of_forall_commute_of_mulEquiv_projSL ψ
      intro s
      have h1 : MulAut.conj (k ^ 3) s = s := by
        rw [map_pow, hk, hβ3, MulAut.one_apply]
      rw [MulAut.conj_apply] at h1
      calc s * k ^ 3 = k ^ 3 * s * (k ^ 3)⁻¹ * k ^ 3 := by rw [h1]
        _ = k ^ 3 * s := by group
    refine hno k k.2 (by simpa using congrArg Subtype.val hk3) ?_ fun s hs => hconj ⟨s, hs⟩
    rw [hconj k]
    group
  · obtain ⟨φ⟩ := nonempty_eqLocus_mulEquiv_projSL_two hm ψ hβ3 hin
    have hdvd : 2 ∣ Nat.card (β.toMonoidHom.eqLocus (MonoidHom.id S)) := by
      rw [Nat.card_congr φ.toEquiv, Sec21.card_projSL_two m hm]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have ht' : orderOf ((t : S) : M) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, ht]
    refine ⟨((t : S) : M), (t : S).2, fun h1 => ?_, ?_, ?_⟩
    · rw [h1, orderOf_one] at ht'
      omega
    · rw [← ht']
      exact pow_orderOf_eq_one _
    · rw [← hβapply]
      exact congrArg Subtype.val t.2

theorem card_dvd_of_forall_fixed_psu {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (hq : 2 < 2 ^ f) {δ : MulAut (unitaryPSU h 3)} (hδ3 : δ ^ 3 = 1)
    (hD : δ ∉ (psuConj h).range) {S : Subgroup (unitaryPSU h 3)} (hS : ∀ s ∈ S, δ s = s) :
    ∃ f₀ : ℕ, f = 3 * f₀ ∧ 1 ≤ f₀ ∧
      Nat.card S ∣ (2 ^ f₀) ^ 3 * ((2 ^ f₀) ^ 2 - 1) * ((2 ^ f₀) ^ 3 + 1) := by
  obtain ⟨σ, hσ3, H, hδH⟩ := unitary_order_three_field_descent hq δ hδ3 hD
  obtain ⟨f₀, hf, hf₀, hcard⟩ := exists_card_fixedField_of_orderOf_eq_three h hσ3
  have h₀ : UnitaryFieldData 2 f₀ (fixedField σ) := ⟨h.prime, hf₀, hcard⟩
  have hbar := bar_coe_fixedField h hf h₀
  set Φ := puHom h hf h₀ hbar with hΦ
  refine ⟨f₀, hf, hf₀, ?_⟩
  set c : MulAut (unitaryPSU h 3) := psuConj h H
  have hle : S.map (c⁻¹ : MulAut (unitaryPSU h 3)).toMonoidHom ≤ Φ.range := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hΦ, mem_range_puHom_iff]
    have h1 := hS s hs
    rw [hδH] at h1
    have h2 : c (psuField h σ (c⁻¹ s)) = c (c⁻¹ s) := by
      rw [MulAut.apply_inv_self]
      simpa only [MulAut.mul_apply] using h1
    exact c.injective h2
  have hker := ker_puHom h hf h₀ hbar
  have : ((StatedScalars (Fin 3) (fixedField σ)).subgroupOf
      (Sec4.glPi false 3 (2 ^ f₀) (fixedField σ))).Normal := hker ▸ Φ.normal_ker
  let Ψ : projImage (Sec4.glPi false 3 (2 ^ f₀) (fixedField σ)) ≃* Φ.range :=
    (statedProjEquivMapMk _).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange Φ))
  have hcardΦ : Nat.card Φ.range = (2 ^ f₀) ^ 3 * ((2 ^ f₀) ^ 2 - 1) * ((2 ^ f₀) ^ 3 + 1) :=
    Item812Res8.card_of_isoPGUThree hf₀ ⟨fixedField σ, inferInstance, h₀.finite,
      by rw [hcard, ← pow_mul, mul_comm f₀ 2], ⟨Ψ.symm⟩⟩
  rw [← hcardΦ, ← Subgroup.card_map_of_injective (c⁻¹ : MulAut (unitaryPSU h 3)).injective]
  exact Subgroup.card_dvd_of_le hle

theorem false_of_forall_fixed_psu {m : ℕ} (hm : 1 ≤ m) {K : Type} [Field K]
    (h : UnitaryFieldData 2 (3 * m) K) (hq : 2 < 2 ^ (3 * m)) {δ : MulAut (unitaryPSU h 3)}
    (hδ3 : δ ^ 3 = 1) (hD : δ ∉ (psuConj h).range) {S : Subgroup (unitaryPSU h 3)}
    (hS : ∀ s ∈ S, δ s = s) (hcard : Nat.card S = 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) :
    False := by
  obtain ⟨f₀, hf, -, hdvd⟩ := card_dvd_of_forall_fixed_psu h hq hδ3 hD hS
  obtain rfl : f₀ = m := by omega
  have h2 : 2 ≤ 2 ^ f₀ :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hm
  rw [hcard, show 2 ^ (3 * f₀) = (2 ^ f₀) ^ 3 by rw [mul_comm, pow_mul]] at hdvd
  exact Item812Res8.not_dvd_unitary h2 hdvd

@[expose] def UnitaryModel (M : Type) [Group M] (m : ℕ) (α : MulAut M) : Prop :=
  ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 (3 * m) K) (_ : 2 < 2 ^ (3 * m))
    (D : MulAut M →* MulAut (unitaryPSU h 3)) (π : M →* unitaryPSU h 3),
    (∀ g : M, D (MulAut.conj g) ∈ (psuConj h).range) ∧
    (∀ (δ : MulAut M) (y : M), π (δ y) = D δ (π y)) ∧
    (∀ y : M, π y = 1 → y ∈ Subgroup.center M) ∧
    D α ∉ (psuConj h).range

theorem unitaryModel_of_psu {M : Type} [Group M] {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 (3 * m) K) (hq : 2 < 2 ^ (3 * m)) (E : M ≃* unitaryPSU h 3)
    {α : MulAut M} (hα : MulAut.congr E α ∉ (psuConj h).range) : UnitaryModel M m α := by
  refine ⟨K, inferInstance, h, hq, (MulAut.congr E).toMonoidHom, E.toMonoidHom, fun g => ?_,
    fun δ y => ?_, fun y hy => ?_, hα⟩
  · change MulAut.congr E (MulAut.conj g) ∈ (psuConj h).range
    rw [congr_mulAutConj]
    exact (stdPinnedPSU3 h).inn_le ⟨E g, rfl⟩
  · change E (δ y) = MulAut.congr E δ (E y)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  · have hy1 : y = 1 := E.injective (by rw [map_one]; exact hy)
    rw [hy1]
    exact one_mem _

theorem unitaryModel_of_su {M : Type} [Group M] {m : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 (3 * m) K) (hq : 2 < 2 ^ (3 * m))
    (E : M ≃* unitarySU 2 (3 * m) K 3) {α : MulAut M}
    (hα : MulAut.congr (suCenterEquiv h hq) (centerDescend _ (MulAut.congr E α)) ∉
      (psuConj h).range) : UnitaryModel M m α := by
  set q := QuotientGroup.mk' (Subgroup.center (unitarySU 2 (3 * m) K 3))
  refine ⟨K, inferInstance, h, hq,
    (MulAut.congr (suCenterEquiv h hq)).toMonoidHom.comp
      ((centerDescend _).comp (MulAut.congr E).toMonoidHom),
    (suCenterEquiv h hq).toMonoidHom.comp (q.comp E.toMonoidHom), fun g => ?_, fun δ y => ?_,
    fun y hy => ?_, hα⟩
  · change MulAut.congr (suCenterEquiv h hq) (centerDescend _ (MulAut.congr E (MulAut.conj g))) ∈
      (psuConj h).range
    rw [congr_mulAutConj, centerDescend_conj, congr_mulAutConj]
    exact (stdPinnedPSU3 h).inn_le ⟨_, rfl⟩
  · change suCenterEquiv h hq (q (E (δ y))) = MulAut.congr (suCenterEquiv h hq)
      (centerDescend _ (MulAut.congr E δ)) (suCenterEquiv h hq (q (E y)))
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    change _ = ((MulAut.congr E δ (E y) : unitarySU 2 (3 * m) K 3) :
      unitarySU 2 (3 * m) K 3 ⧸ Subgroup.center (unitarySU 2 (3 * m) K 3))
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rfl
  · have h1 : q (E y) = 1 := (suCenterEquiv h hq).injective (by rw [map_one]; exact hy)
    have h2 : E y ∈ Subgroup.center (unitarySU 2 (3 * m) K 3) := (QuotientGroup.eq_one_iff _).mp h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro g
    apply E.injective
    rw [map_mul, map_mul]
    exact h2 (E g)

theorem false_of_forall_fixed_of_model {M : Type} [Group M] {m : ℕ} (hm : 1 ≤ m) {K : Type}
    [Field K] {h : UnitaryFieldData 2 (3 * m) K} (hq : 2 < 2 ^ (3 * m))
    {D : MulAut M →* MulAut (unitaryPSU h 3)} {π : M →* unitaryPSU h 3}
    (hπ : ∀ (δ : MulAut M) (y : M), π (δ y) = D δ (π y))
    (hker : ∀ y : M, π y = 1 → y ∈ Subgroup.center M) {δ : MulAut M} (hδ3 : δ ^ 3 = 1)
    (hD : D δ ∉ (psuConj h).range) {S : Subgroup M} (hS : ∀ s ∈ S, δ s = s)
    (hZ : Subgroup.center S = ⊥)
    (hcard : Nat.card S = 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1)) : False := by
  have hinj : Function.Injective (π.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have hc : (s : M) ∈ Subgroup.center M := hker s hs
    have hsZ : s ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff] at hc ⊢
      intro t
      exact Subtype.ext (hc t)
    rw [hZ, Subgroup.mem_bot] at hsZ
    exact hsZ
  refine false_of_forall_fixed_psu hm h hq (δ := D δ) (by rw [← map_pow, hδ3, map_one]) hD
    (S := (π.comp S.subtype).range) ?_ ?_
  · rintro _ ⟨s, rfl⟩
    change D δ (π s) = π s
    rw [← hπ, hS s s.2]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard]

theorem exists_fixed_involution_of_model {M : Type} [Group M] [Finite M] {m : ℕ} (hm : 1 ≤ m)
    {K : Type} [Field K] {h : UnitaryFieldData 2 (3 * m) K} (hq : 2 < 2 ^ (3 * m))
    {D : MulAut M →* MulAut (unitaryPSU h 3)} {π : M →* unitaryPSU h 3}
    (hDin : ∀ g : M, D (MulAut.conj g) ∈ (psuConj h).range)
    (hπ : ∀ (δ : MulAut M) (y : M), π (δ y) = D δ (π y))
    (hker : ∀ y : M, π y = 1 → y ∈ Subgroup.center M) {α : MulAut M} (hα3 : α ^ 3 = 1)
    (hαD : D α ∉ (psuConj h).range) {w : M} (hαw : α * MulAut.conj w = MulAut.conj w * α)
    (ψ : perfectResidual (Subgroup.centralizer ({w} : Set M)) ≃*
      projSL 2 (GaloisField 2 (3 * m))) :
    ∃ v : M, v ≠ 1 ∧ v ^ 2 = 1 ∧ α v = v ∧ v * w = w * v := by
  set C := Subgroup.centralizer ({w} : Set M) with hC
  set S := inSubgroup perfectResidual C with hS
  have ψ' : S ≃* projSL 2 (GaloisField 2 (3 * m)) :=
    ((perfectResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans ψ
  have hβC : ∀ β : MulAut M, β * MulAut.conj w = MulAut.conj w * β → ∀ y ∈ C, β y ∈ C := by
    intro β hβ y hy
    rw [hC, Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have h1 := congrArg (fun φ : MulAut M => φ y) hβ
    simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
    have hy' : w * y * w⁻¹ = y := by rw [← hy]; group
    rw [hy'] at h1
    calc β y * w = w * β y * w⁻¹ * w := by rw [← h1]
      _ = w * β y := by group
  have hαinv : α⁻¹ * MulAut.conj w = MulAut.conj w * α⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hαw, mul_assoc, mul_inv_cancel, mul_one]
  have hCmap : C.map α.toMonoidHom = C :=
    le_antisymm (by rintro _ ⟨y, hy, rfl⟩; exact hβC α hαw y hy)
      fun y hy => ⟨α⁻¹ y, hβC α⁻¹ hαinv y hy, MulAut.apply_inv_self M α y⟩
  have hSmap : S.map α.toMonoidHom = S := by
    rw [hS, map_inSubgroup_perfectResidual α C, hCmap]
  have hSα : ∀ s ∈ S, α s ∈ S := fun s hs => by
    rw [← hSmap]
    exact ⟨s, hs, rfl⟩
  have hZ : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    exact Sec21.eq_one_of_forall_commute_of_mulEquiv_projSL ψ' fun t =>
      Subgroup.mem_center_iff.mp hz t
  have hcard : Nat.card S = 2 ^ (3 * m) * ((2 ^ (3 * m)) ^ 2 - 1) := by
    rw [Nat.card_congr ψ'.toEquiv, Sec21.card_projSL_two _ (by omega)]
  have hno : ∀ k ∈ S, k ^ 3 = 1 → α k = k → ¬ ∀ s ∈ S, α s = k * s * k⁻¹ := by
    intro k _ hk3 hαk hact
    have hαc : α * MulAut.conj k = MulAut.conj k * α := by
      have h1 := mul_mulAutConj_mul_inv α k
      rw [hαk] at h1
      calc α * MulAut.conj k = α * MulAut.conj k * α⁻¹ * α := by group
        _ = MulAut.conj k * α := by rw [h1]
    have hcomm : Commute (MulAut.conj k)⁻¹ α := (Commute.inv_left hαc.symm)
    set δ : MulAut M := (MulAut.conj k)⁻¹ * α with hδ
    have hδ3 : δ ^ 3 = 1 := by
      rw [hδ, hcomm.mul_pow, hα3, mul_one, inv_pow, ← map_pow, hk3, map_one, inv_one]
    have hδS : ∀ s ∈ S, δ s = s := by
      intro s hs
      rw [hδ, MulAut.mul_apply, hact s hs, ← map_inv, MulAut.conj_apply]
      group
    have hδD : D δ ∉ (psuConj h).range := by
      intro hmem
      apply hαD
      have he : D α = D (MulAut.conj k) * D δ := by
        rw [hδ, map_mul, map_inv, mul_inv_cancel_left]
      rw [he]
      exact mul_mem (hDin k) hmem
    exact false_of_forall_fixed_of_model hm hq hπ hker hδ3 hδD hδS hZ hcard
  obtain ⟨v, hvS, hv1, hv2, hαv⟩ := exists_fixed_involution_of_projSL hα3 hSα hm ψ' hno
  have hvC : v ∈ C := Subgroup.map_subtype_le _ hvS
  exact ⟨v, hv1, hv2, hαv, Subgroup.mem_centralizer_singleton_iff.mp hvC⟩

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3U
