module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeRefl
public import CFSG.OddTranspositions.PartFour.ThirteenListThreeSpace
public import CFSG.OddTranspositions.PartFour.ThirteenListThreeSix
public import CFSG.OddTranspositions.PartFour.ThirteenListThreeCenter
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspListThreeTranspCases
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Mult
import CFSG.GroupTheory.PerfectCoverProduct
import CFSG.Timmesfeld.Bridge.Asc72YCount

public section

namespace CFSG.OddTranspositions.PartFour

open scoped commutatorElement Pointwise
open CFSG Subgroup

private theorem eq_one_of_mul_self_of_mem_odd_center {X : Type} [Group X] [Finite X]
    (hZ : Odd (Nat.card (center X))) {x : X} (hx : x ∈ center X) (h2 : x * x = 1) : x = 1 := by
  have h2dvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, h2])
  have hdvd : orderOf x ∣ Nat.card (center X) := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hdvd
    exact ((Nat.not_even_iff_odd.mpr hZ) (even_iff_two_dvd.mpr hdvd)).elim

open scoped commutatorElement in
open CFSG.Fischer.Classification in
theorem reflGroup_eq_commutator_sup_zpowers {n : ℕ}
    {f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)} (hf : IsF3Form f) (hn : 4 ≤ n)
    {v : Fin n → ZMod 3} (hv : f v v = 1) :
    commutator (F3.reflGroup f) ⊔ Subgroup.zpowers (reflElt f v) = ⊤ := by
  classical
  let π := QuotientGroup.mk' (commutator (F3.reflGroup f))
  let K : Subgroup (F3.reflGroup f) :=
    (Subgroup.zpowers (π (reflElt f v))).comap π
  have hbase : (((↑) : F3.reflGroup f → GL (Fin n) (ZMod 3)) ⁻¹' F3.reflSet f) ⊆ (K : Set _) := by
    rintro d hd
    obtain ⟨w, hw, hdw⟩ := F3.mem_reflSet_iff.mp hd
    have hd' : d = reflElt f w := Subtype.ext hdw.symm
    obtain ⟨g, hg, hgr⟩ := F3.exists_conj_refl hf hn hv hw
    have hconj : (⟨g, hg⟩ : F3.reflGroup f) * reflElt f v * ⟨g, hg⟩⁻¹ = reflElt f w :=
      Subtype.ext hgr
    have hcomm : π (⟨g, hg⟩ : F3.reflGroup f) * π (reflElt f v) =
        π (reflElt f v) * π ⟨g, hg⟩ := mul_comm' _ _
    have hπw : π (reflElt f w) = π (reflElt f v) := by
      rw [← hconj, map_mul, map_mul, map_inv, hcomm, mul_assoc, mul_inv_cancel, mul_one]
    change π d ∈ Subgroup.zpowers (π (reflElt f v))
    rw [hd', hπw]
    exact Subgroup.mem_zpowers _
  have hK : K = ⊤ := top_unique (by
    rw [← Subgroup.closure_closure_coe_preimage (k := F3.reflSet f)]
    exact (Subgroup.closure_le K).mpr hbase)
  have hmap := MonoidHom.map_zpowers π (reflElt f v)
  have hsup := Subgroup.comap_map_eq π (Subgroup.zpowers (reflElt f v))
  rw [hmap, QuotientGroup.ker_mk'] at hsup
  rw [sup_comm]
  exact hsup.symm.trans hK


theorem exists_lift_of_psl_four_three {X : Type} [Group X] [Finite X]
    (hZ : Odd (Nat.card (center X))) {s : X} (hs : s * s = 1)
    (C : Subgroup (X ⧸ center X)) (hC : IsQuasisimple C)
    (hmodel : Blueprint.LieModel (C ⧸ center C) .PSL 4 3 1)
    (hsC : (QuotientGroup.mk s : X ⧸ center X) ∈ normalizer C) :
    ∃ L : Subgroup X, s ∈ L ∧ L ⊓ center X = ⊥ ∧
      L.map (QuotientGroup.mk' (center X)) = C ⊔ zpowers (QuotientGroup.mk s) := by
  classical
  let π := QuotientGroup.mk' (center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπker : π.ker = center X := QuotientGroup.ker_mk' _
  have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.mp hC.1
  let N := C.comap π
  let Q : Subgroup X := ⁅N, N⁆
  have hQmap : Q.map π = C := GroupTheory.PerfectCover.map_commutator_comap π hπ hCperf
  have hQperf : Group.IsPerfect Q :=
    GroupTheory.PerfectCover.isPerfect_commutator_comap π hπ (by rw [hπker]) hCperf
  let ρ : Q →* C := (π.comp Q.subtype).codRestrict C fun q => hQmap ▸ ⟨q, q.2, rfl⟩
  have hρ : Function.Surjective ρ := by
    intro c
    obtain ⟨q, hq, hqc⟩ : (c : X ⧸ center X) ∈ Q.map π := hQmap.symm ▸ c.2
    exact ⟨⟨q, hq⟩, Subtype.ext hqc⟩
  have hρker : ∀ q : Q, q ∈ ρ.ker ↔ (q : X) ∈ center X := fun q => by
    rw [MonoidHom.mem_ker]
    change ρ q = 1 ↔ _
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hρcentral : ρ.ker ≤ center Q := fun q hq =>
    Subgroup.mem_center_iff.mpr fun r => Subtype.ext
      (Subgroup.mem_center_iff.mp ((hρker q).mp hq) r)
  have hQq : IsQuasisimple Q :=
    (LocalCores.isQuasisimple_iff_of_surjective hQperf ρ hρ hρcentral).mpr hC
  have hkerbar : ((QuotientGroup.mk' (center C)).comp ρ).ker = center Q := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      LocalCores.comap_center_eq_of_perfect hQperf ρ hρ hρcentral]
  let ebar : Q ⧸ center Q ≃* C ⧸ center C :=
    (QuotientGroup.quotientMulEquivOfEq hkerbar.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hρ))
  have hmodelQ : Blueprint.LieModel (Q ⧸ center Q) .PSL 4 3 1 :=
    Blueprint.LieModel.of_mulEquiv ebar.symm hmodel
  have htwo : IsPGroup 2 (center Q) :=
    ComponentClassification.CatFactsL4U4.Cover82.multiplierL4U4 Q hQq 3 1 Nat.prime_three
      (by decide) le_rfl (Or.inl hmodelQ)
  have hQZ : Q ⊓ center X = ⊥ := inf_center_eq_bot_of_isPGroup_two hZ htwo
  have hsN : s ∈ normalizer N := by
    have h := Subgroup.comap_normalizer_eq_of_le_range (H := C) (f := π)
      (by rw [MonoidHom.range_eq_top_of_surjective _ hπ]; exact le_top)
    change (normalizer C).comap π = normalizer N at h
    rw [← h]
    exact hsC
  have hsQ : s ∈ normalizer Q := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hsN ⊢
    change N.map (MulAut.conj s).toMonoidHom = N at hsN
    change Q.map (MulAut.conj s).toMonoidHom = Q
    rw [show Q = ⁅N, N⁆ from rfl, Subgroup.map_commutator, hsN]
  have hle : zpowers s ≤ normalizer Q := Subgroup.zpowers_le.mpr hsQ
  refine ⟨Q ⊔ zpowers s, Subgroup.mem_sup_right (Subgroup.mem_zpowers s), ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxL, hxZ⟩ := Subgroup.mem_inf.mp hx
    have hxL' : x ∈ (Q : Set X) * (zpowers s : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q (zpowers s) hle]
      exact hxL
    obtain ⟨q, hq, y, hy, rfl⟩ := hxL'
    have hyy : y * y = 1 := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hs, one_zpow]
    have hyq : y * q * y⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hle hy) q).mp hq
    have hsq : q * y * (q * y) ∈ Q := by
      rw [show q * y * (q * y) = q * (y * q * y⁻¹) * (y * y) by group, hyy, mul_one]
      exact Q.mul_mem hq hyq
    have hsqZ : q * y * (q * y) ∈ center X := Subgroup.mul_mem _ hxZ hxZ
    have h1 : q * y * (q * y) = 1 := by
      have : q * y * (q * y) ∈ Q ⊓ center X := Subgroup.mem_inf.mpr ⟨hsq, hsqZ⟩
      rw [hQZ] at this
      exact Subgroup.mem_bot.mp this
    exact Subgroup.mem_bot.mpr (eq_one_of_mul_self_of_mem_odd_center hZ hxZ h1)
  · rw [Subgroup.map_sup, hQmap, MonoidHom.map_zpowers]
    rfl

open CFSG.Fischer.Classification in
theorem exists_reflGroup_lift_of_split {X : Type} [Group X] [Finite X] {s : X}
    (hs : s * s = 1) (hZ : Odd (Nat.card (center X)))
    {f₆ : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (hf₆ : IsF3Form f₆)
    (hT : ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, f₆ x x = 0)
    {c : Fin 6 → ZMod 3} (hc : f₆ c c = 1)
    (θ : F3.reflGroup f₆ →* X ⧸ center X) (hθ : Function.Injective θ)
    (hθc : θ (reflElt f₆ c) = QuotientGroup.mk s) :
    ∃ ι : F3.reflGroup f₆ →* X, Function.Injective ι ∧
      (∀ g, (QuotientGroup.mk (ι g) : X ⧸ center X) = θ g) ∧ ι (reflElt f₆ c) = s := by
  classical
  let r : F3.reflGroup f₆ := reflElt f₆ c
  have hθr : θ r = QuotientGroup.mk s := hθc
  let D₆ : Subgroup (F3.reflGroup f₆) := commutator (F3.reflGroup f₆)
  have hDdata := commutator_reflGroup_six_split hf₆ hT
  have hDq : IsQuasisimple D₆ := hDdata.1
  have hDmodel : Blueprint.LieModel (D₆ ⧸ center D₆) .PSL 4 3 1 := hDdata.2
  have hgen : D₆ ⊔ zpowers r = ⊤ := reflGroup_eq_commutator_sup_zpowers hf₆ (by decide) hc
  have hDnormal : D₆.Normal := inferInstance
  let C := D₆.map θ
  let eC : D₆ ≃* C := D₆.equivMapOfInjective θ hθ
  have hCq : IsQuasisimple C := hDq.of_mulEquiv eC.symm
  have hCmodel : Blueprint.LieModel (C ⧸ center C) .PSL 4 3 1 :=
    Blueprint.LieModel.of_mulEquiv (CFSG.Fischer.quotientCenterCongr eC) hDmodel
  have hsC : (QuotientGroup.mk s : X ⧸ center X) ∈ normalizer C := by
    rw [← hθr]
    have := hDnormal
    exact Subgroup.le_normalizer_map θ (Subgroup.mem_map_of_mem θ
      ((D₆.normalizer_eq_top) ▸ Subgroup.mem_top r))
  obtain ⟨L, hsL, hLZ, hLmap⟩ := exists_lift_of_psl_four_three hZ hs C hCq hCmodel hsC
  have hCgen : C ⊔ zpowers (QuotientGroup.mk s) = θ.range := by
    rw [← hθr, ← MonoidHom.map_zpowers, ← Subgroup.map_sup, hgen, Subgroup.map_top]
  have hLrange : L.map (QuotientGroup.mk' (center X)) = θ.range := hLmap.trans hCgen
  have hLinj : Function.Injective ((QuotientGroup.mk' (center X)).comp L.subtype) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
    have hxZ : (x : X) ∈ center X := (QuotientGroup.eq_one_iff _).mp hx
    have : (x : X) ∈ L ⊓ center X := ⟨x.2, hxZ⟩
    rw [hLZ] at this
    exact Subtype.ext (Subgroup.mem_bot.mp this)
  let eL : L ≃* F3.reflGroup f₆ :=
    ((MonoidHom.ofInjective hLinj).trans
      (MulEquiv.subgroupCongr (by rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hLrange))).trans
        (MonoidHom.ofInjective hθ).symm
  have heLs : eL ⟨s, hsL⟩ = r := by
    have hel : (MonoidHom.ofInjective hθ) r =
        (MulEquiv.subgroupCongr (by
          rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hLrange))
          ((MonoidHom.ofInjective hLinj) ⟨s, hsL⟩) := Subtype.ext hθr
    change (MonoidHom.ofInjective hθ).symm _ = r
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, MulEquiv.trans_apply]
    rw [← hel, MulEquiv.symm_apply_apply]
  let ι : F3.reflGroup f₆ →* X := L.subtype.comp eL.symm.toMonoidHom
  have hι : Function.Injective ι := L.subtype_injective.comp eL.symm.injective
  have heL : ∀ x : L, θ (eL x) = QuotientGroup.mk (x : X) := by
    intro x
    have h := (MonoidHom.ofInjective hθ).apply_symm_apply
      ((MulEquiv.subgroupCongr (by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]; exact hLrange))
          ((MonoidHom.ofInjective hLinj) x))
    exact congrArg Subtype.val h
  refine ⟨ι, hι, fun g => ?_, ?_⟩
  · have h := heL (eL.symm g)
    rw [eL.apply_symm_apply] at h
    exact h.symm
  · have h := eL.symm_apply_apply ⟨s, hsL⟩
    rw [heLs] at h
    exact congrArg Subtype.val h

open CFSG.Fischer.Classification CFSG.LocalAnalysis.WeakClosure81 CFSG.Open in
theorem exists_sevenNine_of_reflGroup_embedding {X : Type} [Group X] {s : X}
    (hs : s * s = 1) {f₆ : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}
    (hf₆ : IsF3Form f₆) {c : Fin 6 → ZMod 3} (hc : f₆ c c = 1)
    (ι : F3.reflGroup f₆ →* X) (hι : Function.Injective ι) (hιc : ι (reflElt f₆ c) = s) :
    ∃ L : Subgroup X, s ∈ L ∧ IsSevenNineGroup ↥L
      {x : ↥L | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1} := by
  let r : F3.reflGroup f₆ := reflElt f₆ c
  have hsL : s ∈ ι.range := ⟨r, hιc⟩
  let eL := (MonoidHom.ofInjective hι).symm
  have heLs : eL ⟨s, hsL⟩ = r := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext hιc.symm
  have horth : orthReflSet 3 6 f₆ = F3.reflSet f₆ := by
    ext g
    simp only [orthReflSet, F3.reflSet, fischerTransvections, Set.mem_setOf_eq]
    have htwo : (-2 : ZMod 3) = 1 := by decide
    constructor
    · rintro ⟨w, hw, hgw⟩
      exact ⟨w, hw.trans htwo, hgw⟩
    · rintro ⟨w, hw, hgw⟩
      exact ⟨w, hw.trans htwo.symm, hgw⟩
  refine ⟨ι.range, hsL, Or.inr ⟨f₆, hf₆.symm, hf₆.nondeg, Or.inl
    ⟨eL.trans (MulEquiv.subgroupCongr (congrArg Subgroup.closure horth.symm)), fun d hd => ?_⟩⟩⟩
  have hd' : (d : X) = s := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hd.1
    have h2 : s ^ (2 : ℤ) = 1 := by rw [zpow_two, hs]
    rw [← hk, ← Int.emod_add_ediv_mul k 2, zpow_add, zpow_mul', h2, one_zpow, mul_one]
    rcases Int.emod_two_eq k with h | h <;> rw [h]
    · exact (hd.2 (Subtype.ext (hk.symm.trans (by
        rw [← Int.emod_add_ediv_mul k 2, zpow_add, zpow_mul', h2, one_zpow, mul_one, h, zpow_zero]
        rfl)))).elim
    · exact zpow_one s
  have hed : eL d = r := by rw [show d = ⟨s, hsL⟩ from Subtype.ext hd', heLs]
  show ((eL d : F3.reflGroup f₆) : GL (Fin 6) (ZMod 3)) ∈ orthReflSet 3 6 f₆
  rw [hed, horth]
  exact F3.refl_mem_reflSet hc

open CFSG.Fischer.Classification CFSG.LocalAnalysis.WeakClosure81 CFSG.Open in
theorem exists_sevenNine_of_reflQuot_lift {X : Type} [Group X] [Finite X] {s : X}
    (hs : s * s = 1) (hZ : Odd (Nat.card (Subgroup.center X))) {m : ℕ} (hm : 7 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}
    (hf : CFSG.Fischer.Classification.IsF3Form f)
    (φ : X ⧸ Subgroup.center X ≃* CFSG.Fischer.Classification.F3.reflGroup f ⧸
      Subgroup.center (CFSG.Fischer.Classification.F3.reflGroup f))
    (hφs : ∃ h : CFSG.Fischer.Classification.F3.reflGroup f,
      (h : GL (Fin m) (ZMod 3)) ∈ CFSG.Fischer.Classification.F3.reflSet f ∧
        φ (QuotientGroup.mk s) = QuotientGroup.mk h) :
    ∃ L : Subgroup X, s ∈ L ∧ CFSG.LocalAnalysis.WeakClosure81.IsSevenNineGroup ↥L
      {x : ↥L | (x : X) ∈ Subgroup.zpowers s ∧ x ≠ 1} := by
  classical
  obtain ⟨h, hh, hφh⟩ := hφs
  obtain ⟨v, hv, hvh⟩ := F3.mem_reflSet_iff.mp hh
  obtain ⟨c, hc, Φ, hΦ, hΦc, hne⟩ := exists_reflGroup_split_six_embedding hm f hf v hv
  let f₆ := diagF3 6 2
  have hf₆ : IsF3Form f₆ := isF3Form_diagF3 (by decide)
  let r : F3.reflGroup f₆ := reflElt f₆ c
  let θ : F3.reflGroup f₆ →* X ⧸ center X :=
    φ.symm.toMonoidHom.comp ((QuotientGroup.mk' (center (F3.reflGroup f))).comp Φ)
  have hθ : Function.Injective θ := φ.symm.injective.comp
    (injective_mk_comp_reflGroup (by omega) hf hΦ hne)
  have hθr : θ r = QuotientGroup.mk s := by
    have hΦr : Φ r = h := Subtype.ext (hΦc.trans hvh)
    change φ.symm (QuotientGroup.mk (Φ r)) = _
    rw [hΦr, ← hφh, MulEquiv.symm_apply_apply]
  obtain ⟨T, hT3, hTQ⟩ := exists_totallySingular_diagF3_six_two
  obtain ⟨ι, hι, -, hιc⟩ := exists_reflGroup_lift_of_split hs hZ hf₆
    ⟨T, hT3, fun x hx => hTQ x hx⟩ hc θ hθ hθr
  exact exists_sevenNine_of_reflGroup_embedding hs hf₆ hc ι hι hιc

open CFSG.Fischer.Classification CFSG.LocalAnalysis.WeakClosure81 CFSG.Open in
theorem oddTranspListThreeTranspReflLift_holds : OddTranspListThreeTranspReflLift := by
  intro X _ _ s hs _ _ hO2 _ _ _ _ m hm f hsym hnd hM
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rw [hs, pow_two] at this
    exact this
  have hZ := CFSG.Timmesfeld.Bridge.Asc72.CentralQuot.odd_card_center hO2
  obtain ⟨φ, hφ⟩ := (fischerCentralQuotientModel_iff
    {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x}).mp hM
  have hφs : φ (QuotientGroup.mk s) ∈ D3 f :=
    (hφ _).mp (show IsConj (QuotientGroup.mk s) (QuotientGroup.mk s) from IsConj.refl _)
  obtain ⟨h, hh, he⟩ := hφs
  exact Or.inr (Or.inr (Or.inr (Or.inl
    (exists_sevenNine_of_reflQuot_lift hs2 hZ hm ⟨hsym, hnd⟩ φ ⟨h, hh, he⟩))))

end CFSG.OddTranspositions.PartFour
