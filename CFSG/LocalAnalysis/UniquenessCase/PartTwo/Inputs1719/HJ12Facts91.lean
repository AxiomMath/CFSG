module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Objects
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Spec

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Sporadic.J2.Module12 (A12 B12)
open CFSG.GF2Type.Smith1979.GammaU (vecOf)
open CFSG.GF2Type.Smith1979.GammaU.StepA (orbitOf)
open CFSG.GF2Type.Smith1979.GammaU (appN codeOf vecOf_inj)
open HJBridge (grpOf)
open HJ12 (wordR hjTauc)

theorem hjOrbit_facts :
    hjV1 ≠ 1 ∧ hjV2 ≠ 1 ∧
      (∀ v : W12, v ≠ 1 → (∃ l ∈ hjL0, l v = hjV1) ∨ (∃ l ∈ hjL0, l v = hjV2)) ∧
      (¬ ∃ l ∈ hjL0, l hjV1 = hjV2) ∧
      Nat.card ↥(MulAction.stabilizer (MulAut W12) hjV1 ⊓ hjL0) = 384 ∧
      Nat.card ↥(MulAction.stabilizer (MulAut W12) hjV2 ⊓ hjL0) = 240 := by
  classical
  have h : HJ12.hjOrbitCheck = true := HJ12.hjOrbitCheck_eq
  simp only [HJ12.hjOrbitCheck, HJ12.gensL, Bool.and_eq_true, beq_iff_eq,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_orbitOf] at h
  obtain ⟨⟨⟨⟨hc1, hc2⟩, hl1⟩, hl2⟩, hall⟩ := h
  have hcl1 := CFSG.GF2Type.Smith1979.GammaU.StepA.closedOrbit_spec hc1
  have hcl2 := CFSG.GF2Type.Smith1979.GammaU.StepA.closedOrbit_spec hc2
  have hdisj : ∀ n < 4096, n ≠ 0 →
      (n ∈ orbitOf [HJ12.hjAc, HJ12.hjBc] 4 ∧ n ∉ orbitOf [HJ12.hjAc, HJ12.hjBc] 1024) ∨
        (n ∉ orbitOf [HJ12.hjAc, HJ12.hjBc] 4 ∧ n ∈ orbitOf [HJ12.hjAc, HJ12.hjBc] 1024) := by
    intro n hn hn0
    have h1 := List.all_eq_true.1 hall n (List.mem_range.2 hn)
    have hn0' : (n == 0) = false := by simpa using hn0
    rw [hn0', Bool.false_or] at h1
    cases ha : (orbitOf [HJ12.hjAc, HJ12.hjBc] 4).contains n <;>
      cases hb : (orbitOf [HJ12.hjAc, HJ12.hjBc] 1024).contains n <;>
      rw [ha, hb] at h1
    · exact absurd h1 (by decide)
    · right
      refine ⟨fun hm => ?_, List.contains_iff_mem.1 hb⟩
      rw [List.contains_iff_mem.2 hm] at ha
      exact absurd ha (by decide)
    · left
      refine ⟨List.contains_iff_mem.1 ha, fun hm => ?_⟩
      rw [List.contains_iff_mem.2 hm] at hb
      exact absurd hb (by decide)
    · exact absurd h1 (by decide)
  have hvec0 : vecOf 0 = 0 := CFSG.GF2Type.Smith1979.GammaU.vecOf_zero
  have hne : ∀ p : ℕ, p < 4096 → p ≠ 0 → (Multiplicative.ofAdd (vecOf p) : W12) ≠ 1 := by
    intro p hp hp0 h1
    have h2 : vecOf p = vecOf 0 := by
      have h3 : Multiplicative.toAdd (Multiplicative.ofAdd (vecOf p) : W12) =
          Multiplicative.toAdd (1 : W12) := congrArg Multiplicative.toAdd h1
      rw [toAdd_ofAdd, toAdd_one] at h3
      rw [h3, hvec0]
    exact hp0 (vecOf_inj hp (by norm_num) h2)
  have hL : Nat.card ↥hjL0 = 604800 := by
    obtain ⟨e⟩ := hjL0_isSpor
    exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hstab : ∀ w : W12, Nat.card ↥(MulAction.stabilizer (MulAut W12) w ⊓ hjL0) =
      Nat.card ↥(MulAction.stabilizer ↥hjL0 w) := fun w =>
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
        invFun := fun l => ⟨l.1.1, l.2, l.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcard : ∀ p, p < 4096 → (∀ x ∈ orbitOf [HJ12.hjAc, HJ12.hjBc] p,
      ∀ g ∈ [HJ12.hjAc, HJ12.hjBc], appN g x ∈ orbitOf [HJ12.hjAc, HJ12.hjBc] p) →
      Nat.card ↥(MulAction.stabilizer (MulAut W12) (Multiplicative.ofAdd (vecOf p)) ⊓ hjL0) *
        (orbitOf [HJ12.hjAc, HJ12.hjBc] p).eraseDups.length = 604800 := by
    intro p hp hcl
    rw [hstab, ← HJBridge.ncard_orbit_hjL0 hp hcl, ← MulAction.index_stabilizer,
      Subgroup.card_mul_index, hL]
  have h384 : Nat.card ↥(MulAction.stabilizer (MulAut W12) hjV1 ⊓ hjL0) * 1575 = 604800 := by
    have h := hcard 4 (by norm_num) hcl1
    rwa [hl1] at h
  have h240 : Nat.card ↥(MulAction.stabilizer (MulAut W12) hjV2 ⊓ hjL0) * 2520 = 604800 := by
    have h := hcard 1024 (by norm_num) hcl2
    rwa [hl2] at h
  refine ⟨hne 4 (by norm_num) (by norm_num), hne 1024 (by norm_num) (by norm_num), ?_, ?_,
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 1575) (h384.trans (by norm_num)),
    Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2520) (h240.trans (by norm_num))⟩
  · intro v hv
    have hvn : v = Multiplicative.ofAdd (vecOf (codeOf (Multiplicative.toAdd v))) := by
      rw [CFSG.GF2Type.Smith1979.GammaU.vecOf_codeOf, ofAdd_toAdd]
    have hn0 : codeOf (Multiplicative.toAdd v) ≠ 0 := fun h0 => hv (by
      rw [hvn, h0, hvec0, ofAdd_zero])
    rcases hdisj _ (CFSG.GF2Type.Smith1979.GammaU.codeOf_lt _) hn0 with ⟨h1, -⟩ | ⟨-, h2⟩
    · left
      obtain ⟨l, hl, hlv⟩ :=
        (HJBridge.mem_orbit_iff (by norm_num) hcl1 (vecOf (codeOf (Multiplicative.toAdd v)))).2
          ⟨_, h1, rfl⟩
      exact ⟨l, hl, by rw [hvn]; exact hlv⟩
    · right
      obtain ⟨l, hl, hlv⟩ :=
        (HJBridge.mem_orbit_iff (by norm_num) hcl2 (vecOf (codeOf (Multiplicative.toAdd v)))).2
          ⟨_, h2, rfl⟩
      exact ⟨l, hl, by rw [hvn]; exact hlv⟩
  · rintro ⟨l, hl, hlv⟩
    obtain ⟨x, hx, hxe⟩ := (HJBridge.mem_orbit_iff (by norm_num) hcl1 (vecOf 1024)).1
      ⟨l⁻¹, inv_mem hl, by
        show l⁻¹ hjV2 = hjV1
        rw [← hlv, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]⟩
    have hx' : x = 1024 :=
      (vecOf_inj (HJBridge.lt_of_mem_orbitOf (by norm_num) hx) (by norm_num) hxe.symm)
    rw [hx'] at hx
    rcases hdisj 1024 (by norm_num) (by norm_num) with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2 (CFSG.GF2Type.Smith1979.GammaU.StepA.self_mem_orbitOf _ _)
    · exact h1 hx

theorem exists_gamma_of_gammaOK {aw : List (List ℕ)} {bw : List ℕ} {g : ℕ} {xw : List ℕ}
    (hok : HJ12.gammaOK aw bw g xw = true) :
    ∃ l ∈ hjL0, l hjV2 ∈ commSub
      (⨆ (a : MulAut W12) (_ : a ∈ grpOf (aw.map wordR)) (_ : a ≠ 1),
        fixV (Subgroup.zpowers a)) (grpOf (aw.map wordR)) := by
  simp only [HJ12.gammaOK, HJ12.gensL, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
    gensOKN_eq, CFSG.GF2Type.Smith1979.GammaU.StepA.native_closedCheck,
    CFSG.GF2Type.Smith1979.GammaU.native_enumGrp,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_idR,
    CFSG.GF2Type.Smith1979.GammaU.native_appN,
    CFSG.GF2Type.Smith1979.GammaU.StepA.native_orbitOf] at hok
  obtain ⟨⟨⟨⟨⟨⟨hg, hc⟩, hb⟩, hb1⟩, hfix⟩, hx⟩, horb⟩ := hok
  have hbA : hjWord bw ∈ grpOf (aw.map wordR) :=
    (HJBridge.mem_grpOf_iff hg hc _).2 ⟨_, List.contains_iff_mem.1 hb, HJBridge.rowsOf_hjWord bw⟩
  have hxA : hjWord xw ∈ grpOf (aw.map wordR) :=
    (HJBridge.mem_grpOf_iff hg hc _).2 ⟨_, List.contains_iff_mem.1 hx, HJBridge.rowsOf_hjWord xw⟩
  have hw : (Multiplicative.ofAdd (vecOf g) : W12) ∈ fixV (Subgroup.zpowers (hjWord bw)) := by
    rw [HJBridge.mem_fixV_zpowers_iff, HJBridge.rowsOf_hjWord bw,
      ← CFSG.GF2Type.Smith1979.GammaU.vecOf_appN, hfix]
  have hwΓ : (Multiplicative.ofAdd (vecOf g) : W12) ∈
      ⨆ (a : MulAut W12) (_ : a ∈ grpOf (aw.map wordR)) (_ : a ≠ 1),
        fixV (Subgroup.zpowers a) :=
    Subgroup.mem_iSup_of_mem (hjWord bw) (Subgroup.mem_iSup_of_mem hbA
      (Subgroup.mem_iSup_of_mem (hjWord_ne_one hb1) hw))
  have hval : hjWord xw (Multiplicative.ofAdd (vecOf g)) * (Multiplicative.ofAdd (vecOf g))⁻¹ =
      Multiplicative.ofAdd (vecOf (g ^^^ appN (wordR xw) g)) := by
    rw [HJBridge.rowsOf_hjWord xw, ← CFSG.GF2Type.Smith1979.GammaU.vecOf_appN,
      CFSG.GF2Type.Smith1979.GammaU.vecOf_xor]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
    funext i
    simp only [Pi.add_apply, Pi.neg_apply]
    generalize vecOf g i = a
    generalize vecOf (appN (wordR xw) g) i = b
    revert a b
    decide
  obtain ⟨l, hl, hlv⟩ := HJBridge.exists_of_mem_orbitOf (p := 1024) (by norm_num)
    (List.contains_iff_mem.1 horb)
  refine ⟨l, hl, ?_⟩
  rw [show hjV2 = Multiplicative.ofAdd (vecOf 1024) from rfl, hlv, ← hval]
  exact Subgroup.subset_closure ⟨_, hxA, _, hwΓ, rfl⟩

theorem hjGamma_facts :
    ∀ A ∈ ({hjA1, hjA2} : Set (Subgroup (MulAut W12))),
      ∃ l ∈ hjL0, l hjV2 ∈ commSub
        (⨆ (a : MulAut W12) (_ : a ∈ A) (_ : a ≠ 1), fixV (Subgroup.zpowers a)) A := by
  have h : HJ12.hjGammaCheck = true := HJ12.hjGammaCheck_eq
  simp only [HJ12.hjGammaCheck, Bool.and_eq_true] at h
  intro A hA
  rcases hA with rfl | rfl
  · exact exists_gamma_of_gammaOK h.1
  · exact exists_gamma_of_gammaOK h.2

theorem map_stab_inf_of_mem_normalizer {g : MulAut W12}
    (hg : g ∈ Subgroup.normalizer (hjL0 : Set (MulAut W12))) (v : W12) :
    (MulAction.stabilizer (MulAut W12) v ⊓ hjL0).map (MulAut.conj g).toMonoidHom =
      MulAction.stabilizer (MulAut W12) (g v) ⊓ hjL0 := by
  rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, ← MulAut.smul_def,
    MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  rw [show hjL0.map (MulEquiv.toMonoidHom (MulAut.conj g)) = hjL0 from
    Subgroup.mem_normalizer_iff_map_conj_eq.1 hg]

theorem card_stab_of_mem_normalizer {g : MulAut W12}
    (hg : g ∈ Subgroup.normalizer (hjL0 : Set (MulAut W12))) (v : W12) :
    Nat.card ↥(MulAction.stabilizer (MulAut W12) (g v) ⊓ hjL0) =
      Nat.card ↥(MulAction.stabilizer (MulAut W12) v ⊓ hjL0) := by
  rw [← map_stab_inf_of_mem_normalizer hg v,
    Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem mem_orbit_v2_iff
    {v : W12} (hv : v ≠ 1) :
    (∃ l ∈ hjL0, l v = hjV2) ↔
      Nat.card ↥(MulAction.stabilizer (MulAut W12) v ⊓ hjL0) = 240 := by
  obtain ⟨-, -, horb, -, h384, h240⟩ := hjOrbit_facts
  have hcard : ∀ {w w' : W12} {l : MulAut W12}, l ∈ hjL0 → l w = w' →
      Nat.card ↥(MulAction.stabilizer (MulAut W12) w ⊓ hjL0) =
        Nat.card ↥(MulAction.stabilizer (MulAut W12) w' ⊓ hjL0) := by
    intro w w' l hl hlw
    rw [← hlw]
    exact (card_stab_of_mem_normalizer (Subgroup.le_normalizer hl) w).symm
  constructor
  · rintro ⟨l, hl, hlv⟩
    rw [hcard hl hlv, h240]
  · intro h
    rcases horb v hv with ⟨l, hl, hlv⟩ | h2
    · rw [hcard hl hlv, h384] at h
      norm_num at h
    · exact h2

theorem exists_mem_hjL0_apply_eq_of_card
    {v w : W12}
    (hv : v ≠ 1) (hw : w ≠ 1)
    (hcv : Nat.card ↥(MulAction.stabilizer (MulAut W12) v ⊓ hjL0) = 240)
    (hcw : Nat.card ↥(MulAction.stabilizer (MulAut W12) w ⊓ hjL0) = 240) :
    ∃ m ∈ hjL0, m v = w := by
  obtain ⟨l₁, hl₁, h1⟩ := (mem_orbit_v2_iff hv).2 hcv
  obtain ⟨l₂, hl₂, h2⟩ := (mem_orbit_v2_iff hw).2 hcw
  refine ⟨l₂⁻¹ * l₁, mul_mem (inv_mem hl₂) hl₁, ?_⟩
  rw [MulAut.mul_apply, h1, ← h2, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]

theorem card_stab_conj_v2
    {g : MulAut W12}
    (hg : g ∈ Subgroup.normalizer (hjL0 : Set (MulAut W12))) {l : MulAut W12}
    (hl : l ∈ hjL0) :
    Nat.card ↥(MulAction.stabilizer (MulAut W12) (g (l hjV2)) ⊓ hjL0) = 240 := by
  rw [card_stab_of_mem_normalizer hg, card_stab_of_mem_normalizer (Subgroup.le_normalizer hl)]
  exact hjOrbit_facts.2.2.2.2.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
