module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUInShapeBasic

public section

namespace CFSG.StandardType

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CoordSU CoordSUIn Multiplicative

theorem ggSUPieceShapeInput_holds : GGSUPieceShapeInput := by
  intro G _ _ f n K _ h p A hA F hFm hr φ hker E J hE hJ hcard
  classical
  have : Finite K := h.finite
  have hp := hA.prime
  have : Fact p.Prime := ⟨hp⟩
  have hpq := hA.not_dvd
  have hιinj : Function.Injective (φ.comp F.ι) := injective_comp_ι hA F hker
  have hlt : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  obtain ⟨T, hT⟩ : ∃ T : Set (Fin F.r → ZMod p), ∀ t, t ∈ T ↔ (φ.comp F.ι) (ofAdd t) ∈ E :=
    ⟨{t | (φ.comp F.ι) (ofAdd t) ∈ E}, fun _ => Iff.rfl⟩
  by_cases hZ0 : ∃ k, ∀ t ∈ T, t k = 0
  · obtain ⟨k, hk⟩ := hZ0
    exact Or.inl ⟨k, fun t ht => hk t ((hT t).mpr ht)⟩
  push Not at hZ0
  have hTsub : ∀ t ∈ T, ∀ t₀ ∈ T, ∀ a : ZMod p, t - a • t₀ ∈ T := fun t ht t₀ ht₀ a =>
    (hT _).mpr (CoordShape.sub_smul_mem ((hT t).mp ht) ((hT t₀).mp ht₀) a)
  have hMc : ∀ Y : ↥(unitarySU 2 f K n), φ Y ∈ φ.range ⊓ Subgroup.centralizer (E : Set G) →
      ∀ t ∈ T, Y * F.ι (ofAdd t) = F.ι (ofAdd t) * Y := by
    intro Y hY t ht
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hY).2 _ ((hT t).mp ht)
    exact (SUNS.commute_of_frame_commute h hker hp hpq (a := F.ι (ofAdd t)) (s := Y)
      (hA.pow _ (ι_mem F _)) h1).symm
  set H := φ.range ⊓ Subgroup.centralizer (E : Set G) with hHdef
  have hHle : H ≤ φ.range := inf_le_left
  have hN₀ : (((fixSU (cvA F)).map φ ⊓ H).subgroupOf H).Normal :=
    normal_fixSU hHle fun Y hY v hv => lin_mem_cvA hZ0 (hMc Y hY) hv
  have hNk : ∀ k, (((fixSU (classSpace F (negQ p (2 ^ f)) T k)).map φ ⊓ H).subgroupOf H).Normal :=
    fun k => normal_fixSU hHle fun Y hY v hv => lin_mem_classSpace hA hFm hTsub hZ0 (hMc Y hY) hv
  have htorH : ∀ s : Fin F.r → ZMod p, (φ.comp F.ι) (ofAdd s) ∈ H := by
    intro s
    refine Subgroup.mem_inf.mpr ⟨⟨F.ι (ofAdd s), rfl⟩,
      Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    obtain ⟨a, rfl⟩ := hE he
    rw [← map_mul, ← map_mul, mul_comm]
  have htorN₀ : ∀ s : Fin F.r → ZMod p, (φ.comp F.ι) (ofAdd s) ∈ (fixSU (cvA F)).map φ ⊓ H :=
    fun s => Subgroup.mem_inf.mpr ⟨⟨F.ι (ofAdd s), fun v hv => lin_ι_apply_of_cvA F _ hv, rfl⟩,
      htorH s⟩
  have htorNk : ∀ k (s : Fin F.r → ZMod p), (∀ l, ORel (negQ p (2 ^ f)) T k l → s l = 0) →
      (φ.comp F.ι) (ofAdd s) ∈ (fixSU (classSpace F (negQ p (2 ^ f)) T k)).map φ ⊓ H := by
    intro k s hs
    refine Subgroup.mem_inf.mpr ⟨⟨F.ι (ofAdd s), fun v hv => ?_, rfl⟩, htorH s⟩
    obtain ⟨-, hvX⟩ := hv
    refine (F.ι_fix _ v).mpr fun j hj => hvX j fun hkj => hj ?_
    rw [toAdd_ofAdd]
    exact hs j hkj
  have hdich : ∀ N : Subgroup G, N ≤ H → (N.subgroupOf H).Normal → J ≤ N ∨ ⁅J, N⁆ = ⊥ :=
    fun N hNH hN => CoordSL.le_or_commutator_eq_bot_of_normal hJ hNH hN
  by_cases hcase : ∃ k₀, ⁅J, (fixSU (classSpace F (negQ p (2 ^ f)) T k₀)).map φ ⊓ H⁆ = ⊥
  ·
    obtain ⟨k₀, hk₀⟩ := hcase
    have hCJ : ∀ u : Fin F.r → ZMod p, (∀ l, ORel (negQ p (2 ^ f)) T k₀ l → u l = 0) →
        (φ.comp F.ι) (ofAdd u) ∈ (φ.comp F.ι).range ⊓ Subgroup.centralizer (J : Set G) :=
      fun u hu => Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩,
        mem_centralizer_of_commutator_eq_bot hk₀ (htorNk k₀ u hu)⟩
    have hEJ : ∀ t ∈ T, (φ.comp F.ι) (ofAdd t) ∈
        (φ.comp F.ι).range ⊓ Subgroup.centralizer (J : Set G) := by
      intro t ht
      refine Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun a ha => ?_⟩
      have h1 := (Subgroup.mem_inf.mp (hJ.1 ha)).2
      exact ((Subgroup.mem_centralizer_iff.mp h1) _ ((hT t).mp ht)).symm
    obtain ⟨t₀, ht₀, ht₀k⟩ := hZ0 k₀
    have hcov : ∃ j₁ j₂, ∀ l, ¬ ORel (negQ p (2 ^ f)) T k₀ l → l = j₁ ∨ l = j₂ := by
      refine exists_cover_two (fun l => ¬ ORel (negQ p (2 ^ f)) T k₀ l)
        (fun a b c hab hac hbc ha hb hc => ?_) k₀
      have hak : a ≠ k₀ := fun h' => ha (by rw [h']; exact ORel.refl k₀)
      have hbk : b ≠ k₀ := fun h' => hb (by rw [h']; exact ORel.refl k₀)
      have hck : c ≠ k₀ := fun h' => hc (by rw [h']; exact ORel.refl k₀)
      have hvmem : (φ.comp F.ι)
          (ofAdd fun j => if ORel (negQ p (2 ^ f)) T k₀ j then t₀ j else 0) ∈
          (φ.comp F.ι).range ⊓ Subgroup.centralizer (J : Set G) := by
        have h1 : (fun j => if ORel (negQ p (2 ^ f)) T k₀ j then t₀ j else 0) =
            t₀ - fun j => if ORel (negQ p (2 ^ f)) T k₀ j then 0 else t₀ j := by
          funext j
          simp only [Pi.sub_apply]
          split_ifs <;> ring
        rw [h1, ofAdd_sub, _root_.map_div]
        exact Subgroup.div_mem _ (hEJ t₀ ht₀)
          (hCJ _ fun l hl => ite_eq_left_iff.mpr fun h' => absurd hl h')
      have hwc : ∀ x y : Fin 4,
          (![Pi.single a 1, Pi.single b 1, Pi.single c 1,
            (t₀ k₀)⁻¹ • fun j => if ORel (negQ p (2 ^ f)) T k₀ j then t₀ j else 0] :
              Fin 4 → Fin F.r → ZMod p) x (![a, b, c, k₀] y) = if x = y then 1 else 0 := by
        intro x y
        fin_cases x <;> fin_cases y <;>
          simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm, hak.symm, hbk.symm, hck.symm, ha,
            hb, hc, ORel.refl, ht₀k]
      have hwm : ∀ x : Fin 4, (φ.comp F.ι) (ofAdd
          ((![Pi.single a 1, Pi.single b 1, Pi.single c 1,
            (t₀ k₀)⁻¹ • fun j => if ORel (negQ p (2 ^ f)) T k₀ j then t₀ j else 0] :
              Fin 4 → Fin F.r → ZMod p) x)) ∈
          (φ.comp F.ι).range ⊓ Subgroup.centralizer (J : Set G) := by
        have hsingle : ∀ l, ¬ ORel (negQ p (2 ^ f)) T k₀ l → (φ.comp F.ι) (ofAdd (Pi.single l 1)) ∈
            (φ.comp F.ι).range ⊓ Subgroup.centralizer (J : Set G) := fun l hl =>
          hCJ _ fun j hj => Pi.single_eq_of_ne (fun h' : j = l => hl (by subst h'; exact hj)) 1
        intro x
        fin_cases x
        · exact hsingle a ha
        · exact hsingle b hb
        · exact hsingle c hc
        · exact StepTwoToral.ofAdd_smul_mem hvmem _
      have h4 := CoordShape.pow_four_le_of_dual hιinj _ _ hwc (ofAdd_sum_smul_mem _ hwm)
      omega
    obtain ⟨j₁, j₂, hj⟩ := hcov
    have hrel : ∀ l, ∃ c : (ZMod p)ˣ, c ∈ negQ p (2 ^ f) ∧
        (ORel (negQ p (2 ^ f)) T k₀ l → ∀ t ∈ T, t l = (c : ZMod p) * t k₀) := by
      intro l
      by_cases hl : ORel (negQ p (2 ^ f)) T k₀ l
      · obtain ⟨c, hcO, hc⟩ := hl
        exact ⟨c, hcO, fun _ => hc⟩
      · exact ⟨1, (negQ p (2 ^ f)).one_mem, fun h' => absurd h' hl⟩
    choose ε hεO hε using hrel
    refine Or.inr ⟨j₁, j₂, ε, hεO, fun s hs => ⟨s k₀, fun l hl1 hl2 => ?_⟩⟩
    have hl : ORel (negQ p (2 ^ f)) T k₀ l := by
      by_contra h'
      rcases hj l h' with h'' | h''
      · exact hl1 h''
      · exact hl2 h''
    exact hε l hl s ((hT s).mpr hs)
  · push Not at hcase
    have hJk : ∀ k, J ≤ (fixSU (classSpace F (negQ p (2 ^ f)) T k)).map φ ⊓ H := fun k =>
      (hdich _ inf_le_right (hNk k)).resolve_right (hcase k)
    exfalso
    rcases hdich _ inf_le_right hN₀ with hJ0 | hJ0
    ·
      have hscal : ∀ a ∈ J, ∃ Z : ↥(unitarySU 2 f K n), φ Z = a ∧ (∀ v ∈ cvA F, lin Z v = v) ∧
          ∀ l, ∃ c : K, ∀ u ∈ rng (F.y l), lin Z u = c • u := by
        intro a ha
        obtain ⟨⟨Z, hZ, hZa⟩, -⟩ := Subgroup.mem_inf.mp (hJ0 ha)
        refine ⟨Z, hZa, hZ, fun l => ?_⟩
        obtain ⟨⟨Z', hZ', hZ'a⟩, -⟩ := Subgroup.mem_inf.mp (hJk l ha)
        have hk1 : φ (Z⁻¹ * Z') = 1 := by rw [map_mul, map_inv, hZa, hZ'a, inv_mul_cancel]
        obtain ⟨c, hc⟩ := hker _ hk1
        have hlin : ∀ v, lin (Z⁻¹ * Z') v = c • v := fun v => by
          rw [lin_apply]
          change (((Z⁻¹ * Z' : ↥(unitarySU 2 f K n)) : GL (Fin n) K) :
            Matrix (Fin n) (Fin n) K) *ᵥ v = c • v
          rw [hc]
          funext x
          simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
        refine ⟨c⁻¹, fun u hu => ?_⟩
        have hu' : lin Z' u = u := hZ' u (mem_classSpace_of_rel (ORel.refl l) hu)
        have h2 : lin Z' u = c • lin Z u := by
          have e : Z' = Z * (Z⁻¹ * Z') := by group
          rw [e, lin_mul, Module.End.mul_apply, hlin, map_smul]
        rw [hu'] at h2
        by_cases hc0 : c = 0
        · rw [hc0, zero_smul] at h2
          rw [h2, map_zero, smul_zero]
        · conv_rhs => rw [h2]
          rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
      refine LinSemisimple.false_of_isQuasisimple_of_commute hJ.2.2 fun x hx y hy => ?_
      obtain ⟨Z, rfl, hZ0, hZs⟩ := hscal x hx
      obtain ⟨Z', rfl, hZ'0, hZ's⟩ := hscal y hy
      rw [← map_mul, ← map_mul]
      congr 1
      refine eq_of_lin_apply fun v => ?_
      rw [lin_mul Z Z', lin_mul Z' Z]
      obtain ⟨w, hw, -, hv⟩ := exists_decomp_pieces hA F v
      have e : v = (v - ∑ l, w l) + ∑ l, w l := by abel
      calc (lin Z * lin Z') v = (lin Z * lin Z') ((v - ∑ l, w l) + ∑ l, w l) := by rw [← e]
        _ = (lin Z' * lin Z) ((v - ∑ l, w l) + ∑ l, w l) := by
          rw [map_add, map_add, map_sum, map_sum]
          congr 1
          · simp only [Module.End.mul_apply]
            rw [hZ'0 _ hv, hZ0 _ hv, hZ'0 _ hv]
          · refine Finset.sum_congr rfl fun l _ => ?_
            obtain ⟨c₁, hc₁⟩ := hZs l
            obtain ⟨c₂, hc₂⟩ := hZ's l
            simp only [Module.End.mul_apply]
            rw [hc₂ _ (hw l), map_smul, hc₁ _ (hw l), map_smul, hc₂ _ (hw l), smul_smul,
              smul_smul, mul_comm]
        _ = (lin Z' * lin Z) v := by rw [← e]
    ·
      have hall : ∀ u : Fin F.r → ZMod p, (φ.comp F.ι) (ofAdd u) ∈
          (φ.comp F.ι).range ⊓ Subgroup.centralizer (J : Set G) := fun u =>
        Subgroup.mem_inf.mpr ⟨⟨_, rfl⟩, mem_centralizer_of_commutator_eq_bot hJ0 (htorN₀ u)⟩
      have h4 := CoordShape.pow_four_le_of_dual hιinj
        (H := (φ.comp F.ι).range ⊓ Subgroup.centralizer (J : Set G))
        (fun a => Pi.single (Fin.castLE hr a) 1) (Fin.castLE hr) (fun a b => by
          simp only [Pi.single_apply, (Fin.castLE_injective hr).eq_iff]
          by_cases hab : a = b
          · simp [hab]
          · simp [hab, Ne.symm hab]) fun x => hall _
      omega

end CFSG.StandardType
