module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionDefs
public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenBasic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Core
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Quotient

variable {W : Type} [Group W] {p : ℕ} {H E : Subgroup W}

theorem GGControlsStrongFusion.map_mk' (h : GGControlsStrongFusion H E) (N : Subgroup W)
    [N.Normal] (hNH : N ≤ H) :
    GGControlsStrongFusion (H.map (QuotientGroup.mk' N)) (E.map (QuotientGroup.mk' N)) := by
  refine ggControlsStrongFusion_iff.mpr ⟨Subgroup.map_mono h.1, ?_⟩
  rintro _ ⟨e, he, rfl⟩ he1 g' hg'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N g'
  have he1' : e ≠ 1 := fun h1 => he1 (by rw [h1, map_one])
  have hmem : g⁻¹ * e * g ∈ (H.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) := by
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hg'
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNH] at hmem
  exact Subgroup.mem_map_of_mem _ (h.mem_of_conj_mem he he1' hmem)

theorem ggCard_map_mk'_of_inf_eq_bot (N : Subgroup W) [N.Normal] (hEN : E ⊓ N = ⊥) :
    Nat.card (E.map (QuotientGroup.mk' N)) = Nat.card E := by
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hxEN : (x : W) ∈ E ⊓ N := Subgroup.mem_inf.mpr ⟨x.2, hx⟩
    rw [hEN, Subgroup.mem_bot] at hxEN
    exact Subgroup.mem_bot.mpr (Subtype.ext hxEN)
  have hmap : E.map (QuotientGroup.mk' N) = ((QuotientGroup.mk' N).comp E.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hmap, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem ggExists_isMinimalNormal (Q : Type) [Group Q] [Finite Q] [Nontrivial Q] :
    ∃ M : Subgroup Q, ∃ _ : M.Normal, CFSG.IsMinimalNormal M ∧ M ≠ ⊥ := by
  classical
  have hex : ∃ k, ∃ M : Subgroup Q, M.Normal ∧ M ≠ ⊥ ∧ Nat.card M = k :=
    ⟨_, ⊤, inferInstance, top_ne_bot, rfl⟩
  obtain ⟨M, hMn, hM1, hMk⟩ := Nat.find_spec hex
  refine ⟨M, hMn, ⟨fun K _ hKM => ?_⟩, hM1⟩
  by_cases hK1 : K = ⊥
  · exact Or.inl hK1
  · right
    have hle := Nat.find_min' hex ⟨K, inferInstance, hK1, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hKM (by rw [hMk]; exact hle)

variable [Finite W]

theorem GGControlsStrongFusion.eq_top_of_le_of_isSolvable (hp : p.Prime)
    (h : GGControlsStrongFusion H E) (hE : IsElemAbelian p E) (hEcard : Nat.card E = p ^ 2)
    {K : Subgroup W} [K.Normal] (hKH : K ≤ H) (hsolv : Group.IsSolvable (W ⧸ K)) : H = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hH
  set N := H.normalCore with hNdef
  have : N.Normal := Subgroup.normalCore_normal H
  have hNH : N ≤ H := Subgroup.normalCore_le H
  have hKN : K ≤ N := (Subgroup.normal_le_normalCore).mpr hKH
  by_cases hEN : E ⊓ N = ⊥
  swap
  ·
    apply hH
    obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hEN
    have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
    obtain ⟨heE, heN⟩ := Subgroup.mem_inf.mp he
    rw [eq_top_iff]
    intro g _
    refine h.mem_of_conj_mem heE he1' (hNH ?_)
    have h' := (Subgroup.normalCore_normal H).conj_mem e heN g⁻¹
    rwa [inv_inv] at h'
  have hNtop : N ≠ ⊤ := fun hN => hH (top_le_iff.mp (hN ▸ hNH))
  have : Nontrivial (W ⧸ N) := QuotientGroup.nontrivial_iff.mpr hNtop
  have hQsolv : Group.IsSolvable (W ⧸ N) := by
    have hle : K ≤ N.comap (MonoidHom.id W) := hKN
    exact Group.isSolvable_of_surjective (f := QuotientGroup.map K N (MonoidHom.id W) hle)
      (QuotientGroup.map_surjective_of_surjective K N (MonoidHom.id W)
        (QuotientGroup.mk_surjective) hle)
  set π := QuotientGroup.mk' N
  have hfus : GGControlsStrongFusion (H.map π) (E.map π) := h.map_mk' N hNH
  have hEel : IsElemAbelian p (E.map π) := ggIsElemAbelian_map hE π
  have hEcard' : Nat.card (E.map π) = p ^ 2 := by
    rw [ggCard_map_mk'_of_inf_eq_bot N hEN, hEcard]
  obtain ⟨M, hMn, hMmin, hM1⟩ := ggExists_isMinimalNormal (W ⧸ N)
  have : Group.IsSolvable M := inferInstance
  obtain ⟨q, hq, hel⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian M
  have : CFSG.IsElementaryAbelian q M := hel
  have hMq : IsPGroup q M := CFSG.IsElementaryAbelian.isPGroup q M
  have : Fact q.Prime := ⟨hq⟩
  have hMH : M ≤ H.map π := by
    by_cases hqp : q = p
    · subst hqp
      obtain ⟨e, he, he1⟩ := ggExists_ne_one_of_card hp hEcard'
      have hR : IsPGroup q ↥(M ⊔ Subgroup.zpowers e) :=
        IsPGroup.to_sup_of_normal_left hMq (ggIsPGroup_zpowers (hEel.2 e he))
      exact le_sup_left.trans (hfus.le_of_isPGroup he he1 hR
        (le_sup_right (a := M) (Subgroup.mem_zpowers e)))
    · refine hfus.le_of_coprime hp hEel hEcard' ?_ Subgroup.le_normalizer_of_normal
      intro hdvd
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hMq
      rw [hn] at hdvd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hdvd)).symm
  have hcomapH : (H.map π).comap π = H := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hNH]
  have hMcomap : (M.comap π).Normal := Subgroup.Normal.comap hMn π
  have hle : M.comap π ≤ N :=
    (Subgroup.normal_le_normalCore).mpr ((Subgroup.comap_mono hMH).trans hcomapH.le)
  apply hM1
  rw [eq_bot_iff, ← Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) M]
  rintro _ ⟨x, hx, rfl⟩
  exact (QuotientGroup.eq_one_iff x).mpr (hle hx)

end Quotient

section Schreier

theorem ggEq_one_of_commute_generalizedFitting {W : Type} [Group W] [Finite W]
    (hsimple : IsSimpleGroup ↥(CFSG.generalizedFitting W))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a) {w : W}
    (hw : ∀ k ∈ CFSG.generalizedFitting W, w * k = k * w) : w = 1 := by
  set K := CFSG.generalizedFitting W
  have hwC : w ∈ Subgroup.centralizer (K : Set W) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => (hw k hk).symm
  have hwK : w ∈ K := CFSG.centralizer_generalizedFitting_le W hwC
  have hZ : (⟨w, hwK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hw g g.2).symm
  have hcenter : Subgroup.center K = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
    · exact h
    · obtain ⟨a, b, hab⟩ := hnab
      exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
  rw [hcenter, Subgroup.mem_bot] at hZ
  exact congrArg Subtype.val hZ

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem ggIsSolvable_quot_generalizedFitting {W : Type} [Group W] [Finite W]
    (hsimple : IsSimpleGroup ↥(CFSG.generalizedFitting W))
    (hnab : ∃ a b : ↥(CFSG.generalizedFitting W), a * b ≠ b * a)
    (hout : Group.IsSolvable (Outer ↥(CFSG.generalizedFitting W))) :
    have : (CFSG.generalizedFitting W).Normal := CFSG.LocalCores.generalized_fitting_characteristic.2
    Group.IsSolvable (W ⧸ CFSG.generalizedFitting W) := by
  intro hKn
  set K := CFSG.generalizedFitting W
  have hcent : ∀ w : W, (∀ k ∈ K, w * k = k * w) → w = 1 :=
    fun _ hw => ggEq_one_of_commute_generalizedFitting hsimple hnab hw
  let Φ : W →* Outer K := (QuotientGroup.mk' (inner K)).comp (MulAut.conjNormal (H := K))
  have hker : Φ.ker ≤ K := by
    intro w hw
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hw
    obtain ⟨k, hk⟩ := hw
    have hwk : (k : W)⁻¹ * w = 1 := by
      refine hcent _ fun x hx => ?_
      have h1 := congrArg Subtype.val (DFunLike.congr_fun hk ⟨x, hx⟩)
      rw [MulAut.conjNormal_apply, MulAut.conj_apply] at h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
      calc (k : W)⁻¹ * w * x = (k : W)⁻¹ * (w * x * w⁻¹) * w := by group
        _ = (k : W)⁻¹ * ((k : W) * x * (k : W)⁻¹) * w := by rw [← h1]
        _ = x * ((k : W)⁻¹ * w) := by group
    have hw' : w = k := by
      calc w = (k : W) * ((k : W)⁻¹ * w) := by group
        _ = k := by rw [hwk, mul_one]
    rw [hw']
    exact k.2
  have hOsolv : Group.IsSolvable Φ.range := inferInstance
  have hQ : Group.IsSolvable (W ⧸ Φ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.quotientKerEquivRange Φ).injective
  have hle : Φ.ker ≤ K.comap (MonoidHom.id W) := hker
  exact Group.isSolvable_of_surjective (f := QuotientGroup.map Φ.ker K (MonoidHom.id W) hle)
    (QuotientGroup.map_surjective_of_surjective Φ.ker K (MonoidHom.id W)
      (QuotientGroup.mk_surjective) hle)

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggHypThreeSixteen_eq_top_of_le (hSch : SchreierFor InCatalog) {W : Type} [Group W]
    [Finite W] {p : ℕ} {H E : Subgroup W} (hyp : GGHypThreeSixteen p H E)
    (hKH : CFSG.generalizedFitting W ≤ H) : H = ⊤ := by
  obtain ⟨⟨hp, -, hE, hEcard, hfus⟩, ⟨hsimple, hnab, hcat⟩, -⟩ := hyp
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  have : IsSimpleGroup ↥(CFSG.generalizedFitting W) := hsimple
  have hout := hSch _ hnab hcat
  exact hfus.eq_top_of_le_of_isSolvable hp hE hEcard hKH
    (ggIsSolvable_quot_generalizedFitting hsimple hnab hout)

open CFSG.LocalAnalysis.ComponentInitial in
theorem ggKGroupFusionLayerInput_of_at (hSch : SchreierFor InCatalog)
    (h : GGKGroupFusionAt fun _ _ => True) : GGKGroupFusionLayerInput := by
  intro W _ _ p H E hyp hL
  by_cases hKH : CFSG.generalizedFitting W ≤ H
  · exact Or.inl (ggHypThreeSixteen_eq_top_of_le hSch hyp hKH)
  · obtain ⟨i, he⟩ := hyp.2.1.2.2
    exact Or.inr (h W p H E i trivial hyp hL hKH he)

end Schreier

end CFSG.StandardType
