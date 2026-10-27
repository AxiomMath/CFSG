module

public import CFSG.LocalAnalysis.StandardType.FS81.RootD6EltDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBFull
public import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic
public import CFSG.GroupTheory.TwoWeightData

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoTB

section

private theorem two_ne_zero_zmod_three : (2 : ZMod 3) ≠ 0 := by decide


private theorem nGen_mul_self (i : Fin 7) :
    nGen (ZMod 2) frameE7 i * nGen (ZMod 2) frameE7 i = 1 := by
  have hW : (WSL : SL2 (ZMod 2)) * WSL = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [WSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]
  rw [nGen, ← map_mul, hW, map_one]

private theorem isPGroup_closure_range_nGen :
    IsPGroup 2 (Subgroup.closure (Set.range (nGen (ZMod 2) frameE7))) := by
  let u : Fin 7 → ↥(adjointGroup .E7 (ZMod 2)) := fun i => nGen (ZMod 2) frameE7 i
  have hsq : ∀ s ∈ Set.range u, s ^ 2 = 1 := by
    rintro _ ⟨i, rfl⟩
    rw [pow_two]
    exact nGen_mul_self i
  have hcomm : ∀ s ∈ Set.range u, ∀ t ∈ Set.range u, s * t = t * s := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    by_cases hij : i = j
    · subst hij
      rfl
    · exact (commute_rho frameE7 hij WSL WSL).eq
  have hpow : ∀ g ∈ Subgroup.closure (Set.range u), g ^ 2 = 1 :=
    CFSG.GroupTheory.TwoWeights.closure_pow_eq_one (S := Set.range u) (n := 2) hsq hcomm
  change IsPGroup 2 (Subgroup.closure (Set.range u))
  refine IsPGroup.iff_orderOf.mpr fun q => ?_
  by_cases hq : q = 1
  · exact ⟨0, by rw [hq, orderOf_one, pow_zero]⟩
  · have hq2 : q ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hpow q q.2
    have hdvd : orderOf q ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hq2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hq
    · exact ⟨1, h⟩

private theorem nGen_conj_tE_update (i : Fin 7) (v : Fin 7 → ZMod 3) :
    nGen (ZMod 2) frameE7 i * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) *
        (nGen (ZMod 2) frameE7 i)⁻¹ =
      tE (ZMod 2) frameE7 (Multiplicative.ofAdd (Function.update v i (-v i))) := by
  refine (nGen_conj_tE (K := ZMod 2) (F := frameE7) i v).trans ?_
  refine congrArg (tE (ZMod 2) frameE7) ?_
  refine congrArg Multiplicative.ofAdd ?_
  funext j
  by_cases hji : j = i
  · subst hji
    rw [reflVec_apply_self]
    simp [Function.update]
    rfl
  · rw [reflVec_apply_of_ne hji]
    simp [Function.update, hji]

private theorem nGen_mem_normalizer_tE_range (i : Fin 7) :
    nGen (ZMod 2) frameE7 i ∈
      Subgroup.normalizer ((tE (ZMod 2) frameE7).range : Set _) := by
  haveI : Finite ↥((tE (ZMod 2) frameE7).range) :=
    Finite.Set.finite_range (tE (ZMod 2) frameE7)
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨w, rfl⟩ := hx
  refine ⟨Multiplicative.ofAdd (Function.update (Multiplicative.toAdd w) i
    (-(Multiplicative.toAdd w) i)), ?_⟩
  rw [show w = Multiplicative.ofAdd (Multiplicative.toAdd w) from (ofAdd_toAdd w).symm]
  exact (nGen_conj_tE_update i (Multiplicative.toAdd w)).symm

private theorem closure_range_nGen_le_normalizer_tE_range :
    Subgroup.closure (Set.range (nGen (ZMod 2) frameE7)) ≤
      Subgroup.normalizer ((tE (ZMod 2) frameE7).range : Set _) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact nGen_mem_normalizer_tE_range i

private theorem eq_single_of_forall_update_neg_eq_smul {v : Fin 7 → ZMod 3} (hv : v ≠ 0)
    (h : ∀ i : Fin 7, ∃ k : ZMod 3, Function.update v i (-v i) = k • v) :
    ∃ i₀ : Fin 7, v = Pi.single i₀ (v i₀) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hex : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  obtain ⟨i₀, hi₀⟩ := hex
  have hzero : ∀ j, j ≠ i₀ → v j = 0 := by
    intro j hj
    obtain ⟨k, hk⟩ := h j
    have hk₁ : k * v i₀ = v i₀ := by
      have h := congrFun hk i₀
      simp [Function.update, Pi.smul_apply, smul_eq_mul, Ne.symm hj] at h
      exact h.symm
    have hk_eq : k = 1 := by
      have h1 : k * v i₀ = 1 * v i₀ := by simpa using hk₁
      exact mul_right_cancel₀ hi₀ h1
    have hk₂ : -v j = v j := by
      have h := congrFun hk j
      simp [Function.update, Pi.smul_apply, smul_eq_mul, hk_eq] at h
      exact h
    have h2 : v j + v j = 0 := neg_eq_iff_add_eq_zero.mp hk₂
    have h3 : (2 : ZMod 3) * v j = 0 := by rwa [two_mul]
    exact (mul_eq_zero.mp h3).resolve_left two_ne_zero_zmod_three
  refine ⟨i₀, ?_⟩
  funext j
  by_cases hj : j = i₀
  · subst hj
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj, hzero j hj]

private theorem exists_conj_rho_mem_highRootSL2 (K : Type) [Field K]
    (i : Fin 7) (A : SL2 K) :
    ∃ n : ↥(adjointGroup .E7 K),
      ((n : ModGL .E7 K) * (rho K frameE7 i A : ModGL .E7 K) *
        (n : ModGL .E7 K)⁻¹) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K := by
  obtain ⟨w, hw⟩ := CFSG.SeitzReduction.EPilot.exists_smul_eq_highRoot (τ := .E7)
    (Or.inr (Or.inl rfl)) (frameE7.isRoot i)
  let n : ModGL .E7 K := canonicalRep (coxeterSystem .E7) K w
  have hn : n ∈ adjointGroup .E7 K :=
    canonicalRep_mem_adjointGroup (coxeterSystem .E7) K w
  have hmem : rootSL2 .E7 K (frameE7.root i) A ∈
      rootSubgroup .E7 K (frameE7.root i) ⊔ rootSubgroup .E7 K (-(frameE7.root i)) := by
    rw [← CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (frameE7.isRoot i)]
    exact ⟨A, rfl⟩
  have hmap : (rootSubgroup .E7 K (frameE7.root i) ⊔
        rootSubgroup .E7 K (-(frameE7.root i))).map (MulAut.conj n).toMonoidHom =
      CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K := by
    rw [Subgroup.map_sup, (canonical_weyl_root_transport .E7 K).2.1 w _ (frameE7.isRoot i),
      (canonical_weyl_root_transport .E7 K).2.1 w _ (IsRoot.neg (frameE7.isRoot i)),
      smul_neg, hw]
    rfl
  have hmem' : (MulAut.conj n).toMonoidHom (rootSL2 .E7 K (frameE7.root i) A) ∈
      CFSG.SeitzReduction.EPilot.highRootSL2 .E7 K := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ hmem
  refine ⟨⟨n, hn⟩, ?_⟩
  simpa [MulAut.conj_apply, coe_rho] using hmem'

private theorem tE_single_eq_rho (i : Fin 7) (c : ZMod 3) :
    tE (ZMod 2) frameE7 (Multiplicative.ofAdd (Pi.single i c)) =
      rho (ZMod 2) frameE7 i ((uSL 1 * vSL 1) ^ c.val) := by
  exact (tE_single frameE7 i c).trans
    (tC_apply_rho frameE7 i (Multiplicative.ofAdd c))

private theorem exists_eq_conj_tE_of_mem_map_conj {c a : ↥(adjointGroup .E7 (ZMod 2))}
    (ha : a ∈ (tE (ZMod 2) frameE7).range.map (MulAut.conj c).toMonoidHom)
    (ha1 : a ≠ 1) :
    ∃ v : Fin 7 → ZMod 3, v ≠ 0 ∧
      a = c * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) * c⁻¹ := by
  obtain ⟨t, ht, haeq⟩ := Subgroup.mem_map.mp ha
  obtain ⟨w, hw⟩ := ht
  let v : Fin 7 → ZMod 3 := Multiplicative.toAdd w
  have hwv : w = Multiplicative.ofAdd v := (ofAdd_toAdd w).symm
  refine ⟨v, ?_, ?_⟩
  · intro h0
    apply ha1
    rw [← haeq, ← hw, hwv]
    change c * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) * c⁻¹ = 1
    simp [v, h0]
  · rw [← haeq, ← hw, hwv]
    change c * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) * c⁻¹ =
      c * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) * c⁻¹
    rfl

private theorem exists_update_neg_eq_smul_of_mem_zpowers {v : Fin 7 → ZMod 3} (i : Fin 7)
    (h : nGen (ZMod 2) frameE7 i * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) *
          (nGen (ZMod 2) frameE7 i)⁻¹ ∈
        Subgroup.zpowers (tE (ZMod 2) frameE7 (Multiplicative.ofAdd v))) :
    ∃ k : ZMod 3, Function.update v i (-v i) = k • v := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hpow : tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) ^ m =
      tE (ZMod 2) frameE7 (Multiplicative.ofAdd (m • v)) := by
    rw [← map_zpow, ← ofAdd_zsmul]
  have hX : nGen (ZMod 2) frameE7 i * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) *
      (nGen (ZMod 2) frameE7 i)⁻¹ =
      tE (ZMod 2) frameE7 (Multiplicative.ofAdd (Function.update v i (-v i))) :=
    nGen_conj_tE_update i v
  have hvec : m • v = Function.update v i (-v i) :=
    tE_injective frameE7 (hpow.symm.trans (hm.trans hX))
  exact ⟨(m : ZMod 3), by rw [← hvec, Int.cast_smul_eq_zsmul]⟩

private theorem exists_update_neg_eq_smul_of_conj_normalizes
    {c a : ↥(adjointGroup .E7 (ZMod 2))} {v : Fin 7 → ZMod 3} (i : Fin 7)
    (ha : a = c * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) * c⁻¹)
    (hN : c * nGen (ZMod 2) frameE7 i * c⁻¹ ∈
      Subgroup.normalizer (Subgroup.zpowers a : Set _)) :
    ∃ k : ZMod 3, Function.update v i (-v i) = k • v := by
  have ha_mem : a ∈ Subgroup.zpowers a :=
    Subgroup.mem_zpowers_iff.mpr ⟨1, zpow_one a⟩
  have hconj : (c * nGen (ZMod 2) frameE7 i * c⁻¹) * a *
      (c * nGen (ZMod 2) frameE7 i * c⁻¹)⁻¹ ∈ Subgroup.zpowers a :=
    (Subgroup.mem_normalizer_iff.mp hN a).mp ha_mem
  have hX : nGen (ZMod 2) frameE7 i * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) *
      (nGen (ZMod 2) frameE7 i)⁻¹ ∈
      Subgroup.zpowers (tE (ZMod 2) frameE7 (Multiplicative.ofAdd v)) := by
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hconj
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨m, ?_⟩
    have h1 := congrArg (fun y => c⁻¹ * y * c) hm
    calc tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) ^ m = c⁻¹ * a ^ m * c := by
          rw [ha, conj_zpow]
          group
      _ = c⁻¹ * ((c * nGen (ZMod 2) frameE7 i * c⁻¹) * a *
            (c * nGen (ZMod 2) frameE7 i * c⁻¹)⁻¹) * c := h1
      _ = nGen (ZMod 2) frameE7 i * tE (ZMod 2) frameE7 (Multiplicative.ofAdd v) *
            (nGen (ZMod 2) frameE7 i)⁻¹ := by
          rw [ha]
          group
  exact exists_update_neg_eq_smul_of_mem_zpowers i hX

private theorem exists_conj_mem_highRootSL2_of_eq_conj_tE (i : Fin 7) (x : ZMod 3)
    {c a : ↥(adjointGroup .E7 (ZMod 2))}
    (ha : a = c * tE (ZMod 2) frameE7 (Multiplicative.ofAdd (Pi.single i x)) * c⁻¹) :
    ∃ g : ↥(adjointGroup .E7 (ZMod 2)),
      ((g * a * g⁻¹ : ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) ∈
        CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) := by
  obtain ⟨n, hn⟩ :=
    exists_conj_rho_mem_highRootSL2 (ZMod 2) i ((uSL 1 * vSL 1) ^ x.val)
  refine ⟨n * c⁻¹, ?_⟩
  have ht : tE (ZMod 2) frameE7 (Multiplicative.ofAdd (Pi.single i x)) =
      rho (ZMod 2) frameE7 i ((uSL 1 * vSL 1) ^ x.val) :=
    tE_single_eq_rho i x
  have hconj : (n * c⁻¹) * a * (n * c⁻¹)⁻¹ =
      n * tE (ZMod 2) frameE7 (Multiplicative.ofAdd (Pi.single i x)) * n⁻¹ := by
    rw [ha]
    group
  have hcoe : ((n * tE (ZMod 2) frameE7 (Multiplicative.ofAdd (Pi.single i x)) * n⁻¹ :
        ↥(adjointGroup .E7 (ZMod 2))) : ModGL .E7 (ZMod 2)) =
      (n : ModGL .E7 (ZMod 2)) *
        (rho (ZMod 2) frameE7 i ((uSL 1 * vSL 1) ^ x.val) : ModGL .E7 (ZMod 2)) *
        (n : ModGL .E7 (ZMod 2))⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ht]
  rw [hconj, hcoe]
  exact hn

theorem e7TorusRootLines_holds : E7TorusRootLines := by
  intro A hA hcard
  obtain ⟨c, hc⟩ := exists_conj_frame_of_card_E7 (K := ZMod 2) (Nat.card_zmod 2) hA
    (le_of_eq hcard.symm)
  refine ⟨(Subgroup.closure (Set.range (nGen (ZMod 2) frameE7))).map
    (MulAut.conj c).toMonoidHom, ?_, ?_, ?_⟩
  · exact isPGroup_closure_range_nGen.map (MulAut.conj c).toMonoidHom
  · calc (Subgroup.closure (Set.range (nGen (ZMod 2) frameE7))).map
          (MulAut.conj c).toMonoidHom
        ≤ (Subgroup.normalizer ((tE (ZMod 2) frameE7).range : Set _)).map
            (MulAut.conj c).toMonoidHom :=
          Subgroup.map_mono closure_range_nGen_le_normalizer_tE_range
      _ = Subgroup.normalizer (((tE (ZMod 2) frameE7).range).map
            (MulAut.conj c).toMonoidHom : Set _) :=
          Subgroup.map_equiv_normalizer_eq _ (MulAut.conj c)
      _ = Subgroup.normalizer (A : Set _) := by rw [← hc]
  · intro a ha ha1 hQN
    have ha' : a ∈ (tE (ZMod 2) frameE7).range.map (MulAut.conj c).toMonoidHom := hc ▸ ha
    obtain ⟨v, hv0, ha_eq⟩ := exists_eq_conj_tE_of_mem_map_conj ha' ha1
    have hupd : ∀ i : Fin 7, ∃ k : ZMod 3, Function.update v i (-v i) = k • v := by
      intro i
      have hqi : c * nGen (ZMod 2) frameE7 i * c⁻¹ ∈
          (Subgroup.closure (Set.range (nGen (ZMod 2) frameE7))).map
            (MulAut.conj c).toMonoidHom :=
        Subgroup.mem_map_of_mem _ (Subgroup.subset_closure (Set.mem_range_self i))
      exact exists_update_neg_eq_smul_of_conj_normalizes i ha_eq (hQN hqi)
    obtain ⟨i, hv⟩ := eq_single_of_forall_update_neg_eq_smul hv0 hupd
    have hPi : a = c * tE (ZMod 2) frameE7
        (Multiplicative.ofAdd (Pi.single i (v i))) * c⁻¹ := by
      conv_lhs => rw [ha_eq, hv]
    exact exists_conj_mem_highRootSL2_of_eq_conj_tE i (v i) hPi

end

end CFSG.StandardType.FrameRoute.FS81
