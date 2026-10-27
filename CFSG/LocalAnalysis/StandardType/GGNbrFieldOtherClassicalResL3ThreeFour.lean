module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3Three
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl2
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofAutSL
public import CFSG.Assembly.GL83StatedBridge
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma212InputsProofCore
public import CFSG.Open.StatedCenterThree

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.Quasithin

namespace L3Three

theorem exists_slHom_of_card_four
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) (L' : Type) [Group L'] [Finite L']
    (ψ : L' →* projectiveSL 3 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) (h3 : Nat.card ψ.ker ∣ 3) :
    ∃ φ : SpecialLinearGroup (Fin 3) K →* L', ∀ g, ψ (φ g) = proj 3 K g := by
  classical
  have hZ0 := CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (n := 3) (k := K) le_rfl
  have hZ : Subgroup.center L' = ψ.ker := by
    refine le_antisymm (fun z hz => ?_) hker
    rw [MonoidHom.mem_ker]
    have hzc : ψ z ∈ Subgroup.center (projectiveSL 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ0, Subgroup.mem_bot] at hzc
    exact hzc
  have hPSL : IsPSL 3 2 2 (L' ⧸ Subgroup.center L') := by
    have key : ∀ H : Subgroup (GL (Fin 3) K), H = StatedSL 3 K →
        Nonempty (LargeEvenProj H ≃* StatedProj (StatedSL 3 K)) := by
      rintro H rfl
      exact ⟨MulEquiv.refl _⟩
    obtain ⟨eS⟩ := key _ (largeEvenSLGroup_eq_statedSL 3)
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
      inferInstance, by rw [hK]; norm_num, ⟨?_⟩⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)).trans
        ((TypeA.recipeEquiv 3 K).symm.trans eS)
  have hodd : ∀ z ∈ Subgroup.center L', ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
    intro z hz k hk
    rw [hZ] at hz
    have h1 : orderOf z ∣ 3 := (Subgroup.orderOf_dvd_natCard ψ.ker hz).trans h3
    have h2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h4 : orderOf z ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
    rw [Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 3 2), Nat.dvd_one,
      orderOf_eq_one_iff] at h4
    exact h4
  obtain ⟨F, _, _, hF, hiso⟩ :=
    CFSG.Quasithin.H13.S126P31.exists_mulEquiv_psl_or_sl_of_quotient hperf hodd hPSL
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fintype F := Fintype.ofFinite F
  let τ : K ≃+* F := FiniteField.ringEquivOfCardEq (K := K) (K' := F) (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF])
  let mτ : SpecialLinearGroup (Fin 3) K →* SpecialLinearGroup (Fin 3) F :=
    SpecialLinearGroup.map τ.toRingHom
  have hmτ : Function.Surjective mτ := fun g => ⟨SpecialLinearGroup.map τ.symm.toRingHom g, by
    ext i j
    simp [mτ]⟩
  let eSL : SpecialLinearGroup (Fin 3) F ≃* StatedSL 3 F :=
    (TypeA.slKerEquiv 3 F).symm.trans (MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL 3))
  obtain ⟨β, hβ⟩ : ∃ β : SpecialLinearGroup (Fin 3) K →* L', Function.Surjective β := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      refine ⟨e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp (eSL.toMonoidHom.comp mτ)),
        e.symm.surjective.comp ((QuotientGroup.mk'_surjective _).comp
          (eSL.surjective.comp hmτ))⟩
    · obtain ⟨e⟩ := he
      exact ⟨e.symm.toMonoidHom.comp (eSL.toMonoidHom.comp mτ),
        e.symm.surjective.comp (eSL.surjective.comp hmτ)⟩
  have hZβ : scalars 3 K ≤ (ψ.comp β).ker := by
    intro s hs
    rw [scalars_eq_center] at hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    have hc : ψ (β s) ∈ Subgroup.center (projectiveSL 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨t, rfl⟩ := (hψ.comp hβ) y
      simp only [Function.comp_apply]
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hs t]
    rwa [hZ0, Subgroup.mem_bot] at hc
  let αbar : projectiveSL 3 K →* projectiveSL 3 K := QuotientGroup.lift (scalars 3 K) (ψ.comp β) hZβ
  have hαbar : ∀ s, αbar (proj 3 K s) = ψ (β s) := fun s => rfl
  have hαs : Function.Surjective αbar := by
    intro y
    obtain ⟨s, rfl⟩ := (hψ.comp hβ) y
    exact ⟨proj 3 K s, hαbar s⟩
  let α : MulAut (projectiveSL 3 K) :=
    MulEquiv.ofBijective αbar ⟨Finite.injective_iff_surjective.mpr hαs, hαs⟩
  obtain ⟨-, Ã, -, hÃ, -⟩ := CFSG.LocalAnalysis.RankFourTheoremC.l212in_lift_linear le_rfl α⁻¹
  refine ⟨β.comp Ã, fun g => ?_⟩
  rw [MonoidHom.comp_apply, ← hαbar, hÃ g]
  exact α.apply_symm_apply (proj 3 K g)

theorem ggTorusNoLineTwoKX_projectiveSL_four
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) :
    GGTorusNoLineTwoKX 3 (fun k => k ∣ 3) (projectiveSL 3 K) (Set.range (conjAut 3 K))
      (conjAut 3 K '' {B | IsReg (B : Matrix (Fin 3) (Fin 3) K)}) :=
  ggTorusNoLineTwoKX_projectiveSL_of_lift (by rw [hK]) fun L' _ _ ψ hψ hker hperf hKp =>
    exists_slHom_of_card_four hK L' ψ hψ hker hperf hKp

end L3Three

theorem largeEvenLabelAll_rowKX_l3ThreeFour {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .A ∧ lab.rank = 2 ∧ lab.n = 6) :
    LargeEvenLabelAll lab fun R _ I _ => (∀ g : R, MulAut.conj g ∈ I) ∧ GGTorusLift 3 0 R ∧
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusNoLineComp 3 0 R I ∧ GGCenterKp (fun k => k ∣ 3) R) := by
  obtain ⟨ht, hl, hn⟩ := h
  refine L3Three.largeEvenLabelAll_rowKX_of_dvd hlab ⟨ht, hl, ?_, ?_⟩ <;> rw [hn] <;> norm_num

theorem largeEvenLabelAll_fixKX_l3ThreeFour
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .A ∧ lab.rank = 2 ∧ lab.n = 6) :
    LargeEvenLabelAll lab (GGRawFieldFixKX 3 (fun k => k ∣ 3)) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn6⟩ := h
  dsimp only at ht hl hn6 ⊢
  subst ht hl hn6
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  exact ⟨K, inferInstance, inferInstance, hK, hQ', fun _ _ f hf hord =>
    L3Three.ggFixDataKX_linear_of_sub (by norm_num) hK (by norm_num)
      (fun K₀ _ _ _ hk => L3Three.ggTorusNoLineTwoKX_projectiveSL_four (by rw [hk]; norm_num))
      hf hord⟩

end CFSG.StandardType

end
