module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeBOddIndex
import CFSG.HardMathSupport.Timmesfeld.LangTorus.GoodRankOne
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.RankThree.Chevalley.SteinbergBIRootSL2Tools
import CFSG.LieType.Chevalley.SignKernelComponentBorel
import CFSG.Blueprint.ChevalleyPinnedLemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferS3

public section

namespace CFSG.StandardType.GGK0LQ

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem lk0xlqs3_pinnedX_sq_of_two_eq_zero {τ : Tag} {L : Type} [Field L]
    (h2 : (2 : L) = 0) (γ : Fin τ.rank → ℤ) (c : L) :
    (pinnedX τ L γ c) ^ 2 = 1 := by
  have hcc : c + c = 0 := by rw [← two_mul, h2, zero_mul]
  rw [sq, ← pinnedX_add, hcc, pinnedX_zero]

private theorem lk0xlqs3_rationalRoots_eq_of_image_eq {τ : Tag} {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ) (i : KernelComponent χ)
    (hρ : (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) '' componentRoots χ i =
      componentRoots χ i) :
    rationalRoots ρ χ i = componentRoots χ i := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => simpa using hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact hρ ▸ Set.mem_image_of_mem ρ ih
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

theorem lq_span_s3
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hp : p.Prime)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hTp : rootDiagUnit τ a ^ p = 1)
    (ha1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hkind : twistKind S.ρ (rootCharHom a) i = .inner) (hp5 : τ = .G2 → 5 ≤ p)
    (hQ : S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2)
    (hrank : ∀ α ∈ componentRoots (rootCharHom a) i, ∀ δ ∈ componentRoots (rootCharHom a) i,
      δ = α ∨ δ = -α)
    (hInv : ∀ m ∈ S.D.model, m ^ 2 = 1 → m ∈ S.Γ) :
    Nonempty (rationalSpan S.ρ S.Γ (rootCharHom a) i ≃* Equiv.Perm (Fin 3)) := by
  classical
  obtain ⟨x, hx⟩ := Quotient.exists_rep i
  have hβmem : x.1 ∈ componentRoots (rootCharHom a) i := ⟨x.2, hx⟩
  have hβroot : IsRoot τ x.1 := isRoot_of_mem_componentRoots hβmem
  have hnegmem : -x.1 ∈ componentRoots (rootCharHom a) i :=
    (isRootComponent_componentRoots i).neg_mem x.1 hβmem
  have hΨeq : componentRoots (rootCharHom a) i = {x.1, -x.1} := by
    ext δ
    constructor
    · intro hδ
      rcases hrank x.1 hβmem δ hδ with h | h
      · exact Or.inl h
      · exact Or.inr h
    · intro hδ
      rcases hδ with h | h
      · rwa [h]
      · rw [h]; exact hnegmem
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  have hqge : 2 ≤ S.D.q := S.hqpow.1.two_le
  have hq_dvd : S.D.q ∣ 2 := by
    rw [← hQ]
    exact dvd_pow_self S.D.q hs0.ne'
  have hq2 : S.D.q = 2 :=
    ((Nat.prime_two.dvd_iff_eq (by omega : S.D.q ≠ 1)).1 hq_dvd).symm
  have hs1 : componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
    have h2s : 2 ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 2 ^ 1 := by
      rw [pow_one]
      rw [← hq2, hQ, hq2]
    exact Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h2s
  have hρΨ : (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)) ''
      componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i := by
    have h := hs
    rw [hs1] at h
    simpa using h
  have hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[1]) := by
    have h := twistInner_of_twistKind_eq_innerT S
      CFSG.HardMathSupport.Timmesfeld.RootAut.rootAutIsWeyl_holds hT i hkind
    rwa [hs1] at h
  obtain ⟨σ, z, hσ2, hY0⟩ :=
    CFSG.StandardType.TwE6ThreeB.exists_rootSpan_inf_model_eq_map_CQ S hq2 hT i hinner
  set T := (CQ σ i).map (MulAut.conj z).toMonoidHom with hTdef
  have hY : rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model = T := by
    rw [hTdef]; exact hY0
  have hrat : rationalRoots S.ρ (rootCharHom a) i = componentRoots (rootCharHom a) i :=
    lk0xlqs3_rationalRoots_eq_of_image_eq S.ρ (rootCharHom a) i hρΨ
  have hRat : rationalSpan S.ρ S.Γ (rootCharHom a) i =
      rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.Γ := by
    rw [rationalSpan, hrat]
  have h2L : (2 : L) = 0 := by
    have h := S.hqpow.2
    rwa [hq2] at h
  have hCQ_le_Γ : CQ σ i ≤ S.Γ.comap (MulAut.conj z).toMonoidHom := by
    unfold CQ
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨γ, hγ, c, hc, rfl⟩
    rw [unionRoots_singleton] at hγ
    have hgenT : z * pinnedX τ L γ c * z⁻¹ ∈ T := by
      refine ⟨pinnedX τ L γ c, ?_, ?_⟩
      · exact pinnedX_mem_CQ (by rw [unionRoots_singleton]; exact hγ) hc
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hgenM : z * pinnedX τ L γ c * z⁻¹ ∈
        rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model := hY.symm ▸ hgenT
    have hsq : (z * pinnedX τ L γ c * z⁻¹) ^ 2 = 1 := by
      have hconj : (z * pinnedX τ L γ c * z⁻¹) ^ 2 =
          z * (pinnedX τ L γ c) ^ 2 * z⁻¹ := by
        rw [show z * pinnedX τ L γ c * z⁻¹ = MulAut.conj z (pinnedX τ L γ c) by
          simp only [MulAut.conj_apply], ← map_pow, MulAut.conj_apply]
      rw [hconj, lk0xlqs3_pinnedX_sq_of_two_eq_zero h2L γ c]
      group
    change (MulAut.conj z).toMonoidHom (pinnedX τ L γ c) ∈ S.Γ
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hInv _ hgenM.2 hsq
  have hT_le_Γ : T ≤ S.Γ := by
    intro t ht
    obtain ⟨g, hg, rfl⟩ := ht
    exact hCQ_le_Γ hg
  have hT_le_rootSpan : T ≤ rootSpan τ L (componentRoots (rootCharHom a) i) := by
    intro t ht
    exact (hY.symm ▸ ht).1
  have hRatT : rationalSpan S.ρ S.Γ (rootCharHom a) i = T := by
    rw [hRat]
    refine le_antisymm ?_ ?_
    · intro w hw
      have hwM : w ∈ rootSpan τ L (componentRoots (rootCharHom a) i) ⊓ S.D.model :=
        ⟨hw.1, S.Γ_le_model hw.2⟩
      rwa [hY] at hwM
    · intro w hw
      exact ⟨hT_le_rootSpan hw, hT_le_Γ hw⟩
  have hC : componentRootSpan (fixSubfield σ) (rootCharHom a) i =
      (rootSL2 τ (fixSubfield σ) x.1).range := by
    rw [CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot hβroot]
    show rootSpan τ (fixSubfield σ) (componentRoots (rootCharHom a) i) = _
    rw [hΨeq]
    simp only [rootSpan, iSup_insert, iSup_singleton]
  have hσq : ∀ c, σ c = c ^ (S.D.q ^ 1) := by
    intro c
    rw [hq2, pow_one]
    exact hσ2 c
  obtain ⟨hfinK, hKcard⟩ := exists_fixSubfield_fintype (S := S) (m := 1) one_pos hσq
  have hK2 : Nat.card (fixSubfield σ) = 2 := by rw [hKcard, hq2, pow_one]
  haveI : Finite (fixSubfield σ) := hfinK
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (fixSubfield σ) := Fintype.ofFinite _
  haveI : CharP (fixSubfield σ) 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 1)
      (by rw [← Nat.card_eq_fintype_card, hK2, pow_one])
  have hCQmap : CQ σ i = (componentRootSpan (fixSubfield σ) (rootCharHom a) i).map
      (baseChangeGL (fixSubfield σ).subtype) := CQ_eq_map i σ
  let eT : rationalSpan S.ρ S.Γ (rootCharHom a) i ≃* T := MulEquiv.subgroupCongr hRatT
  let eTC : T ≃* CQ σ i :=
    (Subgroup.equivMapOfInjective (CQ σ i) (MulAut.conj z).toMonoidHom
      (MulAut.conj z).injective).symm
  let eCC : CQ σ i ≃* componentRootSpan (fixSubfield σ) (rootCharHom a) i :=
    ((Subgroup.equivMapOfInjective (componentRootSpan (fixSubfield σ) (rootCharHom a) i)
        (baseChangeGL (fixSubfield σ).subtype)
        (baseChangeGL_injective (fixSubfield σ).subtype)).trans
      (MulEquiv.subgroupCongr hCQmap.symm)).symm
  let eSL : Matrix.SpecialLinearGroup (Fin 2) ↥(fixSubfield σ) ≃*
      componentRootSpan (fixSubfield σ) (rootCharHom a) i :=
    (MonoidHom.ofInjective (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
      (K := ↥(fixSubfield σ)) x.1)).trans (MulEquiv.subgroupCongr hC.symm)
  open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.Lin in
  obtain ⟨ePerm⟩ := nonempty_mulEquiv_perm_three_of_card_two (K := ↥(fixSubfield σ)) hK2
  exact ⟨eT.trans (eTC.trans (eCC.trans (eSL.symm.trans ePerm)))⟩

end CFSG.StandardType.GGK0LQ

end
