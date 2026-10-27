module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocDefs
import CFSG.RankThree.PartTwo.Sec14.Item148ONLocProofSig
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig
  CFSG.RankThree.PartTwo.Sec14

section Transport

variable {Γ : Type} [Group Γ] [Finite Γ] {A L : Subgroup Γ} {X : Type} [Group X]

theorem thetaQuotientAction_eq_sigmaOf (hAL : A ≤ normalizer (L : Set Γ)) (a : A) :
    CFSG.RankThree.GroupTheory.thetaQuotientAction 3 hAL a = L3PGL.sigmaOf L (hAL a.2) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H z => rfl

theorem actX_eq_congr_sigmaOf (hAL : A ≤ normalizer (L : Set Γ))
    (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) (a : A) :
    actX hAL ψ a = MulAut.congr ψ (L3PGL.sigmaOf L (hAL a.2)) := by
  rw [actX, MonoidHom.comp_apply, thetaQuotientAction_eq_sigmaOf]
  rfl

theorem fixSubgroup_map_eq_autFix (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X)
    (σ : MulAut (L ⧸ aschbacherSolvableCore 3 L)) :
    (Res5Types.fixSubgroup σ).map ψ.toMonoidHom = Sec4.autFix (MulAut.congr ψ σ) := by
  rw [Sec4.autFix_congr ψ σ]
  rfl

theorem locE_range_actX (hAL : A ≤ normalizer (L : Set Γ))
    (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) (hloc : LocA A L) :
    LocE X (actX hAL ψ).range := by
  intro Y hY3 hYE
  set Y' : Subgroup (L ⧸ aschbacherSolvableCore 3 L) := Y.map ψ.symm.toMonoidHom with hY'
  have hY'3 : ¬ 3 ∣ Nat.card Y' := by
    rwa [hY', card_map_of_injective ψ.symm.injective]
  have hY'E : ∀ σ ∈ Sec4.autThetaQuot A L, Y'.map σ.toMonoidHom ≤ Y' := by
    intro σ hσ
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    have hε := hYE (actX hAL ψ ⟨a, haA⟩) ⟨⟨a, haA⟩, rfl⟩ y hy
    rw [actX_eq_congr_sigmaOf, MulAut.congr_apply] at hε
    refine ⟨_, hε, ?_⟩
    change ψ.symm (ψ (L3PGL.sigmaOf L (hAL haA) (ψ.symm y))) =
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, haN⟩) (ψ.symm y)
    rw [MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨a, haA, haN, hσ1, hYθ⟩ := hloc Y' hY'3 hY'E
  refine ⟨actX hAL ψ ⟨a, haA⟩, ⟨⟨a, haA⟩, rfl⟩, ?_, ?_⟩
  · rw [actX_eq_congr_sigmaOf]
    intro h1
    apply hσ1
    have h2 : MulAut.congr ψ (L3PGL.sigmaOf L (hAL haA)) = MulAut.congr ψ 1 := by
      rw [h1, map_one]
    exact (MulAut.congr ψ).injective h2
  · have hYY : Y = Y'.map ψ.toMonoidHom := by
      rw [hY', Subgroup.map_map]
      ext y
      simp
    rw [hYY, actX_eq_congr_sigmaOf]
    refine (Subgroup.map_mono hYθ).trans (le_of_eq ?_)
    rw [Sec6.map_inSubgroup_theta_of_injective ψ.toMonoidHom ψ.injective,
      fixSubgroup_map_eq_autFix]

theorem fixE_range_actX (hAL : A ≤ normalizer (L : Set Γ))
    (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) :
    fixE (actX hAL ψ).range = (L3PGL.fixA A L).map ψ.toMonoidHom := by
  ext x
  rw [mem_fixE]
  constructor
  · intro hx
    refine ⟨ψ.symm x, fun σ hσ => ?_, by simp⟩
    obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
    have h1 := hx (actX hAL ψ ⟨a, haA⟩) ⟨⟨a, haA⟩, rfl⟩
    rw [actX_eq_congr_sigmaOf] at h1
    have h1' : ψ (L3PGL.sigmaOf L (hAL haA) (ψ.symm x)) = x := h1
    have h2 := congrArg ψ.symm h1'
    rw [MulEquiv.symm_apply_apply] at h2
    exact h2
  · rintro ⟨z, hz, rfl⟩ ε ⟨a, rfl⟩
    rw [actX_eq_congr_sigmaOf, MulAut.congr_apply]
    change ψ (L3PGL.sigmaOf L (hAL a.2) (ψ.symm (ψ z))) = ψ z
    rw [MulEquiv.symm_apply_apply]
    congr 1
    exact hz _ (Sec4.mem_autThetaQuot_iff.mpr ⟨a, hAL a.2, a.2, rfl⟩)

end Transport

theorem exists_of_inspectAutLoc {X : Type} [Group X] [Finite X] {P : Subgroup X → Prop}
    (hP : ∀ E : Subgroup (MulAut X), Nat.card E = 9 → (∀ ε ∈ E, ε ^ 3 = 1) → LocE X E →
      IsPGroup 3 (fixE E) →
      ∀ K : Subgroup X, (∀ ε ∈ E, ∀ k ∈ K, ε k ∈ K) → Group.IsPerfect K → K ≠ ⊥ →
        IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) →
        Sec4.IsList46 (K ⧸ aschbacherSolvableCore 3 K) →
        K ≤ (⨆ (ε : MulAut X) (_ : ε ∈ E) (_ : ε ≠ 1),
          pPrimeCoreOf 3 (K ⊓ Sec4.autFix ε)) → P K)
    (hθ : ∀ K' : Subgroup X, P K' → aschbacherSolvableCore 3 K' = ⊥)
    {Γ : Type} [Group Γ] [Finite Γ] {A L K : Subgroup Γ} {e : Γ} (h : Sig148 A L K e)
    (hker : Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) =
      (zpowers e : Set Γ))
    (ψ : L ⧸ aschbacherSolvableCore 3 L ≃* X) (hloc : LocA A L)
    (hfix : IsPGroup 3 (L3PGL.fixA A L))
    (hK46 : Sec4.IsList46 (K ⧸ aschbacherSolvableCore 3 K)) :
    ∃ K' : Subgroup X, P K' ∧ Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* K') := by
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := h.isE27.1.2
  have hAL := h.le_normalizer_L
  have hAK := h.le_normalizer_K
  have hιe : ∀ a : A, actX hAL ψ a = 1 ↔ (a : Γ) ∈ zpowers e := by
    intro a
    rw [actX_eq_one_iff hAL ψ a, ← SetLike.mem_coe, ← hker]
    exact ⟨fun h' => ⟨a.2, h'⟩, fun h' => h'.2⟩
  have he3 : orderOf e = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (hA3 e h.mem) h.ne_one
  have hcardE : Nat.card (actX hAL ψ).range = 9 := by
    have hzA : zpowers e ≤ A := zpowers_le.2 h.mem
    have hker' : (actX hAL ψ).ker = (zpowers e).subgroupOf A := by
      ext a
      rw [MonoidHom.mem_ker, mem_subgroupOf, hιe]
    have hk3 : Nat.card (actX hAL ψ).ker = 3 := by
      rw [hker', Nat.card_congr (subgroupOfEquivOfLe hzA).toEquiv, Nat.card_zpowers, he3]
    have h1 := Subgroup.card_mul_index (actX hAL ψ).ker
    rw [Subgroup.index_ker, hk3, h.isE27.2] at h1
    omega
  have hexpE : ∀ ε ∈ (actX hAL ψ).range, ε ^ 3 = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (by simpa using hA3 a a.2), map_one]
  have hinv : ∀ ε ∈ (actX hAL ψ).range, ∀ k ∈ (kappa h.le ψ).range,
      ε k ∈ (kappa h.le ψ).range := by
    rintro _ ⟨a, rfl⟩ _ ⟨k, rfl⟩
    exact ⟨_, (Ronan148K.kappa_actX h.le ψ hAL hAK a k).symm⟩
  haveI : Group.IsPerfect K := h.isPerfect
  have hKbp : Group.IsPerfect (kappa h.le ψ).range := Group.IsPerfect.range _
  have hkerR : (kappa h.le ψ).rangeRestrict.ker = (kappa h.le ψ).ker :=
    MonoidHom.ker_rangeRestrict _
  obtain ⟨χ⟩ := ONLoc.nonempty_thetaQuot_equiv (kappa h.le ψ).rangeRestrict
    (kappa h.le ψ).rangeRestrict_surjective
    (by rw [hkerR]; exact isSolvable_ker_kappa h.le ψ)
    (by
      rw [hkerR]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_ker_kappa h.le ψ))
  have hKbq : IsQuasisimple ((kappa h.le ψ).range ⧸
      aschbacherSolvableCore 3 (kappa h.le ψ).range) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv χ.symm h.isQuasisimple
  have hKb46 : Sec4.IsList46 ((kappa h.le ψ).range ⧸
      aschbacherSolvableCore 3 (kappa h.le ψ).range) :=
    Sec21.Item223PrintProof.isList46_of_mulEquiv χ.symm hK46
  have hgen : (kappa h.le ψ).range ≤ ⨆ (ε : MulAut X) (_ : ε ∈ (actX hAL ψ).range)
      (_ : ε ≠ 1), pPrimeCoreOf 3 ((kappa h.le ψ).range ⊓ Sec4.autFix ε) := by
    have htop : (⊤ : Subgroup K) ≤ ⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
        (pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ))).subgroupOf K := by
      intro k _
      have hk := h.le_iSup k.2
      have hS : ∀ x : Γ, pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ)) ≤ K := fun x => by
        intro y hy
        obtain ⟨c, -, rfl⟩ := hy
        exact (mem_inf.1 c.2).1
      have hmap : (⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
          (pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ))).subgroupOf K).map K.subtype =
          ⨆ (x : Γ) (_ : x ∈ A) (_ : x ∉ zpowers e),
            pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set Γ)) := by
        simp only [Subgroup.map_iSup, subgroupOf_map_subtype, inf_of_le_left (hS _)]
      rw [← hmap] at hk
      obtain ⟨k', hk', hkk⟩ := hk
      rwa [← Subtype.ext hkk]
    refine (le_of_eq (MonoidHom.range_eq_map (kappa h.le ψ))).trans ((map_mono htop).trans ?_)
    simp only [Subgroup.map_iSup]
    refine iSup_le fun x => iSup_le fun hx => iSup_le fun hxe => ?_
    have hy1 : actX hAL ψ ⟨x, hx⟩ ≠ 1 := fun h1 => hxe ((hιe ⟨x, hx⟩).1 h1)
    exact le_iSup_of_le (actX hAL ψ ⟨x, hx⟩) (le_iSup_of_le ⟨⟨x, hx⟩, rfl⟩
      (le_iSup_of_le hy1 (Ronan148K.map_pPrimeCoreOf_le_autFix h.le ψ hAL hAK hA3 ⟨x, hx⟩)))
  have hPK := hP (actX hAL ψ).range hcardE hexpE (locE_range_actX hAL ψ hloc)
    (by rw [fixE_range_actX hAL ψ]; exact hfix.map _)
    (kappa h.le ψ).range hinv hKbp (Ronan148K.range_kappa_ne_bot h ψ) hKbq hKb46 hgen
  exact ⟨(kappa h.le ψ).range, hPK,
    CFSG.AGLEmbeddingD2.Wilson.Proving.nonempty_quotient_aschbacherSolvableCore_equiv_range
      (kappa h.le ψ) (isSolvable_ker_kappa h.le ψ) (coprime_card_ker_kappa h.le ψ) (hθ _ hPK)⟩

theorem kf148SigL3Loc_of_inspectLoc (hI : InspectSig148L3Loc) : KF148SigL3Loc := by
  unfold KF148SigL3Loc
  intro Γ _ _ A L K e h hker hL hList hq hloc hfix hK46
  obtain ⟨X', _, _, hlist, ⟨φ⟩⟩ := hList
  have hL' : Sec13.IsLThreePi X' := Ronan148K.isLThreePi_of_mulEquiv φ.symm hL
  have hq' : ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e → Sec4.IsoLThreePi X' p e → p = 2 ∨ e ≤ 2 :=
    fun p e _ he hiso => hq p e he (Ronan148K.isoLThreePi_of_mulEquiv φ hiso)
  have hP := hI X' hL' hlist hq'
  have hns : ¬ Group.IsSolvable X' := by
    intro hs
    have hnt : Nontrivial (kappa h.le φ.symm).range :=
      (kappa h.le φ.symm).range.nontrivial_iff_ne_bot.mpr (Ronan148K.range_kappa_ne_bot h φ.symm)
    haveI : Group.IsPerfect K := h.isPerfect
    haveI : Group.IsPerfect (kappa h.le φ.symm).range := Group.IsPerfect.range _
    exact Group.IsPerfect.not_isSolvable (kappa h.le φ.symm).range inferInstance
  haveI hsimp : IsSimpleGroup X' := Ronan148K.isSimpleGroup_of_isLThreePi_not_solvable hL' hns
  have hθ : ∀ K' : Subgroup X', Ronan148K.L3SigType X' K' → aschbacherSolvableCore 3 K' = ⊥ := by
    intro K' hK'
    unfold Ronan148K.L3SigType at hK'
    rcases hK' with rfl | ⟨⟨-, -⟩, ⟨e7⟩⟩ | ⟨p, f, e', hp, hf, -, -, hLE⟩
    · exact Ronan148K.aschbacherSolvableCore_eq_bot_of_mulEquiv Subgroup.topEquiv hns
    · haveI := Ronan148K.isSimpleGroup_alt_seven
      exact Ronan148K.aschbacherSolvableCore_eq_bot_of_mulEquiv e7
        Ronan148K.not_isSolvable_alt_seven
    · unfold IsLThreeEpsAt at hLE
      rcases hLE with ⟨⟨eL⟩⟩ | ⟨h2, ⟨eU⟩⟩
      · haveI := Ronan148K.isSimpleGroup_projSL_three_field p f
        exact Ronan148K.aschbacherSolvableCore_eq_bot_of_mulEquiv eL
          (Ronan148K.not_isSolvable_projSL_three p f hf)
      · haveI := CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.isSimpleGroup_projSU_three_of_ne_two
          p f hf (by omega)
        exact Ronan148K.aschbacherSolvableCore_eq_bot_of_mulEquiv eU
          (Ronan148K.not_isSolvable_projSU_three p f hf h2)
  obtain ⟨K', hK'P, ⟨χ⟩⟩ := exists_of_inspectAutLoc hP hθ h hker φ.symm hloc hfix hK46
  unfold KThetaC148
  unfold Ronan148K.L3SigType at hK'P
  rcases hK'P with rfl | ⟨⟨hf5, hA⟩, ⟨e7⟩⟩ | ⟨p, f, e', hp, hf, he', hiso, hLE⟩
  · exact Or.inl ⟨χ.trans (Subgroup.topEquiv.trans φ)⟩
  · refine Or.inr (Or.inl ⟨?_, ⟨χ.trans e7⟩⟩)
    rcases hA with ⟨⟨g⟩⟩ | ⟨⟨g⟩⟩
    · exact Or.inr (Or.inl ⟨hf5, ⟨φ.symm.trans g⟩⟩)
    · exact Or.inr (Or.inr ⟨hf5, ⟨φ.symm.trans g⟩⟩)
  · exact Or.inr (Or.inr ⟨p, f, e', hp, hf, he', Ronan148K.isoLThreePi_of_mulEquiv φ hiso,
      Ronan148K.isLThreeEpsAt_of_mulEquiv χ.symm hLE⟩)

end CFSG.RankThree.PartTwo.Sec14.Ronan148T
