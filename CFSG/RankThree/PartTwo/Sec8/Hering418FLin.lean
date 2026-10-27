module

public import CFSG.RankThree.PartTwo.Sec8.Hering418FCore
public import CFSG.RankThree.PartTwo.Sec8.Hering418FLinFix
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofL3
public import CFSG.RankThree.PartTwo.Sec8.Hering418FSL
public import CFSG.RankThree.PartTwo.Sec8.Hering418FSU

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418
open CFSG.Open (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK (fixedField)

section Lin


theorem hasKind_of_inducesStdKind_lThree {G : Type} [Group G]
    [Finite G] {L : Subgroup G} {x : G} {j : ℕ} (he : Even j) (hj : 1 ≤ j)
    (φ : L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 j)) {k : KFacts.AutKind}
    (h : KFacts.InducesStdKind L x k) :
    ∃ hx : x ∈ Subgroup.normalizer (L : Set G),
      (KFacts.stdPinnedPSL 3 (GaloisField 2 j)).HasKind
        (KFacts.inducedAutHom L (φ.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 j)))
          ⟨x, hx⟩) k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := Item82Proof.kF82LThreeModel_holds G L x j k he hj ⟨φ⟩ h
  exact (KFacts.inducesKindPSL_iff L le_rfl (φ.trans (Sec4.projSLEquivProjectiveSL 3 _)) x k).mp h1

theorem dichotomy_lThreeSixEven {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hX : IsLThreeSixEven (L ⧸ aschbacherSolvableCore 3 L)) :
    ∃ N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), innBar L ≤ N ∧
      (∀ F : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)), IsElemAbelian 3 F → F ≤ N →
        Nat.card F ≤ 9) ∧
      ∀ (x : G) (hx : x ∈ Subgroup.normalizer (L : Set G)), x ^ 3 = 1 →
        (rho L ⟨x, hx⟩ ∈ N ∧ ¬ (KFacts.InducesStdKind L x .field ∨
            KFacts.InducesStdKind L x .graphField)) ∨
          (rho L ⟨x, hx⟩ ∉ N ∧ (KFacts.InducesStdKind L x .field ∨
            KFacts.InducesStdKind L x .graphField)) := by
  obtain ⟨k, hk, ⟨m, rfl⟩, he, ⟨φ⟩⟩ := hX
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm3 : 1 ≤ 3 * m := by omega
  set F := GaloisField 2 (3 * m) with hFdef
  have hFcard : Nat.card F = 2 ^ (3 * m) := GaloisField.card 2 (3 * m) (by omega)
  have h3 : (3 : F) ≠ 0 := Sec4.three_ne_zero_of_card Nat.prime_two (by norm_num) hFcard
  let e' : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 F :=
    φ.trans (Sec4.projSLEquivProjectiveSL 3 F)
  refine ⟨(linearAutGroup 3 F).comap (MulAut.congr e').toMonoidHom, ?_, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    change MulAut.congr e' (MulAut.conj y) ∈ linearAutGroup 3 F
    rw [KFacts.congr_mulAutConj]
    exact KFacts.innAut_le_linearAutGroup 3 F ⟨_, rfl⟩
  · intro F' hF' hFN
    have hle : F'.map (MulAut.congr e').toMonoidHom ≤ linearAutGroup 3 F := by
      rintro _ ⟨σ, hσ, rfl⟩
      exact hFN hσ
    have := Sec4.card_inf_linearAutGroup_three_le h3 (hF'.map (MulAut.congr e').toMonoidHom)
    rw [inf_eq_left.mpr hle, Subgroup.card_map_of_injective (MulAut.congr e').injective] at this
    exact this
  · intro x hx hx3
    have hτ3 : KFacts.inducedAutHom L e' ⟨x, hx⟩ ^ 3 = 1 :=
      KFacts.inducedAutHom_pow_eq_one L e' hx hx3
    by_cases hD : KFacts.inducedAutHom L e' ⟨x, hx⟩ ∈ linearAutGroup 3 F
    · left
      refine ⟨hD, ?_⟩
      have hsep := KFacts.stdPinnedPSL_separated (K := F) (n := 3) le_rfl
      rintro (h | h)
      · obtain ⟨hx', hkind⟩ := hasKind_of_inducesStdKind_lThree (he : Even (3 * m)) hm3 φ h
        exact hsep.not_mem_inndiag_of_hasKind hkind (by decide) (by decide) hD
      · obtain ⟨hx', hkind⟩ := hasKind_of_inducesStdKind_lThree (he : Even (3 * m)) hm3 φ h
        exact hsep.not_mem_inndiag_of_hasKind hkind (by decide) (by decide) hD
    · right
      exact ⟨hD, Or.inl (KFacts.InducesStdKind.psl 3 F le_rfl
        ⟨e', hx, KFacts.isField_of_pow_three_eq_one le_rfl hτ3 hD⟩)⟩

theorem exists_fixed_order_four_of_hasKind_field {F : Type} [Field F] [Finite F] [CharP F 2]
    {α : MulAut (projectiveSL 3 F)} (h : (KFacts.stdPinnedPSL 3 F).HasKind α .field) :
    ∃ u : projectiveSL 3 F, α u = u ∧ u ^ 4 = 1 ∧ u ^ 2 ≠ 1 := by
  obtain ⟨φ, ⟨τ, rfl⟩, -, d, -, rfl⟩ := h
  refine ⟨d (unipProj F), ?_, ?_, ?_⟩
  · change d ((fieldAut 3 F τ) (d⁻¹ (d (unipProj F)))) = d (unipProj F)
    rw [MulAut.inv_apply_self, fieldAut_unipProj]
  · rw [← map_pow, unipProj_pow_four, map_one]
  · intro h2
    rw [← map_pow] at h2
    exact unipProj_sq_ne_one (d.injective (h2.trans (map_one d).symm))

theorem kF418OuterOn_lThreeSixEven :
    KF418OuterOn (fun X _ => IsLThreeSixEven X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa hbk
  obtain ⟨k, hk, ⟨m, rfl⟩, he, ⟨φ⟩⟩ := hl
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hβ : Sec4.InducesOuterTheta b L := by
    rcases hbk with h | h
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .field) L h (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta (k := .graphField) L h (by decide)
  have hm3 : 1 ≤ 3 * m := by omega
  have hmE : Even m := (Nat.even_mul.mp he).resolve_left (by decide)
  have hm1 : 1 ≤ m := by omega
  set F := GaloisField 2 (3 * m) with hFdef
  have hFcard : Nat.card F = 2 ^ (3 * m) := GaloisField.card 2 (3 * m) (by omega)
  let e' : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 F :=
    φ.trans (Sec4.projSLEquivProjectiveSL 3 F)
  have hsep := KFacts.stdPinnedPSL_separated (K := F) (n := 3) le_rfl
  obtain ⟨hbN', hDb⟩ : ∃ hbN' : b ∈ Subgroup.normalizer (L : Set G),
      KFacts.inducedAutHom L e' ⟨b, hbN'⟩ ∉ linearAutGroup 3 F := by
    rcases hbk with h | h
    · obtain ⟨hx', hkind⟩ := hasKind_of_inducesStdKind_lThree (he : Even (3 * m)) hm3 φ h
      exact ⟨hx', hsep.not_mem_inndiag_of_hasKind hkind (by decide) (by decide)⟩
    · obtain ⟨hx', hkind⟩ := hasKind_of_inducesStdKind_lThree (he : Even (3 * m)) hm3 φ h
      exact ⟨hx', hsep.not_mem_inndiag_of_hasKind hkind (by decide) (by decide)⟩
  have hb3' : KFacts.inducedAutHom L e' ⟨b, hbN'⟩ ^ 3 = 1 :=
    KFacts.inducedAutHom_pow_eq_one L e' hbN' hb3
  obtain ⟨σ, hσ, H, hβH⟩ := KFacts.linear_order_three_field_descent le_rfl _ hb3' hDb
  let e'' : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL 3 F := e'.trans (conjAut 3 F H)⁻¹
  have hβ'' : MulAut.congr e'' c.beta = fieldAut 3 F σ := by
    have h1 : MulAut.congr e'' c.beta =
        MulAut.congr (conjAut 3 F H)⁻¹ (KFacts.inducedAutHom L e' ⟨b, hbN'⟩) :=
      KFacts.congr_trans e' _ _
    rw [h1, hβH, congr_eq_mul_mul_inv]
    group
  obtain ⟨Q, hQfix, hQcomm, hQs, hQns, ⟨ιQ⟩⟩ := exists_core_of_fieldAut e'' c.beta hβ''
  have hQC : Q ≤ Sec8.barCentralizer (Subgroup.zpowers b) L := fun x hx =>
    (KFacts.mem_barCentralizer_zpowers_iff c.hbL x).mpr (hQfix x hx)
  have hQcomm' : ⁅Sec8.barCentralizer (Subgroup.zpowers b) L,
      Sec8.barCentralizer (Subgroup.zpowers b) L⁆ ≤ Q :=
    Subgroup.commutator_le.mpr fun y hy z hz => hQcomm y z
      ((KFacts.mem_barCentralizer_zpowers_iff c.hbL y).mp hy)
      ((KFacts.mem_barCentralizer_zpowers_iff c.hbL z).mp hz)
  obtain ⟨Ψ, hΨ⟩ := c.exists_mulEquiv_of_simple_core hK hQC hQcomm' hQs hQns
  have hσcard : Nat.card (fixedField σ) = 2 ^ m := by
    have h := CFSG.GH74.GLS.IVK.fixedField_card_pow σ
    rw [hσ, hFcard] at h
    have h' : Nat.card (fixedField σ) ^ 3 = (2 ^ m) ^ 3 := by rw [h, ← pow_mul, mul_comm]
    exact Nat.pow_left_injective (by norm_num : 3 ≠ 0) h'
  obtain ⟨ψ⟩ : Nonempty (fixedField σ ≃+* GaloisField 2 m) :=
    nonempty_ringEquiv_of_card_eq (by rw [hσcard, GaloisField.card 2 m (by omega)])
  let eKP : K ⧸ aschbacherSolvableCore 3 K ≃* projSL 3 (GaloisField 2 m) :=
    Ψ.trans (ιQ.trans ((Sec21.Item223CensusResProof.psOfSL
      (Sec21.Item223CensusResProof.slEquiv ψ 3)).trans
        (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 m)).symm))
  let eK : K ⧸ aschbacherSolvableCore 3 K ≃* projectiveSL 3 (GaloisField 2 m) :=
    eKP.trans (Sec4.projSLEquivProjectiveSL 3 (GaloisField 2 m))
  obtain ⟨haK', hkindK⟩ := hasKind_of_inducesStdKind_lThree hmE hm1 eKP hKa
  obtain ⟨uK, huKfix, huK4, huK2⟩ := exists_fixed_order_four_of_hasKind_field hkindK
  set y : K ⧸ aschbacherSolvableCore 3 K := eK.symm uK with hy
  have hyfix : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) y = y := by
    apply eK.injective
    have h1 : KFacts.inducedAutHom K eK ⟨a, c.haK⟩ (eK y) =
        eK (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, c.haK⟩) y) := by
      change MulAut.congr eK _ (eK y) = _
      simp [MulAut.congr_apply]
    rw [← h1]
    have h2 : eK y = uK := by rw [hy]; simp
    rw [h2]
    exact huKfix
  have hy4 : y ^ 4 = 1 := by
    apply eK.injective
    rw [map_pow, map_one]
    have h2 : eK y = uK := by rw [hy]; simp
    rw [h2]
    exact huK4
  have hy2 : y ^ 2 ≠ 1 := by
    intro h
    apply huK2
    have h2 : eK y = uK := by rw [hy]; simp
    rw [← h2, ← map_pow, h, map_one]
  let ι : K ⧸ aschbacherSolvableCore 3 K →* L ⧸ aschbacherSolvableCore 3 L :=
    Q.subtype.comp Ψ.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp Ψ.injective
  set u : L ⧸ aschbacherSolvableCore 3 L := ι y with hu
  have hu4 : u ^ 4 = 1 := by rw [hu, ← map_pow, hy4, map_one]
  have hu2 : u ^ 2 ≠ 1 := by
    rw [hu, ← map_pow]
    intro h
    exact hy2 (hι (h.trans (map_one ι).symm))
  have hαu : c.alpha u = u := by
    have h1 := hΨ y
    rw [hyfix] at h1
    exact h1.symm
  have hβu : c.beta u = u := hQfix _ (Ψ y).2
  have hOTC : KFacts.OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L) :=
    (KFacts.outThreeCyclic_psl3 F).of_mulEquiv e'
  have hcomm : Commute c.beta c.alpha := c.alpha_mul_beta.symm
  obtain ⟨i, -, x, hx⟩ := hOTC c.beta c.alpha hcomm c.beta_pow_three c.alpha_pow_three hβ.2
  have hτu : (c.beta ^ i * c.alpha) u = u := by
    rw [MulAut.mul_apply, hαu]
    exact pow_apply_eq_of_apply_eq hβu i
  have hτ3 : (c.beta ^ i * c.alpha) ^ 3 = 1 := by
    rw [(hcomm.pow_left i).mul_pow, c.alpha_pow_three, mul_one, ← pow_mul, mul_comm, pow_mul,
      c.beta_pow_three, one_pow]
  have hconj : MulAut.congr e'' (c.beta ^ i * c.alpha) = MulAut.conj (e'' x) := by
    rw [← hx, KFacts.congr_mulAutConj]
  have hyy3 : (MulAut.conj (e'' x) : MulAut (projectiveSL 3 F)) ^ 3 = 1 := by
    rw [← hconj, ← map_pow, hτ3, map_one]
  have hyyu : e'' x * e'' u * (e'' x)⁻¹ = e'' u := by
    have h1 : MulAut.congr e'' (c.beta ^ i * c.alpha) (e'' u) = e'' u := by
      change e'' ((c.beta ^ i * c.alpha) (e''.symm (e'' u))) = e'' u
      rw [MulEquiv.symm_apply_apply, hτu]
    rw [hconj] at h1
    exact h1
  have huu4 : e'' u ^ 4 = 1 := by rw [← map_pow, hu4, map_one]
  have huu2 : e'' u ^ 2 ≠ 1 := fun h => hu2 (e''.injective (by rw [map_pow, h, map_one]))
  have hx1 : e'' x = 1 := eq_one_of_conj_fixed_psl3 hyy3 hyyu huu4 huu2
  have hx0 : x = 1 := e''.injective (by rw [hx1, map_one])
  have hτ1 : c.beta ^ i * c.alpha = 1 := by rw [← hx, hx0, map_one]
  apply c.hαβ (i : ℤ)
  rw [zpow_natCast, (hcomm.pow_left i).symm.eq]
  exact hτ1

theorem kF418ModelOn_lThreeSixEven :
    KF418ModelOn (fun X _ => IsLThreeSixEven X) :=
  kF418ModelOn_of_dichotomy (fun _ _ _ _ _ hl => dichotomy_lThreeSixEven hl)
    kF418OuterOn_lThreeSixEven

end Lin

end CFSG.RankThree.PartTwo.Sec8.Hering418
