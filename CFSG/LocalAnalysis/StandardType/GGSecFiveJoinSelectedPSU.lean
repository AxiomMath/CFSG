module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatJoinF4
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSU
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSU
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSU
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.LocalAnalysis.StandardType.GGSelectedRootMatch

public noncomputable section

set_option autoImplicit false

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.RCKRP

theorem false_of_guardedLabel_of_linear_unitary_model {X : Type} [Group X]
    {lab : LargeEvenLabel} (hguard : GuardedLargeEvenLabel lab)
    (hmark : MarkedModel lab X) {t : StatedLieTag} {m f : ℕ}
    (ht : t = .PSL ∨ t = .PSU) (hf : t = .PSL → 2 ≤ f)
    (hmodel : LieModel X t m 2 f) : False := by
  have hchar : markChar lab = 2 := by
    rcases hguard with ⟨hbc, -⟩ | ⟨hdt, -⟩ | hex | ⟨hA, -, -⟩
    · rcases hbc with hbc | hbc <;> simp [markChar, hbc]
    · rcases hdt with hdt | hdt <;> simp [markChar, hdt]
    · rcases hex with hex | hex | hex | hex | hex <;> simp [markChar, hex]
    · simp [markChar, hA]
  obtain ⟨htag, -, hdeg⟩ := cls_typeDet hchar hmark (ht.imp_right Or.inl) hmodel
  rcases hguard with ⟨hbc, -⟩ | ⟨hdt, h4⟩ | hex | ⟨hA, -, hN⟩
  · rcases hbc with hbc | hbc <;> rcases ht with rfl | rfl <;>
      simp [markTag, hbc] at htag
  · have h2 : lab.rank ≠ 2 := by omega
    have h3 : lab.rank ≠ 3 := by omega
    rcases hdt with hdt | hdt <;> rcases ht with rfl | rfl <;>
      simp [markTag, hdt, h2, h3] at htag
  · rcases hex with hex | hex | hex | hex | hex <;>
      rcases ht with rfl | rfl <;> simp [markTag, hex] at htag
  · have htA : t = .PSL := by simpa [markTag, hA] using htag
    have hf1 : f = 1 := by simpa [markDeg, hA, hN] using hdeg
    have := hf htA
    omega

private theorem false_of_guarded_unitary_two_cover {G : Type} [Group G]
    {g : ℕ} {J : Subgroup G}
    (psi : (ggU .PSU 2 (g + 1)).K →* G)
    (hpsi : psi.ker ≤ Subgroup.center (ggU .PSU 2 (g + 1)).K)
    (hrange : psi.range = J) (hq : 4 ≤ 2 ^ (g + 1))
    {lab : LargeEvenLabel} (hguard : GuardedLargeEvenLabel lab)
    (hmark : MarkedModel lab (↥J ⧸ Subgroup.center ↥J)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := GaloisField 2 (2 * (g + 1))
  obtain ⟨⟨chi⟩, hfixed⟩ := RCSTSU.exists_equiv_sl2
    (card_galoisField_two_mul 2 (g + 1) (by omega))
  let eF : GaloisField 2 (g + 1) ≃+*
      CFSG.LieType.Steinberg.fixedSubfield F 2 (g + 1) :=
    CFSG.ClassicalInvolution.Upgrade.fieldIsoOfCard
      ((GaloisField.card 2 (g + 1) (by omega)).trans hfixed.symm)
  let chi0 : (ggU .PSL 2 (g + 1)).K →* (ggU .PSU 2 (g + 1)).K :=
    chi.toMonoidHom.comp (Matrix.SpecialLinearGroup.map eF.toRingHom)
  have hchi : Function.Injective chi0 :=
    chi.injective.comp (SelectedRoot.slMap_injective eF)
  have hchis : Function.Surjective chi0 :=
    chi.surjective.comp (SelectedRoot.slMap_surjective eF)
  let phi : (ggU .PSL 2 (g + 1)).K →* G := psi.comp chi0
  have hphi : phi.ker ≤ Subgroup.center (ggU .PSL 2 (g + 1)).K := by
    intro y hy
    exact Subgroup.comap_center_le_center hchi (hpsi hy)
  have hphir : phi.range = J := by
    dsimp only [phi]
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hchis,
      ← MonoidHom.range_eq_map]
    exact hrange
  have hadm : StatedLieAdmissible .PSL 2 2 (g + 1) := by
    refine ⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩
    all_goals intro h; have := (Prod.mk.inj h).2; omega
  have hmodel := irg_lieModel_quot (Or.inl rfl) hadm phi hphir hphi
  have hf : 2 ≤ g + 1 := by
    by_contra h
    have hg0 : g = 0 := by omega
    subst hg0
    norm_num at hq
  exact false_of_guardedLabel_of_linear_unitary_model hguard hmark
    (Or.inl rfl) (fun _ => hf) hmodel

theorem false_of_guarded_component_of_unitary_cover
    {G : Type} [Group G] [Finite G] {p n g : ℕ} {K J : Subgroup G} {d : G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdp : d ^ p = 1) (hn : 3 ≤ n)
    (phi : (ggU .PSU n (g + 1)).K →* G) (hphir : phi.range = K)
    (hphik : phi.ker ≤ Subgroup.center (ggU .PSU n (g + 1)).K)
    (hdN : d ∈ Subgroup.normalizer (K : Set G))
    (hdID : GGPsiInnerDiag (ggU .PSU n (g + 1)).D phi d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer ({d} : Set G)))
    (hmark : LargeEvenMarking ↥J (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨lab, -, R, _, I, F0, theta, _, _, hguard, hmarked⟩ :=
    largeEvenMarking_exists_markedModel hmark
  have hm : MarkedModel lab (↥J ⧸ Subgroup.center ↥J) :=
    MarkedModel.of_mulEquiv theta.symm hmarked
  obtain ⟨s, hsU, -, hsodd, eps, heps, ⟨e, he, heeps, hcase⟩, J', hJe, hJmap⟩ :=
    rckF1_PSU hp hp2 hdp hn phi hphir hphik hdN hdID hJ
  have hm' : MarkedModel lab (↥(J'.map phi) ⧸ Subgroup.center ↥(J'.map phi)) := by
    rw [hJmap]
    exact hm
  let S : Set (Matrix.GeneralLinearGroup (Fin n) (GaloisField 2 (2 * (g + 1)))) := {s}
  have hSU : ∀ a ∈ S, conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1))
      (a : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) * antidiag n *
      (a : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (g + 1)))) = antidiag n := by
    intro a ha
    obtain rfl : a = s := ha
    exact hsU
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    have ha' : a = s := ha
    have hb' : b = s := hb
    rw [ha', hb']
  have hodd : ∀ a ∈ S, Odd (orderOf a) := by
    intro a ha
    obtain rfl : a = s := ha
    exact hsodd
  by_cases hdeg : 2 ≤ blockDegree
      (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e
  · obtain ⟨t, m, f, ht, hlt, hmodel, -⟩ := ggSixLSevenFieldExtCaseCl_PSU
      (card_galoisField_two_mul 2 (g + 1) (by omega)) n phi hphik
      S hSU hS hodd heps hJe he heeps hdeg
    exact false_of_guardedLabel_of_linear_unitary_model hguard hm' ht
      (fun _ => by omega) hmodel
  have hdeg' : blockDegree
      (Algebra.adjoin (GaloisField 2 (2 * (g + 1))) (Units.val '' S)) e < 2 := by omega
  rcases hcase with hself | ⟨-, hpair, heq⟩
  · subst eps
    obtain ⟨r, iota, U, Lm, hiota, hirange, hgood, -⟩ :=
      exists_blockModel_selfDual_PSU_matrix n g S hS he heps.2.2.2.1 hdeg' hJe
    let nu : (ggU .PSU r (g + 1)).K →* G := phi.comp iota
    have hnur : nu.range = J'.map phi :=
      (MonoidHom.range_comp phi iota).trans (congrArg (fun H => H.map phi) hirange)
    have hnuk : nu.ker ≤ Subgroup.center (ggU .PSU r (g + 1)).K := by
      intro y hy
      exact Subgroup.comap_center_le_center hiota (hphik hy)
    rcases hgood with ⟨hr3, hbad⟩ | ⟨hr2, hq⟩
    · have hadm : StatedLieAdmissible .PSU r 2 (g + 1) :=
        ⟨Nat.prime_two, by omega, hr3,
          fun h => hbad ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩⟩
      exact false_of_guardedLabel_of_linear_unitary_model hguard hm'
        (Or.inr rfl) (fun h => by cases h)
        (irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm nu hnur hnuk)
    · subst r
      exact false_of_guarded_unitary_two_cover nu hnuk hnur hq hguard hm'
  · rw [heq] at hJe
    obtain ⟨k, iota, -, hcent, hirange, -⟩ :=
      exists_blockModelClosure_dualPair_PSU_explicitModel n g S hSU hS he hpair hdeg' hJe
    let nu : (ggU .PSL (k + 1) (2 * (g + 1))).K →* G := phi.comp iota
    have hnur : nu.range = J'.map phi :=
      (MonoidHom.range_comp phi iota).trans (congrArg (fun H => H.map phi) hirange)
    have hnuk : nu.ker ≤ Subgroup.center (ggU .PSL (k + 1) (2 * (g + 1))).K := by
      intro y hy
      exact hcent y (hphik hy)
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst k
      have hsub : Subsingleton
          (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 (2 * (g + 1)))) :=
        Matrix.SpecialLinearGroup.subsingleton_of_subsingleton
      have hbot : J' = ⊥ := by
        rw [← hirange, eq_bot_iff]
        rintro _ ⟨y, rfl⟩
        have hy : y = 1 := @Subsingleton.elim _ hsub y 1
        rw [hy, map_one]
        exact Subgroup.one_mem _
      exact (Subgroup.nontrivial_iff_ne_bot J').mp
        (CFSG.ComponentClassification.Quasisimple.nontrivial hJe.2.2) hbot
    · have hq : 4 ≤ 2 ^ (2 * (g + 1)) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (2 * (g + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hadm : StatedLieAdmissible .PSL (k + 1) 2 (2 * (g + 1)) := by
        refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
        all_goals intro h; have := (Prod.mk.inj h).2; omega
      exact false_of_guardedLabel_of_linear_unitary_model hguard hm'
        (Or.inl rfl) (fun _ => by omega)
        (irg_lieModel_quot (Or.inl rfl) hadm nu hnur hnuk)

theorem GGConfig.false_of_guarded_actual_of_PSU
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X : Subgroup G} (hcfg0 : GGConfig p B Bs x L D J) {n f : ℕ}
    (psi : (ggU .PSU n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSU n f).D .PSU n f psi)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) : False := by
  obtain ⟨d, -, hdG, hdp, hXC⟩ :=
    ggActualMember_internal_component hcfg0 horigin (isQuasisimple_of_largeEvenMarking hmark)
  obtain ⟨hp, hp2, -⟩ :=
    (hcfg0.1.2.2.2.2.2.1 : p ∈ CFSG.Assembly.LargeEvenBeta 4 G)
  have hdN : d ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    Subgroup.le_normalizer hdG
  have hdID : GGPsiInnerDiag (ggU .PSU n f).D psi d :=
    ggPsiInnerDiag_of_mem_range _ (by rw [hpres.2.1.1]; exact hdG)
  have hf : 1 ≤ f := hpres.1.1.2.1
  have hn : 3 ≤ n := hpres.1.1.2.2.1
  cases f with
  | zero => omega
  | succ g =>
    exact false_of_guarded_component_of_unitary_cover hp hp2 hdp hn
      psi hpres.2.1.1 hpres.2.1.2 hdN hdID hXC hmark

theorem ggActualMember_PSU_selected
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs L D J X : Subgroup G} {x : G}
    (hcfg : GGConfig p B Bs x L D J) {n f : ℕ}
    (ψ : (ggU .PSU n f).K →* G)
    (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU .PSU n f).D .PSU n f ψ)
    (horigin : (X = L ∧ x ∈ ggG0 p B x L D J) ∨
      ∃ y : G, GGNbr p B x D J y X ∧ y ∈ ggG0 p B x L D J)
    (hmark : LargeEvenMarking ↥X (fun lab _ _ _ _ _ => GuardedLargeEvenLabel lab)) :
    ∃ S : Subgroup G, MemberSelectedSL2At X S ∧ PresentedSelectedSL2At ψ S :=
  (hcfg.false_of_guarded_actual_of_PSU ψ hpres horigin hmark).elim

end CFSG.StandardType
