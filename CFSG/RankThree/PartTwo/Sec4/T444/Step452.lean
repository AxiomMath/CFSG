module

public import CFSG.RankThree.PartTwo.Sec4.T444.L34Shape
public import CFSG.RankThree.PartTwo.Sec4.T444.QAction
public import CFSG.RankThree.PartTwo.Sec4.T444.Gap452
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartOne
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.KFacts.L34Sections
public import CFSG.RankThree.PartTwo.Sec4.T444.Step451

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.Assembly.RankThreeEven
open scoped MatrixGroups

section General

variable {X : Type*} [Group X]

theorem isSolvable_comap_mk' {N : Subgroup X} [N.Normal] (hN : Group.IsSolvable N)
    {H : Subgroup (X ⧸ N)} (hH : Group.IsSolvable H) :
    Group.IsSolvable (H.comap (QuotientGroup.mk' N)) := by
  have hNle : N ≤ H.comap (QuotientGroup.mk' N) := fun x hx => by
    have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [Subgroup.mem_comap, h1]
    exact one_mem _
  set g : H.comap (QuotientGroup.mk' N) →* H :=
    ((QuotientGroup.mk' N).comp (Subgroup.subtype _)).codRestrict H (fun x => x.2) with hg
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hNle) g ?_
  intro x hx
  have h1 : QuotientGroup.mk' N (x : X) = 1 := congrArg Subtype.val hx
  exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp h1⟩, rfl⟩

variable [Finite X]

theorem isSolvable_oTwoFitting : Group.IsSolvable (oTwoFitting X) := by
  have : Group.IsNilpotent (CFSG.pCore 2 X) := CFSG.pCore_isPGroup.isNilpotent
  exact isSolvable_comap_mk' inferInstance inferInstance

theorem isSolvable_oTwoP (p : ℕ) [Fact p.Prime] : Group.IsSolvable (oTwoP p X) := by
  have : Group.IsNilpotent (CFSG.pCore 2 X) := CFSG.pCore_isPGroup.isNilpotent
  have : Group.IsNilpotent (CFSG.pCore p (X ⧸ CFSG.pCore 2 X)) := CFSG.pCore_isPGroup.isNilpotent
  exact isSolvable_comap_mk' inferInstance inferInstance

theorem false_of_surjective_of_isCyclic_sylow {Y : Type*} [Group Y] [Finite Y] (F : X →* Y)
    (hF : Function.Surjective F) (hcyc : ∀ S : Sylow 3 X, IsCyclic S) {E : Subgroup Y}
    (hexp : Monoid.exponent E ∣ 3) (hcard : Nat.card E = 9) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := E.comap F with hW
  set ψ : W →* E := (F.comp W.subtype).codRestrict E (fun w => w.2) with hψ
  have hψs : Function.Surjective ψ := by
    intro e
    obtain ⟨x, hx⟩ := hF e
    exact ⟨⟨x, show F x ∈ E by rw [hx]; exact e.2⟩, Subtype.ext hx⟩
  obtain ⟨T⟩ : Nonempty (Sylow 3 W) := inferInstance
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
  have htop : ((T.mapSurjective hψs : Sylow 3 E) : Subgroup E) = ⊤ :=
    ((T.mapSurjective hψs).is_maximal' (hEp.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  set T' : Subgroup X := (T : Subgroup W).map W.subtype with hT'
  have hT'p : IsPGroup 3 T' := T.isPGroup'.map _
  obtain ⟨S, hS⟩ := hT'p.exists_le_sylow
  have : IsCyclic S := hcyc S
  have hT'c : IsCyclic T' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hS).toMonoidHom (MulEquiv.surjective _)
  have hTc : IsCyclic T :=
    isCyclic_of_surjective
      ((T : Subgroup W).equivMapOfInjective W.subtype W.subtype_injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  have hEc : IsCyclic E := by
    refine isCyclic_of_surjective (ψ.comp (T : Subgroup W).subtype) ?_
    intro e
    have he : e ∈ (T : Subgroup W).map ψ := htop ▸ Subgroup.mem_top e
    obtain ⟨t, ht, rfl⟩ := he
    exact ⟨⟨t, ht⟩, rfl⟩
  have hexp' := IsCyclic.exponent_eq_card (α := E)
  rw [hcard] at hexp'
  rw [hexp'] at hexp
  norm_num at hexp

end General

section Exclusion

theorem exists_exponent_three_card_nine :
    ∃ E : Subgroup (projSL 3 (GaloisField 2 2)), Monoid.exponent E ∣ 3 ∧ Nat.card E = 9 := by
  set e := (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).symm
  set E₀ := KFacts.L34.eZero (GaloisField 2 2)
  have hk := KFacts.L34.card_galoisField_two_two
  have := KFacts.L34.isElementaryAbelian_eZero hk
  refine ⟨E₀.map e.toMonoidHom, ?_, ?_⟩
  · rw [← Monoid.exponent_eq_of_mulEquiv (E₀.equivMapOfInjective e.toMonoidHom e.injective)]
    exact CFSG.IsElementaryAbelian.exponent_dvd_p 3 E₀
  · rw [Subgroup.card_map_of_injective e.injective, KFacts.L34.card_eZero hk]

variable {X : Type} [Group X] [Finite X]

theorem quasisimple_of_item4_4 (h44 : Item4_4) (hres : Item4_52Residual) (hX : SectionFourHyp X)
    [Group.IsPerfect X] {K : Subgroup X} [K.Normal] (hK : Group.IsSolvable K)
    (h9 : ¬ 9 ∣ Nat.card K) (ψ : X ⧸ K ≃* projSL 3 (GaloisField 2 2)) :
    IsQuasisimple (X ⧸ CFSG.pCore 2 X) := by
  have : IsSimpleGroup (projSL 3 (GaloisField 2 2)) := isSimpleGroup_projSL
  have : IsSimpleGroup (X ⧸ K) := ψ.isSimpleGroup
  have hcardK : K.index = 20160 := by
    change Nat.card (X ⧸ K) = 20160
    rw [Nat.card_congr ψ.toEquiv, KFacts.L34.card_projSL]
  have hdvd : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → 20160 ∣ Nat.card (X ⧸ N) := by
    intro N hN hNs
    have hle : N ≤ K := Census.le_of_isSolvable_of_normal hN hNs
    rw [← hcardK]
    exact Subgroup.index_dvd_of_le hle
  rcases h44 X hX inferInstance K hK this with h1 | he2 | ⟨p, hp, hp3, he3⟩ | (he4 | h4b) |
    ⟨hO2, -⟩
  · exact h1
  ·
    exfalso
    obtain ⟨e2⟩ := he2
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h := hdvd _ inferInstance isSolvable_oTwoFitting
    rw [Nat.card_congr e2.toEquiv, Census.card_SL2] at h
    norm_num at h
  ·
    exfalso
    obtain ⟨e3⟩ := he3
    have : Fact p.Prime := ⟨hp⟩
    have hle : oTwoP p X ≤ K :=
      Census.le_of_isSolvable_of_normal inferInstance (isSolvable_oTwoP p)
    set F : SL(2, ZMod p) →* projSL 3 (GaloisField 2 2) :=
      ψ.toMonoidHom.comp ((QuotientGroup.map (oTwoP p X) K (MonoidHom.id X) hle).comp
        e3.symm.toMonoidHom) with hF
    have hFs : Function.Surjective F := by
      intro y
      obtain ⟨q, rfl⟩ := ψ.surjective y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
      refine ⟨e3 (x : X ⧸ oTwoP p X), ?_⟩
      rw [hF, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
      rfl
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨E, hE, hEc⟩ := exists_exponent_three_card_nine
    exact false_of_surjective_of_isCyclic_sylow F hFs
      (Census.isCyclic_sylow_SL2 (p := p) (by norm_num) (by omega)) hE hEc
  ·
    exfalso
    obtain ⟨e4⟩ := he4
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := hdvd _ inferInstance (isSolvable_oTwoP 3)
    rw [Nat.card_congr e4.toEquiv, ← Nat.card_congr Census.sl3EquivProjSL.toEquiv,
      Census.card_SL3_three] at h
    norm_num at h
  ·
    exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h := hdvd _ inferInstance (isSolvable_oTwoP 3)
    have hc := KFacts.L34.card_of_isExtOf h4b
    have hQ : Nat.card Q8D8 ≤ 64 := by
      have h1 : Nat.card Q8D8 ∣ Nat.card (QuaternionGroup 2 × DihedralGroup 4) :=
        Subgroup.card_quotient_dvd_card _
      have h2 : Nat.card (QuaternionGroup 2 × DihedralGroup 4) = 64 := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := QuaternionGroup 2), QuaternionGroup.card,
          DihedralGroup.nat_card]
      rw [h2] at h1
      exact Nat.le_of_dvd (by norm_num) h1
    have hA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      rfl
    rw [hc, hA5] at h
    have hpos : 0 < 60 * Nat.card Q8D8 := Nat.pos_of_ne_zero (by
      rw [← hA5, ← hc]
      exact Nat.card_pos.ne')
    have := Nat.le_of_dvd hpos h
    omega
  ·
    have hq := hres X hX inferInstance hO2 K hK h9 ⟨ψ⟩
    exact LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot).symm hq

end Exclusion

section Main

variable {G : Type} [Group G] [Finite G] {A M : Subgroup G}

theorem Ctx444.le_normalizer_of_mem_thetaComponents (h45 : Item4_5) (h : Ctx444 G A M)
    {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) : A ≤ Subgroup.normalizer (L : Set G) :=
  h45 G h.sectionFourHyp A h.isE27.isPGroup
    (Or.inr ⟨h.isE27.1, 3, le_rfl, by rw [h.isE27.2]; norm_num⟩) L hL

theorem Ctx444.three_dvd_card_of_not_le (h45 : Item4_5) (h : Ctx444 G A M) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hLM : ¬ L ≤ M) : 3 ∣ Nat.card L := by
  by_contra h3
  exact hLM (h.le_of_le_normalizer (h.le_normalizer_of_mem_thetaComponents h45 hL) h3)

theorem not_map_le_centralizer_of_commutator_eq {Q L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (h3 : 3 ∣ Nat.card L) (hcomm : ⁅L, Q⁆ = L) :
    ¬ Q.map (starQuot G) ≤
      Subgroup.centralizer (L.map (starQuot G) : Set (G ⧸ CFSG.pPrimeCore 3 G)) := by
  intro hle
  have hJ := isComponent_map_starQuot hL h3
  have hbot : (⁅L, Q⁆).map (starQuot G) = ⊥ := by
    rw [Subgroup.map_commutator, Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
  rw [hcomm] at hbot
  have : Nontrivial (L.map (starQuot G)) := isQuasisimple_nontrivial hJ.1
  rw [hbot] at this
  exact (not_nontrivial (⊥ : Subgroup (G ⧸ CFSG.pPrimeCore 3 G))) this

theorem Ctx444.isZ3L34OrHeisSL34_map_starQuot (h434 : Item4_34Sec) (h45 : Item4_5)
    (h : Ctx444 G A M) {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hQL : inSubgroup (CFSG.pPrimeCore 3) M ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ⁅L, inSubgroup (CFSG.pPrimeCore 3) M⁆ = L) (hLM : ¬ L ≤ M) :
    IsZ3L34OrHeisSL34 ((A ⊔ L).map (starQuot G)) := by
  set Q := inSubgroup (CFSG.pPrimeCore 3) M with hQ
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have h3L := h.three_dvd_card_of_not_le h45 hL hLM
  have hQ3 : ¬ 3 ∣ Nat.card Q := not_three_dvd_card_inSubgroup_pPrimeCore M
  obtain ⟨r, _, S, hAS, hSne⟩ := exists_sylow_not_le_centralizer hA3 hQ3
    h.le_normalizer_inSubgroup (not_map_le_centralizer_of_commutator_eq hL h3L hcomm)
  set R := (S : Subgroup Q).map Q.subtype with hR
  have hRQ : R ≤ Q := Subgroup.map_subtype_le _
  have hR3 : ¬ 3 ∣ Nat.card R := fun h3 => hQ3 (h3.trans (Subgroup.card_dvd_of_le hRQ))
  have hRp : IsPGroup r R := S.isPGroup'.map _
  have hs : Group.IsSolvable (A ⊔ R : Subgroup G) :=
    isSolvable_sup_of_le_normalizer (isSolvable_of_isPGroup hA3) (isSolvable_of_isPGroup hRp) hAS
  exact isZ3L34OrHeisSL34_of_item4_34Sec h434 h hL h3L hLM hAL (hRQ.trans hQL) hAS hR3 hs hSne

theorem rank3II_4_52_of (h434 : Item4_34Sec) (h45 : Item4_5) (h44 : Item4_4)
    (hres : Item4_52Residual) : Item4_52 := by
  intro G _ _ A M h _ L hL hQL hcomm hLM
  have hA3 : IsPGroup 3 A := h.isE27.isPGroup
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have h3L := h.three_dvd_card_of_not_le h45 hL hLM
  have hZ := h.isZ3L34OrHeisSL34_map_starQuot h434 h45 hL hQL hcomm hLM
  obtain ⟨K, _, hKs, h9, ⟨ψ⟩⟩ := exists_solvable_quotient_projSL hA3 hL h3L hAL hZ
  have : Group.IsPerfect L := hL.1
  exact ⟨hL.1, hL.2.1,
    quasisimple_of_item4_4 h44 hres (sectionFourHyp_subgroup h.sectionFourHyp L) hKs h9 ψ⟩

end Main

end CFSG.RankThree.PartTwo.Sec4
