module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34U4Sec
public import CFSG.Quasithin.H13.U4ParRecog
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsDSSz

public section

namespace CFSG.Quasithin.H13.U4V

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.U4Par
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

section Glue

variable {G : Type} [Group G]

theorem normal_of_commutator_le {H : Subgroup G} (hH : commutator G ≤ H) : H.Normal := by
  refine ⟨fun x hx g => ?_⟩
  have h1 : g * x * g⁻¹ * x⁻¹ ∈ H :=
    hH (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x))
  have h2 := H.mul_mem h1 hx
  simpa using h2

theorem commutator_le_subgroupOf {X H : Subgroup G} (hXH : ⁅X, X⁆ ≤ H) :
    commutator ↥X ≤ H.subgroupOf X := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  apply hXH
  have e : (commutator ↥X).map X.subtype = ⁅X, X⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← e]
  exact ⟨x, hx, rfl⟩

theorem commutator_le_of_index_le_two [Finite G] {H : Subgroup G} (hidx : H.index ≤ 2) :
    commutator G ≤ H := by
  have hn : H.Normal := normal_of_index_le_two hidx
  have hc : ∀ a b : G ⧸ H, a * b = b * a := by
    have hcard : Nat.card (G ⧸ H) ≤ 2 := by rw [← Subgroup.index]; exact hidx
    rcases Nat.lt_or_ge (Nat.card (G ⧸ H)) 2 with h1 | h2
    · have hpos : 0 < Nat.card (G ⧸ H) := Nat.card_pos
      have h11 : Nat.card (G ⧸ H) = 1 := by omega
      have : Subsingleton (G ⧸ H) := (Nat.card_eq_one_iff_unique.mp h11).1
      exact fun a b => Subsingleton.elim _ _
    · have h22 : Nat.card (G ⧸ H) = 2 := by omega
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : IsCyclic (G ⧸ H) := isCyclic_of_prime_card h22
      exact fun a b => (IsCyclic.commGroup (α := G ⧸ H)).mul_comm a b
  rw [commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [hc (QuotientGroup.mk a) (QuotientGroup.mk b)]
  group

end Glue

section Model

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem mem_radQ_of_rhoF_eq_one {g : parH h} (hg : rhoF h g = 1) :
    (g : hypSU h 2 0) ∈ radQ h := by
  refine mem_radQ_of_chi_rho h (parH_le_parP h g.2) g.2.2.1 ?_
  have h1 : rhoFMat h g = 1 := by
    have h2 : ((rhoF h g : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
        Matrix (Fin 2) (Fin 2) h.fixedField) =
        ((1 : Matrix.SpecialLinearGroup (Fin 2) h.fixedField) :
          Matrix (Fin 2) (Fin 2) h.fixedField) := congrArg Subtype.val hg
    rw [Matrix.SpecialLinearGroup.coe_one] at h2
    exact h2
  rw [← map_rhoFMat h g, h1]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isPGroup_ker_rhoF : IsPGroup 2 (rhoF h).ker := by
  intro g
  obtain ⟨k, hk⟩ := radQ_isPGroup h ⟨_, mem_radQ_of_rhoF_eq_one h (MonoidHom.mem_ker.mp g.2)⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg Subtype.val hk
  simpa using h1

theorem isPGroup_ker_rho2F : IsPGroup 2 (rho2F h).ker := by
  intro g
  have hg : rho2 h ((g : parH2 h) : hypSU h 2 0) = 1 := by
    have h2 : ((rho2F h (g : parH2 h) : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = ((1 : Matrix.SpecialLinearGroup (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K) :=
      congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K))
        (MonoidHom.mem_ker.mp g.2)
    rw [Matrix.SpecialLinearGroup.coe_one] at h2
    exact h2
  obtain ⟨k, hk⟩ := radQ2_isPGroup h ⟨_, mem_radQ2_of_rho2 h (parH2_le_parP2 h (g : parH2 h).2) hg⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg Subtype.val hk
  simpa using h1

theorem nsSecThree_parP : NSSecThree ↥(parP h) := by
  have := h.finite
  have := U4Par.finite_hypSU h
  have := charP_fixedField h
  have hH : NSSecThree ↥(parH h) :=
    NSSecThree.of_ker (rhoF h) (isPGroup_ker_rhoF h) nsSecThree_sl2
  exact NSSecThree.of_commutator_le ((parH h).subgroupOf (parP h))
    (commutator_le_subgroupOf (commutator_parP_le h))
    (hH.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (parH_le_parP h)))

theorem nsSecThree_parP2 : NSSecThree ↥(parP2 h) := by
  have := h.finite
  have := U4Par.finite_hypSU h
  have := h.charP
  have hH : NSSecThree ↥(parH2 h) :=
    NSSecThree.of_ker (rho2F h) (isPGroup_ker_rho2F h) nsSecThree_sl2
  exact NSSecThree.of_commutator_le ((parH2 h).subgroupOf (parP2 h))
    (commutator_le_subgroupOf (commutator_parP2_le h))
    (hH.of_mulEquiv (Subgroup.subgroupOfEquivOfLe (parH2_le_parP2 h)))

theorem isSolvable_parP_one (h : UnitaryFieldData 2 1 K) : Group.IsSolvable ↥(parP h) := by
  have := h.finite
  have := U4Par.finite_hypSU h
  have := charP_fixedField h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) := by
    refine isSolvable_of_card_primeFactors_le_two ?_
    have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) h.fixedField) = 2 * 3 := by
      rw [CFSG.GorensteinWalter.sl2_card_formula, h.card_fixedField]
      norm_num
    rw [h6, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.prime_two.primeFactors,
      Nat.prime_three.primeFactors]
    decide
  have hker : Group.IsSolvable ↥(rhoF h).ker := by
    have := (isPGroup_ker_rhoF h).isNilpotent
    infer_instance
  have hH : Group.IsSolvable ↥(parH h) :=
    Group.isSolvable_of_ker_le_range (rhoF h).ker.subtype (rhoF h)
      (by rw [Subgroup.range_subtype])
  have hle := commutator_le_subgroupOf (commutator_parP_le h)
  have : ((parH h).subgroupOf (parP h)).Normal := normal_of_commutator_le hle
  have hHs : Group.IsSolvable ↥((parH h).subgroupOf (parP h)) :=
    Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe (parH_le_parP h)).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe (parH_le_parP h)).symm.surjective
  have hQ : Group.IsSolvable (↥(parP h) ⧸ (parH h).subgroupOf (parP h)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        apply hle
        have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
          rw [commutatorElement_def]
          group
        rw [e]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact Group.isSolvable_of_ker_le_range ((parH h).subgroupOf (parP h)).subtype
    (QuotientGroup.mk' ((parH h).subgroupOf (parP h)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem not_isSolvable_parP2 : ¬ Group.IsSolvable ↥(parP2 h) := by
  intro hs
  have := h.finite
  have := h.charP
  have hinj : Function.Injective (lev2Hom h) := by
    intro A B hAB
    have h1 := congrArg (rho2 h) hAB
    rw [rho2_lev2Hom, rho2_lev2Hom] at h1
    exact Subtype.ext h1
  let f : Matrix.SpecialLinearGroup (Fin 2) K →* ↥(parP2 h) :=
    (lev2Hom h).codRestrict (parP2 h) fun A => lev2Hom_le_parP2 h ⟨A, rfl⟩
  have hf : Function.Injective f := fun A B hAB => hinj (congrArg Subtype.val hAB)
  have : Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective hf
  have := isSimpleGroup_sl2_of_charTwo K (four_le_card h)
  obtain ⟨A, B, hAB⟩ := exists_sl2_ne_comm K
  exact hAB (IsSimpleGroup.comm_iff_isSolvable.mpr inferInstance A B)

end Model

section Recog

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) {Y : Type} [Group Y]

theorem exists_adapted [Finite Y] {ψ : hypSU h 2 0 →* Y} (hψ : Function.Injective ψ)
    (hidx : ψ.range.index ≤ 2) {T : Subgroup Y} (hT : IsSylowTwoOf T ⊤) :
    ∃ ψ' : hypSU h 2 0 →* Y, Function.Injective ψ' ∧ ψ'.range = ψ.range ∧
      (hypUnitriangular h 2 0).map ψ' = T ⊓ ψ.range :=
  exists_conj_eq_sylow h hT hψ (normal_of_index_le_two hidx)

theorem inf_eq_of_adapted [Finite Y] (ψ : hypSU h 2 0 →* Y) (hψ : Function.Injective ψ)
    (hidx : ψ.range.index ≤ 2) {T M₁ M : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M)
    (hU : (hypUnitriangular h 2 0).map ψ = T ⊓ ψ.range) :
    ∃ i : Fin 2, M = Subgroup.normalizer
        (((![(parP h).map ψ, (parP2 h).map ψ] : Fin 2 → Subgroup Y) i : Subgroup Y) : Set Y) ∧
      M ⊓ ψ.range = (![(parP h).map ψ, (parP2 h).map ψ] : Fin 2 → Subgroup Y) i := by
  have := h.finite
  have := U4Par.finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ψ.range.Normal := normal_of_index_le_two hidx
  have hB : ψ.range ⊓ Subgroup.normalizer ((T ⊓ ψ.range : Subgroup Y) : Set Y) =
      (hypBorel h 2 0).map ψ := by
    rw [← hU, inf_normalizer_map hψ,
      UnitaryHigher.normalizer_hypUnitriangular h (by norm_num) (by norm_num)]
  have hsimple : ∀ N : Subgroup Y, N ≤ ψ.range → ψ.range ≤ Subgroup.normalizer (N : Set Y) →
      N = ⊥ ∨ N = ψ.range := by
    intro N hN hnN
    have := isSimpleGroup_hypSU h
    have hNn : (N.comap ψ).Normal := ⟨fun n hn g => by
      have := (Subgroup.mem_normalizer_iff.mp (hnN ⟨g, rfl⟩) (ψ n)).mp hn
      simpa [Subgroup.mem_comap, map_mul, map_inv] using this⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap ψ) with h0 | h0
    · left
      rw [← Subgroup.map_comap_eq_self hN, h0, Subgroup.map_bot]
    · right
      rw [← Subgroup.map_comap_eq_self hN, h0, ← MonoidHom.range_eq_map]
  have hnot2 : ¬ IsPGroup 2 ψ.range := fun hp =>
    not_isPGroup_hypSU h (hp.of_injective ψ.rangeRestrict
      (MonoidHom.rangeRestrict_injective_iff.mpr hψ))
  set P : Fin 2 → Subgroup Y := ![(parP h).map ψ, (parP2 h).map ψ] with hPdef
  have hP0 : P 0 = (parP h).map ψ := rfl
  have hP1 : P 1 = (parP2 h).map ψ := rfl
  have hBP : ∀ i, ψ.range ⊓ Subgroup.normalizer ((T ⊓ ψ.range : Subgroup Y) : Set Y) ≤ P i := by
    intro i
    rw [hB]
    fin_cases i
    · exact Subgroup.map_mono (UnitaryHigher.hypBorel_le_isoStabilizer h le_rfl (by norm_num))
    · exact Subgroup.map_mono (UnitaryHigher.hypBorel_le_isoStabilizer h (by norm_num) le_rfl)
  have hPmax : ∀ i, IsMaxIn (P i) ψ.range := by
    intro i
    fin_cases i
    · exact (isMaxIn_map_iff hψ _).mpr (isCoatom_parP h)
    · exact (isMaxIn_map_iff hψ _).mpr (isCoatom_parP2 h)
  have hPuniq : ∀ A : Subgroup Y, IsMaxIn A ψ.range →
      ψ.range ⊓ Subgroup.normalizer ((T ⊓ ψ.range : Subgroup Y) : Set Y) ≤ A → ∃ i, A = P i := by
    intro A hA hBA
    rw [hB] at hBA
    have hA' : A = (A.comap ψ).map ψ := (Subgroup.map_comap_eq_self hA.1.le).symm
    have hco : IsCoatom (A.comap ψ) := (isMaxIn_map_iff hψ _).mp (hA' ▸ hA)
    have hBA' : hypBorel h 2 0 ≤ A.comap ψ := Subgroup.map_le_iff_le_comap.mp hBA
    rcases eq_parP_or_eq_parP2 h hco hBA' with e | e
    · refine ⟨0, ?_⟩
      rw [hP0, hA', e]
    · refine ⟨1, ?_⟩
      rw [hP1, hA', e]
  have hne : P 0 ≠ P 1 := by
    rw [hP0, hP1]
    intro e
    exact parP_ne_parP2 h (Subgroup.map_injective hψ e)
  have hO : ∀ i, pCoreOf 2 (P i) ≠ ⊥ := by
    intro i
    fin_cases i
    · change pCoreOf 2 ((parP h).map ψ) ≠ ⊥
      rw [pCoreOf_map_of_inj hψ, Ne, Subgroup.map_eq_bot_iff_of_injective _ hψ]
      exact pCoreOf_parP_ne_bot h
    · change pCoreOf 2 ((parP2 h).map ψ) ≠ ⊥
      rw [pCoreOf_map_of_inj hψ, Ne, Subgroup.map_eq_bot_iff_of_injective _ hψ]
      exact pCoreOf_parP2_ne_bot h
  have hswap : ∀ x : Y, (P 0).map (MulAut.conj x).toMonoidHom ≠ P 1 := by
    intro x e
    have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
    rcases Nat.lt_or_ge m 2 with hm1 | hm
    ·
      have hm1' : m = 1 := by have := h.one_le; omega
      subst hm1'
      apply not_isSolvable_parP2 h
      have hs := isSolvable_parP_one h
      let e1 : ↥(parP h) ≃* ↥(P 0) := (parP h).equivMapOfInjective ψ hψ
      let e2 : ↥(P 0) ≃* ↥(P 1) :=
        ((P 0).equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr e)
      let e3 : ↥(parP2 h) ≃* ↥(P 1) := (parP2 h).equivMapOfInjective ψ hψ
      exact Group.isSolvable_of_surjective (f := ((e1.trans e2).trans e3.symm).toMonoidHom)
        ((e1.trans e2).trans e3.symm).surjective
    ·
      have hcore0 : pCoreOf 2 (perfectCore (P 0)) = (radQ h).map ψ := by
        rw [hP0, ← map_perfectCore, pCoreOf_map_of_inj hψ, pCoreOf_perfectCore_parP h hm]
      have hcore1 : ∀ a ∈ pCoreOf 2 (perfectCore (P 1)), ∀ b ∈ pCoreOf 2 (perfectCore (P 1)),
          a * b = b * a := by
        rw [hP1, ← map_perfectCore, pCoreOf_map_of_inj hψ, comm_map_iff hψ]
        exact fun a ha b hb => pCoreOf_perfectCore_parP2_comm h ha hb
      have hc := hcore1
      rw [← e, ← map_perfectCore, pCoreOf_map_of_inj hinj, hcore0, comm_map_iff hinj,
        comm_map_iff hψ] at hc
      obtain ⟨a, ha, b, hb, hab⟩ := exists_radQ_ne_comm h
      exact hab (hc a ha b hb)
  obtain ⟨i, hMi, hMY, -⟩ := eq_normalizer_of_isYAmalgamPair hidx hsimple hnot2 hpair P hBP
    hPmax hPuniq hne hO hswap
  exact ⟨i, hMi, hMY⟩

end Recog

section Members

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K) {Y : Type} [Group Y]

theorem commutator_le_subgroupOf_of_index [Finite Y] {Y₀ : Subgroup Y} (hidx : Y₀.index ≤ 2)
    (M : Subgroup Y) : commutator ↥M ≤ Y₀.subgroupOf M :=
  commutator_le_subgroupOf ((Subgroup.commutator_mono le_top le_top).trans
    (by rw [← commutator_def]; exact commutator_le_of_index_le_two hidx))

@[expose] noncomputable def subgroupOfEquivInf (M Y₀ : Subgroup Y) :
    ↥(Y₀.subgroupOf M) ≃* ↥(M ⊓ Y₀) :=
  (MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_left Y₀ M).symm).trans
    (Subgroup.subgroupOfEquivOfLe inf_le_left)

theorem nsSecThree_of_isYAmalgamPair [Finite Y]
    (ψ : hypSU h 2 0 →* Y) (hψ : Function.Injective ψ) (hidx : ψ.range.index ≤ 2)
    {T M₁ M : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M) : NSSecThree ↥M := by
  obtain ⟨ψ', hψ', hrange, hU⟩ := exists_adapted h hψ hidx hpair.1
  rw [← hrange] at hidx hU
  obtain ⟨i, -, hMY⟩ := inf_eq_of_adapted h ψ' hψ' hidx hpair hU
  refine NSSecThree.of_commutator_le (ψ'.range.subgroupOf M)
    (commutator_le_subgroupOf_of_index hidx M) ?_
  fin_cases i
  · have hMY' : M ⊓ ψ'.range = (parP h).map ψ' := hMY
    exact (nsSecThree_parP h).of_mulEquiv ((subgroupOfEquivInf M ψ'.range).trans
      ((MulEquiv.subgroupCongr hMY').trans ((parP h).equivMapOfInjective ψ' hψ').symm))
  · have hMY' : M ⊓ ψ'.range = (parP2 h).map ψ' := hMY
    exact (nsSecThree_parP2 h).of_mulEquiv ((subgroupOfEquivInf M ψ'.range).trans
      ((MulEquiv.subgroupCongr hMY').trans ((parP2 h).equivMapOfInjective ψ' hψ').symm))

end Members

theorem isYAmalgamPair_swap {Y : Type} [Group Y] {T M₁ M₂ : Subgroup Y}
    (h : IsYAmalgamPair T M₁ M₂) : IsYAmalgamPair T M₂ M₁ :=
  ⟨h.1, h.2.1.symm, fun M => (h.2.2 M).trans or_comm⟩

theorem u4ExtTwoVertexFact_holds : U4ExtTwoVertexFact := by
  intro f α _ hα
  obtain ⟨Y, _, Ŷ, _, ι, hY, hι, hidx, T, M₁, M₂, hpair, ⟨e⟩⟩ := hα
  obtain ⟨hfin, K, _, h, ψ, hψ, hidx'⟩ :=
    U4Par.exists_embedding (Y := Ŷ) (Or.inr ⟨Y, inferInstance, ι, hY, hι, hidx⟩)
  exact ⟨(nsSecThree_of_isYAmalgamPair h ψ hψ hidx' (isYAmalgamPair_swap hpair)).of_mulEquiv e.φ1,
    (nsSecThree_of_isYAmalgamPair h ψ hψ hidx' hpair).of_mulEquiv e.φ2⟩

theorem exists_isSolvable_of_isYAmalgamPair {Y : Type} [Group Y]
    (hY : CFSG.Blueprint.LieModel Y .PSU 4 2 1 ∨
      ∃ (Y₀ : Type) (_ : Group Y₀) (ι : Y₀ →* Y), CFSG.Blueprint.LieModel Y₀ .PSU 4 2 1 ∧
        Function.Injective ι ∧ ι.range.index = 2)
    {T M₁ M₂ : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M₂) :
    Group.IsSolvable ↥M₁ ∨ Group.IsSolvable ↥M₂ := by
  obtain ⟨hfin, K, _, h, ψ, hψ, hidx⟩ := U4Par.exists_embedding hY
  obtain ⟨ψ', hψ', hrange, hU⟩ := exists_adapted h hψ hidx hpair.1
  rw [← hrange] at hidx hU
  have key : ∀ M : Subgroup Y, M ⊓ ψ'.range = (parP h).map ψ' → Group.IsSolvable ↥M := by
    intro M hM
    have hs := isSolvable_parP_one h
    let e : ↥(ψ'.range.subgroupOf M) ≃* ↥(parP h) := (subgroupOfEquivInf M ψ'.range).trans
      ((MulEquiv.subgroupCongr hM).trans ((parP h).equivMapOfInjective ψ' hψ').symm)
    have h1 : Group.IsSolvable ↥(ψ'.range.subgroupOf M) :=
      Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hle := commutator_le_subgroupOf_of_index hidx M
    have : (ψ'.range.subgroupOf M).Normal := normal_of_commutator_le hle
    have h2 : Group.IsSolvable (↥M ⧸ ψ'.range.subgroupOf M) := by
      refine Group.isSolvable_of_comm fun a b => ?_
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          apply hle
          have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
            rw [commutatorElement_def]
            group
          rw [e]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    exact Group.isSolvable_of_ker_le_range (ψ'.range.subgroupOf M).subtype
      (QuotientGroup.mk' (ψ'.range.subgroupOf M))
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
  obtain ⟨i₂, hM₂, hM₂Y⟩ := inf_eq_of_adapted h ψ' hψ' hidx hpair hU
  obtain ⟨i₁, hM₁, hM₁Y⟩ := inf_eq_of_adapted h ψ' hψ' hidx (isYAmalgamPair_swap hpair) hU
  have hne : i₁ ≠ i₂ := by
    rintro rfl
    exact hpair.2.1 (hM₁.trans hM₂.symm)
  fin_cases i₁
  · exact Or.inl (key M₁ hM₁Y)
  · fin_cases i₂
    · exact Or.inr (key M₂ hM₂Y)
    · exact absurd rfl hne

end CFSG.Quasithin.H13.U4V
