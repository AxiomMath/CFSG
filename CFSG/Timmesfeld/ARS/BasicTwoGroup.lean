module

public import CFSG.Timmesfeld.ARS.Basic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem conjSub_eq_self_iff {H : Subgroup G} {g : G} :
    conjSub H g = H ↔ g ∈ Subgroup.normalizer (H : Set G) :=
  RankOne.map_conj_eq_self_iff

theorem le_normalizer_of_conjSub_le {F K : Subgroup G} (h : ∀ f ∈ F, conjSub K f ≤ K) :
    F ≤ Subgroup.normalizer (K : Set G) := by
  intro f hf
  rw [← RankOne.map_conj_eq_self_iff]
  refine le_antisymm (h f hf) ?_
  calc K = conjSub (conjSub K f⁻¹) f := by rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    _ ≤ conjSub K f := Subgroup.map_mono (h f⁻¹ (F.inv_mem hf))

theorem isPGroup_sup_of_commuting {E F : Subgroup G} (hE : IsPGroup 2 E) (hF : IsPGroup 2 F)
    (h : Commuting E F) : IsPGroup 2 ↥(E ⊔ F) :=
  IsPGroup.to_sup_of_normal_right' hE hF (le_normalizer_of_conjSub_le fun e he =>
    (conjSub_of_forall_commute fun f hf => h e he f hf).le)

theorem Special.isPGroup_sup (hR : IsRootClass R) {E F : Subgroup G} (hE : E ∈ R) (hF : F ∈ R)
    (h : Special R E F) : IsPGroup 2 ↥(E ⊔ F) := by
  have hDE : IsPGroup 2 ↥(⁅E, F⁆ ⊔ E) :=
    isPGroup_sup_of_commuting (hR.isPGroup h.1) (hR.isPGroup hE) h.2.1
  have hnorm : F ≤ Subgroup.normalizer ((⁅E, F⁆ ⊔ E : Subgroup G) : Set G) := by
    refine le_normalizer_of_conjSub_le fun f hf => ?_
    rw [conjSub, Subgroup.map_sup]
    exact sup_le ((conjSub_of_forall_commute fun d hd => (h.2.2 d hd f hf).symm).le.trans
      le_sup_left) (conjSub_le_commutator_sup hf)
  exact (IsPGroup.to_sup_of_normal_right' (hR.isPGroup hF) hDE hnorm).to_le
    (sup_le (le_sup_right.trans le_sup_right) le_sup_left)

theorem isPGroup_sup_of_not_opposite (hR : IsRootClass R) {E F : Subgroup G} (hE : E ∈ R)
    (hF : F ∈ R) (hEF : ¬ Opposite E F) : IsPGroup 2 ↥(E ⊔ F) := by
  by_cases h : E = F
  · subst h
    rw [sup_idem]
    exact hR.isPGroup hE
  rcases hR.rel E hE F hF h with hc | ho | hs
  · exact isPGroup_sup_of_commuting (hR.isPGroup hE) (hR.isPGroup hF) hc
  · exact absurd ho hEF
  · exact hs.isPGroup_sup hR hE hF

theorem isPGroup_of_forall_isPGroup_sup [Finite G] {S : Set (Subgroup G)} {M : Subgroup G}
    (hSM : ∀ E ∈ S, E ≤ M) (hMS : M ≤ ⨆ E ∈ S, E) (hinv : ∀ E ∈ S, ∀ m ∈ M, conjSub E m ∈ S)
    (hpair : ∀ E ∈ S, ∀ F ∈ S, IsPGroup 2 ↥(E ⊔ F)) : IsPGroup 2 M := by
  set P : Subgroup G := (CFSG.pCore 2 M).map M.subtype
  have hP : IsPGroup 2 P := (CFSG.BaerSuzuki.Helpers.pCore_isPGroup 2).map M.subtype
  refine hP.to_le (hMS.trans (iSup₂_le fun E hE => ?_))
  intro x hx
  have hxM : x ∈ M := hSM E hE hx
  refine ⟨⟨x, hxM⟩, ?_, rfl⟩
  rw [SetLike.mem_coe, CFSG.BaerSuzuki.baer_suzuki_iff]
  intro g
  have hpg := hpair E hE _ (hinv E hE g g.2)
  have hle : (Subgroup.closure ({⟨x, hxM⟩, g * ⟨x, hxM⟩ * g⁻¹} : Set M)).map M.subtype ≤
      E ⊔ conjSub E g := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right (conj_mem_conjSub (g : G) hx)
  exact (hpg.to_le hle).of_equiv (Subgroup.equivMapOfInjective _ M.subtype
    M.subtype_injective).symm

theorem CoveredBy.conj (hR : IsRootClass R) {H : Subgroup G} (h : CoveredBy R H) (g : G) :
    CoveredBy R (conjSub H g) := by
  rintro _ ⟨y, hy, rfl⟩ hy1
  have hy1' : y ≠ 1 := fun h1 => hy1 (by rw [h1, map_one])
  obtain ⟨C, hC, hCH, hyC⟩ := h y hy hy1'
  exact ⟨conjSub C g, hR.conjSub_mem hC g, Subgroup.map_mono hCH, ⟨y, hyC, rfl⟩⟩

theorem conjSub_mem_lambdaSet (hR : IsRootClass R) {A B : Subgroup G} (hB : B ∈ lambdaSet R A)
    (g : G) : conjSub B g ∈ lambdaSet R (conjSub A g) := by
  obtain ⟨⟨hBR, hBA, hAB⟩, hcov⟩ := hB
  refine ⟨⟨hR.conjSub_mem hBR g, fun h => hBA (RankOne.map_conj_inj.1 h), hAB.conjSub g⟩, ?_⟩
  have := hcov.conj hR g
  rwa [conjSub, Subgroup.map_sup] at this

theorem mem_lambdaSet_comm {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ lambdaSet R A) :
    A ∈ lambdaSet R B := by
  obtain ⟨⟨-, hBA, hAB⟩, hcov⟩ := hB
  exact ⟨⟨hA, hBA.symm, hAB.symm⟩, sup_comm A B ▸ hcov⟩

theorem isPGroup_M [Finite G] (hR : IsRootClass R) {A : Subgroup G} (hA : A ∈ R) :
    IsPGroup 2 (M R A) ∧ M R A ≤ Subgroup.normalizer (A : Set G) ∧
      ∀ g ∈ Subgroup.normalizer (A : Set G), conjSub (M R A) g = M R A := by
  have hMdef : M R A = A ⊔ ⨆ B ∈ lambdaSet R A, B := rfl
  have hAM : A ≤ M R A := hMdef ▸ le_sup_left
  have hBM : ∀ B ∈ lambdaSet R A, B ≤ M R A := fun B hB => hMdef ▸
    (le_iSup₂ (f := fun (E : Subgroup G) (_ : E ∈ lambdaSet R A) => E) B hB).trans le_sup_right
  have hcomm : Commuting A (M R A) := by
    rw [commuting_iff_le_centralizer, hMdef]
    refine sup_le (commuting_iff_le_centralizer.1 (hR.commuting_self hA))
      (iSup₂_le fun B hB => commuting_iff_le_centralizer.1 hB.1.2.2)
  have hMN : M R A ≤ Subgroup.normalizer (A : Set G) := le_normalizer_of_conjSub_le fun m hm =>
    (conjSub_of_forall_commute fun a ha => (hcomm a ha m hm).symm).le
  have hlam : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ B ∈ lambdaSet R A,
      conjSub B g ∈ lambdaSet R A := fun g hg B hB => by
    have := conjSub_mem_lambdaSet hR hB g
    rwa [conjSub_eq_self_iff.2 hg] at this
  have hnorm :
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((M R A : Subgroup G) : Set G) :=
    le_normalizer_of_conjSub_le fun g hg => by
      rw [Subgroup.map_le_iff_le_comap]
      nth_rewrite 1 [hMdef]
      refine sup_le (fun a ha => ?_) (iSup₂_le fun B hB => ?_)
      · rw [Subgroup.mem_comap]
        apply hAM
        have := conj_mem_conjSub g ha
        rwa [conjSub_eq_self_iff.2 hg] at this
      · rw [← Subgroup.map_le_iff_le_comap]
        exact hBM _ (hlam g hg B hB)
  refine ⟨?_, hMN, fun g hg => RankOne.map_conj_eq_self_iff.2 (hnorm hg)⟩
  refine isPGroup_of_forall_isPGroup_sup (S := insert A (lambdaSet R A)) ?_ ?_ ?_ ?_
  · rintro E (rfl | hE)
    · exact hAM
    · exact hBM E hE
  · rw [hMdef]
    exact sup_le (le_iSup₂_of_le A (Set.mem_insert _ _) le_rfl)
      (iSup₂_le fun B hB => le_iSup₂_of_le B (Set.mem_insert_of_mem _ hB) le_rfl)
  · rintro E (rfl | hE) m hm
    · rw [conjSub_eq_self_iff.2 (hMN hm)]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (hlam m (hMN hm) E hE)
  · have hR' : ∀ E ∈ insert A (lambdaSet R A), E ∈ R := by
      rintro E (rfl | hE)
      · exact hA
      · exact hE.1.1
    intro E hE F hF
    refine isPGroup_sup_of_not_opposite hR (hR' E hE) (hR' F hF) fun hop => ?_
    rcases hE with rfl | hE <;> rcases hF with rfl | hF
    · exact hop.ne rfl
    · exact hop.not_commuting (hR.ne_bot _ hA) hF.1.2.2
    · exact hop.symm.not_commuting (hR.ne_bot _ hA) hE.1.2.2
    · exact not_commuting_of_opposite_of_mem_lambdaSet hR hF.1.1 hop.symm
        (mem_lambdaSet_comm hA hE) hF.1.2.2.symm

theorem commutator_le_sup_conjSub [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) : ⁅A, B⁆ ≤ A ⊔ conjSub A b := by
  intro d hd
  obtain ⟨a, ha, rfl⟩ := (bijOn_commutator_left hR hiso hA hB h hb hb1).surjOn hd
  show ⁅a, b⁆ ∈ A ⊔ conjSub A b
  rw [commutatorElement_def, show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
    (Subgroup.mem_sup_right (conj_mem_conjSub b (A.inv_mem ha)))

theorem sup_conjSub_eq_sup_commutator [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) : A ⊔ conjSub A b = A ⊔ ⁅A, B⁆ :=
  le_antisymm (sup_le le_sup_left ((conjSub_le_commutator_sup hb).trans (sup_comm _ _).le))
    (sup_le le_sup_left (commutator_le_sup_conjSub hR hiso hA hB h hb hb1))

theorem commuting_conjSub_of_special (hR : IsRootClass R) {A B : Subgroup G} (hA : A ∈ R)
    (h : Special R A B) {b : G} (hb : b ∈ B) : Commuting A (conjSub A b) :=
  (Commuting.sup_left h.2.1 (hR.commuting_self hA)).symm.mono le_rfl
    (conjSub_le_commutator_sup hb)

variable {A B C : Subgroup G}

theorem commuting_sup_conjSub (hR : IsRootClass R) (hA : A ∈ R) (hC : C ∈ R)
    (hAB : Special R A B) (hBC : Special R B C) (hAC : Commuting A C) {b : G} (hb : b ∈ B) :
    Commuting (A ⊔ conjSub C b) (conjSub A b ⊔ C) := by
  have h1 : Commuting A (conjSub A b) := commuting_conjSub_of_special hR hA hAB hb
  have h2 : Commuting C (conjSub C b) := commuting_conjSub_of_special hR hC hBC.symm hb
  have h3 : Commuting (conjSub A b) (conjSub C b) := hAC.conjSub b
  exact Commuting.sup_left (Commuting.sup_right h1 hAC) (Commuting.sup_right h3.symm h2.symm)

theorem not_opposite_conjSub [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (hAB : Special R A B) (hBC : Special R B C)
    (hAC : Commuting A C) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) : ¬ Opposite A (conjSub C b) := by
  intro hop
  have hXY := commuting_sup_conjSub hR hA hC hAB hBC hAC hb
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
  have hgY : b * a * b⁻¹ ∈ conjSub A b ⊔ C := Subgroup.mem_sup_left (conj_mem_conjSub b ha)
  have hgcent : b * a * b⁻¹ ∈ Subgroup.centralizer ((A ⊔ conjSub C b : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hXY x hx _ hgY).eq
  have hroot : b * a * b⁻¹ * a⁻¹ ∈ rootElts R := by
    have e : b * a * b⁻¹ * a⁻¹ = ⁅b, a⁆ := (commutatorElement_def b a).symm
    refine ⟨⁅A, B⁆, hAB.1, ?_, ?_⟩
    · rw [e, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hb ha
    · rw [e]
      intro h1
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact hb1 (eq_one_of_commute_of_special hR hiso hA hB hAB ha ha1 hb h1.symm)
  by_cases hgX : b * a * b⁻¹ ∈ A ⊔ conjSub C b
  · exact ha1 (conj_eq_one_iff.1 (hop.eq_one_of_mem_centralizer (hR.mul_self A hA) hgX hgcent))
  · exact ha1 (inv_eq_one.1 (eq_one_of_mul_mem_rootElts hR hA hop hgcent hgX
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left ha)) hroot))

theorem commuting_conjSub_of_commuting [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hA : A ∈ R) (hB : B ∈ R) (hAB : Special R A B) (hAC : Commuting A C) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) (h : Commuting (conjSub A b) C) : Commuting A (conjSub C b) := by
  have h1 : Commuting (A ⊔ ⁅A, B⁆) C := by
    rw [← sup_conjSub_eq_sup_commutator hR hiso hA hB hAB hb hb1]
    exact Commuting.sup_left hAC h
  have h2 : Commuting (conjSub A b⁻¹) C :=
    h1.mono ((conjSub_le_commutator_sup (B.inv_mem hb)).trans (sup_comm _ _).le) le_rfl
  have h3 := h2.conjSub b
  rwa [← conjSub_mul, mul_inv_cancel, conjSub_one] at h3

theorem commuting_or_special_conjSub [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (hAB : Special R A B) (hBC : Special R B C)
    (hAC : Commuting A C) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    (Commuting A (conjSub C b) ∧ Commuting (conjSub A b) C) ∨
      (Special R A (conjSub C b) ∧ Special R (conjSub A b) C) := by
  by_cases hX : Commuting A (conjSub C b)
  · exact Or.inl ⟨hX, (commuting_conjSub_of_commuting hR hiso hC hB hBC.symm hAC.symm hb hb1
      hX.symm).symm⟩
  by_cases hY : Commuting (conjSub A b) C
  · exact absurd (commuting_conjSub_of_commuting hR hiso hA hB hAB hAC hb hb1 hY) hX
  refine Or.inr ⟨?_, ?_⟩
  · have hne : A ≠ conjSub C b := fun e => hX (by rw [← e]; exact hR.commuting_self hA)
    rcases hR.rel A hA _ (hR.conjSub_mem hC b) hne with h | h | h
    · exact absurd h hX
    · exact absurd h (not_opposite_conjSub hR hiso hA hB hC hAB hBC hAC hb hb1)
    · exact h
  · have hne : conjSub A b ≠ C := fun e => hY (by rw [e]; exact hR.commuting_self hC)
    rcases hR.rel _ (hR.conjSub_mem hA b) C hC hne with h | h | h
    · exact absurd h hY
    · exact absurd h.symm
        (not_opposite_conjSub hR hiso hC hB hA hBC.symm hAB.symm hAC.symm hb hb1)
    · exact h

theorem conjSub_sup_conjSub_eq [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (hAB : Special R A B) (hBC : Special R B C)
    {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    ∀ x ∈ A ⊔ B ⊔ C, conjSub ((A ⊔ conjSub C b) ⊔ (conjSub A b ⊔ C)) x =
      (A ⊔ conjSub C b) ⊔ (conjSub A b ⊔ C) := by
  have hN : (A ⊔ conjSub C b) ⊔ (conjSub A b ⊔ C) = (A ⊔ ⁅A, B⁆) ⊔ (C ⊔ ⁅C, B⁆) := by
    rw [← sup_conjSub_eq_sup_commutator hR hiso hA hB hAB hb hb1,
      ← sup_conjSub_eq_sup_commutator hR hiso hC hB hBC.symm hb hb1, sup_sup_sup_comm,
      sup_comm (conjSub C b) C]
  rw [hN]
  have hBN : B ≤ Subgroup.normalizer
      (((A ⊔ ⁅A, B⁆) ⊔ (C ⊔ ⁅C, B⁆) : Subgroup G) : Set G) := by
    refine le_normalizer_of_conjSub_le fun b' hb' => ?_
    rw [conjSub, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup]
    refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
    · exact (conjSub_le_commutator_sup hb').trans
        (sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left))
    · exact (conjSub_of_forall_commute fun d hd => (hAB.2.2 d hd b' hb').symm).le.trans
        (le_sup_right.trans le_sup_left)
    · exact (conjSub_le_commutator_sup hb').trans
        (sup_le (le_sup_right.trans le_sup_right) (le_sup_left.trans le_sup_right))
    · exact (conjSub_of_forall_commute fun d hd => (hBC.symm.2.2 d hd b' hb').symm).le.trans
        (le_sup_right.trans le_sup_right)
  have hle : A ⊔ B ⊔ C ≤ Subgroup.normalizer
      (((A ⊔ ⁅A, B⁆) ⊔ (C ⊔ ⁅C, B⁆) : Subgroup G) : Set G) :=
    sup_le (sup_le ((le_sup_left.trans le_sup_left).trans Subgroup.le_normalizer) hBN)
      ((le_sup_left.trans le_sup_right).trans Subgroup.le_normalizer)
  exact fun x hx => conjSub_eq_self_iff.2 (hle hx)

theorem sup_conjSub_sup_eq {b : G} (hb : b ∈ B) :
    (A ⊔ conjSub C b) ⊔ (conjSub A b ⊔ C) ⊔ B = A ⊔ B ⊔ C := by
  have hbR : b ∈ A ⊔ B ⊔ C := Subgroup.mem_sup_left (Subgroup.mem_sup_right hb)
  refine le_antisymm (sup_le (sup_le (sup_le (le_sup_left.trans le_sup_left) ?_)
    (sup_le ?_ le_sup_right)) (le_sup_right.trans le_sup_left)) ?_
  · exact conjSub_le le_sup_right hbR
  · exact conjSub_le (le_sup_left.trans le_sup_left) hbR
  · exact sup_le (sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) le_sup_right)
      (le_sup_right.trans (le_sup_right.trans le_sup_left))

theorem isPGroup_sup_of_special_special [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (hAB : Special R A B) (hBC : Special R B C)
    (hAC : Commuting A C) : IsPGroup 2 ↥(A ⊔ B ⊔ C) := by
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB
  have hX : IsPGroup 2 ↥(A ⊔ conjSub C b) := isPGroup_sup_of_not_opposite hR hA
    (hR.conjSub_mem hC b) (not_opposite_conjSub hR hiso hA hB hC hAB hBC hAC hb hb1)
  have hY : IsPGroup 2 ↥(conjSub A b ⊔ C) := isPGroup_sup_of_not_opposite hR
    (hR.conjSub_mem hA b) hC fun h =>
      not_opposite_conjSub hR hiso hC hB hA hBC.symm hAB.symm hAC.symm hb hb1 h.symm
  have hXY := isPGroup_sup_of_commuting hX hY (commuting_sup_conjSub hR hA hC hAB hBC hAC hb)
  have hBN : B ≤ Subgroup.normalizer
      (((A ⊔ conjSub C b) ⊔ (conjSub A b ⊔ C) : Subgroup G) : Set G) := fun b' hb' =>
    conjSub_eq_self_iff.1 (conjSub_sup_conjSub_eq hR hiso hA hB hC hAB hBC hb hb1 b'
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb')))
  have := IsPGroup.to_sup_of_normal_right' (hR.isPGroup hB) hXY hBN
  rwa [sup_comm, sup_conjSub_sup_eq hb] at this

theorem eq_one_of_odd_orderOf_of_isPGroup {P : Subgroup G} (hP : IsPGroup 2 P) {x : G}
    (hx : x ∈ P) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hdvd := orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
    (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem commutator_conjSub_eq [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    (hA : A ∈ R) (hB : B ∈ R) (hC : C ∈ R) (hAB : Special R A B) (hBC : Special R B C)
    (hAC : Commuting A C) {a c : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hc : c ∈ C) (hc1 : c ≠ 1)
    (hac : a * c ∈ rootElts R) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    ⁅A, conjSub C b⁆ = ⁅conjSub A b, C⁆ := by
  rcases commuting_or_special_conjSub hR hiso hA hB hC hAB hBC hAC hb hb1 with ⟨hX, hY⟩ | ⟨hX, hY⟩
  · rw [commuting_iff_commutator_eq_bot.1 hX, commuting_iff_commutator_eq_bot.1 hY]
  set α' := b * a * b⁻¹ with hα'
  set γ' := b * c * b⁻¹ with hγ'
  have hα'm : α' ∈ conjSub A b := conj_mem_conjSub b ha
  have hγ'm : γ' ∈ conjSub C b := conj_mem_conjSub b hc
  have hP := isPGroup_sup_of_special_special hR hiso hA hB hC hAB hBC hAC
  obtain ⟨E, hE, hacE, hac1⟩ := hac
  have hcomm : Commute (a * c) (b * (a * c) * b⁻¹) := by
    have hfix : Commute (a * c) b → Commute (a * c) (b * (a * c) * b⁻¹) := fun h' => by
      rw [← h'.eq, mul_inv_cancel_right]
    by_cases hEB : E = B
    · subst hEB
      exact hfix (hR.commute hE hacE hb)
    rcases hR.rel E hE B hB hEB with h | h | h
    · exact hfix (h _ hacE b hb)
    · exfalso
      have hodd := h.odd_orderOf_mul (hR.mul_self E hE) hacE hac1 hb hb1
      have hmem : a * c * b ∈ A ⊔ B ⊔ C := Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right hc))
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hb))
      have h1 := eq_one_of_odd_orderOf_of_isPGroup hP hmem hodd
      have hbE : b ∈ E := by
        rw [← inv_eq_of_mul_eq_one_right h1]
        exact E.inv_mem hacE
      have : b ∈ E ⊓ B := ⟨hbE, hb⟩
      rw [inf_eq_bot hR hiso hE hB hEB, Subgroup.mem_bot] at this
      exact hb1 this
    · rw [conj_eq_commutator_mul]
      have hd : Commute ⁅b, a * c⁆ (a * c) := by
        refine h.2.1 _ ?_ _ hacE
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hb hacE
      exact hd.symm.mul_right (Commute.refl _)
  have hXY := commuting_sup_conjSub hR hA hC hAB hBC hAC hb
  have huX : ⁅a, γ'⁆ ∈ A ⊔ conjSub C b := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ha)
      (Subgroup.mem_sup_right hγ'm)) (Subgroup.inv_mem _ (Subgroup.mem_sup_left ha)))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hγ'm))
  have hvY : ⁅α', c⁆ ∈ conjSub A b ⊔ C := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left hα'm) (Subgroup.mem_sup_right hc))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left hα'm)))
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hc))
  have R1 : γ' * a = ⁅a, γ'⁆⁻¹ * a * γ' := by rw [commutatorElement_def]; group
  have R2 : α' * c = ⁅α', c⁆ * c * α' := by rw [commutatorElement_def]; group
  have C1 : α' * ⁅a, γ'⁆⁻¹ = ⁅a, γ'⁆⁻¹ * α' :=
    ((hXY _ huX α' (Subgroup.mem_sup_left hα'm)).inv_left).symm.eq
  have C2 : α' * a = a * α' := (commuting_conjSub_of_special hR hA hAB hb a ha α' hα'm).symm.eq
  have C3 : γ' * c = c * γ' :=
    (commuting_conjSub_of_special hR hC hBC.symm hb c hc γ' hγ'm).symm.eq
  have C4 : a * ⁅α', c⁆ = ⁅α', c⁆ * a := (hXY a (Subgroup.mem_sup_left ha) _ hvY).eq
  have key : α' * γ' * (a * c) = ⁅a, γ'⁆⁻¹ * ⁅α', c⁆ * (a * c * (α' * γ')) := by
    calc α' * γ' * (a * c) = α' * (γ' * a) * c := by group
      _ = α' * (⁅a, γ'⁆⁻¹ * a * γ') * c := by rw [R1]
      _ = (α' * ⁅a, γ'⁆⁻¹) * a * γ' * c := by group
      _ = (⁅a, γ'⁆⁻¹ * α') * a * γ' * c := by rw [C1]
      _ = ⁅a, γ'⁆⁻¹ * (α' * a) * (γ' * c) := by group
      _ = ⁅a, γ'⁆⁻¹ * (a * α') * (c * γ') := by rw [C2, C3]
      _ = ⁅a, γ'⁆⁻¹ * a * (α' * c) * γ' := by group
      _ = ⁅a, γ'⁆⁻¹ * a * (⁅α', c⁆ * c * α') * γ' := by rw [R2]
      _ = ⁅a, γ'⁆⁻¹ * (a * ⁅α', c⁆) * c * α' * γ' := by group
      _ = ⁅a, γ'⁆⁻¹ * (⁅α', c⁆ * a) * c * α' * γ' := by rw [C4]
      _ = ⁅a, γ'⁆⁻¹ * ⁅α', c⁆ * (a * c * (α' * γ')) := by group
  have hbac : b * (a * c) * b⁻¹ = α' * γ' := by rw [hα', hγ']; group
  rw [hbac] at hcomm
  have huv : ⁅a, γ'⁆ = ⁅α', c⁆ := by
    have h1 : a * c * (α' * γ') = ⁅a, γ'⁆⁻¹ * ⁅α', c⁆ * (a * c * (α' * γ')) := by
      rw [← key, hcomm.eq]
    rw [right_eq_mul, inv_mul_eq_one] at h1
    exact h1
  have hu1 : ⁅a, γ'⁆ ≠ 1 := by
    intro h1
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    have := eq_one_of_commute_of_special hR hiso hA (hR.conjSub_mem hC b) hX ha ha1 hγ'm h1
    exact hc1 (conj_eq_one_iff.1 this)
  by_contra hne
  have hmem : ⁅a, γ'⁆ ∈ ⁅A, conjSub C b⁆ ⊓ ⁅conjSub A b, C⁆ :=
    ⟨Subgroup.commutator_mem_commutator ha hγ'm,
      huv ▸ Subgroup.commutator_mem_commutator hα'm hc⟩
  rw [inf_eq_bot hR hiso hX.1 hY.1 hne, Subgroup.mem_bot] at hmem
  exact hu1 hmem

end CFSG.Timmesfeld.ARS
