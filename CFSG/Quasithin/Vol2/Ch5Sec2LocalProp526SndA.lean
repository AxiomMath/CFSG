module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Tr
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.Quasithin.H13

open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf

namespace Sec526

theorem card_eq_two_pow_of_odd_index {H : Type*} [Group H] {T : Subgroup H} [Finite T]
    (hT : IsPGroup 2 T) (hidx : ¬ 2 ∣ T.index) :
    Nat.card T = 2 ^ (Nat.card H).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  have hidx0 : T.index ≠ 0 := fun h => hidx (h ▸ dvd_zero 2)
  rw [← Subgroup.card_mul_index T, hk, Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hidx0,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem finite_and_factorization_of_pair {Y : Type*} [Group Y] {T M₁ M₂ : Subgroup Y}
    (hpair : IsYAmalgamPair T M₁ M₂) {H : Type*} [Group H] [Finite H] (e : ↥(M₁ ⊓ M₂) ≃* H) :
    Finite Y ∧ (Nat.card Y).factorization 2 = (Nat.card H).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hT2, hTidx⟩ := hpair.1
  have hTidx' : ¬ 2 ∣ T.index := by
    have e1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    rwa [e1] at hTidx
  have hTM : T ≤ M₁ ⊓ M₂ := le_inf
    (Subgroup.le_normalizer.trans ((hpair.2.2 M₁).mpr (Or.inl rfl)).2)
    (Subgroup.le_normalizer.trans ((hpair.2.2 M₂).mpr (Or.inr rfl)).2)
  have : Finite ↥(M₁ ⊓ M₂) := Finite.of_equiv _ e.symm.toEquiv
  have : Finite ↥T :=
    Finite.of_injective (Subgroup.inclusion hTM) (Subgroup.inclusion_injective hTM)
  have hidx0 : T.index ≠ 0 := fun h => hTidx' (h ▸ dvd_zero 2)
  have hY0 : Nat.card Y ≠ 0 := by
    rw [← Subgroup.card_mul_index T]
    exact mul_ne_zero Nat.card_pos.ne' hidx0
  refine ⟨Nat.finite_of_card_ne_zero hY0, ?_⟩
  set T' := T.subgroupOf (M₁ ⊓ M₂) with hT'
  have hTe : ↥T' ≃* ↥T := Subgroup.subgroupOfEquivOfLe hTM
  have : Finite ↥T' := Finite.of_equiv _ hTe.symm.toEquiv
  have hT'2 : IsPGroup 2 T' := hT2.of_equiv hTe.symm
  have hT'idx : ¬ 2 ∣ T'.index := fun h =>
    hTidx' (h.trans (Subgroup.relIndex_dvd_index_of_le hTM))
  have h1 := card_eq_two_pow_of_odd_index hT2 hTidx'
  have h2 := card_eq_two_pow_of_odd_index hT'2 hT'idx
  rw [Nat.card_congr hTe.toEquiv, h1, Nat.card_congr e.toEquiv] at h2
  exact Nat.pow_right_injective le_rfl h2

@[expose] def VertexIso {G : Type*} [Group G] (P₁ P₂ : Subgroup G) {Y : Type*} [Group Y]
    (M₁ M₂ : Subgroup Y) : Prop :=
  Nonempty (↥P₁ ≃* ↥M₁) ∧ Nonempty (↥(P₁ ⊓ P₂) ≃* ↥(M₁ ⊓ M₂)) ∧ Nonempty (↥P₂ ≃* ↥M₂)

variable {G : Type} [Group G]

theorem exists_vertexIso_of_isAmalgamOfGroup {P₁ P₂ : Subgroup G}
    {Pr : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P₁ P₂) Pr) :
    ∃ (Y : Type) (_ : Group Y), Pr Y ∧ ∃ T M₁ M₂ : Subgroup Y, IsYAmalgamPair T M₁ M₂ ∧
      VertexIso P₁ P₂ M₁ M₂ := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨e⟩⟩ := h
  exact ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨e.φ1⟩, ⟨e.φ12⟩, ⟨e.φ2⟩⟩

theorem exists_vertexIso_of_isParabolicAmalgamOfGroup {P₁ P₂ : Subgroup G}
    {Pr : ∀ (Y : Type) [Group Y], Prop}
    (h : IsParabolicAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P₁ P₂) Pr) :
    ∃ (Y : Type) (_ : Group Y), Pr Y ∧ ∃ T M₁ M₂ : Subgroup Y, IsYAmalgamPair T M₁ M₂ ∧
      VertexIso P₁ P₂ M₁ M₂ := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hiso⟩ := h
  exact ⟨Y, _, hY, T, M₁, M₂, hpair, hiso⟩

theorem factorization_eq_of_vertexIso [Finite G] {P₁ P₂ : Subgroup G} {Y : Type} [Group Y]
    {T M₁ M₂ : Subgroup Y} (hpair : IsYAmalgamPair T M₁ M₂) (hv : VertexIso P₁ P₂ M₁ M₂) :
    Finite Y ∧ (Nat.card Y).factorization 2 = (Nat.card ↥(P₁ ⊓ P₂)).factorization 2 := by
  obtain ⟨-, ⟨e⟩, -⟩ := hv
  exact finite_and_factorization_of_pair hpair e.symm

theorem factorization_eq_of_isAmalgamOfGroup [Finite G] {P₁ P₂ : Subgroup G}
    {Pr : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups P₁ P₂) Pr) {k : ℕ}
    (hk : ∀ (Y : Type) [Group Y], Pr Y → (Nat.card Y).factorization 2 = k) :
    (Nat.card ↥(P₁ ⊓ P₂)).factorization 2 = k := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, hv⟩ := exists_vertexIso_of_isAmalgamOfGroup h
  rw [← (factorization_eq_of_vertexIso hpair hv).2, hk Y hY]

theorem isSolvable_of_vertexIso {P₁ P₂ : Subgroup G} {Y : Type} [Group Y] {M₁ M₂ : Subgroup Y}
    (hv : VertexIso P₁ P₂ M₁ M₂) (h : Group.IsSolvable ↥M₁ ∨ Group.IsSolvable ↥M₂) :
    Group.IsSolvable ↥P₁ ∨ Group.IsSolvable ↥P₂ := by
  obtain ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ := hv
  rcases h with h | h
  · exact Or.inl (Group.isSolvable_of_isSolvable_injective (f := e₁.toMonoidHom) e₁.injective)
  · exact Or.inr (Group.isSolvable_of_isSolvable_injective (f := e₂.toMonoidHom) e₂.injective)

theorem card_dvd_of_vertexIso {P₁ P₂ : Subgroup G} {Y : Type} [Group Y] {M₁ M₂ : Subgroup Y}
    (hv : VertexIso P₁ P₂ M₁ M₂) :
    Nat.card ↥P₁ ∣ Nat.card Y ∧ Nat.card ↥P₂ ∣ Nat.card Y := by
  obtain ⟨⟨e₁⟩, -, ⟨e₂⟩⟩ := hv
  rw [Nat.card_congr e₁.toEquiv, Nat.card_congr e₂.toEquiv]
  exact ⟨Subgroup.card_subgroup_dvd_card M₁, Subgroup.card_subgroup_dvd_card M₂⟩

theorem five_dvd_card_of_isLin2Type_two [Finite G] {L : Subgroup G} (h : IsLin2Type L 2) :
    5 ∣ Nat.card ↥L := by
  obtain ⟨F, _, _, hF, α, hα, -⟩ := h
  have h60 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) = 60 := by
    rw [Matrix.card_SL_field, hF]
    decide
  have := Subgroup.card_dvd_of_surjective hα
  rw [h60] at this
  exact (show 5 ∣ 60 by norm_num).trans this

theorem factorization_of_lieModel
    {Y : Type} [Group Y] {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (h : CFSG.Blueprint.LieModel Y t n 2 f) :
    Finite Y ∧ (Nat.card Y).factorization 2 = lieSylowExponent t n * f :=
  ⟨(CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput Y t n 2 f hadm h).1,
    (CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput Y t n 2 f hadm h).2.2⟩

theorem adm_psl3 {f : ℕ} (hf : 1 ≤ f) : StatedLieAdmissible .PSL 3 2 f :=
  ⟨Nat.prime_two, hf, by norm_num, by simp, by simp⟩

theorem adm_psp2 {f : ℕ} (hf : 2 ≤ f) : StatedLieAdmissible .PSp 2 2 f := by
  refine ⟨Nat.prime_two, by omega, le_rfl, fun h => ?_⟩
  have h2 : 2 ^ f = 2 ^ 1 := by simpa using congrArg Prod.snd h
  have := Nat.pow_right_injective le_rfl h2
  omega

theorem adm_g2 {f : ℕ} (hf : 2 ≤ f) : StatedLieAdmissible .G2 0 2 f :=
  CFSG.Open.StatedAPI.statedLieAdmissible_G2_two hf

theorem adm_d4 {f : ℕ} (hf : 1 ≤ f) : StatedLieAdmissible .trialityD4 0 2 f :=
  ⟨Nat.prime_two, hf, rfl⟩

theorem adm_f4 {a : ℕ} (ha : 1 ≤ a) : StatedLieAdmissible .twistedF4 0 2 (2 * a + 1) :=
  ⟨Nat.prime_two, by omega, rfl, rfl, ⟨a, rfl⟩, by omega⟩

theorem adm_psu {n f : ℕ} (hn : 4 ≤ n) (hf : 1 ≤ f) : StatedLieAdmissible .PSU n 2 f :=
  ⟨Nat.prime_two, hf, by omega, fun h => by
    have := congrArg Prod.fst h
    simp at this
    omega⟩

theorem factorization_of_u4ext
    [Finite G] {P₁ P₂ : Subgroup G} {f : ℕ} (hf : 1 ≤ f)
    (h : IsU4ExtTwo f (RankTwoAmalgam.ofSubgroups P₁ P₂)) :
    (Nat.card ↥(P₁ ⊓ P₂)).factorization 2 = 6 * f + 1 := by
  obtain ⟨Y, _, Ŷ, _, ι, hY, hι, hidx, T, M₁, M₂, hpair, ⟨e⟩⟩ := h
  obtain ⟨-, hfac⟩ := factorization_eq_of_vertexIso hpair ⟨⟨e.φ1⟩, ⟨e.φ12⟩, ⟨e.φ2⟩⟩
  obtain ⟨hYf, hY6⟩ := factorization_of_lieModel (adm_psu le_rfl hf) hY
  have hcard : Nat.card Ŷ = 2 * Nat.card Y := by
    rw [← ι.range.card_mul_index, hidx, ← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv]
    ring
  rw [← hfac, hcard, Nat.factorization_mul two_ne_zero Nat.card_pos.ne', Finsupp.add_apply, hY6,
    Nat.Prime.factorization_self Nat.prime_two]
  simp only [lieSylowExponent]
  omega

theorem entry_factorization
    [Finite G] {L1 L2 S : Subgroup G} (h : F112ListALegacyBare L1 L2 S) :
    F112E6Ext L1 L2 S ∨
      (∃ f, 2 ≤ f ∧ (Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))).factorization 2 =
        3 * f ∧ IsLin2Type L1 f ∧ IsLin2Type L2 f) ∨
      (∃ f, 2 ≤ f ∧ (Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))).factorization 2 =
        4 * f ∧ IsLin2Type L1 f ∧ IsLin2Type L2 f) ∨
      (∃ m, 2 ≤ m ∧ (Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))).factorization 2 =
        6 * m) ∨
      (Nat.card ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S))).factorization 2 = 20 := by
  simp only [F112ListALegacyBare] at h
  rcases h with ⟨f, hf, hA, -, hl1, -, hl2⟩ | ⟨f, hf, hA, -, hl1, -, hl2⟩ | ⟨f, hf, hA, -⟩ |
    ⟨f, hf, hA, -⟩ | ⟨a, ha, hA, -⟩ | ⟨f, hf, hA, h1, h2, h3, h4, h5⟩ | ⟨hA, -⟩
  · refine Or.inr (Or.inl ⟨f, hf, factorization_eq_of_isAmalgamOfGroup hA fun Y _ hY => ?_,
      hl1, hl2⟩)
    rw [(factorization_of_lieModel (adm_psl3 (by omega)) hY).2]
    rfl
  · refine Or.inr (Or.inr (Or.inl ⟨f, hf, factorization_eq_of_isAmalgamOfGroup hA
      fun Y _ hY => ?_, hl1, hl2⟩))
    rcases hY with ⟨h1, -⟩ | ⟨-, hY⟩
    · omega
    · rw [(factorization_of_lieModel (adm_psp2 hf) hY).2]
      rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, factorization_eq_of_isAmalgamOfGroup hA
      fun Y _ hY => ?_⟩)))
    rcases hY with ⟨h1, -⟩ | ⟨-, hY⟩
    · omega
    · rw [(factorization_of_lieModel (adm_g2 hf) hY).2]
      rfl
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨2 * f, by omega, factorization_eq_of_isAmalgamOfGroup
      hA fun Y _ hY => ?_⟩)))
    rw [(factorization_of_lieModel (adm_d4 (by omega)) hY).2]
    simp only [lieSylowExponent]
    ring
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨2 * (2 * a + 1), by omega,
      factorization_eq_of_isAmalgamOfGroup hA fun Y _ hY => ?_⟩)))
    rcases hY with ⟨h1, -⟩ | ⟨-, -, hY⟩
    · omega
    · rw [(factorization_of_lieModel (adm_f4 ha) hY).2]
      simp only [lieSylowExponent]
      ring
  · rcases hA with hA | hext
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨f, hf, factorization_eq_of_isAmalgamOfGroup hA
        fun Y _ hY => ?_⟩)))
      rw [(factorization_of_lieModel (adm_psu le_rfl (by omega)) hY).2]
      rfl
    · exact Or.inl ⟨f, hf, hext, h1, h2, h3, h4, h5⟩
  · refine Or.inr (Or.inr (Or.inr (Or.inr (factorization_eq_of_isAmalgamOfGroup hA
      fun Y _ hY => ?_))))
    rw [(factorization_of_lieModel (adm_psu (by norm_num) (by norm_num)) hY).2]
    rfl

end Sec526

end CFSG.Quasithin.H13
