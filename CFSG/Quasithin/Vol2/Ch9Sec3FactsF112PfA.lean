module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Residual
public import CFSG.LieType.BorelTits.Transfer
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.Quasithin.H13.Ch9.F112Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
  CFSG.QuasithinUnique.Setup.X6
open scoped commutatorElement

section Transport

variable {A : Type*} [Group A]

@[expose] def GenComm (D : Subgroup A) : Prop := pCoreOf 2 D ≤ ⁅pCoreOf 2 D, D⁆

@[expose] def VFact (P : Subgroup A) : Prop :=
  ¬ 2 ∣ (perfectCore P).relIndex P ∧ GenComm (perfectCore P)

theorem pCoreOf_map_injective {B : Type*} [Group B] {f : A →* B} (hf : Function.Injective f)
    (X : Subgroup A) : pCoreOf 2 (X.map f) = (pCoreOf 2 X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := map_pCore_mulEquiv 2 e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem genComm_map_iff {B : Type*} [Group B] {f : A →* B} (hf : Function.Injective f)
    (D : Subgroup A) : GenComm (D.map f) ↔ GenComm D := by
  unfold GenComm
  rw [pCoreOf_map_injective hf, ← Subgroup.map_commutator,
    Subgroup.map_le_map_iff_of_injective hf]

theorem vFact_map_iff [Finite A] {B : Type*} [Group B] [Finite B] {f : A →* B}
    (hf : Function.Injective f) (P : Subgroup A) : VFact (P.map f) ↔ VFact P := by
  unfold VFact
  rw [← map_perfectCore, Subgroup.relIndex_map_map_of_injective _ _ hf, genComm_map_iff hf]

theorem vFact_of_mulEquiv [Finite A] {B : Type*} [Group B] [Finite B] {P : Subgroup A}
    {M : Subgroup B} (e : ↥P ≃* ↥M) (h : VFact M) : VFact P := by
  have hψ : Function.Injective (M.subtype.comp e.toMonoidHom) :=
    M.subtype_injective.comp e.injective
  have hM : (⊤ : Subgroup ↥P).map (M.subtype.comp e.toMonoidHom) = M := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, Subgroup.mem_top _, by simp⟩
  have hP : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← hM, vFact_map_iff hψ] at h
  rw [← hP, vFact_map_iff P.subtype_injective]
  exact h

end Transport

section Vertex

variable {A : Type*} [Group A] [Finite A]

theorem le_of_isPGroup_of_odd {P D R : Subgroup A} (hD : (D.subgroupOf P).Normal)
    (hodd : ¬ 2 ∣ D.relIndex P) (hRP : R ≤ P) (hR : IsPGroup 2 R) : R ≤ D := by
  have hc : Nat.Coprime (D.subgroupOf P).index 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd).symm
  have hR' : IsPGroup 2 ↥(R.subgroupOf P) := hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRP).symm
  have hle := le_of_isPGroup_of_coprime_index hc hR'
  intro x hx
  exact Subgroup.mem_subgroupOf.1 (hle (show (⟨x, hRP hx⟩ : ↥P) ∈ R.subgroupOf P from hx))

theorem pCoreOf_eq_commutator {L H P : Subgroup A} (hLH : L ≤ H) (hHP : H ≤ P)
    (hDL : perfectCore P ≤ L) (hV : VFact P) : pCoreOf 2 H = ⁅pCoreOf 2 H, L⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hgen⟩ := hV
  have hDH : perfectCore P ≤ H := hDL.trans hLH
  have hPD : P ≤ Subgroup.normalizer (perfectCore P : Set A) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore P)
  have hQD : pCoreOf 2 H ≤ perfectCore P :=
    le_of_isPGroup_of_odd (perfectCore_normal P) hodd ((pCoreOf_le 2 H).trans hHP)
      (pCoreOf_isPGroup 2 H)
  have hNH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set A) := le_normalizer_pCoreOf 2 H
  have h1 : pCoreOf 2 H ≤ pCoreOf 2 (perfectCore P) :=
    le_pCoreOf_of_le_normalizer 2 hQD (hDH.trans hNH) (pCoreOf_isPGroup 2 H)
  have h2 : pCoreOf 2 (perfectCore P) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hDH)
      ((hHP.trans hPD).trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have heq : pCoreOf 2 (perfectCore P) = pCoreOf 2 H := le_antisymm h2 h1
  refine le_antisymm ?_ ?_
  · rw [← heq]
    exact hgen.trans (Subgroup.commutator_mono le_rfl hDL)
  · rw [Subgroup.commutator_le]
    intro q hq l hl
    have e : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hq ((Subgroup.mem_normalizer_iff.1 (hNH (hLH hl)) q⁻¹).1 (inv_mem hq))

theorem pCoreOf_sup_eq_commutator {L B S : Subgroup A} (hSB : S ≤ B)
    (hBL : B ≤ Subgroup.normalizer (L : Set A)) (hB : Group.IsSolvable ↥B) (hV : VFact (L ⊔ B)) :
    pCoreOf 2 (L ⊔ S) = ⁅pCoreOf 2 (L ⊔ S), L⁆ := by
  have hLP : L ≤ L ⊔ B := le_sup_left
  have hn : (L.subgroupOf (L ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLP).2 (sup_le Subgroup.le_normalizer hBL)
  exact pCoreOf_eq_commutator le_sup_left (sup_le_sup_left hSB L)
    (perfectCore_le_of_sup_solvable hLP hn rfl hB) hV

end Vertex

section YSide

variable {Y : Type*} [Group Y] [Finite Y]

theorem dInf_eq_perfectCore' (M : Subgroup Y) : dInf M = perfectCore M :=
  le_antisymm
    (le_perfectCore_of_perfect (dInf_le M) (Subgroup.isPerfect_iff.mp (dInf_isPerfect M)))
    (le_dInf_of_perfect (Subgroup.isPerfect_iff.mpr (perfectCore_perfect M)) (perfectCore_le M))

omit [Finite Y] in
theorem not_two_dvd_relIndex {T M : Subgroup Y} (hT : IsSylowTwoOf T ⊤)
    (hTM : T ≤ perfectCore M) : ¬ 2 ∣ (perfectCore M).relIndex M := by
  intro h
  apply hT.2.2
  have h1 : (perfectCore M).relIndex M ∣ T.relIndex M := Subgroup.relIndex_dvd_of_le_left M hTM
  have h2 : T.relIndex M ∣ T.index :=
    Subgroup.relIndex_dvd_index_of_le (hTM.trans (perfectCore_le M))
  show 2 ∣ T.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact h.trans (h1.trans h2)

theorem vFact_of_residual {T : Subgroup Y} {P : Fin 2 → Subgroup Y}
    (hR : ResidualOvergroupsAt Y T P) (ha : ∀ j, T ≤ perfectCore (P j))
    (hb : ∀ j, GenComm (perfectCore (P j))) {M₁ M₂ : Subgroup Y}
    (hY : IsYAmalgamPair T M₁ M₂) (h1 : ¬ Group.IsSolvable ↥M₁) (h2 : ¬ Group.IsSolvable ↥M₂) :
    Group.IsSolvable ↥(M₁ ⊓ M₂) ∧ VFact M₁ ∧ VFact M₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT, hne, hiff⟩ := hY
  obtain ⟨hM₁, hN₁⟩ := (hiff M₁).2 (Or.inl rfl)
  obtain ⟨hM₂, hN₂⟩ := (hiff M₂).2 (Or.inr rfl)
  have hT₁ : T ≤ M₁ := Subgroup.le_normalizer.trans hN₁
  have hT₂ : T ≤ M₂ := Subgroup.le_normalizer.trans hN₂
  have htop₁ : M₁ ≠ ⊤ := fun h => hne (hM₂.2 M₁ hM₁.1 (by rw [h]; exact le_top))
  have htop₂ : M₂ ≠ ⊤ := fun h => hne (hM₁.2 M₂ hM₂.1 (by rw [h]; exact le_top)).symm
  obtain ⟨j₁, hj₁, hd₁⟩ := hR.2.2.2.2.1 M₁ hT₁ htop₁ h1
  obtain ⟨j₂, hj₂, hd₂⟩ := hR.2.2.2.2.1 M₂ hT₂ htop₂ h2
  rw [dInf_eq_perfectCore', dInf_eq_perfectCore'] at hd₁ hd₂
  have hv : ∀ (M : Subgroup Y) (j : Fin 2), perfectCore M = perfectCore (P j) → VFact M := by
    intro M j h
    refine ⟨not_two_dvd_relIndex hT ?_, ?_⟩
    · rw [h]
      exact ha j
    · rw [h]
      exact hb j
  have hj : j₁ ≠ j₂ := by
    intro hjj
    subst hjj
    have hD : perfectCore M₂ = perfectCore M₁ := hd₂.trans hd₁.symm
    obtain ⟨R, hR1, hR2, hRN⟩ := hM₁.1
    have hRM : R ≤ M₁ := by
      rw [hRN]
      exact Subgroup.le_normalizer
    have hRO : R ≤ pCoreOf 2 M₁ := le_pCoreOf_of_le_normalizer 2 hRM hRN.le hR2
    have hOD : pCoreOf 2 M₁ ≤ perfectCore M₁ :=
      le_of_isPGroup_of_odd (perfectCore_normal M₁)
        (not_two_dvd_relIndex hT (by rw [hd₁]; exact ha j₁)) (pCoreOf_le 2 M₁)
        (pCoreOf_isPGroup 2 M₁)
    have hOO : pCoreOf 2 M₁ ≤ pCoreOf 2 (perfectCore M₁) :=
      le_pCoreOf_of_le_normalizer 2 hOD ((perfectCore_le M₁).trans (le_normalizer_pCoreOf 2 M₁))
        (pCoreOf_isPGroup 2 M₁)
    have hne' : pCoreOf 2 (perfectCore M₁) ≠ ⊥ := fun h =>
      hR1 (le_bot_iff.1 (h ▸ hRO.trans hOO))
    have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (perfectCore M₁) : Set Y)) :=
      ⟨_, hne', pCoreOf_isPGroup 2 _, rfl⟩
    have hle : ∀ M : Subgroup Y, perfectCore M = perfectCore M₁ →
        M ≤ Subgroup.normalizer (pCoreOf 2 (perfectCore M₁) : Set Y) := by
      intro M hM
      rw [← hM]
      exact (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore M)).trans
        (normalizer_le_normalizer_pCoreOf 2 _)
    have e1 := hM₁.2 _ hloc (hle M₁ rfl)
    have e2 := hM₂.2 _ hloc (hle M₂ hD)
    exact hne (e1.symm.trans e2)
  have hsolv : Group.IsSolvable ↥(P 0 ⊓ P 1) := hR.2.2.2.1
  have hM₁P : M₁ ≤ P j₁ := (hj₁ j₁).2 rfl
  have hM₂P : M₂ ≤ P j₂ := (hj₂ j₂).2 rfl
  have hinf : M₁ ⊓ M₂ ≤ P 0 ⊓ P 1 := by
    fin_cases j₁ <;> fin_cases j₂
    · exact absurd rfl hj
    · exact inf_le_inf hM₁P hM₂P
    · rw [inf_comm (P 0)]
      exact inf_le_inf hM₁P hM₂P
    · exact absurd rfl hj
  exact ⟨Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hinf),
    hv M₁ j₁ hd₁, hv M₂ j₂ hd₂⟩

end YSide

section Amalgam

@[expose] def HasModelFacts (Pr : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (Y : Type) [Group Y], Pr Y → Finite Y ∧ ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ →
    ∃ P : Fin 2 → Subgroup Y, ResidualOvergroupsAt Y T P ∧
      ∀ j, T ≤ perfectCore (P j) ∧ GenComm (perfectCore (P j))

variable {G : Type} [Group G]

theorem not_isSolvable_of_isL2Quot_two {L : Subgroup G} (h : IsL2Quot 2 (oTwoQuot ↥L)) :
    ¬ Group.IsSolvable ↥L := by
  intro hs
  obtain ⟨e⟩ := h
  have hL4 : ∃ s : Finset (GaloisField 2 2), s.card = 4 := by
    have : Fintype (GaloisField 2 2) := Fintype.ofFinite _
    refine ⟨Finset.univ, ?_⟩
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect hL4
  let e' : oTwoQuot ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) :=
    e.trans (pslTwoGf2EquivSl 2)
  have hX : Group.IsPerfect (oTwoQuot ↥L) :=
    Group.IsPerfect.ofSurjective (f := e'.symm.toMonoidHom) e'.symm.surjective
  have hc : Nat.card (oTwoQuot ↥L) = 60 := by
    rw [IsL2Quot.card (by norm_num) ⟨e⟩]
    norm_num
  have : Finite (oTwoQuot ↥L) := Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  have : Nontrivial (oTwoQuot ↥L) := Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
  have : Group.IsSolvable (oTwoQuot ↥L) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥L))
  exact Group.IsPerfect.not_isSolvable (oTwoQuot ↥L) this

theorem vertices_of_amalgam [Finite G] {L1 L2 S : Subgroup G} (hH : Hyp111 L1 L2 S)
    (h1 : IsL2Quot 2 (oTwoQuot ↥L1)) (h2 : IsL2Quot 2 (oTwoQuot ↥L2))
    {Pr : ∀ (Y : Type) [Group Y], Prop} (hPr : HasModelFacts Pr)
    (hα : IsAmalgamOfGroup
      (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S)) Pr) :
    pCoreOf 2 (L1 ⊔ S) = ⁅pCoreOf 2 (L1 ⊔ S), L1⁆ ∧
      pCoreOf 2 (L2 ⊔ S) = ⁅pCoreOf 2 (L2 ⊔ S), L2⁆ := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hpair, ⟨iso⟩⟩ := hα
  obtain ⟨hfin, hmod⟩ := hPr Y hY
  obtain ⟨P, hR, hP⟩ := hmod T hpair.1
  have hns : ∀ (L : Subgroup G) (M : Subgroup Y), (↥(L ⊔ bigB L1 L2 S) ≃* ↥M) →
      IsL2Quot 2 (oTwoQuot ↥L) → ¬ Group.IsSolvable ↥M := by
    intro L M e hq hs
    apply not_isSolvable_of_isL2Quot_two hq
    have : Group.IsSolvable ↥(L ⊔ bigB L1 L2 S) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_sup_left : L ≤ L ⊔ bigB L1 L2 S))
  obtain ⟨hsolv, hV₁, hV₂⟩ := vFact_of_residual hR (fun j => (hP j).1) (fun j => (hP j).2) hpair
    (hns L1 M₁ iso.φ1 h1) (hns L2 M₂ iso.φ2 h2)
  have hB : Group.IsSolvable ↥(bigB L1 L2 S) := by
    have : Group.IsSolvable (RankTwoAmalgam.ofSubgroups M₁ M₂).G12 := hsolv
    have : Group.IsSolvable ↥((L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)) :=
      Group.isSolvable_of_isSolvable_injective (f := iso.φ12.toMonoidHom) iso.φ12.injective
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective
      (le_inf le_sup_right le_sup_right : bigB L1 L2 S ≤ (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S)))
  have hSB : S ≤ bigB L1 L2 S := (le_sup_right : S ≤ borelOf L1 S ⊔ borelOf L2 S ⊔ S)
  have hB1 : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le (sup_le ((inf_le_left : borelOf L1 S ≤ L1).trans Subgroup.le_normalizer)
      hH.h1.borel_le) hH.h1.normalizes
  have hB2 : bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le (sup_le hH.h2.borel_le
      ((inf_le_left : borelOf L2 S ≤ L2).trans Subgroup.le_normalizer)) hH.h2.normalizes
  exact ⟨pCoreOf_sup_eq_commutator hSB hB1 hB (vFact_of_mulEquiv iso.φ1 hV₁),
    pCoreOf_sup_eq_commutator hSB hB2 hB (vFact_of_mulEquiv iso.φ2 hV₂)⟩

theorem eq_two_of_isL2Quot {X : Type*} [Group X] {f : ℕ} (hf : 1 ≤ f) (h : IsL2Quot f X)
    (h2 : IsL2Quot 2 X) : f = 2 := by
  have e := (h.card hf).symm.trans (h2.card (by norm_num))
  norm_num at e
  rcases Nat.lt_or_ge f 3 with hlt | hge
  · interval_cases f
    · norm_num at e
    · rfl
  · exfalso
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hge
    have h64 : 64 ≤ 4 ^ f := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) hge
    have : 8 * 63 ≤ 2 ^ f * (4 ^ f - 1) := Nat.mul_le_mul h8 (by omega)
    omega

end Amalgam

end CFSG.Quasithin.H13.Ch9.F112Pf
