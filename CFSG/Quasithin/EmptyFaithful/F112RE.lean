module

public import CFSG.Quasithin.EmptyFaithful.F112RD
public import CFSG.Quasithin.Recognition.F112TitsMain
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X
open CFSG.Quasithin.He9 (isQuasithinSub_of)

@[expose] def TitsRankLeFive : Prop :=
  ∀ E : Subgroup quasithinTits, IsElemAbelian 2 E → Nat.card E ≤ 32

@[expose] def TwistedF4RankLeFive : Prop :=
  ∀ E : Subgroup (MulAut quasithinTits), IsElemAbelian 2 E → Nat.card E ≤ 32

namespace F112RR

theorem isElemAbelian_map {G G' : Type*} [Group G] [Group G'] (f : G →* G') {A : Subgroup G}
    (h : IsElemAbelian 2 A) : IsElemAbelian 2 (A.map f) := CFSG.SectionRank.isElemAbelian_map h _

theorem isElemAbelian_subgroupOf {G : Type*} [Group G] {E H : Subgroup G}
    (hE : IsElemAbelian 2 E) : IsElemAbelian 2 (E.subgroupOf H) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE H

theorem exists_elemAbelian_of_isAmalgamOfGroup {G : Type} [Group G] {L₁ L₂ : Subgroup G}
    {P : ∀ (Y : Type) [Group Y], Prop}
    (h : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups L₁ L₂) P) {E : Subgroup G}
    (hE : E ≤ L₁ ⊓ L₂) (hEab : IsElemAbelian 2 E) :
    ∃ (Y : Type) (_ : Group Y), P Y ∧ ∃ E' : Subgroup Y, IsElemAbelian 2 E' ∧
      Nat.card E' = Nat.card E := by
  obtain ⟨Y, hY, hP, T', M₁, M₂, -, ⟨e⟩⟩ := h
  let f : ↥(L₁ ⊓ L₂) →* Y := (M₁ ⊓ M₂).subtype.comp e.φ12.toMonoidHom
  have hf : Function.Injective f := (M₁ ⊓ M₂).subtype_injective.comp e.φ12.injective
  refine ⟨Y, hY, hP, (E.subgroupOf (L₁ ⊓ L₂)).map f,
    isElemAbelian_map f (isElemAbelian_subgroupOf hEab), ?_⟩
  rw [Nat.card_congr ((E.subgroupOf (L₁ ⊓ L₂)).equivMapOfInjective f hf).toEquiv.symm]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv

theorem card_le_of_caseTits {G : Type} [Group G] (hT : TitsRankLeFive) {L₁ L₂ : Subgroup G}
    (h : CaseTits L₁ L₂) {E : Subgroup G} (hE : E ≤ L₁ ⊓ L₂) (hEab : IsElemAbelian 2 E) :
    Nat.card E ≤ 32 := by
  obtain ⟨Y, hY, ⟨e⟩, E', hE'ab, hE'card⟩ := exists_elemAbelian_of_isAmalgamOfGroup h.1 hE hEab
  have h1 := hT (E'.map e.toMonoidHom) (isElemAbelian_map e.toMonoidHom hE'ab)
  rw [Nat.card_congr (E'.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm] at h1
  omega

theorem card_le_of_case2F4 {G : Type} [Group G] (hT : TwistedF4RankLeFive) {L₁ L₂ : Subgroup G}
    (h : Case2F4 L₁ L₂) {E : Subgroup G} (hE : E ≤ L₁ ⊓ L₂) (hEab : IsElemAbelian 2 E) :
    Nat.card E ≤ 32 := by
  obtain ⟨Y, hY, hP, E', hE'ab, hE'card⟩ := exists_elemAbelian_of_isAmalgamOfGroup h.1 hE hEab
  rcases hP with ⟨-, ⟨e⟩⟩ | ⟨h3, -⟩
  · have h1 := hT (E'.map e.toMonoidHom) (isElemAbelian_map e.toMonoidHom hE'ab)
    rw [Nat.card_congr (E'.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm] at h1
    omega
  · omega

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T Mc M H Y₁ : Subgroup G} (c : Ctx T Mc M H Y₁)

section Five

variable (hqH : Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)))
  (hq₁ : Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* DihedralGroup 5) ∨
    Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* ↥(CFSG.Open.Sz 0)))

include c hq₁

theorem five_data :
    IsSylowTwoOf T (Y₁ ⊔ T) ∧ (Y₁ ⊔ T) ⊓ Subgroup.normalizer (T : Set G) = T ∧
      (Nonempty (OTwoQuot (Y₁ ⊔ T) ≃* DihedralGroup 5) ∨
        Nonempty (OTwoQuot (Y₁ ⊔ T) ≃* ↥(CFSG.Open.Sz 0))) := by
  obtain ⟨hs, hr, hnn, hX⟩ := oTwoQuot_sup_of_five c.T_pgroup c.T_le_normalizer_L₁ c.sylow_L₁ hq₁
  rw [c.L₁_sup_T] at hs hr hnn hX
  refine ⟨hs, ?_, hX⟩
  have hTle : T ≤ (Y₁ ⊔ T) ⊓ Subgroup.normalizer (T : Set G) :=
    le_inf le_sup_right Subgroup.le_normalizer
  refine le_antisymm ?_ hTle
  have hidx : (T.subgroupOf (Y₁ ⊔ T)).index = 5 := hr
  rcases eq_or_eq_of_le_of_index_prime hTle inf_le_left (by norm_num) hidx with h | h
  · exact h.le
  · exact absurd (h ▸ inf_le_right : Y₁ ⊔ T ≤ Subgroup.normalizer (T : Set G)) hnn

include hqH

theorem hyp111_five : Hyp111 (Y₁ ⊔ T) H T := by
  obtain ⟨hsX, hXN, hXq⟩ := c.five_data hq₁
  have hTX : T ≤ Y₁ ⊔ T := le_sup_right
  have hborelH : borelOf H T = T := by
    unfold borelOf
    rw [inf_of_le_left c.T_le_H]
    exact c.inf_normalizer_H hqH
  have hborelX : borelOf (Y₁ ⊔ T) T = T := by
    unfold borelOf
    rw [inf_of_le_left hTX]
    exact hXN
  refine ⟨⟨inferInstance, c.T_pgroup, hTX.trans Subgroup.le_normalizer, ?_, ?_, ?_, ?_⟩,
    ⟨inferInstance, c.T_pgroup, c.T_le_H.trans Subgroup.le_normalizer, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [inf_of_le_left hTX]
    exact hsX
  · rcases hXq with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e⟩)))
    · exact Or.inr (Or.inl ⟨0, ⟨e⟩⟩)
  · rw [hborelH]
    exact hTX.trans Subgroup.le_normalizer
  · rw [hborelH, sup_eq_left.2 hTX, sup_eq_left.2 hTX]
    exact c.charTwo_X
  · rw [inf_of_le_left c.T_le_H]
    exact c.hT
  · exact Or.inl ⟨1, le_rfl, isL2Quot_one_iff_perm3.mpr hqH⟩
  · rw [hborelX]
    exact c.T_le_H.trans Subgroup.le_normalizer
  · rw [hborelX, sup_eq_left.2 c.T_le_H, sup_eq_left.2 c.T_le_H]
    exact c.charTwo_H
  · rw [sup_assoc, sup_eq_left.2 c.T_le_H, sup_comm]
    exact c.o2_eq_bot_X

theorem case_five (hHay : HayashiFiveThree) : CaseTits (Y₁ ⊔ T) H ∨ Case2F4 (Y₁ ⊔ T) H := by
  obtain ⟨-, hXN, hXq⟩ := c.five_data hq₁
  exact hHay G (Y₁ ⊔ T) H T (c.hyp111_five hqH hq₁) (isQuasithinSub_of c.hs.qtfe.qtke _)
    le_sup_right c.T_le_H (by rw [inf_comm]; exact c.H_inf_X hqH) hXN (c.inf_normalizer_H hqH)
    hXq (isL2Quot_one_iff_perm3.mpr hqH)

end Five

end Ctx

end F112RR

theorem input15208F112At_S3_five_of_hay (hHay : HayashiFiveThree) (hTits : TitsRankLeFive)
    (hF4 : TwistedF4RankLeFive) (h1515 : StageLemma1515CE) (h1519 : StageLemma1519)
    (h15207 : StageLemma15207) (h15201 : StageLemma15201) (h15112 : StageLemma15112) :
    Input15208F112At (Equiv.Perm (Fin 3)) (DihedralGroup 5) ∧
      Input15208F112At (Equiv.Perm (Fin 3)) ↥(CFSG.Open.Sz 0) := by
  have key : ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
      ∀ H : Subgroup G, IsHStar T M H → ∀ Y₁ : Subgroup G, IsY1 T Mc M Y₁ →
      Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3)) →
      (Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* DihedralGroup 5) ∨
        Nonempty (OTwoQuot (Y₁ ⊔ rcOf Mc M) ≃* ↥(CFSG.Open.Sz 0))) → False := by
    intro G _ _ T Mc M hs H hH Y₁ hY₁ hqH hq₁
    have c : F112RR.Ctx T Mc M H Y₁ :=
      ⟨hs, hH, h1515 G T Mc M hs.qtfe hs.mf hs.ce, h1519 G T Mc M hs.qtfe hs.mf hs.ce, hY₁,
        h15207 G T Mc M hs Y₁ hY₁⟩
    obtain ⟨hUab, hUP, hPT, -, hU64⟩ := F112RR.exists_elemAbelian_card_ge hs hH c.c1519
      (h15201 G T Mc M hs) (h15112 G T Mc M hs.qtfe hs.mf hs.ce H hH).1
    have hUT : conjClosure (V154 T Mc M) H ≤ (Y₁ ⊔ T) ⊓ H := by
      rw [inf_comm, c.H_inf_X hqH]
      exact hUP.trans hPT
    rcases c.case_five hqH hq₁ hHay with h | h
    · have := F112RR.card_le_of_caseTits hTits h hUT hUab
      omega
    · have := F112RR.card_le_of_case2F4 hF4 h hUT hUab
      omega
  exact ⟨fun G _ _ T Mc M hs H hH Y₁ hY₁ hqH hq₁ =>
      key G T Mc M hs H hH Y₁ hY₁ hqH (Or.inl hq₁),
    fun G _ _ T Mc M hs H hH Y₁ hY₁ hqH hq₁ =>
      key G T Mc M hs H hH Y₁ hY₁ hqH (Or.inr hq₁)⟩

end CFSG.Quasithin
