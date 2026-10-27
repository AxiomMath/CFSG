module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Alpha
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Shape
import CFSG.LocalAnalysis.WeakClosure81.W183Br1ShapeAux1
import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 CoverOf)
open CFSG.Blueprint (LieModel)

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

structure Br1Alpha (Y T L₁ L₂ A : Subgroup (LGL 2 V)) (Γ : Set (Subgroup (LGL 2 V)))
    (VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V) (i : ℕ) : Prop where
  h : Assumption131 Y Γ VA i
  vfix : ∀ B ∈ Γ, VA B ≤ fixSub B
  two : Br2TwoComp Y T L₁ L₂
  mem : A ∈ Γ
  rank : mRank A ≤ i
  card : Nat.card ↥A = 4
  norm₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V))
  ker₁ : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥
  cent₂ : A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V))

variable {Y T L₁ L₂ A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

private theorem w183_alphaC_inf_eq_bot {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    (htwo : Br2TwoComp Y T L₁ L₂) :
    alphaC Y L₁ ⊓ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨hyY, hyC₁⟩ := Subgroup.mem_inf.mp hy1
  obtain ⟨-, hyC₂⟩ := Subgroup.mem_inf.mp hy2
  exact htwo.cent y hyY
    (fun l hl => ((Subgroup.mem_centralizer_iff.mp hyC₁) l hl).symm)
    (fun l hl => ((Subgroup.mem_centralizer_iff.mp hyC₂) l hl).symm)

private theorem w183_alphaMk_injective_on_G₂ {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    (htwo : Br2TwoComp Y T L₁ L₂) :
    Function.Injective ((alphaMk Y L₁).comp
      ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁)).subtype) := by
  intro a b hab
  have hab' : (alphaMk Y L₁) (a : ↥(alphaX Y L₁)) =
      (alphaMk Y L₁) (b : ↥(alphaX Y L₁)) := hab
  have hker : (a : ↥(alphaX Y L₁)) * (b : ↥(alphaX Y L₁))⁻¹ ∈ MonoidHom.ker (alphaMk Y L₁) := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hab', mul_inv_cancel]
  rw [show MonoidHom.ker (alphaMk Y L₁) =
      (alphaC Y L₁).subgroupOf (alphaX Y L₁) from
    QuotientGroup.ker_mk' ((alphaC Y L₁).subgroupOf (alphaX Y L₁))] at hker
  rw [Subgroup.mem_subgroupOf] at hker
  have hmem : ((a : ↥(alphaX Y L₁)) * (b : ↥(alphaX Y L₁))⁻¹ : LGL 2 V) ∈
      alphaC Y L₁ ⊓ (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))) := by
    rw [Subgroup.mem_inf]
    exact ⟨hker, Subgroup.mem_subgroupOf.mp (a * b⁻¹).2⟩
  rw [w183_alphaC_inf_eq_bot htwo, Subgroup.mem_bot] at hmem
  exact Subtype.ext (Subtype.ext (mul_inv_eq_one.mp hmem))

private theorem w183_isSylowIn_map_of_injective {Q Q' : Type} [Group Q] [Group Q']
    {p : ℕ} {f : Q →* Q'} (hf : Function.Injective f) {P H : Subgroup Q} :
    IsSylowIn p (P.map f) (H.map f) ↔ IsSylowIn p P H := by
  unfold IsSylowIn
  rw [Subgroup.map_le_map_iff_of_injective hf, Subgroup.relIndex_map_map_of_injective _ _ hf]
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  exact ⟨fun h => h.of_equiv (Subgroup.equivMapOfInjective P f hf).symm, fun h => h.map _⟩

private theorem w183_le_centralizer_of_comm {Y T L₁ L₂ : Subgroup (LGL 2 V)}
    (htwo : Br2TwoComp Y T L₁ L₂) :
    L₁ ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
  intro l hl
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (htwo.comm l hl b hb).symm

private theorem w183_le_alphaX {Y T L₁ L₂ : Subgroup (LGL 2 V)} (htwo : Br2TwoComp Y T L₁ L₂) :
    L₁ ≤ alphaX Y L₁ := le_inf htwo.le₁ Subgroup.le_normalizer

private theorem w183_le_alphaX_of_mem {Y T L₁ L₂ A : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}
    (c : Br1Alpha Y T L₁ L₂ A Γ VA i) : A ≤ alphaX Y L₁ :=
  le_inf (c.h.le_G A c.mem) c.norm₁

private theorem w183_isSylowIn_of_alpha {Y T L₁ L₂ A : Subgroup (LGL 2 V)}
    {Γ : Set (Subgroup (LGL 2 V))} {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}
    (c : Br1Alpha Y T L₁ L₂ A Γ VA i) (hSyl : IsSylowIn 2 (alphaA Y L₁ A) (alphaL Y L₁)) :
    IsSylowIn 2 A L₁ := by
  have hπG := w183_alphaMk_injective_on_G₂ c.two
  have hA'G : A.subgroupOf (alphaX Y L₁) ≤
      (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨c.h.le_G A c.mem hx, c.cent₂ hx⟩
  have hL'G : L₁.subgroupOf (alphaX Y L₁) ≤
      (Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact ⟨c.two.le₁ hx, w183_le_centralizer_of_comm c.two hx⟩
  have hinj : Function.Injective ((alphaX Y L₁).subtype.comp
      ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁)).subtype) := fun a b h => Subtype.ext (Subtype.ext h)
  have hmapA : ((A.subgroupOf (alphaX Y L₁)).subgroupOf
        ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁))).map
        ((alphaMk Y L₁).comp
          ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
            (alphaX Y L₁)).subtype) = alphaA Y L₁ A := by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hA'G]
  have hmapL : ((L₁.subgroupOf (alphaX Y L₁)).subgroupOf
        ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁))).map
        ((alphaMk Y L₁).comp
          ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
            (alphaX Y L₁)).subtype) = alphaL Y L₁ := by
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hL'G]
  have hSylG : IsSylowIn 2
      ((A.subgroupOf (alphaX Y L₁)).subgroupOf
        ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁)))
      ((L₁.subgroupOf (alphaX Y L₁)).subgroupOf
        ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁))) :=
    (w183_isSylowIn_map_of_injective hπG).mp (by rw [hmapA, hmapL]; exact hSyl)
  have hmapAG : ((A.subgroupOf (alphaX Y L₁)).subgroupOf
      ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁))).map ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁)).subtype = A.subgroupOf (alphaX Y L₁) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hA'G]
  have hmapLG : ((L₁.subgroupOf (alphaX Y L₁)).subgroupOf
      ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁))).map ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁)).subtype = L₁.subgroupOf (alphaX Y L₁) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hL'G]
  have hSyl' : IsSylowIn 2 (A.subgroupOf (alphaX Y L₁)) (L₁.subgroupOf (alphaX Y L₁)) := by
    rw [← hmapAG, ← hmapLG]
    exact (w183_isSylowIn_map_of_injective
      (p := 2)
      (f := ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf
        (alphaX Y L₁)).subtype)
      (P := (A.subgroupOf (alphaX Y L₁)).subgroupOf
        ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁)))
      (H := (L₁.subgroupOf (alphaX Y L₁)).subgroupOf
        ((Y ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁)))
      Subtype.val_injective).mpr hSylG
  exact w183_isSylowIn_of_subgroupOf (w183_le_alphaX_of_mem c) (w183_le_alphaX c.two) hSyl'

theorem br1_alpha_false_L32 (hfin : FinL32) (c : Br1Alpha Y T L₁ L₂ A Γ VA i)
    (hshape : IsL3 ↥L₁ 1) (hτ : ∃ τ ∈ Y, ActsOnDynkinMod ⊥ L₁ τ) : False := by
  classical
  haveI : Finite (alphaQuot Y L₁) := w183_alpha_finite Y L₁
  obtain ⟨hN, hC⟩ := w183_alpha_normal_cent c.two
  obtain ⟨e⟩ := w183_alpha_shape c.two
  have hshape' : IsL3 ↥(alphaL Y L₁) 1 := LieModel.of_mulEquiv e hshape
  have hAY : A ≤ Y := c.h.le_G A c.mem
  obtain ⟨hcard', hel'⟩ := w183_alpha_card_elem hAY c.norm₁ c.ker₁ c.card (c.h.isElemAb A c.mem)
  have hTI' : IsTISub (alphaQuot Y L₁) (alphaA Y L₁ A) :=
    w183_alpha_ti c.two hAY c.norm₁ c.cent₂ (c.h.isTISub_member c.mem c.rank)
  obtain ⟨τ, hτY, hτd⟩ := hτ
  obtain ⟨τ', hτ''⟩ := w183_alpha_dynkin c.two hτY hτd
  exact hfin (alphaQuot Y L₁) (alphaL Y L₁) hN hshape' hC ⟨τ', hτ''⟩ (alphaA Y L₁ A)
    hcard' hel' hTI'

theorem br1_alpha_false_A6 (hfin : FinA6) (c : Br1Alpha Y T L₁ L₂ A Γ VA i)
    (hshape : IsAlt ↥L₁ 6) (hτ : ∃ τ ∈ Y, ActsOnDynkinMod ⊥ L₁ τ) : False := by
  classical
  haveI : Finite (alphaQuot Y L₁) := w183_alpha_finite Y L₁
  obtain ⟨hN, hC⟩ := w183_alpha_normal_cent c.two
  obtain ⟨e⟩ := w183_alpha_shape c.two
  obtain ⟨e'⟩ := hshape
  have hshape' : IsAlt ↥(alphaL Y L₁) 6 := ⟨e.symm.trans e'⟩
  have hAY : A ≤ Y := c.h.le_G A c.mem
  obtain ⟨hcard', hel'⟩ := w183_alpha_card_elem hAY c.norm₁ c.ker₁ c.card (c.h.isElemAb A c.mem)
  have hTI' : IsTISub (alphaQuot Y L₁) (alphaA Y L₁ A) :=
    w183_alpha_ti c.two hAY c.norm₁ c.cent₂ (c.h.isTISub_member c.mem c.rank)
  obtain ⟨τ, hτY, hτd⟩ := hτ
  obtain ⟨τ', hτ''⟩ := w183_alpha_dynkin c.two hτY hτd
  exact hfin (alphaQuot Y L₁) (alphaL Y L₁) hN hshape' hC ⟨τ', hτ''⟩ (alphaA Y L₁ A)
    hcard' hel' hTI'

theorem br1_alpha_false_Sp44 (hfin : FinG2Y) (c : Br1Alpha Y T L₁ L₂ A Γ VA i)
    (hshape : IsSp4 ↥L₁ 2) (hτ : ∃ τ ∈ Y, ActsOnDynkinMod ⊥ L₁ τ) : False := by
  classical
  haveI : Finite (alphaQuot Y L₁) := w183_alpha_finite Y L₁
  obtain ⟨hN, hC⟩ := w183_alpha_normal_cent c.two
  obtain ⟨e⟩ := w183_alpha_shape c.two
  have hshape' : IsSp4 ↥(alphaL Y L₁) 2 := LieModel.of_mulEquiv e hshape
  have hAY : A ≤ Y := c.h.le_G A c.mem
  obtain ⟨hcard', hel'⟩ := w183_alpha_card_elem hAY c.norm₁ c.ker₁ c.card (c.h.isElemAb A c.mem)
  have hTI' : IsTISub (alphaQuot Y L₁) (alphaA Y L₁ A) :=
    w183_alpha_ti c.two hAY c.norm₁ c.cent₂ (c.h.isTISub_member c.mem c.rank)
  obtain ⟨τ, hτY, hτd⟩ := hτ
  obtain ⟨τ', hτ''⟩ := w183_alpha_dynkin c.two hτY hτd
  have hconf : CorConfig (alphaQuot Y L₁) (alphaA Y L₁ A) :=
    hfin (alphaQuot Y L₁) (alphaL Y L₁) hN hshape' hC ⟨τ', hτ''⟩ (alphaA Y L₁ A)
      hcard' hel' hTI'
  have hconf' : CorConfig ↥(alphaX Y L₁) (A.subgroupOf (alphaX Y L₁)) :=
    w183_alpha_lift c.two hAY c.norm₁ c.cent₂ hconf
  have hAX : A ≤ alphaX Y L₁ := w183_le_alphaX_of_mem c
  have hA' : (A.subgroupOf (alphaX Y L₁)).map (alphaX Y L₁).subtype ∈ Γ := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAX]; exact c.mem
  have hr' : mRank ((A.subgroupOf (alphaX Y L₁)).map (alphaX Y L₁).subtype) ≤ i := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAX]; exact c.rank
  exact c.h.false_of_corConfig c.vfix (alphaX Y L₁).subtype Subtype.val_injective
    (fun g => g.2.1) hA' hr' hconf'

theorem br1_alpha_false_L34 (h65f : Asch6_5Four) (hfin : FinG1)
    (c : Br1Alpha Y T L₁ L₂ A Γ VA i) (hshape : IsL3 ↥L₁ 2) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  have hAY : A ≤ Y := c.h.le_G A c.mem
  let Y' : Subgroup (LGL 2 V) := A ⊔ L₁
  have hY'Y : Y' ≤ Y := sup_le hAY c.two.le₁
  have hLY' : L₁ ≤ Y' := le_sup_right
  have hAY' : A ≤ Y' := le_sup_left
  have hY'N : Y' ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
    sup_le c.norm₁ Subgroup.le_normalizer
  have hLn' : ∀ y ∈ Y', ∀ l ∈ L₁, y * l * y⁻¹ ∈ L₁ := by
    intro y hy l hl
    have h := hY'N hy
    rw [Subgroup.mem_normalizer_iff] at h
    exact (h l).mp hl
  have hY'C₂ : Y' ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    sup_le c.cent₂ (w183_le_centralizer_of_comm c.two)
  have hcent' : ∀ y ∈ Y', (∀ l ∈ L₁, y * l = l * y) → y = 1 := by
    intro y hy hc1
    have hc2 : ∀ l ∈ L₂, y * l = l * y :=
      fun l hl => ((Subgroup.mem_centralizer_iff.mp (hY'C₂ hy)) l hl).symm
    exact c.two.cent y (hY'Y hy) hc1 hc2
  haveI : Finite ↥Y' := Subtype.finite
  obtain ⟨hN, hC⟩ := w183_restrict_normal_cent hLY' hLn' hcent'
  have hshape' : IsL3 ↥(L₁.subgroupOf Y') 2 :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY').symm hshape
  have hcomp := w183_coverOf_and_component_of_isL3 hLY' hN hshape
  have hcard' : Nat.card ↥(A.subgroupOf Y') = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY').toEquiv, c.card]
  have hel' : IsElemAbelian 2 (A.subgroupOf Y') := (c.h.isElemAb A c.mem).subgroupOf Y'
  have hquad : IsQuadraticOn (repOf Y') (A.subgroupOf Y') :=
    isQuadraticOn_lglRep (Y := Y') (c.h.quadratic A c.mem)
  have hALc : A.subgroupOf Y' ⊓
      Subgroup.centralizer ((L₁.subgroupOf Y' : Subgroup ↥Y') : Set ↥Y') = ⊥ := by
    rw [hC]; exact inf_bot_eq _
  have hLsimple' : IsSimpleGroup ↥(L₁.subgroupOf Y') :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hshape'
  have hLnab' : ∃ a b : ↥(L₁.subgroupOf Y'), a * b ≠ b * a :=
    w183_exists_mul_ne_of_isL3_two hshape'
  have hAnorm : A.subgroupOf Y' ≤ Subgroup.normalizer (L₁.subgroupOf Y' : Set ↥Y') := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
    exact le_top
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥(L₁.subgroupOf Y'))) := by
    have hcenter : Subgroup.center ↥(L₁.subgroupOf Y') = ⊥ :=
      w183_center_eq_bot_of_simple hLsimple' hLnab'
    rw [hcenter, Subgroup.card_bot]
    norm_num
  have hinner := h65f ↥Y' (Multiplicative V) (multiplicative_sq_eq_one (W := V)) (repOf Y')
    (repOf_injective Y') (L₁.subgroupOf Y') (A.subgroupOf Y') hcomp.1 hodd hAnorm hcard'
    hel' hquad hALc (↥L₁) (inferInstance : Group ↥L₁) (Or.inl hshape) hcomp.2
  have hAL : A ≤ L₁ := by
    intro a ha
    let aY : ↥Y' := ⟨a, hAY' ha⟩
    have haY : aY ∈ A.subgroupOf Y' := Subgroup.mem_subgroupOf.mpr ha
    obtain ⟨l, hl, hdl⟩ := hinner aY haY
    have hcomm : ∀ l' ∈ L₁, ((aY * l⁻¹ : ↥Y') : LGL 2 V) * l' =
        l' * ((aY * l⁻¹ : ↥Y') : LGL 2 V) := by
      intro l' hl'
      have hl'' : (⟨l', hLY' hl'⟩ : ↥Y') ∈ L₁.subgroupOf Y' :=
        Subgroup.mem_subgroupOf.mpr hl'
      have h := (Subgroup.mem_centralizer_iff.mp hdl) _ hl''
      exact (congrArg (fun z : ↥Y' => (z : LGL 2 V)) h).symm
    have hone : ((aY * l⁻¹ : ↥Y') : LGL 2 V) = 1 :=
      hcent' _ (Y'.mul_mem aY.2 (Y'.inv_mem (hLY' (Subgroup.mem_subgroupOf.mp hl)))) hcomm
    have haeq : a = (l : LGL 2 V) := by
      refine mul_inv_eq_one.mp ?_
      simpa using hone
    exact haeq ▸ Subgroup.mem_subgroupOf.mp hl
  have hA' : (A.subgroupOf L₁).map L₁.subtype ∈ Γ := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAL]; exact c.mem
  have hr' : mRank ((A.subgroupOf L₁).map L₁.subtype) ≤ i := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAL]; exact c.rank
  have hcardL : Nat.card ↥(A.subgroupOf L₁) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, c.card]
  have helL : IsElemAbelian 2 (A.subgroupOf L₁) := (c.h.isElemAb A c.mem).subgroupOf L₁
  exact c.h.false_of_ticorConfigHolds c.vfix (hfin ↥L₁ hshape) L₁.subtype
    Subtype.val_injective (fun g => c.two.le₁ g.2) hA' hr' hcardL helL

theorem br1_alpha_sylow_L24 (hfin : FinA5) (c : Br1Alpha Y T L₁ L₂ A Γ VA i)
    (hshape : IsL2 ↥L₁ 2) : IsSylowIn 2 A L₁ := by
  classical
  haveI : Finite (alphaQuot Y L₁) := w183_alpha_finite Y L₁
  obtain ⟨hN, hC⟩ := w183_alpha_normal_cent c.two
  obtain ⟨e⟩ := w183_alpha_shape c.two
  have hshape' : IsL2 ↥(alphaL Y L₁) 2 := LieModel.of_mulEquiv e hshape
  have hAY : A ≤ Y := c.h.le_G A c.mem
  obtain ⟨hcard', hel'⟩ := w183_alpha_card_elem hAY c.norm₁ c.ker₁ c.card (c.h.isElemAb A c.mem)
  have hTI' : IsTISub (alphaQuot Y L₁) (alphaA Y L₁ A) :=
    w183_alpha_ti c.two hAY c.norm₁ c.cent₂ (c.h.isTISub_member c.mem c.rank)
  have hSyl : IsSylowIn 2 (alphaA Y L₁ A) (alphaL Y L₁) :=
    hfin (alphaQuot Y L₁) (alphaL Y L₁) hN hshape' hC (alphaA Y L₁ A) hcard' hel' hTI'
  exact w183_isSylowIn_of_alpha c hSyl

end CFSG.LocalAnalysis.WeakClosure81

end
