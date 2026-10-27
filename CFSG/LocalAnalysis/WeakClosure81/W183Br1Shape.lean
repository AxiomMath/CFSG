module

public import CFSG.LocalAnalysis.WeakClosure81.W183Fin1
public import CFSG.LocalAnalysis.WeakClosure81.W183Fin2
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6Props
import CFSG.LocalAnalysis.WeakClosure81.W18T189FourBridge
import CFSG.LocalAnalysis.WeakClosure81.W183Br1ShapeAux1
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt Bar2 CoverOf)
open CFSG.Blueprint (LieModel)

@[expose] def FinG2Y : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (L : Subgroup Y), L.Normal → IsSp4 ↥L 2 →
    Subgroup.centralizer (L : Set Y) = ⊥ → (∃ τ : Y, ActsOnDynkinMod ⊥ L τ) → TICorConfigHolds Y

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183_restrict_normal_cent {W : Type} [Group W] {Y L : Subgroup W} (hLY : L ≤ Y)
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) :
    (L.subgroupOf Y).Normal ∧
      Subgroup.centralizer ((L.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊥ := by
  constructor
  · refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hLn g.1 g.2 n.1 hn
  · rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    apply hcent y.1 y.2
    intro l hl
    have hy' := (Subgroup.mem_centralizer_iff.mp hy) (⟨l, hLY hl⟩ : ↥Y)
      (Subgroup.mem_subgroupOf.mpr hl)
    exact (congrArg Subtype.val hy').symm

theorem w183_actsOnDynkinMod_subgroupOf {W : Type} [Group W] {Y L : Subgroup W} (hLY : L ≤ Y)
    {τ : W} (hτ : τ ∈ Y) (h : ActsOnDynkinMod ⊥ L τ) :
    ActsOnDynkinMod ⊥ (L.subgroupOf Y) (⟨τ, hτ⟩ : ↥Y) := by
  obtain ⟨hτnorm, P, hP, hconj⟩ := h
  obtain ⟨-, hPLt, hPmax, S, -, hSL, hSpow, hSidx, hSnorm⟩ := hP
  have hPL : P ≤ L := le_of_lt hPLt
  have hPY : P ≤ Y := hPL.trans hLY
  have hSY : S ≤ Y := hSL.trans hLY
  refine ⟨?_, P.subgroupOf Y, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hτnorm ⊢
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using hτnorm (x : W)
  · refine ⟨bot_le, ?_, ?_, S.subgroupOf Y, bot_le, Subgroup.subgroupOf_mono Y hSL,
      ?_, ?_, ?_⟩
    · have hle : P.subgroupOf Y ≤ L.subgroupOf Y := Subgroup.subgroupOf_mono Y hPL
      refine lt_of_le_of_ne hle ?_
      intro heq
      have hm := congrArg (Subgroup.map Y.subtype) heq
      rw [Subgroup.map_subgroupOf_eq_of_le hPY,
        Subgroup.map_subgroupOf_eq_of_le hLY] at hm
      exact hPLt.ne hm
    · intro X' hPX' hX'L'
      let XX : Subgroup W := X'.map Y.subtype
      have hP_lt_XX : P < XX := by
        refine lt_of_le_of_ne ?_ ?_
        · have hPmap : P = (P.subgroupOf Y).map Y.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hPY).symm
          rw [hPmap]
          exact Subgroup.map_mono hPX'.le
        · intro heq
          have hmap_inj := Subgroup.map_injective (f := Y.subtype) Subtype.val_injective
          have hEq' : P.subgroupOf Y = X' := by
            apply hmap_inj
            rw [Subgroup.map_subgroupOf_eq_of_le hPY, heq]
          exact hPX'.ne hEq'
      have hXX_L : XX ≤ L := by
        have hle : XX ≤ (L.subgroupOf Y).map Y.subtype := Subgroup.map_mono hX'L'
        rwa [Subgroup.map_subgroupOf_eq_of_le hLY] at hle
      have hXXeq : XX = L := hPmax XX hP_lt_XX hXX_L
      have hX'eq : X' = L.subgroupOf Y := by
        apply Subgroup.map_injective (f := Y.subtype) Subtype.val_injective
        rw [Subgroup.map_subgroupOf_eq_of_le hLY]
        exact hXXeq
      exact hX'eq
    · intro s hs
      obtain ⟨k, hk⟩ := hSpow s.1 (Subgroup.mem_subgroupOf.mp hs)
      refine ⟨k, ?_⟩
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      simpa using hk
    · have hrel := Subgroup.relIndex_comap (H := S) (f := Y.subtype) (K := L.subgroupOf Y)
      rw [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype,
        inf_of_le_left hLY] at hrel
      rwa [hrel]
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxL', hxnorm⟩ := hx
      rw [Subgroup.mem_subgroupOf]
      refine hSnorm ⟨Subgroup.mem_subgroupOf.mp hxL', ?_⟩
      change (x : W) ∈ Subgroup.normalizer (S : Set W)
      rw [Subgroup.mem_normalizer_iff] at hxnorm ⊢
      intro s
      constructor
      · intro hs
        have hsY : s ∈ Y := hSY hs
        have hs' : (⟨s, hsY⟩ : ↥Y) ∈ S.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hs
        exact Subgroup.mem_subgroupOf.mp ((hxnorm ⟨s, hsY⟩).mp hs')
      · intro hs
        have hsY : s ∈ Y := by
          have h : (x : W)⁻¹ * ((x : W) * s * (x : W)⁻¹) * (x : W) = s := by
            group
          rw [← h]
          exact Y.mul_mem (Y.mul_mem (Y.inv_mem x.2) (hSY hs)) x.2
        have hs' : (⟨s, hsY⟩ : ↥Y) ∈ S.subgroupOf Y := by
          rw [Subgroup.mem_subgroupOf]
          exact (hxnorm ⟨s, hsY⟩).mpr (Subgroup.mem_subgroupOf.mpr hs)
        exact Subgroup.mem_subgroupOf.mp hs'

  · intro l' hl'
    intro hEq
    let u : ↥Y := (⟨τ, hτ⟩ : ↥Y)⁻¹ * l'
    have hmap := congrArg (Subgroup.map Y.subtype) hEq
    rw [w183_map_conjSubgroup_subgroupOf hPY u.2,
      Subgroup.map_subgroupOf_eq_of_le hPY] at hmap
    exact hconj l'.1 hl' hmap

namespace Assumption131

variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ} {A : Subgroup (LGL 2 V)}

theorem isTISub_member (h : Assumption131 G Γ VA i) (hA : A ∈ Γ) (hr : mRank A ≤ i) :
    IsTISub ↥G (A.subgroupOf G) := by
  have hAG : A ≤ G := h.le_G A hA
  have hmap : (A.subgroupOf G).map G.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAG
  refine h.isTISub_of_member G.subtype Subtype.val_injective (fun g => g.2) ?_ ?_
  · rw [hmap]; exact hA
  · rw [hmap]; exact hr

end Assumption131

variable {Y L A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem br1_false_of_L32 (hfin : FinL32) (h : Assumption131 Y Γ VA i)
    (hLY : L ≤ Y) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hshape : IsL3 ↥L 1)
    (hτ : ∃ τ ∈ Y, ActsOnDynkinMod ⊥ L τ) (hA : A ∈ Γ) (hr : mRank A ≤ i)
    (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  haveI : Finite ↥Y := Subtype.finite
  obtain ⟨hN, hC⟩ := w183_restrict_normal_cent hLY hLn hcent
  have hshape' : IsL3 ↥(L.subgroupOf Y) 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hshape
  have hτ' : ∃ τ : ↥Y, ActsOnDynkinMod ⊥ (L.subgroupOf Y) τ := by
    obtain ⟨τ, hτY, hτd⟩ := hτ
    exact ⟨⟨τ, hτY⟩, w183_actsOnDynkinMod_subgroupOf hLY hτY hτd⟩
  have hcard' : Nat.card ↥(A.subgroupOf Y) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le_G A hA)).toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf Y) := hel.subgroupOf Y
  exact hfin ↥Y (L.subgroupOf Y) hN hshape' hC hτ' (A.subgroupOf Y) hcard' hel'
    (h.isTISub_member hA hr)

theorem br1_false_of_A6 (hfin : FinA6) (h : Assumption131 Y Γ VA i)
    (hLY : L ≤ Y) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hshape : IsAlt ↥L 6)
    (hτ : ∃ τ ∈ Y, ActsOnDynkinMod ⊥ L τ) (hA : A ∈ Γ) (hr : mRank A ≤ i)
    (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  haveI : Finite ↥Y := Subtype.finite
  obtain ⟨hN, hC⟩ := w183_restrict_normal_cent hLY hLn hcent
  have hshape' : IsAlt ↥(L.subgroupOf Y) 6 := by
    obtain ⟨e⟩ := hshape
    exact ⟨(Subgroup.subgroupOfEquivOfLe hLY).trans e⟩
  have hτ' : ∃ τ : ↥Y, ActsOnDynkinMod ⊥ (L.subgroupOf Y) τ := by
    obtain ⟨τ, hτY, hτd⟩ := hτ
    exact ⟨⟨τ, hτY⟩, w183_actsOnDynkinMod_subgroupOf hLY hτY hτd⟩
  have hcard' : Nat.card ↥(A.subgroupOf Y) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le_G A hA)).toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf Y) := hel.subgroupOf Y
  exact hfin ↥Y (L.subgroupOf Y) hN hshape' hC hτ' (A.subgroupOf Y) hcard' hel'
    (h.isTISub_member hA hr)

theorem br1_false_of_Sp44 (hfin : FinG2Y) (h : Assumption131 Y Γ VA i)
    (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) (hLY : L ≤ Y)
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hshape : IsSp4 ↥L 2)
    (hτ : ∃ τ ∈ Y, ActsOnDynkinMod ⊥ L τ) (hA : A ∈ Γ) (hr : mRank A ≤ i)
    (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A) : False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  haveI : Finite ↥Y := Subtype.finite
  obtain ⟨hN, hC⟩ := w183_restrict_normal_cent hLY hLn hcent
  have hshape' : IsSp4 ↥(L.subgroupOf Y) 2 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hshape
  have hτ' : ∃ τ : ↥Y, ActsOnDynkinMod ⊥ (L.subgroupOf Y) τ := by
    obtain ⟨τ, hτY, hτd⟩ := hτ
    exact ⟨⟨τ, hτY⟩, w183_actsOnDynkinMod_subgroupOf hLY hτY hτd⟩
  have hG₀ : TICorConfigHolds ↥Y :=
    hfin ↥Y (L.subgroupOf Y) hN hshape' hC hτ'
  have hcard' : Nat.card ↥(A.subgroupOf Y) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le_G A hA)).toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf Y) := hel.subgroupOf Y
  have hA' : (A.subgroupOf Y).map Y.subtype ∈ Γ := by
    rw [Subgroup.map_subgroupOf_eq_of_le (h.le_G A hA)]; exact hA
  have hr' : mRank ((A.subgroupOf Y).map Y.subtype) ≤ i := by
    rw [Subgroup.map_subgroupOf_eq_of_le (h.le_G A hA)]; exact hr
  exact h.false_of_ticorConfigHolds hVfix hG₀ Y.subtype Subtype.val_injective
    (fun g => g.2) hA' hr' hcard' hel'

theorem br1_false_of_L34 (h65f : Asch6_5Four) (hfin : FinG1) (h : Assumption131 Y Γ VA i)
    (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) (hLY : L ≤ Y)
    (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hshape : IsL3 ↥L 2)
    (hA : A ∈ Γ) (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A) :
    False := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  haveI : Finite ↥Y := Subtype.finite
  obtain ⟨hN, hC⟩ := w183_restrict_normal_cent hLY hLn hcent
  have hshape' : IsL3 ↥(L.subgroupOf Y) 2 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hshape
  have hcomp := w183_coverOf_and_component_of_isL3 hLY hN hshape
  have hcard' : Nat.card ↥(A.subgroupOf Y) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le_G A hA)).toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf Y) := hel.subgroupOf Y
  have hquad : IsQuadraticOn (repOf Y) (A.subgroupOf Y) :=
    isQuadraticOn_lglRep (Y := Y) (h.quadratic A hA)
  have hAL : A.subgroupOf Y ⊓
      Subgroup.centralizer ((L.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) = ⊥ := by
    rw [hC]
    exact inf_bot_eq _
  have hLsimple' : IsSimpleGroup ↥(L.subgroupOf Y) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hshape'
  have hLnab' : ∃ a b : ↥(L.subgroupOf Y), a * b ≠ b * a :=
    w183_exists_mul_ne_of_isL3_two hshape'
  have hAnorm : A.subgroupOf Y ≤ Subgroup.normalizer (L.subgroupOf Y : Set ↥Y) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
    exact le_top
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥(L.subgroupOf Y))) := by
    have hcenter : Subgroup.center ↥(L.subgroupOf Y) = ⊥ :=
      w183_center_eq_bot_of_simple hLsimple' hLnab'
    rw [hcenter, Subgroup.card_bot]
    norm_num
  have hinner := h65f ↥Y (Multiplicative V) (multiplicative_sq_eq_one (W := V)) (repOf Y)
    (repOf_injective Y) (L.subgroupOf Y) (A.subgroupOf Y) hcomp.1 hodd hAnorm hcard' hel'
    hquad hAL (↥L) (inferInstance : Group ↥L) (Or.inl hshape) hcomp.2
  have hAL : A ≤ L := by
    intro a ha
    let aY : ↥Y := ⟨a, h.le_G A hA ha⟩
    have haY : aY ∈ A.subgroupOf Y := Subgroup.mem_subgroupOf.mpr ha
    obtain ⟨l, hl, hdl⟩ := hinner aY haY
    have hcomm : ∀ l' ∈ L, ((aY * l⁻¹ : ↥Y) : LGL 2 V) * l' =
        l' * ((aY * l⁻¹ : ↥Y) : LGL 2 V) := by
      intro l' hl'
      have hl'' : (⟨l', hLY hl'⟩ : ↥Y) ∈ L.subgroupOf Y :=
        Subgroup.mem_subgroupOf.mpr hl'
      have h := (Subgroup.mem_centralizer_iff.mp hdl) _ hl''
      exact (congrArg (fun z : ↥Y => (z : LGL 2 V)) h).symm
    have hone : ((aY * l⁻¹ : ↥Y) : LGL 2 V) = 1 :=
      hcent _ (Y.mul_mem aY.2 (Y.inv_mem (hLY (Subgroup.mem_subgroupOf.mp hl)))) hcomm
    have haeq : a = (l : LGL 2 V) := by
      refine mul_inv_eq_one.mp ?_
      simpa using hone
    exact haeq ▸ Subgroup.mem_subgroupOf.mp hl
  have hA' : (A.subgroupOf L).map L.subtype ∈ Γ := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAL]; exact hA
  have hr' : mRank ((A.subgroupOf L).map L.subtype) ≤ i := by
    rw [Subgroup.map_subgroupOf_eq_of_le hAL]; exact hr
  have hcardL : Nat.card ↥(A.subgroupOf L) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hcard]
  have helL : IsElemAbelian 2 (A.subgroupOf L) := hel.subgroupOf L
  exact h.false_of_ticorConfigHolds hVfix (hfin ↥L hshape) L.subtype
    Subtype.val_injective (fun g => hLY g.2) hA' hr' hcardL helL

theorem br1_sylow_of_L24 (hfin : FinA5) (h : Assumption131 Y Γ VA i)
    (hLY : L ≤ Y) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hshape : IsL2 ↥L 2)
    (hA : A ∈ Γ) (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A) :
    IsSylowIn 2 A L := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  haveI : Finite ↥Y := Subtype.finite
  obtain ⟨hN, hC⟩ := w183_restrict_normal_cent hLY hLn hcent
  have hshape' : IsL2 ↥(L.subgroupOf Y) 2 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hshape
  have hcard' : Nat.card ↥(A.subgroupOf Y) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le_G A hA)).toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf Y) := hel.subgroupOf Y
  have hSyl := hfin ↥Y (L.subgroupOf Y) hN hshape' hC (A.subgroupOf Y) hcard' hel'
    (h.isTISub_member hA hr)
  exact w183_isSylowIn_of_subgroupOf (h.le_G A hA) hLY hSyl

theorem br1_center_of_U34 (hfin : FinU34) (h : Assumption131 Y Γ VA i)
    (hLY : L ≤ Y) (hLn : ∀ y ∈ Y, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hcent : ∀ y ∈ Y, (∀ l ∈ L, y * l = l * y) → y = 1) (hshape : IsU3 ↥L 2)
    (hA : A ∈ Γ) (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4) (hel : IsElemAbelian 2 A) :
    ∃ S : Subgroup (LGL 2 V), IsSylowIn 2 S L ∧ A = (Subgroup.center ↥S).map S.subtype := by
  classical
  haveI : Finite (LGL 2 V) := w183_finite_lgl
  haveI : Finite ↥Y := Subtype.finite
  obtain ⟨hN, hC⟩ := w183_restrict_normal_cent hLY hLn hcent
  have hshape' : IsU3 ↥(L.subgroupOf Y) 2 :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLY).symm hshape
  have hcard' : Nat.card ↥(A.subgroupOf Y) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (h.le_G A hA)).toEquiv, hcard]
  have hel' : IsElemAbelian 2 (A.subgroupOf Y) := hel.subgroupOf Y
  obtain ⟨S', hS', hAeq⟩ := hfin ↥Y (L.subgroupOf Y) hN hshape' hC (A.subgroupOf Y)
    hcard' hel' (h.isTISub_member hA hr)
  let S : Subgroup (LGL 2 V) := S'.map Y.subtype
  let e : ↥S' ≃* ↥S :=
    Subgroup.equivMapOfInjective S' Y.subtype (Subgroup.subtype_injective Y)
  have hSleL : S ≤ L := by
    intro s hs
    obtain ⟨s', hs', rfl⟩ := Subgroup.mem_map.mp hs
    exact Subgroup.mem_subgroupOf.mp (hS'.le hs')
  have hSp : IsPGroup 2 S := hS'.isPGroup.of_equiv e
  have hSidx : ¬ 2 ∣ S.relIndex L := by
    have hrel := Subgroup.relIndex_map_map_of_injective (H := S') (K := L.subgroupOf Y)
      (f := Y.subtype) (Subgroup.subtype_injective Y)
    rw [Subgroup.map_subgroupOf_eq_of_le hLY] at hrel
    rw [hrel]
    exact hS'.not_dvd_relIndex
  have hSyl : IsSylowIn 2 S L := ⟨hSleL, hSp, hSidx⟩
  have hAmap : A = (Subgroup.center ↥S).map S.subtype := by
    have hmapA : (A.subgroupOf Y).map Y.subtype = A :=
      Subgroup.map_subgroupOf_eq_of_le (h.le_G A hA)
    have hmapC : ((Subgroup.center ↥S').map S'.subtype).map Y.subtype =
        (Subgroup.center ↥S).map S.subtype := by
      rw [Subgroup.map_map]
      have hcomp : (Y.subtype).comp S'.subtype = S.subtype.comp (e : ↥S' →* ↥S) := by
        ext x; rfl
      rw [hcomp, ← Subgroup.map_map]
      exact congrArg (Subgroup.map S.subtype) (Subgroup.map_center_eq e)
    calc A = (A.subgroupOf Y).map Y.subtype := hmapA.symm
      _ = ((Subgroup.center ↥S').map S'.subtype).map Y.subtype := by rw [hAeq]
      _ = (Subgroup.center ↥S).map S.subtype := hmapC
  exact ⟨S, hSyl, hAmap⟩

end CFSG.LocalAnalysis.WeakClosure81

end
