module

public import CFSG.Quasithin.Background.E1Invariance
public import CFSG.Quasithin.Background.RonanF713Sylow
public import CFSG.LocalAnalysis.SectionRank.SQTKTransport
public import CFSG.Quasithin.Background.F7TwoE2Base

public section

namespace CFSG.Quasithin.RonanF713

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

variable {G : Type*} [Group G]

private theorem subgroupOf_le_subgroupOf_iff' {X Y H : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    X.subgroupOf H ≤ Y.subgroupOf H ↔ X ≤ Y := by
  rw [← Subgroup.map_le_map_iff_of_injective H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]

private theorem map_subgroupOf_subgroupOfEquivOfLe' {K H : Subgroup G} (hK : K ≤ H)
    (B : Subgroup G) :
    ((B.subgroupOf H).subgroupOf (K.subgroupOf H)).map
        (Subgroup.subgroupOfEquivOfLe hK).toMonoidHom = B.subgroupOf K := by
  ext ⟨x, hx⟩
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  exact Iff.rfl

private theorem isElemAbelian_of_map_injective' {K L : Type*} [Group K] [Group L] {p : ℕ}
    {f : K →* L} (hf : Function.Injective f) {B : Subgroup K}
    (h : IsElemAbelian p (B.map f)) : IsElemAbelian p B := by
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have := E1.commute_of_isElemAbelian h (Subgroup.mem_map_of_mem f x.2)
      (Subgroup.mem_map_of_mem f y.2)
    exact hf (by simpa [map_mul] using this)
  · exact hf (by simpa [map_pow] using h.2 (f x) (Subgroup.mem_map_of_mem f hx))

theorem isE_subgroupOf_loc {i : ℕ} {H T A K : Subgroup G} [Finite ↥H] (hT : T ≤ H) (hA : A ≤ H)
    (hK : K ≤ H) :
    E1.IsE i H T A K ↔
      E1.IsE i (⊤ : Subgroup ↥H) (T.subgroupOf H) (A.subgroupOf H) (K.subgroupOf H) := by
  have hTK : (T ⊓ K).subgroupOf H = T.subgroupOf H ⊓ K.subgroupOf H := rfl
  have hTKH : T ⊓ K ≤ H := inf_le_left.trans hT
  have htau := E1.tauOf_top_subgroupOf hT hA
  haveI : Finite ↥K :=
    Finite.of_injective (Subgroup.inclusion hK) (Subgroup.inclusion_injective hK)
  haveI : Finite ↥(K.subgroupOf H) := inferInstance
  unfold E1.IsE
  rw [← hTK, htau, subgroupOf_le_subgroupOf_iff' ((E1.tauOf_le H T A).trans hT) hTKH,
    E1.isSylowIn_subgroupOf_iff hTKH hK,
    ← map_subgroupOf_subgroupOfEquivOfLe' hK A, ← map_subgroupOf_subgroupOfEquivOfLe' hK (T ⊓ K),
    ← E1.eOne_map, ← E1.eTwo_map, E1.card_barO2_map, E1.card_barRad_map]
  exact and_congr ⟨fun _ => le_top, fun _ => hK⟩ Iff.rfl

theorem isSQTKCat_conjSub_loc {G : Type} [Group G] {X : Subgroup G} [Finite ↥X] (g : G)
    (h : CFSG.SectionRank.IsSQTKCat ↥X) : CFSG.SectionRank.IsSQTKCat ↥(conjSub g X) := by
  haveI : Finite ↥(conjSub g X) := finite_conjSub g X
  let e : ↥(conjSub g X) ≃* ↥X := ((MulAut.conj g).subgroupMap X).symm
  exact CFSG.SectionRank.IsSQTKCat.of_mulEquiv h e

theorem claimCE1_loc (hC : F7Two.ClaimCE1) {G : Type} [Group G] {X S A H : Subgroup G}
    [Finite ↥X] (hX : CFSG.SectionRank.IsSQTKCat ↥X) (hS : IsSylowTwoOf S X) (hAS : A ≤ S)
    (hAel : IsElemAbelian 2 A) (hnot : ¬ A ≤ pCoreOf 2 X) (hE : E1.IsE 1 X S A H) (hAH : A ≤ H) :
    twoResidual H ≤ Subgroup.closure (F7Two.nonTwoConj A H) := by
  have hSX : S ≤ X := hS.1
  have hAX : A ≤ X := hAS.trans hSX
  have hHX : H ≤ X := hE.1
  have hSyl : IsSylowTwoOf (S.subgroupOf X) (⊤ : Subgroup ↥X) := by
    have hS' : IsSylowIn 2 S X := hS
    have h := (E1.isSylowIn_subgroupOf_iff (p := 2) hSX (le_refl X)).mpr hS'
    rw [Subgroup.subgroupOf_self] at h
    exact h
  have hAS' : A.subgroupOf X ≤ S.subgroupOf X := by
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr (hAS (Subgroup.mem_subgroupOf.mp hz))
  have hA'el : IsElemAbelian 2 (A.subgroupOf X) := by
    refine isElemAbelian_of_map_injective' X.subtype_injective ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hAX]
    exact hAel
  have hnot' : ¬ A.subgroupOf X ≤ pCoreOf 2 (⊤ : Subgroup ↥X) := by
    intro hA'
    apply hnot
    calc A = (A.subgroupOf X).map X.subtype := (Subgroup.map_subgroupOf_eq_of_le hAX).symm
      _ ≤ (pCoreOf 2 (⊤ : Subgroup ↥X)).map X.subtype := Subgroup.map_mono hA'
      _ = pCoreOf 2 X := E1.map_subtype_pCoreOf_top X
  have hE' : E1.IsE 1 (⊤ : Subgroup ↥X) (S.subgroupOf X) (A.subgroupOf X) (H.subgroupOf X) :=
    (isE_subgroupOf_loc hSX hAX hHX).mp hE
  have hAH' : A.subgroupOf X ≤ H.subgroupOf X := by
    intro z hz
    exact Subgroup.mem_subgroupOf.mpr (hAH (Subgroup.mem_subgroupOf.mp hz))
  have hX' : CFSG.SectionRank.IsSQTKCat ↥(⊤ : Subgroup ↥X) :=
    CFSG.SectionRank.IsSQTKCat.of_mulEquiv hX Subgroup.topEquiv
  have hgen := hC ↥X (⊤ : Subgroup ↥X) (S.subgroupOf X) (A.subgroupOf X) (H.subgroupOf X)
    hX' hSyl hAS' hA'el hnot' hE' hAH'
  have h1 : twoResidual H ≤ (twoResidual (H.subgroupOf X)).map X.subtype := by
    refine twoResidual_le_of_isTwoQuotient ?_ ?_ ?_
    · have h := Subgroup.map_mono (f := X.subtype) (twoResidual_le (H.subgroupOf X))
      rwa [Subgroup.map_subgroupOf_eq_of_le hHX] at h
    · intro x hx
      have hxX : x ∈ X := hHX hx
      have hmem : (⟨x, hxX⟩ : ↥X) ∈ H.subgroupOf X := Subgroup.mem_subgroupOf.mpr hx
      exact Subgroup.le_normalizer_map X.subtype
        (Subgroup.mem_map_of_mem X.subtype (le_normalizer_twoResidual (H.subgroupOf X) hmem))
    · intro y hy
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (H.subgroupOf X) ⟨y, hHX hy⟩
        (Subgroup.mem_subgroupOf.mpr hy)
      exact ⟨k, ⟨_, hk, by simp⟩⟩
  have h2 : (Subgroup.closure (F7Two.nonTwoConj (A.subgroupOf X) (H.subgroupOf X))).map
      X.subtype ≤ Subgroup.closure (F7Two.nonTwoConj A H) := by
    rw [MonoidHom.map_closure]
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨q, hq, rfl⟩
    have hq' : q ∈ H.subgroupOf X ∧
        ¬ IsPGroup 2 ↥(A.subgroupOf X ⊔ conjSubgroup (A.subgroupOf X) q) := hq
    have hqH : X.subtype q ∈ H := Subgroup.mem_subgroupOf.mp hq'.1
    refine Subgroup.subset_closure ⟨hqH, fun hP => ?_⟩
    refine hq'.2 fun y => ?_
    have hle : A.subgroupOf X ⊔ conjSubgroup (A.subgroupOf X) q ≤
        (A ⊔ conjSubgroup A (X.subtype q)).comap X.subtype := by
      refine sup_le (fun z hz => Subgroup.mem_sup_left hz) (fun z hz => ?_)
      rw [mem_conjSubgroup_iff] at hz
      exact Subgroup.mem_sup_right (by rw [mem_conjSubgroup_iff]; exact hz)
    have hyP : X.subtype y.1 ∈ A ⊔ conjSubgroup A (X.subtype q) := hle y.2
    obtain ⟨k, hk⟩ := F7Two.pow_eq_one_of_mem_isPGroup hP hyP
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using hk))⟩
  have hgen' : twoResidual (H.subgroupOf X) ≤
      Subgroup.closure (F7Two.nonTwoConj (A.subgroupOf X) (H.subgroupOf X)) := hgen
  exact h1.trans ((Subgroup.map_mono (f := X.subtype) hgen').trans h2)

end CFSG.Quasithin.RonanF713
