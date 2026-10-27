module

public import CFSG.Sporadic.Recognition.LyonsSimsInvolutions

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Sporadic.LySchreier
  CFSG.Sporadic.Ly

theorem alternating_eleven_not_comm : ∃ a b : alternatingGroup (Fin 11), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, ?_⟩, ⟨Equiv.swap 0 1 * Equiv.swap 1 3, ?_⟩, ?_⟩
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · simp [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul]
  · intro h
    have h2 := congrArg (fun p : alternatingGroup (Fin 11) => (p : Equiv.Perm (Fin 11)) 2) h
    revert h2
    decide

instance normal_zpowers_centralizer_self {G : Type*} [Group G] (t : G) :
    (zpowers (⟨t, mem_centralizer_singleton_self t⟩ : ↥(centralizer ({t} : Set G)))).Normal :=
  normal_of_le_center <| zpowers_le.2 <| Subgroup.mem_center_iff.2 fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.1 y.2)

theorem isDoubleCoverOfAlt_lyC :
    IsDoubleCoverOfAlt lyC 11 :=
  ⟨isQuasisimple_lyC, card_center_lyC, ⟨lyCenterEquiv⟩⟩

section Blueprint

variable {G : Type} [Group G]

theorem isDoubleCoverOfAlt_of_blueprint {t : G} (ht : orderOf t = 2)
    (hperf : Group.IsPerfect ↥(centralizer ({t} : Set G)))
    (hZ : center ↥(centralizer ({t} : Set G)) =
      zpowers (⟨t, mem_centralizer_singleton_self t⟩ : ↥(centralizer ({t} : Set G))))
    (hq : Nonempty (↥(centralizer ({t} : Set G)) ⧸ center ↥(centralizer ({t} : Set G)) ≃*
      alternatingGroup (Fin 11))) :
    IsDoubleCoverOfAlt ↥(centralizer ({t} : Set G)) 11 := by
  obtain ⟨e⟩ := hq
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 11)) :=
    alternatingGroup.isSimpleGroup (by simp)
  refine ⟨⟨hperf, e.isSimpleGroup, ?_⟩, ?_, ⟨e⟩⟩
  · obtain ⟨a, b, hab⟩ := alternating_eleven_not_comm
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using this
  · rw [hZ, Nat.card_zpowers, Subgroup.orderOf_mk]
    exact ht

theorem sylowData_of_blueprint
    {t : G} (ht : orderOf t = 2) (hcover : IsDoubleCoverOfAlt ↥(centralizer ({t} : Set G)) 11)
    (hZ : center ↥(centralizer ({t} : Set G)) =
      zpowers (⟨t, mem_centralizer_singleton_self t⟩ : ↥(centralizer ({t} : Set G)))) :
    SylowData ↥(centralizer ({t} : Set G)) ⟨t, mem_centralizer_singleton_self t⟩ := by
  obtain ⟨e⟩ := nonempty_mulEquiv_of_doubleCover_alt (by norm_num) hcover isDoubleCoverOfAlt_lyC
  set t' : ↥(centralizer ({t} : Set G)) := ⟨t, mem_centralizer_singleton_self t⟩ with ht'
  have hcenter : e t' ∈ Subgroup.center lyC := by
    rw [← Subgroup.map_center_eq e]
    refine ⟨t', ?_, rfl⟩
    rw [hZ]
    exact Subgroup.mem_zpowers t'
  have ht'1 : t' ≠ 1 := by
    intro h
    have : t = 1 := congrArg Subtype.val h
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hez : e t' = zC := by
    rw [center_lyC, mem_zGroup] at hcenter
    rcases hcenter with h | h
    · exact absurd (e.injective (h.trans (map_one e).symm)) ht'1
    · exact h
  have := sylowData_lyC.of_mulEquiv e.symm
  rwa [← hez, e.symm_apply_apply] at this

theorem oneClassDoubleCover_of_blueprint [Finite G]
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {t : G} (ht : orderOf t = 2) (hperf : Group.IsPerfect ↥(centralizer ({t} : Set G)))
    (hZ : center ↥(centralizer ({t} : Set G)) =
      zpowers (⟨t, mem_centralizer_singleton_self t⟩ : ↥(centralizer ({t} : Set G))))
    (hq : Nonempty (↥(centralizer ({t} : Set G)) ⧸ center ↥(centralizer ({t} : Set G)) ≃*
      alternatingGroup (Fin 11))) :
    OneClassDoubleCover G 11 := by
  have hcover := isDoubleCoverOfAlt_of_blueprint ht hperf hZ hq
  obtain ⟨hcentral, hone⟩ := isCentralInvolution_and_isConj_of_sylowData hs hnab ht
    (sylowData_of_blueprint ht hcover hZ)
  exact ⟨t, hcentral, hone, hcover⟩

end Blueprint

@[expose] def LyRecognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ t : G, orderOf t = 2 → Group.IsPerfect ↥(centralizer ({t} : Set G)) →
      center ↥(centralizer ({t} : Set G)) =
        zpowers (⟨t, mem_centralizer_singleton_self t⟩ : ↥(centralizer ({t} : Set G))) →
      Nonempty (↥(centralizer ({t} : Set G)) ⧸
        zpowers (⟨t, mem_centralizer_singleton_self t⟩ : ↥(centralizer ({t} : Set G))) ≃*
          alternatingGroup (Fin 11)) →
      Nonempty (G ≃* Blueprint.NativeSporadic.Ly)

theorem LyRecognition_of_S_Ly_leaf
    (h : S_Ly_leaf) : LyRecognition := by
  intro G _ _ hs hnab t ht hperf hZ hq
  obtain ⟨e⟩ := hq
  exact h G hs hnab (oneClassDoubleCover_of_blueprint hs hnab ht hperf hZ
    ⟨(QuotientGroup.quotientMulEquivOfEq hZ).trans e⟩)

theorem LyRecognition_of_LyContains
    (h : LyContains) : LyRecognition :=
  LyRecognition_of_S_Ly_leaf (S_Ly_leaf_of_LyContains h)

end CFSG.Sporadic.Recognition.LyonsSims
