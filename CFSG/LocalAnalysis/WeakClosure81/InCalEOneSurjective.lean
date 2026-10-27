module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge
public import CFSG.Quasithin.Background.E1OneSurjective

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem inCalEi_of_eOne
    {G : Type} [Group G] [Finite G]
    {T A K : Subgroup G} {i : ℕ}
    (hAT : A ≤ T)
    (hA : CFSG.Open.IsElemAbelian 2 A)
    (hτ : CFSG.Quasithin.E1.tauOf (⊤ : Subgroup G) T A ≤ T ⊓ K)
    (hSyl : CFSG.Quasithin.IsSylowIn 2 (T ⊓ K) K)
    (hOne : CFSG.Quasithin.E1.EOne ↥K (A.subgroupOf K))
    (hi : 1 ≤ i) :
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.InCalEi i T A K := by
  have hAK : A ≤ K :=
    (CFSG.LocalAnalysis.WeakClosure81.le_tA_of_isElemAbelian hAT hA).trans
      (hτ.trans inf_le_right)
  obtain ⟨p, hp, hp2, hoTwo, _hne, hcomm, hcard⟩ := hOne
  have hfit := CFSG.LocalAnalysis.WeakClosure81.fittingSubgroup_bar2_eq_pCore
    (K := ↥K) hp hp2 hoTwo
  have hrel : (CFSG.Open.pCoreOf 2 K).relIndex A = 2 :=
    (CFSG.LocalAnalysis.WeakClosure81.card_barO2_subgroupOf_eq hAK).symm.trans hcard
  have hcase : ECaseI A K := by
    refine ⟨p, hp, hp2, hoTwo, ?_, hrel⟩
    rw [hfit, Subgroup.commutator_comm]
    exact hcomm
  have hnA : ¬ A ≤ CFSG.Open.pCoreOf 2 K := by
    intro hle
    have h1 : (CFSG.Open.pCoreOf 2 K).relIndex A = 1 := Subgroup.relIndex_eq_one.mpr hle
    omega
  have hm : E3.mQuot A (CFSG.Open.pCoreOf 2 K) = 1 := by
    unfold E3.mQuot
    rw [hrel]
    exact padicValNat.self (p := 2) (by norm_num)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨hτ, CFSG.ABGLocalTools.isSylowOf_iff.mpr hSyl, hnA, Or.inl hcase⟩, ?_⟩
  rw [hm]
  exact hi

theorem inCalEi_comap_and_eOne
    {G Γ : Type} [Group G] [Finite G] [Group Γ]
    {T A K : Subgroup G} {I : Subgroup Γ}
    (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hτ : E1.tauOf (⊤ : Subgroup G) T A ≤ T ⊓ K)
    (hS : IsSylowIn 2 (T ⊓ K) K)
    (π : ↥K →* Γ) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker)
    (hI : E1.IsE 1 ⊤ (((T ⊓ K).subgroupOf K).map π)
      ((A.subgroupOf K).map π) I)
    (hIone : E1.EOne ↥I
      (((A.subgroupOf K).map π).subgroupOf I)) :
    let J : Subgroup G := (I.comap π).map K.subtype
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.InCalEi 1 T A J ∧
      E1.EOne ↥J (A.subgroupOf J) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Γ := Finite.of_surjective π hπ
  have hAK : A ≤ K :=
    (le_sup_left.trans (E1.le_tauOf hT hAT hA)).trans (hτ.trans inf_le_right)
  let S0 : Subgroup ↥K := (T ⊓ K).subgroupOf K
  let A0 : Subgroup ↥K := A.subgroupOf K
  let Sbar : Subgroup Γ := S0.map π
  let Abar : Subgroup Γ := A0.map π
  let J0 : Subgroup ↥K := I.comap π
  let J : Subgroup G := J0.map K.subtype
  change CFSG.LocalAnalysis.UniquenessCase.PartTwo.InCalEi 1 T A J ∧
    E1.EOne ↥J (A.subgroupOf J)
  have hS0 : IsSylowIn 2 S0 ⊤ := by
    have := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ K) (K := K) (H := K)
      inf_le_right le_rfl).mpr hS
    simpa [S0, Subgroup.subgroupOf_self] using this
  have hA0S0 : A0 ≤ S0 := by
    intro a ha
    exact Subgroup.mem_subgroupOf.mpr ⟨hAT (Subgroup.mem_subgroupOf.mp ha), a.2⟩
  have hA0ab : IsElemAbelian 2 A0 := CFSG.Open.IsElemAbelian.subgroupOf hA K
  have hItau : E1.tauOf (⊤ : Subgroup Γ) Sbar Abar ≤ Sbar ⊓ I := hI.2.1
  have hIsyl : IsSylowIn 2 (Sbar ⊓ I) I := hI.2.2.1
  have hτmap : (E1.tauOf (⊤ : Subgroup ↥K) S0 A0).map π ≤
      E1.tauOf (⊤ : Subgroup Γ) Sbar Abar := by
    have h := E1.tauOf_map_le π (H := ⊤) (T := S0) (A := A0) le_top
    rwa [Subgroup.map_top_of_surjective π hπ] at h
  have hJ0 : E1.tauOf (⊤ : Subgroup ↥K) S0 A0 ≤ S0 ⊓ J0 := by
    intro t ht
    have ht' : π t ∈ E1.tauOf (⊤ : Subgroup Γ) Sbar Abar :=
      hτmap (Subgroup.mem_map_of_mem π ht)
    exact ⟨E1.tauOf_le _ _ _ ht, Subgroup.mem_comap.mpr (hItau ht').2⟩
  have hA0J0 : A0 ≤ J0 :=
    (le_sup_left.trans (E1.le_tauOf hS0 hA0S0 hA0ab)).trans (hJ0.trans inf_le_right)
  have hAbarI : Abar ≤ I := by
    calc Abar = A0.map π := rfl
      _ ≤ J0.map π := Subgroup.map_mono hA0J0
      _ ≤ I := Subgroup.map_comap_le π I
  let ψ : J0 →* I := π.subgroupComap I
  have hψ : Function.Surjective ψ := MonoidHom.subgroupComap_surjective π I hπ
  have hker_eq : ψ.ker = π.ker.subgroupOf J0 := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hkerψ : IsPGroup 2 ψ.ker := by
    rw [hker_eq]
    exact hker.comap_subtype
  have hcomp : I.subtype.comp ψ = π.comp J0.subtype :=
    MonoidHom.ext fun x => MonoidHom.subgroupComap_apply_coe π I x
  have hAimg : (A0.subgroupOf J0).map ψ = Abar.subgroupOf I := by
    apply Subgroup.map_injective (f := I.subtype) I.subtype_injective
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hA0J0,
      Subgroup.map_subgroupOf_eq_of_le hAbarI]
  have hJ0one : E1.EOne ↥J0 (A0.subgroupOf J0) :=
    CFSG.Quasithin.E1.eOne_of_surjective_of_isPGroup_ker ψ hψ hkerψ
      (A0.subgroupOf J0) (by rwa [hAimg])
  have hkerS0 : π.ker ≤ S0 := by
    exact IsSylowIn.le_of_normal hS0 le_top (by infer_instance) hker
  have hcomapS0 : Sbar.comap π = S0 := Subgroup.comap_map_eq_self hkerS0
  let Ubar : Sylow 2 I := hIsyl.toSylow
  let U : Sylow 2 J0 := Ubar.comapOfKerIsPGroup ψ hkerψ (by
    rw [ψ.range_eq_top_of_surjective hψ]
    exact le_top)
  have hU : (U : Subgroup J0) = (S0 ⊓ J0).subgroupOf J0 := by
    ext x
    dsimp only [U, Ubar, ψ, J0]
    rw [Sylow.coe_comapOfKerIsPGroup, Subgroup.mem_comap,
      IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      MonoidHom.subgroupComap_apply_coe π I x, Subgroup.mem_subgroupOf,
      Subgroup.mem_inf, ← hcomapS0, Subgroup.mem_comap]
    simp only [Subgroup.mem_comap]
  have hSylOf : CFSG.ABGLocalTools.IsSylowOf 2 (S0 ⊓ J0) J0 :=
    ⟨U, by rw [hU, Subgroup.map_subgroupOf_eq_of_le inf_le_right]⟩
  have hSylJ0 : IsSylowIn 2 (S0 ⊓ J0) J0 :=
    CFSG.ABGLocalTools.isSylowOf_iff.mp hSylOf
  have hcardJ0 : Nat.card (E1.barO2 ↥J0 (A0.subgroupOf J0)) = 2 := by
    obtain ⟨-, -, -, -, -, -, hc⟩ := hJ0one
    exact hc
  have hJ0E : E1.IsE 1 (⊤ : Subgroup ↥K) S0 A0 J0 := by
    refine ⟨le_top, hJ0, hSylJ0, Or.inl ⟨hJ0one, ?_⟩⟩
    rw [hcardJ0]
    norm_num
  have hJ0K : E1.IsE 1 K (T ⊓ K) A J := by
    have h := (E1.isE_map_subtype K (i := 1) (T' := S0) (A' := A0) (K' := J0)).mpr hJ0E
    rwa [Subgroup.map_subgroupOf_eq_of_le inf_le_right,
      Subgroup.map_subgroupOf_eq_of_le hAK] at h
  have hJG : E1.IsE 1 (⊤ : Subgroup G) T A J :=
    E1.eight_two hT hAT hA le_top hτ hS hJ0K
  have hAJ : A ≤ J := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hAK]
    exact Subgroup.map_mono hA0J0
  let α : J0 ≃* J := Subgroup.equivMapOfInjective J0 K.subtype K.subtype_injective
  have hAimgα : (A0.subgroupOf J0).map α.toMonoidHom = A.subgroupOf J := by
    apply Subgroup.map_injective (f := J.subtype) J.subtype_injective
    rw [Subgroup.map_map]
    have hα : J.subtype.comp α.toMonoidHom = K.subtype.comp J0.subtype := by
      ext x
      exact Subgroup.coe_equivMapOfInjective_apply J0 K.subtype K.subtype_injective x
    rw [hα, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hA0J0,
      Subgroup.map_subgroupOf_eq_of_le hAK, Subgroup.map_subgroupOf_eq_of_le hAJ]
  have hJone : E1.EOne ↥J (A.subgroupOf J) := by
    have h := (E1.eOne_map α (A0.subgroupOf J0)).mp hJ0one
    rwa [hAimgα] at h
  exact ⟨inCalEi_of_eOne hAT hA hJG.2.1 hJG.2.2.1
    hJone (by norm_num), hJone⟩

theorem relative_generation_printed_of_eOne
    {G Γ : Type} [Group G] [Finite G] [Group Γ]
    {T A K : Subgroup G}
    (hT : IsSylowIn 2 T ⊤)
    (hAT : A ≤ T) (hA : CFSG.Open.IsElemAbelian 2 A)
    (hτ : E1.tauOf (⊤ : Subgroup G) T A ≤ T ⊓ K)
    (hS : IsSylowIn 2 (T ⊓ K) K)
    (π : ↥K →* Γ) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker)
    (hgen : ((T ⊓ K).subgroupOf K).map π ⊔
      (⨆ I ∈ {I : Subgroup Γ |
        E1.IsE 1 ⊤ (((T ⊓ K).subgroupOf K).map π)
          ((A.subgroupOf K).map π) I ∧
        E1.EOne ↥I (((A.subgroupOf K).map π).subgroupOf I)}, I) = ⊤) :
    K ≤ T ⊔ ⨆ J ∈ {J : Subgroup G |
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.InCalEi 1 T A J}, J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAK : A ≤ K :=
    (le_sup_left.trans (E1.le_tauOf hT hAT hA)).trans (hτ.trans inf_le_right)
  let S0 : Subgroup ↥K := (T ⊓ K).subgroupOf K
  let Gens : Subgroup G := ⨆ J : Subgroup G,
    ⨆ (_ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.InCalEi 1 T A J), J
  let M : Subgroup G := T ⊔ Gens
  let D0 : Subgroup ↥K := M.subgroupOf K
  change K ≤ M
  have hS0D0 : S0 ≤ D0 := by
    intro x hx
    have hxT : (x : G) ∈ T := (Subgroup.mem_subgroupOf.mp hx).1
    exact Subgroup.mem_subgroupOf.mpr (show (x : G) ∈ M from Subgroup.mem_sup_left hxT)
  have hIle : ∀ I : Subgroup Γ, E1.IsE 1 ⊤ (S0.map π) ((A.subgroupOf K).map π) I →
      E1.EOne ↥I (((A.subgroupOf K).map π).subgroupOf I) →
      I ≤ D0.map π := by
    intro I hI hIone
    let J0 : Subgroup ↥K := I.comap π
    let J : Subgroup G := J0.map K.subtype
    have hpair := inCalEi_comap_and_eOne (G := G) (Γ := Γ) (T := T) (A := A) (K := K)
      (I := I) hT hAT hA hτ hS π hπ hker (by simpa [S0] using hI) (by simpa using hIone)
    obtain ⟨hInCal, -⟩ := hpair
    have hJM : J ≤ M :=
      (le_iSup₂_of_le (f := fun J (_ : CFSG.LocalAnalysis.UniquenessCase.PartTwo.InCalEi 1 T A J)
        => J) J (by simpa [J, J0] using hInCal) le_rfl).trans
        (show Gens ≤ M from le_sup_right)
    have hJ0D0 : J0 ≤ D0 := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr
        (hJM (Subgroup.mem_map_of_mem K.subtype hx))
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ I]
    exact Subgroup.map_mono hJ0D0
  have htop : D0.map π = ⊤ := by
    apply top_le_iff.mp
    rw [← hgen]
    refine sup_le ?_ ?_
    · exact Subgroup.map_mono hS0D0
    · exact iSup₂_le fun I hI => hIle I hI.1 hI.2
  have hkerS0 : π.ker ≤ S0 := by
    exact IsSylowIn.le_of_normal
      (show IsSylowIn 2 S0 ⊤ from by
        have := (E1.isSylowIn_subgroupOf_iff (p := 2) (P := T ⊓ K) (K := K) (H := K)
          inf_le_right le_rfl).mpr hS
        simpa [S0, Subgroup.subgroupOf_self] using this)
      le_top (by infer_instance) hker
  have hkerD0 : π.ker ≤ D0 := hkerS0.trans hS0D0
  have hD0top : D0 = ⊤ := by
    have h := Subgroup.comap_map_eq_self (f := π) hkerD0
    rw [htop, Subgroup.comap_top] at h
    exact h.symm
  intro k hk
  exact Subgroup.mem_subgroupOf.mp (hD0top ▸ Subgroup.mem_top (⟨k, hk⟩ : ↥K))

end CFSG.LocalAnalysis.WeakClosure81
