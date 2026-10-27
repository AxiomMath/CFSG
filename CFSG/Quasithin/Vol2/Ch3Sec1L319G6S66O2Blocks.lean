module

public import CFSG.Quasithin.Vol2.Ch3zBlocks
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Perf

public section

namespace CFSG.Quasithin.H13.L319.S66

open CFSG.Quasithin

theorem blocks_perfect_of_trans {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
    {𝓗 : Finset (Subgroup (MulAut V))} (hctx : Ch3z.BlkCtx X T M 𝓗) {K₁ : Subgroup (MulAut V)}
    (h1 : K₁ ∈ 𝓗) (hp : Group.IsPerfect ↥K₁) : ∀ K ∈ 𝓗, Group.IsPerfect ↥K := by
  intro K hK
  obtain ⟨t, -, ht⟩ := hctx.trans h1 hK
  subst ht
  show Group.IsPerfect ↥(K₁.map (MulAut.conj t).toMonoidHom)
  exact Group.IsPerfect.map (MulAut.conj t).toMonoidHom

theorem O2_eq_iSup_of_blocks {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
    {𝓗 : Finset (Subgroup (MulAut V))} (hctx : Ch3z.BlkCtx X T M 𝓗)
    (hperf : ∀ K ∈ 𝓗, Group.IsPerfect ↥K) :
    CFSG.Quasithin.H13.L319.S66.O2 ↥X = (⨆ K ∈ 𝓗, K).subgroupOf X := by
  classical
  haveI : Finite (MulAut V) := MulEquiv.finite_left
  have hJX : ffJ X ≤ X := B6.ffJ_le X
  have hTX : T ≤ X := hctx.mp.isSylow.1
  have hTp : IsPGroup 2 ↥T := hctx.mp.isSylow.2.1
  rw [← hctx.ffJ_eq]
  haveI : ((ffJ X).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).2 (B6.le_normalizer_ffJ X)
  have hP : IsPGroup 2 ↥(T.subgroupOf X) := hTp.comap_subtype
  have hYP : (ffJ X).subgroupOf X ⊔ T.subgroupOf X = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hJX hTX, ← hctx.eq_sup, Subgroup.subgroupOf_self]
  have hYperf : ⁅(ffJ X).subgroupOf X, (ffJ X).subgroupOf X⁆ = (ffJ X).subgroupOf X := by
    obtain ⟨𝓚, h𝓚⟩ : ∃ 𝓚 : Finset (Subgroup ↥X), 𝓚 = 𝓗.image (fun K => K.subgroupOf X) := ⟨_, rfl⟩
    have hin : ∀ K ∈ 𝓗, K.subgroupOf X ∈ 𝓚 := fun K hK => by
      rw [h𝓚]
      exact Finset.mem_image_of_mem (fun K : Subgroup (MulAut V) => K.subgroupOf X) hK
    have hout : ∀ K' ∈ 𝓚, ∃ K ∈ 𝓗, K.subgroupOf X = K' := fun K' hK' => by
      rw [h𝓚] at hK'
      exact Finset.mem_image.mp hK'
    have hle : ffJ X ≤ (⨆ K ∈ 𝓚, K).map X.subtype := by
      rw [hctx.ffJ_eq]
      refine iSup₂_le fun K hK => ?_
      intro k hk
      exact Subgroup.mem_map.mpr
        ⟨⟨k, hctx.mem_le hK hk⟩,
          le_iSup₂ (f := fun K' (_ : K' ∈ 𝓚) => K') (K.subgroupOf X) (hin K hK)
            (Subgroup.mem_subgroupOf.mpr hk), rfl⟩
    have hZ : (ffJ X).subgroupOf X = ⨆ K ∈ 𝓚, K := by
      refine le_antisymm ?_ ?_
      · intro x hx
        obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp (hle (Subgroup.mem_subgroupOf.mp hx))
        have hzx' : z = x := Subtype.ext hzx
        rw [← hzx']
        exact hz
      · refine iSup₂_le fun K' hK' => ?_
        obtain ⟨K, hK, rfl⟩ := hout K' hK'
        intro x hx
        rw [Subgroup.mem_subgroupOf] at hx ⊢
        rw [hctx.ffJ_eq]
        exact (le_iSup₂ (f := fun K (_ : K ∈ 𝓗) => K) K hK) hx
    have hperf' : ∀ K' ∈ 𝓚, Group.IsPerfect ↥K' := by
      intro K' hK'
      obtain ⟨K, hK, rfl⟩ := hout K' hK'
      haveI := hperf K hK
      let e := Subgroup.subgroupOfEquivOfLe (hctx.mem_le hK)
      exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hcomm := commutator_iSup_eq_of_perfect 𝓚 hperf'
    rw [← hZ] at hcomm
    exact hcomm
  exact O2_eq_of_perfect_normal ((ffJ X).subgroupOf X) (T.subgroupOf X) hP hYP hYperf

end CFSG.Quasithin.H13.L319.S66

end
