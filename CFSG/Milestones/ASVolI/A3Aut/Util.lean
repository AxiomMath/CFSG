module

public import CFSG.Milestones.ASVolI.A3Aut.Case5

public section

namespace CFSG.ASVolI

open CFSG.Open
open scoped Pointwise

section Util

theorem burnsideAut_range_inf_normalizer {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (U : Subgroup X) :
    f.range ⊓ Subgroup.normalizer ((U.map f : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (U : Set X)).map f := by
  apply le_antisymm
  · rintro _ ⟨⟨x, rfl⟩, hx⟩
    have hx' : f x ∈ Subgroup.normalizer ((U.map f : Subgroup Y) : Set Y) := hx
    refine ⟨x, ?_, rfl⟩
    show x ∈ Subgroup.normalizer (U : Set X)
    rw [Subgroup.mem_normalizer_iff] at hx' ⊢
    intro u
    constructor
    · intro hu
      have h1 := (hx' (f u)).1 ⟨u, hu, rfl⟩
      obtain ⟨v, hv, hve⟩ := h1
      have : x * u * x⁻¹ = v := hf (by rw [hve]; simp)
      rw [this]
      exact hv
    · intro hu
      have h1 : f x * f u * (f x)⁻¹ ∈ U.map f := ⟨_, hu, by simp⟩
      obtain ⟨v, hv, hve⟩ := (hx' (f u)).2 h1
      rwa [hf hve] at hv
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, burnsideAut_map_le_normalizer_map f (le_refl _) ⟨x, hx, rfl⟩⟩

theorem burnsideAut_exists_equiv_sylow {X P : Type} [Group X] [Group P] [Finite P] (e : X ≃* P)
    {Q : Subgroup X} {R : Subgroup P} (hQ : CFSG.QuasithinUnique.IsSylowTwoOf Q ⊤)
    (hR : CFSG.QuasithinUnique.IsSylowTwoOf R ⊤) : ∃ e' : X ≃* P, Q.map e'.toMonoidHom = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ' : CFSG.QuasithinUnique.IsSylowTwoOf (Q.map e.toMonoidHom) ⊤ := by
    have h := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv e (X := Q) (Y := ⊤)).2 hQ
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
  obtain ⟨h1, h2⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hQ'
  obtain ⟨h3, h4⟩ := CFSG.Quasithin.H13.FiveNorm.isSylowTwoOf_top_index hR
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (h1.toSylow h2) (h3.toSylow h4)
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have hR' : R = MulAut.conj g • Q.map e.toMonoidHom :=
    (congrArg (fun S : Sylow 2 P => (S : Subgroup P)) hg).symm
  rw [hR']
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨e q, ⟨q, hq, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨q, hq, rfl⟩

theorem burnsideAut_isSylowTwoOf_subgroupOf {G : Type} [Group G] {L T : Subgroup G} [L.Normal]
    (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) :
    CFSG.QuasithinUnique.IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
  have hsyl := burnsideA315x_sylow_inf (L := L) hT
  refine ⟨le_top, ?_, ?_⟩
  · exact hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  · have h1 : (((T ⊓ L).subgroupOf L).subgroupOf (⊤ : Subgroup ↥L)).index =
        ((T ⊓ L).subgroupOf L).index := by
      change ((T ⊓ L).subgroupOf L).relIndex ⊤ = _
      exact Subgroup.relIndex_top_right _
    rw [h1]
    exact hsyl.2.2

theorem burnsideAut_isCyclic_of_le {A : Type*} [Group A] {H K : Subgroup A} (hHK : H ≤ K)
    [IsCyclic K] : IsCyclic H := by
  have e : ↥(H.subgroupOf K) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHK
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem burnsideAut_pinned_of_field {X M C : Type} [Group X] [Group M] [Group C]
    {K : Type} [Field K] [Finite K] (φ : RingAut K →* MulAut M) (hφ : Function.Injective φ)
    (hcyc : IsCyclic (RingAut K)) (Ψ : M ≃* C) {UM : Subgroup M}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf UM ⊤)
    (hφU : ∀ σ, UM.map (φ σ).toMonoidHom = UM)
    (P : RingAut K → MulAut C → Prop) (hP : ∀ σ, P σ (MulAut.congr Ψ (φ σ)))
    (ε : X ≃* M) {S : Subgroup X} (hεS : S.map ε.toMonoidHom = UM)
    (F : Subgroup (MulAut X)) (hF : F ≤ φ.range.map (MulAut.congr ε.symm).toMonoidHom) :
    IsCyclic F ∧ Nat.card F ∣ Nat.card (RingAut K) ∧
      ∃ σ : RingAut K, orderOf σ = Nat.card F ∧
        ChA.HasPinnedSylowFieldAction (ε.trans Ψ) S F (P σ) := by
  haveI : Finite (RingAut K) := Finite.of_injective _ (fun a b h => RingEquiv.ext
    fun x => congrFun (congrArg DFunLike.coe h) x)
  set Fm : Subgroup (MulAut M) := F.map (MulAut.congr ε).toMonoidHom with hFm
  have hinv : ∀ x : MulAut X, MulAut.congr ε.symm (MulAut.congr ε x) = x :=
    burnsideAut_congr_symm_congr ε
  have hinv' : ∀ x : MulAut M, MulAut.congr ε (MulAut.congr ε.symm x) = x := fun x => by
    ext y
    simp [MulAut.congr_apply]
  have hFmle : Fm ≤ φ.range := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hF hx
    change MulAut.congr ε (MulAut.congr ε.symm y) ∈ φ.range
    rw [hinv']
    exact hy
  haveI : IsCyclic φ.range := isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  haveI : IsCyclic Fm := burnsideAut_isCyclic_of_le hFmle
  have eF : ↥F ≃* ↥Fm := F.equivMapOfInjective _ (MulAut.congr ε).injective
  have hcardF : Nat.card F = Nat.card Fm := Nat.card_congr eF.toEquiv
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥Fm)
  have hFmz : Fm = Subgroup.zpowers (g : MulAut M) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      have := congrArg Subtype.val hk
      simpa using this
    · rw [Subgroup.zpowers_le]
      exact g.2
  obtain ⟨σ, hσ⟩ := hFmle g.2
  have hord : orderOf σ = Nat.card F := by
    rw [← orderOf_injective φ hφ σ, hσ, hcardF]
    rw [← Nat.card_zpowers]
    exact congrArg (fun H : Subgroup (MulAut M) => Nat.card H) hFmz.symm
  refine ⟨isCyclic_of_surjective eF.symm.toMonoidHom eF.symm.surjective, ?_, σ, hord, ?_⟩
  · rw [← hord]
    exact orderOf_dvd_natCard σ
  refine ⟨S.map (ε.trans Ψ).toMonoidHom, MulAut.congr Ψ (φ σ), rfl, ?_, ?_, hP σ, ?_⟩
  ·
    have h1 : S.map (ε.trans Ψ).toMonoidHom = UM.map Ψ.toMonoidHom := by
      rw [← hεS, Subgroup.map_map]
      rfl
    rw [h1]
    have h2 := (CFSG.QuasithinUnique.Setup.Layer.isSylowTwoOf_map_mulEquiv Ψ (X := UM) (Y := ⊤)).2 hU
    rw [Subgroup.map_top_of_surjective _ Ψ.surjective] at h2
    exact ⟨le_top, h2.2.1, h2.2.2⟩
  ·
    have h1 : F.map (MulAut.congr (ε.trans Ψ)).toMonoidHom =
        Fm.map (MulAut.congr Ψ).toMonoidHom := by
      rw [hFm, Subgroup.map_map]
      congr 1
    rw [h1, hFmz, MonoidHom.map_zpowers, hσ]
    rfl
  ·
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have h1 : S.map (ε.trans Ψ).toMonoidHom = UM.map Ψ.toMonoidHom := by
      rw [← hεS, Subgroup.map_map]
      rfl
    rw [h1, ← map_zpow, ← map_zpow, Subgroup.map_map]
    have h2 : (MulAut.congr Ψ (φ (σ ^ k))).toMonoidHom.comp Ψ.toMonoidHom =
        Ψ.toMonoidHom.comp (φ (σ ^ k)).toMonoidHom := by
      ext y
      simp [MulAut.congr_apply]
    rw [h2, ← Subgroup.map_map, hφU]

end Util

end CFSG.ASVolI
