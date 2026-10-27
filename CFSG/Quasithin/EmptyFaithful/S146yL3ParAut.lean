module

public import CFSG.Quasithin.EmptyFaithful.S146yL3Par
public import CFSG.Quasithin.EmptyFaithful.S146yB1Res
public import CFSG.Quasithin.EmptyFaithful.S146xB2C2
public import CFSG.Quasithin.EmptyFaithful.SzN2Quot
public import CFSG.Quasithin.EmptyFaithful.SBd3Transport
public import CFSG.Quasithin.Vol2.GoldschmidtLem1227EqAbs

public section

namespace CFSG.Quasithin

section Transport

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Family CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.Blueprint CFSG.QuasithinUnique.Ch1

theorem inner_of_normalizes_maxParabolic {Γ : Type} [Group Γ] [Finite Γ] {Ks P : Subgroup Γ}
    (hKs : IsPSL 3 2 1 ↥Ks) (hP : IsMaxParabolic2 Ks P) {d : Γ}
    (hdK : d ∈ Subgroup.normalizer (Ks : Set Γ)) (hdP : d ∈ Subgroup.normalizer (P : Set Γ)) :
    ∃ k ∈ Ks, ∀ x ∈ Ks, d * x * d⁻¹ = k * x * k⁻¹ := by
  obtain ⟨e⟩ := isPSL_three_two_iff.mp hKs
  have hPK : IsMaxParabolic2 (⊤ : Subgroup ↥Ks) (P.subgroupOf Ks) :=
    CFSG.Quasithin.SzN2.isMaxParabolic2_top_of_map hP
  have hPm : IsMaxParabolic2 (⊤ : Subgroup SL3F2) ((P.subgroupOf Ks).map e.toMonoidHom) := by
    have := (SBd3T.isMaxParabolic2_map_iff e.toMonoidHom e.injective ⊤ (P.subgroupOf Ks)).mpr hPK
    rwa [Subgroup.map_top_of_surjective _ e.surjective] at this
  set αK : MulAut ↥Ks := Ks.normalizerMonoidHom ⟨d, hdK⟩ with hαK
  have hαKval : ∀ x : ↥Ks, ((αK x : ↥Ks) : Γ) = d * x * d⁻¹ := fun x => rfl
  have hstab : ∀ k : ↥Ks, αK k ∈ P.subgroupOf Ks ↔ k ∈ P.subgroupOf Ks := by
    intro k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hαKval]
    exact (Subgroup.mem_normalizer_iff.mp hdP (k : Γ)).symm
  set α' : MulAut SL3F2 := e.symm.trans (αK.trans e) with hα'
  have hα'e : ∀ k : ↥Ks, α' (e k) = e (αK k) := by
    intro k
    simp [hα']
  have hmap : ((P.subgroupOf Ks).map e.toMonoidHom).map α'.toMonoidHom =
      (P.subgroupOf Ks).map e.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨m, ⟨k, hk, rfl⟩, rfl⟩
      refine ⟨αK k, (hstab k).mpr hk, ?_⟩
      exact (hα'e k).symm
    · rintro ⟨k, hk, rfl⟩
      refine ⟨e (αK.symm k), ⟨αK.symm k, ?_, rfl⟩, ?_⟩
      · apply (hstab (αK.symm k)).mp
        rwa [MulEquiv.apply_symm_apply]
      · show α' (e (αK.symm k)) = e k
        rw [hα'e, MulEquiv.apply_symm_apply]
  obtain ⟨s, hs⟩ := inner_of_stable hPm α' hmap
  refine ⟨((e.symm s : ↥Ks) : Γ), (e.symm s).2, fun x hx => ?_⟩
  have h2 : e (αK ⟨x, hx⟩) = s * e ⟨x, hx⟩ * s⁻¹ := by
    rw [← hα'e, hs]
    rfl
  have h1 : αK ⟨x, hx⟩ = e.symm s * ⟨x, hx⟩ * (e.symm s)⁻¹ := by
    have := congrArg e.symm h2
    simpa [map_mul, map_inv] using this
  have := congrArg (fun z : ↥Ks => (z : Γ)) h1
  simpa [hαKval] using this


theorem l3TwoParabolicAut_proof : L3TwoParabolicAut := by
  intro Γ _ _ Ts Ks P hTs hKs hP hN
  obtain ⟨e⟩ := isPSL_three_two_iff.mp hKs
  have hcard : Nat.card ↥Ks = 168 := by
    rw [Nat.card_congr (e.trans (slEquivGL 3)).toEquiv]
    exact CFSG.LieType.SteinbergBR.AutGL32.card_GL32
  have hZ : Subgroup.center ↥Ks = ⊥ := center_eq_bot_of_shape (Or.inr (Or.inl hKs))
  have hT2 : IsPGroup 2 ↥(Ts ⊓ Subgroup.normalizer (Ks : Set Γ)) := hTs.to_le inf_le_left
  have h8 := CFSG.Quasithin.H13.Lem1227Eq.autCard_le_eight_of_inner hT2 inf_le_right hZ hcard
    (fun d hd => inner_of_normalizes_maxParabolic hKs hP hd.2 (hN hd))
  have e1 : E2.autCard (Ts ⊓ Subgroup.normalizer (Ks : Set Γ)) Ks = E2.autCard Ts Ks := by
    have h : Ts ⊓ Subgroup.normalizer (Ks : Set Γ) ⊓ Subgroup.normalizer (Ks : Set Γ) =
        Ts ⊓ Subgroup.normalizer (Ks : Set Γ) := by rw [inf_assoc, inf_idem]
    unfold E2.autCard
    rw [h]
  rwa [e1] at h8

end Transport

end CFSG.Quasithin
