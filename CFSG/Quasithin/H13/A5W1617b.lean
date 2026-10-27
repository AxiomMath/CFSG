module

public import CFSG.Quasithin.Recognition.HSTypeConj
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem quasithinIsCComponent_map (φ : G ≃* G) {L X : Subgroup G}
    (h : quasithinIsCComponent L X) :
    quasithinIsCComponent (L.map φ.toMonoidHom) (X.map φ.toMonoidHom) := by
  obtain ⟨hne, hp, hs, hmin⟩ := h
  refine ⟨fun h0 => hne ((map_equiv_eq_bot_iff φ L).mp h0), ?_,
    A3.subnormal_map φ.toMonoidHom hs, ?_⟩
  · rw [← Subgroup.map_commutator, hp]
  · intro K hKL hK1 hKp hKs
    have hK' : K.map φ.symm.toMonoidHom < L := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [← map_equiv_symm_map_equiv φ L]
        exact Subgroup.map_mono hKL.le
      · intro he
        apply hKL.ne
        rw [← he, map_equiv_map_equiv_symm]
    refine hmin _ hK' (fun h0 => hK1 ((map_equiv_eq_bot_iff φ.symm K).mp h0)) ?_ ?_
    · rw [← Subgroup.map_commutator, hKp]
    · have := A3.subnormal_map φ.symm.toMonoidHom hKs
      rwa [map_equiv_symm_map_equiv] at this

theorem quasithinIsLocal_map (φ : G ≃* G) {T L : Subgroup G} (h : quasithinIsLocal T L) :
    quasithinIsLocal (T.map φ.toMonoidHom) (L.map φ.toMonoidHom) := by
  obtain ⟨hT, hc, hidx, hO⟩ := h
  refine ⟨(isPGroup_map_equiv_iff 2 φ T).mpr hT, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup]
    exact quasithinIsCComponent_map φ hc
  · rw [← Subgroup.map_sup]
    show ¬ 2 ∣ (T.map φ.toMonoidHom).relIndex ((L ⊔ T).map φ.toMonoidHom)
    rw [Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
    exact hidx
  · rw [← Subgroup.map_sup, pCoreOf_map_equiv]
    exact fun h0 => hO ((map_equiv_eq_bot_iff φ _).mp h0)

theorem quasithinV2_map (φ : G ≃* G) (L : Subgroup G) :
    quasithinV2 (L.map φ.toMonoidHom) = (quasithinV2 L).map φ.toMonoidHom := by
  unfold quasithinV2
  rw [Subgroup.map_commutator, MonoidHom.map_closure, pCoreOf_map_equiv,
    centralizer_map_equiv, ← map_equiv_inf]
  congr 2
  ext w
  constructor
  · rintro ⟨hw, hw2⟩
    obtain ⟨x, hx, rfl⟩ := hw
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    apply φ.injective
    rw [map_pow]
    simpa using hw2
  · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_pow, hx2, map_one]

theorem quasithinIsFaithfulLocal_map (φ : G ≃* G) {T L : Subgroup G}
    (h : quasithinIsFaithfulLocal T L) :
    quasithinIsFaithfulLocal (T.map φ.toMonoidHom) (L.map φ.toMonoidHom) := by
  obtain ⟨hloc, hO2, hF, hV⟩ := h
  refine ⟨quasithinIsLocal_map φ hloc, ?_, ?_, ?_⟩
  · intro N hNL hN hpow
    have hN'L : N.map φ.symm.toMonoidHom ≤ L := by
      rw [← map_equiv_symm_map_equiv φ L]
      exact Subgroup.map_mono hNL
    have hN' : ((N.map φ.symm.toMonoidHom).subgroupOf L).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hN'L]
      rintro x y ⟨n, hn, rfl⟩ hy
      have hφy : φ y ∈ L.map φ.toMonoidHom := ⟨y, hy, rfl⟩
      have h1 := (Subgroup.normal_subgroupOf_iff hNL).mp hN n (φ y) hn hφy
      refine ⟨φ y * n * (φ y)⁻¹, h1, ?_⟩
      simp
    have hpow' : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N.map φ.symm.toMonoidHom := by
      intro x hx
      obtain ⟨k, hk⟩ := hpow (φ x) ⟨x, hx, rfl⟩
      refine ⟨k, ⟨φ x ^ 2 ^ k, hk, ?_⟩⟩
      simp
    have := hO2 _ hN'L hN' hpow'
    rw [← this, map_equiv_map_equiv_symm]
  · rw [HSType.quasithinGenFitting_map_mulEquiv, hF, pCoreOf_map_equiv]
  · rw [quasithinV2_map]
    exact fun h0 => hV ((map_equiv_eq_bot_iff φ _).mp h0)

end CFSG.Quasithin.H13.A5
