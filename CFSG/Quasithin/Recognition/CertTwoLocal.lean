module

public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Quasithin.Background.F1Amalgam

public section

namespace CFSG.Quasithin

open scoped Pointwise
open CFSG.Open CFSG.QuasithinUnique

section Transport

variable {G H : Type*} [Group G] [Group H]

private theorem map_symm_map (φ : G ≃* H) (M : Subgroup G) :
    (M.map φ.toMonoidHom).map φ.symm.toMonoidHom = M := by
  ext g
  simp only [Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    simpa using hm
  · intro hg
    exact ⟨φ g, ⟨g, hg, rfl⟩, by simp⟩

theorem isTwoLocal_map (φ : G ≃* H) {M : Subgroup G} (h : IsTwoLocal M) :
    IsTwoLocal (M.map φ.toMonoidHom) := by
  obtain ⟨P, hP, hPp, rfl⟩ := h
  refine ⟨P.map φ.toMonoidHom, ?_, hPp.map _, ?_⟩
  · intro hbot
    apply hP
    exact (Subgroup.map_eq_bot_iff_of_injective P
      (show Function.Injective φ.toMonoidHom from φ.injective)).1 hbot
  · exact Subgroup.map_equiv_normalizer_eq P φ

theorem isTwoLocal_map_iff (φ : G ≃* H) {M : Subgroup G} :
    IsTwoLocal (M.map φ.toMonoidHom) ↔ IsTwoLocal M := by
  refine ⟨fun h => ?_, isTwoLocal_map φ⟩
  have := isTwoLocal_map φ.symm h
  rwa [map_symm_map] at this

theorem isMaximalTwoLocal_map (φ : G ≃* H) {M : Subgroup G} (h : IsMaximalTwoLocal M) :
    IsMaximalTwoLocal (M.map φ.toMonoidHom) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨isTwoLocal_map φ h1, fun M' hM' hle => ?_⟩
  have h3 : IsTwoLocal (M'.map φ.symm.toMonoidHom) := isTwoLocal_map φ.symm hM'
  have h4 : M ≤ M'.map φ.symm.toMonoidHom := by
    intro g hg
    rw [Subgroup.mem_map]
    refine ⟨φ g, hle ⟨g, hg, rfl⟩, by simp⟩
  have h5 := h2 _ h3 h4
  have h6 : M' = (M'.map φ.symm.toMonoidHom).map φ.toMonoidHom := by
    have := map_symm_map φ.symm M'
    simpa using this.symm
  rw [h6, h5]

theorem IsYAmalgamPair.map (φ : G ≃* H) {T M₁ M₂ : Subgroup G} (h : IsYAmalgamPair T M₁ M₂) :
    IsYAmalgamPair (T.map φ.toMonoidHom) (M₁.map φ.toMonoidHom) (M₂.map φ.toMonoidHom) := by
  obtain ⟨hsyl, hne, hiff⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨-, hp, hidx⟩ := hsyl
    refine ⟨le_top, hp.map _, ?_⟩
    have e1 : (T.subgroupOf ⊤).index = T.index := Subgroup.relIndex_top_right T
    have e2 : ((T.map φ.toMonoidHom).subgroupOf ⊤).index = (T.map φ.toMonoidHom).index :=
      Subgroup.relIndex_top_right _
    have e3 : (T.map φ.toMonoidHom).index = T.index := Subgroup.index_map_equiv T φ
    rw [e2, e3]
    rwa [e1] at hidx
  · exact fun e => hne (Subgroup.map_injective φ.injective e)
  · have hN : Subgroup.normalizer ((T.map φ.toMonoidHom : Subgroup H) : Set H) =
        (Subgroup.normalizer (T : Set G)).map φ.toMonoidHom :=
      (Subgroup.map_equiv_normalizer_eq T φ).symm
    intro M
    constructor
    · rintro ⟨hM, hNM⟩
      have hM0 : IsMaximalTwoLocal (M.map φ.symm.toMonoidHom) := isMaximalTwoLocal_map φ.symm hM
      have hN0 : Subgroup.normalizer (T : Set G) ≤ M.map φ.symm.toMonoidHom := by
        intro g hg
        rw [Subgroup.mem_map]
        refine ⟨φ g, hNM ?_, by simp⟩
        rw [hN]
        exact ⟨g, hg, rfl⟩
      have hM6 : M = (M.map φ.symm.toMonoidHom).map φ.toMonoidHom := by
        have := map_symm_map φ.symm M
        simpa using this.symm
      rcases (hiff _).1 ⟨hM0, hN0⟩ with h1 | h1
      · left; rw [hM6, h1]
      · right; rw [hM6, h1]
    · rintro (rfl | rfl)
      · obtain ⟨hM, hNM⟩ := (hiff M₁).2 (Or.inl rfl)
        refine ⟨isMaximalTwoLocal_map φ hM, ?_⟩
        rw [hN]
        exact Subgroup.map_mono hNM
      · obtain ⟨hM, hNM⟩ := (hiff M₂).2 (Or.inr rfl)
        refine ⟨isMaximalTwoLocal_map φ hM, ?_⟩
        rw [hN]
        exact Subgroup.map_mono hNM

end Transport

section Recognition

variable {G ι κ : Type*} [Group G] (d : OvergroupData G ι κ)

structure OvergroupData.Extra where
  syl : IsPGroup 2 d.T ∧ ¬ 2 ∣ d.T.index
  g : G
  hg : ∀ i i', g * d.Tel i' * g⁻¹ = d.Tel i → d.Tel i = 1
  a_ne_one : d.a ≠ 1
  xN : ∃ i, ∀ i', d.x * d.Tel i * d.x⁻¹ ≠ d.Tel i'
  yN : ∃ i, ∀ i', d.y * d.Tel i * d.y⁻¹ ≠ d.Tel i'
  PA : Subgroup G
  PA_ne : PA ≠ ⊥
  PA_p : IsPGroup 2 PA
  PA_norm : d.A ≤ Subgroup.normalizer (PA : Set G)
  PB : Subgroup G
  PB_ne : PB ≠ ⊥
  PB_p : IsPGroup 2 PB
  PB_norm : d.B ≤ Subgroup.normalizer (PB : Set G)

variable {d}

theorem OvergroupData.Extra.eq_bot_of_normal (e : d.Extra) (P : Subgroup G) (hPn : P.Normal)
    (hP : IsPGroup 2 P) : P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 G := e.syl.1.toSylow e.syl.2
  have h1 : P ≤ (S : Subgroup G) := hP.le_sylow_of_normal S
  have h2 : P ≤ ((e.g • S : Sylow 2 G) : Subgroup G) := hP.le_sylow_of_normal (e.g • S)
  rw [eq_bot_iff]
  intro p hp
  have hpT : p ∈ d.T := h1 hp
  have hpS : p ∈ ((e.g • S : Sylow 2 G) : Subgroup G) := h2 hp
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hpS
  obtain ⟨t, ht, htp⟩ := hpS
  have ht' : t ∈ d.T := ht
  obtain ⟨i', hi'⟩ := (d.mem_T_iff t).1 ht'
  obtain ⟨i, hi⟩ := (d.mem_T_iff p).1 hpT
  have hconj : p = e.g * t * e.g⁻¹ := by
    rw [← htp]
    simp [MulAut.conj_apply]
  rw [Subgroup.mem_bot, ← hi]
  exact e.hg i i' (by rw [hi', hi, hconj])

theorem OvergroupData.Extra.normalizer_T (e : d.Extra) :
    Subgroup.normalizer (d.T : Set G) = d.T := by
  have hle : d.T ≤ Subgroup.normalizer (d.T : Set G) := Subgroup.le_normalizer
  rcases d.lattice _ hle with h | h | h | h
  · exact h
  · exfalso
    obtain ⟨i, hi⟩ := e.xN
    have hx : d.x ∈ Subgroup.normalizer (d.T : Set G) := by
      rw [h]; exact d.x_mem_A
    obtain ⟨i', hi'⟩ := (d.mem_T_iff _).1
      ((Subgroup.mem_normalizer_iff.1 hx (d.Tel i)).1 (d.Tel_mem_T i))
    exact hi i' hi'.symm
  · exfalso
    obtain ⟨i, hi⟩ := e.yN
    have hy : d.y ∈ Subgroup.normalizer (d.T : Set G) := by
      rw [h]; exact d.y_mem_B
    obtain ⟨i', hi'⟩ := (d.mem_T_iff _).1
      ((Subgroup.mem_normalizer_iff.1 hy (d.Tel i)).1 (d.Tel_mem_T i))
    exact hi i' hi'.symm
  · exfalso
    have hbot := e.eq_bot_of_normal d.T (Subgroup.normalizer_eq_top_iff.1 h) e.syl.1
    exact e.a_ne_one (by simpa [hbot] using d.a_mem_T)

theorem OvergroupData.Extra.isTwoLocal_A (e : d.Extra) : IsTwoLocal d.A := by
  refine ⟨e.PA, e.PA_ne, e.PA_p, ?_⟩
  have hTle : d.T ≤ Subgroup.normalizer (e.PA : Set G) := d.T_le_A.trans e.PA_norm
  rcases d.lattice _ hTle with h | h | h | h
  · exfalso
    have : d.A ≤ d.T := by rw [← h]; exact e.PA_norm
    exact d.T_ne_A (le_antisymm d.T_le_A this)
  · exact h.symm
  · exfalso
    have hAB : d.A ≤ d.B := by rw [← h]; exact e.PA_norm
    have : d.A ≤ d.T := by rw [← d.inf_AB]; exact le_inf le_rfl hAB
    exact d.T_ne_A (le_antisymm d.T_le_A this)
  · exfalso
    exact e.PA_ne (e.eq_bot_of_normal e.PA (Subgroup.normalizer_eq_top_iff.1 h) e.PA_p)

theorem OvergroupData.Extra.isTwoLocal_B (e : d.Extra) : IsTwoLocal d.B := by
  refine ⟨e.PB, e.PB_ne, e.PB_p, ?_⟩
  have hTle : d.T ≤ Subgroup.normalizer (e.PB : Set G) := d.T_le_B.trans e.PB_norm
  rcases d.lattice _ hTle with h | h | h | h
  · exfalso
    have : d.B ≤ d.T := by rw [← h]; exact e.PB_norm
    exact d.T_ne_B (le_antisymm d.T_le_B this)
  · exfalso
    have hBA : d.B ≤ d.A := by rw [← h]; exact e.PB_norm
    have : d.B ≤ d.T := by rw [← d.inf_AB]; exact le_inf hBA le_rfl
    exact d.T_ne_B (le_antisymm d.T_le_B this)
  · exact h.symm
  · exfalso
    exact e.PB_ne (e.eq_bot_of_normal e.PB (Subgroup.normalizer_eq_top_iff.1 h) e.PB_p)

theorem OvergroupData.Extra.isMaximalTwoLocal_A (e : d.Extra) : IsMaximalTwoLocal d.A := by
  refine ⟨e.isTwoLocal_A, fun M' hM' hle => ?_⟩
  obtain ⟨P', hP', hP'p, rfl⟩ := hM'
  rcases d.lattice _ (d.T_le_A.trans hle) with h | h | h | h
  · exfalso
    have : d.A ≤ d.T := by rw [← h]; exact hle
    exact d.T_ne_A (le_antisymm d.T_le_A this)
  · exact h
  · exfalso
    have hAB : d.A ≤ d.B := by rw [← h]; exact hle
    have : d.A ≤ d.T := by rw [← d.inf_AB]; exact le_inf le_rfl hAB
    exact d.T_ne_A (le_antisymm d.T_le_A this)
  · exfalso
    exact hP' (e.eq_bot_of_normal P' (Subgroup.normalizer_eq_top_iff.1 h) hP'p)

theorem OvergroupData.Extra.isMaximalTwoLocal_B (e : d.Extra) : IsMaximalTwoLocal d.B := by
  refine ⟨e.isTwoLocal_B, fun M' hM' hle => ?_⟩
  obtain ⟨P', hP', hP'p, rfl⟩ := hM'
  rcases d.lattice _ (d.T_le_B.trans hle) with h | h | h | h
  · exfalso
    have : d.B ≤ d.T := by rw [← h]; exact hle
    exact d.T_ne_B (le_antisymm d.T_le_B this)
  · exfalso
    have hBA : d.B ≤ d.A := by rw [← h]; exact hle
    have : d.B ≤ d.T := by rw [← d.inf_AB]; exact le_inf hBA le_rfl
    exact d.T_ne_B (le_antisymm d.T_le_B this)
  · exact h
  · exfalso
    exact hP' (e.eq_bot_of_normal P' (Subgroup.normalizer_eq_top_iff.1 h) hP'p)

theorem OvergroupData.Extra.inf_eq_T (e : d.Extra) {M₁ M₂ : Subgroup G}
    (h : IsYAmalgamPair d.T M₁ M₂) : M₁ ⊓ M₂ = d.T := by
  obtain ⟨-, hne, hiff⟩ := h
  have hN : Subgroup.normalizer (d.T : Set G) ≤ d.A := by
    rw [e.normalizer_T]; exact d.T_le_A
  have hN' : Subgroup.normalizer (d.T : Set G) ≤ d.B := by
    rw [e.normalizer_T]; exact d.T_le_B
  have hA := (hiff d.A).1 ⟨e.isMaximalTwoLocal_A, hN⟩
  have hB := (hiff d.B).1 ⟨e.isMaximalTwoLocal_B, hN'⟩
  have hAB : d.A ≠ d.B := fun h => d.T_ne_A (by rw [← d.inf_AB, h, inf_idem])
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (hA.trans hB.symm) hAB
  · rw [← hA, ← hB, d.inf_AB]
  · rw [← hA, ← hB, inf_comm, d.inf_AB]
  · exact absurd (hA.trans hB.symm) hAB

theorem OvergroupData.Extra.recog [Finite G] (e : d.Extra) {T' M₁ M₂ : Subgroup G}
    (h : IsYAmalgamPair T' M₁ M₂) : Nonempty (↥(M₁ ⊓ M₂) ≃* ↥d.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl' : IsSylowTwoOf T' ⊤ := h.1
  obtain ⟨-, hp', hidx'⟩ := hsyl'
  have e1 : (T'.subgroupOf ⊤).index = T'.index := Subgroup.relIndex_top_right T'
  have hidx : ¬ 2 ∣ T'.index := by rwa [e1] at hidx'
  let S : Sylow 2 G := e.syl.1.toSylow e.syl.2
  let S' : Sylow 2 G := hp'.toSylow hidx
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq G S S'
  have hk' : MulAut.conj k • d.T = T' := by
    have h1 := congrArg (fun P : Sylow 2 G => (P : Subgroup G)) hk
    simp only [Sylow.coe_subgroup_smul] at h1
    exact h1
  have hT'map : T' = d.T.map (MulAut.conj k).toMonoidHom := by
    rw [← hk']
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  let φ : G ≃* G := (MulAut.conj k).symm
  have hh := IsYAmalgamPair.map φ h
  have hT'φ : T'.map φ.toMonoidHom = d.T := by
    rw [hT'map]
    exact map_symm_map (MulAut.conj k) d.T
  rw [hT'φ] at hh
  have hinf := e.inf_eq_T hh
  have hinf' : (M₁ ⊓ M₂).map φ.toMonoidHom = d.T := by
    rw [Subgroup.map_inf M₁ M₂ φ.toMonoidHom φ.injective]
    exact hinf
  exact ⟨(Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
    (MulEquiv.subgroupCongr hinf')⟩

end Recognition

end CFSG.Quasithin
