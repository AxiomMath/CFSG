module

public import CFSG.Quasithin.Vol2.Ch6Sec1Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative

section Transport

variable {G G' : Type} [Group G] [Group G']

theorem map_symm_map_mulEquiv (φ : G ≃* G') (H : Subgroup G) :
    (H.map φ.toMonoidHom).map φ.symm.toMonoidHom = H := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨φ x, ⟨x, hx, rfl⟩, by simp⟩

theorem map_map_symm_mulEquiv (φ : G ≃* G') (H : Subgroup G') :
    (H.map φ.symm.toMonoidHom).map φ.toMonoidHom = H := by
  have := map_symm_map_mulEquiv φ.symm H
  rwa [MulEquiv.symm_symm] at this

theorem isSubnormal_map (φ : G ≃* G') {A B : Subgroup G} (h : IsSubnormal A B) :
    IsSubnormal (A.map φ.toMonoidHom) (B.map φ.toMonoidHom) :=
  h.map φ.toMonoidHom

theorem quasithinIsCComponent_map (φ : G ≃* G') {L X : Subgroup G}
    (h : quasithinIsCComponent L X) :
    quasithinIsCComponent (L.map φ.toMonoidHom) (X.map φ.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, isSubnormal_map φ h3,
    fun K hK hK1 hKK hKs => ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ φ.injective]
    exact h1
  · rw [← Subgroup.map_commutator, h2]
  · have hs := isSubnormal_map φ.symm hKs
    rw [map_symm_map_mulEquiv] at hs
    refine h4 (K.map φ.symm.toMonoidHom) ?_ ?_ ?_ hs
    · have hle : K.map φ.symm.toMonoidHom ≤ L := by
        have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hK.le
        rwa [map_symm_map_mulEquiv] at this
      refine lt_of_le_of_ne hle fun heq => hK.ne ?_
      have := congrArg (Subgroup.map φ.toMonoidHom) heq
      rwa [map_map_symm_mulEquiv] at this
    · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ φ.symm.injective]
      exact hK1
    · rw [← Subgroup.map_commutator, hKK]

theorem quasithinIsLocal_map [Finite G] [Finite G'] (φ : G ≃* G') {T L : Subgroup G}
    (h : quasithinIsLocal T L) :
    quasithinIsLocal (T.map φ.toMonoidHom) (L.map φ.toMonoidHom) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.map φ.toMonoidHom, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup]
    exact quasithinIsCComponent_map φ h2
  · rw [← Subgroup.map_sup]
    change ¬ 2 ∣ (T.map φ.toMonoidHom).relIndex ((L ⊔ T).map φ.toMonoidHom)
    rw [Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
    exact h3
  · rw [← Subgroup.map_sup, CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 φ, Ne,
      Subgroup.map_eq_bot_iff_of_injective _ φ.injective]
    exact h4

theorem quasithinIsMaximalLocal_map [Finite G] [Finite G'] (φ : G ≃* G') {T L : Subgroup G}
    (h : quasithinIsMaximalLocal T L) :
    quasithinIsMaximalLocal (T.map φ.toMonoidHom) (L.map φ.toMonoidHom) := by
  refine ⟨quasithinIsLocal_map φ h.1, fun K hK hLK => ?_⟩
  have h1 := quasithinIsLocal_map φ.symm hK
  rw [map_symm_map_mulEquiv] at h1
  have h2 : L ≤ K.map φ.symm.toMonoidHom := by
    have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hLK
    rwa [map_symm_map_mulEquiv] at this
  have h3 := h.2 _ h1 h2
  rw [← h3, map_map_symm_mulEquiv]

theorem inH_map (φ : G ≃* G') {X Y : Subgroup G} (h : InH X Y) :
    InH (X.map φ.toMonoidHom) (Y.map φ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 φ, Ne,
    Subgroup.map_eq_bot_iff_of_injective _ φ.injective]
  exact h.2

theorem isHStar_map (φ : G ≃* G') {T M H : Subgroup G} (h : IsHStar T M H) :
    IsHStar (T.map φ.toMonoidHom) (M.map φ.toMonoidHom) (H.map φ.toMonoidHom) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨inH_map φ h1, fun hle => h2 ?_, fun Y hY hYH hYM => ?_⟩
  · have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hle
    rwa [map_symm_map_mulEquiv, map_symm_map_mulEquiv] at this
  · have hY' : InH T (Y.map φ.symm.toMonoidHom) := by
      have := inH_map φ.symm hY
      rwa [map_symm_map_mulEquiv] at this
    have hYH' : Y.map φ.symm.toMonoidHom ≤ H := by
      have := Subgroup.map_mono (f := φ.symm.toMonoidHom) hYH
      rwa [map_symm_map_mulEquiv] at this
    have hYM' : ¬ Y.map φ.symm.toMonoidHom ≤ M := by
      intro hle
      apply hYM
      have := Subgroup.map_mono (f := φ.toMonoidHom) hle
      rwa [map_map_symm_mulEquiv] at this
    rw [← h3 _ hY' hYH' hYM', map_map_symm_mulEquiv]

end Transport

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer_ch6 {X : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (X : Set G)) :
    X.map (MulAut.conj m).toMonoidHom = X := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hm y).mp hy
  · intro hx
    refine ⟨m⁻¹ * x * m, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) x).mp hx
    simpa using this

theorem Hyp611.conj_of_mem (h : Hyp611 G T M L V n) {m : G} (hmM : m ∈ M)
    (hmV : m ∈ Subgroup.normalizer (V : Set G)) :
    Hyp611 G (T.map (MulAut.conj m).toMonoidHom) M L V n := by
  set φ : G ≃* G := MulAut.conj m with hφ
  have hM : M.map φ.toMonoidHom = M :=
    map_conj_eq_of_mem_normalizer_ch6 (Subgroup.le_normalizer hmM)
  have hL : L.map φ.toMonoidHom = L := map_conj_eq_of_mem_normalizer_ch6 (h.normal hmM)
  have hV : V.map φ.toMonoidHom = V := map_conj_eq_of_mem_normalizer_ch6 hmV
  have hLT : (L ⊔ T).map φ.toMonoidHom = L ⊔ T.map φ.toMonoidHom := by
    rw [Subgroup.map_sup, hL]
  have hloc := quasithinIsLocal_map φ h.maximal.1
  rw [hL] at hloc
  refine
    { simple := h.simple
      nonabelian := h.nonabelian
      qtke := h.qtke
      sylow := ⟨h.sylow.1.map φ.toMonoidHom, ?_⟩
      maxTwoLocal := h.maxTwoLocal
      T_le := ?_
      maximal := ?_
      faithful := ⟨hloc, h.faithful.2⟩
      L_le := h.L_le
      normal := h.normal
      two_le := h.two_le
      lie := h.lie
      module := ⟨?_, ?_, h.module.2.2⟩
      not_a5 := h.not_a5
      nParam_eq_one := ?_
      noLie := ?_ }
  · rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
    exact h.sylow.2
  · rw [← hM]
    exact Subgroup.map_mono h.T_le
  · have := quasithinIsMaximalLocal_map φ h.maximal
    rwa [hL] at this
  · rw [← hV, ← hLT]
    exact Subgroup.map_mono h.module.1
  ·
    let ψ : ↥(L ⊔ T) ≃* ↥(L ⊔ T.map φ.toMonoidHom) :=
      (φ.subgroupMap (L ⊔ T)).trans (MulEquiv.subgroupCongr hLT)
    have hred := isPrimeReduced_map ψ h.module.2.1
    have hmap : (V.subgroupOf (L ⊔ T)).map ψ.toMonoidHom =
        V.subgroupOf (L ⊔ T.map φ.toMonoidHom) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [← hV]
        exact ⟨y, hy, rfl⟩
      · intro hx
        have hx' : (x : G) ∈ V.map φ.toMonoidHom := by rw [hV]; exact hx
        obtain ⟨y, hy, hyx⟩ := hx'
        have hyLT : y ∈ L ⊔ T := by
          have hx2 : (x : G) ∈ (L ⊔ T).map φ.toMonoidHom := by rw [hLT]; exact x.2
          obtain ⟨z, hz, hzx⟩ := hx2
          have : z = y := φ.injective (hzx.trans hyx.symm)
          rw [← this]
          exact hz
        refine ⟨⟨y, hyLT⟩, hy, Subtype.ext ?_⟩
        exact hyx
    rw [← hmap]
    exact hred
  ·
    intro H hH
    have hH' := isHStar_map φ.symm hH
    rw [map_symm_map_mulEquiv] at hH'
    have hMs : M.map φ.symm.toMonoidHom = M := by
      have := congrArg (Subgroup.map φ.symm.toMonoidHom) hM
      rwa [map_symm_map_mulEquiv, eq_comm] at this
    rw [hMs] at hH'
    have h1 := h.nParam_eq_one _ hH'
    have h2 := E1.nParam_conj (m) (H.map φ.symm.toMonoidHom)
    rw [← h2] at h1
    have h3 : A1b.conjSub m (H.map φ.symm.toMonoidHom) = H := by
      unfold A1b.conjSub
      rw [← hφ, map_map_symm_mulEquiv]
    rwa [h3] at h1
  ·
    intro H hH K hK hLie
    have hH' := isHStar_map φ.symm hH
    rw [map_symm_map_mulEquiv] at hH'
    have hMs : M.map φ.symm.toMonoidHom = M := by
      have := congrArg (Subgroup.map φ.symm.toMonoidHom) hM
      rwa [map_symm_map_mulEquiv, eq_comm] at this
    rw [hMs] at hH'
    exact h.noLie _ hH' _ (quasithinIsCComponent_map φ.symm hK) (hLie.map_mulEquiv φ.symm)

theorem Hyp611Nat.conj_of_mem (h : Hyp611Nat G T M L V n) {m : G} (hmM : m ∈ M)
    (hmV : m ∈ Subgroup.normalizer (V : Set G)) :
    Hyp611Nat G (T.map (MulAut.conj m).toMonoidHom) M L V n :=
  { toHyp611 := h.toHyp611.conj_of_mem hmM hmV
    comm_eq := h.comm_eq
    natural := h.natural }

theorem Hyp611.exists_conj_sylow (h : Hyp611 G T M L V n) {P : Subgroup G}
    (hP : P ≤ ch6MV M V) (hP2 : IsPGroup 2 P) :
    ∃ m ∈ ch6MV M V, P ≤ T.map (MulAut.conj m).toMonoidHom := by
  have hTMV : T ≤ ch6MV M V := le_inf h.T_le h.T_le_normalizer
  have hTsyl : IsSylowTwoOf T (ch6MV M V) :=
    E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
      hTMV le_top
  obtain ⟨y, hy, hyT⟩ := exists_conj_le_of_isSylowTwoOf hTsyl hP hP2
  refine ⟨y⁻¹, (ch6MV M V).inv_mem hy, fun x hx => ?_⟩
  have hx' : y * x * y⁻¹ ∈ T := by
    have : y * x * y⁻¹ ∈ cjSub y P := mem_cjSub.mpr (by simpa [mul_assoc] using hx)
    exact hyT this
  refine ⟨y * x * y⁻¹, hx', ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end CFSG.Quasithin.H13
