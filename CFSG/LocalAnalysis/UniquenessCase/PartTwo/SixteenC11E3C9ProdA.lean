module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3NineA
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s1611e3_relIndex_map_dvd {G₁ G₂ : Type*} [Group G₁] [Group G₂] (φ : G₁ →* G₂)
    (H K : Subgroup G₁) : (H.map φ).relIndex (K.map φ) ∣ H.relIndex K := by
  have hK : K.map φ = (φ.comp K.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hK, ← Subgroup.index_comap]
  exact Subgroup.index_dvd_of_le fun k hk =>
    Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)

theorem s1611e3_barSub_sylow {M T V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : M ≤ stabTil V₀ V) (hT : IsSylowIn 2 T M) :
    IsSylowIn 2 (barSub V₀ V hV T) (barSub V₀ V hV M) := by
  let S := stabTil V₀ V
  let F : ↥S →* MulAut (Vtil V₀ V hV) := actTil V₀ V hV
  have hT'p : IsPGroup 2 (T.subgroupOf S) := hT.isPGroup.comap_subtype
  refine ⟨barSub_mono V₀ V hV hT.le, ?_, ?_⟩
  · show IsPGroup 2 ((T.subgroupOf S).map F)
    exact hT'p.map F
  · change ¬ 2 ∣ ((T.subgroupOf S).map F).relIndex ((M.subgroupOf S).map F)
    intro hdvd
    have hdvd' : 2 ∣ (T.subgroupOf S).relIndex (M.subgroupOf S) :=
      hdvd.trans (s1611e3_relIndex_map_dvd F (T.subgroupOf S) (M.subgroupOf S))
    rw [Subgroup.relIndex_subgroupOf hM] at hdvd'
    exact hT.not_dvd_relIndex hdvd'

theorem s1611e3_relIndex_stabilizer_eq_two {W : Type*} [Group W]
    {X K : Subgroup (MulAut W)} {x₁ : MulAut W} (hx₁ : x₁ ∈ X)
    (hx₁K : K.map (MulAut.conj x₁).toMonoidHom ≠ K)
    (huniq : ∀ a ∈ X, ∀ b ∈ X, K.map (MulAut.conj a).toMonoidHom ≠ K →
      K.map (MulAut.conj b).toMonoidHom ≠ K →
        K.map (MulAut.conj a).toMonoidHom = K.map (MulAut.conj b).toMonoidHom) :
    ((X ⊓ Subgroup.normalizer (K : Set (MulAut W))).subgroupOf X).index = 2 := by
  set K' := K.map (MulAut.conj x₁).toMonoidHom with hK'
  have hmemA : ∀ b : X, b ∈ (X ⊓ Subgroup.normalizer (K : Set (MulAut W))).subgroupOf X ↔
      K.map (MulAut.conj (b : MulAut W)).toMonoidHom = K := fun b => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => (Subgroup.mem_normalizer_iff_map_conj_eq).1 h.2,
      fun h => ⟨b.2, (Subgroup.mem_normalizer_iff_map_conj_eq).2 h⟩⟩
  have hinj : ∀ (b : MulAut W) (A₁ A₂ : Subgroup (MulAut W)),
      A₁.map (MulAut.conj b).toMonoidHom = A₂.map (MulAut.conj b).toMonoidHom → A₁ = A₂ :=
    fun b _ _ h => Subgroup.map_injective (MulAut.conj b).injective h
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨x₁, hx₁⟩, fun b => xor_iff_iff_not.mpr ⟨fun hbg hb => ?_, fun hb => ?_⟩⟩
  · rw [hmemA, Subgroup.coe_mul, ← s1611e3_nine_map_conj_map_conj] at hbg
    rw [hmemA] at hb
    exact hx₁K (hinj b K' K (hbg.trans hb.symm))
  · rw [hmemA] at hb
    rw [hmemA, Subgroup.coe_mul, ← s1611e3_nine_map_conj_map_conj]
    by_contra hne
    have h1 := huniq _ (X.mul_mem b.2 hx₁) _ b.2
      (by rw [← s1611e3_nine_map_conj_map_conj]; exact hne) hb
    rw [← s1611e3_nine_map_conj_map_conj] at h1
    exact hx₁K (hinj b K' K h1)

theorem s1611e3_commutator_prod {Z S : Type*} [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) :
    _root_.commutator (Z × S × S) =
      (⊥ : Subgroup Z).prod ((⊤ : Subgroup S).prod (⊤ : Subgroup S)) := by
  rw [_root_.commutator_def]
  simp only [← Subgroup.top_prod_top]
  rw [Subgroup.commutator_prod_prod, Subgroup.commutator_prod_prod]
  simp only [show ⁅(⊤ : Subgroup Z), ⊤⁆ = ⊥ from commutator_eq_bot Z,
    show ⁅(⊤ : Subgroup S), ⊤⁆ = ⊤ from hperf.commutator_eq_top]

theorem s1611e3_commutator_card {F Z S : Type*} [Group F] [CommGroup Z] [Group S]
    (hperf : Group.IsPerfect S) (e : F ≃* Z × S × S) :
    Nat.card ↥(_root_.commutator F) = Nat.card S * Nat.card S := by
  have hmap : (_root_.commutator F).map e.toMonoidHom = _root_.commutator (Z × S × S) := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
    rfl
  rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective, hmap,
    s1611e3_commutator_prod hperf,
    Nat.card_congr (Subgroup.prodEquiv (⊥ : Subgroup Z)
      ((⊤ : Subgroup S).prod (⊤ : Subgroup S))).toEquiv,
    Nat.card_prod, Subgroup.card_bot, one_mul,
    Nat.card_congr (Subgroup.prodEquiv (⊤ : Subgroup S) (⊤ : Subgroup S)).toEquiv,
    Nat.card_prod, Subgroup.card_top]

theorem s1611e3_commutator_conj_mem {W : Type*} [Group W] {F Mb : Subgroup (MulAut W)}
    (hFn : ∀ x ∈ Mb, ∀ f ∈ F, x * f * x⁻¹ ∈ F) :
    ∀ m ∈ Mb, ∀ n ∈ (commutator ↥F).map F.subtype,
      m * n * m⁻¹ ∈ (commutator ↥F).map F.subtype := by
  intro m hm n hn
  have hFmap : F.map (MulAut.conj m).toMonoidHom = F := by
    apply le_antisymm
    · rintro x ⟨f, hf, rfl⟩
      simpa [MulAut.conj_apply] using hFn m hm f hf
    · intro x hx
      refine Subgroup.mem_map.2 ⟨m⁻¹ * x * m, hFn m⁻¹ (Mb.inv_mem hm) x hx, ?_⟩
      show m * (m⁻¹ * x * m) * m⁻¹ = x
      group
  have hEmap : ((commutator ↥F).map F.subtype).map (MulAut.conj m).toMonoidHom =
      (commutator ↥F).map F.subtype := by
    rw [Subgroup.map_subtype_commutator, Subgroup.map_commutator, hFmap,
      ← Subgroup.map_subtype_commutator]
  have hmem : (MulAut.conj m).toMonoidHom n ∈
      ((commutator ↥F).map F.subtype).map (MulAut.conj m).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hn
  rw [hEmap] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem s1611e3_lBar_le_fstar {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D V₀ V L hV) (h9 : Case168_9 D V₀ V hV L) :
    lBar V₀ V hV L ≤ Fstar (Mbar D.M V₀ V hV) := by
  obtain ⟨⟨e⟩, hL3, -, -, -⟩ := h9
  have hLPSL : IsPSL 3 2 1 ↥(lBar V₀ V hV L) := s16n9b_case9_isPSL_of_isL3 hL3
  obtain ⟨hFX, hFn, hselfF⟩ := s16c167_cfg10_fstar_facts (Mbar D.M V₀ V hV)
  have hSC := s16c167_isPSL_simpleCentreless hLPSL
  have hperf := s16c167_isPSL_isPerfect hLPSL
  have hout := s16c167_isPSL_outer_solvable hLPSL
  have hOutF := s16c167_frame_outer_cyclic_square_solvable hSC hperf hout e
  exact s16c167_frame_le_of_perfect hFX (barSub_mono V₀ V hV hc.setting.hyp151.le) hFn hselfF
    hOutF hperf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
